-- | The rule engine, read-only (§7.6, §8).
--
-- This module /finds/ rules. It does not run them: dispatch, the @Choice@
-- frame and backtracking are phase 16's, and the tactics the rules will
-- eventually be are phase 17's. What is here is the part everything else needs
-- first — a rule base in definition order, a persistent iterator over the rules
-- whose heads pass at the focus, and the validation pass that says whether a
-- rule is well formed at all.
--
-- 'Rule' and 'Test' themselves are "Thena.Ops"' — §2.5's layering was wrong and
-- the user corrected it 2026-08-23 (@AGENDA.md@ item 25). The rest of §2.5's
-- listing for this module stands.
module Thena.Rules
  ( -- * Rule bases
    RuleBase (..)
  , ruleBase
  , allRules
  , allCallable
  , allLanguages
  , allSignatures

    -- * Finding rules (§7.6)
  , RuleIter
  , matches
  , dispatch
  , clauses
  , arities
  , next
  , hasNext

    -- * Well-formedness (§2.4, §7.2)
  , RuleError (..)
  , validate
  , validateBase

    -- * Written rules (§8, phase 21)
  , opWords
  , resolveFunction
  , resolveLanguage
  , resolveRule
  , resolveSignature
  , resolveTy
  , builtInTypes
  , resolveBlock
  , testWord
  , testOperands
  , testTypes
  , everyTest
  ) where

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..))
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor (Cursor, Focus (..), context, expectedType, focus)
import Thena.Global.Env (GlobalEnv)
import qualified Thena.Ops as Op
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Name
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  , Value (..)
  , operandsOf
  , refsIn
  , partOf
  , partWords
  , produces
  )
import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..))
import qualified Thena.Surface.Zipper as Zipper
import Thena.Errors (SyntaxError (..))
import Thena.Surface.Read (parseSurfaceText)
import Thena.Surface.Zipper (rootedAt)
import Thena.Syntax.Lexer (lexTokens)
import Thena.Syntax.Parser (parseTerm)
import Thena.Instral.Grammar
  ( GrammarError
  , Item (..)
  , Language
  , Production (..)
  , language
  , parseObject
  )
import qualified Thena.Instral.Type as Ty
import Thena.Instral.Type (Signature (..), Ty (..))
import Thena.Instral.Concrete
  ( RawSignature (..)
  , RawLanguage (..)
  , RawProduction (..)
  , RawGItem (..)
  , RawFunction (..)
  , RawRhs (..)
  , RawTy (..)
  , RawInstr (..)
  , RawOp (..)
  , RawOperand (..)
  , RawRule (..)
  , RawTest (..)
  )
import Data.Either (partitionEithers)

-- --------------------------------------------------------------------------
-- The rule base
-- --------------------------------------------------------------------------

-- | One loaded rule-base file: its name, what it says it is for, where it came
-- from, and its rules **in definition order**, which is search order (§8,
-- DECIDED 2026-08-10).
--
-- **A record and not a bare list, and the machine holds a /list of these/ —
-- DECIDED by the user 2026-08-25.** He was explicit that one base was never the
-- goal: *"the intended goal for when it is nearing maturity is that we can load
-- multiple rule-bases the same way we would load multiple prolog files"*. So a
-- base is a named thing with a provenance, and 'Thena.Engine.Machine' carries
-- @[RuleBase]@ — leftmost searched first.
--
-- **A plain list and no newtype over it.** The order is the list\'s order and
-- there is no invariant to hide, so a wrapper would earn nothing; it would also
-- put @RuleBase@ and @RuleBases@ one @s@ apart, which is exactly the kind of
-- name that fails said out loud.
--
-- The name and description come from the file\'s header line, @rule base ‹name›
-- ‹description› where@ — see "Thena.Driver"\'s @ruleHeader@.
data RuleBase = RuleBase
  { baseName        :: String
  , baseDescription :: Maybe String
  , basePath        :: FilePath
  , baseSignatures  :: [(String, Signature)]
    -- ^ **the types its file declared** (MS5 phase 67), keyed by name; the
    -- arity is @length . 'Thena.Instral.Type.sigParams'@, because a signature's
    -- arrow chain has one link per parameter.
  , baseLanguages   :: [(String, Language)]
    -- ^ **the object languages its file declared** (MS5 phase 69). Each one is a
    -- tag, an opaque @instral@ type and a generated parser; see
    -- "Thena.Instral.Grammar".
  , baseFunctions   :: [Rule]
    -- ^ **the global functions its file declared** (MS5 phase 68a), each already
    -- an ordinary 'Rule' — his §1.1: /a function is a rule with one clause and
    -- no head/. They are kept apart from 'baseRules' for one reason and it is
    -- not the engine's: a function must not appear in 'matches', because a
    -- headless rule matches everywhere and @prove@ would run it. Phase 71's
    -- by-type query wants the list on its own anyway.
  , baseRules       :: [Rule]
  }
  deriving (Eq, Show)

-- | Build one. Nothing is checked here — 'validateBase' is separate, so that a
-- caller who wants the errors gets them all rather than the first.
ruleBase
  :: String -> Maybe String -> FilePath -> [(String, Signature)]
  -> [(String, Language)] -> [Rule] -> [Rule] -> RuleBase
ruleBase = RuleBase

-- | Every rule the engine may search, across every loaded base, **in search
-- order**: the bases in the order they were loaded, and within each the order
-- its file wrote them.
--
-- This is the one place that says what \"leftmost first\" means, which is why
-- 'matches' takes the bases rather than the rules.
allRules :: [RuleBase] -> [Rule]
allRules = concatMap baseRules

-- | Every declared signature, across every loaded base.
--
-- **A signature is a claim about a callable, not about a file**, so a base that
-- declares one for a rule written in another base is not wrong here; whether
-- anything answers to it is 'Thena.Instral.Infer''s question.
allSignatures :: [RuleBase] -> [(String, Signature)]
allSignatures = concatMap baseSignatures

-- | Everything @Call@ may reach: the rules **and the functions**.
--
-- 'allRules' is what 'matches' and 'dispatch' see, and it is deliberately the
-- smaller list — see 'baseFunctions'.
-- | Every object language, across every loaded base.
allLanguages :: [RuleBase] -> [(String, Language)]
allLanguages = concatMap baseLanguages

allCallable :: [RuleBase] -> [Rule]
allCallable bs = concatMap baseRules bs ++ concatMap baseFunctions bs

-- --------------------------------------------------------------------------
-- Finding rules (§7.6)
-- --------------------------------------------------------------------------

-- | The rules still to be offered, in definition order.
--
-- **Persistent, and a lazy list rather than a state-and-step pair** (§7.6). Two
-- things follow that a mutable iterator would not give. A frame may hold one
-- while the UI holds the same one, and advancing either cannot disturb the
-- other. And 'Thena.Engine.Frame' derives @Eq@ and @Show@, which phase 16's
-- @Choice@ constructor needs and which a function inside the iterator would
-- have made impossible.
--
-- Laziness is not a nicety here: 'matches' filters by running heads, heads run
-- 'whnf' (§8), so the tail is real work that 'hasNext' should not do more of
-- than it must.
newtype RuleIter = RuleIter [Rule]
  deriving (Eq, Show)

-- | Every rule whose head passes at the focus, in definition order (§7.6).
--
-- It takes a 'Cursor' rather than a 'Thena.Engine.Development' because
-- @Development@ is "Thena.Engine"'s and this module sits below it — and it can,
-- since @Development@ is a newtype over exactly this cursor. It takes a
-- 'GlobalEnv' because §8's head matching runs 'whnf' and 'whnf' unfolds
-- globals. It needs no name counter: the type a head reads is the one the
-- development /writes down/ ('expectedType'), never one @infer@ derives.
--
-- §7.6's signature is corrected to this.
--
-- **This is a query and nothing more.** No body runs, and nothing is
-- speculatively executed to see whether it would succeed — that is a real
-- feature, a far more expensive one, and it is not MS1 (§2.2, §7.6).
--
-- **The base is no longer partitioned** (MS4 phase 41). A hint used to split it
-- in two — rules whose head asked about one, and the rest — and both halves are
-- gone with the hint: elaboration is a rule called by name, so nothing about it
-- is a dispatch. Every rule whose head passes is a candidate, which is what §7.6
-- said in the first place.
matches :: [RuleBase] -> GlobalEnv -> Cursor -> RuleIter
matches bases env cur =
  RuleIter [ r | r <- allRules bases, all (holds env cur []) (ruleHead r) ]

-- | The rules @Prove@ may actually run: 'matches', less the ones it could not
-- supply arguments for.
--
-- **A parameterised rule is @Call@-only** — §8 says @ruleParams@ are "for
-- @Call@" and @Prove@ passes nothing, so a rule with parameters would be
-- dispatched into a body whose first @Ref@ is unbound. Decided by the user
-- 2026-08-23 (@AGENDA.md@ item 34); asking the user for each parameter was the
-- alternative and was declined.
--
-- **'matches' is deliberately not filtered.** The two answer different
-- questions: this one is /what the engine can run/, and 'matches' is /what
-- could be done here/, which includes @try ‹t›@ because the user can type
-- @try x@. @:matches@ keeps showing it.
dispatch :: [RuleBase] -> GlobalEnv -> Cursor -> RuleIter
dispatch base env cur =
  let RuleIter rs = matches base env cur
   in RuleIter [ r | r <- rs, null (ruleParams r) ]

-- | The clauses @Call@ may run: **this name, this arity, and a head that
-- passes** (§8, phase 23).
--
-- The third filter is what the user reversed a phase-15 decision for — a call
-- tests the callee's head, because with several clauses of one name a call is a
-- search and not a jump. The second is why clauses need not share arity: it is
-- a filter, so a name may carry a one-argument clause and a two-argument one
-- and each call picks its own.
--
-- **The arguments reach the head** (MS4 phase 47). A clause's head may ask
-- about what it was called with — @when surface-is-name t@ — and each clause
-- binds them to /its own/ parameter names, exactly as "Thena.Engine" does when
-- it enters the body. Passing the values rather than an environment is what
-- keeps that true: clauses of one name need not agree about what they call
-- their parameters.
clauses
  :: [RuleBase] -> GlobalEnv -> Cursor -> GlobalName -> [Value] -> RuleIter
clauses bases env cur nm vs =
  RuleIter
    [ r
    | r <- allCallable bases
    , ruleName r == nm
    , length (ruleParams r) == length vs
    , all (holds env cur (zip (ruleParams r) vs)) (ruleHead r)
    ]

-- | The arities of every rule bearing this name, in search order.
--
-- Only a diagnostic: 'Thena.Errors.NoClauseMatched' carries it so that a failed
-- call can say /no clause of @f@ takes two arguments/ rather than only /nothing
-- matched/.
arities :: [RuleBase] -> GlobalName -> [Int]
arities bases nm =
  [ length (ruleParams r) | r <- allCallable bases, ruleName r == nm ]

next :: RuleIter -> Maybe (Rule, RuleIter)
next (RuleIter rs) = case rs of
  []      -> Nothing
  r : rest -> Just (r, RuleIter rest)

-- | Is there another? Phase 16's peek asks this to decide whether a @Choice@
-- frame is worth building at all (§7.3), so it must not force more of the list
-- than one more head match.
hasNext :: RuleIter -> Bool
hasNext (RuleIter rs) = not (null rs)

-- | One shape question, answered against the focus.
--
-- **The cost of shallow heads, in one concrete case** (§8). @GoalTypeIsPi@ asks
-- about the focused component's own type, so at
-- @? x ≐ (λ A . ? h : Nat . h) : ∀ (A : Type₀) -> Nat@ it passes — the guess's
-- type is a Π — while @intro@ itself would fail, because the hole it actually
-- reaches is at @Nat@. That is §8's stated cost arriving, not a bug: the rule
-- matches, runs and fails in its body, and failing in a body is already handled
-- (§7.3). Asking about the hole at the bottom of the guess instead would make
-- the head a traversal, which is what \"shallow\" rules out.
-- **The third argument binds a call's arguments to this clause's parameters**
-- (MS4 phase 47), and is empty for 'matches' and 'dispatch', which supply
-- none.
--
-- **An argument nobody supplied does not exclude the rule.** 'matches' asks
-- /what could be done here/, and whether @elaborate@ applies depends on a term
-- the user has not typed yet — so the honest answer is that the question was
-- not about the state and cannot rule the clause out. It is one reading, not a
-- special case: under 'clauses' every parameter is bound, so the situation
-- arises only where there is genuinely nothing to ask about, and
-- 'validate' refuses a head that names anything but a parameter, so an unbound
-- name here is never a mistake in the rule.
holds :: GlobalEnv -> Cursor -> Op.Env -> Test -> Bool
holds env cur args t = case t of
  FocusIsHole   -> case focus cur of
    OnComponent (Component.Claim {}) -> True
    _                                -> False
  FocusIsGuess  -> case focus cur of
    OnComponent (Component.Guess {}) -> True
    _                                -> False
  FocusIsComponent -> case focus cur of
    OnComponent _ -> True
    _             -> False
  GoalTypeIsPi  -> case reduced of
    Just (Pi {}) -> True
    _            -> False
  -- The one test that does NOT reduce, and it cannot: 'whnf' δ-reduces a
  -- term-level @let@ away (§5.1), so a reduced type is never a 'Let' and this
  -- would be a test that no state can pass. Table 2.8's @intro-let@ reads its
  -- type as written for the same reason, which is the bug this phase found in
  -- 'Thena.Engine' — the two now agree by construction.
  GoalTypeIsLet -> case written of
    Just (Let {}) -> True
    _             -> False
  -- **The tests that ask about an argument rather than about the focus**
  -- (MS4 phases 47 and 49). One per 'Thena.Surface.Concrete.Surface'
  -- constructor, so a clause of @elaborate@ names the node it is for and no
  -- two heads can match one term.
  SurfaceIsName o         -> surfaceIs o isName
  SurfaceIsUniverse o     -> surfaceIs o isUniverse
  SurfaceIsUniverseOpen o -> surfaceIs o isUniverseOpen
  SurfaceIsPlaceholder o  -> surfaceIs o isPlaceholder
  SurfaceIsHole o         -> surfaceIs o isHole
  SurfaceIsApp o          -> surfaceIs o isApp
  SurfaceIsLambda o       -> surfaceIs o isLambda
  SurfaceIsForall o       -> surfaceIs o isForall
  SurfaceIsArrow o        -> surfaceIs o isArrow
  SurfaceIsLet o          -> surfaceIs o isLet
  SurfaceIsAscription o   -> surfaceIs o isAscription
  SurfaceIsElim o         -> surfaceIs o isElim
  SurfaceIsDo o           -> surfaceIs o isDo
  AppArgsAreExplicit o    -> surfaceIs o argsExplicit
  AppHeadIsName o         -> surfaceIs o headIsName
  AppHeadIsElim o         -> surfaceIs o headIsElim
  LambdaBindsMore o       -> surfaceIs o bindsMore
  LambdaBindsOne o        -> surfaceIs o bindsOne
  LetIsAnnotated o        -> surfaceIs o isAnnotatedLet
  LetIsBare o             -> surfaceIs o isBareLet
  -- @instral@'s own data (MS5 phase 65). They read the operand and nothing
  -- else, so they are as cheap as 'holds' needs a head to be.
  ListIsEmpty o           -> valueIs o (\v -> case v of VList vs -> null vs; _ -> False)
  ListIsCons o            -> valueIs o (\v -> case v of VList vs -> not (null vs); _ -> False)
  OptionIsSome o          -> valueIs o (\v -> case v of VOption x -> x /= Nothing; _ -> False)
  OptionIsNone o          -> valueIs o (\v -> case v of VOption x -> x == Nothing; _ -> False)
  where
    -- Written down, then reduced: §8's "head matching runs whnf", because a
    -- goal typed @id Type₀ (Nat -> Nat)@ is a Π and must match.
    written = expectedType cur
    reduced = whnf env (context cur) <$> written

    -- **One shape for every surface test**: read the operand, ask the predicate
    -- of the focus. An operand that is not a surface term is a false question,
    -- not an error — §8's shallow heads, and the reason there are no parameter
    -- kinds (@ms4/CLOSEOUT.md@ 20).
    --
    -- An operand nobody bound does **not** exclude the rule — see this
    -- function's own note above.
    surfaceIs o p = case Op.operandIn args o of
      Left _             -> True
      Right (VSurface z) -> p (Zipper.focus z)
      Right _            -> False

    -- The same shape one layer up: an argument nobody supplied does not exclude
    -- the rule (MS4 phase 47's reading), and a value of the wrong kind answers
    -- False rather than failing — a head asks a question, it does not run.
    valueIs o p = case Op.operandIn args o of
      Left _  -> True
      Right v -> p v

    isName         s = case s of SurfaceName _ -> True; _ -> False
    isUniverse     s = case s of SurfaceUniverse _ -> True; _ -> False
    isUniverseOpen s = case s of SurfaceUniverseOpen -> True; _ -> False
    isPlaceholder  s = case s of SurfacePlaceholder -> True; _ -> False
    isHole         s = case s of SurfaceHole _ -> True; _ -> False
    isApp          s = case s of SurfaceApp _ _ -> True; _ -> False
    isLambda       s = case s of SurfaceLam _ _ -> True; _ -> False
    isForall       s = case s of SurfacePi _ _ -> True; _ -> False
    isArrow        s = case s of SurfaceArrow _ _ -> True; _ -> False
    isLet          s = case s of SurfaceLet {} -> True; _ -> False
    isAscription   s = case s of SurfaceAnnot _ _ -> True; _ -> False
    isElim         s = case s of SurfaceElim {} -> True; _ -> False
    isDo           s = case s of SurfaceDo _ -> True; _ -> False
    headIsName     s = case s of SurfaceApp (SurfaceName _) _ -> True; _ -> False
    headIsElim     s = case s of SurfaceApp (SurfaceElim {}) _ -> True; _ -> False
    argsExplicit   s = case s of
      SurfaceApp _ as -> all (\(SurfaceArg p _) -> p == Explicit) as
      _               -> False
    bindsMore      s = case s of SurfaceLam bs _ -> length bs > 1; _ -> False
    bindsOne       s = case s of SurfaceLam bs _ -> length bs == 1; _ -> False
    isAnnotatedLet s = case s of SurfaceLet _ (Just _) _ _ -> True; _ -> False
    isBareLet      s = case s of SurfaceLet _ Nothing _ _  -> True; _ -> False

-- --------------------------------------------------------------------------
-- Well-formedness (§2.4, §7.2)
-- --------------------------------------------------------------------------

-- | Why a rule is not well formed.
--
-- It lives here and not in "Thena.Errors" for that module's own stated reason:
-- @Thena.Errors@ imports nothing above @Core@, and every one of these names an
-- instruction.
data RuleError
  = DeclarationInBody GlobalName Int
    -- ^ @define-data@ named in a rule body — §3.7's line that a declaration is
    -- a command and not a rule-body operation. Carries the rule and the
    -- instruction's position in the body.
  | BoundNonProducing GlobalName Int Name
    -- ^ @x = attack@: a destination on an op that leaves nothing ('produces')
  | UnboundInRule     GlobalName Int Name
    -- ^ a @Ref@ to a name no parameter and no earlier @Bind@ introduced
    -- The three below are 'resolveRule'\'s, phase 21. They join this type
    -- rather than starting another because they are the same question asked
    -- one step earlier — /is this rule well formed?/ — and a rule file's
    -- loader wants one list, not two.
  | NoSuchTest        GlobalName String
    -- ^ a word after @when@ that names no 'Test'. No instruction index: a head
    -- is not a sequence
  | UnboundInHead     GlobalName Name
    -- ^ a head names something that is not one of the rule's parameters (MS4
    -- phase 47). A head runs before the body, so its environment is the call's
    -- arguments and nothing else — there is no earlier @Bind@ to have made a
    -- name, which is why this is not 'UnboundInRule'
  | BadTestOperands   GlobalName String
    -- ^ the right test word, written with the wrong arguments (MS4 phase 47).
    -- No instruction index, for 'NoSuchTest'\'s reason — a head is not a
    -- sequence
  | ReservedName      GlobalName Name
    -- ^ a parameter or a binding named @true@ or @false@ (MS5 phase 64) — the
    -- two words @instral@ reads as literals wherever an operand is read, so a
    -- variable of either name could never be read back.
  | BadOperands       GlobalName Int String
  | NoSuchTag         GlobalName Int String
    -- ^ @tag\`…\`@ where no parser answers to @tag@ (MS5 phase 61b). The two
    -- built-in ones are @surface@ and @core@; a declared object language brings
    -- its own, which is phase 69.
  | BadRegion         GlobalName Int String SyntaxError
    -- ^ a region whose contents did not parse in the language its tag named.
    -- ^ the right op word, written with the wrong arguments — too many, too
    -- few, or a position where a name was wanted. One error for all three: a
    -- rule body is one line, and the word is enough to find it
  | UnknownType String String
    -- ^ in the signature of ‹name›, ‹word› names no type (MS5 phase 67)
  | TypeArity String String Int Int
    -- ^ …and one that does, given the wrong number of arguments
  | TypeVariableApplied String String
    -- ^ @a b@ — a type variable applied to something. @instral@'s types are
    -- first order and there is nothing a variable could stand for that takes an
    -- argument
  | UnitInsideAType String
    -- ^ @()@ anywhere but as the result. It says /this leaves nothing/, which is
    -- not a type a value can have
  | DuplicateSignature String Int
    -- ^ two signatures for one callable
  | FunctionLeavesNothing String
  | RuleAndFunction String Int
    -- ^ one name is both a rule and a function at one arity (MS5, reviewed
    -- 2026-09-12)
  | BuiltInLanguage String
    -- ^ a grammar declared under a built-in tag's name. @surface@ and @core@ name
    -- Thena's own parsers; 'operandOf' looks a declared language up /first/, so
    -- without this a user grammar would silently replace the fence
  | BuiltInType String
    -- ^ …and the same trap one layer over (2026-09-12). A language's name is a
    -- /type/ as well as a tag, and 'resolveTyIn' looks a declared language up
    -- before the built-ins too, so @language String where { … }@ made @String@ in
    -- every signature mean the object language. The clash it produced said
    -- /wanted String, got String/, and @language List where { … }@ was worse: it
    -- loaded, and @signature f : List -> ()@ stopped being the arity error it is
  | DuplicateLanguage String
    -- ^ two grammars under one name (2026-09-12). The second was unreachable —
    -- every lookup is a 'lookup', which takes the first — so it loaded and did
    -- nothing, exactly what 'DuplicateSignature' exists to stop one layer over
  | BadGrammarItem String String
    -- ^ in the grammar of ‹language›, ‹word› is neither the language itself nor
    -- @name@ (MS5 phase 69)
  | BadGrammar String GrammarError
    -- ^ …and a grammar the generated parser could not run
    -- ^ @f x = say "hi"@ — the right of an @=@ ran something that produces no
    -- value, so there is nothing for the function to be (MS5 phase 68a)
  deriving (Eq, Show)

-- | The load-time pass (§2.4, §7.2). Three checks, one traversal, **every**
-- error rather than the first.
--
-- §9 asks for the first two. The third is the same walk: the environment a body
-- reads is built entirely by its parameters and its own earlier @Bind@s (§8 —
-- heads bind nothing, because there is no pattern language), so an unbound
-- @Ref@ is decidable here, and catching it at load time is the difference
-- between a rule that cannot be written and one that fails halfway through,
-- having already changed the development.
--
-- What it deliberately does not check: that the ops in a body /apply/ at the
-- states the head admits. That is not decidable shallowly, and §8 already
-- states the answer — a rule may match, run and fail.
validate :: Rule -> [RuleError]
validate r = reserved ++ headScope ++ go 0 (initiallyBound r) (ruleBody r)
  where
    nm = ruleName r

    -- **A name that is a literal cannot also be a variable** (MS5 phase 64).
    -- @true@ and @false@ are read as 'Thena.Ops.VBool' wherever an operand is
    -- read, so a parameter or a binding of either name could never be read
    -- back — every @Ref@ to it has already become a literal. Refusing it here
    -- is the difference between a rule that cannot be written and one that
    -- quietly does something else than it says.
    reserved =
      [ ReservedName nm n
      | n <- ruleParams r ++ [ n | Bind n _ <- ruleBody r ]
      , n `elem` reservedNames
      ]

    -- **A head may name only the rule's own parameters** (MS4 phase 47). It
    -- runs before the body, so the environment it reads is the call's
    -- arguments bound to those parameters and nothing else — there is no
    -- earlier @Bind@ for a name to have come from. Catching it here is what
    -- lets 'holds' read an unbound name as /a question about an argument
    -- nobody supplied/ rather than as a mistake it has to guess about.
    headScope =
      [ UnboundInHead nm n
      | t <- ruleHead r
      , n <- concatMap refsIn (testOperands t)
      , n `notElem` ruleParams r
      ]

    go _ _ [] = []
    go i bound (instr : rest) =
      let o     = operationOf instr
          errs  = declaration i o ++ binding i instr o ++ scope i bound o
                    ++ insideLambda i bound o
          bound' = case instr of
            Bind n _ -> n : bound
            Do _     -> bound
       in errs ++ go (i + 1) bound' rest

    -- **A lambda's body is a body and is scoped like one** (found in the long
    -- hunt, 2026-09-13). @operandsOf@ answers with the operands an op /reads/,
    -- and a lambda's body is not one of them — it is a program — so until this
    -- was written @g = \ z -> concat z nosuchname@ loaded clean and failed at
    -- run time, where every other shape of unbound name is a load error. Phase
    -- 68b added lambdas and this walk was not told.
    --
    -- **The lambda's own instruction number is what is reported.** An index
    -- inside the body would collide with the enclosing one, and the lambda is
    -- what the reader sees at that line — the same choice a nested call makes,
    -- which is lifted into the instruction that wanted it.
    insideLambda i bound o = case o of
      Op.Lambda ps body -> inner i (ps ++ bound) body
      _                 -> []

    inner _ _ [] = []
    inner i bound (instr : rest) =
      let o = operationOf instr
       in scope i bound o
            ++ insideLambda i bound o
            ++ inner i (case instr of { Bind n _ -> n : bound; Do _ -> bound }) rest

    operationOf instr = case instr of
      Bind _ o -> o
      Do     o -> o

    declaration i o = case o of
      DefineData _ -> [DeclarationInBody nm i]
      _            -> []

    binding i instr o = case instr of
      Bind n _ | not (produces o) -> [BoundNonProducing nm i n]
      _                           -> []

    scope i bound o =
      [ UnboundInRule nm i n
      | n <- concatMap refsIn (operandsOf o)
      , n `notElem` bound
      ]

-- | A written signature, resolved (MS5 phase 67).
--
-- **The arity comes out of the type**: an arrow chain with three links before
-- the result is a signature at arity three, so nothing is written twice and a
-- signature cannot claim an arity its own type contradicts.
resolveSignature :: [(String, Language)] -> RawSignature -> Either RuleError (String, Signature)
resolveSignature ls (RawSignature nm t) = do
  -- **The variable list is threaded ACROSS the links** (found by mutation
  -- testing, 2026-09-12). Resolving each link on its own numbered every
  -- lowercase name from zero within that link, so @a -> b -> ()@ became
  -- @a -> a -> ()@ and every signature's variables collapsed onto each other.
  ts <- chainOf (chain t) []
  -- **The last link is the result, and @()@ means there is none.** That is the
  -- same distinction 'Thena.Ops.resultOf' draws, said in the surface a rule
  -- author writes — and it is why @()@ anywhere else is refused rather than
  -- quietly dropping a parameter.
  case sequence (init ts) of
    Nothing -> Left (UnitInsideAType nm)
    Just ps -> Right (nm, Signature ps (last ts))
  where
    chain (RawTyArrow a b) = a : chain b
    chain u                = [u]

    chainOf [] _ = Right []
    chainOf (u : us) vs = do
      (m, vs') <- resolveTyIn ls nm vs u
      rest     <- chainOf us vs'
      Right (m : rest)

-- | One written type.
--
-- **A capitalised name is a constructor and a lowercase one is a variable.**
-- Nothing else distinguishes them, and nothing else needs to: it is why a
-- signature needs no @forall@ — its variables are exactly its lowercase names.
--
-- A variable is numbered by where it first appears, so
-- @signature f : a -> b -> a@ resolves to 'Thena.Instral.Type.TVar' 0, 1, 0.
-- The numbering is scheme-local, which is what 'Thena.Instral.Infer'
-- instantiates.
resolveTy :: [(String, Language)] -> String -> RawTy -> Either RuleError (Maybe Ty)
resolveTy ls owner t0 = fmap fst (resolveTyIn ls owner [] t0)

-- | 'resolveTy', threading the scheme's variable names in and out — which is
-- what lets one signature's links share a numbering.
resolveTyIn
  :: [(String, Language)] -> String -> [String] -> RawTy
  -> Either RuleError (Maybe Ty, [String])
resolveTyIn ls owner vs0 t0 = go vs0 t0
  where
    go vs t = case t of
      RawTyUnit -> Right (Nothing, vs)
      -- **A group is its content** — the parentheses did their work in
      -- 'resolveSignature'\'s @chain@ and in the @chainOf@ below, both of which
      -- stop at one (2026-09-12).
      RawTyGroup u -> go vs u
      -- **A parenthesised arrow is a function value** (MS5 phase 68b). Only a
      -- parenthesised one reaches here: 'resolveSignature' splits the top-level
      -- chain into parameters and a result first, so @a -> b@ at the top means
      -- /takes an a, gives a b/ and @(a -> b)@ means /a function/.
      -- **The links are threaded, like every other case here.** Mapping over
      -- them with one starting list numbered each link's variables from zero, so
      -- a nested @(a -> b)@ became @(a -> a)@ — the same collapse the top-level
      -- chain had (both found by mutation testing, 2026-09-12).
      RawTyArrow _ _ -> do
        (ms, vs') <- links vs (chainOf t)
        case sequence ms of
          Nothing -> Left (UnitInsideAType owner)
          Just xs -> Right (Just (TFun (init xs) (last xs)), vs')
      RawTyPair a b -> do
        (ma, vs1) <- go vs a
        (mb, vs2) <- go vs1 b
        case (ma, mb) of
          (Just x, Just y) -> Right (Just (TPair x y), vs2)
          _                -> Left (UnitInsideAType owner)
      RawTyVar v -> Right (Just (TVar (indexOf v vs)), extend v vs)
      RawTyCon nm as
        | not (null as) || isVarName nm ->
            if isVarName nm
              then if null as
                     then Right (Just (TVar (indexOf nm vs)), extend nm vs)
                     else Left (TypeVariableApplied owner nm)
              else applied nm as vs
        | otherwise -> applied nm [] vs

    applied nm as vs = do
      (ms, vs') <- args vs as
      case traverse id ms of
        Nothing -> Left (UnitInsideAType owner)
        Just xs -> fmap (\x -> (Just x, vs')) (constructor nm xs)

    args vs [] = Right ([], vs)
    args vs (a : rest) = do
      (m, vs1)  <- go vs a
      (ms, vs2) <- args vs1 rest
      Right (m : ms, vs2)

    -- **A declared object language is a type** (MS5 phase 69, §6.6, his): the
    -- environment grows with what the user declares, which he ruled is *"exactly
    -- what instral is for"*.
    constructor nm [] | Just _ <- lookup nm ls = Right (TObject nm)
    constructor nm xs = case (nm, xs) of
      ("String", [])      -> Right TString
      ("Name", [])        -> Right TName
      ("Int", [])         -> Right TInt
      ("Char", [])        -> Right TChar
      ("Bool", [])        -> Right TBool
      ("Surface", [])     -> Right TSurface
      ("Core", [])        -> Right TCore
      ("Development", []) -> Right TDevelopment
      ("List", [a])       -> Right (TList a)
      ("Option", [a])     -> Right (TOption a)
      _ | nm `elem` known -> Left (TypeArity owner nm (arityOf nm) (length xs))
        | otherwise       -> Left (UnknownType owner nm)

    known = builtInTypes
    arityOf nm = if nm `elem` ["List", "Option"] then 1 else 0

    -- A nested arrow's own variables share the scheme's numbering, so the list
    -- goes in and comes back out at every link.
    links vs [] = Right ([], vs)
    links vs (u : us) = do
      (m, vs1)   <- go vs u
      (ms, vs2)  <- links vs1 us
      Right (m : ms, vs2)

    chainOf (RawTyArrow a b) = a : chainOf b
    chainOf u                = [u]

    isVarName (c : _) = c `elem` ['a' .. 'z']
    isVarName []      = False

    indexOf v vs = case lookup v (zip vs [0 ..]) of
      Just i  -> i
      Nothing -> length vs
    extend v vs = if v `elem` vs then vs else vs ++ [v]

-- | The words @instral@ reads as literals rather than as names (MS5 phase 64).
--
-- **Two, and they are not lexer keywords** — his ruling, 2026-09-12. One lexer
-- serves every language, so reserving them there would take two constructor
-- names away from every object language;
-- @examples\/determinacy-tactics.thena.script@ uses both.
reservedNames :: [Name]
reservedNames = ["true", "false"]

-- | The names a body may read before it binds anything of its own: **its
-- parameters, and nothing else** (MS4 phase 41).
--
-- It used to add @hint@ when a rule's head asked about one, which was the only
-- name a body could read that no @Bind@ introduced. Nothing is magic now.
initiallyBound :: Rule -> [Name]
initiallyBound = ruleParams

-- | Every rule in one base, checked.
--
-- **This is what a load runs**, since phase 22 — @Thena.Driver.readRuleBase@
-- calls it on every rule as it resolves one, so a base that would not validate
-- is refused rather than installed. §2.4 asked for a load-time pass and until
-- there was a load there was only a test.
validateBase :: RuleBase -> [RuleError]
validateBase = concatMap validate . baseRules

-- --------------------------------------------------------------------------
-- Written rules (§8, phase 21)
-- --------------------------------------------------------------------------

-- | A parsed rule, resolved against the base into the very value a Haskell
-- literal would give.
--
-- **This is the second spelling of an existing type, not a new type**, and that
-- is the phase\'s load-bearing check: "Thena.RuleSyntaxTests" writes each of
-- the shipped base's rules out by hand and asserts that reading
-- @rules/standard.thena.rules@ back gives the same 'Rule's. A fixture, not a
-- round trip against itself.
--
-- It needs the base for one reason — @call ‹name›@. Everything else is a
-- closed vocabulary.
--
-- **Every error, not the first**, for 'validate'\'s reason: instructions
-- resolve independently, so a body with three mistakes reports three.
resolveRule :: [(String, Language)] -> RawRule -> Either [RuleError] Rule
resolveRule ls (RawRule nm ps ts body) =
  case (headErrs, bodyErrs) of
    ([], []) -> Right (Rule g ps tests (concat instrs))
    _        -> Left (headErrs ++ bodyErrs)
  where
    g = GlobalName nm

    (headErrs, tests) = partitionEithers (map test ts)
    test (RawTest w os) = case traverse headOperand os of
      Nothing  -> Left (BadTestOperands g w)
      Just os' -> case testOf w os' of
        Right t                   -> Right t
        Left NoSuchTestWord       -> Left (NoSuchTest g w)
        Left (WrongTestArity _ _) -> Left (BadTestOperands g w)

    (bodyErrs, instrs) =
      partitionEithers (zipWith (instruction ls g) [0 ..] body)

-- | What may be written as an operand of a test (MS4 phase 47).
--
-- **Every leaf a body accepts** (widened at MS5 phase 64, when the primitives
-- arrived): a literal is pure data, and reading one costs 'holds' nothing. What
-- stays refused is the two that would make dispatch /do/ something — a region,
-- which would parse an embedded language, and a nested call, which would run
-- one. That is the whole of the restriction, and it is his §1.1 line about
-- heads staying a restricted fragment rather than a shorter list of shapes.
--
-- 'RawPos' was refused until then because a numeral was only ever @arg 2@'s
-- field position. It is an 'Thena.Ops.VInt' now.
headOperand :: RawOperand -> Maybe Operand
headOperand o = case o of
  -- **A head takes no lambda.** It is a restricted fragment on purpose (§1.1,
  -- his) — 'holds' must answer without running anything.
  RawLambda _ _ -> Nothing
  RawRef "true"  -> Just (Lit (VBool True))
  RawRef "false" -> Just (Lit (VBool False))
  RawRef n  -> Just (Ref n)
  RawText t -> Just (Lit (VText t))
  RawChar c -> Just (Lit (VChar c))
  RawPos k  -> Just (Lit (VInt k))
  -- A list and a pair are built from operands and nothing is run to build one,
  -- so a head may carry them — under the same rule as every other literal (MS5
  -- phase 65). Their elements are checked the same way, which is what keeps a
  -- region and a nested call out of them too.
  RawList os   -> ListOf <$> traverse headOperand os
  RawPairOf a b -> PairOf <$> headOperand a <*> headOperand b
  -- **A tagged region may not appear in a head** (MS5 phase 61b). A head is
  -- evaluated by 'holds' to build the match list, cheaply and without effects;
  -- a region would make dispatch parse an embedded language to find out what
  -- applies. His ruling, 2026-09-11: heads stay a restricted fragment, and
  -- pattern matching is the only thing they are to gain.
  RawRegion _ _ -> Nothing
  RawQuoted _   -> Nothing
  -- **A head may not run code** (§1.1): 'holds' builds the match list without
  -- effects, and a nested call is a call (MS5 phase 63).
  RawNested _ _ -> Nothing

-- | A written grammar, resolved into the language it declares (MS5 phase 69).
--
-- **Two words are special inside a production and nothing else is**: the
-- language's own name is a recursive slot, and @name@ is a bare identifier.
-- The parser could not tell — it does not know what the language is called —
-- which is the same division of labour an op word gets.
resolveLanguage :: RawLanguage -> Either [RuleError] (String, Language)
resolveLanguage (RawLanguage nm _) | nm `elem` builtInTags  = Left [BuiltInLanguage nm]
resolveLanguage (RawLanguage nm _) | nm `elem` builtInTypes = Left [BuiltInType nm]
resolveLanguage (RawLanguage nm ps) = case partitionEithers (map production ps) of
  (e : es, _) -> Left (e : es)
  ([], ps')   -> case language nm ps' of
    Left gs  -> Left (map (BadGrammar nm) gs)
    Right l  -> Right (nm, l)
  where
    production (RawProduction c is) = Production c <$> traverse item is
    item i = case i of
      GTerminal t -> Right (Terminal t)
      GWord w
        | w == nm     -> Right Recurse
        | w == "name" -> Right NameSlot
        | otherwise   -> Left (BadGrammarItem nm w)

-- | The tags that name Thena's own parsers (MS5, reviewed 2026-09-12).
--
-- **A declared language may not take one.** 'operandOf' resolves a declared tag
-- before the built-ins, so @language surface where { … }@ replaced the @⟨ … ⟩@
-- fence's sibling spelling without a word of complaint. The notation being
-- identical for a built-in and a generated parser (§6.0.1) is what makes this a
-- trap rather than a curiosity.
builtInTags :: [String]
builtInTags = ["surface", "core"]

-- | The type constructors @instral@ ships with, and **the one list of them**.
--
-- 'resolveTyIn' reads it to tell an unknown name from one given the wrong number
-- of arguments, and 'resolveLanguage' reads it to refuse a grammar that would
-- take one of these names — the same trap 'builtInTags' catches for the tag,
-- found the same way and on the same day. Written once because two copies of a
-- list like this drift, which is what 'BuiltInType' says.
builtInTypes :: [String]
builtInTypes =
  [ "String", "Name", "Int", "Char", "Bool", "Surface", "Core", "Development"
  , "List", "Option"
  ]

-- | A written function, resolved into the rule it is (MS5 phase 68a).
--
-- **A function IS a rule — his §1.1** — /a rule with one clause and no head/ —
-- and this is where that stops being a description and becomes the
-- implementation: @f x = e@ becomes a headless 'Rule' whose body evaluates @e@
-- and returns it. The engine gains nothing, @Call@ reaches it unchanged, and
-- 'validate' and 'Thena.Instral.Infer' see an ordinary rule.
--
-- **The result is bound to a name no author can write** — @(=)@ contains a
-- token character, so nothing lexes to it — for 'hoisted'\'s reason: the
-- generated name must not collide with a parameter.
--
-- **A function must produce.** @f x = say "hi"@ is refused here rather than by
-- 'validate', which would report it against a binding the author never wrote.
resolveFunction :: [(String, Language)] -> RawFunction -> Either [RuleError] Rule
resolveFunction ls (RawFunction nm ps rhs) = do
  is <- resolveBlock ls g [RawBind resultName rhs]
  case [ () | Bind n o <- is, n == resultName, not (produces o) ] of
    _ : _ -> Left [FunctionLeavesNothing nm]
    []    -> Right (Rule g ps [] (is ++ [Do (Return (Ref resultName))]))
  where
    g          = GlobalName nm
    resultName = lambdaResult

-- | Resolve a written block of instructions (MS4 phase 45).
--
-- **The same resolution a rule body gets**, and deliberately the same function
-- underneath: a @do@ block is the instruction language, so a word that names an
-- op is an op and a word that does not is a rule call, exactly as it is in a
-- rule (phase 25e). Nothing about a block is a second dialect.
--
-- The name is the one errors are reported against. A block has none of its own,
-- so its caller supplies where it came from.
resolveBlock :: [(String, Language)] -> GlobalName -> [RawInstr] -> Either [RuleError] [Instr]
resolveBlock ls g body = case partitionEithers (zipWith (instruction ls g) [0 ..] body) of
  ([], instrs) -> Right (concat instrs)
  (errs, _)    -> Left errs

-- | One written instruction. @‹name› = ‹op›@ is a 'Bind', a bare op is a 'Do' —
-- §7.2\'s two cases, and the grammar has no third.
--
-- **It yields a list, as of MS5 phase 63**, because an operand may be a call:
-- @some-rule (f a) b@ is two instructions, the nested call bound in front of the
-- one that wanted its value. The written index is kept for errors — it is the
-- line the author can see — so the instruction numbers in a message still count
-- what was written and not what it expanded to.
instruction :: [(String, Language)] -> GlobalName -> Int -> RawInstr -> Either RuleError [Instr]
instruction ls g i ri = case ri of
  -- **@x = true@ is the literal, not a call to a rule called @true@** (MS5
  -- phase 73). @true@ and @false@ are read as values wherever an /operand/ is
  -- read (phase 64), and the right of an @=@ is the one place a bare word goes
  -- to 'operation' instead — so without this, @f false@ works and @b = false@
  -- says /no rule is called false/.
  RawBind n (RhsOp (RawOp w [])) | w `elem` reservedNames ->
    pure . Bind n . Op.Value <$> operandOf ls g i "=" (RawRef w)
  RawBind n (RhsOp o)    -> lift (Bind n) o
  -- **A value on the right of an @=@** (MS5 phase 68a) — @x = [1, 2]@. Its
  -- nested calls are lifted exactly as an op's arguments are, and the value
  -- itself becomes a 'Thena.Ops.Value', which is the op with no written form.
  -- **A lambda binds directly**, without going through 'Op.Value': it is
  -- already an op, and wrapping it would build the closure and then copy it.
  RawBind n (RhsValue (RawLambda ps b)) -> pure . Bind n <$> closure ls g i ps b
  RawBind n (RhsValue o) ->
    let (binds, o') = hoistedOne i o
     in (++) <$> traverse (hoistedBind ls g i) binds
              <*> (pure . Bind n . Op.Value <$> operandOf ls g i "=" o')
  RawDo     o            -> lift Do       o
  where
    lift f (RawOp w as) =
      let (binds, as') = hoisted i as
       in (++) <$> traverse (hoistedBind ls g i) binds
                <*> (pure . f <$> operation ls g i (RawOp w as'))

-- | One binding 'hoisted' lifted out — a nested call or a lambda.
hoistedBind :: [(String, Language)] -> GlobalName -> Int -> (Name, RawRhs) -> Either RuleError Instr
hoistedBind ls g i (n, r) = case r of
  RhsOp o                     -> Bind n <$> operation ls g i o
  RhsValue (RawLambda ps b)   -> Bind n <$> closure ls g i ps b
  RhsValue o                  -> Bind n . Op.Value <$> operandOf ls g i "=" o

-- | A lambda, compiled the way a function is: a body that ends in @return@.
--
-- **The same compilation as 'resolveFunction'**, deliberately — §1.1 says a
-- function is a rule with one clause and no head, and a lambda is that function
-- without a name, so there is one way to build a body and not two.
closure :: [(String, Language)] -> GlobalName -> Int -> [Name] -> RawRhs -> Either RuleError Op
closure ls g i ps b = case resolveBlock ls g [RawBind lambdaResult b] of
  Left (e : _) -> Left e
  Left []      -> Left (BadOperands g i "λ")
  Right is
    | any (\x -> case x of { Bind n o -> n == lambdaResult && not (produces o)
                            ; _ -> False }) is -> Left (FunctionLeavesNothing "λ")
    | otherwise -> Right (Op.Lambda ps (is ++ [Do (Return (Ref lambdaResult))]))

-- | Where a lambda's and a function's result is parked. It contains a token
-- character, so nothing an author writes can collide with it.
lambdaResult :: Name
lambdaResult = "(=)"

-- | Lift every nested call out of an operand run, innermost first.
--
-- @some-rule (f (g a)) b@ becomes @(0:1) = g a ; (0:0) = f (0:1) ; some-rule
-- (0:0) b@ — a fixed evaluation order, left to right and innermost first, which
-- is the order the arguments are written in and the only one a reader would
-- guess. It matters because a call changes the development: these are
-- statements, not expressions over a pure value.
--
-- **The names cannot collide with anything written.** A parenthesis is a token,
-- so no identifier can contain one; the pair of numbers is the written
-- instruction's index and a counter within it, which keeps them apart across a
-- body.
hoisted :: Int -> [RawOperand] -> ([(Name, RawRhs)], [RawOperand])
hoisted i as = let (_, bs, os) = go 0 as in (bs, os)
  where
    go k []       = (k, [], [])
    go k (o : os) =
      let (k1, bs1, o') = one k o
          (k2, bs2, os') = go k1 os
       in (k2, bs1 ++ bs2, o' : os')

    -- **A literal is walked into** (MS5 phase 65): @f [g a, b]@ must lift the
    -- @g a@ exactly as @f (g a)@ does, or a call inside a list would reach
    -- 'ref' — which refuses it — and the list would be unwritable with anything
    -- computed in it.
    one k o = case o of
      RawNested w inner ->
        let (k1, bs1, inner') = go (k + 1) inner
            n                 = "(" ++ show i ++ ":" ++ show (k :: Int) ++ ")"
         in (k1, bs1 ++ [(n, RhsOp (RawOp w inner'))], RawRef n)
      -- **A lambda is lifted like a nested call** (MS5 phase 68b), and for a
      -- sharper reason: a closure captures the environment it is made in, so it
      -- is built by an instruction and cannot be a literal. **Nothing is
      -- hoisted out of its body** — that is a scope of its own.
      RawLambda ps b ->
        let n = "(" ++ show i ++ ":" ++ show (k :: Int) ++ ")"
         in (k + 1, [(n, RhsValue (RawLambda ps b))], RawRef n)
      RawList os ->
        let (k1, bs, os') = go k os in (k1, bs, RawList os')
      RawPairOf a b ->
        let (k1, bs1, a') = one k a
            (k2, bs2, b') = one k1 b
         in (k2, bs1 ++ bs2, RawPairOf a' b')
      _ -> (k, [], o)

-- | 'hoisted' for a single operand — what stands right of an @=@ (MS5 phase
-- 68a).
hoistedOne :: Int -> RawOperand -> ([(Name, RawRhs)], RawOperand)
hoistedOne i a = case hoisted i [a] of
  (bs, [o]) -> (bs, o)
  (bs, _)   -> (bs, a)

-- | One written operand, resolved (extracted to the top level at MS5 phase 68a
-- so that the right of an @=@ can use it).
--
-- The three arguments before the operand are only for errors: which rule, which
-- instruction, and the word that wanted it.
operandOf :: [(String, Language)] -> GlobalName -> Int -> String -> RawOperand -> Either RuleError Operand
operandOf ls g i w o = case o of
  -- **Cannot arise**, for 'RawNested'\'s reason: 'hoisted' lifts every lambda
  -- into a binding of its own before this runs (MS5 phase 68b).
  RawLambda _ _ -> Left (BadOperands g i w)
  -- **Cannot arise**: 'hoisted' lifts every nested call into a binding of
  -- its own before this runs, so what reaches here is always a leaf (MS5
  -- phase 63). Written out rather than left to a pattern-match failure.
  RawNested _ _ -> Left (BadOperands g i w)
  -- **@true@ and @false@ are read here and not in the lexer** — his ruling,
  -- 2026-09-12 (MS5 phase 64). One lexer serves every language, and an
  -- object language may well call a constructor @true@; this table is
  -- @instral@'s alone, so reserving them here takes nothing from Surface or
  -- Core. 'validate' refuses a parameter or a binding of either name, so a
  -- rule that meant to use one as a variable is told rather than silently
  -- given a literal.
  RawRef "true"  -> Right (Lit (VBool True))
  RawRef "false" -> Right (Lit (VBool False))
  RawRef n  -> Right (Ref n)
  RawText t -> Right (Lit (VText t))
  RawChar c -> Right (Lit (VChar c))
  -- **A numeral is a value here** (MS5 phase 64), where it is a field
  -- position under a word from 'partWords' — those are read above, before
  -- this. It was 'BadOperands' until this phase, which is one more
  -- load-time check traded for a run-time one: an op given an @Int@ where
  -- it wanted a term fails with 'Thena.Errors.ExpectedTerm', and saying so
  -- earlier is the type system's job (@ms2\/CLOSEOUT.md@ 4b, phase 66).
  RawPos k  -> Right (Lit (VInt k))
  RawList os    -> ListOf <$> traverse (operandOf ls g i w) os
  RawPairOf a b -> PairOf <$> operandOf ls g i w a <*> operandOf ls g i w b
  -- **A tagged region is parsed here, at load** (MS5 phase 61b, §6.0.1), so
  -- that a syntax error in an embedded term arrives with every other syntax
  -- error rather than when a rule happens to run.
  --
  -- The two built-in tags differ in how far they get, and the difference is
  -- the languages' rather than ours: a surface term is unresolved by nature,
  -- so it is finished here; a core term needs the globals and the focus's
  -- context, which do not exist while a rule base is being read.
  -- Corners are the other spelling of a @core@ region, and land in the
  -- same place: unresolved, because a rule base is read before there is
  -- anything to resolve against.
  RawQuoted r -> Right (Lit (VRaw r))
  RawRegion tag src | Just l <- lookup tag ls ->
    -- **A declared object language's parser is generated** (MS5 phase 69,
    -- §6.0.1) and the notation is the built-in tags' — the asymmetry lives here,
    -- in the implementation, and no rule of the language mentions it.
    case parseObject l src of
      Left e  -> Left (BadRegion g i tag e)
      Right t -> Right (Lit (VObject tag (rootedAt t)))
  RawRegion tag src -> case tag of
    "surface" -> case parseSurfaceText src of
      Left e  -> Left (BadRegion g i tag e)
      Right t -> Right (Lit (VSurface (rootedAt t)))
    "core" -> case lexTokens src of
      Left e   -> Left (BadRegion g i tag (LexFailed e))
      Right ts -> case parseTerm ts of
        Left e  -> Left (BadRegion g i tag (ParseFailed e))
        Right r -> Right (Lit (VRaw r))
    _ -> Left (NoSuchTag g i tag)

-- | An op word and its written arguments, resolved.
--
-- The whole word vocabulary is 'Thena.Ops.opKeyword'\'s, read backwards, and
-- the arities are here because that is where they are known. A word this does
-- A word this does not accept is a **rule call** (phase 25e); an accepted word
-- given the wrong arguments is 'BadOperands'. Those are separate mistakes, and
-- only the second is a load-time error now.
-- | The op words, by how many operands they take (MS5 phase 72).
--
-- **Hoisted out of 'operation'\'s @where@** so that a test can walk them: they
-- are the parser's half of the word vocabulary, 'Thena.Ops.opKeyword' is the
-- printer's, and until this phase the only thing crossing the two was
-- @RuleSyntaxTests@' hand-written @everyOp@ — which phase 68a found had no
-- @goto@ row at all, so splitting that word into two would have passed the suite
-- in silence (@ms5\/CLOSEOUT.md@ 5).
--
-- 'opWords' below is what makes the check total over these tables rather than
-- over a list someone has to remember to grow.

nullaryOps :: [(String, Op)]
nullaryOps =
  [ ("along", Along), ("into", Into), ("back", Back), ("reduce", Reduce)
  , ("prim-attack", Attack), ("prim-regret", Regret)
  , ("prim-solve", Solve), ("prim-abandon", Abandon), ("goal", Goal)
  , ("fresh-universe", Op.FreshUniverse)
  , ("here", Here)
  , ("none", Op.None)
  , ("prim-prove", Prove)
  , ("pop-development", Op.PopDevelopment)
  ]
unaryOps :: [(String, Operand -> Op)]
unaryOps =
  [ ("say", Say), ("yield", Op.Yield), ("prim-try", Try)
  , ("return", Op.Return)
  , ("some", Op.Some)
  , ("list-head", Op.ListHead), ("list-tail", Op.ListTail)
  , ("pair-first", Op.PairFirst), ("pair-second", Op.PairSecond)
  , ("option-value", Op.OptionValue)
  , ("goto", Goto), ("goto-named", Op.GotoNamed)
  , ("name-text", Op.NameText)
  , ("surface-of", Op.SurfaceOf)
  , ("push-development", Op.PushDevelopment)
  , ("certify", Certify), ("prim-eliminate", Op.Eliminate)
  , ("typeof", Typing), ("expose", Op.Expose), ("resolve-core", Op.ResolveCore), ("fresh-name", FreshName), ("prim-apply", Op.Apply)
  , ("resolve-name", Op.ResolveName)
  , ("surface-name", Op.SurfaceNameOf)
  , ("surface-universe", Op.SurfaceUniverseOf)
  , ("arrow-domain", Op.ArrowDomain), ("arrow-codomain", Op.ArrowCodomain)
  , ("ascription-type", Op.AscriptionType)
  , ("ascription-term", Op.AscriptionTerm)
  , ("app-function", Op.AppFunction)
  , ("app-last-argument", Op.AppLastArgument)
  , ("app-head", Op.AppHead)
  , ("app-first-argument", Op.AppFirstArgument)
  , ("app-tail", Op.AppTail)
  , ("expand-implicits", Op.ExpandImplicits)
  , ("lambda-name", Op.LambdaName), ("lambda-tail", Op.LambdaTail)
  , ("lambda-body", Op.LambdaBody)
  , ("let-name", Op.LetName), ("let-type", Op.LetType)
  , ("let-value", Op.LetValue), ("let-body", Op.LetBody)
  , ("forall-name", Op.ForallName), ("forall-domain", Op.ForallDomain)
  , ("forall-tail", Op.ForallTail), ("play", Op.Play)
  , ("elim-spine", Op.ElimSpine)
  ]
binaryOps :: [(String, Operand -> Operand -> Op)]
binaryOps =
  [ ("assume", Assume), ("claim", Claim), ("define", Define)
  , ("quantify", Op.Quantify)
  , ("concat", Concat), ("unify", Unify), ("unify-into", Op.UnifyInto)
  , ("arrow", Arrow), ("apply-to", ApplyTo), ("apply-next", Op.ApplyNext)
  ]

-- | Every op word paired with an op that bears it, built from the three tables
-- above — so nothing has to be listed a second time.
--
-- The operands are a placeholder: what is being crossed is the /word/, and
-- 'Thena.Ops.opKeyword' does not read an op's operands.
opWords :: [(String, Op)]
opWords =
  nullaryOps
    ++ [ (w, f sample) | (w, f) <- unaryOps ]
    ++ [ (w, f sample sample) | (w, f) <- binaryOps ]
  where
    sample = Lit (VText "x")

operation :: [(String, Language)] -> GlobalName -> Int -> RawOp -> Either RuleError Op
operation ls g i (RawOp w as)
  -- The field words come first: @arg@ is one of them and also the only word
  -- that reads a position, so a general arity table could not describe it.
  | w `elem` partWords = case as of
      []          -> part Nothing
      [RawPos k]  -> part (Just k)
      _           -> bad
  | otherwise = case (w, as) of
      ("cross",  [RawRef "type"]) -> Right CrossType
      ("cross",  [RawRef "val"])  -> Right CrossValue
      ("cross",  _)               -> bad

      -- @call ‹name› ‹args›@. **The name is recorded and nothing is looked
      -- up** (phase 23): the base is searched when the call runs, which is what
      -- lets a rule call itself and call a rule defined after it, or in a base
      -- loaded after it. 'Thena.Rules.clauses' is the search.
      -- **@prim-intro@ takes an optional name** (MS4 phase 41b): bare, the
      -- binder keeps the one written in the type; with an argument, the
      -- caller's. Spelled here rather than in the arity tables because it is
      -- the one op that appears in two of them.
      ("prim-lambda", [])         -> Right (IntroPi Nothing)
      ("prim-lambda", [a])        -> IntroPi . Just <$> ref a
      ("prim-let", [])            -> Right (IntroLet Nothing)
      ("prim-let", [a])           -> IntroLet . Just <$> ref a
      ("prim-intro", _)           -> bad
      ("call", RawRef r : rest)   -> Call (GlobalName r) <$> traverse ref rest
      ("call", _)                 -> bad


      ("ask", [a, RawRef k])      -> case answerKind k of
        Just ak -> flip Ask ak <$> ref a
        Nothing -> bad
      ("ask", _)                  -> bad

      -- §3.7: a declaration is a command, not a rule-body operation. The word
      -- exists ('Thena.Ops.opKeyword' is total) and resolving it is refused
      -- here, one step before 'validate' would have.
      ("data", _)                 -> Left (DeclarationInBody g i)

      _ -> case (lookup w nullaryOps, lookup w unaryOps, lookup w binaryOps, as) of
        (Just o,  _, _, [])       -> Right o
        (_, Just f,  _, [a])      -> f <$> ref a
        (_, _, Just f,  [a, b])   -> f <$> ref a <*> ref b
        -- **A word that names no op is a call to a rule of that name**
        -- (phase 25e), which is what a bare word has meant at the REPL since
        -- phase 23b. The user, 2026-08-26: *"Bare word was always, always, the
        -- intended design."*
        --
        -- **An op word at an arity the op does not have is a CALL** (MS5
        -- phase 62b, the user's decision): @claim ty@ is not a mistake about
        -- @claim@ — it is a call to the one-argument rule of that name, which
        -- asks for a name and then runs the two-argument op. His words:
        -- /"the normal claim is operation (primitive and built in), the unary
        -- claim is a rule"/.
        --
        -- So a word names an **op at the arities the op has, and a rule at
        -- every other arity**, which is the reading 'clauses' already uses —
        -- it filters by name /and/ arity, so several clauses of one name may
        -- take different numbers of arguments. Ops and rules now agree about
        -- that instead of differing.
        --
        -- **It reverses this module's earlier choice**, which refused the
        -- arity mismatch as 'BadOperands' so that @claim x@ was caught when
        -- the base loaded. The cost is the one below, one word wider:
        --
        -- The cost: a mistyped word is no longer refused at load time; it is
        -- a call that finds no clause when it runs. @NoSuchOp@ went with this
        -- change, being an error that can no longer happen. **That is the
        -- trade phase 23 already took for explicit @call@** (§8: a rule may
        -- call itself, a rule below it, or one in a base loaded later, so no
        -- name can be resolved at load time), and it is what the rule
        -- language's type system is for (closeout 4b).
        _                         -> Call (GlobalName w) <$> traverse ref as
  where
    bad     = Left (BadOperands g i w)
    part k  = maybe bad (Right . Down) (partOf w k)
    -- Spelled out rather than sharing 'bad': a @where@ binding under a guard
    -- does not generalise, and 'bad' is already fixed at 'Op' by its other
    -- uses. The same trap phase 3 met with its @respond@.
    -- **A text literal is accepted wherever an operand is**, not only where an
    -- op wants text. §7.2 already settled that shape: an op given the wrong
    -- kind of value fails at run time with 'Thena.Errors.ExpectedTerm', and
    -- "when the instruction language gets a type system that check moves
    -- there". A grammar that policed it here would be that type system, badly.
    ref     = operandOf ls g i w


-- | What @ask@'s second word may be — 'AnswerKind', spelled.
--
-- @rule-name@ and not @rule@, because @rule@ is a keyword as of this phase and
-- could not be written here. It is the better word anyway: it pairs with
-- @name@, and the two really are "a name in scope" and "the name of a rule".
answerKind :: String -> Maybe AnswerKind
answerKind k = case k of
  "text"      -> Just AText
  "name"      -> Just AName
  "term"      -> Just ATerm
  "rule-name" -> Just ARule
  _           -> Nothing

-- | Build the test a word names, from the operands written after it.
--
-- **Shaped like 'instruction', one layer up**: the word chooses the
-- constructor and the operand count is checked here rather than in the grammar,
-- for §2.5's reason that the parser is shallow. 'Nothing' is /no such test/ and
-- 'Just' with the wrong count is a different error, so the two are told apart
-- by the caller.
testOf :: String -> [Operand] -> Either TestError Test
testOf w os = case [ t | t <- everyTest, testWord t == w ] of
  []    -> Left NoSuchTestWord
  t : _ -> maybe (Left (WrongTestArity (length (testOperands t)) (length os)))
                 Right
                 (withOperands t os)

-- | Why a written test is not one. Local to resolution; 'RuleError' is what
-- escapes.
data TestError = NoSuchTestWord | WrongTestArity Int Int

-- | Put the written operands into a test drawn from 'everyTest'.
--
-- **The words live in 'testWord' and nowhere else**, which is why resolution
-- goes through that list rather than keeping a second table — his standing
-- objection to a word written in two places. What is left here is only /how/ a
-- test is rebuilt from its operands, and the final case is the arity mismatch,
-- which is reachable and is what 'testOf' reports.
--
-- A test added later must extend 'testWord' and 'testTypes', both of which
-- @-Wall@ forces; "Thena.RuleSyntaxTests" round-trips every entry of
-- 'everyTest' through the parser, which is what catches one this function
-- forgot.
withOperands :: Test -> [Operand] -> Maybe Test
withOperands t os = case (t, os) of
  (FocusIsHole,      []) -> Just FocusIsHole
  (FocusIsGuess,     []) -> Just FocusIsGuess
  (FocusIsComponent, []) -> Just FocusIsComponent
  (GoalTypeIsPi,     []) -> Just GoalTypeIsPi
  (GoalTypeIsLet,    []) -> Just GoalTypeIsLet
  (SurfaceIsName _, [o])         -> Just (SurfaceIsName o)
  (SurfaceIsUniverse _, [o])     -> Just (SurfaceIsUniverse o)
  (SurfaceIsUniverseOpen _, [o]) -> Just (SurfaceIsUniverseOpen o)
  (SurfaceIsPlaceholder _, [o])  -> Just (SurfaceIsPlaceholder o)
  (SurfaceIsHole _, [o])         -> Just (SurfaceIsHole o)
  (SurfaceIsApp _, [o])          -> Just (SurfaceIsApp o)
  (SurfaceIsLambda _, [o])       -> Just (SurfaceIsLambda o)
  (SurfaceIsForall _, [o])       -> Just (SurfaceIsForall o)
  (SurfaceIsArrow _, [o])        -> Just (SurfaceIsArrow o)
  (SurfaceIsLet _, [o])          -> Just (SurfaceIsLet o)
  (SurfaceIsAscription _, [o])   -> Just (SurfaceIsAscription o)
  (SurfaceIsElim _, [o])         -> Just (SurfaceIsElim o)
  (SurfaceIsDo _, [o])           -> Just (SurfaceIsDo o)
  (AppArgsAreExplicit _, [o])    -> Just (AppArgsAreExplicit o)
  (AppHeadIsName _, [o])         -> Just (AppHeadIsName o)
  (AppHeadIsElim _, [o])         -> Just (AppHeadIsElim o)
  (LambdaBindsMore _, [o])       -> Just (LambdaBindsMore o)
  (LambdaBindsOne _, [o])        -> Just (LambdaBindsOne o)
  (LetIsAnnotated _, [o])        -> Just (LetIsAnnotated o)
  (LetIsBare _, [o])             -> Just (LetIsBare o)
  (ListIsEmpty _, [o])           -> Just (ListIsEmpty o)
  (ListIsCons _, [o])            -> Just (ListIsCons o)
  (OptionIsSome _, [o])          -> Just (OptionIsSome o)
  (OptionIsNone _, [o])          -> Just (OptionIsNone o)
  _                      -> Nothing

-- | What a test was written with, in written order. 'Thena.Ops.operandsOf'\'s
-- job one type over, and what lets 'testOf' read an arity off 'everyTest'
-- rather than keeping a second table of counts.
-- | Every operand a head test reads, **with the type it wants there** (MS5
-- phase 66b) — 'Thena.Ops.operandTypes' one type over, and for the same reason:
-- two case splits agreeing about arity in twenty-four places is a thing that can
-- come apart, and one cannot disagree with itself.
--
-- **The head is where a rule's parameters get their types**, which is why this
-- exists before inference does: @rule elaborate t :- when (surface-is-name t)@
-- is what says @t@ is a 'Ty.TSurface'. Phase 66c is what reads it that way.
--
-- Every test but the focus questions asks about a term it is handed, and
-- all but the data ones ask about a /surface/ term — head predicates were the
-- surface language's from MS4 phase 47 onward.
testTypes :: Test -> [(Operand, Ty.Ty)]
testTypes t = case t of
  FocusIsHole     -> []
  FocusIsGuess    -> []
  FocusIsComponent -> []
  GoalTypeIsPi    -> []
  GoalTypeIsLet   -> []
  SurfaceIsName o         -> [(o, Ty.TSurface)]
  SurfaceIsUniverse o     -> [(o, Ty.TSurface)]
  SurfaceIsUniverseOpen o -> [(o, Ty.TSurface)]
  SurfaceIsPlaceholder o  -> [(o, Ty.TSurface)]
  SurfaceIsHole o         -> [(o, Ty.TSurface)]
  SurfaceIsApp o          -> [(o, Ty.TSurface)]
  SurfaceIsLambda o       -> [(o, Ty.TSurface)]
  SurfaceIsForall o       -> [(o, Ty.TSurface)]
  SurfaceIsArrow o        -> [(o, Ty.TSurface)]
  SurfaceIsLet o          -> [(o, Ty.TSurface)]
  SurfaceIsAscription o   -> [(o, Ty.TSurface)]
  SurfaceIsElim o         -> [(o, Ty.TSurface)]
  SurfaceIsDo o           -> [(o, Ty.TSurface)]
  AppArgsAreExplicit o    -> [(o, Ty.TSurface)]
  AppHeadIsName o         -> [(o, Ty.TSurface)]
  AppHeadIsElim o         -> [(o, Ty.TSurface)]
  LambdaBindsMore o       -> [(o, Ty.TSurface)]
  LambdaBindsOne o        -> [(o, Ty.TSurface)]
  LetIsAnnotated o        -> [(o, Ty.TSurface)]
  LetIsBare o             -> [(o, Ty.TSurface)]
  -- The four data questions (MS5 phase 65), and the only tests that ask about
  -- something @instral@ owns rather than about a surface node.
  ListIsEmpty o           -> [(o, Ty.TList (Ty.TVar 0))]
  ListIsCons o            -> [(o, Ty.TList (Ty.TVar 0))]
  OptionIsSome o          -> [(o, Ty.TOption (Ty.TVar 0))]
  OptionIsNone o          -> [(o, Ty.TOption (Ty.TVar 0))]

-- | Every operand a head test reads, in the order it is written.
testOperands :: Test -> [Operand]
testOperands = map fst . testTypes

-- | The word a 'Test' is written with. Total, so @-Wall@ makes a new test say
-- how it is spelled — 'Thena.Ops.opKeyword'\'s trick, one type over.
--
-- Hyphenated, which is what §8 and @OBJECTIVE.md@ have always written
-- (@focus-is-hole@, @hint-is-app@) and what the lexer could not read until this
-- phase widened an identifier.
testWord :: Test -> String
testWord t = case t of
  FocusIsHole     -> "focus-is-hole"
  FocusIsGuess    -> "focus-is-guess"
  FocusIsComponent -> "focus-is-component"
  GoalTypeIsPi    -> "goal-type-is-pi"
  GoalTypeIsLet   -> "goal-type-is-let"
  SurfaceIsName _         -> "surface-is-name"
  SurfaceIsUniverse _     -> "surface-is-universe"
  SurfaceIsUniverseOpen _ -> "surface-is-universe-open"
  SurfaceIsPlaceholder _  -> "surface-is-placeholder"
  SurfaceIsHole _         -> "surface-is-hole"
  SurfaceIsApp _          -> "surface-is-app"
  SurfaceIsLambda _       -> "surface-is-lambda"
  SurfaceIsForall _       -> "surface-is-forall"
  SurfaceIsArrow _        -> "surface-is-arrow"
  SurfaceIsLet _          -> "surface-is-let"
  SurfaceIsAscription _   -> "surface-is-ascription"
  SurfaceIsElim _         -> "surface-is-elim"
  SurfaceIsDo _           -> "surface-is-do"
  AppArgsAreExplicit _    -> "app-args-are-explicit"
  AppHeadIsName _         -> "app-head-is-name"
  AppHeadIsElim _         -> "app-head-is-elim"
  LambdaBindsMore _       -> "lambda-binds-more"
  LambdaBindsOne _        -> "lambda-binds-one"
  LetIsAnnotated _        -> "let-is-annotated"
  LetIsBare _             -> "let-is-bare"
  ListIsEmpty _           -> "list-is-empty"
  ListIsCons _            -> "list-is-cons"
  OptionIsSome _          -> "option-is-some"
  OptionIsNone _          -> "option-is-none"

-- | Every test there is. A list and not a case split, so it cannot be total —
-- 'testWord' is what @-Wall@ guards, and "Thena.RuleSyntaxTests" checks this
-- list against it.
-- An argument-taking test appears here with a placeholder operand, which is
-- all 'testWord' and 'testOperands' read: this list says what tests /exist/,
-- not what any written one says.
everyTest :: [Test]
everyTest =
  [ FocusIsHole, FocusIsGuess, FocusIsComponent, GoalTypeIsPi, GoalTypeIsLet
  , SurfaceIsName (Lit (VText ""))
  , SurfaceIsUniverse (Lit (VText ""))
  , SurfaceIsUniverseOpen (Lit (VText ""))
  , SurfaceIsPlaceholder (Lit (VText ""))
  , SurfaceIsHole (Lit (VText ""))
  , SurfaceIsApp (Lit (VText ""))
  , SurfaceIsLambda (Lit (VText ""))
  , SurfaceIsForall (Lit (VText ""))
  , SurfaceIsArrow (Lit (VText ""))
  , SurfaceIsLet (Lit (VText ""))
  , SurfaceIsAscription (Lit (VText ""))
  , SurfaceIsElim (Lit (VText ""))
  , SurfaceIsDo (Lit (VText ""))
  , AppArgsAreExplicit (Lit (VText ""))
  , AppHeadIsName (Lit (VText ""))
  , AppHeadIsElim (Lit (VText ""))
  , LambdaBindsMore (Lit (VText ""))
  , LambdaBindsOne (Lit (VText ""))
  , LetIsAnnotated (Lit (VText ""))
  , LetIsBare (Lit (VText ""))
  , ListIsEmpty (Lit (VText ""))
  , ListIsCons (Lit (VText ""))
  , OptionIsSome (Lit (VText ""))
  , OptionIsNone (Lit (VText ""))
  ]
