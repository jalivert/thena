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
  , resolveRule
  , resolveBlock
  , testWord
  , testOperands
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
  , partOf
  , partWords
  , produces
  )
import Thena.Surface.Concrete (Surface (..))
import qualified Thena.Surface.Zipper as Zipper
import Thena.Syntax.Concrete
  ( RawInstr (..)
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
  , baseRules       :: [Rule]
  }
  deriving (Eq, Show)

-- | Build one. Nothing is checked here — 'validateBase' is separate, so that a
-- caller who wants the errors gets them all rather than the first.
ruleBase :: String -> Maybe String -> FilePath -> [Rule] -> RuleBase
ruleBase = RuleBase

-- | Every rule the engine may search, across every loaded base, **in search
-- order**: the bases in the order they were loaded, and within each the order
-- its file wrote them.
--
-- This is the one place that says what \"leftmost first\" means, which is why
-- 'matches' takes the bases rather than the rules.
allRules :: [RuleBase] -> [Rule]
allRules = concatMap baseRules

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
    | r <- allRules bases
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
  [ length (ruleParams r) | r <- allRules bases, ruleName r == nm ]

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
  -- The first test that asks about an argument rather than about the focus.
  SurfaceIsName o -> case Op.operandIn args o of
    Left _            -> True
    Right (VSurface z) -> case Zipper.focus z of
      SurfaceName _ -> True
      _             -> False
    Right _            -> False
  where
    -- Written down, then reduced: §8's "head matching runs whnf", because a
    -- goal typed @id Type₀ (Nat -> Nat)@ is a Π and must match.
    written = expectedType cur
    reduced = whnf env (context cur) <$> written

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
  | BadOperands       GlobalName Int String
    -- ^ the right op word, written with the wrong arguments — too many, too
    -- few, or a position where a name was wanted. One error for all three: a
    -- rule body is one line, and the word is enough to find it
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
validate r = headScope ++ go 0 (initiallyBound r) (ruleBody r)
  where
    nm = ruleName r

    -- **A head may name only the rule's own parameters** (MS4 phase 47). It
    -- runs before the body, so the environment it reads is the call's
    -- arguments bound to those parameters and nothing else — there is no
    -- earlier @Bind@ for a name to have come from. Catching it here is what
    -- lets 'holds' read an unbound name as /a question about an argument
    -- nobody supplied/ rather than as a mistake it has to guess about.
    headScope =
      [ UnboundInHead nm n
      | t <- ruleHead r
      , Ref n <- testOperands t
      , n `notElem` ruleParams r
      ]

    go _ _ [] = []
    go i bound (instr : rest) =
      let o     = operationOf instr
          errs  = declaration i o ++ binding i instr o ++ scope i bound o
          bound' = case instr of
            Bind n _ -> n : bound
            Do _     -> bound
       in errs ++ go (i + 1) bound' rest

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
      [ UnboundInRule nm i n | Ref n <- operandsOf o, n `notElem` bound ]

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
resolveRule :: RawRule -> Either [RuleError] Rule
resolveRule (RawRule nm ps ts body) =
  case (headErrs, bodyErrs) of
    ([], []) -> Right (Rule g ps tests instrs)
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
      partitionEithers (zipWith (instruction g) [0 ..] body)

-- | What may be written as an operand of a test (MS4 phase 47).
--
-- The same two a body accepts, and 'RawPos' refused for the same reason —
-- a position is 'Down'\'s and nothing else takes one.
headOperand :: RawOperand -> Maybe Operand
headOperand o = case o of
  RawRef n  -> Just (Ref n)
  RawText t -> Just (Lit (VText t))
  RawPos _  -> Nothing

-- | Resolve a written block of instructions (MS4 phase 45).
--
-- **The same resolution a rule body gets**, and deliberately the same function
-- underneath: a @do@ block is the instruction language, so a word that names an
-- op is an op and a word that does not is a rule call, exactly as it is in a
-- rule (phase 25e). Nothing about a block is a second dialect.
--
-- The name is the one errors are reported against. A block has none of its own,
-- so its caller supplies where it came from.
resolveBlock :: GlobalName -> [RawInstr] -> Either [RuleError] [Instr]
resolveBlock g body = case partitionEithers (zipWith (instruction g) [0 ..] body) of
  ([], instrs) -> Right instrs
  (errs, _)    -> Left errs

-- | One written instruction. @‹name› = ‹op›@ is a 'Bind', a bare op is a 'Do' —
-- §7.2\'s two cases, and the grammar has no third.
instruction :: GlobalName -> Int -> RawInstr -> Either RuleError Instr
instruction g i ri = case ri of
  RawBind n o -> Bind n <$> operation g i o
  RawDo     o -> Do     <$> operation g i o

-- | An op word and its written arguments, resolved.
--
-- The whole word vocabulary is 'Thena.Ops.opKeyword'\'s, read backwards, and
-- the arities are here because that is where they are known. A word this does
-- A word this does not accept is a **rule call** (phase 25e); an accepted word
-- given the wrong arguments is 'BadOperands'. Those are separate mistakes, and
-- only the second is a load-time error now.
operation :: GlobalName -> Int -> RawOp -> Either RuleError Op
operation g i (RawOp w as)
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
      ("prim-intro", [])          -> Right (Intro Nothing)
      ("prim-intro", [a])         -> Intro . Just <$> ref a
      ("prim-intro", _)           -> bad
      ("call", RawRef r : rest)   -> Call (GlobalName r) <$> traverse ref rest
      ("call", _)                 -> bad
      -- **@make-elim@'s first word is a datatype, not an operand** (MS4 phase
      -- 41i), so it is spelled here for @call@'s reason rather than sitting in
      -- an arity table: the name is written down, never computed. The rest are
      -- the names its holes are to carry.
      ("make-apply", h : rest)    -> Op.MakeApply <$> ref h <*> traverse ref rest
      ("make-apply", _)           -> bad
      ("make-elim", RawRef d : rest) -> Op.MakeElim (GlobalName d) <$> traverse ref rest
      ("make-elim", _)            -> bad


      ("ask", [a, RawRef k])      -> case answerKind k of
        Just ak -> flip Ask ak <$> ref a
        Nothing -> bad
      ("ask", _)                  -> bad

      -- §3.7: a declaration is a command, not a rule-body operation. The word
      -- exists ('Thena.Ops.opKeyword' is total) and resolving it is refused
      -- here, one step before 'validate' would have.
      ("data", _)                 -> Left (DeclarationInBody g i)

      _ -> case (lookup w nullary, lookup w unary, lookup w binary, as) of
        (Just o,  _, _, [])       -> Right o
        (Just _,  _, _, _)        -> bad
        (_, Just f,  _, [a])      -> f <$> ref a
        (_, Just _,  _, _)        -> bad
        (_, _, Just f,  [a, b])   -> f <$> ref a <*> ref b
        (_, _, Just _,  _)        -> bad
        -- **A word that names no op is a call to a rule of that name**
        -- (phase 25e), which is what a bare word has meant at the REPL since
        -- phase 23b. The user, 2026-08-26: *"Bare word was always, always, the
        -- intended design."*
        --
        -- An op word given the wrong arity is still 'BadOperands' and not a
        -- call, because the arity tables above are consulted first: @claim x@
        -- is a mistake about @claim@, not a call to a rule named @claim@.
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
    ref o   = case o of
      RawRef n  -> Right (Ref n)
      RawText t -> Right (Lit (VText t))
      RawPos _  -> Left (BadOperands g i w)

    nullary =
      [ ("along", Along), ("into", Into), ("back", Back), ("reduce", Reduce)
      , ("prim-attack", Attack), ("prim-regret", Regret)
      , ("prim-solve", Solve), ("prim-abandon", Abandon), ("goal", Goal)
      , ("here", Here)
      , ("prim-prove", Prove)
      , ("pop-development", Op.PopDevelopment)
      ]
    unary =
      [ ("say", Say), ("yield", Op.Yield), ("prim-try", Try), ("prim-elaborate", Op.Elaborate)
      , ("goto", Goto), ("push-development", Op.PushDevelopment)
      , ("certify", Certify), ("prim-eliminate", Op.Eliminate)
      , ("typeof", Typing), ("expose", Op.Expose), ("fresh-name", FreshName), ("prim-apply", Op.Apply)
      ]
    binary =
      [ ("assume", Assume), ("claim", Claim), ("define", Define)
      , ("quantify", Op.Quantify)
      , ("concat", Concat), ("unify", Unify), ("unify-into", Op.UnifyInto)
      , ("arrow", Arrow), ("apply-to", ApplyTo)
      ]

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
-- A test added later must extend 'testWord' and 'testOperands', both of which
-- @-Wall@ forces; "Thena.RuleSyntaxTests" round-trips every entry of
-- 'everyTest' through the parser, which is what catches one this function
-- forgot.
withOperands :: Test -> [Operand] -> Maybe Test
withOperands t os = case (t, os) of
  (FocusIsHole,      []) -> Just FocusIsHole
  (FocusIsGuess,     []) -> Just FocusIsGuess
  (GoalTypeIsPi,     []) -> Just GoalTypeIsPi
  (GoalTypeIsLet,    []) -> Just GoalTypeIsLet
  (SurfaceIsName _, [o]) -> Just (SurfaceIsName o)
  _                      -> Nothing

-- | What a test was written with, in written order. 'Thena.Ops.operandsOf'\'s
-- job one type over, and what lets 'testOf' read an arity off 'everyTest'
-- rather than keeping a second table of counts.
testOperands :: Test -> [Operand]
testOperands t = case t of
  FocusIsHole     -> []
  FocusIsGuess    -> []
  GoalTypeIsPi    -> []
  GoalTypeIsLet   -> []
  SurfaceIsName o -> [o]

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
  GoalTypeIsPi    -> "goal-type-is-pi"
  GoalTypeIsLet   -> "goal-type-is-let"
  SurfaceIsName _ -> "surface-is-name"

-- | Every test there is. A list and not a case split, so it cannot be total —
-- 'testWord' is what @-Wall@ guards, and "Thena.RuleSyntaxTests" checks this
-- list against it.
-- An argument-taking test appears here with a placeholder operand, which is
-- all 'testWord' and 'testOperands' read: this list says what tests /exist/,
-- not what any written one says.
everyTest :: [Test]
everyTest =
  [ FocusIsHole, FocusIsGuess, GoalTypeIsPi, GoalTypeIsLet
  , SurfaceIsName (Lit (VText ""))
  ]
