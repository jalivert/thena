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
  , testWord
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
  , hintName
  , partOf
  , partWords
  , produces
  , usesHint
  )
import Thena.Syntax.Concrete
  ( Raw (..)
  , RawInstr (..)
  , RawOp (..)
  , RawOperand (..)
  , RawRule (..)
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
-- It takes a 'Cursor' rather than a 'Thena.Engine.ProofState' because
-- @ProofState@ is "Thena.Engine"'s and this module sits below it — and it can,
-- since @ProofState@ is a newtype over exactly this cursor. It takes a
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
-- **A hint partitions the base** — 'Thena.Ops.usesHint', decided by the user
-- 2026-08-23, and the argument is there. It is applied /here/ and not only in
-- 'dispatch' so that the two cannot disagree: @:matches@ would otherwise offer
-- @attack@ under a hint that the engine, dispatching, would never run it for.
-- The consequence at the REPL is that @:matches@ with no argument lists exactly
-- what it listed before this phase, and @:matches ‹hint›@ is a separate
-- question with a separate answer.
matches :: [RuleBase] -> GlobalEnv -> Cursor -> Maybe Raw -> RuleIter
matches bases env cur hint =
  RuleIter [ r | r <- allRules bases, usesHint r == isHinted, all (holds env cur hint) (ruleHead r) ]
  where
    isHinted = case hint of
      Just _  -> True
      Nothing -> False

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
dispatch :: [RuleBase] -> GlobalEnv -> Cursor -> Maybe Raw -> RuleIter
dispatch base env cur hint =
  let RuleIter rs = matches base env cur hint
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
-- **No hint**, so a rule whose head asks about one is never a call candidate.
-- 'matches' partitions on exactly this, and passing 'Nothing' here means a call
-- and a hintless dispatch agree about which half of the base they see.
clauses :: [RuleBase] -> GlobalEnv -> Cursor -> GlobalName -> Int -> RuleIter
clauses bases env cur nm n =
  RuleIter
    [ r
    | r <- allRules bases
    , ruleName r == nm
    , length (ruleParams r) == n
    , not (usesHint r)
    , all (holds env cur Nothing) (ruleHead r)
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
holds :: GlobalEnv -> Cursor -> Maybe Raw -> Test -> Bool
holds env cur hint t = case t of
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
  -- The hint is the tree as parsed, not as resolved: whether the name is in
  -- scope is @resolve@'s answer and it is given in the body, where failing is
  -- ordinary (§7.3). A head that resolved would be doing the work twice and
  -- would be a head that is not shallow (§8).
  HintIsName    -> case hint of
    Just (RawName _) -> True
    _                -> False
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
  | NoSuchOp          GlobalName Int String
    -- ^ a word in a body that names no 'Op'
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
validate r = go 0 (initiallyBound r) (ruleBody r)
  where
    nm = ruleName r

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

-- | The names a body may read before it binds anything of its own: its
-- parameters, and — when its head asks about the hint — 'Thena.Ops.hintName',
-- which @Prove@ seeds the environment with (§8, phase 17b).
--
-- Without this line @elab-var@ fails its own load-time check, because @hint@ is
-- a 'Ref' that no @Bind@ introduces.
initiallyBound :: Rule -> [Name]
initiallyBound r
  | usesHint r = hintName : ruleParams r
  | otherwise  = ruleParams r

-- | Every operand an op reads. A total case split, so @-Wall@ makes a new op
-- say whether it reads anything.
operandsOf :: Op -> [Operand]
operandsOf o = case o of
  Assume a b   -> [a, b]
  Claim  a b   -> [a, b]
  Ask    a _   -> [a]
  Say    a     -> [a]
  Concat a b   -> [a, b]
  Unify  a b   -> [a, b]
  Try    a     -> [a]
  Certify a    -> [a]
  Op.Eliminate a -> [a]
  Parse   a    -> [a]
  Op.Resolve a -> [a]
  Call _ as    -> as
  Prove h      -> maybe [] (: []) h
  DefineData _ -> []
  Along        -> []
  Into         -> []
  CrossType    -> []
  CrossValue   -> []
  Down _       -> []
  Back         -> []
  Reduce       -> []
  Attack       -> []
  Intro        -> []
  Regret       -> []
  Solve        -> []
  Abandon      -> []

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
    test w = maybe (Left (NoSuchTest g w)) Right (testOf w)

    (bodyErrs, instrs) =
      partitionEithers (zipWith (instruction g) [0 ..] body)

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
-- not accept is 'NoSuchOp'; an accepted word given the wrong arguments is
-- 'BadOperands'. The two are separate because they are separate mistakes —
-- \"there is no such op\" and \"you wrote it wrong\".
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
      ("call", RawRef r : rest)   -> Call (GlobalName r) <$> traverse ref rest
      ("call", _)                 -> bad

      ("prove", [])               -> Right (Prove Nothing)
      ("prove", [a])              -> Prove . Just <$> ref a
      ("prove", _)                -> bad

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
        _                         -> Left (NoSuchOp g i w)
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
      , ("attack", Attack), ("intro", Intro), ("regret", Regret)
      , ("solve", Solve), ("abandon", Abandon)
      ]
    unary =
      [ ("say", Say), ("try", Try), ("parse", Parse), ("resolve", Op.Resolve)
      , ("certify", Certify), ("eliminate", Op.Eliminate)
      ]
    binary =
      [ ("assume", Assume), ("claim", Claim)
      , ("concat", Concat), ("unify", Unify)
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

testOf :: String -> Maybe Test
testOf w = lookup w [ (testWord t, t) | t <- everyTest ]

-- | The word a 'Test' is written with. Total, so @-Wall@ makes a new test say
-- how it is spelled — 'Thena.Ops.opKeyword'\'s trick, one type over.
--
-- Hyphenated, which is what §8 and @OBJECTIVE.md@ have always written
-- (@focus-is-hole@, @hint-is-app@) and what the lexer could not read until this
-- phase widened an identifier.
testWord :: Test -> String
testWord t = case t of
  FocusIsHole   -> "focus-is-hole"
  FocusIsGuess  -> "focus-is-guess"
  GoalTypeIsPi  -> "goal-type-is-pi"
  GoalTypeIsLet -> "goal-type-is-let"
  HintIsName    -> "hint-is-name"

-- | Every test there is. A list and not a case split, so it cannot be total —
-- 'testWord' is what @-Wall@ guards, and "Thena.RuleSyntaxTests" checks this
-- list against it.
everyTest :: [Test]
everyTest = [FocusIsHole, FocusIsGuess, GoalTypeIsPi, GoalTypeIsLet, HintIsName]
