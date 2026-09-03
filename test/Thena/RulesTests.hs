-- | The rule engine, read-only: what matches where, and what a well-formed
-- rule is.
--
-- Built in Haskell rather than driven through the REPL, for
-- "Thena.EngineTests"' reason — @:matches@ can only reach the states the REPL
-- can reach, and 'Thena.Rules.matches' has to be right for the rest.
module Thena.RulesTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Var
  , close
  , fresh
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, crossType, enter)
import Thena.Development.Partial (Partial (..))
import Thena.Declared (natDecl)
import Thena.Standard (expectedBase)
import Thena.Driver (parseDeclaration)
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , load
  , resumeAt
  , resumeYield
  , step
  )
import Thena.Errors (FailReason)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition
  , addDefinition
  , emptyGlobals
  )
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op
  , Operand (..)
  , Rule (..)
  , Value (..)
  , produces
  )
-- §2.5: "Thena.Ops" is qualified everywhere except "Thena.Engine", because
-- @Assume@ and @Claim@ name both a component and an op.
import qualified Thena.Ops as Ops
import Thena.Surface.Concrete (Surface (..))
import Thena.Surface.Zipper (rootedAt)
import Thena.Rules
  ( RuleError (..)
  , RuleIter
  , allRules
  , hasNext
  , matches
  , next
  , ruleBase
  , validate
  , validateBase
  )

tests :: TestTree
tests =
  testGroup
    "rules"
    [ matchTests
    , iteratorTests
    , validateTests
    , producesTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0, type1 :: Core
type0 = Universe (LZero)
type1 = Universe (levelOfNat 1)

-- | @S -> T@, with a binder nothing refers to.
arrow :: Core -> Core -> Core
arrow s t = Pi (Ident "_") s (close (fst (fresh 0)) t)

-- | @? x : ty . x@ — the shape every hole rule wants.
holeAt :: Core -> Cursor
holeAt ty = enter (Under (Claim v (Ident "goal") ty) (Trailing (Free v)))
  where v = var

-- | @? x ≐ (? y : ty . y) : ty . x@ — what @attack@ makes.
guessAt :: Core -> Cursor
guessAt ty =
  enter (Under (Guess v (Ident "goal") body ty) (Trailing (Free v)))
  where
    body = Under (Claim w (Ident "goal") ty) (Trailing (Free w))
    v = var
    w = fst (fresh 1)

var :: Var
var = fst (fresh 0)

-- | An environment where @Arrow@ is a definition unfolding to a Π. §8's own
-- example of why head matching has to reduce, in the smallest form that has
-- one.
withArrow :: GlobalEnv
withArrow =
  addDefinition
    (GlobalName "Arrow")
    (MkDefinition [] [] type1 (arrow type0 type0))
    emptyGlobals

matching :: GlobalEnv -> Cursor -> [String]
matching env cur = map nameOf (drain (matches expectedBase env cur))

nameOf :: Rule -> String
nameOf r = let GlobalName n = ruleName r in n

-- | Walk an iterator to the end with 'next' alone, which is how the driver's
-- display walks it.
drain :: RuleIter -> [Rule]
drain it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : drain rest

-- --------------------------------------------------------------------------
-- What matches where (§7.6)
-- --------------------------------------------------------------------------

matchTests :: TestTree
matchTests =
  testGroup
    "matches"
    [ -- Three at a hole, and that is what makes the list a list: phase 16 has
      -- to choose between them, and the user sees the choice being made.
      testCase "a hole offers the hole rules, in definition order" $
        matching emptyGlobals (holeAt type0)
          @?= ["attack", "try-core", "abandon", "eliminate-core", "prove", "elaborate", "fill", "unify-refine-core", "apply-core"]

    , testCase "a guess at a non-Π offers only solve and regret" $
        matching emptyGlobals (guessAt type0)
          @?= ["solve", "regret", "prove"]

    , testCase "a guess at a Π offers intro as well" $
        matching emptyGlobals (guessAt (arrow type0 type0))
          @?= ["intro", "solve", "regret", "prove"]

      -- §8: "Head matching runs whnf. A goal typed @id Type (Nat → Nat)@ is a Π
      -- and must match GoalTypeIsPi." Written down, @Arrow@ is a 'Global' and
      -- not a 'Pi'; a head that did not reduce would miss it.
    , testCase "a goal type that only reduces to a Π still matches" $
        matching withArrow (guessAt (Global (GlobalName "Arrow") []))
          @?= ["intro", "solve", "regret", "prove"]

    , testCase "and does not, in an environment where it does not unfold" $
        matching emptyGlobals (guessAt (Global (GlobalName "Arrow") []))
          @?= ["solve", "regret", "prove"]

      -- The one test that must NOT reduce: whnf δ-reduces a term-level let
      -- away (§5.1), so asking about the reduced type would make GoalTypeIsLet
      -- unpassable — which is exactly the bug this phase found in
      -- 'Thena.Engine.introduce'.
    , testCase "a goal type written as a let offers intro" $
        matching emptyGlobals (guessAt (Let (Ident "x") type0 type1 (close var type0)))
          @?= ["intro", "solve", "regret", "prove"]

      -- The invariant checked by different code from the code that maintains
      -- it: the head says @intro@ applies, so @intro@ must actually apply. It
      -- is the direction that /is/ guaranteed for these two rules, and the one
      -- the let bug broke — the op could not do what no head could offer.
    , testCase "where the let clause is offered, intro succeeds" $
        let cur = guessAt (Let (Ident "x") type0 type1 (close var type0))
         in do
              nameOf `map` drain (matches expectedBase emptyGlobals cur)
                @?= ["intro", "solve", "regret", "prove"]
              ranOk (machineAt cur [Do (Ops.Intro Nothing)])

    , testCase "where the Π clause is offered, intro succeeds" $
        ranOk (machineAt (guessAt (arrow type0 type0)) [Do (Ops.Intro Nothing)])

      -- Every head this phase has asks about a component, so nothing applies
      -- in the core fragment. Definite, not "blocked": the focus's shape is
      -- known, which is what §7.6 distinguishes from §8.1's suspension case.
    , testCase "nothing matches in the core fragment" $
        case crossType (holeAt type0) of
          Left e    -> assertFailure ("could not cross: " ++ show e)
          Right cur -> matching emptyGlobals cur @?= []

      -- Definition order is dispatch order (§8), so the match list is always a
      -- subsequence of the base and never a reordering of it.
    , testCase "the match list is a subsequence of the base" $
        let base = map nameOf (allRules expectedBase)
         in mapM_
              (\cur -> assertSubsequence (matching emptyGlobals cur) base)
              [holeAt type0, guessAt type0, guessAt (arrow type0 type0)]
    ]

assertSubsequence :: [String] -> [String] -> IO ()
assertSubsequence xs ys
  | go xs ys  = pure ()
  | otherwise = assertFailure (show xs ++ " is not a subsequence of " ++ show ys)
  where
    go [] _ = True
    go _ [] = False
    go (a : as) (b : bs) = if a == b then go as bs else go (a : as) bs

-- --------------------------------------------------------------------------
-- The iterator (§7.6)
-- --------------------------------------------------------------------------

iteratorTests :: TestTree
iteratorTests =
  testGroup
    "the iterator"
    [ testCase "hasNext agrees with next, at every position" $
        let walk it = case next it of
              Nothing        -> hasNext it @?= False
              Just (_, rest) -> (hasNext it @?= True) >> walk rest
         in walk (matches expectedBase emptyGlobals (holeAt type0))

    , testCase "an empty iterator has nothing" $
        let it = matches expectedBase emptyGlobals (guessAt type0)
         in case next it >>= next . snd >>= next . snd >>= next . snd of
              Nothing -> pure ()
              Just _  -> assertFailure "expected three matches and no more"

      -- §7.6: persistent, "a frame holds one and the UI may hold the same one;
      -- if advancing mutated shared state they would interfere." A lazy list
      -- gives this outright; the test is here because the requirement is on the
      -- type, and a later representation could quietly lose it.
    , testCase "advancing one copy does not disturb another" $
        let it = matches expectedBase emptyGlobals (holeAt type0)
            deep = drop 2 (drain it)
         in do
              _ <- pure deep
              map nameOf (drain it) @?= ["attack", "try-core", "abandon", "eliminate-core", "prove", "elaborate", "fill", "unify-refine-core", "apply-core"]
              map nameOf deep @?= ["abandon", "eliminate-core", "prove", "elaborate", "fill", "unify-refine-core", "apply-core"]
    ]

-- --------------------------------------------------------------------------
-- Well-formedness (§2.4, §7.2)
-- --------------------------------------------------------------------------

named :: String -> [Name'] -> [Instr] -> Rule
named n ps = Rule (GlobalName n) ps []

type Name' = String

validateTests :: TestTree
validateTests =
  testGroup
    "validate"
    [ testCase "the shipped base is clean" $
        concatMap validateBase expectedBase @?= []

      -- §3.7's line, made structural: a declaration is a command, not a
      -- rule-body operation.
    , testCase "define-data in a body is rejected" $
        validate (named "bad" [] [Do (Ops.DefineData someData)])
          @?= [DeclarationInBody (GlobalName "bad") 0]

    , testCase "binding an op that produces nothing is rejected" $
        validate (named "bad" [] [Bind "x" Ops.Attack])
          @?= [BoundNonProducing (GlobalName "bad") 0 "x"]

    , testCase "binding an op that produces something is fine" $
        validate (named "ok" [] [Bind "x" (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))])
          @?= []

    , testCase "a Ref to nothing is rejected" $
        validate (named "bad" [] [Do (Ops.Say (Ref "z"))])
          @?= [UnboundInRule (GlobalName "bad") 0 "z"]

    , testCase "a parameter binds it" $
        validate (named "ok" ["z"] [Do (Ops.Say (Ref "z"))]) @?= []

    , testCase "an earlier Bind binds it" $
        validate
          (named "ok" []
            [ Bind "z" (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))
            , Do (Ops.Say (Ref "z"))
            ])
          @?= []

      -- A later Bind does not: the environment is built as the body runs.
    , testCase "a later Bind does not" $
        validate
          (named "bad" []
            [ Do (Ops.Say (Ref "z"))
            , Bind "z" (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))
            ])
          @?= [UnboundInRule (GlobalName "bad") 0 "z"]

      -- Every error, not the first: a rule author fixing one at a time would
      -- reload once per mistake.
    , testCase "all three are reported, with their positions" $
        validate
          (named "bad" []
            [ Bind "x" Ops.Attack
            , Do (Ops.DefineData someData)
            , Do (Ops.Say (Ref "z"))
            ])
          @?= [ BoundNonProducing (GlobalName "bad") 0 "x"
              , DeclarationInBody (GlobalName "bad") 1
              , UnboundInRule (GlobalName "bad") 2 "z"
              ]

    , testCase "validateBase checks every rule" $
        length (validateBase (ruleBase "test" Nothing ""
                                [ named "a" [] [Bind "x" Ops.Attack]
                                , named "b" [] [Do (Ops.Say (Ref "z"))]
                                ]))
          @?= 2
    ]

-- --------------------------------------------------------------------------
-- 'produces', checked against the engine (§7.2)
-- --------------------------------------------------------------------------

-- | The standing lesson: find the invariant maintained by different code from
-- the code that checks it (phase 5's @context@).
--
-- 'Thena.Ops.produces' is a table, and a table agrees with itself. What decides
-- the question is 'Thena.Engine.perform', so every op is run — in a state where
-- it actually succeeds, which the 'ranOk' half enforces — and the answer is
-- read off @env@. An op that grows a result later, or loses one, fails here
-- rather than silently letting @x = op@ bind nothing.
producesTests :: TestTree
producesTests =
  testGroup
    "produces agrees with the engine"
    [ testCase label (checkProduces env cur before o) | (label, env, cur, before, o) <- table ]
  where
    -- **At @Type₁@, not @Type₀@** (phase 25b): the rows below @try@ a term and
    -- @try@ now checks it, and the term to hand in an empty environment is
    -- @Type₀@ — which inhabits @Type₁@. It was @holeAt type0@ until the side
    -- condition was enforced and the fixture turned out to be ill-typed.
    hole    = holeAt type1
    piHole  = holeAt (arrow type0 type0)
    guessed = [Do Ops.Attack]
    tried   = [Do (Ops.Try (term type0))]
    solved  = [Do (Ops.Try (term type0)), Do Ops.Solve]
    e       = emptyGlobals
    table =
      [ ("ask",         e, hole,    [],            Ops.Ask (text "?") AText)
      , ("concat",      e, hole,    [],            Ops.Concat (text "a") (text "b"))
      , ("assume",      e, hole,    [],            Ops.Assume (text "x") (term type0))
      , ("claim",       e, hole,    [],            Ops.Claim (text "h") (term type0))
      , ("say",         e, hole,    [],            Ops.Say (text "hi"))
      , ("define-data", e, hole,    [],            Ops.DefineData someData)
      , ("certify",     e, hole,    solved,        Ops.Certify (term type0))
      , ("unify",       e, hole,    [],            Ops.Unify (term type0) (term type0))
      , ("reduce",      e, hole,    [Do Ops.CrossType], Ops.Reduce)
      , ("along",       e, twoHoles, [],           Ops.Along)
      , ("into",        e, hole,    guessed,       Ops.Into)
      , ("cross type",  e, hole,    [],            Ops.CrossType)
      , ("cross val",   e, hole,    solved,        Ops.CrossValue)
      , ("down",        e, piHole,  [Do Ops.CrossType], Ops.Down Ops.Dom)
      , ("back",        e, hole,    [Do Ops.CrossType], Ops.Back)
      , ("attack",      e, hole,    [],            Ops.Attack)
      , ("intro",       e, guessAt (arrow type0 type0), [], Ops.Intro Nothing)
      , ("try",         e, hole,    [],            Ops.Try (term type0))
      , ("regret",      e, hole,    tried,         Ops.Regret)
      , ("solve",       e, hole,    tried,         Ops.Solve)
      , ("abandon",     e, twoHoles, [],           Ops.Abandon)
        -- Phase 17b's four. @prove@ and @call@ both hand control to a body and
        -- get it back, so what a @Bind@ on either would name is the caller's
        -- own environment — restored on return, and without the destination.
      , ("prim-prove",  e, hole,    [],            Ops.Prove)
      , ("call",        e, hole,    [],            Ops.Call (GlobalName "try-core") [term type0])
      , ("prim-elaborate", e, hole, [],           Ops.Elaborate (Lit (VSurface (rootedAt SurfaceUniverseOpen))))
      ]

    -- @try ‹t›@, as 'expectedBase' ships it — what @call@ needs something to
    -- call.

checkProduces :: GlobalEnv -> Cursor -> [Instr] -> Op -> IO ()
checkProduces globalEnv cur before o =
  case runOut (machineIn globalEnv cur (before ++ [Bind "r" o])) of
    Left r  -> assertFailure ("the op did not run: " ++ show r)
    Right m -> (lookup "r" (Thena.Engine.env (exec m)) /= Nothing) @?= produces o

-- | @? a : Type₀ . ? goal : Type₀ . goal@, focused on @a@ — the one shape
-- @along@ and @abandon@ both need, and the only one in this module with a
-- component the trailing term does not mention.
twoHoles :: Cursor
twoHoles =
  enter
    ( Under (Claim a (Ident "a") type0)
        (Under (Claim g (Ident "goal") type0) (Trailing (Free g)))
    )
  where
    a = fst (fresh 8)
    g = fst (fresh 9)

someData :: InductiveDefinition
someData = case parseDeclaration emptyGlobals 200 natDecl of
  Right (d, _) -> d
  Left err     -> error ("fixture does not parse: " ++ show err)

term :: Core -> Operand
term = Lit . VTerm . Trailing

text :: String -> Operand
text = Lit . VText

-- | A machine at a given state, holding a program. The counter starts well
-- above every 'Var' the fixtures mint, so nothing it mints collides.
machineIn :: GlobalEnv -> Cursor -> [Instr] -> Machine
machineIn env cur is =
  load is (Machine (Exec [] [] []) (Development cur) [] env expectedBase [] 1000)

machineAt :: Cursor -> [Instr] -> Machine
machineAt = machineIn emptyGlobals

-- | Run to the end, following every channel the driver follows. 'Asking' is
-- answered, because that is the only way an @Ops.Ask@'s destination is ever filled
-- (§7.5) — the whole point of 'produces' saying @True@ for it.
runOut :: Machine -> Either FailReason Machine
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying _ m'       -> runOut m'
  Declaring _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> runOut (resumeAt "ok" m')
  -- Handed straight back, so a rule that yields is still exercised end to
  -- end rather than stopping the harness (MS4 phase 45b).
  Yielding _ m'     -> runOut (resumeYield m')
  Finished m'       -> Right m'
  Stuck r _         -> Left r

ranOk :: Machine -> IO ()
ranOk m = case runOut m of
  Right _ -> pure ()
  Left r  -> assertFailure ("expected the program to run, got " ++ show r)
