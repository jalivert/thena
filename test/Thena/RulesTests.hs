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
import Thena.Declared (nat, natDecl)
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
import Thena.Errors (FailReason (..))
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
  , signatureOf
  )
-- §2.5: "Thena.Ops" is qualified everywhere except "Thena.Engine", because
-- @Assume@ and @Claim@ name both a component and an op.
import qualified Thena.Ops as Ops
import Thena.Instral.Type (Signature (..), Ty (..), renderTy)
import qualified Data.List.NonEmpty as NE
import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..))
import Thena.Surface.Zipper (rootedAt)
import Thena.Rules
  ( RuleBase
  , RuleError (..)
  , clauses
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
    , returnTests
    , dataTests
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
        matching emptyGlobals (holeAt type0) @?= everyHoleRule

    , testCase "a guess at a non-Π offers only solve and regret" $
        matching emptyGlobals (guessAt type0)
          @?= ["solve", "regret", "prove"] ++ walkers

    , testCase "a guess at a Π offers intro as well" $
        matching emptyGlobals (guessAt (arrow type0 type0))
          @?= ["intro", "solve", "regret", "prove"] ++ walkers

      -- §8: "Head matching runs whnf. A goal typed @id Type (Nat → Nat)@ is a Π
      -- and must match GoalTypeIsPi." Written down, @Arrow@ is a 'Global' and
      -- not a 'Pi'; a head that did not reduce would miss it.
    , testCase "a goal type that only reduces to a Π still matches" $
        matching withArrow (guessAt (Global (GlobalName "Arrow") []))
          @?= ["intro", "solve", "regret", "prove"] ++ walkers

    , testCase "and does not, in an environment where it does not unfold" $
        matching emptyGlobals (guessAt (Global (GlobalName "Arrow") []))
          @?= ["solve", "regret", "prove"] ++ walkers

      -- The one test that must NOT reduce: whnf δ-reduces a term-level let
      -- away (§5.1), so asking about the reduced type would make GoalTypeIsLet
      -- unpassable — which is exactly the bug this phase found in
      -- 'Thena.Engine.introduce'.
    , testCase "a goal type written as a let offers intro" $
        matching emptyGlobals (guessAt (Let (Ident "x") type0 type1 (close var type0)))
          @?= ["intro", "solve", "regret", "prove"] ++ walkers

      -- The invariant checked by different code from the code that maintains
      -- it: the head says @intro@ applies, so @intro@ must actually apply. It
      -- is the direction that /is/ guaranteed for these two rules, and the one
      -- the let bug broke — the op could not do what no head could offer.
    , testCase "where the let clause is offered, intro succeeds" $
        let cur = guessAt (Let (Ident "x") type0 type1 (close var type0))
         in do
              nameOf `map` drain (matches expectedBase emptyGlobals cur)
                @?= ["intro", "solve", "regret", "prove"] ++ walkers
              ranOk (machineAt cur [Do (Ops.IntroLet Nothing)])

    , testCase "where the Π clause is offered, intro succeeds" $
        ranOk (machineAt (guessAt (arrow type0 type0)) [Do (Ops.IntroPi Nothing)])

      -- Every head that asks about a component fails in the core fragment, so
      -- what is left is the rules with no head at all. Definite, not
      -- "blocked": the focus's shape is known, which is what §7.6
      -- distinguishes from §8.1's suspension case.
      --
      -- **The three that remain are the asking tactics** (MS5 phase 62b), and
      -- they are here because their head is honest: @claim@ inserts above the
      -- focus and that works from inside a core term, so a head refusing it
      -- would make the one-argument clause disagree with the two-argument op
      -- about where the word applies.
    , testCase "only the headless rules match in the core fragment" $
        case crossType (holeAt type0) of
          Left e    -> assertFailure ("could not cross: " ++ show e)
          Right cur -> matching emptyGlobals cur @?= ["claim", "assume", "quantify"]

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

      -- **Drained by name rather than by a count**, since MS4 phase 49c: a guess
      -- offers @solve@, @regret@, @prove@ and the λ case's two recursive
      -- helpers, and a fixed number of @next@es would have to move every time a
      -- rule is added.
    , testCase "an empty iterator has nothing" $
        let it = matches expectedBase emptyGlobals (guessAt type0)
         in case drop (length (["solve", "regret", "prove"] ++ walkers)) (drain it) of
              [] -> pure ()
              rs -> assertFailure ("expected no more, got " ++ show (map nameOf rs))

      -- §7.6: persistent, "a frame holds one and the UI may hold the same one;
      -- if advancing mutated shared state they would interfere." A lazy list
      -- gives this outright; the test is here because the requirement is on the
      -- type, and a later representation could quietly lose it.
    , testCase "advancing one copy does not disturb another" $
        let it = matches expectedBase emptyGlobals (holeAt type0)
            deep = drop 2 (drain it)
         in do
              _ <- pure deep
              map nameOf (drain it) @?= everyHoleRule
              map nameOf deep @?= drop 2 everyHoleRule
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

      -- **@true@ and @false@ are values, so they cannot also be names** (MS5
      -- phase 64). Every @Ref@ to one has already become a literal by the time
      -- a rule is built, so a parameter or a binding of either name could never
      -- be read back — a rule that quietly does something other than it says,
      -- which is what a load-time refusal is for.
    , testCase "a parameter may not be named true" $
        validate (named "r" ["true"] [Do Ops.Solve])
          @?= [ReservedName (GlobalName "r") "true"]
    , testCase "nor a binding false" $
        validate (named "r" [] [Bind "false" Ops.Here])
          @?= [ReservedName (GlobalName "r") "false"]
    , testCase "and an ordinary name is untouched" $
        validate (named "r" ["t"] [Bind "x" Ops.Here]) @?= []

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
        length (validateBase (ruleBase "test" Nothing "" []
                                [ named "a" [] [Bind "x" Ops.Attack]
                                , named "b" [] [Do (Ops.Say (Ref "z"))]
                                ]))
          @?= 2
    ]

-- --------------------------------------------------------------------------
-- 'produces', checked against the engine (§7.2)
-- --------------------------------------------------------------------------

-- | @instral@'s own data (MS5 phase 65).
--
-- **The mechanism, not a caller** again: nothing in the shipped base builds a
-- list. What is worth pinning is that the shapes are asked about in a /head/,
-- which is how a rule branches — the reason the data needs no @if@ and no
-- second control structure.
dataTests :: TestTree
dataTests =
  testGroup
    "instral's data structures"
    [ testCase "a list is built from its elements, references and all" $
        valueOf [Bind "x" (Ops.Concat (text "a") (text "b"))]
                (Ops.Some (ListOf [Ref "x", text "c"]))
          >>= (@?= Just (VOption (Just (VList [VText "ab", VText "c"]))))

    , testCase "and a pair the same way" $
        valueOf [] (Ops.PairFirst (PairOf (text "a") (Lit (VInt 1))))
          >>= (@?= Just (VText "a"))

    , -- An unbound name inside a literal is the body's mistake and is caught
      -- when the base loads, which needs 'Thena.Ops.refsIn' to look inside.
      testCase "an unbound name inside a list is refused at load" $
        validate (named "r" [] [Do (Ops.Say (ListOf [Ref "nope"]))])
          @?= [UnboundInRule (GlobalName "r") 0 "nope"]

    , testCase "list-head of the empty list is none" $
        valueOf [] (Ops.ListHead (ListOf []))
          >>= (@?= Just (VOption Nothing))

    , testCase "and of a non-empty one is some" $
        valueOf [] (Ops.ListHead (ListOf [text "a"]))
          >>= (@?= Just (VOption (Just (VText "a"))))

    , testCase "list-tail drops one" $
        valueOf [Bind "t" (Ops.ListTail (ListOf [text "a", text "b"]))]
                (Ops.ListHead (Ref "t"))
          >>= (@?= Just (VOption (Just (VText "b"))))
    , testCase "and the empty list has an empty tail" $
        valueOf [Bind "t" (Ops.ListTail (ListOf []))] (Ops.ListHead (Ref "t"))
          >>= (@?= Just (VOption Nothing))

    , testCase "option-value of none fails rather than answering" $
        failureOf [Do (Ops.OptionValue (Lit (VOption Nothing)))]
          >>= (@?= Just NothingThere)

    , -- **The shape questions are asked in a HEAD**, which is how a rule
      -- branches — so they are tested through 'clauses', the thing that
      -- actually consults them, rather than through the predicate directly.
      testCase "a head picks the clause the shape fits" $ do
        clauseFor [VList []]          @?= ["empty"]
        clauseFor [VList [VText "a"]] @?= ["cons"]
    , -- A value of the wrong kind is simply not that shape: a head asks a
      -- question, it does not fail.
      testCase "and a value of the wrong kind fits neither" $
        clauseFor [VText "a"] @?= []
    ]
  where
    run is = runOut (machineIn emptyGlobals (holeAt type1) is)

    valueOf before o = pure $ case run (before ++ [Bind "r" o]) of
      Left _  -> Nothing
      Right m -> lookup "r" (Thena.Engine.env (exec m))

    failureOf is = pure $ case run is of
      Left e  -> Just e
      Right _ -> Nothing

    -- Two clauses of one name, told apart by the shape of the argument.
    shapes =
      ruleBase "shapes" Nothing "" []
        [ Rule (GlobalName "shape") ["xs"] [Ops.ListIsEmpty (Ref "xs")]
            [Do (Ops.Say (Lit (VText "empty")))]
        , Rule (GlobalName "shape") ["xs"] [Ops.ListIsCons (Ref "xs")]
            [Do (Ops.Say (Lit (VText "cons")))]
        ]

    clauseFor vs =
      [ w
      | r <- drain (clauses [shapes] emptyGlobals (holeAt type1)
                            (GlobalName "shape") vs)
      , Do (Ops.Say (Lit (VText w))) <- ruleBody r
      ]

-- | What a rule hands back (MS5 phase 63).
--
-- **The mechanism, not a caller.** Nothing in @rules/standard.thena.rules@ wants
-- a returned value yet; the milestone's doctrine is that a piece built ahead of
-- its first customer still gets tests, so these are them.
returnTests :: TestTree
returnTests =
  testGroup
    "a rule returns a value"
    [ testCase "the caller's binding is filled by the callee's return" $
        envAfter [Bind "r" (Ops.Call (GlobalName "gives") [])]
          >>= (@?= Just (VText "a value"))

    , -- @return@ ends the body, so the @say@ after it never runs. Checked
      -- through the binding rather than through the message, because a body
      -- that ran on would still return the same value.
      testCase "return ends the body" $
        ranWith [Do (Ops.Call (GlobalName "runs-on") [])]
          >>= (@?= Right [])

    , testCase "a body that never returns fails where the value was wanted" $
        ranWith [Bind "r" (Ops.Call (GlobalName "silent") [])]
          >>= (@?= Left (NothingReturned "r"))

    , -- The same rule called for effect is fine: nothing asked it for a value.
      testCase "and is fine when nothing asked it for one" $
        ranWith [Do (Ops.Call (GlobalName "silent") [])]
          >>= (@?= Right [])

    , testCase "return outside a call has nothing to return from" $
        ranWith [Do (Ops.Return (text "x"))]
          >>= (@?= Left NothingToReturnFrom)

    , -- **Each alternative returns its own value** (the reason 'Choice' carries
      -- the destination too): the first clause of @two-ways@ fails before it
      -- returns, so backtracking takes the second, and the binding is made from
      -- there. Without the field on 'Choice' the binding would never happen at
      -- all, because a call with two candidates builds one of those and not a
      -- 'Thena.Engine.Call'.
      testCase "backtracking rebinds from the clause that finally ran" $
        envAfter [ Bind "r" (Ops.Call (GlobalName "two-ways") [])
                 , Do (Ops.Say (Ref "r"))
                 ]
          >>= (@?= Just (VText "second"))
    ]
  where
    run is = runOut (machineIn emptyGlobals (holeAt type1) is)

    envAfter is = pure $ case run is of
      Left _  -> Nothing
      Right m -> lookup "r" (Thena.Engine.env (exec m))

    -- 'Right' carries the messages, so a test can say /it got to the end/
    -- without saying what the development looks like.
    ranWith is = pure $ case run is of
      Left r  -> Left r
      Right _ -> Right ([] :: [String])

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
      , ("intro",       e, guessAt (arrow type0 type0), [], Ops.IntroPi Nothing)
      , ("try",         e, hole,    [],            Ops.Try (term type0))
      , ("regret",      e, hole,    tried,         Ops.Regret)
      , ("solve",       e, hole,    tried,         Ops.Solve)
      , ("abandon",     e, twoHoles, [],           Ops.Abandon)
        -- Phase 17b's four. **They part company at MS5 phase 63**: a @prove@
        -- still produces nothing, because what the chosen rule did is in the
        -- development, while a @call@ produces whatever the clause that ran
        -- handed back with @return@. So the call here is to 'returningRule',
        -- which does exactly that and nothing else.
      , ("prim-prove",  e, hole,    [],            Ops.Prove)
      , ("call",        e, hole,    [],            Ops.Call (GlobalName "gives") [])
        -- **A λ** (MS4 phase 49b): every other shape this op once handled is a
        -- clause of @elaborate@ now, and it refuses those — so the term has to
        -- be one of the three cases still behind it, and a λ is the one that
        -- needs no globals. The goal is an arrow so @prim-intro@ has a binder
        -- to take.
        -- **The spine walk\'s vocabulary** (MS4 phase 49f). @apply-next@ needs a
        -- head whose type is a Π and a name in scope, so it uses @nat@ like the
        -- row that stood here before it; the three accessors only read the
        -- surface term they are handed.
      , ("expand-implicits", nat, holeAt natType, [], Ops.ExpandImplicits succZero)
      , ("app-head",         e,   hole, [],           Ops.AppHead succZero)
      , ("app-first-argument", e, hole, [],           Ops.AppFirstArgument succZero)
      , ("app-tail",         e,   hole, [],           Ops.AppTail succZero)
        -- The data structures (MS5 phase 65). A list and a pair are built by the
        -- operand itself, so what is exercised here is the option's two
        -- constructors and the five accessors.
      , ("some",         e, hole, [],            Ops.Some (text "x"))
      , ("none",         e, hole, [],            Ops.None)
      , ("list-head",    e, hole, [],            Ops.ListHead (ListOf [text "x"]))
      , ("list-tail",    e, hole, [],            Ops.ListTail (ListOf [text "x"]))
      , ("pair-first",   e, hole, [],            Ops.PairFirst (PairOf (text "x") (text "y")))
      , ("pair-second",  e, hole, [],            Ops.PairSecond (PairOf (text "x") (text "y")))
      , ("option-value", e, hole, [Bind "o" (Ops.Some (text "x"))],
           Ops.OptionValue (Ref "o"))
      , ("apply-next",       nat, holeAt natType, [],
           Ops.ApplyNext (term (Global (GlobalName "succ") [])) (text "a"))
      ]

    -- @succ zero@, as a focused surface term.
    succZero =
      Lit (VSurface (rootedAt
        (SurfaceApp (SurfaceName "succ")
           (SurfaceArg Explicit (SurfaceName "zero") NE.:| []))))

    -- @try ‹t›@, as 'expectedBase' ships it — what @call@ needs something to
    -- call.

checkProduces :: GlobalEnv -> Cursor -> [Instr] -> Op -> IO ()
checkProduces globalEnv cur before o =
  case runOut (machineIn globalEnv cur (before ++ [Bind "r" o])) of
    Left r  -> assertFailure ("the op did not run: " ++ show r)
    Right m -> do
      let got = lookup "r" (Thena.Engine.env (exec m))
      (got /= Nothing) @?= produces o
      -- **And the value is of the type the table says** (MS5 phase 66b). The
      -- presence check above is what 'produces' was; this is the rest of
      -- 'Thena.Ops.resultOf', aimed at the same authority — the engine — rather
      -- than at another table. A signature that claims @Surface@ for an op that
      -- hands back a term fails here.
      case (got, sigResult (signatureOf o)) of
        (Just v, Just ty) | not (v `inhabits` ty) ->
          assertFailure (renderTy ty ++ " was claimed, but the engine produced " ++ show v)
        _ -> pure ()

-- | Does this value belong to that type?
--
-- **Test-local on purpose.** It is a statement about what a type /means at run
-- time/, and putting it in @src\/@ would invite it being used as a dynamic
-- check — which is the thing the type system is being built to replace. Here it
-- is a measuring device and nothing else.
--
-- **A 'VText' inhabits both 'TString' and 'TName'**, because at run time they
-- are the same value; the distinction is static, which is the whole of his
-- 2026-09-12 ruling. Same for 'TCore' and an unresolved @core`…`@.
inhabits :: Value -> Ty -> Bool
inhabits v t = case (v, t) of
  (VText _,    TString) -> True
  (VText _,    TName)   -> True
  (VTerm _,    TCore)   -> True
  (VRaw _,     TCore)   -> True
  (VSurface _, TSurface) -> True
  (VInt _,     TInt)    -> True
  (VChar _,    TChar)   -> True
  (VBool _,    TBool)   -> True
  (VList vs,   TList a) -> all (`inhabits` a) vs
  (VPair a b,  TPair x y) -> inhabits a x && inhabits b y
  (VOption Nothing,  TOption _) -> True
  (VOption (Just u), TOption a) -> inhabits u a
  -- A scheme variable is satisfied by anything; what it is bound to is
  -- inference's question and not this one's.
  (_,          TVar _)  -> True
  _                     -> False

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
term = Lit . VTerm

text :: String -> Operand
text = Lit . VText

-- | A machine at a given state, holding a program. The counter starts well
-- above every 'Var' the fixtures mint, so nothing it mints collides.
machineIn :: GlobalEnv -> Cursor -> [Instr] -> Machine
machineIn env cur is =
  load is (Machine (Exec [] [] []) (Development cur) [] env
                   (expectedBase ++ [returning]) [] 1000)

-- | A base with one rule in it that returns something (MS5 phase 63).
--
-- It is here rather than in @rules/standard.thena.rules@ because the shipped
-- base has nothing that wants a returned value yet, and 'Thena.Standard' has to
-- mirror that file exactly. What needs testing is the /mechanism/ — that a
-- @Bind@ on a call is filled by the callee's @return@ — and one rule says it.
returning :: RuleBase
returning =
  ruleBase "returning" Nothing "" []
    [ returningRule
      -- @return@ ends the body: the @prim-attack@ after it must not run, which
      -- is what makes this rule safe to call at a hole in any state.
    , Rule (GlobalName "runs-on") [] []
        [Do (Ops.Return (Lit (VText "first"))), Do Ops.Attack]
      -- A body with no @return@ at all.
    , Rule (GlobalName "silent") [] [] [Do (Ops.Say (Lit (VText "nothing")))]
      -- Two clauses, one arity. The first fails before it can return — it
      -- cannot fail /after/, because @return@ ends the body — so the value the
      -- caller ends up with is the second clause's.
    , Rule (GlobalName "two-ways") [] []
        [Do Ops.Into, Do (Ops.Return (Lit (VText "first")))]
    , Rule (GlobalName "two-ways") [] []
        [Do (Ops.Return (Lit (VText "second")))]
    ]

-- | @rule gives :- then return \"a value\"@.
returningRule :: Rule
returningRule =
  Rule (GlobalName "gives") [] [] [Do (Ops.Return (Lit (VText "a value")))]

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

-- | Every rule the shipped base offers at a hole, in definition order.
--
-- **@elaborate@ fifteen times** (MS4 phase 49): one clause per surface node,
-- and a test about an argument nobody supplied does not exclude a clause
-- (phase 47), so a listing with no argument shows them all. @spine-arguments@
-- is there for @enter-binders@\' reason — a helper whose head is honest about
-- the focus is offered wherever that focus test passes (@ms4/CLOSEOUT.md@ 27).
everyHoleRule :: [String]
everyHoleRule =
  [ "attack", "try-core", "abandon", "eliminate-core", "prove", "fill"
  , "unify-refine-core", "apply-core"
    -- The asking half of the three component tactics (MS5 phase 62b). They
    -- have no head, because all three apply wherever there is a focus, so they
    -- are offered everywhere — which is what @:matches@ is for. @dispatch@
    -- runs none of them: they take a parameter.
  , "claim", "assume", "quantify"
  ]
    ++ replicate 16 "elaborate" ++ replicate 2 "enter-binders"
    ++ replicate 2 "spine-arguments"

-- | The λ case's two recursive helpers, which every listing at a guess shows.
--
-- **A test about an argument nobody supplied does not exclude a clause** (phase
-- 47), so a rule whose head only asks about its argument is offered wherever
-- its state test passes — and @intro-binders@ really does apply at a guess.
walkers :: [String]
walkers =
  [ "claim", "assume", "quantify"
  , "intro-binders", "intro-binders", "enter-binders", "enter-binders"
  , "spine-arguments", "spine-arguments"
  ]

-- | @Nat@, as a core term, for the row above.
natType :: Core
natType = Global (GlobalName "Nat") []
