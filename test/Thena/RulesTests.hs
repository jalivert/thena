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
  , Ident (..)
  , Var
  , close
  , fresh
  , nameDotted
  , nameFromText
  , rootName
  , rootScope
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, crossType, enter, into)
import Thena.Development.Partial (Partial (..))
import Thena.Declared (nat, natDecl, opensIn)
import Thena.Standard (aRule, expectedBase)
import Thena.Driver (parseDeclaration)
import Thena.Core.Trust (TrustLevel (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , load
  , resumeAt
  , resumeYield
  , step
  , splicing
  )
import Thena.Errors (FailReason (..))
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition
  , addDefinition
  , emptyGlobals
  )
import Thena.Instral.Ops
  ( AnswerKind (..)
  , CoreP (..)
  , Instr (..)
  , Op
  , Operand (..)
  , Rule (..)
  , Value (..)
  , produces
  , signatureOf
  )
-- §2.5: "Thena.Instral.Ops" is qualified everywhere except "Thena.Engine", because
-- @Assume@ and @Claim@ name both a component and an op.
import qualified Thena.Instral.Ops as Ops
import Thena.Instral.Type (Signature (..), Ty (..), renderTy)
import qualified Data.List.NonEmpty as NE
import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..))
import Thena.Surface.Zipper (rootedAt)
import Thena.Rules
  ( RuleBase
  , RuleError (..)
  , faultWhy
  , clauses
  , RuleIter
  , allRules
  , hasNext
  , iterRules
  , Match (..)
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
    , focusTests
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

-- | The hole inside the guess — where @attack@ now leaves the cursor, and the
-- only position the introduction tactics act at (MS12 phase 357).
readyAt :: Core -> Cursor
readyAt ty = case into (guessAt ty) of
  Right cur -> cur
  Left e    -> error ("could not enter the guess: " ++ show e)

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
    (rootName "Arrow")
    (MkDefinition [] [] type1 (arrow type0 type0))
    emptyGlobals

matching :: GlobalEnv -> Cursor -> [String]
matching env cur = map nameOf (drain (matches expectedBase env 0 cur))

nameOf :: Rule -> String
nameOf = nameDotted . ruleName

-- | Walk an iterator to the end with 'next' alone, which is how the driver's
-- display walks it.
drain :: RuleIter -> [Rule]
drain = iterRules

-- | The same walk, keeping what each match bound (MS12).
--
-- **It is told the counter to walk from**, because 'next' matches the clause
-- again from whatever it is handed (MS12, @~thwhg@) — so walking an iterator
-- built at 9 from 0 would answer matches nothing ever made.
-- **And the cursor to match the focus against** (MS12 phase 358): the head
-- includes the @at@ pattern, so re-making a match re-matches that too.
drainMatches :: Int -> Cursor -> RuleIter -> [Match]
drainMatches k cur it = case next emptyGlobals k cur it of
  Nothing         -> []
  Just (mt, rest) -> mt : drainMatches k cur rest

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
          @?= ["rename", "solve", "regret", "step", "step", "step"] ++ walkers

      -- **A guess is no longer where @intro@ is offered** (MS12 phase 357): the
      -- introductions act at the hole inside it, so what a guess offers is the
      -- two tactics that act on a guess.
    , testCase "a guess at a Π offers solve and regret, and not intro" $
        matching emptyGlobals (guessAt (arrow type0 type0))
          @?= ["rename", "solve", "regret", "step", "step", "step"] ++ walkers

      -- **Two @intro@ rows, not one** (MS12 phase 326): the nullary pair and the
      -- @intro "a"@ pair his ask of 2026-11-20 added. A row per name and arity,
      -- and every matching rule is always offered.
    , testCase "the hole inside a guess at a Π offers intro" $
        matching emptyGlobals (readyAt (arrow type0 type0)) @?= holeRulesWithIntro

      -- §8: "Head matching runs whnf. A goal typed @id Type (Nat → Nat)@ is a Π
      -- and must match GoalTypeIsPi." Written down, @Arrow@ is a 'Global' and
      -- not a 'Pi'; a head that did not reduce would miss it.
    , testCase "a goal type that only reduces to a Π still matches" $
        matching withArrow (readyAt (Global (rootName "Arrow") []))
          @?= holeRulesWithIntro

    , testCase "and does not, in an environment where it does not unfold" $
        matching emptyGlobals (readyAt (Global (rootName "Arrow") []))
          @?= everyHoleRule

      -- The one test that must NOT reduce: whnf δ-reduces a term-level let
      -- away (§5.1), so asking about the reduced type would make GoalTypeIsLet
      -- unpassable — which is exactly the bug this phase found in
      -- 'Thena.Engine.introduce'.
    , testCase "a goal type written as a let offers intro" $
        matching emptyGlobals (readyAt (Let (Ident "x") type0 type1 (close var type0)))
          @?= holeRulesWithIntro

      -- The invariant checked by different code from the code that maintains
      -- it: the head says @intro@ applies, so @intro@ must actually apply. It
      -- is the direction that /is/ guaranteed for these two rules, and the one
      -- the let bug broke — the op could not do what no head could offer.
    , testCase "where the let clause is offered, intro succeeds" $
        let cur = readyAt (Let (Ident "x") type0 type1 (close var type0))
         in do
              nameOf `map` drain (matches expectedBase emptyGlobals 0 cur)
                @?= holeRulesWithIntro
              ranOk (machineAt cur [Do (Ops.IntroLet Nothing)])

    , testCase "where the Π clause is offered, intro succeeds" $
        ranOk (machineAt (readyAt (arrow type0 type0)) [Do (Ops.IntroPi Nothing)])

      -- **THE COST OF THE HEAD BEING @focus-is-hole@** (MS12 phase 357). The
      -- root of a development has the thesis's @?x : S . x@ shape too, so the
      -- head passes there and the op refuses: a binder put at the root would
      -- change what the development proves, which is what @attack@ is for.
      -- Offered and refused, rather than not offered — §7.3's "failing in a
      -- body is already handled".
    , testCase "and at a hole that is not inside a guess it is offered, then refuses" $
        do
          matching emptyGlobals (holeAt (arrow type0 type0)) @?= holeRulesWithIntro
          case runOut (machineAt (holeAt (arrow type0 type0))
                                 [Do (Ops.IntroPi Nothing)]) of
            Left NotReadyToIntroduce -> pure ()
            other -> assertFailure ("expected a refusal, got " ++ show other)

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
          Right cur -> matching emptyGlobals cur
                         @?= ["claim", "assume", "quantify"]
                               ++ splitHelpers ++ ["run-block"]

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
        let walk it = case next emptyGlobals 0 (holeAt type0) it of
              Nothing        -> hasNext it @?= False
              Just (_, rest) -> (hasNext it @?= True) >> walk rest
         in walk (matches expectedBase emptyGlobals 0 (holeAt type0))

      -- **Drained by name rather than by a count**, since MS4 phase 49c: a guess
      -- offers @solve@, @regret@, @prove@ and the λ case's two recursive
      -- helpers, and a fixed number of @next@es would have to move every time a
      -- rule is added.
    , testCase "an empty iterator has nothing" $
        let it = matches expectedBase emptyGlobals 0 (guessAt type0)
         in case drop (length (["rename", "solve", "regret", "step", "step", "step"] ++ walkers)) (drain it) of
              [] -> pure ()
              rs -> assertFailure ("expected no more, got " ++ show (map nameOf rs))

      -- §7.6: persistent, "a frame holds one and the UI may hold the same one;
      -- if advancing mutated shared state they would interfere." A lazy list
      -- gives this outright; the test is here because the requirement is on the
      -- type, and a later representation could quietly lose it.
    , testCase "advancing one copy does not disturb another" $
        let it = matches expectedBase emptyGlobals 0 (holeAt type0)
            deep = drop 2 (drain it)
         in do
              _ <- pure deep
              map nameOf (drain it) @?= everyHoleRule
              map nameOf deep @?= drop 2 everyHoleRule
    ]

-- --------------------------------------------------------------------------
-- Well-formedness (§2.4, §7.2)
-- --------------------------------------------------------------------------

-- **Its parameters are still written as names** (MS5 phase 82): every rule
-- built here asks a question about /bindings/ and not about patterns, so the
-- helper turns each name into the pattern that binds it and the fixtures below
-- read exactly as they did.
named :: String -> [Name'] -> [Instr] -> Rule
named n ps = aRule (rootName n) (map Ops.PVar ps) []

-- | What 'validate' found, without the place it found it at (MS12 phase 349).
--
-- Every rule here is built by hand and so is in no file ('Thena.Instral.Ops.ruleOrigin'
-- is 'Nothing'); what these cases are about is which fault, and the crossing of
-- a fault against a real file's lines is "Thena.ViewTests"'.
whys :: Rule -> [RuleError]
whys = map faultWhy . validate

type Name' = String

validateTests :: TestTree
validateTests =
  testGroup
    "validate"
    [ testCase "the shipped base is clean" $
        concatMap validateBase expectedBase @?= []

      -- **@true@ and @false@ are values, so they cannot also be names** (MS5
      -- phase 64). Every @Ref@ to one has already become a literal by the time
      -- a rule is built, so a binding of either name could never be read back —
      -- a rule that quietly does something other than it says, which is what a
      -- load-time refusal is for.
      -- **A PARAMETER cannot reach this check since MS5 phase 82.**
      -- 'Thena.Rules.resolvePattern' reads @true@ in a parameter position as
      -- the boolean /pattern/, so the name never exists to be refused and the
      -- case that used to stand here would assert nothing. What replaces it is
      -- in "Thena" "PatternTests", where there is a parser to write the source
      -- line with — recorded here so the disappearance is deliberate rather
      -- than a check quietly lost.
    , testCase "nor a binding false" $
        whys (named "r" [] [Bind (Ops.PVar "false") Nothing Ops.Here])
          @?= [ReservedName (rootName "r") "false"]
    , testCase "and an ordinary name is untouched" $
        validate (named "r" ["t"] [Bind (Ops.PVar "x") Nothing Ops.Here]) @?= []

      -- §3.7's line, made structural: a declaration is a command, not a
      -- rule-body operation.
    , testCase "define-data in a body is rejected" $
        whys (named "bad" [] [Do (Ops.DefineData someData)])
          @?= [DeclarationInBody (rootName "bad") 0]

    , testCase "binding an op that produces nothing is rejected" $
        whys (named "bad" [] [Bind (Ops.PVar "x") Nothing Ops.Attack])
          @?= [BoundNonProducing (rootName "bad") 0 "x"]

    , testCase "binding an op that produces something is fine" $
        validate (named "ok" [] [Bind (Ops.PVar "x") Nothing (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))])
          @?= []

    , testCase "a Ref to nothing is rejected" $
        whys (named "bad" [] [Do (Ops.Say (Ref "z"))])
          @?= [UnboundInRule (rootName "bad") 0 "z" TString]

    , testCase "a parameter binds it" $
        validate (named "ok" ["z"] [Do (Ops.Say (Ref "z"))]) @?= []

    , testCase "an earlier Bind binds it" $
        validate
          (named "ok" []
            [ Bind (Ops.PVar "z") Nothing (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))
            , Do (Ops.Say (Ref "z"))
            ])
          @?= []

      -- A later Bind does not: the environment is built as the body runs.
    , testCase "a later Bind does not" $
        whys
          (named "bad" []
            [ Do (Ops.Say (Ref "z"))
            , Bind (Ops.PVar "z") Nothing (Ops.Concat (Lit (VText "a")) (Lit (VText "b")))
            ])
          @?= [UnboundInRule (rootName "bad") 0 "z" TString]

      -- Every error, not the first: a rule author fixing one at a time would
      -- reload once per mistake.
    , testCase "all three are reported, with their positions" $
        whys
          (named "bad" []
            [ Bind (Ops.PVar "x") Nothing Ops.Attack
            , Do (Ops.DefineData someData)
            , Do (Ops.Say (Ref "z"))
            ])
          @?= [ BoundNonProducing (rootName "bad") 0 "x"
              , DeclarationInBody (rootName "bad") 1
              , UnboundInRule (rootName "bad") 2 "z" TString
              ]

    , testCase "validateBase checks every rule" $
        length (validateBase (ruleBase "test" Nothing "" [] []
                                [ named "a" [] [Bind (Ops.PVar "x") Nothing Ops.Attack]
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
        valueOf [Bind (Ops.PVar "x") Nothing (Ops.Concat (text "a") (text "b"))]
                (Ops.Some (ListOf [Ref "x", text "c"]))
          >>= (@?= Just (VOption (Just (VList [VText "ab", VText "c"]))))

      -- **Observed by destructuring** (MS5 phase 86) — @pair-first@ used to do
      -- this and is gone, because a binding's left side takes the pair apart.
    , testCase "and a pair the same way" $
        valueOf [Bind (Ops.PPair (Ops.PVar "a") (Ops.PVar "b")) Nothing
                      (Ops.Value (PairOf (text "a") (Lit (VInt 1))))]
                (Ops.Value (Ref "a"))
          >>= (@?= Just (VText "a"))

    , -- An unbound name inside a literal is the body's mistake and is caught
      -- when the base loads, which needs 'Thena.Instral.Ops.refsIn' to look inside.
      testCase "an unbound name inside a list is refused at load" $
        whys (named "r" [] [Do (Ops.Say (ListOf [Ref "nope"]))])
          @?= [UnboundInRule (rootName "r") 0 "nope" TString]

      -- **The five destructors are gone** (MS5 phase 86): @list-head@,
      -- @list-tail@, @pair-first@, @pair-second@ and @option-value@. What they
      -- did is a pattern now — the pair above, and
      -- @Thena.RuleFileTests.walking@ for the list and option ones, which is
      -- where the two-clause replacements for the list pair are written out and
      -- run. Nothing that was asserted here stopped being asserted; it moved to
      -- where the replacement lives.

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

    , -- **The environment the match built rides out with the clause** (MS12,
      -- §8's /the environment a match built is carried, never recomputed/).
      -- 'Thena.Rules.clauses' has to match to choose a clause at all, and it
      -- used to answer the clause alone — leaving "Thena.Engine" to run the
      -- same match a second time on entry and a third in @seedFor@. This is
      -- the answer being kept, which is what makes the body's environment and
      -- the clause's choice one event instead of two.
      testCase "the iterator carries what the match bound" $
        envFor [VList [VText "a", VText "b"]]
          @?= [[("x", VText "a"), ("xs", VList [VText "b"])]]
    , -- A clause whose patterns bind nothing is not a missing environment: it
      -- is matching no names, which answers none.
      testCase "and a clause that binds nothing carries an empty one" $
        envFor [VList []] @?= [[]]
    , -- **The name counter rides out with the candidate too** (MS12, §8). A
      -- list pattern mints nothing, so this candidate reports the counter the
      -- search was handed, unchanged.
      testCase "and the counter the search was handed rides out with it" $
        namesFor 9 [VList [VText "a", VText "b"]] @?= [9]

    , -- **NO TWO CANDIDATES OF ONE FORK HAND OUT ONE TOKEN** (MS12, @~thwhg@),
      -- which the binder patterns of MS12 phase 355 are what make visible: a
      -- core binder pattern opens a scope, so each candidate mints, and each is
      -- taken from the counter as it stands then. Entered in turn from 9, the
      -- two open at 9 and at 10.
      --
      -- **It is the re-match and not the candidate list that makes this true.**
      -- 'Thena.Rules.clauses' also runs the counter along its candidates, but
      -- nothing reads those stored counters: 'next' re-makes every match from
      -- the counter it is handed, and 'RuleIter' exports no field, so the
      -- threading in 'clauses' is only what the fallback in 'remade' answers
      -- with when a re-match fails. That is the shape his ruling of 2026-11-26
      -- chose and @~thwhg@'s definition records it.
      testCase "two candidates of one fork open at different tokens" $
        openedAt 9 (peeling 9 [VTerm aPi])
          @?= [ VTerm (Free (fst (fresh 9)))
              , VTerm (Free (fst (fresh 10)))
              ]

    , -- **AND THE RE-MATCH DRAWS A DIFFERENT TOKEN**, which is the other half
      -- of @~thwhg@ made visible: the fork drew at 9 and the alternative is
      -- entered at 60, so the body it binds is opened at 60. The abandoned
      -- branch's spent tokens are never re-drawn.
      testCase "an alternative taken later is opened at a later token" $
        fmap (lookup "e" . matchEnv . fst)
             (next emptyGlobals 60 (holeAt type1) (peeling 9 [VTerm aPi]))
          @?= Just (Just (VTerm (Free (fst (fresh 60)))))

    , -- **AN ALTERNATIVE IS MATCHED AGAIN WHEN IT IS TAKEN** (MS12, @~thwhg@,
      -- his ruling of 2026-11-26). The match made at the fork is what says the
      -- clause is a candidate at all — 'hasNext' decides @Choice@ against
      -- @Call@ and cannot answer without it — but the counter does not go
      -- backwards (§7.4), so by the time backtracking reaches an alternative
      -- the abandoned branch has minted past everything the fork drew. The
      -- match the body runs with is therefore drawn when the alternative is
      -- taken, not when the fork was made.
      --
      -- **Nothing mints in a pattern yet**, so what is observable is the
      -- counter the match answers: built at 9, taken at 60, it answers 60.
      -- §8's binder patterns are what make this show up as a token.
      testCase "an alternative is matched from the counter it is taken at" $
        fmap (matchNames . fst)
             (next emptyGlobals 60 (holeAt type1)
                   (splitting 9 [VList [VText "a", VText "b"]]))
          @?= Just 60

    , -- And it is the same clause bound the same way: re-matching re-draws the
      -- tokens and changes nothing else.
      testCase "and it binds what it bound at the fork" $
        fmap (matchEnv . fst)
             (next emptyGlobals 60 (holeAt type1)
                   (splitting 9 [VList [VText "a", VText "b"]]))
          @?= Just [("x", VText "a"), ("xs", VList [VText "b"])]
    ]
  where
    run is = runOut (machineIn emptyGlobals (holeAt type1) is)

    valueOf before o = pure $ case run (before ++ [Bind (Ops.PVar "r") Nothing o]) of
      Left _  -> Nothing
      Right m -> lookup "r" (Thena.Engine.env (exec m))

    -- Two clauses of one name, told apart by the shape of the argument.
    --
    -- **By their PARAMETER PATTERNS since MS5 phase 86**, where they used to be
    -- told apart by the head tests @list-is-empty@ and @list-is-cons@. The
    -- clause 'Thena.Rules.clauses' picks is the same one; what changed is that
    -- the shape question is asked where the argument is named, and binds its
    -- pieces while it is there.
    shapes =
      ruleBase "shapes" Nothing "" [] []
        [ aRule (rootName "shape") [Ops.PList [] Nothing] []
            [Do (Ops.Say (Lit (VText "empty")))]
        , aRule (rootName "shape") [Ops.PList [Ops.PWild] (Just Ops.PWild)] []
            [Do (Ops.Say (Lit (VText "cons")))]
        ]

    clauseFor vs =
      [ w
      | r <- drain (clauses [shapes] emptyGlobals 0 (holeAt type1)
                            (rootName "shape") vs)
      , Do (Ops.Say (Lit (VText w))) <- ruleBody r
      ]

    -- The same two clauses with patterns that BIND, so that what the match
    -- answered can be looked at and not only which clause it chose.
    binders =
      ruleBase "binders" Nothing "" [] []
        [ aRule (rootName "split") [Ops.PList [] Nothing] []
            [Do (Ops.Say (Lit (VText "empty")))]
        , aRule (rootName "split")
                [Ops.PList [Ops.PVar "x"] (Just (Ops.PVar "xs"))] []
            [Do (Ops.Say (Lit (VText "cons")))]
        ]

    envFor = map matchEnv . matchesFor 0

    namesFor k vs = map matchNames (matchesFor k vs)

    matchesFor k vs =
      drainMatches k (holeAt type1)
                     (clauses [binders] emptyGlobals k (holeAt type1)
                              (rootName "split") vs)

    splitting k vs =
      clauses [binders] emptyGlobals k (holeAt type1) (rootName "split") vs

    -- **Two clauses that both match and both MINT** — a core binder pattern
    -- opens a scope, and opening one is where a pattern spends the counter.
    peelers =
      ruleBase "peelers" Nothing "" [] []
        [ aRule (rootName "peel")
                [Ops.PCore (CPPi Ops.PWild (CPHole Ops.PWild)
                                 (CPHole (Ops.PVar "e")))] []
            [Do (Ops.Say (Lit (VText "first")))]
        , aRule (rootName "peel")
                [Ops.PCore (CPPi Ops.PWild (CPHole Ops.PWild)
                                 (CPHole (Ops.PVar "e")))] []
            [Do (Ops.Say (Lit (VText "second")))]
        ]

    peeling k vs =
      clauses [peelers] emptyGlobals k (holeAt type1) (rootName "peel") vs

    -- Each candidate taken from the counter as it stands then — the engine's
    -- own sequence, where a body minting is what moves the counter on and
    -- @peel@'s body mints nothing, so only the matches do.
    openedAt k it = case next emptyGlobals k (holeAt type1) it of
      Nothing         -> []
      Just (mt, rest) ->
        [ v | Just v <- [lookup "e" (matchEnv mt)] ]
          ++ openedAt (matchNames mt) rest

    -- @∀ (A : Type₁) -> A@, whose body mentions the binder, so what the match
    -- opened it at is what the @${e}@ holds.
    aPi = Pi (Ident "A") type1 (close hidden (Free hidden))
      where hidden = fst (fresh 99)

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
        envAfter [Bind (Ops.PVar "r") Nothing (Ops.Call "gives" [])]
          >>= (@?= Just (VText "a value"))

    , -- @return@ ends the body, so the @say@ after it never runs. Checked
      -- through the binding rather than through the message, because a body
      -- that ran on would still return the same value.
      testCase "return ends the body" $
        ranWith [Do (Ops.Call "runs-on" [])]
          >>= (@?= Right [])

    , testCase "a body that never returns fails where the value was wanted" $
        ranWith [Bind (Ops.PVar "r") Nothing (Ops.Call "silent" [])]
          >>= (@?= Left (NothingReturned (Ops.PVar "r")))

    , -- The same rule called for effect is fine: nothing asked it for a value.
      testCase "and is fine when nothing asked it for one" $
        ranWith [Do (Ops.Call "silent" [])]
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
        envAfter [ Bind (Ops.PVar "r") Nothing (Ops.Call "two-ways" [])
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
-- 'Thena.Instral.Ops.produces' is a table, and a table agrees with itself. What decides
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
      , ("intro",       e, readyAt (arrow type0 type0), [], Ops.IntroPi Nothing)
      , ("try",         e, hole,    [],            Ops.Try (term type0))
      , ("regret",      e, hole,    tried,         Ops.Regret)
      , ("solve",       e, hole,    tried,         Ops.Solve)
      , ("abandon",     e, twoHoles, [],           Ops.Abandon)
        -- Phase 17b's four. **They part company at MS5 phase 63**: a @prove@
        -- still produces nothing, because what the chosen rule did is in the
        -- development, while a @call@ produces whatever the clause that ran
        -- handed back with @return@. So the call here is to 'returningRule',
        -- which does exactly that and nothing else.
      , ("prim-step",  e, hole,    [],            Ops.Dispatch)
      , ("call",        e, hole,    [],            Ops.Call "gives" [])
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
        -- **Its other half** (MS12 phase 321). The row is a @let@ whose
        -- annotation wrote no brace, which is the case that records nothing and
        -- needs no local in scope — what is crossed here is that it produces
        -- nothing, which is the whole of what this table is about.
      , ("record-implicits", e, hole, [], Ops.RecordImplicits explicitLet)
      , ("app-head",         e,   hole, [],           Ops.AppHead succZero)
      , ("app-first-argument", e, hole, [],           Ops.AppFirstArgument succZero)
      , ("app-tail",         e,   hole, [],           Ops.AppTail succZero)
        -- The data structures (MS5 phase 65). A list and a pair are built by the
        -- operand itself, so what is exercised here is the option's two
        -- constructors and the five accessors.
      -- **A lambda** (MS5 review): its types are inference's, its arity is the
      -- table's, and this is what crosses the second against the engine.
      , ("lambda",       e, hole, [],
           Ops.Lambda [Ops.PVar "x"] [Do (Ops.Return (Ref "x"))])
      , ("some",         e, hole, [],            Ops.Some (text "x"))
      , ("none",         e, hole, [],            Ops.None)
      -- **The five destructors left at MS5 phase 86** and have no rows here any
      -- more — @list-head@, @list-tail@, @pair-first@, @pair-second@,
      -- @option-value@. A pattern is not an op, so it has nothing to cross
      -- against this table; @Thena.PatternTests@ crosses it against the matcher
      -- instead.
      , ("apply-next",       nat, holeAt natType, [],
           Ops.ApplyNext (term (Global (nameFromText "Nat.succ") [])) (text "a"))
      ]

    -- @let x : Type\8320 = Type\8320 in x@, as a focused surface term: an
    -- annotated @let@ with no brace in it (MS12 phase 321).
    explicitLet =
      Lit (VSurface (rootedAt
        (SurfaceLet "x" (Just (SurfaceUniverse 0)) (SurfaceUniverse 0)
                    (SurfaceName [] "x"))))

    -- @succ zero@, as a focused surface term.
    succZero =
      Lit (VSurface (rootedAt
        (SurfaceApp (SurfaceName [] "succ")
           (SurfaceArg Explicit (SurfaceName [] "zero") NE.:| []))))

    -- @try ‹t›@, as 'expectedBase' ships it — what @call@ needs something to
    -- call.

checkProduces :: GlobalEnv -> Cursor -> [Instr] -> Op -> IO ()
checkProduces globalEnv cur before o =
  case runOut (machineIn globalEnv cur (before ++ [Bind (Ops.PVar "r") Nothing o])) of
    Left r  -> assertFailure ("the op did not run: " ++ show r)
    Right m -> do
      let e   = Thena.Engine.env (exec m)
          got = lookup "r" e
      (got /= Nothing) @?= produces o
      -- **And the value is of the type the table says** (MS5 phase 66b). The
      -- presence check above is what 'produces' was; this is the rest of
      -- 'Thena.Instral.Ops.resultOf', aimed at the same authority — the engine — rather
      -- than at another table. A signature that claims @Surface@ for an op that
      -- hands back a term fails here.
      -- **The scheme's variables are bound from the operands' actual values
      -- first** (MS5 review). Without this a row whose result is a variable
      -- asserts nothing at all — @(_, TVar _) -> True@ — which is how
      -- @list-head : List a -> a@ survived while the engine answered with an
      -- @Option@. Binding @a@ from the argument makes the claim checkable.
      let bound = foldl bindStep (Just []) (Ops.operandTypes o)
          bindStep acc (op, ty) = acc >>= \b -> case Ops.operandIn e op of
            Left _  -> Just b
            Right v -> bindFrom b v ty
      case (got, sigResult (signatureOf o), bound) of
        (Just v, Just ty, Just b) | not (v `inhabits` substituteTy b ty) ->
          assertFailure (renderTy (substituteTy b ty)
                          ++ " was claimed, but the engine produced " ++ show v)
        (Just v, Just ty, Nothing) | not (v `inhabits` ty) ->
          assertFailure (renderTy ty ++ " was claimed, but the engine produced " ++ show v)
        _ -> pure ()

-- | What a scheme's variables stand for, read off the values an op was given
-- (MS5 review).
--
-- **A 'VText' binds a variable to 'TString'**, and 'inhabits' accepts a 'VText'
-- at either 'TString' or 'TName', so the text ops are not made stricter than
-- they are.
bindFrom :: [(Int, Ty)] -> Value -> Ty -> Maybe [(Int, Ty)]
bindFrom b v ty = case (ty, v) of
  (TVar i, _) -> case lookup i b of
    Just _  -> Just b
    Nothing -> fmap (\t -> (i, t) : b) (principal v)
  (TList a,   VList (u : _))       -> bindFrom b u a
  (TList _,   VList [])            -> Just b
  (TOption a, VOption (Just u))    -> bindFrom b u a
  (TOption _, VOption Nothing)     -> Just b
  (TPair x y, VPair u w)           -> bindFrom b u x >>= \b' -> bindFrom b' w y
  _                                -> Just b

-- | A value's own type, where it has exactly one.
principal :: Value -> Maybe Ty
principal v = case v of
  VText _    -> Just TString
  VInt _     -> Just TInt
  VChar _    -> Just TChar
  VBool _    -> Just TBool
  VTerm _    -> Just TCore
  VRaw _     -> Just TCore
  VSurface _ -> Just TSurface
  _          -> Nothing

substituteTy :: [(Int, Ty)] -> Ty -> Ty
substituteTy b ty = case ty of
  TVar i    -> maybe ty id (lookup i b)
  TList a   -> TList (substituteTy b a)
  TOption a -> TOption (substituteTy b a)
  TPair x y -> TPair (substituteTy b x) (substituteTy b y)
  TFun as r -> TFun (map (substituteTy b) as) (substituteTy b r)
  _         -> ty

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
  -- **A closure's arity is checkable even when its types are not** (MS5 review).
  (VClosure ps _ _, TFun as _) -> length ps == length as
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
someData = case parseDeclaration [] emptyGlobals (opensIn emptyGlobals) 200 natDecl of
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
  load is (Machine (Exec [] [] [] []) (Development cur) [] env
                   (expectedBase ++ [returning]) [] [] [] [] rootScope 1000 [] 0 NoUndischargeableTrust)

-- | A base with one rule in it that returns something (MS5 phase 63).
--
-- It is here rather than in @rules/standard.thena.rules@ because the shipped
-- base has nothing that wants a returned value yet, and 'Thena.Standard' has to
-- mirror that file exactly. What needs testing is the /mechanism/ — that a
-- @Bind@ on a call is filled by the callee's @return@ — and one rule says it.
returning :: RuleBase
returning =
  ruleBase "returning" Nothing "" [] []
    [ returningRule
      -- @return@ ends the body: the @prim-attack@ after it must not run, which
      -- is what makes this rule safe to call at a hole in any state.
    , aRule (rootName "runs-on") [] []
        [Do (Ops.Return (Lit (VText "first"))), Do Ops.Attack]
      -- A body with no @return@ at all.
    , aRule (rootName "silent") [] [] [Do (Ops.Say (Lit (VText "nothing")))]
      -- Two clauses, one arity. The first fails before it can return — it
      -- cannot fail /after/, because @return@ ends the body — so the value the
      -- caller ends up with is the second clause's.
    , aRule (rootName "two-ways") [] []
        [Do Ops.Into, Do (Ops.Return (Lit (VText "first")))]
    , aRule (rootName "two-ways") [] []
        [Do (Ops.Return (Lit (VText "second")))]
    ]

-- | @rule gives :- do return \"a value\"@.
returningRule :: Rule
returningRule =
  aRule (rootName "gives") [] [] [Do (Ops.Return (Lit (VText "a value")))]

machineAt :: Cursor -> [Instr] -> Machine
machineAt = machineIn emptyGlobals

-- | Run to the end, following every channel the driver follows. 'Asking' is
-- answered, because that is the only way an @Ops.Ask@'s destination is ever filled
-- (§7.5) — the whole point of 'produces' saying @True@ for it.
runOut :: Machine -> Either FailReason Machine
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying _ m'       -> runOut m'
  Declaring _ _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Primitively _ _ m' -> runOut m'
  DeclaringGrammar _ m' -> runOut m'
  -- A block the driver would have typed; the harness splices and runs it.
  Playing is m' -> runOut (splicing is m')
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
-- **@elaborate@ once per surface node** (MS4 phase 49), and a test about an
-- argument nobody supplied does not exclude a clause (phase 47), so a listing
-- with no argument shows them all. @spine-arguments@ is there for
-- @enter-binders@\' reason — a helper whose head is honest about the focus is
-- offered wherever that focus test passes (@ms4/CLOSEOUT.md@ 27).
--
-- **The counts live in the 'replicate's and are deliberately not restated
-- here**: this comment said /fifteen/ against an assertion of sixteen until MS2
-- phase 27, which found the same rot in 'Thena.ElaborateTests' the same hour.
--
-- **@fit-core@ is two clauses and both heads pass** (MS2 phase 27) — the choice
-- point between them is what makes it a search rather than a loop.
everyHoleRule :: [String]
everyHoleRule =
    -- **@try-in-scope@ asks @focus-is-hole@ and nothing else** (MS12), so it is
    -- offered at every hole and at no guess. **It is first, ABOVE @attack@**
    -- (his instruction of 2026-11-23): @attack@ never fails, so below it this
    -- rule was never reached by a bare @prove@. @fit-in-scope@ is the same walk
    -- for a hypothesis that has to be applied, and sits just under it.
  [ "try-in-scope", "fit-in-scope"
  , "attack", "try-core", "abandon"
    -- **@rename@ is offered at every component** (MS12 phase 330): its head is
    -- @focus-is-component@, because a word belongs to a binder and all five
    -- components are one. It is therefore in this list and in every guess
    -- listing below, and only the core fragment loses it.
  , "rename", "eliminate-core"
  , "eliminate-generalising-core", "step", "step", "step", "fill"
  , "unify-refine-core", "apply-core"
  , "fit-core", "fit-core"
    -- The asking half of the three component tactics (MS5 phase 62b). They
    -- have no head, because all three apply wherever there is a focus, so they
    -- are offered everywhere — which is what @:matches@ is for. @dispatch@
    -- runs none of them: they take a parameter.
  , "claim", "assume", "quantify"
  ]
    ++ replicate 7 "elaborate"
    -- **The splitting tree's helpers sit BETWEEN two runs of @elaborate@**,
    -- because that is where the base declares them: written beside the clause
    -- that calls them. **Both clauses of a split are in the second run**, the
    -- arm-less one included: it stopped being a clause of its own when the
    -- specialiser arrived, and now calls @split-elaborate@ like the other.
    ++ splitHelpers
    -- **The two interactive tactics** (MS9 phase 231), which ask only
    -- @focus-is-hole@ and so are offered at every one.
    ++ ["induction-core", "case-core"]
    ++ replicate 15 "elaborate"
    ++ ["run-block"]
    -- **@intro-binders@ asks @focus-is-hole@ as of MS12 phase 357**, with
    -- @intro@ itself: what it walks is the hole the cursor stands on. A test
    -- about an argument nobody supplied does not exclude a clause (phase 47),
    -- so all four are offered — a group or a single binder, written or bare.
    ++ replicate 4 "intro-binders"
    ++ replicate 2 "spine-arguments"

-- | 'everyHoleRule' with the two nullary @intro@ clauses, which a Π or a @let@
-- goal adds (MS12 phase 357). The @intro "a"@ pair takes an argument, so a
-- listing with none does not show it.
--
-- **@intro@ is declared just above @attack@** (MS12 phase 357), and definition
-- order is dispatch order, so that is where the rows appear.
holeRulesWithIntro :: [String]
holeRulesWithIntro = before ++ ["intro", "intro"] ++ after
  where
    (before, after) = span (/= "attack") everyHoleRule

-- | The recursive helpers every listing at a guess shows.
--
-- **A test about an argument nobody supplied does not exclude a clause** (phase
-- 47), so a rule whose head only asks about its argument is offered wherever
-- its state test passes. @intro-binders@ left this list in MS12 phase 357: it
-- asks @focus-is-hole@ now, with @intro@.
walkers :: [String]
walkers =
  ["claim", "assume", "quantify"]
    -- **Before @run-block@, because the base declares them there** — beside the
    -- @elaborate@ clause that calls them rather than with the other helpers.
    ++ splitHelpers
    ++ [ "run-block"
       , "spine-arguments", "spine-arguments"
       ]

-- | The splitting tree's helpers (MS9), in the order the base declares them.
--
-- **Headless, or asking only about an argument**, so every one of them is
-- offered wherever a state test passes — @walkers@' own reason, one phase on.
-- They are a list of their own because both listings above show them and a
-- second copy would be a second thing to remember.
splitHelpers :: [String]
splitHelpers =
  [ "no-nesting"
  , "ihs-for", "ihs-for"
  , "reverse-onto", "reverse-onto"
    -- **@any-of@ is headless like the list helpers either side of it** (MS12),
    -- so it is offered wherever they are — the core fragment included.
  , "any-of", "any-of"
  , "apply-all", "apply-all"
  , "instantiate-with"
  , "name-or-stem", "name-or-stem"
  ]
  ++ replicate 6 "intro-arm-binders"
  ++ ["dotted-position-is-forced"]
  ++ replicate 3 "intro-arm-binders"
  ++
  [ "bind-friendlies", "bind-friendlies"
      , "bind-solved", "bind-solved"
  , "same-length", "same-length"
  , "arm-for", "arm-for", "pick", "pick", "arm-needs-body", "arm-needs-body"
  , "elaborate-arm"
  , "case-needs-an-arm", "case-needs-an-arm"
  , "vanished-case-takes-no-body", "vanished-case-takes-no-body"
  , "case-must-vanish", "case-must-vanish", "one-case", "one-case", "one-case"
  , "arm-must-be-for-this-datatype"
  , "arms-are-for-this-datatype", "arms-are-for-this-datatype"
  , "one-arm-per-constructor"
  , "arm-not-repeated", "arm-not-repeated"
  , "arms-are-distinct", "arms-are-distinct"
  , "split-cases", "split-cases", "split-over"
  , "split-claim", "split-claim", "split-elaborate"
  ]
  -- **The interactive spelling's own helpers** (MS9 phase 231), after
  -- @split-elaborate@ because that is where the base declares them. The two
  -- tactics themselves ask @focus-is-hole@, so they are in 'everyHoleRule' and
  -- not here.
  ++ replicate 4 "argument-patterns"
  ++ ["argument-pattern", "open-case", "open-case"]
  ++ ["split-holes", "split-holes", "split-holes-over"]
  ++ ["with-hypotheses", "with-hypotheses"]
  ++ ["without-hypotheses", "without-hypotheses"]

-- | @Nat@, as a core term, for the row above.
natType :: Core
natType = Global (rootName "Nat") []

-- --------------------------------------------------------------------------
-- The focus as a pattern (MS12 phase 358, `~9j34x`)
-- --------------------------------------------------------------------------

-- | __@at@ filters and binds__ — his framing of 2026-09-14, /@at@ names the
-- subject and the tag names the language/.
--
-- **It replaces the four focus tests**, so what is checked here is what those
-- tests were checked for: the right component and no other, and then the thing
-- a test could not do — the parts of the focus, bound.
focusTests :: TestTree
focusTests =
  testGroup
    "the focus, via at"
    [ -- **One form per component, and each matches its own and nothing else.**
      testCase "a claim pattern matches a claim and not a guess" $
        ( offered (claimPat "h" "s") (holeAt type0)
        , offered (claimPat "h" "s") (guessAt type0)
        ) @?= (True, False)

    , testCase "a guess pattern matches a guess and not a claim" $
        ( offered (guessPat "h" "s") (guessAt type0)
        , offered (guessPat "h" "s") (holeAt type0)
        ) @?= (True, False)

    , testCase "an assumption pattern matches neither" $
        ( offered (assumePat "h" "s") (holeAt type0)
        , offered (assumePat "h" "s") (guessAt type0)
        ) @?= (False, False)

      -- **THE BINDER POSITION BINDS THE COMPONENT'S OWN IDENTITY** — the word
      -- it prints and the variable it is, as the 'Identifier' of @~gr236@. That
      -- is what lets a word read off the focus be handed to an op that takes
      -- one, and it is the thing no focus test could ever answer.
    , testCase "the binder binds the component's word and variable" $
        lookup "h" (bound (claimPat "h" "s") (holeAt type0))
          @?= Just (VIdent (Ops.Identifier (Ident "goal") (Just var)))

    , testCase "and the type position binds the type as written" $
        lookup "s" (bound (claimPat "h" "s") (holeAt type0))
          @?= Just (VTerm type0)

      -- **A core pattern at the type position discriminates**, which is the
      -- whole landing in one line: the head asks what shape the goal is and
      -- names its parts.
    , testCase "a core pattern at the type position matches a Π only" $
        ( offered piPat (holeAt (arrow type0 type0))
        , offered piPat (holeAt type0)
        ) @?= (True, False)

    , testCase "and it binds the parts of that Π" $
        [ v | (n, v) <- bound piPat (holeAt (arrow type0 type0)), n == "T" ]
          @?= [VTerm type0]
    ]
  where
    -- A base holding exactly the clause under test, so what is offered is
    -- either that clause or nothing.
    only cp =
      ruleBase "focus" Nothing "" [] []
        [ (aRule (rootName "r") [] [] [Do Ops.Attack]) { ruleFocus = Just cp } ]

    asked cp cur = matches [only cp] emptyGlobals 0 cur

    offered cp cur = not (null (iterRules (asked cp cur)))

    -- **Through 'next', because 'RuleIter' exports no field** — the bindings a
    -- fork made are nobody's to read until an alternative is taken (@~thwhg@),
    -- which is exactly what this does.
    bound cp cur = case next emptyGlobals 0 cur (asked cp cur) of
      Just (mt, _) -> matchEnv mt
      Nothing      -> []

    claimPat x t  = Ops.CompClaim    (Ops.PVar x) (Ops.PVar t)
    guessPat x t  = Ops.CompGuess    (Ops.PVar x) (Ops.PVar t)
    assumePat x t = Ops.CompAssume   (Ops.PVar x) (Ops.PVar t)

    -- @at ? h : core`∀ (${_} : ${T}) -> ${E}`@.
    piPat =
      Ops.CompClaim (Ops.PVar "h")
        (Ops.PCore (CPPi Ops.PWild
                         (CPHole (Ops.PVar "T"))
                         (CPHole (Ops.PVar "E"))))
