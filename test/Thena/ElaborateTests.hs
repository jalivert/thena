{-# LANGUAGE OverloadedLists #-}

-- | Elaboration (MS4 phase 41), and @Call@ (§8, phase 17b).
--
-- **The partition is gone and so are its tests.** Until this phase a hint split
-- the rule base in two, and this module's first group checked that
-- @:matches@ and @:matches ‹hint›@ were two questions with two answers. There
-- is no hint now: elaboration is a rule called by name, so every rule whose
-- head passes is a candidate and there is one question.
--
-- What is checked here instead:
--
--   * **the elaborator's leaves** — a name, a universe, and the two
--     placeholders — end to end, through the machine;
--   * **that a node it has no case for FAILS**, which is phase 41b's list;
--   * **@Call@** — arity, what binds in the callee, and what survives the
--     return.
module Thena.ElaborateTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Data.List (isInfixOf)
import Test.Tasty.QuickCheck
  (Gen, counterexample, forAll, oneof, property, testProperty, withNumTests)

import Thena.Driver
  ( Loaded (..)
  , Response (..)
  , Session
  , command
  , loadProofSource
  , loadRuleBases
  , loadSource
  , newSession
  , withRuleBases
  )
import Thena.Standard (withRules)

import Thena.Core.Level (Level (..))
import qualified Thena.Core.Term
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Literal (..), Var, fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, enter, focus)
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Core.Trust (TrustLevel (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , load
  , step
  , splicing
  )
import Thena.Errors (FailReason (..), MoveError (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Instral.Ops
  ( Instr (..)
  , Operand (..)
  , Rule (..)
  , Value (..)
  )
import qualified Thena.Instral.Ops as Ops
import Thena.Rules
  ( RuleIter
  , matches
  , next
  )
import Thena.Files (startingSession)
import Thena.Render (renderResponse)
import Thena.Standard (expectedBase)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))
import Thena.Surface.Zipper (rootedAt)

tests :: TestTree
tests =
  testGroup
    "elaboration"
    [ leafTests
    , hereTests
    , constructionTests
    , lambdaTests
    , elimTests
    , unsupportedTests
    , baseTests
    , endToEnd
    , honestRefusals
    , testGroup "taking a split apart (MS9 phase 181)" splitParts
    , testGroup "a split with no arms elaborates (MS9 phase 182)" emptySplit
    ]

-- --------------------------------------------------------------------------
-- The message a wrong argument gets (MS8 phase 170)
-- --------------------------------------------------------------------------

-- | **A wrong argument to a name-headed application reports the real error.**
--
-- The three application clauses of @elaborate@ used to overlap: the binary one
-- asked only that the arguments be explicit, so it matched a name-headed spine
-- too and was tried whenever the name-headed clause failed. It claims
-- @f : A -> B@, which a dependent head does not fit, so against @Eq@ or @refl@
-- it failed on its own claim /before/ re-reaching the argument that was wrong,
-- and that spurious failure was what the user saw — @A2 is not bound before A@,
-- naming development components and nothing they wrote. The real error was
-- computed and thrown away.
--
-- **Two different errors were lost the same way**, which is why both are pinned
-- here: a type mismatch, and a parse error inside an object term literal whose
-- message already named the bracket exactly.
--
-- **A non-dependent head always reported honestly**, because the binary clause
-- re-elaborated the argument and met the same error again — so a test over
-- @Nat -> Nat@ would have passed throughout and is no evidence. The head has to
-- be dependent.
honestRefusals :: TestTree
honestRefusals =
  testGroup
    "a wrong argument to a dependent head reports the real error"
    [ testCase "a false equation names the two sides" $
        failureOf
          [ "a : Eq String \"x\" \"x\""
          , "a = refl String \"y\""
          ]
          >>= (@?= "stuck: \"y\" and \"x\" cannot be made equal")

    , testCase "and so does one over Int" $
        failureOf
          [ "a : Eq Int 1 1"
          , "a = refl Int 2"
          ]
          >>= (@?= "stuck: 2 and 1 cannot be made equal")

    , testCase "a wrong argument further in names the types" $
        failureOf
          [ "a : List String"
          , "a = cons String \"x\" (nil Int)"
          ]
          >>= (@?= "stuck: Int and String cannot be made equal")

      -- **The object-term half, and the message was always right** — it is
      -- reached now instead of being discarded. @Eq@ is the dependent head; the
      -- same literal under a non-dependent one reported this all along.
    , testCase "an unparseable literal under Eq names the bracket" $
        failureOf
          [ "y : Token String"
          , "y = /[a-z]+/"
          , ""
          , "language LC, M, N where"
          , "  var : y as occurrence -> y"
          , "  app                   -> ( M N )"
          , ""
          , "a : Eq LC LC`( f` LC`( f g )`"
          , "a = refl LC LC`( f g )`"
          ]
          >>= (@?= "stuck: in LC`( f`: the term ends too soon, expecting y, ( or [")
    ]
  where
    -- **The session the REPL starts in**, prelude and shipped base loaded, so
    -- @Eq@, @List@ and @refl@ are the ones a user has, and a @language@ block
    -- gets the module layout it needs.
    --
    -- **The last line, and the rest of the response is the level solver's
    -- running commentary** — a page of @solved:@ lines, which is what the
    -- manual warns a declaration at the prompt prints. Whitespace is
    -- normalised because a refusal may wrap: the message is what is pinned,
    -- not its line breaks.
    failureOf ls = do
      (s0, _) <- startingSession
      let src = unlines (["module Wrong where", ""] ++ ls)
          (s1, resp) = loadProofSource s0 src
      pure $ case filter (not . null) (renderResponse s1 resp) of
        [] -> "it loaded, and should not have"
        rs -> unwords (words (last rs))

-- --------------------------------------------------------------------------
-- The whole stack, over generated programs (2026-09-13)
-- --------------------------------------------------------------------------

-- | **Write a program, run it, and let the kernel say whether it worked.**
--
-- Everything else in this file looks at one clause of @elaborate@ and the
-- instructions it emits. This looks at nothing: it writes a well-typed surface
-- program, declares it, and asks only that the load reported no error — which
-- means layout, the surface parser, all sixteen clauses of @elaborate@ in
-- @rules\/standard.thena.rules@, the machine, unification, the level solver and
-- @certify@ all agreed, because a declaration ends in @qed@ and @qed@ certifies.
--
-- **The generator is a second reading of the typing rules**, exactly as
-- @TypingTests@' is, one language up: it builds a term together with the type it
-- must have and never asks the system anything. So a program it writes that
-- does not declare is a defect somewhere in that stack, and the counterexample
-- is the program.
--
-- **Binders are plain.** An annotated λ binder is refused by name (@\\ (x : A) ->@
-- is a development-calculus λ, not a surface one), which is a real fact about
-- the language and not a limit of the generator.
endToEnd :: TestTree
endToEnd =
  testGroup
    "a generated program elaborates and certifies"
    [ testProperty "it declares, which means the kernel accepted it" $
        withNumTests 300 $ forAll genProgram $ \(ty, tm) ->
          counterexample (ty ++ "\n  " ++ tm) $
            case loadedError (declaring ty tm) of
              Nothing -> property True
              Just e  -> counterexample (show e) False

      -- **The harness has to have teeth, and this is what says so.** A property
      -- that only ever sees programs that work cannot tell a working stack from
      -- a load that quietly reports nothing, so the two cases below are the
      -- negative control: they must fail, and they fail in different places —
      -- one in elaboration, one in scope resolution.
    , testCase "a program of the wrong type does not declare" $
        case loadedError (declaring "Nat" "(\\ v0 -> v0)") of
          Just _  -> pure ()
          Nothing -> assertFailure "an ill-typed program declared"
    , testCase "and neither does one naming something that is not there" $
        case loadedError (declaring "Nat" "nonsense") of
          Just _  -> pure ()
          Nothing -> assertFailure "a program with an unbound name declared"
    ]
  where
    declaring ty tm =
      loadSource withRules $ unlines
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , "declare it : " ++ ty ++ " ; it = " ++ tm
        ]

-- | A surface type, and a term of it. Non-dependent, over @Nat@.
genProgram :: Gen (String, String)
genProgram = do
  t <- genSurfaceTy 3
  e <- genSurfaceOf [] t 4
  pure (renderSurfaceTy False t, e)

data SurfaceTy = SNat | SArr SurfaceTy SurfaceTy

genSurfaceTy :: Int -> Gen SurfaceTy
genSurfaceTy n
  | n <= 0 = pure SNat
  | otherwise = oneof [pure SNat, SArr <$> genSurfaceTy (n - 1) <*> genSurfaceTy (n - 1)]

renderSurfaceTy :: Bool -> SurfaceTy -> String
renderSurfaceTy _ SNat = "Nat"
renderSurfaceTy p (SArr a b) =
  wrap p (renderSurfaceTy True a ++ " -> " ++ renderSurfaceTy False b)
  where wrap q x = if q then "(" ++ x ++ ")" else x

sameTy :: SurfaceTy -> SurfaceTy -> Bool
sameTy SNat SNat = True
sameTy (SArr a b) (SArr c d) = sameTy a c && sameTy b d
sameTy _ _ = False

-- | A term of the given type, in a scope of @(name, type)@ pairs.
genSurfaceOf :: [(String, SurfaceTy)] -> SurfaceTy -> Int -> Gen String
genSurfaceOf scope ty n = oneof (variables ++ introduction ++ eliminations)
  where
    variables = [ pure v | (v, t) <- scope, sameTy t ty ]

    introduction = case ty of
      SArr a b ->
        [ do
            let v = "v" ++ show (length scope)
            body <- genSurfaceOf ((v, a) : scope) b (n - 1)
            pure ("(\\ " ++ v ++ " -> " ++ body ++ ")")
        ]
      SNat -> pure "zero" : [ (\t -> "(succ " ++ t ++ ")") <$> genSurfaceOf scope SNat (n - 1) | n > 0 ]

    eliminations
      | n <= 0 = []
      | otherwise =
          [ do
              arg <- genSurfaceOf scope a (n - 1)
              pure ("(" ++ f ++ " " ++ arg ++ ")")
          | (f, SArr a b) <- scope
          , sameTy b ty
          ]
            ++ [ do
                   a    <- genSurfaceTy (n - 1)
                   val  <- genSurfaceOf scope a (n - 1)
                   let v = "v" ++ show (length scope)
                   body <- genSurfaceOf ((v, a) : scope) ty (n - 1)
                   pure ("(let " ++ v ++ " : " ++ renderSurfaceTy False a
                           ++ " = " ++ val ++ " in " ++ body ++ ")")
               ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0 :: Core
type0 = Universe LZero

goalVar, hypVar, hyp2Var :: Var
goalVar = fst (fresh 0)
hypVar  = fst (fresh 1)
hyp2Var = fst (fresh 2)

-- | @λ a : Type₀ . ? goal : Type₀ . goal@, focused on the hole — so there is
-- something in scope at the focus for a surface name to denote (§4.5).
-- | A hole claimed at a type of your own (MS6 phase 97c), shaped exactly like
-- 'hole' so the two differ in nothing but the goal.
holeAt :: Core -> Cursor
holeAt ty = case Cursor.along top of
  Right cur -> cur
  Left e    -> error ("fixture will not move: " ++ show e)
  where
    top =
      enter
        ( Under (Assume hypVar (Ident "a") type0)
            (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
        )

stringType :: Core
stringType = Global (GlobalName "String") []

hole :: Cursor
hole = case Cursor.along top of
  Right cur -> cur
  Left e    -> error ("fixture will not move: " ++ show e)
  where
    top =
      enter
        ( Under (Assume hypVar (Ident "a") type0)
            (Under (Claim goalVar (Ident "goal") type0) (Trailing (Free goalVar)))
        )

runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Primitively _ _ m' -> runOut m'
  DeclaringGrammar _ m' -> runOut m'
  -- A block the driver would have typed; the harness splices and runs it.
  Playing is m' -> runOut (splicing is m')
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> ([], Right m')
  Yielding _ m'     -> ([], Right m')
  Finished m'       -> ([], Right m')
  Stuck r _         -> ([], Left r)

-- | Elaborate one surface term into the fixture's hole.
elaborating :: Surface -> Either FailReason Machine
elaborating = elaboratingAt hole

-- | The same, at a cursor of your own.
--
-- **It calls the rule** (MS4 phase 49). Elaboration is a rule of fifteen
-- clauses and nothing else — there is no op behind it as of phase 49f — so this
-- is the only way in.
elaboratingAt :: Cursor -> Surface -> Either FailReason Machine
elaboratingAt cur s =
  snd (runOut (machineAt cur
        [Do (Ops.Call "elaborate" [Lit (VSurface (rootedAt s))])]))

-- | A machine at a cursor, loaded with a program.
--
-- **With the standard base installed**, because elaboration lives in it.
machineAt :: Cursor -> [Instr] -> Machine
machineAt cur is =
  load is (Machine (Exec [] [] []) (Development cur) [] emptyGlobals expectedBase [] [] 1000 0
                   NoUndischargeableTrust)

-- | @? goal : ∀ (a : Type₀) (b : Type₀) -> Type₀@ — two binders, so a miscount
-- would show.
piGoal2 :: Cursor
piGoal2 = enter (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
  where
    inner = Pi (Ident "b") type0 (Thena.Core.Term.close hypVar type0)
    ty    = Pi (Ident "a") type0 (Thena.Core.Term.close hypVar inner)

-- | @? goal : ∀ (A : Type₀) (x : A) -> A@ — the goal whose second binder's type
-- is the first binder, which is the case a written type can only be checked in
-- if it is elaborated where the earlier binders are in scope.
piGoalDep :: Cursor
piGoalDep = enter (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
  where
    inner = Pi (Ident "x") (Free hypVar) (Thena.Core.Term.close hyp2Var (Free hypVar))
    ty    = Pi (Ident "A") type0 (Thena.Core.Term.close hypVar inner)

-- | @? goal : ∀ (a : Type₀) -> Type₀@ — a hole a lambda can be elaborated into.
--
-- **The Π's binder is @a@ and the surface will say @y@**, which is the whole
-- point of the test that uses it.
piGoal :: Cursor
piGoal = enter (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
  where
    ty = Pi (Ident "a") type0 (Thena.Core.Term.close hypVar type0)

-- | The λ binders of the term the development has built, outermost first.
--
-- **In the term and not in the chain**: @attack@ opens a guess, @intro@ binds
-- inside it, and @solve@ commits the lot into one component whose /value/ is a
-- @Lam@. So the surface name that has to survive ends up as a
-- 'Thena.Core.Term.Lam' binder, which is where this looks for it.
identsBound :: Machine -> [String]
identsBound m = chain (Cursor.rebuild (cursor (development m)))
  where
    chain (Under (Define _ _ v _) _) = lams v
    chain (Under _ rest)             = chain rest
    chain (Trailing t)               = lams t
    chain _                          = []

    lams (Lam (Ident i) _ b) = i : lams (Thena.Core.Term.instantiate (Universe LZero) b)
    -- **Past the bindings an elaboration leaves in front of the λ.** A binder
    -- with a written type has that type elaborated into a hole of its own, and
    -- the solved hole is a @let@ sitting between the guess and the λ.
    lams (Let _ v _ b)       = lams v ++ lams (Thena.Core.Term.instantiate (Universe LZero) b)
    lams _                   = []

-- | The variable of the component the focus is on.
--
-- **What "the focus came back" actually means**, and it is what @here@ itself
-- answers — so the assertions below say /this component/ rather than /some
-- property of the path/. An earlier version asked whether @back@ failed, which
-- is a different question and passed for the wrong reason.
focusedVar :: Machine -> Maybe Var
focusedVar m = case focus (cursor (development m)) of
  Cursor.OnComponent (Assume v _ _)   -> Just v
  Cursor.OnComponent (Define v _ _ _) -> Just v
  Cursor.OnComponent (Claim  v _ _)   -> Just v
  Cursor.OnComponent (Guess  v _ _ _) -> Just v
  _                                   -> Nothing

isGuess :: Machine -> Bool
isGuess m = case focus (cursor (development m)) of
  Cursor.OnComponent (Guess {}) -> True
  _                             -> False

isHole :: Machine -> Bool
isHole m = case focus (cursor (development m)) of
  Cursor.OnComponent (Claim {}) -> True
  _                             -> False

drain :: RuleIter -> [Rule]
drain it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : drain rest

-- --------------------------------------------------------------------------
-- The leaves
-- --------------------------------------------------------------------------

leafTests :: TestTree
leafTests =
  testGroup
    "the leaves elaborate"
    [ -- @E⟦x⟧ = FILL x; SOLVE@ — Brady's variable case. What @elab-var@ did
      -- with a hint, one op does with a surface term.
      testCase "a name in scope is attached and committed" $
        case elaborating (SurfaceName "a") of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isGuess m @?= False   -- solved, so it is a definition now

    , testCase "a name that is not in scope says so" $
        case elaborating (SurfaceName "nope") of
          Left (CannotRead (ResolveFailed (NotInScope x))) -> x @?= "nope"
          other -> assertFailure ("expected a scope error: " ++ show other)

      -- **A leaf goes through @FILL@, not through @try@** (MS4 phase 41e), and
      -- this is how that is visible: the fixture's goal is @Type₀@ and
      -- @Type₀ : Type₁@, so the mismatch is reported by the **unification**
      -- @FILL@ does rather than by @try@'s check. Before 41e it was
      -- @GuessIllTyped@; the change is the point.
    , testCase "a leaf goes through FILL, so unification reports the mismatch" $
        case elaborating (SurfaceUniverse 0) of
          Left (UniverseMismatch _ _) -> pure ()
          other -> assertFailure ("expected unification to object: " ++ show other)

      -- **A literal is the one leaf that needs nothing looked up** (MS6 phase
      -- 97c): its term is itself and its type is fixed, so the clause is the
      -- written universe's two instructions. Both directions are stated,
      -- because a clause that filled without checking would pass the first.
    , testCase "a literal elaborates at its own type" $
        case elaboratingAt (holeAt stringType) (SurfaceLiteral (LString "hi")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isGuess m @?= False
    , testCase "and is refused at another type" $
        case elaboratingAt (holeAt stringType) (SurfaceLiteral (LInt 3)) of
          Left (Mismatch _ got want) ->
            (got, want) @?= (Global (GlobalName "Int") [], stringType)
          other -> assertFailure ("expected a clash of the two types: " ++ show other)

      -- **The placeholder elaborates by not elaborating** — his words. The
      -- hole is still a hole afterwards, which is the whole of the behaviour
      -- and the only way to see it.
    , testCase "_ leaves the hole exactly as it was" $
        case elaborating SurfacePlaceholder of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isHole m @?= True

    , testCase "and so does a named placeholder, for now" $
        case elaborating (SurfaceHole "goal") of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isHole m @?= True
    ]

-- --------------------------------------------------------------------------
-- What phase 41 does not do
-- --------------------------------------------------------------------------

-- | **A node with no case fails, and that is deliberate.**
--
-- An elaborator that quietly did nothing here would leave a hole that looked
-- elaborated — the one outcome worse than refusing — so each refusal is named
-- and each name is the specification of the phase that removes it.
--
-- **What is left is the two implicit forms, and they are phase 44's.** @∀@,
-- arrows, @let@ and ascription left this list at phase 41f and @elim@ at 41i,
-- so every structural case of @E⟦·⟧@ is now compiled.
unsupportedTests :: TestTree
unsupportedTests =
  testGroup
    "a node with no case is refused, not ignored"
    [ -- Implicit **arguments** are phase 44's, like implicit binders.
      -- **A brace the head has no position for** (MS4 phase 44b). An implicit
      -- argument is ordinary now; what is still refused is one that cannot be
      -- placed, which the fixture's @a@ — a local, with no recorded plicities
      -- — never can.
      refused "an implicit argument this head has no position for"
        (SurfaceApp (SurfaceName "a") [SurfaceArg Implicit (SurfaceName "a")])
      -- A @∀@ binder must say what it binds. The grammar's @PiBinder@ requires
      -- the annotation, so @∀ x -> B@ does not parse and this is reached only
      -- from a tree built by hand — but 'SurfaceBinder' is shared with λ, where
      -- an untyped binder is ordinary because the goal supplies the type, so
      -- the case is constructible and the ∀ clause has to answer for it. There
      -- is no goal to read a Π's domain off.
    , refusedShape "a ∀ whose first binder has a type"
        (SurfacePi [binder] (SurfaceName "a"))
    ]
  where
    binder = SurfaceBinder Explicit "x" Nothing
    refused what s = testCase what $
      case elaborating s of
        Left (NoElaborationRule w) -> w @?= what
        other -> assertFailure ("expected a refusal: " ++ show other)

    -- **The ∀ case is a clause** (MS4 phase 49b), so its refusal comes from the
    -- move that could not find an annotated binder rather than from an op that
    -- knew every shape — and the clause reads its parts before it touches the
    -- development, so nothing is claimed on the way to failing.
    refusedShape what s = testCase what $
      case elaborating s of
        Left (ExpectedSurfaceShape w) -> w @?= what
        other -> assertFailure ("expected a refusal: " ++ show other)

-- --------------------------------------------------------------------------
-- The λ case (MS4 phase 41b)
-- --------------------------------------------------------------------------

-- | @elim@ (MS4 phase 41i) — the unit fixture has no datatypes, so what can be
-- checked here is the refusal; the working cases are driven through the REPL in
-- "Thena.SessionTests", which is where a datatype can be declared.
elimTests :: TestTree
elimTests =
  testGroup
    "an elim names a datatype"
    [ testCase "and an unknown one is a scope error, not a missing rule" $
        case elaborating (SurfaceElim "D" [] (SurfaceName "a") [] [] (SurfaceName "a")) of
          Left (CannotRead (ResolveFailed (NotADatatype "D"))) -> pure ()
          other -> assertFailure ("expected NotADatatype: " ++ show other)
    ]

lambdaTests :: TestTree
lambdaTests =
  testGroup
    "a lambda elaborates"
    [ -- **The binder takes the SURFACE name, not the type\'s**, which is the
      -- whole reason @prim-intro@ gained an operand. The fixture\'s goal binds
      -- @a@; the surface says @y@; the development must say @y@, or the body\'s
      -- @y@ resolves to nothing.
      testCase "the binder takes the surface name" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" Nothing]
                                     (SurfaceName "y")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> identsBound m @?= ["y"]

      -- **@here@ is what makes this exact rather than careful** (phase 41c).
      -- Before it, the clause counted its own @into@/@along@ and undid them
      -- with matching @back@s; now it parks the component it was called at and
      -- @goto@es it. Two binders rather than one, because a miscount only shows
      -- when the counts differ.
    , testCase "two binders, and the focus still comes back" $
        case elaboratingAt piGoal2 (SurfaceLam [ SurfaceBinder Explicit "y" Nothing
                                               , SurfaceBinder Explicit "z" Nothing ]
                                      (SurfaceName "z")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> (identsBound m, focusedVar m) @?= (["y", "z"], Just goalVar)

      -- **The invariant every later case leans on**: an @Elaborate@ leaves the
      -- focus where it found it. The λ case makes moves and must undo them, or
      -- its own @prim-solve@ lands somewhere else.
    , testCase "and the focus comes back to where it started" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" Nothing]
                                     (SurfaceName "y")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> focusedVar m @?= Just goalVar

      -- **A written type is a check, and the binder is still the goal's** (MS8).
      -- The surface name survives exactly as it does without one.
    , testCase "a written binder type is checked, and the binder is unchanged" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" (Just (SurfaceUniverse 0))]
                                     (SurfaceName "y")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> (identsBound m, focusedVar m) @?= (["y"], Just goalVar)

      -- **The case the written type exists for**: its own type is an earlier
      -- binder of the same group, so it can only be elaborated inside them.
    , testCase "and it may name an earlier binder of the same group" $
        case elaboratingAt piGoalDep (SurfaceLam [ SurfaceBinder Explicit "A" Nothing
                                                 , SurfaceBinder Explicit "x" (Just (SurfaceName "A")) ]
                                        (SurfaceName "x")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> identsBound m @?= ["A", "x"]

      -- A group mixes freely, because the clause peels one binder at a time and
      -- asks about that one.
    , testCase "and a group mixes written and bare binders" $
        case elaboratingAt piGoal2 (SurfaceLam [ SurfaceBinder Explicit "y" (Just (SurfaceUniverse 0))
                                               , SurfaceBinder Explicit "z" Nothing ]
                                      (SurfaceName "z")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> (identsBound m, focusedVar m) @?= (["y", "z"], Just goalVar)

      -- **A wrong one fails at the binder it was written on**, not at @qed@.
    , testCase "and a written type that is not the goal's domain is refused" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" (Just (SurfaceName "String"))]
                                     (SurfaceName "y")) of
          Left _  -> pure ()
          Right m -> assertFailure ("elaborated: " ++ show (identsBound m))

      -- **Only the plicity is still refused**, and @lambda-name@ is where: an
      -- implicit binder is bare or written like any other, so both shapes reach
      -- the one refusal that names it.
    , refusedShape "a λ whose first binder is explicit"
        (SurfaceLam [SurfaceBinder Implicit "x" Nothing] (SurfaceName "x"))
    , refusedShape "a λ whose first binder is explicit"
        (SurfaceLam [SurfaceBinder Implicit "x" (Just (SurfaceUniverse 0))] (SurfaceName "x"))
    ]
  where
    -- **The λ case is clauses now** (MS4 phase 49c, MS8): a plain binder reads
    -- its type off the goal, a written one is elaborated and checked against
    -- it, and @lambda-name@ refuses an implicit binder before anything is
    -- introduced.
    refusedShape what s = testCase what $
      case elaboratingAt piGoal s of
        Left (ExpectedSurfaceShape w) -> w @?= what
        other -> assertFailure ("expected a refusal: " ++ show other)

-- --------------------------------------------------------------------------
-- here (MS4 phase 41c)
-- --------------------------------------------------------------------------

hereTests :: TestTree
hereTests =
  testGroup
    "here answers which component the focus is on"
    [ -- The companion to @goal@, which answers what it is claimed /at/. Nothing
      -- could answer this before: @claim@ and @define@ yield the variables of
      -- holes they make, and @goal@ gives a type.
      testCase "it yields the focused component's variable" $
        case snd (runOut (machineAt hole [Bind (Ops.PVar "h") Nothing Ops.Here])) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> lookup "h" (env (exec m))
                       @?= Just (VTerm (Free goalVar))

      -- **It survives @attack@**, which is the whole reason the λ case can use
      -- it: @attack@ turns @? x : S@ into a guess binding the /same/ variable,
      -- so a @goto@ afterwards finds what @here@ named.
    , testCase "and goto finds it again after attack" $
        case snd (runOut (machineAt hole [ Bind (Ops.PVar "h") Nothing Ops.Here
                                         , Do Ops.Attack
                                         , Do Ops.Into
                                         , Do (Ops.Goto (Ref "h"))
                                         ])) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> focusedVar m @?= Just goalVar

      -- Off the spine there is no component and no variable, which is the same
      -- refusal every component op gives.
    , testCase "and it is refused in the core fragment" $
        case snd (runOut (machineAt hole [Do Ops.CrossType, Bind (Ops.PVar "h") Nothing Ops.Here])) of
          Left (CannotMove NotOnTheSpine) -> pure ()
          other -> assertFailure ("expected a refusal: " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- Term construction (MS4 phase 41d)
-- --------------------------------------------------------------------------

-- | The first two ops that build a term — gap 2, arriving with a caller.
constructionTests :: TestTree
constructionTests =
  testGroup
    "arrow and apply-to build terms"
    [ -- **Stated as the property, not as the representation.** An arrow's
      -- codomain does not mention its binder, and instantiating the scope with
      -- anything at all must give the codomain back unchanged — which says
      -- \"non-dependent\" without the test having to know which variable was
      -- minted to close it.
      testCase "an arrow's codomain does not mention its binder" $
        case built (Ops.Arrow (litTerm type0) (litTerm hyp)) of
          Just (Pi (Ident "_") dom sc) -> do
            dom @?= type0
            Thena.Core.Term.instantiate type0 sc @?= hyp
            Thena.Core.Term.instantiate hyp   sc @?= hyp
          other -> assertFailure ("not an arrow: " ++ show other)

    , testCase "apply-to builds an application" $
        built (Ops.ApplyTo (litTerm hyp) (litTerm type0))
          @?= Just (App hyp type0)

      -- **They build; they do not check.** @Type₀@ applied to anything is not
      -- well formed and this still constructs it: a constructed term is checked
      -- where it is used, by @claim@'s side condition or @try@'s.
      -- @.claude\/spec\/representation.md@ §3.4's line.
    , testCase "and neither checks what it builds" $
        built (Ops.ApplyTo (litTerm type0) (litTerm type0))
          @?= Just (App type0 type0)

      -- Pure: the development is untouched, which is why they need no focus.
    , testCase "and neither touches the development" $
        case snd (runOut (machineAt hole [Bind (Ops.PVar "r") Nothing (Ops.Arrow (litTerm type0) (litTerm type0))])) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> focusedVar m @?= Just goalVar
    ]
  where
    litTerm t = Lit (VTerm t)
    hyp       = Free hypVar

    built o = case snd (runOut (machineAt hole [Bind (Ops.PVar "r") Nothing o])) of
      Right m -> case lookup "r" (env (exec m)) of
        Just (VTerm t) -> Just t
        _                         -> Nothing
      Left _  -> Nothing

-- --------------------------------------------------------------------------
-- The shipped base
-- --------------------------------------------------------------------------

baseTests :: TestTree
baseTests =
  testGroup
    "the shipped base"
    [ -- Every rule whose head passes, and no partition to divide them.
      --
      -- **@elaborate@ appears once per surface node** (MS4 phase 49), and a
      -- test about an argument nobody supplied does not exclude a clause (phase
      -- 47), so a bare @:matches@ lists them all. What to show a reader is
      -- presentation, deliberately unexamined (§8).
      --
      -- **The counts live in the 'replicate's and are deliberately not restated
      -- here**: this comment said /thirteen/ against an assertion of sixteen
      -- until MS2 phase 27 — a count in prose beside an assertion that grows.
      --
      -- **@fit-core@ is two clauses and both heads pass**, which is the point
      -- of it: the choice point between them is the search.
      testCase "every rule whose head passes is a candidate" $
        [ n | Rule (GlobalName n) _ _ _ <- drain (matches expectedBase emptyGlobals hole) ]
          @?= [ "attack", "try-core", "abandon", "eliminate-core"
              , "prove", "fill", "unify-refine-core", "apply-core"
              , "fit-core", "fit-core"
              , "claim", "assume", "quantify"
              ]
              ++ replicate 20 "elaborate" ++ ["run-block"]
              ++ replicate 2 "spine-arguments"

    , testCase "prove is a rule over prim-prove" $
        case [ r | r@(Rule (GlobalName "prove") _ _ _) <- drain (matches expectedBase emptyGlobals hole) ] of
          [Rule _ ps _ b] -> (ps, b) @?= ([], [Do Ops.Prove])
          other           -> assertFailure ("expected one clause: " ++ show other)
    ]


-- --------------------------------------------------------------------------
-- Taking a split apart (MS9 phase 181)
-- --------------------------------------------------------------------------

-- | The five head tests and the three moves over @induction … of@ and
-- @case … of@, through a rule base and at run time.
--
-- __Nothing elaborates a split yet__, so the clause these exist for is not
-- written: this walks one and /says/ what it reached, which is the only way to
-- observe a move whose answer is a focused surface term. The suite's own word
-- tables already check that each op parses, reads back and has a keyword; what
-- they cannot check is that a frame reaches the child it names, and
-- "Thena.SurfaceZipperTests" checks that against @rebuild@ rather than against
-- a running rule.
--
-- __The second arm is reached through @split-tail@__, so a tail that dropped
-- the later arms, or kept the first, would print the wrong name here.
--
-- @name-text@ is in the walk because @surface-name@ answers a @Name@ and @say@
-- takes text — the one-way crossing, used in the direction that exists.
splitParts :: [TestTree]
splitParts =
  [ testCase "induction: the word, the target, each arm's body, then the end" $
      walks "describe surface`induction tgt of { zero -> zzz ; succ m -> sss }`"
        ["induction", "tgt", "zzz", "sss", "end"]
    -- __No arms is a legal split__, and it is what the recursion stops at —
    -- @case t of { }@ is the whole of a case analysis on a datatype with no
    -- constructors.
  , testCase "case with no arms: the word, the target, and straight to the end" $
      walks "describe surface`case other of { }`" ["case", "other", "end"]
  ]
  where
    walks call want = case loadedError loaded of
      Just e  -> assertFailure (show e)
      Nothing -> [ w | Ran ws _ _ <- loadedResponses loaded, w <- ws ] @?= want
      where loaded = loadSource walkSession call

-- | A base that walks a split and says the name at each place it lands.
walkBase :: String
walkBase = unlines
  [ "rule base splitwalk where"
  , "name-of : Surface -> ()"
  , "rule name-of g :- when (surface-is-name g)"
  , "  do w = surface-name g ; x = name-text w ; say x"
  , ""
  , "walk-arms : Surface -> ()"
  , "rule walk-arms t :- when (surface-is-split t) (split-has-no-arms t)"
  , "  do say \"end\""
  , "rule walk-arms t :- when (surface-is-split t) (split-has-arms t)"
  , "  do b = split-arm-body t"
  , "     ; name-of b"
  , "     ; r = split-tail t"
  , "     ; walk-arms r"
  , ""
  , "describe : Surface -> ()"
  , "rule describe t :- when (surface-is-split t) (split-is-induction t)"
  , "  do say \"induction\" ; g = split-target t ; name-of g ; walk-arms t"
  , "rule describe t :- when (surface-is-split t) (split-is-cases t)"
  , "  do say \"case\" ; g = split-target t ; name-of g ; walk-arms t"
  ]

-- | The walk beside the shipped base, as 'Thena.SpecialiseTests' does it: a
-- load __replaces__ the bases a session searches, so the standard rules go
-- back in alongside.
walkSession :: Session
walkSession = case loadRuleBases newSession [("walk.thena.rules", walkBase)] of
  (s, BasesLoaded bs) -> withRuleBases (expectedBase ++ bs) s
  (_, other)          -> error ("the fixture's base did not load: " ++ show other)


-- --------------------------------------------------------------------------
-- A split with no arms (MS9 phase 182)
-- --------------------------------------------------------------------------

-- | @case e of { }@ — case analysis on a datatype with no constructors.
--
-- __The whole stack, and the kernel is the judge__: a declaration ends in
-- @qed@ and @qed@ certifies, so a load that reports no error means layout, the
-- parser, the clause, the elimination tactic and @certify@ all agreed.
--
-- __One clause serves both words.__ A datatype with no constructors has no
-- methods, so there is nothing for an inductive hypothesis to attach to and
-- @induction@ and @case@ cannot differ here — which is why the clause tests
-- @split-has-no-arms@ and not the analysis.
--
-- __The target's type is not known before the target is elaborated__, so the
-- clause claims a hole for it and unification solves that hole on the way
-- past. The @Tsplit@ in the extracted term below is that hole, and it is
-- solved — @Empty {ℓ}@ — rather than left open, which is the thing worth
-- pinning: a clause that failed to solve it would still load and still
-- certify, with a level parameter nobody wrote.
emptySplit :: [TestTree]
emptySplit =
  [ testCase "case: it declares, so the kernel accepted it" $
      declares "case" >>= (@?= Nothing)
  , testCase "and induction, on the same clause" $
      declares "induction" >>= (@?= Nothing)
    -- The eliminator is applied to no methods at all — @()@ — which is the
    -- observable difference between this and every other elimination.
  , testCase "the term is an elimination with no methods, at a solved type" $ do
      shown <- extracted "case"
      assertBool shown ("elim Empty" `isInfixOf` shown)
      assertBool shown ("Tsplit = Empty" `isInfixOf` shown)
  ]
  where
    source word = unlines
      [ "module Vacuous where"
      , ""
      , "fromEmpty : Empty -> Unit"
      , "fromEmpty = \\ e -> " ++ word ++ " e of { }"
      ]

    loaded word = do
      (s0, _) <- startingSession
      pure (loadProofSource s0 (source word))

    declares word = do
      (s1, resp) <- loaded word
      pure $ case resp of
        ProofLoaded {} -> Nothing
        other          -> Just (unwords (renderResponse s1 other))

    extracted word = do
      (s1, _) <- loaded word
      pure (unwords (renderResponse' s1 ":show fromEmpty"))

    renderResponse' sn l = let (sn', r) = command sn l in renderResponse sn' r
