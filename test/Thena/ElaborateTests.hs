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
    , testGroup "the splitting tree (MS9 phase 184)" splittingTree
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
              ++ replicate 7 "elaborate"
              ++ [ "no-nesting", "ihs-for", "ihs-for"
                 , "reverse-onto", "reverse-onto", "apply-all", "apply-all"
                 , "instantiate-with" ]
              ++ replicate 8 "intro-arm-binders"
              ++ [ "bind-friendlies", "bind-friendlies", "bind-solved", "bind-solved"
                 , "same-length", "same-length"
                 , "arm-for", "arm-for", "pick", "pick", "arm-needs-body"
                 , "elaborate-arm", "case-needs-an-arm"
                 , "vanished-case-takes-no-body", "vanished-case-takes-no-body"
                 , "case-must-vanish", "one-case", "one-case", "one-case"
                 , "arm-must-be-for-this-datatype"
                 , "arms-are-for-this-datatype", "arms-are-for-this-datatype"
                 , "one-arm-per-constructor"
                 , "arm-not-repeated", "arm-not-repeated"
                 , "arms-are-distinct", "arms-are-distinct"
                 , "split-cases", "split-cases", "split-over"
                 , "split-claim", "split-claim", "split-elaborate"
                 ]
              ++ replicate 15 "elaborate"
              ++ ["run-block"]
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

    -- __AN ARM WITH NO BODY ANSWERS @none@__ (MS9 phase 189), and this is the
    -- test that the walk reaches the /next/ arm afterwards: an empty arm is a
    -- legal arm, so @split-tail@ still has to peel it. @name-of-body@ is the
    -- fixture's own reader, one clause per shape, which is how a rule is meant
    -- to take @split-arm-body@'s answer apart.
  , testCase "an arm with no body: the walk says so and goes on to the next" $
      walks "describe surface`induction tgt of { vnil -> ; vcons k a as -> sss }`"
        ["induction", "tgt", "empty", "sss", "end"]

    -- __A NESTED pattern, read to depth two__ (MS9 phase 183), which is the
    -- measurement the design rests on: @cons n x (cons m y nil)@ parses today,
    -- so a reader answering a flat list of names would be wrong on syntax the
    -- parser already accepts. @pattern-arguments@ answers with /patterns/ and
    -- @show-pat@ recurses, so the whole tree comes out in order.
  , testCase "a pattern is read to its leaves, nesting and all" $
      walks ("patterns surface`induction v of "
             ++ "{ nil -> a ; cons n x (cons m y nil) -> b ; _ -> c }`")
        [ "nil", "|"
        , "cons", "n", "x", "cons", "m", "y", "nil", "|"
        -- __A wildcard is not a name__, and 'SurfacePattern' draws that
        -- distinction on purpose: a pattern's @_@ binds where a term's @_@ is a
        -- hole to solve.
        , "_", "|"
        , "end"
        ]

    -- __The one test that is not a shape question__, and the one without which
    -- no splitting tree can pair an arm with a constructor.
    -- __@chose 1@ is the ordering being a real choice point__, not noise: with
    -- the names equal BOTH clauses' heads pass — the second has no head — so
    -- the engine records an alternative and would run @different@ if the first
    -- clause's body failed. With the names unequal the first head excludes
    -- itself, one candidate is left, and nothing is recorded.
  , testCase "two names read at run time can be compared" $
      walks "cmp \"cons\" \"cons\"" ["chose 1: cmp", "same"]
  , testCase "and told apart, with no alternative left to record" $
      walks "cmp \"cons\" \"nil\"" ["different"]
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
  , "name-of-body : Option Surface -> ()"
  , "rule name-of-body (some b) :- do name-of b"
  , "rule name-of-body none :- do say \"empty\""
  , ""
  , "walk-arms : Surface -> ()"
  , "rule walk-arms t :- when (surface-is-split t) (split-has-no-arms t)"
  , "  do say \"end\""
  , "rule walk-arms t :- when (surface-is-split t) (split-has-arms t)"
  , "  do b = split-arm-body t"
  , "     ; name-of-body b"
  , "     ; r = split-tail t"
  , "     ; walk-arms r"
  , ""
  , "describe : Surface -> ()"
  , "rule describe t :- when (surface-is-split t) (split-is-induction t)"
  , "  do say \"induction\" ; g = split-target t ; name-of g ; walk-arms t"
  , "rule describe t :- when (surface-is-split t) (split-is-cases t)"
  , "  do say \"case\" ; g = split-target t ; name-of g ; walk-arms t"
    -- The pattern readers (MS9 phase 183). @show-pat@ is recursive through
    -- @pattern-arguments@, which is what reads a NESTED pattern.
  , ""
  , "show-pats : List Pattern -> ()"
  , "rule show-pats [] :- do"
  , "rule show-pats [p, ...ps] :- do show-pat p ; show-pats ps"
  , ""
  , "show-pat : Pattern -> ()"
  , "rule show-pat p :- when (pattern-is-wildcard p) do say \"_\""
  , "rule show-pat p :- when (pattern-is-name p)"
  , "  do w = pattern-head p"
  , "     ; x = name-text w"
  , "     ; say x"
  , "     ; as = pattern-arguments p"
  , "     ; show-pats as"
  , ""
  , "patterns : Surface -> ()"
  , "rule patterns t :- when (surface-is-split t) (split-has-no-arms t) do say \"end\""
  , "rule patterns t :- when (surface-is-split t) (split-has-arms t)"
  , "  do p = split-arm-pattern t"
  , "     ; show-pat p"
  , "     ; say \"|\""
  , "     ; r = split-tail t"
  , "     ; patterns r"
    -- Two clauses and an ordering, there being no negation: the first is
    -- excluded when the names differ, so the second is what runs.
  , ""
  , "cmp : Name -> Name -> ()"
  , "rule cmp a b :- when (same-name a b) do say \"same\""
  , "rule cmp a b :- do say \"different\""
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
    -- No methods at all, which is the observable difference between this and
    -- every other elimination.
    --
    -- **AND THE WORD IS WHAT DECIDES THE HEAD** (MS9 phase 188). @case@ applies
    -- the generated @caseEmpty@, @induction@ builds an @elim Empty@ node. The
    -- two are convertible — @caseD@ δ-unfolds to exactly that elimination — so
    -- nothing downstream and nothing in the kernel can tell them apart; what
    -- changed is that the term now says which word was written.
  , testCase "case: the term applies caseEmpty, at a solved type" $ do
      shown <- extracted "case"
      assertBool shown ("caseEmpty" `isInfixOf` shown)
      assertBool shown ("Tsplit = Empty" `isInfixOf` shown)

  , testCase "induction: the term is an elim node with no methods" $ do
      shown <- extracted "induction"
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


-- --------------------------------------------------------------------------
-- The splitting tree (MS9 phase 184)
-- --------------------------------------------------------------------------

-- | @induction t of { p -> e ; … }@ with arms, end to end and through the
-- kernel.
--
-- __The first case is the milestone's point__: a function defined by pattern
-- matching, which declares — so @qed@ certified it — and then /computes/.
-- @pred (succ (succ zero))@ reducing to @succ zero@ is the whole claim, and it
-- is checked by reduction rather than by reading the term, because the term is
-- an @elim@ either way and only reduction says the methods went to the right
-- constructors.
--
-- __The refusals are each a different cause and each says so__, which is the
-- part that took work. The obvious shape for the arm search — one rule that
-- matches the constructor's name and elaborates the body — makes both clauses a
-- choice point, so a body that fails to elaborate backtracks into the search,
-- walks on through the arms and reports /the search/. Every one of these four
-- then said @no clause of arm-for applies here@. MS8 phase 170 found the same
-- thing in the application clauses; the fix is the same, a pair of
-- complementary tests so no choice point is recorded at all.
splittingTree :: [TestTree]
splittingTree =
  [ testCase "a function defined by pattern matching declares and computes" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (natModule ++ predDef))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf pred (succ (succ zero))"
      unwords (renderResponse s2 q) @?= "succ zero"

    -- __A RECURSIVE CALL IS THE INDUCTION HYPOTHESIS__ (MS9 phase 186, his
    -- ruling of 2026-10-19). The name being defined is assumed while the body
    -- elaborates and @tie-recursion@ replaces each application of it, so the
    -- arm writes an ordinary call and no rule knows that it is one.
    --
    -- __Checked by reduction and not by reading the term__, for the reason the
    -- case above gives: only reduction says the hypothesis went to the right
    -- place. @double (succ (succ zero))@ is four, and it is four because the
    -- call became the hypothesis about @m@ and not anything else of type
    -- @Nat@ in scope.
  , testCase "a recursive call becomes the induction hypothesis, and computes" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (natModule ++
            [ "double : Nat -> Nat"
            , "double = \\ n -> induction n of"
            , "  { zero -> zero ; succ m -> succ (succ (double m)) }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1
            ":convert double (succ (succ zero)) \8799 succ (succ (succ (succ zero)))"
      unwords (words (unwords (renderResponse s2 q))) @?=
        "double (succ (succ zero)) \8799 succ (succ (succ (succ zero))) yes"

    -- __The structural guard, and it is the whole of it.__ An eliminator makes
    -- the hypothesis available only at the smaller index, so a call on
    -- anything else names no hypothesis and is refused. This stands in for a
    -- termination checker: there is nothing to check, because there is nothing
    -- to express.
  , refuses "a recursive call that is not structurally smaller is refused"
      [ "loop : Nat -> Nat"
      , "loop = \\ n -> induction n of { zero -> zero ; succ m -> loop zero }"
      ]
      "stuck: no induction hypothesis is about this call, so it is not \
      \structurally smaller: loop zero"

    -- The name used as a value rather than called. There is no hypothesis for
    -- that, and leaving it would make the body open.
  , refuses "the name being defined cannot be used as a value"
      [ "self : Nat -> Nat"
      , "self = self"
      ]
      "stuck: the name being defined is used as a value, and only a call to \
      \it can be an induction hypothesis"
    -- The arm names fewer variables than the constructor takes arguments.
  , refuses "a pattern of the wrong arity is caught by same-length"
      [ "bad : Nat -> Nat"
      , "bad = \\ n -> induction n of { zero -> zero ; succ -> zero }"
      ]
      "stuck: no clause of same-length applies here"
    -- Coverage: a method survived and no arm was written for it. **The refusal
    -- names the complaint and not the search** (MS9 phase 190) — until the law
    -- landed, @arm-for@ ran out of arms and reported itself, which named a rule
    -- in the shipped base instead of the missing arm.
  , refuses "a case that survived with no arm is refused by name"
      [ "partial : Nat -> Nat"
      , "partial = \\ n -> induction n of { zero -> zero }"
      ]
      "stuck: no clause of case-needs-an-arm applies here"

    -- __EVERY ARM THE USER WROTE WAS ASKED FOR__ — his ruling of 2026-10-20,
    -- built in MS9 phase 190. The three below are the three ways an arm went
    -- unlooked-at before it, each of which loaded and declared in silence, and
    -- __each refusal names what the user did and not the rule that went
    -- looking__. The fourth, a body written for a case the specialiser closed,
    -- needs an indexed family and is with the @Vec@ tests.
  , refuses "a second arm for a constructor that already has one is refused"
      [ "dup : Nat -> Nat"
      , "dup = \\ n -> induction n of { zero -> zero ; zero -> zero ; succ m -> m }"
      ]
      "stuck: no clause of one-arm-per-constructor applies here"
    -- __A head that is a constructor of SOME datatype, just not this one.__
    -- @constructor-datatype@ answers, and the names do not agree. The separate
    -- case below is the head that is no constructor at all, which stops one op
    -- earlier and names the word instead.
  , refusesIn vecModule "an arm headed by another datatype's constructor is refused"
      [ "foreign : Nat -> Nat"
      , "foreign = \\ n -> induction n of { zero -> zero ; vnil -> zero ; succ m -> m }"
      ]
      "stuck: no clause of arm-must-be-for-this-datatype applies here"
    -- __A misspelled constructor was ALREADY refused before the law__, and the
    -- only thing wrong with it was the words: it ran the arm search out and
    -- reported @no clause of arm-for applies here@. It now stops in
    -- @constructor-datatype@, which names the word the user typed.
  , refuses "an arm headed by a word that is no constructor names the word"
      [ "typo : Nat -> Nat"
      , "typo = \\ n -> induction n of { zero -> zero ; succc m -> m }"
      ]
      "stuck: succc is not a constructor"
    -- A nested pattern argument is a second split, which is a later phase.
  , refuses "a nested pattern argument is declined by name"
      [ "nested : Nat -> Nat"
      , "nested = \\ n -> induction n of { zero -> zero ; succ (succ m) -> m }"
      ]
      "stuck: no clause of no-nesting applies here"

    -- ----------------------------------------------------------------
    -- A SPLIT THAT REFINES A POSITION BOUND OUTSIDE IT (MS9 phases 191, 195)
    -- ----------------------------------------------------------------

    -- __THE AMBIENT NAME MEANS THE REFINED THING, AND THAT IS THE WHOLE OF
    -- WHAT THIS ASSERTS__ (MS9 phase 195, his ruling of 2026-10-20:
    -- /"elaboration is 'compilation' — they should not change how they write
    -- their proof because of how we compile it"/).
    --
    -- Splitting @e : Ev (s m)@ against @evs@'s own @Ev (s (s n))@ leaves @s n@
    -- facing @m@, and @m@ is bound /outside/ the split, so nothing on the rule's
    -- side can move to fit it: the split generalises @m@ and the arm solves the
    -- copy to @s n@. **So @m@ in the arm is @s n@**, the goal @IsSucc (s m)@ is
    -- @IsSucc (s (s n))@, and @isucc m@ inhabits it. Before this phase the copy
    -- bound nothing, @m@ reached back out to the unrefined entry, and the arm
    -- was refused — which is the state @~tzwjk@ recorded.
    --
    -- **It computes, which is the part a declaration alone would not say**: the
    -- definition the arm binds @m@ to is the term the split forced, reduced, so
    -- @namesOuter (s z) (evs z evz)@ is @isucc (s z)@ and not @isucc@ of a
    -- β-redex.
  , testCase "a name bound outside a split means what the split refined it to" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (evModule ++
            [ "namesOuter : \8704 (m : N) (e : Ev (s m)) -> IsSucc (s m)"
            , "namesOuter = \\ m e -> case e of { evs n en -> isucc m }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf namesOuter (s z) (evs z evz)"
      unwords (renderResponse s2 q) @?= "isucc (s z)"

    -- __AND THE THREE SHAPES PHASE 191 WAS BUILT FOR__, which had been a
    -- fixture nothing loaded: the copy that is refined and read under its own
    -- name (@usesHyp@'s @h@), the copy that is solved (@refined@), and an index
    -- the arm mentions (@mentionsIndex@). Each declares, and the two that can
    -- compute are asserted by @refl@ inside the module, so a wrong refinement
    -- fails here rather than passing quietly.
  , testCase "a generalising split: refined, used and mentioned all declare" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (evModule ++
            [ "refined : \8704 (m : N) (e : Ev (s m)) -> IsSucc m"
            , "refined = \\ m e -> case e of { evs n en -> isucc n }"
            , "usesHyp : \8704 (m : N) (h : Ev m) (e : Ev (s m)) -> IsSucc m"
            , "usesHyp = \\ m h e -> case e of { evs n en -> isucc n }"
            , "mentionsIndex : \8704 (m : N) (e : Ev (s m)) -> IsSucc (s m)"
            , "mentionsIndex = \\ m e -> case e of { evs n en -> isucc (s n) }"
            , "check1 : Eq (IsSucc (s z)) (refined (s z) (evs z evz)) (isucc z)"
            , "check1 = refl (IsSucc (s z)) (isucc z)"
            , "check3 : Eq (IsSucc (s (s z))) (mentionsIndex (s z) (evs z evz)) (isucc (s z))"
            , "check3 = refl (IsSucc (s (s z))) (isucc (s z))"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))

    -- __AND SO DOES A NAME A FRIENDLY INDEX ABSTRACTED__ (MS9 phase 196,
    -- @~8v3pg@), which is the same ruling on the path that makes no copy. An
    -- index the target supplies as a plain variable that no other entry mentions
    -- needs no equation: the motive abstracts it outright. So nothing is
    -- generalised and nothing is solved, and until this phase nothing bound the
    -- ambient name either — the arm's goal was about the abstracted variable
    -- while the name still reached the entry outside.
    --
    -- @indexIsRefined@ is the shape, and @m@ is the author's own name for
    -- @Ev m@'s index: in the @evz@ arm it means @z@ and in the @evs@ arm it
    -- means @s (s n)@, so one @refl N m@ answers both. @sameIndex@ is the same
    -- thing where the index is the constructor's OWN argument — @mk@'s @k@ —
    -- and writing @mk m@ there was refused with @m and k cannot be made equal@.
    --
    -- **Both compute**: @check@ asserts the first by @refl@ inside the module,
    -- and the @:whnf@ below is the second, so a name bound to the wrong term
    -- fails here rather than passing quietly.
  , testCase "a friendly index's ambient name means the refined thing too" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (evModule ++
            [ "data D : N -> Type\8320 where"
            , "  mk : \8704 (k : N) -> D k"
            , ""
            , "indexIsRefined : \8704 (m : N) (e : Ev m) -> Eq N m m"
            , "indexIsRefined = \\ m e -> case e of \
              \{ evz -> refl N m ; evs n en -> refl N m }"
            , "sameIndex : \8704 (m : N) (d : D m) -> D m"
            , "sameIndex = \\ m d -> case d of { mk k -> mk m }"
            , "check : Eq (Eq N z z) (indexIsRefined z evz) (refl N z)"
            , "check = refl (Eq N z z) (refl N z)"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf sameIndex (s z) (mk (s z))"
      unwords (renderResponse s2 q) @?= "mk (s z)"

    -- __AND WHERE THE PREMISE IS INTRODUCED MAKES NO DIFFERENCE__ (MS9 phase
    -- 197, @~k54hh@), which is the same ruling again: the statement
    -- @\8704 (n : N) (x : A n) (u : N) (f : F n u) -> N@ says nothing about the
    -- order a proof introduces its own premises in, and @\ n x u ->@ across the
    -- top is what a student writes.
    --
    -- Both proofs here are the same text with @u@ and @f@ bound in two places,
    -- and the inner @case f of@ has to generalise the ambient @u@ either way —
    -- @fs@'s own @s m@ faces @u@ and there is nothing on the rule's side to
    -- move. @inside@ always worked. __@outside@ was refused with @N and
    -- Eq {0} N (s m) u -> N cannot be made equal@__ — the equation stated and
    -- kept, because the generalisation was cancelled rather than made.
    --
    -- __What cancelled it was the @az@ arm.__ The split's own closure found @u@
    -- and the induction hypothesis and wanted both; the context it looked at
    -- also held @azMethod@ and @azCase@, the /previous arm's/ solved
    -- definitions, whose types mention @u@ because the statement's @f@ is in
    -- them — and one definition anywhere in the closure used to cancel every
    -- copy. They are now skipped, and nothing else about the split moved.
    --
    -- **Both compute, to the same answer**, so a generalisation that lands on
    -- the wrong copy fails here rather than declaring quietly.
  , testCase "where a premise is introduced does not decide whether it loads" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (reachModule ++
            [ "inside : \8704 (n : N) (x : A n) (u : N) (f : F n u) -> N"
            , "inside = \\ n x -> induction x of \
              \{ az -> \\ u f -> z ; as k p -> \\ u f -> case f of { fs j m r -> m } }"
            , "outside : \8704 (n : N) (x : A n) (u : N) (f : F n u) -> N"
            , "outside = \\ n x u -> induction x of \
              \{ az -> \\ f -> z ; as k p -> \\ f -> case f of { fs j m r -> m } }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let two = "(s (s z)) (as (s z) (as z az)) (s (s z)) (fs (s z) (s z) (fs z z fz))"
          (s2, q) = command s1 (":whnf inside " ++ two)
          (s3, q') = command s2 (":whnf outside " ++ two)
      unwords (renderResponse s2 q) @?= "s z"
      unwords (renderResponse s3 q') @?= "s z"

    -- __AND A RECURSION MAY SUPPLY A GENERALISED PREMISE__ (MS9 phase 198,
    -- @~krvdx@). Where the statement's own premises include one the split has to
    -- generalise, the induction hypothesis stops being "the declaration's
    -- telescope minus the target": the motive quantifies a copy of each
    -- generalised entry and states one equation per tied index, so the
    -- hypothesis takes those first.
    --
    -- @e@ is the case, and it is generalised because its type mentions @n@, the
    -- index of the target. The hypothesis in the @as@ arm is
    -- @∀ (n : N) (e : Eq N n n) -> Eq N k n -> N@, and the call supplies the
    -- first two: @k@ is what the recursion says @n@ is at the smaller subject
    -- and @refl N k@ is what it says @e@ is. **The equation is then reflexive,
    -- and that is why the call's own arguments decide it** rather than anything
    -- the arm carries.
    --
    -- Before this phase the call was the hypothesis applied to the arguments
    -- after the one it recurses on, so @refl N k@ landed in the slot wanting an
    -- @N@ and the kernel refused it with @N and Eq are different names@.
    --
    -- **@p38@ is the other spelling and stays refused**, which is the machinery
    -- working: it passes the arm's own @e@, which the split refined to the copy
    -- at @s k@, where a hypothesis about @k@ wants @Eq N k k@.
  , testCase "a recursion supplies the premise a split generalised" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (reachModule ++
            [ "takesPremise : \8704 (n : N) (x : A n) (e : Eq N n n) -> N"
            , "takesPremise = \\ n x e -> induction x of \
              \{ az -> z ; as k p -> s (takesPremise k p (refl N k)) }"
            , "noPremise : \8704 (n : N) (x : A n) -> N"
            , "noPremise = \\ n x -> induction x of \
              \{ az -> z ; as k p -> s (noPremise k p) }"
              -- Asserted by @refl@ inside the module rather than with
              -- @:whnf@, which stops at the @s@ the answer is headed by and so
              -- would say nothing about the recursion under it.
            , "check : Eq N (takesPremise (s z) (as z az) (refl N (s z))) (s z)"
            , "check = refl N (s z)"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
  , refusesIn reachModule "a recursion passing the arm's own refined premise is refused"
      [ "wrongPremise : \8704 (n : N) (x : A n) (e : Eq N n n) -> N"
      , "wrongPremise = \\ n x e -> induction x of \
        \{ az -> z ; as k p -> s (wrongPremise k p e) }"
      ]
      "stuck: s k and k cannot be made equal"

    -- __AND A RECURSION MAY VARY A PREMISE THE SPLIT DID NOT SPLIT ON__ (MS9
    -- phase 198, @~754m3@), which is the last of the four and the one the two
    -- TAPL rewrites were waiting on.
    --
    -- @u@ is the case. The tied index seeds @n@, and the forward closure takes
    -- @f : F n u@ because its type mentions @n@ — but it used to leave @u@
    -- behind, so the induction hypothesis read @∀ n' (f' : F n' u) -> …@ about
    -- the **ambient** @u@. The inner split then refines that @u@ to @s m@ while
    -- the recursion needs the hypothesis at @m@, so **the hypothesis the proof
    -- needs did not exist in the arm at all** and nothing at the call could have
    -- found it. The closure now closes backward as well — an entry a generalised
    -- entry's type mentions is generalised too — and the copies are a telescope
    -- that mentions nothing it did not take.
    --
    -- **It computes**, so a hypothesis generalised at the wrong index fails here
    -- rather than declaring: three @fs@ layers deep, the answer counts them.
  , testCase "a recursion varies a premise the split did not split on" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (reachModule ++
            [ "varies : \8704 (n : N) (x : A n) (u : N) (f : F n u) -> N"
            , "varies = \\ n x u f -> induction x of \
              \{ az -> z ; as k p -> case f of { fs j m r -> s (varies k p m r) } }"
            , "check : Eq N (varies (s (s z)) (as (s z) (as z az)) (s (s z)) \
              \(fs (s z) (s z) (fs z z fz))) (s (s z))"
            , "check = refl N (s (s z))"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))

    -- ----------------------------------------------------------------
    -- A FORCED POSITION (MS9 phase 185)
    -- ----------------------------------------------------------------

    -- __@vtail@, which is the milestone's own case and the one phase 184 could
    -- not do.__ Splitting @v : Vec A (succ n)@ solves @vcons@'s own @k@ against
    -- the outer @n@, so the subgoal binds two of the constructor's three
    -- arguments and the pattern names three. The name in the forced position
    -- becomes a /definition/ equal to what it was forced to — his ruling of
    -- 2026-10-19 — so the arm's text means what it reads like either way.
    --
    -- __And no @vnil@ arm is written__, because that case vanished: the
    -- conflicting equation closed the method outright, so there is nothing to
    -- elaborate into and nothing for coverage to want.
  , testCase "a split over an indexed family declares, with a forced position" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (vecModule ++ vtailDef))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      -- Saturated, because @:whnf@ reads a CORE term and nothing is inserted
      -- there: @vcons@'s parameter is an argument like any other, and an
      -- under-applied former is not a 'Canonical' for ι to fire on.
      let (s2, q) = command s1 ":whnf vtail Nat zero (vcons Nat zero zero (vnil Nat))"
      unwords (renderResponse s2 q) @?= "vnil Nat"

    -- __AN EMPTY ARM IS HOW THE VANISHED CASE IS WRITTEN__ (MS9 phase 189, his
    -- ruling of 2026-10-20). @vnil@'s method is closed by a conflicting
    -- equation — @succ n = zero@ — so there is nothing to prove and the arm
    -- carries no term. The same proof as above, with the case named rather than
    -- left out, and it declares and computes identically.
  , testCase "an arm with no body is accepted where the case vanished" $ do
      (s0, _) <- startingSession
      let src = vecModule ++
            [ "vtail : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
            , "vtail = \\ A n v -> induction v of { vnil -> ; vcons k a as -> as }"
            ]
          (s1, r) = loadProofSource s0 (unlines src)
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf vtail Nat zero (vcons Nat zero zero (vnil Nat))"
      unwords (renderResponse s2 q) @?= "vnil Nat"

    -- __A BODY WHERE THE CASE VANISHED IS THE REFUSAL THE LAW ADDS__ (MS9 phase
    -- 190). @vnil@'s method is closed by a conflicting equation, so a term
    -- written in that arm is the user claiming the case is reachable against a
    -- proof that it is not. Before the law it loaded, declared and computed,
    -- with @nonsense@, @zzz@ and @qqq@ in no scope and no word said.
  , refusesIn vecModule "a body for a case that vanished is refused"
      [ "vtailB : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
      , "vtailB = \\ A n v -> induction v of { vnil -> nonsense zzz qqq ; vcons k a as -> as }"
      ]
      "stuck: no clause of vanished-case-takes-no-body applies here"

    -- __AND REFUSED WHERE THE CASE SURVIVED__, which is the other half of the
    -- same ruling: @zero@'s method is right there, so there is something to
    -- prove and the arm is what proves it. **The refusal names the user's
    -- mistake and not the search** — @arm-for@ found the arm; what is missing is
    -- its body.
  , refuses "an arm with no body is refused where the case survived"
      [ "pred : Nat -> Nat"
      , "pred = \\ n -> induction n of { zero -> ; succ m -> m }"
      ]
      "stuck: no clause of arm-needs-body applies here"

    -- __The forced position is a definition, and @refl@ proves it.__ The goal
    -- is @Eq Nat n n@ and the arm answers with @refl Nat k@, whose type is
    -- @Eq Nat k k@. The two are convertible only because @k@ /is/ @n@ — a
    -- definition, not a propositional equation — so this is the design's claim
    -- that no @Eq@ hypothesis and no transport is needed, run rather than
    -- argued.
  , testCase "and the name it binds is definitionally what it was forced to" $ do
      (s0, _) <- startingSession
      let src = vecModule ++
            [ "tailLen : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Eq Nat n n"
            , "tailLen = \\ A n v -> induction v of { vcons k a as -> refl Nat k }"
            ]
          (s1, r) = loadProofSource s0 (unlines src)
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))

    -- A wildcard in a forced position binds nothing at all, there being no
    -- binder to take and no name asked for.
  , testCase "a wildcard in a forced position binds nothing" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (vecModule ++
            [ "vtailW : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
            , "vtailW = \\ A n v -> induction v of { vcons _ a as -> as }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))

    -- __TWO forced positions, which is the shape the corpus is made of__: an
    -- inversion lemma over an indexed family whose index is pinned to a
    -- two-argument constructor form. @okNode@ takes four arguments and the
    -- equation @Eq Tr (node a b) (node p q)@ decomposes by injectivity into two
    -- that are then solved, so @a@ and @b@ are both definitions and only the two
    -- sub-derivations are binders. It computes, which is what says the methods
    -- went to the right constructors.
  , testCase "an inversion lemma forces two positions and still computes" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (okModule ++
            [ "left : \8704 (p q : Tr) -> Ok (node p q) -> Ok p"
            , "left = \\ p q d -> induction d of { okNode a b da db -> da }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1
            ":whnf left leaf leaf (okNode leaf leaf okLeaf okLeaf)"
      unwords (renderResponse s2 q) @?= "okLeaf"

    -- __TWO HYPOTHESES, AND THE CALL SAYS WHICH__ (MS9 phase 186). @okNode@
    -- has two recursive arguments, so the arm has a hypothesis about each; the
    -- call names @da@, so it is that one, and nothing had to be told. This is
    -- the case where selection by /type/ would have had two candidates.
  , testCase "a call picks its hypothesis out of two by the argument it names" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (okModule ++
            [ "count : \8704 (t : Tr) -> Ok t -> Nat"
            , "count = \\ t d -> induction d of"
            , "  { okLeaf -> zero ; okNode a b da db -> succ (count a da) }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      -- @:convert@ and not @:whnf@: weak head normal form stops at the
      -- @succ@, so only conversion says the hypothesis reduced to @zero@.
      let (s2, q) = command s1
            ":convert count (node leaf leaf) (okNode leaf leaf okLeaf okLeaf) \
            \\8799 succ zero"
      unwords (words (unwords (renderResponse s2 q))) @?=
        "count (node leaf leaf) (okNode leaf leaf okLeaf okLeaf) \8799 succ zero yes"

    -- __And a call naming both is refused rather than guessed at.__ Which
    -- argument it recurses on is simply not written down, and there is no
    -- ordering to fall back on that would not be arbitrary.
  , refusesIn okModule "a call naming two hypotheses is refused as ambiguous"
      [ "g : Tr -> Tr -> Tr"
      , "g = \\ x y -> induction x of { leaf -> leaf ; node l r -> g l r }"
      ]
      "stuck: this call names 2 arguments that have an induction hypothesis, \
      \so which one it recurses on is not written down: g l r"

    -- __A SPLIT AT A VARIABLE INDEX TIES NOTHING__ (MS9 phase 186, `~7pn6x`),
    -- and this is the case the whole corpus is: every lemma in
    -- @examples\/progress.thena@ splits a derivation whose indices are the
    -- lemma's own variables. Until the fix each arm was handed
    -- @Eq Tr leaf t -> …@, an equation over an ambient variable, which is rigid
    -- and which no specialiser transition can touch.
    --
    -- __It is the tactic's own scaffolding that caused it.__ @induction … of@
    -- cannot know the target's type before elaborating it, so it claims a hole
    -- for the type and a hole for the target; the user's own hypothesis and the
    -- type hole then both mention the index, and the friendliness test counted
    -- them as fixed premises. The regression this guards is therefore invisible
    -- to any test that calls the tactic directly — it needs the surface.
  , testCase "a split at a variable index states no equation" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (okModule ++
            [ "idOk : \8704 (t : Tr) -> Ok t -> Ok t"
            , "idOk = \\ t d -> induction d of"
            , "  { okLeaf -> okLeaf ; okNode a b da db -> okNode a b da db }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf idOk leaf okLeaf"
      unwords (renderResponse s2 q) @?= "okLeaf"

    -- __And two indices, which is `progress`'s own shape__: a derivation
    -- indexed by both the term and its type, with the target bound as a λ
    -- parameter beside them.
  , testCase "and a family with two variable indices" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (okModule ++
            [ "data Ty : Type\8320 where"
            , "  base : Ty"
            , ""
            , "data Has : Tr -> Ty -> Type\8320 where"
            , "  hLeaf : Has leaf base"
            , "  hNode : \8704 (a b : Tr) -> Has a base -> Has b base"
            , "    -> Has (node a b) base"
            , ""
            , "fine : \8704 (t : Tr) (T : Ty) -> Has t T -> Ty"
            , "fine = \\ t T d -> induction d of"
            , "  { hLeaf -> base ; hNode a b da db -> base }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))

    -- __A forced position cannot be destructured__, and that is a limitation of
    -- the feature rather than of this phase: an inaccessible position binds
    -- nothing, so there is nothing for a sub-pattern to match on. @no-nesting@
    -- is the refusal, exactly as it is in a surviving position.
  , refusesIn vecModule "a nested pattern in a forced position is declined"
      [ "vtailN : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
      , "vtailN = \\ A n v -> induction v of { vcons (succ j) a as -> as }"
      ]
      "stuck: no clause of no-nesting applies here"

    -- ----------------------------------------------------------------
    -- @case … of@ WITH ARMS (MS9 phase 188)
    -- ----------------------------------------------------------------

    -- __The same split, through @caseD@ instead of the eliminator.__ The term
    -- is an application of the generated @caseNat@ global rather than an
    -- @Eliminate@ node, so every method is the eliminator's minus its inductive
    -- hypotheses — and @pred@ wants none, which is why this is the honest
    -- spelling of it.
    --
    -- __Checked by reduction__, for the reason @induction@'s own case gives:
    -- only reduction says the methods went to the right constructors, and here
    -- it also says @caseNat@ δ-unfolds to the elimination underneath.
  , testCase "case: a function defined by case analysis declares and computes" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (natModule ++
            [ "predC : Nat -> Nat"
            , "predC = \\ n -> case n of { zero -> zero ; succ m -> m }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf predC (succ (succ zero))"
      unwords (renderResponse s2 q) @?= "succ zero"

    -- __And the term says which word was written.__ @caseNat@ applied, with a
    -- method per constructor and no hypothesis in either.
  , testCase "and the term applies caseNat, not an elim node" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 (unlines (natModule ++
            [ "predC : Nat -> Nat"
            , "predC = \\ n -> case n of { zero -> zero ; succ m -> m }"
            ]))
          (s2, q) = command s1 ":show predC"
          shown   = unwords (renderResponse s2 q)
      assertBool shown ("caseNat" `isInfixOf` shown)

    -- __A RECURSIVE CALL IN A @case@ ARM IS REFUSED, AND BY ITSELF.__ Nothing
    -- checks for it: @caseD@'s methods carry no hypothesis, so there is none
    -- for @tie-recursion@ to tie the call to, and the refusal is the same one a
    -- call on the wrong index gets under @induction@. That is the whole of why
    -- @case@ against @induction@ is a /type/ here and not a convention.
  , refuses "a recursive call in a case arm has no hypothesis to tie to"
      [ "dblC : Nat -> Nat"
      , "dblC = \\ n -> case n of { zero -> zero ; succ m -> succ (succ (dblC m)) }"
      ]
      "stuck: no induction hypothesis is about this call, so it is not \
      \structurally smaller: dblC m"

    -- __The equations and the forced positions are shared__, which is the
    -- claim that the two words differ by hypotheses and nothing else. @vnil@
    -- vanishes on a conflicting equation with no arm written, @vcons@'s own
    -- @k@ is forced to the outer @n@, and the arm binds two of three.
  , testCase "case over an indexed family forces a position the same way" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (vecModule ++
            [ "vtailC : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
            , "vtailC = \\ A n v -> case v of { vcons k a as -> as }"
            ]))
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure (unwords (renderResponse s1 other))
      let (s2, q) = command s1 ":whnf vtailC Nat zero (vcons Nat zero zero (vnil Nat))"
      unwords (renderResponse s2 q) @?= "vnil Nat"

    -- Coverage fails the same way under @case@, and says the same thing.
  , refuses "a case that survived with no arm is refused under case too"
      [ "partialC : Nat -> Nat"
      , "partialC = \\ n -> case n of { zero -> zero }"
      ]
      "stuck: no clause of case-needs-an-arm applies here"
  ]
  where
    natModule =
      [ "module M where", ""
      , "data Nat : Type\8320 where"
      , "  zero : Nat"
      , "  succ : Nat -> Nat"
      , ""
      ]
    -- Phase 191's own shapes: a family whose constructor's index wraps the
    -- recursive one twice, so a split against @Ev (s m)@ leaves @s n@ facing an
    -- @m@ bound outside it and the split has to generalise.
    evModule =
      [ "module Ev where"
      , ""
      , "data N : Type\8320 where"
      , "  z : N"
      , "  s : N -> N"
      , ""
      , "data Ev : N -> Type\8320 where"
      , "  evz : Ev z"
      , "  evs : \8704 (n : N) (e : Ev n) -> Ev (s (s n))"
      , ""
      , "data IsSucc : N -> Type\8320 where"
      , "  isucc : \8704 (n : N) -> IsSucc (s n)"
      , ""
      ]
    -- Phase 197's shape (@~k54hh@): a two-index family whose constructor's
    -- second index wraps its own argument, so a split against @F (s k) u@
    -- leaves @s m@ facing an ambient @u@ and has to generalise it — under an
    -- @induction@ on a /second/ family, which is what puts the previous arm's
    -- solved definitions in the context the split looks at. @fz@ is here only
    -- so that a closed inhabitant exists and the proofs can be computed.
    reachModule =
      [ "module Reach where"
      , ""
      , "data N : Type\8320 where"
      , "  z : N"
      , "  s : N -> N"
      , ""
      , "data F : N -> N -> Type\8320 where"
      , "  fz : F z z"
      , "  fs : \8704 (k : N) (m : N) (r : F k m) -> F (s k) (s m)"
      , ""
      , "data A : N -> Type\8320 where"
      , "  az : A z"
      , "  as : \8704 (k : N) (p : A k) -> A (s k)"
      , ""
      ]
    vecModule =
      natModule ++
      [ "data Vec (A : Type\8320) : Nat -> Type\8320 where"
      , "  vnil : Vec A zero"
      , "  vcons : \8704 (k : Nat) (a : A) (as : Vec A k) -> Vec A (succ k)"
      , ""
      ]
    okModule =
      natModule ++
      [ "data Tr : Type\8320 where"
      , "  leaf : Tr"
      , "  node : Tr -> Tr -> Tr"
      , ""
      , "data Ok : Tr -> Type\8320 where"
      , "  okLeaf : Ok leaf"
      , "  okNode : \8704 (a b : Tr) -> Ok a -> Ok b -> Ok (node a b)"
      , ""
      ]
    vtailDef =
      [ "vtail : \8704 (A : Type\8320) (n : Nat) -> Vec A (succ n) -> Vec A n"
      , "vtail = \\ A n v -> induction v of { vcons k a as -> as }"
      ]
    predDef =
      [ "pred : Nat -> Nat"
      , "pred = \\ n -> induction n of { zero -> zero ; succ m -> m }"
      ]

    refuses = refusesIn natModule

    refusesIn prefix what ls want = testCase what $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines (prefix ++ ls))
          said = filter (not . null) (renderResponse s1 r)
      case said of
        [] -> assertFailure "it loaded, and should not have"
        rs -> unwords (words (last rs)) @?= want
