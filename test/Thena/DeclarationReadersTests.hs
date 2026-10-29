-- | The six ops that read a declaration back (MS9 phase 176).
--
-- **Until this phase @make-data@ could declare a datatype and nothing could
-- read one.** A splitting tree asks, at every node, which constructors a family
-- has and what each one's arguments are called; `~kq4kc` cannot start without
-- a way to ask.
--
-- **Driven at the machine, like "Thena.EngineTests", and not through the
-- REPL.** Two of the six answer with an 'Ops.VInt', and @say@ takes text — so a
-- rule base cannot observe a count at all today. Running the op and reading
-- @env@ tests the op; running it through a rule would only test the plumbing,
-- and would leave a third of the vocabulary unasserted.
--
-- **The environment is "Thena.Declared"'s @natVec@**, so these agree with the
-- core suites about what @Nat@ and @Vec@ are rather than transcribing them a
-- second time.
module Thena.DeclarationReadersTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core)
import Thena.Core.Trust (TrustLevel (..))
import Thena.Declared (natVec, natVecCounter)
import Thena.Driver (parseCore)
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , env
  , load
  , newDevelopment
  , step
  )
import Thena.Errors (FailReason (..))
import Thena.Instral.Ops (Instr (..), Op (..), Operand (..), Pattern (..), Value (..))
import Thena.Standard (expectedBase)

-- | A machine over @Nat@ and @Vec@, with the name counter those declarations
-- left behind.
machine :: [Instr] -> Machine
machine is =
  load is (Machine (Exec [] [] []) ps [] natVec expectedBase [] [] n 0
                   NoUndischargeableTrust)
  where
    (ps, n) = newDevelopment natVecCounter

-- | Run one op and hand back what it bound to @it@.
--
-- The op is the whole program, so the machine reaches 'Finished' and @env@
-- holds the answer. A failure comes back as the reason, which is what the
-- refusal cases assert on.
ran :: Op -> Either FailReason Value
ran o = go (machine [Bind (PVar "it") Nothing o])
  where
    go m = case step m of
      Continue m' -> go m'
      Finished m' -> case lookup "it" (env (exec m')) of
        Just v  -> Right v
        Nothing -> error "the op bound nothing"
      Stuck r _ -> Left r
      other     -> error ("unexpected outcome: " ++ show other)

-- | A core term, parsed in @natVec@ exactly as a user would write it.
term :: String -> Core
term src = case parseCore [] natVec [] natVecCounter src of
  Left e        -> error ("fixture does not parse: " ++ show e)
  Right (t, _)  -> t

ty :: String -> Operand
ty = Lit . VTerm . term

name :: String -> Operand
name = Lit . VText

-- | The names in a 'VList', or a failure saying what came back instead.
nameList :: Either FailReason Value -> IO [String]
nameList r = case r of
  Right (VList vs) -> traverse one vs
  other            -> assertFailure ("expected a list of names, got " ++ show other)
  where
    one v = case v of
      VText w -> pure w
      _       -> assertFailure ("expected a name in the list, got " ++ show v)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral — reading a declaration"
    [ datatypeOf
    , counts
    , constructors
    , refusals
    ]

-- | **The one that has to reduce**, and the reason it shares
-- "Thena.Tactics.Eliminate"'s @spineOf@.
datatypeOf :: TestTree
datatypeOf =
  testGroup
    "datatype-of"
    [ testCase "a bare datatype is its own head" $
        ran (DatatypeOf (ty "Nat")) @?= Right (VText "Nat")

      -- **§12 invariant 6, and the case that makes this op non-trivial.** A
      -- user writes @Vec Nat zero@, which resolves to nested applications over
      -- the generated former wrapper; only after δ unfolds it and β saturates
      -- it is the term the 'Thena.Core.Term.Canonical' that carries the
      -- datatype's name. Reading the written form alone answers /"that type is
      -- not a datatype"/ about a datatype.
    , testCase "a saturated family application reduces to its head" $
        ran (DatatypeOf (ty "Vec Nat zero")) @?= Right (VText "Vec")

    , testCase "and so does a partially applied one" $
        ran (DatatypeOf (ty "Vec Nat")) @?= Right (VText "Vec")

      -- A universe has a head and it is not a declared family.
    , testCase "a universe is refused, and named" $
        ran (DatatypeOf (ty "Type\8320"))
          @?= Left (NotDeclaredAs "that type" "a datatype")
    ]

-- | The two counts, which are the only reason this suite is at the machine and
-- not in a rule base: nothing in @instral@ can @say@ an 'VInt'.
counts :: TestTree
counts =
  testGroup
    "the parameter and index counts"
    [ testCase "Vec has one parameter" $
        ran (DatatypeParameters (name "Vec")) @?= Right (VInt 1)

    , testCase "and one index" $
        ran (DatatypeIndices (name "Vec")) @?= Right (VInt 1)

      -- **The pair that would be wrong if the two ops were one accessor.**
      -- @Nat@ has neither, so a reader that answered with a telescope's length
      -- for the wrong half would still say @0@ here and only @Vec@ tells them
      -- apart.
    , testCase "Nat has no parameters" $
        ran (DatatypeParameters (name "Nat")) @?= Right (VInt 0)

    , testCase "and no indices" $
        ran (DatatypeIndices (name "Nat")) @?= Right (VInt 0)
    ]

constructors :: TestTree
constructors =
  testGroup
    "the constructors"
    [ -- **Declaration order, and it is load-bearing**: it is the order the
      -- eliminator's methods are in, so a rule walking methods and a rule
      -- walking constructors agree without either being told.
      testCase "in declaration order" $ do
        cs <- nameList (ran (ConstructorsOf (name "Nat")))
        cs @?= ["zero", "succ"]

    , testCase "and for a family with a parameter" $ do
        cs <- nameList (ran (ConstructorsOf (name "Vec")))
        cs @?= ["nil", "cons"]

    , testCase "a constructor knows its datatype" $
        ran (ConstructorDatatype (name "succ")) @?= Right (VText "Nat")

    , testCase "including one of a parameterised family" $
        ran (ConstructorDatatype (name "cons")) @?= Right (VText "Vec")

      -- The argument names, which is what a split names its pattern variables
      -- after. **The parameter is not among them** — @A@ is @Vec@'s and not
      -- @cons@'s, which is §3.7's split showing up in the answer.
    , testCase "a constructor's arguments are named, parameters excluded" $ do
        as <- nameList (ran (ConstructorArguments (name "cons")))
        as @?= ["n", "a", "as"]

    , testCase "a nullary constructor has none" $ do
        as <- nameList (ran (ConstructorArguments (name "zero")))
        as @?= []

    , testCase "and so does nil, whose family has a parameter" $ do
        as <- nameList (ran (ConstructorArguments (name "nil")))
        as @?= []

      -- @succ : Nat -> Nat@ is written as an arrow, so its one argument has no
      -- name in the source. **The count is still right**, which is what a
      -- pattern's arity is read from; what it is called is the resolver's.
    , testCase "an unnamed argument still counts" $ do
        as <- nameList (ran (ConstructorArguments (name "succ")))
        length as @?= 1
    ]

-- | **Failing is an answer here**, not just an error: @constructor-datatype@
-- refusing a name /is/ "that name is not a constructor", which is how a
-- splitting rule tells a constructor pattern from a variable one without a
-- test of its own.
refusals :: TestTree
refusals =
  testGroup
    "what each reader refuses"
    [ testCase "a datatype is not a constructor" $
        ran (ConstructorDatatype (name "Nat"))
          @?= Left (NotDeclaredAs "Nat" "a constructor")

    , testCase "nor are its arguments askable" $
        ran (ConstructorArguments (name "Vec"))
          @?= Left (NotDeclaredAs "Vec" "a constructor")

    , testCase "a constructor is not a datatype" $
        ran (ConstructorsOf (name "succ"))
          @?= Left (NotDeclaredAs "succ" "a datatype")

    , testCase "and neither are its parameters countable" $
        ran (DatatypeParameters (name "succ"))
          @?= Left (NotDeclaredAs "succ" "a datatype")

    , testCase "a name nothing declared" $
        ran (ConstructorsOf (name "Nonesuch"))
          @?= Left (NotDeclaredAs "Nonesuch" "a datatype")

    , testCase "and the same name as a constructor" $
        ran (ConstructorDatatype (name "Nonesuch"))
          @?= Left (NotDeclaredAs "Nonesuch" "a constructor")
    ]
