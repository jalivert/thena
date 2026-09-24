-- | Object terms in @instral@ — as operands, and as patterns (MS6 phase 104c;
-- @ms6\/SPEC.md@ §8).
--
-- **The fixture is the realistic one, and it is the phase's whole point**: a
-- surface module declares the grammar, and a rule base is loaded /after/ it,
-- so the grammar is on the machine when the base is read. That is what phase
-- 104b's ordering made possible.
--
-- **The load-bearing test is 'matchesThroughDefinition'**: the pattern is
-- matched against a global whose body is the chain of @let@s elaboration
-- leaves. Matching it needs the term tried as written, then reduced and tried
-- again — his rule of 2026-09-20 — so a matcher that only compared shapes, and
-- one that only compared reduced shapes, both fail it.
module Thena.ObjectTermTests (tests) where

import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver
  (Response (..), Session (..), loadProofSource, loadRuleBases)
import Thena.Engine (Machine (..))
import Thena.Instral.Ops
  ( Instr (..)
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Pattern (..)
  , Skeleton (..)
  , Slot (..)
  , Value (..)
  , matchPattern
  , operandIn
  )
import Thena.Rules (RuleBase (..))
import Thena.Repl (rulesPath, startingSession)

tests :: TestTree
tests =
  withResource loadedModule (const (pure ())) $ \io ->
    testGroup
      "object terms in instral (\167\&8)"
      [ testGroup "a rule file sees a grammar loaded before it" (reading io)
      , testGroup "what a pattern matches" (matching io)
      , testGroup "what an operand builds" (building io)
      ]

-- ---------------------------------------------------------------------------

-- | The module that declares the language, and one term of it.
languageModule :: String
languageModule =
  unlines
    [ "module Lang where"
    , ""
    , "x : Token String"
    , "x = /[a-z]+/"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  app                   -> ( M N )"
    , ""
    , "fg : LC"
    , "fg = LC`( f g )`"
    ]

-- | The session with it loaded, and the shipped base's text beside it.
loadedModule :: IO (Session, String)
loadedModule = do
  (s0, _) <- startingSession
  shipped <- rulesPath >>= readFile
  case loadProofSource s0 languageModule of
    (s1, ProofLoaded {}) -> pure (s1, shipped)
    (_, other) -> assertFailure (show other)

-- | Load a rule base of one's own beside the shipped one, and hand back its
-- rules — or the response, when it was refused.
withRules :: IO (Session, String) -> String -> IO (Either Response [Rule])
withRules io src = do
  (s, shipped) <- io
  pure $ case loadRuleBases s [("shipped", shipped), ("mine", src)] of
    (s', BasesLoaded _) ->
      Right (concatMap baseRules (filter ((== "mine") . baseName) (rules (sessionMachine s'))))
    (_, other) -> Left other

-- | The one rule a base of one's own declared.
oneRule :: IO (Session, String) -> String -> IO Rule
oneRule io src = withRules io src >>= \r -> case r of
  Right (x : _) -> pure x
  Right []      -> assertFailure "the base declared no rule"
  Left other    -> assertFailure (show other)

refused :: IO (Session, String) -> String -> IO Response
refused io src = withRules io src >>= \r -> case r of
  Left other -> pure other
  Right _    -> assertFailure "it loaded, and should not have"

base :: String -> String
base body = "rule base mine where\n\n" ++ body ++ "\n"

-- ---------------------------------------------------------------------------

reading :: IO (Session, String) -> [TestTree]
reading io =
  [ -- **The grammar is consulted once, here.** What the clause keeps is the
    -- shape, with a hole where each splice was and the slot it stands at.
    testCase "a pattern resolves to the shape its production denotes" $ do
      r <- oneRule io (base "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"")
      ruleParams r
        @?= [ PObject (SNode (GlobalName "app")
                         [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ]) ]

  , testCase "and a token class's text resolves to the literal it denotes" $ do
      r <- oneRule io (base "rule v LC[var]`x` :- do say \"x\"")
      ruleParams r
        @?= [PObject (SNode (GlobalName "var") [SLit (LString "x")])]

    -- **A hole at a token class binds an @instral@ value, not a term** — the
    -- slot's type, which is what 104b's ordering made knowable at load.
  , testCase "a hole at a token class is typed String" $ do
      r <- oneRule io (base "rule v LC[var]`${s}` :- do say s")
      ruleParams r
        @?= [PObject (SNode (GlobalName "var") [SHole (AtPrimitive (GlobalName "String")) (PVar "s")])]

  , testCase "and using it as a term is a type error when the base loads" $ do
      r <- refused io (base "rule v LC[var]`${s}` :- do fill s")
      case r of
        BasesIllTyped (_ : _) -> pure ()
        other -> assertFailure (show other)

  , testCase "a tag naming no language is refused" $ do
      r <- refused io (base "rule v Nope`x` :- do say \"x\"")
      case r of
        RuleFileRefused _ _ -> pure ()
        other -> assertFailure (show other)

  , testCase "so is a production the language does not have" $ do
      r <- refused io (base "rule v LC[nope]`x` :- do say \"x\"")
      case r of
        RuleFileRefused _ _ -> pure ()
        other -> assertFailure (show other)

  , testCase "and text the grammar cannot read" $ do
      r <- refused io (base "rule v LC`( f` :- do say \"x\"")
      case r of
        RuleFileRefused _ _ -> pure ()
        other -> assertFailure (show other)
  ]

-- ---------------------------------------------------------------------------

matching :: IO (Session, String) -> [TestTree]
matching io =
  [ -- **THE test of the phase.** @fg@ is a global whose body is the chain of
    -- @let@s elaboration leaves, so the pattern matches only if the term is
    -- tried as written, then reduced and tried again.
    testCase "it matches through a definition and its let-chain" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      case matchPattern env p (VTerm (Global (GlobalName "fg") [])) of
        Just bs -> map fst bs @?= ["f", "a"]
        Nothing -> assertFailure "it did not match"

  , testCase "and it matches the same term written out" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      let t = con "app" [con "var" [Primitive (LString "f")], con "var" [Primitive (LString "g")]]
      case matchPattern env p (VTerm t) of
        Just bs -> map snd bs @?= [VTerm (con "var" [Primitive (LString "f")])
                                  , VTerm (con "var" [Primitive (LString "g")])]
        Nothing -> assertFailure "it did not match"

  , testCase "a hole at a token class binds the literal as a String" $ do
      (env, p) <- setup "rule v LC[var]`${s}` :- do say s"
      matchPattern env p (VTerm (con "var" [Primitive (LString "f")]))
        @?= Just [("s", VText "f")]

  , testCase "a written token matches only itself" $ do
      (env, p) <- setup "rule v LC[var]`x` :- do say \"x\""
      ( matchPattern env p (VTerm (con "var" [Primitive (LString "x")]))
        , matchPattern env p (VTerm (con "var" [Primitive (LString "y")])) )
        @?= (Just [], Nothing)

    -- **An arity is part of the shape.** The wrapper on its own is a term of
    -- the right name and the wrong length, and the walk over the arguments
    -- would bind nothing at all rather than refusing it.
  , testCase "a constructor applied to too few arguments does not match" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      ( matchPattern env p (VTerm (Global (GlobalName "app") []))
        , matchPattern env p (VTerm (con "app" [con "var" [Primitive (LString "f")]])) )
        @?= (Nothing, Nothing)

    -- **The brackets restrict here too**, as they do in a surface literal.
  , testCase "a production's pattern does not match another production" $ do
      (env, p) <- setup "rule v LC[var]`${s}` :- do say s"
      let t = con "app" [con "var" [Primitive (LString "f")], con "var" [Primitive (LString "g")]]
      matchPattern env p (VTerm t) @?= Nothing
  ]
  where
    setup src = do
      (s, _) <- io
      r <- oneRule io (base src)
      case ruleParams r of
        p : _ -> pure (globals (sessionMachine s), p)
        []    -> assertFailure "the rule has no parameter"

-- ---------------------------------------------------------------------------

building :: IO (Session, String) -> [TestTree]
building io =
  [ -- **With no splices the term is known when the file loads**, so the
    -- operand is a value and not an expression.
    testCase "a region with no splices is a value" $ do
      o <- operandOfRule "rule lit x :- do t = LC`( f g )` ; say \"x\""
      case o of
        Lit (VTerm t) ->
          t @?= con "app" [con "var" [Primitive (LString "f")], con "var" [Primitive (LString "g")]]
        other -> assertFailure (show other)

  , testCase "and one with splices is assembled when it is read" $ do
      o <- operandOfRule "rule lit x :- do t = LC[var]`${x}` ; say \"x\""
      operandIn [("x", VText "zzz")] o
        @?= Right (VTerm (con "var" [Primitive (LString "zzz")]))

    -- **What keeps a hole honest is the check at load, not the assembly.** The
    -- fold writes whichever literal the value is, and a body that puts the
    -- wrong kind there never gets that far.
  , testCase "the wrong kind at a token class is refused when the base loads" $ do
      r <- refused io (base "rule lit x :- do t = LC[var]`${x}` ; fill x")
      case r of
        BasesIllTyped (_ : _) -> pure ()
        other -> assertFailure (show other)
  ]
  where
    operandOfRule src = do
      r <- oneRule io (base src)
      case [ o | Bind _ _ (Value o) <- ruleBody r ] of
        o : _ -> pure o
        []    -> assertFailure "the rule binds nothing"

con :: String -> [Core] -> Core
con name = foldl App (Global (GlobalName name) [])
