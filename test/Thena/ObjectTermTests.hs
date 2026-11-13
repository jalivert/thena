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

import Thena.Core.Term (Core (..), Literal (..), rootName)
import Thena.Declared (named)
import Thena.Driver
  ( Leniency (..)
  , Response (..)
  , Session
  , machineOf
  , loadRuleTexts
  )
import Thena.Engine (Machine (..), rules)
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
import Thena.Files (loadProofFile, rulesPath, startingSession)

tests :: TestTree
tests =
  withResource loadedModule (const (pure ())) $ \io ->
    testGroup
      "object terms in instral (\167\&8)"
      [ testGroup "a rule file sees a grammar loaded before it" (reading io)
      , testGroup "a rule file writes its own open lines" opening
      , testGroup "what a pattern matches" (matching io)
      , testGroup "what an operand builds" (building io)
      ]

-- ---------------------------------------------------------------------------

-- | __The module that declares the language, and one term of it__ —
-- @test\/modules\/Rooted.thena@.
--
-- **It is a file on disc and was a string here until MS11 phase 297.** A rule
-- file states what it refers to now, so a base reaches a language only by
-- importing the module that declares it — and a module has a name to import
-- only when it was reached by one. 'Thena.Driver.loadProofSource' reaches a
-- module by no name at all, so nothing loaded that way can be imported, which
-- is 'Thena.Driver.sessionDeclaredBy''s own rule and not this phase's.
languageModule :: FilePath
languageModule = "test/modules/Rooted.thena"

-- | What a base written against it has to say first.
languageImport :: String
languageImport = "import test.modules.Rooted"

-- | The session with it loaded, and the shipped base's text beside it.
loadedModule :: IO (Session, String)
loadedModule = do
  (s0, _) <- startingSession
  shipped <- rulesPath >>= readFile
  (s1, out, trouble) <- loadProofFile Strict s0 languageModule
  case (trouble, [ () | ProofLoaded {} <- out ]) of
    ([], _ : _) -> pure (s1, shipped)
    _           -> assertFailure (show out)

-- | Load a rule base of one's own beside the shipped one, and hand back its
-- rules — or the response, when it was refused.
withRules :: IO (Session, String) -> String -> IO (Either Response [Rule])
withRules io src = do
  (s, shipped) <- io
  pure $ case loadRuleTexts s [("shipped", shipped), ("mine", src)] of
    (s', BasesLoaded _ _) ->
      Right (concatMap baseRules (filter ((== "mine") . baseName) (rules (machineOf s'))))
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
base = baseOf languageImport

-- | The same, for a base written against some other module (MS11 phase 297).
baseOf :: String -> String -> String
baseOf stated body =
  "rule base mine where\n\n" ++ stated ++ "\n\n" ++ body ++ "\n"

-- ---------------------------------------------------------------------------

reading :: IO (Session, String) -> [TestTree]
reading io =
  [ -- **The grammar is consulted once, here.** What the clause keeps is the
    -- shape, with a hole where each splice was and the slot it stands at.
    testCase "a pattern resolves to the shape its production denotes" $ do
      r <- oneRule io (base "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"")
      ruleParams r
        @?= [ PObject (SNode (named "test.modules.Rooted.LC.app")
                         [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ]) ]

  , testCase "and a token class's text resolves to the literal it denotes" $ do
      r <- oneRule io (base "rule v LC[var]`x` :- do say \"x\"")
      ruleParams r
        @?= [PObject (SNode (named "test.modules.Rooted.LC.var") [SLit (LString "x")])]

    -- **A hole at a token class binds an @instral@ value, not a term** — the
    -- slot's type, which is what 104b's ordering made knowable at load.
  , testCase "a hole at a token class is typed String" $ do
      r <- oneRule io (base "rule v LC[var]`${s}` :- do say s")
      ruleParams r
        @?= [PObject (SNode (named "test.modules.Rooted.LC.var") [SHole (AtPrimitive (rootName "String")) (PVar "s")])]

  , testCase "and using it as a term is a type error when the base loads" $ do
      r <- refused io (base "rule v LC[var]`${s}` :- do fill s")
      case r of
        BasesIllTyped (_ : _) -> pure ()
        other -> assertFailure (show other)

    -- **A TAG RESOLVES LIKE ANY OTHER NAME** (MS10 phase 260, `~zjkvd`), so a
    -- language in a namespace is reached by its path and the pattern's shape
    -- carries the production's whole name.
    --
    -- **This is the one that must not move when a scope arrives** (MS10 phase
    -- 267): a written whole name resolves under any scope, so a rule file that
    -- opens nothing reads exactly as it did when a tag had to be whole. The
    -- @open@ forms are in 'opening' below.
  , testCase "a rule file reaches a namespaced language by its path" $ do
      r <- inNamespaces oneNamespace
             [ "rule swap A.LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      case r of
        Right (x : _) -> ruleParams x
          @?= [ PObject (SNode (named "test.modules.OneNested.A.LC.app")
                           [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ]) ]
        Right []   -> assertFailure "the base declared no rule"
        Left other -> assertFailure (show other)

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

-- | **A rule file writes its own @open@ lines** (MS10 phase 267), which is the
-- piece of `~jmw4k` his decision of 2026-11-03 pulled forward into MS10.
--
-- **Every test here is a pair**: the short spelling under an @open@, and the
-- same text without it. That is deliberate — a test that only shows the short
-- spelling working cannot tell a scope that was honoured from a word that
-- happened to resolve anyway.
--
-- The fixture is its own, and not 'loadedModule''s: what the phase is for is a
-- language that lives inside a @namespace@, and @Lang@ declares one at the root.
opening :: [TestTree]
opening =
  [ testCase "open A reaches a language declared inside A" $ do
      r <- inNamespaces oneNamespace
             [ "open A", "", "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      shapeOf r @?= Right (SNode (named "test.modules.OneNested.A.LC.app")
                             [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ])

    -- **The pair.** Nothing else changes, so what the test above measures is
    -- the @open@ and not the tag.
  , testCase "and without the open the same word reaches nothing" $ do
      r <- inNamespaces oneNamespace
             [ "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      refusal r

  , testCase "open A renaming ( LC -> L ) renames the tag" $ do
      r <- inNamespaces oneNamespace
             [ "open A renaming ( LC -> L )", ""
             , "rule swap L[app]`( ${f} ${a} )` :- do say \"x\"" ]
      shapeOf r @?= Right (SNode (named "test.modules.OneNested.A.LC.app")
                             [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ])

  , testCase "and the word it was renamed from no longer reaches it" $ do
      r <- inNamespaces oneNamespace
             [ "open A renaming ( LC -> L )", ""
             , "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      refusal r

  , testCase "open A ( LC ) selects the language" $ do
      r <- inNamespaces oneNamespace
             [ "open A ( LC )", ""
             , "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      shapeOf r @?= Right (SNode (named "test.modules.OneNested.A.LC.app")
                             [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ])

  , testCase "and open A hiding ( LC ) keeps it out" $ do
      r <- inNamespaces oneNamespace
             [ "open A hiding ( LC )", ""
             , "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      refusal r

    -- **Two namespaces answering one word is refused and not chosen**, which
    -- is 'Thena.Core.Term.globalUnder''s own answer: either would parse, so
    -- picking one would be the system deciding what the author did not write.
  , testCase "two opened namespaces answering one tag is refused" $ do
      r <- inNamespaces twoNamespaces
             [ "open A", "open B", ""
             , "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      refusal r

  , testCase "and the path still says which was meant" $ do
      r <- inNamespaces twoNamespaces
             [ "open A", "open B", ""
             , "rule swap B.LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      shapeOf r @?= Right (SNode (named "test.modules.TwoNested.B.LC.app")
                             [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ])

    -- **@open X in ‹declaration›@ reaches that declaration and stops**, which
    -- is the fifth of the forms his ruling of 2026-10-30 gave the surface
    -- language. A rule file's declarations are independent, so what it covers
    -- is one rule.
  , testCase "open A in reaches the declaration under it" $ do
      r <- inNamespaces oneNamespace
             [ "open A in"
             , "  rule swap LC[app]`( ${f} ${a} )` :- do say \"x\"" ]
      shapeOf r @?= Right (SNode (named "test.modules.OneNested.A.LC.app")
                             [ SHole AtTerm (PVar "f"), SHole AtTerm (PVar "a") ])

  , testCase "and not the declaration after it" $ do
      r <- inNamespaces oneNamespace
             [ "open A in"
             , "  rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
             , "rule other LC[app]`( ${f} ${a} )` :- do say \"y\"" ]
      refusal r
  ]
  where
    shapeOf r = case r of
      Right (x : _) -> case ruleParams x of
        PObject sk : _ -> Right sk
        ps             -> Left ("the rule's parameters were " ++ show ps)
      Right []   -> Left "the base declared no rule"
      Left other -> Left (show other)

    refusal r = case r of
      Left (RuleFileRefused _ _) -> pure ()
      Left other -> assertFailure (show other)
      Right _    -> assertFailure "it loaded, and should not have"

-- | One namespace holding one language, which is the shape the phase exists
-- for; and two, so that one word can be reached from both.
--
-- **Files on disc since MS11 phase 297**, for 'languageModule''s reason: a base
-- may only reach a language it imports, and there is nothing to import until
-- the module has been reached by a name.
oneNamespace, twoNamespaces :: (FilePath, String)
oneNamespace  = ( "test/modules/OneNested.thena"
                , "import test.modules.OneNested" )
twoNamespaces = ( "test/modules/TwoNested.thena"
                , "import test.modules.TwoNested" )

-- | Load a module of namespaced languages, then a rule base written against it.
inNamespaces :: (FilePath, String) -> [String] -> IO (Either Response [Rule])
inNamespaces (path, stated) body = do
  (s0, _) <- startingSession
  shipped <- rulesPath >>= readFile
  (s1, out, trouble) <- loadProofFile Strict s0 path
  case (trouble, [ () | ProofLoaded {} <- out ]) of
    ([], _ : _) -> withRules (pure (s1, shipped)) (baseOf stated (unlines body))
    _           -> assertFailure (show out)

-- ---------------------------------------------------------------------------

matching :: IO (Session, String) -> [TestTree]
matching io =
  [ -- **THE test of the phase.** @fg@ is a global whose body is the chain of
    -- @let@s elaboration leaves, so the pattern matches only if the term is
    -- tried as written, then reduced and tried again.
    testCase "it matches through a definition and its let-chain" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      case matchPattern env p (VTerm (Global (named "test.modules.Rooted.fg") [])) of
        Just bs -> map fst bs @?= ["f", "a"]
        Nothing -> assertFailure "it did not match"

  , testCase "and it matches the same term written out" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      let t = con "LC.app" [con "LC.var" [Primitive (LString "f")], con "LC.var" [Primitive (LString "g")]]
      case matchPattern env p (VTerm t) of
        Just bs -> map snd bs @?= [VTerm (con "LC.var" [Primitive (LString "f")])
                                  , VTerm (con "LC.var" [Primitive (LString "g")])]
        Nothing -> assertFailure "it did not match"

  , testCase "a hole at a token class binds the literal as a String" $ do
      (env, p) <- setup "rule v LC[var]`${s}` :- do say s"
      matchPattern env p (VTerm (con "LC.var" [Primitive (LString "f")]))
        @?= Just [("s", VText "f")]

  , testCase "a written token matches only itself" $ do
      (env, p) <- setup "rule v LC[var]`x` :- do say \"x\""
      ( matchPattern env p (VTerm (con "LC.var" [Primitive (LString "x")]))
        , matchPattern env p (VTerm (con "LC.var" [Primitive (LString "y")])) )
        @?= (Just [], Nothing)

    -- **An arity is part of the shape.** The wrapper on its own is a term of
    -- the right name and the wrong length, and the walk over the arguments
    -- would bind nothing at all rather than refusing it.
  , testCase "a constructor applied to too few arguments does not match" $ do
      (env, p) <- setup "rule swap LC[app]`( ${f} ${a} )` :- do say \"x\""
      ( matchPattern env p (VTerm (Global (named "test.modules.Rooted.LC.app") []))
        , matchPattern env p (VTerm (con "LC.app" [con "LC.var" [Primitive (LString "f")]])) )
        @?= (Nothing, Nothing)

    -- **The brackets restrict here too**, as they do in a surface literal.
  , testCase "a production's pattern does not match another production" $ do
      (env, p) <- setup "rule v LC[var]`${s}` :- do say s"
      let t = con "LC.app" [con "LC.var" [Primitive (LString "f")], con "LC.var" [Primitive (LString "g")]]
      matchPattern env p (VTerm t) @?= Nothing
  ]
  where
    setup src = do
      (s, _) <- io
      r <- oneRule io (base src)
      case ruleParams r of
        p : _ -> pure (globals (machineOf s), p)
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
          t @?= con "LC.app" [con "LC.var" [Primitive (LString "f")], con "LC.var" [Primitive (LString "g")]]
        other -> assertFailure (show other)

  , testCase "and one with splices is assembled when it is read" $ do
      o <- operandOfRule "rule lit x :- do t = LC[var]`${x}` ; say \"x\""
      operandIn [("x", VText "zzz")] o
        @?= Right (VTerm (con "LC.var" [Primitive (LString "zzz")]))

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

-- **Under the fixture module's own namespace** (MS12 phase 313):
-- @test/modules/Rooted.thena@ is @module test.modules.Rooted where@.
con :: String -> [Core] -> Core
con name = foldl App (Global (named ("test.modules.Rooted." ++ name)) [])
