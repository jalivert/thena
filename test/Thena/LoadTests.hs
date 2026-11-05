-- | Loading a file, and the prelude (§9, phase 11).
--
-- **A file is a script of command lines** — decided by the user 2026-08-22. So
-- most of this suite is about 'loadSource', which is pure and takes contents
-- rather than a path (§12 invariant 4 keeps IO in "Thena.Repl"). The two cases
-- that must touch the disk are the shipped prelude ones, and they go through
-- 'loadPrelude' — the same function @repl@ calls at startup, so they fail if
-- the @data-files@ wiring is wrong rather than only if the parser is.
--
-- **The golden transcripts do not load the prelude and this suite does.**
-- 'Thena.Repl.transcript' starts from a bare 'newSession' on purpose: it is the
-- harness for the loop, the existing scripts declare their own @Nat@ and
-- @Empty@, and the prelude's own @Empty@ would collide with phase 10's. That
-- divergence from the real @repl@ is covered here instead — see
-- 'preludeIsInTheWay'.
module Thena.LoadTests (tests) where

import Data.Maybe (isJust)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Data.List (isInfixOf, nub)

import Thena.Core.Level (Level (..), instantiateLevels)
import Thena.Core.Term (Core (..), rootName)
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..), Warning (..))
import Thena.Declared (declaredAs, named)
import Thena.Driver
  ( CommandError (..)
  , LoadError (..)
  , Loaded (..)
  , LoadKind (..)
  , Response (..)
  , RuleFileError (..)
  , Session
  , machineOf
  , pendingQuestion
  , Stop (..)
  , command
  , kindOf
  , loadProofSource
  , loadRuleBases
  , loadSource
  , moduleImports
  , moduleLoaded
  , moduleName
  , moduleOfFile
  , modulesLoaded
  , moduleText
  , declaredByModule
  , ModuleName
  , moduleDeclaring
  , preludeModule
  , concealedFrom
  , openedByModule
  , openedFrom
  , newSession
  , oneLine
  , parseSurfaceModule
  )
import Thena.Engine (Development, Machine (..), development)
import Thena.Files (rulesPath)
import Thena.Core.Term (nameDotted, openedPath, substLevelsIn)
import qualified Thena.Global.Env as Env (declaredNames)
import Thena.Global.Env
  ( Definition (..)
  , lookupDefinition
  , InductiveDefinition
  , eliminatorType
  , inductiveLevels
  , isDeclared
  , lookupInductive
  )
import Thena.Global.Declare (DeclareError (..))
import Thena.Files (Trouble (..), consultRuleFiles, following, loadProofFile, startingSession)
import Thena.Render
  ( rendering
  ,renderTrouble, renderResponse, renderCore, renderEliminator)
import Thena.Core.Convert (convert)
import Thena.Core.Context ()
import Thena.Standard (withRules)
import Thena.Rules (RuleError (..))
import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty.Golden (goldenVsString)

tests :: TestTree
tests =
  testGroup
    "loading a file (§9, phase 11)"
    [ testGroup "the shipped prelude" preludeTests
    , testGroup "a file is a script of command lines" scriptTests
    , testGroup "a load stops, and says where" failureTests
    , testGroup "three kinds behind one word (phase 43)" kindTests
    , testGroup "a proof module (phase 43)" moduleTests
    , testGroup "MS4 tier 0 (phase 43)" tierTests
    , testGroup "a namespace block (MS10 phase 254)" namespaceTests
    , testGroup "the five forms of open (MS10 phase 254)" openTests
    , testGroup "shadowing is announced (MS10 phase 264)" shadowingTests
    , testGroup "an import graph (MS11 phase 274)" importTests
    , testGroup "a rule base states what it depends on (MS11 phase 276)" baseImportTests
    , testGroup "a module sees its imports and the prelude (MS11 phase 282)" isolationTests
    , testGroup "a file does not end its own opens (MS11 phase 283)" openIsolationTests
    , testGroup "import and consult at the prompt (MS11 phase 284)" promptActTests
    ]

-- --------------------------------------------------------------------------
-- A module resolves against its imports, its own declarations and the
-- prelude (MS11 phase 282, @~xdt8c@)
-- --------------------------------------------------------------------------

-- | __His ruling of 2026-11-05, measured from both sides__: what a module may
-- reach and what it may not.
--
-- *"A correct file is correct only if it can be type-checked in isolation
-- relying only on what it imports and defines."* Every test here would have
-- passed before the phase — the session held everything — so what each one
-- pins is the refusal, or that something the ruling keeps did not go with it.
-- | A module name from text, for a test that knows the text is one.
named' :: String -> ModuleName
named' t = case moduleName t of
  Just m  -> m
  Nothing -> error ("not a module name: " ++ t)

isolationTests :: [TestTree]
isolationTests =
  [ -- **The hack itself, and it is gone.** @Bit@ is in the session and the
    -- module does not import it, so its names are not this module's to write.
    testCase "a module does not see a module the session loaded" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Bit.thena"
      case loadProofSource s1 "module Borrower where\n\nb : Bit.Bit\nb = Bit.off\n" of
        (_, ProofLoaded {}) -> assertFailure "the session's Bit was reachable"
        (s2, r) -> assertBool (unwords (renderResponse s2 r))
                              (any (isInfixOf "not in scope: Bit.Bit")
                                   (renderResponse s2 r))

  , -- **And the import is what repairs it**, through the door that can read
    -- one: @Pair@ imports @Bit@ and writes @Bit.Bit@, from a fresh session.
    testCase "and the same names are reachable to a module that imports it" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Pair.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ]
        @?= ["test.modules.Bit", "test.modules.Pair"]

  , -- **AN IMPORT IS NOT TRANSITIVE** — his ruling of 2026-11-03: @public@ is
    -- what makes a dependency travel, and until it exists a module's own
    -- imports stay its own. @OnlyPair@ imports @Pair@, which imports @Bit@, and
    -- writes @Bit.Bit@: the walk loads all three and the refusal is about the
    -- name, not about the file.
    testCase "and not to a module that only imports its importer" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/OnlyPair.thena"
      case out of
        [r] -> assertBool (unwords (renderResponse s0 r))
                          (any (isInfixOf "not in scope: Bit.Bit")
                               (renderResponse s0 r))
        _   -> assertFailure (show (map (renderTrouble s0) trouble))

  , -- **The prelude needs no import**, which is what makes it the prelude:
    -- @UsesPrelude@ imports nothing and writes @Eq@ and @refl@.
    testCase "the prelude is reachable with nothing imported" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/UsesPrelude.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.UsesPrelude"]

  , -- **A LINE TYPED AT THE PROMPT IS NOT A MODULE and is not isolated**, so it
    -- keeps the session — which is what makes the system usable while a file is
    -- being written. This is the restoration as much as the rule: the
    -- concealment is lifted when the load ends, and @Bit@ went in through a
    -- load that had it concealed.
    testCase "the prompt still reaches everything the session holds" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Bit.thena"
      let (_, r) = oneLine s1 ":infer Bit.off"
      assertBool (unwords (renderResponse s1 r))
                 (not (any (isInfixOf "not in scope") (renderResponse s1 r)))

  , -- **The subtraction, read directly.** A module with no imports conceals the
    -- session's own declarations and nothing else: not the prelude's, which it
    -- may reach, and not a primitive, which is the language's rather than any
    -- module's.
    testCase "the concealment is the session's names, less the prelude's" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Bit.thena"
      let hidden = map nameDotted (concealedFrom [] s1)
      assertBool (show hidden) ("Bit.Bit" `elem` hidden)
      assertBool (show hidden) ("Eq.Eq" `notElem` hidden)
      assertBool (show hidden) ("String" `notElem` hidden)

  , -- **And an import takes its module's names out of it**, generated names
    -- included: this is the one place the two halves of phase 280's provenance
    -- meet, and a key recorded under the wrong module would be concealed from
    -- the file that imports it.
    testCase "and an import takes that module's names out of it" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Bit.thena"
      let hidden = map nameDotted (concealedFrom [named' "test.modules.Bit"] s1)
      assertBool (show hidden) ("Bit.Bit" `notElem` hidden)
      assertBool (show hidden) ("Bit.off" `notElem` hidden)
  ]

-- --------------------------------------------------------------------------
-- A file does not end its own @open@s (MS11 phase 283, @~w46f8@)
-- --------------------------------------------------------------------------

-- | __The second route to the thing his ruling of 2026-11-05 removes.__
--
-- Phase 282 stopped a module reaching a /name/ the session held; a top-level
-- @open@ the session held was the other way in, and a file that wrote a bare
-- @off@ loaded or failed according to which file went in before it.
--
-- **EVERY TEST HERE IS A PAIR, because the two branches are a word apart**: a
-- test that only showed a short spelling working could not tell an @open@ that
-- travelled from a word that resolved anyway. @Inherits@ writes a bare @off@
-- and gets it from the module it imports; @BareOpen@ writes the same line,
-- imports the namespace's declarations and no @open@ of them, and is refused.
openIsolationTests :: [TestTree]
openIsolationTests =
  [ -- **The defect itself, as it was measured.** @Pair@'s top level writes
    -- @open Bit@, so before this phase loading it first was what made
    -- @BareOpen@'s bare @off@ resolve.
    testCase "a module does not see an open the session is holding" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Pair.thena"
      (_, out, trouble) <- loadProofFile s1 "test/modules/BareOpen.thena"
      assertBool (show (map (renderTrouble s1) trouble)) (null trouble)
      assertBool (show (map (renderResponse s1) out))
                 (any (isInfixOf "not in scope: off")
                      (concatMap (renderResponse s1) out))

  , -- **And it is refused from a fresh session too**, which is the whole claim:
    -- one answer whatever the session is holding.
    testCase "and it is refused the same way with nothing loaded" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/BareOpen.thena"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      assertBool (show (map (renderResponse s0) out))
                 (any (isInfixOf "not in scope: off")
                      (concatMap (renderResponse s0) out))

  , -- **The other branch of the pair: an @open@ travels with an @import@.**
    -- @Opener@ declares @Bit@ and opens it; @Inherits@ imports @Opener@, writes
    -- a bare @off@ and writes no @open@. This is @examples/Progress.thena@'s
    -- shape, and the corpus is why it must hold.
    testCase "but an open travels with an import" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Inherits.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ]
        @?= ["test.modules.Opener", "test.modules.Inherits"]

  , -- **AND IT TRAVELS ONE HOP, which is 'declaredByModule''s rule and not a
    -- second one.** @Inherits@ wrote no @open@ of its own, so it leaves none
    -- for its own importer: were it otherwise a module would inherit spellings
    -- for names it cannot see, since the names stop at the first module without
    -- @public@ (his ruling of 2026-11-03).
    testCase "and it travels one hop, as a declaration does" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Inherits.thena"
      let direct   = map openedPath (openedFrom [named' "test.modules.Opener"] s1)
          indirect = map openedPath (openedFrom [named' "test.modules.Inherits"] s1)
      assertBool (show direct)   (["Bit"] `elem` direct)
      assertBool (show indirect) (["Bit"] `notElem` indirect)

  , -- **The prelude's own @open Eq@ is the general case and not an exception**:
    -- it is how every module in the project reaches @refl@, and it arrives by
    -- the one route an import uses.
    testCase "the prelude's opens are what a module starts with" $ do
      (s0, _) <- startingSession
      let opens = map openedPath (openedFrom [] s0)
      assertBool (show opens) (["Eq"] `elem` opens)

  , -- **An @open@ inside a @namespace@ block is not the module's to pass on**,
    -- because it is popped where the block ends — @~ckmsk@, his ruling of
    -- 2026-11-03. @ScopedOpen@ writes exactly one @open@ and writes it inside a
    -- block.
    testCase "an open inside a namespace block is left behind by nobody" $ do
      (s0, _) <- startingSession
      (s1, _, trouble) <- loadProofFile s0 "test/modules/ScopedOpen.thena"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      map openedPath (openedByModule (named' "test.modules.ScopedOpen") s1) @?= []

  , -- **A LINE TYPED AT THE PROMPT IS NOT A MODULE**, so it keeps what a load
    -- left it: @Pair@'s @open Bit@ is still in force at the prompt after it
    -- loads. This is the restoration as much as the rule — the @open@s the
    -- module wrote go back on top of the session's own.
    testCase "the prompt keeps the opens a load left it" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Pair.thena"
      let (_, r) = oneLine s1 ":infer off"
      assertBool (unwords (renderResponse s1 r))
                 (not (any (isInfixOf "not in scope") (renderResponse s1 r)))
  ]

-- --------------------------------------------------------------------------
-- @import@ and @consult@ at the prompt (MS11 phase 284)
-- --------------------------------------------------------------------------

-- | __His ruling of 2026-11-03: both acts are writable in a surface file, in a
-- rule file, and at the prompt.__ Neither parsed there until this phase —
-- @1:1: unexpected import@.
--
-- **They take a module NAME where @:load@ and @:consult@ take paths**, and the
-- consequence worth a test is the header check: @~r58qh@ asks a module's header
-- to match the name it was reached by, and only when it is reached by name. A
-- prompt @import@ reaches it by name, so it is asked — which is what a door
-- built on 'ProofRequested' would have skipped.
promptActTests :: [TestTree]
promptActTests =
  [ testCase "import loads the module it names, and what that imports" $ do
      (s0, _) <- startingSession
      (s1, out, trouble) <- atPrompt s0 "import test.modules.Inherits"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ]
        @?= ["test.modules.Opener", "test.modules.Inherits"]
      assertBool "and it is in" (moduleLoaded (named' "test.modules.Inherits") s1)

  , -- A module is loaded once however many files reach it, and the prompt is
    -- not an exception to that.
    testCase "and a second import of it declares nothing again" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- atPrompt s0 "import test.modules.Bit"
      (_, out, trouble) <- atPrompt s1 "import test.modules.Bit"
      assertBool (show (map (renderTrouble s1) trouble)) (null trouble)
      out @?= [ModuleAlreadyIn (named' "test.modules.Bit")]

  , -- **THE PAIR, and it is the whole reason the response carries a name.**
    -- @Misnamed.thena@ calls itself @test.modules.Elsewhere@: reached by name
    -- it is refused, and reached by its path it is not.
    testCase "the header is checked, because the prompt reaches it by name" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- atPrompt s0 "import test.modules.Misnamed"
      out @?= []
      case trouble of
        [Unloadable p (ModuleMisnamed reached header)] -> do
          p @?= "test/modules/Misnamed.thena"
          reached @?= named' "test.modules.Misnamed"
          header  @?= named' "test.modules.Elsewhere"
        other -> assertFailure (show (map (renderTrouble s0) other))

  , testCase "and the same file loaded by its path is accepted" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Misnamed.thena"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Elsewhere"]

  , -- A name is not a path: every step is an ordinary word.
    testCase "a word that is no module name is refused before any IO" $
      case snd (command newSession "import test/modules/Bit.thena") of
        Rejected e -> e @?= NotAModuleName "test/modules/Bit.thena"
        other      -> assertFailure (show other)

  , testCase "and a hyphen is not a word either" $
      case snd (command newSession "import foo-bar") of
        Rejected e -> e @?= NotAModuleName "foo-bar"
        other      -> assertFailure (show other)

  , -- **The same cycle refusal a file's import gets**, because it is the same
    -- walk: nothing about the graph is written twice.
    testCase "a cycle reached from the prompt is refused by name" $ do
      (s0, _) <- startingSession
      (_, _, trouble) <- atPrompt s0 "import test.modules.LoopA"
      case trouble of
        [Unloadable _ (ImportCycle ms)] ->
          map moduleText ms
            @?= ["test.modules.LoopA", "test.modules.LoopB", "test.modules.LoopA"]
        other -> assertFailure (show (map (renderTrouble s0) other))

  , -- **@consult@ reaches a base by the same kind of name**, the act supplying
    -- the extension: @test.modules.Inspecting@ is
    -- @test/modules/Inspecting.thena.rules@, and the base's own @import@ brings
    -- in the module declaring the language it talks about.
    testCase "consult reaches a rule base by its module name" $ do
      (s0, _) <- startingSession
      (s1, out, trouble) <- atPrompt s0 "consult test.modules.Inspecting"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Lang"]
      assertBool "the base went in" (not (null [ () | BasesLoaded _ <- out ]))
      -- A consult pushes, so the shipped base is still underneath it.
      assertBool "and it pushed rather than replaced"
                 (length (rules (machineOf s1)) > length (rules (machineOf s0)))

  , -- The base may not change under a half-built proof (the user, 2026-08-25),
    -- which is @:consult@'s own rule and not a second one. An @import@ is not
    -- refused, for the reason @:load proof@ is not.
    testCase "consult is refused while a proof is open" $
      case snd (command proving "consult test.modules.Inspecting") of
        Rejected e -> e @?= ProofUnderway (rootName "t")
        other      -> assertFailure (show other)

  , testCase "and import is not" $
      case snd (command proving "import test.modules.Bit") of
        ImportRequested m -> m @?= named' "test.modules.Bit"
        other             -> assertFailure (show other)
  ]
  where
    -- | A line typed at the prompt, **followed as the loop follows it**: the
    -- driver answers with a request and "Thena.Files" does the reading, so a
    -- test that stopped at the response would not touch the disk at all.
    atPrompt s line = case oneLine s line of
      (s', resp) -> case following s' resp of
        Just io -> io
        Nothing -> pure (s', [resp], [])

    proving = fst (command newSession ":theorem t : Type\8320")

-- --------------------------------------------------------------------------
-- The forms of @open@ (MS10 phase 254)
-- --------------------------------------------------------------------------

-- | His ruling of 2026-10-30 gives five, and each is asserted by what it keeps
-- OUT as well as by what it lets in.
--
-- **A form that let everything in would pass a test that only checked what it
-- admits**, which is the whole risk here: @open X ( a )@ and @open X@ differ
-- only in what they refuse.
openTests :: [TestTree]
openTests =
  [ testCase "open X Y Z opens each of them" $ loads twoNamespaces

  , testCase "open X ( a b ) admits those words" $ loads selective
  , testCase "and keeps the others out" $ notInScope selectiveMisses "succ"

  , testCase "open X hiding ( a ) admits the rest" $ loads hidingSome
  , testCase "and keeps that one out" $ notInScope hidingMisses "succ"

  , testCase "open X renaming ( a -> b ) admits it as b" $ loads renamingOne
  , -- **The old spelling goes**, as Agda's renaming does — which is what makes
    -- it the tie-break for two languages sharing a letter rather than a second
    -- way in.
    testCase "and the word it renamed is no longer in scope" $
      notInScope renamingMisses "succ"

  , -- **One declaration is the signature and the equation**, because that is
    -- what a declaration is in this language.
    testCase "open X in reaches the declaration under it, pair and all" $
      loads localOpen
  , testCase "and stops at the end of it" $ notInScope localOpenEnds "succ"
  ]
  where
    loads src = do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (_, ProofLoaded {}) -> pure ()
        (_, other)          -> assertFailure (show other)

    notInScope src w = do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (_, Ran _ _ (Halted (CannotRead (ResolveFailed (NotInScope x)))))
          | x == w -> pure ()
        (_, Ran _ _ (Halted r)) -> assertFailure (show r)
        (_, other)              -> assertFailure (show other)

    nat =
      "data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n"

    header o = "module O where\n" ++ nat ++ o

    twoNamespaces =
      header "data Bit : Type\8320 where\n\
             \  off : Bit\n\
             \open Nat Bit\n\
             \both : Bit.Bit\n\
             \both = off\n"

    selective =
      header "open Nat ( zero )\n\
             \only : Nat.Nat\n\
             \only = zero\n"

    selectiveMisses =
      header "open Nat ( zero )\n\
             \bad : Nat.Nat\n\
             \bad = succ zero\n"

    hidingSome =
      header "open Nat hiding ( succ )\n\
             \only : Nat.Nat\n\
             \only = zero\n"

    hidingMisses =
      header "open Nat hiding ( succ )\n\
             \bad : Nat.Nat\n\
             \bad = succ zero\n"

    renamingOne =
      header "open Nat renaming ( succ -> s )\n\
             \good : Nat.Nat\n\
             \good = s Nat.zero\n"

    renamingMisses =
      header "open Nat renaming ( succ -> s )\n\
             \bad : Nat.Nat\n\
             \bad = succ Nat.zero\n"

    localOpen =
      header "open Nat in one : Nat.Nat\n\
             \one = succ zero\n"

    localOpenEnds =
      header "open Nat in one : Nat.Nat\n\
             \one = succ zero\n\
             \after : Nat.Nat\n\
             \after = succ Nat.zero\n"

-- --------------------------------------------------------------------------
-- A rule base's own imports (MS11 phase 276)
-- --------------------------------------------------------------------------

-- | @import ‹module›@ in a rule file, which is what closes the hack his ruling
-- of 2026-11-03 named: a base that talks about a language used to rely on the
-- session having loaded it first.
--
-- **Every case here is a PAIR with @Unstated@**, the same base without the
-- import line. A test that only showed the import working could not tell a
-- dependency that was stated from one the session happened to satisfy — and
-- before this phase the session always did, because the fixture loaded the
-- module itself.
baseImportTests :: [TestTree]
baseImportTests =
  [ testCase "the base's own import is what makes its tag resolve" $ do
      (s0, _) <- startingSession
      (s1, out, trouble) <- consultRuleFiles s0 ["test/modules/Inspecting.thena.rules"]
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Lang"]
      assertBool "the base went in" (not (null [ () | BasesLoaded _ <- out ]))
      assertBool "and the module is in the session"
                 (moduleLoaded (importNamed "test.modules.Lang") s1)

  , -- **The pair**, and the only difference between the two files is the line.
    testCase "and the same base without it is refused" $ do
      (s0, _) <- startingSession
      (_, _, trouble) <- consultRuleFiles s0 ["test/modules/Unstated.thena.rules"]
      case trouble of
        [Unloadable p (RuleFileRefused _ (RuleIllFormed _))] ->
          p @?= "test/modules/Unstated.thena.rules"
        other -> assertFailure (show (map (renderTrouble s0) other))

  , -- A dependency asks that the module BE there, not that this act load it.
    testCase "a module already in the session is not loaded again" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Lang.thena"
      (_, out, trouble) <- consultRuleFiles s1 ["test/modules/Inspecting.thena.rules"]
      assertBool (show (map (renderTrouble s1) trouble)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= []

  , testCase "an import that is not on disc installs nothing" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- consultRuleFiles s0 ["test/modules/Absentee.thena.rules"]
      out @?= []
      case trouble of
        [Unreadable p _] -> p @?= "test/modules/Nowhere.thena"
        other            -> assertFailure (show (map (renderTrouble s0) other))

  , -- **The modules a base brought in are the base's**, so a base that will not
    -- install does not leave them behind. Asked of the environment, because the
    -- response is a refusal either way.
    testCase "a base that is refused takes what it imported back with it" $ do
      (s0, _) <- startingSession
      (s1, _, trouble) <- consultRuleFiles s0 ["test/modules/BadRule.thena.rules"]
      assertBool "it refused" (not (null trouble))
      assertBool "the language went back"
                 (not (isDeclared (declaredAs "A.LC") (globals (machineOf s1))))
      assertBool "and so did the record of the module"
                 (not (moduleLoaded (importNamed "test.modules.Lang") s1))

  , -- 'ImportsUnread''s counterpart for a base, and the refusal names only what
    -- is missing.
    testCase "the door with no IO refuses a base that imports" $ do
      (s0, _) <- startingSession
      src <- readFile "test/modules/Inspecting.thena.rules"
      case loadRuleBases s0 [("test/modules/Inspecting.thena.rules", src)] of
        (_, RuleFileRefused _ (RuleImportsUnread ms)) ->
          map moduleText ms @?= ["test.modules.Lang"]
        (_, other) -> assertFailure (show other)
  ]
  where
    importNamed t = case moduleName t of
      Just m  -> m
      Nothing -> error ("not a module name: " ++ t)

-- --------------------------------------------------------------------------
-- The import graph (MS11 phase 274)
-- --------------------------------------------------------------------------

-- | @import ‹module›@, and what loading one costs.
--
-- **The modules are on disc, in @test\/modules@, and are reached by NAME** —
-- that is the thing under test. A module name is a path under the source root
-- (@Thena.Driver.moduleFile@), the root is the process\'s working directory, so
-- @test.modules.Bit@ is @test\/modules\/Bit.thena@. A fixture written as a
-- string could not exercise any of this.
--
-- **Each case says what it would look like if the mechanism were absent**,
-- because most of them pass trivially otherwise: a diamond that loaded its
-- shared module twice would collide, and a closure that landed half of itself
-- would leave the environment holding declarations no file asked for.
importTests :: [TestTree]
importTests =
  [ testCase "a module is elaborated after the ones it imports" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Pair.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Bit", "test.modules.Pair"]

  , -- **The diamond is the case that cannot be got right by accident**:
    -- @Both@ imports @Bit@ and @Pair@, and @Pair@ imports @Bit@ too, so a walk
    -- that did not remember what it had gathered would elaborate @Bit@ twice
    -- and the second one would collide with the first one's @Bit.Bit@.
    testCase "a diamond reaches the shared module once" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Both.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ]
        @?= ["test.modules.Bit", "test.modules.Pair", "test.modules.Both"]

  , -- The same memory, across two commands rather than inside one walk.
    testCase "and a module the session already loaded is not loaded again" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Bit.thena"
      assertBool "Bit is in" (moduleLoaded (named' "test.modules.Bit") s1)
      (_, out, trouble) <- loadProofFile s1 "test/modules/Pair.thena"
      assertBool (show (map (renderResponse s1) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Pair"]

  , -- **Loaded by a path that is no module name, so there is nothing to
    -- remember.** @0unnameable@ begins with a digit, so it is no step of a
    -- module name — which is the case every numbered example is in, and the
    -- reason the field is a 'Maybe' rather than a name invented from the path.
    -- Such a file loads, and nothing can import it.
    testCase "a file whose path is no module name is remembered by nothing" $ do
      (s0, _) <- startingSession
      (s1, out, _) <- loadProofFile s0 "test/modules/0unnameable.thena"
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["Unnameable"]
      moduleOfFile "test/modules/0unnameable.thena" @?= Nothing
      -- **The prelude is the one module a fresh session has remembered** (MS11
      -- phase 282): it is marked under the name its own header gives it, so
      -- that every module may reach it without importing anything. So
      -- /nothing to remember/ is now /nothing but the prelude/.
      modulesLoaded s1 @?= [preludeModule]

  , -- **The header-against-path check, and it is asked HERE ONLY** — his ruling
    -- of 2026-11-05, @~r58qh@. @Misnamed.thena@ declares
    -- @module test.modules.Elsewhere where@, so reaching it by name finds a file
    -- that answers to another name.
    testCase "a module whose header disagrees with its path is refused" $ do
      (s0, _) <- startingSession
      (_, _, trouble) <- loadProofFile s0 "test/modules/ImportsMisnamed.thena"
      case trouble of
        [Unloadable p (ModuleMisnamed reached header)] -> do
          p @?= "test/modules/Misnamed.thena"
          (moduleText reached, moduleText header)
            @?= ("test.modules.Misnamed", "test.modules.Elsewhere")
        other -> assertFailure (show (map (renderTrouble s0) other))

  , -- **The other half of the ruling, and the half that makes it cheap**: the
    -- same file, loaded by its path, is never asked to agree with anything. If
    -- the check were unconditional this would be refused too, and a file would
    -- be illegal because of where it sits.
    testCase "and the same file loaded by its path is not asked" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Misnamed.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Elsewhere"]

  , -- **The one addition every part of visibility rides on** (MS11 phase 280):
    -- nothing can be narrowed while a global carries no record of where it came
    -- from. @Lang.thena@ declares a token class and a language inside a
    -- @namespace@, so what lands is @A.x@ and everything under @A.LC@ — the
    -- datatype itself among them, as @A.LC.LC@, since a type lives inside its
    -- own namespace (his design of 2026-10-29).
    testCase "a module's globals are recorded as its own" $ do
      (s0, _) <- startingSession
      (s1, _, trouble) <- loadProofFile s0 "test/modules/Lang.thena"
      assertBool (show (map (renderTrouble s0) trouble)) (null trouble)
      let mine = map nameDotted (declaredByModule (named' "test.modules.Lang") s1)
      assertBool (show mine) (all (`elem` mine) ["A.x", "A.LC.LC"])

  , -- **A key is named once however many tables hold it.** A constructor is in
    -- two of the four 'Env.declaredNames' concatenates, so the list would carry
    -- it twice without the dedup, and anything counted off it would be wrong.
    testCase "and each of them once" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Lang.thena"
      let mine = map nameDotted (declaredByModule (named' "test.modules.Lang") s1)
      length mine @?= length (nub mine)

  , -- **The keys that ARRIVED, not the items the file wrote**, which is the whole
    -- reason this is a difference of two environments: a generated name belongs
    -- to the module whose declaration produced it, and an export list has no
    -- other answer available to it.
    testCase "and the names its declarations generated with them" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Lang.thena"
      let mine = map nameDotted (declaredByModule (named' "test.modules.Lang") s1)
      -- The language's productions and its generated substitution, none of
      -- which is written as a declaration anywhere in the file.
      assertBool (show mine)
        (all (`elem` mine) ["A.LC.var", "A.LC.app", "A.LC.subst-x"])

  , testCase "a global says which module declared it" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/Lang.thena"
      case [ g | g <- declaredByModule (named' "test.modules.Lang") s1
               , nameDotted g == "A.LC.var" ] of
        g : _ -> fmap moduleText (moduleDeclaring g s1)
                   @?= Just "test.modules.Lang"
        []    -> assertFailure "A.LC.var is not among the module's names"

  , -- **An absence and not an invented answer.** @0unnameable.thena@ is reached
    -- by no module name, so what it declares belongs to no module — the same
    -- thing that is true of anything typed at the prompt. Whether an export list
    -- can say anything about such a name is `~jmw4k`'s and is not decided here.
    testCase "and a file reached by no name declares for no module" $ do
      (s0, _) <- startingSession
      (s1, _, _) <- loadProofFile s0 "test/modules/0unnameable.thena"
      let known = [ g | g <- Env.declaredNames (globals (machineOf s1))
                      , nameDotted g == "Three.Three" ]
      case known of
        g : _ -> moduleDeclaring g s1 @?= Nothing
        []    -> assertFailure "Three.Three was not declared"

  , testCase "a cycle is refused, and names the path the walk took" $ do
      (s0, _) <- startingSession
      (_, _, trouble) <- loadProofFile s0 "test/modules/LoopA.thena"
      case trouble of
        [Unloadable _ (ImportCycle ms)] ->
          map moduleText ms
            @?= ["test.modules.LoopA", "test.modules.LoopB", "test.modules.LoopA"]
        other -> assertFailure (show (map (renderTrouble s0) other))

  , testCase "an import that is not on disc names the file it looked for" $ do
      (s0, _) <- startingSession
      (_, _, trouble) <- loadProofFile s0 "test/modules/Absent.thena"
      case trouble of
        [Unreadable p _] -> p @?= "test/modules/Nowhere.thena"
        other            -> assertFailure (show (map (renderTrouble s0) other))

  , -- **All or none across the whole closure**, which is
    -- 'loadProofItemsConsulting''s own bargain widened: @Broken@ imports @Bit@
    -- and then fails, and what must not survive is @Bit@.
    testCase "a closure whose last module fails declares nothing at all" $ do
      (s0, _) <- startingSession
      (s1, out, _) <- loadProofFile s0 "test/modules/Broken.thena"
      assertBool ("it loaded: " ++ show (map (renderResponse s1) out))
                 (null [ () | ProofLoaded {} <- out ])
      assertBool "Bit went back with it"
                 (not (isDeclared (declaredAs "Bit") (globals (machineOf s1))))
      assertBool "and so did the record of it"
                 (not (moduleLoaded (named' "test.modules.Bit") s1))

  , -- **A refusal inside a file nobody named has to name it** (MS11 phase 275).
    -- The root file's failure stays a response, because the user typed that
    -- path and it is in front of them; an imported one becomes trouble, and the
    -- bare /not in scope/ this used to be was about a file the user had not
    -- mentioned.
    testCase "a failure inside an imported module names that module's file" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/ImportsBroken.thena"
      assertBool (show (map (renderResponse s0) out)) (null out)
      case trouble of
        [Unloadable p _] -> p @?= "test/modules/Broken.thena"
        other            -> assertFailure (show (map (renderTrouble s0) other))

  , testCase "and the file the user named still answers with a response" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile s0 "test/modules/Broken.thena"
      assertBool ("trouble: " ++ show (map (renderTrouble s0) trouble))
                 (null trouble)
      assertBool "it refused" (not (null out))
      assertBool "and not as a load"
                 (null [ () | ProofLoaded {} <- out ])

  , -- 'ConsultsUnread''s twin: the pure door cannot read a file, so it refuses
    -- rather than elaborating a module whose dependencies are not in.
    testCase "the door with no IO refuses a module that imports" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 (unlines ["module M where", "import test.modules.Bit"]) of
        (_, ImportsUnread ms) -> map moduleText ms @?= ["test.modules.Bit"]
        (_, other)            -> assertFailure (show other)

  , -- **Written inside a block and still the module's**, for 'moduleConsults''
    -- reason: what an import says is which modules this one depends on, and a
    -- namespace does not change that.
    testCase "an import inside a namespace block is still the module's" $
      importsOf (unlines [ "module M where"
                         , "namespace A where"
                         , "  import test.modules.Bit" ])
        @?= ["test.modules.Bit"]

  , testCase "and the written order is kept" $
      importsOf (unlines [ "module M where"
                         , "import test.modules.Bit"
                         , "import test.modules.Pair" ])
        @?= ["test.modules.Bit", "test.modules.Pair"]
  ]
  where
    importsOf src = case parseSurfaceModule src of
      Right (_, items) -> map moduleText (moduleImports items)
      Left e           -> error (show e)

-- --------------------------------------------------------------------------
-- @namespace@ (MS10 phase 254)
-- --------------------------------------------------------------------------

-- | A namespace is a prefix, and the walk out of one.
--
-- **Both halves are asserted on the same module**, because they are two sides
-- of one thing: a declaration goes inside the namespace, and a name written
-- inside it is looked for there first. A module that declared correctly but
-- resolved at the root would not load at all, and one that resolved correctly
-- while declaring at the root would load and declare the wrong keys — so each
-- test says which it is checking.
namespaceTests :: [TestTree]
namespaceTests =
  [ testCase "it puts what it declares inside itself" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 namespacedModule of
        (s1, ProofLoaded {}) -> do
          let env = globals (machineOf s1)
          isDeclared (named "A.Nat.Nat") env @?= True
          isDeclared (named "A.Nat.zero") env @?= True
          isJust (lookupDefinition (named "A.one") env) @?= True
          -- **Nothing lands at the root**, which is the half a module that
          -- resolved correctly would still get wrong.
          isDeclared (named "Nat.Nat") env @?= False
        (_, other) -> assertFailure (show other)

  , -- @one = Nat.succ Nat.zero@ is written inside @A@ with no @open@, so it
    -- loads only because the walk tried @A.Nat.succ@.
    testCase "and a name written inside it is tried there first" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 namespacedModule of
        (_, ProofLoaded _ ds _ _) -> ds @?= ["A.Nat", "A.one", "A.two"]
        (_, other) -> assertFailure (show other)

  , testCase "nesting is a longer prefix and needs nothing of its own" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 nestedModule of
        (s1, ProofLoaded {}) -> do
          let env = globals (machineOf s1)
          isDeclared (named "A.B.Leaf.Leaf") env @?= True
          isJust (lookupDefinition (named "A.B.inner") env) @?= True
          isJust (lookupDefinition (named "A.outer") env) @?= True
        (_, other) -> assertFailure (show other)

  , -- **The whole point of the walk being ordered**: @Nat.Nat@ is a name at the
    -- root /and/ inside @A@, and inside @A@ it means the inner one. His ruling
    -- of 2026-10-30 — nearer wins outright, where two @open@s would be refused.
    testCase "a nearer namespace wins over the root outright" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 shadowingModule of
        (s1, ProofLoaded {}) -> do
          let env = globals (machineOf s1)
          -- @inner@'s type is written @Nat.Nat@ inside @A@, so it is @A@'s.
          case lookupDefinition (named "A.inner") env of
            Just d  -> definitionType d @?= Canonical (named "A.Nat.Nat") [] []
            Nothing -> assertFailure "A.inner was not declared"
          -- The same text outside the block is the root's, unchanged.
          case lookupDefinition (named "outer") env of
            Just d  -> definitionType d @?= Canonical (named "Nat.Nat") [] []
            Nothing -> assertFailure "outer was not declared"
        (_, other) -> assertFailure (show other)

  , -- A namespace's effect ends with its block, which is what makes it a
    -- declaration rather than a mode: the word after it is at the root again.
    testCase "and the block is where its effect ends" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 escapingModule of
        (_, Ran _ _ (Halted (CannotRead _))) -> pure ()
        (_, other) -> assertFailure (show other)
  ]
  where
    namespacedModule =
      "module NS where\n\
      \namespace A where\n\
      \  data Nat : Type\8320 where\n\
      \    zero : Nat\n\
      \    succ : Nat -> Nat\n\
      \\n\
      \  one : Nat.Nat\n\
      \  one = Nat.succ Nat.zero\n\
      \\n\
      \  two : A.Nat.Nat\n\
      \  two = Nat.succ one\n"

    nestedModule =
      "module NS where\n\
      \namespace A where\n\
      \  namespace B where\n\
      \    data Leaf : Type\8320 where\n\
      \      leaf : Leaf\n\
      \\n\
      \    inner : Leaf.Leaf\n\
      \    inner = Leaf.leaf\n\
      \\n\
      \  outer : B.Leaf.Leaf\n\
      \  outer = B.Leaf.leaf\n"

    shadowingModule =
      "module NS where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \namespace A where\n\
      \  data Nat : Type\8320 where\n\
      \    one : Nat\n\
      \\n\
      \  inner : Nat.Nat\n\
      \  inner = Nat.one\n\
      \\n\
      \outer : Nat.Nat\n\
      \outer = Nat.zero\n"

    -- @A@'s @only@ is reached from inside the block and not from after it.
    escapingModule =
      "module NS where\n\
      \namespace A where\n\
      \  data Leaf : Type\8320 where\n\
      \    leaf : Leaf\n\
      \\n\
      \escaped : Leaf.Leaf\n\
      \escaped = Leaf.leaf\n"

-- --------------------------------------------------------------------------
-- Shadowing (MS10 phase 264)
-- --------------------------------------------------------------------------

-- | A word that changes what it means, and the module door it changes at.
--
-- **His ruling of 2026-11-03 accepted the shadowing**, so what is asserted here
-- is the announcement rather than a refusal: both names, written in full,
-- because in the case that matters their short spellings are the same word.
--
-- **A module is where the @data@ door can be reached at all**, which is why
-- these are here and not in "Thena.SessionTests": a datatype's name is a bare
-- word at the @data@ line, so only a @namespace@ can put one at a path that
-- another declaration's name can take.
shadowingTests :: [TestTree]
shadowingTests =
  [ -- @Nat.zero@ is the inner datatype's alias until @data Nat@ declares a
    -- constructor of exactly that name. **The former can never do this** —
    -- everything a @data@ block declares lands inside its own namespace — so a
    -- constructor is the only name at this door that can take a word.
    testCase "a constructor that takes a datatype's word says so" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 constructorTakesTheWord of
        (_, ProofLoaded _ _ _ ws) ->
          ws @?= [NameShadows (named "Nat.zero") (named "Nat.zero.zero")]
        (_, other) -> assertFailure (show other)

  , -- **Once, not twice**: a constructor is installed as the constant it is and
    -- again as the wrapper its name means when written, so the keys the
    -- environment gained name it twice and the word it took is one word.
    testCase "and says it once, however many keys the name added" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 constructorTakesTheWord of
        (_, ProofLoaded _ _ _ ws) -> length ws @?= 1
        (_, other) -> assertFailure (show other)

  , -- A module's theorem comes in by the definition door, not by @:theorem@,
    -- so this is the half 'Thena.SessionTests' cannot reach.
    testCase "a theorem in a module says so as it lands" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 theoremTakesTheWord of
        (_, ProofLoaded _ _ _ ws) ->
          ws @?= [NameShadows (named "Nat") (named "Nat.Nat")]
        (_, other) -> assertFailure (show other)

  , -- **The other direction says nothing, and it is right not to**: a @data@
    -- block puts everything it declares inside its own namespace, so a
    -- datatype arriving under a word a definition already holds takes no word
    -- from anyone — @Foo@ is still the definition and the datatype is
    -- @Foo.Foo@, which is how the load reports it.
    --
    -- **What this pins is that the block answers its OWN word with the
    -- datatype being declared**: @ff : Foo@ is written where a definition
    -- called @Foo@ is in scope, and it still means the datatype. **The @data@
    -- LINE at the prompt refuses the same text** — "Thena.SessionTests",
    -- /the prompt refuses a constructor a module accepts/, has that divergence
    -- and the item it is written in.
    testCase "a data block answers its own word with the datatype, not a definition" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 datatypeUnderATakenWord of
        (s1, ProofLoaded _ _ _ ws) -> do
          let env = globals (machineOf s1)
          -- The declaration was accepted at all, which 'targetIndices' only
          -- permits when the constructor's target IS the family being
          -- declared, so this is the whole of the claim.
          isDeclared (named "Foo.Foo") env @?= True
          isDeclared (named "Foo.ff") env @?= True
          isJust (lookupDefinition (named "Foo") env) @?= True
          ws @?= []
        (_, other) -> assertFailure (show other)
  ]
  where
    constructorTakesTheWord =
      "module Shadow where\n\
      \namespace Nat where\n\
      \  data zero : Type\8320 where\n\
      \    z : zero\n\
      \\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n"

    theoremTakesTheWord =
      "module Shadow where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \Nat : Type\8321\n\
      \Nat = Type\8320\n"

    datatypeUnderATakenWord =
      "module Shadow where\n\
      \Foo : Type\8321\n\
      \Foo = Type\8320\n\
      \\n\
      \data Foo : Type\8320 where\n\
      \  ff : Foo\n"

-- --------------------------------------------------------------------------
-- The prelude
-- --------------------------------------------------------------------------

preludeTests :: [TestTree]
preludeTests =
  [ testCase "it is found where cabal put it, and loads clean" $ do
      (s, trouble) <- startingSession
      concatMap (renderTrouble s) trouble @?= []

  , testCase "and declares exactly Eq, refl, Unit, unit and Empty" $ do
      (s, _) <- startingSession
      let env = globals (machineOf s)
      sequence_
        [ assertBool (n ++ " is not declared") (isDeclared (named n) env)
        | n <- ["Eq.Eq", "Eq.refl", "Unit.Unit", "Unit.unit", "Empty.Empty"]
        ]

    -- §9's phase-11 deliverable, in full: "Eq's generated eliminator is J and
    -- can be used". Pinned as a string, for 'Thena.EliminatorTests'' reason.
  , testCase "Eq's generated eliminator is J" $ do
      (s, _) <- startingSession
      let env = globals (machineOf s)
          n0  = names (machineOf s)
      case lookupInductive (declaredAs "Eq") env of
        Nothing -> assertFailure "Eq is not declared"
        Just d  ->
          -- **The indices are @_@ and not @x@** (MS4 phase 54): the prelude is
          -- a surface module now, and elaborating @A -> A -> Type@ leaves the
          -- arrow\'s binders anonymous where "Thena.Syntax.Resolve" named them.
          -- 'Thena.Core.Term.Ident' is display metadata (§3.5), so the
          -- eliminator is the same one; only its printing moved.
          --
          -- **At @Eq {0}@**, not at its bare parameter (MS3 phase 31d): the
          -- eliminator is a scheme now, and what a use site sees is the
          -- instantiation. Rendering it uninstantiated would pin @ℓ@'s number,
          -- which is a counter value and no business of this assertion.
          renderEliminator (rendering [] n0) (declaredAs "Eq") (atZero d (fst (eliminatorType d LZero n0)))
            @?= [ "elim Eq.Eq : ∀ (A : Type₀) (P : ∀ (_ : A) (_1 : A) -> Eq.Eq {0} A _ _1 -> Type₀) \
                  \-> (∀ (a : A) -> P a a (Eq.refl {0} A a)) \
                  \-> ∀ (_ : A) (_1 : A) (target : Eq.Eq {0} A _ _1) -> P _ _1 target"
                ]

    -- "and can be used": eliminating a 'refl' must actually fire. The motive is
    -- constant so the reduct is the method applied to the one index.
  , testCase "and J computes on refl" $ do
      (s, _) <- startingSession
      afterLines s
        [ ":whnf elim Eq {0} (Unit {0}) \
          \(\\ (x : Unit {0}) (y : Unit {0}) (p : Eq {0} (Unit {0}) x y) -> Unit {0}) \
          \((\\ (a : Unit {0}) -> a)) (unit {0} unit {0}) (refl {0} (Unit {0}) (unit {0}))"
        ]
        (\l -> do
            loadedError l @?= Nothing
            renderedLast l @?= Just "Unit.unit {0}")

    -- The real @repl@ has the prelude in scope and 'transcript' does not; this
    -- is the difference, made visible.
  , testCase "preludeIsInTheWay: Empty cannot be redeclared over the prelude" $ do
      (s, _) <- startingSession
      afterLines s ["data Empty : Type₀ where { }"] $ \l ->
        loadedError l @?= Just (LoadStopped 1)
  ]

-- --------------------------------------------------------------------------
-- A file is a script
-- --------------------------------------------------------------------------

scriptTests :: [TestTree]
scriptTests =
  [ testCase "every line runs, in order" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            length (loadedResponses l) @?= 2
            mapM_ (\n -> assertBool (n ++ " missing") (declared n l)) ["A0", "B0"]

  , testCase "a blank line is a line, and is counted" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", "", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            loadedResponses l !! 1 @?= Blank

    -- The whole reason to reuse 'oneLine' rather than call 'command' directly:
    -- an op that asks is answered by the next line of the file, exactly as it
    -- would be by the next line typed (§7.5).
  , testCase "a question is answered by the next line" $
      let l = sourceWithRules ["assume core`Type₀`", "A"]
       in do
            loadedError l @?= Nothing
            length (loadedResponses l) @?= 2

  , testCase ":quit ends the load and is not a failure" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":quit", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            declared "A0" l @?= True
            declared "B0" l @?= False
  ]

-- --------------------------------------------------------------------------
-- Failing
-- --------------------------------------------------------------------------

failureTests :: [TestTree]
failureTests =
  [ testCase "it stops at the first failure, and names the line" $
      let l = source
                [ "data A0 : Type₀ where { a0 : A0 }"
                , "data B0 : Type₀ where { b0 : (B0 -> A0) -> B0 }"
                , "data C0 : Type₀ where { c0 : C0 }"
                ]
       in do
            loadedError l @?= Just (LoadStopped 2)
            declared "A0" l @?= True
            declared "C0" l @?= False

    -- The reason is the last response, not a second copy inside 'LoadError'.
  , testCase "and the reason is the last response, not carried twice" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":no-such-command-here"]
       in case reverse (loadedResponses l) of
            Rejected _ : _ -> pure ()
            other          -> assertFailure ("not a rejection: " ++ show (take 1 other))

  , testCase "a syntax error stops it too" $
      (loadedError (source ["data ohno"]) @?= Just (LoadStopped 1))

    -- **A refused line stops it too, and did not until phase 96** (found
    -- 2026-09-16). 'Thena.Driver.stopped' said it listed /the four ways a line
    -- does not do what it said/ and 'Thena.Driver.LineRefused' was not one of
    -- them, so a line that printed an error was stepped over and the file
    -- carried on — taking away the whole reason a load is worth more than
    -- typing the lines, which is that the failure has an address.
    --
    -- The second assertion is what says it was really skipped before: a test
    -- that only checked the error could pass on a load that stopped for some
    -- other reason entirely.
  , testCase "a line no op or rule will take stops it" $
      let l = sourceWithRules
                [ "say nosuchtag`x y`"
                , "data A0 : Type₀ where { a0 : A0 }"
                ]
       in do
            loadedError l @?= Just (LoadStopped 1)
            declared "A0" l @?= False

    -- And it really is the refusal that stopped it, not something else: a tag
    -- naming no language is resolution's complaint, not the parser's.
  , testCase "and the refusal is the last response" $
      case reverse (loadedResponses (sourceWithRules ["say nosuchtag`x y`"])) of
        LineRefused _ : _ -> pure ()
        other             -> assertFailure ("not a refusal: " ++ show (take 1 other))

    -- **The kernel refusing a @qed@ stops it too, and did not until phase 96.**
    -- 'Thena.Driver.Uncertified'\'s own comment says it is /shaped like
    -- 'Thena.Driver.Refused'/, which was in the list; it was not, so a script
    -- whose theorem the kernel would not accept carried on as if it had been
    -- admitted.
    --
    -- @lift@ is level-polymorphic with @ℓ₂₄ ≤ ℓ₂₅@ owed, so @lift {1 0}@ infers
    -- and @try@ accepts it — the obligation is collected only by the kernel
    -- (§5.3) — and @qed@ is where it is refused. That makes this the one shape
    -- where a line gets all the way to the end and still did not do what it
    -- said.
  , testCase "a qed the kernel refuses stops it" $
      let l = sourceWithRules
                [ ":theorem lift : ∀ (A : Type) -> Type"
                , "try-core core`\\ (A : Type) -> A`"
                , "solve"
                , "qed"
                , ":theorem bad : Type₁ -> Type₀"
                , "try-core core`lift {1 0}`"
                , "solve"
                , "qed"
                , "data A0 : Type₀ where { a0 : A0 }"
                ]
       in do
            loadedError l @?= Just (LoadStopped 8)
            declared "A0" l @?= False

  , testCase "nested :load is refused, not followed" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":load somewhere.thena.script"]
       in do
            loadedError l @?= Just (NestedLoad 2)
            -- what ran before it still ran
            declared "A0" l @?= True

    -- **AND THE OTHER TWO KINDS, WHICH WERE SILENTLY DROPPED** (MS10 phase
    -- 268). The case matched a script alone, so a @:load@ naming a proof
    -- module or a rule base ran to a response nothing followed: the line did
    -- nothing, said nothing, and the load went on. Found while measuring
    -- `~txbz5` through a script, where a @:load@ of an example looked like a
    -- printer ignoring its scope.
  , testCase "a nested :load of a proof module is refused too" $
      let l = source ["data A0 : Type\8320 where { a0 : A0 }", ":load somewhere.thena"]
       in do
            loadedError l @?= Just (NestedLoad 2)
            declared "A0" l @?= True

  , testCase "and one of a rule base" $
      let l = source ["data A0 : Type\8320 where { a0 : A0 }", ":load somewhere.thena.rules"]
       in do
            loadedError l @?= Just (NestedLoad 2)
            declared "A0" l @?= True

    -- **AND AN @import@, WHICH ARRIVED WITH THE SAME DEFECT** (MS11 phase 284).
    -- A script is run by a pure function, so an @import@ in one cannot be
    -- followed any more than a @:load@ can — and recorded-and-dropped is the
    -- worst of the three answers, because the script carries on without what it
    -- said it needed and fails somewhere else. **This is what the five
    -- @.thena.script@ files in @examples/@ are still waiting for**; the prompt
    -- takes the word, a script does not.
  , testCase "and an import, which a script cannot follow either" $
      let l = source ["data A0 : Type\8320 where { a0 : A0 }", "import test.modules.Bit"]
       in do
            loadedError l @?= Just (NestedLoad 2)
            declared "A0" l @?= True

  , testCase "a file that ends while something is asking says so" $
      loadedError (sourceWithRules ["assume core`Type₀`"]) @?= Just (UnansweredQuestion 1)

    -- **And it does not leave the session waiting** (MS7 phase 123). The
    -- pending question used to be an argument the caller threaded, and the
    -- REPL passed 'Nothing' after a load rather than whatever the file left
    -- behind. Now that it is 'pendingQuestion' the load has to clear it, or the
    -- next line typed at the prompt would be read as the answer to a question
    -- nobody was shown.
  , testCase "and the session it hands back is not still asking" $
      pendingQuestion (loadedSession (sourceWithRules ["assume core`Type₀`"])) @?= Nothing

    -- **The ruling this phase rests on, asserted** — HIS, 2026-09-28: /"Feels
    -- like a question and answer is an atomic unit."/ So 'pendingQuestion' is
    -- not in a 'Snapshot' and @:undo@ does not step back into a question: one
    -- @:undo@ takes back the asking and the answering together.
    --
    -- Driven through 'oneLine' rather than 'loadSource', because a load
    -- clears the question as it finishes (the test above) and a mid-file
    -- state is exactly what this needs to see.
  , testCase "asking lives on the session, and one :undo takes back the pair" $ do
      let (s1, _) = oneLine withRules "assume core`Type₀`"
          (s2, _) = oneLine s1 "x"
          (s3, _) = oneLine s2 ":undo"
      isJust (pendingQuestion s1) @?= True   -- the line asked, and the session says so
      pendingQuestion s2 @?= Nothing         -- the answer settled it
      pendingQuestion s3 @?= Nothing         -- and undoing does not bring it back
      assertBool "the pair really did build something" (devOf s2 /= devOf withRules)
      devOf s3 @?= devOf withRules         -- and one :undo took the whole pair back
  ]

-- | The development, for comparing one state against another.
devOf :: Session -> Development
devOf = development . machineOf

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

-- | Run lines against an empty session.
source :: [String] -> Loaded
source = loadSource newSession . unlines

-- | The same, with the standard base installed.
--
-- **The asking form of @assume@ needs it** (MS5 phase 62b): @assume core`T`@ is a
-- rule now, not a shape the driver recognised, so a session with no base has
-- nothing to call — the same as for @attack@ or @intro@ since phase 23b.
sourceWithRules :: [String] -> Loaded
sourceWithRules = loadSource withRules . unlines

-- | Run lines against a session that already has something in it.
afterLines :: Session -> [String] -> (Loaded -> IO ()) -> IO ()
afterLines s ls k = k (loadSource s (unlines ls))

-- | Is this DATATYPE declared — every caller below asks about one, and a
-- datatype is @D.D@ since MS10 phase 243, so the lookup is 'declaredAs' and not
-- the root word. Asking at the root answers 'False' for a datatype that is
-- perfectly well declared, which reads as a load that did nothing.
declared :: String -> Loaded -> Bool
declared n l = isDeclared (declaredAs n) (globals (machineOf (loadedSession l)))

-- | The last line's rendered term, printed as the REPL would print it.
--
-- A string rather than the 'Core': @unit@ could come back as the wrapper's
-- 'Thena.Core.Term.Global' or as the saturated 'Thena.Core.Term.Canonical', and
-- both are correct reducts of this elimination (§5.1). What the deliverable
-- claims is that J computes, and the printed answer is the honest witness.
renderedLast :: Loaded -> Maybe String
renderedLast l = case reverse (loadedResponses l) of
  Rendered t : _ -> Just (renderCore (rendering [] (names (machineOf (loadedSession l)))) [] t)
  _              -> Nothing

-- | A datatype's own level parameters, all instantiated at zero.
atZero :: InductiveDefinition -> Core -> Core
atZero d t = case instantiateLevels (inductiveLevels d) (map (const LZero) (inductiveLevels d)) of
  Just sub -> substLevelsIn sub t
  Nothing  -> t

-- --------------------------------------------------------------------------
-- The three kinds (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | @:load@ answers one question — which kind is this — and the extension
-- answers it, with the keywords saying the same thing out loud.
--
-- **The three suffixes are disjoint**, which is the property worth a test of
-- its own: a path has exactly one reading, and @.thena.rules@ is not a
-- @.thena@ that happens to end in something.
kindTests :: [TestTree]
kindTests =
  [ testCase "a bare .thena is a proof module" $
      kindOf "examples/arith.thena" @?= LoadProof
  , testCase ".thena.rules is a rule base, not a proof module" $
      kindOf "rules/standard.thena.rules" @?= LoadRules
  , testCase ".thena.script is a script, not a proof module" $
      kindOf "prelude/prelude.thena.script" @?= LoadScript

  , testCase "the keyword says which, and overrides nothing else" $
      case snd (command newSession ":load proof somewhere.thena") of
        ProofRequested p -> p @?= "somewhere.thena"
        other            -> assertFailure (show other)

  , -- The keyword is read before the path, so a script *named* like a proof
    -- module still loads as a script when it is asked for.
    testCase "a keyword beats the extension" $
      case snd (command newSession ":load script odd.thena") of
        LoadRequested p -> p @?= "odd.thena"
        other           -> assertFailure (show other)

  , testCase "and without one the extension decides" $
      case snd (command newSession ":load odd.thena") of
        ProofRequested p -> p @?= "odd.thena"
        other            -> assertFailure (show other)

  , testCase "mixing kinds in one load is refused" $
      case snd (command newSession ":load a.thena b.thena.rules") of
        Rejected _ -> pure ()
        other      -> assertFailure (show other)
  ]

-- --------------------------------------------------------------------------
-- Proof modules (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | A whole file of surface declarations, elaborated.
--
-- These go through 'loadProofSource', which is pure and takes the contents,
-- for the same reason 'loadSource' does: §12 invariant 4 keeps IO in
-- "Thena.Repl".
-- | A datatype whose constructor has a dependent argument telescope, so
-- no-confusion is skipped and the load warns (MS6 phase 98).
dependentModule :: String
dependentModule =
  unlines
    [ "module W where"
    , ""
    , "data Chain (A : Type\8320) : A -> A -> Type\8320 where"
    , "  link : forall (x : A) (y : A) (z : A) (p : Chain A x y) (q : Chain A y z) -> Chain A x z"
    , "open Chain"
    ]

moduleTests :: [TestTree]
moduleTests =
  [ testCase "a module declares what it says it declares" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 natModule of
        (_, ProofLoaded nm ds _ _) -> (nm, ds) @?= ("M", ["Nat", "one"])
        (_, other)             -> assertFailure (show other)

  -- **This module used to be the warning channel's fixture** (MS6 phase 98),
  -- because @link@'s @q@ premise depends on @y@ and the no-confusion generator
  -- declined @Chain@ for it. MS9 phase 212 states a transported chain of
  -- equations for exactly that shape, so the load is silent and the lemma is
  -- there — which is what these now say. The channel itself is exercised by
  -- "Thena.GrammarTests", whose module load warns about a vacuous binder.
  , testCase "a dependent argument telescope no longer warns" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 dependentModule of
        (_, ProofLoaded nm ds _ ws) -> do
          (nm, ds) @?= ("W", ["Chain"])
          ws @?= []
        (_, other) -> assertFailure (show other)

  , testCase "and it gets its no-confusion lemma like any other datatype" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 dependentModule
          g = globals (machineOf s1)
      map (\n -> isDeclared (named n) g)
          ["Chain.Chain", "Chain.lemmata.NoConfusion", "Chain.lemmata.noConfusion"]
        @?= [True, True, True]

  , testCase "a load with nothing to say warns about nothing" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 natModule of
        (_, ProofLoaded _ _ _ ws) -> ws @?= []
        (_, other) -> assertFailure (show other)

  , testCase "and the globals are really there afterwards" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 natModule
          g = globals (machineOf s1)
      map (\n -> isDeclared (named n) g)
          ["Nat.Nat", "Nat.zero", "Nat.succ", "one"]
        @?= [True, True, True, True]

  , -- **A declaration named with a path is admitted into that namespace**
    -- (MS10 phase 243), which is what the generated substitution family needs:
    -- it is written as surface source and goes through this very path.
    testCase "a declaration written with a path declares into that namespace" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 qualifiedModule of
        (_, ProofLoaded nm ds _ _) -> (nm, ds) @?= ("Q", ["Nat", "Nat.one", "two"])
        (_, other) -> assertFailure (show other)

  , -- **The base word is not also declared.** @define-global@ read its name as
    -- text and rooted it until this phase, so a path was silently dropped.
    testCase "and only the qualified name is in the environment" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 qualifiedModule
          g = globals (machineOf s1)
      map (\n -> isDeclared (named n) g) ["Nat.one", "one"] @?= [True, False]

  , -- **Quiet on success, loud on failure** — his call, 2026-09-02. The success
    -- case above carries no op messages at all; this one keeps them, because
    -- that is where the reason is.
    testCase "a module that does not elaborate reports why" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 badModule of
        (_, ProofLoaded {}) -> assertFailure "admitted, and it should not have been"
        (_, _)               -> pure ()

  , -- **Comments, in the other two kinds** (MS4 phase 43). The surface cases
    -- are in "Thena.SurfaceTests"; these are the two that do not go through the
    -- lexer first — a script splits its command word off before lexing, and a
    -- rule base reads its header textually.
    testCase "a comment line in a proof module is skipped" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 commentedModule of
        (_, ProofLoaded nm ds _ _) -> (nm, ds) @?= ("M", ["Nat", "one"])
        (_, other)             -> assertFailure (show other)

  , testCase "a comment line in a script is a blank line" $
      loadedError (loadSource newSession
        "-- a heading\ndata Nat : Type\8320 where { zero : Nat }  -- trailing\n")
        @?= Nothing

  , testCase "and -- without a space is still not one" $
      loadedError (loadSource newSession "--nope\n") @?= Just (LoadStopped 1)

  , -- **A top-level @do@ block** (MS4 phase 45), his: at the top of a module a
    -- block is an item, not an expression. It is spliced into the module's own
    -- instruction program, so what this pins is that the items around it are
    -- unaffected — the module goes on declaring after it.
    testCase "a top-level do block runs and the module goes on" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 blockModule of
        (_, ProofLoaded nm ds n _) -> (nm, ds, n) @?= ("M", ["Nat", "one"], 1)
        (_, other)               -> assertFailure (show other)

  , testCase "and what it declared is really there" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 blockModule
      isDeclared (rootName "one") (globals (machineOf s1)) @?= True

  , -- **Resolution happens where the block runs** (MS6 phase 104b), so a block
    -- whose op is given the wrong operands stops the run rather than refusing
    -- the file before it starts. It was a syntax error until this phase,
    -- because the words were turned into ops while the file was still being
    -- read — which asked what they meant before the declarations above them
    -- had run.
    testCase "a block with bad operands stops the run where it stands" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 badBlockModule of
        (_, Ran _ _ (Halted (BlockOperands _ "cross"))) -> pure ()
        (_, other) -> assertFailure (show other)

  , -- **And it is typed the moment it is about to run** (MS6 phase 104b),
    -- by the checker the prompt uses, so the message is the one it always was.
    -- **What changed is what is declared by then**: the items above it have
    -- run, because a module is a sequence and its blocks are no longer hoisted
    -- out of it. MS5 phase 90 checked every block before the module started,
    -- which is what made a @language@ block above a block unusable.
    --
    -- **The evidence for that moved into the response at phase 144** (MS6
    -- closeout 15). It used to be @Nat@ still being declared afterwards, which
    -- is the leak that phase closed — so the assertion below is the response's
    -- own shape instead, and it says the same thing: @BlockIllTyped@ with a
    -- reason means the block was resolved and typed, and resolution is exactly
    -- what needs @Nat@ to have been declared. A block run before its module's
    -- declarations gives 'BlockRefused' with an @UnboundInRule@ — the sibling
    -- test below shows that shape — so the two cannot be confused.
    testCase "a top-level block that does not type check stops the run" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 mistypedBlockModule of
        (_, Ran _ _ (BlockIllTyped (_ : _))) -> pure ()
        (_, other) -> assertFailure (show other)

  , -- **A load that does not complete declares nothing** (MS6 closeout 15,
    -- his ruling 2026-09-30). This is the invariant phase 144 establishes and
    -- it is asserted on the one module in this file that fails after declaring
    -- something: @Nat@ lands, then the block does not type check.
    testCase "and the module it had already declared is rolled back" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 mistypedBlockModule
      isDeclared (rootName "Nat") (globals (machineOf s1)) @?= False

  , -- **A module that redeclares a name is refused for the name.**
    -- It is the first thing a newcomer does — write @data Nat@, or copy an
    -- @Eq@ out of an example — and until this was fixed what came back was a
    -- sentence about a constructor's target, because the elaborated target of
    -- an already-declared datatype is a saturated @Canonical@ former and
    -- 'Thena.Global.Declare.targetIndices' read only the @Global@ spine.
    testCase "a module redeclaring a prelude datatype is refused for the name" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 redeclaringModule of
        (_, Ran _ _ (Refused (AlreadyDeclared g))) -> g @?= declaredAs "Unit"
        (_, other) -> assertFailure (show other)

  , -- **And the same holds with no prelude in it**: one module declaring the
    -- same datatype twice. The second is refused for its name, which is what
    -- says the first fix is about the shape of the target and not about where
    -- the clashing declaration came from.
    testCase "and the same datatype twice in one module is refused the same way" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 twiceDeclaredModule of
        (_, Ran _ _ (Refused (AlreadyDeclared g))) -> g @?= declaredAs "Widget"
        (_, other) -> assertFailure (show other)

  , -- **Everything goes back except the fresh counter**, which must go forward
    -- or a name the user has seen would be reissued (MS2 closeout 4f) — and a
    -- failed load does show them, in its @solved: ?ℓn@ lines.
    testCase "but the fresh counter goes forward across a failed load" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 mistypedBlockModule
      assertBool "the counter did not advance"
        (names (machineOf s1) > names (machineOf s0))

  , -- **The point of the rollback, and the reason it is worth a phase**: the
    -- session survives a typo. Before this, the names that had landed made the
    -- corrected file unloadable — 'Thena.Global.Declare' refused the
    -- re-declaration and blamed the constructor's target (@AGENDA.md@ 81).
    testCase "so the corrected module loads in the same session" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 mistypedBlockModule
      case loadProofSource s1 blockModule of
        (_, ProofLoaded nm ds n _) -> (nm, ds, n) @?= ("M", ["Nat", "one"], 1)
        (_, other) -> assertFailure (show other)

  , -- **Each top-level block is its own scope**, as a block is — and since
    -- MS6 phase 104b that is a fact about the run and not only about the
    -- check. A block is a call to @run-block@, so its instructions run in a
    -- frame; until this phase they were spliced into the module's one program
    -- and shared its one environment, while the checker typed each in a scope
    -- of its own and refused the disagreement.
    testCase "a name bound in one top-level block is not in scope in the next" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 twoBlockModule of
        (_, Ran _ _ (BlockRefused [UnboundInRule _ _ "x"])) -> pure ()
        (_, other) -> assertFailure (show other)

  , -- **A global block is a call to a rule** (MS6 phase 104b), so how a module
    -- treats its blocks is written in the shipped base and a user may replace
    -- it. Proved by a block that fails when it is played: the shipped
    -- @run-block@ plays it and the load stops, and a base of one's own that
    -- does not play it lets the module through.
    testCase "the shipped run-block plays a block, and a failing one stops the load" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 failingBlockModule of
        (_, Ran _ _ (Halted _)) -> pure ()
        (_, other) -> assertFailure (show other)

  , testCase "and a base of one's own may take the block over entirely" $ do
      (s0, _) <- startingSession
      shipped <- rulesPath >>= readFile
      let mine = "rule base mine where\n\n\
                 \run-block : Surface -> ()\n\
                 \rule run-block t :- do say \"intercepted\"\n"
      case loadRuleBases s0 [("mine", mine), ("shipped", shipped)] of
        (s1, BasesLoaded _) -> case loadProofSource s1 failingBlockModule of
          (_, ProofLoaded {}) -> pure ()
          (_, other) -> assertFailure (show other)
        (_, other) -> assertFailure (show other)

  , testCase "a file that is not a module at all is a syntax error" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 "data Nat : Type\8320 where { zero : Nat }" of
        (_, Failed _) -> pure ()
        (_, other)    -> assertFailure (show other)
  ]
  where
    -- **@two@ names @Nat.one@ to reach it**, so this module says both halves:
    -- a qualified declaration is installed, and a qualified name written in a
    -- term afterwards finds it (phase 241).
    qualifiedModule =
      "module Q where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \open Nat\n\
      \\n\
      \Nat.one : Nat\n\
      \Nat.one = succ zero\n\
      \\n\
      \two : Nat\n\
      \two = succ Nat.one\n"

    natModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \open Nat\n\
      \\n\
      \one : Nat\n\
      \one = succ zero\n"

    commentedModule =
      "-- a module about numbers\n\
      \module M where\n\
      \\n\
      \-- the numbers themselves\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat      -- successor\n\
      \open Nat\n\
      \\n\
      \one : Nat\n\
      \one = succ zero\n"

    blockModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \open Nat\n\
      \\n\
      \do\n\
      \  say \"here\"\n\
      \\n\
      \one : Nat\n\
      \one = succ zero\n"

    -- A block whose instruction fails when it runs, for the two tests about
    -- @run-block@: @goto-named@ is given a name no component has.
    failingBlockModule =
      "module F where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \do\n\
      \  goto-named \"nowhere\"\n"

    -- **@cross body@**, because the other two candidates stopped being
    -- resolution failures: an op word at an arity the op does not have is a
    -- call (MS5 phase 62b), and a numeral is an 'Thena.Instral.Ops.VInt' rather than a
    -- misplaced field position (MS5 phase 64). What is left is an operand no
    -- reading of the word admits, and @cross@ takes exactly two.
    mistypedBlockModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \do\n\
      \  prim-try 3\n"

    redeclaringModule =
      "module M where\n\
      \data Unit : Type\8320 where\n\
      \  unit : Unit\n"

    twiceDeclaredModule =
      "module M where\n\
      \data Widget : Type\8320 where\n\
      \  mk : Widget\n\
      \\n\
      \data Widget : Type\8320 where\n\
      \  mk2 : Widget\n"

    twoBlockModule =
      "module M where\n\
      \do\n\
      \  x = \"one\"\n\
      \\n\
      \do\n\
      \  say x\n"

    badBlockModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \do\n\
      \  cross body\n"

    badModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \one : Nat\n\
      \one = nosuchthing\n"

-- --------------------------------------------------------------------------
-- MS4 tier 0 (phase 43)
-- --------------------------------------------------------------------------

-- | **The checkpoint MS4\'s done-when calls tier 0**: a surface file that
-- declares a datatype, defines a function by elimination, uses one declaration
-- from another, and proves a theorem about it — elaborated from a file, with
-- every term argument written out.
--
-- @examples\/Tier0.thena@ is the deliverable and the golden is what it
-- produced. His reason for wanting the explicit form first, 2026-09-01:
-- /"Couldn\'t we have a demo that uses all explicit arguments in case we want
-- to test out that we are doing well and all is according the plan?"/
tierTests :: [TestTree]
tierTests =
  [ goldenVsString "tier0" "test/golden/tier0.golden" $ do
      (s, trouble) <- startingSession
      (s1, out, _) <- loadProofFile s "examples/Tier0.thena"
      let shown = concatMap (renderResponse' s1) ["one", "two", "plusZeroLeft"]
      pure (toLazyByteString (stringUtf8 (unlines
        (concatMap (renderTrouble s) trouble
          ++ concatMap (renderResponse s1) out ++ shown))))

  , -- **Implicit insertion is semantically transparent**, which is the property
    -- MS4\'s done-when asks for at phase 44 and not an approximation of it.
    -- The two spellings do **not** give the same term — they differ by one
    -- @=@-binding, because @fill@ parks a written argument and an inserted one
    -- is simply never elaborated into (@ms4\/CLOSEOUT.md@ 8, recorded at 44b).
    -- So the check is convertibility, which is the property; the syntactic gap
    -- is the finding, and it is already written down.
    testCase "a written implicit argument and an inserted one agree" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 bothSpellings of
        (_, ProofLoaded {}) -> pure ()
        (_, other)           -> assertFailure (show other)

  , testCase "and they are convertible, not merely both admitted" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 bothSpellings
          m = machineOf s1
      case ( lookupDefinition (rootName "oneExplicit") (globals m)
           , lookupDefinition (rootName "oneImplicit") (globals m)
           ) of
        (Just a, Just b) ->
          case convert (globals m) [] 0 (definitionBody a) (definitionBody b) of
            (Nothing, _, _) -> pure ()
            (Just why, _, _) -> assertFailure (show why)
        _ -> assertFailure "one of the two was not admitted"
  ]
  where
    renderResponse' s g = case lookupDefinition (rootName g) (globals (machineOf s)) of
      Just d  -> [g ++ " = " ++ renderCore (rendering [] 0) [] (definitionBody d)]
      Nothing -> [g ++ " is missing"]

    bothSpellings =
      "module Both where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \open Nat\n\
      \\n\
      \idE : forall (A : Type\8320) -> A -> A\n\
      \idE = \\ A x -> x\n\
      \\n\
      \idI : forall {A : Type\8320} -> A -> A\n\
      \idI = \\ A x -> x\n\
      \\n\
      \oneExplicit : Nat\n\
      \oneExplicit = idE Nat (succ zero)\n\
      \\n\
      \oneImplicit : Nat\n\
      \oneImplicit = idI (succ zero)\n"
