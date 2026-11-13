-- | Object-language blocks, read and validated (MS6 phase 101; @ms6\/SPEC.md@
-- §4.1–4.5, §5.1, §7.0).
--
-- Three layers, each tested on its own and then through a module load:
--
-- * the lexer takes a @language@ or @context@ block at column 1 of a module
--   whole, as raw text, and only in a module;
-- * "Thena.Language.Reader" gives its shape — header, productions, metadata,
--   items, binding forms;
-- * "Thena.Language.Grammar" gives its meaning, against what is declared —
--   and every refusal of §4.5 is asserted as its structured value, the golden
--   pinning the words.
--
-- **The roles are asserted production by production** for the spec's own STLC
-- grammar, because they are what phase 103 will put on the constructors and
-- generated substitution will read: a wrong role here is a wrong substitution
-- there, three phases away.
module Thena.GrammarTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), rootName, nameDotted)
import Thena.Declared (named)
import Thena.Driver
  ( Leniency (..)
  , Response (..)
  , RuleFileError (..)
  , Session
  , command
  , machineOf
  , Stop (..)
  , loadProofSource
  , loadRuleTexts
  , newSession
  )
import Thena.Engine (Machine (..))
import Thena.Errors (SyntaxError (..), Warning (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Global.Env (isDeclared)
import Thena.Language.Grammar
import Thena.Language.Reader
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Files (startingSession, loadProofFile)
import Thena.Render (renderTrouble, renderResponse)
import Thena.Syntax.Lexer
  (BlockKind (..), Located (..), Token (..), isIdentifier, lexModule, lexTokens)

tests :: TestTree
tests =
  testGroup
    "object-language blocks"
    [ testGroup "the lexer takes a block whole, in a module" lexing
    , testGroup "the reader gives its shape" reading
    , testGroup "the checker gives its meaning" meaning
    , testGroup "a metavariable is scoped to its language" scoped
    , testGroup "and says which classes a grammar reaches" reaching
    , testGroup "and a notation block gives a function a spelling" notating
    , testGroup "and refuses what §4.5 refuses" refusals
    , goldenVsString "grammars" "test/golden/grammars.golden" $ do
        (s0, trouble) <- startingSession
        let run (title, src) =
              let (s1, r) = loadProofSource Strict s0 src
               in ("-- " ++ title) : renderResponse s1 r
        pure (toLazyByteString (stringUtf8
          (unlines (concatMap (renderTrouble s0) trouble ++ concatMap run (("the spec's STLC", stlc) : map fst refused ++ unreadable)))))
    ]

-- ---------------------------------------------------------------------------

-- | **A metavariable is scoped to the namespace its language's datatype opens**
-- — HIS ruling of 2026-11-02, MS10 phase 255, `~g4k5g`. The table used to be
-- every installed grammar's letters, so two object languages could not both use
-- @e@; what a block may write is now what the @open@s above it bring into view.
scoped :: [TestTree]
scoped =
  [ -- **The refusal the item measured, and it is gone.** Neither language is
    -- open in the other's block, so @Expr@'s @e@ and @Code@'s @e@ are already
    -- different names — no @namespace@ written anywhere.
    accepted "two languages may both declare e"
      (expr "e" ++ code "e") ["Expr", "Code"]
    -- **A judgment borrows a letter per language it talks about**, which is the
    -- case his ruling is about: a judgment declares none of its own.
  , accepted "a judgment borrows a letter from each language it opens"
      (expr "e" ++ ["open Expr", ""] ++ code "c" ++ ["open Code", ""] ++ judgment "e" "c")
      ["Expr", "Code", "compiles"]
    -- **Refused and not chosen**, as every other two-answer lookup is.
  , refusal "two open languages that both use e is refused, naming both"
      (expr "e" ++ code "e" ++ ["open Expr", "open Code", ""] ++ judgment "e" "e")
      ("refused: in the judgment compiles: e is a metavariable of Scoped.Code and Scoped.Expr, "
         ++ "all in scope here; open one renaming it")
    -- **The tie-break is @open … renaming@**, and it needed nothing new.
  , accepted "and a renaming settles it"
      (expr "e" ++ code "e" ++ ["open Expr", "open Code renaming ( e -> c )", ""]
         ++ judgment "e" "c")
      ["Expr", "Code", "compiles"]
    -- **The one silent thing the scoping introduced** (§4.2: a word that is no
    -- metavariable is a terminal), so it is a warning and not a refusal.
  , testCase "a letter whose language is shut is a terminal, and warns" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines (["module Shut where", ""]
             ++ ["language Ty, T, S where", "  base  -> \953", "  arrow -> ( T -> S )", ""]
             ++ ["language LC, M where", "  app -> ( M M )", "  ty  -> ( T )"])) of
        (_, ProofLoaded _ _ _ ws) ->
          ws @?= [ MetavariableNotOpen LanguageBlock "LC" "ty" "T" "Shut.Ty" ]
        (_, other) -> assertFailure (show other)

    -- **A BLOCK MAY BE WRITTEN INSIDE A @namespace@ BLOCK — MS10 PHASE 258.**
    -- All four kinds, and each one's datatype, constructors and generated
    -- equipment land under the namespace. This is the placement half of the
    -- scoping: the metavariable half was phase 255.
  , testCase "all four block kinds declare inside a namespace" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 blocksInANamespace of
        (_, ProofLoaded _ ds _ _) ->
          ds @?= ["A.x", "A.Ty", "A.LC", "A.Ctx", "A.typing"]
        (_, other) -> assertFailure (show other)

    -- **The generated equipment is placed once, not twice.** A definition is
    -- minted relative to the namespace and the declaring op supplies the
    -- prefix, so an absolute mint would have landed at @A.A.LC.subst.A.x@.
    --
    -- **THE CLASS IS NAMED AFTER THE LANGUAGE AND NOT BEFORE IT** (MS12 phase
    -- 313, 'Thena.Language.Grammar.classIn'): the steps the language's own name
    -- has already said are not said again, so @A.x@ inside @A.LC@ gives
    -- @A.LC.subst.x@. His ruling of 2026-11-10 spells the family
    -- @Compiles.subst.Source.x@ — the class's name after the language — and
    -- from this phase a module's declarations live under the module's name, so
    -- repeating the shared steps would have made that ruling's own example
    -- @Two.Compiles.subst.Two.Source.x@ and the printer's promised @subst.x@
    -- unreachable. A class the language does NOT share a prefix with is
    -- unchanged, which is the case that distinction exists for.
  , testCase "and a language's substitution is placed under the namespace" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 blocksInANamespace
          env = globals (machineOf s1)
      ( isDeclared (named "NSAll.A.LC.subst.x") env
        , isDeclared (named "NSAll.A.LC.fv.x") env
        , isDeclared (named "NSAll.A.LC.subst.A.x") env
        , isDeclared (named "NSAll.LC.subst.x") env ) @?= (True, True, False, False)

    -- **A COMMA LIST REACHES THE OWNING LANGUAGE BY ITS KEY, NOT ITS WORD**
    -- (2026-11-10). The pair rule a rule's grammar gets per class names the
    -- class's owning language as an Earley nonterminal, and a nonterminal is
    -- the dotted key — built from the word it referred to one that does not
    -- exist, so the comma-list form could not parse at all for a language
    -- inside a namespace: this body refused with @unexpected ','@ while the
    -- same body at the top level took it.
    -- **NOTHING IN THE EXAMPLE CORPUS CAN CATCH THAT**, because every example
    -- declares its token class at the top level.
    -- 'Thena.Language.Judgment.ownerKey'.
  , testCase "a comma list parses for a language inside a namespace" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module Swap where", ""
             , "namespace A where"
             , "  x : Token String"
             , "  x = /[a-z][a-zA-Z0-9']*/"
             , "  language LC, M, N, E where"
             , "    var : x as occurrence -> x"
             , "    abs : x as binder     -> ( λ x . E[x] )"
             , "    app                   -> ( M N )"
             , ""
             , "open A.LC", ""
             , "judgment sw = M ⇄ N where", ""
             , "  Swap:  ---------------------------------------"
             , "         ( x_1 x_2 ) ⇄ ( x_1 x_2 )[x_1->x_2, x_2->x_1]"
             , "" ]) of
        (_, ProofLoaded _ ds _ ws) -> (ds, ws) @?= (["A.x", "A.LC", "sw"], [])
        (_, other) -> assertFailure (show other)
    -- **A WRITTEN SUBSTITUTION MAY NAME ITS CLASS — HIS RULING OF 2026-11-10.**
    -- Neither written form said which class it substituted for: the bracket's
    -- middle item is a slot that reads a name, and a comma list's pair was
    -- built from the class's word. So this file — a compilation relation over
    -- two languages whose identifier classes are both written @x@, which
    -- phase 304 made loadable — could write no substitution at all. **Both
    -- forms take a qualifier now**, the class's whole name, and the bare
    -- spelling is unchanged wherever it is unambiguous.
  , testCase "a substitution names its class, so two classes of one word are both writable" $ do
      (s0, _) <- startingSession
      s <- either assertFailure pure (loadOrSay s0 oneWordTwoClasses)
      said s ":parse Compiles ( a ~> b ) [ Source.x: y -> c ]"
        @?= [ "subst.Source.x(step(var(a), ref(b)), y, var(c))" ]
      said s ":parse Compiles ( a ~> b ) [ Target.x: y -> c ]"
        @?= [ "subst.Target.x(step(var(a), ref(b)), y, ref(c))" ]
      -- **The bare spelling is still two readings here, and that is what the
      -- qualifier is for** — not a defect left behind. It names both.
      said s ":parse Compiles ( a ~> b ) [ y -> c ]"
        @?= [ "in Compiles`( a ~> b ) [ y -> c ]`: this term parses two ways, as subst.Source.x(step(var(a), ref(b)), y, var(c)) and as subst.Target.x(step(var(a), ref(b)), y, ref(c))" ]
      -- **And a comma list qualifies each pair**, so the simultaneous
      -- substitution gets one list per class with that class's pair in it —
      -- where before the second class's language could not appear in a pair at
      -- all and the two lists were keyed by the one word.
      drop 1 (said s ":show ok")
        @?= [ "  { ok.R-both : ∀ (C : Compiles) (x : String) (N : LC) (P : Mach) -> ok`${Compiles.subst-* {0 0 0 0 0 0} C (cons {0} (And {0 0} String LC) (both {0 0} String LC x N) (nil {0} (And {0 0} String LC))) (cons {0} (And {0 0} String Mach) (both {0 0} String Mach x P) (nil {0} (And {0 0} String Mach)))} good` }" ]

    -- **A block's own word opens where it is written** (MS10 phase 258): the
    -- @open Ty@ inside the namespace is what every one of those blocks needs,
    -- since a block that writes its letters with its language shut installs
    -- them as literal text. A namespace resolves by the same walk a name does.
    -- **A CLASS THE BLOCK CANNOT SEE IS A TERMINAL, AND THAT IS SILENT**
    -- (MS10 phase 259). §4.2 makes any unresolved word a terminal, so a class
    -- shut away in another namespace is the same trap phase 255 found for a
    -- letter — and gets the same warning, naming the class in full.
  , testCase "a class in a closed namespace is read as a terminal, with a warning" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module Shut where", ""
             , "namespace B where"
             , "  x : Token String"
             , "  x = /[a-z][a-zA-Z0-9']*/"
             , ""
             , "namespace A where"
             , "  language LC, M, N where"
             , "    app -> ( M N )"
             , "    idx -> ( x )"
             , "" ]) of
        (_, ProofLoaded _ ds _ ws) -> do
          ds @?= ["B.x", "A.LC"]
          ws @?= [ TokenClassNotOpen LanguageBlock "LC" "idx" "x" "Shut.B.x" ]
        (_, other) -> assertFailure (show other)

    -- **AN @open@ REACHES TO THE END OF THE BLOCK IT IS WRITTEN IN — HIS
    -- RULING OF 2026-11-03, `~ckmsk`.** Before it, a @namespace@ block's
    -- @open@ kept working for the rest of the file, so the second of two
    -- namespaces could not declare a language of the same word: it was refused
    -- 'MetavariableTaken', which is very nearly the collision this milestone
    -- exists to remove. **And nothing the author wrote was wrong** — since
    -- phase 255 a block MUST be opened beside itself or its letters stop being
    -- metavariables, so the required shape was the leaking one.
  , testCase "two namespaces may both hold a language of one word" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 twoNamespacesOneWord of
        (_, ProofLoaded _ ds _ ws) -> (ds, ws) @?= (["A.Ty", "B.Ty"], [])
        (_, other) -> assertFailure (show other)

    -- **The pop is why the bare word answers neither**, and that is the point:
    -- the opens came off with their blocks, so @Ty@ outside them is not a
    -- language at all — where a term of each is still written by its path.
  , testCase "and the word that each block opened is shut again after it" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 twoNamespacesOneWord
          ask t = last (said s1 (":infer " ++ t))
      ( ask "A.Ty`\956`", ask "B.Ty`\959`", ask "Ty`\956`" ) @?=
        ( "A.Ty`\956` : A.Ty.Ty"
        , "B.Ty`\959` : B.Ty.Ty"
        , "stuck: no language called Ty has been declared" )

    -- **A FILE'S TOP LEVEL IS NOT ONE OF THOSE BLOCKS** and its @open@s are
    -- unchanged — they join the session, which is what @examples/02@'s closing
    -- @open Ctx@ is for and what `~7zn7k` settled. So the same two namespaces
    -- with an @open A@ written at the file's level answer the bare word.
  , testCase "a file-level open is not popped, so the bare word resolves" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 (twoNamespacesOneWord ++ "\nopen A\n")
      -- **And the TYPE shortens too**, which is the same open read back by
      -- the printer: @A.Ty.Ty@ spells as @Ty@ while the open is live, where the
      -- test above printed it whole with both blocks shut.
      last (said s1 ":infer Ty`\956`") @?= "Ty`\956` : Ty"

    -- **A GENERATED NOTATION MAY NOT DEPEND ON WHICH @open@ THE AUTHOR WROTE**
    -- (MS10 phase 265). The ascription in a generated @subst-x@ production was
    -- the class's WORD, so a language reaching a class in another namespace was
    -- refused outright — @open Source.LC@ is all the metavariables need, and
    -- the bare @x@ in the generated block then reached nothing at all. The
    -- ascription is the class's PATH now, where the function's name still hangs
    -- off its word. **The @swapped@ line is the notation itself**, so the block
    -- is exercised and not merely accepted.
  , testCase "a language reaches a class in another namespace with only its own open" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 classAcrossANamespace of
        (_, ProofLoaded _ ds _ ws) ->
          (ds, ws) @?= (["Source.x", "Source.LC", "Wrap", "swapped"], [])
        (_, other) -> assertFailure (show other)

    -- **And the generated family is the reaching language's, with the reached
    -- class's WHOLE NAME inside the family's step** — @Wrap.subst.Source.x@
    -- for a class @Source.x@, his ruling of 2026-11-10. It used to be
    -- @Wrap.subst-x@, the one place in the module system where a path was
    -- dropped, and `~ps4c7` is the item that ruling closed.
  , testCase "and the generated family hangs off the reached class's path" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 classAcrossANamespace
          env = globals (machineOf s1)
      ( isDeclared (named "Notate.Wrap.subst.Source.x") env
        , isDeclared (named "Notate.Wrap.fv.Source.x") env
        , isDeclared (named "Notate.Wrap.subst.x") env ) @?= (True, True, False)

    -- **TWO CLASSES OF ONE WORD ARE ACCEPTED — HIS RULING OF 2026-11-10,
    -- `~ps4c7`.** They were refused from MS10 phase 259 until phase 304,
    -- because a generated name was suffixed with the class's WORD and @fv-x@
    -- would have meant two things. The class's whole name sits inside the
    -- family's step now, so @Top.fv.B.x@ and @Top.fv.C.x@ are two names and
    -- there is nothing to refuse. **This is the file the item was measured on.**
  , testCase "one language reaching two classes of one word is accepted" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource Strict s0 twoClassesOneWord
      case r of
        ProofLoaded _ ds _ _ -> do
          ds @?= ["B.x", "B.L1", "C.x", "C.L2", "Top"]
          let env = globals (machineOf s1)
          ( isDeclared (named "Twice.Top.subst.B.x") env
            , isDeclared (named "Twice.Top.subst.C.x") env
            , isDeclared (named "Twice.Top.fv.B.x") env
            , isDeclared (named "Twice.Top.fv.C.x") env
            , isDeclared (named "Twice.Top.subst-*") env )
            @?= (True, True, True, True, True)
        _ -> assertFailure (unlines (renderResponse s1 r))

    -- **AND THE BRACKET NOTATION OF THOSE TWO IS AMBIGUOUS — `~5659b`, OPEN.** The
    -- generated notation's own text is still the class's bare word, so both classes
    -- install @e [ x -> n ]@ and a term written that way parses two ways. **It is
    -- reported and names both readings**, and the functions are reachable by name — the
    -- test above declares them. Pinned here so the residue is not mistaken for a
    -- regression, and so a fix has something to change.
  , testCase "but the bracket notation of two classes of one word is ambiguous" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 twoClassesOneWord
          out = last (said s1 ":parse Top ( a , b ) [ y -> c ]")
      assertBool out ("parses two ways" `isInfixOf` out)
      assertBool out ("Top.subst.B.x" `isInfixOf` out
                        && "Top.subst.C.x" `isInfixOf` out)

    -- **A TOKEN CLASS MAY BE CALLED `all` — `~xrq7t`, phase 304.** It could not before:
    -- the simultaneous substitution was @L.subst-all@ and the per-class one was
    -- @subst-@ plus the class's word, so the two names coincided, **the file was
    -- accepted**, and a use of it failed with a mismatch naming neither. The
    -- simultaneous one is @L.subst-*@ now and `*` cannot begin a name, so no class can
    -- be spelled it. **The `refl` is the point**: the substitution is not merely
    -- declared, it computes.
  , testCase "a token class may be called all, and its substitution computes" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module AllClass where", ""
             , "all : Token String"
             , "all = /[a-z][a-zA-Z0-9']*/"
             , ""
             , "language LC, M, N, E where"
             , "  var : all as occurrence -> all"
             , "  abs : all as binder     -> ( \955 all . E[all] )"
             , "  app                     -> ( M N )"
             , ""
             , "replaces : Eq LC (LC.subst.all LC`( \955 y . ( x y ) )` \"x\" LC`z`)"
             , "                 LC`( \955 y . ( z y ) )`"
             , "replaces = refl LC LC`( \955 y . ( z y ) )`", "" ]) of
        (s1, ProofLoaded _ ds _ _) -> do
          ds @?= ["all", "LC", "replaces"]
          let env = globals (machineOf s1)
          ( isDeclared (named "AllClass.LC.subst-*") env
            , isDeclared (named "AllClass.LC.subst.all") env ) @?= (True, True)
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))

    -- **A TAG RESOLVES LIKE ANY OTHER NAME — MS10 PHASE 260, `~zjkvd`, HIS
    -- RULING OF 2026-10-30.** Until this phase a tag was matched against a
    -- root-level grammar name, so a language inside a @namespace@ had no
    -- writable terms in any spelling: the bare word found nothing and the
    -- qualified one did not lex. Four readings, in one load.
  , testCase "a tag resolves by the walk, qualified or bare, inside or after open" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module Tags where", ""
             , "namespace A where"
             , "  x : Token String"
             , "  x = /[a-z][a-zA-Z0-9']*/"
             , ""
             , "  language LC, M, N, E where"
             , "    var : x as occurrence -> x"
             , "    app                   -> ( M N )"
             , ""
             , "  open LC"
             , ""
             , "  bare : LC"
             , "  bare = LC" ++ region "( y y )"
             , ""
             , "  atProduction : LC"
             , "  atProduction = LC[var]" ++ region "y"
             , ""
             , "  qualified : LC"
             , "  qualified = A.LC" ++ region "( y y )"
             , ""
             , "open A"
             , ""
             , "afterOpen : A.LC"
             , "afterOpen = LC" ++ region "( z z )"
             , "" ]) of
        (_, ProofLoaded _ ds _ _) ->
          ds @?= [ "A.x", "A.LC", "A.bare", "A.atProduction", "A.qualified", "afterOpen" ]
        (_, other) -> assertFailure (show other)

    -- **`open … renaming` reaches a tag, and the original word does not** — both
    -- for free, because the walk is `globalUnder` and nothing about a tag is
    -- written a second time.
  , testCase "a renamed open renames the tag, and the original word is gone" $ do
      (s0, _) <- startingSession
      let src extra = unlines
             ([ "module Renamed where", ""
              , "x : Token String"
              , "x = /[a-z][a-zA-Z0-9']*/"
              , ""
              , "namespace A where"
              , "  language LC, M, N where"
              , "    var : x as occurrence -> x"
              , "    app                   -> ( M N )"
              , ""
              , "  open LC"
              , ""
              , "open A renaming ( LC -> Lam )"
              , ""
              , "renamed : A.LC"
              , "renamed = Lam" ++ region "( y y )"
              , "" ] ++ extra)
      case loadProofSource Strict s0 (src []) of
        (_, ProofLoaded _ ds _ _) -> ds @?= ["x", "A.LC", "renamed"]
        (_, other) -> assertFailure (show other)
      let (s1, r) = loadProofSource Strict s0
                      (src ["gone : A.LC", "gone = LC" ++ region "( y y )", ""])
      case r of
        ProofLoaded {} -> assertFailure "the renamed-away word still named the language"
        _ -> last (renderResponse s1 r) @?=
               "stuck: no language called LC has been declared"

    -- **TWO OPENED NAMESPACES OFFERING ONE TAG IS REFUSED, not chosen** — the
    -- same answer every other two-answer lookup gives, and the writer's fix is
    -- the path. `~7x8rt` owns the wording of a scoping refusal.
  , testCase "two opened namespaces offering one tag is ambiguous" $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource Strict s0 (unlines
             [ "module Ambiguous where", ""
             , "namespace A where"
             , "  language Ty where"
             , "    base -> \953"
             , ""
             , "namespace B where"
             , "  language Ty where"
             , "    other -> \969"
             , ""
             , "open A"
             , "open B"
             , ""
             , "which : A.Ty"
             , "which = Ty" ++ region "\953"
             , "" ])
      case r of
        ProofLoaded {} -> assertFailure "an ambiguous tag was accepted"
        _ -> last (renderResponse s1 r) @?=
               "stuck: Ty could be Ambiguous.B.Ty or Ambiguous.A.Ty, so it is ambiguous here"

  , testCase "and a namespace resolves by the walk, so open Ty works inside A" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module Opens where", ""
             , "namespace A where"
             , "  language Ty, T where"
             , "    base -> \953"
             , ""
             , "  open Ty"
             , "" ]) of
        (_, ProofLoaded _ ds _ _) -> ds @?= ["A.Ty"]
        (_, other) -> assertFailure (show other)
  ]
  where
    -- A backtick written as its code point, because this file is Haskell
    -- source and a tag's fence is a backtick either way.
    region txt = [toEnum 96] ++ txt ++ [toEnum 96]
    expr m = [ "language Expr, " ++ m ++ " where", "  lit  -> z"
             , "  plus -> ( " ++ m ++ "\8321 + " ++ m ++ "\8322 )", "" ]
    code m = [ "language Code, " ++ m ++ " where", "  push -> PUSH"
             , "  seq  -> ( " ++ m ++ "\8321 ; " ++ m ++ "\8322 )", "" ]
    judgment e c = [ "judgment compiles = " ++ e ++ " ~> " ++ c ++ " where", ""
                   , "  C-lit:  ----------", "          z ~> PUSH" ]

    -- **The token class is INSIDE the namespace** (MS10 phase 259, the last
    -- piece of `~g4k5g`): a class resolves by the same outward walk a
    -- metavariable and a function name do, and what the generated names hang
    -- off is the class's word, so @A.x@ still gives @A.LC.fv.x@.
    -- Two namespaces, each declaring a language of the same word and opening
    -- it beside itself, which is the shape phase 255 requires.
    twoNamespacesOneWord = unlines
      [ "module TwoTy where", ""
      , "namespace A where"
      , "  language Ty, T, S where"
      , "    base  -> \956"
      , "    arrow -> ( T -> S )"
      , ""
      , "  open Ty"
      , ""
      , "namespace B where"
      , "  language Ty, T, S where"
      , "    base  -> \959"
      , "    arrow -> ( T => S )"
      , ""
      , "  open Ty"
      , "" ]

    -- **A class inside a namespace, reached by a language outside it** (MS10
    -- phase 265). @Wrap@ reads @Source.LC@'s terms, so it reaches @Source.x@
    -- through them and gets a substitution family of its own — and the only
    -- @open@ it needs is the one its metavariable @M@ needs.
    classAcrossANamespace = unlines
      [ "module Notate where", ""
      , "namespace Source where"
      , "  x : Token String"
      , "  x = /[a-z][a-zA-Z0-9']*/"
      , ""
      , "  language LC, M, N, E where"
      , "    var : x as occurrence -> x"
      , "    app                   -> ( M N )"
      , ""
      , "open Source.LC"
      , ""
      , "language Wrap, W where"
      , "  box -> [ M ]"
      , ""
      , "swapped : Wrap"
      , "swapped = Wrap`[ ( a b ) ][ a -> c ]`"
      , "" ]

    blocksInANamespace = unlines
      [ "module NSAll where", ""
      , "namespace A where"
      , "  x : Token String"
      , "  x = /[a-z][a-zA-Z0-9']*/"
      , ""
      , "  language Ty, T, S where"
      , "    base  -> \953"
      , "    arrow -> ( T -> S )"
      , ""
      , "  open Ty"
      , ""
      , "  language LC, M, N, E where"
      , "    var : x as occurrence -> x"
      , "    abs : x as binder     -> ( \955 x : T . E[x] )"
      , "    app                   -> ( M N )"
      , ""
      , "  open LC"
      , ""
      , "  context Ctx, G where"
      , "    empty  -> \183"
      , "    extend -> G , x : T"
      , ""
      , "  open Ctx"
      , "  open extend-in"
      , ""
      , "  judgment typing = G \8866 M : T where"
      , ""
      , "    T-var:  x : T \8712 G"
      , "            -----------"
      , "            G \8866 x : T"
      , ""
      , "  open typing"
      ]

    accepted what body want = testCase what $ do
      r <- loads body
      r @?= Right want
    refusal what body want = testCase what $ do
      r <- loads body
      r @?= Left want

    loads body = do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource Strict s0 (unlines (["module Scoped where", ""] ++ body))
      pure $ case r of
        ProofLoaded _ names _ _ -> Right names
        _                       -> Left (last (renderResponse s1 r))

-- ---------------------------------------------------------------------------

lexing :: [TestTree]
lexing =
  [ testCase "a block at column 1 is one token, keyword excluded" $
      tokens lexModule "language L, M where\n  f -> ( M )\n"
        @?= Right [TBlock LanguageBlock " L, M where\n  f -> ( M )\n"]
  , testCase "it ends at the next line with anything in column 1" $
      tokens lexModule "context C, G where\n  e -> .\n\n  f -> G ,\nx : T\n"
        @?= Right [ TBlock ContextBlock " C, G where\n  e -> .\n\n  f -> G ,\n"
                  , TIdent "x", TColon, TIdent "T" ]
  , testCase "characters Thena reserves are just text inside it" $
      tokens lexModule "language L where\n  f -> [ λ ⌜ ] /\n"
        @?= Right [TBlock LanguageBlock " L where\n  f -> [ λ ⌜ ] /\n"]
    -- MS8 phase 158: the fourth block word.
  , testCase "a notation block is taken whole too" $
      tokens lexModule "notation C where\n  join a b -> a \8746 b\n"
        @?= Right [TBlock NotationBlock " C where\n  join a b -> a \8746 b\n"]
  , testCase "outside a module the keyword is a keyword and nothing more" $
      tokens lexTokens "language L" @?= Right [TLanguage, TIdent "L"]
    -- **AN INDENTED BLOCK IS A BLOCK SINCE MS10 PHASE 258**, which is what
    -- lets one be written inside a @namespace@ block. It used to be refused by
    -- the lexer — @tokens lexModule "  context C"@ gave @TContext@ and an
    -- identifier — and the parser then said /unexpected context/.
  , testCase "an indented block is a block too" $
      tokens lexModule "  context C, G where\n    e -> .\n"
        @?= Right [TBlock ContextBlock " C, G where\n    e -> .\n"]
    -- **And the keyword's own column is what ends it**: a line back at the
    -- keyword's column is the namespace's next item, not more of the block.
  , testCase "and it ends at a line indented no further than the keyword" $
      tokens lexModule "  context C, G where\n    e -> .\n  x : T\n"
        @?= Right [ TBlock ContextBlock " C, G where\n    e -> .\n"
                  , TIdent "x", TColon, TIdent "T" ]
  , -- His ruling, 2026-09-19: both words are reserved, as language is.
    -- @notation@ joined them at MS8 phase 158.
    testCase "context, judgment and notation are no longer names" $
      map isIdentifier ["context", "judgment", "notation", "contexts", "notations"]
        @?= [False, False, False, True, True]
  ]
  where
    tokens lexer src = map (\(Located _ t) -> t) <$> lexer src

-- | A slot at a universe, both as a type former's own spelling and as a
-- function's (MS8 phase 160). @same@ is `refl`, so the load asserts that the
-- universe slot was filled with the type @Ty@ and @k@ ran.
universeSlots :: String
universeSlots =
  unlines
    [ "module U where", ""
    , "language Ty, T, S where"
    , "  base  -> ι"
    , "  arrow -> ( T -> S )", ""
    , "open Ty"
    , "data Imp : Type₀ -> Type₀ -> Type₁ where"
    , "  { impIntro : ∀ (A : Type₀) (B : Type₀) -> (A -> B) -> Imp A B }", ""
    , "open Imp"
    , "notation Imp A B -> A ⊃ B where", ""
    , "k : Type₀ -> Ty -> Ty"
    , "k = \\ A -> \\ t -> t", ""
    , "notation Ty where"
    , "  k A t -> ⟪ A ⟫ t", ""
    , "u : Ty"
    , "u = Ty`⟪ Ty ⟫ ι`", ""
    , "same : Eq Ty u base"
    , "same = refl Ty base", ""
    ]

-- | The write-up's §4 Example 1, both ways (MS8 phase 160). @same@ is `refl`, so
-- the load asserts that the notation builds the hand-written term.
lamByHand :: String
lamByHand =
  unlines
    [ "module Lam where", ""
    , "w : Token String"
    , "w = /[a-z]+/", ""
    , "language Tw, P, Q where"
    , "  twBase  -> ο"
    , "  twArrow -> ( P ⇒ Q )", ""
    , "open Tw"
    , "data Lam : Type₀ where"
    , "  { lmVar : String -> Lam"
    , "  ; lmAbs : String -> Tw -> Lam -> Lam"
    , "  ; lmApp : Lam -> Lam -> Lam }", ""
    , "open Lam"
    , "notation Lam where"
    , "  lmVar (v : w) : v as occurrence -> v"
    , "  lmAbs (v : w) p b : v as binder -> ( ƛ v : p . b[v] )"
    , "  lmApp a b                       -> ( a b )", ""
    , "e : Lam"
    , "e = Lam`( ƛ a : ο . a )`", ""
    , "same : Eq Lam e (lmAbs \"a\" twBase (lmVar \"a\"))"
    , "same = refl Lam (lmAbs \"a\" twBase (lmVar \"a\"))", ""
    ]

lamByBlock :: String
lamByBlock =
  unlines
    [ "module Lam where", ""
    , "w : Token String"
    , "w = /[a-z]+/", ""
    , "language Tw, P, Q where"
    , "  twBase  -> ο"
    , "  twArrow -> ( P ⇒ Q )", ""
    , "open Tw"
    , "language Lam, M, N, E where"
    , "  lmVar : w as occurrence -> w"
    , "  lmAbs : w as binder     -> ( ƛ w : P . E[w] )"
    , "  lmApp                   -> ( M N )", ""
    , "open Lam"
    ]

loadOrSay :: Session -> String -> Either String Session
loadOrSay s0 src = case loadProofSource Strict s0 src of
  (s1, ProofLoaded {}) -> Right s1
  (s1, other) -> Left (last (renderResponse s1 other))

-- | **Two languages whose identifier classes are both written @x@, and a
-- relation between them** — the shape of two-language metatheory, and the file
-- phase 304 made loadable by giving a generated name the class's path. Its
-- judgment writes a comma list that qualifies each pair with its class.
oneWordTwoClasses :: String
oneWordTwoClasses = unlines
  [ "module Two where", ""
  , "namespace Source where"
  , "  x : Token String"
  , "  x = /[a-z][a-zA-Z0-9']*/"
  , "  language LC, M, N, E where"
  , "    var : x as occurrence -> x"
  , "    abs : x as binder     -> ( λ x . E[x] )"
  , "    app                   -> ( M N )"
  , ""
  , "namespace Target where"
  , "  x : Token String"
  , "  x = /[a-z][a-zA-Z0-9']*/"
  , "  language Mach, P, Q, B where"
  , "    ref  : x as occurrence -> x"
  , "    lam  : x as binder     -> ( fn x . B[x] )"
  , "    call                   -> ( P @ Q )"
  , ""
  , "open Source.LC"
  , "open Target.Mach", ""
  , "language Compiles, C where"
  , "  step -> ( M ~> P )", ""
  , "open Compiles", ""
  , "judgment ok = C good where", ""
  , "  R-both: ------------------------------------------"
  , "          C[Source.x: x -> N, Target.x: x -> P] good"
  , "" ]

-- | A judgment indexed by a judgment, declared by hand and then spelled — the
-- shape `~wkv37` said a @judgment@ block cannot generate (MS8 phase 160).
validSource :: String
validSource =
  unlines
    [ "module V where", ""
    , "x : Token String"
    , "x = /[a-z]+/", ""
    , "language Ty, T, S where"
    , "  base  -> ι"
    , "  arrow -> ( T -> S )", ""
    , "open Ty"
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  app                   -> ( M N )", ""
    , "open LC"
    , "context Ctx, Γ where"
    , "  empty  -> ·"
    , "  extend -> Γ , x : T", ""
    , "open Ctx"
    , "judgment typing = Γ ⊢ M : T where", ""
    , "  T-var:  x : T ∈ Γ"
    , "          -----------"
    , "          Γ ⊢ x : T", ""
    , "data Valid : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Type₀ where"
    , "  { validAny : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Valid G M T d }", ""
    , "open Valid"
    , "notation Valid G M T d -> ⊢ G , M , T by d valid where", ""
    ]

loadProofSession :: Session -> Either String Session
loadProofSession s0 = case loadProofSource Strict s0 validSource of
  (s1, ProofLoaded {}) -> Right s1
  (s1, other) -> Left (unlines (renderResponse s1 other))

-- | **Two namespaces whose token classes are both written @x@, and a third language
-- that reaches both** — the shape of all two-language metatheory, and the file `~ps4c7`
-- was measured on. **Refused from MS10 phase 259 until MS11 phase 304**, when his ruling
-- of 2026-11-10 made the class a path inside the family's step.
twoClassesOneWord :: String
twoClassesOneWord = unlines
  [ "module Twice where", ""
  , "namespace B where"
  , "  x : Token String"
  , "  x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "  language L1, P where"
  , "    v : x as occurrence -> x"
  , "    pp -> ( P P )"
  , ""
  , "namespace C where"
  , "  x : Token String"
  , "  x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "  language L2, Q where"
  , "    w : x as occurrence -> x"
  , "    qq -> [ Q Q ]"
  , ""
  , "open B.L1"
  , "open C.L2"
  , ""
  , "language Top, R where"
  , "  pair -> ( P , Q )"
  , "" ]

said :: Session -> String -> [String]
said s line = let (s', r) = command s line in renderResponse s' r

-- ---------------------------------------------------------------------------

reading :: [TestTree]
reading =
  [ testCase "a header, and a production of each shape" $
      readBlock LanguageBlock 1
        " LC, M, N where\n  var : x as occurrence -> x\n  app -> ( M N )\n"
        @?= Right
          (Block LanguageBlock "LC" ["M", "N"]
             [ Production 2 "var" [] (Just (AsOccurrence "x")) [Word "x"]
             , Production 3 "app" [] Nothing (map Word ["(", "M", "N", ")"])
             ] [])
  , testCase "the three metadata forms" $
      map (fmap (map productionMetadata . blockProductions) . readBlock LanguageBlock 1)
        [ " L where\n  f : x as binder -> x\n"
        , " L where\n  f : { x, y } as binders -> x y\n"
        , " L where\n  f : {x,y} as binders -> x y\n"
        ]
        @?= map (Right . (: []) . Just) [AsBinders ["x"], AsBinders ["x", "y"], AsBinders ["x", "y"]]
  , testCase "a binding form reads across the spaces in its bracket" $
      items " L where\n  f -> E[x, y] ( E [ x ] )\n"
        @?= Right [ Binding "E" ["x", "y"], Word "(", Word "E", Word "[", Word "x", Word "]", Word ")" ]
  , testCase "a deeper line continues the production, and -- starts a comment" $
      items " L where\n  f -> a b -- not an item\n       c\n"
        @?= Right (map Word ["a", "b", "c"])
  , testCase "-> after the first is a terminal" $
      items " Ty, T where\n  arrow -> T -> T\n" @?= Right (map Word ["T", "->", "T"])
  , testCase "-->, not a comment, is a terminal too" $
      items " L where\n  f -> a --> b\n" @?= Right (map Word ["a", "-->", "b"])
  ]
  where
    items src = concatMap productionItems . blockProductions <$> readBlock LanguageBlock 1 src

unreadable :: [(String, String)]
unreadable =
  [ ("no where", "module M where\n\nlanguage L M\n  f -> a\n")
  , ("metadata that is none of the three", "module M where\n\nlanguage L where\n  f : x as whatever -> x\n")
  , ("a production with no arrow", "module M where\n\nlanguage L where\n  f a b\n")
  , ("a bracket never closed", "module M where\n\nlanguage L, M where\n  f -> M[b c\n")
  , ("a line indented less", "module M where\n\nlanguage L where\n    f -> a\n  g -> b\n")
  ]

-- ---------------------------------------------------------------------------

-- | The spec's own grammars (§4.6, §5.2), with a vacuous binder added.
-- | **One language, two name classes** (MS8 phase 153). @x@ is the class @L@
-- reads an occurrence at; @X@ is bound by @big@ and occurs nowhere, which is
-- F-sub's shape in miniature — there @Λ X <: T . t@ binds a type variable from
-- a term production and every occurrence of it is in a type. The class @X@
-- belonging to another grammar is `~5k3mg`; recording which class a binder
-- binds at is what makes that expressible at all.
twoClasses :: String
twoClasses =
  unlines
    [ "module Two where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "X : Token String"
    , "X = /[A-Z][a-zA-Z0-9']*/"
    , ""
    , "language L, M, N where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( lam x . M[x] )"
    , "  big : X as binder     -> ( all X . M[X] )"
    , "open L"
    ]

-- | **A binder of one language free in a slot of another** (MS8 phase 154).
-- @P@ owns the class @X@, and @L@ binds an @X@ over a slot of @P@ — so @P@
-- reaches the class @f@'s binder binds at and the block installs. It is what
-- `~5k3mg` exists for, refused until phase 154, and still refused when the
-- slot's language reaches no such class.
foreignScope :: String
foreignScope =
  unlines
    [ "module Foreign where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "X : Token String"
    , "X = /[A-Z][a-zA-Z0-9']*/"
    , ""
    , "language P, R where"
    , "  pvar : X as occurrence -> X"
    , "open P"
    , ""
    , "language L, M where"
    , "  var : x as occurrence -> x"
    , "  f : X as binder       -> ( pack X = M in R[X] )"
    , "open L"
    ]

-- | **Three languages in a chain** (MS8 phase 154). @P@ reads an occurrence at
-- @x@ and nothing else does; @Q@ holds an @R@, and @L@ holds an @S@ — so the
-- class @L@ reaches it reaches through two slots and names nowhere itself.
chained :: String
chained =
  unlines
    [ "module Chain where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language P, R where"
    , "  pvar : x as occurrence -> x"
    , "open P"
    , ""
    , "language Q, S where"
    , "  pwrap -> ( R )"
    , "open Q"
    , ""
    , "language L, M where"
    , "  lpair -> ( S M )"
    , "open L"
    ]

stlc :: String
stlc =
  unlines
    [ "module STLC where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> T -> S"
    , "open Ty"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( \955 x : T . E[x] )"
    , "  app                   -> ( M N )"
    , "  repeat                -> { M M }"
    , "  vacuous : { x } as binders -> let x = M in N"
    , "open LC"
    , ""
    , "context Ctx, \915 where"
    , "  empty  -> \183"
    , "  extend -> \915 , x : T"
    , "open Ctx"
    ]

meaning :: [TestTree]
meaning =
  [ testCase "the module loads, with the vacuous binder's warning" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 stlc of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "Ty", "LC", "Ctx"]
          -- **One warning, and it used to be two** (MS9 phase 212). The second
          -- was the context's generated lookup (phase 107): its @ne@ premise
          -- depends on earlier arguments, and the no-confusion generator
          -- declined the whole datatype for it. It now states a transported
          -- chain of equations instead, so there is nothing to warn about —
          -- asserted below rather than left to the absence of a line.
          ws @?= [ VacuousBinder LanguageBlock "LC" "vacuous" "x" ]
        (_, other) -> assertFailure (show other)
  , testCase "the arguments and roles of LC, production by production" $ do
      gs <- installed stlc
      case [ g | g <- gs, grammarName g == named "STLC.LC" ] of
        [g] ->
          -- **The datatype's constructors, so `constructorProductions`** — since
          -- MS8 phase 159 the grammar also carries the generated @E[x -> N]@
          -- notation, which is a function production and asserted below.
          map (\p -> (gproductionName p, gproductionArguments p)) (constructorProductions g)
            @?= [ (named "STLC.LC.var", [Argument "x" str (Occurrence (named "STLC.x"))])
                , (named "STLC.LC.abs", [ Argument "x" str (Binder (named "STLC.x"))
                                     , Argument "T" (lang "Ty") Plain
                                     , Argument "E" (lang "LC") (Scope [0]) ])
                , (named "STLC.LC.app", [Argument "M" (lang "LC") Plain, Argument "N" (lang "LC") Plain])
                  -- §4.3: a name written twice is one argument.
                , (named "STLC.LC.repeat", [Argument "M" (lang "LC") Plain])
                , (named "STLC.LC.vacuous", [ Argument "x" str (Binder (named "STLC.x"))
                                         , Argument "M" (lang "LC") Plain
                                         , Argument "N" (lang "LC") Plain ])
                ]
        other -> assertFailure (show (length other) ++ " grammars called LC")
    -- **The notation generated substitution declares** (MS8 phase 159, §6.3,
    -- `~hwxrx`): the bracket form is no longer a privilege of the rule parser
    -- but a function production of the grammar, written as @E[x -> N]@ would be
    -- written by hand.
    --
    -- **The slot names are the production's own parameters since MS8 phase
    -- 171**, @e@ and @n@. They used to be metavariables in scope — the
    -- grammar's own for the term, the class's owner's for the replacement —
    -- hunted for so that no two slots shared a word, and the hunt existed only
    -- because a slot's word had to resolve to a metavariable somewhere. **Only
    -- the middle slot keeps a word that means something elsewhere**: it reads a
    -- name of the class, and a class slot is labelled with its class, which is
    -- what lets a rule write @x@ there.
  , testCase "generated substitution declares its own notation" $ do
      gs <- installed stlc
      case [ g | g <- gs, grammarName g == named "STLC.LC" ] of
        [g] -> do
          [ (gproductionName p, gproductionItems p)
            | p <- grammarProductions g, gproductionKind p == Function ]
            -- **TWO SPELLINGS, BOTH GENERATED** — his ruling of 2026-11-10.
            -- The qualified one carries the class's whole name as a terminal,
            -- which is the only thing in either production that says which
            -- class is substituted for; here the class is at the top level, so
            -- that terminal is the bare @x@ and the slot beside it reads a name.
            @?= [ ( GlobalName ["STLC", "LC", "subst"] "x"
                  , [ Slot "e" (lang "LC") []
                    , Terminal "["
                    , Slot "x" str []
                    , Terminal "->"
                    , Slot "n" (lang "LC") []
                    , Terminal "]" ] )
                , ( GlobalName ["STLC", "LC", "subst"] "x"
                  , [ Slot "e" (lang "LC") []
                    , Terminal "["
                    , Terminal "x"
                    , Terminal ":"
                    , Slot "x" str []
                    , Terminal "->"
                    , Slot "n" (lang "LC") []
                    , Terminal "]" ] ) ]
          -- Nothing of it reaches the datatype: §4.8's whole mechanism.
          map gproductionName (constructorProductions g)
            @?= map (named . ("STLC." ++))
                    [ "LC.var", "LC.abs", "LC.app"
                    , "LC.repeat", "LC.vacuous"
                    ]
        other -> assertFailure (show (length other) ++ " grammars called LC")
    -- **A context gets one too**, and `ContextTests` is where it is asserted:
    -- it needs a context that /reaches/ a class, which this fixture's @Ctx@ does
    -- not — its @Ty@ reads no occurrence, so nothing in it is ever substituted.
    -- **Two classes in one grammar** (MS8 phase 153, `~tmnrr` and `~5k3mg`).
    -- The whole of what this phase adds is that the two binders are recorded at
    -- the two different classes rather than both saying only "binder" — so a
    -- generator can tell them apart, which phase 155 is what needs it.
  , testCase "a binder at a second class is recorded at that class" $ do
      gs <- installed twoClasses
      case [ g | g <- gs, grammarName g == named "Two.L" ] of
        [g] ->
          [ (gproductionName p, map argumentRole (gproductionArguments p))
          | p <- constructorProductions g ]
            @?= [ (named "Two.L.var", [Occurrence (named "Two.x")])
                , (named "Two.L.abs", [Binder (named "Two.x"), Scope [0]])
                , (named "Two.L.big", [Binder (named "Two.X"), Scope [0]])
                ]
        other -> assertFailure (show (length other) ++ " grammars called L")
    -- **It installs and says nothing** (MS8 phase 155). It used to warn: the
    -- generator renamed every binder with the one map it carried, so @big@'s
    -- @X@ came back as one of @L@'s own variables. Now @X@ is a class no
    -- language owns, so nothing can occur at it, no map substitutes for it and
    -- that binder is never renamed — the case is correct rather than said.
  , testCase "and the block installs, with nothing to say about the second class" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 twoClasses of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "X", "L"]
          ws @?= []
        (_, other) -> assertFailure (show other)
    -- **A binder scoping into another language installs and says nothing**
    -- (MS8 phase 154 lifted the refusal; 155 made the generator walk the slot).
    -- It warned in between, because a method of @L.subst-*@ was given a
    -- recursive result only for an argument of its own language and rebuilt a
    -- foreign one as written.
  , testCase "a binder free in another language's slot installs, and nothing is owed" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 foreignScope of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "X", "P", "L"]
          ws @?= []
        (_, other) -> assertFailure (show other)
    -- **A module may use another's metavariables, and the import is what makes
    -- it so** (MS11 phase 282, @~xdt8c@, his ruling of 2026-11-05). It was two
    -- module /sources/ loaded into one session, and what made @M@ reachable was
    -- that the session happened to hold the language declaring it — the hack
    -- that ruling removes. The pair on disc says it properly, and
    -- @BorrowsMetavars.thena@ writes its own @open@ rather than inheriting the
    -- one the first module wrote.
  , testCase "a module may use an imported module's metavariables" $ do
      (s0, _) <- startingSession
      (_, out, trouble) <- loadProofFile Strict s0 "test/modules/BorrowsMetavars.thena"
      assertBool (show (map (renderResponse s0) out)) (null trouble)
      [ nm | ProofLoaded nm _ _ _ <- out ]
        @?= ["test.modules.Metavars", "test.modules.BorrowsMetavars"]
  -- Written out a second time: a name DROPPED from 'builtInTags' would pass
  -- the walk in 'refused' by disappearing from it.
  , testCase "the built-in tags are exactly these two" $
      builtInTags @?= ["surface", "core"]
    -- **The MS5 form is gone with no trace** (phase 106, his ruling): in a rule
    -- file @language@ is a reserved word that nothing reads, so it is a plain
    -- syntax error and not a message about where languages went.
  , testCase "a rule file may not declare a language" $
      case snd (loadRuleTexts newSession
                  [("t.thena.rules", "rule base t where\nlanguage Tm where { var : name }\n")]) of
        RuleFileRefused _ (RuleSyntaxError _) -> pure ()
        other -> assertFailure (show other)
    -- **TWO MODULES MAY EACH DECLARE A LANGUAGE CALLED @LC@ — MS12 PHASE
    -- 313.** A module's declarations live under the name its header gives it,
    -- so these are @STLC.LC@ and @Again.LC@ and neither is the other. Before
    -- that phase every module declared at the root, the second block's name was
    -- the first block's name, and the second module was refused — which is what
    -- this test used to assert.
    --
    -- **The bare word is then an ambiguity, not a refusal of the module**, and
    -- that is the general rule: a name reachable two ways is refused where it is
    -- /written/, naming both (his ruling of 2026-10-30).
  , testCase "a second module may declare a language of the same word" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource Strict s0 stlc
      case loadProofSource Strict s1 "module Again where\n\nlanguage LC, P where\n  f -> P\n" of
        (_, ProofLoaded nm ds _ _) -> (nm, ds) @?= ("Again", ["LC"])
        (_, other) -> assertFailure (show other)
    -- **And one module may not declare it twice**, which is where the clash
    -- now lives: the second block's datatype is the first block's datatype.
  , testCase "but one module may not declare it twice" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (unlines
             [ "module Twice where", ""
             , "language LC, P where"
             , "  f -> P", ""
             , "language LC, Q where"
             , "  g -> Q" ]) of
        (_, Ran _ _ (Refused (GrammarRefused e))) ->
          e @?= GrammarError LanguageBlock "LC" NameTaken
        (_, other) -> assertFailure (show other)
  ]
  where
    -- **Under the @stlc@ fixture's own module namespace** (MS12 phase 313):
    -- the fixture is @module STLC where@.
    str = OfClass (named "STLC.x") (rootName "String") (regex "[a-z][a-zA-Z0-9']*")
    lang = OfLanguage . named . ("STLC." ++)
    installed src = do
      (s0, _) <- startingSession
      pure (grammars (machineOf (fst (loadProofSource Strict s0 src))))

-- ---------------------------------------------------------------------------

-- | A context, and a function over it to give a spelling to (MS8 phase 158,
-- §4.8, `~hwxrx`).
--
-- **@join@ is written as a projection rather than by @elim C@** — the checks
-- are about its /type/, and nothing here reduces it. @examples/@ is where the
-- real @append@ is written.
joining :: String
joining =
  unlines
    [ "module Joining where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base -> o"
    , "open Ty"
    , ""
    , "context C, G, D where"
    , "  e   -> \183"
    , "  ext -> G , x : T"
    , "open C"
    , ""
    , "join : C -> C -> C"
    , "join = \\ a b -> a"
    ]

-- | 'joining' with a @notation@ block after it.
joiningWith :: String -> String
joiningWith block = joining ++ "\n" ++ block ++ "\n"

-- | **The spelling a declared function gets, and what it does not change**
-- (MS8 phase 158, §4.8, `~hwxrx`).
--
-- The point of the phase is the last case: an index position of a judgment rule
-- is filled by parsing object notation, so a rule could only ever write what
-- the grammar's /constructors/ spell — and the paper's comma between two
-- contexts means @append@, which no constructor may be. The three before it are
-- what has to stay true for that to be worth having: the datatype the context
-- generated is untouched, its lookup relation is untouched, and the production
-- is marked 'Function' so that everything written against
-- 'constructorProductions' does not see it.
notating :: [TestTree]
notating =
  [ -- **A SLOT MAY BE AT A UNIVERSE, AND THAT IS THE THIRD MISSING WORD** (MS8
    -- phase 160, HIS ruling of 2026-10-11: the universes get notation, `ሁ40茠`,
    -- `ሁ40茡`, …, zero-based). Without it @k : Type₀ -> Ty -> Ty@ cannot be
    -- spelled at all — the word would mean nothing, become literal text, and the
    -- production would be refused for having one slot too few.
    --
    -- **Two slots at one universe need the prime**, as two slots at one language
    -- need the subscript: a name written twice is one argument (§4.3).
    testCase "a slot may be at a universe, and is filled by a type" $ do
      (s0, _) <- startingSession
      s1 <- either assertFailure pure (loadOrSay s0 universeSlots)
      -- @same@ in the fixture is `refl` over @k Ty base@, so the load asserts
      -- that the universe slot was filled with the type @Ty@ and the function
      -- ran. Here the sorts are what the checker recorded.
      let gs = grammars (machineOf s1)
      map argumentSort (concat [ gproductionArguments p
                               | g <- gs, grammarName g == named "U.Imp"
                               , p <- grammarProductions g ])
        @?= [OfUniverse 0, OfUniverse 0]
    -- **A universe slot is refused where the argument types are generated FROM
    -- the slots**, which is your describing-versus-generating line: an argument
    -- quantifying over @Type₀@ would raise the datatype's own universe.
  , testCase "a slot at a universe is refused in a language block" $ do
      (s0, _) <- startingSession
      loadOrSay s0 (unlines
        [ "module U where", ""
        , "language Ty, T, S where"
        , "  base   -> ι"
        , "  tagged -> ⟪ 𝕌₀ ⟫", "" ])
        @?= Left ("refused: in the grammar of Ty, production tagged: 𝕌₀ is a slot at Type₀, "
                    ++ "and this block generates its arguments' types from its slots — so declare "
                    ++ "the datatype and give it notation instead")
  , -- **`data` PLUS `notation` IS A `language` BLOCK, EQUIPMENT INCLUDED** (MS8
    -- phase 160, HIS ruling of 2026-10-10: *"generating nothing and declaring
    -- nothing was never a goal, just a way to talk about it"*). This is the
    -- write-up's §4 Example 1 hand-written, and the two routes are compared on
    -- the three things that could differ: the datatype, the generated family,
    -- and what a reading of the notation builds.
    testCase "a block that installs a grammar generates the substitution family" $ do
      (s0, _) <- startingSession
      byHand <- either assertFailure pure (loadOrSay s0 lamByHand)
      byBlock <- either assertFailure pure (loadOrSay s0 lamByBlock)
      -- The datatype, constructor for constructor.
      said byHand ":show Lam" @?= said byBlock ":show Lam"
      -- The family, which the hand-written route generated from the roles its
      -- @notation@ block declared.
      said byHand ":infer Lam.subst.w"
        @?= ["Lam.subst.w : Lam -> String -> Lam -> Lam"]
      said byHand ":infer Lam.subst.w" @?= said byBlock ":infer Lam.subst.w"
      -- And @same@ in the fixture is `refl`, so the load itself asserts that
      -- the notation builds exactly the hand-written constructor application.
      map gproductionKind (concat [ grammarProductions g | g <- grammars (machineOf byHand)
                                                         , grammarName g == named "Lam.Lam" ])
        -- Three constructors, and the two 'Function's are the generated
        -- substitution's own notation block (phase 159) — so the equipment
        -- arrived with its spelling, exactly as a @language@ block's does.
        -- **Two, because a class gets a bare spelling and a qualified one**
        -- (his ruling of 2026-11-10).
        @?= [Constructor, Constructor, Constructor, Function, Function]
    -- **A role belongs to the block that installs the grammar** — HIS ruling,
    -- 2026-10-11. The family is generated once, from the roles the grammar was
    -- installed with, and a block that edits a grammar cannot add to a family
    -- that is already declared.
  , testCase "a role in a block that edits a grammar is refused, and says where it belongs" $ do
      (s0, _) <- startingSession
      loadOrSay s0 (unlines
        [ "module E where", ""
        , "x : Token String"
        , "x = /[a-z]+/", ""
        , "language Ty, T, S where"
        , "  base  -> ι"
        , "  arrow -> ( T -> S )", ""
        , "open Ty"
        , "context Ctx, Γ where"
        , "  empty  -> ·"
        , "  extend -> Γ , x : T", ""
        , "open Ctx"
        , "notation Ctx where"
        , "  extend : x as occurrence -> ⟪ Γ , x , T ⟫", "" ])
        @?= Left ("refused: in the notation for Ctx, production extend: a role belongs to the "
                    ++ "block that installs the grammar, and E.Ctx's is installed already, with "
                    ++ "its substitution generated from the roles it had then")
    -- **The family is generated FROM THE GRAMMAR**, so a constructor with no
    -- production would get no method and the generated @elim@ would be one
    -- short — @D has 2 constructor(s), so this elim needs 2 method(s), not 1@,
    -- three layers from the cause. In a @language@ block this cannot arise,
    -- because there the productions are the constructors.
  , testCase "a block that installs a grammar and declares a role must spell every constructor" $ do
      (s0, _) <- startingSession
      loadOrSay s0 (unlines
        [ "module D where", ""
        , "x : Token String"
        , "x = /[a-z]+/", ""
        , "data D : Type₀ where"
        , "  { dOne : String -> D"
        , "  ; dTwo : String -> D }", ""
        , "open D"
        , "notation D where"
        , "  dOne (v : x) : v as occurrence -> ⟨ v ⟩", "" ])
        @?= Left ("refused: in the notation for D: it declares a role, so it generates D's "
                    ++ "substitution from these productions — and D.D.dTwo is a constructor of D "
                    ++ "that no production spells")
  , -- **THE HEADER FORM GIVES A DECLARED NAME ITS OWN SPELLING, AND THE NAME
    -- NEED NOT BE A GRAMMAR** (MS8 phase 160, `~hwxrx`, and it closes `~wkv37`).
    -- This is the write-up's §4 Example 2, hand-written: a datatype declared in
    -- Surface, then a @notation@ block whose header is its statement's spelling.
    -- **The block installs a grammar where there was none**, and the type's own
    -- name is its metavariable, which is what gives its slots their words.
    --
    -- **The fourth slot is the word @typing@ — a hole at @typing G M T@**, whose
    -- indices come from the declaration by position, not from the spelling. A
    -- judgment declares no metavariables, correctly, so this word resolves in a
    -- @notation@ block and nowhere else; in a @language@ block it would have no
    -- indices to be given and is `~8pk9r`.
    testCase "the header spells a hand-written type former, indexed by a judgment" $ do
      (s0, _) <- startingSession
      case loadProofSession s0 of
        Left e -> assertFailure e
        Right s1 -> do
          let gs = grammars (machineOf s1)
          v <- case [ g | g <- gs, grammarName g == named "V.Valid" ] of
                 [g] -> pure g
                 other -> assertFailure (show (length other) ++ " grammars called Valid")
          -- One production, the type former's own spelling, named after it.
          map (\p -> (gproductionName p, gproductionKind p)) (grammarProductions v)
            @?= [(named "V.Valid.Valid", TypeFormer)]
          map argumentSort (concatMap gproductionArguments (grammarProductions v))
            @?= map (OfLanguage . named . ("V." ++)) ["Ctx", "LC", "Ty", "typing"]
          -- And the constructor's target prints in it: a judgment over a
          -- judgment, spelled.
          said s1 ":show Valid" !! 1
            @?= "  { validAny : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing`${G} ⊢ ${M} : ${T}`) -> Valid`⊢ ${G} , ${M} , ${T} by ${d} valid` }"
  , -- **A SUFFIXED WORD RESOLVES TO THE METAVARIABLE IT IS A SUFFIX OF** (MS8
    -- phase 160, HIS ruling of 2026-10-10). A type declared outside a block has
    -- no metavariables to alias, so its slots are its own name with subscripts
    -- — *"subscripts are enough"* — and the rule already existed for a rule's
    -- /text/, so this is the same rule one layer down.
    --
    -- **Before this both words were terminals**, so the production had no slots
    -- at all and @twin@ would have been @twin : C@.
    testCase "a slot may be a metavariable's name with a suffix" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (joiningWith "notation C where\n  join a b -> ⟦ a , b ⟧") of
        (s1, ProofLoaded {}) -> do
          let gs = grammars (machineOf s1)
          c <- case [ g | g <- gs, grammarName g == named "Joining.C" ] of
                 [g] -> pure g
                 other -> assertFailure (show (length other) ++ " grammars called C")
          -- Two parameters, both at @C@ because that is what @join@ takes.
          map gproductionArguments [ p | p <- grammarProductions c
                                       , gproductionName p == named "Joining.join" ]
            @?= [[ Argument "a" (OfLanguage (named "Joining.C")) Plain
                 , Argument "b" (OfLanguage (named "Joining.C")) Plain ]]
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
  , -- **A refusal that quotes a type may not print a nameless argument.** The
    -- stand-in 'functionShape' peels a telescope with used to be a global with
    -- an empty name, so a result type mentioning an earlier argument printed
    -- nothing where that argument was: @nil@'s @List {\8467} A@ reached the refusal
    -- as @nil returns List {\8467} , not a Ctx@. The prelude's @nil@ is the only
    -- shipped function whose result mentions its own argument, which is why the
    -- case went unseen until a notation block named it.
    testCase "a result that mentions an argument names it" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (joiningWith "notation C where\n  List.nil a b -> a \8746 b") of
        (_, Ran _ _ (Refused (GrammarRefused
             (GrammarError _ _ (InProduction "List.nil" (FunctionResult r)))))) -> case r of
          Canonical _ _ [a] -> a @?= Global (rootName "\8249A\8250") []
          other             -> assertFailure (show other)
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
  , testCase "the block installs, declares nothing, and adds one production" $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 (joiningWith "notation C where\n  join a b -> a \8746 b") of
        (s1, ProofLoaded _ names _ _) -> do
          -- @join@ is the definition's own name; the block declares nothing.
          names @?= ["x", "Ty", "C", "join"]
          let gs = grammars (machineOf s1)
          c <- case [ g | g <- gs, grammarName g == named "Joining.C" ] of
                 [g] -> pure g
                 other -> assertFailure (show (length other) ++ " grammars called C")
          map gproductionName (grammarProductions c)
            @?= [named "Joining.C.e", named "Joining.C.ext", named "Joining.join"]
          map gproductionKind (grammarProductions c)
            @?= [Constructor, Constructor, Function]
          -- **The datatype is the one it was**, which is the whole reason this
          -- is not the refused joining constructor: @C@ stays a list.
          map gproductionName (constructorProductions c)
            @?= map named ["Joining.C.e", "Joining.C.ext"]
          -- Plain arguments, in the parameter list's order, at the types the
          -- declaration gives them (MS8 phase 171).
          map gproductionArguments [ p | p <- grammarProductions c
                                       , gproductionName p == named "Joining.join" ]
            @?= [[ Argument "a" (OfLanguage (named "Joining.C")) Plain
                 , Argument "b" (OfLanguage (named "Joining.C")) Plain ]]
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
    -- **The term is written in the same module as the block** (MS11 phase 282,
    -- @~xdt8c@). It was a second module loaded into the session the first one
    -- left, which his ruling of 2026-11-05 no longer lets resolve: a module
    -- reaches what it imports and what it declares, and nothing here is about
    -- modules — it is about a notation elaborating to its function.
  , testCase "and a term is written in it, and reduces to the constructors" $ do
      (s0, _) <- startingSession
      -- @join a b = a@, so the right-hand context is dropped: the notation
      -- elaborated to the function and the function ran.
      case loadProofSource Strict s0
             (joiningWith
                ("notation C where\n  join a b -> a \8746 b\n\n"
                   ++ "j : Eq C C`\183 , x : o \8746 \183` (ext e \"x\" base)\n"
                   ++ "j = refl C (ext e \"x\" base)")) of
        (_, ProofLoaded {}) -> pure ()
        (s2, other) -> assertFailure (unlines (renderResponse s2 other))
    -- **Nothing the context generated moves** (MS8 phase 158): the datatype and
    -- the lookup relation were generated when the @context@ block loaded, and a
    -- function production is not a constructor, so neither could change. Pinned
    -- by loading the same module with and without the block and comparing the
    -- names declared.
  , testCase "the names a module declares are the same with the block and without" $ do
      (s0, _) <- startingSession
      let declared src = case loadProofSource Strict s0 src of
            (_, ProofLoaded _ ns _ _) -> Right ns
            (s1, other) -> Left (unlines (renderResponse s1 other))
      without <- pure (declared joining)
      with <- pure (declared (joiningWith "notation C where\n  join a b -> a \8746 b"))
      with @?= without
    -- **The done-when of the phase.** @S-split@ is F-sub's type-substitution
    -- lemma in miniature: its premise's index is two contexts joined, which is
    -- what the paper writes and what no grammar could spell until now. The
    -- refusal it replaces was measured on 2026-10-07:
    -- @its premises `Γ , X <: T , Δ ⊢ T <: S` do not parse: unexpected 'Δ'@.
  , testCase "a judgment rule writes it in an index position" $ do
      (s0, _) <- startingSession
      -- One module, for the reason the test above it gives.
      case loadProofSource Strict s0
             (joiningWith
                ("notation C where\n  join a b -> a \8746 b\n\n" ++ unlines
                   [ "judgment sub = G \8866 T <: S where"
                   , "  S-refl:"
                   , "    ----------"
                   , "    G \8866 T <: T"
                   , ""
                   , "  S-split:"
                   , "    G \8746 D \8866 T <: S"
                   , "    -----------------"
                   , "    G \8866 T <: S"
                   ])) of
        (_, ProofLoaded _ names _ _) -> names @?= ["x", "Ty", "C", "join", "sub"]
        (s2, other) -> assertFailure (unlines (renderResponse s2 other))
  ]

-- ---------------------------------------------------------------------------

-- | **Which classes a grammar reaches** (MS8 phase 154, `~5k3mg`): the classes
-- its own roles name, and everything the grammars in its slots reach. The
-- generator of phase 155 indexes a substitution by this set, so what is pinned
-- here is the set and its order — this grammar's own first, then first
-- encountered.
--
-- **The cyclic case is the whole reason it is a fixpoint and not a walk in
-- declaration order — his ruling, 2026-10-04.** No source can declare two
-- mutually dependent grammars today (`~m5dvd`), so the graph is built here by
-- hand: a walk that trusted the order, or one with no visited set, would not
-- come back from it.
reaching :: [TestTree]
reaching =
  [ testCase "a class a role of the grammar itself names" $ do
      gs <- installedIn twoClasses
      map (classesReached gs) [grammarCalled gs "Two.L"]
        @?= [[named "Two.x", named "Two.X"]]
  , testCase "and nothing for a grammar whose roles name none" $ do
      gs <- installedIn stlc
      classesReached gs (grammarCalled gs "STLC.Ty") @?= []
  , testCase "a class reached through two slots, named by neither grammar between" $ do
      gs <- installedIn chained
      map (map nameString . classesReached gs . grammarCalled gs)
          (map ("Chain." ++) ["P", "Q", "L"])
        @?= [["Chain.x"], ["Chain.x"], ["Chain.x"]]
      map (map nameString . classesNamed . grammarCalled gs)
          (map ("Chain." ++) ["P", "Q", "L"])
        @?= [["Chain.x"], [], []]
  , testCase "and two grammars that reach each other terminate at the union" $
      map (map nameString . classesReached cyclic) cyclic
        @?= [["u", "v"], ["v", "u"]]
  ]
  where
    -- Loudly, because a module that did not load leaves no grammars at all and
    -- every assertion below would then be about the empty list.
    installedIn src = do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 src of
        (s1, ProofLoaded {}) -> pure (grammars (machineOf s1))
        (s1, other) -> do
          _ <- assertFailure (unlines (renderResponse s1 other))
          pure []
    -- **Under the fixture's own module namespace** (MS12 phase 313): a
    -- module's languages live under the name its header gives it, so the
    -- grammar a block in @module M where@ installed is @M.L@.
    grammarCalled gs n = case [ g | g <- gs, grammarName g == named n ] of
      g : _ -> g
      [] -> error ("no grammar called " ++ n)
    nameString = nameDotted

-- | Two grammars, each with a slot of the other: @A@ reads @u@ and @B@ reads
-- @v@, so each reaches both. Written out because no module can declare it.
cyclic :: [Grammar]
cyclic = [one "A" "u" "B", one "B" "v" "A"]
  where
    one l cls other =
      Grammar LanguageBlock (rootName l) [l, l ++ "'"]
        [ GProduction (rootName (l ++ "var")) [Slot cls (klass cls) []]
            [Argument cls (klass cls) (Occurrence (rootName cls))] Constructor
        , GProduction (rootName (l ++ "in")) [Slot other (OfLanguage (rootName other)) []]
            [Argument other (OfLanguage (rootName other)) Plain] Constructor
        ]
    klass cls = OfClass (rootName cls) (rootName "String") (regex "[a-z]+")

-- ---------------------------------------------------------------------------

-- | One module per refusal, with the value each must refuse with. Every module
-- has the classes @x : Token String@ and @n : Token Int@ above its block.
refused :: [((String, String), GrammarError)]
refused =
  [ inProduction "a binding form's head is not a metavariable"
      "language L, M where\n  bad -> q[x] M" "bad" (NotAMetavariable "q")
  , inProduction "a binder that is not a String"
      "language L, M where\n  num : n as binder -> n M[n]" "num" (BinderNotString "n" int)
  , inProduction "an occurrence that is not a String"
      "language L, M where\n  num : n as occurrence -> n" "num" (OccurrenceNotString "n" int)
  , inProduction "a bracket naming what is not an argument"
      "language L, M where\n  f -> ( M[x] )" "f" (NotAnArgument "x")
  , inProduction "a bracket naming an occurrence"
      "language L, M where\n  f : x as occurrence -> x M[x]" "f" (OccurrenceBinds "x")
  , inProduction "a bracket naming what the declared binders do not"
      "language L, M where\n  f : { x } as binders -> x n M[n]" "f" (NotADeclaredBinder "n")
  , inProduction "metadata naming what is not written"
      "language L, M where\n  f : x as occurrence -> M" "f" (NotAnArgument "x")
  , inProduction "one argument written with two scopes"
      "language L, M where\n  f -> M M[x] x" "f" (ScopesDiffer "M")
  , inProduction "a production with no items"
      "language L, M where\n  f ->" "f" NoItems
  , block "a metavariable named twice" "language L, M, M where\n  f -> M" (MetavariableRepeated "M")
  , block "a metavariable that is already a token class" "language L, x where\n  f -> x" (MetavariableTaken "x")
  , block "a language named like something declared" "language x where\n  f -> a" NameTaken
  , block "a constructor named like something declared" "language L, M where\n  x -> a" (ConstructorTaken "x")
  , block "two productions of one name" "language L, M where\n  f -> a\n  f -> b" (ConstructorTaken "f")
  , contextBlock "a context without one empty and one extension production"
      "context C, G where\n  e -> \183\n  f -> G G" ContextShape
    -- MS7 phase 127, his ruling of 2026-09-28: the placeholder's glyph is
    -- reserved, and a grammar that could write it or read it is refused so that
    -- one glyph never means two things in one buffer.
  , inProduction "a terminal that writes the placeholder"
      "language L, M where\n  f -> \9608 M" "f" (ReservedTerminal "\9608")
  , inProduction "a terminal that merely contains it"
      "language L, M where\n  f -> a\9608b M" "f" (ReservedTerminal "a\9608b")
    -- **The narrowed refusal** (MS8 phase 154): @P@ has no occurrence at all, so
    -- nothing inside an @R@ can ever be at the class @f@'s binder binds at, and
    -- there is nothing there for substitution to do.
  , ( ( "a binder free in a language that reaches no such class"
      , "module M where\n\nx : Token String\nx = /[a-z]+/\n\n"
          ++ "language P, R where\n  base -> o\nopen P\n\n"
          ++ "language L, M where\n  var : x as occurrence -> x\n"
          ++ "  f : x as binder -> ( let x = M in R[x] )\n"
      )
    , GrammarError LanguageBlock "L"
        (InProduction "M.L.f" (ScopeElsewhere "R" (named "M.P") (named "M.x")))
    )
  , ( ( "a token class that would read it"
      , "module M where\n\nany : Token String\nany = /./\n\nlanguage L, M where\n  f -> any M\n"
      )
    , GrammarError LanguageBlock "L" (InProduction "f" (ReservedClass "any"))
    )
  ]
    -- §4.8's own refusals (MS8 phase 158, `~hwxrx`). All but the first two are
    -- about one production, and they are the checks a function production needs
    -- that a constructor production does not: a definition of that name exists
    -- and takes exactly what the notation's slots hand it.
    ++ [ notationBlock "a block naming no installed grammar"
           "Nope" "notation Nope where\n  join a b -> a \8746 b" NoSuchGrammar
       , notationBlock "a block declaring a metavariable of its own"
           "C" "notation C, Z where\n  join a b -> a \8746 b" (NotationMetavars ["Z"])
       , inNotation "a production naming nothing declared"
           "notation C where\n  nosuch a b -> a \8746 b" "nosuch" NotADeclaredFunction
         -- The check spans every installed grammar, not this one: a production
         -- name is unique across all of them, which 'productionBody' relies on.
       , inNotation "a production naming another grammar's constructor"
           "notation C where\n  Ty.base a b -> a \8746 b" "Ty.base" FunctionHasNotation
       , inNotation "a production naming one the grammar already has"
           "notation C where\n  ext a b -> a \8746 b" "ext" FunctionHasNotation
       , inNotation "more slots than the function takes"
           "notation C where\n  join a b c -> a \8746 b \8746 c" "join" (FunctionArity 2 3)
         -- **The three MS8 phase 171 adds**, and the one it retires. A slot's
         -- sort is read off the declaration now rather than checked against it,
         -- so @FunctionSlot@ — a slot at a sort the function does not take
         -- there — cannot arise: there is nothing left for the two to disagree
         -- about. What can go wrong is the parameter list itself.
       , inNotation "the same name for two of the arguments"
           "notation C where\n  join a a -> a \8746 a" "join" (ParamRepeated "a")
       , inNotation "a parameter the notation never writes"
           "notation C where\n  join a b -> a \8746 a" "join" (ParamUnspelled "b")
       , inNotation "a parameter naming an argument no notation reads"
           "lift : C -> String -> C\nlift = \\ a s -> a\n\nnotation C where\n  lift a s -> a \8853 s"
           "lift" (ParamNotReadable "s" (Global (rootName "String") []))
       , inNotation "a function that does not return the grammar's datatype"
           "dom : C -> C -> Ty\ndom = \\ a b -> Ty.base\n\nnotation C where\n  dom p q -> p \8746 q"
           "dom" (FunctionResult (datatype "Joining.Ty"))
       , inNotation "a production writing a binding form"
           "notation C where\n  join a b -> a \8746 b[x]" "join" (FunctionBinds "b")
       , inNotation "a production with metadata"
           "notation C where\n  join a b : x as occurrence -> a \8746 b" "join" FunctionMetadata
         -- **A role belongs to the block that installs the grammar** (HIS
         -- ruling, 2026-10-11; phase 160). @C@ is installed by the @context@
         -- block above, so a later block may add spellings and not roles —
         -- the substitution family is already declared and a second one
         -- cannot be declared over it.
       , inNotation "a role in a block that only adds spellings"
           "notation C where\n  ext a b : a as occurrence -> a \8746 b" "ext"
           (RolesAfterTheGrammar (named "Joining.C"))
       ]
    -- **A built-in tag may not name a language** (moved here from MS5's
    -- grammars at phase 106). A rule base reads an installed grammar's tag
    -- first, so @language core@ took every later @core`…`@ for its own. It walks
    -- 'builtInTags' so that a third tag cannot be added to the list alone.
    ++ [ block ("a language named like the built-in tag " ++ t)
               ("language " ++ t ++ ", M where\n  f -> a") BuiltInTag
       | t <- builtInTags ]
  where
    -- **The class is under the fixture's module namespace** (MS12 phase 313):
    -- every @klass@ fixture here is @module M where@.
    int = OfClass (named "M.n") (rootName "Int") (regex "[0-9]+")
    wrap body =
      "module M where\n\nx : Token String\nx = /[a-z]+/\n\nn : Token Int\nn = /[0-9]+/\n\n" ++ body ++ "\n"
    inProduction title body p why = ((title, wrap body), GrammarError LanguageBlock "L" (InProduction p why))
    block title body problem = ((title, wrap body), GrammarError LanguageBlock (nameOf body) problem)
    contextBlock title body problem = ((title, wrap body), GrammarError ContextBlock "C" problem)
    nameOf body = takeWhile (`notElem` ", ") (drop (length "language ") body)
    -- MS8 phase 158. The block goes after 'joining', which declares the context
    -- @C@ and the function @join@ over it; a case that needs another definition
    -- writes it in @body@ above its own block.
    notationBlock title g body problem =
      ((title, joiningWith body), GrammarError NotationBlock g problem)
    inNotation title body p why = notationBlock title "C" body (InProduction p why)

refusals :: [TestTree]
refusals =
  [ testCase title $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 src of
        (_, Ran _ _ (Refused (GrammarRefused e))) -> e @?= want
        (_, other) -> assertFailure (show other)
  | ((title, src), want) <- refused
  ]
  ++
  [ testCase ("unreadable: " ++ title) $ do
      (s0, _) <- startingSession
      case loadProofSource Strict s0 src of
        (_, Failed (BlockUnreadable e)) -> e @?= want
        (_, other) -> assertFailure (show other)
  | ((title, src), want) <-
      zip unreadable
        [ HeaderWithoutWhere 3
        , MetadataMalformed 4 "x as whatever"
        , ProductionWithoutArrow 4
        , BindingMalformed 4 ""
        , IndentedLess 5
        ]
  ]

-- | A generated datatype as a type: what a saturated former reduces to, which
-- is what a §4.8 refusal carries so that its message can show the author the
-- type their own signature says (MS8 phase 160).
-- **A name may carry its module's namespace** (MS12 phase 313), so this reads
-- the whole written name and makes the datatype's own namespace its last step:
-- @Joining.Ty@ is the type former @Joining.Ty.Ty@.
datatype :: String -> Core
datatype n = Canonical (asDeclared (named n)) [] []
  where asDeclared (GlobalName ps w) = GlobalName (ps ++ [w]) w

regex :: String -> Regex
regex = either (error . show) id . parseRegex
