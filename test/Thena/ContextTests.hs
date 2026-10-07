-- | A context's lookup relation (MS6 phase 107; @ms6\/SPEC.md@ §5.3).
--
-- **The proofs are the load-bearing tests.** A lookup at the top of a context
-- is @extend-here@; one under a later binding of a different name is @extend-there-extend@,
-- whose @ne@ is proved with no axiom from @eqString@ alone, which is what
-- §2.1 promised and what phase 109's proofs will have to do. And a lookup
-- that would skip a binding of the /same/ name is refused, because @ne@ has no
-- proof — that is the shadowing §5.3 generates @ne@ for.
--
-- Around them: what is declared, the notation read and printed back through
-- the same grammar machinery as any object term, where the separator goes when
-- the context slot is last, and what a context must have to be given a lookup.
module Thena.ContextTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver
  ( Response (..)
  , Session
  , machineOf
  , command
  , loadProofSource
  )
import Thena.Engine (Machine (..))
import Thena.Language.Build (buildTerm, printRegion)
import Thena.Language.Earley (parse, pieces)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar (earleyRules)
import Thena.Files (startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore, renderResponse)

tests :: TestTree
tests =
  testGroup
    "a context's lookup relation"
    [ testGroup "what is declared (§5.3)" declared
    , testGroup "the notation is a grammar" notation
    , testGroup "proofs of lookups" proofs
    , testGroup "two kinds of binding (MS8 phase 156)" twoKinds
    , testGroup "substitution through a context (MS8 phase 157)" substituted
    , testGroup "what a context needs" refused
    ]

-- ---------------------------------------------------------------------------

header :: [String]
header =
  [ "module Ctx where"
  , ""
  , "x : Token String"
  , "x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "language Ty, T, S where"
  , "  base  -> \953"
  , "  arrow -> ( T -> S )"
  , ""
  , "context Ctx, \915 where"
  , "  empty  -> \183"
  , "  extend -> \915 , x : T"
  , ""
  ]

-- | **F-sub's Γ** (MS8 phase 156, `~23rg2`): two extension productions, one per
-- kind of binding. Until this phase the block was refused outright — *"a context
-- needs one empty and one extension production"* — so the context of POPLMark
-- part 2A could not be written down at all, and nothing about it could be stated
-- let alone proved.
fsubHeader :: [String]
fsubHeader =
  [ "module Fsub where"
  , ""
  , "x : Token String"
  , "x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "X : Token String"
  , "X = /[A-Z][a-zA-Z0-9']*/"
  , ""
  , "language Ty, T, S where"
  , "  tvar : X as occurrence -> X"
  , "  top                    -> \8868"
  , "  fun                    -> ( T -> S )"
  , ""
  , "context Ctx, \915 where"
  , "  empty  -> \183"
  , "  bindTm -> \915 , x : T"
  , "  bindTy -> \915 , X <: T"
  , ""
  ]

twoKinds :: [TestTree]
twoKinds =
  [ testCase "a context with two extensions gets a lookup relation for each" $ do
      s <- loaded fsubHeader
      map (take 1 . said s) [":show bindTm-in", ":show bindTy-in"] @?=
        [ ["data bindTm-in : String -> Ty -> Ctx -> Type\8320 where"]
        , ["data bindTy-in : String -> Ty -> Ctx -> Type\8320 where"]
        ]
    -- **Each notation is its own extension's**, by the recipe §5.3 already had:
    -- the entry with the context slot and its separator taken out, then @\8712@.
    -- So F-sub reads both of its lookups the way the paper writes them.
  , testCase "and a notation each, read by the same parser as any object term" $ do
      s <- loaded fsubHeader
      said s ":infer bindTm-in`x : \8868 \8712 \183`" @?= ["bindTm-in`x : \8868 \8712 \183` : Type\8320"]
      said s ":infer bindTy-in`X <: \8868 \8712 \183`" @?= ["bindTy-in`X <: \8868 \8712 \183` : Type\8320"]
    -- **The `ne` premise is generated only where the stepped-over extension
    -- reads names of the SAME class** — his settlement of 2026-10-04, and the
    -- reason is that shadowing is within a namespace. So looking a term variable
    -- up past a type binding takes no inequality at all, and the proof below is
    -- the whole of it: no `ne` argument is written.
  , testCase "a term lookup steps over a type binding with nothing to prove" $ do
      _ <- loaded (fsubHeader ++
        [ "pastType : bindTm-in`x : \8868 \8712 \183 , x : \8868 , X <: \8868`"
        , "pastType = bindTm-there-bindTy (bindTm empty \"x\" top) \"x\" top \"X\" top"
        , "             (bindTm-here empty \"x\" top)" ])
      pure ()
  , testCase "and a type lookup over a term binding the same way" $ do
      _ <- loaded (fsubHeader ++
        [ "pastTerm : bindTy-in`X <: \8868 \8712 \183 , X <: \8868 , x : \8868`"
        , "pastTerm = bindTy-there-bindTm (bindTy empty \"X\" top) \"X\" top \"x\" top"
        , "             (bindTy-here empty \"X\" top)" ])
      pure ()
    -- **Shadowing within one namespace is unchanged**: stepping a term lookup
    -- over another term binding still needs the inequality, so a binding hidden
    -- by a later one of the same name is still unreachable.
  , testCase "stepping over a binding of its own kind still needs the inequality" $ do
      r <- load (fsubHeader ++
        [ "shadowed : bindTm-in`x : \8868 \8712 \183 , x : \8868 , x : \8868`"
        , "shadowed = bindTm-there-bindTm (bindTm empty \"x\" top) \"x\" top \"x\" top"
        , "             (bindTm-here empty \"x\" top)" ])
      either (const (pure ())) (const (assertFailure "it was reached with no ne")) r
  ]

substituted :: [TestTree]
substituted =
  [ -- **A context gets a substitution for every class it reaches** (MS8 phase
    -- 157, `~mnr39`): F-sub's Γ holds @Ty@ slots and @Ty@ owns the type class,
    -- so @Ctx-subst-X@ exists and is the @[X↦P]Δ@ of the type-substitution
    -- lemma. **No @Ctx-fresh-X@**, because a context owns no class — minting a
    -- name belongs to the language whose notation can write one.
    testCase "a context reaching a class gets a substitution into its owner" $ do
      s <- loaded fsubHeader
      said s ":infer Ctx-subst-X" @?= ["Ctx-subst-X : Ctx -> String -> Ty -> Ctx"]
      said s ":infer Ctx-fresh-X" @?= ["stuck: not in scope: Ctx-fresh-X"]
    -- **The load is the assertion.** @through@ does not type-check unless the
    -- fold recurses through the context and substitutes in each entry's type,
    -- and @freeOf@ unless the free type variables of a context are its entries'.
  , testCase "it folds through the context, and the context's own names are left alone" $ do
      _ <- loaded (fsubHeader ++
        [ "through : Eq Ctx (Ctx-subst-X (bindTm (bindTy empty \"X\" top) \"y\" (tvar \"X\")) \"X\" top)"
        , "                 (bindTm (bindTy empty \"X\" top) \"y\" top)"
        , "through = refl Ctx (bindTm (bindTy empty \"X\" top) \"y\" top)"
        , ""
        , "freeOf : Eq (List String) (Ctx-fv-X (bindTm empty \"y\" (tvar \"Z\")))"
        , "            (cons String \"Z\" (nil String))"
        , "freeOf = refl (List String) (cons String \"Z\" (nil String))" ])
      pure ()
    -- **And a rule may write it**, which is what `~mnr39` is for: F-sub's
    -- type-substitution lemma is stated @Γ, [X↦P]Δ ⊢ …@, and §6.3's notation
    -- now reaches a context because the generator's rule for one is the same as
    -- for a language.
  , testCase "a rule may substitute through a context in its own notation" $ do
      s <- loaded (fsubHeader ++
        [ "judgment sub = \915 \8866 T <: S where", ""
        , "  S-refl: ------------"
        , "          \915 \8866 T <: T", ""
        , "  S-narrow: \915[X -> T] \8866 S <: S'"
        , "            --------------------"
        , "            \915 \8866 S <: S'" ])
      said s ":infer S-narrow" @?=
        [ "S-narrow : \8704 (\915 : Ctx) (X : String) (T : Ty) (S : Ty) (S' : Ty)"
            ++ " -> sub`${Ctx-subst-X \915 X T} \8866 ${S} <: ${S'}` -> sub`${\915} \8866 ${S} <: ${S'}`" ]
    -- **A context whose entries can hold no name gets nothing**, which is
    -- STLC's: its @Ty@ has no variable production, so there is nothing in a Γ
    -- to substitute for.
  , testCase "and a context that reaches no class gets none" $ do
      s <- loaded header
      map (said s) [":infer Ctx-subst-all", ":infer Ctx-fv-x"] @?=
        [ ["stuck: not in scope: Ctx-subst-all"]
        , ["stuck: not in scope: Ctx-fv-x"] ]
  ]

-- | @x ≠ y@, from @eqString@ and nothing else: the motive sends a string to
-- @Unit@ when it is @"x"@ and to @Empty@ otherwise, and @Eq@'s eliminator
-- carries @unit@ from one side to the other.
xNotY :: [String]
xNotY =
  [ "xNotY : Eq String \"x\" \"y\" -> Empty"
  , "xNotY = \\ q ->"
  , "  elim Eq (String)"
  , "    (\\ a b r -> elim Comparison () (\\ c -> Type\8320) ((Unit) (Empty)) () (eqString \"x\" a)"
  , "                -> elim Comparison () (\\ c -> Type\8320) ((Unit) (Empty)) () (eqString \"x\" b))"
  , "    ((\\ a d -> d))"
  , "    (\"x\" \"y\") q unit"
  , ""
  ]

-- | Load a module and answer with the session, or the refusal's last line.
load :: [String] -> IO (Either String Session)
load body = do
  (s0, _) <- startingSession
  pure $ case loadProofSource s0 (unlines body) of
    (s1, ProofLoaded {}) -> Right s1
    (s1, other) -> Left (last (renderResponse s1 other))

loaded :: [String] -> IO Session
loaded body = load body >>= either assertFailure pure

said :: Session -> String -> [String]
said s line = let (s', r) = command s line in renderResponse s' r

-- ---------------------------------------------------------------------------

declared :: [TestTree]
declared =
  [ testCase ":show prints the relation and both constructors" $ do
      s <- loaded header
      said s ":show extend-in" @?=
        [ "data extend-in : String -> Ty -> Ctx -> Type₀ where"
        , "  { extend-here : ∀ (Γ : Ctx) (x : String) (T : Ty) -> extend-in`${x} : ${T} ∈ ${Γ} , ${x} : ${T}`"
        , "  ; extend-there-extend : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty)"
            ++ " -> (Eq {0} String x x' -> Empty {0})"
            ++ " -> extend-in`${x} : ${T} ∈ ${Γ}` -> extend-in`${x} : ${T} ∈ ${Γ} , ${x'} : ${T'}` }"
        ]
  ]

notation :: [TestTree]
notation =
  [ testCase "the notation is read and built as the relation applied" $ do
      s <- loaded header
      let gs = grammars (machineOf s)
      case parse (earleyRules gs) (Earley.StartAt "extend-in") (pieces "x : \953 \8712 \183 , y : \953") of
        Left why -> assertFailure (show why)
        Right tree -> buildTerm gs tree @?= Right
          (apps "extend-in" [str "x", con "base", apps "extend" [con "empty", str "y", con "base"]])
  , testCase "and prints back as the text it was read from" $ do
      s <- loaded header
      let m = machineOf s
      printRegion (grammars m) (renderCore (Rendering [] 0) [])
          (apps "extend-in" [str "x", con "base", apps "extend" [con "empty", str "x", con "base"]])
        @?= Just "x : \953 \8712 \183 , x : \953"
  , testCase "a lookup literal is a type" $ do
      s <- loaded header
      said s ":infer extend-in`x : \953 \8712 \183`" @?= ["extend-in`x : \953 \8712 \183` : Type\8320"]
    -- **The separator is the terminals between the context slot and its
    -- neighbouring slot** — the next one, or the previous when it is last.
  , testCase "a context written with its slot last loses the separator before it" $ do
      s <- loaded
        [ "module Last where", "", "x : Token String", "x = /[a-z]+/", ""
        , "language Ty, T where", "  base -> \953", ""
        , "context D, \916 where", "  none -> \949", "  push -> x : T ; \916", "" ]
      said s ":show push-in" !! 0 @?= "data push-in : String -> Ty -> D -> Type\8320 where"
      case parse (earleyRules (grammars (machineOf s))) (Earley.StartAt "push-in")
                 (pieces "x : \953 \8712 x : \953 ; \949") of
        Left why -> assertFailure (show why)
        Right _ -> pure ()
  ]
  where
    str = Primitive . LString
    con n = Global (GlobalName n) []
    apps f = foldl App (con f)

proofs :: [TestTree]
proofs =
  [ testCase "a lookup at the top is extend-here" $ do
      _ <- loaded (header ++
        [ "found : extend-in`x : \953 \8712 \183, x : \953`"
        , "found = extend-here empty \"x\" base" ])
      pure ()
  , testCase "one under a later binding of another name is extend-there-extend, with ne proved" $ do
      _ <- loaded (header ++ xNotY ++
        [ "under : extend-in`x : \953 \8712 \183, x : \953, y : \953`"
        , "under = extend-there-extend (extend empty \"x\" base) \"x\" base \"y\" base xNotY (extend-here empty \"x\" base)" ])
      pure ()
  , testCase "extend-here does not reach under a later binding" $ do
      r <- load (header ++
        [ "wrong : extend-in`x : \953 \8712 \183, x : \953, y : \953`"
        , "wrong = extend-here (extend empty \"x\" base) \"x\" base" ])
      either (const (pure ())) (const (assertFailure "extend-here was accepted under y")) r
    -- The shadowing: to reach the earlier x past a later x, ne must prove
    -- x ≠ x, and xNotY is a proof of something else.
  , testCase "and extend-there-extend cannot skip a binding of the same name" $ do
      r <- load (header ++ xNotY ++
        [ "shadowed : extend-in`x : \953 \8712 \183, x : \953, x : ( \953 -> \953 )`"
        , "shadowed = extend-there-extend (extend empty \"x\" base) \"x\" base \"x\" (arrow base base) xNotY (extend-here empty \"x\" base)" ])
      either (const (pure ())) (const (assertFailure "a shadowed binding was reached")) r
    -- And what it would take is exactly a refutation of refl: reaching the
    -- earlier x needs Eq String "x" "x" -> Empty, which applied to refl is
    -- Empty. So the shadowed binding cannot be reached by any term.
  , testCase "what it would take is a proof that x is not x" $ do
      _ <- loaded (header ++
        [ "needs : (Eq String \"x\" \"x\" -> Empty) -> extend-in`x : \953 \8712 \183, x : \953, x : ( \953 -> \953 )`"
        , "needs = \\ ne -> extend-there-extend (extend empty \"x\" base) \"x\" base \"x\" (arrow base base) ne (extend-here empty \"x\" base)"
        , ""
        , "absurdly : (Eq String \"x\" \"x\" -> Empty) -> Empty"
        , "absurdly = \\ ne -> ne (refl String \"x\")" ])
      pure ()
  ]

refused :: [TestTree]
refused =
  [ refusal "an extension with no name"
      ["context C, G where", "  e -> \183", "  f -> G , T"]
      "refused: in the context C: its extension f needs exactly one name to look up, and it has none"
  , refusal "an extension with two"
      ["y : Token String", "y = /[a-z]+/", "", "context C, G where", "  e -> \183", "  f -> G , x = y : T"]
      "refused: in the context C: its extension f needs exactly one name to look up, and it has x, y"
  , refusal "a lookup name already declared"
      ["f-here : Ty", "f-here = base", "", "context C, G where", "  e -> \183", "  f -> G , x : T"]
      "refused: C's lookup f-here is already declared"
    -- **A production with TWO of its own slots is still refused** (MS8 phase
    -- 156): a lookup relation steps over one binding, and there is nothing for
    -- it to read in a form that joins two contexts. More than one *extension* is
    -- what stopped being refused.
  , refusal "a production that joins two contexts"
      ["context C, G where", "  e -> \183", "  f -> G , x : T", "  j -> G ; G"]
      "refused: in the context C: a context needs one production with no context slot and at least one with exactly one"
  , refusal "a context with no extension at all"
      ["context C, G where", "  e -> \183", "  n -> \183 \183"]
      "refused: in the context C: a context needs one production with no context slot and at least one with exactly one"
  ]
  where
    refusal what body want = testCase what $ do
      r <- load (take 9 header ++ body)
      either (@?= want) (const (assertFailure "it loaded")) r
