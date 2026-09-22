-- | @judgment@ blocks, both tiers (MS6 phase 108; @ms6\/SPEC.md@ §6).
--
-- **The generated constructors are the load-bearing tests**, compared whole
-- through @:show@: quantification in order of first appearance (§6.2), the
-- premises after it in written order, the conclusion as the notation applied,
-- and a substitution as the functions of §4.7 (§6.3). The derivations below
-- them check that what came out is the relation it should be — the kernel
-- accepts a typing derivation and a step whose right-hand side it computes,
-- and refuses the wrong one.
--
-- Around them: how premises are told apart when only whitespace separates
-- them, what a name in a rule may be, the annotated tier, and the refusals.
module Thena.JudgmentTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (entryIdent)
import Thena.Core.Term (GlobalName (..), Ident (..))
import Thena.Driver (Response (..), Session (..), command, loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Global.Env (ConstructorDefinition (..), InductiveDefinition (..), lookupInductive)
import Thena.Language.Reader (Block (..), Production (..), RawRule (..), ReadError (..), readBlock)
import Thena.Repl (renderResponse, startingSession)
import Thena.Syntax.Lexer (BlockKind (..))

tests :: TestTree
tests =
  testGroup
    "judgments"
    [ testGroup "reading a block (§6.1, §6.4)" reading
    , testGroup "what a rule generates (§6.2, §6.5)" generated
    , testGroup "premises" premises
    , testGroup "substitution in a rule (§6.3)" substitution
    , testGroup "the annotated tier (§6.4)" annotated
    , testGroup "derivations" derivations
    , testGroup "refusals" refused
    ]

-- ---------------------------------------------------------------------------

-- | STLC's syntax and contexts, as examples 01 and 02 declare them.
header :: [String]
header =
  [ "module J where"
  , ""
  , "x : Token String"
  , "x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "language Ty, T, S where"
  , "  base  -> ι"
  , "  arrow -> ( T -> S )"
  , ""
  , "language LC, M, N, E where"
  , "  var : x as occurrence -> x"
  , "  abs : x as binder     -> ( λ x : T . E[x] )"
  , "  app                   -> ( M N )"
  , ""
  , "context Ctx, Γ where"
  , "  empty  -> ·"
  , "  extend -> Γ , x : T"
  , ""
  ]

typing :: [String]
typing =
  [ "judgment typing = Γ ⊢ M : T where"
  , ""
  , "  T-var:  x : T ∈ Γ"
  , "          -----------"
  , "          Γ ⊢ x : T"
  , ""
  , "  T-abs:  Γ , x : S ⊢ E : T"
  , "          ----------------------------------"
  , "          Γ ⊢ ( λ x : S . E ) : ( S -> T )"
  , ""
  , "  T-app:  Γ ⊢ M : ( S -> T )    Γ ⊢ N : S"
  , "          --------------------------------"
  , "          Γ ⊢ ( M N ) : T"
  , ""
  ]

valueAndStep :: [String]
valueAndStep =
  [ "judgment value = M value where"
  , ""
  , "  V-abs:  ---------------------"
  , "          ( λ x : T . E ) value"
  , ""
  , "judgment step = M --> N where"
  , ""
  , "  E-beta:  N value"
  , "           ---------------------------------"
  , "           ( ( λ x : T . E ) N ) --> E[x->N]"
  , ""
  , "  E-app1:  M --> M'"
  , "           --------------------"
  , "           ( M N ) --> ( M' N )"
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

-- | The names a constructor's arguments are bound under. @:show@ prints an
-- argument nothing depends on as an arrow, so a premise's name is seen here.
argumentNames :: Session -> String -> String -> [String]
argumentNames s d c =
  [ n | Just ind <- [lookupInductive (GlobalName d) (globals (sessionMachine s))]
      , con <- inductiveConstructors ind, constructorName con == GlobalName c
      , Ident n <- map entryIdent (constructorArguments con) ]

refusal :: String -> [String] -> String -> TestTree
refusal what body want = testCase what $ do
  r <- load (header ++ body)
  either (@?= want) (const (assertFailure "it loaded")) r

-- ---------------------------------------------------------------------------

reading :: [TestTree]
reading =
  [ testCase "the notation is one production named after the judgment, and each rule is cut at its line" $
      fmap (\b -> (blockName b, map productionName (blockProductions b), blockRules b))
        (readBlock JudgmentBlock 1 (unlines
          [ " step = M --> N where"
          , "  E-app1:  M --> M'"
          , "           --------"
          , "           ( M N ) --> ( M' N )"
          , "  V:  -----"
          , "      M --> M" ]))
        @?= Right ("step", ["step"],
             [ RawRule 2 "E-app1" Nothing ["M --> M'"] "( M N ) --> ( M' N )"
             , RawRule 5 "V" Nothing [] "M --> M" ])
    -- His ruling, 2026-09-21: a line break ends a premise, and a line indented
    -- further than the premise column continues the one above.
  , testCase "a line break ends a premise line, and a name may stand apart from its colon" $
      fmap blockRules (readBlock JudgmentBlock 1 (unlines
          [ " j = M ok where"
          , "  R :  M ok    N ok"
          , "       E ok"
          , "       ---"
          , "       M ok" ]))
        @?= Right [RawRule 2 "R" Nothing ["M ok N ok", "E ok"] "M ok"]
  , testCase "a line indented further than the premise column continues the one above" $
      fmap blockRules (readBlock JudgmentBlock 1 (unlines
          [ " j = M ok where"
          , "  R:  Γ ⊢ M :"
          , "          ( S -> T )"
          , "      N ok -- a comment keeps the spacing before it"
          , "      ---"
          , "      M ok" ]))
        @?= Right [RawRule 2 "R" Nothing ["Γ ⊢ M : ( S -> T )", "N ok"] "M ok"]
  , testCase "a premise line indented less than the first is refused" $
      readBlock JudgmentBlock 1 " j = M ok where\n  R:  M ok\n     N ok\n      ---\n      M ok\n"
        @?= Left (PremiseIndentedLess 3)
  , testCase "the annotated tier's quantifier ends at the -> that ends its line" $
      fmap blockRules (readBlock JudgmentBlock 1 (unlines
          [ " j = M ok where"
          , "  rule R where ∀ (f : LC -> LC)"
          , "                 (M : LC) ->"
          , "      M ok"
          , "      ----"
          , "      M ok" ]))
        @?= Right [RawRule 2 "R" (Just "∀ (f : LC -> LC) (M : LC)") ["M ok"] "M ok"]
  , testCase "a rule with no line" $
      readBlock JudgmentBlock 1 " j = M ok where\n  R:  M ok\n      M ok\n"
        @?= Left (RuleWithoutLine 2)
  , testCase "a rule with nothing below its line" $
      readBlock JudgmentBlock 1 " j = M ok where\n  R:  M ok\n      ---\n" @?= Left (RuleWithoutConclusion 2)
  , testCase "a rule with no name" $
      readBlock JudgmentBlock 1 " j = M ok where\n  M ok\n  ---\n  M ok\n"
        @?= Left (RuleUnnamed 2)
  , testCase "a quantifier whose -> does not end its line" $
      readBlock JudgmentBlock 1 " j = M ok where\n  rule R where ∀ (M : LC) -> M ok\n      ---\n      M ok\n"
        @?= Left (QuantifierMalformed 2)
  , testCase "a header that is not ‹name› = ‹notation› where" $
      readBlock JudgmentBlock 1 " j M ok where\n" @?= Left (JudgmentHeaderMalformed 1)
  ]

generated :: [TestTree]
generated =
  [ testCase ":show typing — quantified in order of first appearance, then the premises" $ do
      s <- loaded (header ++ typing)
      said s ":show typing" @?=
        [ "data typing : Ctx -> LC -> Ty -> Type₀ where"
        , "  { T-var : ∀ (x : String) (T : Ty) (Γ : Ctx) -> Ctx-in`${x} : ${T} ∈ ${Γ}` -> typing`${Γ} ⊢ ${LC`${x}`} : ${T}`"
        , "  ; T-abs : ∀ (Γ : Ctx) (x : String) (S : Ty) (E : LC) (T : Ty) -> typing`${Γ} , ${x} : ${S} ⊢ ${E} : ${T}` -> typing`${Γ} ⊢ ( λ ${x} : ${S} . ${E} ) : ( ${S} -> ${T} )`"
        , "  ; T-app : ∀ (Γ : Ctx) (M : LC) (S : Ty) (T : Ty) (N : LC) -> typing`${Γ} ⊢ ${M} : ( ${S} -> ${T} )` -> typing`${Γ} ⊢ ${N} : ${S}` -> typing`${Γ} ⊢ ( ${M} ${N} ) : ${T}` }"
        ]
  , testCase "a rule with no premises and no metavariable of its own" $ do
      s <- loaded (header ++ ["judgment okTy = T ok where", "", "  U:  ---", "      ι ok", ""])
      said s ":show okTy" @?= ["data okTy : Ty -> Type₀ where", "  { U : okTy`ι ok` }"]
  , testCase "suffixed metavariables are further ones of the same sort" $ do
      s <- loaded (header ++
        [ "judgment alike = T ~ S where", ""
        , "  Tr:  T ~ T'    T' ~ T₁    T₁ ~ T2    T2 ~ T_1    T_1 ~ T_r'"
        , "       ------------------------------"
        , "       T ~ T_r'", "" ])
      said s ":show alike" @?=
        [ "data alike : Ty -> Ty -> Type₀ where"
        , "  { Tr : ∀ (T : Ty) (T' : Ty) (T₁ : Ty) (T2 : Ty) (T_1 : Ty) (T_r' : Ty) -> alike`${T} ~ ${T'}` -> alike`${T'} ~ ${T₁}` -> alike`${T₁} ~ ${T2}` -> alike`${T2} ~ ${T_1}` -> alike`${T_1} ~ ${T_r'}` -> alike`${T} ~ ${T_r'}` }" ]
    -- §6.1: the language's own name is one of its metavariables, and a binder
    -- named like the type it ranges over would shadow it.
  , testCase "a metavariable named like a type is primed, away from the others too" $ do
      s <- loaded (header ++
        [ "judgment again = M twice where", ""
        , "  A:  LC twice    LC' twice"
        , "      --------------------"
        , "      ( LC LC' ) twice", "" ])
      said s ":show again" @?=
        [ "data again : LC -> Type₀ where"
        , "  { A : ∀ (LC'' : LC) (LC' : LC) -> again`${LC''} twice` -> again`${LC'} twice` -> again`( ${LC''} ${LC'} ) twice` }" ]
  , testCase "the notation is installed: a judgment literal is a type, and :parse reads one" $ do
      s <- loaded (header ++ typing)
      said s ":infer typing`· ⊢ ( λ x : ι . x ) : ( ι -> ι )`"
        @?= ["typing`· ⊢ ( λ x : ι . x ) : ( ι -> ι )` : Type₀"]
      said s ":parse typing · ⊢ x : ι"
        @?= ["typing(empty, var(x), base)"]
  ]

premises :: [TestTree]
premises =
  [ testCase "premises separated by whitespace alone are told apart by parsing" $ do
      s <- loaded (header ++ typing)
      -- T-app's two premises are one line; the constructor has both.
      said s ":show typing" !! 3
        @?= "  ; T-app : ∀ (Γ : Ctx) (M : LC) (S : Ty) (T : Ty) (N : LC) -> typing`${Γ} ⊢ ${M} : ( ${S} -> ${T} )` -> typing`${Γ} ⊢ ${N} : ${S}` -> typing`${Γ} ⊢ ( ${M} ${N} ) : ${T}` }"
  , testCase "one premise per line, and one continued onto the next" $ do
      s <- loaded (header ++
        [ "judgment typed = Γ ⊢ M : T where", ""
        , "  T-app:  Γ ⊢ M :"
        , "              ( S -> T )"
        , "          Γ ⊢ N : S"
        , "          ---------------"
        , "          Γ ⊢ ( M N ) : T", "" ])
      said s ":show typed" !! 1
        @?= "  { T-app : ∀ (Γ : Ctx) (M : LC) (S : Ty) (T : Ty) (N : LC) -> typed`${Γ} ⊢ ${M} : ( ${S} -> ${T} )` -> typed`${Γ} ⊢ ${N} : ${S}` -> typed`${Γ} ⊢ ( ${M} ${N} ) : ${T}` }"
  , testCase "a named premise binds its name; an unnamed one is d‹k›" $ do
      s <- loaded (header ++ typing ++
        [ "judgment twice = Γ ⊢ M :: T where", ""
        , "  B:  left : Γ ⊢ M : T    Γ ⊢ M : T"
        , "      ------------------------------"
        , "      Γ ⊢ M :: T", "" ])
      said s ":show twice" @?=
        [ "data twice : Ctx -> LC -> Ty -> Type₀ where"
        , "  { B : ∀ (Γ : Ctx) (M : LC) (T : Ty) -> typing`${Γ} ⊢ ${M} : ${T}` -> typing`${Γ} ⊢ ${M} : ${T}` -> twice`${Γ} ⊢ ${M} :: ${T}` }" ]
      argumentNames s "twice" "B" @?= ["Γ", "M", "T", "left", "d2"]
    -- x is a metavariable, so `x : T ∈ Γ` is never a premise named x.
  , testCase "a lookup premise is not read as a premise named by its metavariable" $ do
      s <- loaded (header ++ typing)
      said s ":show typing" !! 1
        @?= "  { T-var : ∀ (x : String) (T : Ty) (Γ : Ctx) -> Ctx-in`${x} : ${T} ∈ ${Γ}` -> typing`${Γ} ⊢ ${LC`${x}`} : ${T}`"
  , refusal "a premise named like a metavariable"
      (typing ++ ["judgment bad = M bad where", "", "  B:  M' : · ⊢ M : ι", "      ---", "      M bad", ""])
      "refused: in the judgment bad, rule B: a premise may not be named M', which is a metavariable"
  , refusal "two premises named alike"
      (typing ++ ["judgment bad = M bad where", "", "  B:  d : · ⊢ M : ι    d : · ⊢ M : ι", "      ---", "      M bad", ""])
      "refused: in the judgment bad, rule B: a premise may not be named d, which the rule already uses"
  ]

substitution :: [TestTree]
substitution =
  [ testCase "E[x->N] is LC-subst" $ do
      s <- loaded (header ++ valueAndStep)
      said s ":show step" !! 1
        @?= "  { E-beta : ∀ (N : LC) (x : String) (T : Ty) (E : LC) -> value`${N} value` -> step`( ( λ ${x} : ${T} . ${E} ) ${N} ) --> ${LC-subst E x N}`"
  , testCase "a list is simultaneous, LC-subst-all, and chained brackets are sequential" $ do
      s <- loaded (header ++
        [ "judgment sub = M ~> N where", ""
        , "  S:  ---"
        , "      M ~> E[x->M, x'->N][x1->N']", "" ])
      said s ":show sub" @?=
        [ "data sub : LC -> LC -> Type₀ where"
        , "  { S : ∀ (M : LC) (E : LC) (x : String) (x' : String) (N : LC) (x1 : String) (N' : LC) -> sub`${M} ~> ${LC-subst (LC-subst-all {0 0 0} E (cons {0} (And {0 0} String LC) (both {0 0} String LC x M) (cons {0} (And {0 0} String LC) (both {0 0} String LC x' N) (nil {0} (And {0 0} String LC))))) x1 N'}` }" ]
    -- §6.3's CHECK: the left of -> is a binder-sorted name.
  , refusal "the left of -> is not a name"
      ["judgment sub = M ~> N where", "", "  S:  ---", "      M ~> E[M->N]", ""]
      "refused: in the judgment sub, rule S: its conclusion `M ~> E[M->N]` is not a sub judgment: unexpected 'M' at character 8, expecting x"
  ]

annotated :: [TestTree]
annotated =
  [ testCase "quantification is as written, and may range over a derivation" $ do
      s <- loaded (header ++ typing ++
        [ "judgment ann = Γ ⊢ M :: T where", ""
        , "  rule A where ∀ (T : Ty) (M : LC) (Γ : Ctx) (d : typing Γ M T) ->"
        , "      Γ ⊢ M : T"
        , "      ---------"
        , "      Γ ⊢ M :: T", "" ])
      said s ":show ann" @?=
        [ "data ann : Ctx -> LC -> Ty -> Type₀ where"
        , "  { A : ∀ (T : Ty) (M : LC) (Γ : Ctx) -> typing`${Γ} ⊢ ${M} : ${T}` -> typing`${Γ} ⊢ ${M} : ${T}` -> ann`${Γ} ⊢ ${M} :: ${T}` }" ]
      argumentNames s "ann" "A" @?= ["T", "M", "Γ", "d", "d1"]
  , refusal "a name quantified twice — a rule's ∀ lists its metavariables, it does not nest"
      (typing ++
        [ "judgment ann = Γ ⊢ M :: T where", ""
        , "  rule A where ∀ (M : LC) (M : LC) (Γ : Ctx) (T : Ty) ->"
        , "      Γ ⊢ M : T"
        , "      ---------"
        , "      Γ ⊢ M :: T", "" ])
      "refused: in the judgment ann, rule A: M is quantified twice"
  , refusal "a metavariable used and not quantified"
      (typing ++
        [ "judgment ann = Γ ⊢ M :: T where", ""
        , "  rule A where ∀ (M : LC) (Γ : Ctx) ->"
        , "      Γ ⊢ M : T"
        , "      ---------"
        , "      Γ ⊢ M :: T", "" ])
      "refused: in the judgment ann, rule A: T is used but not quantified"
  ]

derivations :: [TestTree]
derivations =
  [ testCase "a typing derivation checks against its judgment literal" $ do
      _ <- loaded (header ++ typing ++
        [ "idTyped : typing`· ⊢ ( λ x : ι . x ) : ( ι -> ι )`"
        , "idTyped = T-abs empty \"x\" base (var \"x\") base (T-var \"x\" base (extend empty \"x\" base) (Ctx-here empty \"x\" base))" ])
      pure ()
  , testCase "one at the wrong type is refused" $ do
      r <- load (header ++ typing ++
        [ "wrong : typing`· ⊢ ( λ x : ι . x ) : ι`"
        , "wrong = T-abs empty \"x\" base (var \"x\") base (T-var \"x\" base (extend empty \"x\" base) (Ctx-here empty \"x\" base))" ])
      either (const (pure ())) (const (assertFailure "a derivation at the wrong type loaded")) r
  , testCase "E-beta's right-hand side is computed by substitution" $ do
      _ <- loaded (header ++ valueAndStep ++
        [ "beta : step`( ( λ x : ι . ( x x ) ) ( λ y : ι . y ) ) --> ( ( λ y : ι . y ) ( λ y : ι . y ) )`"
        , "beta = E-beta LC`( λ y : ι . y )` \"x\" base LC`( x x )` (V-abs \"y\" base LC`y`)" ])
      pure ()
  , testCase "and a step to anything else is refused" $ do
      r <- load (header ++ valueAndStep ++
        [ "beta : step`( ( λ x : ι . ( x x ) ) ( λ y : ι . y ) ) --> ( λ y : ι . y )`"
        , "beta = E-beta LC`( λ y : ι . y )` \"x\" base LC`( x x )` (V-abs \"y\" base LC`y`)" ])
      either (const (pure ())) (const (assertFailure "a wrong step loaded")) r
  ]

refused :: [TestTree]
refused =
  [ refusal "a name that is not a metavariable is never an implicit binding (§6.2)"
      ["judgment bad = Γ ⊢ M : T where", "", "  B:  ---", "      Γ ⊢ p : T", ""]
      "refused: in the judgment bad, rule B: p is not a metavariable"
  , refusal "a conclusion of another judgment"
      (valueAndStep ++ ["judgment bad = M bad where", "", "  B:  ---", "      M value", ""])
      "refused: in the judgment bad, rule B: its conclusion `M value` is not a bad judgment: unexpected 'v' at character 3, expecting bad or ["
    -- M is a metavariable, so it is not reported as one that is not: the
    -- conclusion simply does not start the way a typing judgment does.
  , refusal "a conclusion that starts with a metavariable in the wrong place"
      ["judgment bad = Γ ⊢ M : T where", "", "  B:  ---", "      M ⊢ M : T", ""]
      "refused: in the judgment bad, rule B: its conclusion `M ⊢ M : T` is not a bad judgment: unexpected 'M' at character 1, expecting · or a metavariable of Ctx"
  , refusal "a notation that binds"
      ["judgment bad = E[x] ok where", "", "  B:  ---", "      E ok", ""]
      "refused: in the judgment bad, production bad: E is written as a binding form, and a judgment's notation binds nothing"
  , refusal "a rule named like something declared"
      ["judgment bad = M ok where", "", "  var:  ---", "        M ok", ""]
      "refused: bad's constructor var is already declared"
  , refusal "a judgment named like something declared"
      ["judgment LC = M ok where", "", "  B:  ---", "      M ok", ""]
      "refused: LC is already declared"
  ]
