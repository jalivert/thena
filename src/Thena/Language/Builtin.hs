-- | The advising grammars for Thena's own two tags, @surface@ and @core@
-- (MS7 phase 147).
--
-- **These are secondary grammars and they never parse anything.** Happy runs
-- the line — "Thena.Surface.Read" for a @surface@ region, "Thena.Syntax.Parser"
-- for a @core@ one — and what is here answers only /what may I write next/.
-- **HIS RULING, 2026-10-01**, and his reason is the one that settles it: Happy's
-- parser is a **translating** parser, it builds the Haskell tree, so pointing
-- the chart at the real thing is not a grammar exercise. @.claude\/RULINGS.md@,
-- *Rulings of 2026-10-01*.
--
-- **Hand-written, and that is the decision rather than an omission.** There is
-- no table to derive these from the way @Thena.Rules.opWords@ served phase 137:
-- the only description of the surface language is @Surface\/Parser.y@, which is
-- over /tokens/ with a layout pass in the middle where this is over
-- /characters/. Deriving would mean using Happy as a library, which is the
-- in-house generator itself — *"the same class of complexity"*
-- (@AGENDA.md@ 94). So these are kept in step by hand, and two tests make that
-- hold rather than hope: see "Thena.Language.BuiltinTests".
--
-- __The one invariant.__ **An advising grammar may accept less than the running
-- one and never more.** Everything narrow here is narrow on purpose:
--
-- * **no layout** — the chart is scannerless over characters and the offside
--   rule is a pass over tokens, so @let { x = y } in x@ is described and the
--   braceless @let x = y in x@, which runs, is not. **Solved at the generator,
--   not here** (@AGENDA.md@ 94);
-- * **no splices** — @surface\`${t}\`@ is a parse error today and 'Surface' has
--   no node for a spliced value, so offering @${@ would make this wider than
--   what runs. The real fix is @AGENDA.md@ 96; a @core@ region's splices do
--   exist and are described below;
-- * **narrower lexemes** — "Thena.Language.Lexemes" says why.
--
-- __Why the strata are mirrored rather than flattened.__ The first cut wrote one
-- recursive nonterminal per language and let the grammar be ambiguous, on the
-- grounds that an ambiguous grammar costs nothing to a parser that only ever
-- queries the chart. **It is wider, and that is fatal.** @Term : Arrowed ':'
-- Arrowed@ is not recursive on the right, so Happy /rejects/ @a : b : c@ and a
-- flattened @Term -> Term ':' Term@ accepts it. The strata are the grammar, not
-- decoration.
--
-- __And why that is safe to show a frontend.__ A stratum is named
-- @\‹public\>\/\‹stratum\>@ — @surface:Term\/app@ — and
-- "Thena.View.Chart" reports the part before the @\/@. So an offer says
-- /a surface term goes here/ and never @surface:Term\/arrowed@, which is a name
-- this module invented and no user has met. The invariant is phase 141's, one
-- size up: **nothing a frontend sees may be a nonterminal invented for
-- plumbing.**
module Thena.Language.Builtin
  ( surfaceHead
  , coreHead
  , surfaceRules
  , coreRules
  , publicHead
  ) where

import Thena.Language.Grammar (Grammar, productionBody)
import Thena.Language.Regex (Regex)
import Thena.Language.Build (languageNames, productionNames)
import qualified Thena.Language.Earley as E
import Thena.Language.Lexemes
  (charRegex, identRegex, numberRegex, regexRegex, stringRegex, universeRegex)

-- | The nonterminal a @surface@ region parses at, and the only surface head a
-- frontend is ever shown.
surfaceHead :: String
surfaceHead = "surface:Term"

-- | The nonterminal a @core@ region parses at — the development calculus's own
-- grammar, which is what @core\`…\`@, corners and @:core@ all read.
coreHead :: String
coreHead = "core:Term"

-- | The public head a stratum belongs to: everything before the @\/@.
--
-- **Total, and the identity on a head with no @\/@** — a language name, an
-- @Operand:T@, @instral:Argument@. A language or metavariable cannot contain
-- either @:@ or @\/@, so no user grammar's nonterminal is ever rewritten by
-- this.
publicHead :: String -> String
publicHead = takeWhile (/= '/')

-- ---------------------------------------------------------------------------
-- The surface language

-- | Every production of the surface language, for the object languages loaded
-- now.
--
-- **The tagged term literals are contributed here from what is installed**, not
-- named in a list — which is the whole of what lets this exist before any
-- object language does. A @language LC@ loaded mid-session is writable inside a
-- @surface@ region immediately, with nothing rebuilt, for the same reason
-- 'Thena.Language.Instral.literalProductions' already works that way.
surfaceRules :: [Grammar] -> [E.Rule]
surfaceRules gs = concat
  [ term, arrowed, app, args, arg, atom gs, terms, arguments
  , binders, binder, piBinders, piBinder, names, bindings, binding
  ]
  where
    s = surfaceHead
    arrowedH = s ++ "/arrowed"
    appH     = s ++ "/app"
    argsH    = s ++ "/args"
    argH     = s ++ "/arg"
    atomH    = s ++ "/atom"
    termsH   = s ++ "/terms"
    argumentsH = s ++ "/arguments"
    binderH  = "surface:Binder"
    bindersH = binderH ++ "/binders"
    piBinderH  = binderH ++ "/pi"
    piBindersH = binderH ++ "/pi-binders"
    namesH   = "surface:Name" ++ "/names"
    bindingH  = "surface:Binding"
    bindingsH = bindingH ++ "/bindings"

    -- **Ascription binds loosest and does not nest**, which is the one place a
    -- flattened grammar would have gone wider: @a : b : c@ is not a surface term.
    term =
      [ rule s "annot" [nt arrowedH, lit ":", nt arrowedH]
      , rule s "arrowed" [nt arrowedH]
      ]

    -- **Both spellings of each binder word**, because the lexer has both:
    -- @\\@ is @λ@ and @forall@ is @∀@ ("Thena.Syntax.Lexer").
    arrowed =
      [ rule arrowedH ("lam" ++ w) [lit l, nt bindersH, lit "->", nt arrowedH]
      | (w, l) <- [("", "λ"), ("-ascii", "\\")]
      ] ++
      [ rule arrowedH ("pi" ++ w) [lit l, nt piBindersH, lit "->", nt arrowedH]
      | (w, l) <- [("", "∀"), ("-word", "forall")]
      ] ++
      [ rule arrowedH "let"
          [lit "let", lit "{", nt bindingsH, lit "}", lit "in", nt arrowedH]
      , rule arrowedH "arrow" [nt appH, lit "->", nt arrowedH]
      , rule arrowedH "app" [nt appH]
      ]

    app =
      [ rule appH "atom" [nt atomH]
      , rule appH "spine" [nt atomH, nt argsH]
      ]

    args =
      [ rule argsH "one" [nt argH]
      , rule argsH "more" [nt argsH, nt argH]
      ]

    arg =
      [ rule argH "explicit" [nt atomH]
      , rule argH "implicit" [lit "{", nt s, lit "}"]
      ]

    -- @Terms@ may be empty in @Surface\/Parser.y@ and the chart has no empty
    -- rules, so the parenthesised group is spelled twice rather than the list
    -- being made optional.
    terms =
      [ rule termsH "one" [nt atomH]
      , rule termsH "more" [nt termsH, nt atomH]
      ]

    arguments =
      [ rule argumentsH "none" [lit "(", lit ")"]
      , rule argumentsH "some" [lit "(", nt termsH, lit ")"]
      ]

    binders =
      [ rule bindersH "one" [nt binderH]
      , rule bindersH "more" [nt bindersH, nt binderH]
      ]

    -- **A λ's binder need not be annotated and a ∀'s must be**, which is the
    -- difference between @LamBinder@ and @PiBinder@ and the reason there are two.
    binder =
      [ rule binderH "name" [scan "name" identRegex]
      , rule binderH "typed" [lit "(", nt namesH, lit ":", nt s, lit ")"]
      , rule binderH "implicit" [lit "{", nt namesH, lit ":", nt s, lit "}"]
      , rule binderH "implicit-bare" [lit "{", nt namesH, lit "}"]
      ]

    piBinders =
      [ rule piBindersH "one" [nt piBinderH]
      , rule piBindersH "more" [nt piBindersH, nt piBinderH]
      ]

    piBinder =
      [ rule piBinderH "typed" [lit "(", nt namesH, lit ":", nt s, lit ")"]
      , rule piBinderH "implicit" [lit "{", nt namesH, lit ":", nt s, lit "}"]
      ]

    names =
      [ rule namesH "one" [scan "name" identRegex]
      , rule namesH "more" [nt namesH, scan "name" identRegex]
      ]

    bindings =
      [ rule bindingsH "one" [nt bindingH]
      , rule bindingsH "more" [nt bindingsH, lit ";", nt bindingH]
      ]

    binding =
      [ rule bindingH "bind" [scan "name" identRegex, lit "=", nt s]
      , rule bindingH "typed" [scan "name" identRegex, lit ":", nt s, lit "=", nt s]
      ]

    atom gs' =
      [ rule atomH "name" [scan "name" identRegex]
        -- **@?foo@ is two tokens and not one** — @?@ cannot start an identifier,
        -- so the lexer hands over @TQuery@ and then the name, and @? foo@ with a
        -- space is a surface hole too. Writing it as one scan would be narrower
        -- than what runs, which is allowed, and wrong about why.
      , rule atomH "hole" [lit "?", scan "name" identRegex]
      , rule atomH "universe" [scan "universe" universeRegex]
      , rule atomH "universe-open" [lit "Type"]
      , rule atomH "string" [scan "string" stringRegex]
      , rule atomH "char" [scan "char" charRegex]
      , rule atomH "int" [scan "int" numberRegex]
      , rule atomH "regex" [scan "regex" regexRegex]
      , rule atomH "parens" [lit "(", nt s, lit ")"]
      , rule atomH "elim"
          [ lit "elim", scan "name" identRegex, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      ] ++ literals atomH gs'

-- ---------------------------------------------------------------------------
-- The development calculus

-- | Every production of the development calculus's grammar — @core\`…\`@,
-- @⌜ t ⌝@ and every @:@-command that reads one.
--
-- **Splices are described by neither grammar**, and for one reason rather than
-- two: they are writable only where the language is embedded. @Surface@ has no
-- node for one at all; @Raw@ has two, but @}$@ is a token the /region/ scanner
-- emits, so a splice lexes inside @core\`…\`@ and not in a @:core@ argument.
-- @AGENDA.md@ 96.
coreRules :: [Grammar] -> [E.Rule]
coreRules gs = concat
  [ term, app, atom gs, atoms, arguments, binders, binder
  , ident, levels, levelArgs, constraint
  ]
  where
    c = coreHead
    appH   = c ++ "/app"
    atomH  = c ++ "/atom"
    atomsH = c ++ "/atoms"
    argumentsH = c ++ "/arguments"
    binderH  = "core:Binder"
    bindersH = binderH ++ "/binders"
    identH = "core:Name"
    levelsH = "core:Level" ++ "/levels"
    levelArgsH = "core:Level" ++ "/arguments"
    constraintH = "core:Constraint"

    term =
      [ rule c "lam" [lit "λ", nt bindersH, lit "->", nt c]
      , rule c "lam-ascii" [lit "\\", nt bindersH, lit "->", nt c]
      , rule c "pi" [lit "∀", nt bindersH, lit "->", nt c]
      , rule c "pi-word" [lit "forall", nt bindersH, lit "->", nt c]
        -- **A @let@ in the development calculus always carries its type**, where
        -- the surface's is optional: there is nothing here to infer it with.
      , rule c "let"
          [lit "let", nt identH, lit "=", nt c, lit ":", nt c, lit "in", nt c]
      , rule c "claim"
          [lit "let", lit "?", nt identH, lit ":", nt c, lit "in", nt c]
      , rule c "guess"
          [ lit "let", lit "?", nt identH, lit ":", nt c, lit "≐"
          , lit "(", nt c, lit ")", lit "in", nt c
          ]
      , rule c "pending" [nt constraintH, lit "▸", nt c]
      , rule c "elim"
          [ lit "elim", nt identH, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      , rule c "elim-at"
          [ lit "elim", nt identH, nt levelArgsH, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      , rule c "arrow" [nt appH, lit "->", nt c]
      , rule c "app" [nt appH]
      ]

    app =
      [ rule appH "atom" [nt atomH]
      , rule appH "spine" [nt appH, nt atomH]
      ]

    -- @Atoms@ may be empty, as the surface's @Terms@ may; same two spellings.
    atoms =
      [ rule atomsH "one" [nt atomH]
      , rule atomsH "more" [nt atomsH, nt atomH]
      ]

    arguments =
      [ rule argumentsH "none" [lit "(", lit ")"]
      , rule argumentsH "some" [lit "(", nt atomsH, lit ")"]
      ]

    -- **Always annotated**: a binder with no type is a parse error here rather
    -- than a hole (@PLAN-representation.md@ §2.6).
    binders =
      [ rule bindersH "one" [nt binderH]
      , rule bindersH "more" [nt bindersH, nt binderH]
      ]

    binder = [ rule binderH "typed" [lit "(", nt identH, lit ":", nt c, lit ")"] ]

    -- **No splice production, and the phase's own test is why.** @${x}@ is an
    -- atom and a name in @Raw@ (MS5 phases 81 and 88), but @}$@ is emitted only
    -- by the /region/ scanner — so a splice lexes inside @core\`…\`@ and not in a
    -- bare @:core@ argument, and one rule set serves both. Describing it would
    -- have been wider than what runs, which 'neverWiderCore' caught on
    -- @let ${ x }$ = x : x in x@. **It is the same question his surface-splice
    -- ruling asks** — a splice belongs where the language is embedded — so both
    -- languages' splices are answered together in @AGENDA.md@ 96 rather than
    -- half-answered here.
    ident = [ rule identH "word" [scan "name" identRegex] ]

    levels =
      [ rule levelsH "one" [scan "int" numberRegex]
      , rule levelsH "more" [nt levelsH, scan "int" numberRegex]
      ]

    levelArgs =
      [ rule levelArgsH "none" [lit "{", lit "}"]
      , rule levelArgsH "some" [lit "{", nt levelsH, lit "}"]
      ]

    constraint =
      [ rule constraintH "in"
          [ nt bindersH, lit "⊢", nt c, lit "≟", nt c, lit ":", nt c ]
      , rule constraintH "closed"
          [ lit "⊢", nt c, lit "≟", nt c, lit ":", nt c ]
      ]

    atom gs' =
      [ rule atomH "name" [scan "name" identRegex]
      , rule atomH "at" [scan "name" identRegex, nt levelArgsH]
      , rule atomH "universe" [scan "universe" universeRegex]
      , rule atomH "universe-open" [lit "Type"]
      , rule atomH "string" [scan "string" stringRegex]
      , rule atomH "char" [scan "char" charRegex]
      , rule atomH "int" [scan "int" numberRegex]
      , rule atomH "regex" [scan "regex" regexRegex]
      , rule atomH "parens" [lit "(", nt c, lit ")"]
        -- **Corners are not described, on his instruction of 2026-10-01.** They
        -- are an atom in @Raw@ and the phase that wrote this described them; he
        -- had them taken out again rather than left for the removal to find:
        -- *"I don't want to risk it sticking around through the future
        -- refactor."* @⌜ t ⌝@ is to be replaced by @core\`t\`@ throughout —
        -- @AGENDA.md@ 98 — and nothing new points at it in the meantime.
      ] ++ literals atomH gs'

-- ---------------------------------------------------------------------------
-- Shared

-- | The tagged term literals, at a head that takes an atom.
--
-- **The same three symbols phase 141 uses** — the opening tag, the language's
-- own nonterminal, the closing fence — plus the empty region, which both
-- grammars accept. @L[p]\`…\`@ inlines that production's body for phase 141's
-- reason: a wrapper nonterminal would be a name this module invented, and
-- reaching the whole language through it would accept terms the running parser
-- refuses.
literals :: String -> [Grammar] -> [E.Rule]
literals head' gs = concat
  [ [ E.Rule (head' ++ "/`" ++ l) head' [E.Literal (l ++ "`"), E.Nonterminal l, fence] []
    , E.Rule (head' ++ "/``" ++ l) head' [E.Literal (l ++ "`"), fence] []
    ] ++
    [ E.Rule (head' ++ "/`" ++ l ++ "[" ++ p ++ "]") head'
        (E.Literal (l ++ "[" ++ p ++ "]`") : productionBody gs p ++ [fence]) []
    | p <- productionNames gs l
    ]
  | l <- languageNames gs
  ]
  where fence = E.Literal "`"

rule :: String -> String -> [E.Symbol] -> E.Rule
rule h nm body = E.Rule (h ++ "/" ++ nm) h body []

lit :: String -> E.Symbol
lit = E.Literal

nt :: String -> E.Symbol
nt = E.Nonterminal

scan :: String -> Regex -> E.Symbol
scan = E.Scan
