-- | The advising grammars for Thena's own two tags, @surface@ and @core@
-- (MS7 phases 147 and 148).
--
-- **These are secondary grammars and they never parse anything.** Happy runs
-- the line — "Thena.Surface.Read" for a @surface@ region, "Thena.Syntax.Parser"
-- for a @core@ one — and what is here answers only /what may I write next/.
-- **HIS RULING, 2026-10-01**: Happy's parser is a **translating** parser, it
-- builds the Haskell tree, so pointing the chart at the real thing is not a
-- grammar exercise. @.claude\/RULINGS.md@, *Rulings of 2026-10-01*.
--
-- **Hand-written, and that is the decision rather than an omission.** There is
-- no table to derive these from the way @Thena.Rules.opWords@ served phase 137,
-- and deriving from @Surface\/Parser.y@ would mean using Happy as a library,
-- which is the in-house generator itself (@AGENDA.md@ 94). So these are kept in
-- step by hand, and two tests make that hold rather than hope: see
-- "Thena.Language.BuiltinTests".
--
-- __Written for Earley, not copied from Happy — HIS CORRECTION, 2026-10-02.__
-- Phase 147 mirrored all six rungs of @Surface\/Parser.y@'s term ladder —
-- @Term@, @Arrowed@, @App@, @Args@, @Arg@, @Atom@. **Four of them exist only
-- because LALR needs an unambiguous grammar**, and his objection was exactly
-- that: /"You were supposed to leverage the power the Earley has — it should
-- allow for a more natural way of defining the surface since the language we
-- support is only a subset."/ The chart holds every reading and this grammar
-- never parses, so ambiguity costs nothing but chart size, and precedence rungs
-- buy nothing. **One recursive head per language**, and the only extra is
-- 'surfaceAtomHead', for the two slots where Happy genuinely wants an atom.
--
-- __What flattening would get wrong, and does not.__ Two restrictions in the
-- surface are about the /language/ and not about trees, checked by running the
-- real parser rather than reading it:
--
-- > x : y          yes     elim d (a) m (b) (c) t       yes
-- > x : y : z      NO      elim d (a) m x (b) (c) t     NO
-- > (x : y) : z    yes     elim d (a) (m n) (b) (c) t   yes
--
-- **Ascription does not nest**, so it is not a production of the term: it is
-- spelled out at the five places @Surface\/Parser.y@ writes @Term@ rather than
-- @Arrowed@ — which keeps one head and still refuses @x : y : z@.
-- **@elim@'s motive and target take one atom each**, which is what
-- 'surfaceAtomHead' is for. Everything else in the ladder is tree shape: the flat grammar accepts
-- exactly the same strings.
--
-- __The one invariant.__ **An advising grammar may accept less than the running
-- one and never more.** Everything narrow here is narrow on purpose:
--
-- * **no layout** — the chart is scannerless over characters and the offside
--   rule is a pass over tokens, so @let { x = y } in x@ is described and the
--   braceless @let x = y in x@, which runs, is not. Solved at the generator
--   (@AGENDA.md@ 94);
-- * **no splices** — @surface\`${t}\`@ is a parse error today, and a @core@
--   splice lexes only inside a region, so one rule set cannot describe it
--   honestly. @AGENDA.md@ 96;
-- * **no term literal of another language in an operand** — @core\`t\`@ and
--   @surface\`t\`@ stand where a value stands, and this grammar describes the
--   values. **It was two gaps until MS10 phase 269** (`~3t63k`), corners and
--   the @⟨…⟩@ alias each being the same thing written a third and a fourth
--   way; there is one spelling to describe now, which is the item's point;
-- * **narrower lexemes** — "Thena.Language.Lexemes" says why.
--
-- __Every head is a phrase, and the separator is a space.__ A head is
-- @surface term@, @core atom@, @surface binder@ — **words a dropdown can show**,
-- because there is nothing left to hide. A language name and a metavariable are
-- identifiers, so neither can contain a space: the separator collides with
-- nothing and needs no mapping in the view. **Phase 147's @\/@ convention and
-- the @publicHead@ that went with it are gone** — they existed only to hide
-- rungs that should not have been written. The colons that remain elsewhere —
-- @Operand:Core@ and friends — are phases 137–142's and are his, on
-- @ms7\/CLOSEOUT.md@ 36.
module Thena.Language.Builtin
  ( surfaceHead
  , surfaceAtomHead
  , surfaceContents
  , coreHead
  , surfaceRules
  , coreRules
  ) where

import Thena.Core.Term (InScope, nameFromText)
import Thena.Language.Grammar (Grammar, productionBody, tagText)
import Thena.Language.Build (languageNames, productionNames, productionRule)
import qualified Thena.Language.Earley as E
import Thena.Language.Lexemes
  ( charRegex
  , identRegex
  , numberRegex
  , qualifiedIdentRegex
  , regexRegex
  , stringRegex
  , universeRegex
  )
import Thena.Language.Regex (Regex)

-- | The nonterminal a @surface@ region parses at.
surfaceHead :: String
surfaceHead = "surface term"

-- | **What the contents of a @surface@ region may be**: a term, or one with an
-- ascription on it.
--
-- Exported because the rule for @surface\`…\`@ itself is built where the other
-- tagged literals are ("Thena.Language.Instral"), and the fact that ascription
-- is allowed at the top of a region and nowhere recursive belongs here with the
-- rest of the grammar rather than there.
surfaceContents :: [[E.Symbol]]
surfaceContents = [ [E.Nonterminal surfaceHead] , ascribedAt surfaceHead ]

ascribedAt :: String -> [E.Symbol]
ascribedAt h = [E.Nonterminal h, E.Literal ":", E.Nonterminal h]

-- | **What needs no parentheses in a surface term**, and the one rung of Happy's
-- ladder worth keeping: @elim@'s motive and target take exactly one of these, so
-- a flat term there would accept @elim d (a) m x (b) (c) t@, which Happy refuses.
--
-- Exported because "Thena.Language.Instral" contributes the @do@ block at this
-- head — the block's productions are @instral@'s statement ones, and that module
-- is where the statement head lives.
surfaceAtomHead :: String
surfaceAtomHead = "surface atom"

-- | The nonterminal a @core@ region parses at — the development calculus's own
-- grammar, which is what @core\`…\`@ and @:core@ read.
coreHead :: String
coreHead = "core term"

-- ---------------------------------------------------------------------------
-- The surface language

-- | Every production of the surface language, for the object languages loaded
-- now.
--
-- **The tagged term literals are contributed here from what is installed**, not
-- named in a list — which is the whole of what lets this exist before any object
-- language does. A @language LC@ loaded mid-session is writable inside a
-- @surface@ region immediately, with nothing rebuilt.
surfaceRules :: [Grammar] -> InScope -> [E.Rule]
surfaceRules gs sc = concat
  [ term, atom, arguments, terms, binders, piBinders, name, names, bindings ]
  where
    t = surfaceHead
    atomH = surfaceAtomHead
    argumentsH = "surface arguments"
    termsH = "surface terms"
    bindersH = "surface binders"
    piBindersH = "surface pi binders"
    namesH = "surface names"
    nameH = "surface name"
    bindingsH = "surface bindings"

    -- | **A position where @Surface\/Parser.y@ writes @Term@ rather than
    -- @Arrowed@**: a term, or one with an ascription on it. Spelled out at each
    -- such position instead of being a production of the term, because
    -- @Term : Arrowed ':' Arrowed@ **does not nest** — @x : y : z@ is not a
    -- surface term — and a recursive @t -> t ':' t@ would offer a @:@ that
    -- cannot run.
    --
    -- There are five such positions and they are marked with this, so the one
    -- fact lives in one place: inside parentheses, inside an implicit argument,
    -- a binder's type, a binding's value and its type, and the contents of a
    -- region.
    ascribed = [ [nt t], ascribedAt t ]

    -- Both alternatives of every body that holds an ascribable position.
    at h nm before after =
      [ rule nm' h (before ++ body ++ after)
      | (nm', body) <- zip [nm, nm ++ " ascribed"] ascribed
      ]

    -- **Flat and ambiguous on purpose.** Application, the arrow and the binder
    -- forms are all productions of one head; the chart keeps every reading and
    -- nothing here ever parses, so the readings cost nothing and the grammar
    -- says what the language is rather than how an LALR table is built.
    term =
      [ rule "atom" t [nt atomH]
      , rule "application" t [nt t, nt atomH]
      , rule "arrow" t [nt t, lit "->", nt t]
      ] ++
      at t "implicit application" [nt t, lit "{"] [lit "}"] ++
      [ rule ("lambda" ++ w) t [lit l, nt bindersH, lit "->", nt t]
      | (w, l) <- [("", "λ"), (" ascii", "\\")]
      ] ++
      [ rule ("forall" ++ w) t [lit l, nt piBindersH, lit "->", nt t]
      | (w, l) <- [("", "∀"), (" word", "forall")]
      ] ++
      [ rule "let" t [lit "let", lit "{", nt bindingsH, lit "}", lit "in", nt t] ]

    atom =
      [ rule "name" atomH [nt nameH]
        -- **@?foo@ is two tokens and not one** — @?@ cannot start an identifier,
        -- so the lexer hands over @TQuery@ and then the name, and @? foo@ with a
        -- space is a surface hole too.
        --
        -- **A hole's name is not qualified**: it names a component of the
        -- development, whose scope has no namespaces.
      , rule "hole" atomH [lit "?", scan "name" identRegex]
      , rule "universe" atomH [scan "universe" universeRegex]
      , rule "open universe" atomH [lit "Type"]
      , rule "string" atomH [scan "string" stringRegex]
      , rule "char" atomH [scan "char" charRegex]
      , rule "int" atomH [scan "int" numberRegex]
      , rule "regex" atomH [scan "regex" regexRegex]
      , rule "eliminator" atomH
          [ lit "elim", nt nameH, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      ] ++
      at atomH "parenthesised" [lit "("] [lit ")"] ++
      literals atomH gs sc

    -- @Terms@ may be empty in @Surface\/Parser.y@ and the chart has no empty
    -- rules, so the parenthesised group is spelled twice.
    arguments =
      [ rule "none" argumentsH [lit "(", lit ")"]
      , rule "some" argumentsH [lit "(", nt termsH, lit ")"]
      ]

    terms =
      [ rule "one" termsH [nt atomH]
      , rule "more" termsH [nt termsH, nt atomH]
      ]

    -- **A λ's binder need not be annotated and a ∀'s must be**, which is the
    -- difference between @LamBinder@ and @PiBinder@ and the reason there are two
    -- runs.
    --
    -- **The run has no singular head beside it** — his instruction, 2026-10-02,
    -- after seeing @[core binder]@ and @[core binders]@ offered side by side:
    -- the singular and the plural of one word in a dropdown read as a bug.
    -- 'runOf' spells each form twice instead, which costs rules and no names.
    binders = runOf bindersH
      ( [ [scan "name" identRegex]
        , [lit "{", nt namesH, lit "}"]
        ] ++ typedForms )

    piBinders = runOf piBindersH typedForms

    typedForms =
      [ [lit "("] ++ body ++ [lit ":"] ++ asc ++ [lit ")"] | (body, asc) <- forms ] ++
      [ [lit "{"] ++ body ++ [lit ":"] ++ asc ++ [lit "}"] | (body, asc) <- forms ]
      where forms = [ ([nt namesH], a) | a <- ascribed ]

    -- **A name may be qualified** (MS10): the path's steps, glued by the
    -- reserved dot. The binder positions below are deliberately not — a binder
    -- is a word in the development's own scope, which has no namespaces.
    name = [ rule "word" nameH [scan "name" qualifiedIdentRegex] ]

    names =
      [ rule "one" namesH [scan "name" identRegex]
      , rule "more" namesH [nt namesH, scan "name" identRegex]
      ]

    bindings = runWith bindingsH (lit ";")
      ( [ [scan "name" identRegex, lit "="] ++ a | a <- ascribed ] ++
        [ [scan "name" identRegex, lit ":", nt t, lit "="] ++ a | a <- ascribed ] )

-- ---------------------------------------------------------------------------
-- The development calculus

-- | Every production of the development calculus's grammar — @core\`…\`@ and
-- every @:@-command that reads one.
--
-- **Flat, like the surface, and with no ascription to spell out**: the
-- development calculus has none. The one extra head is the atom, for @elim@'s
-- slots and for the parenthesised runs.
coreRules :: [Grammar] -> InScope -> [E.Rule]
coreRules gs sc = concat
  [ term, atom, atoms, arguments, binders, name, qname, levels, levelArgs
  , constraint ]
  where
    c = coreHead
    atomH = "core atom"
    atomsH = "core atoms"
    argumentsH = "core arguments"
    bindersH = "core binders"
    nameH = "core name"
    qnameH = "core qualified name"
    levelsH = "core levels"
    levelArgsH = "core level arguments"
    constraintH = "core constraint"

    term =
      [ rule "atom" c [nt atomH]
      , rule "application" c [nt c, nt atomH]
      , rule "arrow" c [nt c, lit "->", nt c]
      ] ++
      [ rule ("lambda" ++ w) c [lit l, nt bindersH, lit "->", nt c]
      | (w, l) <- [("", "λ"), (" ascii", "\\")]
      ] ++
      [ rule ("forall" ++ w) c [lit l, nt bindersH, lit "->", nt c]
      | (w, l) <- [("", "∀"), (" word", "forall")]
      ] ++
      [ -- **A @let@ in the development calculus always carries its type**, where
        -- the surface's is optional: there is nothing here to infer it with.
        rule "let" c [lit "let", nt nameH, lit "=", nt c, lit ":", nt c, lit "in", nt c]
      , rule "claim" c [lit "let", lit "?", nt nameH, lit ":", nt c, lit "in", nt c]
      , rule "guess" c
          [ lit "let", lit "?", nt nameH, lit ":", nt c, lit "≐"
          , lit "(", nt c, lit ")", lit "in", nt c
          ]
      , rule "pending" c [nt constraintH, lit "▸", nt c]
      , rule "eliminator" c
          [ lit "elim", nt qnameH, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      , rule "eliminator at" c
          [ lit "elim", nt qnameH, nt levelArgsH, nt argumentsH, nt atomH
          , nt argumentsH, nt argumentsH, nt atomH
          ]
      ]

    atom =
      [ rule "name" atomH [nt qnameH]
      , rule "at level" atomH [nt qnameH, nt levelArgsH]
      , rule "universe" atomH [scan "universe" universeRegex]
      , rule "open universe" atomH [lit "Type"]
      , rule "string" atomH [scan "string" stringRegex]
      , rule "char" atomH [scan "char" charRegex]
      , rule "int" atomH [scan "int" numberRegex]
      , rule "regex" atomH [scan "regex" regexRegex]
      , rule "parenthesised" atomH [lit "(", nt c, lit ")"]
      ] ++ literals atomH gs sc

    atoms =
      [ rule "one" atomsH [nt atomH]
      , rule "more" atomsH [nt atomsH, nt atomH]
      ]

    arguments =
      [ rule "none" argumentsH [lit "(", lit ")"]
      , rule "some" argumentsH [lit "(", nt atomsH, lit ")"]
      ]

    -- **Always annotated**: a binder with no type is a parse error here rather
    -- than a hole (@.claude\/spec\/interface.md@ §2.6). One head, no singular beside
    -- the plural — see 'runOf'.
    binders = runOf bindersH [ [lit "(", nt nameH, lit ":", nt c, lit ")"] ]

    -- **No splice production**, and the phase's own test is why: @}$@ is emitted
    -- by the /region/ scanner, so a splice lexes inside @core\`…\`@ and not in a
    -- bare @:core@ argument, and one rule set serves both. @AGENDA.md@ 96.
    -- **And a qualified one** (MS10), which is what a generated name now is:
    -- @Nat.elim@, @Term.noConfusion@. The rule is left-recursive so a path of
    -- any depth reads.
    -- **A binder's name is a word; a reference's may be qualified** (MS10).
    -- Two nonterminals, because the running parser draws the same line:
    -- @let Nat.elim = …@ binds nothing, and an advising grammar that offered it
    -- would be wider than the parser — the one thing these may never be.
    name = [ rule "word" nameH [scan "name" identRegex] ]

    qname = [ rule "name" qnameH [scan "name" qualifiedIdentRegex] ]

    levels =
      [ rule "one" levelsH [scan "int" numberRegex]
      , rule "more" levelsH [nt levelsH, scan "int" numberRegex]
      ]

    levelArgs =
      [ rule "none" levelArgsH [lit "{", lit "}"]
      , rule "some" levelArgsH [lit "{", nt levelsH, lit "}"]
      ]

    constraint =
      [ rule "in context" constraintH
          [ nt bindersH, lit "⊢", nt c, lit "≟", nt c, lit ":", nt c ]
      , rule "closed" constraintH
          [ lit "⊢", nt c, lit "≟", nt c, lit ":", nt c ]
      ]

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
--
-- **The body is looked up by the production's full name** (MS10 phase 253) — see
-- 'Thena.Language.Instral.literalProductions', which had the same stale lookup.
-- **THE TAG SHORTENS AND THE KEY DOES NOT — MS12 PHASE 313.** A module's
-- declarations live under the module's own name from that phase, so the key of
-- a language in @examples\/Stlc01Syntax.thena@ is
-- @examples.Stlc01Syntax.LC@ — and with the key as the opening literal the only
-- way to write an object literal inside a surface region was to type the whole
-- path. 'Thena.Language.Grammar.tagText' is the walk a written tag already
-- resolves by, and everything the rule points into stays dotted.
-- 'Thena.Language.Instral.literalProductions' is the same pair, for a REPL line.
literals :: String -> [Grammar] -> InScope -> [E.Rule]
literals head' gs sc = concat
  [ [ E.Rule (head' ++ " " ++ l) head' [E.Literal (t ++ "`"), E.Nonterminal l, fence] []
    , E.Rule (head' ++ " empty " ++ l) head' [E.Literal (t ++ "`"), fence] []
    ] ++
    [ E.Rule (head' ++ " " ++ l ++ " " ++ p) head'
        ( E.Literal (t ++ "[" ++ p ++ "]`")
            : maybe [] (productionBody gs) (productionRule gs l p) ++ [fence] ) []
    | p <- productionNames gs l
    ]
  | l <- languageNames gs
  , let t = tagText gs sc (nameFromText l)
  ]
  where fence = E.Literal "`"

-- | **A run of one or more of something, as one head.**
--
-- @h -> f@ and @h -> h f@ for each form @f@, so there is no singular head beside
-- the plural — **his instruction, 2026-10-02**: @[core binder]@ and
-- @[core binders]@ offered together are the singular and the plural of one word,
-- which reads as a bug rather than as help. Each form is spelled twice, which
-- costs rules and no names.
runOf :: String -> [[E.Symbol]] -> [E.Rule]
runOf h = run h []

-- | 'runOf' with a separator between the elements — a @let@'s bindings.
runWith :: String -> E.Symbol -> [[E.Symbol]] -> [E.Rule]
runWith h sep = run h [sep]

run :: String -> [E.Symbol] -> [[E.Symbol]] -> [E.Rule]
run h sep forms = concat
  [ [ rule (show k) h form
    , rule (show k ++ " more") h (E.Nonterminal h : sep ++ form)
    ]
  | (k, form) <- zip [0 :: Int ..] forms
  ]

-- | A rule, named after what it is and headed by the thing it builds.
--
-- **The name carries the head**, so a tree node says @surface term arrow@ rather
-- than @arrow@ — there are two @application@s and two @let@s across the two
-- grammars and a name is what a 'Thena.Language.Earley.Tree' records.
rule :: String -> String -> [E.Symbol] -> E.Rule
rule nm h body = E.Rule (h ++ " " ++ nm) h body []

lit :: String -> E.Symbol
lit = E.Literal

nt :: String -> E.Symbol
nt = E.Nonterminal

scan :: String -> Regex -> E.Symbol
scan = E.Scan
