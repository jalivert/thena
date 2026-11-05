# Example programs

Real Thena programs. **Every file here loads as it stands**, and together they
show what the language can do at this point. There are two sets.

## The object-language series — numbered, read in order

Written for MS6, and extended as each feature lands. Each file builds on the
ones before it. **A test loads every numbered file in order**
(`Thena.ExamplesTests`), so if one stops loading the suite fails, and the fix is
to the file.

| file | what it shows |
|---|---|
| `Stlc01Syntax.thena` | A token class; `Ty` and `LC` declared as grammars; terms written in their own notation; `${…}` splices; `LC[var]`; generated substitution, with capture avoidance, simultaneity and free variables proved by `refl` |
| `Stlc02Contexts.thena` | A `context` block; its lookup relation `x : T ∈ Γ`; lookups proved with `extend-here` and `extend-there-extend`; a disequality `x ≠ f` proved with no axiom; why a shadowed binding cannot be reached |
| `Stlc03TypingAndReduction.thena` | Typing, values and call-by-value reduction as `judgment` blocks in paper notation; a named premise; `E[x->N]` in a rule; typing derivations stated as judgment literals; reduction steps whose right-hand side the kernel computes by substitution, one of them capture-avoiding |
| `Stlc04TakingTermsApart.thena.rules` | A rule base that matches `LC` terms in their own notation (`LC[app]`( ${f} ${a} )``) and builds them (`LC`( ${t} ${t} )``) |
| `Stlc05GroupingBySplicing.thena` | A language with no parentheses, where `f a b` reads two ways; a splice as a group (`` Ex`${Ex`f a`} b` ``), to any depth; a name or a computation spliced in as a group; the splices `09` shows the printer writing for itself |
| `Stlc06MoreJudgments.thena` | Many steps as a judgment built on `step`, with a two-step run; the annotated tier (`rule … where ∀ … ->`) ranging over a derivation; a swap by simultaneous substitution with Redex-style subscripts (`x_1`, `x_2`) beside the sequential version that gets it wrong; a premise continued onto a second line |
| `Stlc07Preservation.thena` | **Preservation for STLC, for closed terms** — the milestone's goal. A proof about the substitution Thena generated in 01, following its `String.dec` decisions: weakening, free variables, why no binder is renamed, the substitution lemma over a whole map, inversion, preservation. Ends by typing a reduct through `preservation` |
| `Stlc08PreservationByTactics.thena.script` | **The same proof again, by tactics**, as a script of command lines: each lemma a `:theorem`, its inductions and case splits done with `eliminate-core`, the cases filled with `` elaborate surface`…` ``, the β case taken apart by two nested eliminations. Reuses 07's definitions, not its lemmas |
| `Stlc10PreservationAnyContext.thena` | **Preservation for ANY context** — what `07` could not do. An open argument can capture, so the generated substitution renames the binder, and the file **proves** that the minted name is fresh. **Three trusted laws about `String.append` and everything else derived**: associativity, and that a string differs from itself with a `'` appended, with and without more after it. No lengths and no arithmetic — the counting is a `Longer` computed from two lists |
| `Stlc09Printing.thena` | **Terms shown in their own notation** — the other direction from 01. A judgment's statement printed as it reads on paper; a name kept rather than unfolded into what it stands for, in a splice; the splices the printer writes where a grammar groups by splicing, as 05 writes them by hand; a variable spelled like one of the grammar's own terminals, which is fenced where the same position otherwise is not; reading it all back with `:core` |

## System F-sub — `poplmark/`, its own set

**`examples/poplmark/` is loaded in a FRESH session**, not with the series above: it
declares its own `Ty`, and two languages of one name cannot be installed at once. Six
files, each stating what it imports, answering the POPLMark challenge's problem 1A — transitivity of
subtyping for System F-sub. `examples/poplmark/README.md` is the account: what is proved,
the one premise added to the paper's rules and why, and the one step that is left over
with its refutation.

## The earlier proofs — TAPL's arithmetic language, by hand

Written in MS4 and MS5, before object languages existed. The language is a
hand-written `data Term`. **The generated pair still appeals to `elim`
throughout; the hand-written ones were rewritten as splits in MS9**, so the two
styles sit side by side here and `DeterminacySurface.thena` against
`DeterminacyPatterns.thena` is the same theorem in both. All but the last two
rows are also test fixtures, loaded by path from their own tests; those two load
today, and nothing checks that they keep doing so.

**Every file here is named after the module it declares, and its header is its
path** — `examples/Canonical.thena` declares `examples.Canonical`. A file whose
path held a hyphen could be reached by no module name at all, so it could neither
be imported nor state what it imports; that is why none of them does now.

| file | what it is |
|---|---|
| `Canonical.thena` | Canonical forms, TAPL 8.3.1. Imports nothing |
| `Progress.thena` | Progress, TAPL 8.3.2. Imports `Canonical` |
| `Preservation.thena` | Preservation, TAPL 8.3.3. Imports `Canonical` and `Progress` |
| `Normal.thena` | A value is a normal form. Imports `Canonical` and `Progress` |
| `DeterminacySurface.thena` | Determinacy, TAPL 3.5.4, in the surface language. **Generated** by `determinacy.py`: regenerate it, never patch it |
| `DeterminacyTactics.thena.script` | The same proof driven by tactics. **Generated** too |
| `DeterminacyPatterns.thena` | The same theorem, with **every one of its lemmas** by dependent pattern matching — no `elim` and no no-confusion anywhere. Its header says why a recursion across a generalising split is written exactly like any other one, and nothing in it binds an induction hypothesis. Read it beside `DeterminacySurface.thena` |
| `Tier0.thena` | MS4's first checkpoint: a datatype, a function by elimination, a theorem |
| `DependentIndex.thena.script`, `Products.thena.script` | REPL scripts: elimination over an indexed family, and no-confusion |
| `ChoicePoints.thena.rules` | What a choice point resumes into |
| `Trying.thena` | A scratch module, with a `Bool` and two commented-out attempts |

## Loading the series

**Every file in the series states what it depends on**, so any one of them loads
on its own and brings its prefix with it:

```
cabal run thena
:load examples/Stlc07Preservation.thena
```

For the whole series, `10`, `09` and `06` import every other surface module
between them; the rule base states its own dependency too, and the script is a
list of commands, so it goes last:

```
:load examples/Stlc10PreservationAnyContext.thena
:load examples/Stlc09Printing.thena
:load examples/Stlc06MoreJudgments.thena
:consult examples/Stlc04TakingTermsApart.thena.rules
:load examples/Stlc08PreservationByTactics.thena.script
```

A module is loaded once however many files reach it, so loading `09` after `10`
re-reads `01`, `02` and `03` not at all. The script is the one piece that still
needs the session to hold what it reuses: `import` at the prompt is what would
let it say so.

## Things to try once they are loaded

```
thena spine> :show LC
data LC : Type₀ where
  { var : String -> LC
  ; abs : String -> Ty -> LC -> LC
  ; app : LC -> LC -> LC }

thena spine> :parse LC ( λ x : ι . ( x x ) )
abs(x, base, app(var(x), var(x)))

thena spine> :parse LC ( f x y )
in LC`( f x y )`: unexpected 'y' at character 7, expecting )

thena spine> :show extend-in
data extend-in : String -> Ty -> Ctx -> Type₀ where
  { extend-here : ∀ (Γ : Ctx) (x : String) (T : Ty) -> extend-in`${x} : ${T} ∈ ${Γ} , ${x} : ${T}`
  ; extend-there-extend : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty) -> (Eq {0} String x x' -> Empty {0}) -> extend-in`${x} : ${T} ∈ ${Γ}` -> extend-in`${x} : ${T} ∈ ${Γ} , ${x'} : ${T'}` }

thena spine> :parse typing · ⊢ ( λ x : ι . x ) : ( ι -> ι )
typing(empty, abs(x, base, var(x)), arrow(base, base))

thena spine> :show halts
data halts : LC -> Type₀ where
  { H-value : ∀ (M : LC) -> value`${M} value` -> halts`${M} ⇓`
  ; H-step : ∀ (M : LC) (M' : LC) -> step`${M} --> ${M'}` -> halts`${M'} ⇓` -> halts`${M} ⇓` }

thena spine> :parse Ex f a b
in Ex`f a b`: this term parses two ways, as juxt(ref(f), juxt(ref(a), ref(b))) and as juxt(juxt(ref(f), ref(a)), ref(b))

thena spine> describe LC`( λ x : ι . x )`
a function binding x

thena spine> :theorem w : LC
proving w : LC
thena spine> self-apply LC`( λ x : ι . x )`
thena spine> qed
w : LC   ∎
```

`:parse LC` with no text enters an interactive mode, where Tab asks the parser
what can come next. Leave it with `:done`.

## What these do not show yet, and why

- **Loading `02` prints one warning**, that `extend-in` gets no no-confusion
  lemma, **`03` prints two**, for `typing` and `step`, and **`06` three**: a
  constructor whose premise's type mentions an earlier argument gets none, and
  every rule with a premise is such a constructor. They are accurate and harmless here.

