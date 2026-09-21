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
| `01-stlc-syntax.thena` | A token class; `Ty` and `LC` declared as grammars; terms written in their own notation; `${…}` splices; `LC[var]`; generated substitution, with capture avoidance, simultaneity and free variables proved by `refl` |
| `02-contexts.thena` | A `context` block; its lookup relation `x : T ∈ Γ`; lookups proved with `Ctx-here` and `Ctx-there`; a disequality `x ≠ f` proved with no axiom; why a shadowed binding cannot be reached |
| `03-typing-and-reduction.thena` | Typing, values and call-by-value reduction as `judgment` blocks in paper notation; a named premise; `E[x->N]` in a rule; typing derivations stated as judgment literals; reduction steps whose right-hand side the kernel computes by substitution, one of them capture-avoiding |
| `04-taking-terms-apart.thena.rules` | A rule base that matches `LC` terms in their own notation (`LC[app]`( ${f} ${a} )``) and builds them (`LC`( ${t} ${t} )``) |
| `05-grouping-by-splicing.thena` | A language with no parentheses, where `f a b` reads two ways; a splice as a group (`` Ex`${Ex`f a`} b` ``), to any depth; a name or a computation spliced in as a group; why printing is the open half |
| `06-more-judgments.thena` | Many steps as a judgment built on `step`, with a two-step run; the annotated tier (`rule … where ∀ … ->`) ranging over a derivation; a swap by simultaneous substitution with Redex-style subscripts (`x_1`, `x_2`) beside the sequential version that gets it wrong; a premise continued onto a second line |

## The earlier proofs — TAPL's arithmetic language, by hand

Written in MS4 and MS5, before object languages existed. The language is a
hand-written `data Term`, and the proofs use `elim` throughout. All but the last
two rows are also test fixtures, loaded by path from their own tests; those two
load today, and nothing checks that they keep doing so.

| file | what it is |
|---|---|
| `canonical.thena` | Canonical forms, TAPL 8.3.1. Load first |
| `progress.thena` | Progress, TAPL 8.3.2. After `canonical` |
| `preservation.thena` | Preservation, TAPL 8.3.3. After `canonical` and `progress` |
| `normal.thena` | A value is a normal form. After `canonical` and `progress` |
| `determinacy-surface.thena` | Determinacy, TAPL 3.5.4, in the surface language. **Generated** by `determinacy.py`: regenerate it, never patch it |
| `determinacy-tactics.thena.script` | The same proof driven by tactics. **Generated** too |
| `tier0.thena` | MS4's first checkpoint: a datatype, a function by elimination, a theorem |
| `dependent-index.thena.script`, `products.thena.script` | REPL scripts: elimination over an indexed family, and no-confusion |
| `choice-points.thena.rules` | What a choice point resumes into |
| `trying.thena` | A scratch module, with a `Bool` and two commented-out attempts |

## Loading the series

```
cabal run thena
:load examples/01-stlc-syntax.thena
:load examples/02-contexts.thena
:load examples/03-typing-and-reduction.thena
:load rules rules/standard.thena.rules examples/04-taking-terms-apart.thena.rules
:load examples/05-grouping-by-splicing.thena
:load examples/06-more-judgments.thena
```

A module's declarations stay in scope for the next module loaded in the same
session, and that is the only way one file sees another; there are no imports
yet. A rule file is read with the grammars already loaded, so the modules come
first.

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

thena spine> :show Ctx-in
data Ctx-in : String -> Ty -> Ctx -> Type₀ where
  { Ctx-here : ∀ (Γ : Ctx) (x : String) (T : Ty) -> Ctx-in x T (extend Γ x T)
  ; Ctx-there : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty) -> (Eq {0} String x x' -> Empty {0}) -> Ctx-in x T Γ -> Ctx-in x T (extend Γ x' T') }

thena spine> :parse typing · ⊢ ( λ x : ι . x ) : ( ι -> ι )
typing(empty, abs(x, base, var(x)), arrow(base, base))

thena spine> :show halts
data halts : LC -> Type₀ where
  { H-value : ∀ (M : LC) -> value M -> halts M
  ; H-step : ∀ (M : LC) (M' : LC) -> step M M' -> halts M' -> halts M }

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

- **Preservation for STLC.** That is phase 109, the milestone's goal.
- **Terms printed in their own notation.** `:show` prints
  `app (abs "x" base (var "x")) …`, not `` LC`( ( λ x : ι . x ) … )` ``. That is
  not wired in yet.
- **Loading `02` prints one warning**, that `Ctx-in` gets no no-confusion
  lemma, **`03` prints two**, for `typing` and `step`, and **`06` three**: a
  constructor whose premise's type mentions an earlier argument gets none, and
  every rule with a premise is such a constructor. They are accurate and harmless here.

