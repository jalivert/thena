# Example programs

Real Thena programs, written to show **what the language can do right now**.
Each file loads as it stands, and the files grow as features land. Read them in
order, since each one builds on the one before.

The older `examples/` directory holds MS4-era proofs (`canonical`, `progress`,
`preservation`, `normal`) over a hand-written TAPL language. The files here use
the object-language features instead: grammars, notation, contexts, and
generated substitution.

## The files

| file | what it shows |
|---|---|
| `01-stlc-syntax.thena` | A token class; `Ty` and `LC` declared as grammars; terms written in their own notation; `${…}` splices; `LC[var]`; generated substitution, with capture avoidance, simultaneity and free variables proved by `refl` |
| `02-contexts.thena` | A `context` block; its lookup relation `x : T ∈ Γ`; lookups proved with `Ctx-here` and `Ctx-there`; a disequality `x ≠ f` proved with no axiom; why a shadowed binding cannot be reached |
| `03-typing-and-reduction.thena` | Typing, values and call-by-value reduction as ordinary inductive families; typing derivations; reduction steps whose right-hand side the kernel computes by substitution, one of them capture-avoiding |
| `04-taking-terms-apart.thena.rules` | A rule base that matches `LC` terms in their own notation (`LC[app]`( ${f} ${a} )``) and builds them (`LC`( ${t} ${t} )``) |

## Loading them

```
cabal run thena
:load .examples/01-stlc-syntax.thena
:load .examples/02-contexts.thena
:load .examples/03-typing-and-reduction.thena
:load rules rules/standard.thena.rules .examples/04-taking-terms-apart.thena.rules
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

- **`judgment` blocks.** `03` writes `typing` and `step` by hand as `data`,
  which is what a `judgment` block will generate from paper notation. That is
  phase 108.
- **Preservation for STLC.** That is phase 109, the milestone's goal.
- **Terms printed in their own notation.** `:show` prints
  `app (abs "x" base (var "x")) …`, not `` LC`( ( λ x : ι . x ) … )` ``. That is
  not wired in yet.
- **Loading `02` prints one warning**, that `Ctx-in` gets no no-confusion
  lemma. It is accurate and harmless here.

Every file in this directory loads without an error. If one ever stops loading,
the file is out of date and should be fixed, not the check skipped.
