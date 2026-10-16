# Thena

[![Haskell CI](https://github.com/jalivert/thena/actions/workflows/haskell.yml/badge.svg?branch=main)](https://github.com/jalivert/thena/actions/workflows/haskell.yml)

Thena is an interactive proof assistant for the metatheory of programming
languages. You describe a language as a collection of inductive families — its
syntax, its values, its reduction and typing relations — and prove theorems
about it interactively, one step at a time.

The proof engine re-implements the *development calculus* of Conor McBride's
1999 doctoral thesis, *Dependently Typed Functional Programs and their Proofs*
(the system he called OLEG). Thena follows the thesis on the type theory and
departs from it on interaction, where it takes its own approach.

> **Status.** Research prototype, under active development. The type theory, the
> proof engine, a surface language and a rule-based elaborator are implemented
> and covered by around 1,300 tests. The graphical interface and the
> mixed-initiative proof search described below are in progress. The interface
> today is a REPL.

## What is different about it

Two commitments shape the system.

**One mechanism.** Elaboration — turning surface syntax into fully explicit core
terms — and proof search are not separate subsystems. They are the same
rule-directed engine, running over the same rule base, with the same
backtracking and the same choice points. A rule fires when its head matches the
current goal, whether that goal came from checking a definition or from a step
in a proof.

**The logic lives in user space.** The rules that drive elaboration and search
are an ordinary text file, loaded at startup, written in a small readable
language — not compiled into the binary. The whole elaborator is a single rule
with one clause per surface construct, plus three short helper rules. Two
clauses, in full:

```
-- E⟦x⟧ — a bare name: resolve it, fill the goal, discharge it.
rule elaborate t :- when focus-is-hole (surface-is-name t)
  then w = surface-name t
     ; x = resolve-name w
     ; fill x
     ; solve

-- E⟦\ x => e⟧ — introduce the binders, elaborate the body, discharge.
rule elaborate t :- when focus-is-hole (surface-is-lambda t)
  then h = here
     ; prim-attack
     ; call intro-binders t
     ; into
     ; call enter-binders t
     ; b = lambda-body t
     ; call elaborate b
     ; goto h
     ; solve
```

A reader — a student, a researcher, a curious user — can open that file, follow
it, and change it. This is deliberate. It makes the type theory and the search
strategy something you can inspect and adjust rather than something you take on
trust, and it is what we mean by calling Thena a proof assistant built for
learning as much as for use.

## The intended way of working

The usual interaction with a tactic-based prover is: the user lays out the
structure of the proof by hand, then invokes an automation tactic to close the
goals that remain. Thena is being built to support the reverse. The assistant
attempts the proof itself, using a simple and legible search, and stops to ask
the user only at a step that needs a human decision — which induction to do,
which hypothesis to use, which lemma to bring in. The aim is to make the amount
of automation a continuous choice rather than a fixed line between "by hand" and
"automatic", and to let a person and an automated agent share the work on a
proof in a way that stays inspectable throughout.

## A look at it

`cabal run thena` opens a REPL with a small prelude loaded. Proofs over the
development calculus are explicit sequences of small steps:

```
thena spine> :theorem id : forall (A : Type0) -> A -> A
proving id : ∀ (A : Type₀) -> A -> A
thena spine> attack
thena spine> intro
thena spine> intro
thena spine> :show
▶ let ? id : ∀ (A : Type₀) -> A -> A ≐ (
    λ (A : Type₀) ->
    λ (_ : A) ->
    let ? id1 : A in
    id1
  ) in
  id
thena spine> into
thena spine> along
thena spine> along
thena spine> try-core ⌜ _ ⌝
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
id : ∀ (A : Type₀) -> A -> A   ∎
```

`qed` re-checks the finished term with an independent kernel before admitting
it. If it does not check, nothing is admitted.

## Examples

Thena's developments live in [`examples/`](examples/README.md) — every file
loads as it stands, and [`examples/README.md`](examples/README.md) is the
file-by-file index. There are three sets, each with its own load order. Thena
has no module imports yet: globals declared by one file stay in scope for the
next loaded in the same session, so "load in order" means what it says.

### 1. Type safety for TAPL's arithmetic language — by hand

The earliest proofs, written before object languages existed. The language is
the untyped arithmetic of Pierce's *Types and Programming Languages*, chapter 3
— a hand-written `data Term`, a numeric-value predicate, and a ten-rule
small-step relation — plus the simply-typed layer of TAPL chapter 8. The proofs
use `elim` throughout, and all but two files are also test fixtures, so the
suite fails if one stops loading.

| theorem | file | statement |
|---|---|---|
| determinacy, TAPL 3.5.4 | [`examples/determinacy-surface.thena`](examples/determinacy-surface.thena) | `determinacy : forall (t t1 : Term) -> Step t t1 -> forall (t2 : Term) -> Step t t2 -> Eq Term t1 t2` |
| canonical forms, TAPL 8.3.1 | [`examples/canonical.thena`](examples/canonical.thena) | `canonicalBool : forall (v : Term) -> Value v -> HasType v bool -> Or (Eq Term v true) (Eq Term v false)`, and `canonicalNat` for `nat` |
| progress, TAPL 8.3.2 | [`examples/progress.thena`](examples/progress.thena) | `progress : forall (t : Term) (T : Ty) -> HasType t T -> Or (Value t) (Steps t)` |
| preservation, TAPL 8.3.3 | [`examples/preservation.thena`](examples/preservation.thena) | `preservation : forall (t t' : Term) -> Step t t' -> forall (U : Ty) -> HasType t U -> HasType t' U` |
| exclusivity | [`examples/normal.thena`](examples/normal.thena) | `valueNoStep : forall (v : Term) -> Value v -> forall (u : Term) -> Step v u -> Empty` — a value takes no step, so the disjunction `progress` returns is a real case split |

The determinacy proof is **generated** (by
[`examples/determinacy.py`](examples/determinacy.py) — regenerate it, never
patch it) and exists in two forms: as a program in the surface language
(`determinacy-surface`) and as a tactic-driven script
([`examples/determinacy-tactics.thena.script`](examples/determinacy-tactics.thena.script)).
The canonical-forms proof beside it is a third of the size and **written by
hand**. Load the safety chain in order:

```
cabal run thena
thena spine> :load examples/canonical.thena
thena spine> :load examples/progress.thena
thena spine> :load examples/preservation.thena
```

### 2. Preservation for STLC — as an object language

The numbered series
([`01`](examples/01-stlc-syntax.thena)–[`10`](examples/10-preservation-any-context.thena))
declares STLC itself — syntax, contexts, typing, and call-by-value reduction in
paper notation — then proves preservation about the substitution Thena
generates. This is the current showcase: grammars with binders, splices,
judgment blocks, capture-avoiding substitution proved by `refl`, and a rule
base that matches object terms in their own notation.

- [`01-stlc-syntax.thena`](examples/01-stlc-syntax.thena) — `Ty` and `LC`
  declared as grammars; terms written ``LC`( λ x : ι . x )` ``; generated
  substitution with capture avoidance proved by `refl`.
- [`02-contexts.thena`](examples/02-contexts.thena) — a `context` block, its
  lookup relation `x : T ∈ Γ`, and lookups proved with `extend-here` /
  `extend-there-extend`.
- [`03-typing-and-reduction.thena`](examples/03-typing-and-reduction.thena) —
  typing, values, and reduction as `judgment` blocks; typing derivations stated
  as judgment literals.
- [`04-taking-terms-apart.thena.rules`](examples/04-taking-terms-apart.thena.rules)
  — a rule base matching `LC` terms in their own notation.
- [`05-grouping-by-splicing.thena`](examples/05-grouping-by-splicing.thena) and
  [`06-more-judgments.thena`](examples/06-more-judgments.thena) — splices,
  multi-step judgments, the annotated tier.
- [`07-preservation.thena`](examples/07-preservation.thena) — **preservation
  for closed terms**, the series' goal:
  `preservation : forall (M : LC) (M1 : LC) (T : Ty) (d : typing empty M T) (s : step M M1) -> typing empty M1 T`,
  via weakening, the substitution lemma, and inversion.
- [`08-preservation-by-tactics.thena.script`](examples/08-preservation-by-tactics.thena.script)
  — **the same proof by tactics**: each lemma a `:theorem`, inductions and case
  splits with `eliminate-core`, cases filled with `elaborate ⟨ … ⟩`.
- [`10-preservation-any-context.thena`](examples/10-preservation-any-context.thena)
  — **preservation for any context**:
  `preservationAny : forall (G : Ctx) (M : LC) (M1 : LC) (T : Ty) (d : typing G M T) (s : step M M1) -> typing G M1 T`.
  An open argument can capture, so the generated substitution renames the
  binder, and the file **proves** that the name it mints is fresh — from three
  trusted laws about `appendString`, with no arithmetic anywhere in it.
- [`09-printing.thena`](examples/09-printing.thena) — terms shown in their own
  notation, the printer writing the splices `05` writes by hand.

```
cabal run thena
thena spine> :load examples/01-stlc-syntax.thena
thena spine> :load examples/02-contexts.thena
thena spine> :load examples/03-typing-and-reduction.thena
thena spine> :load rules rules/standard.thena.rules examples/04-taking-terms-apart.thena.rules
thena spine> :load examples/05-grouping-by-splicing.thena
thena spine> :load examples/06-more-judgments.thena
thena spine> :load examples/07-preservation.thena
thena spine> :load examples/08-preservation-by-tactics.thena.script
thena spine> :load examples/09-printing.thena
```

### 3. Transitivity for System F-sub — POPLMark 1A

[`examples/poplmark/`](examples/poplmark/README.md) answers problem **1A** of
the POPLMark challenge (Aydemir et al., *Mechanized Metatheory for the Masses*,
2005): transitivity of subtyping for pure System F-sub. Six files, read in
order — syntax, contexts, well-formedness, subtyping, typing, transitivity —
with [`examples/poplmark/README.md`](examples/poplmark/README.md) as the
account. **Load these in a fresh session**: the series above declares its own
`Ty`, and two languages of one name cannot be installed at once.

```
cabal run thena
thena spine> :load examples/poplmark/01-syntax.thena
thena spine> :load examples/poplmark/02-contexts.thena
thena spine> :load examples/poplmark/03-wellformed.thena
thena spine> :load examples/poplmark/04-subtyping.thena
thena spine> :load examples/poplmark/05-typing.thena
thena spine> :load examples/poplmark/06-transitivity.thena
```

What is proved is the mutual induction at the heart of 1A — transitivity and
narrowing together, by induction on the middle type — with everything
kernel-checked:

```
transitivity : forall (wk : forall (Q : Ty) -> Wk Q) (G : Ctx) (S Q T : Ty)
                 (d1 : sub G S Q) (d2 : sub G Q T) -> sub G S T
narrowing    : forall (wk : forall (Q : Ty) -> Wk Q) (G : Ctx) (Xn : String) (Q : Ty) (D : Ctx) ...
                 -> sub (append (bindTy G Xn P) D) M N
```

The `wk` hypothesis is plain weakening between well-formed contexts, used in
exactly one case (narrowing's `SA-Trans-TVar`). It is stated openly as a
hypothesis because it is **false** — `06` closes with `wkIsFalse`, a refutation
showing the obstruction is the renaming α-equivalence exists to take, which
nominal Thena does not have. The README in that directory works the
counterexample. One premise was added to the paper's rules (`SA-All` requires
`⊢ Γ , X <: T1 ok`); everything else is the paper's, unchanged.

## Building

Requires GHC (with `base` 4.21), Cabal, and `alex` + `happy` (resolved
automatically by Cabal).

```
cabal build
cabal test
cabal run thena
```

`:help` lists the REPL commands. `docs/LANGUAGES.md` says what can be written
where. `docs/MANUAL.md` is the reference, with worked
sessions and an honest account of what the system can and cannot currently do.

## Layout

| path | |
|---|---|
| `src/` | the implementation — core calculus, engine, elaborator, parser, kernel |
| `rules/standard.thena.rules` | the rule base: elaboration and search, in full |
| `prelude/prelude.thena` | the standard prelude, itself a surface module |
| `examples/` | worked developments, including the determinacy proof |
| `docs/MANUAL.md` | the reference manual — worked sessions, captured from the running program |
| `docs/LANGUAGES.md` | what can be written where — the four languages, their fences, and how they embed |
| `DECISIONS.md` | the design decisions, written for readers who know Agda, Coq, Idris or Lean |

## Research context

Thena is developed in the [Programming Languages and Systems
group](https://d3s.mff.cuni.cz/research/programming-languages/) at the Faculty
of Mathematics and Physics, Charles University. It belongs to a line of work
that treats interactive proof as a *programming system* — taking the
environment in which proofs are built, not only the calculus underneath it, as
something to study and design deliberately.

An early description of the interaction model appeared as an extended abstract
at HATRA 2024, *"Don't Call Us, We'll Call You: Towards Mixed-Initiative
Interactive Proof Assistants for Programming Language Theory."* A tutorial paper
on the core system is in preparation.

## Development

Thena is implemented with the assistance of an AI coding tool (Claude). The
design is directed by the authors, and every change is planned, reviewed and
tested before it lands. How a proof assistant of this shape can be built and
extended in that way is itself one of the project's research interests.

## License

Thena is released under the MIT license. See [`LICENSE`](LICENSE).
