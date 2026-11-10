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
> proof engine, a surface language, a rule-based elaborator and a module system
> are implemented and covered by around 3,300 tests. The graphical interface and
> the mixed-initiative proof search described below are in progress. The
> interface today is the REPL, `cabal run thena`; `cabal run thena-check`
> type-checks files in batch with no terminal, and an experimental terminal UI,
> `cabal run thena-tui`, is being built on a separate track.

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
language — not compiled into the binary. It holds 120 rules, and the elaborator
is one of them: `elaborate`, with a clause per surface construct — 22 of them —
while the rest are the tactics and the helpers they share. Two clauses of
`elaborate`, in full:

```
-- E⟦x⟧ — a bare name: resolve it, fill the goal, discharge it.
elaborate : Surface -> ()
rule elaborate t :- when focus-is-hole (surface-is-name t)
  do w = surface-name t
     ; x = resolve-name w
     ; fill x
     ; solve

-- E⟦\ x => e⟧ — introduce the binders, elaborate the body, discharge. The
-- group is walked by recursion: intro-binders peels one binder off and calls
-- itself on the tail, so the term is its own counter.
rule elaborate t :- when focus-is-hole (surface-is-lambda t)
  do h = here
     ; prim-attack
     ; into
     ; k = here
     ; back
     ; body = call intro-binders t k
     ; goto body
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
thena spine> try-core core`_`
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
id : ∀ (A : Type₀) -> A -> A   ∎
```

`qed` re-checks the finished term with the kernel before admitting it, trusting
nothing the engine recorded along the way. If it does not check, nothing is
admitted. The kernel re-derives the typing itself, but shares its reduction and
conversion code with the elaborator, so it is a separate check and not yet a
separate implementation.

## Examples

Thena's developments live in [`examples/`](examples/README.md) — every file
loads as it stands, and [`examples/README.md`](examples/README.md) is the
file-by-file index. There are three sets, and **every file in all three imports
what it depends on**, so any one of them loads on its own. The three are grouped
by what they show, not by what has to be loaded first.

### 1. Type safety for TAPL's arithmetic language — by hand

The earliest proofs, written before object languages existed. The language is
the untyped arithmetic of Pierce's *Types and Programming Languages*, chapter 3
— a hand-written `data Term`, a numeric-value predicate, and a ten-rule
small-step relation — plus the simply-typed layer of TAPL chapter 8. The four
hand-written proofs are dependent pattern matching, with no `elim` and no
appeal to no-confusion in them; the generated determinacy pair beside them is
`elim` throughout, which is what makes the two readable side by side. All but
two files are also test fixtures, so the suite fails if one stops loading.

| theorem | file | statement |
|---|---|---|
| determinacy, TAPL 3.5.4 | [`examples/DeterminacySurface.thena`](examples/DeterminacySurface.thena), generated and `elim` throughout, beside [`examples/DeterminacyPatterns.thena`](examples/DeterminacyPatterns.thena), the same theorem with every lemma a split | `determinacy : forall (t t1 : Term) -> Step t t1 -> forall (t2 : Term) -> Step t t2 -> Eq Term t1 t2` |
| canonical forms, TAPL 8.3.1 | [`examples/Canonical.thena`](examples/Canonical.thena) | `canonicalBool : forall (v : Term) -> Value v -> HasType v bool -> Or (Eq Term v true) (Eq Term v false)`, and `canonicalNat` for `nat` |
| progress, TAPL 8.3.2 | [`examples/Progress.thena`](examples/Progress.thena) | `progress : forall (t : Term) (T : Ty) -> HasType t T -> Or (Value t) (Steps t)` |
| preservation, TAPL 8.3.3 | [`examples/Preservation.thena`](examples/Preservation.thena) | `preservation : forall (t t' : Term) -> Step t t' -> forall (U : Ty) -> HasType t U -> HasType t' U` |
| exclusivity | [`examples/Normal.thena`](examples/Normal.thena) | `valueNoStep : forall (v : Term) -> Value v -> forall (u : Term) -> Step v u -> Empty` — a value takes no step, so the disjunction `progress` returns is a real case split |

The determinacy proof is **generated** (by
[`examples/determinacy.py`](examples/determinacy.py) — regenerate it, never
patch it) and exists in two forms: as a program in the surface language
(`determinacy-surface`) and as a tactic-driven script
([`examples/DeterminacyTactics.thena.script`](examples/DeterminacyTactics.thena.script)).
The canonical-forms proof beside it is a third of the size and **written by
hand**. The safety chain loads in one line, because each file imports what it
stands on:

```
cabal run thena
thena spine> import examples.Preservation
```

### 2. Preservation for STLC — as an object language

The numbered series
([`01`](examples/Stlc01Syntax.thena)–[`10`](examples/Stlc10PreservationAnyContext.thena))
declares STLC itself — syntax, contexts, typing, and call-by-value reduction in
paper notation — then proves preservation about the substitution Thena
generates. This is the current showcase: grammars with binders, splices,
judgment blocks, capture-avoiding substitution proved by `refl`, and a rule
base that matches object terms in their own notation.

- [`Stlc01Syntax.thena`](examples/Stlc01Syntax.thena) — `Ty` and `LC`
  declared as grammars; terms written ``LC`( λ x : ι . x )` ``; generated
  substitution with capture avoidance proved by `refl`.
- [`Stlc02Contexts.thena`](examples/Stlc02Contexts.thena) — a `context` block, its
  lookup relation `x : T ∈ Γ`, and lookups proved with `extend-here` /
  `extend-there-extend`.
- [`Stlc03TypingAndReduction.thena`](examples/Stlc03TypingAndReduction.thena) —
  typing, values, and reduction as `judgment` blocks; typing derivations stated
  as judgment literals.
- [`Stlc04TakingTermsApart.thena.rules`](examples/Stlc04TakingTermsApart.thena.rules)
  — a rule base matching `LC` terms in their own notation.
- [`Stlc05GroupingBySplicing.thena`](examples/Stlc05GroupingBySplicing.thena) and
  [`Stlc06MoreJudgments.thena`](examples/Stlc06MoreJudgments.thena) — splices,
  multi-step judgments, the annotated tier.
- [`Stlc07Preservation.thena`](examples/Stlc07Preservation.thena) — **preservation
  for closed terms**, the series' goal:
  `preservation : forall (M : LC) (M1 : LC) (T : Ty) (d : typing empty M T) (s : step M M1) -> typing empty M1 T`,
  via weakening, the substitution lemma, and inversion.
- [`Stlc08PreservationByTactics.thena.script`](examples/Stlc08PreservationByTactics.thena.script)
  — **the same proof by tactics**: each lemma a `:theorem`, inductions and case
  splits with `eliminate-core`, cases filled with `` elaborate surface`…` ``.
- [`Stlc10PreservationAnyContext.thena`](examples/Stlc10PreservationAnyContext.thena)
  — **preservation for any context**:
  `preservationAny : forall (G : Ctx) (M : LC) (M1 : LC) (T : Ty) (d : typing G M T) (s : step M M1) -> typing G M1 T`.
  An open argument can capture, so the generated substitution renames the
  binder, and the file **proves** that the name it mints is fresh — from three
  trusted laws about `appendString`, with no arithmetic anywhere in it.
- [`Stlc09Printing.thena`](examples/Stlc09Printing.thena) — terms shown in their own
  notation, the printer writing the splices `05` writes by hand.

**Each file imports what it depends on**, so load whichever one you want and the
ones under it come in with it:

```
cabal run thena
thena spine> import examples.Stlc07Preservation
```

**Every file loads on its own**, so there is no order to get right. For the whole
series, three of the surface modules import everything else between them, the rule
base states its own dependency, and the script states its own imports:

```
thena spine> import examples.Stlc10PreservationAnyContext
thena spine> import examples.Stlc09Printing
thena spine> import examples.Stlc06MoreJudgments
thena spine> consult examples.Stlc04TakingTermsApart
thena spine> :replay examples/Stlc08PreservationByTactics.thena.script
```

### 3. Transitivity for System F-sub — POPLMark 1A

[`examples/poplmark/`](examples/poplmark/README.md) answers problem **1A** of
the POPLMark challenge (Aydemir et al., *Mechanized Metatheory for the Masses*,
2005): transitivity of subtyping for pure System F-sub. Six files, read in
order — syntax, contexts, well-formedness, subtyping, typing, transitivity —
with [`examples/poplmark/README.md`](examples/poplmark/README.md) as the
account. Each file imports the ones under it, so the last one brings the whole
series. **Load it in a fresh session**: the STLC series above declares its own
`Ty`, and two declarations of one name cannot be installed at once.

```
cabal run thena
thena spine> import examples.poplmark.Fsub06Transitivity
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
cabal run thena-check -- examples/Preservation.thena
```

`cabal test` runs the unit suites. **The example corpus is its own suite behind
a flag** and is worth running after any change to a grammar or the elaborator:

```
cabal test thena-examples --flags=examples
```

`:help` lists the REPL commands. `docs/LANGUAGES.md` says what can be written
where. `docs/MANUAL.md` is the reference, with worked
sessions and an honest account of what the system can and cannot currently do.

## Layout

| path | |
|---|---|
| `src/` | the implementation — core calculus, engine, elaborator, parser, kernel |
| `app/` | the entry points — the REPL, the batch checker `thena-check`, the TUI |
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
