# Thena

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

Larger developments are in `examples/`. The acceptance test for the core system
is a full proof of *determinacy of evaluation* for the untyped arithmetic
language of TAPL chapter 3 (Pierce, *Types and Programming Languages*, Theorem
3.5.4) — the language, the numeric-value predicate, the ten-rule small-step
relation, and twenty-one supporting lemmas ending in:

```
determinacy : forall (t t1 : Term) -> Step t t1
           -> forall (t2 : Term) -> Step t t2 -> Eq Term t1 t2
```

It exists both as a REPL script over the development calculus and as a program
in the surface language:

```
cabal run thena
thena spine> :load examples/determinacy-surface.thena
```

## Building

Requires GHC (with `base` 4.21), Cabal, and `alex` + `happy` (resolved
automatically by Cabal).

```
cabal build
cabal test
cabal run thena
```

`:help` lists the REPL commands. `docs/MANUAL.md` is the reference, with worked
sessions and an honest account of what the system can and cannot currently do.

## Layout

| path | |
|---|---|
| `src/` | the implementation — core calculus, engine, elaborator, parser, kernel |
| `rules/standard.thena.rules` | the rule base: elaboration and search, in full |
| `prelude/prelude.thena` | the standard prelude, itself a surface module |
| `examples/` | worked developments, including the determinacy proof |
| `docs/MANUAL.md` | the reference manual — worked sessions, captured from the running program |
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
