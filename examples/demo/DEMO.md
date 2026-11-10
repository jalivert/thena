# Demo — a running order

**The room:** programming-language researchers who know what a typing judgment
is and have a faint idea what you have been building. Not all type theorists.
Some will have written a Coq or Agda proof once and not enjoyed it; some will
never have opened a proof assistant.

**The one sentence they should leave with:** *you describe your language once,
as a grammar and a set of inference rules, and you get the substitution, the
parser, the printer and an interactive proof assistant for it — and the thing
that elaborates your syntax and the thing that searches for your proofs are the
same machine.*

**Shape:** sixty minutes of spine, with thirty minutes of depth to drop in or
leave out depending on the room. Two surfaces, alternating: `./tc` for anything
settled ahead of time, the four-pane TUI for anything live.

---

## 0. Before they arrive

```
cabal build exe:thena exe:thena-check exe:thena-tui
cabal test thena-examples --flags=examples        # ~80s, proves the demo still loads
```

- **One terminal, large font, dark theme chosen from the back of the room**
  (`:theme` lists them — decide this in the room, not at your desk).
- **A second terminal already sitting in the project root** for `./tc`.
- `examples/demo/` open in an editor you can show.
- **Have `examples/Stlc01Syntax.thena` and `examples/poplmark/` ready but not
  loaded.** They are the scale argument in Act 7 and nothing before that.

**Do not load the demo set and the Stlc series into one session.** Both declare
a language called `Ty` and the second one refused is not the demo you want.

---

## 1. The problem — ten minutes, no machine

Say what metatheory costs, in their terms, because this is the part that earns
the rest.

- You have a language. You want to know it does not get stuck, or that its types
  are preserved, or that its subtyping is transitive. These are theorems about
  syntax.
- **The proofs are mostly bookkeeping.** Substitution and its lemmas, capture
  avoidance, free-variable sets, weakening, inversion. In Coq or Agda you write
  all of that yourself, or you pick a representation — de Bruijn, locally
  nameless, HOAS — and then you carry the consequences of that choice through
  every proof.
- **And then the language changes**, and you do it again.
- **POPLMark** is the canonical statement of this: a 2005 challenge asking
  whether anyone's tool could do the metatheory of System F-sub without the
  encoding swallowing the mathematics. Name it; some of them will know it.

**The claim:** the bookkeeping is derivable from the language's own description.
Say the language once, in its own notation, and the machine supplies the rest.

**Say what it is not.** Not a programming language with a compiler. Not a
general-purpose proof assistant — it is specialised for language metatheory and
that specialisation is what buys the automation. It is a research prototype.

---

## 2. A language, in four lines — ten minutes, live

Open an empty file. **Build it in front of them**; this is the single most
persuasive thing in the hour.

```
language Ty, T, S where
  bool -> Bool
  nat  -> Nat

language Tm, M, N, P where
  true   -> true
  false  -> false
  cond   -> ( if M then N else P )
  zero   -> 0
  succ   -> ( succ M )
  pred   -> ( pred M )
  isZero -> ( iszero M )
```

Then, in the session:

- `:show Tm` — **the block declared a datatype.** One constructor per
  production. Say this out loud: *the grammar and the inductive family are the
  same declaration.*
- Write a term in the notation you just invented: `Tm`( if ( iszero 0 ) then ( succ 0 ) else 0 )``.
- `:parse Tm ( succ ( succ 0 ) )` — **text in, constructor application out.**
- The `refl` in `Demo01Expressions.thena`: `two = Tm`( succ ( succ 0 ) )`` and
  `succ (succ zero)` are **the same term**, proved by reflexivity. There is no
  quoting layer and no reflection step. Emphasise this; it is why splices work.
- `${…}`: `Tm`( succ ${two} )`` — **terms compose in the notation.**
- Make the parser fail in front of them and read the message.

**Emphasise:** they did not write a parser, a pretty-printer, an AST, or a
substitution function. **Then show the binder case** — switch to
`examples/Stlc01Syntax.thena` for sixty seconds only, and show
`avoidsCapture`: the generated substitution renames a binder to avoid capture,
and the fact is proved by `refl`, because the kernel *runs* the substitution.
Say: *nothing is renamed behind your back, and when it is renamed you can prove
what to.* Then come back.

---

## 3. Inference rules, as you write them on paper — ten minutes

`examples/demo/Demo02Judgments.thena`. Show the source, not the output, first.

```
judgment typing = ⊢ M : T where

  T-if:      ⊢ M : Bool      ⊢ N : T      ⊢ P : T
             ---------------------------------------
             ⊢ ( if M then N else P ) : T
```

- `:judgment typing` — **it reads back as a paper prints it.**
- `:show typing` — **and it is an inductive family**, one constructor per rule,
  every metavariable quantified. The two printings are the same object. Let them
  sit with that for a moment: *the notation is not a comment.*
- Point out `E-predSucc`, whose premise comes from a **different** judgment.
- Point out `M'` — a suffix makes another metavariable of the same language, so
  the congruence rules read as they do on paper.

**This is the beat for the non-type-theorists.** A judgment is a type; a
derivation is a value of it; type-checking the file *is* checking the
derivations. Say it in those three clauses and move on.

---

## 4. Checked ahead of time — ten minutes, `./tc`

`examples/demo/Demo03Derivations.thena`, then `Demo04Progress.thena`.

```
./tc examples/demo/Demo03Derivations.thena
./tc examples/demo/Demo04Progress.thena
echo $?
```

- **`tc` is a compiler-shaped front door.** Point it at a sequence of files, it
  loads the prelude and the shipped rule base, and the exit status is the
  answer. It chains with `&&`. There is no terminal and nothing interactive.
- In `Demo03`: a typing derivation written out as the tree it is; the
  reflexive-transitive closure declared as an ordinary judgment on top of
  another; **a whole run of a program, as a proof.**
- In `Demo04`: **progress** — a well-typed term is a value or it steps. TAPL
  8.3.2. Show the statement, then the `T-if` arm, and say the one thing about it
  that matters:

  > `progress c1 bool d1` in that arm is **not a recursive call**. Elaboration
  > ties it to the induction hypothesis the method already holds about `d1`. A
  > call that is not about a subderivation has no hypothesis to tie to and is
  > refused. **That is the whole termination story** — there is no termination
  > checker, and nothing names a hypothesis binder.

- `:infer progress` to show the statement the system believes.
- **Then open `examples/Progress.thena` beside it** — the same theorem, for the
  same language, over a hand-written `data Term`. Same shape, no grammar, no
  notation. *This is what you write when the tool does not help you.*

---

## 5. Live, in the four panes — fifteen minutes

Switch to `cabal run thena-tui`. This is the half of the demo that people
remember, so give it room and go slowly.

```
import examples.demo.Demo04Progress
```

Warm up with the smallest proof there is, from
`Demo05ByTactics.thena.script`:

```
:theorem zeroIsValue : value`0 value`
try-core core`V-num zero NV-zero`
solve
qed
```

Then the real beat — **a proof is a term with holes in it, and you have a
cursor**:

```
:theorem predSteps-live : forall (t : Tm) (n : nvalue`${t} nv`) -> Steps Tm`( pred ${t} )`
attack
intro
intro
into
along
along
:where
case-core core`n`
```

What to say, in this order:

- **`attack` turns a hole into a guess**; `intro` moves a `∀` out of the goal
  and into the body. **The proof is an incomplete term**, not a stack of
  tactics, and the goals pane is showing you that term.
- **`:where` is four things**: focus, path, context, expected type. The *path*
  is the one to point at — you are somewhere inside a term and you can walk
  anywhere.
- **`case-core` is the split.** One hole per surviving case, **inside that
  case's own binders, with the split's equations already discharged.** Show
  `NV-succCase1`'s goal: it is about `( pred ( succ M ) )`, with `M` and its
  derivation in scope. **Nothing has to be transported.** This is the thing Coq
  users will react to — say *no `inversion`, no `dependent destruction`, no
  equality to rewrite along.*
- Fill the two cases **in whichever order you like**, and say that the order is
  free because the holes are named positions in a term.
- `qed` — **and say that `qed` re-checks the finished term with the kernel.**
  The tactics are not trusted; the term they built is checked.

Then the mixed mode, which is the thing he asked for:

```
:theorem predSteps-handover : forall (t : Tm) (n : nvalue`${t} nv`) -> Steps Tm`( pred ${t} )`
do { attack ; intro ; intro ; into ; along ; along ; yield "over to you" }
```

**A rule can hand control to you mid-elaboration.** It suspended, you are
standing in its development, you drive, and a bare `yield` hands it back and
lets it finish. Say what that means: *the automation and the human are in the
same loop, not in two phases.*

> **Wart, know it before you hit it:** while a yield is suspended, its message
> reprints after every line you type. Harmless, noisy on a projector. Item
> `~28czj`.

---

## 6. One mechanism — ten minutes, and this is the research claim

Do not skip this one, and do not rush it. It is the part that is an argument
rather than a feature.

- `:rules` — **the elaborator is a text file.** 120 rules, loaded at startup,
  not compiled in. `elaborate` is one of them, with a clause per surface
  construct; the rest are the tactics and their helpers.
- Open `rules/standard.thena.rules` and read a clause of `elaborate` aloud —
  the lambda one is five lines and reads as a sentence.
- `:matches` at an open hole — **which rules apply here.** Note that it does not
  ask whether you are elaborating or proving, **because there is no such
  question**: a rule fires when its head matches the goal. (At a bare hole this
  prints a dozen clauses of `elaborate` and little else, which makes the point
  but reads as a wall — it is worth asking at a position where the answer is
  short.)
- `:choices` and `retry` — **elaboration backtracks**, through the same choice
  points a proof search does.
- `:step on` and watch the machine pane.

**The argument, in his terms:** elaboration and proof search are not two
subsystems over a shared substrate, and neither is implemented in terms of the
other. They are one rule-directed engine over one rule base. The design rule
that keeps it that way is *nothing in the system may ask which of the two it is
doing* — and the payoff is here: a tactic you write is available to the
elaborator, and a rule the elaborator needs is available as a tactic.

**Expect the question** *"isn't that just Prolog with types?"* — the honest
answer is that the resemblance is deliberate, and the difference is that the
goals are typed holes in a development and the solutions are checked by a
kernel.

---

## 7. What you owe, and what it rests on — five minutes

`examples/demo/Demo06Trust.thena`.

```
import examples.demo.Demo06Trust
:whnf nothingOwed
```

- **`trusted T e` asserts a type.** `e` is checked at whatever type it really
  has; the term is then given `T` with nothing relating the two.
- `:whnf nothingOwed` prints `T-zero` — **the claim was met, so the trust
  reduced away to nothing.** This is why it is not an axiom: *a term still
  printing as `trusted` is a term whose claim is still load-bearing.*
- Then build on the pending one and show the report:

```
:theorem restsOnOwed : typing`⊢ ( succ 0 ) : Nat`
try-core core`owed zero T-zero`
solve
:trust
qed
```

  **`qed` admits the theorem and prints what it rests on**, in the judgment's
  own notation. Say the three classes — discharged, pending, undischargeable —
  and that only `:trust none` is a guarantee.

- **Optional, and it lands well:** assert something provably false and let the
  default setting refuse it, *after* the kernel has already accepted the term.
  Say why that order is right: it is your policy, not the kernel's judgement.

---

## 8. Scale — five minutes

Now the files you did not build live, in a **fresh session**.

- `examples/Stlc07Preservation.thena` — preservation for STLC, from a grammar,
  with the generated substitution and its lemmas.
- `examples/Stlc08PreservationByTactics.thena.script` — **the same proof again,
  by tactics.** Both ways, same statement.
- `examples/poplmark/` — **POPLMark problem 1A**, transitivity of subtyping for
  System F-sub, under one hypothesis, with that hypothesis refuted in the same
  file. Show `examples/poplmark/README.md` and say what is left over and why.
- One number: around 3,300 tests, and the example corpus is gated on every pull
  request.

> Loading the whole numbered series takes about 45 seconds. **Do not do it
> live.** Have a session with it already loaded, or show `./tc` output you ran
> beforehand.

---

## 9. Where it is going — five minutes

- The TUI is on its own track and is being built out; what they just saw is
  early.
- **An agent pane** — a conversation beside the proof, with the agent able to
  see the files you have imported and the development you are standing in.
  **This does not exist yet.** If you want to mention it, mention it as a
  direction, and say the interesting part is not the chat: it is that the
  development is a structure with named holes and a cursor, so an agent can be
  pointed at a *position* rather than handed a wall of text. Item `~sh8mb`.
- Honest list of what it cannot do yet — take it from `docs/MANUAL.md` §12
  rather than from memory.

---

## Things to have ready for questions

| they ask | point at |
|---|---|
| how do I know the kernel is right | `docs/MANUAL.md` §9; the kernel is small and `qed` re-checks |
| what representation is substitution | generated per language from the grammar; `:show LC.subst.x` on an Stlc session |
| can I use de Bruijn | yes, today, by writing it — and `DECISIONS.md` says why the framework does not impose one |
| is it total / does it have a termination checker | no checker; the induction hypothesis is an assumption tied by elaboration, §4 above |
| how does it compare to Agda/Coq/Beluga/Abella | specialised, much smaller, and the automation comes from the language description |
| is it K / UIP | without-K, deliberately; `uip` is refused and that is the system working |
| where is the code | `github.com/jalivert/thena`, `DECISIONS.md` is the design record |

## Warts to steer around, all measured

- **After a split, a goal's printed type carries `let refined1 = … in`
  scaffolding.** Accurate, ugly on a projector. Prefer `:where` to `:show` once
  a split has happened.
- **A split's binder names are the declaration's own names**, so a theorem that
  quantifies over `M` will shadow a split binder called `M` and the printed name
  is then one you cannot type back. **Pick binder names that do not collide**
  — `t`, not `M`. This is item `~nmtcq`.
- **A hole left in a surface file does not hand you an unfinished proof** — the
  declaration is refused and the module rolled back. See
  `pending/Demo07Holes.thena`. Item `~mgqwb`.
- **`:core`, `:dev`, `:goal`, `:whnf`, `:convert`, `:load` and `:consult` are
  scheduled for deletion.** They work now. Prefer `import ‹module›` and
  `consult ‹module›` typed at the prompt, which are what survive.

## If something breaks live

- A refused file is a demo, not a failure — read the message out and say what it
  caught.
- Everything in `examples/demo/` is checked by `cabal test thena-examples
  --flags=examples`. If a file will not load, something changed since that run.
- `:abandon` puts down a proof that has gone wrong; `:undo` steps back.
  **A refused `qed` leaves the proof standing** — nothing is thrown away because
  the kernel said no, and that is worth saying out loud when it happens.
