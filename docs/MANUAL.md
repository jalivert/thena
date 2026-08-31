# Thena — a user's manual for the REPL

Thena is an interactive proof assistant for language metatheory. This manual
shows how to drive it: what the commands are, what a proof session looks like,
and what the system can currently do.

Every transcript below is real output, captured from the program.

> **Scope note.** This is the interface the authors use to build and test the
> system. It exposes the *development calculus* directly, which is why proofs
> here are made of small explicit steps. A student-facing surface language is a
> later milestone and is not what you are looking at.

---

## 1. Starting up

```bash
cabal run thena
```

Use `cabal run` rather than the built binary directly — it is what tells the
program where the prelude file is installed.

You land at a prompt with a small prelude already loaded (`Eq` and `refl`,
`Unit` and `unit`, `Empty`) and one empty goal:

```
thena spine> :show
▶ let ? goal : Type₀ in
  goal
thena spine> :quit
```

`:quit` exits. `:help` lists every command in one screen; this manual is the
longer reference.

### The two prompts

The prompt tells you which fragment the cursor is in.

| prompt | you are standing on |
|---|---|
| `thena spine>` | the chain — a component, or a pending equation |
| `thena core>` | inside a term |

Some commands only make sense in one of them, and say so when you get it wrong.

### The one naming rule

> **A bare word acts. A word with a colon looks.**

`intro` changes the proof. `:show` does not. That distinction holds for every
command in the system, and it is the fastest way to guess whether something is
safe to try.

---

## 2. Writing terms

The syntax is small and fully explicit — every binder is annotated, and nothing
is inferred.

| | |
|---|---|
| function | `λ (x : A) -> b` |
| function type | `∀ (x : A) -> B`, or `A -> B` when `B` does not mention `x` |
| application | `f a b` |
| universes | `Type₀`, `Type₁`, … |
| local definition | `let x = s : S in t` |
| a hole | `let ? x : S in t` |
| a hole with a proposed body | `let ? x : S ≐ (g) in t` |
| eliminator use | `elim D (params) motive (methods) (indices) target` |

**Every symbol has an ASCII spelling**, so nothing here requires a special
keyboard:

| unicode | ASCII |
|---|---|
| `λ` | `\` |
| `∀` | `forall` |
| `Type₀` | `Type0` |
| `≟` | `?=` |
| `≐` | `≈` |
| `⊢` | `\|-` |
| `▸` | `\|>` |
| `⌜ ⌝` | `[\| \|]` |

```
thena spine> :core \ (A : Type0) -> A
λ (A : Type₀) -> A
thena spine> :core forall (A : Type0) -> A -> A
∀ (A : Type₀) -> A -> A
```

Input is echoed back in the unicode spelling. **There are no comments** — `--`
is not a comment, it is an unrecognised command.

---

## 3. Looking at things

Seven commands, none of which change anything.

| command | what it does |
|---|---|
| `:show` | print the whole development, with `▶` marking the cursor |
| `:show ‹name›` | print a global — a datatype, or a proved theorem |
| `:core ‹term›` | parse, resolve and print a term |
| `:dev ‹development›` | the same, for a development |
| `:infer ‹term›` | print the term's type |
| `:whnf ‹term›` | reduce to weak head normal form |
| `:convert ‹t› ≟ ‹u›` | are these two terms convertible? |
| `:elim ‹datatype›` | print the datatype's elimination rule |
| `:where` | print the focus, the path, the context and the expected type |

```
thena spine> :core succ (succ zero)
succ (succ zero)
thena spine> :infer succ (succ zero)
succ (succ zero) : Nat
thena spine> :convert succ zero ≟ succ zero
succ zero ≟ succ zero   yes
```

---

## 4. Declaring a datatype

```
thena spine> data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> :show Nat
data Nat : Type₀
  { zero : Nat
  ; succ : Nat -> Nat }
```

Declaring a datatype checks strict positivity and **generates three things**:

**A wrapper function per constructor**, so a constructor can be written without
all its arguments:

```
thena spine> :show succ
succ : Nat -> Nat
succ = λ (x : Nat) -> succ x
```

**An elimination rule.** It is not stored as a global — it is a rule, and you
ask for it at whatever universe you want the motive valued in:

```
thena spine> :elim Nat
elim Nat : ∀ (P : Nat -> Type₀) -> P zero -> (∀ (x : Nat) -> P x -> P (succ x)) -> ∀ (target : Nat) -> P target
thena spine> :elim Nat Type₁
elim Nat : ∀ (P : Nat -> Type₁) -> P zero -> (∀ (x : Nat) -> P x -> P (succ x)) -> ∀ (target : Nat) -> P target
```

**A no-confusion lemma**, which is what makes "different constructors are not
equal" and "constructors are injective" usable in a proof:

```
thena spine> :show noConfusionNat
noConfusionNat : ∀ (x : Nat) (y : Nat) -> Eq Nat x y -> NoConfusionNat x y
```

Indexed families work too. Where a constructor's argument types depend on
earlier arguments, the no-confusion lemma cannot be stated, and the system says
so plainly rather than failing:

```
no noConfusionNV: nvSucc's argument n has a type that depends on an earlier argument,
so its equation cannot be stated
```

---

## 5. A first proof

`:theorem` opens a proof. `qed` closes it and admits the result as a global.

```
thena spine> :theorem id : ∀ (A : Type₀) -> A -> A
proving id : ∀ (A : Type₀) -> A -> A
thena spine> :show
▶ let ? id : ∀ (A : Type₀) -> A -> A in
  id
```

A proof starts as a single **hole**: a name, a type, and nothing else.

`attack` turns the hole into a *guess* — a hole with a proposed body you are
about to build. `intro` moves a `∀` binder out of the goal and into the body.

```
thena spine> attack
thena spine> intro
thena spine> intro
thena spine> :show
▶ let ? id : ∀ (A : Type₀) -> A -> A ≐ (
    λ (A : Type₀) ->
    λ (_ : A) ->
    let ? id : A in
    id
  ) in
  id
```

Two λs have appeared, and the remaining hole now has type `A`. Move the cursor
down to it — `into` enters the guess body, `along` steps past a binder — and ask
where you are:

```
thena spine> into
thena spine> along
thena spine> along
thena spine> :where
focus
  let ? id : A in
path
  root ▸ ≐ id ▸ A ▸ _
context
  A : Type₀
  _ : A
type
  A
```

`try` proposes a term for the hole; `solve` accepts it. Then walk back out,
`solve`-ing each guess as you go, and finish:

```
thena spine> try _
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
id : ∀ (A : Type₀) -> A -> A   ∎
thena spine> :show id
id : ∀ (A : Type₀) -> A -> A
id = let id = λ (A : Type₀) (_ : A) -> let id = _ : A in id : ∀ (A : Type₀) -> A -> A in id
```

`qed` re-checks the finished term with the kernel before admitting it. If it
does not check, nothing is admitted.

### The proof commands

| | |
|---|---|
| `attack` | turn the focused hole into a guess, ready to be built |
| `intro` | move one `∀` binder from the goal into the guess body |
| `try ‹term›` | propose a term for the focused hole |
| `solve` | accept the focused guess — it becomes a definition |
| `regret` | throw away a guess's body, back to a plain hole |
| `abandon` | remove the focused hole entirely |
| `assume ‹x› : ‹S›` | add a hypothesis above the focus |
| `claim ‹x› : ‹S›` | add a new hole above the focus |
| `unify ‹t› ≟ ‹u›` | solve holes by unification |
| `reduce` | reduce the focused term one step, in place |

`reduce` acts on whatever term the cursor is standing on, and the change is
committed to the development:

```
thena core> :show
  let ? two : Nat ≐ (
▶   (λ (x : Nat) -> succ x) zero
  ) in
  two
thena core> reduce
thena core> :show
  let ? two : Nat ≐ (
▶   succ zero
  ) in
  two
```

`assume` and `claim` will ask for a name if you leave it out. The question is
asked on its own line, and your answer is read at the `>` prompt:

```
thena spine> claim : Nat
name for the hole? it will have type Nat
> k
claimed k
```

---

## 6. Navigating

The development is a chain, and terms hang off it. The cursor sits at exactly
one position.

| | |
|---|---|
| `along` | step past the focused link |
| `into` | enter a guess's body |
| `back` | undo the last move, whatever it was |
| `cross type` | move into the focused component's **type** |
| `cross val` | move into a definition's **value** |

Once you are inside a term, each field has its own word — so no word ever
changes meaning depending on what is in focus:

```
fun  arg  dom  cod  val  type  body  motive  target
param ‹n›   method ‹n›   index ‹n›   arg ‹n›
```

The numbered ones count from one.

```
thena spine> :goal ∀ (n : Nat) -> Eq Nat n n
▶ let ? goal : ∀ (n : Nat) -> Eq Nat n n in
  goal
thena spine> cross type
thena core> :where
focus
  ∀ (n : Nat) -> Eq Nat n n
path
  root ▸ type of goal
context
  (nothing in scope)
thena core> cod
thena core> :where
focus
  Eq Nat n n
path
  root ▸ type of goal ▸ cod
context
  n : Nat
```

Note the prompt changed to `thena core>`, and that descending into the codomain
brought `n` into scope. `back` reverses any move, including that one.

`:goal ‹type›` throws the current development away and starts a fresh one — handy
for scratch work.

---

## 7. Proof by induction

`eliminate ‹target›` is the induction tactic. It builds the motive, works out
what each case has to prove, and posts one hole per case.

Assume `Nat`, addition as `plus`, and congruence of `succ` are already proved.

```
thena spine> :theorem plusZero : ∀ (n : Nat) -> Eq Nat (plus n zero) n
proving plusZero : ∀ (n : Nat) -> Eq Nat (plus n zero) n
thena spine> attack
thena spine> intro
thena spine> into
thena spine> along
thena spine> eliminate n
subgoals: zeroMethod, succMethod
```

Two subgoals, named after the constructors. Look at what it built:

```
thena spine> :show
  let ? plusZero : ∀ (n : Nat) -> Eq Nat (plus n zero) n ≐ (
    λ (n : Nat) ->
    let ? zeroMethod : Eq Nat (plus zero zero) zero in
    let ? succMethod : ∀ (x : Nat) -> Eq Nat (plus x zero) x -> Eq Nat (plus (succ x) zero) (succ x) in
▶   let ? plusZero : Eq Nat (plus n zero) n ≐ (
      elim Nat () (λ (target : Nat) -> Eq Nat (plus target zero) target) (zeroMethod succMethod) () n
    ) in
    plusZero
  ) in
  plusZero
```

The base case wants `Eq Nat (plus zero zero) zero`; the step case gets an
induction hypothesis and must produce the successor case. Fill them in and
finish:

```
thena spine> back
thena spine> back
thena spine> try refl Nat zero
thena spine> solve
thena spine> along
thena spine> try \ (x : Nat) (ih : Eq Nat (plus x zero) x) -> congSucc (plus x zero) x ih
thena spine> solve
thena spine> along
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
plusZero : ∀ (n : Nat) -> Eq Nat (plus n zero) n   ∎
```

`eliminate` works on inductively defined **relations** too, which is what proofs
about a reduction relation need — see §11.

One thing to know: `eliminate` refuses when a premise of the goal would have to
follow the target into the abstraction, because the induction it could give you
there would be too weak to use. The workaround is the ordinary one — do not
`intro` something you need generalised.

---

## 8. The rule engine

Thena has a small base of named rules, and it can pick one for you.

`:matches` lists the rules that apply where you are standing. `prove` runs one.

```
thena spine> :theorem id : ∀ (A : Type₀) -> A -> A
proving id : ∀ (A : Type₀) -> A -> A
thena spine> attack
thena spine> :matches
intro-pi
solve
regret
thena spine> prove
chose 74: intro-pi
```

Three rules matched, so the engine reports which one it took and leaves a
**choice point** behind — the number is its identifier.

```
thena spine> :choices
74  intro-pi   untried: solve, regret
```

`retry` backtracks to the nearest choice point and takes the next alternative.
Here both remaining alternatives fail, so it exhausts the choice point and
undoes the whole thing:

```
thena spine> retry
retrying 74: solve
backtracking to 74: regret
thena spine> :show
▶ let ? id : ∀ (A : Type₀) -> A -> A in
  id
thena spine> :choices
no choice points
```

Search is meant to be inspectable, not a black box: you can always see what was
chosen, what is untried, and undo it.

Choice-point numbers are unique but **not consecutive** — they are drawn from
the same counter as variable names, so the first one in a session is rarely `1`.

### Elaboration by hint

`prove ‹name›` and `:matches ‹name›` narrow the rule base to rules that can use
the hint:

```
thena spine> :matches
attack
try ‹t›
abandon
eliminate ‹t›
thena spine> :matches a
elab-var
```

### Watching the machine

`:step on` puts the engine in single-step mode, and `:step` advances one
instruction. This is how you see what a rule actually does:

```
thena spine> :step on
thena spine> prove a
pc
  0  prove with hint
env
  hint = ‹a›
stack
  (empty)
thena spine> :step
pc
  0  t = resolve hint
  1  call ‹rule try› (t)
  2  solve
env
  hint = ‹a›
stack
  call, 0 instruction(s) to resume
thena spine> :step
pc
  0  call ‹rule try› (t)
  1  solve
env
  t = ⌜a⌝
  hint = ‹a›
stack
  call, 0 instruction(s) to resume
```

`:run` finishes the current run without stepping; `:step off` leaves the mode.

---

## 9. The kernel

The kernel is an independent check. It does not trust the machine.

| | |
|---|---|
| `:extract` | read the finished term off the development |
| `certify ‹type›` | check the extracted term really has that type |
| `:revalidate` | re-derive the whole development's well-formedness from scratch |

```
thena core> :extract
let goal = zero : Nat in goal
thena core> certify Nat
certified
thena core> certify Nat -> Nat
the kernel refused it
in the term:
  let goal = zero : Nat in goal has type Nat
    but Nat -> Nat was expected
    Nat -> Nat and Nat do not match
```

An unfinished proof cannot be extracted, and the message says exactly what is
still open:

```
thena core> :extract
stuck: not finished: the hole k is still open, so there is no term yet
```

`qed` runs `certify` for you. These commands are for inspecting a proof
mid-flight, or for convincing yourself the machine has not cheated.

---

## 10. Sessions

You can have several proofs open, park them, and come back.

| | |
|---|---|
| `:theorem ‹x› : ‹T›` | start a proof |
| `:suspend` | park the current proof under its name |
| `:resume ‹name›` | pick a parked proof back up |
| `:proofs` | list what is open and what is parked |
| `:abandon` | throw the current proof away |
| `:undo` | undo the last command that changed anything |
| `qed` | certify and admit |

```
thena spine> attack
thena spine> :undo
▶ let ? two : Nat in
  two
thena spine> :undo
nothing to undo
thena spine> :suspend
suspended two
thena spine> :proofs
  two : Nat
```

Declarations made while a proof is suspended are still there when you resume —
globals are session-wide, proofs are not.

---

## 11. Loading a file, and what the system has proved

A `.thena` file is a script of REPL command lines, run in order.

```
thena spine> :load examples/determinacy.thena
```

`examples/determinacy.thena` is the acceptance test for the whole first
milestone. It declares the language of chapter 3 of Pierce's *Types and
Programming Languages* — a seven-constructor term language, a numeric-value
predicate, and a ten-rule small-step reduction relation —

```
thena spine> :show Term
data Term : Type₀
  { true : Term
  ; false : Term
  ; ifthen : Term -> Term -> Term -> Term
  ; zero : Term
  ; succ : Term -> Term
  ; pred : Term -> Term
  ; iszero : Term -> Term }
```

— and proves twenty-one theorems, ending with **determinacy of evaluation**,
TAPL Theorem 3.5.4:

```
determinacy : ∀ (t : Term) (t1 : Term) -> Step t t1 -> ∀ (t2 : Term) -> Step t t2 -> Eq Term t1 t2   ∎
```

Every one of the twenty-one is checked by the kernel as it is admitted. The
whole file loads in a couple of seconds.

The proof is structured as ten inversion lemmas plus the main induction, so
that no elimination sits inside another. The file is machine-generated —
`examples/determinacy.thena.py` regenerates it byte for byte — because 110 of
its 130 case branches are mechanical constructor clashes.

---

## 12. What it can and cannot currently do

**It can:** declare inductive families with parameters and indices; generate
their eliminators and no-confusion lemmas; reduce, infer types and test
convertibility; unify, including parking equations it cannot yet decide; prove
theorems by hand at the REPL with full undo; do induction on data and on
inductively defined relations; dispatch named rules with backtracking; check
finished proofs with an independent kernel; and load files of commands.

**It cannot yet:**

- **No surface language.** You write the development calculus directly. There
  is no Agda-like language to elaborate from — the elaboration *mechanism*
  exists, but only the "this hole is that variable in scope" case is wired up.
- **No comments in files**, and no layout-sensitive syntax.
- **No completion of command or identifier names.** Line editing and history
  come from `haskeline`, so the arrow keys work, but tab completes filenames
  only — which is `haskeline`'s default, not a choice.
- **No automation beyond the small rule base.** There is no `auto`, no
  simplifier, no decision procedure. Every proof step above is one you type.
- **No cumulativity and no universe polymorphism.** `Type₀` is not a `Type₁`;
  where you need a rule at a higher universe you ask for it (`:elim Nat Type₁`).
- **No no-confusion lemma for a constructor with dependent argument types** —
  the system tells you when it skipped one and why.
- **No proof scripts.** A `.thena` file is a flat sequence of commands, not a
  structured document.

---

## 13. Command reference

**Bare words act.**

| | |
|---|---|
| `attack` `intro` `solve` `regret` `abandon` | the hole operations |
| `try ‹term›` | propose a term for the focused hole |
| `assume ‹x› : ‹S›` / `claim ‹x› : ‹S›` | add a hypothesis / a hole above the focus |
| `unify ‹t› ≟ ‹u›` | solve by unification |
| `eliminate ‹target›` | induction |
| `reduce` | reduce the focused term in place |
| `along` `into` `back` | move on the chain |
| `cross type` / `cross val` | move into a term |
| `fun` `arg` `dom` `cod` `val` `type` `body` `motive` `target` | descend into a field |
| `param ‹n›` `method ‹n›` `index ‹n›` `arg ‹n›` | descend into a numbered field |
| `prove` / `prove ‹hint›` | let the rule engine choose and run a rule |
| `retry` / `retry ‹n›` | backtrack to a choice point |
| `data ‹D› … { … }` | declare an inductive family |
| `certify ‹type›` | ask the kernel |
| `qed` | certify and admit the finished proof |

**Colon commands look.**

| | |
|---|---|
| `:show` / `:show ‹name›` | the development / a global |
| `:where` | focus, path, context, expected type |
| `:core ‹t›` `:dev ‹p›` | parse and print |
| `:infer ‹t›` `:whnf ‹t›` `:convert ‹t› ≟ ‹u›` | type, reduct, convertibility |
| `:elim ‹D›` / `:elim ‹D› ‹universe›` | the elimination rule |
| `:matches` / `:matches ‹hint›` | which rules apply here |
| `:choices` | open choice points |
| `:step on` / `:step` / `:step off` / `:run` | single-step the machine |
| `:theorem ‹x› : ‹T›` | start a proof |
| `:suspend` `:resume ‹name›` `:proofs` `:abandon` `:undo` | session management |
| `:goal ‹T›` | discard everything and start a fresh scratch goal |
| `:extract` `:revalidate` | read off the term / recheck the development |
| `:load ‹path›` | run a file of commands |
| `:bases` / `:rules` | the loaded rule bases / the rules in them |
| `:help` | this table, in one screen |
| `:quit` | exit |
