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

You land at a prompt with a small prelude already loaded — `Eq` and `refl`,
`Unit` and `unit`, `Empty`, `And` and `both`, `Sigma` and `pair`, with `fst`,
`snd`, `andLeft` and `andRight` proved — and one empty goal:

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
| universes | `Type₀`, `Type₁`, …, or a bare `Type` whose level is inferred |
| level arguments | `refl {0}`, `And {0 1}` — see below |
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

### Universes, and the level arguments you write

`Typeₙ` is the universe at level `n`, and a bare `Type` is the same thing with
the level left to be worked out:

```
thena spine> :infer Type₀
Type₀ : Type₁
thena spine> :infer Type
Type (?ℓ229) : Type (suc ?ℓ229)
```

`?ℓ229` is an unknown level. It is not a default and it is not zero — it is
carried along until something pins it down, which is what lets one declaration
serve every level.

**Smaller universes sit inside larger ones.** A `Type₀` is accepted where a
`Type₁` is wanted:

```
thena spine> :infer (\ (A : Type₁) -> A) Type₀
(λ (A : Type₁) -> A) Type₀ : Type₁
```

They are still different universes, so nothing collapses:

```
thena spine> :convert Type₀ ≟ Type₁
Type₀ ≟ Type₁   no
  Type₀ and Type₁ are different universes
```

**A datatype declared over a bare `Type` gets a level parameter**, and every use
of it writes that level in braces:

```
thena spine> :show Eq
data Eq {ℓ₇} (A : Type (ℓ₇)) : A -> A -> Type (ℓ₇) where
  { refl : ∀ (a : A) -> Eq {ℓ₇} A a a }
```

So `Eq` on its own is not a term — `Eq {0} Nat x y` is. The parameters are
prenex, which means a use writes all of them or none:

```
thena spine> :infer refl
refl has 1 level parameter, and was given 0 level arguments
its level parameters are prenex, so a use writes every one of them
thena spine> :infer refl {1}
refl {1} : ∀ (A : Type₁) (a : A) -> Eq {1} A a a
```

A datatype over two of them gets two parameters, and its own level is their
join:

```
thena spine> :show And
data And {ℓ₇₂ ℓ₇₃} (A : Type (ℓ₇₂)) (B : Type (ℓ₇₃)) : Type (ℓ₇₂ ⊔ ℓ₇₃) where
  { both : A -> B -> And {ℓ₇₂ ℓ₇₃} A B }
```

`⊔` is the one symbol that is printed and never written: the join is computed
from the constructors, so there is nothing to type and no ASCII spelling for it.

A subscripted `ℓ₇` is a level *parameter*; a `?ℓ229` is a level still unknown.
That is the whole of the notation.

---

## 3. Looking at things

These commands only look; none of them changes anything. `:help` lists them
all, along with everything else.

| command | what it does |
|---|---|
| `:show` | print the whole development, with `▶` marking the cursor |
| `:show ‹name›` | print a global — a datatype, or a proved theorem |
| `:core ‹term›` | parse, resolve and print a term |
| `:surface ‹term›` | parse and print a **surface** term |
| `:dev ‹development›` | the same, for a development |
| `:infer ‹term›` | print the term's type |
| `:whnf ‹term›` | reduce to weak head normal form |
| `:convert ‹t› ≟ ‹u›` | are these two terms convertible? |
| `:elim ‹datatype›` | print the datatype's elimination rule |
| `:where` | print the focus, the path, the context and the expected type |

### The surface language

`:surface` is the same idea one language over. Thena is growing a **surface
language** — the one you will write programs in — beside the development
calculus, and `:surface` shows what its parser made of what you typed. Nothing
is resolved and no names are looked up: turning a surface term into a core term
is *elaboration*, which is not built yet.

```
thena spine> :surface \ x (y : A) -> f x {B} y
λ x (y : A) -> f x {B} y
```

It has three things the development calculus does not: a lambda binder may have
no type, an argument in braces is **implicit**, and `_` and `?goal` are
placeholders — `_` for something inference should find, `?goal` for something
you mean to prove yourself. None of them *do* anything yet.

It also has **layout**. `let` opens a block, and you may write the block either
way — the offside rule and explicit braces mean the same thing:

```
thena spine> :surface let { x = a ; y = b } in f x y
let x = a in let y = b in f x y
```

The bindings are **sequential**, not mutually recursive, which is why that
prints as nested `let`s: a development is a chain, so `y` is in scope after `x`
and nothing in the calculus underneath can express two bindings that refer to
each other.

The indentation-sensitive spelling needs more than one line, and the REPL reads
one line at a time — so until surface **files** arrive you can only write a
block with explicit braces here.

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
thena spine> data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> :show Nat
data Nat : Type₀ where
  { zero : Nat
  ; succ : Nat -> Nat }
```

**Write the universe as a bare `Type` and it is worked out for you**, from the
constructors' own levels, and becomes a level parameter if nothing pins it:

```
thena spine> data Box (A : Type) : Type where { box : A -> Box A }
declared Box
thena spine> :show Box
data Box {ℓ₂₅₆} (A : Type (ℓ₂₅₆)) : Type (ℓ₂₅₆) where
  { box : A -> Box {ℓ₂₅₆} A }
```

A written `Typeₙ` is still checked rather than believed:

```
thena spine> data Big : Type₀ where { wrap : Type₀ -> Big }
refused: the argument x of wrap lives in Type₁, which the datatype's own Type₀ does not contain
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
noConfusionNat : ∀ (x : Nat) (y : Nat) -> Eq {0} Nat x y -> NoConfusionNat x y
noConfusionNat = λ (x : Nat) (y : Nat) (e : Eq {0} Nat x y) -> elim Eq {0} …
```

(`:show` prints the body too; it is one long line and is elided here.)

Indexed families work too. Where a constructor's argument types depend on
earlier arguments, the no-confusion lemma cannot be stated, and the system says
so plainly rather than failing:

```
no noConfusionNV: nvSucc's argument p has a type that depends on an earlier argument, so its equation cannot be stated
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
    let ? id1 : A in
    id1
  ) in
  id
```

The inner hole is `id1`, not `id`: every component in a development has a name
of its own, so that `goto ‹name›` always means one place.

Two λs have appeared, and the remaining hole now has type `A`. Move the cursor
down to it — `into` enters the guess body, `along` steps past a binder — and ask
where you are:

```
thena spine> into
thena spine> along
thena spine> along
thena spine> :where
focus
  let ? id1 : A in
path
  root ▸ ≐ id ▸ A ▸ _
context
  A : Type₀
  _ : A
type
  A
```

`try-core` proposes a term for the hole; `solve` accepts it. Then walk back out,
`solve`-ing each guess as you go, and finish:

```
thena spine> try-core ⌜ _ ⌝
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
id : ∀ (A : Type₀) -> A -> A   ∎
thena spine> :show id
id : ∀ (A : Type₀) -> A -> A
id = let id = λ (A : Type₀) (_ : A) -> let id1 = _ : A in id1 : ∀ (A : Type₀) -> A -> A in id
```

`qed` re-checks the finished term with the kernel before admitting it. If it
does not check, nothing is admitted.

### What `qed` does about levels

Write the statement with a bare `Type` instead of `Type₀`, prove it exactly the
same way, and the theorem comes out polymorphic — the level that was left
unknown becomes a parameter:

```
thena spine> :theorem id : ∀ (A : Type) -> A -> A
proving id : ∀ (A : Type (?ℓ229)) -> A -> A
…
thena spine> qed
id {ℓ₂₄₀} : ∀ (A : Type (ℓ₂₄₀)) -> A -> A   ∎
```

Sometimes one level is not enough, and the proof leaves a *relation* between two
of them. That relation is part of the theorem, and is printed inside the type,
before a `⊢`:

```
thena spine> :theorem lift : Type -> Type
proving lift : Type (?ℓ229) -> Type (?ℓ230)
thena spine> try-core ⌜ \ (x : Type) -> x ⌝
thena spine> solve
thena spine> qed
lift {ℓ₂₃₈ ℓ₂₃₉} : (ℓ₂₃₈ ≤ ℓ₂₃₉) ⊢ Type (ℓ₂₃₈) -> Type (ℓ₂₃₉)   ∎
```

Read it as *given `ℓ₂₃₈ ≤ ℓ₂₃₉`, this type*. A constraint that held at every
level would have been discharged and never stored, so if there is no `⊢`, there
is nothing to meet.

A use of `lift` writes two levels and owes the condition. **The debt is
collected by the kernel, not at the moment you type the term** — `:infer` and
`try-core` will hand you `lift {1 0}` quite happily, and `qed` is where it stops:

```
thena spine> :theorem bad : Type₁ -> Type₀
proving bad : Type₁ -> Type₀
thena spine> try-core ⌜ lift {1 0} ⌝
thena spine> solve
thena spine> qed
the kernel refused it
1 is not at most 0
```

`:revalidate` says the same thing at any point, without closing the proof.

### The proof commands

| | |
|---|---|
| `attack` | turn the focused hole into a guess, ready to be built |
| `intro` | move one `∀` binder from the goal into the guess body |
| `try-core ⌜ term ⌝` | propose a term for the focused hole |
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
thena core> claim : Nat
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
thena spine> :goal ∀ (n : Nat) -> Eq {0} Nat n n
▶ let ? goal : ∀ (n : Nat) -> Eq {0} Nat n n in
  goal
thena spine> cross type
thena core> :where
focus
  ∀ (n : Nat) -> Eq {0} Nat n n
path
  root ▸ type of goal
context
  (nothing in scope)
thena core> cod
thena core> :where
focus
  Eq {0} Nat n n
path
  root ▸ type of goal ▸ cod
context
  n : Nat
```

Note the prompt changed to `thena core>`, and that descending into the codomain
brought `n` into scope. `back` reverses any move, including that one.

`:goal ‹type›` replaces whatever component is in focus with a fresh hole of that
type — at a fresh prompt, where the only component is the starting goal, that
amounts to starting over. Handy for scratch work.

---

## 7. Proof by induction

`eliminate-core ⌜ target ⌝` is the induction tactic. It builds the motive, works out
what each case has to prove, and posts one hole per case.

The example needs `Nat`, addition, and congruence of `succ`.
`examples/tier0.thena` declares the first two; the third is one line.

```
thena spine> :load examples/tier0.thena
module Tier0
  declared Nat
  declared plus
  declared identity
  declared one
  declared two
  declared plusZeroLeft
thena spine> declare congSucc : ∀ (a b : Nat) -> Eq Nat a b -> Eq Nat (succ a) (succ b) ; congSucc = \ a b e -> elim Eq (Nat) (\ x y q -> Eq Nat (succ x) (succ y)) ((\ c -> refl Nat (succ c))) (a b) e
…
```

(Elaborating a declaration at the prompt prints a page of `solved: ?ℓ…` lines,
elided here. Inside a `.thena` module they are suppressed — see §11.)

```
thena spine> :theorem plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n
proving plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n
thena spine> attack
thena spine> intro
thena spine> into
thena spine> along
thena spine> eliminate-core ⌜ n ⌝
subgoals: zeroMethod, succMethod
```

Two subgoals, named after the constructors. Look at what it built:

```
thena spine> :show
  let ? plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n ≐ (
    λ (n : Nat) ->
    let ? zeroMethod : Eq {0} Nat (plus zero zero) zero in
    let ? succMethod : ∀ (x : Nat) -> Eq {0} Nat (plus x zero) x -> Eq {0} Nat (plus (succ x) zero) (succ x) in
▶   let ? plusZero1 : Eq {0} Nat (plus n zero) n ≐ (
      elim Nat () (λ (target : Nat) -> Eq {0} Nat (plus target zero) target) (zeroMethod succMethod) () n
    ) in
    plusZero1
  ) in
  plusZero
```

The base case wants `Eq {0} Nat (plus zero zero) zero`; the step case gets an
induction hypothesis and must produce the successor case. Fill them in and
finish:

```
thena spine> back
thena spine> back
thena spine> try-core ⌜ refl {0} Nat zero ⌝
thena spine> solve
thena spine> along
thena spine> try-core ⌜ \ (x : Nat) (ih : Eq {0} Nat (plus x zero) x) -> congSucc {0 0} (plus x zero) x ih ⌝
thena spine> solve
thena spine> along
thena spine> solve
thena spine> back
thena spine> back
thena spine> back
thena spine> back
thena spine> solve
thena spine> qed
plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n   ∎
```

**A core tactic's argument is written in corners**, `⌜ … ⌝`. A command line is
a run of atoms, exactly as it would be inside a rule body, so
`try-core refl {0} Nat zero` would be four arguments and is refused — the
corners say where the term begins and ends, and inside them nothing needs
parenthesising.

The `-core` suffix marks the tactics that take a **development-calculus** term.
The surface language exists beside it — `:infer`, `declare` and a `.thena` proof
module all take surface terms, and §11 shows one — so the suffix says which of
the two layers a tactic is written against. Note `congSucc {0 0}` above: a core
term writes a polymorphic global's level arguments, where a surface term has
them inferred. The names are provisional and the suffixes are meant to go.

`eliminate-core` works on inductively defined **relations** too, which is what
proofs about a reduction relation need — see §11.

One thing to know: `eliminate-core` refuses when a premise of the goal would have to
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
intro
solve
regret
thena spine> prove
chose 235: intro
```

Three rules matched, so the engine reports which one it took and leaves a
**choice point** behind — the number is its identifier.

```
thena spine> :choices
235  intro   untried: solve, regret
```

`retry` backtracks to the nearest choice point and takes the next alternative.
Here both remaining alternatives fail, so it exhausts the choice point and
undoes the whole thing:

```
thena spine> retry
retrying 235: solve
backtracking to 235: regret
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
try-core ‹t›
abandon
eliminate-core ‹t›
unify-refine-core ‹t›
apply-core ‹f›
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
  1  call try-core t
  2  prim-solve
env
  hint = ‹a›
stack
  call, 0 instruction(s) to resume
thena spine> :step
pc
  0  call try-core t
  1  prim-solve
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
thena spine> :extract
let goal = zero : Nat in goal
thena spine> certify Nat
certified
thena spine> certify Nat -> Nat
the kernel refused it
in the term:
  let goal = zero : Nat in goal has type Nat
    but Nat -> Nat was expected
    Nat -> Nat and Nat do not match
```

An unfinished proof cannot be extracted, and the message says exactly what is
still open:

```
thena spine> :extract
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

`:load` reads three kinds of file and the extension says which: a `.thena`
**proof module**, a `.thena.script` script of REPL command lines, or one or more
`.thena.rules` rule bases. `:load proof`, `:load script` and `:load rules` say
it out loud instead.

A script is command lines, run in order.

```
thena spine> :load examples/determinacy-tactics.thena.script
```

A **proof module** is the surface language: a header, then declarations, laid
out by indentation. It reports what it declared and nothing else — elaborating
one declaration prints a dozen lines of unification chatter, and a file of them
would bury its own output.

```
thena spine> :load examples/tier0.thena
module Tier0
  declared Nat
  declared plus
  declared identity
  declared one
  declared two
  declared plusZeroLeft
thena spine> :infer plus one one
plus one one : Nat
```

`:infer` takes a **surface** term and elaborates it where you are asking, then
puts the development back exactly as it was. A development-calculus term goes in
corners instead: `:infer ⌜ succ zero ⌝`.

A comment is `--` followed by a space, running to the end of the line, and it
works the same way in all three kinds of file. Without the space it is not a
comment, so `-->` is still yours to use.

`examples/determinacy-tactics.thena.script` is the acceptance test for the whole first
milestone. It declares the language of chapter 3 of Pierce's *Types and
Programming Languages* — a seven-constructor term language, a numeric-value
predicate, and a ten-rule small-step reduction relation —

```
thena spine> :show Term
data Term : Type₀ where
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
determinacy : ∀ (t : Term) (t1 : Term) -> Step t t1 -> ∀ (t2 : Term) -> Step t t2 -> Eq {0} Term t1 t2   ∎
```

Every one of the twenty-one is checked by the kernel as it is admitted. The
whole file loads in a couple of seconds.

The proof is structured as ten inversion lemmas plus the main induction, so
that no elimination sits inside another. The file is machine-generated —
`examples/determinacy.py` regenerates it byte for byte — because 110 of
its 130 case branches are mechanical constructor clashes.

**The same proof exists twice.** `examples/determinacy-surface.thena` is a proof
module in the surface language — 278 lines where the script is 1190 — and it
proves the same theorem through the same rule base:

```
thena spine> :load examples/determinacy-surface.thena
```

One generator emits both, and the test suite asserts they arrive at the same
statement, so a weaker version of either cannot pass quietly. Reading them side
by side is the shortest way to see what elaboration is doing.

---

## 12. What it can and cannot currently do

**It can:** declare inductive families with parameters and indices, at an
inferred universe level or a written one; generate their eliminators and
no-confusion lemmas; infer the levels of a theorem and generalise it at `qed`,
constraints and all; reduce, infer types and test convertibility, with smaller
universes sitting inside larger ones; unify, including parking equations it
cannot yet decide; prove theorems by hand at the REPL with full undo; do
induction on data and on inductively defined relations; dispatch named rules
with backtracking; check finished proofs with an independent kernel; and load
files of commands.

It also has a **surface language** — layout-sensitive, with implicit arguments
and inferred level arguments — and elaborates it into the development calculus.
**That elaborator is not in the binary**: it is fifteen clauses of one rule in
`rules/standard.thena.rules`, which you can read and change. `prelude/prelude.thena`
and `examples/determinacy-surface.thena` are both written in the surface
language and elaborated on load.

**It cannot yet:**

- **A λ binder must be plain.** `\ x -> e`, never `\ (x : Nat) -> e` and never
  `\ {A} -> e`; the type comes from the goal. It says
  *"expected a surface term that is a λ whose first binder is plain"*.
- **A `let` must be annotated when its type is dependent** — when the value's
  type mentions the value's own arguments and one of those is a local variable:

  ```
  let nc = noConfusionTerm x y q in …                          -- refused
  let nc : NoConfusionTerm x y = noConfusionTerm x y q in …     -- fine
  ```

  This is the same requirement Agda and Idris make. **The message you get is
  poor** — it names machine-generated holes — because the refusal happens inside
  unification, and only the elaboration rule that made those holes knows what
  they stand for. A simple `let n = succ zero in n` needs no annotation.
- **A development-calculus term writes its level arguments.**
  `⌜ congSucc {0 0} a b e ⌝`, never `⌜ congSucc a b e ⌝`. A **surface** term has
  them inferred, which is most of the difference between the two versions of the
  determinacy proof.
- **No automation beyond the rule base.** There is no `auto`, no simplifier, no
  decision procedure. Every proof step above is one you type.
- **No completion of command or identifier names.** Line editing and history
  come from `haskeline`, so the arrow keys work, but tab completes filenames
  only — which is `haskeline`'s default, not a choice.
- **No no-confusion lemma for a constructor with dependent argument types** —
  the system tells you when it skipped one and why.

---

## 13. Command reference

**Bare words act.**

| | |
|---|---|
| `attack` `intro` `solve` `regret` `abandon` | the hole operations |
| `try-core ⌜ term ⌝` | propose a term for the focused hole |
| `apply-core ⌜ f ⌝` / `unify-refine-core ⌜ t ⌝` | apply a function / refine by unification |
| `goto ‹name›` | move to a hole by name |
| `assume ‹x› : ‹S›` / `claim ‹x› : ‹S›` | add a hypothesis / a hole above the focus |
| `unify ‹t› ≟ ‹u›` | solve by unification |
| `eliminate-core ⌜ target ⌝` | induction |
| `reduce` | reduce the focused term in place |
| `along` `into` `back` | move on the chain |
| `cross type` / `cross val` | move into a term |
| `fun` `arg` `dom` `cod` `val` `type` `body` `motive` `target` | descend into a field |
| `param ‹n›` `method ‹n›` `index ‹n›` `arg ‹n›` | descend into a numbered field |
| `prove` / `prove ‹hint›` | let the rule engine choose and run a rule |
| `retry` / `retry ‹n›` | backtrack to a choice point |
| `data ‹D› … where { … }` | declare an inductive family |
| `certify ‹type›` | ask the kernel |
| `qed` | certify and admit the finished proof |

**Colon commands look.**

| | |
|---|---|
| `:show` / `:show ‹name›` | the development / a global |
| `:where` | focus, path, context, expected type |
| `:core ‹t›` `:dev ‹p›` | parse and print |
| `:surface ‹t›` | parse and print a surface term |
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
