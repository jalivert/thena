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

> **Captured 2026-09-13, against commit `aa451f5`.** Every transcript below is
> real output — driven through the program, not written by hand, and re-driven
> whenever the manual changes. Thena is a research prototype under active
> development and it moves weekly: things that were impossible one week are
> ordinary the next, and something that worked yesterday can break. **If a
> transcript here disagrees with what you see, the program is right and this
> document is stale** — please say so.
>
> **Read it in order and type along.** Each chapter continues the session before
> it, so the state builds up as you go; where that is not true the text says
> *From a fresh session.* just above the block, and means it. A `…` inside a
> block stands for output left out for length.

## 1. Starting up

```bash
cabal run thena
```

Use `cabal run` rather than the built binary directly — it is what tells the
program where the prelude file is installed.

You land at a prompt with a small prelude already loaded, and one empty goal.
**This is everything it gives you:**

| | |
|---|---|
| equality | `Eq`, `refl` |
| the unit and empty types | `Unit`, `unit`, `Empty` |
| conjunction | `And`, `both`, with `andLeft` and `andRight` proved |
| dependent pairs | `Sigma`, `pair`, with `fst` and `snd` proved |
| lists | `List`, `nil`, `cons` |
| the result of comparing | `Comparison`, `same`, `different` |
| a decision, with its evidence | `Dec`, `yes`, `no` |
| transport along an equality | `transport` proved |
| deciding a literal equality | `String.dec`, `Char.dec`, `Int.dec` proved, each from two trusted laws |

`String`, `Char`, `Int` and `Token` are in scope as well — those are built in
rather than declared, so they are there in any environment — along with the
four primitive functions, `String.eq`, `Char.eq`, `Int.eq` and `String.append`.

`String.dec a b` answers `yes` with a proof that `a` and `b` are equal, or `no`
with a refutation, and on a name it does not know it is stuck — so a proof that
eliminates it gets the equality in one branch and its refutation in the other.
That is what `String.eq` alone cannot give you, and it is the reason the prelude
has both. `String.dec` is a *definition*, written in `prelude/prelude.thena`,
and what it rests on is two `trusted` claims about `String.eq`: that a `same`
answer means the two really are equal (`String.eqEqual`), and that the
comparison answers `same` of a literal and itself (`String.eqRefl`). Chapter 9
is what those are; `isSame` is the helper that tells the two answers apart.

**There is no `Nat`, and no arithmetic.** A module that wants numbers declares
them, which every example here does; `Int` is a primitive with literals and
equality and nothing to do induction over. The prelude is deliberately the
logical equipment and nothing else — it is `prelude/prelude.thena`, a readable
file you can change.


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
| a trusted term | `trusted T e` — see chapter 9 |

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
Type : Type (suc ?ℓ4695)
```

`?ℓ229` is an unknown level. It is not a default and it is not zero — it is
carried along until something pins it down, which is what lets one declaration
serve every level.

**Smaller universes sit inside larger ones.** A `Type₀` is accepted where a
`Type₁` is wanted:

```
thena spine> :infer core`(\ (A : Type₁) -> A) Type₀`
(λ (A : Type₁) -> A) Type₀ : Type₁
```

The corners are not decoration here. A bare argument is a *surface* term and a
surface λ binder carries no type, so `\ (A : Type₁) -> A` is the development
calculus's λ and has to say so.

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
data Eq {ℓ₆₆} (A : Type (ℓ₆₆)) : A -> A -> Type (ℓ₆₆) where
  { refl : ∀ (a : A) -> Eq {ℓ₆₆} A a a }
```

So `Eq` on its own is not a term — `Eq {0} Nat x y` is. **Written on the
surface, the levels are yours not to write**: a use of a polymorphic name gets
one unknown per parameter, and unification settles them.

```
thena spine> :infer refl
refl : ∀ (A : Type (?ℓ4702)) (a : A) -> Eq {?ℓ4702} A a a
```

Written in the development calculus they are explicit, and **prenex** — a use
writes all of them or none:

```
thena spine> :infer core`refl {1}`
refl {1} : ∀ (A : Type₁) (a : A) -> Eq {1} A a a
thena spine> :infer core`refl {1 0}`
refl has 1 level parameter, and was given 2 level arguments
its level parameters are prenex, so a use writes every one of them
```

A datatype over two of them gets two parameters, and its own level is their
join:

```
thena spine> :show And
data And {ℓ₅₆₆ ℓ₅₆₇} (A : Type (ℓ₅₆₆)) (B : Type (ℓ₅₆₇)) : Type (ℓ₅₆₆ ⊔ ℓ₅₆₇) where
  { both : A -> B -> And {ℓ₅₆₆ ℓ₅₆₇} A B }
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

---

## 4. Declaring a datatype

```
thena spine> data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> open Nat
opened Nat
thena spine> :show Nat
data Nat : Type₀ where
  { zero : Nat
  ; succ : Nat -> Nat }
```

**A declaration opens a namespace named after itself**, so the type is `Nat.Nat`
and the constructors are `Nat.zero` and `Nat.succ`. A written `Nat` reaches the
type anyway, because a declaration's short name is derived from the environment;
`open Nat`, on the line above, is what lets the rest of this chapter write
`zero` and `succ` without the prefix. `DECISIONS.md`, *Modules and namespaces*,
has the whole of it — the other four forms of `open`, and `namespace` in a file.

**A later declaration may take that short name, and it is allowed to.** Prove a
theorem called `Nat` and the word `Nat` means the theorem from the `qed` on; the
datatype is still there and is still `Nat.Nat`, which is how you write it. You
are told before it costs you anything — `:theorem Nat : Type₁` answers

> warning: the name Nat reaches Nat.Nat here, so proving it shadows that one —
> it is then reached by writing it in full

so that renaming the theorem is still free. The same warning, in the past tense,
comes from `declare` and from a loaded file, where the name is in the
environment the moment the line lands. Nothing is lost either way: both names
exist, and a path always reaches what it names.

Now the three commands of the last chapter have something to look at:

```
thena spine> :core succ (succ zero)
succ (succ zero)
thena spine> :infer succ (succ zero)
succ (succ zero) : Nat
thena spine> :convert succ zero ≟ succ zero
succ zero ≟ succ zero   yes
```

**Write the universe as a bare `Type` and it is worked out for you**, from the
constructors' own levels, and becomes a level parameter if nothing pins it:

```
thena spine> data Box (A : Type) : Type where { box : A -> Box A }
declared Box
thena spine> :show Box
data Box {ℓ₄₉₁₀} (A : Type (ℓ₄₉₁₀)) : Type (ℓ₄₉₁₀) where
  { Box.box : A -> Box {ℓ₄₉₁₀} A }
```

A written `Typeₙ` is still checked rather than believed:

```
thena spine> data Big : Type₀ where { wrap : Type₀ -> Big }
refused: the argument x of Big.wrap lives in Type₁, which the datatype's own Type₀ does not contain
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
thena spine> :show Nat.lemmata.noConfusion
Nat.lemmata.noConfusion : ∀ (x : Nat) (x' : Nat) -> Eq {0} Nat x x' -> Nat.lemmata.NoConfusion x x'
Nat.lemmata.noConfusion = λ (u : Nat) (v : Nat) (q : Eq {0} Nat u v) -> elim Eq {0} …
```

(`:show` prints the body too; it is one long line and is elided here.)

Indexed families get one too, and there the lemma gives **each side its own
indices**: a `Ladder x` and a `Ladder x'` are compared by a *chain* of equations
— one between the indices, then one between the elements with the first
transported along it — rather than by a single `Eq`. That is what lets the lemma
be applied where the two sides are not visibly at the same index, which is what
acyclicity needs. Where a family has no indices the chain is the one equation it
always was, and the lemma reads exactly as `Nat.lemmata.noConfusion` does above.

The same chain is how an argument whose *type* mentions an earlier argument is
handled: the later equation is stated after transporting along the earlier one,
so every equation is still between two terms of one type.

```
thena spine> data Ladder : Nat -> Type₀ where { base : Ladder zero ; step : ∀ (n : Nat) (r : Ladder n) -> Ladder (succ n) }
declared Ladder
thena spine> :infer Ladder.lemmata.noConfusion
Ladder.lemmata.noConfusion : ∀ (x : Nat) (x1 : Ladder x) (x' : Nat) (x'1 : Ladder x') (q : Eq {0} Nat x x') -> Eq {0} (Ladder x') ((elim Eq {0} (Nat) (λ (u : Nat) (v : Nat) (w : Eq {0} Nat u v) -> Ladder u -> Ladder v) ((λ (a : Nat) (z : Ladder a) -> z)) (x x') q) x1) x'1 -> Ladder.lemmata.NoConfusion x x1 x' x'1
```

`DECISIONS.md`, *Thena does not assume K*, says what that buys and what it does
not.

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
of its own, so that `goto-named "‹name›"` always means one place.

There are three `goto`s and they differ in what they take. `goto-named "h"`
searches for a hole by the name you can see; `goto` is the one a rule body uses,
taking the variable it is holding rather than a name; and `goto-root` takes
nothing and goes to the top of the development. `goto-root` is the only move
that cannot fail — `back` refuses when there is nothing above it, and
`goto-root` is already where it is going.

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
thena spine> try-core core`_`
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
thena spine> :theorem idPoly : ∀ (A : Type) -> A -> A
proving idPoly : ∀ (A : Type (?ℓ5790)) -> A -> A
thena spine> try-core core`\ (A : Type) (a : A) -> a`
thena spine> solve
thena spine> qed
idPoly {ℓ₅₈₀₂} : ∀ (A : Type (ℓ₅₈₀₂)) -> A -> A   ∎
```

Sometimes one level is not enough, and the proof leaves a *relation* between two
of them. That relation is part of the theorem, and is printed inside the type,
before a `⊢`:

```
thena spine> :theorem lift : Type -> Type
proving lift : Type (?ℓ5804) -> Type (?ℓ5805)
thena spine> try-core core`\ (x : Type) -> x`
thena spine> solve
thena spine> qed
lift {ℓ₅₈₁₃ ℓ₅₈₁₄} : (ℓ₅₈₁₃ ≤ ℓ₅₈₁₄) ⊢ Type (ℓ₅₈₁₃) -> Type (ℓ₅₈₁₄)   ∎
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
thena spine> try-core core`lift {1 0}`
thena spine> solve
thena spine> qed
the kernel refused it
1 is not at most 0
thena spine> :abandon
abandoned bad
```

`:revalidate` says the same thing at any point, without closing the proof.

**A refused `qed` leaves the proof open**, which is the point — nothing is
thrown away because the kernel said no. `:abandon` is how you put it down, and
until you do, `:theorem` will tell you there is one in progress.

### The proof commands

| | |
|---|---|
| `attack` | turn the focused hole into a guess, ready to be built |
| `intro` | move one `∀` binder from the goal into the guess body |
| `` try-core core`term` `` | propose a term for the focused hole |
| `solve` | accept the focused guess — it becomes a definition |
| `regret` | throw away a guess's body, back to a plain hole |
| `abandon` | remove the focused hole entirely |
| `` assume "‹x›" core`‹S›` `` | add a hypothesis above the focus |
| `` claim "‹x›" core`‹S›` `` | add a new hole above the focus |
| `` unify core`‹t›` core`‹u›` `` | solve holes by unification |
| `reduce` | reduce the focused term one step, in place |

`reduce` acts on whatever term the cursor is standing on, and the change is
committed to the development:

```
thena spine> :theorem two : Nat
proving two : Nat
thena spine> try-core core`(\ (x : Nat) -> succ x) zero`
thena spine> into
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
thena core> claim core`Nat`
name for the new hole?
> k
claimed k
thena core> :abandon
abandoned two
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
fun  arg  dom  cod  val  type  body  motive  target  claimed  actual
param ‹n›   method ‹n›   index ‹n›   arg ‹n›
```

The numbered ones count from one. `claimed` and `actual` descend into the two
types a trusted term carries — the type it claims, and the type its body was
actually checked at; `body` reaches the body itself, as it does under a `λ` and
in a `let`.

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

`` eliminate-core core`target` `` is the induction tactic. It builds the motive, works out
what each case has to prove, and posts one hole per case.

The example needs `Nat`, addition, and congruence of `succ`.
`examples/Tier0.thena` declares the first two; the third is one line. It
declares its own `Nat`, so it wants a session that has not already got one.

*From a fresh session.*

```
thena spine> :load examples/Tier0.thena
module examples.Tier0
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
thena spine> eliminate-core core`n`
subgoals: zeroMethod, succMethod
```

Two subgoals, named after the constructors. Look at what it built:

```
thena spine> :show
  let ? plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n ≐ (
    λ (n : Nat) ->
    let ? zeroMethod : Eq {0} Nat (plus zero zero) zero in
    let ? succMethod : ∀ (_ : Nat) -> Eq {0} Nat (plus _ zero) _ -> Eq {0} Nat (plus (succ _) zero) (succ _) in
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
thena spine> try-core core`refl {0} Nat zero`
thena spine> solve
thena spine> along
thena spine> try-core core`\ (x : Nat) (ih : Eq {0} Nat (plus x zero) x) -> congSucc {0 0} (plus x zero) x ih`
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

**A core tactic's argument is written in a fence**, `` core`…` ``. A command
line is a run of operands, exactly as it would be inside a rule body, so
`try-core refl {0} Nat zero` would be four arguments and is refused — the fence
says where the term begins and ends, and inside it nothing needs parenthesising.

**A surface term is written the same way**, `` surface`…` `` — so
`` elaborate surface`succ zero` ``. Every embedded term is written in the fence its
language is entitled to, and an argument in no fence is neither language: it is
a name, a number or a string, read exactly as a rule body reads one. That is why
`goto-named` takes `goto-named "h"` and not `goto-named h` — the second is a
*reference*, and at the prompt there is usually nothing bound to it. (`goto` is
a separate word taking the *variable* a hole binds, which a rule body holds and
the prompt rarely does.)

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

There is a second induction tactic, `eliminate-generalising-core`, which does
follow them: it proves the more general statement, over a fresh copy of every
premise the target's indices mention, and applies it to the premises you have.
That is what the surface language's `induction … of` and `case … of` are built
on, and there the extra copies are solved away case by case so you never see
them. Driving it by hand you do see them, as a further argument to every method
you write — unless you ask for the split rather than for the eliminator, which
is the next section.

### One goal per case, with its binders already in scope

`induction-core core`target`` is the same split the surface language writes,
driven by hand. It posts one hole per case, and each hole is *inside* that
case's own binders, with the equations the split stated already discharged. So
you write the body of the arm and nothing else.

```
thena spine> :theorem plusZeroAgain : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n
proving plusZeroAgain : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n
thena spine> attack
thena spine> intro
thena spine> into
thena spine> along
thena spine> induction-core core`n`
subgoals: zeroMethod, succMethod
subgoals: zeroCase
subgoals: succCase
```

`zeroCase` and `succCase` are the two to prove. Walk into the step case and
look at it:

```
thena spine> goto-named "succCase1"
thena spine> :where
focus
  let ? succCase1 : Eq {0} Nat (plus (succ u) zero) (succ u) in
path
  root ▸ ≐ plusZeroAgain ▸ n ▸ zeroCase ▸ zeroMethod ▸ ≐ succCase ▸ u ▸ ih ▸ n1
context
  n : Nat
  zeroCase : Eq {0} Nat (plus zero zero) zero
  zeroMethod : Eq {0} Nat (plus zero zero) zero
  u : Nat
  ih : Eq {0} Nat (plus u zero) u
  n1 = succ u : Nat
type
  Eq {0} Nat (plus (succ u) zero) (succ u)
```

Three things to notice. The constructor's argument is `u` and the induction
hypothesis is `ih`, both in scope as ordinary assumptions — `succ`'s argument
has no name in the declaration, so one was minted; where a constructor does name
its arguments, those are the names you get. `n`, the variable the proof was
about, is a *definition* inside this case: `succ u`, which is what the split
refined it to. And the goal is the one you would expect, with no equation left
to discharge, where `eliminate-core` would have handed you the method type and
left the lambda to you.

Fill both cases and finish:

```
thena spine> try-core core`congSucc {0 0} (plus u zero) u ih`
thena spine> solve
thena spine> goto-named "succCase"
thena spine> solve
thena spine> goto-named "zeroCase1"
thena spine> try-core core`refl {0} Nat zero`
thena spine> solve
thena spine> goto-named "zeroCase"
thena spine> solve
thena spine> goto-named "zeroMethod"
thena spine> solve
thena spine> goto-named "succMethod"
thena spine> solve
thena spine> goto-named "plusZeroAgain1"
thena spine> solve
thena spine> goto-root
thena spine> solve
thena spine> qed
plusZeroAgain : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n   ∎
```

Each case can be proved in any order, and `goto-named` is how you get to one:
the holes keep their names for as long as they are open. `case-core` is the
other word — the same thing without the induction hypotheses, for a proof that
takes a value apart rather than recursing on it. A case the split proves
impossible is not posted at all; you are shown only what is left to do.

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
prove
claim ‹ty›
assume ‹ty›
quantify ‹ty›
no-nesting []
ihs-for ‹t› ‹c›
ihs-for ‹t› ‹c›
reverse-onto [] ‹acc›
reverse-onto [x, ...xs] ‹acc›
apply-all ‹f› []
apply-all ‹f› [x, ...xs]
instantiate-with ‹f› ‹vs›
name-or-stem ‹n› ‹stem›
name-or-stem ‹n› ‹stem›
intro-arm-binders [] [] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders [p, ...ps] [(b, none), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders [p, ...ps] [(b, none), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders [p, ...ps] [(b, (some f)), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders [p, ...ps] [(b, (some f)), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders [p, ...ps] [(b, oc), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
dotted-position-is-forced ‹e› (some f) ‹vs› ‹k›
intro-arm-binders ‹ps› [(b, none), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders ‹ps› [(b, none), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
intro-arm-binders ‹ps› [(b, (some f)), ...bs] ‹vs› ‹ds› ‹fs› ‹k›
bind-friendlies [] ‹vs› ‹ds›
bind-friendlies [(n, f), ...fs] ‹vs› ‹ds›
bind-solved [] ‹k›
bind-solved [(n, v), ...ds] ‹k›
same-length [] []
same-length [p, ...ps] [n, ...ns]
arm-for ‹t› ‹c›
arm-for ‹t› ‹c›
pick ‹w› ‹c› ‹p› ‹b› ‹r›
pick ‹w› ‹c› ‹p› ‹b› ‹r›
arm-needs-body ‹k› (some b)
arm-needs-body ‹k› none
elaborate-arm ‹t› ‹c› ‹sub› ‹bs› ‹fs› (p, ob)
case-needs-an-arm ‹t› ‹c› ‹sub› ‹bs› ‹fs› (some a)
case-needs-an-arm ‹t› ‹c› ‹sub› ‹bs› ‹fs› none
vanished-case-takes-no-body none
vanished-case-takes-no-body (some (p, none))
case-must-vanish none
case-must-vanish (some h)
one-case ‹t› ‹c› ‹sub› ‹bs› ‹fs›
one-case ‹t› ‹c› none ‹bs› ‹fs›
one-case ‹t› ‹c› (some sub) ‹bs› ‹fs›
arm-must-be-for-this-datatype ‹a› ‹b›
arms-are-for-this-datatype ‹t› ‹d›
arms-are-for-this-datatype ‹t› ‹d›
one-arm-per-constructor ‹a› ‹b›
arm-not-repeated ‹w› ‹t›
arm-not-repeated ‹w› ‹t›
arms-are-distinct ‹t›
arms-are-distinct ‹t›
split-cases ‹t› [] [] ‹m›
split-cases ‹t› [c, ...cs] [mh, ...ms] ‹m›
split-over ‹t› ‹cs› (hs, m)
split-claim ‹t› ‹x›
split-claim ‹t› ‹x›
split-elaborate ‹t›
argument-patterns [] ‹acc›
argument-patterns [(b, oc), ...bs] ‹acc›
argument-patterns [(b, oc), ...bs] ‹acc›
argument-patterns [(b, oc), ...bs] ‹acc›
argument-pattern ‹b›
open-case ‹mh› none ‹bs› ‹fs›
open-case ‹mh› (some sub) ‹bs› ‹fs›
split-holes [] [] ‹m›
split-holes [(c, ihs), ...cs] [mh, ...ms] ‹m›
split-holes-over ‹cs› (hs, m)
with-hypotheses []
with-hypotheses [c, ...cs]
without-hypotheses []
without-hypotheses [c, ...cs]
run-block ‹t›
intro-binders ‹t› ‹k›
intro-binders ‹t› ‹k›
intro-binders ‹t› ‹k›
intro-binders ‹t› ‹k›
spine-arguments ‹h› ‹f› ‹t›
spine-arguments ‹h› ‹f› ‹t›
thena spine> prove
chose 5340: intro
```

Three rules matched, so the engine reports which one it took and leaves a
**choice point** behind — the number is its identifier.

```
thena spine> :choices
5340  intro   untried: solve, regret, prove
```

`retry` backtracks to the nearest choice point and takes the next alternative.
Here both remaining alternatives fail, so it exhausts the choice point and
undoes the whole thing:

```
thena spine> retry
retrying 5340: solve
backtracking to 5340: regret
thena spine> :show
▶ let ? id : ∀ (A : Type₀) -> A -> A in
  id
thena spine> :choices
5340  regret   untried: prove
```

Search is meant to be inspectable, not a black box: you can always see what was
chosen, what is untried, and undo it.

Choice-point numbers are unique but **not consecutive** — they are drawn from
the same counter as variable names, so the first one in a session is rarely `1`.

### A choice point is not reached by accident

A failing command unwinds looking for an alternative — that is what makes a
tactic a search. **It stops at the line you typed.** A choice point an earlier
line left is yours to reach with `retry`, and nothing reaches it for you:

*From a fresh session.*

```
thena spine> :theorem t : ∀ (A : Type₀) -> A -> A
proving t : ∀ (A : Type₀) -> A -> A
thena spine> prove
chose 4690: attack
thena spine> regret
thena spine> back
stuck: already at the root
  undoing that would backtrack to 4690, which was chosen before this line — retry 4690 to take it
```

`regret` took the guess back off and `back` had nothing left to pop. Without the
boundary, that `back` would have taken `prove`'s untried alternatives and put the
guess back — a navigation command undoing the line before it.

Nothing is forbidden: `retry 685` still takes it. The point is that crossing out
of your own line is something you ask for, because backtracking past a line
takes a route on which that line was never typed — so the command that caused it
could not have been given.

A choice point the *current* line made is reached as it always was, which is why
`retry` above still falls through `solve` into `regret` in one command.

### What is on offer here

`:matches` lists every rule whose head passes at the focus — the same list the
engine would search, in the order it would search it. **It takes no argument.**
A rule that wants one is shown with a placeholder for it, and elaboration's
clauses are in the list like everything else, because elaboration is search:

```
thena spine> :matches
attack
try-core ‹t›
abandon
eliminate-core ‹t›
eliminate-generalising-core ‹t›
prove
…
```

### Watching the machine

`:step on` puts the engine in single-step mode, and `:step` advances one
instruction. This is how you see what a rule actually does — `attack` is a rule
whose body is one primitive:

```
thena spine> :step on
thena spine> attack
pc
  0  prim-attack
env
  (empty)
stack
  call, 0 instruction(s) to resume
  call, 0 instruction(s) to resume (returned)
  call, 0 instruction(s) to resume (returned)
  call, 0 instruction(s) to resume (returned)
thena spine> :step
pc
  (empty)
env
  (empty)
stack
  call, 0 instruction(s) to resume
  call, 0 instruction(s) to resume (returned)
  call, 0 instruction(s) to resume (returned)
  call, 0 instruction(s) to resume (returned)
thena spine> :run
thena spine> :step off
```

`:run` finishes the current run without stepping; `:step off` leaves the mode.

Single-stepping is the smallest of a family. `:step ‹n›` lets every line do at
most `n` instructions before handing control back, and `:run ‹n›` advances a
paused run by that many without changing the setting — so `:step on` is `:step 1`
and `:step off` is no budget at all. An editor uses this to stay responsive: it
advances a long search a slice at a time, draws whatever it wants to draw
between slices, and stops the search by simply not asking for the next one.

*From a fresh session.*

```
thena spine> data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> open Nat
opened Nat
thena spine> :step 6
thena spine> declare idn : Nat -> Nat ; idn = \ n -> n
pc
  0  u = universe-at l
  1  return u
env
  l = Type (?ℓ4878)
stack
  call, 14 instruction(s) to resume
  call, 8 instruction(s) to resume
  call, 0 instruction(s) to resume (returned)
thena spine> :run 6
pc
  0  u = universe-at l
  1  return u
env
  l = Type (?ℓ4880)
stack
  call, 11 instruction(s) to resume
  call, 14 instruction(s) to resume (returned)
  call, 8 instruction(s) to resume
  call, 0 instruction(s) to resume (returned)
thena spine> :run
solved: ?ℓ4876
solved: ?ℓ4878
solved: ?ℓ4880
already equal
thena spine> :step off
```

---

## 9. The kernel

The kernel is an independent check. It does not trust the machine.

| | |
|---|---|
| `:extract` | read the finished term off the development |
| `` certify core`‹type›` `` | check the extracted term really has that type |
| `:revalidate` | re-derive the whole development's well-formedness from scratch |

*From a fresh session.*

```
thena spine> data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> open Nat
opened Nat
thena spine> :goal Nat
▶ let ? goal : Nat in
  goal
thena spine> try-core core`zero`
thena spine> solve
thena spine> :extract
let goal = zero : Nat in goal
thena spine> certify core`Nat`
certified
thena spine> certify core`Nat -> Nat`
the kernel refused it
in the term:
  let goal = zero : Nat in goal has type Nat
    but Nat -> Nat was expected
    Nat -> Nat and Nat do not match
```

An unfinished proof cannot be extracted, and the message says exactly what is
still open:

```
thena spine> claim "k" core`Nat`
thena spine> :extract
stuck: not finished: the hole k is still open, so there is no term yet
```

`qed` runs `certify` for you. These commands are for inspecting a proof
mid-flight, or for convincing yourself the machine has not cheated.

### Saying "take my word for it"

Some things are true and you cannot prove them here. `trusted T e` is a term
whose type is **asserted**: `e` is checked as usual, at whatever type it really
has, and the term is then given `T` with nothing relating the two.

`honest` below asserts something that is already true, so it goes in without
comment. `liar` asserts something false, and a definition does not reach the
environment unless the session's trust setting allows what it rests on — so it
has to be asked for. The next section is what that setting is; `:trust any`
allows everything, and we put the setting back straight afterwards:

```
thena spine> declare honest : Eq Nat zero zero ; honest = trusted (Eq Nat zero zero) (refl Nat zero)
…
thena spine> :trust any
…
thena spine> declare liar : Eq Nat zero (succ zero) ; liar = trusted (Eq Nat zero (succ zero)) (refl Nat zero)
…
thena spine> :trust no-undischargeable
…
thena spine> :whnf honest {0}
refl {0} Nat zero
thena spine> :whnf liar {0}
trusted (Eq {0} Nat zero (succ zero)) (Eq {0} Nat zero zero) (refl {0} Nat zero)
```

**The kernel's check is then modulo the claims you made this way** — which is the
trade every system makes somewhere, under one name or another.

What makes it worth having rather than an axiom is that it **reduces when the
claim comes true**, which is what the two reductions above show. The term carries
both types, the one claimed and the one its body really has, and when they turn
out to be the same type the whole thing contracts to the body: `honest`'s claim
was met, so nothing is left of it. `liar`'s was not, and what prints shows you
both halves. As the names inside them become known the two converge, so a term
still printing as `trusted` is a term whose claim is still load-bearing.

You can leave the type to be worked out, as anywhere else — `trusted _ e` is an
ordinary placeholder in that position, and `claimed` and `actual` are the two
field words for navigating into one (chapter 6).

### How much of that you want to allow

`:trust` says what the proof in front of you rests on, and how much the session
is willing to accept. Every claim is one of three things:

| | |
|---|---|
| discharged | the two types are convertible, so the claim is met and the trust is carrying nothing |
| pending | not met, and not impossible — some instance could still make the two agree |
| undischargeable | it can never be met, by any instance, in any later session |

The last one is decided by comparing the two types position by position: where
they are built from different formers at some position, no substitution will ever
bring them together. `Eq Nat zero (succ zero)` against `Eq Nat zero zero` agrees
at the head and clashes at the third argument, which is why the test looks all
the way down rather than at the head alone.

A claim is read **at the use where the use settles it, and at the definition
otherwise**, and the report says which — because the same node can be honest in
a definition and a lie at a use of it. `liar`'s claim is undischargeable at
`liar {0}` and tells you nothing at all read from a partial application.

`:trust none`, `:trust no-undischargeable` and `:trust any` set how much is
allowed. A session starts at `no-undischargeable`, and the setting is asked at
**both** of the ways a definition reaches the environment — `qed` refuses a proof
resting on something it does not permit, and `declare` refuses a definition the
same way, which is why `liar` above had to be asked for. Both ask after the
kernel has already accepted the term, because this is your policy and not the
kernel's judgement.

```
thena spine> :trust
trust: no undischargeable trust
  resting on nothing
thena spine> :theorem reckless : Eq {0} Nat zero (succ zero)
proving reckless : Eq {0} Nat zero (succ zero)
thena spine> attack
thena spine> into
thena spine> try-core core`liar {0}`
thena spine> solve
thena spine> back
thena spine> solve
thena spine> :trust
trust: no undischargeable trust
  undischargeable, at the use of liar
    claims Eq {0} Nat zero (succ zero)
    body   Eq {0} Nat zero zero
thena spine> qed
certified
the trust level refused it
trust: no undischargeable trust
  undischargeable, at the use of liar
    claims Eq {0} Nat zero (succ zero)
    body   Eq {0} Nat zero zero
thena spine> :trust any
trust: any trust
  undischargeable, at the use of liar
    claims Eq {0} Nat zero (succ zero)
    body   Eq {0} Nat zero zero
thena spine> qed
reckless : Eq {0} Nat zero (succ zero)   ∎
  undischargeable, at the use of liar
    claims Eq {0} Nat zero (succ zero)
    body   Eq {0} Nat zero zero
```

Nothing is prevented for long: the proof is left standing, and the setting is one
word away. What changes is that the word is yours.

**Only `none` is a guarantee.** `no-undischargeable` stops a claim that is
provably false, and it does not stop a false one — a claim can be discharged at
every instance anyone has written down and still be nonsense, and `Empty` is
provable that way. Treat the middle setting as hygiene, not as safety.

### What the prelude itself asks you to trust

This is not only a facility for your own proofs: the prelude uses it. Deciding
whether two strings are equal is the case, and it is the one that forced the
feature. `String.eq` computes — it answers `same` or `different` on two literals
— but nothing in the type theory connects that answer to the equality type, and
no term you can write closes the gap. So `String.dec` is a definition resting on
two claims about `String.eq`, and `:trust` names both:

```
thena spine> :trust no-undischargeable
trust: no undischargeable trust
  resting on nothing
thena spine> :theorem decides : Dec {0 0} (Eq {0} String "x" "x")
proving decides : Dec {0 0} (Eq {0} String "x" "x")
thena spine> attack
thena spine> into
thena spine> try-core core`String.dec "x" "x"`
thena spine> solve
thena spine> back
thena spine> solve
thena spine> :trust
trust: no undischargeable trust
  pending, in String.dec · String.eqEqual
    claims Eq {0} String a b
    body   Eq {0} String a a
  pending, in String.dec · String.eqRefl
    claims Eq {0} Comparison (String.eq a a) same
    body   Eq {0} Comparison same same
thena spine> qed
decides : Dec {0 0} (Eq {0} String "x" "x")   ∎
  pending, in String.dec · String.eqEqual
    claims Eq {0} String a b
    body   Eq {0} String a a
  pending, in String.dec · String.eqRefl
    claims Eq {0} Comparison (String.eq a a) same
    body   Eq {0} Comparison same same
```

`in String.dec · String.eqEqual` is the route: the claim is not in your proof, it
is in a definition your proof reached through another one. Both read **pending**,
and here is why that is worth understanding rather than working around. The
claims are read at `String.eqEqual`'s own definition, where `a` and `b` are its
binders and nothing is settled — and they are read there rather than at `"x"`
and `"x"` because the walk takes one hop into a definition and stops. It is not
a normaliser, deliberately: finding out which claims *survive* reduction means
reducing, and `qed` may not be made to diverge.

So `:trust none` will not close this proof, even though `String.dec "x" "x"`
reduces to `refl {0} String "x"` with nothing trusted left in it. The strictest
setting is a statement about what a proof *reaches*, not about what is left
after it runs. If you want it, the two laws are four lines of
`prelude/prelude.thena` and you can read exactly what you are taking on.

---

## 10. Sessions

You can have several proofs open, park them, and come back.

| | |
|---|---|
| `:theorem ‹x› : ‹T›` | start a proof |
| `:suspend` | park what you are working on, under its name |
| `:resume ‹name›` | pick a parked one back up |
| `:proofs` | list what is open and what is parked |
| `:abandon` | throw away what you are working on |
| `:undo` | undo the last command that changed anything |
| `qed` | certify and admit |

```
thena spine> :theorem two : Nat
proving two : Nat
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

**`:undo` goes back one *change*, not one line.** A command that succeeded and
altered nothing does not have to be undone twice — so it does not take a step of
its own, and the next `:undo` reaches past it to the last thing that did
something. A proof boundary clears the history, which is why the second one here
has nothing left to do.

Declarations made while a proof is suspended are still there when you resume —
globals are session-wide, proofs are not.

---

## 11. Loading a file, and what the system has proved

`:load` reads three kinds of file and the extension says which: a `.thena`
**proof module**, a `.thena.script` script of REPL command lines, or one or more
`.thena.rules` rule bases. `:load proof`, `:load script` and `:load rules` say
it out loud instead.

A script is command lines, run in order, and the output is everything those
lines would have printed at the prompt.

### `:consult` puts a rule base on top of the stack

`:load rules …` replaces every base you had with the ones you name. `:consult`
**adds** instead: the bases you name go on top of the stack, and everything
already there goes on being searched underneath them.

*From a fresh session.*

```
thena spine> :consult examples/ChoicePoints.thena.rules
loaded demo (3 rules)
loaded standard (120 rules)
```

**The last thing you consulted is tried first.** The shipped base is consulted for
you when the session starts, so it sits at the bottom and is tried last — which is
why a tactic of your own gets a chance before anything general does. Consulting the
same file twice really does put it on twice; nothing is deduplicated.

Like `:load rules`, it is refused while a proof is open or suspended: the base may
not change under a half-built development.

*From a fresh session.*

```
thena spine> :load examples/DeterminacyTactics.thena.script
…
determinacy : ∀ (t : Term) (t1 : Term) -> Step t t1 -> ∀ (t2 : Term) -> Step t t2 -> Eq {0} Term t1 t2   ∎
```

A **proof module** is the surface language: a header, then declarations, laid
out by indentation. It reports what it declared and nothing else — elaborating
one declaration prints a dozen lines of unification chatter, and a file of them
would bury its own output.

*From a fresh session.*

```
thena spine> :load examples/Tier0.thena
module examples.Tier0
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
a `core` fence instead: `` :infer core`succ zero` ``.

A comment is `--` followed by a space, running to the end of the line, and it
works the same way in all three kinds of file. Without the space it is not a
comment, so `-->` is still yours to use.

### `import` says which modules a file stands on

A module names the other surface modules it depends on, at the top, and **what it
names is loaded first**:

```
module Both where

import Stlc.Terms
import Stlc.Lemmata

open Stlc
```

**A module name is a path, dotted**, under the directory you started `thena` in:
`Stlc.Terms` is `Stlc/Terms.thena`, and `consult Stlc.Tactics` is
`Stlc/Tactics.thena.rules` — the word you write says which kind of file it is, so
the extension is never written. Every step is an ordinary word, so there is no
`..` and no way to name a file whose stem is not one.

**A file's header has to be the name its path gives.** `Stlc/Terms.thena` begins
`module Stlc.Terms where`, and **Thena asks only when somebody imports it**:

```
thena spine> :load test/modules/ImportsMisnamed.thena
test/modules/Misnamed.thena: imported as test.modules.Misnamed, but its header says test.modules.Elsewhere
```

Both names are in the refusal because either could be the slip — the file may be in
the wrong place, or the header may have a typo. A file you load by its path is never
asked, so `:load some/odd-name.thena` works and a file whose path is not a module
name is loadable but not importable.

Loading one file therefore loads a graph, and you see a report for each module as
it goes in, the one you asked for last. **A module is loaded once however many
files reach it**, so two files importing the same third costs nothing. **A cycle is
refused**, and says which path it took. And **a load is all or nothing across the
graph**: if the file you asked for does not go in, nothing it pulled in stays
either, so you fix one file rather than unpicking a half-loaded session.

What a file imports is the file's own business, and so is what it consults: a
module you import is elaborated against *its* rule bases, not yours, which is what
makes a file that works on its own work for whoever imports it.

**And a file reaches nothing else the session happens to hold.** What a module may
write is what it imported, what it declares itself, and the prelude. So a definition
you made at the prompt, or a module you loaded by hand an hour ago, is not in scope
inside a file — you get `not in scope`, the same as if it had never been declared.
Nor is what your own imports imported: if `Pair` imports `Bit` and you import `Pair`,
`Bit`'s names are not yours to write, and a second `import` line is how you say you
want them. The rule is one sentence — **a file is correct on its own or not at all**
— and it is what makes a file you send someone a file that loads.

**An `open` does not travel at all.** The short spellings a file's top level opened
belong to that file and to nobody else — not to the next file you happen to load, and
not to whoever imports it. `open` says how a name is written where *you* stand;
`public` says what your file offers. One word, one job:

```
module Progress where

import Canonical          -- Canonical declares Term and writes `open Term`

open Term                 -- and this file says so for itself

p : Term.Term
p = true                  -- Term.true, written short
```

Without that `open Term` the last line is `not in scope: true`, however many files
that opened it had gone in first. So a bare word in your file means what your own
file says it means: no `import` can make one resolve, and no second `import` can make
one ambiguous between two namespaces you never named.

**The prelude is the one list you start with**, because every surface file imports the
prelude whether it says so or not — Haskell's arrangement. That is why `refl` is a
word you can write anywhere: the prelude writes `open Eq` and you get the prelude.

**The prompt is the exception, deliberately.** A line you type is not a file anybody
will load again, so it reaches everything the session holds, the module you have just
loaded included — which is how you poke at one. An `open` a file left behind stays in
force at the prompt too, for the same reason.

### An act says how far it reaches

An `import` or a `consult` reaches the rest of the file. Give it a block and it reaches
that block instead:

```
module Proofs where

import Stlc.Scratch where       -- in here, and nowhere else
  helper : Scratch.Thing
  helper = Scratch.mk

consult Stlc.Crush where        -- these rules, for this one proof
  hard : …
  hard = do { crush }

after : Scratch.Thing           -- not in scope: Scratch.Thing
```

**Nothing else ends one.** An `import` written inside a `do` block, a `data` block, a
`namespace` block or a definition's body is still the file's, to the end of the file —
the act is what says its extent, so there is no list of constructs to remember.

**Nesting a consult is how you say which base wins.** The innermost one is the last
pushed and the first searched, which is the stack rule over again and not a new one.

What a block does *not* change is the loading: a module you import inside one is a
dependency like any other, loaded before your file, and a definition you wrote in the
block keeps working after it — including for someone who imports your file and cannot
name its type at all. The names in a type are resolved where you write them, once.

No `open` comes with it: a module that opens a namespace at its own top level hands
you the names and never the short spellings, inside a block or out of one. The
`open`s a block may use are the ones you write in it.

**A rule file takes a block on either act too.** The import works exactly as above —
the block's rules may write what the module reaches, the rules after it may not:

```
rule base describing where

import Stlc.Terms where         -- Terms' names and its languages, in here only
  rule describe LC[app]`( ${f} ${a} )` :- do
    say "an application"

rule elsewhere :- do            -- LC is not writable here
  say "something else"
```

**A `consult` block in a rule file is a region of *time* rather than a region of the
file.** There are no proofs here for a pool to be scoped to, so what the block scopes is
the *running* of the rules in it: each one runs with that base pushed on top of the pool
and popped when it finishes, so it is searched first for them and is not in the pool for
the rest of the file.

```
rule base pins where

consult Stlc.Crush where
  rule inside :- do
    call answer              -- Crush's answer, if it has one

rule answer :- do            -- this file's own
  say "pins"

rule outside :- do
  call answer                -- this file's: Crush is not in the pool here
```

**A rule that calls out of its block is refused when you load the file.** Had `outside`
called a rule that only `Crush` defines, the load would fail and name `outside`: the
check asks what each rule reaches, not what the file as a whole brought in, so you hear
about it when you load rather than the first time somebody runs the rule.

Three things to know before you write one.

- **It travels with the rule, not with the file.** The push happens wherever those rules
  are called from, as deep as the call goes, so a base you pin for one rule is briefly
  the highest-priority base in the session of whoever calls it.
- **The clause you wrote against is still there.** A base in front is *tried* first and
  never substituted: every matching rule is offered in pool order, so the worst that
  happens is that something is tried before it.
- **You can see it while it is on.** The push goes into the one pool `:bases` reads, so
  stepping into one of those rules and asking shows that base at the top. At rest it is
  absent, because at rest it really is not in the pool.

> **What you reach is up to the file you imported.** It says what it offers with
> `exporting` and `private`, below, and passes its own dependencies on with
> `public import` and `public consult`.

**A file can hand on a rule base, and `public consult` is how.** A surface file has
no rules of its own, but it can say that the tooling its proofs were written against
travels with it:

```
module Stlc exporting ( Term ) where

public consult Stlc.Tactics        -- and now `import Stlc` brings these rules too
```

Whoever writes `import Stlc` is searched against `Stlc.Tactics` as well, pushed where
their `import` line stands. Without the word it stays the publisher's own: `consult
Stlc.Tactics` means those rules apply while `Stlc` is being elaborated and nowhere
else, and an importer who wants them writes a `consult` of their own. It travels as
far as the `public` lines go — a file that wrote `public import Stlc` hands the same
rules on again.

**A base you consult brings its own dependencies with it.** A rule base that talks
about a language `import`s the surface module declaring it, and that module is loaded
for you, before the file that consulted the base — you do not name it yourself.

### `exporting` says which of your declarations other files may name

Put the list on the header and the rest of the file is yours alone:

```
module Bits exporting ( Bit ) where

data Bit : Type₀ where
  off : Bit
  on : Bit

flip : Bit -> Bit                 -- a helper, and not part of the interface
flip = λ b -> elim Bit () (λ _ -> Bit) (Bit.on Bit.off) () b
```

A file that imports `Bits` may write `Bit`, `Bit.off`, `Bit.elim` and anything else
under `Bit`. Write `flip` and you get `not in scope: flip` — the same answer as for a
module you never imported.

**You name namespaces, not names.** `exporting ( Bit )` means *everything under
`Bit`*, now and later. You never wrote `Bit.elim` or anything under `Bit.lemmata`
yourself, and Thena may generate more there as it improves, so listing names
one by one would mean maintaining a list of names you never typed.

**To export a type without its constructors, name the type:**

```
module Opaque exporting ( Tri.Tri ) where

data Tri : Type₀ where
  low : Tri
  mid : Tri
  high : Tri
```

Now an importer writes `Tri` or `Tri.Tri` and cannot write `Tri.mid` or `Tri.elim`.
The short `Tri` comes along with the type because it is a shorthand *for* the type.

**Leave the clause out and everything is exported**, which is what every file did
before this existed. `exporting ( )` says something else: this file exports nothing.

**Or say what you withhold instead**, which is the clause for a file that exports
most of what it declares:

```
module Bits hiding ( flip ) where   -- everything but this
```

**One clause, either word** — never both — which is the choice `open X ( … )` and
`open X hiding ( … )` already make. The unit is the namespace here too, so
`hiding ( Tri )` keeps the constructors back with the type, and it writes to the same
deny-list `private` does: a header that withholds a declaration and a `private` in
front of it come to the same thing.

**Or keep one thing back and list nothing.** `private` in front of a declaration says
it is yours:

```
module Kept where

data Shown : Type₀ where
  yes : Shown
  no : Shown

private helper : Shown -> Shown
helper = λ s -> s
```

Write `Shown.yes` from another file and it is there; write `helper` and it is not. In
front of a signature it covers the equation under it and stops there; in front of a
`data` declaration it keeps the whole namespace back, constructors and eliminator
included.

### `public import` passes a dependency on

Importing a file gives you what that file exports — not what it imported. So this is
refused:

```
module A where
data Bit : Type₀ where { off : Bit ; on : Bit }

module B where
import A                 -- B uses A

module C where
import B
x : Bit.Bit              -- not in scope: Bit.Bit — C never imported A
```

Put `public` on B's import and C gets it:

```
module B where
public import A          -- and so does whoever imports B
```

**It travels as far as the `public` words go**, so a chain of public imports reaches all
the way. That is how one file can be the thing you import instead of a list of twelve
imports — and why a file's internal dependencies stay internal unless you say otherwise.

`exporting` on your header is about *your* declarations; `public import` is about what
travels through you. **They do not interact**, so a file can export nothing of its own
and still pass a dependency on — the alternative would make you re-list another module's
namespaces as though they were yours. To hand on only part of what you imported, narrow
the import line itself: see *An import can say which names it takes* below.

**Your own file always sees all of itself**, and so does the prompt — after loading
`Bits` you can still `:infer flip`. What the list changes is only what *another file*
may name.

> **It hides names; it does not make anything abstract.** A term carries its real
> names however you wrote the header, so a constructor you kept back can still appear
> in a goal, spelled with a name you are not allowed to type.

### An import can say which names it takes

The header says what a file *offers*. The import line says what you *take*, with the
same two words. `test/modules/Twins.thena` offers both of its datatypes:

```
module test.modules.Twins where

data Bit : Type₀ where
  off : Bit
  on : Bit

data Tri : Type₀ where
  lo : Tri
  hi : Tri
```

So an importer can ask for part of it:

```
import test.modules.Twins ( Bit )          -- this namespace and no more
import test.modules.Twins hiding ( Tri )   -- everything but this
import test.modules.Twins                  -- everything Twins offers
```

**One clause, either word, never both** — the choice `open X ( … )` and a header
already make — and **you name namespaces, not names** here too, so `( Bit )` takes
the type and its constructors together. Write the names the way `Twins` writes them.
Write `Tri.lo` under the first line and you get `not in scope: Tri.Tri`.

**A clause that names something the module does not offer is refused**, and it says
which name missed. `TypoClause.thena` asks `Twins` for a `Nonesuch`:

*From a fresh session.*

```
thena spine> :load test/modules/TypoClause.thena
test.modules.Twins offers no Nonesuch
```

That is the one list Thena checks this way. `open X ( … )` still ignores a word that
is not there.

**Put `public` in front and the narrowing travels.** What goes on to whoever imports
you is what you took, not what you were offered:

```
module Middle where
public import test.modules.Twins ( Bit )   -- Bit is what Middle hands on

module User where
import Middle
x : Bit.Bit                                -- fine
y : Tri.Tri                                -- not in scope: Middle narrowed Tri away
```

It keeps narrowing however long the chain is — a file that public-imports `Middle`
hands on `Bit` alone, and nothing downstream widens it back.

**So you can take a whole module for yourself and re-export part of it**, by writing
both lines. They are two statements about one module and do not cancel:

```
import test.modules.Twins                  -- all of it, for my own use
public import test.modules.Twins ( Bit )   -- but only Bit travels
```

**A rule file's `import` takes the same clause**, and it narrows the object languages
a module offers along with its names: keep `LC` out and a rule written in `LC` is
refused at the tag. `consult` takes no clause.

### A header that lists its exports is told what it passes on

If your header says `exporting ( … )` and a `public import` hands on names the list
does not mention, Thena says so — and hands them on anyway:

*From a fresh session.*

```
thena spine> :load test/modules/GetsThrough.thena
module test.modules.Guarded
  declared Bit
  declared flip
module test.modules.PassesNothingOwn
  declared ownThing
warning: public import test.modules.Guarded passes on Bit, which this file's exporting clause does not list
module test.modules.GetsThrough
  declared mine
```

**The names still travel.** The warning exists because the two statements are about
different things — your list governs *your* declarations, a `public import` governs
what came through you — so a reader of your header alone does not see everything your
file offers. **To silence it, name those namespaces in your own list**, which means
naming another module's namespaces in your header; that is a little clunky and it is
the price of the header being honest.

A header with `hiding ( … )`, or with no clause at all, never raises it: neither
claims to enumerate what the file offers, so there is nothing for a passed-on name to
be missing from.

### `import` and `consult` are typed at the prompt too

The two words a file writes are the two you type: `import examples.Stlc01Syntax`
loads that module by its name and reports it exactly as `:load` would, and
`consult examples.Stlc04TakingTermsApart` pushes that rule base on top of the search
stack. **Neither takes a path** — every step of a module name is an ordinary word,
the act supplies the extension, and `import test/modules/Bit.thena` is refused with
*is not a module name*.

Two things follow from reaching a module **by name**. Its header must be the name
you used, so `import examples.Elsewhere` is refused if the file at that path calls
itself something else — the same check an `import` in a file gets, and one `:load`
by path does not make. And a module already in does nothing: `import` it twice and
the second answers `module examples.Stlc01Syntax is already in` rather than
colliding with its own declarations.

**`public` in front of either word is accepted here and warned.** Nothing imports or
consults a session, so the word has nothing to say at the prompt — and a line pasted
out of a file should act rather than fail to parse. `public consult
examples.Stlc04TakingTermsApart` consults the base and says `warning: public consult
acts as a plain consult: nothing consults a session` first.

**A script states what it stands on too, and its acts are yours afterwards.** A
`.thena.script` file is a list of command lines, and it may write `import` and
`consult` at its top like any other file —
`examples/Stlc08PreservationByTactics.thena.script` names the four modules it reuses
and loads on its own. **What a script brings in stays after the script ends**, which
is where it differs from a module: a module's `consult` lasts only as long as that
module is being elaborated, and a script is a batch of lines you typed, so its
effects are yours.

A `:load` inside a file is still refused — *a :load inside a loaded file is not
followed*. It is the construct `import` and `consult` replace, and it is the one with
no cycle check behind it; an `import` cycle is refused by name.

### An import can stop in the middle and hand you the wheel

A module's declarations are turned into **one program**, and that program is run by
the same machine, through the same loop, as a line you type. So an import is one line
whose program happens to be long — and **a program can stop**.

It stops when a rule reaches `yield`. Nothing in the shipped base does; a base you
consult may, and `examples/demo/Demo08Pausing.thena.rules` is two lines that do:

```
rule elaborate t :- when focus-is-hole (surface-is-placeholder t)
  do yield "a placeholder: fill it and `yield` to carry on"
```

With that consulted, importing a file that leaves a placeholder hands you **that
declaration's own goal**, in the module's own scope. `Demo07Holes` declares
`zeroIsValue` and leaves its proof a `_`:

*From a fresh session.*

```
thena spine> :consult examples/demo/Demo08Pausing.thena.rules
…
thena spine> import examples.demo.pending.Demo07Holes
…
a placeholder: fill it and `yield` to carry on
  elaborating examples.demo.pending.Demo07Holes — yield to carry on, :abandon to give the import up
thena spine> :where
focus
  let ? goal : value`0 value` in
path
  root ▸ zeroIsValue
context
  zeroIsValue : value`0 value`
type
  value`0 value`
```

`:where` says `root ▸ zeroIsValue` — the declaration the file is writing, not a
scratch goal. Fill the hole, type `yield`, and the import carries on and finishes,
declaring everything the module wrote, and any further modules its closure still had
to load.

**Nothing of the module is declared until the whole import finishes.** A suspended
load is one command that has not come back, so `:abandon` puts the session back
exactly as it stood — and it **takes with it anything you declared at the prompt
meanwhile, and says so**: what you proved during the suspension may rest on the
module's own declarations, and leaving it would leave a reference dangling.

**What is in scope while you hold the wheel is what the elaboration has** — the
module's imports and what it has declared so far, not the rest of your session. You
are standing inside that file's elaboration.

While a load is standing still, **a second `import` is refused**, and so is
**`:theorem`** — which brings us to the next part.

### Park the import, prove the lemma, pick it back up

A placeholder usually wants a lemma, and a lemma is a theorem — which you cannot
start while the import is standing, because entering a proof empties the machine's
program and would throw the suspended elaboration away. The refusal says what to do:

```
thena spine> :theorem helper : value`0 value`
a rule has handed control over — yield to hand it back before starting a proof, or :suspend to park the import of examples.demo.pending.Demo07Holes
```

So park it. **It goes into `:proofs`, under the name you imported it by**, beside any
parked proofs you have:

```
thena spine> :suspend
parked the import of examples.demo.pending.Demo07Holes
  it is in :proofs — :resume examples.demo.pending.Demo07Holes to carry on with it
thena spine> :proofs
  examples.demo.pending.Demo07Holes : an import, standing in a yield
```

Now the theorem is allowed, and **it is proved in the module's scope**, because
parking leaves the module's imports and rule bases in force:

```
thena spine> :theorem helper : value`0 value`
proving helper : value`0 value`
thena spine> try-core core`V-num zero NV-zero`
thena spine> solve
thena spine> qed
helper : value`0 value`   ∎
thena spine> :resume examples.demo.pending.Demo07Holes
picked the import of examples.demo.pending.Demo07Holes back up
  still elaborating examples.demo.pending.Demo07Holes — yield to carry on, :abandon to give the import up
thena spine> try-core core`helper`
a placeholder: fill it and `yield` to carry on
(yield to hand control back)
thena spine> solve
a placeholder: fill it and `yield` to carry on
(yield to hand control back)
thena spine> yield
module examples.demo.pending.Demo07Holes
  declared zeroIsValue
```

**The yield's message reprints after every line that steps the machine**, which is why
it appears twice above. It is cosmetic, and `:where` and `:show` do not provoke it.

Four things are worth knowing about that sequence.

**`:suspend`, `:resume`, `:proofs` and `:abandon` do not care which kind of thing they
are acting on.** A proof has a statement and `qed` certifies it; a parked import has
the name you imported it by and nothing certifies it. There is no second word for
parking an import, and no second list.

**Nothing parks or unparks itself.** `qed` does not hand the import back the wheel —
you pick it up when you want it.

**A second `import` is refused while one is parked**, for the same reason the lemma is
proved in the module's scope: there is one set of rule bases and one scope in force,
and the parked import expects to find its own when you pick it up. To give a parked
import up, `:resume` it and then `:abandon` it.

**`yield` while it is parked says *nothing has yielded*.** Yielding is about the
program in front of you, and parking moved that program into the parked import. For
the same reason, you cannot `yield` out of the lemma: it is a different program.

### `:replay` runs a script as though you had typed it

`:replay ‹path›` submits a script's lines one at a time, exactly as if you had
typed each one at the prompt. **It is how a stored proof is taken up again**: a
saved session is a `.thena.script`, so taking one up, reloading it and stepping
through it are one operation at three speeds.

*From a fresh session.*

```
thena spine> :replay test/modules/Replayed.thena.script
module test.modules.Bit
  declared Bit
opened Bit
thena spine> :undo
▶ let ? goal : Type₀ in
  goal
```

**The `:replay` line itself is not part of your session's transcript — the lines
it brought are.** So a transcript built by replaying is indistinguishable from
one you typed: `:undo` steps back through a replay line by line, as above, and
nothing afterwards can tell how those lines arrived. That is also why a stored
proof-script never has to name another one.

A script may `:replay` a script. A script that replays itself — or an ancestor of
itself — is refused, because a replay submits lines and a loop would never end:
*these scripts replay each other*. Sameness is what the files said rather than
what they were called, so the same file under two spellings is still a loop.

**A rule file states its dependencies the same way.** A base that talks about a
language imports the module declaring it:

```
rule base inspecting where

import Stlc.Syntax

open Stlc.Syntax

rule describe LC[var]`${s}` :- do
  say (concat "a variable called " s)
```

Consulting that base loads `Stlc/Syntax.thena` first and tells you it did, because a
base cannot be read before the language it mentions exists. **The module stays in
your session**, unlike a surface file's consults — the base's rules run in your
session later and need the language there. A module you already have is not loaded
again, and a base that will not install takes back whatever it brought in.

**And it may consult.** Write `consult` and the base says which other base its rules
are written against; write `public` in front of the `import` and whoever consults this
base may name the language too, without importing the module themselves:

```
rule base sharp where

public import Stlc.Syntax     -- the language, and you get it too
consult Stlc.Broad            -- the base I build on; you get it, underneath me
```

**A `consult` in a rule file fetches the base and puts it directly beneath this one**,
and all the way down: consult `sharp` and you are searched against `sharp`, then
`Stlc.Broad`, then whatever `Stlc.Broad` is written against. You never have to know
what a base you consult was built on, and the base and its library are always
adjacent — which is the point. The strict reading, where a plain `consult` *asks* and
you supply the base, left the base's position to you, so an unrelated base you had
loaded could sit between a base and its helper and answer a call its author thought
they had pinned.

**`public consult` in a rule file still works and warns that the word is idle**,
since a `consult` there already hands the base on — `warning: public consult
Stlc.Broad acts as a plain consult: a rule file's consult already hands the base on to
whoever consults this one`.

**A surface file's two words are unchanged**: there a plain `consult` is for your own
proofs and `public consult` is what passes the base on to whoever imports you.

**And what a base publishes reaches a rule file as well as a surface file.** A base
that consults `sharp` above may write `Stlc.Syntax`'s language in its own patterns,
because `sharp` said `public import`. A plain `import` in `sharp` would keep the
language to itself — even though consulting it has put that module in your session,
which a rule file may never rely on.

`examples/DeterminacyTactics.thena.script` is the acceptance test for the whole first
milestone. It declares the language of chapter 3 of Pierce's *Types and
Programming Languages* — a seven-constructor term language, a numeric-value
predicate, and a ten-rule small-step reduction relation —

*From a fresh session.*

```
thena spine> :load examples/DeterminacyTactics.thena.script
…
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

**The same proof exists twice.** `examples/DeterminacySurface.thena` is a proof
module in the surface language — 278 lines where the script is 1190 — and it
proves the same theorem through the same rule base:

*From a fresh session.*

```
thena spine> :load examples/DeterminacySurface.thena
module examples.DeterminacySurface
…
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
with backtracking; check finished proofs with the kernel; and load
files of commands.

It also has a **surface language** — layout-sensitive, with implicit arguments
and inferred level arguments — and elaborates it into the development calculus.
**That elaborator is not in the binary**: it is sixteen clauses of one rule in
`rules/standard.thena.rules`, which you can read and change. `prelude/prelude.thena`
and `examples/DeterminacySurface.thena` are both written in the surface
language and elaborated on load.

**It cannot yet:**

- **A λ binder may carry its type, but not braces.** `\ x -> e` takes the
  binder's type from the goal, and `\ (x : Nat) -> e` writes it out — the written
  type is *checked* against the goal's, so the λ you get is the same either way
  and a type that disagrees is refused where you wrote it. You may annotate some
  binders of a group and not others. **`\ {A} -> e` is refused**: a brace in a
  signature says callers may leave that argument out, and a λ binds its
  arguments in order whether or not a caller wrote them. It says
  *"expected a surface term that is a λ whose first binder is explicit"*.
- **A `let` must be annotated when its type is dependent** — when the value's
  type mentions the value's own arguments and one of those is a local variable:

  ```
  let nc = Term.lemmata.noConfusion x y q in …                                  -- refused
  let nc : Term.lemmata.NoConfusion x y = Term.lemmata.noConfusion x y q in …     -- fine
  ```

  This is the same requirement Agda and Idris make. **The message you get is
  poor** — it names machine-generated holes — because the refusal happens inside
  unification, and only the elaboration rule that made those holes knows what
  they stand for. A simple `let n = succ zero in n` needs no annotation.
- **A development-calculus term writes its level arguments.**
  `` core`congSucc {0 0} a b e` ``, never `` core`congSucc a b e` ``. A
  **surface** term has
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
| `` try-core core`term` `` | propose a term for the focused hole |
| `` apply-core core`f` `` / `` unify-refine-core core`t` `` | apply a function / refine by unification |
| `goto-named "‹name›"` | move to a hole by name |
| `goto-root` | move to the root of the development |
| `` assume "‹x›" core`‹S›` `` / `` claim "‹x›" core`‹S›` `` | add a hypothesis / a hole above the focus |
| `` assume core`‹S›` `` / `` claim core`‹S›` `` | the same, asking for the name |
| `` unify core`‹t›` core`‹u›` `` | solve by unification |
| `` eliminate-core core`target` `` | induction |
| `` eliminate-generalising-core core`target` `` | the same, and it generalises the premises the target's indices mention |
| `induction-core core`target`` | the split: one hole per case, inside that case's own binders |
| `case-core core`target`` | the same without the induction hypotheses |
| `reduce` | reduce the focused term in place |
| `along` `into` `back` | move on the chain |
| `cross type` / `cross val` | move into a term |
| `fun` `arg` `dom` `cod` `val` `type` `body` `motive` `target` `claimed` `actual` | descend into a field |
| `param ‹n›` `method ‹n›` `index ‹n›` `arg ‹n›` | descend into a numbered field |
| `prove` | let the rule engine choose and run a rule |
| `retry` / `retry ‹n›` | backtrack to a choice point |
| `data ‹D› … where { … }` | declare an inductive family |
| `declare ‹sig› ; ‹equation›` | elaborate a surface declaration |
| `` quantify "‹x›" core`‹S›` `` | add a ∀-binder above the focus |
| `do { ‹instruction› ; … }` | play a block of instructions here |
| `yield` | hand control back to a rule that yielded |
| `` certify core`‹type›` `` | ask the kernel |
| `qed` | certify and admit the finished proof |

**Colon commands look.**

| | |
|---|---|
| `:show` / `:show ‹name›` | the development / a global |
| `:where` | focus, path, context, expected type |
| `:core ‹t›` `:dev ‹p›` | parse and print |
| `:surface ‹t›` | parse and print a surface term |
| `:parse ‹L› ‹text›` | parse an object term with a language's grammar; `█` is a part not written yet |
| `:parse ‹L›` … `:done` | every line is an L term; Tab at the cursor shows what fits, and completes a production |
| `:infer ‹t›` `:whnf ‹t›` `:convert ‹t› ≟ ‹u›` | type, reduct, convertibility |
| `:elim ‹D›` / `:elim ‹D› ‹universe›` | the elimination rule |
| `:judgment ‹J›` | its rules above the bar, as a paper writes them |
| `:matches` | which rules apply here — it takes no argument |
| `:accepts ‹type›` / `:produces ‹type›` | what takes a value of that type / gives one |
| `:choices` | open choice points |
| `:step on` / `:step` / `:step off` / `:run` | single-step the machine |
| `:theorem ‹x› : ‹T›` | start a proof |
| `:suspend` `:resume ‹name›` `:proofs` `:abandon` `:undo` | session management — a proof, or a parked import |
| `:goal ‹T›` | discard everything and start a fresh scratch goal |
| `:extract` `:revalidate` | read off the term / recheck the development |
| `:trust` | the trust level, and what this proof rests on |
| `:trust none` / `no-undischargeable` / `any` | how much unproved typing to allow |
| `:load ‹path›` | a proof module, a script, or rule bases |
| `:load proof` / `rules` / `script` | say which, rather than by extension |
| `:replay ‹path›` | run a proof-script, line by line, as if typed |
| `:consult ‹path›` | push rule bases on top of the search stack |
| `:bases` / `:rules` | the loaded rule bases / the rules in them |
| `:help` | this table, in one screen |
| `:quit` | exit |
