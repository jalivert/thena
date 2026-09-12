# Decisions

**What Thena decided, and what it means for you.**

Every noteworthy decision goes here — lexing, the type theory, the tactic
language, the session — whatever the layer. Two audiences, and they want the
same thing:

- **us**, so a decision is written down once instead of re-derived from the
  code;
- **you**, if you already know Agda, Coq, Idris or Lean and want to know what is
  different here before you start guessing.

It is not a tutorial and it is not a specification. It is the list of places
Thena made a choice, with enough of the reason to tell whether you would have
made the same one.

**Adding to it:** when a decision is made, add it to its section the same day,
under a heading that says the decision rather than the topic. Say what you can
and cannot write, and give the shortest example that shows it. Reasons are worth
one paragraph, not three; the full argument lives in the design notes.

---

## Concrete syntax and lexing

### An identifier may contain almost anything

*Decided 2026-08-25; consequences accepted 2026-08-29.*

Most languages reserve a generous set of punctuation and give you the rest.
Thena does the opposite: it reserves as little as it can, so you can name things
in your own notation — `≼`, `Γ⊢`, `x'`, `2-cell`, `∂f/∂x` are all one identifier.

**Reserved, and nothing else:**

| | |
|---|---|
| brackets and separators | `(` `)` `{` `}` `[` `]` `;` `,` `"` |
| operator characters | `λ` `∀` `⊢` `≟` `≐` `≈` `▸` `⌜` `⌝` |
| whitespace | |
| keywords | `let` `in` `elim` `forall` `where` `rule` `when` `then` |

A name starts with an ASCII letter, `_`, or any non-reserved character above
ASCII.

**What follows, and it is the part that will catch you out.** `:` and `=` are
*not* reserved, so they can sit inside a name. The lexer takes the longest
match, so:

```
x:S          one identifier, called "x:S"
x : S        three tokens — this is what you want
x: S         two tokens: the identifier "x:" and then S
```

**Ascription must be spaced on its left.** In practice, space both sides and
you will never think about it again.

**ASCII digraphs need a space before them** — `->`, `:-`, `|>`, `[|` — for the
same reason:

```
Type₀->Type₀      one identifier, and "not in scope"
Type₀ ->Type₀     fine — a space after is not needed
Type₀ -> Type₀    fine
```

**The Unicode spellings never need one**, because those characters *are*
reserved:

```
∀ (x : Type₀)-> x     fine
```

**`rule`, `when` and `then` are keywords** and cannot be used as names. Op words
are not: `solve`, `type`, `goal` and the rest stay perfectly good identifiers,
which is why a rule is written `rule ‹name› :- when … then …` and not with the
op words reserved.

---

## Universes and levels

*Decided across MS3 (2026-08-27 to 2026-08-29); written up 2026-08-30.*

### `Type` infers its level; `Typeₙ` pins it

Write `Type` and Thena works out which universe you meant. Write `Type₀`,
`Type₁`, … and it holds you to it.

```
:theorem id : ∀ (A : Type) -> A -> A      the level is inferred, and generalised
:theorem id0 : ∀ (A : Type₀) -> A -> A    this one is Type₀'s copy and nothing else
```

This is Coq's typical ambiguity, with one difference worth knowing: **nothing is
ever defaulted.** An inferred level that the proof does not pin down is *not*
quietly set to zero — it becomes a parameter of the theorem. Defaulting would
turn every polymorphic statement into its `Type₀` instance.

### Level polymorphism is prenex, inferred, and never written

There is no syntax for declaring a level schema, on a theorem or on a datatype.
`qed` generalises whatever levels the proof left open, and `data` does the same
for a declaration.

```
:theorem id : ∀ (A : Type) -> A -> A
try (\ (A : Type) (a : A) -> a) ; solve ; qed
id {ℓ₁₃} : ∀ (A : Type (ℓ₁₃)) -> A -> A   ∎
```

Agda's `∀ {ℓ}` and Coq's `Polymorphic` have no counterpart here. If you want a
particular level, write `Typeₙ` and you will get exactly it; that, and not a
written schema, is the escape hatch when inference does not do what you wanted.

**Prenex means the parameters are all at the front and none is first-class.**
There is no `Setω`, no `Level` in the term language, and levels are not values.

### A use writes its level arguments in braces, and writes all of them

Positionally, in the order they appear in the type, and **numerals only**:

```
id {0}                fine
id {0 1}              fine, for two parameters
id                    refused — 1 level parameter, 0 level arguments given
id {suc 0}            a parse error: a level argument is an atom
```

There is no inference of level *arguments* at a use site the way there is for a
bare `Type`. If a name has level parameters, you write them.

`⊔` — the join — is a real part of the level algebra and prints in inferred
types (`And {ℓ₇₂ ℓ₇₃} : Type (ℓ₇₂ ⊔ ℓ₇₃)`), but **you cannot write one.** Only
inference builds a join.

### A reference's level arguments are part of what it is

`Eq {0}` and `Eq {1}` are two different things and Thena will not convert one
into the other:

```
:convert Eq {0} ≟ Eq {1}      no — Type₀ and Type₁ are different universes
```

Datatypes and definitions are *invariant* in their level arguments. Cumulativity
(below) applies to universes and to a function's result, not to a family's
levels — the same rule Coq's non-cumulative inductives have.

### Cumulativity: smaller universes sit inside larger ones

A term whose type is `Type₀` is usable wherever `Type₁` is wanted. A function's
**codomain** is covariant and its **domain is invariant**, which is the sound
direction: a function that wants `Type₁` arguments cannot stand in for one that
wants `Type₀` arguments.

**But `≟` is still equality**, so subsumption does not make two universes equal:

```
:convert Type₀ ≟ Type₁        no — they are compatible, not equal
```

### A datatype's level is computed from its constructors, and a written one is checked

Write `data D … : Type` and the declared universe becomes the least one
containing every constructor argument; whatever is still open is generalised.

```
data Eq (A : Type) : A -> A -> Type where { refl : ∀ (a : A) -> Eq A a a }
:show Eq
data Eq {ℓ₇} (A : Type (ℓ₇)) : A -> A -> Type (ℓ₇) where …
```

Write `Typeₙ` and the size restriction is checked against exactly that:

```
data Big : Type₀ where { wrap : Type₀ -> Big }
refused: the argument x of wrap lives in Type₁, which the datatype's own Type₀
does not contain
```

**A datatype with nothing to contribute stays polymorphic.** `data Empty : Type
where { }` has no constructor argument, so there is nothing to take the maximum
of and the level is generalised rather than computed to zero.

### A theorem can carry conditions on its levels, and they are part of its type

Generalisation may leave a relation between two of the new parameters that is
neither always true nor always false. It is stored on the theorem and owed again
at every use, and it prints **inside** the type, behind a turnstile:

```
:show lift
lift {ℓ₂₅₂ ℓ₂₅₃} : (ℓ₂₅₂ ≤ ℓ₂₅₃) ⊢ Type (ℓ₂₅₂) -> Type (ℓ₂₅₃)
```

Read it as *given these, this type*: the conditions are hypotheses **you**
discharge by choosing level arguments, not facts that hold anyway. A condition
that held for every instantiation would have been discharged when the theorem
was admitted and never stored — which is why the turnstile is `⊢` and not `⊨`.

Each condition gets its own parentheses, and a theorem with none has no
turnstile at all.

`:infer lift {1 0}` will still print a type — a look does not collect the
conditions — but `:revalidate` and `qed` refuse it: *1 is not at most 0*.

**A level parameter's number is a subscript** — `ℓ₂₅₂`, not `ℓ252` — because a
level *is* a number and the undecorated form reads as one. A level
metavariable, which you will see while a proof is open, keeps its digits behind
a `?`: `Type (?ℓ229)`.

---

### A level your type never mentions is defaulted, not turned into a parameter

A proof can end up mentioning universe levels that its **type** does not. They
come from the elaborator, not from you: every application claims a domain and a
codomain, and nothing pins their levels.

Such a level cannot be determined by anyone. A use site supplies level arguments
and reads the type to know what they mean, so a parameter the type never names
is one every caller must write in order to say nothing at all. Before this,
`a1 = (\ x -> x) zero` came out as:

```
a1 {ℓ₃₂₈ ℓ₃₂₉} : Nat
```

Now those levels are given their **least** value and substituted away:

```
a1 : Nat
```

The partition is exactly occurrence in the type, and it applies to datatypes the
same way — a level only a constructor mentions is defaulted, one the former's
type mentions is kept.

**Real polymorphism is never touched.** `Eq {ℓ} (A : Type ℓ)` mentions `ℓ` in
its own type, so `ℓ` stays a parameter and `e : Eq {ℓ} Nat zero zero` remains
usable at every level. The rule is about levels nobody can choose, not about
levels you might not want to choose.

Least means least, not zero: a level bounded below by 2 is defaulted to 2, and
conditions that the defaulting discharges disappear from the type along with it.

**If there is no least value, the definition is refused.** `2 ≤ max ?a ?b` is a
disjunction — `(2, 0)` and `(0, 2)` both work and neither is smaller — so there
is nothing to default to, and nothing is guessed.

---

## The core language and its type theory

*Nothing recorded yet.*

---

## The development calculus

### There are five components, not McBride's four — the fifth is `∀`

A development is a chain of bindings, and reading the finished term off it folds
each binding into a term former. McBride's four give you three formers:

```
λ x : S      becomes  λ x : S . …          an assumption
x = s : S    becomes  let x = s : S in …   a local definition
? x : S                                    a hole — nothing yet
? x ≐ g : S                                a guess — a hole with a candidate
∀ x : S      becomes  ∀ (x : S) -> …       Thena's fifth
```

Without the fifth, **a development can be a term but never a type**. That
matters as soon as types are written in a language that has to be elaborated:
`∀ (x : A) -> B` needs `x` in scope while `B` is worked out, writing a component
is the only way anything gets into scope, and every component there was folded
into a λ or a `let`.

You can write one, and the tactic that makes one is `quantify`:

```
:theorem t : Type₁
attack
quantify A : Type₀
▶ let ? t : Type₁ ≐ (
    ∀ (A : Type₀) ->
    let ? t1 : Type (?ℓ5) in
    t1
  ) in
  t
```

Note the codomain's universe: **`quantify` claims it at a level of its own**,
not at the ∀'s. `∀ (A : Type₀) -> A` lives in `Type₁` while its codomain lives
in `Type₀`, so inheriting would pin the whole thing a level too low.

The concrete syntax is the one a Π already had, and a leading `∀` run in a
development reads as components — exactly as a leading `λ` run does. So a
development whose *trailing term* is a bare Π needs corners:

```
:dev ∀ (A : Type₀) -> A        two links and a trailing A
:dev ⌜ ∀ (A : Type₀) -> A ⌝    one trailing Π
```

### A name you write is the name you get, even if something else has it

`claim`, `assume`, `define` and `quantify` take the identifier you give them and
do not rename it, refuse it, or number it. Two components may carry the same
name; `goto ‹name›` then takes the first, and what is printed is freshened for
the screen only.

This is what lets the surface language shadow. `\ x -> \ x -> x` and
`let x = a in let x = b in x` mean what they mean in any other functional
language, and the inner binding wins — which could not be true if the
development insisted its identifiers were distinct.

A tactic that needs a name *nobody* has still asks for one, with `fresh-name`.

---

## Tactics and the rule engine

### A rule's head may ask about what the rule was called with

*Decided 2026-09-03.*

A head used to ask only about the focus — is it a hole, does its type reduce to
a Π. So two clauses of one name and one arity could not be told apart, and the
first always won. A test may now take operands, and it is written in
parentheses:

```
rule pick s :- when focus-is-hole (surface-is-name s) then say "a name"
rule pick s :- when focus-is-hole                     then say "not a name"
```

```
thena spine> pick foo
a name
thena spine> pick (Type₀ -> Type₀)
not a name
```

**A bare word is a test of no operands**, and that is why the brackets are
there: a head is a run of tests with nothing between them, so
`when focus-is-hole surface-is-name t` would read as one test applied to two
words. It is the ambiguity a REPL argument run has, answered the same way.

A head may name **only the rule's own parameters** — it runs before the body, so
there is no earlier binding for a name to have come from, and
`when (surface-is-name q)` on a rule that has no `q` is refused when the base is
loaded. A test asked about an argument nobody supplied — which is what `:matches`
does, since it calls nothing — does not rule the clause out.

**There are no parameter kinds.** A test that asks a surface question of a core
term is simply false: the clause does not match, and nothing tells you why. That
is what a Prolog head does, and it is the same bargain the instruction language
already strikes for operands.

### `unify-refine` is `fill` then `solve`

*Decided 2026-09-03.*

McBride's tactic is now written as the two halves it always had:

```
rule fill t :- when focus-is-hole
  then n = fresh-name "refined" ; x = define n t
     ; s = typeof x ; g = goal ; unify-into s g ; prim-try x

rule unify-refine-core t :- when focus-is-hole then fill t ; solve
```

`fill ⌜ t ⌝` parks `t` in a `=`-binding, unifies its type with the goal's
and attaches it as a **guess**; `solve` discharges the guess. Both are callable
on their own, which is the point — elaboration has to get in between the two to
elaborate a term's parts once its shape is known.

**`fill` carries no `-core` postfix**, where `try-core`, `apply-core`,
`eliminate-core` and `unify-refine-core` do. That postfix frees a word for the
surface tactic that will want it; it is not what says an argument is core, since
the corners say that already. Nothing is waiting for `fill`'s word — *fill this
hole with a term I wrote* is `elaborate`. And its argument is a core term
because its caller is a **rule** that has just built one with `apply-to` or
`resolve-name`, not a user typing corners.

**And it fixed a real difference.** `fill` asks `unify-into` where the rule used
to ask `unify`, so cumulativity now reaches the hand-driven tactic:

```
thena spine> :theorem lower : Type₂
thena spine> unify-refine-core ⌜ Type₀ ⌝
already equal
```

That said *"Type₁ and Type₂ are different universes"* before. The term's type
need only be **usable** where the goal is wanted, and the check on the next line
subsumes anyway — so what the unification there is for is solving, not deciding.
Elaboration had been given the directed version already; the tactic had not, and
the same operation answered differently depending on which one you reached it
through.

### Elaboration is a rule with one clause per surface node

*Decided 2026-09-03.*

`elaborate` is thirteen clauses, and each says which surface node it is for:

```
rule elaborate t :- when focus-is-hole (surface-is-name t)
  then w = surface-name t ; x = resolve-name w ; fill t ; solve

rule elaborate t :- when focus-is-hole (surface-is-placeholder t) then
```

So `:step` through an elaboration shows the clause, not one opaque instruction:

```
thena spine> elaborate a
pc
  0  w = surface-name t
  1  x = resolve-name w
  2  call fill x
  3  call solve
```

**Exactly one head matches any term**, so a call to `elaborate` never has a
choice to make and never leaves a choice point. That is what the head predicates
are for — there is one `surface-is-…` per node kind, and a clause that names its
node cannot collide with another.

**A rule body may be empty**, which it could not before. `E⟦_⟧` is *do nothing*:
the hole is already there and unification is expected to find it. A clause that
does nothing and a clause that does not match are different answers, so the
empty body is saying something. `then` is still required.

**A rule loops by recursing over the surface term.** The λ case needs one
`prim-intro` per binder of a group, and a rule body is a straight run of
instructions with no iteration — so a helper peels one binder and calls itself
on the tail, and the term is its own counter:

```
rule intro-binders t :- when focus-is-guess (lambda-binds-more t)
  then x = lambda-name t ; prim-intro x
     ; tl = lambda-tail t ; call intro-binders tl

rule intro-binders t :- when focus-is-guess (lambda-binds-one t)
  then x = lambda-name t ; prim-intro x
```

**Peeling in the elaborate clause itself would not do**, because attacking once
per binder nests the λs and wraps each in its own `let` — a different proof
term. The run has to be emitted, and recursion is what emits it.

**Eleven of the fourteen clauses are real** (49b added `∀`, `->`, `let` — two clauses, since the
annotation is optional and a head cannot say *not* — the ascription and `do`;
49c added the λ). Two still run `prim-elaborate`: an application, which matches
its arguments against the head's plicities and then claims a hole per slot, and
an `elim`, which claims one per field. Both hand a **list of names** to a single
op, which recursion cannot build.

A clause takes its surface term apart with **moves**, which answer with a
surface term focused on the part rather than a detached one:

```
rule elaborate t :- when focus-is-hole (surface-is-arrow t)
  then … ; a = arrow-domain t ; call elaborate a
        ; … ; b = arrow-codomain t ; call elaborate b
```

They do not reuse the cursor's words — `dom` and `cod` already move the
development's ambient cursor, and one word for two different things is what the
project rules out.

### Two ops a rule needs that it cannot write down

*Decided 2026-09-03.*

`fresh-universe` is a universe at a **fresh level meta** — what the surface
writes as a bare `Type`. A rule cannot write it as a literal, because the whole
point of the meta is that it is new at every use.

`resolve-name ‹text›` is what a name denotes: the context at the focus first,
then the globals, with a definition's level arguments inserted.

```
thena spine> do { z = resolve-name "zero" ; fill z ; solve }
```

Both exist because they are what elaboration actually puts in an operand —
every other term a rule handles comes from an op or from its caller.

### The eliminator is an ordinary function you can name

*Decided 2026-09-03.*

Declaring a datatype has always generated a function for the type former and one
for each constructor, so that `succ` on its own is a value you can pass around.
It now generates one for the **eliminator** too, named `elim` followed by the
datatype's name:

```
thena spine> data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }
declared Nat
thena spine> :show elimNat
elimNat {ℓ₂₅₄} : ∀ (P : Nat -> Type (ℓ₂₅₄)) -> P zero -> (∀ (x : Nat) -> P x -> P (succ x)) -> ∀ (target : Nat) -> P target
elimNat = λ (P : Nat -> Type (ℓ₂₅₄)) (method : P zero) (method1 : ∀ (x : Nat) -> P x -> P (succ x)) (target : Nat) -> elim Nat () P (method method1) () target
```

So `elim D …` in a surface term is not a special form any more — it is written
in groups for legibility, but it means an application of that function, and the
two elaborate to the same term. **The level the motive lives in is a level
parameter of the wrapper**, like any other polymorphic global's, so a use
supplies it the same way.

`elim` is still a keyword, and `elimNat` is still one identifier — keywords are
whole tokens. The generated name is checked for a clash the way a constructor's
is: `data Bool …` is refused if you already have something called `elimBool`.

### Elaboration is written in the rule base, all of it

*Decided 2026-09-03.*

Turning what you write into a proof term is not built into the program. It is
fifteen clauses of a rule called `elaborate` in `rules/standard.thena.rules`, one
per kind of thing you can write, and you can read them, change them, or load a
base of your own:

```
-- E⟦x⟧ = FILL x ; SOLVE — Brady's variable case.
rule elaborate t :- when focus-is-hole (surface-is-name t)
  then w = surface-name t
     ; x = resolve-name w
     ; fill x
     ; solve
```

`:rules` lists them and `:step` runs an elaboration one instruction at a time.

**Elaboration and proof search are the same machine** — the same rule base, the
same choice points, the same backtracking. A clause that applies a function to
its arguments does it by recursion, one argument per step, because the rule
language has no loops and needs none: the term you wrote is the counter.

### The prelude is a program you can read

*Decided 2026-09-03.*

`Eq`, `Unit`, `Empty`, `And`, `Sigma` and the four theorems over them are a
**surface module** — `prelude/prelude.thena` — not a script of proof-assistant
commands. It is written the way you would write your own file:

```
data And (A : Type) (B : Type) : Type where
  both : forall (a : A) (b : B) -> And A B

andLeft : forall (A : Type) (B : Type) (c : And A B) -> A
andLeft = \ A B c -> elim And (A B) (\ z -> A) ((\ a b -> a)) () c
```

Every line of it goes through the same elaborator your own files do, so if the
prelude loads, elaboration works.

**Writing `Type` rather than `Type₀` is what makes these general.** `andLeft`
comes out as

```
andLeft {ℓ₀ ℓ₁} : ∀ (A : Type ℓ₀) (B : Type ℓ₁) -> And {ℓ₀ ℓ₁} A B -> A
```

— one level parameter for each component, matching `And {ℓ₀ ℓ₁} : Type (ℓ₀ ⊔ ℓ₁)`.
`Sigma` is deliberately written at `Type₀` and stays monomorphic, so `fst` and
`snd` have no level parameters at all.

---

### A `let` whose type is dependent must be annotated

Thena does not infer the type of a `let`-bound name when that type mentions the
value's own arguments. Write it:

```
let nc = noConfusionTerm x y q in nc            -- refused
let nc : NoConfusionTerm x y = noConfusionTerm x y q in nc      -- fine
```

This is the same requirement Agda and Idris make, and for the same reason:
inferring a dependent type for an unannotated binding is undecidable in general,
and guessing at one is worse than asking. A `let` whose type is simple —
`let n = succ zero in n` — needs no annotation and never will.

**The refusal is currently reported badly**, in terms of machine-generated hole
names, because the failure surfaces inside unification and only the elaboration
rule that created those holes knows what they stand for. Giving the rule
language a way to catch a failure and speak for it is open work; the semantics
above are not.

The same limit applies to an application whose head is not a name — a β-redex
like `(\ p -> e) v` — where there is no annotation to write. Use a `let`.

### `instral` has types, and a name is not a string

*Decided 2026-09-12.*

The instruction language is typed: `String`, `Name`, `Int`, `Char`, `Bool`,
`List a`, `Pair`, `Option a`, and four abstract types the machine owns —
`Surface`, `Core`, `Development`, `Name`. Every op has a signature.

**`Name` is a separate type from `String`, even though both are text.** More
types is more disambiguating power: it catches `say h` where `h` is a hole's
name, and `goto m` where `m` is a message.

```
claim  : Name -> Core -> Core
say    : String -> ()
concat : String -> String -> String
```

**A string literal is accepted at either**, so `fresh-name "refined"` needs
nothing. A *variable* is not: going from a name to a string is written down.

```
n = ask "name for the new hole?" name    -- n : Name
t = name-text n                          -- t : String
m = concat "claimed " t
```

**`core\`…\`` has type `Core`, and so does a resolved term.** What the tag
evaluates to has not been resolved yet — a rule base loads before the prelude,
so `core\`Nat\`` cannot find `Nat` when it is written — but the type system does
not tell the two apart, so `resolve-core : Core -> Core` and giving it a term
that is already resolved fails when it runs, not when it loads.

### A rule base is type checked when it loads

*Decided 2026-09-12.*

Every rule in every loaded base is inferred together, at load, and **a base that
does not type check is not installed** — the same all-or-nothing a syntax error
already gets. Nothing is annotated; a rule's signature comes from its head
predicates and from the ops its body uses.

```
rule elaborate t :- when focus-is-hole (surface-is-name t) then …
```

`surface-is-name` is what makes `t` a `Surface`, so `elaborate : Surface -> ()`.
`:load` reports what it found and leaves the previous rules in place:

```
the rules do not type check:
  oops, instruction 1: wanted Core, got Surface
```

Two things that used to fail halfway through a proof now fail at load: a literal
of the wrong kind (`prim-try 3`), and **binding a call to a rule no clause of
which returns**. A rule *some* of whose clauses return can still fail at run
time, because which clause runs is decided then.

**A call to a name nothing defines is still allowed** — a rule may call one in a
base you load later, so it is reported when the search finds no clause.

**A rule is inferred at one type**, not generalised: a helper used at `Surface`
in one place and `Core` in another is an error, not a polymorphic rule.

### A rule file may declare functions, and they need no keyword

*Decided 2026-09-12.*

A function is written the way Haskell writes one, beside the rules in the same
file:

```
twice x = concat x x

signature shout : String -> String
shout x = twice (twice x)
```

**A function is a rule with one clause and no head**, and that is not an analogy
— it becomes one. Call it from a rule body by name, exactly as you call a rule.
The one difference you can see: a function is **not offered as a tactic**, so it
never appears in `:matches` and `prove` never runs it.

**A function must produce a value.** `f x = say "hi"` is refused — `say` leaves
nothing, so there is nothing for `f` to be.

### Two ways to ask what applies: by state, and by type

*Decided 2026-09-12.*

`:matches` asks *what applies to this development* — a rule qualifies because its
head passes. The new pair asks about a **type** instead:

```
thena spine> :accepts Surface
  elaborate/1 : Surface -> ()   (rule)
  spine-arguments/3 : Core -> Core -> Surface -> ()   (rule)
thena spine> :produces String
  twice/1 : String -> String
```

Two commands rather than one with a direction: *what can I pass this to* and
*what will give me one*. Both list rules and functions, and mark which is which —
a rule may also turn up in `:matches`, a function never will.

**A polymorphic signature answers a concrete question.** A rule whose parameter
is `a` is listed by `:accepts Core`, because it does accept one. Asking about `a`
lists only what takes a variable.

### What you type at the prompt is a block

*Decided 2026-09-12.*

An entry is an `instral` block, so assignment and sequencing work at the prompt:

```
thena spine> h = here ; claim "k" ⌜ Type₀ ⌝ ; goto h
thena spine> n = 42 ; say "ok"
```

**A binding dies with the entry.** Not a prohibition — that is what block scope
means, and it is why there is no persistent REPL environment for `:undo` to
unwind. The `do { … }` workaround is no longer needed for this.

**An entry may span lines.** It keeps reading while it cannot be finished — a
trailing `;`, or an unclosed bracket — and **every continuation line must be
indented**, the same rule a rule file uses for declarations:

```
thena spine> h = here ;
         ...   claim "k" ⌜ Type₀ ⌝ ;
         ...   goto h
```

An unindented continuation is refused and the entry is dropped.

### An object language is declared with a grammar, and becomes a type

*Decided 2026-09-12.*

```
language Tm where {
  var : name ;
  app : "(" Tm Tm ")" ;
  lam : "fn" name "·" Tm
  }
```

That one declaration gives you three things: **`Tm` as a type** you can write in
a signature, **`` Tm`…` `` as the only way to make one**, and a one-way coercion
`surface-of` to a Surface term.

```
signature asSurface : Tm -> Surface
asSurface t = surface-of t

rule go :- then t = Tm`(x y)` ; s = asSurface t ; …
```

A production builds its constructor applied to what its slots parsed, so
`` Tm`(x y)` `` is the Surface term `app (var x) (var y)`. **A term you write in
the tag is well formed by construction**, because the tag is the only way to make
one — and it is *not* a Surface term until you coerce it:

```
go, instruction 1: wanted Surface, got Tm
```

**Terminals are Thena tokens.** A grammar is written over the same lexer
everything else uses, so `"."` is refused (it is not a token) where `"·"` is
fine. A production may not begin with the language itself, and may not be empty.

**The name must be free — as a tag AND as a type.** A declared language is
looked up before the built-ins in both places, so `language String where { … }`
would have made `String` in every signature mean the grammar, and
`language surface where { … }` would have replaced the `⟨ … ⟩` fence. Both are
refused, and so are two grammars under one name:

```
bad.thena.rules: in the grammar of String: String is one of instral's own types,
  so a grammar may not take its name
```

### `instral` has lambdas, and a local shadows a rule

*Decided 2026-09-12.*

```
signature onTwice : (String -> String) -> String -> String
onTwice f x = f (f x)

rule go :- then d = \ s -> concat s s
     ; m = onTwice d "a"                 -- aaaa
     ; say m
```

A lambda is a function without a name — it is compiled the same way and applied
the same way. **In an argument it takes parentheses**, like every other compound
argument: `once (\ s -> concat s s)`.

**A function type is n-ary, not curried.** `a -> b -> c` is a function of *two*
arguments; applying a one-argument lambda to two is a type error, because
`instral` dispatches on arity. Parentheses are what make an arrow a value: in
`signature f : (a -> b) -> a -> b` the first argument is a function.

**That holds in the result too**, so a function that gives a function says so:

```
signature mk : String -> (String -> String)   -- one argument, gives a function
mk s = \ z -> concat s z

signature two : String -> String -> String    -- two arguments
two a b = concat a b
```

The two are different callables, and `:accepts String` lists them apart.

**A local shadows a rule.** A word in a body is an op if one bears that name,
otherwise the local if one is bound, otherwise a rule of that name. So binding a
name that is also a rule changes what later lines mean — the op words are not
affected, but rule names are.

### A declaration begins in column 1

*Decided 2026-09-12. It is why a function needs no keyword.*

`rule` and `signature` announce themselves; a function's name does not, so a
rule file says where a declaration stops by indentation:

```
rule f :- then say "hi"
     ; prove              -- indented: still part of the rule above
g x = concat x x          -- column 1: a new declaration
```

Without the rule, `g` would be read as another argument to `say`. Rules may
still span as many lines as you like — indent the continuations.

### A value can be bound to a name

*Decided 2026-09-12.*

```
p = (1, true)
l = [1, 2, 3]
n = 42
```

Until now the right of an `=` in a rule body had to be an operation, so a literal
could be passed and returned but never named. `x = y` still means *call `y`* —
that reading is unchanged.

### A rule may declare its type, and that is what makes it reusable

*Decided 2026-09-12.*

A signature is its own declaration, on a line above the clauses — a name has
several clauses and one type.

```
signature spine-arguments : Core -> Core -> Surface -> ()
rule spine-arguments h f t :- when focus-is-component (surface-is-app t) then …
rule spine-arguments h f t :- when focus-is-component (surface-is-name t) then …
```

**The arity is the arrow chain's.** That signature is about `spine-arguments` at
three arguments and says nothing about one of two — a different rule, as far as
dispatch is concerned. `()` is the result and only the result: it says the rule
leaves nothing to bind.

**A capitalised name is a type, a lowercase one is a variable.** Nothing needs a
`forall` — a signature's variables are exactly its lowercase names.

**Write one when you want a rule usable at more than one type.** Without a
signature a rule is inferred at a single type, so this is refused:

```
rule ignore x :- then say "ignored"
rule usesName :- then n = fresh-name "h" ; ignore n     -- a Name
rule usesTerm :- then h = here ; ignore h               -- a Core
```

Adding `signature ignore : a -> ()` makes both uses fine, because each use gets
its own copy of the type.

**A signature is checked, not believed.** If the body needs more than the
signature promised, the *signature* is reported:

```
signature f/1: the signature says any type here, but the body needs Core
```

### `goto` takes a variable; `goto-named` takes a name

*Decided 2026-09-12. Renames what you type at the prompt.*

They were one word taking either. They are two operations: `goto` is exact,
`goto-named` **searches the whole development from the root** and takes the
first component it finds.

```
goto-named "h"        -- at the prompt, and in a body that minted the name
h = here ; goto h     -- in a body holding the variable
```

At the prompt you almost always want the second word, because a typed `"h"` is a
name. `goto` there needs a `do` block with something bound in it.

---

## The REPL and the session

### There are three kinds of file, and the extension says which

*Decided 2026-09-02.*

| extension | what it is |
|---|---|
| `.thena` | a **proof module** — the surface language: a header, then declarations |
| `.thena.script` | a script of REPL command lines, run in order |
| `.thena.rules` | a rule base |

`:load ‹path›` reads the extension. `:load proof ‹path›`, `:load script ‹path›`
and `:load rules ‹path›…` say it out loud instead, and the keyword wins over the
extension. **One `:load` may not mix kinds** — several rule bases at once is
fine, a script and a rule base together is refused rather than ordered somehow.

**A kernel refusal does not stop a load.** If a `qed` inside a script or module
is refused by the kernel, the file **keeps going** and the lines after it run.
So a load that reports later declarations may still have left one theorem
unadmitted, and the refusal scrolls past among them.

```
:load proof.thena     -- a qed the kernel refuses does NOT end the load
:revalidate           -- this is what tells you the session is sound
```

Every other way a line fails — a parse error, a rejected tactic, a halted
machine, a refused command — stops the file. A kernel refusal is the one that
does not, and it is the sharpest of them. **Run `:revalidate` after loading
anything you did not write yourself.**

**You cannot load a rule base while a proof is suspended.** Between theorems is
fine; a suspended proof is one you are *inside but not at*, and loading would
change the base under a half-built proof. That is the same argument that rules
out a `rule` command altogether: the test is whether the half you have already
built would replay the same afterwards.

```
module Tier0 where

data Nat : Type₀ where
  zero : Nat
  succ : Nat -> Nat

one : Nat
one = succ zero
```

The header is real syntax, so `module` is a reserved word everywhere — you
cannot name anything `module`, in any of the three kinds of file. `where` opens
a block, so a module's declarations and a datatype's constructors are laid out
by indentation; explicit `{ ; }` works exactly as well, and gives the same tree.

**Loading a proof module is quiet.** It reports the module and what it declared,
one line each. Elaborating a single declaration emits a dozen lines about
solving level metas; a file of them buries its own output. Type the declaration
at the prompt and you still see everything. A module that fails keeps all of it,
because that is where the reason is.

**That silence covers a `say` you wrote yourself.** If a rule of yours prints
something, you will see it at the prompt and not during a load — there is no way
today for a rule to speak from inside one, and no flag to turn the rest back on.
The line between *the loader's* output, *a rule's* output and *the file's* has
not been drawn, and drawing it belongs to the interaction model rather than to
the loader.

### A comment is `--` followed by a space, in every kind of file

*Decided 2026-09-02.*

```
-- a whole line
one : Nat
one = succ zero        -- or the end of one
```

**The space is the rule.** `--` with no space after it is not a comment, so
`-->` and `--x` stay available for whatever wants them later. Nothing is written
`--`-first today — `-` may appear inside a name but not start one — and
requiring the space means nothing has to be given up to get comments.

**One syntax for all three kinds of file**, proof modules, scripts and rule
bases alike, including above a rule base's own header. His reason: *"They might
not fit super naturally in the .thena.script files or .thena.rules files, but
that's fine. Better they are uniform than three different ones."*

A comment carries no tokens, so it never affects layout: a comment line is not
an item, and it neither opens nor closes a block.

### `do { … }` drops into the instruction language, in a term or at the top

*Decided 2026-09-03.*

A `do` block holds the **instruction** language — the same one a rule body is
written in. Two places take one, and they are the same syntax in two roles:

```
-- an expression: elaborating it means playing it
foo = do { attack ; prove }

-- an item: it plays where the declarations around it declare
do
  say "and now for something completely different"
```

It lays out like everything else, and it is an **atom**, so an argument run
takes one without parentheses: `try do { attack }`.

**This is why there is no surface term meaning *no proof given, search for one*.**
You write `do { prove }`, and a search strategy is then a rule name rather than
syntax — `do { auto }` names a rule you wrote, and the system knows nothing
about it.

**What a block cannot do yet: mention a term.** An operand is an identifier, a
number or a string, so a block can search, navigate and bind but cannot
construct. Term literals in a body are a later phase.

**A block is not a script.** REPL commands — `:theorem`, `:show`, `qed` — are
the driver's and are not instructions; a `.thena.script` file is where those
live.

### `yield` goes both ways, because it names one thing

*Decided 2026-09-03.*

A rule body can stop and hand control to you:

```
elaborate (do { h = here ; yield "look at this" ; goto h ; prove })
   look at this
   (yield to hand control back)
```

You are then standing **inside** the suspended rule. Every command works — this
is not a question, which takes an answer and refuses everything else — and
`:show` shows the half-built development. Typing `yield` hands control back.

**The same word in both directions**, because it names one thing: a transfer of
control. Who it goes to is settled by who is speaking, and yielding to yourself
is a no-op, so there is nothing to confuse it with. It is bare rather than
`:yield` for the usual reason — it acts.

**The yield is not consumed**, so after each line you are handed the prompt
again, until you `yield` out.

**`do { … }` is a REPL command**, and inside a yield it is the useful one: the
driver's own commands take terms and names, so `goto h` looks for a hole *called*
`h`, while `do { goto h }` reads whatever the suspended rule bound `h` to. A
block's own bindings survive to the next line while a rule is suspended.

You can break the rule you are standing in — shadow one of its locals and its
body will go wrong. That is allowed on purpose.

### `instral` has lists, pairs and options, and you take them apart in a rule's head

*Decided 2026-09-12.*

```
rule join xs :- when (list-is-empty xs) then return ""
rule join xs :- when (list-is-cons xs)
  then h = list-head xs ; c = option-value h ; t = list-tail xs
     ; r = join t ; s = concat c r ; return s
```

`[a, b, c]` is a list and `(a, b)` is a pair; an option is `some x` or `none`.
The elements are ordinary operands, so `[x, "c"]` reads `x` where the list is
built.

**There is no `if` and no `case`, and none is needed**: a rule branches on its
head, so a function over a list is two clauses, one per shape. `list-is-empty`,
`list-is-cons`, `option-is-some` and `option-is-none` are head tests like every
other question a rule asks.

`list-head` answers an *option*, so the empty list needs no separate answer.
`option-value` on `none` fails — ask with `option-is-some` first.

**A compound argument is parenthesised, inside a literal as anywhere else**:
`[(g a), b]`, and `((g a), b)` for a pair whose first component is a call.

**You cannot bind a literal to a name.** `x = [1, 2]` is refused: the right-hand
side of a binding is an operation, so a value comes from an op or from a rule
that returns one. `f [1, 2]` and `return [1, 2]` are both fine.

### `instral` has four primitive values

*Decided 2026-09-12.*

```
say "a string"     -- text, since phase 22b
return 42          -- a number
return 'c'         -- a character
return true        -- a boolean; false too
```

A numeral is a number wherever a field word is not in front of it — `arg 2` and
`param 0` still read theirs as a position, because those select a field rather
than take a value.

**`true` and `false` are reserved in `instral`, and nowhere else.** They are not
keywords: one lexer serves every language here, and an object language is free to
declare a constructor called `true` — `examples/determinacy-tactics.thena.script`
does. Inside a rule they are values, so a rule may not use either as a parameter
or a binding; it is refused when the base loads rather than silently read as a
literal.

There are no operations on any of them yet — no arithmetic, no comparison. You
can carry a value and hand it back; computing with it comes with the type system.

### A rule returns what it says it returns

*Decided 2026-09-12.*

```
rule twice t :- then s = concat t t ; return s
rule shout t :- then m = twice (twice t) ; say m
```

A rule hands a value back with `return`, and a caller that wrote `x = ‹rule›`
gets it. A rule with no `return` hands nothing back; a caller that asked for a
value from one gets *nothing was returned to bind to x*, at the call, rather than
an unbound name further down.

**`return` ends the body** — anything after it does not run.

The alternative was *the value of the last instruction*, as in a Haskell `do`
block. It was declined because most bodies end in something that produces
nothing — `prim-solve`, `prim-try`, `say` — so a rule that wanted to return would
have had to be written to end on the producing op. The return value would then be
a constraint on the order of the body, and invisible where the rule is called.

`prove` is not a call and returns nothing: what the rule it chose did is in the
development.

### An argument may itself be a call

*Decided 2026-09-12.*

```
shout (twice t)          -- one call, with a call as its argument
x = twice t ; shout x    -- what it means, and what you had to write before
```

A compound untagged argument is written in parentheses, and a parenthesised
call is evaluated before the call that wanted it — **left to right, innermost
first**. The order is fixed and worth knowing, because these are statements: a
rule changes the development, so when it runs is observable.

**A rule's head may not contain one.** A head says what a rule is about and is
checked to build the match list; running a call to find out whether a rule
applies is not something a head may do.

### A typed line is one line of `instral`, and a bare argument is not a term

*Decided 2026-09-11.*

```
try-core ⌜ zero ⌝              -- a core term, in corners
elaborate ⟨ succ zero ⟩        -- a surface term, in angle brackets
claim "h" ⌜ Nat ⌝              -- a string, and a core term
goto "h"                       -- a string: the hole's name
goto h                         -- a REFERENCE, to whatever h is bound to
```

**An argument written in no fence is neither language.** It is an `instral`
value — a name, a number or a string — read exactly as a rule body reads one.
Until this point a bare argument at the prompt was a *surface term*, which made
Surface the one language you could write without saying so, and forced `goto`'s
argument to be special-cased in the implementation to get a name out of a
position that otherwise produced a surface tree.

So there is now one reading of a line, wherever you type it: the word names an
**op** if one bears that word, and a **rule** otherwise; its arguments are
operands. That was already true inside a rule body and inside `do { … }`.

What this costs you is explicitness — `unify ⌜ a ⌝ ⌜ b ⌝` where it used to be
`unify a ≟ b` — and what it buys is that a line means the same thing in all
three places.

### An op word at another arity calls a rule of that name

*Decided 2026-09-11.*

```
claim "h" ⌜ Nat ⌝     -- two arguments: the op
claim ⌜ Nat ⌝         -- one argument: a rule, which asks you for the name
```

A word names an **op at the arities that op has, and a rule at every other
arity**. Rules already worked this way — clauses of one name are selected by
name *and* number of arguments, so they need not agree about how many they take
— and ops now agree with them instead of being a separate question.

This is what lets `claim ⌜ Nat ⌝` be an ordinary rule in the rule base rather
than a shape the REPL recognises. You can write your own clause of any op's name
at an arity the op does not have, and it will be found.

**The cost is that a mistyped word is no longer caught when a rule base loads.**
`prim-solve x` used to be refused as *`prim-solve` was written with the wrong
arguments*; it is now a call to a rule called `prim-solve` that takes one
argument, and if there is none you find out when it runs. That is the same trade
already made for `call`, where a rule may name a rule defined later or in a base
not loaded yet.

### `:infer` takes a surface term; a core one goes in corners

*Decided 2026-09-02.*

```
:infer succ zero          -- a surface term: elaborated
:infer ⌜ succ zero ⌝      -- a development-calculus term: resolved
```

This is the rule everywhere an argument is written — `try-core ⌜ x ⌝` against
`try x` — now applied to the one command that had been core-only.

`:infer ‹surface›` answers *if this term were put here, what would its type be?*
It elaborates into a fresh hole at the focus, reads the type off, rechecks the
development, and then **puts the development back exactly as it was**. Nothing
it built survives the line, so it is a look despite doing real work.

The type it prints is reduced further than `:infer ⌜t⌝`'s — it has to be, to see
past the hole the elaboration solved. The two agree up to conversion, and print
the same.

### `:help` lists the commands, not the tactics

*Decided 2026-08-31.*

`:help` prints every command the REPL itself has, split by the naming rule —
a bare word acts, a word with a colon looks — **and the ops**, which are in
the binary and which nothing else lists. `attack`, `intro`, `try`, `solve`,
`eliminate` and the rest are **not** commands and not ops: they
are rules in a rule base, reached by writing their name the way a rule body
would. Listing them under `:help` would state a loaded file's contents from
inside the binary, and would be wrong the moment you load a different base.

So the last line of `:help` says where they are instead:

```
any other bare word calls a rule of that name; :rules lists them.
```

`:rules` prints the rules of every loaded base, in search order. If a word is
in neither list, `no such command` says so and points back at `:help`.

### `:undo` takes back a line, whether or not you are proving

*Decided 2026-08-29.*

A session always has a development — at a fresh prompt you are standing in a
scratch one with a single hole called `goal`. You can build in it: `assume`,
`claim`, `:goal`, tactics, `certify`, all with no `:theorem` open.

**`:undo` works there, and so does the rewind that undoes a failed line.** Both
used to require a proof, which was an accident of where the undo stack was
stored rather than a decision.

**`:undo` does not cross a proof boundary.** `:theorem`, `qed`, `:abandon`,
`:suspend` and `:resume` each start a fresh history:

```
assume A : Type₀
:theorem t : Type₀
:undo                  nothing to undo — it will not step back past :theorem
```

**Why `qed` in particular:** admitting a theorem writes it into the global
environment, and the environment is not part of what `:undo` restores — it only
ever grows. An `:undo` across a `qed` would rewind your development and leave the
theorem admitted, which is worse than refusing.

**Loading a file leaves no undo history**, for the same reason: a file declares
datatypes and admits theorems, and neither is something `:undo` could honestly
reverse.
