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
one paragraph, not three; the argument lives in `.claude/`.

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

*Nothing recorded yet.*

---

## The REPL and the session

### `:help` lists the commands, not the tactics

*Decided 2026-08-31.*

`:help` prints every command the REPL itself has, split by the naming rule —
a bare word acts, a word with a colon looks — and nothing else. `attack`,
`intro`, `try`, `solve`, `eliminate` and the rest are **not** commands: they
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
