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

*Decided 2026-08-25; consequences accepted 2026-08-29. The keyword list is
reviewed whenever a word is reserved — most recently 2026-10-19.*

Most languages reserve a generous set of punctuation and give you the rest.
Thena does the opposite: it reserves as little as it can, so you can name things
in your own notation — `≼`, `Γ⊢`, `x'`, `2-cell`, `∂f/∂x` are all one identifier.

**Reserved, and nothing else:**

| | |
|---|---|
| brackets and separators | `(` `)` `{` `}` `[` `]` `;` `,` `"` |
| operator characters | `λ` `∀` `⊢` `≟` `≐` `≈` `▸` `⌜` `⌝` |
| whitespace | |
| keywords | `forall` `let` `in` `elim` `induction` `case` `of` `trusted` `where` `data` `module` `do` `rule` `language` `context` `judgment` `notation` `when` |

A name starts with an ASCII letter, `_`, or any non-reserved character above
ASCII.

**A keyword is a whole token, so a word that merely *contains* one is a name.**
`caseNat` and `datatype-of` are each one identifier; the lexer takes the longest
match, so a keyword rule can only win on the whole word.

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

**`rule`, `when` and `do` are keywords** and cannot be used as names. Op words
are not: `solve`, `type`, `goal` and the rest stay perfectly good identifiers,
which is why a rule is written `rule ‹name› :- when … do …` and not with the
op words reserved.

### A token class's regular expression is small, and refuses what it does not mean

*Decided 2026-09-18.*

An object language's identifiers and numerals are regular expressions, written
between slashes. The syntax is exactly: characters, `\` escapes, classes
`[a-z]` and `[^…]`, `.`, `*` `+` `?`, sequence, `|` and parentheses. No
captures, no backreferences, no lookaround, no lazy quantifiers.

**What other dialects give a meaning and this one does not is refused rather
than read as a literal:**

```
/[^ \t\n]+/      fine — not whitespace
/\S+/            refused — \S is not supported
/a{3}/           refused — unexpected '{'
/^[a-z]+$/       refused — unexpected '^'
/\{\$/           fine — escaped, they are literal
/(a)\1/          refused — a backslash before a digit is a backreference elsewhere
/[[:alpha:]]/    refused — an unescaped [ inside a class
/[\[a-z]/        fine — escaped, it is literal
```

Read as literals, `/\S+/` would quietly mean `S+`, and someone coming from
Perl or POSIX would find out much later. Refusing them also means `\s`, `{n}`
or POSIX classes can be added later without changing what any accepted
expression means.

### Corners and `⟨…⟩` are on their way out, in favour of tagged term literals

*Decided 2026-10-01.*

Two older notations say exactly what a tagged term literal says:

```
⌜ t ⌝   [| t |]        a core term, inside an instruction
core`t`                the same thing, and the one that stays

⟨ e ⟩                  a surface term — the lexer turns ⟨ into the tag `surface`
surface`e`             the same thing, and the one that stays
```

**Both still work and neither is offered any more.** Completion will not suggest them,
and nothing new in the system points at them. They are to be replaced one for one and
removed.

**Why, and it is not tidiness.** These are the last places where *which language this text
is in* is decided by the punctuation you reached for rather than by a tag naming the
language. Thena's whole embedding story is the tag: one notation, any language, including
the ones you define yourself. A second spelling that works for only two of them has to be
carried by every feature that comes after, and each one pays for it.

The same decision covers the REPL commands that read an untagged term — `:core`, `:dev`,
`:goal`, `:whnf`, `:convert` — which are debugging commands older than tagged literals.
`core\`t\`` is a one-for-one replacement and is accepted everywhere a term is.

---

### Surface and Core will not become `language` definitions

*Decided 2026-10-01.*

Thena lets you define an object language as a grammar — `language LC, E where …` —
and then write its terms in a fenced literal, `` LC`( λ x : ι . x )` ``. The obvious
next thought is that Thena's own languages should be defined the same way: a prelude
declaring `surface` and `core` as ordinary grammars, the system bootstrapped in itself.
**They will not be.** Not now, and not when the tooling would make it easy.

**What you can and cannot write.** `surface` and `core` are reserved tags, and a
`language` block may not be named either of them:

```
language surface, Term where      refused — surface is one of Thena's own tags
surface`\ x -> x`                 fine — always has been, and is unaffected
```

**Why.** The bootstrap is an attractive result and it is not the project's result. Thena
exists to be a novel and useful proof assistant — applied theory, proving a concept — and
making its own surface and core languages self-described would put the whole of that
under pressure in service of an elegance. The honest version of the same claim arrives by
another road: Thena's parser generator, when it replaces the current Alex and Happy, will
take **one** grammar file per language, and that file both parses the language into its
tree and produces the editor's completions. "The same grammar you can read is the grammar
that runs" is as strong a statement of openness, and it costs the project nothing it
needs.

**What this means in practice.** The surface and core grammars exist twice: as the
translating parser that runs your input, and as a secondary grammar that answers *what
may I write here* for an editor. The second is narrower than the first by design — it
will stay quiet where it does not know rather than guess — and it never parses anything.
Nothing is foreclosed: the day a bootstrap is cheap, it is still available.

### A type written on a λ binder is a check, not a declaration

`\ (a : String) -> a` and `\ a -> a` give you the same proof term. The binder's type always
comes from the goal; a type you write on the binder is elaborated and compared with it, and
the comparison is conversion — not subsumption, so a *narrower* written type is refused
rather than accepted. If you want the narrower one, change the goal.

**Why a check and not a declaration.** The other reading — introduce the binder at the type
you wrote and let the goal be checked against the result — makes the same program elaborate
to two different terms depending on whether you annotated it, and makes the binder's type a
thing you wrote rather than the thing the goal says it is. A check leaves no trace at all:
nothing downstream can tell an annotated binder from a bare one.

**The type is elaborated where the binders before it are in scope**, so it may name them:

```
polyId : ∀ (A : Type₀) -> A -> A
polyId = \ A (a : A) -> a
```

and binders in one group may be written or bare in any mix — `\ (a : S) b (c : T) -> e`.
Where the goal's domain is not yet known, the written type *solves* it rather than being
compared with it, because the comparison is unification.

**A brace on a λ binder is refused.** A brace in a signature says callers may leave that
argument out; the λ binds its arguments in order whether a caller wrote them or not, so
there is nothing for a brace to mean there. `\ A x -> x` is the spelling for a signature
written `∀ {A : Type₀} -> A -> A`.

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

### There are three primitive types, and a literal is a term

*Decided 2026-09-18.*

`String`, `Char` and `Int` are types the system knows, at `Type₀`, and their
literals are ordinary terms:

```
thena spine> :infer ⌜ "hello" ⌝
"hello" : String
thena spine> :infer ⌜ 42 ⌝
42 : Int
```

**They are not datatypes.** They have no constructors and no eliminator, an
`Int` is arbitrary precision, and the only thing you can do with two literals
is compare them. **The three names are taken**: a declaration called `String`
is refused the way any clash is.

A literal is written where a term is written — in a surface definition, in a
theorem, or inside corners — and it elaborates to itself:

```
greeting : String
greeting = "hello"
```

Two literals of a primitive type are compared with `eqString`, `eqChar` or
`eqInt`, which answer with the prelude's `Comparison` (`same` or `different`)
and compute only on literals:

```
thena spine> :whnf ⌜ eqString "a" "b" ⌝
different
```

**`Comparison` and not `Bool`**, because an object language you model routinely
declares its own `true` and `false` — Thena has one namespace, and the prelude
leaves those names to you.

They exist for language modelling: an object language's identifiers are
strings, and a language that has numerals or characters needs somewhere to put
them. The alternative — building them from an inductive numeral, as Coq does —
was weighed and refused, because it makes every identifier in every
object-language term a chain of constructors.

### Preservation for a modelled language is proved about the substitution Thena generates

*Decided 2026-09-22.* `examples/07-preservation.thena` proves, for the λ-calculus
of `01`–`03`,

```
preservation : ∀ (M : LC) (M1 : LC) (T : Ty) -> typing empty M T -> step M M1 -> typing empty M1 T
```

in the surface language, with `elim` and no proof sugar. **It is about the
generated `LC-subst-all`**, not a substitution written for the proof: the
proof names the generated function's pieces, checks with `refl` that they are
the same terms, and follows its `decString` decisions case by case.

**It is proved twice.** `examples/08-preservation-by-tactics.thena.script`
proves every lemma again by tactics — `:theorem`, `attack`, `intro`,
`eliminate-core` for each induction and case split, `elaborate ⟨ … ⟩` for each
case — and reaches the same statement as `preservation-tactics`.

**`07` is stated for closed terms**, as Software Foundations states it. The
argument substituted in a β-step is then closed, so no binder is ever renamed.

### And for any context, resting on three laws about `appendString`

*Decided 2026-10-12; the trust narrowed to the three laws on 2026-10-16.*
`examples/10-preservation-any-context.thena` proves the same theorem with no
restriction on the context:

```
preservationAny : ∀ (G : Ctx) (M : LC) (M1 : LC) (T : Ty)
                -> typing G M T -> step M M1 -> typing G M1 T
```

With an open argument a β-step **can** capture, so the generated substitution
renames the binder — `( λ y : ι . x )[x -> ( λ w : ι . y )]` is
`( λ y' : ι . ( λ w : ι . y ) )`, which the file proves by `refl`. The proof then
has to know the minted name really is fresh.

**Three laws about `appendString` are trusted and everything else is proved**:

```
appendAssoc      (a ++ b) ++ c  =  a ++ (b ++ c)
primeDiffers     eqString a (a ++ "'")           is  different
primeMoreDiffers eqString a ((a ++ "'") ++ b)    is  different
```

Each is a fact about a primitive that computes only on two literals and goes
neutral on anything else, which is the same position the prelude's
`eqStringEqual` is in. On literals each one **discharges**: both sides reduce,
claimed and actual become convertible, and the node contracts — `:whnf
appendAssoc "a" "b" "c"` is its own body. They are pending exactly where they
carry weight.

**The name chooser's specification is a theorem.** `L-fresh-‹k› y avoid` is not
in `avoid` — that used to be the trusted claim, and it is now derived from the
three laws by the argument the generated code is built on: the candidates `y`,
`y'`, `y''`, … are pairwise distinct, each rejection spends one name of the
list, and the fuel, which is `avoid` itself, runs out only once the list is
exhausted. **Nothing is added to the theorem's statement**: `preservationAny`
has no extra hypothesis.

**There is no counting in it and no arithmetic.** *Longer* is `|xs| > |ys|`
computed from the two lists, so *longer than something, being empty* reduces to
`Empty` and the base case closes by reduction rather than by a pigeonhole over
numbers. **A length as an `Int` would not have helped.** `String`, `Char` and
`Int` are primitive *types* — no constructors, no eliminator — so there is no
induction over a length, and `length (a ++ b) = length a + length b` is a claim
about open arguments like any other: adding `lengthString` and arithmetic would
have traded one trusted law for two and widened the kernel permanently.

### `decString` compares two strings and hands you the proof

*Decided 2026-09-21.* Beside `eqString`, `eqChar` and `eqInt`, the prelude
declares `decString`, `decChar` and `decInt`:

```
decString : ∀ (a : String) (b : String) -> Dec (Eq String a b)

data Dec (A : Type) : Type where
  yes : forall (p : A) -> Dec A
  no : forall (n : A -> Empty) -> Dec A
```

On two literals it computes to `yes (refl String "a")`, or to `no ‹a
refutation›` — a real proof of `Eq String "a" "b" -> Empty` that the kernel
checks like any other. On a name you do not know it does not compute, and that
is where it earns its place: **eliminating `decString y x` gives you
`Eq String y x` in one branch and its refutation in the other**, where
`eqString y x` tells you only which branch you are in. So a proof about a
name nobody knows can follow the decision:

```
varMiss : forall (y : String) (x : String) (N : LC) (ne : Eq String y x -> Empty)
            -> Eq LC (LC-subst (var y) x N) (var y)
```

**Generated substitution decides with `decString`**, which is what lets a
proof about `LC-subst` follow it at all. What is trusted is the same as for
`eqString`: the verdict on two literals. The refutation it writes is built
from `decString` itself and checked by the kernel.

### Trust is a term, and it reduces away when it stops being needed

*Decided 2026-10-04.* Every system has a way to say *"this is true, take my word
for it"* — Coq's `Axiom`, Agda's `postulate`, Lean's `sorry`, Idris 2's
`believe_me`. **Not one of them reduces during type checking**, which is the right
call for an axiom and useless when the thing you are asserting has to compute.
Thena has a term instead:

```
trusted T e
```

It is an ordinary core term. `e` is checked as usual, at whatever type it really
has; the node is then given `T`, and **nothing relates the two** — that is the
trust, and it is the whole of it. So `trusted Empty (refl Nat zero)` type-checks,
and a development that rests on a claim like it is verified modulo that claim.

**What makes it worth having rather than a postulate is that it is conditional,
and it reduces.** `trusted T e` contracts to `e` the moment `T` and `e`'s own type
turn out to be the same type, and stays frozen until then. Internally the node
carries both — `trusted claimed actual body` — so the pair is the obligation with
both halves visible, and you can see the two converge as the names in them
instantiate. A node that never becomes checkable never reduces, and then it is
behaving exactly as a postulate would, except that it is local to one term, its
body was checked at *some* type, and it is listed when you ask what a theorem
depends on. Agda's `primTrustMe` is the same idea and the only precedent for it.

**Why a λ cannot do this**, since it is the first thing to try:
`λ (a b : String) . refl String a` has type `∀ a b -> Eq String a a`, never
`∀ a b -> Eq String a b`. A λ defers *evaluation*, not *checking* — its body is
checked once, generically, with the variable arbitrary. Nothing in an ordinary term
language keeps a **typing** judgement open, because a term's type is settled when
it is checked. Making the obligation an argument,
`λ (a b : String) (p : Eq String a b) . p`, is the honest trust-free version and
works exactly when somebody can supply `p`; for a name the system does not know,
nobody can.

**The restriction worth knowing about.** The contraction asks the real conversion
checker, not a syntactic approximation of it, but it declines to act when that
comparison comes back owing a constraint on universe levels — which happens only
when a level is still unknown. The node simply stays, and a stuck well-typed term
is a valid proof, so nothing is lost but an occasional reduction.

**`trusted` is a reserved word, and the type may be left to inference.**
`trusted _ e` puts an ordinary placeholder in the type position and the goal
supplies it; nothing about that position is special. One consequence of a declared
type being level-generalised is worth expecting: `honest : Eq Nat zero zero` has a
claim at the *parameter* `ℓ` while its body's type is at `0`, and a reference's
level arguments are part of what it is — so the term contracts at `honest {0}`
rather than where it was declared. A term still printing as `trusted` is one whose
claim has not been met yet, which is what the pair is there to tell you.

### The asserted type is stored, not re-derived, and the development calculus writes it

*Decided 2026-10-05.* A trusted node has to remember two types — the one it asserts
and the one its body really has — because the node contracts exactly when those two
turn out to be the same, and that moment arrives as names instantiate. The choice is
whether to **store** the body's type or **re-infer** it each time the question is
asked. Thena stores it. Internally the node is three fields:

```
trusted ‹claimed› ‹actual› ‹body›
```

Re-inferring would mean running the type checker inside reduction, which is the
wrong direction in the layering and would make every reduction step's cost depend on
the size of a term's type.

**The surface language writes two fields and derives the third; the development
calculus writes all three.** Elaborating `trusted T e` infers `e`'s type and fills
`actual` in, so a user of the surface cannot get it wrong. The development calculus
is the printed, re-readable form of a term — what is printed can be typed back — so
it writes what is there, which means a user typing a term at the prompt, or into a
rule or a tactic, can write an `actual` of their own choosing.

**What happens when they write a wrong one is that it does not type-check.** The
typing rule checks the body *against* the stored type rather than inferring and
comparing, which is what keeps the stored field honest:

```
thena spine> :infer ⌜ trusted (Eq {0} Nat zero zero) (Eq {0} Nat zero (succ zero)) (refl {0} Nat zero) ⌝
refl {0} Nat zero has type Eq {0} Nat zero zero
  but Eq {0} Nat zero (succ zero) was expected
  in argument 3 of Eq, succ and zero are different names
```

So a node that survives certification cannot be lying about its body's type, and the
stored field cannot drift out of step with the term under substitution.

**One gap, and it is cumulativity rather than trust.** That check is subsumption, not
conversion — a term usable at `Type₀` is usable at `Type₁` — so a stored type strictly
*above* the body's own is accepted:

```
thena spine> :infer ⌜ trusted Type₀ Type₂ Type₀ ⌝
trusted Type₀ Type₂ Type₀ : Type₀
```

`Type₀` really has type `Type₁`. Nothing becomes unsound: the stored type is what the
claim is compared against, so inflating it can only stop a node contracting that
would otherwise have contracted, which moves the claim from *discharged* to *pending*
and leaves it in the report. It cannot go the other way, because a stored type
*below* the body's own is refused outright.

**Whether storing it is worth this is open.** The alternative is to re-derive the
body's type at every comparison and let the written form carry two fields everywhere,
which costs type inference inside reduction and buys the impossibility of writing the
field at all.

### How much you trust is a setting, not a verdict the checker hands down

*Decided 2026-10-06.* Given a term whose type is merely asserted, the obvious
move is to refuse it somewhere. Thena classifies it instead and lets the user say
how much to allow.

Every claim a development rests on is **discharged** — the two types are
convertible, so the claim is met and the trust is carrying nothing —
**pending**, or **undischargeable**, which means it can never be met by any
instance in any later session. The last is decided by comparing the two types
position by position: `Eq Nat zero (succ zero)` against `Eq Nat zero zero` agrees
at the head and clashes at the third argument, so a head-only test would miss it.
A clash in a closed universe level counts too — see *A universe level decides
impossible when it is known* below. Anything not positively a clash counts as
merely pending, because calling an honest claim impossible costs a refused proof
while the converse costs only a less specific report.

**A claim is read at the use where the use settles it, and at the definition
otherwise, and the report says which.** That distinction is the point rather than
a detail. A claim like `∀ (a b : Nat) -> Eq Nat a b` is perfectly open read
inside its own body and is a lie at `… zero (succ zero)`, so the
`Print Assumptions` shape — list what a theorem's definitions assume — reports a
proof of `Empty` built that way as resting on one open claim. A use is only
allowed to settle it when it actually does: a partial application, a bare
reference that passes nothing, and a use reached through a further definition all
fall back to the definition. Threading arguments through every hop instead would
be full normalisation, which may diverge and has no business in `qed`'s path.

**The session carries a trust level with three settings** — *no trust*, *no
undischargeable trust*, *any trust* — and the user moves between them freely,
including between theorems. The setting is asked *after* the kernel has accepted
the term, because this is policy and not the kernel's judgement, and the
classification is reported whether or not it refuses. The expected pattern is to
sit on the middle setting and drop to *any* for one strange thing.

**It is asked at both of the ways a definition reaches the environment, and
getting that wrong was a real hole.** A definition arrives either by closing a
proof or by being written down whole, and for a while only the first asked — so
a definition resting on a claim that can never be met could be *declared* at the
strictest setting, and the setting bit only when some later proof used it. The
strictest setting is the one soundness guarantee, and it has to mean *nothing
unsound gets in* rather than *nothing unsound is concluded*: a declared
definition is a first-class inhabitant of the environment, it is listed, the
prompt completes against it, a later declaration may mention it in a type, and it
outlives the setting in a script. Both doors now refuse the same way:

```
thena spine> :trust none
thena spine> declare liar : Eq Nat zero (succ zero) ; liar = trusted (Eq Nat zero (succ zero)) (refl Nat zero)
the trust level refused it
trust: no trust
  undischargeable, written here
    claims Eq {ℓ₁} Nat zero (succ zero)
    body   Eq {0} Nat zero zero
thena spine> :trust any
thena spine> declare liar : Eq Nat zero (succ zero) ; liar = trusted (Eq Nat zero (succ zero)) (refl Nat zero)
```

Writing something knowingly false therefore means saying so first, which is the
setting doing its job rather than the system preventing anything.

**What the setting still says nothing about is what is already in the
environment.** The report is a view on the proof in front of you, so immediately
after a definition is admitted it is not what the report is about — and that is
a separate question from admission, deliberately left open.

**His ruling: the report stays on the current proof, and a `:trust env` command
does the wide check.** `:trust` tells you what *this* proof rests on — following
uses into the global declarations it reaches, each classified where the use
settles it — and what the environment already holds is a separate question for a
separate command. `:trust env` walks the environment when asked rather than every
frame, which keeps the frontend's redraw rule intact: a frontend asks for it the
way the user does.

**Only *no trust* is a soundness guarantee, and the middle one is not sold as
one.** What the middle setting refuses is a claim that is provably false, and a
claim can be discharged at every instance anybody has written down and still be
nonsense: `Empty` is provable that way. It stops accidents, not adversaries.

**`no trust` still admits a *discharged* claim — item `~xhf2g`, and this is the
one part of the above that is a choice rather than a consequence.** A claim whose
two types are convertible is met, so the body already has the type the node
asserts and the node reduces away; refusing it would refuse a term that is sound.
*Settled 2026-10-12: this reading stands.*

**What *discharged* means operationally, because the strictest setting is exactly
as strong as this answer.** It is: **convertible now, by computation, with
nothing left open.**

- **Computation counts.** The question is put to the real conversion checker, so
  reduction, unfolding a definition and η all count — it is not syntactic
  identity. With `N = Nat` and `one = succ zero`, a claim of `Eq N zero zero` over
  a body of type `Eq Nat zero zero` is discharged, and so is `Eq Nat one (succ
  zero)` over `Eq Nat (succ zero) (succ zero)`. Neither pair is equal as written.
- **Nothing may be left owing.** A *yes* that owes a constraint on universe
  levels does not count as discharged, which is the same condition the
  contraction itself declines on. This keeps the report and the reducer saying
  the same thing rather than nearly the same thing.
- **It is asked, never recorded.** The classification is recomputed every time it
  is wanted, so a claim is pending while something is open and discharged the
  instant that thing is supplied — the same node, the same definition, a
  different answer at a different instance.

So the strictest setting admits exactly what the reducer would contract away, and
nothing else: at that setting every asserted type in a proof is one the system
could have erased.

**The alternative reading, kept as `~xhf2g`, is that the setting should mean *no
asserted type reaches this proof at all*.** That is a stricter promise and a
one-line change. **What it would cost is smaller than it first appears, and the
earlier claim here was wrong**: it is not that the prelude becomes unusable
because its own claims are discharged — the prelude's claims are *pending*, so
they already fail the strictest setting today. What the literal reading would cost
is only a proof that reaches a claim which genuinely is discharged. **If that
reading ever wins, this subsection is what changes with it.**

### What a proof rests on is a view, asked for, and never pushed at you

*Decided 2026-10-06, and the consequence accepted 2026-10-12.* The accounting of
what a development rests on — every asserted type it reaches, classified, and
where each one came from — is a **view**: it walks the proof when you ask it and
nothing anywhere recomputes it when the proof changes. It is deliberately not a
hook in type checking. Checking runs on every refinement; *what does this proof
currently rest on* is a question about the chain, the same shape as asking where
you are, so it is answered when it is asked.

**The cost is that the answer can go stale and nothing says so.** At a prompt
that is harmless: you ask, you discharge a claim, the old text is still on your
screen and you know it. **In a tool that draws it, it is harmless in only one
direction.** A panel that draws the report and caches it will show *fewer*
outstanding claims than there really are, and look authoritative doing it. Fewer
is the direction that matters, because this report is what a reader checks before
believing a proof.

**So the rule is that a frontend re-asks rather than caches**, which is the rule
it already follows for every other view, and this is deliberately not made the
first exception to it. What makes re-asking cheap is a pre-pass: before walking
anything, the accounting asks whether the term reaches an asserted type at all
and stops immediately if it does not, which is the answer for almost every term
in the system.

**There is no notification, and that is the decision rather than an omission.**
Telling a frontend *your report has changed* would be the first thing of its kind
in the system, and it is not needed by a frontend that redraws.

### A universe level decides *impossible* when it is known, and only then

*Decided 2026-10-12.* Classifying an asserted type as **undischargeable** — it can
never be met, by any instance, in any later session — is a comparison of two types
position by position, and until this decision it ignored universe levels
altogether. The reason it did is real: a level written in a declaration is not
always a number. It is generalised into a parameter and instantiated at each use,
exactly as a term binder is, so *"these two levels differ"* is not on its own a
reason to call anything impossible.

Take a definition whose claim sits at its own level parameter while its body's type
sits one above:

```
declare g : Type ; g = trusted Type Type₀
```

Its two types agree at exactly one instance, and the report follows the use rather
than the declaration:

```
thena spine> :whnf g {1}
Type₀
thena spine> :trust
  discharged, at the use of g
    claims Type₁
    body   Type₁
```

At any other instance the claim is false, and it was being reported as *pending* —
*not yet* — about something that is never:

```
thena spine> :whnf g {0}
trusted Type₀ Type₁ Type₀
thena spine> :trust
  undischargeable, at the use of g      <- said "pending" before this decision
    claims Type₀
    body   Type₁
```

**The line is whether every level in the comparison is closed.** A level's normal
form is a constant plus a set of variables with offsets; an empty variable set
means no metavariable and no parameter, so nothing in any later session can move
it, and two such levels that differ are a permanent clash. One variable anywhere
and the answer goes back to *pending* — reach the same `g` through a further
definition, where its parameter is still standing, and that is what you get:

```
thena spine> :trust
  pending, in h · g
    claims Type (ℓ₁₀₂₁)
    body   Type₁
```

That line is right, and `g {1}` above is the instance that discharges it.

**It is equality, not the subtyping order.** A node contracts when its two types
are *convertible*, and conversion asks for levels to be equal; cumulativity lives
in the typing rule, which is a different question. So a closed `Type₀` against a
closed `Type₁` can never discharge, however the hierarchy is ordered, and no
reasoning about `max` or about constraints is involved — the comparison is
equality of normal forms, which the implementation already had.

**A level sits in more places than a universe, and the commoner one is a former's
level argument.** `Type₀` against `Type₁` is the rare shape; a datatype used at two
levels is the ordinary one, and it hides behind heads that agree:

```
thena spine> :trust
  undischargeable, written here
    claims Eq {1} Nat zero zero
    body   Eq {0} Nat zero zero
```

Same datatype, same three arguments, and the whole of the clash is in the level.
Both a saturated constructor's level arguments and an applied former's are compared
this way.

**Where it deliberately stops.** An eliminator carries level arguments too and they
are not compared, because a stuck elimination is never called impossible at all —
it may still compute. The governing rule is unchanged and is what makes the whole
test safe to have: it answers *impossible* only where it is certain, and *pending*
everywhere else, because calling an honest claim impossible refuses a sound proof
while the converse costs only a less specific report.

### A primitive that supplies a type is retired; a primitive that computes stays

*Decided 2026-10-06.* An assistant for metatheory keeps meeting facts that are
true and unprovable in its own theory — and the cheap answer is to add a built-in
function for each one, which is an escape hatch with no structure and nothing a
user can inspect. Thena's answer is to split the two jobs a built-in was doing.

Deciding whether two strings are equal is the case that forced it. `eqString`
*computes*: on two literals it answers `same` or `different`, and nothing in the
core term language can do that, so it stays a reduction rule. What it cannot do
is tie that answer to the equality type — `eqString y x` says nothing about
`Eq String y x` for an unknown `y` — and that gap is a *typing* claim, so it is
written as one:

```
eqStringEqual : ∀ (a b : String) -> Eq Comparison (eqString a b) same -> Eq String a b
eqStringRefl  : ∀ (a : String) -> Eq Comparison (eqString a a) same
```

Both are definitions in the prelude whose bodies are `trusted` terms, and
`decString`, which answers `yes` with a proof or `no` with a refutation, is an
ordinary definition built on them — it eliminates the comparison with a motive
that keeps the answer, so each branch is handed the evidence of which answer it
is, and the refutation is *derived* rather than built by the implementation.
`decString` itself trusts nothing.

**What this buys is that the trust is listed rather than built in.** A user who
asks what a proof rests on is told `in decString · eqStringEqual`, with both the
claimed type and the type the body really had, and can read the four lines of
prelude that say it. Before, the same trust was sixty lines of Haskell that
constructed the answer term, and no command could name it at all.

**It costs the strictest trust setting for these proofs, and that is stated
rather than hidden.** The claims are read at their own definition's binders,
where they are *pending* — so *no trust* will not close a proof that decides a
literal equality, even though `decString "x" "x"` reduces to `refl String "x"`
with nothing trusted left in it. Finding out which claims survive reduction means
reducing, which may diverge and has no business in `qed`'s path, so the strictest
setting is a statement about what a proof reaches and not about what is left when
it runs.

**Revisit note, on his ruling: this conservatism is accepted for now.** A future
`qed` could normalize first and classify what survives reduction rather than what
the proof reaches — which would close proofs deciding literal equalities at the
strictest setting. That puts reduction that may diverge in `qed`'s path, the thing
currently ruled out, so it is recorded here rather than built.

### A token class is an ordinary definition, and its regex takes its type as an argument

*Decided 2026-09-19.*

A token class is a definition of type `Token T`, written like every other
definition, with a signature and an equation. `T` is what a matched token
becomes in an object-language term:

```
ident : Token String
ident = /[a-z][a-zA-Z0-9']*/

digit : Token Char
digit = /[0-9]/
```

**There is no one-line form, and the annotation is required.** `ident = /…/`
alone is refused, as any equation without a signature is.

**The literal holds only its text; `T` is found by unification.** A regex
literal has type `∀ (T : Type₀) -> Token T`, so `/[0-9]/` elaborates to
`/[0-9]/ ?T` and the signature solves `?T`. What gets stored is `/[0-9]/ Char`,
which is what `:show` prints. Nothing is defaulted: with nothing to say what
`T` is, elaboration fails.

**It is the one literal that is not a value of a primitive type on its own.**
A string, a character and a number each have a type; a regex has a Π, and what
it stands for depends on the argument. So `/[a-z]/ Bool` is a well typed term
of `Token Bool` as far as the kernel is concerned — nothing can take a `Token`
apart, so it proves nothing — and it is the declaration check below, not
typing, that refuses it.

```
thena spine> :infer (/[a-z]/ : Token Char)
/[a-z]/ : Token Char : Token Char
```

**The checks run when the class is declared, not in the kernel.** Core accepts
`/[a-z]+/ Char`, since the literal is well typed at every `T`, and loading it
refuses it:

```
refused: in the token class n: /[a-z]+/ accepts "a", which is not an Int
```

Nothing can take a `Token` apart, so a wrong one cannot prove anything; what
the check protects is the grammar that reads the class. It refuses:
- a `T` other than `String`, `Char` or `Int`;
- a regex that does not parse;
- a regex that matches the empty string;
- a regex that accepts something `T` cannot hold. The witness shown is a
  shortest such string.


### An object language's grammar is a block of its own notation

*Decided 2026-09-19.*

A `language` or `context` block at the margin of a module is read by its own
reader, not by Thena's lexer, so its notation can use `[`, `λ`, `⌜` or `/`:

```
x : Token String
x = /[a-z]+/

language LC, M, N, E where
  var : x as occurrence -> x
  abs : x as binder     -> ( λ x : T . E[x] )
  app                   -> ( M N )

context Ctx, Γ where
  empty  -> ·
  extend -> Γ , x : T
```

**Items are separated by whitespace**, so `Γ ,` and not `Γ,`. The
separation is needed only in the grammar; a term is written `Γ, x : T`,
because whitespace between object tokens is optional when it is parsed. A
binding form is the exception: `E[x, y]` is one item, bracket adjacent. A
production is one line, and a deeper line continues it.

**`context`, `judgment` and `notation` are reserved words**, like `language`. A name in a
production is a metavariable, then a token class, then a terminal, and a
metavariable may not be named like an existing one or a class — uniqueness is
across every grammar in scope, not per block. **A name is refused for not being a
metavariable only where one is required**: a binding form's head, and the
metadata. Anywhere else a plain word is simply a terminal, which is why a
production may say `( λ x : T . E[x] )` without declaring `λ` or `.`.

A block sees what is above it, as every declaration does. **So there are no
mutually recursive languages**, and that is deliberate rather than a limit of the
reader: Thena has no mutual inductives, so a pair of languages that referred to
each other could not be given the datatypes they generate.

It is checked when the module loads, and a binder that binds in nothing is a
warning, not an error.


### In a slot stands a nonterminal, and a slot is one word

*Decided 2026-10-11.*

A grammar in Thena looks like a notation for an inductive definition, and reading it
that way is nearly right. It is right that a production corresponds to a
constructor, that a slot corresponds to an argument, and that a reading elaborates
to the head applied to what the slots hold. It is wrong about what a slot *is*, and
that is where days go.

```
the datatype says      app : LC -> LC -> LC      arguments have TYPES
the production says    app -> ( M N )            slots hold NONTERMINALS
a use site says        ( y z )                   slots are filled with TERMS
```

**A slot is filled with a term rather than a type.** The one case where a term
written at a slot is a type is the case where the slot is at a universe — an
instance of the rule, not an exception to it.

The consequence that matters in practice. Give a spelling to a function whose last
argument is a derivation:

```
collapse : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Ctx

notation collapse G M T d -> ⟨ G , M , T by d ⟩
```

The fourth slot is the parameter `d`. Writing the derivation's *type* there —
`⟨ Γ , M , T by Γ ⊢ M : T ⟩` — is not merely hard to read, it is a different
production: `Γ ⊢ M : T` is a reading, three slots and two pieces of text, so that
spelling has three slots each written twice and no slot at all for the derivation.

**Until 2026-10-16 that fourth slot was the single word `typing`, the grammar's own
name**, because a judgment declares no word for its derivations — which said
nothing about *which* argument was meant. Naming the parameters replaced it.
Agda's `syntax` declarations name one argument per slot and would write `by d`;
Thena keeps one kind of word in a production instead, so the word is the one that
names the nonterminal.

So a grammar is **not** an inductive definition. It is a projection of one, and since
the `notation` block it projects several declarations at once — a datatype's
constructors, functions over that datatype, and type formers. The nonterminal of a
`language` or a `context` is named after a type; a judgment's is named after a type
*former*, and what it parses is a derivation.

### Notation is assignable to anything declared, and a universe is spelled `𝕌₀`

*Decided 2026-10-09/11, built 2026-10-11.*

A `notation` block gives a spelling to any declared name — a function, a
constructor, or a type former of any arity — under one rule: a spelling whose
slots are one per argument of that name's type, elaborating to that name applied
to what the slots hold. The header carries the name's own spelling:

```
data bound : String -> Tp -> Env -> Type₀ where { bHere : … ; bThere : … }

notation bound (v : x) A Δ -> v ◂ A ◂ Δ where
```

A premise is an argument's type, so anything with a type spelling may stand above
a rule's bar — including a plain `LC`, since a rule is a constructor and an
argument may be at any type. And the universes have spellings of their own,
`𝕌₀`, `𝕌₁`, …, zero-based, so that a universe can be written where a type is
wanted — without them `k : Type₀ -> Ty -> Ty` had no spelling at all, since a
slot then had to be a word naming a nonterminal.

**Since 2026-10-16 a notation names its own arguments** rather than borrowing
words from the grammars, which is the section *A notation names its own arguments*
below; the examples here are in that form.

```
collapse : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Ctx
notation Ctx where
  collapse G M T d -> ⟨ G , M , T by d ⟩
```

The fourth slot is `d`: a hole at a derivation, whose type and indices come from
the declaration. **A `notation` block can do this because it describes a
declaration that already exists.** In a `language` block the argument types are
generated *from* the slots, so there is nothing to read a type off — and for the
same reason a slot at a universe is refused there.

**That line runs through the whole feature.** A hand-written datatype with an
assigned notation gets the full freedom of Surface: any universe, an index
telescope that depends on earlier indices, a judgment indexed by another
judgment. A `language`, `context` or `judgment` block stays simpler, and its
family is fixed at `Type₀` with independent indices. Where the two meet, the
hand-written route is the escape:

```
data Valid : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Type₀ where …
notation Valid G M T d -> ⊢ G , M , T by d valid where
```

A block that installs a grammar for a hand-written datatype also generates its
substitution family from the roles its productions carry, so `data` plus
`notation` is a `language` block with extra freedom rather than a weaker version
of one.

### A `notation` block gives a function a spelling, so a rule can say what a paper says

*Decided 2026-10-07, built 2026-10-08.*

A judgment rule writes its indices in object notation, and object notation can
only spell what the grammar's productions build. Those are constructors — so
F-sub's type-substitution lemma, which the paper writes `Γ, X<:Q, Δ ⊢ t : T`, was
unwritable. That comma means *append* between two contexts, and no constructor
spells append:

```
S-split: Γ , X <: T , Δ ⊢ T <: S
refused: … its premises do not parse: unexpected 'Δ' at character 14
```

A `notation` block gives a declared **function** a spelling in a grammar:

```
append : Ctx -> Ctx -> Ctx
append = …

notation Ctx where
  append a b -> a ∪ b
```

`a ∪ b` now parses wherever a `Ctx` is expected — a rule's index position
included — and elaborates to `append` applied to what the two slots read. So the
paper's rule is writable:

```
S-split : ∀ (Γ : Ctx) (Δ : Ctx) (T : Ty) (S : Ty)
            -> sub`${Γ} ∪ ${Δ} ⊢ ${T} <: ${S}` -> sub`${Γ} ⊢ ${T} <: ${S}`
```

**The datatype is untouched: `Ctx` stays a list.** That is why this is not a
joining *constructor*, which was considered and refused — a
`join : Ctx -> Ctx -> Ctx` constructor makes `Ctx` a tree, in which
`join (join a b) c`, `join a (join b c)`, `join empty a` and `a` are four
distinct terms denoting one context, conversion is structural, and nothing
identifies them. **A function reduces; a constructor does not.** A production
with two slots of the context's own sort therefore stays refused.

**It is a separate top-level block rather than part of the `language` or
`context` block, and the reason is scoping**: the function's type mentions the
datatype that block declares, so it cannot be written above it.

**The function form is written, never inferred.** "There is a function of that
name in scope" is already the check that catches a clash
(`Ctx's constructor nil is already declared`), so inferring from it would consume
that diagnostic, and deleting a definition above the block would silently turn a
function production back into a constructor — changing the datatype and
everything generated from it.

The block declares nothing and generates nothing: the datatype, the lookup
relations and the substitution are the ones the grammar's own block made. The
checks are that the name is a declared function, that it is not already some
grammar's production, and that its type takes the slots in arity and sort and
returns the grammar's datatype.

**What it costs**: every term a rule mentions must be a named global with a
declared notation — no inline lambda, no inline `elim`. That is loud at the
declaration rather than at every use, and it is the payment for not escaping the
modelling framework. Precedence is not part of it: `Γ , X <: Q ∪ Δ` parses
uniquely because the competing reading needs `Q ∪ Δ` to be a type, while
`Γ ∪ Δ ∪ Γ'` is ambiguous and is reported when the term is parsed.

**And the substitution notation is now one of these rather than a privilege.**
`E[x -> M]` was the one spelling the system hard-wired: rules the rule parser
added for itself, and a special case in the elaborator that recognised them.
Generated substitution now writes the block a user would have written —

```
notation LC where
  LC-subst-x -> M [ x -> N ]
```

— as a surface item, checked the same way. Two things follow and both are gains.
It **parses outside a rule**, so `` LC`x[x -> y]` `` is an ordinary term literal
where it used to be a parse error; and it **prints back**, so a rule whose index
substitutes reads ``sub`${Γ} [ ${X} -> ${T} ] ⊢ …` `` instead of splicing
`${Ctx-subst-X Γ X T}`.

**The comma list stays sugar**, because `E[x -> M, y -> N]` builds a *list* per
class and no object grammar spells a list. So the one-pair form is a production
and the list form is not — which means the list form is still a rule's privilege
and does not parse in a term literal.


### A notation names its own arguments, and anything declared may have one

*Decided 2026-10-16, built the same day.*

A `notation` production says which argument each place in the spelling is for, by
naming them and taking them in order:

```
data Valid : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Type₀ where
  { validAny : ∀ (G : Ctx) (M : LC) (T : Ty) (d : typing G M T) -> Valid G M T d }

notation Valid G M T d -> ⊢ G , M , T by d valid where
```

**The names are local.** The first is the first parameter or index of the thing
being spelled, and nothing requires it to be spelled the way the declaration
spells its own binders — `notation Valid a b c p -> ⊢ a , b , c by p valid` means
the same. A word of the spelling is a slot exactly when it is one of those names;
every other word is literal text. The rules are what you would expect: as many
names as arguments, no name twice, and every name written somewhere — an argument
with nowhere to be written could not be given.

**A slot's type is read off the declaration rather than checked against the
spelling**, so the two cannot disagree. The one thing a declaration cannot say is
which token class a `String` argument reads, which is the entry below.

**Before this a slot was a word that happened to be a metavariable of some
grammar in scope, and that could not say which argument it meant.** Where a
derivation goes there was no word at all — a judgment declares none, since an
arbitrary derivation has no one type — so the *grammar's own name* stood in:
`notation Valid -> ⊢ Γ , M , T by typing valid`. That read like a claim about the
fourth argument's type while claiming nothing, and the identical line was accepted
for a declaration whose fourth argument is `typing G M base`, third index nailed to
`ι`. It also forced a grammar to carry words it did not need: two identical words
collapse to one slot, so `append -> Γ ∪ Γ` is refused and `Ctx` had to declare a
second word, `Δ`, purely so a two-argument function could be spelled.

**Anything declared may have notation, including a judgment's rules and a
datatype's constructors — the condition is that it not be ambiguous.** A rule
given a spelling is a derivation you can write:

```
notation plain where
  T-any -> ⟪ Γ ! M ! T ⟫
```
```
thena spine> :infer plain`⟪ · ! x ! ι ⟫`
plain`⟪ · ! x ! ι ⟫` : plain`· ⊢ x : ι`
```

Spell a rule like its own statement and the statement stops being readable, which
is the one thing you may not do — and you are told, with the colliding rule named:

```
thena spine> :infer plain`· ⊢ x : ι`
stuck: in plain`· ⊢ x : ι`: this term parses two ways,
       as plain(empty, var(x), base) and as T-any(empty, var(x), base)
```

**That check is at parse time, so a colliding notation loads clean** and the
breakage appears when somebody writes an affected term. A declaration-time check
is intended and is not here yet.

### A `String` argument says which token class it reads

*Decided 2026-10-16, built the same day.*

A slot's type comes from the declaration, and for every type but one that settles
what may be written there: `Ctx` is a grammar, so a `Ctx` argument reads a
context. `String` is not a grammar. What makes a string readable inside a term is
a token class, and a language may declare as many of them over `String` as it
likes — F-sub reads two kinds of name, capitalised for type variables and not for
term variables:

```
X : Token String       X = /[A-Z][a-zA-Z0-9']*/
x : Token String       x = /[a-z][a-zA-Z0-9']*/
```

Both are `Token String`, so the declaration `notIn : String -> Ctx -> Type₀`
cannot say which kind of name its first argument is. **A `String` parameter is
therefore ascribed with the class it reads, and only a `String` parameter may
be:**

```
notation notIn (v : X) G -> v # G where
```

The ascription names the **class** and not the parameter, because that name is
the word a rule writes where the slot is — F-sub's rules write `X # Γ`, as the
paper does.

**What it buys is a refusal.** `#` is *this type variable is not declared in Γ*,
and with the class in place a term variable cannot be written there:

```
thena spine> :parse notIn X # ·
notIn(X, empty)
thena spine> :parse notIn y # ·
in notIn`y # ·`: unexpected 'y' at character 1, expecting X
```

There is no third option where the slot reads any string at all, because a term
is a sequence of tokens and every token belongs to a class. So a `String`
parameter that names none is refused, and the refusal says what is missing:

```
refused: in the notation for P, production P: s names an argument of String, which
no notation reads by itself — if it is a String, say which token class, as
( s : ‹class› )
```

### A rule's premise may be named, and later premises may write the name

*Decided 2026-10-16, built the same day.*

```
judgment check = Γ ⊢ M ⇐ T where

  CheckRule:  p1 : Γ ⊢ M : T
              p2 : ⊢ Γ , M , T by p1 valid
              --------------------------
              Γ ⊢ M ⇐ T
```

A name is in scope for every premise after it, on the same line or a later one,
wherever a term of that premise's own type can be written — and in the conclusion.
So `CheckRule`'s second premise is a statement *about the derivation the first one
names*:

```
CheckRule : ∀ (Γ : Ctx) (M : LC) (T : Ty) (p1 : typing`${Γ} ⊢ ${M} : ${T}`)
              -> Valid`⊢ ${Γ} , ${M} , ${T} by ${p1} valid`
              -> check`${Γ} ⊢ ${M} ⇐ ${T}`
```

Papers do this as `D :: J` and “by IH”. An unnamed premise is still `d1`, `d2`, …
by its position, and a name may not be a metavariable of any grammar, nor a type
the rule mentions, nor another premise's name — so a name in a premise means
exactly one thing.

### `:judgment` shows a judgment's rules the way a paper writes them

*Decided 2026-10-16, built the same day.*

```
thena spine> :judgment typing
  d1 : x : T ∈ Γ
  -------------- T-var
  Γ ⊢ x : T

  d1 : Γ ⊢ M : ( S -> T )
  d2 : Γ ⊢ N : S
  ----------------------- T-app
  Γ ⊢ ( M N ) : T
```

An argument at a judgment's statement is a premise; every other argument is a
metavariable and is left out, which is what a paper does. A premise carries its own
name, so a named premise reads here as it was written. It is derived from the
declared types, so a hand-written datatype with notation shows the same way a
generated judgment does.

**It is a display and nothing reads it back.** The statements above the bar stand
as *types*, and a derivation needs terms in those positions — so this form could
not be a way of writing one even in principle. `:show` still gives the
declaration, which is the thing that round-trips; the two answer different
questions. And it is `:judgment` rather than `:rules` because `:rules` is the
engine's rule base: an `instral` rule and an inference rule are different things.

### An object term is parsed by its grammar, and `:parse` shows how

*Decided 2026-09-19.*

A language's terms are parsed character by character from its grammar. There
is no separate lexer, so what a token is depends on where you are, and
whitespace between tokens is optional. A token class tries every length it
matches, not just the longest. Nothing has precedence, and a term that parses
two ways is refused, with both readings shown:

```
thena spine> :parse LC (λf:(ι->ι).(λy:ι.f y))
abs(f, arrow(base, base), abs(y, base, app(var(f), var(y))))
thena spine> :parse LC f a b
in LC`f a b`: this term parses two ways, as app(var(f), app(var(a), var(b))) and as app(app(var(f), var(a)), var(b))
```

A name a production writes twice must read the same both times, and the error
says so when it doesn't. **`?` is a missing sub-term**, and only a sub-term,
never a piece of notation:

```
thena spine> :parse LC ( λ ? : ι . ? )
abs(?, base, ?)
```

`?` can be written only until the structural editor exists. The editor will
make a missing piece with a keystroke, and `?` will then be free for object
languages to use.

**`:parse` with no text is a mode where every line is a term**, until `:done`.
In it, **Tab asks the parser what fits at the cursor**:

```
parse LC> ( λ‸              Tab →   ( λ ? : ? . ? )
parse LC> ( λ‸ )            Tab →   ( λ ? : ? . ? )     (the closer was already there)
parse LC> ( λ‸ x            Tab →   lists  ‹x›          (your binder is not written over)
parse LC> ( ‸               Tab →   lists  λ  (  ‹LC›  ‹x›  {
parse LC> ( λ x : ‸? . ? )  Tab →   lists  ‹Ty›         (nothing fits, but the slot wants one)
parse LC> ( λ x : ?‸ . x )  Tab →   lists  ι  (      (what can replace the ?)
```

When exactly one production is open at the cursor — one that has recognised
something and has not finished — Tab writes the rest of it, `?` for its slots,
and **only as much of it as the text after the cursor does not already
supply**: a closer already written is not written twice, and a hole is never
put in front of something you typed. Otherwise Tab lists what can go at the
cursor such that the line can still be finished, counting what's already
written after the cursor; and when nothing at all fits there, it lists what
the open position is waiting for, so the parser's expectation is visible
rather than silent. On a `?`, Tab fills that hole, so it offers only notation.
The options appear when you press Tab, not as you move; options that follow
the cursor are the structural editor's job.


### A language block declares a datatype, and its terms are ordinary terms

*Decided 2026-09-20.*

The grammar is the declaration. From it come a datatype, one constructor per
production, its arguments the production's distinct names in order of first
appearance:

```
language LC, M, N, E where
  var : x as occurrence -> x
  abs : x as binder     -> ( λ x : T . E[x] )
  app                   -> ( M N )
```

```
thena spine> :show LC
data LC : Type₀ where
  { var : String -> LC
  ; abs : String -> Ty -> LC -> LC
  ; app : LC -> LC -> LC }
```

**It is an ordinary datatype**: it has the eliminator, the constructor wrappers
and the no-confusion equipment any `data` has, and you could have written it by
hand. A `context` block declares one too. **A name written twice in a
production is one argument** (`twice -> { M M }` gives `twice : LC -> LC`),
because the two occurrences must read the same.

So a term of an object language is an ordinary term:

```
thena spine> :infer ⌜ abs "x" base (var "x") ⌝
abs "x" base (var "x") : LC
```

What the block records beyond the datatype is which argument **binds** and
which is an **occurrence** of a name — the metadata generated substitution
reads. That is why `x as binder` and `x as occurrence` are written at all.


### Grouping is part of your grammar — Thena reserves nothing

*Decided 2026-09-20.*

An object term is parsed **only** by the productions you declare. Thena has no
grouping parentheses of its own, no precedence, no associativity and no
implicit anything. If `( f x )` is to be writable, some production must say so.

There are two ways to get grouping, and they differ in what ends up in the
datatype.

**Parenthesize inside the productions**, the fully-parenthesized style of most
paper grammars:

```
app -> ( M N )        app : LC -> LC -> LC
```

The parentheses are terminals of that production. They cost nothing: the
datatype has exactly the constructors your language has.

**Or declare grouping as a production of its own:**

```
paren -> ( M )        paren : LC -> LC
```

Now grouping is a **constructor**. `paren e` and `e` are different terms, every
proof by `elim LC` gets a `paren` case, and a lemma about `app` says nothing
about `paren (app …)`. That is usually not what you want, and it is the reason
to prefer the first style.

**Ambiguity is reported, never resolved.** Write `app -> M N` and `f a b` has
two readings, so Thena refuses it and shows you both. Nothing picks one for
you, because nothing knows which you meant.

**What this buys.** The grammar is the whole of the notation: what you declare
is what you write, and what Thena prints back — a production is also a printing
rule. There is no fixity table to learn or to get wrong, and every character is
yours, brackets and `λ` included, because none of them is reserved.

**What it costs.** You design your grammar to be unambiguous yourself, and you
find out when a term is read rather than when the grammar is declared. Deeply
nested notation needs care that a built-in precedence would have handled.

**Others draw the line elsewhere.** SASyLF keeps parentheses for itself: they
group object-language terms, you disambiguate with them, and a literal
parenthesis in your language has to be quoted. Agda gives you mixfix operators
with fixity declarations, and its own parentheses group. Both take a piece of
the notation back from the object language in exchange for grouping you do not
have to write. Thena takes none of it, and you write the production.

### A term prints in its language's notation, and the printer finds its own fences

*Decided 2026-09-22.*

A term of a language you declared is shown in that language's notation, in
`:show`, in `:infer` and in every goal — not as the constructor application it
is:

```
idIsValue : value`( λ x : ι . x ) value`      -- and not: value (abs "x" base (var "x"))
```

**A judgment prints the same way**, because a judgment is a production too, so
a theorem's statement reads as it would on paper:

```
preservation : ∀ (M : LC) (M1 : LC) (T : Ty)
  -> typing`· ⊢ ${M} : ${T}` -> step`${M} --> ${M1}` -> typing`· ⊢ ${M1} : ${T}`
```

**What the notation cannot write stands in a splice**, in Thena's own syntax: a
variable, a stuck call, a name you gave a term. **The printer does not reduce**,
so `theId` is shown as `value`${theId} value`` rather than unfolded into the
term it stands for.

**Where a grammar groups by splicing, the printer splices.** It writes the term
flat, reads its own text back with the same parser, and fences the smallest
subterm the reading disagrees about, until what it wrote reads back as what it
meant. A grammar that brackets its productions never reaches the second
attempt; one that does not gets what you would have written by hand:

```
Ex`${Ex`f a`} b`        -- juxt (juxt f a) b, in a language with no parentheses
Ex`f ${Ex`a b`}`        -- juxt f (juxt a b)
```

**The check is on the text, not on the shape of the grammar** — which matters
because nothing is reserved inside an object language. The same position with
the same child production needs a fence when a name collides with one of your
terminals and not otherwise, so `let f = a b in c` prints flat while
`let f = a in in b` does not. No table over positions could tell those apart.

**What is printed can be typed back.** The development calculus reads a tagged
term literal too, so a goal you are shown is text you can paste into `:core`,
`:theorem` or a tactic argument, splices and all. `Core` gained nothing for any
of this: a literal is notation, and it resolves to the constructor application
it denotes.

### An object term is written the same way in a rule — and there it also matches

*Decided 2026-09-20.*

The notation you write a term of your language with works in `instral` too, and
**which direction it means is decided by where it stands**. In an operand it
builds; in a pattern it matches. `${…}` supplies a value in the first and binds
one in the second.

```
rule beta LC[app]`( ( λ ${x} : ${A} . ${B} ) ${N} )` :- do
  ...                                   -- x, A, B, N are bound here
  t = LC`( ${B} ${N} )`                 -- and spliced back in here
```

**What a splice binds is the slot's type.** At a language slot it is a term; at
a token class it is the value the class matched — a `String`, a `Char` or an
`Int`, not a term wrapping one. So `LC[var]`${s}`` gives you `s` to `say`, and
using it where a term is wanted is a type error when the file loads.

**Brackets restrict, here as in a surface term.** `` LC`…` `` matches any term
of the language, `` LC[var]`…` `` only a variable occurrence. Text with no
splice matches itself: `` LC[var]`x` `` is the variable called `x` and nothing
else.

**A pattern is tried as written, and then reduced and tried again.** An object
term in a goal is whatever elaboration produced — a global, a chain of `let`s,
a wrapper not yet reduced — so matching only the written shape would almost
never fire. Trying the written shape *first* keeps a pattern that wants an
unreduced form able to see it. It is one rule for every pattern, not a rule
about object terms.

**Load the language's file before the rules that take it apart.** A rule file
is read with the grammars the session already has, so the module declaring
`language LC` has to have been loaded first. Load them the other way round and
the tag names a language nothing has declared, which is the error it looks
like.

---

### A `do` block is resolved and checked where it runs, and a module's own goes through a rule

*Decided 2026-09-20.*

A module is a **sequence**. Its declarations run in the order you wrote them,
and each one sees exactly what is above it. Until this decision, `do` blocks
were the exception: they were turned into instructions and type checked while
the file was still being read, before any declaration in it had run.

```
language LC, M, N, E where
  var : x as occurrence -> x
  app                   -> ( M N )

do
  ...                             -- this block is read after the block above
                                  -- has been checked and installed
```

**What this changes for you.** A block's words become operations, and its types
are checked, at the moment the program reaches it. So a mistake in a block is
reported *after* the declarations above it have gone in, the way a mistake in a
term already was — where before it refused the whole file and declared nothing.
Blocks were the only construct with that behaviour, and nothing else in a
module has it.

**A module's top-level block is a call to a rule**, `run-block`, which lives in
the shipped base and is two lines:

```
run-block : Surface -> ()
rule run-block t :- do play t
```

So **how a module treats its own blocks is yours to change**: load a base that
defines `run-block` ahead of the shipped one and every top-level block in every
module goes through your version instead. A clause of your own is offered first
if it is written first, as for any rule.

**Each top-level block is its own scope**, and now really is: the call gives it
a frame, so a name bound in one block is not in scope in the next. Before, the
instructions were spliced into the module's one program and shared its one
environment — the checker refused a block that read a name from the block above
it, but the run would have found it.

**Reading a module now consults nothing.** Lexing, layout, parsing and grouping
are a pure function of the text; every question about what a name means is
asked while the module runs.

---

### You write an object term in backticks, and splice into it

*Decided 2026-09-20.*

A term of a language you declared is written with the language's name and a
pair of backticks. It elaborates to the constructor application it denotes —
an ordinary value of the ordinary datatype the block generated, with no branded
type and no coercion:

```
identity : LC
identity = LC`( λ x : ι . x )`      -- abs "x" base (var "x")
```

**The text inside is your language's, not Thena's.** Nothing in it is reserved:
`λ`, `[`, `?` and the rest are whatever your grammar says they are. Three
characters have to be written behind a backslash, because they are how the
region itself is delimited: `` \` ``, `\\` and `\$`.

**`${ … }` splices a term in**, and the slot it stands in decides its type:

```
applied : LC
applied = LC`( ${identity} ${identity} )`
```

A splice is a whole term and not a name — ``LC`( ${f x} y )`` — and it is
elaborated where it stands, at the type the constructor's argument has. A slot
that is a token class takes one too, at `String`, `Char` or `Int`.

**Brackets start the parse at one production.** `` LC`…` `` reads any term of
`LC`; `` LC[var]`…` `` reads a variable occurrence and nothing else:

```
y : LC
y = LC[var]`y`                      -- var "y"
z : LC
z = LC[var]`( λ x : ι . x )`        -- refused: that is not a var
```

**A literal is parsed when it elaborates, not when the file is read.** A module
is parsed whole before its own `language` block is installed, so the grammar
does not exist yet when the region is lexed. What this costs you: a term your
grammar cannot read is reported as the definition elaborates, with the position
in the text and what was expected there, rather than as a syntax error.

**There is no hole.** `?` inside a literal is an ordinary character of your
language. It is a hole in `:parse` only, and a term with one is not a term —
a constructor has no missing argument.

---

### A judgment is written as on paper, and it is an inductive family

*Decided 2026-09-21.* A `judgment` block gives a notation, whose slots are the
judgment's indices **in the order they are written**, and its rules:

```
judgment typing = Γ ⊢ M : T where

  T-var:  x : T ∈ Γ
          -----------
          Γ ⊢ x : T

  T-app:  Γ ⊢ M : ( S -> T )    Γ ⊢ N : S
          --------------------------------
          Γ ⊢ ( M N ) : T
```

It declares an ordinary datatype, one constructor per rule, and `:show typing`
prints it:

```
data typing : Ctx -> LC -> Ty -> Type₀ where
  T-var : ∀ (x : String) (T : Ty) (Γ : Ctx) -> extend-in x T Γ -> typing Γ (var x) T
  T-app : ∀ (Γ : Ctx) (M : LC) (S : Ty) (T : Ty) (N : LC)
            -> typing Γ M (arrow S T) -> typing Γ N S -> typing Γ (app M N) T
```

**Every metavariable is quantified, in the order it first appears**, reading
the premises and then the conclusion. A metavariable is one a `language` or
`context` declared, or a token class's name, with any suffix of primes, digits,
subscripts or underscore subscripts: `M'`, `N₁`, `T2`, `x'`, `M_1`, `T_left`. **Nothing else is a name in a rule**: a
rule has no object literals, so `Γ ⊢ p : T` is refused (`p is not a
metavariable`) rather than quantifying a `p`.

**A line break ends a premise.** Several may share a line, separated by
whitespace, and parsing decides where one ends; a line indented further than
the first premise continues the one above:

```
  T-app:  Γ ⊢ M :
              ( S -> T )
          Γ ⊢ N : S
          ---------------
          Γ ⊢ ( M N ) : T
```

A premise may be named, `d : Γ ⊢ M : T`; one that is
not is `d1`, `d2`, … by position. A premise is never named like a
metavariable, so `x : T ∈ Γ` is always the lookup. `E[x->N]` is `LC-subst E x
N`; `E[x->M, y->N]` is `LC-subst-all`, simultaneous; `E[x->M][y->N]` is one
after the other.

**The annotated tier writes the quantification**, which fixes the argument
order and may range over a derivation:

```
  rule A where ∀ (T : Ty) (M : LC) (Γ : Ctx) (d : typing Γ M T) ->
      Γ ⊢ M : T
      ---------
      Γ ⊢ M :: T
```

There, a metavariable the `∀` does not bind is refused, and so is a name it
binds twice: the `∀` lists the rule's metavariables, it does not nest. **The notation is
installed**, as a context's lookup is: `` typing`· ⊢ ( λ x : ι . x ) : ( ι -> ι )` ``
is a type, and `:parse typing …` reads one.

### A context gets a lookup relation per kind of binding, written `x : T ∈ Γ`

*Decided 2026-09-21; one relation per extension 2026-10-04.* A `context` block
declares its datatype and, beside it, the relation that looks a name up — one for
each form the context can be extended by:

```
context Ctx, Γ where
  empty  -> ·
  extend -> Γ , x : T
```

```
data extend-in : String -> Ty -> Ctx -> Type₀ where
  extend-here : ∀ (Γ : Ctx) (x : String) (T : Ty) -> extend-in x T (extend Γ x T)
  extend-there-extend
    : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty)
        -> (Eq String x x' -> Empty) -> extend-in x T Γ -> extend-in x T (extend Γ x' T')
```

**A context may be extended in more than one way**, and System F's cannot be
written any other way — its Γ carries both a term's type and a type variable's
bound:

```
context Ctx, Γ where
  empty  -> ·
  bindTm -> Γ , x : T
  bindTy -> Γ , X <: T
```

That declares `bindTm-in` and `bindTy-in`, each reading its own notation —
`x : T ∈ Γ` and `X <: T ∈ Γ` — and each with a constructor for stepping over
every kind of binding: `bindTm-there-bindTm`, `bindTm-there-bindTy`, and the two
for `bindTy-in`. **The names come from the extension production, not the
context**, because three names taken from the context alone would collide the
moment there are two extensions.

**Its notation is the extension with the context taken out, then `∈` and the
context**, and it is a grammar like any other: `` extend-in`x : ι ∈ ·, x : ι` ``
is the type `extend-in "x" base (extend empty "x" base)`, `:parse extend-in …`
reads it, and it prints back. The separator goes with the context: `Γ , x : T`
gives `x : T ∈ Γ`, and so does `x : T ; Γ`. **The indices are the notation's
slots in order**, as a judgment's are, so the context comes last.

**A later binding shadows an earlier one of the same name.** `extend-there-extend`
asks for a proof that the two names differ. For two literals that proof needs no
axiom; `eqString` and `Eq`'s eliminator give it:

```
xNotY : Eq String "x" "y" -> Empty
xNotY = \ q ->
  elim Eq (String)
    (\ a b r -> elim Comparison () (\ c -> Type₀) ((Unit) (Empty)) () (eqString "x" a)
                -> elim Comparison () (\ c -> Type₀) ((Unit) (Empty)) () (eqString "x" b))
    ((\ a d -> d))
    ("x" "y") q unit
```

Reaching an `x` under a later `x` would need `Eq String "x" "x" -> Empty`, and
nothing proves that.

**Only a binding of the same kind of name needs that proof.** Shadowing happens
within one namespace, so looking a term variable up past `X <: T` asks for
nothing — `bindTm-there-bindTy` has no inequality premise at all.

**Each extension must have exactly one name** (a `Token String` argument),
because that is what the lookup compares, and a production that joins two
contexts is refused. Weakening and exchange are not generated.

**A context also gets substitution, by the same rule a language does.** For every
kind of name its entries can hold, it gets the free-variables function and the
substitution — so F-sub's Γ, whose entries hold types, gets:

```
Ctx-fv-X     : Ctx -> List String
Ctx-subst-X  : Ctx -> String -> Ty -> Ctx
Ctx-subst-all : Ctx -> List (And String Ty) -> Ctx
```

`Ctx-subst-X` is the `[X↦P]Δ` that System F's type-substitution lemma is written
with, and a rule may write it in notation: `Γ[X -> T]` elaborates to
`Ctx-subst-X Γ X T`.

It is a plain fold with **no capture avoidance and no renaming**, because a
context's name slot is an ordinary name and not a binder: `Γ , x : T` has no body
for `x` to scope over. So each entry's name is copied as written and each entry's
types are substituted. **It does not stop at a binding of the kind it is
substituting for** — applied to `· , X <: ⊤ , x : X` it replaces that `X` as
well, since that `X` binds nothing — which is what the lemma needs, because it
substitutes into the part of the context *after* the binding. A context gets no
`fresh`, because minting a name belongs to the language that reads that kind of
name. A context whose entries can hold no name at all gets nothing.

### A language gets substitution for free, and a binder is renamed only when it would capture

*Decided 2026-09-21; one family per kind of name 2026-10-07.* A `language` block
with a variable production (`var : x as occurrence -> x`) also declares functions
for every kind of name it can contain, right after its datatype — here the one
kind, `x`:

```
LC-fresh-x   : String -> List String -> String
LC-fv-x      : LC -> List String
LC-subst-all : LC -> List (And String LC) -> LC     -- simultaneous
LC-subst-x   : LC -> String -> LC -> LC             -- LC-subst-x E x N is E[x->N]
```

**The kind is in the name even when there is only one**, because leaving it out
in that case would be a special case in the naming rule, and a language may read
more than one kind of name — see the next entry.

They are ordinary definitions, written by `elim` and elaborated like anything
you write. They compute, so a substitution's answer is provable by `refl`:

```
captured : Eq LC (LC-subst-x (abs "y" base (var "x")) "x" (var "y")) (abs "y'" base (var "y"))
captured = refl LC (abs "y'" base (var "y"))
```

**A binder keeps its name unless keeping it would capture**, and is then primed
until it is free: `y`, `y'`, `y''`. Nothing is renamed behind your back, so
capture is something you can see happen and see avoided. A list substitutes
simultaneously (`[x->y, y->x]` swaps), and of two pairs for one name the first
wins.

What it needs of the language, each refused at the block with a message: one
variable production **per kind of name**, taking only its occurrence; and a
binder free only in an argument of a language that reads names of that binder's
kind — see the next entry. A language that can contain no name at all (`Ty` in
the example above) gets nothing. The four names are yours to keep free — declaring `LC-fv` first
is refused.

A binder of one kind does not bind names of another: the kinds are separate
namespaces, and a binder at a kind no language reads is never renamed at all,
because nothing can ever occur at it.

Two things arrived with it. **`List`, with `nil` and `cons`, is in the
prelude**, so those names are taken from every object language until imports
exist. **`appendString : String -> String -> String`** is the one way to build
a `String`, and it computes only on two literals. The types that mention `List`
carry a level parameter, `LC-fv {ℓ}`, because a list of names is a list at any
level and nothing is defaulted.

### A binder may scope into another language, if that language reads that kind of name

*Decided 2026-10-04, built 2026-10-06.* A binding form's body may be a slot of a
different language, so long as names of the binder's kind can actually occur in
it:

```
language Ty, T, S where
  tvar : X as occurrence -> X
  arrow                  -> T -> S

language Tm, M, N where
  var  : x as occurrence -> x
  abs  : x as binder     -> ( λ x : T . M[x] )
  pack : X as binder     -> ( pack X = T in S[X] )
```

`pack` binds `X`, and `S` is a `Ty` — another language's term. Before, that was
refused outright: a binder had to be free only in arguments of its own language,
because substitution over that language is the only thing that walks into them.
The refusal now asks a question instead, and it is a question about more than one
grammar: **which kinds of name does a language reach?** Those its own occurrences
and binders name, and everything the languages in its slots reach. `Ty` reads
`X`, so `pack` is allowed. Had `Ty` read no names at all, nothing inside an `S`
could ever be an `X` and the form is refused as before — with a message that says
so.

**This is computed as a reachability fixpoint and not as a walk in declaration
order**, although no two languages may yet refer to each other, so the two would
agree today. They will not when they can, and the cost of writing it the right
way now is nothing.

`Tm` therefore reaches two kinds of name while owning one, and gets a
substitution for each:

```
Tm-subst-x   : Tm -> String -> Tm -> Tm     -- a term for a term variable
Tm-subst-X   : Tm -> String -> Ty -> Tm     -- a TYPE for a type variable
Tm-subst-all : Tm -> List (And String Tm) -> List (And String Ty) -> Tm
```

**A kind of name belongs to the language whose variable production reads it**, and
that is what a substitution for it replaces a name *with* — so `Tm-subst-X` takes
a type. Two unrelated languages may both read `x : Token String`, each the owner
for itself; what is refused is one language reaching two that read the same kind,
where the substitution would have no single language to replace a name with.

It matters because System F's polymorphism is this shape: `Λ X <: T . t` binds a
type variable in a *term* production while every occurrence of `X` is in a type.
And it is why substituting for one kind of name has to be able to rename binders
of **every** kind the term can contain — substituting `λ y : X . y`, which has a
free type variable, for `x` in `Λ X <: Top . x` captures that `X` unless the type
binder is renamed too.

**A slot of another language is walked through that language's own
substitution**, with the maps that language needs and any binder of this one that
scopes over the slot added to them. So `pack`'s `S` is substituted rather than
copied, and nothing about a foreign slot is opaque any more unless the language in
it can contain no name at all.

**Substituting for one kind of name renames binders of every kind.** Replacing
`z` by `λ y : X . y` in `Λ X <: Top . z` gives `Λ X' <: Top . (λ y : X . y)`:
the type binder is renamed because the term being substituted in has a free type
variable, and renaming only the term binders would have captured it.

### Thena does not assume K, and a dependent index telescope is handled by transported equations

**Thena's identity type is the ordinary Martin-Löf one and K — uniqueness of identity
proofs — is not assumed.** So `uip : (q : Eq A a a) -> Eq (Eq A a a) q (refl A a)` is not
provable here, as it is not in Agda under `--without-K`:

```
uip = \ A a q -> case q of { refl b -> refl (Eq A b b) (refl A b) }

stuck: the goal does not survive generalising the target
```

**The reason is structural rather than a check.** Splitting on a target of an indexed
family works by generalising the family's indices into the motive and carrying one equation
per index into each method. A motive abstracts the indices *separately*, so the arm's goal
has to make sense when they differ — and a goal that needs the equality proof to be `refl`
has no such reading. There is nothing to switch off: the K-needing goal cannot be written
down.

**The deletion step is kept, and keeping it is sound.** An equation `Eq I t t` constrains
nothing and its binder is bound and ignored. This is the step that requires K in a system
where a clause's right-hand side may depend on the equality proof; in Thena the goal never
mentions these proofs, so the step is the proof-irrelevant one.

**Where an index's type depends on an earlier index, the equation is stated after
transporting along the earlier one.** `Eq (Vec A n) as as'` is ill-typed when
`as' : Vec A n'`; what is stated instead is the equation between `as` transported along
`n ≡ n'` and `as'`, so every equation stays homogeneous. This is the homogeneous
*telescopic equality* of Cockx, Devriese and Piessens, *Pattern Matching Without K* (2014),
and it is what Thena uses in place of a heterogeneous ("John Major") equality, whose
elimination rule is equivalent to K.

**That is built for a constructor's arguments, which is where the no-confusion equipment
needs it.** Every `data` gets its `NoConfusion` family and `noConfusion` lemma now,
including `Vec`, `Fin` and any judgment whose rule takes an argument typed by an earlier
one; before, such a datatype was declared without equipment and the load said so. For a
two-argument constructor the lemma's diagonal case reads

```
NoConfusionFin (fs n i) (fs n' i')
  = DPair (Eq N n n') (λ q. Eq (Fin n') (transport q i) i')
```

— a *dependent* pair, because the second equation's type mentions the first equation's
proof. Where the rest of the chain does not mention an equation's proof the pair is the
ordinary `And` it always was, so nothing written against the old shape changed. **Which of
the two it is, is read off the equation that was built and not predicted from the
telescope**: an argument may be carried along inside a chain while nothing mentions the
argument itself, and the rest of the chain still mentions its proof.

**And the same construction is now built one telescope over, for the family's own
indices.** Eliminating `b : Below (succ m) (fz m)` — where `Below : ∀ (n : Nat) (i : Fin n)
-> Type₀` — used to be refused outright, because `Eq (Fin i₁) i₂ (fz m)` has its two sides
at `Fin i₁` and `Fin (succ m)`. Each method now carries

```
∀ (m₁ : Nat) (q : Eq Nat (succ m₁) (succ m))
  -> Eq (Fin (succ m)) (transport q (fz m₁)) (fz m) -> …
```

The carrier is the *actual* earlier index, so the equation is homogeneous; the actual side
is left bare, which is what keeps it in reach of the unifier; and the generalised side is
carried there along the earlier equation. Where no index's type mentions an earlier one the
chain is empty and the equation is the one it always was.

**And for an indexed family the no-confusion pair gives each element its own indices.** A
pair that puts both elements at one index group says nothing about two elements at two
*different* indices — and that is what acyclicity needs, its last step being an assumed
equation between two constructor applications whose indices are not visibly the same. So
the family takes an index group per element, and the lemma takes a *chain* where it took a
single `Eq`:

```
NoConfusionEv : ∀ (n : N) -> Ev n -> ∀ (n' : N) -> Ev n' -> Type₀
noConfusionEv : ∀ (n : N) (a : Ev n) (n' : N) (b : Ev n')
                  (q : Eq N n n')
               -> Eq (Ev n') (transport q a) b
               -> NoConfusionEv n a n' b
```

The chain is **curried**, one argument per equation, rather than packaged into a pair: a
split holds its equations as separate binders, one per tied index, so a lemma it calls
takes them that way. The payload is unchanged — on the diagonal both sides are the same
constructor, whose own arguments determine both index groups, so the indices need no
equations of their own.

**Where a family has no indices this is the shape it always had**, the chain being its one
equation, so a proof written against the old lemma is untouched: all 318 uses across the
examples needed no change. The two shapes lived side by side under separate names for a
day — the telescopic one was generated first and replaced the other once it was known to
sit snugly, so that no corpus measurement had to separate two changes at once.

**It costs one thing: a family whose index telescope is dependent now needs `DPair` to get
a no-confusion lemma at all.** The reason is worth following, because it is a constraint on
anyone writing a prelude rather than a detail of the generator.

The chain is stated over the telescope `(indices; element)`, and each equation of a chain
is stated after *transporting* the earlier side along the earlier equation. A transport
needs a motive — `λ z . A[x := z]` — and where a *later* entry's type also mentions `x`
that motive cannot be written: it would have to mention the later entry at a type it no
longer has. The entries that must move together are therefore packaged, moved once, and
walked down one component at a time; and a package of two entries or more is a dependent
pair. For

```
Below : ∀ (n : Nat) (i : Fin n) -> Type₀
```

`i`'s type mentions `n` and the element's type mentions both, so comparing a `Below n i`
with a `Below n' i'` packages `i` with the element and the chain wants `DPair`.

**The homogeneous lemma never wanted it**, because both elements sat at one index group and
there was nothing to transport — so this is a need the replacement introduced, and it joins
the per-datatype questions the generator already asks (`Empty` only with two or more
constructors, `Unit` only for a nullary diagonal, and so on). **Asking once, for every
datatype, would be wrong**: the prelude must declare `Eq` before `DPair`, since `DPair`'s
own no-confusion states equations — so a blanket demand would silently lose `NoConfusionEq`
at the very line the rest is built on. `Eq`'s two indices mention neither each other nor
anything else, so `Eq` is not in this position and neither is anything else Thena ships.

**What a prelude that gets it wrong loses is the whole lemma for that one datatype**, not a
weaker version of it: declaring a dependently indexed family before `DPair` now yields no
no-confusion for it, where before the replacement it yielded the homogeneous one. That is
the price of having one shape instead of two, and it is paid in a corner nothing reaches.

**And every `data` gets the acyclicity equipment: `BelowD`, `NotEqD`, `NotBelowD` and
`NotBelowEqD`.** These are what a *cycle* is discharged with — an equation between a
variable and a term that contains it structurally, `k ≃ s k`, which is how a case the user
correctly omitted is recognised as impossible rather than merely undischarged. For `N`:

```
BelowN      : ∀ (P : N -> Type₀) (n : N) -> Type₀
NotEqN      : ∀ (x : N) (y : N) -> Type₀
NotBelowN   : ∀ (x : N) (y : N) -> Type₀
NotBelowEqN : ∀ (x : N) (y : N) -> Type₀
```

`BelowN P n` is the tuple asserting `P` of everything structurally smaller than `n` —
`Unit` at a constructor with no recursive argument, and `And ‹the sub-tuple› (P a)` per
recursive argument otherwise. It is **one elimination at a type-valued motive**, and the
inductive hypothesis the eliminator hands each method *is* the sub-tuple, because the
elimination computes a type rather than a proof. `NotEqN` is `≢`, `NotBelowN` is
`≮ := Below (λ w . x ≢ w)`, and `NotBelowEqN` is `≰ := ≮ × ≢`.

**`belowD` and `recD` — the tuple's inhabitant and the structural recursor built from it —
are not generated, and that was measured rather than assumed.** Every elimination the
acyclicity construction needs is an ordinary `elim D` at a motive the generator writes, so
nothing ever mentions them.

**For an indexed family the two sides sit at two different index groups**, related by the
same curried chain the telescopic lemma takes: a cycle compares a variable with a
constructor application, and for an indexed family those are at different indices. So

```
NotEqEv : ∀ (n : N) -> Ev n -> ∀ (n' : N) -> Ev n' -> Type₀
```

reduces to `(q : Eq N n n') (r : Eq (Ev n') (transport q x) y) -> Empty`.

**Four more names are reserved per datatype, in the same shared namespace**, so a
definition already called `BelowFoo` makes `data Foo` refuse. **The equipment has its own
precondition and is skipped on its own**: it needs `Unit` where a constructor has no
recursive argument, and a datatype that cannot have it keeps its no-confusion lemma
regardless. It costs about 4% of the time it takes to load the example corpus, measured.

**And the acyclicity theorem itself: `noCycleDiagD` and `noCycleD`.** The first says no term
is structurally below itself; the second says nothing equal to a term is below it either,
and it is what a *cycle* is discharged with. For `N`:

```
noCycleDiagN : ∀ (n : N) -> NotBelowN n n
noCycleN     : ∀ (x : N) (y : N) -> Eq N x y -> NotBelowN x y
```

So the user's correctly omitted case — the one where a split leaves `n ≃ s n` behind
because the case cannot arise — is discharged by

```
noSelfN : ∀ (n : N) -> Eq N n (s n) -> Empty
noSelfN = \ n e -> andRight (NotBelowN n n) (NotEqN n n) (noCycleN n (s n) e) (refl N n)
```

**For an indexed family the equation is the chain**, so `noCycleD` takes it curried and the
contradiction is reached by supplying reflexivity, which makes every transport contract. No
appeal to UIP anywhere, and no heterogeneous equality.

`noCycleDiagD` carries the appendix's `Step` lemma **inline** at each recursive argument of
each constructor, rather than under a name of its own: each is used exactly once, so a name
would reserve one per recursive argument of every constructor and buy nothing.

### When `noCycle` is not generated, and what you see if it is not

*Decided 2026-10-27, and the condition changed the same week.*

**Whether a datatype gets `noCycleDiagD` and `noCycleD` is decided by the checker and not
by a question about the telescope.** The two are generated, checked, and kept if they
check; if the checker refuses one, both are withheld and the declaration goes through
without them. The four relations above, and the no-confusion pair, are generated
regardless.

**No shape of constructor telescope is known to be withheld today.** It used to be one — a
constructor with a *middle* argument, one that both depends on an earlier argument and is
depended on by a later one:

```
enode : ∀ (x : A) (y : B x) (r : E) -> E              -- y depends on x; nothing depends on y
fnode : ∀ (x : A) (y : B x) (z : C x y) (r : F) -> F  -- y is in the middle
```

Both get their acyclicity equipment now. An argument that a later argument depends on
cannot be transported on its own — the motive would have to mention the later argument at a
type it no longer has — so it travels packaged with the arguments that depend on it, and
the chain reads each component back out by *projection*. **The package holds exactly the
arguments that have to travel, and is moved one component at a time**, along the equations
that component's own type mentions and in the order those equations were stated. Taking the
contiguous span over them instead dragged in an argument that nothing in the package
mentions, and that argument's own equation then came out as a projection out of a pair
transported along its neighbour's proof — a transport no step of the nested `J` eliminates.

**What you lose where they are withheld.** Exactly one thing: a split over such a family
keeps a cyclic equation instead of refuting it, so a case you were right to omit is refused
with `no clause of case-must-vanish applies here` rather than accepted. Nothing is accepted
that should not be — the loss is capability — and nothing else about the declaration
changes.

**The whole acyclicity bundle — six definitions per `data` — costs about 8% of the time it
takes to load the example corpus**, and about 30% on the largest single development in it.
Measured by generating and not generating, two runs each.

### Every shape of index telescope declares, and the fourth dependent index does not finish

*Measured 2026-10-28.*

**A family whose index telescope has several indices each depending on an earlier one, with
the family's own element depending on all of them, declares and splits.** A relation between
two vectors — `Append`, `Permutation` — has that shape, and it was refused outright until
2026-10-28 with `the generated noConfusionD does not typecheck, which is a bug in Thena`.

```
data One   : ∀ (n : Nat) (as : Vec A n) -> Type₀                           -- fine
data After : ∀ (n : Nat) (as : Vec A n) (m : Nat) -> Type₀                 -- fine
data Pair2 : ∀ (n : Nat) (as : Vec A n) (bs : Vec A n) -> Type₀            -- fine
data Both2 : ∀ (n : Nat) (as : Vec A n) (m : Nat) (bs : Vec A m) -> Type₀  -- fine
data Three : ∀ (n : Nat) (as bs cs : Vec A n) -> Type₀                     -- fine, ~9 s
data Four  : ∀ (n : Nat) (as bs cs ds : Vec A n) -> Type₀      -- does not finish
```

**What that last line is, and it is a cost rather than a rule.** The telescopic equality
such a family generates grows by about eight times with each dependent index: the chain and
the proof of it come to 47 KB together for one dependent index, 520 KB for two and 5 MB for
three. Checking them costs 0.05 s, 0.7 s and 9 s. **A fourth does not finish**, so a
relation over four vectors of one length is not usable today, and it stops rather than
telling you so.

**It was 25× before, and three did not finish.** What came down is duplication, not work:
the pair a package travels in writes its second parameter six times and `J` writes its
motive three, and both of those hold every projection read out of the package so far.
Naming them with a `let` — which changes nothing a term *means* — took the three-index chain
from 77 MB to 5 MB.

**A level-polymorphic index type.** The equipment generated over an index telescope is
stated at the datatype's own level joined with every index type's, and not at the
datatype's alone. An index is not a constructor argument: the size restriction bounds an
argument's type below the datatype's level, and nothing bounds an index's, so
`data Only (A : Type) : ∀ (n : Nat) -> Vec A n -> Type` relates the two not at all. Stating
the chain at the datatype's level refused that declaration outright unless some constructor
argument happened to force the two levels together.

**Two shapes are still refused, and both are a missing step of that chain rather than a
missing equality.** An index whose type mentions an earlier index that was *abstracted
outright* has no equation to transport along; and two mentioned indices that are themselves
chained — `Chain : ∀ (n : Nat) (i : Fin n) (b : Below n i) -> Type₀` — need a motive
abstracting the equality *proof* as well as its endpoint.

**And splitting on such a family solves its chain.** A later equation of the chain is
stated about an earlier one's *proof*, so the step that solves the earlier one removes the
binder that proof is — and so it supplies `refl` for that proof as it goes, every transport
along it computes away, and the next equation is an ordinary homogeneous one. For

```
data Q : ∀ (n : N) -> Fin n -> Type₀ where
  mk : ∀ (n : N) (i : Fin n) -> Q n i

tied : ∀ (m : N) (x : Q (s m) (fz m)) -> N
tied = \ m x -> case x of { mk n i -> m }
```

both equations are discharged and the arm binds `n` and `i` and nothing else. Before, this
was refused.

**This is the paper's own `solution` step, and it is derived rather than assumed.** The
step wants *based path induction* — a motive over the end that varies and the proof, with
the other end fixed — while Thena's `Eq` has both ends as indices and so gives the
symmetric Martin-Löf rule. The gap is closed by the singleton `Σ (y : I). y ≡ t`, which has
one inhabitant up to `Eq`: the ordinary rule proves that, and carrying the goal along it is
an ordinary transport. **No universe is spent**, which the obvious alternative — quantifying
over the goal family — would have cost.

**Taking a constructor equation *apart* crosses a chain too, and that is what makes a
pinned index splittable.** For

```
data Small : ∀ (n : N) -> Fin n -> Type₀ where
  isFz : ∀ (n : N) -> Small (s n) (fz n)

tiedTwo : ∀ (m : N) (x : Small (s m) (fz m)) -> N
tiedTwo = \ m x -> case x of { isFz n -> n }
```

the first equation is between two applications of `s`, so injectivity fires where
`tied`'s solution did. It replaces that equation with one about `s`'s argument and drops
its binder — and the second equation was stated about that binder. **The no-confusion
lemma run backwards turns the new equation back into a proof of the old one, and its
round-trip law says the proof it rebuilds is the one that was given**, so the second
equation is restated along the rebuilt proof and the law carries the method back. Both
definitions are generated per datatype beside `noConfusion` itself. Before, this was
refused.

**It crosses a chain for a constructor of one argument over a datatype with no indices,
and keeps the equation otherwise.** More arguments put the new equations in a pair, and
there is then no single proof to rebuild from; indices make the law an equation between
packaged chains rather than between proofs.

**And where both sides of an equation are the *same* constructor application, taking it
apart is offered where deleting it is refused.** Deletion matches such an equation first —
the two sides are literally the same term — and deletion is the one step that cannot cross
a chain. But injectivity applies to that very equation, so it is tried instead of refusing,
and no part of it is K: `s z = s z` is read apart to `z = z`, and that to nothing at all,
because a constructor with no arguments states no equations. At that bottom the proof is
rebuilt from the trivial chain and the same round-trip law carries the method back. For

```
data T : Fin (s (s z)) -> Type₀ where
  mkT : ∀ (i : Fin (s z)) -> T (fs (s z) i)

pinned : ∀ (x : T (fs (s z) (fz z))) -> Fin (s z)
pinned = \ x -> case x of { mkT i -> i }
```

`T`'s index pins `fs`'s first argument to the same term on both sides, so the chain's first
equation is `Eq N (s z) (s z)`. The split goes through and the arm computes with the
argument it bound. Before, it was refused with UIP given as the reason.

**And where the index *pins* a constructor argument, the equation is taken apart by
projection, which states no equation about the pinned one at all.** Splitting

```
headAll : ∀ (A : Type₀) (P : A -> Type₀) (m : N) (a : A) (as : Vec A m)
            (ps : All A P (s m) (vcons A m a as)) -> P a
headAll = \ A P m a as ps -> case ps of { allNil -> ; allCons n b bs pb qs -> pb }
```

asks what `vcons A m b bs = vcons A m a as` tells you, and taking a constructor equation
apart states one equation per argument — including the **length**, which is `m` on both
sides because `vcons`'s own result type says the length is the index. That equation says
nothing, and deleting it is K, so the split used to stop there. Now each argument's
equation comes instead from a function out of the family *at that index*, so every
equation is stated at the pinned type and none mentions another's proof — and the pinned
argument, whose two sides are the same by typing, gets no equation at all. **Agda accepts
this definition without K for the same reason**: its unifier never states an equation for
a position the index determines.

**One shape still cannot cross a chain, and that one is the K line itself.** An equation
between a *variable* and itself that nothing pins, with a later equation stated about its
proof, has no constructor head for injectivity to take apart whatever order the steps are
tried in, and deleting it is UIP. A split that meets it is refused by name, with the
position and what is missing.

**A split also takes a constructor equation apart when the constructor's own arguments are
dependent.** That is the no-confusion chain rather than the motive's one, and the two are
independent: a datatype with no indices at all can have it. For

```
data Pack : Type₀ where
  pack : ∀ (n : N) (i : Fin n) -> Pack

data Holds : Pack -> Type₀ where
  holds : ∀ (n : N) (i : Fin n) -> Holds (pack n i)

depth : ∀ (m : N) (j : Fin m) (x : Holds (pack m j)) -> N
depth = \ m j x -> case x of { holds n i -> s n }
```

the split's one equation is `Eq Pack (pack n i) (pack m j)`; taking it apart gives the two
equations the lemma's dependent pair holds, the first solves `n` and supplies `refl` for its
own proof, the transport in the second computes away and it solves `i`. Before, the
equation was handed back undischarged and the arm did not typecheck.

**The case where the constructor's result type pins the argument is the one the step above
buys.** `fs n i` and `fs m j` inhabit one `Fin` only when `n` and `m` are the same term, so
the chain's first equation is between two identical terms — deletion's shape, taken apart by
injectivity since it is also two applications of one constructor. `pinned` above is that
case end to end.

**What this costs: nothing you can currently name in language metatheory.** The proofs K
buys are proofs *about* equality proofs rather than proofs that use them. If one is ever
needed, K is provable rather than assumed for any type with decidable equality (Hedberg),
so it can be had for one datatype instead of assumed everywhere.

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
rule pick s :- when focus-is-hole (surface-is-name s) do say "a name"
rule pick s :- when focus-is-hole                     do say "not a name"
```

```
thena spine> pick surface`foo`
chose 681: pick
a name
thena spine> pick surface`Type₀ -> Type₀`
not a name
```

**The argument is written in the surface fence**, and it did not have to be when
this was decided: a REPL line was an argument run then, so a bare `foo` was a
surface term. Since MS5 a REPL line is one line of `instral` and a bare word is
a *reference*, so a surface term says which language it is in — which is the
same rule a rule body follows.

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
  do n = fresh-name "refined" ; x = define n t
     ; s = typeof x ; g = goal ; unify-into s g ; prim-try x

rule unify-refine-core t :- when focus-is-hole do fill t ; solve
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
  do w = surface-name t ; x = resolve-name w ; fill t ; solve

rule elaborate t :- when focus-is-hole (surface-is-placeholder t) do
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

**The three application clauses were an exception to that until 2026-10-15, and
the exception was the whole cause of two bad error messages.** An application is
split by its head — a name, an `elim`, or a term to elaborate in its own right —
and the third clause used to ask only that the arguments be explicit. So it
matched a name-headed application too, and was tried whenever the name-headed
clause failed. It claims `f : A -> B`, an arrow, which a dependent head does not
fit, so against `Eq` or `refl` it failed on its own claim *before* re-reaching the
argument that was actually wrong — and that spurious failure was what you were
shown:

```
a : Eq String "x" "x"    a = refl String "y"    stuck: A2 is not bound before A
```

`A` and `A2` are development components, nothing the user wrote. The real error
was computed and thrown away. The same discard hid a parse error inside an object
term literal: a missing bracket under `Eq` reported `A3 is not bound before A1`,
while the message naming the bracket existed and was discarded.

**The third clause now names its head, `app-head-is-term`, so the three are
mutually exclusive and the paragraph above is true without exception.** Both
messages are now the real one:

```
a : Eq String "x" "x"    a = refl String "y"    stuck: "y" and "x" cannot be made equal
```

**A head predicate is how this was fixed, and no failure ranking or clause
priority was added.** The head language has no negation, so "neither a name nor
an `elim`" is a third positive test, the way `let`'s annotated and bare clauses
are two. **It also removed a choice point from every name-headed application** —
elaborating `succ y` used to record one, because a second clause matched and
could be offered.

### A recursive call *is* the induction hypothesis, and that is the whole termination story

Write a function by splitting, and call it recursively:

```
double : Nat -> Nat
double = \ n -> induction n of { zero -> zero ; succ m -> succ (succ (double m)) }
```

`double (succ (succ zero))` is four. There is no `fix`, no case tree and no
termination checker — `double m` in the `succ` arm *is* the induction hypothesis
the eliminator already supplies, and elaboration replaces it with that
hypothesis.

**So the guard is not a check, it is what can be said.** An eliminator makes the
hypothesis available only at the smaller index, so there is nothing to verify:

```
loop = \ n -> induction n of { zero -> zero ; succ m -> loop zero }
  no induction hypothesis is about this call, so it is not structurally
  smaller: loop zero
```

`loop zero` names nothing that the `succ` method received a hypothesis about, so
it does not elaborate. Coq checks a guard condition in the kernel; Thena has
nothing to check, because an unguarded recursion cannot be written down.

**How the call finds its hypothesis is worth knowing, because the obvious way
does not work.** The name being defined is in scope in its own body as an
ordinary assumption, and a pass over the elaborated term replaces each
application of it. Which binder of a method is a hypothesis is read off the
datatype — a method takes the constructor's arguments and then one hypothesis per
*recursive* argument, in order — and a call resolves to the hypothesis about the
argument it **names**. Types cannot decide it: in `double`'s `succ` arm both the
pattern variable `m` and the hypothesis about it have type `Nat`, so a search by
type would pick either and still typecheck.

Three consequences a user meets:

- **A call naming two recursive arguments is refused**, because which one it
  recurses on is not written down. `g l r` in a `node l r` arm is that case.
- **Where a split pins an index, the arm's hypotheses are guarded by an equation
  and no call resolves there.** That is not a restriction being imposed: an
  inversion lemma's hypotheses are genuinely unusable, which is why the ones
  written by hand are bound and ignored.
- **A premise bound before the split is fixed, and the recursion may pass it but
  not vary it.** The motive quantifies what the split generalises and what it
  refines, and nothing else — so a premise already introduced stays at the one
  value it had, and the hypothesis is the statement at that value. Passing it is
  free, and the argument is simply dropped:

  ```
  size : ∀ (t : Tr) -> Ok t -> Tr -> Nat
  size = \ t d u -> induction d of
    { okLeaf -> zero ; okNode a b da db -> succ (size a da u) }
  ```

  Varying it is not the hypothesis, and says so:

  ```
  size2 = \ t d u -> induction d of
    { okLeaf -> zero ; okNode a b da db -> succ (size2 a da (node u u)) }
    the split fixed u and this call passes node u u, so it is not the
    induction hypothesis — a premise the induction varies is bound inside
    the arm and not before the split: size2 a da (node u u)
  ```

  **Bind it inside the arm and it varies freely**, because the motive then
  quantifies it and the hypothesis takes it:

  ```
  size3 = \ t d -> induction d of
    { okLeaf -> \ u -> zero
    ; okNode a b da db -> \ u -> succ (size3 a da (node u u)) }
  ```

  This is the one thing about an `induction` that the *shape* of the proof
  decides rather than its statement, and it is why a lemma that strengthens its
  own hypothesis — `chain n c`'s distinctness, where the recursion is at `c` with
  one more prime — writes that premise to the right of the split.

### A split whose equation has no solution hands you the equation, and says which one

Splitting a value asks whether the constructor's indices can be made equal to the
ones the thing you are splitting has. Thena discharges such a question by
substituting one side for the other, by discriminating two different
constructors, or by reading a constructor apart — and where the index is built by
a function that is not injective, none of those applies and none ever could:

```
data Cat : String -> Type₀ where
  mk : forall (a : String) (b : String) -> Cat (appendString a b)

pick : forall (x : String) (y : String) (p : Cat (appendString x y)) -> String
pick = \ x y p -> case p of { mk a b -> a }
```

`appendString a b` and `appendString x y` can be the same string without `a` and
`x` being the same — `"ab"` then `"c"` is `"a"` then `"bc"` — so nothing can
conclude `a = x`.

**The split is still offered, and the equation becomes a hypothesis of the arm.**
It is true where you stand, so taking it costs one binder and the proof goes
through:

```
pick = \ x y p -> case p of { mk a b -> \ q -> a }
```

**Refusing the split instead would withdraw that proof**, which is why Thena
keeps the equation where the standard presentation reports a failure. An arm that
does not take it is refused, and the refusal names the equation it owes:

```
stuck: String and Eq {0} String (appendString a b) (appendString x y) -> String
       cannot be made equal
  they differ by one argument, which the shorter side has to take first:
  Eq {0} String (appendString a b) (appendString x y)
```

The second line is said of any two types that differ by one argument, so an
under-applied term says it too.

**And writing no arm, or an arm with no body, says the same thing from the other
side.** Leaving a case out is the claim that it cannot arise; this one can, and
the refusal says what keeps it alive:

```
pick = \ x y p -> case p of { }
  stuck: this case did not vanish: it keeps
         Eq {0} String (appendString a b) (appendString x y),
         which no transition can discharge, so there is something to prove here
```

**It does not say which repair**, because the same fact is reported where no arm
was written, where an arm has no body, and where no arms were written at all —
what to change differs in each and you know which you wrote, while what the
system knows is only that the case is live.

### Dot patterns are optional here, because we run the eliminator and not the clause

When a split determines one of a constructor's arguments, that argument has no
binder left in the case it produces. Splitting `v : Vec A (succ n)` makes `vcons`'s
own length equal to `n`, so

```
vcons : ∀ (k : Nat) (a : A) (as : Vec A k) -> Vec A (succ k)
```

yields a case binding two arguments, not three. A reader who knows Agda will expect
to have to write `.n` there, and to be *required* to.

**Thena lets you write a name instead, and binds it as a definition.** Both spellings
exist; the dot is a way to say more, never an obligation.

**The reason is that the requirement protects something Thena does not have.**
Inaccessible terms — Agda's dot patterns — were introduced to keep a *left-hand side*
matchable: a matcher needs its pattern linear in the variables it binds, and
specialisation naturally wants one variable in two positions. Marking the position
inaccessible makes it bind nothing, and linearity survives. In the literature those
marks are inserted *by the translation*; requiring the programmer to write them is a
separate choice.

Thena has no left-hand side to keep linear. `induction t of { … }` elaborates to an
application of the datatype's eliminator, and the definition computes by that
eliminator's reduction rule:

```
pred = \ n -> induction n of { zero -> zero ; succ m -> m }
  elaborates to   elim Nat () (λ target -> Nat) (zeroMethod succMethod) () n
  and  pred (succ (succ zero))  reduces to  succ zero
```

There is no matcher in that term, so nothing needs to be linear and nothing has to be
marked.

**Nor does the determined fact have to be carried.** The transition that forces the
argument eliminates it by substitution, so the case is handed types already written in
the outer names — the sub-derivations of an inverted typing judgment have type
`Has m …`, not `Has m1 …`. And where you do name the position, the name is a
definition, so the equality is *definitional*: `m1` and `m` are convertible, and `refl`
proves `m1 = m` with no transport.

**What is given up is a check, not an ability.** With dots required, the mark is an
assertion the system verifies. Without them, the same text means a binder or a
definition depending on an inference you cannot see, and changing a lemma's statement
can silently change which. The answer to that is the dot, written where you want the
check — and, later, an editor that can say it about the arm your cursor is in. **Loading a
file says nothing about it**, deliberately: a line per determined position, over a file of
fifty theorems, is noise rather than information.

**So the dot is the check, written where you want it.** Four things are legal in a
determined position and all four mean something different:

```
case xs of { vcons n  a as -> … }   -- n is a DEFINITION equal to the forced term
case xs of { vcons _  a as -> … }   -- ask for nothing
case xs of { vcons .n a as -> … }   -- ASSERT it is determined, and to n
case xs of { vcons ._ a as -> … }   -- assert it is determined, decline to say to what
```

A dot binds nothing. The term after it is an ordinary term — `.n` for a name,
`.(succ n)` for anything larger — elaborated at the type the position has and then
unified with the term the equation forced it to. So the type is checked as well as the
value: `.true` where a `Nat` was determined is refused before the comparison is
reached. And because a placeholder elaborates to a hole that unification solves, `._`
costs nothing beyond the assertion it makes.

**A dot on a position nothing determined is refused.** That is the assertion failing,
and it is the whole of what the notation buys: splitting a `Vec A n` with `n` a plain
variable generalises it and leaves `vcons`'s own length a genuine binder, so there is
nothing there to assert. `examples/dot-patterns.thena` has all of it, the refusals
included.

**What a dot cannot do is destructure.** A position can be determined to a compound
term — splitting `Vec A (succ (succ n))` determines `vcons`'s length to `succ n` — and
either spelling can name it or ignore it; an inaccessible position binds nothing, so
there is no sub-pattern inside one. That is a refusal under both spellings alike.

### A case that cannot happen is an arm with no body, and there is no `impossible`

Splitting a `Vec A (succ n)` leaves no `vnil` case: `succ n = zero` is a conflict, so
that method is discharged by the conflict and there is nothing to prove. Agda has you
write an absurd pattern; Idris has you write `impossible`. **Thena has you write the arm
and stop at the arrow.**

```
vtail : forall (A : Type₀) (n : Nat) -> Vec A (succ n) -> Vec A n
vtail = \ A n v -> induction v of { vnil -> ; vcons k a as -> as }
```

The whole split may also be written with no arms at all — `induction d of { }` — which
is how the inversion lemmas in `examples/canonical.thena` are written, and **an empty
arm is that same notion for one case rather than for all of them.** A keyword would have
been a second spelling for something the syntax could already say.

**And it would have spent the name.** A tactic called `impossible` — one that takes a
case you believe cannot arise and finds the contradiction for you — is wanted, and a
tactic in Thena is an ordinary rule whose name is an ordinary identifier. One lexer
serves the surface and the rule language, so a word reserved for `induction … of` is a
word no rule can be called.

**Writing a body there is a refusal, not a redundancy.** The case being gone is
something the system has a proof of, so a term written in that arm is a claim that the
case can arise, against that proof. The converse is a refusal too: an empty arm for a
case that *did* survive is refused, so believing a case impossible when the system
could not discharge it is something you find out at the split. **What the refusal says
today is only that the arm needs a body**; it does not hand you the method, and
improving that is open work.

**Underneath it is one law — every arm you wrote was asked for.** Elaboration walks the
datatype's constructors asking for an arm for each, and the law is the other direction.
It is what refuses an arm for a case that vanished, an arm headed by a constructor of
some other datatype, and a second arm for a constructor that already has one — three
mistakes, one rule, and nothing in the system has to tell them apart.

### A split refines variables bound before it, where it has to and not otherwise

A split's motive abstracts the *indices* of the family, so splitting `e : Ev (s m)`
abstracts `s m` — not `m`. On its own that leaves `m` fixed, and a goal about `m` rather
than about `s m` has nothing for the motive to abstract. **So where it has to, the motive
also quantifies a fresh copy of the outside variable**, states the equation about the
copy, and the use site passes the variable itself together with `refl`. The copy is a
binder the elaborator introduced, so the specialiser can solve it; the variable stays
where it was. This is all that is needed:

```
refined : forall (m : N) (e : Ev (s m)) -> IsSucc m
refined = \ m e -> case e of { evs n en -> isucc n }
```

`evs n en` forces `m`'s copy to be `s n`, the goal arrives as `IsSucc (s n)`, and
`isucc n` is the arm. It computes, too: `refined (s z) (evs z evz)` is `isucc z` by `refl`.

**A hypothesis about a refined variable comes with it**, because a hypothesis whose type
mentions a refined variable is refined too — otherwise the arm would hold a hypothesis
about something that no longer means what it meant. Inside the arm it arrives under its
own name:

```
usesHyp : forall (m : N) (h : Ev m) (e : Ev (s m)) -> IsSucc m
usesHyp = \ m h e -> case e of { evs n en -> isucc n }
```

**AND "WHERE IT HAS TO" IS DECIDED BY LOOKING, POSITION BY POSITION.** Compare the rule's
own index with the scrutinee's. If the rule's side is one of the **rule's own variables** —
`eSucc c1` against `succ p` — then that variable is the one that moves, the equation is
solved with no copy involved, and nothing is generalised. Only where the rule's side has
something else facing a bare outside variable — `eIfTrue`'s `true` against `p` — is a copy
the only thing a solution can reach, and only there is one made.

**That is not an optimisation.** Generalising where it was not needed costs real proofs,
because the copy is quantified *after* the rule's own binders: a rule variable that would
have been solved to a term mentioning the copy cannot be, since that points backwards, and
the equation is kept instead. Making a copy only where nothing else will do is what keeps
both kinds of case working at once.

**A STATEMENT ABOUT THE THING YOU SPLIT IS REFINED, GOAL AND PREMISES TOGETHER.** The
ordinary dependent statement — *here is a thing, here is a fact about the thing* — splits:

```
data L : Type₀ where { ln : L ; lc : N -> L -> L }
data P : L -> Type₀ where { mkP : forall (l : L) -> P l }

bothWays : forall (l : L) (q : P l) -> P l
bothWays = \ l q -> case l of { ln -> mkP ln ; lc a as -> q }
```

The `ln` arm is asked for `P ln`, not for `P l`, and `q` there is a `P ln`. Both halves
have to move at once: refining the goal alone would leave the arm holding a fact about
`l`, which inside the arm means `ln` and so can no longer be named.

**Unlike an index, the thing you split on is refined everywhere it appears and never
leaves an equation behind** — it is the subject of the elimination, so in each arm it
simply *is* that arm's constructor. The looking-position-by-position rule above is about
indices only; a premise mentioning the subject is always carried.

**BUT A SPLIT GENERALISES WHOLE PREMISES, AND NEVER A PART OF AN INDEX.** This is the one
place where a hand-written eliminator can still state a motive a split cannot, and a proof
that needs it says so in its own statement:

```
-- the induction varies the Δ INSIDE the context, so the context and the
-- equation are arguments — which is the motive, written down
tyRebindAt : forall (G : Ctx) (Xn : String) (A : Ty) (B : Ty) (C : Ctx) (T : Ty)
               (h : ty C T) (D : Ctx) (e : Eq Ctx C (append (bindTy G Xn A) D))
               -> ty (append (bindTy G Xn B) D) T

tyRebind = \ G Xn A B D T h ->
  tyRebindAt G Xn A B (append (bindTy G Xn A) D) T h D
    (refl Ctx (append (bindTy G Xn A) D))
```

`examples/poplmark/03-wellformed.thena` and `06-transitivity.thena` each have exactly one
lemma of that shape, and the wrapper means no caller sees it. **Where the index IS a
variable there is nothing to say**: the split abstracts it, and `examples/progress.thena`
is made of that case.

**AND A PREMISE ABOUT AN INDEX IS CARRIED TOO.** The position-by-position rule decides
whether the *index* gets a copy, which is a question about what a method can be stated at;
whether an *arm* can use a fact you already have is a different question, and the answer is
the same as for the subject:

```
h : forall (a : String) (c : String) -> R a c -> Eq String a c -> R c a
h = \ a c p q -> case q of { refl u -> p }
```

Splitting the equation makes `a` and `c` the same `u`, so `p` is an `R u u` and it is the
answer. Nothing demands a copy of either index — `refl`'s index is its own argument at both
positions — so until MS9 `p` was left standing at `R a c` beside an arm whose subject was
`u`, and the lemma could not be written at all.

**AND THE SCRUTINEE ITSELF IS ONE OF THE NAMES THAT MEANS THE REFINED THING.** Inside an
arm the thing being split *is* the constructor applied to that arm's own variables, so the
name you gave it means that:

```
p19 : forall (U : Ty) (d : D U) -> D U
p19 = \ U d -> case d of { mk V -> d }
```

`d` in the arm is `mk V`, and the proof computes. Writing `mk V` there instead is the same
proof, which is the point: which positions a split refined, and under which names, is
elaboration's business and not something the author should have to spell differently.

**A recursion across such a split is written as an ordinary recursive call, whatever the
split had to generalise** — one index tied or several, a premise introduced before the
subject or after it, a premise the recursion varies or one it does not. The induction
hypothesis is reached by calling the function being defined; nothing in an arm binds one
or names one.

**A RECURSIVE CALL MAY BE WRITTEN INSIDE A SPLIT THAT GENERALISES.** A split that
generalises makes each case prove something *more general* than the goal it came from — the
case is about a fresh copy of the subject — so the hypothesis the case has to use is the
copy of the enclosing arm's, which the split quantified along with everything else whose
type mentions the subject. The recursion check follows that: a call inside such an arm is
tied to the copy, and the copy is an unguarded premise of the method, so no termination
argument is spent.

**AND NOTHING IN THE ARM SAYS A SPLIT GENERALISED.** A name the split refined means the
refined thing, whether the refinement came from a surviving copy or from one an equation
solved outright. Where the case solves the copy of an outside variable — `eIf`'s own `c1`
becomes the copy of `p` — the outside name is bound in the arm as a definition equal to
that term, so the arm is written exactly as it would be if nothing had been copied:

```
; eIf p p' a b sr -> \ u s -> case s of
    { …
    ; eIf c1 c1' c2 c3 sr2 -> cong Term Term (\ x -> ifthen x c2 c3) p' c1' (determinacy p p' sr c1' sr2) }
```

`p` there is the inner case's own subject and `sr` is the copy, refined to `Step p p'`,
which is what makes the call typecheck with nothing transported. The `eSucc` arm, whose
split generalises nothing, is written the same way — and that is the point, because an
author has no way of knowing which of the two they are in.

**AND THAT HOLDS WHERE NOTHING WAS COPIED AT ALL.** An index the scrutinee supplies as a
plain variable that no other premise mentions needs no equation: the motive abstracts it
outright, which already generalises everything that mentions it. Nothing is copied and
nothing is solved there — and the author's name for it still means what the case made of
it:

```
indexIsRefined : forall (m : N) (e : Ev m) -> Eq N m m
indexIsRefined = \ m e -> case e of { evz -> refl N m ; evs n en -> refl N m }
```

`m` is `Ev m`'s index, and one `refl N m` answers both arms because in the first it is `z`
and in the second it is `s (s n)`. The same holds when the index is the constructor's own
argument: splitting a `d : D m` on `mk k` leaves `m` meaning `k`, and `mk m` is the same
term as `mk k`.

**Which positions a split copied, and which copies it solved, is elaboration's business.**
Elaboration is compilation: nobody should write a proof differently because of how it is
compiled. **Agda and Idris show none of it either**, because a clause's whole left-hand
side is one unification problem rather than one scrutinee with everything to its left
fixed.

**A RECURSION MAY ALSO VARY A PREMISE THE SPLIT DID NOT SPLIT ON.** A proof by induction
on one premise may recurse at a different value of another, and nothing has to be said:

```
varies : forall (n : N) (x : A n) (u : N) (f : F n u) -> N
varies = \ n x u f -> induction x of
  { az -> z ; as k p -> case f of { fs j m r -> s (varies k p m r) } }
```

The induction is on `x`, and the call recurses at `m` rather than at `u`. What makes it
work is that the split generalises `u` along with `f`, because `f`'s type mentions it — a
copy is only useful if it is a copy of everything it is about.

**A RECURSION MAY SUPPLY A PREMISE THE SPLIT HAD TO GENERALISE.** Where the statement's own
premises include one the split generalises, the recursive call says what it is at the
smaller subject and nothing else changes:

```
takesPremise : forall (n : N) (x : A n) (e : Eq N n n) -> N
takesPremise = \ n x e -> induction x of
  { az -> z ; as k p -> s (takesPremise k p (refl N k)) }
```

`e` is generalised because its type mentions `n`, the target's index. The recursion is at
`k`, so the premise it needs is `refl N k` and that is what is written. **Passing the arm's
own `e` instead is refused**, and it should be: the split refined `e` to the copy at
`s k`, which is not a premise about `k`.

**AND WHERE YOU INTRODUCE A PREMISE IS NOT PART OF THE PROOF EITHER.** A statement says
what the premises are, not the order a proof takes them in, so `\ n x u f ->` across the top
and a `\ u f ->` inside each arm are the same proof and both load:

```
inside  = \ n x -> induction x of
  { az -> \ u f -> z ; as k p -> \ u f -> case f of { fs j m r -> m } }
outside = \ n x u -> induction x of
  { az -> \ f -> z ; as k p -> \ f -> case f of { fs j m r -> m } }
```

Both are `forall (n : N) (x : A n) (u : N) (f : F n u) -> N`, and in both the inner split
has to generalise the ambient `u` — `fs`'s own `s m` faces it and there is nothing on the
rule's side to move. The second spelling was refused until MS9: the generalisation a nested
split needed was cancelled by what the elaborator had left in scope for the arms before it,
which is nothing a proof can see or plan around.

**And where the family recurses at one index and concludes at another, the recursion is
what asks for the copy — MS9.** No *arm* needs one from

```
data T : N -> Type₀ where
  tv : forall (g : N) -> T g
  tl : forall (g : N) (p : T (s g)) -> T g
```

because `tl` concludes at its own `g`, which the split solves away. But the induction
hypothesis is the motive at the *premise's* index, `s g`, so a proof that varies a premise
across the recursion

```
atTop : forall (g : N) (d : T g) (g1 : N) (inc : Inc g g1) -> N
atTop = \ g d g1 inc -> induction d of
  { tv g0 -> g1
  ; tl g0 p -> atTop (s g0) p (s g1) (mkInc (s g0) (s g1)) }
```

gets a hypothesis constrained against the variable outside the split, which no call can
satisfy. **So the same question is asked of each recursive premise's indices as of the
constructor's conclusion**, and that is the whole rule — it demands nothing extra where
the premise sits at one of the constructor's own arguments, which is why `vtail` over
`Vec` still copies nothing. **Where you introduce a premise does not decide whether your
proof loads**, and that is the property these rules exist to keep.

**An arm can be written to take a leftover equation** — `evs n en -> \ q -> …` — and then
transport by hand. It type-checks, and it is deliberately not how the examples are written:
an arm whose right-hand side is a function of an equation you had no way to predict is
elaboration showing through the surface, not a way to write proofs.
`examples/determinacy-patterns.thena` has no such arm, and no `elim` either.

### The hand-driven induction tactic does not generalise, and the generalising one has its own name

*Decided 2026-10-22, built 2026-10-26.*

The motive above is built by one function, and the surface's `induction … of` is not its
only caller: `eliminate-core ⌜ t ⌝` at the prompt reaches the same construction and hands
you one hole per case to fill in by hand. **A copy is free only where something solves
it.** Elaborating a split runs `specialise` over every method, which solves each copy and
drops its binder, so the arm never sees one. Driving the tactic by hand there is no
specialiser, so every copy is a further argument to every method you write — and every
later widening of *what a split generalises* lands on the proof scripts again.

So there are two tactics, and the plain word is the plain construction:

```
eliminate-core ⌜ t ⌝                -- §3.7: the target and its indices, premises fixed
eliminate-generalising-core ⌜ t ⌝   -- … and a fresh copy of the premises the indices mention
```

**Two rules and not one with a flag.** A rule says only what it is about, and these are
about two motives; a `generalise?` argument would be a mode. Underneath, one function with
one more parameter, exactly as `induction` and `case` are one function with a scheme
parameter — nothing in `Core` or the kernel can tell any of the three results apart.

**The generalising one is reachable by any rule**, not reserved to elaboration, because a
construction that is right for one caller may be right for another; what it is not is the
word a person reaches for first.

**What it costs**: a hand-written method cannot refine a variable bound outside its split
unless it asks for the generalising tactic. That is the behaviour the tactic path had
before the generalising motive existed, and it is the right default — the surface language
is where refinement is meant to come from for free.

### The split has a spelling you type, and it hands you one goal per case

*Decided and built 2026-10-28.*

`eliminate-core` gives you the eliminator's methods, equations and all. **The split is a
different thing and now has its own words**:

```
induction-core core`t`    -- one hole per case, inside that case's own binders
case-core core`t`         -- the same, without the induction hypotheses
```

They run what the surface language runs — the generalising motive, then `specialise` over
every method — and then, instead of elaborating an arm, they leave the method open. So
each case's hole is already under that case's binders, the equations the split stated are
already discharged, and what you write is the body of the arm:

```
thena spine> induction-core core`n`
subgoals: zeroMethod, succMethod
subgoals: zeroCase
subgoals: succCase
thena spine> goto-named "succCase1"
thena spine> :where
…
context
  n : Nat
  u : Nat
  ih : Eq {0} Nat (plus u zero) u
  n1 = succ u : Nat
type
  Eq {0} Nat (plus (succ u) zero) (succ u)
```

Three things follow from it being the same mechanism. **A name bound outside the split
means what the split refined it to**, so `n` is a definition — `succ u` — inside the step
case. **A forced constructor argument is a definition too** rather than a binder, which is
the same rule an arm gets. And **a case the split proves impossible is never posted**: its
method is closed on the way past, so you are shown what is left to do and nothing else.

**Where a constructor names its arguments, those are the names you get.** Where it does
not — `succ : Nat -> Nat` writes a bare arrow — a name is minted, `u` for an argument and
`ih` for the hypothesis about it, because a goal binding `_` is not usable. The written
path never needed this: an arm names the arguments itself, and a recursive call finds its
hypothesis without naming it.

**What is still hand work** is navigation: each case is reached with `goto-named`, and the
plumbing between a filled case and the finished proof is solved by hand. Focusing the next
goal by itself is a separate thing and is not built.

### `case` says the arm does not recurse, and the type is what says it

```
predC : Nat -> Nat
predC = \ n -> case n of { zero -> zero ; succ m -> m }

double : Nat -> Nat
double = \ n -> induction n of { zero -> zero ; succ m -> succ (succ (double m)) }
```

Two words, one mechanism. `induction t of { … }` elaborates to the datatype's
eliminator, whose every method is handed one inductive hypothesis per recursive
argument. `case t of { … }` elaborates to the generated `caseNat` — the same
eliminator with those hypotheses dropped — so a `case` arm has nothing to recurse
with:

```
dblC = \ n -> case n of { zero -> zero ; succ m -> succ (succ (dblC m)) }
  no induction hypothesis is about this call, so it is not structurally smaller: dblC m
```

**Nothing checks for that.** There is no rule anywhere that says a `case` arm may
not recurse. The hypothesis is simply not in scope, so the call has nothing to tie
to and is refused by the same mechanism that refuses a call at the wrong index
under `induction`. Writing `case` is therefore a claim the type carries, not a
comment: `examples/canonical.thena` is all `case`, because inversion never
recurses, and `examples/progress.thena` has exactly one `induction` in it.

**Everything else about the two is identical.** The same motive generalising the
indices, the same equations recovering their specificity, the same forced
positions, the same vanished cases. `case` over an indexed family forces a
constructor argument exactly as `induction` does:

```
vtailC : ∀ (A : Type₀) (n : Nat) -> Vec A (succ n) -> Vec A n
vtailC = \ A n v -> case v of { vcons k a as -> as }
```

**And the kernel cannot tell them apart**, which is the point of doing it this
way. `caseNat` is an ordinary definition whose body is an `elim Nat` with a λ
discarding each hypothesis, so it δ-unfolds to the elimination and is checked as
one. Nothing was added to the core language, and a proof written either way is the
same term up to unfolding.

### Writing no arms is the claim that every case is impossible

```
trueNotNat : forall (d : HasType true nat) -> Empty
trueNotNat = \ d -> induction d of { }
```

`HasType` has seven constructors, and none of them can have built this derivation:
every one disagrees with `true` or with `nat`. So the split has nothing to answer,
and writing no arms is how you say that. Each method is closed by its own
conflicting equation and the proof is complete.

**It is not a second form of split.** The same walk runs over the same methods,
and the only thing the empty brace changes is that *every* method is now required
to vanish. A datatype with no constructors — `case e of { }` at `e : Empty` —
satisfies that by having no methods at all, which is how the two cases turned out
to be one. A method that survives is refused by name:

```
oops = \ t n -> induction n of { }
  no clause of case-must-vanish applies here      -- nvZero did not vanish
```

**`induction` and `case` mean the same thing here, and that is a consequence
rather than a convenience.** The two words differ by whether a method carries
inductive hypotheses; with no method surviving there is nothing for a hypothesis
to be attached to, so there is nothing left for them to differ about.

**One consequence worth knowing, and it is about universes rather than splitting.**
A declaration's statement is level-polymorphic in any level it does not pin, and
`Empty` is a family with a level. The seven-method proof pinned level 0 along the
way, because it passed `Empty` to `absurd`, whose argument is declared at `Type₀`.
The arm-less proof names nothing, so the lemma you get is the more general one:

```
trueNotNat {ℓ} : HasType true nat -> Empty {ℓ}
```

Both readings are lemmas you can use, and `trueNotNat {0}` is the old one. **Writing
a shorter proof of the same signature can therefore give you a more general global**
— worth knowing, and not a thing to work around.

### The same lesson, one level on: a search must not be a choice point over the work

`induction t of { … }` elaborates by walking a datatype's constructors against
the method holes an elimination claimed, and for each one finding the arm the
user wrote for it. The obvious shape is one rule that matches the constructor's
name *and* elaborates that arm's body.

**That shape loses every error the body produces.** With one name test and an
ordering, both clauses of the search match whenever the names agree, so the
engine keeps the other as an alternative; a body that then fails to elaborate
backtracks into the search, which walks on through the remaining arms, runs out,
and reports *itself*. A recursive call with nothing to resolve to, a pattern of
the wrong arity and a missing arm all came back as the same sentence about the
search.

**So the search answers with the arm and does nothing else, and its two clauses
are made mutually exclusive by a pair of complementary tests** — `same-name` and
`different-name`, the way `let`'s annotated and bare clauses are two positive
tests rather than a negation. The caller elaborates, and the caller's failure is
its own. Each of those three now says what actually happened.

**This is why the head language still has no negation and does not need one.**
Every exclusive pair so far has been writable as two positive tests, and each
time that has also removed a choice point the user would otherwise have been
offered.

**A rule body may be empty**, which it could not before. `E⟦_⟧` is *do nothing*:
the hole is already there and unification is expected to find it. A clause that
does nothing and a clause that does not match are different answers, so the
empty body is saying something. `do` is still required.

**A rule loops by recursing over the surface term.** The λ case needs one
`prim-lambda` per binder of a group, and a rule body is a straight run of
instructions with no iteration — so a helper peels one binder and calls itself
on the tail, and the term is its own counter:

```
rule intro-binders t k :- when focus-is-guess (lambda-binds-more t) (lambda-is-bare t)
  do x  = lambda-name t
     ; k2 = prim-lambda x
     ; tl = lambda-tail t
     ; body = call intro-binders tl k2
     ; return body

rule intro-binders t k :- when focus-is-guess (lambda-binds-one t) (lambda-is-bare t)
  do x = lambda-name t
     ; k2 = prim-lambda x
     ; return k2
```

**It returns the hole it ended at, and the caller `goto`es that** rather than
counting its way back down — `prim-lambda` and `prim-let` produce the hole they
claim for what is left of the goal. Counting moves was what the deleted
`enter-binders` did, and it is only right while the binders are the sole
components in the chain: a λ whose binder carries a written type claims a hole
*inside* them, and the count is then off by one per annotation. That is why
there are two further clauses for an annotated binder.

**Peeling in the elaborate clause itself would not do**, because attacking once
per binder nests the λs and wraps each in its own `let` — a different proof
term. The run has to be emitted, and recursion is what emits it.

**Every clause is written in the rule base** (49b added `∀`, `->`, `let` — two clauses, since
the annotation is optional and a head cannot say *not* — the ascription and `do`;
49c added the λ). The two that still ran a `prim-elaborate` were an application,
which matches its arguments against the head's plicities, and an `elim`, which
claims a hole per field: both hand a **list of names** to a single op, which
recursion cannot build. **Since 49f there is no `prim-elaborate` and no Haskell
elaborator behind any of it** — `rules/standard.thena.rules` is the whole of
E⟦·⟧, in nineteen clauses.

A clause takes its surface term apart with **moves**, which answer with a
surface term focused on the part rather than a detached one:

```
rule elaborate t :- when focus-is-hole (surface-is-arrow t)
  do … ; a = arrow-domain t ; call elaborate a
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
  do w = surface-name t
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

**The trust-bearing definitions are surface definitions too, since 2026-10-14.**
`transport`, `isSame` and the six laws the three `dec` functions rest on were
written in the development calculus for eight days, because a surface
`trusted T e` leaves the type its body really has to a hole and that hole could
not be solved under a λ — which is where every one of those claims sits. That was
a defect in unification, not a limit of the surface language, and with it fixed
the file a reader opens to see what the system takes on trust is written in the
language they write their own proofs in.

**Their types are ascribed, and here is why.** A surface type cannot say which level a datatype
application sits at, and it does not need to except when nothing else decides it.
A brace in a surface term means an implicit *value* argument, and elaboration
places it against the head's recorded argument positions (`plicitiesOf`,
`Engine.hs`); a datatype's level is not an argument position — it lives in
`Global`'s own level list — so `Eq {0} String a b` is refused with *"an implicit
argument this head has no position for"*. The level is inferred instead, and what a
declaration leaves undecided becomes a level **parameter** of the declared name.
**Here it is undecided**: `String`, `Char` and `Int` sit at a fixed `Type₀`, and
cumulativity then asks only that `Eq`'s level be at least 0, so each occurrence
would get a parameter of its own. Writing `A : Type` instead would have tied them
together — but these laws are about primitive literals, not a parameter. Ascribing
the whole type decides it. Ascribing the type
pins it:

```
eqStringEqual : ∀ (a : String) (b : String)
  -> (Eq Comparison (eqString a b) same : Type₀) -> (Eq String a b : Type₀)
```

and the stored type is exactly what the development calculus wrote,
`-> Eq {0} Comparison (eqString a b) same -> Eq {0} String a b`, with no
ascription left in it. **A body needs no such thing**: a level argument in a term
is inserted at the use.

**`define-global`, the op that hands a finished definition out from a rule base,
stays** — his ruling the same day. It is `declare-primitive`'s sibling and is
what `examples/10-preservation-any-context.thena` uses; it is simply no longer
the only way to write a definition that rests on trust.

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
rule elaborate t :- when focus-is-hole (surface-is-name t) do …
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

**A call to a name nothing defines is refused when the bases load** (*decided
2026-09-15*). The bases you load together are the program — in any order, and a
rule may call one written below it — and a call to a name none of them defines,
or to a name at an arity it does not have, is a type error:

```
rule go :- do helper 1 2
rule helper x :- do prim-prove
```
```
the rules do not type check:
  go, instruction 1: helper takes 1 argument, not 2 arguments
```

So a rule file that uses the shipped tactics is loaded together with the shipped
base: `:load rules standard.thena.rules mine.thena.rules`.

**A rule is inferred at one type**, not generalised: a helper used at `Surface`
in one place and `Core` in another is an error, not a polymorphic rule.
*Superseded 2026-09-13 — see "A rule or function used at two types is inferred,
not refused".*

### A rule file may declare functions, and they need no keyword

*Decided 2026-09-12.*

A function is written the way Haskell writes one, beside the rules in the same
file:

```
twice x = concat x x

shout : String -> String
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

*Superseded 2026-09-21 (MS6 phase 106): the rule-file `language` declaration,
the type it gave, and `surface-of` are deleted, and `language` in a rule file
is now a syntax error. A language is declared in a module and its terms are
`Core` values — see "A language block declares a datatype, and its terms are
ordinary terms" and "An object term is written the same way in a rule". A
language may still not take a built-in tag's name.*

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
asSurface : Tm -> Surface
asSurface t = surface-of t

rule go :- do t = Tm`(x y)` ; s = asSurface t ; …
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

### There are three name spaces, and a name may be reused across them

*Decided 2026-09-16.*

A name you write is read in one of three places, and Thena keeps a separate
space for each. **Within a space a name means one thing; across spaces the same
word is free to mean three.**

| space | what is in it | who may add to it |
|---|---|---|
| **types** | `String` `Name` `Int` `Char` `Bool` `Surface` `Core` `Development` `Level` `List` `Option` | nothing — the set is closed |
| **tags** | `surface` `core` | a `language` block in a module |
| **callables** | op words, rule names, function names, locals | a rule, a function, a binding |

So these load together, and the two `twice`es never meet — one is only ever
written as a tag, the other only ever called:

```
language twice, M where          -- in a module
  one -> 1

twice : String -> String         -- in a rule file
twice s = concat s s
```

**A language's name is checked against the built-in tags**, because a rule file
reads an installed language's tag before its own:

```
refused: core is one of Thena's own tags, so a language may not take its name
```

*Updated 2026-09-21 (MS6 phase 106): until then a rule-file `language`
declaration also entered the type space, and was checked against the type
list too.*

Inside a space, a collision is refused. Two languages under one name, and:

```
ns.thena.rules: in twice: this name is both a rule and a function at 1 argument
```

**The callable space is shared on purpose and is the subtle one**, because it
holds four kinds of thing. The rules that sort them out are elsewhere in this
document: an op word at another arity calls a rule of that name, a local shadows
a rule, and a bare word right of an `=` is the local it names.

**Reserved words are in no space.** The eleven (`forall let in elim where data
module do rule language when`) are taken from every language at once, because
one lexer serves them all.

### `instral` has lambdas, and a local shadows a rule

*Decided 2026-09-12.*

```
onTwice : (String -> String) -> String -> String
onTwice f x = f (f x)

rule go :- do d = \ s -> concat s s
     ; m = onTwice d "a"                 -- aaaa
     ; say m
```

A lambda is a function without a name — it is compiled the same way and applied
the same way. **In an argument it takes parentheses**, like every other compound
argument: `once (\ s -> concat s s)`.

**A function type is n-ary, not curried.** `a -> b -> c` is a function of *two*
arguments; applying a one-argument lambda to two is a type error, because
`instral` dispatches on arity. Parentheses are what make an arrow a value: in
`f : (a -> b) -> a -> b` the first argument is a function.

**That holds in the result too**, so a function that gives a function says so:

```
mk : String -> (String -> String)   -- one argument, gives a function
mk s = \ z -> concat s z

two : String -> String -> String    -- two arguments
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
rule f :- do say "hi"
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

**It needs no keyword** *(decided 2026-09-13)*. A declaration that begins with a
plain word is a signature or a function, and the token after the name says
which — `:` for a signature, a parameter or `=` for a function:

```
shout : String -> String      -- a signature
shout s = concat s "!"        -- the function it describes
```

`signature` was a keyword until then, and because one lexer serves every
language it was unusable as a name in Surface, Core and every object language
too. It is an ordinary identifier again.

```
spine-arguments : Core -> Core -> Surface -> ()
rule spine-arguments h f t :- when focus-is-component (surface-is-app t) do …
rule spine-arguments h f t :- when focus-is-component (surface-is-name t) do …
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
rule ignore x :- do say "ignored"
rule usesName :- do n = fresh-name "h" ; ignore n     -- a Name
rule usesTerm :- do h = here ; ignore h               -- a Core
```

Adding `ignore : a -> ()` makes both uses fine, because each use gets
its own copy of the type.

*Superseded 2026-09-13: that example now loads with no signature — see "A rule
or function used at two types is inferred, not refused". A signature is still
checked, as below.*

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

### `goto-root` goes to the top, and it is the one move that cannot fail

*Decided 2026-09-27. Adds a word.*

The third member of the family. `goto` and `goto-named` both search **from the
root**; `goto-root` takes nothing and stops there.

```
goto-root             -- wherever you were, you are now at the top
back                  -- refuses at the root: there is nothing above it
```

Every other move can say no — `into` wants a guess, `along` wants somewhere to
go, `back` answers `AtRoot`. `goto-root` is already where it is going, so it
always succeeds, including when you are at the root already.

**It is also what a click is made of.** An editor names a position by the moves
that reach it from the root, so a click compiles to `goto-root` and then those
moves — an ordinary program you could have typed, snapshotted and undoable like
any line. Clicking the top of a development is `goto-root` on its own.

### Every datatype generates `caseD` as well as `elimD`

*Decided 2026-10-18.*

`elimD` is induction: every method is handed one inductive hypothesis per
recursive argument, whether it wants one or not. Analysing the cases of a term
and *not* recursing on it is the other thing you do with a datatype, and through
`elimD` you cannot ask for it — you bind the hypothesis and ignore it at every
method. So a second definition is generated, the same scheme with those binders
dropped:

```
thena spine> :elim Nat
elim Nat : ∀ (P : Nat -> Type₀) -> P zero -> (∀ (x : Nat) -> P x -> P (succ x)) -> ∀ (target : Nat) -> P target
thena spine> :show caseNat
caseNat {ℓ} : ∀ (P : Nat -> Type ℓ) -> P zero -> (∀ (x : Nat) -> P (succ x)) -> ∀ (target : Nat) -> P target
caseNat = λ P method method1 target -> elim Nat () P (method (λ x ih -> method1 x)) () target
```

So `pred` is `caseNat (λ t -> Nat) zero (λ m -> m)`, and the method for `succ`
takes the predecessor and nothing else.

**It is a definition and not a new kind of term.** Its body is an `elim D` whose
methods are its own under a λ per hypothesis, so `caseD` δ-unfolds to an
ordinary elimination, reduces like one and is checked like one. Nothing in the
kernel can tell a case analysis from an induction, and `caseNat` and `elimNat`
with the hypotheses ignored are the same term.

**Its name is one more the declaration takes.** Generated names share your
namespace, so declaring `Nat` when something called `caseNat` already exists is
refused, exactly as it is for `elimNat` and for `noConfusionNat`.

---

### `specialise` discharges the equations an elimination hands you, and keeps the ones it cannot

*Decided 2026-10-18.*

Eliminating a family at specific indices gives you one method per constructor
with the equations that recover those indices attached. Splitting `v : Vec A (succ n)`
to prove `Vec A n` hands over

```
nilMethod  : Eq {0} Nat zero (succ n) -> Vec A n
consMethod : ∀ (n1 : Nat) -> A -> Vec A n1
           -> (Eq {0} Nat n1 (succ n) -> Vec A n)
           -> Eq {0} Nat (succ n1) (succ n) -> Vec A n
```

and until now you discharged each one by hand, with a generated `noConfusion`
and an `Empty` elimination for the branches that cannot occur and a transport
for the ones that can. `specialise ‹constructor› ‹equations›` does it instead.
At `nilMethod` it leaves **no subgoal at all** — `zero` against `succ n` cannot
hold — and at `consMethod` it leaves

```
A -> Vec A n -> (Eq {0} Nat n (succ n) -> Vec A n) -> Vec A n
```

The binder `n1` is gone, because the equation determined it, and the vector is
at `n` rather than at `n1` — which is exactly the coercion you were writing.

**It is one instruction and not four**, for the same reason `prim-eliminate` is
one: everything it does is term construction over a declaration, and a granular
version would need a term-building sub-vocabulary that nothing else has asked
for. What is *not* inside it is the choice of what to split, which is an
ordinary rule — a wrong choice is a failed elaboration, while a wrong proof term
would be a lie, and the second is the one the kernel has to be the judge of. So
everything `specialise` builds is checked against the method it claims to prove
before you are given it.

**There are five transitions, and the fifth is what recognises a case you were
right to leave out.** An equation of a term with itself goes; two different
constructors close the method; the same constructor splits into its arguments; a
binder the equation determines is substituted away; and — since 2026-10-27 — an
equation between a term and something that *contains it structurally*, `Eq Nat m
(succ m)`, closes the method too. Nothing inhabits such an equation, so the case
it belongs to cannot arise.

**So a correctly omitted case is accepted, and nothing is said about it.** `case`
with empty braces, or an arm with no body, is how you write that the case cannot
happen; before this, the equation survived, the method stayed open and the
omission was refused. The proof is the generated acyclicity equipment above:
`noCycleD` says the equation puts one side structurally below the other, the
tuple it answers with holds `x ≢ x`, and reflexivity makes that an `Empty`. For

```
data Step : N -> N -> Type₀ where
  down : ∀ (n : N) -> Step (s n) n

noSelf : ∀ (n : N) (st : Step n n) -> Empty
noSelf = \ n st -> case st of { }
```

the tied target asks for a number that is its own successor, and the braces are
empty. `examples/omitted-cases.thena` is the same thing at four shapes. **A case
that does arise is still refused**, by name, as it always was.

**An equation it cannot simplify is kept, not refused.** When none of the five
applies, the equation stays a hypothesis of the simplified method — that is what
you were handed before, so the worst case is the behaviour this replaces.

**`prim-eliminate` now answers with a number**: how many equations each of its
methods carries. A method type is Π binders all the way down and does not say
which of them are the equations, so `specialise` has to be told — and the
elimination that stated them is the only thing that knows.

---

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

### A load can warn, and a warning changes nothing

*Decided 2026-09-18.*

`:load` used to either install everything or refuse everything. It can now also
**succeed and say something**:

```
thena spine> :load proof examples/stlc.thena
module STLC
  declared Ty
  ...
warning: in the grammar of LC, production vacuous: x binds in nothing
```

Everything named as declared **is** declared — a warning is a remark about a
declaration that went in, never a half-refusal. The warnings come after the
list, in the order the file caused them, and each names what it is about rather
than a line number.

This is why it exists: a warning survives where a message does not. Loading a
file discards the running commentary (elaborating one declaration prints a
dozen level solutions), and before this the one thing worth warning about —
equipment a declaration did not get — was shown at the prompt and lost in a
file.

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

### Every `do` block is checked before it runs, and a top-level one is its own scope

*Decided 2026-09-15.*

A `do` block is validated and type checked before any of it runs, wherever it is
written — inside a surface term, at the prompt, or at the top of a module. A
mistake is refused and nothing it would have done happens:

```
thena spine> do { prim-try 3 }
instruction 1: wanted Core, got Int
```

**Each `do` block is its own scope, and what it sees from the module is the
globals declared above it.** A name bound in one block is not in scope in the
next, and a declaration further down does not exist yet:

```
module M where

do
  x = "one"

do
  say x          -- refused: no parameter or earlier binding is called x
```

```
module M where

data Nat : Type₀ where
  zero : Nat

do
  t = resolve-core core`one`     -- stuck: not in scope: one

one : Nat
one = zero
```

The local half is refused when the file loads. The global half is refused when
the block runs, because a written core term is resolved at run time — so the
declarations above the block have already been made by then.

**That timing is a current limit, not the intent.** A core term's names are
resolved against the development as it stands when the instruction runs — Γ at
the focus, then the globals — and a name may be a hypothesis the proof binds
before that instruction, so the check cannot simply be moved as things are. The direction is to check tagged term literals when the file loads,
which may mean reworking how they are treated; it is not scheduled.

**While a rule is yielding, a block you type sees the rule's locals**, and they
have the types their values have — so `do { goto h }` reads the rule's `h`, and
`do { say h }` is refused when `h` holds a term.

### Levels: `instral` holds one, but has no level arithmetic

*Decided 2026-09-14, confirmed as intentional 2026-09-15.*

A rule can make a level and build a universe at it, and nothing more:

```
l = level 2            -- a closed level, exactly what Type₂ writes
m = fresh-level        -- a fresh unknown, what a bare Type writes
u = universe-at l      -- the term Type₂
```

There is no `level-suc` and no `level-max`. The level **algebra** — successor and
join — is built only by the level solver, whose normal form and satisfiability
check are written against a single source of level expressions. A rule that could
write `level-max a b` would be a second source. It can be added the day something
needs it.

### A lambda takes at least one parameter, and a function is not curried

*Decided 2026-09-15.*

`\ -> e` does not parse. A value needs no lambda — `x = e` names it and `r = x`
uses it — and calling a local with no arguments is refused:

```
rule go :- do d = "text" ; call d
```
```
go, instruction 2: d holds a value, not something to call with no arguments — write r = d to use it
```

**Functions are not curried.** A function's type is n-ary: `join a b = concat a b`
takes exactly two arguments, and `join "x"` is refused with *join takes 2
arguments, not 1 argument*. A function that returns a function says so, with
parentheses: `adder : String -> (String -> String)` and `adder a = \ b -> concat a
b`, after which `p = adder "x" ; m = p "y"` works.

### An instruction number is the line you wrote, counted from 1

*Decided 2026-09-15.*

Every message about a rule body names the statement as written, whichever check
found the mistake. A nested call does not add a line, and a type annotation is a
line of its own:

```
rule go :-
  do k : String
     k = "x"
     prim-try k      -- go, instruction 3: wanted Core, got String
```

A mistake inside a lambda names the line the lambda is on.

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

### `instral` has lists, pairs and options, and you take them apart with patterns

*Decided 2026-09-12; **rewritten 2026-09-14**, when patterns replaced the nine
words this section used to teach.*

```
rule join [] :- do return ""
rule join [c, ...t] :- do r = join t ; s = concat c r ; return s
```

`[a, b, c]` is a list and `(a, b)` is a pair; an option is `some x` or `none`.
The elements are ordinary operands, so `[x, "c"]` reads `x` where the list is
built.

**There is no `if` and no `case`, and none is needed**: a clause's parameters are
patterns, so a function over a list is two clauses, one per shape — and each one
names the pieces while it tests for them.

**A pattern also stands on the left of a binding**, which is how you take a pair
or an option apart in the middle of a body:

```
(a, b)   = p
(some v) = o
```

**A refutable pattern that does not match is a failure.** In a rule that means
the search tries the next clause; in a function it is the caller's failure, as
in Haskell.

**Nine words went when patterns arrived** and none of them has a replacement in
the language, because the language no longer needs one: `list-head`,
`list-tail`, `pair-first`, `pair-second` and `option-value` were ops, and
`list-is-empty`, `list-is-cons`, `option-is-some` and `option-is-none` were head
tests. Write the pattern instead.

**The one thing a pattern does not give you is a total head.** `list-head` used
to answer an *option*, so the empty list needed no separate answer; a pattern is
partial. Two clauses say it:

```
head' []        = none
head' [a, ..._] = some a
```

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
rule twice t :- do s = concat t t ; return s
rule shout t :- do m = twice (twice t) ; say m
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

**A mistyped word is still caught when a rule base loads.** `prim-solve x` is a
call to a rule called `prim-solve` that takes one argument, and if no loaded base
has one it is refused, saying the op takes none (*since 2026-09-15; before that
it failed only when it ran*).

### A rule file lays out, exactly like Haskell

*Decided 2026-09-13.*

A rule file is one layout block and a rule body is a block that `do` opens, so
a body can be written as indented lines with no separators at all:

```
rule demo :- when focus-is-hole do
  m = shout "hi"
  say m
```

**Every older spelling still works** — one line, explicit braces, and the
leading-`;` style the shipped base is written in:

```
rule fill t :- when focus-is-hole
  do n = fresh-name "refined"
     ; x = define n t
```

That last one is why **a line beginning with `;` is a continuation whatever its
column**: the separator is already written, so there is nothing for the offside
rule to insert and nothing to close.

**Declarations line up with the first one.** The file's block takes its column
from the first declaration, as a Haskell block takes its column from its first
token, so a declaration that does not line up is a syntax error in either
direction. A file indented as a whole is consistent and therefore fine.

### A function body may be a `do` block

*Decided 2026-09-13.*

`f x = e` is one expression. For locals, write a block:

```
shout : String -> String
shout s = do
  wrapped = concat "<" s
  closed  = concat wrapped ">"
  return closed
```

The block *is* the function's body, so it says `return` itself — and the short
form is that block with the `return` written for you. A lambda's body takes the
same two shapes. A block that never returns is refused, as `f x = say "hi"`
already was.

**`do` and not `=`.** Making `=` open a block would reach into the surface
language's `let x = e` bindings, which are the same token in the same lexer;
Haskell does not make `=` a layout keyword either.

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

### A rule or function used at two types is inferred, not refused

*Decided 2026-09-13.*

Callables are split by the call graph and each group is generalised before
anything that calls it is checked — Hindley-Milner. So a helper used at two
types is fine with no annotation:

```
idf x = do { return x }

rule go :- do h = here ; a = idf h ; n = fresh-name "x" ; b = idf n
```

**A local is not generalised.** The same shape one level in is refused:

```
rule go :- do
  g = \ z -> do { return z }
  h = here ; a = g h
  n = fresh-name "x" ; b = g n     -- wanted Core, got Name
```

That is *Let Should Not Be Generalised*, and it is what an annotation is for —
see below.

**Inside one group nothing is generalised either.** Two mutually recursive
callables share their variables, so calling one at two types *from inside the
group* is an error. From outside, the group is a scheme and each use is
independent.

**An annotation is documentation and a promise now, not the only way to a second
type.**

### A local may be annotated, and then it is polymorphic

*Decided 2026-09-13.*

`‹name› : ‹type›` on a line of its own, above the binding it is about — the same
spelling a top-level signature uses, one level in:

```
rule go :- do
  g : a -> a
  g = \ z -> do { return z }
  h = here ; a = g h
  n = fresh-name "x" ; b = g n       -- fine, because g is a scheme
```

**An annotation is checked, not believed.** A body that pins one of the
annotation's variables to a particular type has broken the promise, and the
*annotation* is what is reported. A concrete annotation is an ordinary
constraint and has to be true.

**An annotation with no binding after it is refused** — it is a typo, most often
a name changed on one line and not the other.

### A written core term may have holes

*Decided 2026-09-13.*

A term written in a rule can splice in values that are already terms:

```
d  = claim dn u1
c  = claim cn u2
ar = resolve-core core`${d} -> ${c}`
```

**A splice stands where a term stands.** So the template is parsed once, when
the file loads — what each hole wants is known from where it sits, and a splice
that is not a term, or that names nothing, is refused then. The values are
filled in when the instruction runs, which is when they exist.

Both core spellings take one: `` core`${d} -> ${c}` `` and `⌜ ${d} -> ${c} ⌝`.

**A splice is closed**, so a binder above it does not capture it — the same
weakening every term built under a binder gets.

**This is not string substitution**, and it could not be: the terms a rule
builds carry unsolved level metas, and `Type (suc ?ℓ683)` is not something you
can write down and read back.

### A failing command never backtracks past the line you typed

*Decided 2026-09-16.*

A command that fails unwinds the machine's stack looking for an alternative —
that is what makes a tactic a search. **It stops at the line you typed.** A
choice point an earlier line left is not reached implicitly:

```
thena spine> prove
chose 685: attack
thena spine> regret                 -- take the guess back off
thena spine> back                   -- at the root: nothing to pop
stuck: already at the root
  undoing that would backtrack to 685, which was chosen before this line — retry 685 to take it
```

Before this, `back` would have taken `prove`'s untried alternatives and put the
guess back — **undoing the `regret` you had just typed, with a navigation
command.**

**Nothing is forbidden.** `retry 685` still takes it, and `:choices` still lists
it. What changed is that crossing a line boundary is now something you ask for.

**Why.** Backtracking past the running line takes a route on which that line was
never typed — the command that caused the backtracking could not have been
given. Nothing replays a prompt, so the command is lost either way; making it
explicit costs nothing and shows you what happened.

**A choice point *this* line made is reached exactly as before.** A rule driving
its own search is untouched, and so is `retry`, which lowers the boundary to the
choice point you named — so an alternative that fails on its own still falls
through to the next one inside that command.

**The same rule applies while a rule has yielded to you**, and that is the case
worth understanding, because it is the one that bites hardest:

```
rule pause :- do prove ; yield "over to you" ; say "rule resumed"
```

`prove` leaves a choice point, then the rule hands you the prompt. If a command
you type there fell past that choice point, **control would be taken back from
you** — the rest of your line discarded, your bindings replaced, and the rule
re-entered on another alternative. And because the choice point was made *inside*
the rule, what it re-runs is the rest of that body — **so the rule yields again,
printing a message identical to the one you are looking at.** You would be in a
different context with nothing on screen to say so.

There is one REPL and one rule for it. Working at the prompt means the same thing
whether or not a rule is waiting on you.

### `apply` saturates; `fit` searches for the arity

*Decided 2026-09-16.*

`apply-core` reads the head's whole telescope and claims a hole for every
argument at once. **`fit-core` does not know the arity and does not ask** — it
tries the spine as it stands, and if that does not fit the goal it claims one
more argument and tries again.

```
thena spine> :theorem t2 : P                  -- mk : Nat -> Nat -> P
thena spine> fit-core ⌜ mk ⌝
chose 34: fit-core
backtracking to 34: fit-core
chose 39: fit-core
backtracking to 39: fit-core
chose 43: fit-core
already equal
```

Each `backtracking to` line is an arity being given up. **It stops at the first
one that fits**, so a head whose result type already matches is applied to
nothing at all:

```
thena spine> :theorem t0 : Nat -> Nat
thena spine> fit-core ⌜ succ ⌝                -- fits as it stands
thena spine> apply-core ⌜ succ ⌝              -- saturates, lands on Nat
stuck: Nat and Nat -> Nat cannot be made equal
```

**It is two clauses of a rule and nothing else** — no loop, no new operation:

```
rule fit-core f :- when focus-is-hole
  do fill f ; solve

rule fit-core f :- when focus-is-hole
  do n = fresh-name "a" ; f2 = apply-next f n ; call fit-core f2
```

Nothing sequences them. Both heads pass, so the engine builds a choice point,
and the first clause *failing* is what reaches the second. `:choices` shows the
choice point afterwards, and `retry` pushes the search to a longer spine.

### A rule is searched; a function is called

*Decided 2026-09-13.*

A rule may have many clauses and calling it is a **search**: the engine builds a
choice point, tries each clause whose head passes, and backtracks into the rest
if one fails. `:choices` lists it and `retry` reaches it.

A function is not that. It is **called** — one clause, entered and stayed in.
Nothing about it appears in `:choices`, `retry` cannot reach it, and a failure
inside it is the caller's failure rather than a reason to try something else.

**So a function has one clause per arity**, and a second is refused:

```
f x = concat x "a"
f x = concat x "b"     -- in f: a function has one clause, and nothing tells a
                       -- second one at 1 argument apart from the first
```

Different arities are different functions, as they are for rules. Until there
are patterns nothing can tell two clauses apart, so the second could only ever
be reached by the first one *failing* — which is a rule's behaviour, and writing
a rule is how you ask for it.

### A `do` block in a surface term is checked before any of it runs

*Decided 2026-09-13.*

A `do` block written inside a surface term **is the solution to the hole it
stands in** — `E⟦do { … }⟧` is *play the block*, and what it leaves behind is
the term it built. So it sits wherever a term does, including the right of a
`let`:

```
let x : Type₀ = do { u = fresh-universe ; fill u ; solve } in x
```

It has no type of its own to declare, and **a `return` in one is refused**:
there is nothing for a value to be returned to.

Its instructions are resolved, validated and type-checked when the term is
read — in a rule file, at the prompt, in a module, in a `declare`. A mistake in
one is reported before anything is elaborated, so nothing is half-built:

```
thena spine> elaborate ⟨ do { say 3 } ⟩
do block 1, instruction 1: wanted String, got Int
```

### A `:load` that fails declares nothing

*Decided 2026-09-30.*

```
thena spine> :load mine.thena
stuck: Beta and Alpha cannot be made equal
thena spine> :show Alpha
nothing named Alpha has been declared
```

A module is loaded **all or nothing**. If the run stops for any reason — a type error, a
block that does not check, an unanswered question — the session is put back exactly as it
was, and nothing the module had already declared survives.

**Before this, the declarations above the failure stayed**, `:undo` could not take them
back, and loading the corrected file then failed on the names that had landed. One typo
cost you the session.

**What a completed load leaves is unchanged.** A module that finishes is loaded whatever
it left in the development, which is what the REPL is for; the rule is about a run that
*stops*, not about an unfinished proof.

**One thing does not go back: the fresh-name counter.** A failed load has already shown
you names, and a name you have seen is never reissued.

### A renamed binder is a name your language can write

*Decided 2026-10-01.*

```
language L, M, N, E where
  var : n as occurrence -> n      -- n = /[a-z]+/, no prime in the class
  abs : n as binder     -> ( lam n . E[n] )
```

Substituting under a binder renames it to avoid capture, and the new name is **built from
your identifier class**, so it is always a name the notation can print and read back:
`/[a-z]+/` renames `y` to `ya`, while a class that admits `'` renames to `y'` as before.

The character is decided on the class's own automaton — it must extend *every* string the
class accepts — so this is by construction rather than by convention, and nothing in it
knows about any particular character.

**A class no single character extends** — `/[a-z][0-9]/`, where nothing may follow `a1` —
is **not refused**. It loads with a warning saying that a renamed binder will not print in
that notation. Substitution is unaffected; only printing the renamed name back is lost.

### A multi-line entry is bracketed by `:{` and `:}`

*Decided 2026-09-13.*

At the prompt, one line is one entry. To type several, open with `:{` and close
with `:}`, each alone on its line:

```
thena spine> :{
         ... h = here
         ... claim "k" ⌜ Type₀ ⌝
         ... goto h
         ... :}
```

The lines between are laid out the way a rule file is, so they need no `;`. It
is GHCi's spelling, and it is the only place the REPL asks for anything
unusual — there is no rule about what a continuation must look like, because
the brackets say where the entry ends.

**A trailing `;` is a complete entry**, not a request for more.

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

### Patterns — in a parameter, and on the left of a binding

*Decided 2026-09-14.*

A clause's parameters are **patterns**, and so is the left of a `=` in a body:

```
size []           = "empty"
size [_, ...rest] = "many"

rule go :- do
  p = mk "l" "r"
  (x, y) = p
  m = concat x y
  say m
```

`[a, b]`, `[a, ...rest]`, `(x, y)`, `(some x)`, `none`, `true`, `3`, `'c'`,
`"text"` and `_` are all patterns. A plain name is the pattern that binds it, so
nothing that could be written before means anything different.

**A refutable pattern that does not match is a failure.** In a rule the search
tries the next clause; in a function it is the caller's failure, as in Haskell.
There is no irrefutable/refutable distinction to learn.

**Patterns are linear** — `f x x` is refused. Matching a value against another
value is a different feature.

**A destructuring binding cannot be annotated**: `n : Ty` above a binding says
*this local is a scheme of this type*, and a compound pattern binds several
names with several types.

### A rule body opens with `do`

*Decided 2026-09-14; it was `then` until then.*

```
rule attack :- when focus-is-hole do prim-attack
```

Two reasons: `:-` is Prolog's neck, so `:- then` read as *then then*; and a block
of instructions is spelled `do` **everywhere else** — a function's body, a
surface term's block, a REPL `do { … }`. This was the one place with a word of
its own. **`then` is an ordinary identifier again** in every language.

### `instral` has a `Level`, and `fresh-universe` is not a primitive

*Decided 2026-09-15.*

```
l = level 2          -- an exact level, the one Type₂ means
l = fresh-level      -- a fresh meta, the one a bare Type means
u = universe-at l
```

`Level` is its own type and not `Int`, because a level a rule holds is usually a
**meta the solver has not decided**, and no numeral can be one.

**`fresh-universe` is a function over the two**, not an op — it was two
operations wearing one name. Its spelling is unchanged.

**There is no `level-suc` and no `level-max`**, deliberately: those are the level
*algebra*, and the solver stays their only author. A numeral is not an algebra.

### A splice supplies a nonterminal — a term, or a name

*Decided 2026-09-14.*

```
core`${d} -> ${d}`                  a term
core`λ (${n} : ${d}) -> ${d}`       a NAME, and a term
⌜ λ (${n} : ${d}) -> ${d} ⌝          the same, in corners
```

**The position decides what the binding must hold** — a term position wants a
`Core`, a name position wants a `Name` — so nothing is annotated and the two
cannot be confused. Both are checked when the file loads, along with a splice
that names nothing.

Every name position takes one: a λ or ∀ binder, a `let`, a claim, a guess, an
`elim`'s datatype, and a global at level arguments.

**A level position needs no splice**: build the universe with `universe-at` and
splice the term.

## Building a frontend

*Added 2026-09-24, MS7; rewritten 2026-09-27, when the decision below replaced a
network protocol with a library boundary.*

### Thena is a library, and a frontend links it

```
thena                  -- the terminal REPL, one frontend among others
```

A frontend advances a session with two functions on `Thena.Driver` and **never
opens it**: `Session` is abstract, and everything a frontend can see comes from
`Thena.View`, which describes a term, a development, a rule, the machine and the
parser's offers in its own vocabulary.

So a frontend never learns what a de Bruijn index is, when a Π is dependent, or
what distinguishes a guess from a claim. It renders what it is handed.

**The enforcement is cabal's.** A frontend's `build-depends` names `thena:view`,
which is a re-export list and has no modules of its own; `thena` is then a
transitive dependency, and Haskell imports only from direct ones:

```
import Thena.Engine (Machine)
  Could not load module 'Thena.Engine'.
  It is a member of the hidden package 'thena-0.1.0.0'.
```

Twelve modules are named: `Thena.Driver`, `Thena.Repl`, `Thena.View` and the
nine `Thena.View.*`. Nothing else is reachable, and a view that could not be
used through the list did not survive writing it — `coreView` took a `Core`,
which a frontend can neither obtain nor name, and became `focusTypeView`.

**Nothing in the library touches a terminal.** The REPL's line editing lives in
the `thena` executable, so a frontend that draws its own screen links no line
editor; what it reuses from `Thena.Repl` is the rendering and the session start,
which are not the terminal's.

**There was a WebSocket and a JSON message protocol here**, so that a browser
could be the frontend. It was removed: there is no remote client, the same
boundary is stronger as types than as a schema, and everything the protocol
carried is now a function call.

### A view is asked for, not handed back

A command returns what happened. It does not return a picture of the system.

```haskell
(session', response) = oneLine session ":theorem t : Type\8320"
links                = developmentView (Budget 200) session'   -- ask, whenever you draw
```

Every view is a function of the session, so a frontend recomputes the ones it is
showing after each command — or after a movement, or on a redraw — and a view
that follows the cursor does so for free. Nothing has to be subscribed to and
nothing can go stale.

The session supplies everything a view needs: the grammars loaded, the names in
scope at the focus, where each of them is bound, the name counter and the
cursor's route. A frontend passes a depth budget, which is its own choice, and
nothing else.

Every view is reachable with nothing but `thena:view` on the `build-depends`
line, and a test suite that depends on exactly that is what keeps it so.

### A region is written text and splices, and may name its production

A region of object syntax is not a string. It is the runs the user typed with the
splices between them, because a splice holds a host term the object grammar
cannot read:

```haskell
displayParse gs "LC" Nothing [WrittenText "( ", WrittenSplice, WrittenText " x )"]
```

The splices of a region are numbered in order from zero, and the offer at a
cursor splits the region without renumbering — so which splice is which never
depends on where the cursor stands.

`Nothing` reads the region as any term of the language; `Just "app"` reads it as
that one production, which is what a region written with a production named on it
means. Asking for a language or a production nothing declared is refused by name
rather than answered with an empty offer.

### A part of a term you have not written yet is `█`, and `█` is reserved

A region may have parts left unwritten, and one glyph says so:

```
LC`( █ x )`          -- the first argument has not been written yet
```

`█` (U+2588 FULL BLOCK) means exactly that, **everywhere a region is read** — at
the prompt, in a frontend, and in a `.thena` file on disk. It is not a hole: a
hole is written `?x`, is part of your program, and is solved by elaboration; a
placeholder is a part of a term nobody has written yet, and a term that still has
one does not elaborate. You are told which slot is empty:

```
in LC`( █ x )`: the M is missing
```

**No grammar may use `█`.** A production that writes it, or a token class that
would read it, is refused when the block is declared:

```
language L, M where
  f -> █ M
  → the terminal `█` contains the reserved █, which is how a part of a term
    that is not written yet is shown
```

That is the price of the feature, and it is paid deliberately: a glyph that meant
a placeholder in one region and a terminal in another could be told apart only by
looking closely, which fails anyone who cannot — and someone will type it to see
what happens.

**It was `?` until MS7, and `?` is now yours to use.** A grammar may write `?` as
an ordinary terminal:

```
language Q where
  opt -> ? Q
```

An editor need not put the character in its text at all: a placeholder can be
handed over as its own run, beside the splices, so a frontend that tracks
positions renders whatever it likes — an empty box, a highlight — and never
splices a glyph into a string.

### The offer lists the productions that fit, whole

Ask what may be written at a position and you are told three things: the symbols
that fit, what the position is waiting for, and **every production that may begin
there, with its shape and its skeleton**.

```
app:   ( LC LC )          -- what to show in a list
       ( █ █ )            -- what goes in the buffer when it is chosen
```

The skeleton arrives as runs, not as a string, so an editor that inserts it knows
where the unwritten parts are without going looking for them — and you can step
straight into the first one.

Only productions that could still leave the line finishable are listed. Inside a
parenthesis with one slot left, a production needing two does not appear.

### A project is text on disk, and there is no other format

A project is the files and the order you load them in. There is no binary form,
no JSON form and no manifest.

```
:load examples/01-untyped.thena     -- this is what storing a project means
```

The order is part of the project, not presentation: a module's globals are in
scope for the next one loaded.

**Stored as written, not resolved.** If a tactic that is a builtin today becomes
an ordinary rule tomorrow and keeps its name, every stored file keeps working;
rename it and they break, which is what a text file would do and is the point.

A JSON spelling of the same trees was built and then removed. It would have been
a second canonical form of every program, and two forms drift — so a Thena file
is equally at home in this system's own interface, in your usual editor, and in
anything built later over LSP.

**A half-written term is still text.** The parser takes a placeholder inline, so
a term you have not finished is an ordinary string and needs no special
representation to be stored or sent anywhere.

### The text printers take one rendering, not a grammar list and a counter

*Decided 2026-09-30.*

```haskell
renderCore (renderingOf session) context term
```

Everything in `Thena.Render` below `renderResponse` takes a `Rendering` — what a render
carries and does not change — rather than the installed grammars and a name counter as
two arguments.

**Build one with `renderingOf` and there is no counter to supply.** That matters because
there was no value a caller could correctly supply: the counter seeds the fresh variables
a printer mints to descend a term, `Var`'s constructor is hidden so no safe number can be
picked by inspection, and a low one silently corrupts the output — rendered from zero,
`A -> A` prints as `∀ (_ : A) -> _`, because the collision makes the dependency check
answer wrongly.

### A printed value can be read back

`instral` values printed at the prompt used Haskell's escaping, which renders `∀`
as `\8704` and a tab as `\t` — neither of which the lexer accepts. So a string
holding a tab, or any non-ASCII character, printed in a form that could not be
typed back.

It now uses the escaping the reader actually implements. **If you print a value
and paste it back, it is the same value.**

### A Core term displays as a labelled tree, not text

The editor cannot be handed the string the terminal prints — it needs to hover
a binder, highlight its occurrences, fold a subterm, point at "the motive"
rather than "argument four". None of that is answerable from text.

So a Core term has a *display representation*: every node carries its address
and what it is — never what it looks like. A variable carries the address of
its binder, not a de Bruijn index; a universe carries its level already
normalised; an eliminator's slots are labelled (parameters, motive, methods,
indices, target) instead of one flat argument list. **No text, no
parentheses, no layout crosses** — whether a Π prints as an arrow is only
whether its bound variable occurs, which the editor can already see, so it is
the editor's call and not the server's.

### A modelled language's term is a production, not a shape

A term written in an object language — `LC\`( \955 x : \953 . x )\`` — could
have displayed as a generic constructor application, the way the terminal
falls back to when it cannot print one in its own notation. It does not: the
display says *this is `abs`, with these three slots*, in the grammar's own
written order, and the editor lays it out from the grammar it holds. Nothing
about notation crosses.

Two things the grammar alone cannot say still have to: where a splice was
needed for grouping, because a person cannot always write a term flat and
have it read back what it means — that is the parser's answer, computed once
and handed across rather than asked of the editor. And which slot is a
binder versus an occurrence, so a variable in an object language highlights
the way one in Core does — not yet built.

### The development displays as its own chain

The development — the components a proof is built from, with a focus in
it — displays as the chain it is, one entry per assumption, definition,
claim, guess or pending constraint, ending in the term at the end. A guess's
own body is a chain of its own, nested inside its link, because a guess is
the one place the chain branches.

Three things only the server knows: whether a link is the focus (at
chain-link precision — a focus somewhere inside a type is a separate,
already-addressed question), whether a guess is pure enough for `solve` to
take, and whether anything later in the development still depends on a
given hole.

### A statement's display reuses the printer's own generalisation

`instral`'s instruction set has grown past sixty operations, and the
terminal printer stopped needing one case per operation early on: a
statement is *the word, then its operands*, for all but a handful. The
editor's display is generic for the same reason and reuses the same two
functions that decide it, rather than keeping a second table that could
drift from the first the way one already has.


### A long run goes in slices, and stopping it is not asking for the next one

There is no "interrupt". Instead the machine takes a fuel budget: how many
instructions a run may do before it hands control back. `:step ‹n›` sets what
every line may spend, `:run ‹n›` spends a budget once without changing that
setting, and `:step on` is simply the budget `1` — single-stepping is the
smallest case of one notion, not a mode of its own.

```
thena> :step 500
thena> prove              -- runs 500 instructions, then pauses
thena> :run 500           -- one more slice
thena> :run               -- and let it finish
```

A paused run is an ordinary stopped machine, so everything that works after
`:step` works here: `:choices` lists the live choice points and `retry ‹n›`
takes a different route. That is the reason for fuel rather than an
asynchronous interrupt — an interrupted fold cannot be resumed, and being able
to look at a search that was going well and carry on is the point.

A frontend builds a job out of this and nothing else: advance a slice, draw
whatever it wants to draw, advance again; stopping is not calling again. One
session advances one thing at a time, so an editor refuses a second submission
while a run is live rather than queuing it.

Two things fuel does not bound. A single instruction may be a kernel call —
`certify`, a `data` declaration, a grammar check — and those run to completion,
so one unit of fuel can take minutes. And three operations are unbounded by
construction, because they read the finished state rather than reporting it:
loading a file, `qed`, and `:infer`. **That is intended and not a gap** — ruled
2026-10-02 — so a frontend waits out a `:load` and a resumable one is not owed.

### A tagged literal is notation, not a term — `Core` carries no tag

``LC`( M N )` `` and `app M N` are **the same term**. The tag says which grammar to
read the text with; once it is read, what is left is an ordinary application of that
language's constructors. Nothing in `Core` records that you wrote the notation.

So the notation is *reconstructed* when a term is shown. A term is written back as a
literal when its head constructor is a production of some grammar — the lookup is by
constructor name, so there is never a choice of notation to make — and the layout is
then printed, re-parsed, and accepted only when the reading gives back the same tree.
Where it does not, a subterm is fenced in a splice and the check runs again. That is
why a term you wrote flat can come back with a fence in it: the fence is what makes
the text read as the term.

The alternative was a `Core` constructor holding the tag, and it does not survive one
question: is a tagged term convertible with its own contents? It has to be — a
theorem proved about ``typing`· ⊢ ${M} : ${T}` `` must apply to `typing ctxEmpty M T`,
or the notation is a different language rather than a way of writing this one. A
constructor that conversion must ignore is a constructor every part of the kernel must
remember to strip, and one that quietly destroys unique normal forms, since a tag
could then sit at any subterm any number of times.

What this costs you is real and small: the system does not remember whether you typed
a term as object text or in Core notation, and it does not remember your spacing. What
it buys is that the two spellings are one term everywhere, with no rule about when
they are interchangeable, because there is nothing to interchange.

### Completion is derived from the op table, so it can never disagree with dispatch

Typing at the prompt offers you the statements that exist *now*: every op, and every
rule in every base you have loaded. That list is not written down anywhere. It is
computed, each time you ask, from the same tables the engine dispatches on — the op
table for the words and their arities, each rule's declared signature for what its
arguments are. Load a rule base mid-session and the completions change immediately,
with nothing to regenerate.

The alternative was a second grammar for `instral`, written beside the one Happy uses
to actually run your line. Two grammars for one language drift, and the drift is
silent: the parser that runs your program and the parser that advises you would slowly
come to disagree about what the language is. Deriving both from one table is what
makes that impossible rather than merely unlikely.

Note what this does *not* change: your line is still run by Happy. The derived grammar
only answers "what may I write here", never "what does this mean".

### A slot's type narrows what is offered, and never prevents what you write

`quantify` takes a `Name` and then a `Core`, so after `quantify ` you are offered names,
and after `quantify x ` you are offered terms. The offer walks from argument to argument
as you type.

But writing something the slot does not want is not refused. Type a tagged term literal
where a `Name` was expected — `goto LC\`` — and you still get the full completion for
that literal, from the object language's own grammar, **marked as recovered** so the
editor can show you that the line will not run as written.

The mechanism is one rule rather than an exception list: when the whole line has no
reading at your cursor, the system asks a narrower question about the unit you are
standing in. Inside a tagged term literal, that language answers; in a half-typed word,
the statement grammar answers, filtered by what you have typed.

Two things were considered and rejected. Accepting everything everywhere would have
made the offers useless, because nothing would distinguish what belongs here from what
is merely tolerated. Teaching the parser to "forgive" a misplaced literal would have
made it dishonest — it would report a reading that does not exist. Neither is needed:
the grammar stays strict and truthful, and the help comes from asking a different,
smaller question.

### The prompt completes what you are writing, and says when it is guessing

*Added 2026-09-30, MS7 phases 139–143.*

Press Tab, or open a dropdown, and the system answers **what may be written here** —
not from a list of keywords, but from the same tables it dispatches with. Ask at any
point in a line and you get the words, the token classes and the productions that could
stand there, narrowed to the type the position wants.

```
fill                 -- a Core goes here: a name, a call, or a tagged literal
fill ( typeof        -- inside a call: its own argument, which is a Core
fill LC`( λ x :      -- inside a literal: ι, from the grammar YOU declared
h = here             -- a binding
goto                 -- ...and h is offered here, with its type
:inf                 -- completes to :infer
:step                -- on, off, or a number
```

Four things follow from where the answers come from.

**A slot says what it wants, because a slot is a nonterminal named after its type.**
*"Argument 2 wants a `Core`"* is not a feature layered on the answer; it is the answer.

**A nested call is offered wherever its result fits.** `fill ( goal )` is suggested
because `goal` returns a `Core` and `fill` takes one — the same table that dispatches
the call decides it, so a rule you write today is completable today.

**Inside a tagged literal, your own grammar answers.** The object grammars are part of
the same chart as the statement syntax, so one line is read once: the type slot of your
`abs` production offers your `ι`, and nothing had to be told about either.

**An answer that cannot be trusted says so.** When the line does not read, the system
asks a narrower question about the unit under the cursor and marks the answer
*recovered* — completing `atta` to `attack` says nothing about whether `attack` may
stand there, and a frontend is expected to draw it differently. A standalone term at the
prompt is answered this way on purpose: it is not a legal line, so the help arrives
marked rather than pretending.

**What it does not do**: a surface or core term — `:infer`'s argument, or
`` surface`…` `` — gets no completion, because those are the only languages with no
grammar in the chart. The system says *something goes here* and does not pretend to
list it.
