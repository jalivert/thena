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

**It is stated for closed terms**, as Software Foundations states it. The
argument substituted in a β-step is then closed, so no binder is ever renamed.
For any context the argument may have free names, a binder may be renamed, and
proving the renamed binder fresh needs facts about strings that Thena cannot
state yet.

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

**`context` and `judgment` are reserved words**, like `language`. A name in a
production is a metavariable, then a token class, then a terminal, and a
metavariable may not be named like an existing one or a class. A block sees
what is above it, as every declaration does. It is checked when the module
loads, and a binder that binds in nothing is a warning, not an error.


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
parse LC> ( ‸               Tab →   lists  λ  (  ‹LC›  ‹x›  {
parse LC> ( λ x : ?‸ . x )  Tab →   lists  ι  (      (what can replace the ?)
```

When the terminal just before the cursor belongs to one production only, Tab
inserts the rest of it, `?` for its slots. That happens only at the end of the
line, never in the middle. Otherwise Tab lists what can go at the cursor such
that the line can still be finished, counting what's already written after
the cursor. On a `?`, Tab fills that hole, so it offers only notation. The
options appear when you press Tab, not as you move; options that follow the
cursor are the structural editor's job.


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
  T-var : ∀ (x : String) (T : Ty) (Γ : Ctx) -> Ctx-in x T Γ -> typing Γ (var x) T
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

### A context gets a lookup relation, written `x : T ∈ Γ`

*Decided 2026-09-21.* A `context` block declares its datatype and, beside it,
the relation that looks a name up:

```
context Ctx, Γ where
  empty  -> ·
  extend -> Γ , x : T
```

```
data Ctx-in : String -> Ty -> Ctx -> Type₀ where
  Ctx-here  : ∀ (Γ : Ctx) (x : String) (T : Ty) -> Ctx-in x T (extend Γ x T)
  Ctx-there : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty)
                -> (Eq String x x' -> Empty) -> Ctx-in x T Γ -> Ctx-in x T (extend Γ x' T')
```

**Its notation is the extension with the context taken out, then `∈` and the
context**, and it is a grammar like any other: `` Ctx-in`x : ι ∈ ·, x : ι` `` is
the type `Ctx-in "x" base (extend empty "x" base)`, `:parse Ctx-in …` reads it,
and it prints back. The separator goes with the context: `Γ , x : T` gives
`x : T ∈ Γ`, and so does `x : T ; Γ`. **The indices are the notation's slots
in order**, as a judgment's are, so the context comes last.

**A later binding shadows an earlier one of the same name.** `Ctx-there` asks
for a proof that the two names differ. For two literals that proof needs no
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

The constructors are named after the context, as `Ctx-in` is, so two contexts
in one session do not clash. **The extension must have exactly one name** (a
`Token String` argument), because that is what the lookup compares. Weakening
and exchange are not generated.

### A language gets substitution for free, and a binder is renamed only when it would capture

*Decided 2026-09-21.* A `language` block with a variable production
(`var : x as occurrence -> x`) also declares four functions, right after its
datatype:

```
LC-fresh     : String -> List String -> String
LC-fv        : LC -> List String
LC-subst-all : LC -> List (And String LC) -> LC     -- simultaneous
LC-subst     : LC -> String -> LC -> LC             -- LC-subst E x N is E[x->N]
```

They are ordinary definitions, written by `elim` and elaborated like anything
you write. They compute, so a substitution's answer is provable by `refl`:

```
captured : Eq LC (LC-subst (abs "y" base (var "x")) "x" (var "y")) (abs "y'" base (var "y"))
captured = refl LC (abs "y'" base (var "y"))
```

**A binder keeps its name unless keeping it would capture**, and is then primed
until it is free: `y`, `y'`, `y''`. Nothing is renamed behind your back, so
capture is something you can see happen and see avoided. A list substitutes
simultaneously (`[x->y, y->x]` swaps), and of two pairs for one name the first
wins.

What it needs of the language, each refused at the block with a message:
exactly one variable production, taking only its occurrence; and a binder free
only in arguments of the language itself. A language with no occurrence (`Ty`)
gets nothing. The four names are yours to keep free — declaring `LC-fv` first
is refused.

Two things arrived with it. **`List`, with `nil` and `cons`, is in the
prelude**, so those names are taken from every object language until imports
exist. **`appendString : String -> String -> String`** is the one way to build
a `String`, and it computes only on two literals. The types that mention `List`
carry a level parameter, `LC-fv {ℓ}`, because a list of names is a list at any
level and nothing is defaulted.

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
  then n = fresh-name "refined" ; x = define n t
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
  then w = surface-name t ; x = resolve-name w ; fill t ; solve

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
thena spine> :load proof examples/canonical.thena
module Canonical
  declared Term
  ...
warning: no noConfusionNV: nvSucc's argument 2 (n) has a type that depends on an
  earlier argument, so its equation cannot be stated
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

A rule file is one layout block and a rule body is a block that `then` opens, so
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
  then n = fresh-name "refined"
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

## The editor interface

*Added 2026-09-24, MS7. None of this is an editor — it is the server side an
editor is built against.*

### Thena speaks a protocol, and the REPL is one of its clients

```
thena                  -- the terminal REPL
thena --socket 9000    -- the same session, on a WebSocket
```

The terminal REPL no longer reaches into the system directly: it sends messages
and renders what comes back, exactly as a remote client does. Only the transport
differs — in one case a function call, in the other a socket.

**Why you might care:** anything the REPL can do, a client can do, and the golden
transcripts that pin the REPL's behaviour are therefore also the protocol's
regression tests. The socket listens on loopback only.

### A project is an ordered list of modules, and it is stored as written

A project can be stored as JSON or as text, and **both load to the same session**.
The order is part of the project, not presentation: a module's globals are in
scope for the next one loaded.

**Stored as written, not resolved.** If a tactic that is a builtin today becomes
an ordinary rule tomorrow and keeps its name, every stored project keeps working.
Rename it and they break — which is what a text file would do, and is the point:
JSON and text are two spellings of one artifact rather than two artifacts.

### A printed value can be read back

`instral` values printed at the prompt used Haskell's escaping, which renders `∀`
as `\8704` and a tab as `\t` — neither of which the lexer accepts. So a string
holding a tab, or any non-ASCII character, printed in a form that could not be
typed back.

It now uses the escaping the reader actually implements. **If you print a value
and paste it back, it is the same value.**

