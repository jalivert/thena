# Thena's languages: what can be written where

Thena has **four languages**, and this document says what each one is, where you
may write it, and how one is embedded in another. It is meant to be enough on its
own — you should not have to read anything else to know where a term goes.

| | what it is | where you write it |
|---|---|---|
| **Surface** | the language you write proofs in — binders, applications, `let`, `data` | `.thena` proof modules; inside `⟨ … ⟩` |
| **Core** | what the kernel checks — no sugar, no implicits | inside `⌜ … ⌝`; built by ops |
| **development calculus** (DC) | the half-built proof itself: holes, guesses, hypotheses | built by tactics; printed by `:show` |
| **`instral`** | the instruction language — rules, functions, and what you type at the prompt | `.thena.rules` files; `do { … }` blocks; REPL entries |

An object language you declare yourself is a fifth thing, but it is not a fifth
language of Thena's: it is Surface data with a grammar, and §6 covers it.

---

## 1. Untagged means `instral`

Anywhere an argument is written without a fence, it is `instral` — a name, a
number, a string, a list, a pair. There is no privileged bare language.

```
claim n ty                 -- two instral references
say "claimed"              -- a string literal
f [1, 2, 3] (a, b)         -- a list and a pair
```

**A compound argument takes parentheses.** `some-rule (f a) b` is one call and
one variable; without them nobody can tell one argument from two.

## 2. Every other language is written in a fence

```
⟨ \ A a -> a ⟩             -- Surface
⌜ succ zero ⌝              -- Core
Tm`(x y)`                  -- an object language you declared
```

The fences are self-delimiting, so they nest and need no parentheses of their
own. A tagged region's contents are parsed **when the file loads**, not when the
rule runs, so a syntax error inside one arrives with every other syntax error.

```
thena spine> :theorem id : ∀ (A : Type₀) (a : A) -> A
proving id : ∀ (A : Type₀) -> A -> A
thena spine> elaborate ⟨ \ A a -> a ⟩
already equal
thena spine> qed
id : ∀ (A : Type₀) -> A -> A   ∎
```

**A written core term is resolved by a visible step.** `try-core ⌜ x ⌝` compiles
to `⌜1⌝ = resolve-core ⌜ x ⌝ ; try-core ⌜1⌝`, because the same term written in
two places may resolve to two different things and you should be able to see
which one you got.

## 3. `instral`: declarations

A `.thena.rules` file holds three kinds of declaration, side by side.

```
rule claim ty :-
  then n = ask "name for the new hole?" name
     ; claim n ty

twice : String -> String
twice s = concat s s
```

- **a rule** — `rule ‹name› ‹params› :- when ‹tests› then ‹body›`. The head is a
  run of shape questions; a test with arguments is parenthesised.
- **a signature** — `‹name› : ‹type›`, on a line of its own and needing no
  keyword. The arity
  is the arrow chain's, so a signature is about one arity only. Parentheses make
  an arrow a value in either position: `(a -> b) -> a -> b` takes a function and
  `String -> (String -> String)` gives one.
- **a function** — `‹name› ‹params› = ‹expression›`, with no keyword. A function
  is a rule with one clause and no head; the only visible difference is that it
  is never offered as a tactic.

**A declaration begins in column 1.** Indent every continuation line. That is
what lets a function need no keyword of its own:

```
rule f :- then say "hi"
     ; prove              -- indented: still the rule above
g x = concat x x          -- column 1: a new declaration
```

```
thena spine> :load bad.thena.rules
bad.thena.rules: 2:3: unexpected rule
```

## 4. `instral`: statements

The body of a rule, a `do { … }` block inside a Surface term, and what you type
at the prompt are all the same language.

```
rule demo :- then p = (1, true)
     ; l = [1, 2, 3]
     ; m = twice "ab"
     ; say m
     ; f = \ z -> concat "<" z
     ; r = f "z"
     ; say r
```

```
thena spine> demo
abab
<z
```

- `‹name› = ‹expression›` binds; a bare expression is run for effect.
- `return ‹value›` ends the body and is what the caller gets.
- A word is **an op** if one bears that name, otherwise **the local** if one is
  bound, otherwise **a call to a rule** of that name. The op words are never
  shadowed.
- A lambda is `\ x -> e`; in an argument it takes parentheses.

**What you type at the prompt is a block**, so a binding lives for the entry and
dies with it:

```
thena spine> h = here ; claim "k" ⌜ Type₀ ⌝ ; goto h
```

An entry may span lines. Open it with `:{` and close it with `:}`, each alone
on its line, and the lines between are one entry — separated by the offside
rule, so they need no `;`:

```
thena spine> :{
         ... h = here
         ... claim "k" ⌜ Type₀ ⌝
         ... goto h
         ... :}
```

`:{` and `:}` are the only place the REPL asks for anything unusual, and they
are GHCi's spelling.

## 5. `instral` has types, and they are checked when a file loads

```
String   Name   Int   Char   Bool
List a   Option a   (a, b)   a -> b
Surface   Core   Development
```

Nothing is annotated unless you want it to be: a rule's type is inferred from its
head predicates and from the ops its body uses. **A base that does not type check
is not installed**, and the previous rules stay in place.

```
thena spine> :load bad.thena.rules
the rules do not type check:
  bad, instruction 1: wanted Core, got Surface
```

Two rules about types worth knowing:

- **`Name` is not `String`.** A string literal is accepted at either, so
  `fresh-name "h"` needs nothing; a *variable* going from a name to a string is
  written down, with `name-text`.
- **Write a signature when you want a rule usable at more than one type.**
  Without one a rule is inferred at a single type. A signature is *checked*, and
  a promise the body does not keep is reported against the signature:

```
thena spine> :load over.thena.rules
the rules do not type check:
  signature f/1: the signature says any type here, but the body needs Core
```

You can ask what fits a type:

```
thena spine> :accepts String
  ignore/1 : a -> ()   (rule)
  twice/1 : String -> String
thena spine> :produces String
  twice/1 : String -> String
```

`:matches` asks the other question — what applies to *this development* — and a
rule qualifies there because its head passes, not because its signature fits.

## 6. Declaring an object language

A grammar declaration gives you a type, a tag, and a coercion.

```
language Tm where {
  var : name ;
  app : "(" Tm Tm ")"
  }

asSurface : Tm -> Surface
asSurface t = surface-of t
```

- **`Tm` is a type** you can write in a signature.
- **`` Tm`…` `` is the only way to make one**, so a value of it is well formed by
  construction. A production builds its constructor applied to what its slots
  parsed, so `` Tm`(x y)` `` is the Surface term `app (var x) (var y)`.
- **`surface-of` is the one-way coercion.** Until you apply it, a `Tm` is not a
  Surface term as far as the type system is concerned.

**A grammar is written over Thena's own tokens**, so a terminal must be exactly
one: `"·"` is fine, `"."` is not. A production may not begin with the language
itself, and may not be empty.

```
thena spine> :load loop.thena.rules
loop.thena.rules: in the grammar of Tm: loop begins with the language itself
```

## 7. REPL commands are not a language

A **bare word acts** and a **word with a colon looks**. The colon commands manage
the session or show you something; `:help` lists them. Everything else you type
is `instral`, which is why there is no separate REPL grammar to learn.

The one exception is `:goal`, which is a colon command that changes the
development. It is known and kept deliberately for now.

## 8. Where this is written down

`DECISIONS.md` at the repository root records each of these as a decision, with
the shortest example that shows it, in the order they were taken.
