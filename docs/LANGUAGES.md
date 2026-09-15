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
  do n = ask "name for the new hole?" name
     ; claim n ty

twice : String -> String
twice s = concat s s
```

- **a rule** — `rule ‹name› ‹params› :- when ‹tests› do ‹body›`. The head is a
  run of shape questions; a test with arguments is parenthesised.
- **a signature** — `‹name› : ‹type›`, on a line of its own and needing no
  keyword. The arity
  is the arrow chain's, so a signature is about one arity only. Parentheses make
  an arrow a value in either position: `(a -> b) -> a -> b` takes a function and
  `String -> (String -> String)` gives one.
- **a function** — `‹name› ‹params› = ‹expression›` or `‹name› ‹params› = do
  ‹block›`, with no keyword. A function may have several clauses, tried in
  order as in Haskell.

**A rule is searched; a function is called.** A rule's clauses are alternatives:
the first that matches runs, and if it fails the next is tried, so a rule can
leave a choice point. A function makes no choice point, is never offered by
`:matches`, and is never run by `prove`.

**A declaration begins in column 1**, and a block's lines line up under its
first instruction. That is what lets a function need no keyword of its own:

```
rule base indented where

rule f :-
  do say "hi"
     prove                -- lined up under say: still the rule above
 g x = concat x x         -- column 2: neither part of f nor a new declaration
```

```
thena spine> :load indented.thena.rules
indented.thena.rules: 6:2: unexpected g
```

Written in column 1, `g x = concat x x` is a new declaration and the file loads.

## 4. `instral`: statements

The body of a rule, a `do { … }` block inside a Surface term, and what you type
at the prompt are all the same language.

```
rule demo :- do p = (1, true)
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

- `‹pattern› = ‹expression›` binds; a bare expression is run for effect.
- `return ‹value›` ends the body and is what the caller gets.
- A word is **an op** if one bears that name at that number of arguments,
  otherwise **the local** if one is bound, otherwise **a call to a rule or
  function** of that name.
- A lambda is `\ x -> e`; in an argument it takes parentheses. **A lambda takes
  at least one parameter** — a value needs no lambda: `x = e` names it and
  `r = x` uses it.
- **A function is not curried.** `join a b = concat a b` takes two arguments,
  and `join "x"` is refused — *join takes 2 arguments, not 1 argument*. A
  function that gives a function says so in its type:
  `adder : String -> (String -> String)`, `adder a = \ b -> concat a b`.
- `‹name› : ‹type›` on its own line, just above a binding, annotates that local.

### Patterns

A parameter and the left of a binding are both **patterns** over `instral`'s own
data: `x`, `_`, a literal, `[]`, `[a, b]`, `[a, ...rest]`, `(x, y)`, `(some x)`,
`none`. A shape is asked in the pattern rather than by a test, so a fold is two
clauses:

```
rule walk [] :- do say "done"
rule walk [x, ...t] :-
  do say x
     walk t

rule go :- do walk ["a", "b"]
```

```
thena spine> go
a
b
done
```

**A pattern that does not match is a failure.** In a rule that means the next
clause is tried, and you can see it:

```
three = ["one", "two", "three"]

rule pick :- do [only] = three ; say only
rule pick :- do [a, b, _] = three ; m = concat a b ; say m
```

```
thena spine> pick
chose 680: pick
backtracking to 680: pick
onetwo
```

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
String   Name   Int   Char   Bool   Level
List a   Option a   (a, b)   a -> b
Surface   Core   Development
```

Nothing is annotated unless you want it to be: a rule's type is inferred from its
head predicates, its patterns and the ops its body uses. **A base that does not type check
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
- **Inference is Hindley-Milner.** A rule or function is generalised, so
  `rule ignore x :- do say "ignored"` can be used at a `Name` in one place and a
  `Core` in another with no signature. **A local is not generalised**: a lambda
  bound in a body is used at one type unless you annotate it.
- **A signature is documentation that is checked.** A promise the body does not
  keep is reported against the signature:

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

The signatures shown are the inferred ones, functions included.

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

## 7. Splices: holes in a written core term

A written core term may have holes, filled from `instral` bindings when the
instruction runs:

```
rule arrow-demo :-
  do d = resolve-core core`Type₀`
     t = resolve-core core`${d} -> ${d}`
     claim "k" t

rule level-demo :-
  do l = level 2
     u = universe-at l
     t = resolve-core core`${u} -> ${u}`
     claim "big" t
```

```
thena spine> arrow-demo
thena spine> level-demo
thena spine> :show
  let ? k : Type₀ -> Type₀ in
  let ? big : Type₂ -> Type₂ in
▶ let ? t : Type₀ in
  t
```

**A splice stands for what the grammar expects in that position**, so the
template is parsed when the file loads and only the values wait. A term position
wants a `Core` and a name position — a binder, a `let`, a claim — wants a
`Name`, and both are checked at load:

```
rule wrong :-
  do d = resolve-core core`Type₀`
     t = resolve-core core`λ (${d} : ${d}) -> ${d}`
```

```
the rules do not type check:
  wrong, instruction 2: wanted Name, got Core
```

A level needs no splice of its own: build a universe with `level ‹n›` or
`fresh-level` and `universe-at`, and splice the term.

**Only the core grammar takes a splice today.** Neither `` surface`…` `` nor an
object language's region does.

## 8. REPL commands are not a language

A **bare word acts** and a **word with a colon looks**. The colon commands manage
the session or show you something; `:help` lists them. Everything else you type
is `instral`, which is why there is no separate REPL grammar to learn.

The one exception is `:goal`, which is a colon command that changes the
development. It is known and kept deliberately for now.

## 9. Where this is written down

`DECISIONS.md` at the repository root records each of these as a decision, with
the shortest example that shows it, in the order they were taken.
