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

*Nothing recorded yet. The universe work is MS3; its decisions are in
`.claude/plans/milestones/ms3/` and `.claude/discussion/` and should be summarised
here.*

---

## The core language and its type theory

*Nothing recorded yet.*

---

## The development calculus

*Nothing recorded yet.*

---

## Tactics and the rule engine

*Nothing recorded yet.*

---

## The REPL and the session

*Nothing recorded yet.*
