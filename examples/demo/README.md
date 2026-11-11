# The demo set

**A small language, carried from its grammar to a theorem about it**, in files
short enough to read off a projector. TAPL's arithmetic and boolean
expressions: two types, seven term formers, no binders — so nothing here is
about substitution, and everything is about the machinery.

**Load it in a fresh session.** It declares a language called `Ty`, as the
numbered series does, and two languages of one name cannot be installed at
once.

```
./tc examples/demo/Demo01Expressions.thena \
     examples/demo/Demo02Judgments.thena \
     examples/demo/Demo03Derivations.thena \
     examples/demo/Demo04Progress.thena \
     examples/demo/Demo06Trust.thena
```

Each file states what it imports, so any one of them loads on its own and
brings its prefix with it — at the prompt by module name, which is what
survives:

```
cabal run thena
import examples.demo.Demo04Progress
:replay examples/demo/Demo05ByTactics.thena.script
```

| file | what it shows |
|---|---|
| `Demo01Expressions.thena` | The language as a grammar: two `language` blocks, terms written in the notation they just defined, `${…}` splices, `Tm[succ]` to start the parse at one production, and a `refl` proving that the literal **is** the constructor application |
| `Demo02Judgments.thena` | Typing, numeric values, values and small-step reduction as `judgment` blocks — written above and below a bar, as a paper writes them. A premise drawn from another judgment; `M'` as another metavariable of the same language |
| `Demo03Derivations.thena` | A typing derivation written out as the tree it is; the reflexive-transitive closure declared as an ordinary judgment on top of another; a whole run to a value; and that the answer really is finished |
| `Demo04Progress.thena` | **Progress — TAPL 8.3.2.** Canonical forms, three step-producing lemmas, and the theorem, by induction on the typing derivation. The recursive call **is** the induction hypothesis. Compare `examples/Progress.thena`, the same theorem for the same language over a hand-written `data Term` |
| `Demo05ByTactics.thena.script` | **The interactive half.** The smallest possible proof in three lines, then a lemma proved by `case-core` — one hole per surviving case, inside that case's own binders, equations already discharged |
| `Demo06Trust.thena` | `trusted` and `:trust`: a claim that is met and reduces away to nothing, and one that is **pending** and is still load-bearing. `qed` admits the theorem and prints what it rests on |
| `pending/Demo07Holes.thena` | **Does not load, deliberately.** The shape the demo wants — a hole left where a proof should be, picked up interactively on load — and the measured account of what happens instead. Item `~mgqwb` |
| `Demo08Pausing.thena.rules` | **One rule that makes the elaborator hand you the hole.** A clause of `elaborate` whose body is `yield`, where the shipped base's is empty. `:consult` it and `declare two : Nat ; two = succ _` stops on the placeholder's own hole with the declaration's context in scope; fill it, `yield`, and the declaration lands. **At the prompt only** — a module load throws the suspension away, which is all `~mgqwb` is |

## The two documents beside them

- **`PRACTICE.md`** — exercises, no solutions. Working through them is how the
  presenter gets fluent.
- **`DEMO.md`** — a running order for an hour in front of people who do
  programming-language research but are not all type theorists.

## What the corpus suite checks

`cabal test thena-examples --flags=examples` loads the five modules in a fresh
session, replays the script, and pins the statements of `progress` and
`predSteps-tactics`. **It is here so the demo cannot rot**: nothing else in the
tree loads these files.
