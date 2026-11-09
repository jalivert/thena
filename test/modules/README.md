# Modules an import graph is tested on — MS11 phase 274

**Reached by NAME and not by path**, which is the whole point of them: a module
name is a path under the project's source root (`Thena.Driver.moduleFile`), the
root here is the process's working directory, and so `test.modules.Bit` is this
directory's `Bit.thena`. Every step of a module name is a word, so a directory
whose name is not one could hold no importable module at all.

`Thena.LoadTests` — *an import graph* and *a rule base states what it depends on* —
is what reads them. They are deliberately
tiny: what is under test is the graph — the order, the diamond, the cycle, and
that a closure lands all or none — and not what a module can declare.

**The two rule bases are a pair and only the pair measures anything.**
`Inspecting.thena.rules` imports `Lang.thena` and resolves a tag of the language it
declares; `Unstated.thena.rules` is the same file without the `import` line and is
refused. Before MS11 phase 276 every test of a rule file's scope loaded the module
itself first, so the session satisfied the dependency and nothing could tell a stated
one from a lucky one.

**AND THE PAIR IS RUN TWICE SINCE MS11 PHASE 297, THE SECOND TIME WITH `Lang` ALREADY
IN.** Refusing `Unstated` in a session that never loaded `Lang` measures only that the
dependency is absent. **Until phase 297 the same file LOADED as soon as anything else had
put `Lang` in** — `./tc test/modules/Lang.thena test/modules/Unstated.thena.rules` printed
`loaded unstated (1 rule)` — because a rule base was resolved in a scope that concealed
nothing. `Thena.LoadTests`' *and it is refused even when the module IS in* is the case
that measures isolation, and `.claude/HAZARDS.md` has why the first pair could not.

**Three of them are MS11 phase 297's, and they are `Thena.ObjectTermTests`', not this
suite's.** `Rooted.thena` declares a language at a module's root and one term of it,
`OneNested.thena` one inside a `namespace`, `TwoNested.thena` two namespaces that answer
one word. They were strings inside that test module until a rule file had to state what it
refers to: a base reaches a language only by importing the module declaring it, and a
module has a name to import only once it was reached by one —
`Thena.Driver.loadProofSource` reaches a module by no name at all, so nothing loaded that
way can be named in an `import`.

**`Misnamed.thena` declares `module test.modules.Elsewhere where`** and
`ImportsMisnamed.thena` imports it — the pair for `~r58qh`, his ruling of
2026-11-05. Importing it is refused; loading `Misnamed.thena` by its path is not,
because the match is only asked on the way in. `0unnameable.thena` is the other
half of that: a path that is no module name at all, so its header is never
compared with anything.

**Four of them are MS11 phase 282's**, his ruling of 2026-11-05 that a module resolves
against its own imports, its own declarations and the prelude. `UsesPrelude.thena`
imports nothing and writes `Eq` and `refl`, so the prelude needs no import.
`OnlyPair.thena` imports `Pair`, which imports `Bit`, and writes `Bit.Bit`: it is
refused, because an import is not transitive until `public import` exists.
**Four more are MS11 phase 283's**, `~w46f8`: a file does not end its own `open`s.
`Opener.thena` declares `Bit` and writes `open Bit` at its top level, and
`Inherits.thena` imports it and writes a bare `off` with no `open` of its own — an
`open` travels with an `import`, which is `examples/Progress.thena`'s shape.
`BareOpen.thena` is the other half of that pair: it imports `Bit.thena`, which opens
nothing, writes the same bare `off` and is refused — before the phase it was refused
or accepted according to whether a file whose top level wrote `open Bit` had gone in
first. `ScopedOpen.thena` writes its one `open` inside a `namespace` block, which
nobody inherits, because the block is where it ends (`~ckmsk`).

`Metavars.thena` and `BorrowsMetavars.thena` are a pair `Thena.GrammarTests` reads —
one declares a language, the other imports it and borrows its metavariable, writing its
own `open` rather than inheriting one. Before the phase that pair was two module
sources loaded into one session, which measured the session and not the import.

**Nine of them are MS11 phase 288's**, `public consult`. `Tooling.thena.rules` is the
only place a rule called `marker` exists, so a `do` block that calls it resolves
exactly when that base is in the module's pool — which is what every one of these
measures. It also `import`s `Lang.thena`, which is the point: before this phase a file
could consult only a base that depended on nothing.

- `Keeps.thena` consults it plainly and calls `marker`, and **names `Lang` nowhere** —
  the base's own dependency joins the closure.
- `Stacked.thena` consults `Tooling` and `Louder` and calls a rule from each, so two
  bases really are in one pool. `Louder.thena.rules` imports nothing and is the second
  base purely so the order has two things to order.
- `Publishes.thena` writes `public consult test.modules.Tooling` and declares nothing
  else. `GetsTooling.thena` imports it and calls `marker`; `MissesTooling.thena` is the
  control, importing `Keeps.thena` instead, and is refused.
- `PassesTooling.thena` writes `public import test.modules.Publishes` and
  `GetsPassedTooling.thena` imports that — the closure, since what travels is what the
  imported module *got*. `KeepsPublisher.thena` is the plain-import half and
  `MissesPassedTooling.thena` imports it and is refused.

**Six of them are `.thena.script` files, MS11 phase 296's** (`~qnfcp`), and they exist
because `Thena.Files.loadFile` is the function under test and it reads a real file:

- `ImportsBit.thena.script` is the feature — `import`, `open`, and a line that needs
  both. `ConsultsLouder.thena.script` is the same for `consult`, and `Louder` is the
  base that imports nothing, so nothing but the consult is being measured.
- `ImportsNowhere.thena.script` and `ImportsBrokenToo.thena.script` are the two ways a
  followed act fails: a module the disc has not got, which arrives as `Trouble`, and
  one that will not elaborate, which arrives as a stopped `Response` about the file the
  line named. **Each is followed by a `data A0` line that must NOT have run.**
- `LoadsAModule.thena.script` is the refusal that stays: a `:load` inside a file, with a
  `data A0` line before it that must have run.
- `ImportsLoop.thena.script` reaches `LoopA`/`LoopB` through a script, so the cycle
  refusal is the module walk's own and is not written twice.

**And four are `~2kc72`'s, which is OPEN on MS11's closeout list and is not a suite's.**
`WithheldLang.thena` exports `keep` only and declares a language; `TakesLang.thena.rules`
imports it and matches `LC[app]`, which **loads** — the leak; `NamesLang.thena` names the
type and is refused, *not in scope: LC*; `WritesLang.thena` writes the notation without
naming the type and is refused one step later, *not in scope: LC.app*, which is how we
know **a surface importer gets the grammar too**. Run them with `./tc`. Added 2026-11-09
because the first measurement's files had been deleted and the item had to be
reproduced from its own text.

**And three are MS11 phase 302's, for `:replay`** (`~22qjj`, his ruling of 2026-11-09).
`Thena.LoadTests` — *a replay is the lines, not the asking* — is what reads them:

- `Replayed.thena.script` is what gets replayed, and its three lines are chosen so that
  each of the ruling's halves is observable: an `import`, so there is a file the hash
  list must hold while the script itself must not; an `open`; and a `claim`, which
  changes the development and so pushes the undo snapshot that a replay must leave
  behind and a `:load script` of the same file must not.
- `ReplaysReplayed.thena.script` replays it and then writes a line that needs what the
  replay brought, so a nested replay is measured as a replay and not only as a read.
- `ReplaysItself.thena.script` is the loop, refused rather than followed.

**And six are MS11 phase 300's, for a rule file's `consult B where { … }`** (`~k68d7`).
Four of them are a pool and two are names:

- `Pins.thena.rules` holds `Quiet.thena.rules` for one block. Both answer `answer`, so
  which clause runs says where the push landed: `inside` gets `Quiet`'s, `outside` gets
  the file's own, and `:bases` at rest lists neither `Quiet` nor anything else new.
  `peeks` yields from inside the block, which is the only way to see the pushed base
  listed; `breaks` calls a rule of `Quiet` that fails, which is how the pool after a
  body that never reached its pop is measured.
- `Nests.thena.rules` writes a block inside a block, with `Loud.thena.rules` as the
  inner one's base — three clauses of `answer` and three answers, which is *nesting is
  priority*.
- `ScopedBorrows.thena.rules` and `ScopedBorrowsAfter.thena.rules` are the names half
  and only the pair measures anything: both consult `Lends.thena.rules`, which hands
  `Lang` on with `public import`, and the first writes `LC[app]` inside the block while
  the second writes it after. The first loads; the second is refused.
