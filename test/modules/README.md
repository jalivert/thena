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
