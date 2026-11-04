# Modules an import graph is tested on — MS11 phase 274

**Reached by NAME and not by path**, which is the whole point of them: a module
name is a path under the project's source root (`Thena.Driver.moduleFile`), the
root here is the process's working directory, and so `test.modules.Bit` is this
directory's `Bit.thena`. Every step of a module name is a word, so a directory
whose name is not one could hold no importable module at all.

`Thena.LoadTests`, *an import graph*, is what reads them. They are deliberately
tiny: what is under test is the graph — the order, the diamond, the cycle, and
that a closure lands all or none — and not what a module can declare.
