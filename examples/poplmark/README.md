# System F-sub, and the POPLMark challenge

The POPLMark challenge (Aydemir et al., *Mechanized Metatheory for the Masses*,
TPHOLs 2005) asks for the metatheory of System F-sub — System F plus subtyping
plus records — machine-checked, in a way that still looks like the paper. This
directory is Thena's answer to **problem 1A**, transitivity of subtyping for
pure F-sub.

**Load these in a fresh session.** The numbered series in `examples/` declares
its own `Ty`, and two languages of one name cannot be installed at once.

```
cabal run thena
:load examples/poplmark/01-syntax.thena
:load examples/poplmark/02-subtyping.thena
:load examples/poplmark/03-typing.thena
:load examples/poplmark/04-transitivity.thena
```

| file | what it shows |
|---|---|
| `01-syntax.thena` | Part 2's whole language. Two token classes, so types read `X` and terms read `x`; `Ty` with `⊤`, the arrow and the quantifier; `Tm` **binding at both levels in one grammar** — `λ x : T . t` binds a term variable and `Λ X <: T . t` a type variable. The generated substitutions, `Tm-subst-X` among them: type substitution into a term |
| `02-subtyping.thena` | `Γ` with **two extension forms**, `x : T` and `X <: T`, and the two lookup relations that come with them; `append` given the paper's comma by a `notation` block, so `Γ , X <: Q , Δ` parses as a rule's index; `Ctx-subst-X` for `Γ[X -> T]`; the five algorithmic subtyping rules, and derivations |
| `03-typing.thena` | The six typing rules with subsumption. `T-TApp`'s conclusion is `T12[X -> T2]`, so the kernel computes the type of an instantiation rather than being told it |
| `04-transitivity.thena` | **Problem 1A.** Reflexivity; inversion of subtyping on the shape of the lower type; weakening; narrowing's lookup lemma; and transitivity-with-narrowing, all four cases of the induction on the middle type — **under one hypothesis, which is then refuted** |

## What is proved, and what stops it

Everything in `04` is kernel-checked. The outer induction on the middle type
is complete: `transTop`, `transTVar`, `transArrow` and `transAll`, with
`narrowFrom` giving narrowing from transitivity at the same type.
`transitivity` and `narrowing` are assembled from them.

They take one hypothesis, `Wk Q`:

```
Wk = \ Q -> forall (G : Ctx) (Xn : String) (D : Ctx) (P : Ty) (dp : sub G P Q)
              -> sub (append (bindTy G Xn P) D) P Q
```

which is the paper's silent step: *a derivation in Γ still holds in Γ , X <: P , Δ.*
It is used in exactly one place — narrowing's `SA-Trans-TVar` case, where the
variable looked up is the one being narrowed.

**`wkIsFalse` refutes it.** The paper's step rests on the Barendregt
convention, that bound names are fresh for the context. Thena's names are
nominal and there is no such convention, so a context may shadow:

```
· , B <: ⊤ , Y <: B           ⊢ Y <: B      -- yBelowB, derivable
· , B <: ⊤ , Y <: B , Y <: Y  ⊢ Y <: B      -- noYBelowB, refuted
```

In the second, `Y`'s binding is `Y <: Y`, so the only rule that could conclude
it is `SA-Trans-TVar`, and its lookup can only find `Y <: Y`, which leaves the
same goal.

So **1A needs a well-formedness discipline that the paper's rules as written do
not supply**, and supplying it is a decision about what F-sub is here, not an
implementation detail: narrowing has to be restricted to contexts with distinct
names, and `SA-All` has to require its bound variable fresh for the context so
that transitivity can meet that restriction. Neither is in the challenge's
statement of the rules.

## Not here

Problem **1B** (records) needs variable-arity productions; **2A** (type safety)
needs reduction and the term-substitution lemmas; **2B** needs record patterns;
**3** (animation) is a non-goal. `.jalivert/POPLMARK.md` has the gap analysis.
