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
:load examples/poplmark/02-contexts.thena
:load examples/poplmark/03-wellformed.thena
:load examples/poplmark/04-subtyping.thena
:load examples/poplmark/05-typing.thena
:load examples/poplmark/06-transitivity.thena
```

| file | what it shows |
|---|---|
| `01-syntax` | Part 2's whole language. Two token classes, so types read `X` and terms read `x`; `Ty` with `⊤`, the arrow and the quantifier; `Tm` **binding at both levels in one grammar** — `λ x : T . t` binds a term variable and `Λ X <: T . t` a type variable. The generated substitutions, `Tm-subst-X` among them: type substitution into a term |
| `02-contexts` | `Γ` with **two extension forms**, `x : T` and `X <: T`, and the two lookup relations that come with them; `append` given **the paper's comma** by a `notation` block, so `Γ , X <: Q , Δ` parses as a rule's index; `Ctx-subst-X` for `Γ[X -> T]` |
| `03-wellformed` | `X # Γ` and `Γ ⊢ T ty` and `⊢ Γ ok`: the laws the paper gets from its notation and we have to say out loud. `#` is a hand-written family given paper notation, because its last rule needs a side condition. Then the lemmas that make them work: inversion, and **rebinding** — nothing that only cares which names are declared can tell `Γ , X <: Q , Δ` from `Γ , X <: P , Δ` |
| `04-subtyping` | The five algorithmic subtyping rules, with **one premise added** to `SA-All`: `⊢ Γ , X <: T1 ok`. Derivations |
| `05-typing` | The six typing rules with subsumption. `T-TApp`'s conclusion is `T12[X -> T2]`, so the kernel computes the type of an instantiation rather than being told it |
| `06-transitivity` | **Problem 1A.** Reflexivity; inversion of subtyping on the shape of the lower type; narrowing in full; transitivity, all four cases of the induction on the middle type — **under one hypothesis, which is then refuted** |

## Why the rules are not quite the paper's

The paper's contexts are finite **functions**, so `Γ, X<:T` is notation that
only means something when `X` is new, and a context can never repeat a name.
Thena's context is a datatype and its comma is a constructor, so
`· , Y <: ⊤ , Y <: ⊤` is a value, and a lookup takes the newest entry. That is
a deliberate decision of this project — shadowing allowed, newest wins.

So the law has to be written down. `03` writes it, and `04` requires it at the
one rule that extends a context. Everything else is the paper's, unchanged.

## What is proved, and what stops it

Everything here is kernel-checked. The outer induction on the middle type is
complete — `transTop`, `transTVar`, `transArrow`, `transAll` — with
`narrowFrom` giving narrowing from transitivity at the same type, and
`transitivity` and `narrowing` assembled from them. `SA-All`'s new premise is
load-bearing: `narrowFrom` rebuilds the rule in the narrowed context and gets
the premise it needs by `okRebind`.

What is left is **plain weakening between well-formed contexts**:

```
Wk = \ Q -> forall (G : Ctx) (Xn : String) (D : Ctx) (P : Ty)
              (o : ok (append (bindTy G Xn P) D)) (dp : sub G P Q)
              -> sub (append (bindTy G Xn P) D) P Q
```

used in exactly one place — narrowing's `SA-Trans-TVar` case, where the variable
looked up is the one being narrowed.

**`wkIsFalse` refutes it, and not because of context hygiene.** Both contexts
below are well formed. What goes wrong is in the **derivation**: its own
quantifier binds `Z`, and the weakening declares `Z`.

```
· , B <: ⊤                           ⊢ ( ∀ Z <: ⊤ . Z ) <: ( ∀ Z <: ⊤ . ⊤ )   bindsZ
· , B <: ⊤ , Z <: ( ∀ Z <: ⊤ . Z )   ⊢ ( ∀ Z <: ⊤ . Z ) <: ( ∀ Z <: ⊤ . ⊤ )   noBindsZ
```

The first holds: `SA-All`'s premise asks that `· , B <: ⊤ , Z <: ⊤` be well
formed, and it is. The second cannot: `SA-All` would ask that
`· , B <: ⊤ , Z <: ( ∀ Z <: ⊤ . Z ) , Z <: ⊤` be well formed, and `Z` is
declared twice. No other rule can conclude it.

**This is the step α-equivalence exists to take** — rename the bound variable
and the obstruction is gone. Thena is nominal by design: a bound name is a
`String` field and changing it changes the type. So 1A's last step is not a
missing lemma about contexts; it is the renaming the system does not have.

## Not here

Problem **1B** (records) needs variable-arity productions; **2A** (type safety)
needs reduction and the term-substitution lemmas; **2B** needs record patterns;
**3** (animation) is a non-goal. `.jalivert/POPLMARK.md` has the gap analysis.
