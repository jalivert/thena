BASE = r'''data Term : Type₀ where { true : Term ; false : Term ; ifthen : Term -> Term -> Term -> Term ; zero : Term ; succ : Term -> Term ; pred : Term -> Term ; iszero : Term -> Term }
data NV : Term -> Type₀ where { nvZero : NV zero ; nvSucc : ∀ (t : Term) (n : NV t) -> NV (succ t) }
data Step : Term -> Term -> Type₀ where { eIfTrue : ∀ (t2 : Term) (t3 : Term) -> Step (ifthen true t2 t3) t2 ; eIfFalse : ∀ (t2 : Term) (t3 : Term) -> Step (ifthen false t2 t3) t3 ; eIf : ∀ (t1 : Term) (t1' : Term) (t2 : Term) (t3 : Term) (s : Step t1 t1') -> Step (ifthen t1 t2 t3) (ifthen t1' t2 t3) ; eSucc : ∀ (t1 : Term) (t1' : Term) (s : Step t1 t1') -> Step (succ t1) (succ t1') ; ePredZero : Step (pred zero) zero ; ePredSucc : ∀ (v : Term) (nv : NV v) -> Step (pred (succ v)) v ; ePred : ∀ (t1 : Term) (t1' : Term) (s : Step t1 t1') -> Step (pred t1) (pred t1') ; eIsZeroZero : Step (iszero zero) true ; eIsZeroSucc : ∀ (v : Term) (nv : NV v) -> Step (iszero (succ v)) false ; eIsZero : ∀ (t1 : Term) (t1' : Term) (s : Step t1 t1') -> Step (iszero t1) (iszero t1') }
:theorem absurd : ∀ (C : Type₀) (e : Empty {0}) -> C
try (\ (C : Type₀) (e : Empty {0}) -> elim Empty {0} () (\ (t : Empty {0}) -> C) () () e)
solve
qed
:theorem sym : ∀ (A : Type₀) (a : A) (b : A) (e : Eq {0} A a b) -> Eq {0} A b a
attack
intro
intro
intro
intro
into
along
along
along
along
eliminate e
back
try (\ (c : A) -> refl {0} A c)
solve
along
solve
back
back
back
back
back
back
solve
qed
:theorem subst : ∀ (A : Type₀) (P : A -> Type₀) (a : A) (b : A) (e : Eq {0} A a b) -> P a -> P b
attack
intro
intro
intro
intro
intro
into
along
along
along
along
along
eliminate e
back
try (\ (c : A) (h : P c) -> h)
solve
along
solve
back
back
back
back
back
back
back
solve
qed
:theorem cong : ∀ (A : Type₀) (B : Type₀) (f : A -> B) (a : A) (b : A) (e : Eq {0} A a b) -> Eq {0} B (f a) (f b)
attack
intro
intro
intro
intro
intro
intro
into
along
along
along
along
along
along
eliminate e
back
try (\ (c : A) -> refl {0} B (f c))
solve
along
solve
back
back
back
back
back
back
back
back
solve
qed
:theorem trans : ∀ (A : Type₀) (a : A) (b : A) (c : A) (e : Eq {0} A a b) -> Eq {0} A b c -> Eq {0} A a c
attack
intro
intro
intro
intro
intro
into
along
along
along
along
along
eliminate e
back
try (\ (z : A) (h : Eq {0} A z c) -> h)
solve
along
solve
back
back
back
back
back
back
back
solve
qed
'''

#!/usr/bin/env python3
"""Regenerates examples/determinacy.thena — MS1's target (§9, phase 18).

    python3 examples/determinacy.thena.py > examples/determinacy.thena

The file it writes is the artifact; this is here so that a change to the
elimination tactic does not leave 1190 lines of REPL script to re-derive by
hand.  What it knows is the ten rules of TAPL's one-step evaluation relation
(STEP), the statement of each lemma (LEMMAS), and how to close a branch that is
not a constructor clash (the 'fin' tables) — the clashes it works out itself,
which is 110 of the 130 branches.
"""

import itertools, sys


def C(n, *a): return ('c', n, list(a))
def V(n):     return ('v', n)
def pp(t, top=True):
    if t[0] == 'v' or not t[2]: return t[1]
    s = t[1] + " " + " ".join(pp(x, False) for x in t[2])
    return s if top else "(" + s + ")"

STEP = [
  dict(n="eIfTrue",  tel=[("c1","Term"),("c2","Term")],
       lhs=C("ifthen", C("true"), V("c1"), V("c2")), rhs=V("c1"), rec=False),
  dict(n="eIfFalse", tel=[("c1","Term"),("c2","Term")],
       lhs=C("ifthen", C("false"), V("c1"), V("c2")), rhs=V("c2"), rec=False),
  dict(n="eIf",      tel=[("c1","Term"),("c2","Term"),("c3","Term"),("c4","Term")],
       lhs=C("ifthen", V("c1"), V("c3"), V("c4")),
       rhs=C("ifthen", V("c2"), V("c3"), V("c4")), rec=True),
  dict(n="eSucc",    tel=[("c1","Term"),("c2","Term")],
       lhs=C("succ", V("c1")), rhs=C("succ", V("c2")), rec=True),
  dict(n="ePredZero", tel=[], lhs=C("pred", C("zero")), rhs=C("zero"), rec=False),
  dict(n="ePredSucc", tel=[("c1","Term"),("nv1","NV c1")],
       lhs=C("pred", C("succ", V("c1"))), rhs=V("c1"), rec=False),
  dict(n="ePred",    tel=[("c1","Term"),("c2","Term")],
       lhs=C("pred", V("c1")), rhs=C("pred", V("c2")), rec=True),
  dict(n="eIsZeroZero", tel=[], lhs=C("iszero", C("zero")), rhs=C("true"), rec=False),
  dict(n="eIsZeroSucc", tel=[("c1","Term"),("nv1","NV c1")],
       lhs=C("iszero", C("succ", V("c1"))), rhs=C("false"), rec=False),
  dict(n="eIsZero",  tel=[("c1","Term"),("c2","Term")],
       lhs=C("iszero", V("c1")), rhs=C("iszero", V("c2")), rec=True),
]

# The conjunction NoConfusionTerm builds for a constructor with several
# arguments: right-nested And {0}, and Unit {0} when there is nothing to conjoin.
# Must agree with Thena.Global.NoConfusion.conjoin exactly.
def conj(ts):
    if not ts: return "Unit {0}"
    if len(ts) == 1: return ts[0]
    return "And {0} (%s) (%s)" % (ts[0], conj(ts[1:]))

# One projection out of that nest per conjunct. The last is the residue itself,
# because conj stops wrapping at one element.
def projections(nc, eqs):
    out, rest = [], "(%s)" % nc
    for i in range(len(eqs) - 1):
        tail = conj(eqs[i+1:])
        out.append("(andLeft (%s) (%s) %s)" % (eqs[i], tail, rest))
        rest = "(andRight (%s) (%s) %s)" % (eqs[i], tail, rest)
    out.append(rest)
    return out

def compose(ps, body):
    for p in reversed(ps): body = p % body
    return body

def decompose(a, b, q, goal, ctr):
    ps, work, leaves = [], [(a, b, q)], []
    while work:
        x, y, qq = work.pop(0)
        if x[0] == 'c' and y[0] == 'c':
            if x[1] != y[1]:
                # NoConfusionTerm at two different formers computes to Empty {0},
                # so discrimination is absurd rather than a continuation.
                return (compose(ps, "absurd (%s) (noConfusionTerm %s %s %s)"
                                    % (goal, pp(x,0), pp(y,0), qq)), None)
            if not x[2]: continue
            eqs, binders, sub = [], [], []
            for (l, r) in zip(x[2], y[2]):
                e = "e%d" % next(ctr)
                ty = "Eq {0} Term %s %s" % (pp(l, False), pp(r, False))
                eqs.append(ty)
                binders.append("(%s : %s)" % (e, ty))
                sub.append((l, r, e))
            # The lemma now hands back the conjunction itself. Bind it once,
            # then feed the argument equations in by projection.
            nc = "nc%d" % next(ctr)
            ps.append("(\\ (%s : %s) -> (\\ %s -> %%s) %s) (noConfusionTerm %s %s %s)"
                      % (nc, conj(eqs), " ".join(binders),
                         " ".join(projections(nc, eqs)),
                         pp(x,0), pp(y,0), qq))
            work = sub + work
        else:
            leaves.append((pp(x), pp(y), qq))
    return (ps, leaves)

def eq(leaves, a, b):
    for (x, y, q) in leaves:
        if x == a and y == b: return q
    raise KeyError((a, b, leaves))

def transport(to, frm, dst, proof, term):
    return ("subst Term (\\ (x : Term) -> Step x %s) %s %s (%s) (%s)"
            % (to, frm, dst, proof, term))

def chain(steps):
    a, b, p = steps[-1]
    proof, end = p, b
    for (a2, b2, p2) in reversed(steps[:-1]):
        proof = "trans Term (%s) (%s) (%s) (%s) (%s)" % (a2, b2, end, p2, proof)
    return proof

def congs(head, left, right, proofs):
    """Eq {0} Term (head left) (head right), one argument at a time."""
    render = lambda xs: head % tuple(xs)
    steps, cur = [], list(left)
    for i, (l, r, pr) in enumerate(zip(left, right, proofs)):
        nxt = list(cur); nxt[i] = r
        hole = head % tuple(cur[:i] + ["x"] + cur[i+1:])
        steps.append((render(cur), render(nxt),
                      "cong Term Term (\\ (x : Term) -> %s) %s %s (%s)" % (hole, l, r, pr)))
        cur = nxt
    return chain(steps)


# One entry per inversion lemma: the statement, how many binders to introduce
# before eliminating, the left index the target is at, and the goal as a
# function of the right index.
LEMMAS = []
def lemma(name, ty, intros, target, left, goal, fin):
    LEMMAS.append(dict(n=name, ty=ty, intros=intros, tgt=target, L=left, goal=goal, fin=fin))

A = "Term"

# ---- values do not step ---------------------------------------------------
lemma("trueNoStep",  "∀ (u : Term) (s : Step true u) -> Empty {0}", ["u","s"], "s",
      C("true"), lambda y: "Empty {0}", {})
lemma("falseNoStep", "∀ (u : Term) (s : Step false u) -> Empty {0}", ["u","s"], "s",
      C("false"), lambda y: "Empty {0}", {})
lemma("zeroNoStep",  "∀ (u : Term) (s : Step zero u) -> Empty {0}", ["u","s"], "s",
      C("zero"), lambda y: "Empty {0}", {})
lemma("succNoStep",
      "∀ (w : Term) (ih0 : ∀ (u : Term) (s : Step w u) -> Empty {0}) (u : Term) "
      "(s : Step (succ w) u) -> Empty {0}",
      ["w","ih0","u","s"], "s", C("succ", V("w")), lambda y: "Empty {0}",
      {"eSucc": lambda lv, g: "ih0 c2 (%s)" % transport("c2","c1","w",eq(lv,"c1","w"),"sr")})

# ---- the ten inversions ---------------------------------------------------
lemma("invIfTrue",
      "∀ (a : Term) (b : Term) (u : Term) (s : Step (ifthen true a b) u) -> Eq {0} Term a u",
      ["a","b","u","s"], "s", C("ifthen", C("true"), V("a"), V("b")),
      lambda y: "Eq {0} Term a %s" % y,
      {"eIfTrue": lambda lv, g: "sym Term c1 a %s" % eq(lv,"c1","a"),
       "eIf":     lambda lv, g: "absurd (%s) (trueNoStep c2 (%s))"
                    % (g, transport("c2","c1","true",eq(lv,"c1","true"),"sr"))})

lemma("invIfFalse",
      "∀ (a : Term) (b : Term) (u : Term) (s : Step (ifthen false a b) u) -> Eq {0} Term b u",
      ["a","b","u","s"], "s", C("ifthen", C("false"), V("a"), V("b")),
      lambda y: "Eq {0} Term b %s" % y,
      {"eIfFalse": lambda lv, g: "sym Term c2 b %s" % eq(lv,"c2","b"),
       "eIf":      lambda lv, g: "absurd (%s) (falseNoStep c2 (%s))"
                     % (g, transport("c2","c1","false",eq(lv,"c1","false"),"sr"))})

lemma("invIf",
      "∀ (p : Term) (p' : Term) (a : Term) (b : Term) (s0 : Step p p') "
      "(ih0 : ∀ (w : Term) (sw : Step p w) -> Eq {0} Term p' w) (u : Term) "
      "(s : Step (ifthen p a b) u) -> Eq {0} Term (ifthen p' a b) u",
      ["p","p'","a","b","s0","ih0","u","s"], "s",
      C("ifthen", V("p"), V("a"), V("b")),
      lambda y: "Eq {0} Term (ifthen p' a b) %s" % y,
      {"eIfTrue":  lambda lv, g: "absurd (%s) (trueNoStep p' (%s))"
                     % (g, transport("p'","p","true","sym Term true p %s" % eq(lv,"true","p"),"s0")),
       "eIfFalse": lambda lv, g: "absurd (%s) (falseNoStep p' (%s))"
                     % (g, transport("p'","p","false","sym Term false p %s" % eq(lv,"false","p"),"s0")),
       "eIf":      lambda lv, g: congs("ifthen %s %s %s", ["p'","a","b"], ["c2","c3","c4"],
                     ["ih0 c2 (%s)" % transport("c2","c1","p",eq(lv,"c1","p"),"sr"),
                      "sym Term c3 a %s" % eq(lv,"c3","a"),
                      "sym Term c4 b %s" % eq(lv,"c4","b")])})

lemma("invSucc",
      "∀ (p : Term) (p' : Term) (s0 : Step p p') "
      "(ih0 : ∀ (w : Term) (sw : Step p w) -> Eq {0} Term p' w) (u : Term) "
      "(s : Step (succ p) u) -> Eq {0} Term (succ p') u",
      ["p","p'","s0","ih0","u","s"], "s", C("succ", V("p")),
      lambda y: "Eq {0} Term (succ p') %s" % y,
      {"eSucc": lambda lv, g: "cong Term Term (\\ (x : Term) -> succ x) p' c2 "
                              "(ih0 c2 (%s))" % transport("c2","c1","p",eq(lv,"c1","p"),"sr")})

lemma("invPredZero",
      "∀ (u : Term) (s : Step (pred zero) u) -> Eq {0} Term zero u",
      ["u","s"], "s", C("pred", C("zero")), lambda y: "Eq {0} Term zero %s" % y,
      {"ePredZero": lambda lv, g: "refl {0} Term zero",
       "ePred":     lambda lv, g: "absurd (%s) (zeroNoStep c2 (%s))"
                      % (g, transport("c2","c1","zero",eq(lv,"c1","zero"),"sr"))})

lemma("invPredSucc",
      "∀ (v : Term) (nv : NV v) (u : Term) (s : Step (pred (succ v)) u) -> Eq {0} Term v u",
      ["v","nv","u","s"], "s", C("pred", C("succ", V("v"))),
      lambda y: "Eq {0} Term v %s" % y,
      {"ePredSucc": lambda lv, g: "sym Term c1 v %s" % eq(lv,"c1","v"),
       "ePred":     lambda lv, g: "absurd (%s) (nvNoStep (succ v) (nvSucc v nv) c2 (%s))"
                      % (g, transport("c2","c1","(succ v)",eq(lv,"c1","succ v"),"sr"))})

lemma("invPred",
      "∀ (p : Term) (p' : Term) (s0 : Step p p') "
      "(ih0 : ∀ (w : Term) (sw : Step p w) -> Eq {0} Term p' w) (u : Term) "
      "(s : Step (pred p) u) -> Eq {0} Term (pred p') u",
      ["p","p'","s0","ih0","u","s"], "s", C("pred", V("p")),
      lambda y: "Eq {0} Term (pred p') %s" % y,
      {"ePredZero": lambda lv, g: "absurd (%s) (zeroNoStep p' (%s))"
                      % (g, transport("p'","p","zero","sym Term zero p %s" % eq(lv,"zero","p"),"s0")),
       "ePredSucc": lambda lv, g: "absurd (%s) (nvNoStep (succ c1) (nvSucc c1 nv1) p' (%s))"
                      % (g, transport("p'","p","(succ c1)",
                            "sym Term (succ c1) p %s" % eq(lv,"succ c1","p"),"s0")),
       "ePred":     lambda lv, g: "cong Term Term (\\ (x : Term) -> pred x) p' c2 "
                                  "(ih0 c2 (%s))" % transport("c2","c1","p",eq(lv,"c1","p"),"sr")})

lemma("invIsZeroZero",
      "∀ (u : Term) (s : Step (iszero zero) u) -> Eq {0} Term true u",
      ["u","s"], "s", C("iszero", C("zero")), lambda y: "Eq {0} Term true %s" % y,
      {"eIsZeroZero": lambda lv, g: "refl {0} Term true",
       "eIsZero":     lambda lv, g: "absurd (%s) (zeroNoStep c2 (%s))"
                        % (g, transport("c2","c1","zero",eq(lv,"c1","zero"),"sr"))})

lemma("invIsZeroSucc",
      "∀ (v : Term) (nv : NV v) (u : Term) (s : Step (iszero (succ v)) u) -> Eq {0} Term false u",
      ["v","nv","u","s"], "s", C("iszero", C("succ", V("v"))),
      lambda y: "Eq {0} Term false %s" % y,
      {"eIsZeroSucc": lambda lv, g: "refl {0} Term false",
       "eIsZero":     lambda lv, g: "absurd (%s) (nvNoStep (succ v) (nvSucc v nv) c2 (%s))"
                        % (g, transport("c2","c1","(succ v)",eq(lv,"c1","succ v"),"sr"))})

lemma("invIsZero",
      "∀ (p : Term) (p' : Term) (s0 : Step p p') "
      "(ih0 : ∀ (w : Term) (sw : Step p w) -> Eq {0} Term p' w) (u : Term) "
      "(s : Step (iszero p) u) -> Eq {0} Term (iszero p') u",
      ["p","p'","s0","ih0","u","s"], "s", C("iszero", V("p")),
      lambda y: "Eq {0} Term (iszero p') %s" % y,
      {"eIsZeroZero": lambda lv, g: "absurd (%s) (zeroNoStep p' (%s))"
                        % (g, transport("p'","p","zero","sym Term zero p %s" % eq(lv,"zero","p"),"s0")),
       "eIsZeroSucc": lambda lv, g: "absurd (%s) (nvNoStep (succ c1) (nvSucc c1 nv1) p' (%s))"
                        % (g, transport("p'","p","(succ c1)",
                              "sym Term (succ c1) p %s" % eq(lv,"succ c1","p"),"s0")),
       "eIsZero":     lambda lv, g: "cong Term Term (\\ (x : Term) -> iszero x) p' c2 "
                                    "(ih0 c2 (%s))" % transport("c2","c1","p",eq(lv,"c1","p"),"sr")})


def arg(t): return pp(t, False)

def branch(lem, ct):
    goal = lem['goal'](arg(ct['rhs']))
    bs = list(ct['tel'])
    if ct['rec']:
        bs.append(("sr", "Step c1 c2"))
        bs.append(("ih", "Eq {0} Term c1 %s -> %s" % (arg(lem['L']), lem['goal']("c2"))))
    bs.append(("q", "Eq {0} Term %s %s" % (arg(ct['lhs']), arg(lem['L']))))
    res, leaves = decompose(ct['lhs'], lem['L'], 'q', goal, itertools.count(1))
    body = res if leaves is None else compose(res, lem['fin'][ct['n']](leaves, goal))
    return "\\ %s -> %s" % (" ".join("(%s : %s)" % b for b in bs), body)

def proof(name, ty, intros, tgt, bodies):
    m, k = len(bodies), len(intros)
    out = [":theorem %s : %s" % (name, ty), "attack"]
    out += ["intro"] * k + ["into"] + ["along"] * k + ["eliminate " + tgt]
    out += ["back"] * m
    for b in bodies:
        out += ["try (" + b + ")", "solve", "along"]
    out += ["solve"] + ["back"] * (1 + k + m) + ["solve", "qed"]
    return out

def lemma_script(lem):
    return proof(lem['n'], lem['ty'], lem['intros'], lem['tgt'],
                 [branch(lem, ct) for ct in STEP])

DET_TY = ("∀ (t : Term) (t1 : Term) (s1 : Step t t1) (t2 : Term) (s2 : Step t t2) "
          "-> Eq {0} Term t1 t2")
DET = {
 "eIfTrue":     "invIfTrue c1 c2",
 "eIfFalse":    "invIfFalse c1 c2",
 "eIf":         "invIf c1 c2 c3 c4 sr ih",
 "eSucc":       "invSucc c1 c2 sr ih",
 "ePredZero":   "invPredZero",
 "ePredSucc":   "invPredSucc c1 nv1",
 "ePred":       "invPred c1 c2 sr ih",
 "eIsZeroZero": "invIsZeroZero",
 "eIsZeroSucc": "invIsZeroSucc c1 nv1",
 "eIsZero":     "invIsZero c1 c2 sr ih",
}

def det_branch(ct):
    bs = list(ct['tel'])
    if ct['rec']:
        bs.append(("sr", "Step c1 c2"))
        bs.append(("ih", "∀ (u : Term) -> Step c1 u -> Eq {0} Term c2 u"))
    bs.append(("u", "Term"))
    bs.append(("s", "Step %s u" % arg(ct['lhs'])))
    return "\\ %s -> %s u s" % (" ".join("(%s : %s)" % b for b in bs), DET[ct['n']])

NV_SCRIPT = proof("nvNoStep",
  "∀ (v : Term) (nv : NV v) (u : Term) (s : Step v u) -> Empty {0}", ["v","nv"], "nv",
  ["\\ (u : Term) (s : Step zero u) -> zeroNoStep u s",
   "\\ (c1 : Term) (n : NV c1) (ih : ∀ (u : Term) -> Step c1 u -> Empty {0}) "
   "(u : Term) (s : Step (succ c1) u) -> succNoStep c1 ih u s"])

if __name__ == "__main__":
    print(BASE, end="")
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    lines = []
    for lem in LEMMAS:
        if which in ("all", lem['n']): lines += lemma_script(lem)
        if lem['n'] == "succNoStep" and which in ("all", "nvNoStep"):
            lines += NV_SCRIPT
    if which in ("all", "determinacy"):
        lines += proof("determinacy", DET_TY, ["t","t1","s1"], "s1",
                       [det_branch(ct) for ct in STEP])
    print("\n".join(lines))
