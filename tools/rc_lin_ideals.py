#!/usr/bin/env python3
"""Check Campion's Lemma 3.2 in the form r9 Response 15 uses (§7.14).

For every naturally labelled poset P on at most MAXN elements:
  * Lin(P), the non-codiscrete linear preorders refining P (ordered
    surjections of P onto 1 < ... < r, r >= 2, with a < b in P implying
    rank(a) <= rank(b)), is in bijection with the nonempty chains of
    nonempty PROPER downsets of P (L -> E1 ⊂ E1∪E2 ⊂ ...).  The paper's
    Definition of DC(P) says only "nonempty"; including P itself would break
    the bijection, which this script also confirms.
  * For P not discrete, I -> I ∩ Min(P) maps nonempty proper downsets to
    nonempty proper downsets, is monotone, below the identity and below
    the constant Min(P) (Arone's coreflection; the zigzag of Response 15).

Note the refinement direction: a linear preorder L refines P when a <=_P b
implies a <=_L b.
"""
import itertools, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from rc_collapse import naturally_labelled_posets

MAXN = int(sys.argv[1]) if len(sys.argv) > 1 else 5

def downsets(n, rel):
    out = []
    for bits in range(1 << n):
        S = frozenset(i for i in range(n) if bits >> i & 1)
        if all(a in S for (a, b) in rel if b in S):
            out.append(S)
    return out

def lin(n, rel):
    res = 0
    for r in range(2, n + 1):
        for f in itertools.product(range(r), repeat=n):
            if set(f) != set(range(r)):
                continue
            # refines P: a < b in P implies f(a) <= f(b)
            if all(f[a] <= f[b] for (a, b) in rel):
                res += 1
    return res

def chains(sets):
    sets = sorted(sets, key=len)
    cnt = 0
    def rec(last, i):
        nonlocal cnt
        for j in range(i, len(sets)):
            if last < sets[j]:
                cnt += 1
                rec(sets[j], j + 1)
    for j, s in enumerate(sets):
        cnt += 1
        rec(s, j + 1)
    return cnt

total = 0
for n in range(1, MAXN + 1):
    for rel in naturally_labelled_posets(n):
        D = downsets(n, rel)
        full = frozenset(range(n))
        T = [S for S in D if S and S != full]
        L = lin(n, rel)
        assert L == chains(T), (n, rel)
        if n >= 2:
            assert L != chains([S for S in D if S]), "including P would also match?"
        Min = frozenset(i for i in range(n) if not any(b == i for (a, b) in rel))
        if Min != full:
            for I in T:
                c = I & Min
                assert c in T and c <= I and c <= Min
                for J in T:
                    if I <= J:
                        assert (I & Min) <= (J & Min)
        total += 1
print(f"{total} posets ok: |Lin(P)| = #chains of nonempty proper downsets; "
      "I -> I ∩ Min is a coreflecting zigzag")
