"""Stong dismantling of the poset of compatible ordered antichain partitions.

For a finite poset P, Pi(P) is the set of ordered partitions B_1 | ... | B_r of P
into nonempty antichains such that a < b in P implies block(a) < block(b),
ordered by refinement (pi <= sigma iff sigma refines pi).  Pi(P) is the poset
of serializations of a strict 2-cell with event poset P (notes/hpol-obligations.md).

Claim checked here (Lemma D of the note): for m a maximal element of P, removing
the elements outside Q_m = {pi : last block is {m}} in the order of the key
    (-e(pi), shared before alone, shared: finer first, alone: coarser first),
where e(pi) is the number of elements in blocks after the block of m, removes a
beat point at every step: an up-beat point with partner  ...|B\\{m}|{m}|...  when
m shares its block B, and a down-beat point with partner  ...|{m} u B_{i+1}|...
when m is alone in a non-final block.  Q_m is isomorphic to Pi(P - m), so by
induction Pi(P) dismantles to a point.

Usage: python3 tools/order_partition_dismantle.py <seed> <trials> [maxn]
"""
import itertools, random, sys

def rand_poset(n, p, rng):
    lt = {(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p}
    changed = True
    while changed:
        changed = False
        for (a, b) in list(lt):
            for (c, d) in list(lt):
                if b == c and (a, d) not in lt:
                    lt.add((a, d)); changed = True
    return lt

def ordered_partitions(n, lt):
    res = []
    def rec(rem, seq, placed):
        if not rem:
            res.append(tuple(seq)); return
        rem_s = sorted(rem)
        for k in range(1, len(rem_s) + 1):
            for B in itertools.combinations(rem_s, k):
                if any((a, b) in lt for a in B for b in B): continue
                if any((a, b) in lt and a not in placed for b in B for a in range(n)): continue
                rec(rem - set(B), seq + [frozenset(B)], placed | set(B))
    rec(set(range(n)), [], set())
    return res

def refines(s, p):
    i = 0
    for B in p:
        acc = set()
        while acc != B:
            if i >= len(s) or not s[i] <= B: return False
            acc |= s[i]; i += 1
    return i == len(s)

def le(a, b):            # a <= b  iff  b refines a
    return refines(b, a)

def block_of(p, m):
    return next(j for j, B in enumerate(p) if m in B)

def key(p, m):
    i = block_of(p, m)
    alone = len(p[i]) == 1
    e = sum(len(B) for B in p[i + 1:])
    return (-e, 1 if alone else 0, len(p) if alone else -len(p))

def partner(p, m):
    i = block_of(p, m)
    if len(p[i]) > 1:
        return p[:i] + (p[i] - {m}, frozenset([m])) + p[i + 1:], 'up'
    return p[:i] + (p[i] | p[i + 1],) + p[i + 2:], 'down'

def check(n, lt):
    m = max(x for x in range(n) if not any((x, b) in lt for b in range(n)))
    E = set(ordered_partitions(n, lt))
    for x in sorted((p for p in E if p[-1] != frozenset([m])), key=lambda p: key(p, m)):
        y, kind = partner(x, m)
        if y not in E: return False
        if kind == 'up':
            ok = all(le(y, z) for z in E if z != x and le(x, z))
        else:
            ok = all(le(z, y) for z in E if z != x and le(z, x))
        if not ok: return False
        E.discard(x)
    return all(p[-1] == frozenset([m]) for p in E)

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    maxn = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    rng = random.Random(seed); bad = 0
    for _ in range(trials):
        n = rng.randint(1, maxn); lt = rand_poset(n, rng.random(), rng)
        if not check(n, lt):
            bad += 1; print('FAIL', n, sorted(lt))
    print('posets', trials, 'failures', bad)
