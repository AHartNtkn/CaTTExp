#!/usr/bin/env python3
"""Explicit collapse of the antichain-block complex X(P) (relative-coherence.md §7.12).

X(P): faces of the permutohedron on the events of a finite poset P whose
vertices are all linear extensions of P.  A face is an ordered partition
(B_1, ..., B_r) of the events into antichains such that a < b in P implies
block(a) < block(b).  Its dimension is sum(|B_i| - 1).  Facets: split one
block B into an ordered pair (A, B minus A) of nonempty sets.

Matching M (L0 = the natural order 0 < 1 < ... < N-1, a linear extension):
  * tail(F) = the longest suffix of F of the form ({j}, {j+1}, ..., {N-1});
    F' = F with the tail removed, a face of X(P restricted to {0..m}).
  * If F' is empty then F = L0 and F is critical.
  * Otherwise z = m (the L0-last event of F', maximal in P|{0..m}).
      - z in a block B with |B| > 1:  F is matched DOWN with
        (..., {z}, B - z, ...).
      - z a singleton block of F' (never the last block of F'):  F is
        matched UP with the face merging {z} and the next block.

The script checks, for every naturally labelled poset on at most MAXN
elements:
  1. every face is an ordered antichain partition, and the dimension
     bound (blocks of a k-face have at most k+1 events) holds;
  2. M is a well-defined involution pairing each face with a facet or a
     cofacet, with merged and split faces still in X(P);
  3. the measure (tail length, number of events before z) strictly
     increases lexicographically along every V-path step;
  4. M is acyclic (the modified Hasse diagram is a DAG);
  5. L0 is the only critical cell.
By Forman's discrete Morse theory (X(P) is a regular CW complex: a
polyhedral subcomplex of the permutohedron), 4 and 5 say X(P) collapses
to the vertex L0.
"""
import itertools
import sys

MAXN = int(sys.argv[1]) if len(sys.argv) > 1 else 6


def naturally_labelled_posets(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for bits in range(1 << len(pairs)):
        rel = {pairs[t] for t in range(len(pairs)) if bits >> t & 1}
        if all((i, k) in rel for (i, j) in rel for (j2, k) in rel if j == j2):
            yield rel


def ordered_partitions(s):
    s = list(s)
    if not s:
        yield ()
        return
    for r in range(1, len(s) + 1):
        for first in itertools.combinations(s, r):
            rest = [x for x in s if x not in first]
            for tail in ordered_partitions(rest):
                yield (frozenset(first),) + tail


def is_face(F, rel):
    pos = {e: i for i, B in enumerate(F) for e in B}
    return all(pos[a] < pos[b] for (a, b) in rel)  # also forces antichains


def dim(F):
    return sum(len(B) - 1 for B in F)


def tail_split(F, n):
    t, j = 0, n - 1
    while t < len(F) and F[len(F) - 1 - t] == frozenset([j]):
        t += 1
        j -= 1
    return F[:len(F) - t], t


def partner(F, n):
    """Return (partner face, 'up'|'down') or None if critical."""
    Fp, t = tail_split(F, n)
    if not Fp:
        return None
    z = n - t - 1
    i = next(i for i, B in enumerate(Fp) if z in B)
    B = Fp[i]
    if len(B) > 1:
        G = F[:i] + (frozenset([z]), B - {z}) + F[i + 1:]
        return G, 'down'
    assert i + 1 < len(Fp), "z is never the last block of F'"
    G = F[:i] + (B | F[i + 1],) + F[i + 2:]
    return G, 'up'


def measure(F, n):
    Fp, t = tail_split(F, n)
    if not Fp:
        return (t, -1)
    z = n - t - 1
    i = next(i for i, B in enumerate(Fp) if z in B)
    return (t, sum(len(B) for B in Fp[:i]))


def facets(F):
    for i, B in enumerate(F):
        if len(B) < 2:
            continue
        L = sorted(B)
        for r in range(1, len(L)):
            for A in itertools.combinations(L, r):
                A = frozenset(A)
                yield F[:i] + (A, B - A) + F[i + 1:]


def check(n, rel):
    faces = [F for F in ordered_partitions(range(n)) if is_face(F, rel)]
    fs = set(faces)
    L0 = tuple(frozenset([i]) for i in range(n))
    match, crit = {}, []
    for F in faces:
        k = dim(F)
        assert all(len(B) <= k + 1 for B in F)
        p = partner(F, n)
        if p is None:
            crit.append(F)
            continue
        G, d = p
        assert G in fs, (F, G)
        assert dim(G) == k + (1 if d == 'up' else -1)
        if d == 'up':
            assert F in set(facets(G))
        else:
            assert G in set(facets(F))
        match[F] = G
    for F, G in match.items():
        assert match[G] == F
    assert crit == [L0], crit
    # V-path steps: sigma (matched up to tau) -> other facet sigma' of tau
    # that is itself matched up.  Measure must strictly increase.
    succ = {F: [] for F in faces}
    for F in faces:
        for S in facets(F):
            if match.get(S) == F:
                succ[S].append(F)          # matched edge goes up
            else:
                succ[F].append(S)          # other edges go down
        if F in match and dim(match[F]) == dim(F) + 1:
            tau = match[F]
            for S in facets(tau):
                if S != F and S in match and dim(match[S]) == dim(S) + 1:
                    assert measure(S, n) > measure(F, n), (F, tau, S)
    # acyclicity of the modified Hasse diagram (Kahn's algorithm)
    indeg = {F: 0 for F in faces}
    for F in faces:
        for G in succ[F]:
            indeg[G] += 1
    stack = [F for F in faces if indeg[F] == 0]
    seen = 0
    while stack:
        F = stack.pop()
        seen += 1
        for G in succ[F]:
            indeg[G] -= 1
            if indeg[G] == 0:
                stack.append(G)
    assert seen == len(faces), "cycle in modified Hasse diagram"
    return len(faces)


def main():
    total_posets = total_faces = 0
    for n in range(1, MAXN + 1):
        cnt = 0
        for rel in naturally_labelled_posets(n):
            total_faces += check(n, rel)
            cnt += 1
        total_posets += cnt
        print(f"n={n}: {cnt} posets ok", flush=True)
    print(f"all {total_posets} posets ok ({total_faces} faces): "
          "matching valid, acyclic, measure increases, single critical cell L0")


if __name__ == "__main__":
    main()
