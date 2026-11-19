#!/usr/bin/env python3
"""
4-endomorphisms of F_T(Gamma) (and of F_T(Gamma)/(C)) for
Gamma = Sigma[m] v Sigma[n], through global dimension 4.

Source: notes/conjectures/answered/lax-interchange-every-dimension-r2-2026-11-19.md
(the r2 response, sections 2-5, and its verification). Under T's raw support
equations every 4-endomorphism is idempotent, so any two non-identity
4-endomorphisms X : u => u, Y : v => v with u, v composable along a 2-cell
give an elementary interchanger chi_{2,3}(X,X,Y,Y) with an identity reverse.
This script lists such pairs, before and after imposing (C) H = 1.

Model (all words chronological; one hom, from f_0 g_0 to f_m g_n):
  2-cells  words: shuffles of a_1..a_m and b_1..b_n.
  3-cells  paths of elementary crossings chi(a_i, b_j) : b_j a_i => a_i b_j,
           modulo T's outer composite-crossing equations (7) in every context:
           every recursive expansion of a block chi(A, B) (A, B contiguous
           runs, B immediately before A) is the same 3-cell.
           (r, t and tau need a varying 3-cell inside one factor or a third
           factor, so they are identities here.)
  4-cells  paths of contextual generators [p | x iota(F, G) y | q] (F on the
           left interval, G on the right, "right first => left first"),
           F, G nonidentity 3-cells, modulo
             - the restricted composition laws (20)-(21): iota(F1;F2, G) and
               iota(F, G1;G2) split when the other argument is a literal chi
               term (a block chi(A, B), any expansion);
             - T's support equations: parallel 4-paths with the same set of
               (irreducible) contextual edges are equal;
             - optionally (C): [p | H(A1,A2;B1,B2) | q] = 1 for all
               consecutive nonempty blocks, all contexts, where
               H = [B1 chi(A1,B2) A2 | iota(chi(A1,B1), chi(A2,B2)) | A1 chi(A2,B1) B2].
           Whiskering by 2-cells and the balancing equations are built in:
           generators are identified by positions in the full word.

A 4-cell from c to c' is an equivalence class of edge sets of paths c -> c'
(support equations); the other equations are closed under pre- and
post-composition by computing on all (c, c', E) triples.

Usage: t_endomorphisms.py [m n] ...   (default: 1 1, 1 2, 2 2, 1 3, 2 3, 2 4, 3 3)
"""
import sys
from itertools import combinations
from functools import lru_cache


def words(m, n):
    out = []
    for pos in combinations(range(m + n), m):
        w, i, j = [], 0, 0
        for k in range(m + n):
            if k in pos:
                i += 1; w.append(('a', i))
            else:
                j += 1; w.append(('b', j))
        out.append(tuple(w))
    return out


def apply(w, pr):
    """apply chi(a_i, b_j): requires b_j immediately before a_i."""
    i, j = pr
    k = w.index(('b', j))
    if k + 1 < len(w) and w[k + 1] == ('a', i):
        w = list(w); w[k], w[k + 1] = w[k + 1], w[k]
        return tuple(w)
    return None


def run(w, seq):
    for pr in seq:
        w = apply(w, pr)
        if w is None:
            return None
    return w


@lru_cache(maxsize=None)
def expansions(A, B):
    """all recursive expansions of chi(A, B), A, B tuples of indices."""
    if len(A) == 1 and len(B) == 1:
        return frozenset({((A[0], B[0]),)})
    out = set()
    for k in range(1, len(A)):          # chi(A1A2,B) = chi(A1,B)A2 ; A1chi(A2,B)
        for e1 in expansions(A[:k], B):
            for e2 in expansions(A[k:], B):
                out.add(e1 + e2)
    for k in range(1, len(B)):          # chi(A,B1B2) = B1chi(A,B2) ; chi(A,B1)B2
        for e1 in expansions(A, B[k:]):
            for e2 in expansions(A, B[:k]):
                out.add(e1 + e2)
    return frozenset(out)


def blocks(w):
    """(A, B) with B a contiguous b-run immediately followed by a contiguous a-run."""
    out = []
    L = len(w)
    for k2 in range(L - 1):             # last b at k2, first a at k2+1
        if w[k2][0] != 'b' or w[k2 + 1][0] != 'a':
            continue
        k1 = k2
        while k1 > 0 and w[k1 - 1][0] == 'b':
            k1 -= 1
        k3 = k2 + 1
        while k3 + 1 < L and w[k3 + 1][0] == 'a':
            k3 += 1
        for s in range(k1, k2 + 1):
            for e in range(k2 + 1, k3 + 1):
                B = tuple(w[x][1] for x in range(s, k2 + 1))
                A = tuple(w[x][1] for x in range(k2 + 1, e + 1))
                out.append((A, B))
    return out


def scc(nodes, succ):
    """Tarjan, iterative; returns node -> component id."""
    index, low, comp, st, on = {}, {}, {}, [], set()
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ.get(root, [])))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        st.append(root); on.add(root)
        while work:
            v, it = work[-1]
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    st.append(w); on.add(w)
                    work.append((w, iter(succ.get(w, []))))
                    break
                elif w in on:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    while True:
                        w = st.pop(); on.discard(w); comp[w] = v
                        if w == v:
                            break
    return comp


class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        p = self.p
        p.setdefault(x, x)
        r = x
        while p[r] != r:
            r = p[r]
        while p[x] != r:
            p[x], x = r, p[x]
        return r

    def union(self, x, y):
        a, b = self.find(x), self.find(y)
        if a != b:
            self.p[a] = b


def analyse(m, n, impose_C, state_cap=3_000_000):
    W = words(m, n)
    # all 3-paths from every word
    paths = []
    def dfs(P, w, seq):
        paths.append((P, seq))
        for k in range(len(w) - 1):
            if w[k][0] == 'b' and w[k + 1][0] == 'a':
                pr = (w[k + 1][1], w[k][1])
                dfs(P, apply(w, pr), seq + (pr,))
    for P in W:
        dfs(P, P, ())
    pathset = set(paths)

    # 3-cell classes: composite-crossing equations in context
    uf3 = UF()
    for (P, seq) in paths:
        uf3.find((P, seq))
        w = P
        for t in range(len(seq) + 1):
            for (A, B) in blocks(w):
                ex = expansions(A, B)
                L = len(A) * len(B)
                if L >= 2 and seq[t:t + L] in ex:
                    for e in ex:
                        uf3.union((P, seq), (P, seq[:t] + e + seq[t + L:]))
            if t < len(seq):
                w = apply(w, seq[t])
    cls = lambda P, seq: uf3.find((P, seq))

    literal = set()
    for P in W:
        for (A, B) in blocks(P):
            for e in expansions(A, B):
                literal.add(cls(P, e))

    def left_right_ok(S, G, F):
        lettersG = {('a', i) for i, j in G} | {('b', j) for i, j in G}
        lettersF = {('a', i) for i, j in F} | {('b', j) for i, j in F}
        posG = [S.index(x) for x in lettersG]
        posF = [S.index(x) for x in lettersF]
        return max(posF) < min(posG)

    def key(P, p, G, F, q):
        S = run(P, p)
        S2 = run(S, G + F)
        return (cls(P, p), S, cls(S, F), cls(S, G), cls(S2, q))

    def src_tgt(P, p, G, F, q):
        return cls(P, p + G + F + q), cls(P, p + F + G + q)

    def reducible(S, G, F):
        Fl, Gl = cls(S, F) in literal, cls(S, G) in literal
        return (Gl and len(F) >= 2) or (Fl and len(G) >= 2)

    # canonical expansion of a generator into irreducible edges
    memo = {}
    def expand(P, p, G, F, q):
        k = key(P, p, G, F, q)
        if k in memo:
            return memo[k]
        S = run(P, p)
        if not reducible(S, G, F):
            res = (k,)
        elif cls(S, G) in literal and len(F) >= 2:
            F1, F2 = F[:1], F[1:]
            res = expand(P, p, G, F1, F2 + q) + expand(P, p + F1, G, F2, q)
        else:
            G1, G2 = G[:1], G[1:]
            res = expand(P, p + G1, G2, F, q) + expand(P, p, G1, F, G2 + q)
        memo[k] = res
        return res

    edges = {}      # irreducible key -> (src, tgt)
    eqs = []        # (d1, d2, path1, path2)
    for (P, seq) in paths:
        r = len(seq)
        for t in range(r):
            S = run(P, seq[:t])
            for g in range(1, r - t):
                for f in range(1, r - t - g + 1):
                    p, G, F, q = seq[:t], seq[t:t + g], seq[t + g:t + g + f], seq[t + g + f:]
                    if not left_right_ok(S, G, F):
                        continue
                    if run(P, p + F + G + q) is None:
                        continue
                    s, tg = src_tgt(P, p, G, F, q)
                    if not reducible(S, G, F):
                        edges[key(P, p, G, F, q)] = (s, tg)
                        continue
                    canon = expand(P, p, G, F, q)
                    if cls(S, G) in literal:
                        for k in range(1, len(F)):
                            F1, F2 = F[:k], F[k:]
                            alt = expand(P, p, G, F1, F2 + q) + expand(P, p + F1, G, F2, q)
                            if alt != canon:
                                eqs.append((s, tg, canon, alt))
                    if cls(S, F) in literal:
                        for k in range(1, len(G)):
                            G1, G2 = G[:k], G[k:]
                            alt = expand(P, p + G1, G2, F, q) + expand(P, p, G1, F, G2 + q)
                            if alt != canon:
                                eqs.append((s, tg, canon, alt))
    # (C): H(A1,A2;B1,B2) = 1 in every context
    nC = 0
    if impose_C:
        by_end, by_start = {}, {}
        for (P, seq) in paths:
            by_end.setdefault(run(P, seq), []).append((P, seq))
            by_start.setdefault(P, []).append(seq)
        for S0 in W:
            for (A, B) in blocks(S0):
                if len(A) < 2 or len(B) < 2:
                    continue
                # need B1 B2 A1 A2 with B = B1B2, A = A1A2
                S3 = run(S0, next(iter(expansions(A, B))))
                for ka in range(1, len(A)):
                    for kb in range(1, len(B)):
                        A1, A2, B1, B2 = A[:ka], A[ka:], B[:kb], B[kb:]
                        p0 = next(iter(expansions(A1, B2)))
                        Gx = next(iter(expansions(A2, B2)))
                        Fx = next(iter(expansions(A1, B1)))
                        q0 = next(iter(expansions(A2, B1)))
                        for (P, pre) in by_end.get(S0, []):
                            for suf in by_start.get(S3, []):
                                p, q = pre + p0, q0 + suf
                                s, tg = src_tgt(P, p, Gx, Fx, q)
                                assert s == tg, "H is not a loop"
                                eqs.append((s, s, expand(P, p, Gx, Fx, q), ()))
                                nC += 1

    # keys in expansions that never appeared directly as irreducible configurations
    # cannot exist (every expansion step is itself a scanned configuration).
    for v in memo.values():
        for k in v:
            assert k in edges, k

    # Endomorphisms only involve the strongly connected component of their
    # base 3-cell: a loop at c, and every context X . L . Y of an equation
    # inside such a loop, stays in that component. So compute per component.
    out_edges = {}
    for k, (s, tg) in edges.items():
        out_edges.setdefault(s, []).append((k, tg))
    nodes = {cls(P, seq) for (P, seq) in paths}
    comp = scc(nodes, {x: [y for _, y in out_edges.get(x, [])] for x in nodes})
    cyclic = {x for x in nodes
              if any(comp[y] == comp[x] for _, y in out_edges.get(x, []))}
    if impose_C == 'plus':
        # (C+): every rotation of every H instance is an identity too
        for (d1, d2, L1, L2) in list(eqs):
            if d1 == d2 and L2 == () and len(L1) > 1:
                for i in range(1, len(L1)):
                    n_i = edges[L1[i - 1]][1]
                    eqs.append((n_i, n_i, L1[i:] + L1[:i], ()))

    # Exact quotient on each component, with edge sets as bitmasks:
    # states (x, E) reachable from c; generating pairs from the equations
    # with arbitrary left context X : c -> d1; then closure under appending
    # edges (right congruence). Equal (x, E) is the support equation.
    endo, too_big = {}, []
    members = {}
    for x in cyclic:
        members.setdefault(comp[x], []).append(x)
    for cid, mem in members.items():
        cedges = [(k, s_, t_) for k, (s_, t_) in edges.items()
                  if s_ in cyclic and t_ in cyclic and comp[s_] == cid and comp[t_] == cid]
        bit = {k: 1 << i for i, (k, _, _) in enumerate(cedges)}
        outs = {}
        for k, s_, t_ in cedges:
            outs.setdefault(s_, []).append((bit[k], t_))
        ceqs = [(d1, d2, sum(bit[k] for k in set(L1)), sum(bit[k] for k in set(L2)))
                for (d1, d2, L1, L2) in eqs
                if d1 in cyclic and comp[d1] == cid and comp[d2] == cid]
        for c in mem:
            seen = {(c, 0)}
            stack = [(c, 0)]
            while stack and len(seen) <= state_cap:
                x, E = stack.pop()
                for bk, y in outs.get(x, []):
                    st = (y, E | bk)
                    if st not in seen:
                        seen.add(st); stack.append(st)
            if len(seen) > state_cap:
                too_big.append(c)
                continue
            uf = UF()
            work = []
            for (x, EX) in seen:
                for (d1, d2, m1, m2) in ceqs:
                    if x == d1 and m1 != m2:
                        work.append(((d2, EX | m1), (d2, EX | m2)))
            while work:
                u, v = work.pop()
                ru, rv = uf.find(u), uf.find(v)
                if ru == rv:
                    continue
                uf.p[ru] = rv
                for bk, y in outs.get(u[0], []):
                    work.append(((y, u[1] | bk), (y, v[1] | bk)))
            idc = uf.find((c, 0))
            classes = {uf.find((x, E)) for (x, E) in seen if x == c} - {idc}
            if classes:
                endo[c] = classes
    nodes = cyclic

    # 3-cell endpoints
    ends3 = {}
    for (P, seq) in paths:
        ends3[cls(P, seq)] = (P, run(P, seq), seq)
    pairs = []
    for u in endo:
        for v in endo:
            if ends3[u][1] == ends3[v][0]:
                pairs.append((u, v))
    return dict(words=len(W), paths=len(paths), classes3=len(nodes),
                edges=len(edges), eqs=len(eqs), nC=nC, endo=endo, pairs=pairs, too_big=too_big,
                ends3=ends3)


def show(w):
    return ''.join(f"{x}{i}" for x, i in w)


def main():
    args = [int(x) for x in sys.argv[1:]]
    sizes = list(zip(args[::2], args[1::2])) or [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (2, 4), (3, 3)]
    for (m, n) in sizes:
        for C, tag in ((False, "F_T     "), (True, "F_T/(C) "), ('plus', "F_T/(C+)")):
            R = analyse(m, n, C)
            print(f"Sigma[{m}] v Sigma[{n}] {tag}: 3-cells on 4-cycles {R['classes3']}, "
                  f"irreducible 4-generators {R['edges']}, 4-equations {R['eqs']}; "
                  f"3-cells with nonidentity endomorphisms {len(R['endo'])}, "
                  f"2-composable pairs {len(R['pairs'])}"
                  + (f", UNDECIDED (state cap) at {len(R['too_big'])} 3-cells" if R['too_big'] else ""),
                  flush=True)
            for u in list(R['endo'])[:2]:
                P, Q, su = R['ends3'][u]
                print(f"    endomorphism on {show(P)} -> {show(Q)} {su}")
            for u, v in R['pairs'][:2]:
                Pu, Qu, su = R['ends3'][u]
                Pv, Qv, sv = R['ends3'][v]
                print(f"    pair u: {show(Pu)} -> {show(Qu)} {su};  v: {show(Pv)} -> {show(Qv)} {sv}")


if __name__ == '__main__':
    main()
