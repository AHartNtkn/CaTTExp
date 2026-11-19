# Dimension-3 layering complexes (notes/homotopy-polygraphs.md §4).
#
# A 3-dimensional diagram G is a planar progressive 2-dimensional diagram D_0 (one wire colour,
# marked vertices) followed by 3-steps g : S_g ⇛ T_g. Each step replaces a whiskerable block S_g
# of 2-vertices by a diagram T_g with the same boundary words. S_g may be empty (g sits on a
# contiguous run of wires w: an identity source 1_w), or T_g may be empty (identity target), but
# not both (that would be an endo-cell of an iterated identity, excluded by Theorem N).
# Non-empty S_g, T_g are tight: no wire runs straight from their input to their output.
#
# A normal marked 3-mesh (a "layering") of G is
#   * an ordered partition T_1 | ... | T_r of the 3-steps into simultaneous 3-tiers,
#   * a 2-dimensional tier encoding of every regular slice L_i = D_{T_1 ∪ ... ∪ T_i}, and
#   * a 2-dimensional tier encoding of every singular slice S_i: L_{i-1} with each S_g
#     (g in T_i) contracted to one point vertex,
# such that the legs S_i → L_{i-1} (expand each point to S_g) and S_i → L_i (expand to T_g)
# exist as maps of 2-trusses: rows of S_i go to blocks of consecutive rows (a block may be empty
# when the row only holds points with empty expansion), each item to a contiguous,
# order-preserving segment, regular words matching.
# M ≤ N when N's 3-tiers refine M's and every slice of N receives the induced 2-truss map from
# the corresponding slice of M.
#
# The script enumerates the poset P_G, checks it is a partial order, removes beat points (Stong;
# preserves homotopy type) and computes Z/2 homology of the order complex of the core.
# Claim tested: every component of B P_G is contractible.
# Usage: python3 tools/layering3_check.py [seed] [trials] [kinds]
#   kinds: 'p' = only 3-positive steps (S, T non-empty); 'a' = also identity sources/targets.
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tier_complex_check import encodings, build, boundary_connected

class Invalid(Exception):
    pass

def pid(g):
    return ('P:' + g, 0)

def owner_vertex(port):
    return None if port[0] in ('S', 'T') else port[0]

# ---------------------------------------------------------------- 2D diagrams with edge ids
# D = (verts {vid: (nin, nout)}, edges {eid: (tailport, headport)}, nsrc, ntgt)
# tailports: (vid,'o',k) or ('S',j); headports: (vid,'i',j) or ('T',k).

def from_build(src, tgt, V, tag):
    verts = {(tag, v): (len(V[v][0]), len(V[v][1])) for v in V}
    tail, head = {}, {}
    for j, e in enumerate(src): tail[e] = ('S', j)
    for k, e in enumerate(tgt): head[e] = ('T', k)
    for v, (ins, outs) in V.items():
        for j, e in enumerate(ins): head[e] = ((tag, v), 'i', j)
        for k, e in enumerate(outs): tail[e] = ((tag, v), 'o', k)
    return verts, {(tag, 'e', e): (tail[e], head[e]) for e in tail}, len(src), len(tgt)

def to_V(D):
    verts, edges, ns, nt = D
    ins = {v: [None]*verts[v][0] for v in verts}
    outs = {v: [None]*verts[v][1] for v in verts}
    src = [None]*ns; tgt = [None]*nt
    for e, (op, ip) in edges.items():
        if op[0] == 'S': src[op[1]] = e
        else: outs[op[0]][op[2]] = e
        if ip[0] == 'T': tgt[ip[1]] = e
        else: ins[ip[0]][ip[2]] = e
    return tuple(src), tuple(tgt), {v: (tuple(ins[v]), tuple(outs[v])) for v in verts}

# ---------------------------------------------------------------- 3-steps
class Step:
    """S: frozenset of 2-vertices (possibly empty). If S is non-empty, w_in/w_out are the in- and
    out-ports of S vertices on its boundary, in order. If S is empty, wires is the list of edge
    ids it sits on. T: (Tverts, Tedges internal, t_in ports, t_out ports), possibly empty."""
    def __init__(self, name, S, w_in, w_out, wires, Tverts, Tedges, t_in, t_out):
        self.name, self.S = name, frozenset(S)
        self.w_in, self.w_out, self.wires = list(w_in), list(w_out), list(wires)
        self.Tverts, self.Tedges, self.t_in, self.t_out = Tverts, Tedges, list(t_in), list(t_out)
        assert self.S or self.Tverts, 'endo-cell of an identity'
    def arity(self):
        return (len(self.wires), len(self.wires)) if not self.S else (len(self.w_in), len(self.w_out))

def split_id(g, j):
    return ('s:' + g, 'e', j)

class Diagram3:
    def __init__(self, D0, steps):
        self.D0, self.steps = D0, steps
        self.byname = {g.name: g for g in steps}
        self._D = {frozenset(): D0}
        self._enc = {}

    def resolve(self, e, D, X):
        """the edge of D that an identity-source step generated on wire e now sits on."""
        edges = D[1]; n = 0
        while e not in edges:
            n += 1
            if n > 50: raise Invalid('cannot resolve')
            if e[0].startswith('s:'):
                g = self.byname[e[0][2:]]
                if g.name in X: raise Invalid('split edge missing')
                e = g.wires[e[2]]
            else:
                raise Invalid('wire not present')
        return e

    def boundary(self, g, D, X):
        """in-edges and out-edges of g's region in D (lists, in order)."""
        verts, edges, _, _ = D
        if g.S:
            if not g.S <= set(verts): raise Invalid('source not present')
            byhead = {ip: e for e, (op, ip) in edges.items()}
            bytail = {op: e for e, (op, ip) in edges.items()}
            ein = [byhead[p] for p in g.w_in]; eout = [bytail[p] for p in g.w_out]
            for e in ein:
                if owner_vertex(edges[e][0]) in g.S: raise Invalid('not convex')
            for e in eout:
                if owner_vertex(edges[e][1]) in g.S: raise Invalid('not convex')
            return ein, eout
        w = [self.resolve(e, D, X) for e in g.wires]
        return w, w

    def apply(self, D, g, X):
        verts, edges, ns, nt = D
        ein, eout = self.boundary(g, D, X)
        nv = {v: a for v, a in verts.items() if v not in g.S}
        nv.update(g.Tverts)
        ne = {e: pq for e, pq in edges.items()
              if not (owner_vertex(pq[0]) in g.S and owner_vertex(pq[1]) in g.S)}
        if not g.S:
            for j, e in enumerate(ein):
                op, ip = ne[e]
                ne[e] = (op, g.t_in[j]); ne[split_id(g.name, j)] = (g.t_out[j], ip)
        elif not g.Tverts:
            for j in range(len(ein)):
                op = ne[ein[j]][0]; ip = ne[eout[j]][1]
                del ne[eout[j]]; ne[ein[j]] = (op, ip)
        else:
            for j, e in enumerate(ein): ne[e] = (ne[e][0], g.t_in[j])
            for k, e in enumerate(eout): ne[e] = (g.t_out[k], ne[e][1])
        ne.update(g.Tedges)
        return nv, ne, ns, nt

    def D(self, X):
        X = frozenset(X)
        if X in self._D: return self._D[X]
        for gname in sorted(X):
            Y = X - {gname}
            try:
                r = self.apply(self.D(Y), self.byname[gname], Y)
            except Invalid:
                continue
            self._D[X] = r
            return r
        raise Invalid('unreachable state')

    def slice(self, X, P):
        """D_X with the steps in P contracted to points."""
        key = (frozenset(X), frozenset(P))
        if not hasattr(self, '_sl'): self._sl = {}
        if key not in self._sl: self._sl[key] = self._slice(X, P)
        return self._sl[key]

    def _slice(self, X, P):
        D = self.D(X)
        verts, edges, ns, nt = D
        nv = dict(verts); ne = dict(edges)
        used_v = set()
        # regions with a source first, then the points of identity-source steps, so that a
        # point sitting on a boundary wire of another region lands on the already-rewired edge
        pos = [n for n in sorted(P) if self.byname[n].S]
        pts = [n for n in sorted(P) if not self.byname[n].S]
        for gname in pos:
            g = self.byname[gname]
            ein, eout = self.boundary(g, D, X)
            if used_v & g.S: raise Invalid('overlap')
            used_v |= g.S
            p = pid(gname)
            for v in g.S: del nv[v]
            nv[p] = g.arity()
            for e in list(ne):
                a, b = ne[e]
                if owner_vertex(a) in g.S and owner_vertex(b) in g.S: del ne[e]
            for j, e in enumerate(ein): ne[e] = (ne[e][0], (p, 'i', j))
            for k, e in enumerate(eout): ne[e] = ((p, 'o', k), ne[e][1])
        def res(e, pending):
            n = 0
            while e not in ne:
                n += 1
                if n > 50 or not e[0].startswith('s:'): raise Invalid('wire not present')
                h = e[0][2:]
                if h in pending: return None          # sits on a point not yet placed
                if h in X or h in P: raise Invalid('wire not present')
                e = self.byname[h].wires[e[2]]
            return e
        pending = set(pts)
        while pending:
            progress = False
            for gname in sorted(pending):
                g = self.byname[gname]
                ws = [res(e, pending - {gname}) for e in g.wires]
                if any(w is None for w in ws): continue
                p = pid(gname); nv[p] = g.arity()
                for j, e in enumerate(ws):   # points stacked on one wire: generation order
                    op, ip = ne[e]
                    ne[e] = (op, (p, 'i', j)); ne[split_id(gname, j)] = ((p, 'o', j), ip)
                pending.discard(gname); progress = True
            if not progress: raise Invalid('cyclic points')
        for op, ip in ne.values():
            for port in (op, ip):
                v = owner_vertex(port)
                if v is not None and v not in nv: raise Invalid('point on a wire inside another region')
        return nv, ne, ns, nt

    def encs(self, X, P):
        key = (frozenset(X), frozenset(P))
        if key not in self._enc:
            src, tgt, V = to_V(self.slice(X, P))
            self._enc[key] = (V, encodings(src, tgt, V))
        return self._enc[key]

# ---------------------------------------------------------------- 2-truss maps between slices
def words(enc, V, src=()):
    if not enc: return [tuple(src)]
    ws = []
    for tier in enc:
        w = []
        for it in tier:
            w += [it[1]] if it[0] == 'e' else list(V[it[1]][0])
        ws.append(tuple(w))
    last = []
    for it in enc[-1]:
        last += [it[1]] if it[0] == 'e' else list(V[it[1]][1])
    ws.append(tuple(last))
    return ws

_SM = {}
def slice_map(G, A, encA, B, encB):
    key = (id(G), A, encA, B, encB)
    if key not in _SM:
        if len(_SM) > 2000000: _SM.clear()
        _SM[key] = _slice_map(G, A, encA, B, encB)
    return _SM[key]

def _slice_map(G, A, encA, B, encB):
    """Does the unique marked 2-truss map from slice A=(XA,PA) with encoding encA to slice
    B=(XB,PB) with encoding encB exist?  Points of A not in B are expanded in B."""
    (XA, PA), (XB, PB) = A, B
    VA, _ = G.encs(XA, PA); VB, _ = G.encs(XB, PB)
    DA, DB = G.slice(XA, PA), G.slice(XB, PB)
    vown = {}
    for g in PA - PB:
        st = G.byname[g]
        for v in (st.Tverts if g in XB else st.S): vown[v] = pid(g)
    par = {e: e for e in DA[1]}
    def f(x):
        while par[x] != x: x = par[x]
        return x
    for g in PA - PB:
        st = G.byname[g]
        empty = (not st.Tverts) if g in XB else (not st.S)
        if not empty: continue
        p = pid(g)
        for j in range(st.arity()[0]):
            ein = [e for e, (op, ip) in DA[1].items() if ip == (p, 'i', j)][0]
            eout = [e for e, (op, ip) in DA[1].items() if op == (p, 'o', j)][0]
            par[f(eout)] = f(ein)
    cls = {}
    for e in DA[1]: cls.setdefault(f(e), set()).add(e)
    def edge_class(e):
        """A-edges that B-edge e stands for, or None if internal to an expanded region."""
        return cls[f(e)] if e in DA[1] else None
    rowA = {}
    for a, tier in enumerate(encA):
        for it in tier:
            if it[0] == 'v': rowA[it[1]] = a
    eown = []
    for a, tier in enumerate(encA):
        d = {}
        for idx, it in enumerate(tier):
            if it[0] == 'e': d[it[1]] = idx
            else:
                for e in VA[it[1]][0] + VA[it[1]][1]: d[e] = idx
        eown.append(d)
    itemidx = [{it[1]: idx for idx, it in enumerate(tier) if it[0] == 'v'} for tier in encA]
    assign = []
    for tier in encB:
        rows = {rowA[vown.get(it[1], it[1])] for it in tier if it[0] == 'v'}
        if len(rows) != 1: return False
        assign.append(rows.pop())
    if assign != sorted(assign): return False
    for R, tier in enumerate(encB):
        a = assign[R]; seq = []
        for it in tier:
            if it[0] == 'v':
                seq.append(itemidx[a][vown.get(it[1], it[1])]); continue
            c = edge_class(it[1])
            if c is None:   # internal edge of an expanded region
                x = vown.get(owner_vertex(DB[1][it[1]][0]))
                if x is None or x not in itemidx[a]: return False
                seq.append(itemidx[a][x]); continue
            owners = {eown[a][e] for e in c if e in eown[a]}
            if len(owners) != 1: return False
            seq.append(owners.pop())
        if seq != sorted(seq): return False
    wA, wB = words(encA, VA, to_V(DA)[0]), words(encB, VB, to_V(DB)[0])
    for a in range(len(encA) + 1):
        R = next((R for R in range(len(encB)) if assign[R] >= a), len(encB))
        wb = wB[R]
        if len(wb) != len(wA[a]): return False
        for eb, ea in zip(wb, wA[a]):
            c = edge_class(eb)
            if c is None or ea not in c: return False
    return True

# ---------------------------------------------------------------- meshes
def tiers_sequences(G):
    names = sorted(g.name for g in G.steps)
    out = []
    def rec(X, seq):
        if len(X) == len(names):
            out.append(tuple(seq)); return
        rest = [n for n in names if n not in X]
        for k in range(1, len(rest)+1):
            for T in itertools.combinations(rest, k):
                T = frozenset(T)
                try:
                    G.slice(X, T); G.D(X | T)
                except Invalid:
                    continue
                rec(X | T, seq + [T])
    rec(frozenset(), [])
    return out

def slices_of(pi):
    X = frozenset(); sl = [(X, frozenset())]
    for T in pi:
        sl.append((X, T)); X = X | T; sl.append((X, frozenset()))
    return sl

def meshes(G, cap=None):
    res = []
    for pi in tiers_sequences(G):
        sl = slices_of(pi)
        def rec(i, chosen):
            if cap is not None and len(res) > cap: return
            if i == len(sl):
                res.append((pi, tuple(chosen))); return
            _, E = G.encs(*sl[i])
            for e in E:
                if i > 0:
                    if i % 2 == 1:
                        if not slice_map(G, sl[i], e, sl[i-1], chosen[-1]): continue
                    else:
                        if not slice_map(G, sl[i-1], chosen[-1], sl[i], e): continue
                rec(i+1, chosen + [e])
        rec(0, [])
    return res

def refines(pi, pj):
    k = 0
    for T in pi:
        acc = frozenset()
        while acc != T:
            if k >= len(pj) or not pj[k] <= T: return False
            acc |= pj[k]; k += 1
    return k == len(pj)

def leq(G, M, N):
    (pi, eM), (pj, eN) = M, N
    if not refines(pi, pj): return False
    slM, slN = slices_of(pi), slices_of(pj)
    for b, (XB, PB) in enumerate(slN):
        src = None
        for a, (XA, PA) in enumerate(slM):
            if not PA and not PB and XA == XB: src = a; break
        if src is None:
            for a, (XA, PA) in enumerate(slM):
                if PA and XA <= XB <= XA | PA and PB <= PA and (XB | PB) <= (XA | PA): src = a; break
        if src is None: return False
        if not slice_map(G, slM[src], eM[src], slN[b], eN[b]): return False
    return True

# ---------------------------------------------------------------- topology of finite posets
def analyse_poset(n, lt):
    up = {i: set() for i in range(n)}; down = {i: set() for i in range(n)}
    for i, j in lt: up[i].add(j); down[j].add(i)
    parent = list(range(n))
    def f(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for i, j in lt: parent[f(i)] = f(j)
    comps = {}
    for i in range(n): comps.setdefault(f(i), []).append(i)
    results = []
    for c in comps.values():
        alive = set(c); changed = True
        while changed and len(alive) > 1:
            changed = False
            for x in list(alive):
                U = up[x] & alive; Dn = down[x] & alive
                minU = [u for u in U if not (down[u] & U)]
                maxD = [d for d in Dn if not (up[d] & Dn)]
                if len(minU) == 1 or len(maxD) == 1:
                    alive.discard(x); changed = True
        if len(alive) == 1:
            results.append((len(c), 1, {0: 1})); continue
        results.append((len(c), len(alive), homology(sorted(alive), up)))
    return results

def homology(core, up):
    S = set(core)
    chains = {0: [(x,) for x in core]}; k = 0
    while chains[k]:
        nxt = [ch + (y,) for ch in chains[k] for y in up[ch[-1]] & S]
        k += 1; chains[k] = nxt
        if sum(len(v) for v in chains.values()) > 400000: return {'too_big': True}
    idx = {d: {c: i for i, c in enumerate(L)} for d, L in chains.items()}
    def rank2(rows):
        basis = {}; r = 0
        for x in rows:
            while x:
                h = x.bit_length() - 1
                if h in basis: x ^= basis[h]
                else: basis[h] = x; r += 1; break
        return r
    ranks = {}
    for d in range(1, k):
        rows = []
        for ch in chains[d]:
            x = 0
            for i in range(len(ch)): x ^= 1 << idx[d-1][ch[:i] + ch[i+1:]]
            rows.append(x)
        ranks[d] = rank2(rows)
    betti = {}
    for d in range(k):
        b = len(chains[d]) - ranks.get(d, 0) - ranks.get(d+1, 0)
        if b: betti[d] = b
    return betti

def analyse(G, ms=None):
    if ms is None: ms = meshes(G)
    lt = set()
    for i, M in enumerate(ms):
        for j, N in enumerate(ms):
            if i != j and leq(G, M, N): lt.add((i, j))
    for (i, j) in lt:
        assert (j, i) not in lt, 'not antisymmetric'
    succ = {}
    for i, j in lt: succ.setdefault(i, set()).add(j)
    for i, js in succ.items():
        for j in js:
            for k in succ.get(j, ()):
                assert (i, k) in lt, 'not transitive'
    return ms, analyse_poset(len(ms), lt)

# ---------------------------------------------------------------- random generation
def random_tight(m, n, rng, tag, tries=400):
    for _ in range(tries):
        k = rng.randint(1, 2); w = m; seq = []
        for _ in range(k):
            p = rng.randint(0, min(2, w)); q = rng.randint(0, 2)
            if p == 0 and q == 0: q = 1
            a = rng.randint(0, w - p); seq.append((p, q, a)); w += q - p
        if w != n: continue
        src, tgt, V = build(m, seq)
        if set(src) & set(tgt): continue
        if not boundary_connected(src, tgt, V): continue
        verts, edges, _, _ = from_build(src, tgt, V, tag)
        t_in = [None]*m; t_out = [None]*n; inner = {}
        for e, (op, ip) in edges.items():
            if op[0] == 'S': t_in[op[1]] = ip
            elif ip[0] == 'T': t_out[ip[1]] = op
            else: inner[e] = (op, ip)
        return verts, inner, t_in, t_out
    return None

def random_D0(rng, nv):
    while True:
        L = rng.randint(1, 3); seq = []; w = L
        for _ in range(rng.randint(*nv)):
            p = rng.randint(0, min(2, w)); q = rng.randint(0, 2)
            if p == 0 and q == 0: q = 1
            a = rng.randint(0, w - p); seq.append((p, q, a)); w += q - p
        src, tgt, V = build(L, seq)
        if boundary_connected(src, tgt, V): return from_build(src, tgt, V, 'd')

def random_diagram(rng, nv=(2, 4), nsteps=(1, 3), kinds='a'):
    D0 = random_D0(rng, nv)
    G = Diagram3(D0, [])
    X = frozenset()
    for s in range(rng.randint(*nsteps)):
        g = random_step(G, X, rng, 'g%d' % s, kinds)
        if g is None: break
        G.steps.append(g); G.byname[g.name] = g
        try:
            G.D(X | {g.name})
        except Invalid:
            G.steps.pop(); del G.byname[g.name]; break
        X = X | {g.name}
    G._D = {frozenset(): D0}; G._enc = {}; G._sl = {}
    return G

def random_step(G, X, rng, name, kinds, tries=60):
    D = G.D(X)
    src, tgt, V = to_V(D)
    encs = [e for e in encodings(src, tgt, V) if all(sum(1 for it in t if it[0] == 'v') == 1 for t in e)]
    if not encs: return None
    for _ in range(tries):
        enc = rng.choice(encs)
        ws = words(enc, V, src)
        kind = rng.choice(['pos', 'pos', 'idsrc', 'idtgt']) if kinds == 'a' else 'pos'
        if kind == 'idsrc':
            i = rng.randrange(len(ws))
            if not ws[i]: continue
            a = rng.randrange(len(ws[i])); b = min(len(ws[i]), a + rng.randint(1, 2))
            w = list(ws[i][a:b])
            T = random_tight(len(w), len(w), rng, 't:' + name)
            if T is None: continue
            Tv, Te, t_in, t_out = T
            return Step(name, (), [], [], w, Tv, Te, t_in, t_out)
        if not enc: continue
        i = rng.randrange(len(enc)); j = min(len(enc), i + rng.randint(1, 2))
        S = {it[1] for t in enc[i:j] for it in t if it[0] == 'v'}
        ein = [e for e in ws[i] if owner_vertex(D[1][e][1]) in S]
        eout = [e for e in ws[j] if owner_vertex(D[1][e][0]) in S]
        if not ein and not eout: continue
        allin = {e for v in S for e in V[v][0] if owner_vertex(D[1][e][0]) not in S}
        allout = {e for v in S for e in V[v][1] if owner_vertex(D[1][e][1]) not in S}
        if set(ein) != allin or set(eout) != allout: continue
        below, above = list(ws[i]), list(ws[j])
        def ctx(word, sub):
            idx = [k for k, e in enumerate(word) if e in sub]
            if not idx: return None
            if idx != list(range(idx[0], idx[0] + len(idx))): return None
            return tuple(word[:idx[0]]), tuple(word[idx[-1]+1:])
        c1, c2 = ctx(below, set(ein)), ctx(above, set(eout))
        if c1 is None and c2 is None: continue
        if c1 is None and below != list(c2[0] + c2[1]): continue
        if c2 is None and above != list(c1[0] + c1[1]): continue
        if c1 is not None and c2 is not None and c1 != c2: continue
        w_in = [D[1][e][1] for e in ein]; w_out = [D[1][e][0] for e in eout]
        if kind == 'idtgt':
            if len(ein) != len(eout) or not ein: continue
            return Step(name, S, w_in, w_out, [], {}, {}, [], [])
        T = random_tight(len(ein), len(eout), rng, 't:' + name)
        if T is None: continue
        Tv, Te, t_in, t_out = T
        return Step(name, S, w_in, w_out, [], Tv, Te, t_in, t_out)
    return None

MAXMESH = 500

def describe(G):
    out = []
    for g in G.steps:
        kind = 'idsrc' if not g.S else ('idtgt' if not g.Tverts else 'pos')
        out.append((g.name, kind, len(g.S), len(g.Tverts), g.arity()))
    return out

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    kinds = sys.argv[3] if len(sys.argv) > 3 else 'a'
    rng = random.Random(seed)
    src, tgt, V = build(1, [(1, 2, 0), (2, 1, 0)])
    print('2D sanity (no steps):', analyse(Diagram3(from_build(src, tgt, V, 'd'), []))[1])
    src, tgt, V = build(0, [(0, 0, 0), (0, 0, 0)])
    print('two scalars (expect a circle):', analyse(Diagram3(from_build(src, tgt, V, 'd'), []))[1])
    src, tgt, V = build(0, [(0, 1, 0), (1, 0, 0), (0, 1, 0), (1, 0, 0)])
    D0 = from_build(src, tgt, V, 'd')
    Tv, Te, _, _ = from_build(*build(0, [(0, 2, 0), (2, 0, 0)]), 't:g0')
    G = Diagram3(D0, [Step('g0', {('d', 0), ('d', 1)}, [], [], [], Tv, Te, [], [])])
    print('floating components with a 3-step (expect a circle):', analyse(G)[1])
    tested = bad = skipped = 0; maxsize = 0; hist = {}
    for t in range(trials):
        _SM.clear()
        G = random_diagram(rng, nv=(1, 3), nsteps=(1, 3), kinds=kinds)
        if not G.steps: continue
        ms = meshes(G, cap=MAXMESH)
        if len(ms) > MAXMESH: skipped += 1; continue
        try:
            ms, res = analyse(G, ms)
        except AssertionError as ex:
            print('ASSERT', t, ex, describe(G)); bad += 1; continue
        tested += 1; maxsize = max(maxsize, len(ms))
        key = tuple(sorted(k for _, k, *_ in describe(G)))
        hist[key] = hist.get(key, 0) + 1
        if not ms:
            print('EMPTY', t, describe(G)); bad += 1; continue
        if any(r[2] != {0: 1} for r in res):
            print('NONCONTRACTIBLE', t, describe(G), res, flush=True); bad += 1
    print('tested', tested, 'bad', bad, 'skipped (too large)', skipped, 'max poset', maxsize)
    print('step kinds:', hist)

# ---------------------------------------------------------------- Quillen fibres over 3-tier sequences
def fibre_analysis(G, ms):
    """Tests the reduction P_G → Π_G (forget slice encodings). Returns (topology of Π_G,
    list of non-contractible upper fibres {M : φ(M) refines π})."""
    n = len(ms)
    lt = {(i, j) for i in range(n) for j in range(n) if i != j and leq(G, ms[i], ms[j])}
    pis = sorted({M[0] for M in ms}, key=repr)
    pidx = {p: k for k, p in enumerate(pis)}
    plt = {(pidx[a], pidx[b]) for a in pis for b in pis if a != b and refines(a, b)}
    top = analyse_poset(len(pis), plt)
    badf = []
    for p in pis:
        sub = [i for i in range(n) if refines(p, ms[i][0])]
        loc = {i: k for k, i in enumerate(sub)}
        r = analyse_poset(len(sub), {(loc[i], loc[j]) for (i, j) in lt if i in loc and j in loc})
        if len(r) != 1 or r[0][2] != {0: 1}: badf.append((p, r))
    return top, badf

# ---------------------------------------------------------------- interchange slices (model K)
# Between consecutive 3-tiers (and before the first, after the last) a normal 3-mesh may contain
# artificial singular slices A with no 3-vertex: L ← A → L', A a common coarsening of the two
# regular encodings, not both legs identities. They carry the 2-dimensional isotopies
# (interchanges) between 3-tiers. Model K allows at most K of them per gap; K = 0 is the
# model above. A mesh is (slices, encodings) with slices L_0, s_1, L_1, ..., s_m, L_m.

def slice_lists(pi, K):
    gaps = len(pi) + 1
    for ks in itertools.product(range(K + 1), repeat=gaps):
        X = frozenset(); sl = [(X, frozenset())]
        for g in range(gaps):
            for _ in range(ks[g]):
                sl.append((X, frozenset())); sl.append((X, frozenset()))
            if g < len(pi):
                sl.append((X, pi[g])); X = X | pi[g]; sl.append((X, frozenset()))
        yield tuple(sl)

def meshes_k(G, K, cap=None):
    res = []
    for pi in tiers_sequences(G):
        for sl in slice_lists(pi, K):
            def rec(i, chosen):
                if cap is not None and len(res) > cap: return
                if i == len(sl):
                    res.append((sl, tuple(chosen))); return
                _, E = G.encs(*sl[i])
                for e in E:
                    if i > 0:
                        if i % 2 == 1:
                            if not slice_map(G, sl[i], e, sl[i-1], chosen[-1]): continue
                        else:
                            if not slice_map(G, sl[i-1], chosen[-1], sl[i], e): continue
                            if not sl[i-1][1] and chosen[-2] == chosen[-1] == e: continue
                    rec(i+1, chosen + [e])
            rec(0, [])
    return res

def leq_k(G, M, N, count=False):
    (slM, eM), (slN, eN) = M, N
    m, n = len(slM) // 2, len(slN) // 2
    found = 0
    for mid in itertools.combinations_with_replacement(range(n + 1), max(m - 1, 0)):
        alpha = (0,) + mid + (n,) if m > 0 else (0,)
        if m == 0 and n != 0: break
        ok = True
        for j in range(m):       # every point of M's singular slice j appears in its interval
            pts = set()
            for b in range(alpha[j], alpha[j+1]): pts |= slN[2*b+1][1]
            if pts != set(slM[2*j+1][1]): ok = False; break
        if not ok: continue
        for b in range(n + 1):
            srcs = [2*j for j in range(m + 1) if alpha[j] == b]
            srcs += [2*j+1 for j in range(m) if alpha[j] <= b <= alpha[j+1]]
            for a in srcs:
                if not _struct(slM[a], slN[2*b]) or not slice_map(G, slM[a], eM[a], slN[2*b], eN[2*b]):
                    ok = False; break
            if not ok: break
        if ok:
            for b in range(n):
                srcs = [2*j+1 for j in range(m) if alpha[j] <= b < alpha[j+1]]
                if len(srcs) != 1: ok = False; break
                a = srcs[0]
                if not _struct(slM[a], slN[2*b+1]) or not slice_map(G, slM[a], eM[a], slN[2*b+1], eN[2*b+1]):
                    ok = False; break
        if ok:
            found += 1
            if not count: return True
    return found if count else False

def _struct(A, B):
    (XA, PA), (XB, PB) = A, B
    return PB <= PA and XA <= XB <= XA | PA and (XB | PB) <= (XA | PA)

def analyse_k(G, K, cap=None):
    ms = meshes_k(G, K, cap)
    if cap is not None and len(ms) > cap: return ms, None, 0
    lt = set(); multi = 0
    for i, M in enumerate(ms):
        for j, N in enumerate(ms):
            if i != j:
                c = leq_k(G, M, N, count=True)
                if c: lt.add((i, j))
                if c > 1: multi += 1
    cycles = sum(1 for (i, j) in lt if (j, i) in lt) // 2
    if cycles: return ms, {'not a poset: pairs with maps both ways': cycles}, multi
    return ms, analyse_poset(len(ms), lt), multi
