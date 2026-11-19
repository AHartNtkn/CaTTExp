# Check (2026-11-19, homotopy-polygraphs response, Followup 2 Sec. 2): for a progressive planar
# diagram G (one wire colour) with every component meeting the boundary, every connected
# component of the regular CW complex K_G (cells = tier encodings, faces = tier splittings)
# has the Z/2 homology of a point. Floating scalars give circles. Usage: tier_complex_check.py [seed]
import itertools, sys, random
from functools import lru_cache

def build(init_len, seq):
    """seq: list of (p,q,a): apply vertex with p inputs at visible position a, q outputs."""
    word = list(range(init_len)); nxt = init_len
    V = {}
    for i,(p,q,a) in enumerate(seq):
        ins = word[a:a+p]; assert len(ins)==p
        outs = list(range(nxt, nxt+q)); nxt += q
        V[i] = (tuple(ins), tuple(outs))
        word = word[:a]+outs+word[a+p:]
    return tuple(range(init_len)), tuple(word), V

def encodings(src, tgt, V):
    allv = frozenset(V)
    zero = [v for v in V if not V[v][0]]
    res = []
    @lru_cache(None)
    def go(word, used):
        if used == allv:
            return [()] if word == tgt else []
        out = []
        rem = [v for v in V if v not in used]
        # ready p>0 vertices with contiguous inputs
        ready = {}
        for v in rem:
            ins = V[v][0]
            if not ins: continue
            for s in range(len(word)-len(ins)+1):
                if word[s:s+len(ins)] == ins:
                    ready[v] = s
        zr = [v for v in rem if not V[v][0]]
        for k in range(len(ready)+1):
            for S in itertools.combinations(sorted(ready), k):
                # zero-input vertices: choose subset and gap assignment and order
                for kz in range(len(zr)+1):
                    if k+kz == 0: continue
                    for Z in itertools.permutations(zr, kz):
                        # assign gaps to Z in nondecreasing order (permutation gives order within gap)
                        blocks = {ready[v]: v for v in S}
                        for gaps in itertools.combinations_with_replacement(range(len(word)+1), kz):
                            # disallow gap strictly inside a block
                            bad = False
                            for g in gaps:
                                for v in S:
                                    s = ready[v]
                                    if s < g < s+len(V[v][0]): bad = True
                            if bad: continue
                            items = []; nw = []
                            zi = 0; pos = 0
                            while True:
                                while zi < kz and gaps[zi] == pos:
                                    items.append(('v',Z[zi])); nw += V[Z[zi]][1]; zi += 1
                                if pos >= len(word): break
                                if pos in blocks:
                                    v = blocks[pos]; items.append(('v',v)); nw += V[v][1]; pos += len(V[v][0])
                                else:
                                    items.append(('e',word[pos])); nw.append(word[pos]); pos += 1
                            tier = tuple(items)
                            for rest in go(tuple(nw), used | frozenset(S) | frozenset(Z)):
                                out.append((tier,)+rest)
        return out
    return go(src, frozenset())

def split(tier, parts, V):
    """parts: list of sets of vertices (ordered). returns list of tiers."""
    res = []
    for j,P in enumerate(parts):
        items = []
        for it in tier:
            if it[0]=='e': items.append(it)
            else:
                v = it[1]
                if v in P: items.append(it)
                else:
                    idx = next(i for i,Q in enumerate(parts) if v in Q)
                    edges = V[v][1] if idx < j else V[v][0]
                    items += [('e',e) for e in edges]
        res.append(tuple(items))
    return res

def faces(enc, V):
    out = []
    for ti, tier in enumerate(enc):
        vs = [it[1] for it in tier if it[0]=='v']
        n = len(vs)
        for mask in range(1, 2**n-1):
            A = {vs[i] for i in range(n) if mask>>i & 1}; B = set(vs)-A
            out.append(enc[:ti]+tuple(split(tier,[A,B],V))+enc[ti+1:])
    return out

def dim(enc):
    return sum(sum(1 for it in t if it[0]=='v')-1 for t in enc)

def rank2(rows):
    # rows: list of python ints (bitsets)
    basis = {}
    r = 0
    for x in rows:
        while x:
            h = x.bit_length()-1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; r += 1; break
    return r

def analyse(src, tgt, V):
    E = encodings(src, tgt, V)
    Es = set(E)
    assert len(Es)==len(E)
    # union-find on components via faces
    parent = {e:e for e in E}
    def f(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    F = {}
    for e in E:
        fs = faces(e, V)
        for g in fs: assert g in Es, (e,g)
        F[e] = fs
        for g in fs: parent[f(g)] = f(e)
    comps = {}
    for e in E: comps.setdefault(f(e), []).append(e)
    out = []
    for c in comps.values():
        bydim = {}
        for e in c: bydim.setdefault(dim(e), []).append(e)
        idx = {d:{e:i for i,e in enumerate(L)} for d,L in bydim.items()}
        ranks = {}
        for d,L in bydim.items():
            if d==0: ranks[d]=0; continue
            rows = []
            for e in L:
                x = 0
                for g in F[e]: x |= 1 << idx[d-1][g]
                rows.append(x)
            ranks[d] = rank2(rows)
        betti = {}
        for d,L in bydim.items():
            betti[d] = len(L) - ranks[d] - ranks.get(d+1,0)
        chi = sum((-1)**d*len(L) for d,L in bydim.items())
        out.append((len(c), chi, {d:b for d,b in betti.items() if b}))
    return out

def boundary_connected(src, tgt, V):
    # union find on vertices+boundary
    par = {}
    def f(x):
        par.setdefault(x,x)
        while par[x]!=x: x=par[x]
        return x
    def u(a,b): par[f(a)] = f(b)
    owner = {}
    for e in src: owner.setdefault(e,[]).append('B')
    for e in tgt: owner.setdefault(e,[]).append('B')
    for v,(i,o) in V.items():
        f(('v',v))
        for e in i+o: owner.setdefault(e,[]).append(('v',v))
    for e,L in owner.items():
        for x in L[1:]: u(L[0],x)
    f('B')
    return all(f(('v',v))==f('B') for v in V)

if __name__ == '__main__':
    # sanity: two scalars
    s,t,V = build(0, [(0,0,0),(0,0,0)])
    print('two scalars', analyse(s,t,V))
    s,t,V = build(1, [(1,0,0),(0,1,0)])
    print('cap then cup', analyse(s,t,V))
    random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    tested = 0; bad = 0
    for trial in range(4000):
        n = random.randint(2,5); L = random.randint(0,3); seq = []; w = L
        for _ in range(n):
            p = random.randint(0, min(2,w)); q = random.randint(0,2)
            a = random.randint(0, w-p); seq.append((p,q,a)); w += q-p
        s,t,V = build(L, seq)
        bc = boundary_connected(s,t,V)
        try:
            res = analyse(s,t,V)
        except AssertionError as ex:
            print('ASSERT', seq, ex); bad += 1; continue
        ok = all(b=={0:1} for _,_,b in res)
        if bc and not ok: print('COUNTEREX', L, seq, res); bad += 1
        if not bc and ok: pass
        tested += bc
    print('boundary-connected tested', tested, 'bad', bad)
