#!/usr/bin/env python3
"""Check the base-dimension-4 counterexample to the relative Gray-generator
presentation (notes/conjectures/answered/fibration-presentations-all-dimensions-2026-11-19.md,
Followup section 1).

One 0-cell; 1-cells are words in {g, t} (strings, position 0 = leftmost letter).
2-generators act on substrings:  delta: g => gg,  c: t => tg,  u: gtt => t.
A 2-path is a sequence of steps (generator, position).  Two 2-paths are the same
strict 2-cell iff related by swapping adjacent steps acting on disjoint windows
(strict interchange).  3-generators (whiskerable in any 2-cell context):
  D     : c0;delta1      =>  c0;c0
  M     : u0;c0          =>  c2;u0
  V     : c1;u2;u0       =>  delta0;u1;u0
  kappa : delta0;delta1  =>  delta0;delta0
We enumerate all 2-cells gt^4 => t and every contextual application of the
3-generators, and check that no positive 3-cell lies over the short side
R -> E -> L of the pentagon.
"""
from itertools import product

GEN = {"d": ("g", "gg"), "c": ("t", "tg"), "u": ("gtt", "t")}

def apply(w, step):
    gname, i = step
    s, t = GEN[gname]
    if w[i:i+len(s)] != s:
        return None
    return w[:i] + t + w[i+len(s):]

def paths(w, goal, maxlen):
    out = []
    def go(w, acc):
        if w == goal:
            out.append(tuple(acc))
        if len(acc) == maxlen:
            return
        for g in GEN:
            for i in range(len(w)):
                w2 = apply(w, (g, i))
                if w2 is not None:
                    go(w2, acc + [(g, i)])
    go(w, [])
    return out

def swap(w, p, k):
    """Try to interchange steps k, k+1 of path p starting at word w."""
    for j in range(k):
        w = apply(w, p[j])
    (g1, i1), (g2, i2) = p[k], p[k+1]
    s1, t1 = GEN[g1]; s2, t2 = GEN[g2]
    # step2 acts on the word after step1; windows disjoint?
    if i2 + len(s2) <= i1:            # step2 entirely left of step1's output
        new = ((g2, i2), (g1, i1 - len(s2) + len(t2)))
    elif i2 >= i1 + len(t1):          # step2 entirely right of step1's output
        new = ((g2, i2 - len(t1) + len(s1)), (g1, i1))
    else:
        return None
    q = p[:k] + new + p[k+2:]
    # sanity: q must be a valid path with the same endpoints
    x = w
    for st in new:
        x = apply(x, st)
        if x is None:
            return None
    return q

def classes(start, ps):
    ps = set(ps); seen = {}; cls = []
    for p in sorted(ps):
        if p in seen: continue
        comp = {p}; stack = [p]
        while stack:
            q = stack.pop()
            for k in range(len(q) - 1):
                r = swap(start, q, k)
                if r is not None and r not in comp:
                    comp.add(r); stack.append(r)
        idx = len(cls); cls.append(comp)
        for q in comp: seen[q] = idx
    return cls, seen

THREE = {
    "D": ("t", (("c", 0), ("d", 1)), (("c", 0), ("c", 0))),
    "M": ("gtt", (("u", 0), ("c", 0)), (("c", 2), ("u", 0))),
    "V": ("gttt", (("c", 1), ("u", 2), ("u", 0)), (("d", 0), ("u", 1), ("u", 0))),
    "kappa": ("g", (("d", 0), ("d", 1)), (("d", 0), ("d", 0))),
}

def check_three_typing():
    for n, (w, s, t) in THREE.items():
        a = w; b = w
        for st in s: a = apply(a, st)
        for st in t: b = apply(b, st)
        assert a is not None and a == b, n

def edges(start, cls, seen):
    E = set()
    for ci, comp in enumerate(cls):
        for p in comp:
            words = [start]
            for st in p: words.append(apply(words[-1], st))
            for n, (w, s, t) in THREE.items():
                L = len(s)
                for k in range(len(p) - L + 1):
                    cur = words[k]
                    for off in range(len(cur) - len(w) + 1):
                        if cur[off:off+len(w)] != w: continue
                        if tuple((g, i + off) for g, i in s) != p[k:k+L]: continue
                        q = p[:k] + tuple((g, i + off) for g, i in t) + p[k+L:]
                        E.add((ci, n, seen[q]))
    return E

if __name__ == "__main__":
    check_three_typing()
    start, goal = "gtttt", "t"
    ps = paths(start, goal, 7)   # forced length is 5; 7 shows nothing longer exists
    assert all(len(p) == 5 for p in ps)
    cls, seen = classes(start, ps)
    E = edges(start, cls, seen)
    name = {}
    for ci, comp in enumerate(cls):
        rep = min(comp)
        name[ci] = " ".join(f"{g}{i}" for g, i in rep)
    print("2-paths", len(ps), "2-cells", len(cls), "3-edges", len(E))
    for a, n, b in sorted(E):
        print(f"  [{name[a]}] --{n}--> [{name[b]}]")
    # base projection: count V-steps; D, M, kappa project to identities.
    R = seen[(("c",1),("c",3),("u",4),("u",2),("u",0))]
    Eearly = seen[(("c",2),("d",0),("u",1),("u",2),("u",0))]
    Llast = {seen[(("d",0),("d",1),("u",2),("u",1),("u",0))],
             seen[(("d",0),("d",0),("u",2),("u",1),("u",0))]}
    out_R_V = {b for a, n, b in E if a == R and n == "V"}
    out_E = {b for a, n, b in E if a == Eearly}
    print("V-successors of R:", sorted(name[b] for b in out_R_V))
    print("outgoing edges of E_early:", len(out_E))
    # reachability from R
    reach = {R}; fr = [R]
    while fr:
        x = fr.pop()
        for a, n, b in E:
            if a == x and b not in reach: reach.add(b); fr.append(b)
    print("L-vertices reachable from R:", len(reach & Llast))
