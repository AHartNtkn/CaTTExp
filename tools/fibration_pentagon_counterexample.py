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
from fibration_factor_search import Rule, Stage

STAGE = Stage({letter: ("x", "x") for letter in "gt"}, {
    "d": Rule("x", "g", "gg"),
    "c": Rule("x", "t", "tg"),
    "u": Rule("x", "gtt", "t"),
})

THREE = {
    "D": ("x", "t", (("c", 0), ("d", 1)), (("c", 0), ("c", 0))),
    "M": ("x", "gtt", (("u", 0), ("c", 0)), (("c", 2), ("u", 0))),
    "V": ("x", "gttt", (("c", 1), ("u", 2), ("u", 0)), (("d", 0), ("u", 1), ("u", 0))),
    "kappa": ("x", "g", (("d", 0), ("d", 1)), (("d", 0), ("d", 0))),
}

if __name__ == "__main__":
    start, goal = "gtttt", "t"
    ps = list(STAGE.backwards("x", start, goal, {"u"}, 3))
    assert all(len(p) == 5 for p in ps)
    cls, seen = STAGE.quotient(ps)
    E = STAGE.edges("x", start, cls, seen, THREE)
    assert (len(ps), len(cls), len(E)) == (18, 8, 8)
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
    def projection(path):
        trees = ["a"] * 4
        for word, (g, i) in zip(STAGE.slices("x", start, path), path):
            if g == "u":
                j = word[:i].count("t")
                trees[j:j + 2] = [(trees[j], trees[j + 1])]
        return trees[0]

    balanced = (("a", "a"), ("a", "a"))
    assert {b for a, _, b in E if a == R and projection(cls[b][0]) == balanced} == {Eearly}
    assert not out_E and reach & Llast == Llast
