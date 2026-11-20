#!/usr/bin/env python3
"""Check ordered crossing histories in two full D2 prisms with incompatible edge rankings."""
from fibration_factor_search import Rule, Stage


FIBRE = {"a": (0, 1), "b": (0, 1), "i": (1, 2), "j": (1, 2)}
# Words here are in right-to-left order.
RELATIONS = {"r": ("ia", "ib"), "s": ("jb", "ja")}
BASE = {"p": "012", "q": "345"}


def check():
    arrows, rules, disks = {}, {}, {}
    for v in (0, 1):
        for f, (x, y) in FIBRE.items():
            arrows[f.upper() if v else f] = (v, x), (v, y)
        for h, (u, w) in RELATIONS.items():
            transform = str.upper if v else str.lower
            rules[h+str(v)] = Rule((v, 0), transform(u), transform(w))
    for name, wires in BASE.items():
        for x, letter in enumerate(wires):
            arrows[letter] = (0, x), (1, x)
        for f, (x, y) in FIBRE.items():
            rules[name+f] = Rule((0,x), f.upper()+wires[x], wires[y]+f)
    for x in range(3):
        rules["u"+str(x)] = Rule((0,x), BASE["p"][x], BASE["q"][x])

    def crossings(name, word):
        return tuple((name+f, len(word)-1-i) for i, f in enumerate(reversed(word)))
    for name, wires in BASE.items():
        for h, (u, v) in RELATIONS.items():
            disks[name+h] = ((0,0), u.upper()+wires[0], crossings(name,u)+((h+"0",1),),
                             ((h+"1",0),)+crossings(name,v))
    for f,(x,y) in FIBRE.items():
        disks["M"+f] = ((0,x), f.upper()+BASE["p"][x], (("u"+str(x),1),("q"+f,0)),
                        (("p"+f,0),("u"+str(y),0)))
    stage = Stage(arrows,rules)
    for h,(u,v) in RELATIONS.items():
        pole = (0,0)
        word = u.upper()+BASE["p"][0]
        goal = BASE["q"][2]+v
        paths = list(stage.backwards(pole,word,goal,{"u0","u1","u2"},1))
        cells,index = stage.quotient(paths)
        moves = stage.edges(pole,word,cells,index,disks)
        initial = index[(("u0",len(u)),)+crossings("q",u)+((h+"0",1),)]
        final = index[((h+"1",0),)+crossings("p",v)+(("u2",0),)]
        def histories(cell, seen):
            assert cell not in seen
            if cell == final:
                yield ()
            for start,label,end in moves:
                if start == cell:
                    for rest in histories(end, seen | {cell}):
                        yield (label,)+rest
        histories_here = set(histories(initial,set()))
        old_side = tuple("M"+f for f in reversed(u)) + ("p"+h,)
        new_side = ("q"+h,) + tuple("M"+f for f in reversed(v))
        assert {old_side,new_side} <= histories_here
        def tape(history):
            return "".join(label[1] for label in reversed(history) if label[0] == "M")
        assert (tape(old_side), tape(new_side)) == (u,v)
        assert all(tape(history) in (u,v) for history in histories_here)
        print(f"{h}: {len(paths)} writings, {len(cells)} middle 2-cells, {len(moves)} "
              f"3-edges, {len(histories_here)} source-to-target label histories, tape {u}->{v}")
    # Both strict decreases cannot hold for additive weights: the difference
    # of the two incidence vectors is negated after exchanging the guards.
    from collections import Counter
    def change(rule):
        row = Counter(rule[1])
        row.subtract(rule[0])
        return row
    r,s = map(change, RELATIONS.values())
    assert any(r.values()) and all(r[f] == -s[f] for f in FIBRE)


if __name__ == "__main__":
    check()
