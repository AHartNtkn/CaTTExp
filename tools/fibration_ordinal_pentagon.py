#!/usr/bin/env python3
"""Strict factor search on an even-dual 4-simplex with finite path fibres [i+1]."""
from itertools import combinations

from fibration_factor_search import Rule, Stage


def simplex(gap):
    arrows, rules, kind = {}, {}, {}
    edge, fibre = {}, {}

    def arrow(source, target):
        ident = chr(0x400 + len(arrows))
        arrows[ident] = source, target
        return ident

    def add(family, pole, lhs, rhs):
        label = (family, len(rules))
        rules[label] = Rule(pole, lhs, rhs)
        kind[label] = family

    def offset(i, j):
        return gap * (j - i - 1)

    for i in range(5):
        for r in range(i + 1):
            fibre[i, r] = arrow((i, r), (i, r + 1))
        for j in range(i + 1, 5):
            for r in range(i + 2):
                edge[i, j, r] = arrow((i, r), (j, r + offset(i, j)))

    def route(vertices, r):
        word = ""
        for i, j in zip(vertices, vertices[1:]):
            word = edge[i, j, r] + word
            r += offset(i, j)
        return word, r

    def prefix(start, end, i):
        return "".join(fibre[i, r] for r in reversed(range(start, end)))

    for i, j in combinations(range(5), 2):
        for r in range(i + 1):
            add("c", (i, r), fibre[j, r+offset(i,j)] + edge[i,j,r],
                edge[i,j,r+1] + fibre[i,r])
    for i, j, k in combinations(range(5), 3):
        for r in range(i + 2):
            word, s = route((i,j,k), r)
            add("u", (i, r), prefix(s, s+gap, k) + word, edge[i,k,r])

    stage = Stage(arrows, rules)

    def writing(pole, initial, sequence):
        word, path = initial, []
        for family, pos in sequence:
            options = [label for label, rule in rules.items()
                       if kind[label] == family and pos in stage.sites(pole, word, rule.source, rule.vertex)]
            assert len(options) == 1, (family, pos, options)
            step = options[0], pos
            word = tuple(stage.slices(pole, word, [step]))[-1]
            path.append(step)
        return tuple(path)

    prisms = {}
    def prism(name, vertices, r, extra, src, tgt):
        i, j = vertices[0], vertices[-1]
        pole = (i,r)
        word, s = route(vertices, r)
        word = prefix(s, r+offset(i,j)+extra, j) + word
        prisms[name,vertices,r] = pole, word, writing(pole, word, src), writing(pole, word, tgt)

    for i,j,k in combinations(range(5), 3):
        for r in range(i+1):
            prism("M",(i,j,k),r,1, (("u",1),("c",0)),
                  (("c",gap),("c",gap+1),("u",0)))
    for vertices in combinations(range(5), 4):
        for r in range(vertices[0]+2):
            # Right comb versus left comb, crossing the inner contraction's component.
            src = ((("c",1),) if gap else ()) + (("u",gap+1),("u",0))
            tgt = (("u",gap),("u",0))
            prism("V",vertices,r,0,src,tgt)
    events = {label for label in rules if kind[label] == "u"}
    for vertices in combinations(range(5), 4):
        # Exhaust both faces of each object associator before using its disk.
        for r in range(vertices[0]+2):
            pole, word, src, tgt = prisms["V",vertices,r]
            cells, index = stage.quotient(stage.backwards(pole, word, edge[vertices[0],vertices[-1],r], events, 2))
            assert len(cells) == 2 and index[src] != index[tgt]
    return stage, kind, events, prisms, edge, route, prefix


def check(gap):
    stage, kind, events, prisms, edge, route, prefix = simplex(gap)
    edges_to_base = {letter: (i,j) for (i,j,_),letter in edge.items()}
    pentagon = tuple(range(5))
    word, s = route(pentagon, 0)
    word = prefix(s, gap*3, 4) + word
    pole = (0,0)
    paths = list(stage.backwards(pole,word,edge[0,4,0],events,3))
    cells, index = stage.quotient(paths)
    moves = stage.edges(pole,word,cells,index,prisms)

    def tree(path):
        forest = list("4321")  # ordered in the displayed right-to-left word
        for w,(label,i) in zip(stage.slices(pole,word,path),path):
            if kind[label] == "u":
                cut = sum(c in edges_to_base for c in w[:i])
                forest[cut:cut+2] = ["(" + "".join(forest[cut:cut+2]) + ")"]
        return forest[0]

    shapes = []
    for members in cells:
        trees = {tree(p) for p in members}
        assert len(trees) == 1
        shapes.append(trees.pop())
    def follows(sequence):
        reached = {i for i,s in enumerate(shapes) if s == sequence[0]}
        for next_shape in sequence[1:]:
            todo = list(reached)
            while todo:
                x = todo.pop()
                for a,(name,_,_),b in moves:
                    if a == x and name == "M" and b not in reached:
                        reached.add(b)
                        todo.append(b)
            reached = {b for a, (name, _, _), b in moves
                       if name == "V" and a in reached and shapes[b] == next_shape}
        return bool(reached)
    right, left = "(4(3(21)))","(((43)2)1)"
    short = follows([right,"((43)(21))",left])
    long = follows([right,"(4((32)1))","((4(32))1)",left])
    assert short == (gap == 0) and long
    print(f"gap={gap} writings={len(paths)} middle={len(cells)} contextual_edges={len(moves)} "
          f"short={short} long={long}")


if __name__ == "__main__":
    for gap in (0,1):
        check(gap)
