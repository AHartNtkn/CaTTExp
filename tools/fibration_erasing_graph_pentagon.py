#!/usr/bin/env python3
"""One-sided face enumeration on a pentagon with a cyclic graph fibre and idempotent erasure."""
from collections import defaultdict
from fibration_factor_search import Rule, Stage


def pentagon_routes(stage, word, cells, moves):
    def projected_tree(word, path):
        nodes = list("4321")
        for w,(name,i) in zip(stage.slices("x",word,path),path):
            if name == "u":
                j = w[:i].count("t")
                nodes[j:j+2] = ["("+ "".join(nodes[j:j+2]) +")"]
        return nodes[0]

    trees = []
    for c in cells:
        choices = {projected_tree(word,p) for p in c}
        assert len(choices) == 1
        trees.append(choices.pop())

    def follows(route):
        states = {i for i,t in enumerate(trees) if t == route[0]}
        for t in route[1:]:
            stack = list(states)
            while stack:
                i = stack.pop()
                for a,g,b in moves:
                    if a == i and g != "V" and b not in states:
                        states.add(b)
                        stack.append(b)
            states = {b for a,g,b in moves if a in states and g == "V" and trees[b] == t}
        return bool(states)
    right, left = "(4(3(21)))", "(((43)2)1)"
    short = follows([right,"((43)(21))",left])
    long = follows([right,"(4((32)1))","((4(32))1)",left])
    return short, long


def check(e):
    # P fixes g and erases j. The multiplication component has length e in g.
    stage = Stage({a: ("x","x") for a in "tgj"},
                  {name: Rule("x", lhs, rhs) for name, lhs, rhs in (
                      ("c", "gt", "tg"), ("j", "t", "tj"), ("u", "g"*e+"tt", "t"))})
    u = "g"*e + "tt"
    three = {
        "G": ("x", "g"+u, (("u",1),("c",0)), (("c",e),("c",e+1),("u",0))),
        "J": ("x", u, (("u",0),("j",0)), (("j",e+1),("u",0))),
        "V": ("x", "g"*(2*e)+"ttt", ((("c",1),) if e else ())+(("u",e+1),("u",0)),
              (("u",e),("u",0))),
    }
    ending = defaultdict(list)
    for source, path in stage.ending_at("x","t",{"u"},3):
        ending[source].append(path)
    # All candidate one-sided 2-factors are generated before their other poles are tested.
    assert all("j" not in word and all(g!="j" for p in paths for g,_ in p)
               for word, paths in ending.items())
    word = "g"*(3*e) + "tttt"
    cells, index = stage.quotient(ending[word])
    moves = stage.edges("x",word,cells,index,three)
    short, long = pentagon_routes(stage, word, cells, moves)
    assert long and short == (e == 0)
    assert not any(name == "J" for _,name,_ in moves)
    print(f"e={e} one-sided sources={len(ending)} one-sided writings={sum(map(len,ending.values()))} "
          f"at required poles={len(cells)} short={short} long={long}")


if __name__ == "__main__":
    for e in (0,1):
        check(e)
