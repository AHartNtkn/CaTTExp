#!/usr/bin/env python3
"""Compile a deterministic tape machine into the parallel 2-cells of an erasing edge prism."""
from fibration_factor_search import Rule, Stage


def compile_stage(tape, transitions, initial):
    forward = {}
    for (q, a), (r, b, direction) in transitions.items():
        if direction == "R":
            cases = [(q+a+c, b+r+c) for c in tape] + [(q+a+">", b+r+"_>")]
        elif direction == "L":
            cases = [(c+q+a, r+c+b) for c in tape] + [("<"+q+a, "<"+r+"_"+b)]
        else:
            raise ValueError("expected L or R")
        for lhs, rhs in cases:
            forward[f"tape{len(forward)}"] = (lhs, rhs)

    # The machine runs in the backward direction of the fibre rules.
    rules = {n: Rule("X", rhs, lhs) for n, (lhs, rhs) in forward.items()}
    rules["h"] = Rule("X", "z", initial)
    alphabet = sorted({c for rule in rules.values() for c in rule.source+rule.target})
    arrows = {c: ("X","X") for c in alphabet}
    arrows["t"] = ("X","Y")
    def crossings(word):
        return tuple(("cross" + c, 0) for c in reversed(word))
    prisms = {n: ("X", "t", crossings(rule.source)+((n,1),), crossings(rule.target))
              for n, rule in rules.items()}
    rules.update({"cross" + c: Rule("X", "t", "t"+c) for c in alphabet})
    return Stage(arrows, rules), forward, prisms, crossings


def simulation(stage, forward, crossings, initial, steps):
    word, history = initial, []
    for _ in range(steps):
        options = [(name, i) for name,(lhs,_) in forward.items()
                   for i in range(len(word)-len(lhs)+1) if word.startswith(lhs, i)]
        assert len(options) <= 1, (word, options)
        if not options:
            break
        name,i = options[0]
        lhs,rhs = forward[name]
        word = word[:i] + rhs + word[i+len(lhs):]
        history.append((name,i+1))  # lift past the leading base edge
    path = crossings(word) + tuple(reversed(history))
    assert tuple(stage.slices("X", "t", path))[-1] == "t"+initial
    return len(history)


def check():
    stop = {("q","1"): ("q","1","R")}
    for n in (1,2,3,4):
        initial = "<q" + "1"*n + ">"
        stage, forward, prisms, crossings = compile_stage("1_", stop, initial)
        paths = list(stage.backwards("X", "t", "t"+initial, set(), 0))
        cells, index = stage.quotient(paths)
        edges = stage.edges("X", "t", cells, index, prisms)
        source = index[crossings("z") + (("h",1),)]
        target = index[crossings(initial)]
        assert {(k,b) for a,k,b in edges if a == source} == {("h",target)}
        assert not any(a == target for a,_,_ in edges)
        # At these machine configurations there is one pure rewrite history
        # per reverse prefix, plus the h alternative. Match the *whole* graph.
        by_prefix = {}
        for i, members in enumerate(cells):
            codes = {tuple(name for name, _ in path if name in forward or name == "h")
                     for path in members}
            assert len(codes) == 1
            key = codes.pop()
            assert key not in by_prefix
            by_prefix[key] = i
        expected = {(i, p[0], by_prefix[p[1:]]) for p, i in by_prefix.items() if p}
        assert edges == expected
        peak = max(sum(name in forward for name,_ in p) for p in paths)
        assert peak == n == simulation(stage, forward, crossings, initial, n+1)
        print(f"halt after {n}: writings={len(paths)} cells={len(cells)} prism-reachable=2")
    for direction in ("L","R"):
        loop = {("q","_"): ("q","_",direction)}
        initial = "<q_>"
        stage, forward, _, crossings = compile_stage("_", loop, initial)
        for n in range(25):
            assert simulation(stage, forward, crossings, initial, n) == n
        print(f"{direction}-moving machine: checked distinct parallel cells with 0..24 tape steps")


if __name__ == "__main__":
    check()
