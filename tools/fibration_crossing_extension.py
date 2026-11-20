"""Test for a named first prism or source crossing at a prescribed target."""
from fibration_factor_search import Rule, Stage


def check(w, v, tape_rules, expected):
    alphabet = set(w + v + "".join(s + t for s, t in tape_rules))
    assert not alphabet.intersection("tzyLR")
    changes = [("start", "z", "L" + w + "R"), ("finish", "L" + v + "R", "y")]
    changes.extend((f"rule{k}", s, t) for k, (s, t) in enumerate(tape_rules))
    arrows = {c: ("X", "X") for c in alphabet.union("zyLR")}
    arrows["t"] = ("X", "Y")
    rules = {name: Rule("X", s, t) for name, s, t in changes}
    for c in alphabet.union("zyLR"):
        rules["cross_" + c] = Rule("X", "t", "t" + c)

    def crosses(word):
        return tuple(("cross_" + c, 0) for c in reversed(word))

    stage = Stage(arrows, rules)
    prisms = {name: ("X", "t", crosses(s) + ((name, 1),), crosses(t))
              for name, s, t in changes}
    # These finite examples have terminating reverse tape rules.
    paths = list(stage.backwards("X", "t", "ty", set(), 0))
    cells, index = stage.quotient(paths)
    edges = stage.edges("X", "t", cells, index, prisms)
    predecessors = {i: set() for i in range(len(cells))}
    for a, _, b in edges:
        predecessors[b].add(a)
    final = index[crosses("y")]
    reaches_target = {final}
    pending = [final]
    while pending:
        for a in predecessors[pending.pop()] - reaches_target:
            reaches_target.add(a)
            pending.append(a)
    required = crosses("z")
    starts = {i for i, reps in enumerate(cells)
              if any(p[:1] == required for p in reps)}
    first_prism = {a for a, label, b in edges if label == "start" and b in reaches_target}
    possible = {i for i in reaches_target if any(g == "start" for g, _ in cells[i][0])}
    assert starts & reaches_target == possible == first_prism
    assert bool(first_prism) == expected
    # Identity is always a solution of the problem with no prescribed prefix.
    assert final in reaches_target and final not in starts
    print(f"{w}->{v}: {len(cells)} cells, {len(edges)} contextual edges, "
          f"{len(starts & reaches_target)} admissible sources")


if __name__ == "__main__":
    check("abc", "adc", [("b", "d")], True)
    check("abc", "dac", [("b", "d")], False)
    check("aa", "bb", [("a", "b")], True)
    check("ab", "ab", [], True)
