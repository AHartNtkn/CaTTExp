"""Check the base, weight, padded substring step and short side of Response 10."""

from fibration_pentagon_counterexample import STAGE, THREE


def check_base(source, target, rules):
    # Each 2-generator has two base paths and a component at the unique fibre
    # vertex. A nonempty path to its right postcomposes by the erasing functor.
    disks = {
        "split": ("a", "aa", ""), "fold": ("aa", "a", "g"),
        "d": ("a", "a", ""), "j": ("t", "a", ""),
        "m": ("pp", "p", "g"), "X": ("taa", "pp", ""),
        "Y": ("p", "ta", ""),
    }
    letters = set("LR" + source + target + "".join(l + r for l, r in rules))
    for letter in letters:
        disks["letter_" + letter] = ("a", "a", letter)

    def read(word, steps):
        origins = list(range(len(word)))
        component = ""
        for name, pos in steps:
            lhs, rhs, value = disks[name]
            assert word[pos:pos + len(lhs)] == lhs
            end = pos + len(lhs)
            if end == len(word):
                component += value
            word = word[:pos] + rhs + word[end:]
            origins[pos:end] = [None] * len(rhs)
        return word, component, tuple(i for i in origins if i is not None)

    def tape(word):
        return [("letter_" + c, 1) for c in word]

    left, test = [("d", 0)], [("split", 1), ("fold", 1)]
    faces = [
        ("aa", left, left + test, "", "g"),
        ("aa", left + test, left + tape("L" + source + "R"),
         "g", "L" + source + "R"),
        ("aa", left + tape("L" + target + "R"), left, "L" + target + "R", ""),
        ("taa", [("X", 0), ("m", 0), ("Y", 0)], [("fold", 1)], "g", "g"),
    ]
    faces.extend(("aa", left + tape(l), left + tape(r), l, r) for l, r in rules)

    def tree(*positions):
        return [("m", i) for i in positions]

    faces.extend([
        ("ppp", tree(0, 0), tree(1, 0), "g", "gg"),
        ("pppp", tree(0, 0, 0), tree(2, 1, 0), "g", "ggg"),
    ])
    assert read("pppp", tree(0, 1, 0)) == read("pppp", tree(2, 0, 0))
    assert read("pppp", tree(0, 1, 0)) == ("p", "gg", ())

    idle_left, idle_right = set(), set()
    for word, src, tgt, u, v in faces:
        end, value, wires = read(word, src)
        other_end, other_value, other_wires = read(word, tgt)
        assert (end, value, other_value) == (other_end, u, v)
        for kept in (wires, other_wires):
            for k in range(1, len(word) + 1):
                if all(i in kept for i in range(k)):
                    idle_left.add(word[:k])
                if all(i in kept for i in range(len(word) - k, len(word))):
                    idle_right.add(word[-k:])
    assert idle_left == {"t"} and idle_right == {"a"}

    # Exchange P through a nonempty prefix around each simulated rule.
    for l, r in rules:
        for side in (l, r):
            prefix, suffix = tape("L" + source), tape(target + "R")
            assert read("aa", left + prefix + tape(side) + suffix) == read(
                "aa", prefix + left + tape(side) + suffix)


def check_short_side():
    word = "gtttt"
    paths = list(STAGE.backwards("x", word, "t", {"u"}, 3))
    cells, index = STAGE.quotient(paths)
    moves = {k: THREE[k] for k in ("D", "M", "V")}
    edges = STAGE.edges("x", word, cells, index, moves)

    def tree(path):
        leaves = ["p"] * 4
        for current, (name, pos) in zip(STAGE.slices("x", word, path), path):
            if name == "u":
                j = current[:pos].count("t")
                leaves[j:j + 2] = [tuple(leaves[j:j + 2])]
        return leaves[0]

    r = ("p", ("p", ("p", "p")))
    e = (("p", "p"), ("p", "p"))
    trees = [tree(reps[0]) for reps in cells]
    assert trees.count(r) == 1
    root = trees.index(r)
    outgoing = [(label, end) for start, label, end in edges if start == root]
    assert all(label == "V" for label, _ in outgoing)
    balanced = [end for _, end in outgoing if trees[end] == e]
    assert len(balanced) == 1
    assert all(start != balanced[0] for start, _, _ in edges)
    assert (len(paths), len(cells), len(edges)) == (18, 8, 7)
    print("18 writings, 8 exchange classes, 7 marked edges, balanced successor is a sink")


if __name__ == "__main__":
    check_base("abc", "acc", [("b", "c"), ("bc", "aaa")])
    check_base("a", "bbb", [])
    print("Base globularity, erasing weight, and disjoint idle words checked")
    check_short_side()
