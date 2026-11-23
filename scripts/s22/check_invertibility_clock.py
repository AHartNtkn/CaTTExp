"""Finite checks of the clocked presentation and the finite-height separating fibres."""

from itertools import product

from check_invertibility import Cell, identity, parallel, then, whisker


TAPE = ("_", "1")


def tagged(state, symbol):
    return f"[{state},{symbol}]"


def clock_rules(machine):
    rules = []
    for (state, symbol), (next_state, written, motion) in machine.items():
        tag = lambda c: tagged(next_state, c)
        head = (state, symbol)
        if motion == "right":
            for c in TAPE:
                rules.append((head + (c,), (written, tag(c), "T")))
            rules.append((head + ("R",), (written, tag("_"), "T", "R")))
        elif motion == "left":
            for c in TAPE:
                rules.append(((c,) + head, (tag(c), "T", written)))
            rules.append((("L",) + head, ("L", tag("_"), "T", written)))
        else:
            assert motion == "stay"
            rules.append((head, (tag(written), "T")))
    for c in TAPE:
        rules.extend([(("T", c), (c, "T")), ((c, "B"), ("B", c))])
    rules.append((("T", "R"), ("B", "R", "s")))
    states = {state for state, symbol in machine} | {entry[0] for entry in machine.values()}
    for state in states:
        for c in TAPE:
            rules.append(((tagged(state, c), "B"), (state, c)))
    assert all(0 < len(left) <= len(right) for left, right in rules)
    return rules


def rewrites(word, rules):
    for left, right in rules:
        for start in range(len(word) - len(left) + 1):
            end = start + len(left)
            if word[start:end] == left:
                yield word[:start] + right + word[end:]


def simulate(machine, initial, steps):
    """Run the tape machine directly, independently of the string rules."""
    state, tape, head = initial
    tape = list(tape)
    words = []
    for clock in range(steps + 1):
        words.append(("L", *tape[:head], state, *tape[head:], "R", *(("s",) * clock)))
        transition = machine.get((state, tape[head]))
        if clock == steps or transition is None:
            break
        state, tape[head], motion = transition
        if motion == "right":
            head += 1
            if head == len(tape):
                tape.append("_")
        if motion == "left":
            if head == 0:
                tape.insert(0, "_")
            else:
                head -= 1
    return words


def check_run(machine, initial, steps):
    words = simulate(machine, initial, steps)
    rules = clock_rules(machine)
    for clock, (word, expected) in enumerate(zip(words, words[1:])):
        # In the unclocked presentation the step gives w_i ->* w_{i+1} s.
        current = word[:len(word) - clock]
        expected = expected[:len(expected) - clock]
        for _ in range(2 * len(current) + 6):
            successor, = rewrites(current, rules)
            current = successor
            if current == expected:
                break
        assert current == expected
    return words, rules


def check_terminal_component(machine, initial, steps):
    words, rules = check_run(machine, initial, steps)
    terminal = words[-1]
    assert not list(rewrites(terminal, rules))
    backwards = [(right, left) for left, right in rules]
    component = {words[0]}
    frontier = [words[0]]
    successor = {}
    branching = 0
    while frontier:
        word = frontier.pop()
        after = list(rewrites(word, rules))
        before = set(rewrites(word, backwards))
        assert len(after) == (0 if word == terminal else 1)
        if after:
            successor[word] = after[0]
        branching += len(before) > 1
        for neighbor in before.union(after):
            assert len(neighbor) <= len(terminal)
            if neighbor not in component:
                component.add(neighbor)
                frontier.append(neighbor)
    # Every congruent word converges, even those reached by inverse transitions.
    converges = {terminal}
    for word in component:
        path = set()
        while word not in converges:
            assert word not in path
            path.add(word)
            word = successor[word]
        converges.update(path)
    assert converges == component
    return len(component), branching, len(terminal)


def check_clocks():
    # A distinct predecessor state merges with the main run. The main head
    # crosses both tape ends before halting, and also takes a stationary step.
    machine = {
        ("q0", "_"): ("q1", "1", "right"),
        ("other", "_"): ("q1", "1", "right"),
        ("q1", "_"): ("q2", "1", "left"),
        ("q2", "1"): ("q3", "_", "left"),
        ("q3", "_"): ("halt", "1", "stay"),
    }
    cases = [("q0", "_", 0), ("q1", "1_", 1), ("q2", "1", 0)]
    for initial in cases:
        size, forks, bound = check_terminal_component(machine, initial, 8)
        assert forks > 0
        print(f"{initial[0]}: {size} congruent words, {forks} branching predecessors, "
              f"maximum length {bound}.")
    assert check_terminal_component({}, ("halt", "_", 0), 0) == (1, 0, 4)
    print("The immediate-halt input is an isolated word of length 4.")
    for motion in ("left", "right", "stay"):
        rules = {("loop", symbol): ("loop", "1", motion) for symbol in TAPE}
        words, _ = check_run(rules, ("loop", "_", 0), 24)
        assert len(words) == 25 and words[-1].count("s") == 24
        added_tape_cells = 0 if motion == "stay" else 24
        assert len(words[-1]) == len(words[0]) + 24 + added_tape_cells
        if motion == "stay":
            # After the initial write the same head, state and tape recur.
            assert words[2] == words[1] + ("s",)
    print("24 successive clock factors checked independently on each of three infinite runs.")


def check_fibres():
    # Compute reversibility by descending from the identity-only layer.
    layers = [[Cell(0), Cell(1)]]
    for _ in range(6):
        layers.append([Cell(bit, s, t) for s, t in product(layers[-1], repeat=2)
                       if parallel(s, t) for bit in range(min(s.bit, t.bit) + 1)])
    base = identity(Cell(1))
    defect = Cell(0, base, base)
    assert whisker(0, defect) == defect and whisker(1, defect) == identity(base)
    for height in range(2, len(layers)):
        reversible = {identity(cell) for cell in layers[height]}
        for degree in range(height, 0, -1):
            cancellations = {(h.source, h.target) for h in reversible}
            accepted = set()
            for f in layers[degree]:
                opposite = [g for g in layers[degree]
                            if (g.source, g.target) == (f.target, f.source)]
                left = any((then(g, f), identity(f.target)) in cancellations for g in opposite)
                right = any((then(f, g), identity(f.source)) in cancellations for g in opposite)
                if left and right:
                    accepted.add(f)
            reversible = accepted
            assert reversible == {identity(cell) for cell in layers[degree - 1]}
            if degree == 2:
                assert defect not in reversible
    print("All reversible cells computed in truncated bit fibres of heights 2–6; "
          "each fibre excludes the root defect.")


if __name__ == "__main__":
    check_clocks()
    check_fibres()
