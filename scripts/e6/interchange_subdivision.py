"""Check subdivision of both oriented cylinders and mixed surface tableaux."""

from collections import Counter
from functools import cache
from itertools import product

from interchange_cylinders import atom, compose
from interchange_quotient_fibers import partitions
from two_slot_interchange import inversions, moves


def stack_image(table, degree, slot, lo, hi):
    """Send the top globe to the composite on [lo,hi] in a stack of globes."""
    def chain_image(chain):
        result = []
        for basis in chain:
            rank, side = basis[slot]
            if rank == degree:
                labels = range(lo, hi)
            elif rank == degree - 1:
                labels = [(lo, hi)[side]]
            else:
                labels = [side]
            result.extend(basis[:slot] + ((rank, label),) + basis[slot + 1:]
                          for label in labels)
        return tuple(sorted(result))
    return tuple((chain_image(a), chain_image(b)) for a, b in table)


@cache
def cylinder_data(degree, slot):
    """Return a disk atom and both insertion contexts on its varying input."""
    def mixed(x, b):
        return atom((x, b) if slot == 0 else (b, x))

    variable, edge = (degree, 2), (1, 2)
    if slot == 0:
        left = compose(mixed((0, 0), edge), mixed(variable, (0, 1)), 0)
        right = compose(mixed(variable, (0, 0)), mixed((0, 1), edge), 0)
    else:
        left = compose(mixed(variable, (0, 0)), mixed((0, 1), edge), 0)
        right = compose(mixed((0, 0), edge), mixed(variable, (0, 1)), 0)
    for cut in range(1, degree - 1):
        before, after = mixed((cut, 0), edge), mixed((cut, 1), edge)
        if slot == 0:
            left, right = compose(before, right, cut), compose(left, after, cut)
        else:
            left, right = compose(left, after, cut), compose(before, right, cut)
    return mixed(variable, edge), left, right


def check_cylinder(degree, slot, lo, mid, hi):
    disk, left, right = cylinder_data(degree, slot)

    def first(rows):
        return stack_image(rows, degree, slot, lo, mid)

    def second(rows):
        return stack_image(rows, degree, slot, mid, hi)

    if slot == 0:
        first_move = compose(first(disk), second(right), degree - 1)
        second_move = compose(first(left), second(disk), degree - 1)
    else:
        first_move = compose(first(left), second(disk), degree - 1)
        second_move = compose(first(disk), second(right), degree - 1)
    assert compose(first_move, second_move, degree) == stack_image(disk, degree, slot, lo, hi)


def surface_cell(start, end):
    """Steiner table of a strict 2-cell on a string of suspensions of chains."""
    assert len(start) == len(end) and all(a <= b for a, b in zip(start, end))
    def path(state):
        return tuple((1, i, height) for i, height in enumerate(state))
    top = tuple((2, i, height) for i, (a, b) in enumerate(zip(start, end))
                for height in range(a, b))
    return ((((0, 0),), ((0, len(start)),)), (path(start), path(end)), (top, top))


def tensor(x, y):
    return tuple(tuple(tuple(sorted((a, b)
                                    for i in range(3) if 0 <= d - i <= 2
                                    for a in x[i][side] for b in y[d-i][side ^ (i % 2)]))
                       for side in range(2)) for d in range(5))


def surface_faces(generator):
    if generator[0] == 0:
        return ()
    degree, slot, height = generator
    if degree == 1:
        return (0, slot), (0, slot+1)
    return (1, slot, height), (1, slot, height+1)


def check_surface_table(rows):
    assert len(rows[0][0]) == len(rows[0][1]) == 1
    for degree in range(1, len(rows)):
        expected = Counter(rows[degree-1][1])
        expected.subtract(rows[degree-1][0])
        for chain in rows[degree]:
            differential = Counter()
            for a, b in chain:
                for side, a_face in enumerate(surface_faces(a)):
                    differential[a_face, b] += 2*side - 1
                for side, b_face in enumerate(surface_faces(b)):
                    differential[a, b_face] += (-1)**a[0] * (2*side - 1)
            assert differential == expected
    assert rows[-1][0] == rows[-1][1]


def schedules(widths, state=None):
    state = state or (0,) * len(widths)
    if state == widths:
        yield (state,)
    for slot, (at, end) in enumerate(zip(state, widths)):
        if at < end:
            next_state = state[:slot] + (at + 1,) + state[slot+1:]
            for tail in schedules(widths, next_state):
                yield (state, *tail)


def check_sweep(xs, ys, strips):
    big = tensor(surface_cell(xs[0], xs[-1]), surface_cell(ys[0], ys[-1]))
    check_surface_table(big)
    current = Counter(big[3][0])
    composed = None
    for j, strip in enumerate(strips):
        for lo, hi in strip:
            tile = tensor(surface_cell(xs[lo], xs[hi]), surface_cell(ys[j], ys[j+1]))
            consumed, produced = map(Counter, tile[3])
            assert consumed <= current
            before = tuple(sorted(current.elements()))
            current = current - consumed + produced
            after = tuple(sorted(current.elements()))
            step = big[:3] + ((before, after), tile[4])
            check_surface_table(step)
            composed = step if composed is None else compose(composed, step, 3)
    assert composed == big


def surface_mark(edge, pure, charge):
    """Return the two marker counts and the forbidden-pair count."""
    if edge.family == "i":
        left, right = sorted(map(set, edge.parts), key=min)
        return (len(left & pure) * len(right & pure),
                len(left - pure) * len(right - pure),
                len(left & pure) * len(right - pure))
    varying = set(edge.parts[-1])
    if varying & pure:
        return None
    mixed = charge * len(varying)
    if edge.family == "h":
        mixed -= len(varying) * len(set(edge.parts[0]) - pure)
    return 0, mixed, 0


def check_surface_words():
    counts = Counter()
    for a_count, b_count in [(2, 2), (2, 3)]:
        for states in schedules((a_count, b_count, 1)):
            word = []
            for before, after in zip(states, states[1:]):
                slot = next(i for i in range(3) if before[i] != after[i])
                word.append("C" if slot == 2 else "AB"[slot] + str(after[slot]))
            word = tuple(word)
            c = word.index("C")
            edges = [e for e in moves(word) if e.family != "globe"]
            for a_cut, b_cut, early_pure in product(range(a_count+1), range(b_count+1), (False, True)):
                pure = {e for e in word if e != "C" and
                        ((int(e[1:]) <= (a_cut if e[0] == "A" else b_cut)) == early_pure)}
                if not pure or not pure <= set(word[:c] if early_pure else word[c+1:]):
                    continue
                early, late = ("P", "M") if early_pure else ("M", "P")
                marked = []
                for e in edges:
                    marks = surface_mark(e, pure, b_count+1)
                    if marks is None or marks[2]:
                        continue
                    p, m, _ = marks
                    assert not (p and m)
                    label = "P"*p + "M"*m
                    marked.append((e, label))
                    if e.family == "h":
                        b, a = e.parts
                        direct = next(x for x in edges if x.family == "r"
                                      and x.lo == e.lo+len(b) and x.hi == e.hi)
                        correction = next(x for x in moves(e.apply(word)) if x.family == "i"
                                          and x.lo == e.lo and x.hi == e.lo+len(a)+len(b))
                        added = surface_mark(correction, pure, b_count+1)
                        expected = surface_mark(direct, pure, b_count+1)
                        assert tuple(x+y for x, y in zip(marks, added)) == expected
                        assert correction.apply(e.apply(word)) == direct.apply(word)
                        counts["joins"] += 1
                for x, xs in marked:
                    for y, ys in marked:
                        if x.hi > y.lo:
                            continue
                        assert x.apply(y.apply(word)) == y.apply(x.apply(word))
                        change = inversions(ys+xs, early, late) - inversions(xs+ys, early, late)
                        assert change >= 0
                        if early in xs and late in ys:
                            assert change > 0
                            if x.family == y.family == "i":
                                counts["inner drops"] += 1
                        counts["exchanges"] += 1
    assert counts["inner drops"] and counts["joins"]
    return counts


if __name__ == "__main__":
    cylinders = 0
    for degree, slot in product(range(3, 13), range(2)):
        for mid in range(1, 7):
            for end in range(mid + 1, 8):
                check_cylinder(degree, slot, 0, mid, end)
                cylinders += 1
    sweeps = 0
    for left_widths, right_widths in [((1, 1), (1, 1)), ((1, 0, 2), (1, 1)),
                                      ((1, 2), (1, 0)), ((2,), (1, 0, 1))]:
        for xs, ys in product(schedules(left_widths), schedules(right_widths)):
            for strips in product(partitions(len(xs)-1), repeat=len(ys)-1):
                check_sweep(xs, ys, strips)
                sweeps += 1
    print(f"Checked {cylinders} contextual cylinder subdivisions in both orientations.")
    print(f"Checked {sweeps} signed tile pastes on horizontally composed surfaces.")
    counts = check_surface_words()
    print(f"Checked {counts['exchanges']} positional exchanges and {counts['joins']} join equations, "
          f"including {counts['inner drops']} strict drops with two inner markers.")
