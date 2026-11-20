"""Check the rank-four semaphore construction on typed grids of planar gates."""

from collections import Counter
from functools import cache, reduce
from itertools import combinations, product

from catt import STAR, arr, check_ctx, comp2, infer, v
from relative_coherence_hidden_seam import identity


def rectangle(left, right, bottom, top):
    return frozenset(product(range(left, right + 1), range(bottom, top + 1)))


class Ring:
    def __init__(self, n):
        assert n >= 4
        last = 1 + 2 * (n - 3)
        left = rectangle(1, 1, 1, 3)
        top = [rectangle(x, x + 2, 3, 3) for x in range(1, last, 2)]
        right = rectangle(last, last, 1, 3)
        bottom = rectangle(1, last, 1, 1)
        self.core = [left, *top, right, bottom]
        outward = [(-1, 0), *[(0, 1)] * len(top), (1, 0), (0, -1)]
        self.balcony = [frozenset((x + dx, y + dy) for x, y in h)
                        for h, (dx, dy) in zip(self.core, outward)]
        self.box = [h | b for h, b in zip(self.core, self.balcony)]
        self.signal = [sorted(b)[len(b) // 2] for b in self.balcony]
        self.sites = rectangle(0, last + 1, 0, 4)
        self.n = n
        for i, j in combinations(range(n), 2):
            adjacent = (j - i) in (1, n - 1)
            assert bool(self.box[i] & self.box[j]) == adjacent
            assert bool(self.core[i] & self.core[j]) == adjacent
        for i, site in enumerate(self.signal):
            assert site not in set().union(*self.core)
            assert all(site not in self.box[j] for j in range(n) if j != i)

    def phase(self, site, process, resource):
        predecessor = (process - 1) % self.n
        return 2 * resource + int(site in self.box[predecessor])


def resource_count(programs):
    return 1 + max((op[1] for p in programs for op in p if op), default=0)


def typed_presentation(layout, programs):
    """Generate and type-check every declaration for these elementary programs."""
    resources = resource_count(programs)
    width = max(x for x, _ in layout.sites) + 1
    height = max(y for _, y in layout.sites) + 1
    ctx = (STAR,) * (width + 1)

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    wires = {(x, y): declare(arr(STAR, v(x), v(x + 1)))
             for x in range(width) for y in range(height + 1)}
    cells = {(s, b): declare(arr(infer(ctx, wires[s]), wires[s], wires[s[0], s[1] + 1]))
             for s in sorted(layout.sites)
             for b in range(2 if s in layout.signal else 2 * resources)}

    def arrow(a, b):
        assert infer(ctx, a) == infer(ctx, b)
        return declare(arr(infer(ctx, a), a, b))

    for s in sorted(layout.sites.difference(layout.signal)):
        for level in range(2 * resources - 1):
            arrow(cells[s, level], cells[s, level + 1])
    signals = [[arrow(cells[s, 0], cells[s, 1]) for _ in range(len(program) + 1)]
               for s, program in zip(layout.signal, programs)]

    def strip(sites, terms):
        order = sorted(sites)
        cut = 0 if order[0][0] != order[-1][0] else 1
        return reduce(lambda a, b: comp2(ctx, cut, a, b), (terms[s] for s in order))

    roots = {}
    holds = {}
    for i, h in enumerate(layout.core):
        for r in range(resources):
            pieces = {s: cells[s, layout.phase(s, i, r)] for s in h}
            roots[i, r] = strip(h, pieces)
            holds[i, r] = arrow(roots[i, r], roots[i, r])
    for i, program in enumerate(programs):
        h, balcony = layout.core[i], layout.balcony[i]
        sig = layout.signal[i]

        def face(stage, r, holding):
            pieces = {s: cells[s, layout.phase(s, i, r)] for s in balcony if s != sig}
            pieces[sig] = signals[i][stage]
            outer = strip(balcony, pieces)
            inner = holds[i, r] if holding else identity(ctx, roots[i, r])
            cut = 0 if min(h)[0] == max(h)[0] else 1
            return comp2(ctx, cut, inner, outer) if min(h) < min(balcony) else comp2(ctx, cut, outer, inner)

        for t, op in enumerate(program):
            if op is None:
                arrow(signals[i][t], signals[i][t + 1])
            else:
                kind, r = op
                arrow(face(t, r, kind == 'V'), face(t + 1, r, kind == 'P'))
    check_ctx(ctx)
    return len(ctx)


def thread_states(program):
    held = set()
    result = [frozenset()]
    for op in program:
        if op:
            kind, resource = op
            if kind == 'P':
                assert resource not in held
                held.add(resource)
            else:
                assert kind == 'V'
                held.remove(resource)
        result.append(frozenset(held))
    assert not held
    return result


def clock_chart(layout, programs, states, pos, moving, resources):
    """Build the strict spatial precedence graph from the actual phase words on sites."""
    slots = {s: [] for s in layout.sites if s not in layout.signal}
    for i, t in enumerate(pos):
        touched = programs[i][t] if i in moving else None
        for r in states[i][t]:
            if touched == ('V', r):
                continue
            for s in layout.core[i]:
                slots[s].append((layout.phase(s, i, r), ('hold', i, r)))
        if touched:
            r = touched[1]
            for s in layout.box[i] - {layout.signal[i]}:
                slots[s].append((layout.phase(s, i, r), ('marker', i, r)))

    after = {}
    indegree = Counter()

    def precedes(a, b):
        targets = after.setdefault(a, set())
        after.setdefault(b, set())
        if b not in targets:
            targets.add(b)
            indegree[b] += 1

    for s, carriers in slots.items():
        phases = [p for p, _ in carriers]
        assert len(phases) == len(set(phases)), (s, carriers)
        gates = {p: name for p, name in carriers}
        word = []
        for p in range(2 * resources):
            if p in gates:
                word.append(gates[p])
            if p + 1 < 2 * resources:
                word.append(('clock', s, p))
        for a, b in zip(word, word[1:]):
            precedes(a, b)
    ready = [a for a in after if indegree[a] == 0]
    visited = 0
    while ready:
        a = ready.pop()
        visited += 1
        for b in after[a]:
            indegree[b] -= 1
            if indegree[b] == 0:
                ready.append(b)
    return visited == len(after)


def compare_cubes(layout, programs):
    states = [thread_states(p) for p in programs]
    resources = resource_count(programs)
    choices = [range(len(p) + 1) for p in programs]
    legal = set()
    rejected = Counter()
    for pos in product(*choices):
        enabled = [i for i, t in enumerate(pos) if t < len(programs[i])]
        for n in range(len(enabled) + 1):
            for moving in combinations(enabled, n):
                needed = [states[i][t] | states[i][t + (i in moving)] for i, t in enumerate(pos)]
                capacity_ok = not set.intersection(*(set(holds) for holds in needed))
                actual = clock_chart(layout, programs, states, pos, moving, resources)
                assert actual == capacity_ok, (pos, moving)
                if actual:
                    legal.add((pos, moving))
                else:
                    rejected[n] += 1
    print('Legal chart counts by dimension:', sorted(Counter(len(m) for _, m in legal).items()),
          'rejected:', sorted(rejected.items()))
    return legal


def histories(programs, legal):
    end = tuple(map(len, programs))
    start = (0,) * len(end)

    @cache
    def visit(pos):
        if pos == end:
            return [()]
        out = []
        for n in range(1, len(pos) + 1):
            for moving in combinations(range(len(pos)), n):
                if (pos, moving) in legal:
                    nxt = tuple(x + (i in moving) for i, x in enumerate(pos))
                    out.extend((moving,) + tail for tail in visit(nxt))
        return out

    cells = visit(start)
    ids = {c: i for i, c in enumerate(cells)}
    sizes, ranks = Counter(), Counter()
    pivots = {}
    for c in cells:
        dim = sum(end) - len(c)
        sizes[dim] += 1
        column = 0
        for k, block in enumerate(c):
            for n in range(1, len(block)):
                for first in combinations(block, n):
                    second = tuple(i for i in block if i not in first)
                    column ^= 1 << ids[c[:k] + (first, second) + c[k + 1:]]
        while column and column.bit_length() in pivots:
            column ^= pivots[column.bit_length()]
        if column:
            pivots[column.bit_length()] = column
            ranks[dim] += 1
    betti = tuple(sizes[d] - ranks[d] - ranks[d + 1] for d in range(max(sizes) + 1))
    print('Endpoint chart strings:', len(cells), 'mod-two Betti numbers:', betti)
    return betti


def milestone_programs(dimension, boxes):
    """Compile open forbidden boxes on the coarse unit cube, including its boundary."""
    assert all(len(box) == dimension for box in boxes)
    programs, centers = [], []
    for i in range(dimension):
        program = []
        center = {}
        for j in (-1, 0, 1, 2):
            program.extend(('V', r) for r, box in enumerate(boxes) if box[i][1] == j)
            center[j] = len(program)
            program.append(None)
            program.extend(('P', r) for r, box in enumerate(boxes) if box[i][0] == j)
            program.append(None)
        programs.append(tuple(program))
        centers.append(center)
    return programs, centers


def square_boundary_milestones():
    # In C_L, when every coordinate is positive the set of unfinished coordinates
    # must be a face of L. These are the two minimal nonfaces of a square boundary.
    boxes = [tuple((0, 1 if i in pair else 2) for i in range(4))
             for pair in [(0, 2), (1, 3)]]
    programs, centers = milestone_programs(4, boxes)
    states = [thread_states(p) for p in programs]
    layout = Ring(4)
    for coord in product((0, 0.5, 1), repeat=4):
        # Sample the source/target centers and the unexpanded open gap between batches.
        pos = tuple(centers[i][x] if x in (0, 1)
                    else centers[i][0] + 1 + len(boxes) for i, x in enumerate(coord))
        active = {i for i, x in enumerate(coord) if x < 1}
        expected = 0 in coord or not ({0, 2} <= active or {1, 3} <= active)
        assert clock_chart(layout, programs, states, pos, (), len(boxes)) == expected
    print('Square-boundary compiler: all 81 coarse open faces agree with the spatial clock words.')


def projective_milestone_link():
    # Minimal nonfaces of the six-vertex triangulation in Ziemianski, section 6.
    forbidden = [(1, 2, 3), (2, 3, 4), (3, 4, 5), (4, 5, 1), (5, 1, 2),
                 (1, 3, 6), (2, 4, 6), (3, 5, 6), (4, 1, 6), (5, 2, 6)]
    boxes = [tuple((0, 1 if i + 1 in triple else 2) for i in range(6)) for triple in forbidden]
    programs, centers = milestone_programs(6, boxes)
    states = [thread_states(p) for p in programs]
    layout = Ring(6)
    faces = []
    for n in range(1, 7):
        row = []
        for moving in combinations(range(6), n):
            pos = tuple(centers[i][0] + 1 + len(boxes) if i in moving else centers[i][1]
                        for i in range(6))
            if clock_chart(layout, programs, states, pos, (), len(boxes)):
                row.append(moving)
        if row:
            faces.append(row)
    assert list(map(len, faces)) == [6, 15, 10]
    for prime, expected in [(2, (1, 1, 1)), (3, (1, 0, 0))]:
        ranks = [0]
        for lower, upper in zip(faces, faces[1:]):
            pivots = {}
            index = {f: i for i, f in enumerate(lower)}
            for f in upper:
                col = [0] * len(lower)
                for i in range(len(f)):
                    col[index[f[:i] + f[i + 1:]]] = (-1) ** i % prime
                while any(col):
                    j = next(i for i, value in enumerate(col) if value)
                    if j not in pivots:
                        pivots[j] = [v * pow(col[j], -1, prime) % prime for v in col]
                        break
                    col = [(a - col[j] * b) % prime for a, b in zip(col, pivots[j])]
            ranks.append(len(pivots))
        ranks.append(0)
        betti = tuple(len(f) - ranks[i] - ranks[i + 1] for i, f in enumerate(faces))
        assert betti == expected
        print(f'Six-process milestone past link mod {prime}: {betti}.')


if __name__ == '__main__':
    ring = Ring(4)
    neutral = [(None,)] * 4
    assert clock_chart(ring, neutral, [thread_states(p) for p in neutral],
                       (0,) * 4, tuple(range(4)), resource_count(neutral))
    typed_presentation(ring, neutral)
    single = [(('P', 0), ('V', 0))] * 4
    print('Checked CaTT declarations:', typed_presentation(ring, single))
    legal = compare_cubes(ring, single)
    betti = histories(single, legal)
    assert betti[:3] == (1, 0, 1) and not any(betti[3:])
    # One thread holds both resources, with a private step during the overlap.
    double = [(('P', 0), ('P', 1), None, ('V', 0), ('V', 1)),
              (('P', 1), ('V', 1)), (('P', 0), ('V', 0)), (('P', 0), ('V', 0))]
    compare_cubes(ring, double)
    print('Checked two-resource CaTT declarations:', typed_presentation(ring, double))
    square_boundary_milestones()
    projective_milestone_link()
