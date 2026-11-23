"""Check the Moore path sweep at all slots and intermediate times of an insertion."""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory

from partial_cylinder_steiner import trees
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_scalar_pairs import branches, splice, trunk


@dataclass(frozen=True)
class Diagram:
    cells: tuple
    children: tuple = ()


@cache
def height(tree):
    return max((1 + height(c) for c in tree), default=0)


def identity(cell, times=1):
    for _ in range(times):
        cell = (cell,)
    return cell


def sample_cell(rank, ends, rng):
    if rank == 0:
        return rng.randrange(3)
    a, b = ends
    if a == b and rng.randrange(3):
        return (a,)
    lower = None if rank == 1 else (a[0], a[-1])
    middle = tuple(sample_cell(rank-1, lower, rng) for _ in range(rng.randrange(2)))
    return (a,) + middle + (b,)


def labelling(tree, rng, rank=0, ends=None):
    cells = tuple(sample_cell(rank, ends, rng) for _ in range(len(tree)+1))
    return Diagram(cells, tuple(labelling(c, rng, rank+1, cells[i:i+2]) for i, c in enumerate(tree)))


def compose(left, right, above_cut):
    if above_cut == 1:
        assert left[-1] == right[0]
        return left + right[1:]
    start = [compose(x, right[0], above_cut-1) for x in left]
    finish = [compose(left[-1], y, above_cut-1) for y in right[1:]]
    return tuple(start + finish)


def standard(d, remaining):
    if not d.children:
        return identity(d.cells[0], remaining)
    assert remaining > 0
    parts = iter(standard(c, remaining-1) for c in d.children)
    result = next(parts)
    for part in parts:
        result = compose(result, part, remaining)
    return result


def constant(d, cell):
    return Diagram((cell,) * len(d.cells), tuple(constant(c, (cell,)) for c in d.children))


def sweep(d, depth, time):
    if depth == 1:
        cells = [d.cells[0]]
        children = []
        for c in d.children:
            path = c.cells[0]
            if time:
                spent = min(time, len(path)-1)
                prefix = path[:spent+1]
                time -= spent
                assert prefix[0] == cells[-1]
            else:
                prefix = (cells[-1],)
            children.append(constant(c, prefix))
            cells.append(prefix[-1])
        return Diagram(tuple(cells), tuple(children)), time
    children = []
    for c in d.children:
        partial, time = sweep(c, depth-1, time)
        children.append(partial)
    return Diagram(d.cells, tuple(children)), time


def duration(d, depth):
    if depth == 1:
        return sum(len(c.cells[0])-1 for c in d.children)
    return sum(duration(c, depth-1) for c in d.children)


def disc(top, depth):
    if not depth:
        return Diagram((top,))
    a = b = top
    for _ in range(depth):
        a, b = a[0], b[-1]
    return Diagram((a, b), (disc(top, depth-1),))


def exterior(d, path, inner, slot_rank):
    i, *tail = path
    if tail:
        child = exterior(d.children[i], tail, inner[0], slot_rank-1)
        return Diagram(d.cells, d.children[:i] + (child,) + d.children[i+1:])
    end = i + len(inner)
    block = Diagram(d.cells[i:end+1], d.children[i:end])
    old_disc = disc(standard(block, slot_rank), slot_rank)
    assert old_disc.cells == (d.cells[i], d.cells[end])
    return Diagram(d.cells[:i+1]+d.cells[end:], d.children[:i]+old_disc.children+d.children[end:])


def check_insertions(limit=5):
    counts = Counter()
    rng = Random(483071)
    shapes = [t for size in range(limit+1) for t in trees(size)]
    for outer in shapes:
        for path, rank in branches(outer):
            for inner in shapes:
                if trunk(inner) < len(path)-1 or height(inner) > rank:
                    continue
                joined = splice(outer, path, inner)
                labels = labelling(joined, rng)
                original = exterior(labels, path, inner, rank)
                assert standard(original, height(outer)) == standard(labels, height(outer))
                counts['standard composites'] += 1
                for depth in range(1, height(outer)+1):
                    total = duration(labels, depth)
                    assert duration(original, depth) == total
                    for time in range(total+1):
                        partial, unused = sweep(labels, depth, time)
                        other, remaining = sweep(original, depth, time)
                        assert unused == remaining == 0
                        assert exterior(partial, path, inner, rank) == other
                        counts['complete intermediate tuples'] += 1
                        if 0 < time < total:
                            counts['interior times'] += 1
                    if not total:
                        counts['zero-duration stages'] += 1
    # Independent check: horizontal motion of two paths crosses the product
    # through its left-hand corner, distinguishing the directed exchange.
    left = ((0, 1), (0, 2, 1))
    right = ((1, 3), (1, 4, 3))
    route = compose(left, right, 2)
    assert route == ((0, 1, 3), (0, 2, 1, 3), (0, 2, 1, 4, 3))
    assert route[1] != compose(left[0], right[-1], 1)
    return counts


def check_matching_clocks():
    # A split carrier is the product of its blocks. At either projection the
    # external path runs from the common source clock to the block's clock.
    grid = tuple(Fraction(i, 4) for i in range(5))
    def between(first, last, u):
        return (1-u)*first + u*last

    def at(start, delta, elapsed, duration):
        assert duration or not delta
        if duration == 0:
            return start
        return start + delta * min(1, max(0, elapsed/duration))

    def concat(start, increments, durations, time):
        for delta, length in zip(increments, durations, strict=True):
            if time <= length:
                return at(start, delta, time, length)
            time -= length
            start += delta
        return start

    checks = mismatches = 0
    for left, right, more_left, more_right in product(range(3), repeat=4):
        initial = (max(left, right), max(more_left, more_right))
        blocks = ((left, more_left), (right, more_right))
        mismatches += any(pair[0] != pair[1] for pair in ((left, right), (more_left, more_right)))
        for lengths in blocks:
            increments = tuple((2-i)*bool(length) for i, length in enumerate(lengths))
            for u in grid:
                local = tuple(between(a, b, u) for a, b in zip(initial, lengths))
                for t in grid:
                    clock = t * sum(local)
                    result = concat(0, increments, local, clock)
                    # Independently clamp the spent time in each piece.
                    expected = sum(at(0, inc, clock-sum(local[:i]), local[i])
                                   for i, inc in enumerate(increments))
                    assert result == expected
                    if u in (0, 1):
                        end = initial if u == 0 else lengths
                        assert result == concat(0, increments, end, t*sum(end))
                    checks += 1
    # A normalized track may move inside a parameter interval even if both
    # prescribed endpoint lifts and the reference path have length zero.
    for u, t in product(grid, repeat=2):
        length = 4*u*(1-u)
        value = u*(1-u)*t
        assert length or value == 0
        assert at(0, u*(1-u), t*length, length) == value
    return checks, mismatches


def check_checker(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (work / 'Expanded.catt').write_text("""import examples/eh-common
def expanded = coh [ [[a,b],[c]] : swap_src(comp[a,b],c) -> swap_tgt(comp[a,b],c) ]
def nested {f{a}g{b}h}{i{c}j} = swap(comp[a,b],c)
""")
        (work / 'Compare.catt').write_text("""import Expanded
def insertion {f{a}g{b}h}{i{c}j} : nested(a,b,c) -> expanded(a,b,c) = id(expanded(a,b,c))
""")
        raw = run(binary, work, 'Expanded.catt')
        accepted(raw, 'Expanded.catt', ['nested'])
        assert 'Inferring expanded\n' in raw
        accepted(run(binary, work, 'Compare.catt', ['--sua']), 'Compare.catt', ['insertion'])
        rejected(run(binary, work, 'Compare.catt', ['--su']), 'Compare.catt', 'insertion')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    for name, n in check_insertions().items():
        print(f'{n:,} {name}')
    print('product path evaluations and unequal-clock cases:', *check_matching_clocks())
    if args.catt_strict:
        check_checker(args.catt_strict.resolve())
        print('checked insertion at the nonstandard swap head')
