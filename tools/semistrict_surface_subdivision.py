"""Check the incidence and generic return calculations of Researcher Response 24."""
import argparse
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, coh_between, comp2, disc_tree, infer,
                  sub_from, subst_tm, subst_ty, tdim, tree_ctx, v)
from emit_agda import Emitter
from rc_oracle import _top
from relative_coherence_hidden_seam import identity
from semistrict_surface_return_gaps import Presentation
from semistrict_surface_scalar_cube import exchange


class Subdivision:
    def __init__(self, width, boundary=()):
        assert width >= 2
        self.width = width
        self.ctx = boundary
        self.chains = []

    def declare(self, ty):
        cell = v(len(self.ctx))
        self.ctx += (ty,)
        return cell

    def attach(self, ty):
        """Return the evaluation and one private top generator."""
        if ty == STAR:
            vertex = self.declare(ty)
            return vertex, vertex[1]
        _, base, source, target = ty
        middle = [self.attach(base) for _ in range(self.width - 1)]
        seams = [source, *(term for term, _ in middle), target]
        beads = [self.declare(arr(base, a, b)) for a, b in zip(seams, seams[1:])]
        rank = tdim(ty) + 1
        self.chains.append((rank, [b[1] for b in beads], [p for _, p in middle]))
        term = beads[0]
        for bead in beads[1:]:
            term = comp2(self.ctx, rank - 1, term, bead)
        assert infer(self.ctx, term) == ty
        return term, beads[0][1]


def check_incidence(chart, labels, samples):
    ctx = chart.ctx
    check_ctx(ctx)
    checks = 0
    for rank, beads, markers in chart.chains:
        for index, ty in enumerate(ctx):
            if tdim(ty) + 1 != rank:
                continue
            source, target = (_top(ctx, t) for t in ty[2:])
            assert source or target
            assert source.keys().isdisjoint(target)
            for j, marker in enumerate(markers):
                assert (target.get(marker, 0) - source.get(marker, 0)
                        == (index == beads[j]) - (index == beads[j + 1]))
                checks += 1
        for term in samples:
            ty = infer(ctx, term)
            if tdim(ty) + 1 != rank:
                continue
            top = _top(ctx, term)
            source, target = (_top(ctx, t) for t in ty[2:])
            for j, marker in enumerate(markers):
                assert (top.get(beads[j], 0) - top.get(beads[j + 1], 0)
                        == target.get(marker, 0) - source.get(marker, 0))
            if term in labels or ty[2] == ty[3]:
                assert len({top.get(bead, 0) for bead in beads}) == 1
    return checks


def composite_example(width, emitter):
    x = v(0)
    arrow = arr(STAR, x, x)
    ctx = (STAR, arrow)
    f = v(1)
    double = comp2(ctx, 0, f, f)
    unit = identity(ctx, x)
    ctx += (arr(arrow, double, f), arr(arrow, unit, unit))
    a, scalar = v(2), v(3)
    paste = comp2(ctx, 1, a, identity(ctx, f))
    ctx += (arr(infer(ctx, a), paste, a),)
    h = v(4)
    ctx += (arr(infer(ctx, h), h, h),)
    check_ctx(ctx)

    chart = Subdivision(width)
    labels = []
    for ty in ctx:
        labels.append(chart.attach(subst_ty(ty, labels))[0])
    samples = [*labels, *(v(i) for i in range(len(chart.ctx)))]
    for t in (double, paste, comp2(ctx, 1, scalar, scalar), comp2(ctx, 0, f, a)):
        samples.append(subst_tm(t, labels))
    checks = check_incidence(chart, labels, samples)
    for i, t in enumerate(labels):
        assert infer(chart.ctx, t) == subst_ty(ctx[i], labels)
    assert sum(_top(chart.ctx, labels[3]).values()) == width
    if emitter is not None:
        # Check the scalar and the cell attached to a non-variable 2-boundary.
        for i in (3, 4):
            prefix = chart.ctx[:max(_top(chart.ctx, labels[i])) + 1]
            emitter.check_type('translated' + str(i), prefix, labels[i], subst_ty(ctx[i], labels))
    return checks


def generic_return(rank, width):
    """Label the relative chart in its original globe, including the last seam."""
    disc = tree_ctx(disc_tree(rank))
    top = v(len(disc) - 1)
    if rank == 0:
        return [top], top
    smaller = tree_ctx(disc_tree(rank - 1))
    lower_labels, lower_eval = generic_return(rank - 1, width)
    target = disc[-1][3]
    target_map = sub_from(smaller, disc, {len(smaller) - 1: target})
    seam = subst_tm(lower_eval, target_map)
    source = disc[-1][2]
    first = coh_between(disc, disc_tree(rank), [top], source, seam)
    last = coh_between(disc, disc_tree(rank - 1), [target],
                       lower_eval, v(len(smaller) - 1))
    beads = [first, *[identity(disc, seam) for _ in range(width - 2)], last]
    labels = [subst_tm(t, target_map) for t in lower_labels] * (width - 1) + beads
    value = beads[0]
    for bead in beads[1:]:
        value = comp2(disc, rank - 1, value, bead)
    return labels, value


def check_return(rank, width, emitter):
    disc = tree_ctx(disc_tree(rank))
    chart = Subdivision(width, disc[:-1])
    evaluation, _ = chart.attach(disc[-1])
    extra, value = generic_return(rank, width)
    labels = [v(i) for i in range(len(disc) - 1)] + extra
    assert len(labels) == len(chart.ctx)
    for ty, term in zip(chart.ctx, labels):
        assert infer(disc, term) == subst_ty(ty, labels)
    assert subst_tm(evaluation, labels) == value
    top = v(len(disc) - 1)
    assert value != top and _top(disc, value) == {top[1]: 1}
    for k, (left, right) in enumerate(((value, top), (top, value))):
        witness = coh_between(disc, disc_tree(rank), [top], left, right)
        ty = arr(disc[-1], left, right)
        assert infer(disc, witness) == ty
        if emitter is not None:
            emitter.check_type(f'return{rank}dir{k}', disc, witness, ty)


def repeated_loop(emitter):
    """Decode the strict local 3-rules from the actual width-two presentation."""
    ctx = (STAR, arr(STAR, v(0), v(0)))
    unit = identity(ctx, v(1))
    ctx += (arr(infer(ctx, unit), unit, unit),)
    chart = Subdivision(2)
    labels = []
    for ty in ctx:
        labels.append(chart.attach(subst_ty(ty, labels))[0])
    check_ctx(chart.ctx)
    pairs = [beads for rank, beads, _ in chart.chains if rank == 2]
    (depart, arrive), = pairs
    outer = labels[1]
    leave, enter = chart.ctx[depart], chart.ctx[arrive]
    assert leave[2] == enter[3] == outer
    middle = leave[3]
    assert middle == enter[2] and middle != outer
    # Each strict path is one petal, with a different private interior vertex.
    interiors = []
    for path in (outer, middle):
        first, second = sorted(_top(chart.ctx, path))
        start, seam = chart.ctx[first][2:]
        assert start == labels[0] and seam != start
        assert chart.ctx[second][2:] == (seam, start)
        interiors.append(seam)
    assert interiors[0] != interiors[1]
    rules = [ty for ty in chart.ctx if tdim(ty) + 1 == 3]
    lap = comp2(chart.ctx, 1, v(depart), v(arrive))
    unit = identity(chart.ctx, outer)
    assert [ty[2:] for ty in rules] == [(unit, lap), (lap, unit)]
    square = exchange(chart.ctx, v(arrive), v(depart))
    emitter.check_type('newSquare', chart.ctx, square, infer(chart.ctx, square))

    # A history records only the side of each step. Within each side the two
    # beads alternate, so its starting state and this list recover every event.
    protected = lambda word: word.index('L') < word.rindex('R')
    checks = 0
    for size in (2, 4, 6, 8):
        for sides in product('LR', repeat=size):
            word = ''.join(sides)
            if word.count('L') % 2 != 1 or not protected(word):
                continue
            for i in range(size + 1):
                moves = []
                if word[i:i + 2] == 'RL':
                    moves.append(word[:i] + 'LR' + word[i + 2:])
                for side in 'LR':
                    on_outer = (word[:i].count(side) % 2 == (side == 'L'))
                    if on_outer:
                        lap = side * 2
                        moves.append(word[:i] + lap + word[i:])
                        if word[i:i + 2] == lap:
                            moves.append(word[:i] + word[i + 2:])
                assert all(protected(new) for new in moves)
                checks += len(moves)
    return checks


def check_overlapping_paths():
    """Verify protected events with rules whose windows cross the square's cut."""
    words = {'A': 'a', 'B': 'ab', 'C': 'bc', 'D': 'cd', 'E': 'abcd', 'F': 'd'}
    edges = {a: (i, i + 1) for i, a in enumerate('abcd')}
    marks = {}
    for token, word in words.items():
        edges[token] = (edges[word[0]][0], edges[word[-1]][1])
        marks['+' + token] = (word, token)
        marks['-' + token] = (token, word)
    pres = Presentation(edges, marks, [])
    start, end = 'Bcd', 'abD'

    def histories(path, steps):
        if path == end:
            yield steps
        if len(steps) < 6:
            for name, (source, target) in marks.items():
                offset = path.find(source)  # Distinct old letters make each window unique.
                if offset >= 0:
                    new = path[:offset] + target + path[offset + len(source):]
                    yield from histories(new, steps + ((offset, name),))

    def moves(steps):
        for new, _ in pres.moves(start, steps):
            yield new
        for i, path in enumerate(pres.walk(start, steps)):
            for token, word in words.items():
                offset = path.find(word)
                if offset >= 0:
                    lap = ((offset, '+' + token), (offset, '-' + token))
                    yield steps[:i] + lap + steps[i:]
                    if steps[i:i + 2] == lap:
                        yield steps[:i] + steps[i + 2:]

    def protected(steps):
        paths = pres.walk(start, steps)
        assert paths[-1] == end
        first, last = None, None
        for i, ((offset, name), path) in enumerate(zip(steps, paths)):
            lo = sum(len(words.get(c, c)) for c in path[:offset])
            hi = lo + len(words[name[1:]])
            if lo == 0 and first is None:
                first = i
                assert name == '-B'
            if hi == 4:
                last = i
        assert steps[last][1] == '+D'
        return first < last

    moves_checked = 0
    for steps in histories(start, ()):
        if protected(steps):
            for new in moves(steps):
                assert protected(new)
                moves_checked += 1
    return moves_checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    checks = 0
    for width in (2, 3, 4):
        checks += composite_example(width, emitter if width == 2 else None)
        for rank in (1, 2, 3):
            check_return(rank, width, emitter if width == 2 else None)
    print(f'{check_overlapping_paths()} moves with overlapping spatial windows')
    moves = repeated_loop(emitter)
    print(f'{moves} protected-order moves at the new boundary')
    print(f'{checks} generator incidence entries, 9 generic returns in both directions')
    if args.agda_dir:
        for name, imports in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            module = name + 'SurfaceSubdivision'
            source = emitter.module(module, __doc__)
            (args.agda_dir / (module + '.agda')).write_text(
                source.replace('open import CaTTExp.Pure', 'open import ' + imports))


if __name__ == '__main__':
    main()
