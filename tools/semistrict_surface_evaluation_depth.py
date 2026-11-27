"""Audit the relative attachments for rank-wise evaluation in round 3, Response 4."""
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import product

from semistrict_surface_temporal_ideals import Atom, Box, Row, check_horns, compose, events, lower


@dataclass(frozen=True)
class Head(Atom):
    argument: Row


def depth(row):
    def factor_depth(factor):
        if isinstance(factor, Box):
            return 1 + max(depth(factor.left), depth(factor.right))
        if isinstance(factor, Head):
            return 1 + depth(factor.argument)
        return 0
    return max((factor_depth(f) for f in row.factors), default=0)


def readings(bound):
    """All reduced readings within a constructor count (temporal seams cost zero)."""
    by_size = [{Row(0), Row(1)}]
    for n in range(1, bound + 1):
        layer = {Row(a.source, (Head(a.source, a.target, a),)) for a in by_size[n-1]}
        if n == 1:
            layer.update(Row(s, (Atom(s, t),)) for s, t in product(range(2), repeat=2))
        for k in range(n):
            for a, b in product(by_size[k], by_size[n-1-k]):
                if a.factors or b.factors:
                    layer.update(lower(j, a, b) for j in (0, 1))
        for k in range(1, n):
            for a, b in product(by_size[k], by_size[n-k]):
                if a.target == b.source and len(b.factors) == 1:
                    joined = compose(a, b)
                    if len(joined.factors) == len(a.factors) + 1:
                        layer.add(joined)
        by_size.append(layer)
    return set.union(*by_size)


def check():
    arrows = readings(3)
    # Independent enumeration by actual composition, including stationary factors.
    cuts = defaultdict(set)
    for a in arrows:
        for b in arrows:
            if a.target != b.source:
                continue
            f = compose.__wrapped__(a, b)
            if f in arrows:
                cuts[f].add((a, b))
                assert depth(a) <= depth(f) and depth(b) <= depth(f)

    @cache
    def strings(f, n):
        if n == 1:
            return {(f,)}
        return {(a, *rest) for a, b in cuts[f] for rest in strings(b, n-1)}

    boxes = opaque = serial = horns = 0
    for f in arrows:
        if not f.factors:
            continue
        for n in range(1, len(events(f)) + 1):
            flags = {s for s in strings(f, n) if all(a.factors for a in s)}
            if len(f.factors) > 1:
                serial += len(flags)
            elif isinstance(f.factors[0], Box):
                box = f.factors[0]
                lifts = defaultdict(int)
                for left, right in product(strings(box.left, n), strings(box.right, n)):
                    image = tuple(lower(box.cut, a, b) for a, b in zip(left, right, strict=True))
                    if all(a.factors for a in image):
                        lifts[image] += 1
                assert lifts == dict.fromkeys(flags, 1)
                boxes += len(flags)
            else:
                assert flags == {(f,)}
                opaque += isinstance(f.factors[0], Head)
        if len(f.factors) > 1:
            horns += check_horns(events(f))
    print(f'{len(arrows)} reduced arrows. Verified {boxes} unique product flags, '
          f'{opaque} indivisible head instances, and {serial} serial flags ({horns} inner horns).')

    # On larger inputs force folds, empty images, and both kinds of constructor
    # around a consecutive word. Test the substitution law as an equality of
    # actual arrows, with all component seams and opaque arguments retained.
    def substitute(f, letter):
        result = Row(0)
        for factor in f.factors:
            if isinstance(factor, Box):
                part = lower(factor.cut, substitute(factor.left, letter),
                             substitute(factor.right, letter))
            elif isinstance(factor, Head):
                argument = substitute(factor.argument, letter)
                part = Row(0, (Head(0, 0, argument),))
            else:
                part = letter(factor)
            result = compose(result, part)
        return result

    x = Row(0, (Atom(0, 0),))
    actions = (Row(0), x, compose(x, x), lower(1, x, x), Row(0, (Head(0, 0, x),)))
    substitutions = 0
    for image in actions:
        def first(a):
            return image if a.source == a.target else x
        for later in actions:
            def second(a):
                return later
            def composite(a):
                return substitute(first(a), second)
            for f in arrows:
                assert substitute(substitute(f, first), second) == substitute(f, composite)
                substitutions += 1
    print(f'{substitutions} iterated substitutions agree on their full readings.')


if __name__ == '__main__':
    check()
