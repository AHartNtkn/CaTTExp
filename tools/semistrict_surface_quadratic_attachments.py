"""Test joined degree-five differences with quadratic and linear four-cell attachments."""

from argparse import ArgumentParser
from itertools import product

from semistrict_surface_reversible_five import quotient


def joined_reading(r, s, attachments, relations, face):
    quadratic = r * (r + 1) // 2
    if min(r, s) < 0 or any(len(row) != quadratic + s for row in attachments):
        raise ValueError('expected one quadratic and linear boundary vector per four-cell')
    mixed = r * s
    for vector in [*relations, face]:
        if len(vector) != mixed + len(attachments):
            raise ValueError('expected mixed entries followed by one degree per four-cell')
        degrees = vector[mixed:]
        if any(sum(d*a[i] for d, a in zip(degrees, attachments, strict=True))
               for i in range(quadratic + s)):
            raise ValueError('the proposed four-cell degrees have nonzero spherical boundary')
    rows = list(relations)
    for i in range(r):
        for cell in attachments:
            relation = [0] * len(face)
            relation[i*s:(i+1)*s] = cell[quadratic:]
            rows.append(relation)
    return quotient(rows, face)


def audit():
    count = 0
    for d, v, p, q in product(range(1, 6), (-2, 0, 3), (-1, 1, 2), (0, 1, 3)):
        attachments = [[1, -d], [v, -v*d]]
        relations = [[p, -v*q, q]]
        for x, y in product(range(-3, 4), repeat=2):
            face = [x, -v*y, y]
            # A multiple of the single relation must match the free degree
            # exactly and the mixed coefficient modulo d.
            if q:
                expected = y % q == 0 and (x - p * (y//q)) % d == 0
            else:
                expected = y == 0 and any((x - p*n) % d == 0 for n in range(d))
            assert (not any(joined_reading(1, 1, attachments, relations, face))) == expected
            count += 1
    cross = [[0, 0, 1, 2, -3]]
    # Two independent mixed summands; linear relations apply in each.
    assert not any(joined_reading(2, 2, cross, [], [2, -3, -4, 6, 0]))
    assert any(joined_reading(2, 2, cross, [], [2, 0, 0, -3, 0]))
    try:
        joined_reading(2, 2, cross, [], [0, 0, 0, 0, 1])
    except ValueError as error:
        assert 'spherical boundary' in str(error)
    else:
        raise AssertionError('accepted a nonspherical four-cell degree')
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bottom', nargs=2, type=int, metavar=('R', 'S'))
    parser.add_argument('--attach', action='append', nargs='*', type=int, default=[])
    parser.add_argument('--rel', action='append', nargs='*', type=int, default=[])
    parser.add_argument('--face', nargs='*', type=int)
    args = parser.parse_args()
    if args.bottom is None and args.face is None and not (args.attach or args.rel):
        print(f'{audit()} joined lattice comparisons and the two-colour and spherical degree checks passed.')
    elif args.bottom is None or args.face is None:
        parser.error('provide --bottom and --face together')
    else:
        try:
            result = joined_reading(*args.bottom, args.attach, args.rel, args.face)
        except ValueError as error:
            parser.error(str(error))
        print(f'joined fills: {not any(result)}')
