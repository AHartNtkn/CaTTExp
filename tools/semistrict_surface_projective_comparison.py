"""Check the oriented two-particle cover and its raw scalar exchange boundaries."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
from math import prod
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_join_repair_tower import validate


def project(face):
    # A cell of the antipodal quotient is a pair of opposite signed faces.
    # Use increasing axis order to orient both lifts and their image.
    first_sign = face[0][1]
    return tuple((axis, sign * first_sign) for axis, sign in face)


def boundary(chain):
    result = Counter()
    for face, coefficient in chain.items():
        for i in range(len(face)):
            result[face[:i] + face[i + 1:]] += (-1) ** i * coefficient
    return {face: value for face, value in result.items() if value}


def push(chain):
    result = Counter()
    for face, coefficient in chain.items():
        result[project(face)] += coefficient
    return {face: value for face, value in result.items() if value}


def check_cover(rank):
    cycle = {}
    hemisphere = {}
    for signs in product((-1, 1), repeat=rank):
        facet = tuple(enumerate(signs))
        cycle[facet] = prod(signs)
        if signs[-1] == 1:
            hemisphere[facet] = cycle[facet]
    assert not boundary(cycle)
    # One sheet relative to its equator gives the top-cell generator
    # after the quotient by RP^(rank-2).
    assert all(face[-1][0] < rank - 1 for face in boundary(hemisphere))
    sheet = push(hemisphere)
    assert len(sheet) == 2 ** (rank - 1) and set(map(abs, sheet.values())) == {1}
    image = push(cycle)
    degrees = {image.get(face, 0) * orientation for face, orientation in sheet.items()}
    assert degrees == {1 + (-1) ** rank}
    return len(cycle), degrees.pop()


def check_boundaries(checkout, ranks):
    rows = []
    for rank in ranks:
        base = 'x'
        for _ in range(rank - 2):
            base = f'id({base})'
        context = f'(x : *) (a : id({base}) -> id({base}))'
        word = 'comp[a,a]'
        rows.append((rank, context, base, 'a', word, f'eh({base},a,a)', f'id({word})'))
    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for flags in ((), ('--su',)):
            validate(checkout / 'target/release/catt_strict', directory, flags, rows)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=Path, help='Rice checker checkout with release binary')
    args = parser.parse_args()
    for rank in range(3, 10):
        facets, degree = check_cover(rank)
        print(f'Rank {rank}: projected {facets} oriented facets, relative degree {degree}.')
    if args.checkout:
        check_boundaries(args.checkout.resolve(), range(3, 7))
        print('Rice checked the weak exchange faces and their strict-unit swap at ranks 3 through 6.')
