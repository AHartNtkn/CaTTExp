"""Signed motions of two packet births with empty initial end and named leaves."""
from argparse import ArgumentParser
from itertools import product
import json

from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import cyclic, inv, reduced
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_trefoil_mixed import substitute


def generators(p, q):
    # Number the meridians in positive perimeter order on each side.
    right_pushes = []
    for i in range(p, 0, -1):
        left = push((i,))
        reflected = tuple((1 if g > 0 else -1) * (p + 1 - abs(g)) for g in left)
        right_pushes.append(cable(reflected, [1] * p + [q]))
    left_pushes = [cable(push((j,)), [p] + [1] * q) for j in range(q, 0, -1)]
    return right_pushes + left_pushes


def expand(word, images):
    return reduced(x for g in word for x in (images[g-1] if g > 0 else inv(images[-g-1])))


def normal_form(p, q, word):
    # Eliminate the last left push using equality of the two perimeters.
    images = [(i,) for i in range(1, p + q)]
    images.append(inv(tuple(range(p + 1, p + q))) + tuple(range(1, p + 1)))
    return expand(word, images)


def solve(p, q, word, terminal=False):
    if min(p, q) < 1 or any(not 1 <= abs(g) <= p + q for g in word):
        raise ValueError('expected positive packet sizes and signed packet generator indices')
    normal = normal_form(p, q, word)
    answer = dict(free_normal_form=normal, trivial_terminal_braid=not normal)
    if terminal:
        braid = expand(word, generators(p, q))
        action = braid_image(p + q, braid)
        answer.update(terminal_artin_word=braid,
                      packet_curves=[cyclic(substitute(w, action)) for w in
                                     (range(1, p + 1), range(p + 1, p + q + 1))])
    return answer


def audit():
    for p, q in product(range(1, 5), repeat=2):
        gens = generators(p, q)
        left, right = tuple(range(1, p + 1)), tuple(range(p + 1, p + q + 1))
        perimeter = braid_image(p + q, cable((1, 1), [p, q]))
        for word in (left, right):
            assert braid_image(p + q, expand(word, gens)) == perimeter
        for stem in ((), (1,), (-p, p + q)):
            assert not normal_form(p, q, stem + left + inv(right) + inv(stem))
    # Compare equality of every pair via the induced bijection on the
    # observed classes, including cancellations and the perimeter relation.
    seen, reverse = {}, {}
    gens = generators(2, 2)
    letters = (*range(1, 5), *range(-4, 0))
    count = 0
    for n in range(4):
        for word in product(letters, repeat=n):
            normal = normal_form(2, 2, word)
            action = braid_image(4, expand(word, gens))
            assert seen.setdefault(normal, action) == action
            assert reverse.setdefault(action, normal) == normal
            count += 1
    # Along a reduced alternating word successive edges share exactly the
    # vertex fixed by the new syllable. A pure commutator has zero linking.
    commutator = (1, 3, -1, -3)
    path = [tuple(solve(2, 2, commutator[:i], True)['packet_curves']) for i in range(5)]
    assert len(set(path)) == 5
    for i, (before, after) in enumerate(zip(path, path[1:])):
        assert [j for j in range(2) if before[j] == after[j]] == [1 - i % 2]
    assert solve(2, 2, commutator)['free_normal_form'] == commutator
    print(f'{count} signed words gave {len(seen)} distinct Artin actions and free normal forms.')
    print('Both perimeters agree for all 16 size pairs. The commutator visits five distinct tree edges.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('sizes', type=int, nargs='*', metavar='N',
                        help='two packet sizes followed by signed packet generators')
    parser.add_argument('--terminal', action='store_true', help='also calculate the terminal braid and disk curves')
    args = parser.parse_args()
    if not args.sizes:
        audit()
    elif len(args.sizes) < 2:
        parser.error('supply both packet sizes')
    else:
        print(json.dumps(solve(*args.sizes[:2], args.sizes[2:], args.terminal), indent=2))
