"""Verify the two-strand group model and raw fourth-degree repairs through word attachments."""
import argparse
from itertools import permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, run


ONE = (0, 1, 2)
GROUP = tuple(permutations(ONE))
# All end groups above weight two are trivial. Combining these weights into
# one absorbing object gives the same finite table of morphism operations.
WEIGHTS = range(4)


def arrows(weight):
    return GROUP if weight == 2 else (ONE,)


def then(first, second):
    return tuple(second[i] for i in first)


def plus(left, right):
    return min(left + right, 3)


def tensor(left, f, right, g):
    if not left:
        return g
    if not right:
        return f
    return ONE


def check_model():
    for a, b in product(WEIGHTS, repeat=2):
        for f, h, g, k in product(arrows(a), arrows(a), arrows(b), arrows(b)):
            assert then(tensor(a, f, b, g), tensor(a, h, b, k)) == tensor(
                a, then(f, h), b, then(g, k))
    for a, b, c in product(WEIGHTS, repeat=3):
        for f, g, h in product(arrows(a), arrows(b), arrows(c)):
            assert tensor(plus(a, b), tensor(a, f, b, g), c, h) == tensor(
                a, f, plus(b, c), tensor(b, g, c, h))
            assert tensor(0, ONE, a, f) == tensor(a, f, 0, ONE) == f

    for crossing in GROUP:
        def braid(a, b):
            return crossing if a == b == 1 else ONE

        for a, b in product(WEIGHTS, repeat=2):
            for f, g in product(arrows(a), arrows(b)):
                assert then(tensor(a, f, b, g), braid(a, b)) == then(
                    braid(a, b), tensor(b, g, a, f))
        for a, b, c in product(WEIGHTS, repeat=3):
            assert braid(a, plus(b, c)) == then(
                tensor(plus(a, b), braid(a, b), c, ONE),
                tensor(b, ONE, plus(a, c), braid(a, c)))
            assert braid(plus(a, b), c) == then(
                tensor(a, ONE, plus(b, c), braid(b, c)),
                tensor(plus(a, c), braid(a, c), b, ONE))

    s, t = (1, 0, 2), (0, 2, 1)
    st = then(s, t)
    assert then(s, s) == then(t, t) == then(then(st, st), st) == ONE
    assert st != ONE and then(st, s) != then(s, st)
    print('Verified tensor and braid laws for all six S3 crossings, including noncentral st.')


def check_raw(checkout):
    base = '(x : *) (a : id(x) -> id(x))'
    loop = 'comp[a,a] -> comp[a,a]'
    e, unit, word = 'eh(x,a,a)', 'id(comp[a,a])', 'comp[s,t]'
    frame = f'{base} (s : {loop}) (t : {loop})'
    # Deliberately separate the two group letters. Both paths use a comparison
    # to a nonempty word before or after the cancellation declaration.
    out = f'{frame} (label : {e} -> {word}) (cancel : {word} -> {unit})'
    back = f'{frame} (expand : {unit} -> {word}) (labelback : {word} -> {e})'
    lines = [
        'import examples/eh',
        f'def contract {out} : {e} -> {unit} = comp[label,cancel]',
        f'def introduce {back} : {unit} -> {e} = comp[expand,labelback]',
        f'def right_context {out} : comp[{e},s] -> comp[{unit},s] = comp[[comp[label,cancel]],s]',
        f'def third_strand {back} : comp[[{unit}],a] -> comp[[{e}],a] = comp[[[comp[expand,labelback]]],a]',
    ]
    with TemporaryDirectory() as tmp:
        path = Path(tmp)
        (path / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (path / 'Ambient.catt').write_text('\n'.join(lines) + '\n')
        accepted(run(checkout / 'target/release/catt_strict', path, 'Ambient.catt'),
                 'Ambient.catt', ('contract', 'introduce', 'right_context', 'third_strand'))
    print('Rice checked both orientations, a non-base 3-cell context and a third strand.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    args = parser.parse_args()
    check_model()
    check_raw(args.checkout.resolve())
