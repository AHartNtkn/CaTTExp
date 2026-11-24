"""Verify the weight-two monoidal categories that distinguish a repair's whiskers."""
import argparse
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, run


@dataclass(frozen=True)
class Arrow:
    source: int
    target: int
    # () denotes an identity, None an absorbing arrow; (left,right) a single mark.
    mark: tuple | None


def identity(i):
    return Arrow(i, i, ())


def vertical(a, b):
    if a.target != b.source:
        raise ValueError('vertical seam mismatch')
    if a.mark == ():
        return b
    if b.mark == ():
        return a
    return Arrow(a.source, b.target, None)


def horizontal(a, b):
    s, t = a.source ^ b.source, a.target ^ b.target
    if a.mark is None or b.mark is None or (a.mark and b.mark):
        return Arrow(s, t, None)
    if a.mark:
        return Arrow(s, t, (a.mark[0], a.mark[1] ^ b.source))
    if b.mark:
        return Arrow(s, t, (a.source ^ b.mark[0], b.mark[1]))
    return identity(s)


def verify(source, target):
    two = (0, 1)
    arrows = [identity(i) for i in two] + [Arrow(i, j, None) for i, j in product(two, repeat=2)]
    for l, r in product(two, repeat=2):
        arrows.append(Arrow(l ^ source ^ r, l ^ target ^ r, (l, r)))
    pairs = [(a, b) for a in arrows for b in arrows if a.target == b.source]
    for a in arrows:
        assert vertical(identity(a.source), a) == a == vertical(a, identity(a.target))
        assert horizontal(identity(0), a) == a == horizontal(a, identity(0))
    for a, b, c in product(arrows, repeat=3):
        assert horizontal(horizontal(a, b), c) == horizontal(a, horizontal(b, c))
        if a.target == b.source and b.target == c.source:
            assert vertical(vertical(a, b), c) == vertical(a, vertical(b, c))
    for (a, b), (c, d) in product(pairs, repeat=2):
        assert horizontal(vertical(a, b), vertical(c, d)) == vertical(horizontal(a, c), horizontal(b, d))
    for l, r in product(two, repeat=2):
        mark = Arrow(l ^ source ^ r, l ^ target ^ r, (l, r))
        left, right = horizontal(identity(1), mark), horizontal(mark, identity(1))
        assert (left.source, left.target) == (right.source, right.target) and left != right
    return len(pairs)**2


def rice(checkout):
    ctx = '(x : *) (a : id(x) -> id(x))'
    w = 'comp[a,a]'
    for raw in (True, False):
        braid = 'eh(x,a,a)' if raw else f'id({w})'
        args = f'{ctx} (k : {braid} -> id({w}))'
        l = f'comp[comp[{braid},[k]],unitor_r({braid})]'
        r = f'comp[comp[[k],{braid}],unitor_l({braid})]'
        ty = f'comp[{braid},{braid}] -> {braid}'
        if raw:
            lines = [f'def leftslide {args} : {ty} = {l}', f'def rightslide {args} : {ty} = {r}']
        else:
            lines = [f'def leftslide {args} : {l} -> k = id(k)', f'def rightslide {args} : {r} -> k = id(k)']
        with TemporaryDirectory() as tmp:
            folder = Path(tmp)
            (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
            (folder / 'Marks.catt').write_text('\n'.join(['import examples/eh', *lines, '']))
            log = run(checkout / 'target/release/catt_strict', folder, 'Marks.catt',
                      () if raw else ('--su',))
            accepted(log, 'Marks.catt', ('leftslide', 'rightslide'))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rice-dir', type=Path)
    args = p.parse_args()
    total = sum(verify(s, t) for s, t in product((0, 1), repeat=2))
    print(f'4 parity choices, {total} monoidal interchange checks, 16 separated whisker pairs')
    if args.rice_dir:
        rice(args.rice_dir.resolve())
        print('Rice checked both raw slides and their strict-unit reductions after replacing the crossing by an identity')
