"""Verify indexed disagreement on actual parallel schedules of grid squares."""

from check_interchange_grid_contractions import four_cells
from check_interchange_grid_windows import convert
from grid_loop_words import classes
from interchange_grid_occurrence import IndexedPaths
from interchange_grid_windows import Expressions


def check():
    n = 4
    letters, parents = four_cells(n)
    table = classes((n, n), (0, 0))

    def ends(w):
        p, f, g, q = w
        return table[p+g+f+q], table[p+f+g+q]

    wide = next(w for w in sorted(letters) if len(w[1]) == len(w[2]) == 2
                and ends(w)[0] == ends(w)[1])
    base = ends(wide)
    early, late = [w for w in sorted(letters) if ends(w) == base
                   and len(w[1]) == len(w[2]) == 1][:2]

    pads = Expressions()
    paths = IndexedPaths(pads, n, (0, 0))
    e, l = (pads.tile(convert(w)) for w in (early, late))
    u, v = pads.cat(l, e), pads.cat(e, l)
    square = paths.add(('atom', 0, 0, 0))

    def pad(p, child, q):
        return paths.add(('pad', p, child, q))

    def cat(a, b):
        return paths.add(('cat', a, b))

    # Two parallel routes doing two disjoint copies of the same square.
    straight = cat(pad(0, square, u), pad(v, square, 0))
    swapped = cat(pad(u, square, 0), pad(0, square, v))
    assert all(paths.disagrees(straight, swapped, i) for i in range(2))
    assert not paths.disagrees(straight, swapped, 2)
    assert paths.disagrees(square, straight, 1)  # shorter-end convention

    a, b = next(pair for pair, parent in parents.items() if parent == wide)
    whole = pads.tile(convert(wide))
    split = pads.cat(pads.tile(convert(a)), pads.tile(convert(b)))
    # Add a new column to the left of the temporal histories. Both rows cross
    # it first; its row word is ud. Compare distribution of this 3-action
    # through both immediate pads, using a different subdivision of each.
    larger = IndexedPaths(pads, n+1, (0, 0))
    head = larger.add(('atom', 0, 0, 0))
    inner = larger.add(('pad', whole, head, split))
    original = larger.add(('context', 'ud', inner, ''))
    lower_head = larger.add(('context', 'ud', head, ''))
    distributed = larger.add(('pad', pads.pad('ud', split, ''), lower_head,
                               pads.pad('ud', whole, '')))
    assert not larger.disagrees(original, distributed, 0)

    # Toggle only the terminal pair, retaining the same source and target at
    # each step. Computation visits one branch even after seventy doublings.
    forward, changed = straight, swapped
    source, target = pads.cat(u, u), pads.cat(v, v)
    for _ in range(69):
        first = pad(0, forward, source)
        changed = cat(first, pad(target, changed, 0))
        forward = cat(first, pad(target, forward, 0))
        source, target = pads.cat(source, source), pads.cat(target, target)
    size = 2**70
    assert paths.lengths[forward] == paths.lengths[changed] == size
    for i in (0, size//2, size-3):
        assert not paths.disagrees(forward, changed, i)
    for i in (size-2, size-1):
        assert paths.disagrees(forward, changed, i)
    print('Distributed 3-actions and distinct subdivisions agree on both selected 4-pads.')
    print(f'Checked the first differing square of parallel length-{size} schedules '
          f'at zero-based index {size-2} and checked its neighbours.')


if __name__ == '__main__':
    check()
