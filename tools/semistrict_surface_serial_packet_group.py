"""Decide the raw loop group of a gate-dependent scalar chain at its fixed ends.

Use {"initial": m, "steps": [{"slot": a, "input": p, "output": q, "seam": [...]}]}.
Each seam is the signed braid AFTER its event. Slots start at zero.
"""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import cyclic, inv
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_trefoil_mixed import substitute


def inspect(data):
    m = data['initial']
    if type(m) is not int or m < 0:
        raise ValueError('invalid initial width')
    owners = [-1] * m
    exterior = False
    for i, step in enumerate(data['steps']):
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        if any(type(x) is not int for x in (a, p, q)) or min(p, q) < 0 or not 0 <= a <= len(owners)-p:
            raise ValueError('invalid site ports')
        used = owners[a:a+p]
        if i and i-1 not in used:
            raise ValueError('consecutive sites have no common gate')
        exterior |= -1 in used
        owners[a:a+p] = [i]*q
        for g in step.get('seam', ()):
            if type(g) is not int or not 0 < abs(g) < len(owners):
                raise ValueError('invalid seam crossing')
            j = abs(g)-1
            owners[j], owners[j+1] = owners[j+1], owners[j]
    return exterior or any(k >= 0 for k in owners)


def resized_circle(circle, n, a, p, q):
    # Collapse an enclosed port to its first puncture, then expand that one.
    basis = [(i+1,) for i in range(a)]
    basis += [tuple(range(a+1, a+q+1))] + [()]*(p-1)
    basis += [(i+1+q-p,) for i in range(a+p, n)]
    return substitute(circle, basis)


def solve(data):
    exterior = inspect(data)
    steps, m = data['steps'], data['initial']
    if not steps or not m or exterior:
        return dict(free_rank=0, reason='no sites' if not steps else
                    'exterior gate used or produced' if exterior else 'no spectators')
    width = m
    for i, step in enumerate(steps):
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        if i:
            # A full twist at the input disk fixes the carried curve exactly
            # when their geometric intersection is zero.
            twist = tuple(range(a+1, a+p))*p
            twisted = substitute(circle, braid_image(width, twist))
            if cyclic(twisted) != cyclic(circle):
                return dict(free_rank=0, crossing_site=i+1, carried_curve=circle)
            circle = resized_circle(circle, width, a, p, q)
        else:
            circle = tuple(range(a+1, a+q+1))
        width += q-p
        circle = substitute(circle, braid_image(width, inv(step.get('seam', ()))))
    return dict(free_rank=m, reason='all input disks nested')


def extends(data, first):
    """Independently solve Response 52's tuple equations for one first-site braid."""
    width = data['initial']
    loop = first
    for i, step in enumerate(data['steps']):
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        if i:
            keep = set(range(width)) - set(range(a+1, a+p))
            marker = restrict(width, loop, keep)
            expanded = cable(marker, [1]*a + [p] + [1]*(width-a-p))
            if braid_image(width, loop) != braid_image(width, expanded):
                return False
            loop = marker
        across = cable(loop, [1]*a + [q] + [1]*(width-a-p))
        seam = tuple(step.get('seam', ()))
        loop = inv(seam) + across + seam
        width += q-p
    return braid_image(width, loop) == braid_image(width, ())


def audit():
    def event(a, p, q, seam=()):
        return dict(slot=a, input=p, output=q, seam=seam)

    checked = 0
    def compare(data, free_words):
        nonlocal checked
        rank = solve(data)['free_rank']
        for w in free_words:
            assert extends(data, push(w)) == (bool(rank) or not w), (data, w)
            checked += 1
        return rank

    comm = (1, 1, 2, 2, -1, -1, -2, -2)
    for pair in combinations(range(3), 2):
        assert braid_image(2, restrict(3, comm, set(pair))) == braid_image(2, ())
    for length in range(5):
        for seam in product((1, -1, 2, -2), repeat=length):
            row = [0, 1, 2]
            for g in seam:
                a = abs(g)-1
                row[a], row[a+1] = row[a+1], row[a]
            if row[2] == 2:
                compare(dict(initial=1, steps=[event(0, 0, 2, seam), event(0, 2, 0)]),
                        [(), (1,), (-1,), (1, 1)])
    assert not compare(dict(initial=1, steps=[event(0, 0, 2, comm), event(0, 2, 0)]), [(1,)])
    # Three born gates. Two enter the changing port, the third bypasses it.
    # Move the rightmost born gate around a spectator while the other two
    # remain together. Only the final merger can see this crossing.
    words = [(), (1,), (2,), (1, 2, -1, -2), (-2, 1)]
    for first, second in product([(), (1, 1), (2, 2), (3, 3), (4, 4)], [(), (1, 1), (2, 2), (3, 3)]):
        data = dict(initial=2, steps=[event(0, 0, 3, first), event(0, 2, 1, second), event(0, 2, 0)])
        compare(data, words)
    delayed = dict(initial=2, steps=[event(0, 0, 3, (3, 3)), event(0, 2, 1), event(0, 2, 0)])
    assert solve(delayed)['crossing_site'] == 3
    # Non-round carried disk survives at the intermediate port and returns.
    restored = dict(initial=2, steps=[event(0, 0, 3, (3, 3)), event(0, 2, 1, (-2, -2)), event(0, 2, 0)])
    assert compare(restored, words) == 2
    assert solve(dict(initial=2, steps=[event(1, 0, 0)]))['free_rank'] == 2
    for boundary in ([event(0, 1, 0)], [event(1, 0, 1)]):
        assert solve(dict(initial=1, steps=boundary))['free_rank'] == 0
    print(f'{checked} independent fixed-end tuple decisions agree, including the three-strand '
          'commutator and the delayed and restored mergers.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', type=Path, nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())), indent=2))
    else:
        audit()
