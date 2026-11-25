"""Localize a scalar dependent history at one site, with signed comparison paths.

The input is the initial width and list of port steps of the serial packet solver.
Return the spectator-free closed program, the exterior braid, and the site paths
from the original history to the program run on the left of all spectators.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_serial_packet_group import inspect
from semistrict_surface_shared_edge import braid_image


def layout(data):
    if inspect(data) or not data['steps']:
        raise ValueError('a nonempty closed productive history with spectator-only ends is required')
    mobile = [False] * data['initial']
    program = []
    outside = ()
    for step in data['steps']:
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        inside_slot = sum(mobile[:a])
        mobile[a:a+p] = [True]*q
        seam = step.get('seam', ())
        inside = {i for i, bit in enumerate(mobile) if bit}
        program.append(dict(slot=inside_slot, input=p, output=q,
                            seam=restrict(len(mobile), seam, inside)))
        outside += restrict(len(mobile), seam, set(range(len(mobile))) - inside)
        for g in seam:
            i = abs(g)-1
            mobile[i], mobile[i+1] = mobile[i+1], mobile[i]
    return program, reduced(outside)


def expand(path, width, a, p, q):
    return cable(path, [1]*a + [q] + [1]*(width-a-p))


def localize(data):
    program, exterior = layout(data)
    # All mobile points are placed to the left of the spectators. Park the
    # entire spectator braid after the final death in that comparison history.
    width = data['initial']
    first_slot = data['steps'][0]['slot']
    path = tuple(range(first_slot, 0, -1))
    paths = []
    for i, (step, target) in enumerate(zip(data['steps'], program, strict=True)):
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        if i:
            keep = set(range(width)) - set(range(a+1, a+p))
            path = restrict(width, incoming, keep)
            if braid_image(width, expand(path, width, a, p, p)) != braid_image(width, incoming):
                return dict(localized=False, failed_site=i+1)
        # Check that the path identifies the actual substitution slots,
        # including a singleton port where recabling imposes no condition.
        order = list(range(width-p+1))
        for g in path:
            j = abs(g)-1
            order[j], order[j+1] = order[j+1], order[j]
        if order[target['slot']] != a:
            raise AssertionError('comparison does not carry the marked site')
        paths.append(path)
        after = expand(path, width, a, p, q)
        target_seam = target['seam']
        if i == len(program)-1:
            target_seam += exterior
        incoming = reduced(inv(step.get('seam', ())) + after + target_seam)
        width += q-p
    assert braid_image(width, incoming) == braid_image(width, ())
    return dict(localized=True, program=program, spectator_braid=exterior, site_paths=paths)


def verify(data, result):
    """Replay the end and seam squares from the certificate alone."""
    width = data['initial']
    assert len(result['program']) == len(data['steps']) == len(result['site_paths'])
    previous = ()
    for i, step in enumerate(data['steps']):
        a, p, q = (step[k] for k in ('slot', 'input', 'output'))
        target = result['program'][i]
        path = result['site_paths'][i]
        source = expand(path, width, a, p, p)
        assert braid_image(width, previous) == braid_image(width, source)
        after = expand(path, width, a, p, q)
        width += q-p
        target_seam = tuple(target['seam'])
        if i+1 == len(data['steps']):
            target_seam += tuple(result['spectator_braid'])
        previous = inv(step.get('seam', ())) + after + target_seam
    assert braid_image(width, previous) == braid_image(width, ())


def audit():
    from semistrict_surface_serial_packet_group import solve

    def step(slot, p, q, seam=()):
        return dict(slot=slot, input=p, output=q, seam=seam)

    yes = no = 0
    def check(data):
        nonlocal yes, no
        result = localize(data)
        assert result['localized'] == bool(solve(data)['free_rank'])
        if result['localized']:
            verify(data, result)
            yes += 1
        else:
            no += 1

    # All placements of one two-strand packet beside two spectators. Follow
    # the named strands to find the actual slot of the last written port.
    for length in range(4):
        for seam in product((1, -1, 2, -2, 3, -3), repeat=length):
            for start in range(3):
                names = list(range(4))
                for g in seam:
                    j = abs(g)-1
                    names[j], names[j+1] = names[j+1], names[j]
                slots = sorted(names.index(k) for k in (start, start+1))
                if slots[1] == slots[0]+1:
                    check(dict(initial=2, steps=[step(start, 0, 2, seam), step(slots[0], 2, 0, (1,))]))
    for middle, end in product([(), (3, 3), (-3, -3), (4,), (1, 1)],
                               [(), (2, 2), (-2, -2), (3,), (1, 1)]):
        check(dict(initial=2, steps=[step(0, 0, 3, middle), step(0, 2, 1, end), step(0, 2, 0)]))
    check(dict(initial=2, steps=[step(1, 0, 0, (-1,))]))
    print(f'{yes} localizations replayed at both ends and every signed seam; '
          f'{no} rejected histories agreed with the independent intersection test.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', type=Path, nargs='?')
    args = cli.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = localize(data)
        if result['localized']:
            verify(data, result)
        print(json.dumps(result, indent=2))
    else:
        audit()
