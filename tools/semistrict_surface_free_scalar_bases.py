"""Read the pure or mixed test for free 3-scalars over an ordinary planar base."""
from argparse import ArgumentParser
import json
from pathlib import Path

from catt import STAR, arr, comp2, infer, subst_tm, v
from ct_suspension import ident
from emit_agda import Emitter
from semistrict_surface_join_bubbles import bubble
from semistrict_surface_top_string_tester import check_map, emit_map


def test_base(data, width):
    roots = set(data['probes'])
    gates = data['rules']
    # A positive run on the empty word needs both its first and its last step
    # at its root. Intermediate steps may take place at any object.
    starts = {x for x, a, _ in gates.values() if not a}
    ends = {x for x, _, b in gates.values() if not b}
    candidate_roots = roots & starts & ends
    witness = bubble(data['edges'], gates, width, roots=candidate_roots)
    if not roots:
        return dict(test='no probes')
    if not candidate_roots:
        return dict(test='pure')
    if witness is None:
        return dict(test='undetermined', checked_width=width)
    root, history = witness
    return dict(test='mixed', object=root, positive_history=history)


def typed(directory):
    mixed = (STAR,)
    unit = ident(mixed, v(0))
    blank = ident(mixed, unit)
    mixed += (arr(infer(mixed, unit), unit, unit), arr(infer(mixed, blank), blank, blank))
    # The graph x -> y is connected. A floating segment is born and dies at y.
    ctx = (STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(1), v(1)))
    y_unit = ident(ctx, v(1))
    ctx += (arr(infer(ctx, y_unit), y_unit, v(3)), arr(infer(ctx, y_unit), v(3), y_unit))
    at_x, at_y = [ident(ctx, ident(ctx, v(i))) for i in (0, 1)]
    ctx += (arr(infer(ctx, at_x), at_x, at_x), arr(infer(ctx, at_y), at_y, at_y))
    core = comp2(ctx, 1, v(4), v(5))
    place = (v(1), core, v(7))
    read = (v(0), v(0), unit, unit, v(1), blank, ident(mixed, blank), v(2))
    check_map(mixed, ctx, place)
    check_map(ctx, mixed, read)
    assert subst_tm(core, read) == comp2(mixed, 1, v(1), blank)
    assert subst_tm(place[2], read) == v(2)
    if directory:
        e = Emitter()
        emit_map(e, 'placeMixed', mixed, ctx, place)
        emit_map(e, 'selectBirth', ctx, mixed, read)
        e.check_eq('readCore', core, read, comp2(mixed, 1, v(1), blank))
        e.check_eq('readProbe', v(7), read, v(2))
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'FreeScalarBases.agda').write_text(e.module('FreeScalarBases', __doc__))


def audit():
    data = dict(edges={'u': ('x', 'y'), 'f': ('y', 'y')},
                rules={'b': ('y', '', 'f'), 'd': ('y', 'f', '')}, probes=[])
    assert test_base(data, 2)['test'] == 'no probes'
    data['probes'] = ['x']
    assert test_base(data, 2)['test'] == 'pure'
    data['probes'] = ['y']
    assert test_base(data, 0)['test'] == 'undetermined'
    assert test_base(data, 1)['positive_history'] == [(0, 'b'), (0, 'd')]
    # A return at marked x can require a birth at unmarked y inside a wire loop.
    data['edges']['v'] = ('y', 'x')
    data['rules'] = {'open': ('x', '', 'uv'), 'inner': ('y', '', 'f'),
                     'close': ('x', 'ufv', '')}
    data['probes'] = ['x']
    assert test_base(data, 2)['test'] == 'undetermined'
    assert test_base(data, 3)['positive_history'] == [(0, 'open'), (1, 'inner'), (0, 'close')]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='JSON with edges, rules, and probe objects')
    parser.add_argument('--width', type=int, default=4)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(test_base(json.loads(args.input.read_text()), args.width)))
        return
    audit()
    typed(args.agda_dir)
    print('Checked rooted witnesses, the two-object probe placements, and both mixed substitutions.')


if __name__ == '__main__':
    main()
