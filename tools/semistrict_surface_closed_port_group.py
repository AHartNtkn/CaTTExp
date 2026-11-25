"""Compute the fixed-end raw group of a dependent chain of positioned planar ports.

Input is the positioned chart and seam format of semistrict_surface_serial_gate_tracks.
The supplied site loops are optional and are replaced by computed loops.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_component_braids import Components, Group, cabling, restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, realize, reduced
from semistrict_surface_pocket_chain import trace
from semistrict_surface_serial_gate_tracks import read_track
from semistrict_surface_shared_edge import braid_image


def first_basis(data):
    first = data['charts'][0]
    diagram = tuple(map(tuple, first['diagram']))
    ports = {g: (s, t) for g, (_, s, t) in data['gates'].items()}
    group = Group(diagram, ports, len(data['path']))
    pos = group.loc[first['slot']]
    for face in group.packets:
        for j, (_, left, right) in enumerate(face):
            if left != pos or right != pos+1:
                continue
            basis = []
            for k in range(len(face)):
                if k == j:
                    continue
                i, end = sorted((j, k))
                # Approach the other sibling, wind once, and return.
                move = tuple(range(i+1, end))
                turn = move + (end, end) + inv(move)
                path = group.path + cabling(face, turn) + inv(group.path)
                basis.append(path)
            return basis
    raise AssertionError('point marker has no sibling face')


def lift(data, first):
    paths = []
    ports = {g: (s, t) for g, (_, s, t) in data['gates'].items()}
    for i, chart in enumerate(data['charts']):
        d = tuple(map(tuple, chart['diagram']))
        a = chart['slot']
        p, q = len(chart['input']), len(chart['output'])
        if i:
            seam = tuple(data['seams'][i-1])
            incoming = reduced(inv(seam) + after + seam)
            n = len(d)-1+p
            keep = set(range(n)) - set(range(a+1, a+p))
            path = restrict(n, incoming, keep)
            back = cable(path, [1]*a + [p] + [1]*(len(d)-a-1))
            if braid_image(n, back) != braid_image(n, incoming):
                return None
        else:
            path = first
        legal = realize(d, d, path, ports)
        if legal is None:
            return None
        paths.append(legal)
        after = cable(legal, [1]*a + [q] + [1]*(len(d)-a-1))
    checked = dict(data, charts=[dict(ch, loop=w) for ch, w in zip(data['charts'], paths, strict=True)])
    assert read_track(checked)['nonzero']
    return paths


def contact(data):
    first = data['charts'][0]
    stationary = [True]*(len(first['diagram'])-1+len(first['input']))
    for index, chart in enumerate(data['charts']):
        a = chart['slot']
        p = len(chart['input'])
        chart_marks = stationary[:a] + [False] + stationary[a+p:]
        named = tuple((offset, j) for j, (offset, _) in enumerate(chart['diagram']))
        ports = {j: data['gates'][g][1:] for j, (_, g) in enumerate(chart['diagram'])}
        components = Components(named, ports, len(data['path']))
        floating = set()
        for core, skeleton in components.skeleton.items():
            floating.update(skeleton)
            if any(not chart_marks[j] for j in skeleton) and any(
                    chart_marks[j] for j in components.subtree[core]):
                return dict(site=index+1, reason='mobile core carries a stationary gate')
        if any(not mark and j not in floating for j, mark in enumerate(chart_marks)):
            return dict(site=index+1, reason='mobile gate on an anchored core')
        stationary[a:a+p] = [False]*len(chart['output'])
        if index < len(data['seams']):
            for g in data['seams'][index]:
                j = abs(g)-1
                stationary[j], stationary[j+1] = stationary[j+1], stationary[j]
    return None


def solve(data):
    if not data['charts']:
        if data['seams']:
            raise ValueError('seam without a site')
        return dict(free_rank=0)
    read_track(dict(data, charts=[dict(ch, loop=()) for ch in data['charts']]))
    used, surviving, _, _ = trace(data)
    if used or surviving:
        return dict(free_rank=0)
    obstruction = contact(data)
    if obstruction is not None:
        return dict(free_rank=0, contact=obstruction)
    basis = first_basis(data)
    if not basis:
        return dict(free_rank=0)
    witness = lift(data, basis[0])
    return dict(free_rank=len(basis) if witness is not None else 0,
                first_face_holes=len(basis), meridian_track=witness)


def nested(seam):
    # The first site creates one two-wire lens with an interior scalar p, and
    # one exterior scalar. The middle site acts strictly inside the new lens.
    ports = {g: ['x','',''] for g in ('site','p','r','extra','hole')}
    ports.update(B=['x','','ff'], D=['x','ff',''])
    def row(*gates):
        return [(0,g) for g in gates]
    inside = row('B') + [(1,'p')] + row('D','extra')
    after = row('B') + [(1,'r')] + row('D','extra')
    return dict(vertex='x', path='', edges={'f':['x','x']}, gates=ports,
                charts=[dict(diagram=row('site','hole'),slot=0,input=[],output=inside),
                        dict(diagram=row('B')+[(1,'site')]+row('D','extra','hole'),
                             slot=1,input=[(0,'p')],output=[(0,'r')]),
                        dict(diagram=row('site','hole'),slot=0,input=after,output=[])],
                seams=[[],cable(seam,[3,1,1])])


def audit():
    from semistrict_surface_serial_packet_group import solve as scalar
    count = 0
    for length in range(5):
        for letters in product((1,-1,2,-2),repeat=length):
            row = list(range(3))
            for g in letters:
                i = abs(g)-1
                row[i], row[i+1] = row[i+1], row[i]
            if row != list(range(3)):
                continue
            expected = scalar(dict(initial=1, steps=[dict(slot=0,input=0,output=2,seam=letters),
                                                     dict(slot=0,input=2,output=0)]))
            assert solve(nested(letters))['free_rank'] == expected['free_rank']
            count += 1
    comm = (1,1,2,2,-1,-1,-2,-2)
    assert solve(nested(comm))['free_rank'] == 0
    # A site within a stationary two-wire lens sees its two interior sibling
    # points. The gate on the outside and both gates of the lens are spectators.
    row = [(0,'B'),(1,'site'),(1,'a'),(1,'b'),(0,'D'),(0,'outside')]
    data = nested(())
    data['gates'].update({g:['x','',''] for g in ('a','b','outside')})
    data.update(charts=[dict(diagram=row,slot=1,input=[],output=[(0,'p')]),
                        dict(diagram=row,slot=1,input=[(0,'p')],output=[])],seams=[[]])
    assert solve(data)['free_rank'] == 2
    w, v = first_basis(data)
    assert lift(data, reduced(w+v+inv(w)+inv(v))) is not None
    data['charts'] = [dict(diagram=[(0,'B'),(1,'site'),(0,'D'),(0,'outside')],
                           slot=1,input=[],output=[])]
    data['seams'] = []
    assert solve(data)['free_rank'] == 0
    # The middle chart cuts the floating core along two rim wires. Its
    # port has two through wires with one retained interior scalar.
    for seam, rank in [((), 1), ((2,2), 0)]:
        wired = nested(seam)
        wired['gates']['J'] = ['x','ff','ff']
        wired['charts'][1] = dict(diagram=[(0,'B'),(0,'J'),(0,'D'),(0,'extra'),(0,'hole')],
                                  slot=1,input=[(1,'p')],output=[(1,'r')])
        assert solve(wired)['free_rank'] == rank

    # Contract disconnected pieces on opposite sides of a through wire.
    # The active marker is connected to that wire only in the middle chart.
    for floating in (False, True):
        gates = {'P':['x','',''], 'Q':['x','',''], 'w':['x','f','f'],
                 'site':['x','',''], 'hole':['x','',''],
                 'B':['x','','f'], 'D':['x','f','']}
        before = [(0,'B')] if floating else []
        after = [(0,'D')] if floating else []
        charts = [dict(diagram=before+[(0,'site')]+after+[(0,'hole')],
                       slot=len(before),input=[],output=[(0,'P')]),
                  dict(diagram=before+[(0,'w')]+after+[(0,'hole')],
                       slot=len(before),input=[(0,'P')],output=[(0,'Q')]),
                  dict(diagram=before+[(0,'site')]+after+[(0,'hole')],
                       slot=len(before),input=[(0,'Q')],output=[])]
        data = dict(vertex='x', path='' if floating else 'f', edges={'f':['x','x']},
                    gates=gates, charts=charts, seams=[[],[]])
        answer = solve(data)
        assert answer['free_rank'] == 0 and answer['contact']['site'] == 2
    # Expanding J leaves two disconnected rods and a free scalar. With
    # the marker present the two rods meet, giving just one outer carrier.
    outer = nested(())
    outer['gates'].update(B=['x','','f'], C=['x','','f'], J=['x','ff','ff'],
                          D=['x','f',''], E=['x','f',''])
    prefix, suffix = [(0,'B'), (1,'C')], [(1,'E'), (0,'D')]
    outer['charts'] = [dict(diagram=[(0,'site'),(0,'hole')],slot=0,input=[],
                            output=prefix+[(1,'p')]+suffix),
                       dict(diagram=prefix+[(0,'J')]+suffix+[(0,'hole')],slot=2,
                            input=[(1,'p')],output=[(1,'r')]),
                       dict(diagram=[(0,'site'),(0,'hole')],slot=0,
                            input=prefix+[(1,'r')]+suffix,output=[])]
    outer['seams'] = [[],[]]
    assert solve(outer)['free_rank'] == 1

    # A stationary point enters the gap between the two loose ends of a
    # fork. The middle marker closes a face around it without consuming it.
    outer['gates']['B'] = ['x','','ff']
    for ch, side, point in [(outer['charts'][0],'output','p'), (outer['charts'][2],'input','r')]:
        ch[side] = [(0,'B'),(1,point)]+suffix
    outer['charts'][1].update(diagram=[(0,'B'),(1,'hole'),(0,'J')]+suffix,slot=2)
    enter = (-4,3,2)
    outer['seams'] = [enter, inv(enter)]
    answer = solve(outer)
    assert answer['free_rank'] == 0 and answer['contact']['site'] == 2
    print(f'{count} signed wired histories agree with the outer sibling calculation; '
          'the pure commutator seam kills the group. Nested faces yield ranks two and zero; anchoring, sharing a core and enclosing a stationary point each kill the group.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', type=Path, nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())), indent=2))
    else:
        audit()
