"""Extract a closed wired program and check the comparison at every written port."""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_closed_port_group import nested, solve
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, realize, reduced
from semistrict_surface_movie_spine import expanded
from semistrict_surface_serial_gate_tracks import motion, read_track
from semistrict_surface_shared_edge import braid_image


def inner_chart(data, chart, mobile):
    """Forget exterior wires, retaining the offset in each mobile wire row."""
    wires = [False]*len(data['path'])
    diagram = []
    for (offset, gate), keep in zip(chart['diagram'], mobile, strict=True):
        _, before, after = data['gates'][gate]
        assert all(bit == keep for bit in wires[offset:offset+len(before)])
        if keep:
            diagram.append((sum(wires[:offset]), gate))
        wires[offset:offset+len(before)] = [keep]*len(after)
    assert not any(wires)
    return dict(chart, diagram=diagram, slot=sum(mobile[:chart['slot']]), loop=())


def extract(data):
    first = data['charts'][0]
    slot = first['slot']
    position, gate = first['diagram'][slot]
    prefix = list(map(tuple, first['diagram'][:slot]))
    suffix = list(map(tuple, first['diagram'][slot+1:]))
    mobile = [False]*(len(prefix)+len(suffix))
    inner, packed, inside, placed, outside = [], [], [], [], []
    for i, chart in enumerate(data['charts']):
        a, p, q = chart['slot'], len(chart['input']), len(chart['output'])
        assert not any(not bit for bit in mobile[a:a+p])
        sub = inner_chart(data, chart, mobile[:a]+[True]+mobile[a+p:])
        inner.append(sub)
        drawing = prefix+[(position+j,g) for j,g in sub['diagram']]+suffix
        packed.append(dict(sub, diagram=drawing, slot=slot+sub['slot']))
        mobile[a:a+p] = [True]*q
        if i < len(data['seams']):
            seam = data['seams'][i]
            selected = {j for j, bit in enumerate(mobile) if bit}
            w = restrict(len(mobile), seam, selected)
            inside.append(w)
            placed.append(tuple(g+slot if g>0 else g-slot for g in w))
            outside.extend(restrict(len(mobile), seam, set(range(len(mobile)))-selected))
            for g in seam:
                j = abs(g)-1
                mobile[j], mobile[j+1] = mobile[j+1], mobile[j]
    base = {k:data[k] for k in ('edges','gates','vertex','path')}
    return (dict(base, vertex=data['gates'][gate][0], path='', charts=inner, seams=inside),
            dict(base, charts=packed, seams=placed), reduced(outside))


def expansion(path, chart, side):
    widths = [1]*len(chart['diagram'])
    widths[chart['slot']] = len(chart[side])
    return cable(path, widths)


def localize(data):
    group = solve(data)
    if not group['free_rank']:
        return dict(free_rank=0)
    program, packed, exterior = extract(data)
    read_track(program)
    read_track(packed)
    ports = {g: (s,t) for g, (_,s,t) in data['gates'].items()}
    incoming, paths = (), []
    for i, (chart, target) in enumerate(zip(data['charts'], packed['charts'], strict=True)):
        a, p = chart['slot'], len(chart['input'])
        n = len(chart['diagram'])-1+p
        path = restrict(n, incoming, set(range(n))-set(range(a+1,a+p))) if i else ()
        legal = realize(tuple(map(tuple,chart['diagram'])), tuple(map(tuple,target['diagram'])), path, ports)
        assert legal is not None
        assert braid_image(n, expansion(legal,chart,'input')) == braid_image(n, incoming)
        paths.append(legal)
        after = expansion(legal,chart,'output')
        if i < len(data['seams']):
            incoming = reduced(inv(data['seams'][i])+after+packed['seams'][i])
    # The target runs its exterior history after the last site.
    end = expanded(chart, 'output')
    assert motion(expanded(target,'output'), ports, exterior) == end
    assert braid_image(len(end), after+exterior) == braid_image(len(end), ())
    return dict(free_rank=group['free_rank'], program=program, packed=packed,
                exterior_seam=exterior, site_paths=paths)


def audit():
    positive = negative = 0
    for n in range(5):
        for seam in product((1,-1,2,-2), repeat=n):
            order = list(range(3))
            for g in seam:
                i = abs(g)-1
                order[i], order[i+1] = order[i+1], order[i]
            if order != list(range(3)):
                continue
            result = localize(nested(seam))
            if result['free_rank']:
                positive += 1
            else:
                negative += 1
    # The stationary lens and its two-wire boundary enclose the entire
    # computation. At both seams a spectator moves around the mobile packet.
    data = nested(())
    data['gates'].update(K=['x','','ff'], L=['x','ff',''], J=['x','ff','ff'])
    data['charts'][1] = dict(diagram=[(0,'B'),(0,'J'),(0,'D'),(0,'extra'),(0,'hole')],
                            slot=1,input=[(1,'p')],output=[(1,'r')])
    for ch in data['charts']:
        ch['diagram'] = [(0,'K')]+[(1+p,g) for p,g in ch['diagram']]+[(0,'L')]
        ch['slot'] += 1
    across = tuple(g+1 for g in cable((1,1),[4,1]))
    data['seams'] = [across,inv(across)]
    result = localize(data)
    assert result['free_rank'] == 1 and result['site_paths'][1]
    assert result['program']['charts'][1]['diagram'] == [(0,'B'),(0,'J'),(0,'D'),(0,'extra')]
    # Crossing stationary siblings remains at the written end.
    exterior = nested(())
    exterior['gates']['s'] = ['x','','']
    for i,ch in enumerate(exterior['charts']):
        ch['diagram'].append((0,'s'))
        if i == 2:
            ch['diagram'][-2:] = [(0,'s'),(0,'hole')]
    exterior['seams'][1] = (5,)
    assert localize(exterior)['exterior_seam'] == (1,)
    print(f'{positive} signed wired localizations checked, {negative} zero-group cases. '
          'Nested wire offsets, a nonconstant through-wire comparison and an exterior crossing passed.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', type=Path, nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(localize(json.loads(args.input.read_text())), indent=2))
    else:
        audit()
