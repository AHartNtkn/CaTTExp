"""Replace a scalar cap movie by a detecting tangle of binary cups and caps.

Accept {"initial":n,"movie":[...]} in the output format of the cap thread solver
(or its initial_threads field); arbitrary signed point-rule input with steps is
resolved first. Each chord of a spanning forest receives a certified full twist count.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_cap_threads import resolve_caps
from semistrict_surface_component_braids import Partition
from semistrict_surface_gate_forests import cable


def trace(initial,movie):
    if type(initial) is not int or initial<0:
        raise ValueError('expected nonnegative initial width')
    ports,edges,rows,crossings = [],[],[],[]
    def create(n):
        start = len(edges)
        block = list(range(start,start+n))
        edges.extend([len(ports),None] for _ in block)
        ports.append(block)
        return block
    row = []
    for _ in range(initial):
        row.extend(create(1))
    for event in movie:
        rows.append(row.copy())
        if 'braid' in event:
            for g in event['braid']:
                if type(g) is not int or not 1<=abs(g)<len(row):
                    raise ValueError('crossing outside the row')
                i = abs(g)-1
                crossings.append((row[i],row[i+1]))
                row[i],row[i+1] = row[i+1],row[i]
        else:
            birth = 'birth' in event
            n = event['birth' if birth else 'death']
            a = event['slot']
            if type(n) is not int or n<=0 or type(a) is not int or not 0<=a<=len(row)-(0 if birth else n):
                raise ValueError('invalid cap size or position')
            if birth:
                row[a:a] = create(n)
            else:
                for e in row[a:a+n]:
                    edges[e][1] = len(ports)
                ports.append(list(reversed(row[a:a+n])))
                del row[a:a+n]
    for e in row:
        edges[e][1] = len(ports)
        ports.append([e])
    return ports,edges,rows+[row],crossings


def ribbon(data):
    if 'steps' in data:
        data = resolve_caps(data)
    initial = data['initial_threads'] if 'initial_threads' in data else data['initial']
    movie = data['movie']
    ports,edges,rows,crossings = trace(initial,movie)
    forest = Partition()
    chords = []
    for e,(s,t) in enumerate(edges):
        if forest.at(s)==forest.at(t):
            chords.append(e)
        else:
            forest.unite(s,t)
    component = [forest.at(s) for s,_ in edges]
    genus_rank = Counter(component[e] for e in chords)
    # Crossings between different components do not enter either self-linking form.
    crossing_count = Counter(component[a] for a,b in crossings if component[a]==component[b])
    twists = {e:1+genus_rank[component[e]]*crossing_count[component[e]] for e in chords}
    result = []
    for i,event in enumerate(movie):
        if 'braid' in event:
            result.append(dict(braid=cable(event['braid'],[2]*len(rows[i]))))
            continue
        a = event['slot']
        birth = 'birth' in event
        n = event['birth' if birth else 'death']
        # Outer sides of the first and last bands form one arc; each
        # intervening gap contributes a small adjacent cup (or reversed cap).
        sites = [2*a]+[2*a+2*j-1 for j in range(1,n)]
        if birth:
            result.extend(dict(birth=2,slot=j) for j in sites)
            for j,e in enumerate(rows[i+1][a:a+n],a):
                if e in twists:
                    result.append(dict(braid=[2*j+1]*(2*twists[e])))
        else:
            result.extend(dict(death=2,slot=j) for j in reversed(sites))
    return dict(initial_threads=2*initial,movie=result,chord_twists=twists,
                graph_components=len(set(component)),cycle_rank=len(chords))


def boundary_components(ports,edges):
    # Walk each ribbon side by crossing an edge and taking the cyclic successor.
    following = {}
    for v,block in enumerate(ports):
        for i,e in enumerate(block):
            s,t = edges[e]
            following[(t if s==v else s,e)] = (v,block[(i+1)%len(block)])
    pending = set(following)
    count = 0
    while pending:
        start = next(iter(pending))
        h = start
        while h in pending:
            pending.remove(h)
            h = following[h]
        assert h==start
        count += 1
    return count


def paired_components(data):
    # Join the two sides of each initial and final band along the time boundary.
    initial = data['initial_threads']
    row = list(range(initial))
    ends = Partition()
    for j in range(0,initial,2):
        ends.unite(j,j+1)
    next_id = initial
    for event in data['movie']:
        if 'braid' in event:
            for g in event['braid']:
                i = abs(g)-1
                row[i],row[i+1] = row[i+1],row[i]
        elif 'birth' in event:
            assert event['birth']==2
            j = event['slot']
            row[j:j] = [next_id,next_id+1]
            ends.unite(next_id,next_id+1)
            next_id += 2
        else:
            assert event['death']==2
            j = event['slot']
            ends.unite(row[j],row[j+1])
            del row[j:j+2]
    for j in range(0,len(row),2):
        ends.unite(row[j],row[j+1])
    return len({ends.at(i) for i in range(next_id)})


def closed_linking(movie):
    # For closed diagrams, orient the traced components and read their actual linking numbers.
    ports,edges,_,_ = trace(0,movie)
    if any(len(v)!=2 for v in ports):
        raise ValueError('expected a closed binary cap diagram')
    signs,labels = {},{}
    for e in range(len(edges)):
        if e in signs:
            continue
        g,d = e,1
        while g not in signs:
            signs[g],labels[g] = d,e
            vertex = edges[g][1 if d==1 else 0]
            a,b = ports[vertex]
            g,d = (a if b==g else b),-d
    _,_,rows,_ = trace(0,movie)
    linking = Counter()
    for row,event in zip(rows,movie):
        row = row.copy()
        for gen in event.get('braid',[]):
            i = abs(gen)-1
            a,b = row[i:i+2]
            if labels[a]!=labels[b]:
                pair = tuple(sorted((labels[a],labels[b])))
                linking[pair] += signs[a]*signs[b]*(1 if gen>0 else -1)
            row[i],row[i+1] = b,a
    assert all(n%2==0 for n in linking.values())
    return {k:n//2 for k,n in linking.items()}


def double_tangle(data):
    """Place a spatial reflection to the left and join corresponding ends by nested caps."""
    width = data['initial_threads']
    out = [dict(birth=2,slot=j) for j in range(width)]
    for event in data['movie']:
        if 'braid' in event:
            real = [(width+abs(g))*(1 if g>0 else -1) for g in event['braid']]
            reflected = [(width-abs(g))*(-1 if g>0 else 1) for g in event['braid']]
            out.append(dict(braid=real+reflected))
        else:
            key = 'birth' if 'birth' in event else 'death'
            slot = event['slot']
            if event[key]!=2:
                raise ValueError('the closure expects binary caps')
            mirror_slot = width-slot-(2 if key=='death' else 0)
            out.extend([{key:2,'slot':width+slot},{key:2,'slot':mirror_slot}])
            width += 2 if key=='birth' else -2
    out.extend(dict(death=2,slot=j) for j in reversed(range(width)))
    return dict(initial_threads=0,movie=out)


def check_fold(data):
    # Name an arbitrary meridian letter at each bottom point and each cup.
    # The mirrored row must always be the reverse list of inverse real words.
    from semistrict_surface_cap_threads import artin
    from semistrict_surface_history_group import inv
    w = data['initial_threads']
    row = [(j+1,) for j in range(w)]
    full = []
    double = iter(double_tangle(data)['movie'])
    for j in reversed(range(w)):
        op = next(double)
        slot = op['slot']
        assert op['birth']==2
        full[slot:slot] = [inv(row[j]),row[j]]
    label = w
    for e in data['movie']:
        if 'braid' in e:
            for g in e['braid']:
                artin(row,g)
            for g in next(double)['braid']:
                artin(full,g)
        else:
            birth = 'birth' in e
            a = e['slot']
            real,mirror = next(double)['slot'],next(double)['slot']
            if birth:
                label += 1
                pair = [(label,),(-label,)]
                row[a:a] = pair
                full[real:real] = pair
                full[mirror:mirror] = pair
            else:
                # A death imposes the peripheral relator. The reflected
                # peripheral is its inverse already in the ambient free group.
                peripheral = tuple(row[a:a+2])
                assert tuple(full[real:real+2])==peripheral
                del full[real:real+2]
                assert tuple(full[mirror:mirror+2])==tuple(inv(v) for v in reversed(peripheral))
                del full[mirror:mirror+2]
                del row[a:a+2]
        assert full==[inv(v) for v in reversed(row)]+row
    for op in double:
        j = op['slot']
        assert op['death']==2 and full[j]==inv(full[j+1])
        del full[j:j+2]
    assert not full


def audit():
    checked = 0
    for a,b in product(range(1,5),repeat=2):
        for word in ([],[1],[-1],[1,-1],[1,1,1]):
            for last in (1,2,a+b):
                movie = [dict(birth=a,slot=0),dict(birth=b,slot=a),dict(braid=word),
                         dict(death=last,slot=a+b-last)]
                data = ribbon(dict(initial=0,movie=movie))
                ports,edges,_,_ = trace(0,movie)
                assert paired_components(data)==boundary_components(ports,edges)
                checked += 1
                if len(word)<=1:
                    check_fold(data)
    for word in ([],[1],[-1],[1,1],[-1,-1],[1,1,1]):
        movie = [dict(birth=2,slot=0),dict(braid=word),dict(death=2,slot=0)]
        r = ribbon(dict(initial=0,movie=movie))
        assert paired_components(r)==2 and len(r['chord_twists'])==1
        # A two-strand cap at both ends gives one annulus core. Its two
        # boundary sides have linking equal up to orientation to its framing.
        linking, = closed_linking(r['movie']).values()
        t, = r['chord_twists'].values()
        assert abs(linking) in (abs(t-len(word)),t+len(word)) and linking!=0
    planar = [dict(birth=3,slot=0),dict(death=3,slot=0)]
    theta = ribbon(dict(initial=0,movie=planar))
    assert paired_components(theta)==3 and theta['cycle_rank']==2
    assert sorted(abs(n) for n in closed_linking(theta['movie']).values() if n)==[1,1]
    print(f'{checked} cap diagrams agree with their independent ribbon boundary walks; '
          '144 doubled tangles passed the signed meridian fold, and six annulus framings '
          'and the planar theta linking numbers passed.')


def rice(checkout):
    from semistrict_surface_exact_boundary import accepted,run
    bare = '(x : *) (a : id(x) -> id(x))'
    ctx = bare+' (b : id(id(x)) -> comp[a,a]) (d : comp[a,a] -> id(id(x)))'
    grow = 'grow(x,a,b,d)'
    shrink = 'shrink(x,a,b,d)'
    inner = 'comp[a,comp[comp[b,c],comp[comp[d,e],f]]]'
    paired = 'comp[comp[a,b],comp[c,d],comp[e,f]]'
    code = f"""import examples/eh
def grow {ctx} : a -> comp[comp[a,a],a] = comp[unitor_l_inv(a),comp[[b],a]]
def shrink {ctx} : comp[comp[a,a],a] -> a = comp[comp[[d],a],unitor_l(a)]
def pairs = coh [[a,b,c,d,e,f] : {inner} -> {paired}]
def unpack = coh [[a,b,c,d,e,f] : {paired} -> {inner}]
def openRibbon {ctx} : id(id(x)) -> comp[comp[a,a],comp[a,a],comp[a,a]] =
  comp[b,comp[a,[{grow}]],comp[a,[comp[comp[a,a],[{grow}]]]],pairs(a,a,a,a,a,a)]
def half {bare} : comp[comp[a,a],comp[a,a],comp[a,a]] -> comp[comp[a,a],comp[a,a],comp[a,a]] =
  comp[comp[a,a],[eh(x,a,a)],[eh(x,a,a)]]
def closeRibbon {ctx} : comp[comp[a,a],comp[a,a],comp[a,a]] -> id(id(x)) =
  comp[unpack(a,a,a,a,a,a),comp[a,[comp[comp[a,a],[{shrink}]]]],comp[a,[{shrink}]],d]
def smallProbe {ctx} : id(id(x)) -> id(id(x)) = comp[b,d]
def thetaRibbon {ctx} : id(id(x)) -> id(id(x)) =
  comp[smallProbe(x,a,b,d),openRibbon(x,a,b,d),half(x,a),half(x,a),closeRibbon(x,a,b,d)]
"""
    with TemporaryDirectory() as temp:
        folder = Path(temp)
        (folder/'examples').symlink_to(checkout/'examples',target_is_directory=True)
        (folder/'Ribbon.catt').write_text(code)
        for flags in ([],['--sua']):
            accepted(run(checkout/'target/release/catt_strict',folder,'Ribbon.catt',flags),
                     'Ribbon.catt',['grow','shrink','openRibbon','half','closeRibbon','smallProbe','thetaRibbon'])
    print('Rice checked the framed theta boundary and the two-use probe in raw and insertion modes.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',nargs='?',type=Path)
    cli.add_argument('--rice',type=Path,help='built catt-strict checkout')
    cli.add_argument('--close',action='store_true',help='also attach the reflected tangle at the ends')
    args = cli.parse_args()
    if args.input:
        result = ribbon(json.loads(args.input.read_text()))
        if args.close:
            result['closure'] = double_tangle(result)
        print(json.dumps(result,indent=2))
    else:
        audit()
    if args.rice:
        rice(args.rice.resolve())
