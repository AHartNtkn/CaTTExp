"""Resolve positive point-rule movies to through strands detecting probe differences.

Input is {"initial":2,"steps":[{"slot":0,"input":2,"output":1,"seam":[]},...]}.
Slots are zero-based. Signed adjacent seam crossings are one-based and follow the site.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import reduced
from semistrict_surface_planar_tiers import artin_step


def resolve(data):
    initial = data['initial']
    if type(initial) is not int or initial < 0:
        raise ValueError('initial must be a nonnegative number of points')
    live = list(range(initial))
    prefix = [(edge,) for edge in live]
    starts = list(prefix)
    successor = {}
    events = []
    for step in data['steps']:
        slot,p,q = (step[key] for key in ('slot','input','output'))
        if any(type(x) is not int for x in (slot,p,q)) or min(p,q)<1 or not 0<=slot<=len(live)-p:
            raise ValueError('site requires nonempty ports at a live slot')
        incoming = live[slot:slot+p]
        outgoing = list(range(len(prefix),len(prefix)+q))
        prefix.extend(prefix[incoming[0]]+(e,) for e in outgoing)
        starts.extend(prefix[e] for e in outgoing[1:])
        successor.update((e,outgoing[0]) for e in incoming)
        live[slot:slot+p] = outgoing
        seam = step.get('seam',[])
        events.append((slot,incoming,outgoing,live.copy(),seam))
        for crossing in seam:
            if type(crossing) is not int or not 1<=abs(crossing)<len(live):
                raise ValueError('seam crosses outside the row')
            i = abs(crossing)-1
            live[i],live[i+1] = live[i+1],live[i]

    paths = []
    for start in starts:
        path = list(start)
        while path[-1] in successor:
            path.append(successor[path[-1]])
        paths.append(path)
    packets = [[] for _ in prefix]
    for i,path in enumerate(paths):
        for edge in path:
            packets[edge].append(i)
    # The columns for initial segments and extra outputs give a unit lower triangle.
    handles = [path[-1] for path in starts]
    for i,path in enumerate(paths):
        assert handles[i] in path and not set(handles[i+1:]).intersection(path)
    assert all(packets)

    threads = [thread for edge in range(initial) for thread in packets[edge]]
    meridians = [(t+1,) for t in threads]
    braid = []

    def cross(g):
        i = abs(g)-1
        a,b = meridians[i:i+2]
        if g>0:
            meridians[:] = artin_step(tuple(meridians),i)
        else:
            meridians[i:i+2] = [b,reduced(tuple(-x for x in reversed(b))+a+b)]
        braid.append(g)
        threads[i],threads[i+1] = threads[i+1],threads[i]

    readings = []
    for slot,incoming,outgoing,row,seam in events:
        left = sum(len(packets[e]) for e in row[:slot])
        order = [t for e in outgoing for t in packets[e]]
        assert threads[left:left+len(order)]==[t for e in incoming for t in packets[e]]
        def peripheral():
            return reduced(tuple(g for w in meridians[left:left+len(order)] for g in w))
        before = peripheral()
        for j,t in enumerate(order,left):
            pos = threads.index(t,j)
            while pos>j:
                cross(pos)
                pos -= 1
        assert peripheral()==before
        readings.append(before)
        def packet_words(edges):
            words = []
            i = 0
            for edge in edges:
                end = i+len(packets[edge])
                words.append(reduced(tuple(g for w in meridians[i:end] for g in w)))
                i = end
            return words
        expected = packet_words(row)
        after = row.copy()
        for g in seam:
            i = abs(g)-1
            after[i],after[i+1] = after[i+1],after[i]
            a,b = expected[i:i+2]
            if g>0:
                expected = list(artin_step(tuple(expected),i))
            else:
                expected[i:i+2] = [b,reduced(tuple(-x for x in reversed(b))+a+b)]
        for g in cable(seam,[len(packets[e]) for e in row]):
            cross(g)
        assert packet_words(after)==expected
    assert threads==[t for e in live for t in packets[e]]
    for t,w in zip(threads,meridians):
        assert [w.count(i+1)-w.count(-i-1) for i in range(len(paths))]==[
            int(i==t) for i in range(len(paths))]
    return dict(rank=len(paths),paths=paths,handle_edges=handles,packets=packets,
                braid=braid,site_peripherals=readings,terminal_order=threads)


def rice(checkout):
    from semistrict_surface_exact_boundary import accepted,run
    ctx = '(x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x)) (c : id(x) -> id(x))'
    at = '(x,a,b,c)'
    # Merge initial packets (a,c) and b, then split the sorted packet into (a,b) and c.
    program = f"""import examples/eh
def turn = coh [[u,v,w] : comp[comp[u,v],w] -> comp[u,comp[v,w]]]
def back = coh [[u,v,w] : comp[u,comp[v,w]] -> comp[comp[u,v],w]]
def mergepkt {ctx} : comp[comp[a,c],b] -> comp[a,comp[b,c]] =
  comp[turn(a,c,b),comp[a,[eh(x,c,b)]]]
def splitpkt {ctx} : comp[a,comp[b,c]] -> comp[comp[a,b],c] = back(a,b,c)
def routed {ctx} : comp[comp[a,c],b] -> comp[comp[a,b],c] = comp[mergepkt{at},splitpkt{at}]
"""
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root/'examples').symlink_to(checkout/'examples',target_is_directory=True)
        (root/'Threads.catt').write_text(program)
        for flags in ([],['--sua']):
            accepted(run(checkout/'target/release/catt_strict',root,'Threads.catt',flags),
                     'Threads.catt',['mergepkt','splitpkt','routed'])


def audit():
    from relative_coherence_frame_module import echelon
    checked = 0
    for initial in (1,2,3):
        for sizes in product((1,2),repeat=4):
            p,q,p2,q2 = sizes
            if p>initial or p2>initial-p+q:
                continue
            for a in range(initial-p+1):
                width = initial-p+q
                for b in range(width-p2+1):
                    for seam in ([[]] if width==1 else [[],[1],[-1],[1,-1],[-1,-1]]):
                        data = dict(initial=initial,steps=[
                            dict(slot=a,input=p,output=q,seam=seam),dict(slot=b,input=p2,output=q2)])
                        r = resolve(data)
                        # Independently compute the abelian group map on *all* edges.
                        columns = [{i:1 for i in pkt} for pkt in r['packets']]
                        pivots,kernel = echelon(columns)
                        assert len(kernel)==2 and len(pivots)==initial+q+q2-2
                        assert all(v[k]==1 for k,(v,_) in pivots.items())
                        checked += 1
    print(f'{checked} positive signed movies passed the peripheral, path-rank and integral lattice checks.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',nargs='?',type=Path)
    cli.add_argument('--rice',type=Path,help='built catt-strict checkout')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(resolve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
    if args.rice:
        rice(args.rice.resolve())
        print('Rice accepted the packet merge, split and composite at the written types in raw and insertion modes.')
