"""Recognize point and two-terminal planar ports and compare lifted rule corners.

JSON with edges, gates and rules (site to {input,output} positioned rows)
checks both written ports, allowing repeated gate colours. Alternatively use
closed_port_links JSON with diagram, blocks and paths for a lifted corner.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_batch_traces import coarse, validate
from semistrict_surface_birth_death_packets import expand, follow
from semistrict_surface_closed_port_links import Corner, solve as solve_corner
from semistrict_surface_component_braids import Components, cabling, restrict
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import exchange, inv, reduced
from semistrict_surface_probe_movies import Faces
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_probe_retraction import probe_word


def reaches(edges,start):
    found,pending = {start},[start]
    while pending:
        for j in edges[pending.pop()]:
            if j not in found:
                found.add(j)
                pending.append(j)
    return found


def classify(model,site,block):
    vertex,source,target = model.gates[site]
    if model.sweep(vertex,source,block)!=target:
        raise ValueError('port has the wrong boundary')
    if not block:
        return None
    if not source and not target:
        return dict(kind='point')
    rows = tuple((p,j) for j,(p,_) in enumerate(block))
    ports = {j:model.ports[g] for j,(_,g) in enumerate(block)}
    width = len(source)
    wires = [None]*width
    forward,back = defaultdict(set),defaultdict(set)
    inputs = set()
    for p,j in rows:
        k,l = map(len,ports[j])
        for i in wires[p:p+k]:
            if i is None:
                inputs.add(j)
            else:
                forward[i].add(j)
                back[j].add(i)
        wires[p:p+k] = [j]*l
    outputs = set(wires)
    if None in outputs or len(inputs)>1 or len(outputs)>1:
        return None
    parts = Components(rows,ports,width)
    floating = set().union(*parts.skeleton.values())
    core = set(ports)-floating
    if not core:
        return None
    first,last = min(core),max(core)
    if (inputs and inputs!={first}) or (outputs and outputs!={last}):
        return None
    if reaches(forward,first)!=core or reaches(back,last)!=core:
        return None
    faces = Faces(rows,ports,width)
    exterior = {f for (r,p),f in faces.spots.items()
                if r in (0,len(rows)) or p in (0,faces.slices[r])}
    if any(faces.holes[f] for f in exterior):
        return None
    return dict(kind='two-terminal',first=first,last=last,core=sorted(core),
                enclosed=sorted(floating))


def recognize(data):
    # Port typing is based at the declared site, independently of any context
    # where a particular use is whiskered.
    if not data['rules']:
        return {}
    first = next(iter(data['rules']))
    model = Presentation(dict(data,diagram=[],rules={},path='',vertex=data['gates'][first][0]))
    return {k:{side:classify(model,k,ports[side]) for side in ('input','output')}
            for k,ports in data['rules'].items()}


def wired_representative(model,k,b):
    report = classify(model,k,b)
    return report['first'] if report else None


def gather(rows,groups,ports):
    """Gather disjoint wired blocks at their first rows by legal exchanges."""
    path = []
    for group in groups:
        at = next(i for i,(_,g) in enumerate(rows) if g in group)
        limit = at+1
        for j in range(at+1,len(rows)):
            if rows[j][1] not in group:
                continue
            for pos in range(j,limit,-1):
                for letter in (pos,-pos):
                    moved = exchange(rows,letter,ports)
                    if moved is not None:
                        break
                if moved is None:
                    raise ValueError('blocked when gathering a port')
                path.append(letter)
                rows = moved
            limit += 1
    return rows,tuple(path)


def fixture():
    gates = {k:['x','a','a'] for k in ('A','D','l','r','y','z')}
    gates.update({k:['x','a','aa'] for k in ('a+','d+')})
    gates.update({k:['x','aa','a'] for k in ('a-','d-')})
    gates.update({k:['x','',''] for k in ('p','q','P','s','t')})
    blocks = dict(A=[(0,'a+'),(0,'l'),(1,'p'),(1,'q'),(1,'r'),(0,'a-')],
                  D=[(0,'d+'),(0,'y'),(1,'z'),(0,'d-')],P=[(0,'s'),(0,'t')])
    joint = [(0,'A'),(0,'P'),(1,'D')]
    return dict(edges={'a':['x','x']},gates=gates,vertex='x',path='aa',
                diagram=joint,blocks=blocks)


def audit():
    data = fixture()
    c = Corner(data,wired_representative)
    ports = c.model.ports
    blocks = c.blocks
    assert classify(c.model,'A',blocks['A'])==dict(kind='two-terminal',first=0,last=5,
                                                   core=[0,1,4,5],enclosed=[2,3])
    assert classify(c.model,'D',blocks['D'])['core']==list(range(4))
    assert classify(c.model,'P',blocks['P'])==dict(kind='point')
    # Preserve the graph and typed outer words while breaking the terminal
    # test in three different ways. Repeated colours count by occurrence.
    checks = [(blocks['D']+[(1,'p')],False), ([(0,'p'),(0,'l')],False),
              ([(0,'a+'),(0,'a-'),(0,'l'),(0,'l')],True)]
    for b,expected in checks:
        assert (classify(c.model,'A',b) is not None)==expected
    extra = dict(data,gates=data['gates']|{'W':['x','aa','aa'],'B':['x','','aa'],
                                           'K':['x','aa','']})
    m = Presentation(dict(extra,diagram=[],rules={}))
    for block in ([(0,'l'),(1,'r')],[(0,'l')]):
        assert classify(m,'W',block) is None
    assert classify(m,'B',[(0,'B'),(1,'r')]) is None  # two distinct output gates
    assert classify(m,'B',[(0,'B'),(0,'a-'),(0,'a+')])['first']==0
    assert classify(m,'K',[(0,'a-'),(0,'a+'),(0,'K')])['last']==2

    # Enumerate reachable readings of the corner with both connected cores,
    # retaining independent orders of the two parallel branches and all
    # shuffles on the two exterior wires. Use no floating decorations in
    # this enumeration; their independent motions are tested below.
    xy = {k:[(p,g) for p,g in blocks[k] if g not in ('p','q')] for k in ('A','D')}
    root = expand(((0,'A'),(1,'D')),xy)
    pending,seen = deque([root]),{root}
    groups = [set(g for _,g in b) for b in xy.values()]
    trials = 0
    while pending:
        rows = pending.popleft()
        for order in (groups,groups[::-1]):
            result,word = gather(rows,order,ports)
            assert follow(rows,word,ports)==result
            at = 0
            restored = []
            while at<len(result):
                k, = [k for k,b in xy.items() if result[at][1] in {g for _,g in b}]
                pos = result[at][0]
                block = result[at:at+len(xy[k])]
                assert {g for _,g in block}=={g for _,g in xy[k]}
                assert classify(c.model,k,[(q-pos,g) for q,g in block]) is not None
                restored.append((pos,k))
                at += len(block)
            assert tuple(restored) in (((0,'A'),(1,'D')),((1,'D'),(0,'A')))
            trials += 1
        for j in range(1,len(rows)):
            for sign in (1,-1):
                nxt = exchange(rows,sign*j,ports)
                if nxt is not None and nxt not in seen:
                    pending.append(nxt)
                    seen.add(nxt)
    # Loops inside the central digon and at the separate point port are
    # independent. Compare restrictions on actual positioned return words.
    parts = Components(c.rows,ports,2)
    packets = parts.packets(c.rows,ports)
    def turn(a,b):
        group, = [f for f in packets if [k for k,_,_ in f]==[a,b]]
        return cabling(group,(1,1))
    inside,beside = turn('p','q'),turn('s','t')
    for a,b in [(inside,beside),(inv(inside),beside),(inside,inv(beside))]:
        w = a+b
        assert follow(c.rows,w,ports)==c.rows
        assert c.image(c.project('A',w))==c.image(b)
        assert c.image(c.project('P',w))==c.image(a)
        assert c.image(c.project('D',w))==c.image(w)
    print(f'{len(seen)} positioned readings; {trials} simultaneous gatherings replayed')
    print('bounded-face decorations, exterior punctures, through wires and one-sided terminals checked')


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    f = v(1)
    ff = comp2(ctx,0,f,f)
    def hom(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (hom(f,ff),hom(ff,f),hom(f,f),hom(f,f))
    # Two genuine interior branches, followed by a join; the other port
    # also contains two gates, so neither side is a bare gate.
    branch = comp2(ctx,0,v(4),v(5))
    fork = comp2(ctx,1,comp2(ctx,1,v(2),branch),v(3))
    line = comp2(ctx,1,v(4),v(5))
    ctx += (hom(fork,line),hom(line,fork))
    check_ctx(ctx)
    both = comp2(ctx,0,v(6),v(7))
    if directory:
        out = Emitter()
        out.check_type('oppositeChangesOnAdjacentWires',ctx,both,infer(ctx,both))
        (directory/'TwoTerminalPorts.agda').write_text(out.module('TwoTerminalPorts',__doc__.splitlines()[0]))


def audit_probe_face():
    # Open a bounded face on a spatial wire. Replace its lower boundary B
    # by F,G. The last change consumes G and the face, leaving F outside.
    signatures = {'a:a':('open','g'), 'a:aa':('B','replace'), 'a:aaa':('F',),
                  'aaa:aa':('G',), 'aa:a':('J',), 'aaa:a':('close','K'), ':':('p','q')}
    gates = {k:['x',*sig.split(':')] for sig,ks in signatures.items() for k in ks}
    pocket = [(1,'p'),(1,'q'),(0,'J')]
    def batch(rows,k,source,target):
        return dict(diagram=rows,sites={k:dict(input=source,output=target)})
    batches = [batch([(0,'open')],'open',[(0,'g')],[(0,'B')]+pocket),
               batch([(0,'replace')]+pocket,'replace',[(0,'B')],[(0,'F'),(0,'G')]),
               batch([(0,'F'),(0,'close')],'close',[(0,'G')]+pocket,[(0,'K')])]
    data = dict(edges={'a':['x','x']},gates=gates,path='a',vertex='x',batches=batches,seams=[[],[]])
    validate(data)
    model = Presentation(dict(data,diagram=[],rules={}))
    for b in batches:
        for k,io in b['sites'].items():
            assert all(classify(model,k,port) for port in io.values())
    _,gaps,nodes = coarse(data)
    region = nodes.at((1,gaps[1].spots[1,1]))
    visits = [(i,f) for i,gap in enumerate(gaps) for f in set(gap.spots.values())
              if nodes.at((i,f))==region]
    assert [i for i,_ in visits]==[1,2]
    for (i,f),shell in zip(visits,['B','G']):
        gap = gaps[i]
        boundary = set()
        for j,(p,k) in enumerate(gap.rows):
            s,t = model.ports[k]
            incident = [(j+side,q) for side,width in enumerate((len(s),len(t)))
                        for q in range(p,p+width+1)]
            if any(gap.spots[a]==f for a in incident):
                boundary.add(k)
        assert boundary=={shell,'p','q','J'} and gap.holes[f]==2
    # Pull the end tie's cap loop across its entire wired port. Project to
    # the two children and a candidate outer puncture. In the compactified
    # plane the meridian of the shell is inverse to the two-child peripheral.
    rows = gaps[2].rows
    cap = (2,3,4,5)  # middle reading F,G,p,q,J with the probe first
    loop = push(tuple(reversed(cap)))
    names = [k for _,k in rows]
    for shell in ('G','F'):
        ids = {0}|{names.index(k)+1 for k in (shell,'p','q')}
        image = probe_word(len(ids),restrict(len(rows)+1,loop,ids))
        basis = [(-1,-2),(1,),(2,)]
        evaluated = reduced(tuple(a for g in image for a in
                                  (basis[g-1] if g>0 else inv(basis[-g-1]))))
        assert (not evaluated)==(shell=='G')
    print('temporary two-hole face reaches exactly two cuts; only its continuing boundary gate kills the tested cap')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = recognize(data) if 'rules' in data else solve_corner(data,wired_representative)
        print(json.dumps(result,indent=2))
    else:
        audit()
        audit_probe_face()
        typed(args.agda_dir)
