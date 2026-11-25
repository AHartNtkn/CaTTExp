"""Check connected wired ports by rotation and angle sums at their actual rim sectors.

JSON: edges, gates and rules mapping sites to {input,output} positioned rows.
Alternatively use the closed-port corner JSON with blocks and paths. External
floating components are allowed; a wired port needs one core touching all legs.
"""
from argparse import ArgumentParser
from collections import deque
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_birth_death_packets import expand, follow
from semistrict_surface_closed_port_links import Corner, solve as solve_corner
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import exchange, inv
from semistrict_surface_two_terminal_ports import classify


class FramedMap:
    def __init__(self,width,rows,ports):
        # Darts are (vertex, direction, port number). Ordered input ports
        # followed by reversed output ports give the same rotation everywhere.
        self.rotation,self.mate = {},{}
        def vertex(j,m,n):
            ins = [(j,'in',i) for i in range(m)]
            outs = [(j,'out',i) for i in range(n)]
            self.rotation[j] = ins+outs[::-1]
            return ins,outs
        def edge(a,b):
            self.mate[a],self.mate[b] = b,a
        self.bottom,self.top = -2,-1
        _,bottom = vertex(self.bottom,0,width+2)
        wires = bottom[1:-1]
        for j,(p,k) in enumerate(rows):
            m,n = map(len,ports[k])
            ins,outs = vertex(j,m,n)
            for a,b in zip(wires[p:p+m],ins,strict=True):
                edge(a,b)
            wires[p:p+m] = outs
        top,_ = vertex(self.top,len(wires)+2,0)
        for a,b in zip([bottom[0],*wires,bottom[-1]],top,strict=True):
            edge(a,b)

    def core(self):
        rim = [self.mate[d][0] for j in (self.bottom,self.top) for d in self.rotation[j]
               if 0<d[2]<len(self.rotation[j])-1]
        if not rim or min(rim)<0:
            return []
        seen,stack = {rim[0]},[rim[0]]
        while stack:
            for dart in self.rotation[stack.pop()]:
                neighbor = self.mate[dart][0]
                if neighbor>=0 and neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        return sorted(seen) if set(rim)<=seen else []

    def profile(self):
        # Index each framed face by all its frame corners. Repeated visits of
        # a face and bridges use their separate darts, not vertex sets.
        successor,angle = {},{}
        for rot in self.rotation.values():
            for i,a in enumerate(rot):
                b = rot[(i+1)%len(rot)]
                successor[a] = b
                angle[a] = (0 if a[1]!=b[1] else
                            1 if i==len(rot)-1 and rot[0][1]==rot[-1][1] else -1)
        rim,internal = {},[]
        unseen = set(self.mate)
        while unseen:
            d = next(iter(unseen))
            corners,charge,total = [],0,0
            while d in unseen:
                unseen.remove(d)
                a = self.mate[d]
                total += angle[a]
                if a[0]<0:
                    corners.append(a)
                else:
                    charge += angle[a]
                d = successor[a]
            if corners:
                rim[tuple(sorted(corners))] = charge
            else:
                internal.append(total)
        return rim,internal


def inspect(model,site,block):
    vtx,s,t = model.gates[site]
    if model.sweep(vtx,s,block)!=t:
        raise ValueError('port has the wrong path boundary')
    if not block:
        return None
    if not s and not t:
        return dict(kind='point')
    graph = FramedMap(len(s),block,model.ports)
    core = graph.core()
    if not core:
        return None
    rim,_ = graph.profile()
    star,_ = FramedMap(len(s),[(0,site)],model.ports).profile()
    assert rim==star
    return dict(kind='wired',core=core,representative=core[0],rim_sectors=len(rim)-1)


def representative(model,k,b):
    report = inspect(model,k,b)
    return report['representative'] if report else None


def recognize(data):
    if not data['rules']:
        return {}
    site = next(iter(data['rules']))
    model = Presentation(dict(data,vertex=data['gates'][site][0],path='',diagram=[],rules={}))
    return {k:{side:inspect(model,k,io[side]) for side in ('input','output')}
            for k,io in data['rules'].items()}


def audit_ports():
    signatures = [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)]
    gates = {f'g{i}{j}':['x','a'*i,'a'*j] for i,j in signatures}
    gates.update({f'S{i}{j}':['x','a'*i,'a'*j] for i in range(4) for j in range(5)})
    model = Presentation(dict(edges={'a':['x','x']},gates=gates,vertex='x',path='',diagram=[],rules={}))
    good = broader = excluded = 0
    for start in range(4):
        def walk(rows,width):
            nonlocal good,broader,excluded
            if rows and (start or width):
                site = f'S{start}{width}'
                report = inspect(model,site,rows)
                if report:
                    good += 1
                    broader += classify(model,site,rows) is None
                else:
                    excluded += 1
            if len(rows)==3:
                return
            for m,n in signatures:
                if width+n-m<=4:
                    for p in range(width-m+1):
                        walk(rows+[(p,f'g{m}{n}')],width+n-m)
        walk([],start)
    assert good and broader and excluded
    print(f'{good} spanning ports preserve every rim-sector charge; {broader} fail the two-terminal test; '
          f'{excluded} nonspanning or through-wire ports separated')


def audit_corners():
    gates = {k:['x','aa','aa'] for k in ('A','D')}
    gates.update({k:['x','a','aa'] for k in ('F','H')})
    gates.update({k:['x','aa','a'] for k in ('G','J')})
    gates.update({k:['x','',''] for k in ('p','q','r','s','P')})
    blocks = {'A':[(0,'p'),(0,'F'),(1,'G')],'D':[(1,'H'),(0,'J')],'P':[(0,'q'),(0,'r')]}
    data = dict(edges={'a':['x','x']},gates=gates,vertex='x',path='aaaa',
                blocks=blocks,diagram=[(0,'A'),(2,'D'),(0,'P'),(0,'s')])
    c = Corner(data,representative)
    assert c.sizes['A'][:3]==[0,3,0]
    assert all(classify(c.model,k,blocks[k]) is None for k in ('A','D'))
    # The ancillary point p can braid with other stationary points in the
    # same exterior face. First move p from below A to above A and D.
    approach = ()
    state = c.rows
    for i in range(1,5):
        for g in (i,-i):
            moved = exchange(state,g,c.model.ports)
            if moved is not None:
                break
        assert moved is not None
        state = moved
        approach += (g,)
    twist = approach+(5,5)+inv(approach)
    assert follow(c.rows,twist,c.model.ports)==c.rows
    assert c.image(c.project('A',twist))==c.image(()) and c.image(twist)!=c.image(())
    # P is not able to absorb the individual p/q linking either.
    assert solve_corner(dict(data,paths={'A':twist,'D':(),'P':()}),representative)=={'incompatible_pair':['A','P']}
    # Independent finite exchange-component check. Start with the two core
    # blocks and a wired spectator strictly between their footprints.
    xy = {k:[r for r in blocks[k] if r[1]!='p'] for k in ('A','D')}
    gate = dict(c.model.ports,z=('a','a'))
    initial = expand(((0,'A'),(2,'z'),(3,'D')),xy)
    pending,seen = deque([initial]),{initial}
    grouped = set()
    while pending:
        rows = pending.popleft()
        keys = ['A' if k in ('F','G') else 'D' if k in ('H','J') else 'z' for _,k in rows]
        if all(keys.count(k)==1 or max(i for i,x in enumerate(keys) if x==k)-
               min(i for i,x in enumerate(keys) if x==k)==1 for k in set(keys)):
            # Contract the actual consecutive blocks at the proper offset.
            out = []
            for j,(p,k) in enumerate(rows):
                symbol = keys[j]
                if j and symbol==keys[j-1]:
                    continue
                out.append((p-(1 if k=='H' else 0),symbol))
            grouped.add(tuple(out))
        for j in range(1,len(rows)):
            for g in (j,-j):
                new = exchange(rows,g,gate)
                if new is not None and new not in seen:
                    pending.append(new)
                    seen.add(new)
    assert len(grouped)==6
    print(f'{len(seen)} distinct positioned expansions give all {len(grouped)} joint readings; '
          'non-core satellite twist separated by the lifted corner test')


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    f = v(1)
    ff = comp2(ctx,0,f,f)
    def hom(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (hom(f,ff),hom(ff,f))
    # Rebracket the middle three wires between a split on the left and a
    # merge on the right. The opposite port is a two-wire gate.
    p = tree_ctx(string_tree(0,[1,1,1]))
    x,y,z = map(v,maximal_vars(p))
    fit = head(p,comp2(p,0,comp2(p,0,x,y),z),comp2(p,0,x,comp2(p,0,y,z)))
    fit = subst_tm(fit,sub_from(p,ctx,dict(zip(maximal_vars(p),[f]*3))))
    stagger = comp2(ctx,1,comp2(ctx,1,comp2(ctx,0,v(2),f),fit),comp2(ctx,0,f,v(3)))
    ctx += (hom(ff,ff),)
    ctx += (hom(stagger,v(4)),hom(v(4),stagger))
    check_ctx(ctx)
    tm = comp2(ctx,0,v(5),v(6))
    if directory:
        out=Emitter()
        out.check_type('twoStaggeredChanges',ctx,tm,infer(ctx,tm))
        (directory/'PortAngles.agda').write_text(out.module('PortAngles',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(recognize(data) if 'rules' in data else solve_corner(data,representative),indent=2))
    else:
        audit_ports()
        audit_corners()
        typed(args.agda_dir)
