"""Compile planar ports over the three-gate wired base to one boxed gate.

JSON fields width (initial wire count) and diagram ([wire offset, b/d/t]).
For a whole update give two such ports in fields source and target.
--certificate emits each local 3-rule or planar interchange and its context.
"""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import json
from pathlib import Path


@dataclass(frozen=True)
class Cell:
    source: int
    target: int
    op: str
    children: tuple = ()


def identity(n):
    return Cell(n,n,'id')


def stack(*cells):
    if any(a.target!=b.source for a,b in zip(cells,cells[1:])):
        raise ValueError('noncomposable rows')
    items = tuple(x for c in cells for x in (c.children if c.op=='stack' else (c,)) if x.op!='id')
    if not items:
        return identity(cells[0].source)
    return items[0] if len(items)==1 else Cell(items[0].source,items[-1].target,'stack',items)


def beside(*cells):
    items = []
    for c in cells:
        for cell in c.children if c.op=='beside' else (c,):
            if cell.op=='id':
                if not cell.source:
                    continue
                if items and items[-1].op=='id':
                    cell = identity(cell.source+items.pop().source)
            items.append(cell)
    if not items:
        return identity(0)
    if len(items)==1:
        return items[0]
    return Cell(sum(c.source for c in items),sum(c.target for c in items),'beside',tuple(items))


gates = {g:Cell(s,t,g) for g,s,t in [('b',0,1),('d',1,0),('t',2,2),('m',2,1),('s',1,2),('h',1,1)]}
b,d,t,m,s,h = gates.values()
one = identity(1)
zero = identity(0)


@lru_cache(None)
def pack(n):
    if n==0:
        return b
    return one if n==1 else stack(beside(pack(n-1),one),m)


def mirror(c):
    if c.op=='id':
        return c
    if c.op=='stack':
        return stack(*(mirror(t) for t in reversed(c.children)))
    if c.op=='beside':
        return beside(*(mirror(t) for t in c.children))
    return {'b':d,'d':b,'m':s,'s':m,'h':h,'t':t}[c.op]


def box(r,k):
    return stack(pack(r),h,mirror(pack(k)))


library = {'horizontal':(beside(h,h),stack(m,h,s)),'vertical':(stack(h,h),h),
           'join-assoc':(stack(beside(one,m),m),stack(beside(m,one),m)),
           'join-left-unit':(stack(beside(b,one),m),one),'join-right-unit':(stack(beside(one,b),m),one),
           'cancel-empty':(stack(d,b),one),'cancel-fork':(stack(s,m),one)}
for name in ('assoc','left-unit','right-unit'):
    library['fork-'+name] = tuple(map(mirror,library['join-'+name]))
for c in (b,d,t,one,zero):
    name = c.op if c.op!='id' else 'id'+str(c.source)
    library['leaf-'+name] = (c,box(c.source,c.target))


@dataclass(frozen=True)
class Move:
    name: str
    grid: tuple = ()
    reverse: bool = False
    frames: tuple = ()

    def ends(self):
        if self.name=='rectangle':
            rows = self.grid
            assert rows and rows[0] and all(len(row)==len(rows[0]) for row in rows)
            a = beside(*(stack(*col) for col in zip(*rows)))
            b = stack(*(beside(*row) for row in rows))
        elif self.name=='update':
            assert not self.reverse
            a,b = h,h
        else:
            a,b = library[self.name]
        if self.reverse:
            a,b = b,a
        for axis,l,r in self.frames:
            op = stack if axis=='stack' else beside
            a,b = op(l,a,r),op(l,b,r)
        assert (a.source,a.target)==(b.source,b.target)
        return a,b

    def flipped(self):
        return Move(self.name,self.grid,not self.reverse,self.frames)


@dataclass
class PathProof:
    start: Cell
    end: Cell
    moves: list


def step(name,rows=()):
    move = Move(name,tuple(map(tuple,rows)))
    return PathProof(*move.ends(),[move])


def same(c):
    return PathProof(c,c,[])


def reverse(path):
    return PathProof(path.end,path.start,[m.flipped() for m in reversed(path.moves)])


def chain(*paths):
    assert all(a.end==b.start for a,b in zip(paths,paths[1:]))
    return PathProof(paths[0].start,paths[-1].end,[move for path in paths for move in path.moves])


def frame(axis,l,p,r):
    op = stack if axis=='stack' else beside
    moves = [Move(m.name,m.grid,m.reverse,(*m.frames,(axis,l,r))) for m in p.moves]
    return PathProof(op(l,p.start,r),op(l,p.end,r),moves)


def vertical(p,l=None,r=None):
    return frame('stack',identity(p.start.source) if l is None else l,p,
                 identity(p.start.target) if r is None else r)


def horizontal(p,l=zero,r=zero):
    return frame('beside',l,p,r)


def dual_join(p):
    # Only join-unit/associativity moves and rectangles occur in this proof.
    moves = []
    for m in p.moves:
        grid = tuple(tuple(map(mirror,row)) for row in reversed(m.grid))
        name = m.name.replace('join-','fork-')
        frames = tuple((axis,mirror(r),mirror(l)) if axis=='stack' else (axis,mirror(l),mirror(r))
                       for axis,l,r in m.frames)
        moves.append(Move(name,grid,m.reverse,frames))
    return PathProof(mirror(p.start),mirror(p.end),moves)


def join(r,k):
    a,bk = pack(r),pack(k)
    if k==0:
        arrange = step('rectangle',[(a,zero),(one,b)])
        return chain(vertical(arrange,r=m),vertical(step('join-right-unit'),l=a))
    if r==0:
        arrange = step('rectangle',[(zero,bk),(b,one)])
        return chain(vertical(arrange,r=m),vertical(step('join-left-unit'),l=bk))
    if k==1:
        return same(pack(r+1))
    q = pack(k-1)
    arrange = step('rectangle',[(a,beside(q,one)),(one,m)])
    regroup = reverse(step('rectangle',[(beside(a,q),one),(m,one)]))
    return chain(vertical(arrange,r=m),vertical(step('join-assoc'),l=beside(a,q,one)),
                 vertical(regroup,r=m),vertical(horizontal(join(r,k-1),r=one),r=m))


def cancel(n):
    if n==0:
        return step('cancel-empty')
    if n==1:
        return same(one)
    p = pack(n-1)
    regroup = reverse(step('rectangle',[(mirror(p),one),(p,one)]))
    return chain(vertical(regroup,l=s,r=m),vertical(horizontal(cancel(n-1),r=one),l=s,r=m),step('cancel-fork'))


def parallel(a,b):
    x,u,y,v = a.start.source,b.start.source,a.start.target,b.start.target
    before,after = beside(pack(x),pack(u)),beside(mirror(pack(y)),mirror(pack(v)))
    arrange = step('rectangle',[(pack(x),pack(u)),(h,h),(mirror(pack(y)),mirror(pack(v)))])
    return chain(horizontal(a,r=b.start),horizontal(b,l=a.end),arrange,
                 vertical(step('horizontal'),l=before,r=after),
                 vertical(join(x,u),r=stack(h,s,after)),vertical(dual_join(join(y,v)),l=stack(pack(x+u),h)))


def serial(a,b):
    r,n,k = a.start.source,a.start.target,b.start.target
    assert b.start.source==n
    return chain(vertical(a,r=b.start),vertical(b,l=a.end),
                 vertical(cancel(n),l=stack(pack(r),h),r=stack(h,mirror(pack(k)))),
                 vertical(step('vertical'),l=pack(r),r=mirror(pack(k))))


def normalize(c):
    if c.op in ('beside','stack'):
        op = parallel if c.op=='beside' else serial
        path = normalize(c.children[0])
        for q in c.children[1:]:
            path = op(path,normalize(q))
        return path
    if c.op=='id' and c.source>1:
        return parallel(normalize(identity(c.source-1)),step('leaf-id1'))
    name = 'id'+str(c.source) if c.op=='id' else c.op
    return step('leaf-'+name)


def replay(path):
    state = path.start
    for move in path.moves:
        src,dst = move.ends()
        assert state==src, (move.name,state,src)
        state = dst
    assert state==path.end
    return state


def display(c):
    if c.op=='id':
        return ['id',c.source]
    return [c.op,*map(display,c.children)] if c.children else c.op


def emit(move):
    return dict(rule=move.name,reverse=move.reverse,grid=[[display(c) for c in row] for row in move.grid],
                frames=[[axis,display(l),display(r)] for axis,l,r in move.frames])


def read_port(data):
    width = data['width']
    if type(width)!=int or width<0:
        raise ValueError('expected a nonnegative initial width')
    port = identity(width)
    for pos,name in data['diagram']:
        if name not in ('b','d','t'):
            raise ValueError('expected an original gate b, d, or t')
        g = gates[name]
        if type(pos)!=int or not 0<=pos<=port.target-g.source:
            raise ValueError('gate outside wire interval')
        row = beside(identity(pos),g,identity(port.target-pos-g.source))
        port = stack(port,row)
    return port


def compile_port(data,certificate=False):
    port = read_port(data)
    path = normalize(port)
    assert replay(path)==box(port.source,port.target)
    assert replay(reverse(path))==port
    result = dict(source=display(port),boxed=display(path.end),moves=dict(Counter(m.name for m in path.moves)))
    if certificate:
        result['certificate'] = list(map(emit,path.moves))
    return result


def compile_update(data,certificate=False):
    a,z = (read_port(data[k]) for k in ('source','target'))
    if (a.source,a.target)!=(z.source,z.target):
        raise ValueError('the two ports must have matching wire boundaries')
    centre = vertical(step('update'),l=pack(a.source),r=mirror(pack(a.target)))
    proof = chain(normalize(a),centre,reverse(normalize(z)))
    assert replay(proof)==z
    result = dict(source=display(a),target=display(z),moves=dict(Counter(m.name for m in proof.moves)))
    if certificate:
        result['certificate'] = list(map(emit,proof.moves))
    return result


def audit():
    from semistrict_surface_history_group import exchange
    used = set()
    for r in range(5):
        for k in range(5):
            p = join(r,k)
            assert replay(p)==pack(r+k) and replay(dual_join(p))==mirror(pack(r+k))
    tested = moves = 0
    for n in range(5):
        todo = [(n,[])]
        while todo:
            width,rows = todo.pop()
            proof = compile_port(dict(width=n,diagram=rows))
            used.update(proof['moves'])
            moves += sum(proof['moves'].values())
            tested += 1
            if len(rows)<2:
                for g in (b,d,t):
                    for pos in range(width-g.source+1):
                        todo.append((width-g.source+g.target,rows+[(pos,g.op)]))
    assert used==set(library)|{'rectangle'}
    for n in range(4):
        for gates1,gates2 in [([[n,'b'],[n,'d']],[]),([],[[0,'b'],[0,'d']])]:
            result = compile_update(dict(source=dict(width=n,diagram=gates1),target=dict(width=n,diagram=gates2)))
            assert result['moves']['update']==1
    # The two occurrences of t delimit a lens. A floating b;d component
    # lives inside on one side of this attachment and outside on the other.
    inside = ((0,'t'),(1,'b'),(1,'d'),(0,'t'))
    outside = ((0,'t'),(0,'b'),(0,'d'),(0,'t'))
    ports = {name:('f'*c.source,'f'*c.target) for name,c in gates.items()}
    reach = {inside}
    agenda = [inside]
    while agenda:
        at = agenda.pop()
        for letter in (-3,-2,-1,1,2,3):
            dest = exchange(at,letter,ports)
            if dest is not None and dest not in reach:
                reach.add(dest)
                agenda.append(dest)
    assert outside not in reach
    crossing = compile_update(dict(source=dict(width=2,diagram=inside),target=dict(width=2,diagram=outside)))
    assert crossing['moves']['update']==1
    print(f'{tested} situated ports, {moves} forward moves and their reverses, all {len(library)} template pairs exercised.')
    print('The lens attachment compiles at its original ends; its two ports lie in separate planar exchange components.')


def typed(directory):
    from functools import reduce
    from catt import STAR,arr,check_ctx,comp2,disc_tree,infer,src,subst_tm,subst_ty,tgt,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity as unit
    from semistrict_surface_directed_power_queries import apply

    def row(ctx,cut,cells):
        return reduce(lambda a,b:comp2(ctx,cut,a,b),cells)
    def path(ctx,x,letters):
        return row(ctx,0,letters) if letters else unit(ctx,x)
    def hom(ctx,a,b):
        return arr(infer(ctx,a),a,b)
    graph = (STAR,arr(STAR,v(0),v(0)))
    def wires(n):
        return path(graph,v(0),[v(1)]*n)
    base = graph+tuple(hom(graph,wires(c.source),wires(c.target)) for c in gates.values())
    names = {name:v(i+2) for i,name in enumerate(gates)}

    @lru_cache(None)
    def fit(r,k,expand):
        # Generic line on distinct objects, also when either subword is empty.
        line = tree_ctx(((),)*(r+k))
        edges = [v(2*i+2) for i in range(r+k)]
        flat = path(line,v(0),edges)
        split = comp2(line,0,path(line,v(0),edges[:r]),path(line,v(2*r-1 if r else 0),edges[r:]))
        if flat==split:
            return None
        change = head(line,flat,split) if expand else head(line,split,flat)
        sigma = [v(0) if ty==STAR else v(1) for ty in line]
        return subst_tm(change,sigma)

    @lru_cache(None)
    def read(c):
        if c.op=='id':
            return unit(base,wires(c.source))
        if c.op=='stack':
            return row(base,1,list(map(read,c.children)))
        if c.op!='beside':
            return names[c.op]
        a = c.children[0]
        term = read(a)
        r,k = a.source,a.target
        for y in c.children[1:]:
            middle = comp2(base,0,term,read(y))
            terms = [u for u in (fit(r,y.source,True),middle,fit(k,y.target,False)) if u is not None]
            term = row(base,1,terms)
            r,k = r+y.source,k+y.target
        return term

    full = base
    instruction = {}
    for name,(a,z) in library.items():
        for back,l,r in [(False,a,z),(True,z,a)]:
            instruction[name,back] = v(len(full))
            full += (hom(base,read(l),read(r)),)
    update = v(len(full))
    full += (hom(base,names['h'],names['h']),)
    check_ctx(full)
    emitter = Emitter() if directory else None
    for name,left,right in [('leaf-t',names['m'],names['s']),('leaf-id0',names['b'],names['d'])]:
        centre = row(full,1,[left,update,right])
        term = row(full,2,[instruction[name,False],centre,instruction[name,True]])
        expected = read(library[name][0])
        assert infer(full,term)==hom(full,expected,expected)
        if emitter:
            emitter.check_type('closedBox' if name=='leaf-id0' else 'wiredBox',full,term,hom(full,expected,expected))

    # Distinct source/target 2-gates at two-wire ends; a packet wire decodes
    # to ff. Verify the decoder and its actual fixed-boundary correction.
    ff = wires(2)
    old = graph+(hom(graph,ff,ff),)*2
    old += (hom(old,v(2),v(3)),)
    named = old[:4]+(graph[1],)
    p = v(4)
    named += (hom(named,ff,p),hom(named,p,ff),hom(named,p,p),hom(named,p,p))
    start,finish = (row(named,1,[v(5),v(i),v(6)]) for i in (7,8))
    named += (hom(named,v(2),start),hom(named,finish,v(3)),hom(named,v(7),v(8)))
    term = row(named,2,[v(9),row(named,1,[v(5),v(11),v(6)]),v(10)])
    disk = tree_ctx(disc_tree(2))
    top = v(len(disk)-1)
    dressed = row(disk,1,[unit(disk,src(disk,top)),top,unit(disk,tgt(disk,top))])
    def collar(ctx,cell,expand):
        x,y = (top,dressed) if expand else (dressed,top)
        return apply(ctx,(disk,head(disk,x,y)),[cell])
    images = [v(i) for i in range(4)]+[ff,unit(old,ff),unit(old,ff),v(2),v(3),
              collar(old,v(2),True),collar(old,v(3),False),v(4)]
    for i,value in enumerate(images):
        assert infer(old,value)==subst_ty(named[i],images[:i])
    high = tree_ctx(disc_tree(3))
    j = v(len(high)-1)
    inner = row(high,1,[unit(high,src(high,src(high,j))),j,unit(high,tgt(high,tgt(high,j)))])
    decoded = row(high,2,[collar(high,src(high,j),True),inner,collar(high,tgt(high,j),False)])
    assert apply(old,(high,decoded),[v(4)])==subst_tm(term,images)
    readback = apply(old,(high,head(high,decoded,j)),[v(4)])
    if emitter:
        emitter.check_typed('readDistinctUpdates',old,readback)
        (directory/'BoxedPort.agda').write_text(emitter.module('BoxedPort',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--certificate',action='store_true')
    parser.add_argument('--presentation',action='store_true',help='print the fixed gates and 3-rule faces')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.presentation:
        print(json.dumps(dict(wires=['f'],gates={k:[c.source,c.target] for k,c in gates.items()},
                              bidirectional={k:[display(a),display(z)] for k,(a,z) in library.items()},
                              directed={'update':[display(h),display(h)]}),indent=2))
    elif args.input:
        data = json.loads(args.input.read_text())
        compile_query = compile_update if 'source' in data else compile_port
        print(json.dumps(compile_query(data,args.certificate),indent=2))
    else:
        audit()
        typed(args.agda_dir)
