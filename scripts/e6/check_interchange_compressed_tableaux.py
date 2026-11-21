"""Compare row-program coordinates with contraction on individually named cells."""

from itertools import product
from random import Random

from check_interchange_grid_contractions import normal_path
from interchange_compressed_tableaux import Block, Tableaux
from interchange_shared_whiskers import Words
from check_interchange_row_bounds import moving_halves
from interchange_gray_composition import check_stationary
from interchange_subdivision import stack_image
from t_endomorphisms import all_extensions


def fold(raw, nodes):
    if not nodes:
        return 0
    while len(nodes) > 1:
        nodes = [raw.join(a,b) for a,b in zip(nodes[::2],nodes[1::2])] + (
            nodes[-1:] if len(nodes) % 2 else [])
    return nodes[0]


def repeat(raw, node, n):
    result = 0
    while n:
        if n % 2:
            result = raw.join(result,node)
        n //= 2
        if n:
            node = raw.join(node,node)
    return result


def explicit_coordinates(events, rows):
    result = [[] for _ in range(rows)]
    for rs, cs in normal_path(events):
        area = len(rs)*len(cs)
        for r, values in enumerate(result):
            values.append(Block(rs[0], rs[-1]+1, len(cs)) if r in rs else None)
            values.extend([None]*(area-1))
    return result


def decode(records, node):
    pending = [node]
    while pending:
        i = pending.pop()
        if not i:
            continue
        rule = records.nodes[i]
        if rule[0] == 'join':
            pending.extend(reversed(rule[1:]))
        elif rule[0] == 'blank':
            yield from (None for _ in range(records.weight[i]))
        else:
            yield rule[1]
            yield from (None for _ in range(records.weight[i]-1))


def verify(raw, roots, rows):
    table = Tableaux(raw,rows)
    for node, initial, events in roots:
        codes = table.coordinates(node,initial)
        assert [list(decode(table.rec,x)) for x in codes] == explicit_coordinates(events, rows)


def check_small():
    total = 0
    for rows, cols in ((2,6),(3,3),(4,3)):
        raw, batch = Words(), []
        for events in sorted(all_extensions(tuple(range(rows)),tuple(range(cols)))):
            root = fold(raw,[raw.letter(r) for r,_ in events])
            batch.append((root,(0,)*rows,events))
            if len(batch) == 96:
                verify(raw,batch,rows)
                total += len(batch)
                raw, batch = Words(), []
        verify(raw,batch,rows)
        total += len(batch)
    rng = Random(1729)
    for _ in range(30):
        rows = 6
        raw, batch = Words(), []
        spelling = tuple(rng.randrange(rows) for _ in range(28))
        root = fold(raw,[raw.letter(r) for r in spelling])
        counts = [0]*rows
        need = [0]*(rows-1)
        for r in spelling:
            counts[r] += 1
            for j in range(rows-1):
                need[j] = max(need[j], counts[j+1]-counts[j])
        for gaps in product(range(2), repeat=rows-1):
            height = [0]*rows
            for j in reversed(range(rows-1)):
                height[j] = height[j+1]+need[j]+gaps[j]
            initial = tuple(height)
            events = []
            for r in spelling:
                events.append((r,-height[r]))
                height[r] += 1
            batch.append((root,initial,events))
        verify(raw,batch,rows)
        total += len(batch)
    print(f"{total} schedules and starting shuffles agree with named rectangular contractions.")


def counter(raw, n):
    separator = raw.letter(2*n)
    pieces = [separator]
    for i in range(n):
        u,d = (raw.letter(2*i+j) for j in (0,1))
        pieces.extend((u,u,d,d))
    value = fold(raw,pieces+[separator])
    for i in range(n):
        u,d = (raw.letter(2*i+j) for j in (0,1))
        value = fold(raw,[value,u,value,d])
    stride = 2*raw.length[value]+1
    start = tuple(stride*(n-r//2) for r in range(2*n+1))
    return value, start


def check_counter():
    # Enumerate the substrings only in this small witness for the grammar
    # lower bound. The proof uses the recursive schedule for all n.
    n=5
    raw=Words()
    root,start=counter(raw,n)
    letters=[]
    pending=[root]
    while pending:
        node=pending.pop()
        rule=raw.rules[node]
        if len(rule)==2:
            pending.extend(~x for x in reversed(rule))
        else:
            letters.append(rule[0])
    height=list(start)
    events=[]
    for r in letters:
        events.append((r,-height[r]))
        height[r]+=1
    canonical=[]
    for rs,cs in normal_path(events):
        canonical.extend(r for _ in reversed(cs) for r in rs)
    observed = set()
    for i, r in enumerate(canonical):
        if r != 2*n or i+4*n+1 >= len(canonical) or canonical[i+4*n+1] != 2*n:
            continue
        factor = tuple(canonical[i+1:i+4*n+1])
        if 2*n not in factor:
            observed.add(factor)
    assert len(observed)==2**n
    verify(raw,[(root,start,events)],2*n+1)
    print(f"All {2**n} distinct length-{4*n} assignment factors occur in the canonical sweep.")


def check_long():
    raw=Words()
    rows=5
    width=2**116+3
    letters=[raw.letter(i) for i in range(rows)]
    columns=repeat(raw,fold(raw,letters),width)
    strips=fold(raw,[repeat(raw,v,width) for v in letters])
    cut=width//3
    batches=fold(raw,[repeat(raw,fold(raw,letters),cut),
                      fold(raw,[repeat(raw,v,width-cut) for v in letters])])
    # The forbidden 2-by-3 projection in the first two rows cannot expand.
    seed=fold(raw,[letters[r] for r in (0,0,1,0,1,1)])
    bad=fold(raw,[seed,fold(raw,[repeat(raw,v,3) for v in letters[2:]]),
                  repeat(raw,fold(raw,letters),width-3)])
    table=Tableaux(raw,rows)
    start=(0,)*rows
    assert table.equal(columns,strips,start) and table.equal(batches,strips,start)
    assert not table.equal(bad,strips,start)
    nonzero=tuple(2**125 if r<2 else 0 for r in range(rows))
    assert not table.equal(columns,strips,nonzero)
    print(f"{width} implicit moving positions on five rows: column, row and batch sweeps agree; two inequalities distinguished.")


def check_cylinder_rows():
    total = 0
    for p, rows, width in product((4,5,6),range(2,6),range(2,6)):
        def heights(chain):
            markers = {col:layer for (dim,layer),(rank,col) in chain if dim==p-1 and rank==1}
            moving = [index for (dim,index),(rank,_) in chain if dim==p and rank==0]
            assert sorted(moving)==list(range(width)) and len(markers)==rows
            order = range(rows) if p%2==0 else reversed(range(rows))
            return tuple(markers[i] for i in order)
        def check(parts,middle):
            actual = [(heights(x[p][0]),heights(x[p][1])) for x in parts]
            assert actual==[((0,)*rows,middle),(middle,(width,)*rows)]
        for cut in range(1,width):
            parts = [stack_image(z,1,1,0,rows) for z in moving_halves(p,0,cut,width)]
            check(parts,(cut,)*rows)
            total += 1
        for cut in range(1,rows):
            parts = [stack_image(z,p,0,0,width) for z in check_stationary(p,0,cut,rows)]
            first = cut if p%2==0 else rows-cut
            check(parts,(width,)*first+(0,)*(rows-first))
            total += 1
    print(f"{total} signed cylinder subdivisions give the predicted individual marker heights.")

if __name__=='__main__':
    check_cylinder_rows()
    check_small()
    check_counter()
    check_long()
