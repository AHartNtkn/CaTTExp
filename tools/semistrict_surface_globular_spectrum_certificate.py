"""Verify the finite obstruction closing the degree-six globular Gray spectrum.

--emit FILE exports the all-boundary reduction to the two extremal face rows.
The three resulting marked top rows are tested by exact trace-aware pasting.
"""

from argparse import ArgumentParser
from collections import Counter,deque
from pathlib import Path
from itertools import combinations,product
from semistrict_surface_tree_spectra import Tree

from semistrict_surface_branched_comparisons import certificate_rows, query
from semistrict_surface_generated_quotient import Chart, minus, only_these_rows
from semistrict_surface_penultimate_intervals import check
from semistrict_surface_trace_quotient import TracePasting

SHAPES = [[[[]]],[[[[]],[[]]]],[[[]]]]
LEAST_SOURCE = (0,2,5,7,18,22,26,27,29,46,49,54,58)
GREATEST_TARGET = (9,11,12,14,31,34,38,43,45,47,52,57,61)


def exterior_reach(chart,start,sign):
    """Every arc is an actual native step at the fixed old lower boundary."""
    steps = []
    for w in chart.layers[5]:
        if any(d==0 for d,x in w):
            steps.append([(chart.indices[4][f],sign*n) for f,n in chart.boundary(w).items()])
    reached = {start}
    todo = deque([start])
    while todo:
        current = todo.popleft()
        for step in steps:
            v = Counter(current)
            v.update(dict(step))
            if min(v.values())<0:
                continue
            target = tuple(sorted(v.elements()))
            if target not in reached:
                reached.add(target)
                todo.append(target)
    return sorted(reached)


def specified(name,indices,size):
    counts = Counter(indices)
    return '(and '+' '.join(f'(= {name}{i} {counts[i]})' for i in range(size))+')'


def reduction(chart):
    # The middle change at the high step has high outer phases and the change
    # at the low step has low outer phases. Basis order is verified explicitly.
    for i,phases in ((19,(1,1,1)),(8,(0,0,0))):
        w = chart.layers[5][i]
        assert [d for d,x in w]==[1,3,1]
        assert (w[0][1][1],w[1][1][1][0],w[2][1][1])==phases
    old = certificate_rows()
    for top in (LEAST_SOURCE,GREATEST_TARGET):
        image = Counter()
        for i in top:
            image.update({chart.indices[3][f]:n for f,n in chart.boundary(chart.layers[4][i]).items()})
        expected = Counter(old[3][1])
        expected.subtract(old[3][0])
        assert image==expected
    accepted = []
    for r,pair in enumerate(old[:4]):
        for tag,indices in zip(('m','p'),pair):
            accepted.append(specified(f'r{r}{tag}',indices,len(chart.layers[r])))
    starts = exterior_reach(chart,LEAST_SOURCE,1)
    ends = exterior_reach(chart,GREATEST_TARGET,-1)
    for name,rows in [('r4m',starts),('r4p',ends)]:
        accepted.append('(or '+' '.join(specified(name,v,len(chart.layers[4])) for v in rows)+')')
    assert len(starts)==len(ends)==16
    outside = '(assert (not (and '+' '.join(accepted)+')))'
    return query(SHAPES,require_raw_failure=False,
                 constraints=['(assert (> y8 0))','(assert (> y19 0))',outside])


def fold_column(shape,keep):
    """Retain specified children recursively; a degenerate top generator maps to zero."""
    source = Tree(shape)
    target_children = []
    images = {(0,v):(0,sum(i<v for i,_ in keep)) for v in source.layers[0]}
    for new_index,(i,child_keep) in enumerate(keep):
        child_shape,child_map = fold_column(shape[i],child_keep)
        target_children.append(child_shape)
        for (d,x),(_,y) in child_map.items():
            images[d+1,(i,x)] = (d+1,(new_index,y))
    target = Tree(target_children)
    for r,layer in source.layers.items():
        if not r:
            continue
        for x in layer:
            src,tgt = source.faces[x]
            boundary = Counter()
            for f,n in ((src,-1),(tgt,1)):
                if (r-1,f) in images:
                    boundary[images[r-1,f][1]] += n
            expected = Counter()
            if (r,x) in images:
                a,b = target.faces[images[r,x][1]]
                expected[b] += 1
                expected[a] -= 1
            assert boundary==expected
    return target_children,images


def folding_checks():
    outer = [[[],[],[]],[[],[]]]
    middle = [[[[],[[]]],[[],[],[]],[[[]],[]]],[[[],[]],[[],[]]]]
    outer_maps = []
    for event,steps in enumerate(outer):
        for cut in range(len(steps)):
            shape,image = fold_column(outer,[(event,[(cut,[])])])
            assert shape==SHAPES[0]
            for low in range(cut+1):
                for high in range(cut+1,len(steps)+1):
                    assert image[1,(event,low)]==(1,(0,0))
                    assert image[1,(event,high)]==(1,(0,1))
            outer_maps.append(image)
    checked = 0
    for event,steps in enumerate(middle):
        for low,high in combinations(range(len(steps)),2):
            for i,j in product(range(len(steps[low])),range(len(steps[high]))):
                plan = [(event,[(low,[(i,[])]),(high,[(j,[])])])]
                shape,image = fold_column(middle,plan)
                assert shape==SHAPES[1]
                for reduced,(step,change) in enumerate(((low,i),(high,j))):
                    for parallel in range(len(steps[step][change])+1):
                        label = (event,(step,(change,parallel)))
                        assert image[3,label]==(3,(0,(reduced,(0,0))))
                checked += len(outer_maps)**2
    print(f'{checked} branching threshold-map combinations verified',flush=True)


def certificate(emit=None,from_target=False):
    folding_checks()
    chart = Chart(SHAPES,5)
    sentence = reduction(chart)
    if emit:
        emit.write_text(sentence)
    assert check(sentence)=='unsat'
    print('All conflicting old faces have the prescribed lower rows and lie between the two extrema '
          '(16 possible sources and 16 possible targets).',flush=True)
    lower = certificate_rows()[:4]
    old = tuple(tuple(chart.row(r,s) for s in pair) for r,pair in enumerate(lower))
    boundary = old+((chart.row(4,LEAST_SOURCE),chart.row(4,GREATEST_TARGET)),)
    choices = [[0,3,5,8,14,19,j,23,30,32,33] for j in (20,21,22)]
    assert only_these_rows(chart,boundary[4],choices,required=(8,19))
    search = TracePasting(chart,from_target=from_target)
    faces = tuple(tuple(tuple(chart.layers[r][i] for i in s) for s in pair)
                  for r,pair in enumerate(lower))
    trace = search.traces.read(faces)
    for side in boundary[4]:
        assert search.generated(old+((side,side),),trace)
    delta = minus(boundary[4][1],boundary[4][0])
    for solution in choices:
        top = chart.row(5,solution)
        assert chart.differential(5,top)==delta
        assert not search.generated(boundary+((top,top),),trace)
        print(f'Excluded all eleven atoms together at middle phase {solution[6]-20}.',flush=True)
    print(f'{search.visited:,} decorated states checked at the extremal boundary.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--emit',type=Path)
    parser.add_argument('--from-target',action='store_true',help='peel terminal steps first')
    args = parser.parse_args()
    certificate(args.emit,args.from_target)
