"""Decide private degree-four planar comparisons by independent groups of updates.

--comparison FILE uses the normalized old readings of private_four_surface.
Blocks of at most two updates use only their source and target prefix sets.
"""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_private_four_surface import Diagram


def independent(left, right):
    e, _, s = left
    f, _, t = right
    return (s | 1 << e) & ~t == 0 or (t | 1 << f) & ~s == 0


def blocks(source, target):
    """Topologically ordered SCCs of the union of the two trace orders."""
    keys = tuple(letter[:2] for letter in source)
    index = {key:k for k,key in enumerate(keys)}
    after = [1 << k for k in range(len(keys))]
    for word in (source,target):
        for left,right in combinations(word,2):
            if not independent(left,right):
                after[index[left[:2]]] |= 1 << index[right[:2]]
    for k,successors in enumerate(after):
        for i in range(len(keys)):
            if after[i] & (1 << k):
                after[i] |= successors
    # Strict containment of reachable sets along every condensation edge.
    remaining = set(range(len(keys)))
    result = []
    for i in sorted(remaining,key=lambda k:-after[k].bit_count()):
        if i in remaining:
            component = {j for j in remaining if after[j] == after[i]}
            result.append({keys[j] for j in component})
            remaining -= component
    return result


def decide(chart, source, target):
    wanted = {letter[:2]:letter[2] for letter in target}
    if wanted.keys() != {m[:2] for m in source} or any(s & ~wanted[e,j] for e,j,s in source):
        return None, []
    parts = blocks(source,target)
    rank = {key:i for i,part in enumerate(parts) for key in part}
    word = list(source)
    moves = []

    def commute(k):
        assert independent(word[k],word[k+1])
        word[k],word[k+1] = word[k+1],word[k]
        moves.append(('commute',k))

    def reorder(key):
        for i in range(1,len(word)):
            k = i
            while k and key(word[k-1]) > key(word[k]):
                commute(k-1)
                k -= 1

    def finish(k):
        e,j,s = word[k]
        missing = wanted[e,j] & ~s
        while missing:
            bit = missing & -missing
            x = bit.bit_length()-1
            assert chart.legal(x,s) and chart.legal(e,s | bit)
            moves.append(('grow',k,x))
            s |= bit
            missing ^= bit
        word[k] = (e,j,s)

    reorder(lambda m:rank[m[:2]])
    offset = 0
    for part in parts:
        goal = tuple(m for m in target if m[:2] in part)
        if len(part) <= 2:
            if word[offset][:2] != goal[0][:2]:
                e,j,s = word[offset]
                f,l,t = word[offset+1]
                if (s | 1 << e) & ~wanted[f,l] == 0:
                    finish(offset+1)
                else:
                    assert (t | 1 << f) & ~wanted[e,j] == 0
                    finish(offset)
                commute(offset)
            for k in range(offset,offset+len(part)):
                finish(k)
        else:
            path = chart.search(tuple(word[offset:offset+len(part)]), goal)
            if path is None:
                return None, parts
            moves.extend((kind,k+offset,*rest) for kind,k,*rest in path)
            word[offset:offset+len(part)] = goal
        offset += len(part)
    dest = {m[:2]:i for i,m in enumerate(target)}
    reorder(lambda m:dest[m[:2]])
    assert tuple(word) == target
    return moves, parts


def solve(data):
    chart = Diagram(data['width'],data['schedule'])
    (a,w),(b,v) = (chart.read(data['start'],data[k]) for k in ('source','target'))
    if a != b:
        raise ValueError('expected parallel old readings')
    path,parts = decide(chart,w,v)
    return dict(surface_filler=path is not None,block_sizes=list(map(len,parts)),trace_moves=path)


def checks():
    from semistrict_surface_checkpoint_orders import readings
    from semistrict_surface_private_histories import closure
    from semistrict_surface_planar_event_projection import cuts
    from semistrict_surface_planar_columns import Column
    for width,schedule in [(2,[(0,1,2),(0,1,1),(2,1,1),(0,2,1)]),
                           (3,[(1,2,1),(0,1,2),(1,2,2)])]:
        chart = Diagram(width,schedule)
        _,sites = cuts(Column(width,schedule))
        for mask in range(1<<len(schedule)):
            assert chart.sites(mask)==sites.get(frozenset(i for i in range(len(schedule)) if mask>>i&1),{})
    comparisons = 0
    for n,marks in [(3,(0,1,2)),(3,(0,0,1)),(4,(1,3))]:
        start = tuple(range(n))
        chart = Diagram(n,[(i,1,1) for i in reversed(start)])
        words = {chart.read(start,w)[1] for w in readings(start,start[::-1],marks)}
        for source in words:
            reachable = closure(source,lambda w:(q for _,q in chart.steps(w)))
            for target in words:
                steps,_ = decide(chart,source,target)
                assert (steps is not None) == (target in reachable)
                if steps is not None:
                    w = source
                    for move in steps:
                        w = dict(chart.steps(w))[move]
                    assert w == target
                comparisons += 1
    n = 48
    start = list(range(n))
    source,target = [],[]
    for i in range(0,n,2):
        source.extend([(i,0),i,(i+1,0)])
        target.extend([(i+1,0),i,(i,0)])
    result = solve(dict(width=n,schedule=[(i,1,1) for i in reversed(start)],start=start,
                        source=source,target=target))
    assert result['surface_filler'] and result['block_sizes']==[2]*(n//2)
    print(f'{comparisons} comparisons match full trace reachability; 48-event case '
          f'has 24 two-update blocks and {len(result["trace_moves"])} replayable moves')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--comparison',type=Path)
    args = parser.parse_args()
    if args.comparison:
        print(json.dumps(solve(json.loads(args.comparison.read_text()))))
    else:
        checks()
