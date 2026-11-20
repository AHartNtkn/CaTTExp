"""Exhaust an ordered crossing rank on a length-graded fibre with two loops."""

from collections import Counter

from fibration_erasing_graph_pentagon import pentagon_routes
from fibration_factor_search import Rule, Stage


def sorting_stage(e):
    rules = {name: Rule('x', source, target) for name, source, target in (
        ('G', 'gt', 'tg'), ('B', 'gt', 'tb'), ('r', 'bg', 'gb'), ('u', 'g'*e+'tt', 't'))}
    return Stage({letter: ('x', 'x') for letter in 'tgb'}, rules)


def inversions(word):
    return sum(word[:i].count('b') for i, c in enumerate(word) if c == 'g')


def cylinder(n):
    stage = sorting_stage(1)
    source = 'g'*n+'t'
    target = 't'+'g'*(n//2)+'b'*(n-n//2)
    cells, index = stage.quotient(stage.backwards('x', source, target, {'u'}, 0))
    # Source crosses bg and performs r at the source fibre. Target crosses gb.
    # At the target fibre P(r) is the identity.
    disks = {'D': ('x', 'ggt', (('G', 1), ('B', 0), ('r', 1)), (('B', 1), ('G', 0)))}
    heights = []
    for reps in cells:
        values = set()
        for path in reps:
            record = ''.join(g.lower() for g, _ in reversed(path) if g in ('G','B'))
            values.add(inversions(record))
        assert len(values) == 1
        heights.append(values.pop())
    moves = stage.edges('x', source, cells, index, disks)
    assert moves and all(heights[i] == heights[j]+1 for i, _, j in moves)
    assert max(heights) == (n//2)*(n-n//2)
    print(f'Width {n}: {len(index)} serial writings, {len(cells)} middle cells, '
          f'{len(moves)} contextual prism edges, maximum inversion rank {max(heights)}.')


def pentagon(e):
    stage = sorting_stage(e)
    def degree(word):
        return word.count('b') + word.count('g') - e*word.count('t')
    assert all(degree(r.source) == degree(r.target) for r in stage.rules.values())
    # Check every 2-face reaching the cartesian pole. No extra letter survives there.
    sources = list(stage.ending_at('x', 't', {'u'}, 3))
    assert all('b' not in w and all(name in ('G','u') for name,_ in path) for w,path in sources)
    w = 'g'*(3*e)+'tttt'
    cells, index = stage.quotient(p for v,p in sources if v == w)
    moves = stage.edges('x',w,cells,index,{
        'M': ('x','g'+stage.rules['u'].source,(('u',1),('G',0)),(('G',e),('G',e+1),('u',0))),
        'V': ('x','g'*(2*e)+'ttt',((('G',1),) if e else ())+(('u',e+1),('u',0)), (('u',e),('u',0)))})
    short, long = pentagon_routes(stage, w, cells, moves)
    assert short == (e == 0) and long
    print(f'e={e}: {len(cells)} pentagon classes, moves {dict(sorted(Counter(g for _,g,_ in moves).items()))}, '
          f'short={short}, long={long}.')


if __name__ == '__main__':
    for width in range(2, 6):
        cylinder(width)
    for e in (0,1):
        pentagon(e)
