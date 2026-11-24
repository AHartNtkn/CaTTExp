"""Exclude polygon meetings by positive braid-prefix intervals at the endpoint cuts."""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_serial_polygons import decide as serial, frames
from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_stationary_polygons import coset, initial_atoms, passive_prefix, spelling, strip_atom


def divides(n, a, b):
    if len(a) > len(b):
        return False
    x, y = positive_normal(n,a), positive_normal(n,b)
    while x:
        g = min(initial_atoms(x))
        if g not in initial_atoms(y):
            return False
        x, y = strip_atom(n,x,g), strip_atom(n,y,g)
    return True


def charts(model, source, first, second):
    u,end = model.parse(source,first)
    v,other = model.parse(source,second)
    if model.attachments or end != other:
        raise ValueError('expected parallel positive 3-computad readings')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    data = resolution(source,(first,second),arities,'swap')
    if data is None:
        return None
    widths,flow,graph,orders = data
    n = sum(widths)
    def run(reading, records):
        word, info = frames(source,graph,flow,reading,records)
        names, k, old = list(range(n)), 0, {}
        for p,(before,partition,j) in info.items():
            for g in word[k:j]:
                names[g-1],names[g] = names[g],names[g-1]
            k = j
            i = before[2]
            start = sum(size for _,size in partition[:i])
            stop = start+partition[i][1]
            old[p] = (frozenset(names[:start]),tuple(names[start:stop]),j)
        return word,old
    a,x = run(orders[0],u)
    b,y = run(orders[1],v)
    if positive_normal(n,a) != positive_normal(n,b):
        return None
    if any(not x[p][0] <= y[p][0] or x[p][1] != y[p][1] for p in x):
        return None
    return n, a, b, x, y


def interval(n, word, prefix_len, location, size):
    stop = location+size
    prefix,suffix=word[:prefix_len],word[prefix_len:]
    lo = tuple(reversed(spelling(coset(n,prefix,location,stop))))
    hi = prefix+passive_prefix(n,suffix,location,stop)[0]
    return lo,hi


def permits(chart, p, q):
    """A meeting P before Q forces the initial P and final Q cuts to meet."""
    n,a,b,x,y = chart
    start,P,pa=x[p]
    finish,Q,qb=y[q]
    if not start.union(P)<=finish or set(Q).intersection(P):
        return False
    u=interval(n,a,pa,len(start),len(P))
    v=interval(n,b,qb,len(finish),len(Q))
    return divides(n,u[0],v[1]) and divides(n,v[0],u[1])


def locks(model, source, first, second):
    chart = charts(model,source,first,second)
    if chart is None:
        return dict(surface=False, obstruction='incompatible resolved placements')
    old, new = list(chart[3]), list(chart[4])
    dest = {p:j for j,p in enumerate(new)}
    blocked = []
    for p,q in combinations(old,2):
        if not permits(chart,p,q) and not permits(chart,q,p):
            blocked.append((p,q))
            if dest[p]>dest[q]:
                return dict(surface=False, obstruction='required meeting has incompatible cuts',
                            polygon_pair=(p,q))
    never = set(blocked)
    fixed = all((p,q) in never for p,q in zip(old,old[1:]))
    return dict(surface=None, fixed_order=fixed, excluded_meetings=blocked)


def decide(model, source, first, second, radius=None):
    test = locks(model,source,first,second)
    if test['surface'] is not None:
        return test
    fixed = serial(model,source,first,second,radius)
    if fixed['surface'] is True:
        return {**test, 'surface':True, 'checkpoints':fixed['checkpoints']}
    if test['fixed_order'] and (fixed['surface'] is False or 'checkpoints' not in fixed
                                or any(r['surface'] is False for r in fixed['checkpoints'])):
        return {**test, 'surface':False, 'obstruction':fixed.get('obstruction','fixed-order rejection')}
    return test


def checks():
    from semistrict_surface_raw_movie_graph import steps
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_one_step_reflection import quotient
    from itertools import product
    words = [w for length in range(4) for w in product((1,2,3),repeat=length)]
    divs = 0
    for a,b in product(words,repeat=2):
        assert divides(4,a,b) == (quotient(a,b) is not None)
        divs += 1
    s = ((0,'s'),)
    bubble = ((0,'b'),(0,'d'))
    rules = [Rule('',s,s),Rule('',s,bubble)]
    model = Movies(Presentation({'f':(0,0)}, {'s':('',''),'b':('','f'),'d':('f','')},
                                rules, {'s':0, 'b':0}), '')
    source = s*5
    def query(braid):
        lead = ((0,0),)+steps(braid)
        x = lead+((1,2),)+steps(rectangle(2,2,2))
        y = lead+steps(rectangle(2,1,2))+((1,4),)
        return x,y
    positive = query((0,0,1,1))
    test = decide(model,source,*positive,radius=4)
    assert test['surface'] is True and test['fixed_order']
    chart = charts(model,source,*positive)
    assert chart[3][0][0].union(chart[3][0][1]) <= chart[4][1][0]
    # Same individual crossing counts. Reversing the order of the two
    # twists allows them to be placed on opposite sides of a joint frame.
    other = query((1,1,0,0))
    assert not locks(model,source,*other)['fixed_order']
    padded = Movies(Presentation({'f':(0,0)},model.pres.marks,
                                 [rules[0],Rule('f',((1,'s'),),((1,'b'),(1,'d')))],
                                 {'s':0,'b':0}), 'f')
    assert serial(padded,((1,'s'),)*5,*positive,4)['surface'] is None
    assert decide(padded,((1,'s'),)*5,*positive,4)['surface'] is False

    from random import Random
    from semistrict_surface_raw_movie_graph import raw_updates,read
    from semistrict_surface_polygon_windings import exchange
    rng = Random(113)
    trajectories = commutations = 0
    for _ in range(260):
        h,first = source, ()
        for _ in range(rng.randrange(4,9)):
            choices = [(('swap',i),model.swap(h,i,True)) for i in range(len(h)-1)]
            choices.extend(((p,i),r[0]) for i in range(len(h)) for p in (0,1)
                           if (r := model.named(h,p,i)) is not None)
            act,h = rng.choice([(op,t) for op,t in choices if t is not None])
            first += (act,)
        ids = list(range(sum(p != 'swap' for p,_ in first)))
        word, exchanged = first,set()
        for _ in range(5):
            hs,windows = read(model,source,word)
            opts = list(raw_updates(model,word,hs,windows,len(word)))
            if not opts:
                break
            v = rng.choice(opts)
            move = exchange(word,v,windows)
            if move is not None:
                j,_ = move
                exchanged.add(tuple(sorted(ids[j:j+2])))
                ids[j:j+2] = reversed(ids[j:j+2])
                commutations += 1
            word = v
        result = locks(model,source,first,word)
        assert result['surface'] is not False
        assert exchanged.isdisjoint(result['excluded_meetings'])
        trajectories += 1
    return dict(positive_divisibility=divs, braid_sensitive_locks=2,
                fixed_order_with_two_gains=test['surface'], padded_rejection=True,
                placed_trajectories=trajectories, observed_meetings=commutations)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query', type=Path)
    parser.add_argument('--radius', type=int)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target'])))
                 for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result = decide(model,source,q['first'],q['second'],args.radius)
    else:
        result = checks()
    print(json.dumps(result))
