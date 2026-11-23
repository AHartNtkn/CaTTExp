"""Read a positive planar 2-computad interval by tracking the ports of each event."""
import argparse
from dataclasses import dataclass
from itertools import combinations
import json
from semistrict_surface_interval_degrees import degree_bounds


@dataclass(frozen=True)
class Event:
    name: str
    inputs: tuple
    outputs: tuple


def read(initial, rules, history, events=None):
    """Port names are (creator occurrence, port index), with creator -1 at the input."""
    if any(not l or not r for l,r in rules.values()):
        raise ValueError('each rule must have nonempty input and output')
    fresh = events is None
    events = [] if fresh else events
    lookup = {(e.name,e.inputs):i for i,e in enumerate(events)}
    live = [(x,(-1,i)) for i,x in enumerate(initial)]
    order = []
    for name,pos in history:
        left,right = rules[name]
        block = live[pos:pos+len(left)]
        if pos < 0 or [x for x,_ in block] != list(left):
            raise ValueError('ill-typed temporal step')
        ports = tuple(p for _,p in block)
        if fresh:
            idx = len(events)
            events.append(Event(name,ports,tuple((idx,i) for i in range(len(right)))))
        elif (name,ports) not in lookup:
            return None
        else:
            idx = lookup[name,ports]
        order.append(idx)
        live[pos:pos+len(left)] = list(zip(right,events[idx].outputs))
    if len(order) != len(events):
        return None
    return events, tuple(order), tuple(live)


def execute(live,event):
    try:
        pos = live.index(event.inputs[0])
    except ValueError:
        return None
    if live[pos:pos+len(event.inputs)] != event.inputs:
        return None
    return pos, live[:pos]+event.outputs+live[pos+len(event.inputs):]


def traces(initial, events):
    def walk(live, used, steps, written):
        if len(steps) == len(events):
            yield steps,written
        for i,e in enumerate(events):
            if i in used:
                continue
            fired = execute(live,e)
            if fired:
                pos,after = fired
                yield from walk(after,used|{i},steps+(i,),written+((e.name,pos),))
    yield from walk(initial,set(),(),())


def swap_native(initial, events, order, k):
    live = initial
    for idx in order[:k]:
        _,live = execute(live,events[idx])
    first = execute(live,events[order[k]])
    second = execute(live,events[order[k+1]])
    return second is not None and second[0] < first[0]


def positive_sort(initial, events, start, goal):
    order = list(start)
    certificate = []
    for i,x in enumerate(goal):
        j = order.index(x)
        while i < j:
            if not swap_native(initial,events,order,j-1):
                return None
            certificate.append(j-1)
            order[j-1],order[j] = x,order[j-1]
            j -= 1
    return certificate


def solve(data):
    initial, rules = data['initial'], data['rules']
    events,start,source_end = read(initial,rules,data['source'])
    target = read(initial,rules,data['target'],events)
    if target is None or target[2] != source_end:
        return {'same_diagram': False, 'raw_3_path': False}
    goal = target[1]
    ports = tuple((-1,i) for i in range(len(initial)))
    cert = positive_sort(ports,events,start,goal)
    result = {'same_diagram':True, 'target_occurrences':goal, 'adjacent_swaps':cert,
              'raw_3_path':cert is not None}
    if cert is not None:
        (r,clique),_ = degree_bounds(start,goal,set())
        result.update(reversed_clique=clique, failing_higher_degrees=list(range(4,r+2)),
                      all_raw_from=max(4,r+2))
    return result


def checks():
    rules = {'split':('x','xx'),'join':('xx','x'),'loop':('x','x'),
             'wide':('xx','xxx')}
    charts = pairs = legal_swaps = cubes = 0
    for n,history in [
        (4,[('split',0),('loop',1),('join',2),('loop',3),('join',0)]),
        (5,[('loop',4),('split',2),('loop',0),('join',3),('loop',2)]),
        (5,[('split',4),('loop',3),('wide',1),('split',0),('join',6)]),
        (4,[('loop',3),('loop',2),('loop',1),('loop',0)]),
        (3,[('split',1),('loop',3),('join',1),('loop',0),('join',0)])]:
        events,_,expected = read('x'*n,rules,history)
        ports = tuple((-1,i) for i in range(n))
        written = dict(traces(ports,events))
        adjacency = {w:set() for w in written}
        orientations = set()
        for w,h in written.items():
            assert read('x'*n,rules,h,events)[1:] == (w,expected)
            for j,(a,b) in enumerate(zip(w,w[1:])):
                v = w[:j]+(b,a)+w[j+2:]
                if v in written:
                    # Directly read the two *independent* input positions before
                    # each event. Positive exchange requires right-before-left.
                    if h[j][1] > written[v][j][1]:
                        adjacency[w].add(v)
                        orientations.add((a,b))
                        legal_swaps += 1
        assert all((b,a) not in orientations for a,b in orientations)
        cuts = {frozenset():ports}
        inversions = {}
        for w in written:
            inversions[w] = {(a,b) for a,b in combinations(w,2) if a>b}
            live,cut = ports,frozenset()
            for e in w:
                _,live = execute(live,events[e])
                cut = cut|{e}
                assert cuts.setdefault(cut,live) == live
        for w in written:
            seen,todo = {w},[w]
            while todo:
                for v in adjacency[todo.pop()]-seen:
                    seen.add(v)
                    todo.append(v)
            for v in written:
                cert = positive_sort(ports,events,w,v)
                assert (cert is not None) == (v in seen)
                if cert is not None:
                    p = w
                    for j in cert:
                        q = p[:j]+(p[j+1],p[j])+p[j+2:]
                        assert q in adjacency[p]
                        p = q
                    assert p == v
                    changed = inversions[w]^inversions[v]
                    between = [t for t in written if (inversions[t]^inversions[w]) <= changed]
                    next_at = {}
                    for t in between:
                        for k,e in enumerate(t):
                            next_at.setdefault(frozenset(t[:k]),set()).add(e)
                    for cut,enabled in next_at.items():
                        spatial = sorted(enabled,key=lambda e: execute(cuts[cut],events[e])[0])
                        assert spatial == sorted(enabled,key=v.index)
                        for size in range(2,len(spatial)+1):
                            for atom in combinations(spatial,size):
                                for e in atom:
                                    _,after = execute(cuts[cut],events[e])
                                    assert after == cuts[cut|{e}]
                                    rest = [execute(after,events[f])[0] for f in atom if f != e]
                                    assert rest == sorted(rest)
                                cubes += 1
                pairs += 1
        charts += 1
    unrelated = {'initial':'xx','rules':rules,'source':[('split',0),('join',0)],
                 'target':[('split',1),('join',1)]}
    assert not solve(unrelated)['same_diagram']
    print(f'{charts} planar diagrams, {pairs} temporal history comparisons, '
          f'{legal_swaps} literal directed exchanges, {cubes} interval cube placements')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--chart',help='JSON with initial edges, rules and two lists of [name,offset]')
    args = parser.parse_args()
    if args.chart:
        with open(args.chart) as handle:
            print(json.dumps(solve(json.load(handle))))
    else:
        checks()
