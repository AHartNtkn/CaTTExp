"""Decide existence of a gate-dependent return on a scalar-rule computad.

Use the point_gates/rules format of semistrict_surface_empty_returns. --net emits
the equivalent marking-reachability problem. --encode-net gives the converse
reduction. --witness replays a positive return beside a stationary gate.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_empty_returns import movie
from semistrict_surface_one_test_reachability import ordinary
from semistrict_surface_positive_labels import reachable, succ


def compile_return(data):
    places = data['point_gates']
    if len(set(places)) != len(places):
        raise ValueError('expected distinct scalar colours')
    edges, labels = [], []
    for name, (inputs, outputs) in data['rules'].items():
        if any(c not in places for c in (*inputs,*outputs)):
            raise ValueError('unknown port colour')
        source = tuple(inputs.count(c) for c in places)
        target = tuple(outputs.count(c) for c in places)
        for a in sorted(set(inputs)) or [None]:
            for b in sorted(set(outputs)) or [None]:
                left = ('first',) if a is None else ('live',a)
                right = ('last',) if b is None else ('live',b)
                edges.append((left, right, tuple(x-int(c==a) for c,x in zip(places,source)),
                              tuple(x-int(c==b) for c,x in zip(places,target))))
                labels.append(name)
    zero = (0,)*len(places)
    return ordinary((('first',),zero), (('last',),zero), edges), labels


def encode_net(net):
    source, target = net['source'], net['target']
    places = [f'p{i}' for i in range(len(source))]
    def port(mark):
        if len(mark) != len(places) or any(type(x) is not int or x<0 for x in mark):
            raise ValueError('expected a nonnegative marking of the declared dimension')
        return ['control', *(p for p,n in zip(places,mark) for _ in range(n))]
    rules = dict(start=[[],port(source)], finish=[port(target),[]])
    for i,(a,b) in enumerate(net['transitions']):
        rules[f't{i}'] = [port(a),port(b)]
    return dict(point_gates=[*places,'control','spectator'], rules=rules)


def query(data, witness=False):
    net, labels = compile_return(data)
    ok = reachable(net)
    result = dict(dependent_return=ok)
    if not witness or not ok:
        return result
    start, target = tuple(net['source']), tuple(net['target'])
    queue, parent = deque([start]), {start:None}
    while target not in parent:
        state = queue.popleft()
        for name,(a,b) in zip(labels,net['transitions'],strict=True):
            nxt = succ(state,a,b)
            if nxt is not None and nxt not in parent:
                parent[nxt] = (state,name)
                queue.append(nxt)
    path = []
    while target != start:
        target, name = parent[target]
        path.append(name)
    path.reverse()
    charts = movie(data,path)
    # Every firing inserts its outputs at the front. The stable selection
    # of the next inputs takes a fresh occurrence of any shared colour first.
    # Add one independent spectator at the written ends of this test.
    raw = park_spectator(charts)
    return dict(result, firings=path, occurrence_movie=charts, meridian_track=raw['meridian_track'])


def park_spectator(charts):
    from semistrict_surface_closed_port_group import solve
    charts['gates']['spectator'] = ['x','','']
    for ch in charts['charts']:
        ch['diagram'].append((0,'spectator'))
    raw = solve(charts)
    assert raw['free_rank'] == 1
    return raw


def audit():
    from semistrict_surface_empty_returns import return_rules
    # These transitions preserve at most two total data tokens. Independent
    # enumeration retains the set of colours freshly output at the last step.
    changes = [('', 'ab'), ('', 'a'), ('a','b'), ('b','a'), ('ab','a'), ('a',''), ('ab','')]
    checked = 0
    for n in range(len(changes)+1):
        for pairs in combinations(changes,n):
            rules = {str(i):[list(a),list(b)] for i,(a,b) in enumerate(pairs)}
            data = dict(point_gates=['a','b'], rules=rules)
            queue = deque([('', None)])
            seen = set(queue)
            exists = False
            while queue and not exists:
                live, fresh = queue.popleft()
                for a,b in pairs:
                    if fresh is None and a or fresh is not None and not set(a).intersection(fresh):
                        continue
                    if any(live.count(c)<a.count(c) for c in a):
                        continue
                    remaining = list(live)
                    for c in a:
                        remaining.remove(c)
                    new = (''.join(sorted(remaining+list(b))), b)
                    if not new[0]:
                        exists = True
                        break
                    if new not in seen:
                        seen.add(new)
                        queue.append(new)
            assert query(data)['dependent_return'] == exists
            checked += 1
    fork = dict(point_gates=['a','b'], rules={'birth':[[],['a','b']],
                                             'left':[['a'],[]], 'right':[['b'],[]]})
    assert return_rules(fork) and not query(fork)['dependent_return']
    assert query(dict(point_gates=[],rules={'site':[[],[]]}),True)['firings'] == ['site']
    backward = 0
    for start,end in product(range(4),repeat=2):
        net = dict(source=[start],target=[end],transitions=[([2],[1])])
        answer = query(encode_net(net),witness=True)
        assert answer['dependent_return'] == (start==end or 1<=end<start)
        backward += 1
    # The control colour is revisited, with another fresh colour available
    # at one step. Soundness requires consuming the exact final marking.
    net = dict(source=[1,0], target=[0,1], transitions=[([1,0],[0,1])])
    assert query(encode_net(net),True)['firings'] == ['start','t0','finish']
    from semistrict_surface_empty_tapes import run
    tape = run(dict(states=['s','t','h'],start='s',scanned='_',instructions=[
        ['s','_','t','a','R'], ['t','_','h','a','L']]),20)['movie']
    assert len(park_spectator(tape)['meridian_track']) == len(tape['charts'])
    print(f'{checked} finite fresh-output searches and {backward+1} reverse encodings agree; '
          'positive witnesses replay with a nonzero positioned meridian. The split death has only an unrestricted return. The wired accepting tape carries its meridian.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', nargs='?', type=Path)
    mode = cli.add_mutually_exclusive_group()
    mode.add_argument('--net', action='store_true')
    mode.add_argument('--encode-net', action='store_true')
    mode.add_argument('--witness', action='store_true')
    args = cli.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = encode_net(data) if args.encode_net else compile_return(data)[0] if args.net else query(data,args.witness)
        print(json.dumps(result,indent=2))
    else:
        audit()
