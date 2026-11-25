"""Generate and audit the one-root circuit and two-root Petri return reductions."""
from argparse import ArgumentParser
from itertools import permutations, product
import json
from pathlib import Path

from semistrict_surface_closed_returns import Templates, decide, shell_net, unary_markings
from semistrict_surface_serial_gate_tracks import read_track


def circuit_ports(nodes):
    if not nodes:
        raise ValueError('the last circuit node must be the output')
    gates,rules = {},{}
    def state(i,side):
        name = side+str(i)
        gates[name] = ['y','','']
        return [(0,name)]
    def lens(name,body,outer=False):
        x,path = ('x','fg') if outer else ('y','hh')
        start,end = 'B'+name,'D'+name
        gates[start] = [x,'',path]
        gates[end] = [x,path,'']
        return [(0,start)]+[(p+1,g) for p,g in body]+[(0,end)]
    for i,node in enumerate(nodes):
        a,b = state(i,'s'),state(i,'t')
        if type(node) is bool:
            if node:
                rules[f'input{i}'] = ['y',a,b]
            continue
        op,j,k = node
        if op not in ('and','or') or not (0<=j<i and 0<=k<i):
            raise ValueError('expected a binary topologically ordered monotone circuit')
        for n,child in enumerate([j,k]):
            wrapper = f'{i}_{n}'
            before = lens(wrapper,state(child,'s'))
            after = lens(wrapper,state(child,'t'))
            if op=='or' or n==0:
                rules['call'+wrapper] = ['y',a,before]
            else:
                rules['next'+wrapper] = ['y',prev,before]
            if op=='or' or n==1:
                rules['done'+wrapper] = ['y',after,b]
            prev = after
    last = len(nodes)-1
    rules['open'] = ['x',[],lens('outer',state(last,'s'),True)]
    rules['close'] = ['x',lens('outer',state(last,'t'),True),[]]
    return dict(vertex='x',edges={'f':['x','y'],'g':['y','x'],'h':['y','y']},gates=gates,rules=rules)


def binary_ports(net):
    d = shell_net(dict(net,transitions=[]),1)
    d['edges'] = {'f':['x','y'],'g':['y','x']}
    for name in d['gates']:
        d['gates'][name] = ['y','','']
    d['gates'].update(B=['x','','fg'],D=['x','fg',''])
    for i,(before,after) in enumerate(net['transitions']):
        for side in (before,after):
            if len(side)!=len(net['source']) or any(type(n) is not int or n<0 for n in side):
                raise ValueError('invalid transition')
        ops = [(j,True) for j,n in enumerate(before) for _ in range(n)]
        ops += [(j,False) for j,n in enumerate(after) for _ in range(n)]
        token = 'control'
        for k,(j,take) in enumerate(ops):
            following = f'control{i}_{k}' if k+1<len(ops) else 'control'
            d['gates'][following] = ['y','','']
            data = [(0,f'p{j}')]
            a = [(0,token)]+(data if take else [])
            b = [(0,following)]+([] if take else data)
            d['rules'][f't{i}_{k}'] = ['y',a,b]
            token = following
        # A transition between zero vectors has no effect on reachability.
    return d


def replay_calls(d):
    # Deterministic circuits (AND only) have one possible next instruction
    # inside their first lens. Replay the real written diagrams at their slots.
    gates = dict(d['gates'],sx=['x','',''],sy=['y','',''])
    charts,live = [],[]
    def take(rule,j,offset):
        x,a,b = rule
        assert live[j:j+len(a)]==[(offset+p,g) for p,g in a]
        charts.append(dict(diagram=live[:j]+[(offset,'s'+x)]+live[j+len(a):],
                           slot=j,input=a,output=b,loop=[]))
        live[j:j+len(a)] = [(offset+p,g) for p,g in b]
    take(d['rules']['open'],0,0)
    while live:
        possible = []
        for name,rule in d['rules'].items():
            if name=='open':
                continue
            left = rule[1]
            for j,(offset,g) in enumerate(live):
                if live[j:j+len(left)]==[(offset+p,h) for p,h in left]:
                    possible.append((rule,j,offset))
        if not possible:
            return None
        event, = possible
        take(*event)
    track = dict(d,gates=gates,path='',charts=charts,seams=[[] for _ in charts[1:]])
    return read_track(track)['sites']


def audit():
    # All two-colour unary rule sets, with small explicit endpoint lists.
    moves = [((),(0,)),((),(1,)),((0,),()),((1,),()),((0,),(1,)),((1,),(0,))]
    ends = [(),(0,),(1,),(0,0),(0,1),(1,1)]
    for mask in range(1<<len(moves)):
        enabled = [m for i,m in enumerate(moves) if mask & (1<<i)]
        match = unary_markings(enabled)
        for source in ends:
            reached = {source}
            todo = [source]
            while todo:
                state = todo.pop()
                for a,b in enabled:
                    if a and a[0] not in state:
                        continue
                    row = list(state)
                    if a:
                        row.remove(a[0])
                    dest = tuple(sorted(row+list(b)))
                    if len(dest)<=4 and dest not in reached:
                        reached.add(dest)
                        todo.append(dest)
            assert all(match(source,t)==(t in reached) for t in ends)
    # Five independent unary gates belong to the same core. The sorted
    # core and its face containing a point must be stable under each order.
    core = Templates(dict(edges={'f':['x','x']},gates={
        'B':['x','','fffff'],'D':['x','fffff',''],'u':['x','f','f'],'p':['x','','']}))
    for gap in (1,2):
        shapes = set()
        marked = set()
        for perm in permutations(range(5)):
            row = [(0,'B')]+[(j,'u') for j in perm]+[(gap,'p'),(0,'D')]
            shapes.add(core.forest('x',row))
            marked.add(core.forest('x',row,1+perm.index(2)))
        assert len(shapes)==len(marked)==1 and shapes!=marked
        if gap==1:
            first = shapes
        else:
            assert shapes!=first
    for a,b,op in product((False,True),(False,True),('and','or')):
        answer = (a and b) if op=='and' else (a or b)
        for dependent in (False,True):
            assert decide(circuit_ports([a,b,[op,0,1]]),dependent)['positive_return']==answer
    c = [True]+[['and',j,j] for j in range(4)]
    assert replay_calls(circuit_ports(c))==63
    assert replay_calls(circuit_ports([False,*c[1:]])) is None
    for dependent in (False,True):
        assert decide(circuit_ports(c),dependent)['positive_return']
    # A lens with two siblings requires two independent internal changes.
    d = circuit_ports([True])
    for name,side in [('open',2),('close',1)]:
        row = d['rules'][name][side]
        row.insert(1,row[1])
    assert decide(d)['positive_return'] and not decide(d,True)['positive_return']
    for a,b in [(1,1),(2,0),(0,2)]:
        d = binary_ports(dict(source=[1,1],target=[a,b],transitions=[([1,1],[2,0])]))
        assert all(len(left)<=2 and len(right)<=2 for name,(_,left,right) in d['rules'].items()
                   if name not in ('open','close'))
        # The intermediate controller cannot accept or start a second transition.
        for dependent in (False,True):
            assert decide(d,dependent)['positive_return']==(b!=2)
    print('2304 unary marking comparisons, 16 circuit truth-table decisions, and a 63-use dependent replay passed.')
    print('All 120 connected-core orders agree at each of two distinct face addresses, with and without a gate mark.')
    print('The two-child return distinguishes the dependence condition. Six two-root controller queries passed.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--circuit',type=Path,help='JSON list of booleans and [and/or, left, right] nodes')
    group.add_argument('--net',type=Path,help='marking reachability instance with explicit arc multiplicities')
    args = parser.parse_args()
    if args.circuit:
        print(json.dumps(circuit_ports(json.loads(args.circuit.read_text())),indent=2))
    elif args.net:
        print(json.dumps(binary_ports(json.loads(args.net.read_text())),indent=2))
    else:
        audit()
