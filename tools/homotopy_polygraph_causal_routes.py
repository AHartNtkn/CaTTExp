"""Decide the three-witness semaphore class (requires islpy)."""

from collections import defaultdict
from functools import cache
from itertools import combinations, combinations_with_replacement, product

import islpy as isl

from homotopy_polygraph_parking import acquisition_before_release
from homotopy_polygraph_milestones import binary_pairs, compact, orders
from homotopy_polygraph_two_resources import profiles
from homotopy_polygraph_transfer_complexity import compile_cnf, control
from homotopy_polygraph_transfer_graph import transfer_options


@cache
def action(dx, dy):
    return isl.Map(f'{{ [x,y] -> [u,v] : u=x+({dx}) and v=y+({dy}) and u>=0 and v>=0 }}')


@cache
def repeat(dx, dy, xneed, yneed):
    return isl.Map(f'''{{ [x,y] -> [u,v] : exists k : k >= 1 and
                    u=x+{dx}k and v=y+{dy}k and x>={xneed} and y>={yneed}
                    and u-({dx})>={xneed} and v-({dy})>={yneed} }}''')


def can_relay(graph, left, right):
    """Start at P(left) from zero and finish at V(right) to zero."""
    assert left != right
    starts = {t for _, op, t in graph if op == ('P', left)}
    ends = {s for s, op, _ in graph if op == ('V', right)}
    if not starts or not ends:
        return False
    if starts & ends:
        return True
    states = {v for s, _, t in graph for v in (s, t)}
    deltas = {('P',left):(1,0), ('V',left):(-1,0), ('P',right):(0,1), ('V',right):(0,-1)}
    forward = defaultdict(set)
    for s, op, t in graph:
        forward[s].add((t, *deltas.get(op, (0,0))))
    reached = {s: isl.Set('{ [x,y] : x=1 and y>=0 }') if s in starts else isl.Set('{ [x,y] : false }')
               for s in states}
    target = isl.Set('{ [x,y] : x>=0 and y=1 }')
    walks = {(s,s,0,0,0,0) for s in states}
    pumps = set()
    while True:
        if any(not reached[s].intersect(target).is_empty() for s in ends):
            return True
        previous = reached.copy()

        def propagate(s, t, relation):
            reached[t] = reached[t].union(reached[s].apply(relation)).coalesce()

        for s in states:
            for t, dx, dy in forward[s]:
                propagate(s, t, action(dx, dy))
        for s, dx, dy, a, b in pumps:
            propagate(s, s, repeat(dx, dy, a, b))
        if all(reached[s].is_equal(previous[s]) for s in states):
            return False
        # Add summaries of all closed walks of the next length. The global
        # flattening theorem for 2-VASS guarantees stabilization.
        walks = {(s,t,x+dx,y+dy,max(a,-x-dx),max(b,-y-dy))
                 for s,u,x,y,a,b in walks for t,dx,dy in forward[u]}
        pumps.update((s,x,y,a,b) for s,t,x,y,a,b in walks if s == t and (x or y))


def circle_routes(controls, main):
    users = defaultdict(set)
    for i, graph in enumerate(controls):
        if any(acquisition_before_release(graph, a, b) for a,b in
               [(('P',main),('V',main)), (('V',main),('P',main))]):
            raise ValueError("main resource is not monotone")
        for _, op, _ in graph:
            if op is not None and op[1] != main:
                users[op[1]].add(i)
    if any(len(us) > 2 for us in users.values()):
        raise ValueError("auxiliary resource has more than two users")

    @cache
    def relay(i, a, b):
        return can_relay(controls[i], a, b)

    def routes(path, incoming):
        i = path[-1]
        if incoming != main and relay(i, incoming, main):
            yield path
        for r, actors in users.items():
            if r != incoming and i in actors and len(actors) == 2 and relay(i,incoming,r):
                j, = actors - {i}
                if j not in path:
                    yield from routes((*path,j), r)

    all_routes = [p for i in range(len(controls)) for p in routes((i,), main)]
    for a,b,c in combinations(all_routes, 3):
        if len(set(a+b+c)) == len(a+b+c):
            return a,b,c
    return None



def homotopical(controls, main):
    numbers = [sum(any(op == (sign,main) for _,op,_ in g) for g in controls)
               for sign in ('P','V')]
    if min(numbers) > 3:
        raise ValueError("expected at most three acquisition or release users")
    return circle_routes(controls, main) is None


def route_cnf(nvars, clauses):
    # Split each coloured arc into two private directed links. A colour process
    # has separate branches for its occurrences, so it cannot change ports.
    coloured = compile_cnf(nvars, clauses)
    (target, start), = transfer_options(coloured[-1])
    incoming = defaultdict(list)
    outgoing = defaultdict(list)
    main = 'main'
    incoming[start].append(main)
    outgoing[target].append(main)
    actors = []
    for index, graph in enumerate(coloured[:-3]):
        ports = []
        for j, (v,w) in enumerate(sorted(transfer_options(graph))):
            before, after = (index,j,'in'), (index,j,'out')
            outgoing[v].append(before)
            incoming[w].append(after)
            ports.append((before,after))
        actors.append(control(ports))
    for v in sorted(incoming.keys() | outgoing.keys()):
        actors.append(control(product(incoming[v],outgoing[v])))
    for i in (0,1):
        actors.extend([control([(main,i)]),control([(i,main)])])
    return actors


def word(ops):
    return [(i, op, i+1) for i, op in enumerate(ops)]


def check():
    # A finite-state test alone would accept the first relay. The second and
    # third failures have infinite reachable counter sets.
    start, end = ('P',0), ('V',1)
    assert not can_relay(word([start, ('V',0), ('V',0), end]), 0, 1)
    assert not can_relay([(0,start,1),(1,('P',1),1),(1,('P',1),2),
                          (2,('P',1),3),(3,end,4)], 0, 1)
    assert not can_relay([(0,start,1),(1,('P',0),1),(1,('P',1),2),
                          (2,('P',1),3),(3,end,4)], 0, 1)
    assert can_relay([(0,start,1),(1,('P',0),1),(1,('V',0),2),
                      (2,('V',0),3),(3,end,4)], 0, 1)

    # Distinguish a genuine transfer of the last unit from one which returns
    # the output count to an interior (nonzero) height.
    def literal(segment):
        for i, a in enumerate(segment):
            if a != start:
                continue
            for j in range(i+1, len(segment)):
                if segment[j] != end:
                    continue
                x = y = 0
                balances = []
                for op, r in segment[i:j+1]:
                    if r == 0:
                        x += 1 if op == 'P' else -1
                    else:
                        y += 1 if op == 'P' else -1
                    balances.append((x,y))
                if min(p for p,_ in balances) >= 0 and y == min(0, *(q for _,q in balances)):
                    return True
        return False
    alphabet = (start, end, ('P',1), ('V',0))
    for seq in product(alphabet, repeat=5):
        assert can_relay(word(seq),0,1) == literal(seq), seq
    print('1,024 literal two-counter words and four relay controls agree.')

    g = 'main'
    paths = [[word([('P',g), ('V',(i,0))]),
              word([('P',(i,0)), ('V',(i,1))]),
              word([('P',(i,1)), ('V',g)])] for i in range(3)]
    controls = sum(paths, [])
    witness = circle_routes(controls, g)
    assert witness == ((0,1,2), (3,4,5), (6,7,8))
    print('Disjoint circle routes:', witness)
    # Replay the binary order of the certificate independently of route search.
    names = [g] + [(i,j) for i in range(3) for j in range(2)]
    programs = [[(op, names.index(r)) for _,(op,r),_ in graph] for graph in controls]
    initial = [tuple(0 if ('P',r) in w else 1 for r in range(len(names))) for w in programs]
    states = profiles(programs, initial)
    serial = [i for i, w in enumerate(programs) for _ in w]
    h = orders(programs, states, serial, binary_pairs(states, range(1,len(names))))
    assert compact(states, [0], h)[2] == (1,1)
    print('Six main milestones in the reconstructed binary order give circle homology.')
    controls[4] = word([('P',(1,0)), ('V',(1,0)), ('V',(1,0)), ('V',(1,1))])
    assert homotopical(controls,g)
    print('Three-arrival decision accepts after the middle relay cannot forward its input.')

    literals = (1,-1,2,-2)
    types = [(x,) for x in literals] + list(combinations(literals,2))
    checked = negative = 0
    for clauses in combinations_with_replacement(types,3):
        sat = any(all(any(bits[abs(x)-1] == (x>0) for x in c) for c in clauses)
                  for bits in product((False,True), repeat=2))
        assert homotopical(route_cnf(2,clauses),g) == (not sat), clauses
        checked += 1
        negative += not sat
    print(f'{checked} SAT encodings agree with truth assignments ({negative} unsatisfiable).')


if __name__ == '__main__':
    check()
