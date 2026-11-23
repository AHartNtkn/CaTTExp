"""Decide the three-scalar Gray cube return on one loop with one nonempty gap (islpy)."""
import argparse
from itertools import product

import islpy as isl
from homotopy_polygraph_causal_routes import repeat
from semistrict_surface_three_axis_paths import Chart, check_chart


def traverse(state, letters):
    """Execute adjacent crossings on temporal scalar positions along the fixed edge path."""
    for pos in letters:
        i = pos - 1
        if i < 0 or i + 1 >= len(state) or state[i] < state[i + 1]:
            raise ValueError(f'crossing {pos} is undefined at {state}')
        state = state[:i] + (state[i + 1], state[i]) + state[i + 2:]
    return state


def contexts(width, graph, attachments):
    """Whisker a declared step by stationary temporal events and spatial edge paths."""
    anchored = set()
    for span, slots, lhs, rhs in attachments:
        if span < 0 or any(p < 0 or p > span for p in slots):
            raise ValueError('scalar slot outside the attaching edge path')
        if traverse(slots, lhs) != traverse(slots, rhs):
            raise ValueError('nonparallel attaching faces')
        for state in graph:
            for offset in range(width - span + 1):
                positions = tuple(offset + p for p in slots)
                for i in range(len(state) - len(slots) + 1):
                    if state[i:i+len(slots)] == positions:
                        anchored.add((state, tuple(x + i for x in lhs), tuple(x + i for x in rhs)))
    return anchored


def effects(state, path):
    left = right = 0
    for pos in path:
        dest = traverse(state, (pos,))
        if dest == state:
            if state == tuple(sorted(state, reverse=True)):
                left += 1
            elif state == tuple(sorted(state)):
                right += 1
            else:
                raise ValueError('loop outside an endpoint')
        state = dest
    return left, right


def moves(anchored):
    return {(effects(state, lhs), effects(state, rhs)) for state, lhs, rhs in anchored}


def controlled_reachable(start, goal, rules):
    """Reachability for guarded two-counter steps between finitely many controls."""
    def singleton(point):
        x, y = point
        return isl.Set(f'{{ [x,y] : x={x} and y={y} }}')

    steps = {(s, t, c-a, d-b, a, b) for (s, (a, b)), (t, (c, d)) in rules}
    walks = steps.copy()
    pumps = set()
    empty = isl.Set('{ [x,y] : false }')
    seen = {q: empty for q in {start[0], goal[0]} | {p for s, t, *_ in steps for p in (s, t)}}
    seen[start[0]] = singleton(start[1])
    target = singleton(goal[1])
    while seen[goal[0]].intersect(target).is_empty():
        previous = seen.copy()
        for s, t, dx, dy, a, b in steps:
            step = isl.Map(f'{{ [x,y] -> [u,v] : x>={a} and y>={b} and '
                           f'u=x+({dx}) and v=y+({dy}) }}')
            seen[t] = seen[t].union(seen[s].apply(step)).coalesce()
        pumps.update((s, dx, dy, a, b) for s, t, dx, dy, a, b in walks if s == t and (dx or dy))
        for s, dx, dy, a, b in pumps:
            seen[s] = seen[s].union(seen[s].apply(repeat(dx, dy, a, b))).coalesce()
        if all(previous[q].is_equal(seen[q]) for q in seen):
            return False
        walks = {(s, t, x+u, y+v, max(a, c-x), max(b, d-y))
                 for s, m, x, y, a, b in walks for n, t, u, v, c, d in steps if m == n}
    return True


def reachable(start, goal, rules):
    return controlled_reachable((0, start), (0, goal), {((0, l), (0, r)) for l, r in rules})


def instance(gaps, attachments):
    if len(gaps) != 2 or min(gaps) != 0 or max(gaps) <= 0:
        raise ValueError('exactly one gap must be nonempty')
    chart = Chart((('a', '', ''),)*3, tuple('f'*n for n in gaps))
    histories, count = check_chart(chart)
    assert count is None
    states = {tuple(p for p, _ in h) for h in histories}
    first = max(states)
    forward = (first, (1, 2, 1), (2, 1, 2))
    anchored = contexts(sum(gaps), states, attachments) | {forward}
    end, start = (effects(first, word) for word in forward[1:])
    return start, end, anchored


def check():
    comparisons = 0
    decisions = 0
    for gaps in ((0, 1), (2, 0)):
        width = sum(gaps)
        start, goal, _ = instance(gaps, [])
        desc = (width, gaps[0], 0)
        # Check actual word replacements at all contextual occurrences against
        # counter guards, including proper temporal and spatial whiskers.
        inputs = []
        for span in range(width+1):
            for size in range(4):
                for slots in product(range(span+1), repeat=size):
                    paths = [()]
                    for n in range(1, 4):
                        for w in product(range(1, size), repeat=n):
                            try:
                                traverse(slots, w)
                                paths.append(w)
                            except ValueError:
                                continue
                    inputs.extend((span, slots, l, r) for l in paths for r in paths
                                  if l != r and traverse(slots, l) == traverse(slots, r))
        _, _, anchored = instance(gaps, inputs)
        def word(i, j):
            first, second = ((1, 2) if gaps[0] == 0 else (2, 1))
            return (second,)*i + (first, second) + (first,)*j

        for state, l, r in anchored:
            (a,b), (c,d) = effects(state, l), effects(state, r)
            for i,j in product(range(5), repeat=2):
                old = word(i,j)
                actual = {old[:k] + r + old[k+len(l):] for k in range(len(old)-len(l)+1)
                          if traverse(desc, old[:k]) == state and old[k:k+len(l)] == l}
                assert actual == ({word(i-a+c, j-b+d)} if i >= a and j >= b else set())
                comparisons += 1

        for a,b,c in product(range(3), repeat=3):
            # A length-preserving system is independently finite from any fixed total.
            if c > a+b:
                continue
            rules = {(goal, start), ((a,b), (c,a+b-c))}
            for initial, final in [(start, goal), ((0,3),(2,1)), ((2,1),(0,3))]:
                found = {initial}
                while True:
                    extra = {(i-u+x,j-v+y) for i,j in found for (u,v),(x,y) in rules
                             if i>=u and j>=v} - found
                    if not extra:
                        break
                    found |= extra
                assert reachable(initial, final, rules) == (final in found)
                decisions += 1

        # Mixed changes with genuinely unbounded positive and negative instances.
        scale = lambda p,n: tuple(v*n for v in p)
        for n in (9, 30):
            rules = {(goal, start), (start, scale(start, 2)), (scale(start,n), goal)}
            assert reachable(start, goal, rules)
            assert not reachable(start, goal, {(goal,start), (start,scale(start,2))})
    print(f'{comparisons:,} contextual rewrites and {decisions} finite reachability decisions agreed.')
    print('Unbounded growth and repairs with thresholds 9 and 30 checked on both gap placements.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gaps', nargs=2, type=int)
    parser.add_argument('--attach', action='append', default=[], metavar='SPAN:SLOTS:LHS:RHS',
                        help='comma-separated scalar positions and two adjacent-crossing words')
    args = parser.parse_args()
    if args.gaps is None:
        check()
        return
    inputs = []
    try:
        for item in args.attach:
            span, slots, lhs, rhs = item.split(':')
            inputs.append((int(span), tuple(map(int,slots.split(','))) if slots else (),
                           tuple(map(int,lhs)), tuple(map(int,rhs))))
        start, end, anchored = instance(args.gaps, inputs)
        print('raw return exists' if reachable(start, end, moves(anchored)) else 'raw return absent')
    except ValueError as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
