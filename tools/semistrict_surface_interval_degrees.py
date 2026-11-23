"""Degree bounds and contextual cube/prism reverse certificates for globular Gray intervals."""
import argparse
from itertools import combinations, permutations, product


def degree_bounds(start, end, updated):
    """Return weighted clique width and a largest witness with two consecutive bare axes.

    Strands have distinct positional names. The input shuffles are assumed to
    admit a native reading. Updated is the set of slots with nonempty unary paths.
    """
    if len(set(start)) != len(start) or set(start) != set(end) or len(start) != len(end):
        raise ValueError('the two temporal lists must name the same distinct strands')
    if not set(updated) <= set(start):
        raise ValueError('update slots must occur in the interval')
    ranks = {x:i for i,x in enumerate(end)}
    best = (0, ())
    mixed = (0, ())
    # Flags are 0 = before the forced pair, 1 = its first axis, 2 = after it.
    # Cap size at three so an isolated square cannot count as a higher witness.
    states = []
    for j, x in enumerate(start):
        entries = {(0,1):(1+(x in updated), (x,)), (1,1):(1,(x,))}
        for i in range(j):
            if ranks[start[i]] <= ranks[x]:
                continue
            for (flag, size),(score, chain) in states[i].items():
                options = {0:((0,1+(x in updated)),(1,1)),
                           1:((2,1),), 2:((2,1+(x in updated)),)}[flag]
                for next_flag, add in options:
                    key = next_flag, min(3,size+1)
                    if key not in entries or entries[key][0] < score+add:
                        entries[key] = score+add, chain+(x,)
        states.append(entries)
        for (flag,size), result in entries.items():
            if flag == 0 and result[0] > best[0]:
                best = result
            if flag == 2 and size == 3 and result[0] > mixed[0]:
                mixed = result
    return best, mixed


def isolate(start, end, marks):
    rank = {x:i for i,x in enumerate(end)}
    if len(marks) < 2 or any(rank[a] <= rank[b] for a,b in zip(marks,marks[1:])):
        raise ValueError('the marked sequence must reverse')
    i, j = start.index(marks[0]), start.index(marks[-1])
    left, right, seen = [], [], []
    for x in start[i:j+1]:
        if x in marks:
            seen.append(x)
        elif rank[x] < rank[seen[-1]]:
            left.append(x)
        else:
            right.append(x)
    if tuple(seen) != marks:
        raise ValueError('marks must be in input order')
    block = start[:i]+tuple(left)+marks+tuple(right)+start[j+1:]
    after = start[:i]+tuple(left)+marks[::-1]+tuple(right)+start[j+1:]
    return block, after


def reaches(order, target, rank, forbidden):
    """Replay explicit sorting, checking native direction and the protected clique."""
    order = list(order)
    for i,x in enumerate(target):
        j = order.index(x)
        while j > i:
            a = order[j-1]
            if rank[a] <= rank[x] or (a in forbidden and x in forbidden):
                return False
            order[j-1],order[j] = x,a
            j -= 1
    return tuple(order) == target


def checks():
    masks = marks = 0
    for n in range(1,7):
        end = tuple(range(n))
        rank = {x:x for x in end}
        updates = list(product((0,1), repeat=n)) if n<=5 else [(0,)*n,(1,)*n]
        for start in permutations(end):
            cliques = []
            for r in range(1,n+1):
                for clique in combinations(start,r):
                    if any(a < b for a,b in zip(clique,clique[1:])):
                        continue
                    cliques.append(clique)
                    if r < 2:
                        continue
                    before,after = isolate(start,end,clique)
                    assert reaches(start,before,rank,clique) and reaches(after,end,rank,clique)
                    marks += 1
            for bits in updates:
                active = {x for x,b in enumerate(bits) if b}
                best, mixed = degree_bounds(start,end,active)
                weighted = lambda chain: sum(1+(x in active) for x in chain)
                expected = max(weighted(chain) for chain in cliques)
                paired = max((weighted(chain)-(a in active)-(b in active)
                              for chain in cliques if len(chain)>=3
                              for a,b in zip(chain,chain[1:])), default=0)
                assert (best[0],mixed[0]) == (expected,paired)
                masks += 1
    print(f'{masks} weighted degree bounds against subset enumeration, '
          f'{marks} protected clique isolations replayed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start')
    parser.add_argument('--end')
    parser.add_argument('--updated', default='')
    args = parser.parse_args()
    if args.start:
        def seq(s):
            return tuple(map(int,s.split(','))) if s else ()
        best,mixed = degree_bounds(seq(args.start),seq(args.end),set(seq(args.updated)))
        print('all old types inhabited from degree', best[0]+2)
        print('highest certified failing degree', mixed[0]+1 if mixed[0] else None,
              'on reversed strands', mixed[1])
    else:
        checks()
