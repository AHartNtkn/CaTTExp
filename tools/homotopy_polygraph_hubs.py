"""Realize strict dominance complexes by typed semaphore programs with a fixed hub set."""

from homotopy_polygraph_milestones import binary_pairs, orders
from homotopy_polygraph_two_resources import profiles


def dominance_program(rows, columns):
    """Compute the relation from actual binary visits, in a binary-legal serialization."""
    n, m, t = len(rows), len(columns), len(rows[0])
    source = range(m)
    hubs = range(m, m+t)
    sinks = range(m+t, m+t+n)
    actors = [i for group in (source,hubs,sinks) for i in group]
    main = 0
    holds = [[1] * (1+t*(m+n)) for _ in actors]
    words = [[] for _ in actors]
    queues = [[] for _ in hubs]
    next_link = 1
    for j in source:
        holds[j][main] = 0
        words[j].append(('P',main))
        for k,h in enumerate(hubs):
            link = next_link
            next_link += 1
            holds[h][link] = 0
            words[j].append(('V',link))
            queues[k].append((columns[j][k],0,link))
    for i,s in enumerate(sinks):
        for k,h in enumerate(hubs):
            link = next_link
            next_link += 1
            holds[s][link] = 0
            queues[k].append((rows[i][k],1,link))
            words[s].append(('P',link))
        words[s].append(('V',main))
    for h,queue in zip(hubs,queues):
        words[h] = [('V' if send else 'P',link) for _,send,link in sorted(queue)]
    states = profiles(words,holds)
    # Only a sender and its recipient ever change their link. Check that every
    # acquisition in the serialization finds the sender's positive visit finished.
    current = [row[:] for row in holds]
    free = [sum(row[r] == 0 for row in current) for r in range(next_link)]
    serial = []
    for a,w in enumerate(words):
        for op,r in w:
            old = current[a][r]
            current[a][r] += 1 if op == 'P' else -1
            assert current[a][r] >= 0
            free[r] += int(current[a][r] == 0) - int(old == 0)
            assert r == main or free[r] > 0
            serial.append(a)
    H = orders(words,states,serial,binary_pairs(states, range(1,next_link)))
    result = [frozenset(i for i,s in enumerate(sinks) if (s,t) not in H[j,0]) for j in source]
    assert result == [frozenset(i for i,row in enumerate(rows)
                                if all(x < y for x,y in zip(row,col))) for col in columns]
    return result


def circles(count):
    # Translate copies of the coordinate unit vectors along (1,-1,0).
    rows, edges = [], []
    for i in range(count):
        start = len(rows)
        for k in range(3):
            rows.append(tuple(4*i*d + int(a == k) for a,d in enumerate((1,-1,0))))
        edges.extend([(start,start+1),(start+1,start+2),(start+2,start)])
        if i:
            edges.append((start-3,start+1))
    cols = [tuple(1+max(a,b) for a,b in zip(rows[i],rows[j])) for i,j in edges]
    return rows,cols,edges


def check():
    for size in (1,2,3,5,8):
        rows,cols,edges = circles(size)
        faces = dominance_program(rows,cols)
        assert faces == list(map(frozenset,edges))
        assert len(set(faces)) - len(rows) + 1 == size
        print(f'Three hubs: {len(rows)} vertices, {len(faces)} edges, {size} circles.')
    for t in range(2,7):
        rows = [tuple(int(a==i) for a in range(t)) for i in range(t)]
        cols = [tuple(1 if a==j else 2 for a in range(t)) for j in range(t)]
        assert dominance_program(rows,cols) == [frozenset(range(t))-{j} for j in range(t)]
        print(f'{t} hubs: boundary of the {t-1}-simplex.')


if __name__ == '__main__':
    check()
