"""Enumerate actual exchanges between insertions of DM at visits to A."""

from itertools import combinations
from math import comb

from fibration_factor_search import Rule, Stage


def history(initial, length):
    return ''.join('D' if (initial + i) % 2 == 0 else 'M' for i in range(length))


def visits(initial, path):
    return [i for i in range(len(path) + 1) if (initial + i) % 2 == 0]


def insertions(initial, n, added):
    start = history(initial, n)

    def extend(path, positions, left):
        if left == 0:
            yield positions
        else:
            for i in visits(initial, path):
                yield from extend(path[:i]+'DM'+path[i:], positions+(i,), left-1)

    return list(extend(start, (), added))


def signature(initial, n, positions):
    # Follow the old 3-steps, keeping the two end fragments as well as complete DM's.
    retained = list(range(n))
    for i in positions:
        retained[i:i] = [None, None]
    return tuple(i for i, label in enumerate(retained) if label is not None)


def check():
    # The marker for a four-change has two-poles A,A and word poles empty,tg.
    # Its 2-marker X can occupy the whole spatial diagram only once.
    stage = Stage({'t': ('x','x'), 'g': ('x','x')},
                  {a: Rule('x', s, t) for a,s,t in (
                      ('u','','t'),('h','','g'),('c','gt','tg'),
                      ('D','t','tg'),('M','g','tg'),('X','','tg'))})
    unary, _ = stage.quotient(stage.backwards('x','','tg',{'X','D','M'},1))
    assert [p for group in unary for p in group if any(a == 'X' for a,_ in p)] == [(('X',0),)]
    assert not list(stage.backwards('x','','tg',{'X','D','M'},2))

    # Time-coordinate of the actual four-rule: insert two 3-steps DM with empty source.
    # Stage.exchanges includes both orders at a shared empty gap. Restrict sites to A.
    time = Stage({a: ('x','x') for a in 'DM'}, {'Z': Rule('x','','DM')})
    cases = writings = classes = 0
    for initial in (0,1):
        for n in range(8):
            places = visits(initial, history(initial,n))
            for k in range(5):
                paths = insertions(initial, n, k)
                steps = [tuple(('Z', i) for i in p) for p in paths]
                quotient, _ = time.quotient(steps)
                images = []
                for group in quotient:
                    sigs = {signature(initial, n, [i for _,i in p]) for p in group}
                    assert len(sigs) == 1
                    images.append(sigs.pop())
                assert len(images) == len(set(images))
                if places:
                    r = len(places)-1
                    expected = set()
                    for indices in combinations(range(r+k), r):
                        positions = list(range(places[0]))
                        for i in indices:
                            positions.extend((places[0]+2*i, places[0]+2*i+1))
                        positions.extend(range(places[-1]+2*k,n+2*k))
                        expected.add(tuple(positions))
                    assert set(images) == expected and len(images) == comb(r+k,r)
                else:
                    assert len(images) == int(k == 0)
                cases += 1
                writings += len(paths)
                classes += len(images)
    print(f'{cases} parallel 3-boundary queries, {writings} four-writings, '
          f'{classes} exchange classes exactly identified by the surviving positions.')


if __name__ == '__main__':
    check()
