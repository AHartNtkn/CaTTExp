"""Count temporal positions using events that never vary in an outer 4-edge."""

from itertools import product

from interchange_path_grading import History, cross, i_faces, r_faces, word


def crossing(a, b):
    return cross(word(a), word(b))


def count(h, selected):
    return sum(e in selected for e in h.events)


def join_routes(a, b):
    block = cross(a.start, b.end)
    final_block = cross(a.end, b.end)
    source = b.pad(right=a.start).then(block).then(a.pad(right=b.end))
    middle = a.pad(left=b.start).then(b.pad(right=a.end)).then(final_block)
    target = b.pad(right=a.start).then(a.pad(left=b.end)).then(final_block)
    narrow = tuple(b.pad(right=a.start).then(h) for h in r_faces(a, b.end))
    correction = tuple(h.then(final_block) for h in i_faces(b, a))
    assert (source, target) == narrow and (middle, target) == correction
    return source, middle, target


def six_strands():
    # The right operand traverses two independent inner windows, with fc
    # in between. The left pair ab is the only moving event of the late r.
    early = i_faces(crossing('e', 'f'), crossing('c', 'd'))
    middle = crossing('c', 'f').pad(left=word('e'), right=word('d'))
    late = i_faces(crossing('c', 'e'), crossing('d', 'f'))
    a = crossing('a', 'b')
    selected = set(early[0].events + middle.events + late[0].events)
    # For this fixed triangle chain the short sides are ab and bz.
    triangles = [('a', 'b', z) for z in 'cdef']
    forbidden = {(v, u) for x, y, z in triangles for u, v in ((x, y), (y, z))}
    assert selected.isdisjoint(forbidden)
    histories = {}
    joins = {}
    for i, j in product(range(2), repeat=2):
        b = early[i].then(middle).then(late[j])
        source, joined, target = join_routes(a, b)
        histories[i, j, 0] = source
        histories[i, j, 1] = target
        joins[i, j] = joined
        assert source.start == word('fedcba') and target.end == word('abcedf')
        assert count(a, selected) == 0
        assert [count(h, selected) for h in (source, joined, target)] == [5]*3
        for state in (source, joined, target):
            assert tuple(e for e in state.events if e in selected) == b.events
    # The contextual r is C. The remaining active edges change precisely
    # the early or late product at its actual occurrence in each 3-history.
    for k in range(2):
        for j in range(2):
            for i, h in enumerate(early):
                assert histories[i,j,k].events[:2] == h.events
        for i in range(2):
            for j, h in enumerate(late):
                assert histories[i,j,k].events[3:5] == h.events
    for first, second in ((0,1), (1,0)):
        i=j=k=0
        schedule=[histories[i,j,k]]
        k=1
        schedule.append(histories[i,j,k])
        for mark in (first,second):
            if mark:
                j=1
            else:
                i=1
            schedule.append(histories[i,j,k])
        assert schedule[-1] == histories[1,1,1]
        assert all(x != y and x.start == y.start and x.end == y.end
                   for x,y in zip(schedule,schedule[1:]))
    print('Executed both four-input schedules and four wide join factorizations on six strands.')


def window(start, first, second):
    return (start, start+first+second, first*second) if first*second else None


def read(windows, cut):
    early = late = 0
    for w in windows:
        if w is None:
            continue
        lo, hi, weight = w
        if hi <= cut:
            early += weight
        elif cut <= lo:
            late += weight
        else:
            return None
    return early, late


def split_windows():
    checked = 0
    for a,b,c in product(range(5), repeat=3):
        for cut in range(a+b+c+1):
            for pieces in ((window(0,a,c), window(a,b,c)),
                           (window(b,a,c), window(0,b,c))):
                assert read([window(0,a+b,c)],cut) == read(pieces,cut)
                checked += 1
    print(f'Checked {checked} split-window comparisons with zero and positive projected lengths.')


if __name__ == '__main__':
    six_strands()
    split_windows()
