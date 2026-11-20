"""Find the first-column circle in a periodic guarded-switch strip."""

from graphlib import CycleError, TopologicalSorter
from itertools import product

from homotopy_polygraph_periodic_strip import strip_arcs
from homotopy_polygraph_semaphore import histories


def first_column_cut(rows, columns, incident):
    strip = strip_arcs(rows,columns,incident)
    first = next(actor for slab in columns for actor in slab)
    t, z = (0,'T'), (0,'Z')
    left = [(*first,1)]+[(j,'columns-Z',0) for j in range(first[0],-1,-1)]+[(*z,3)]
    assert first[0] <= 1  # strip_arcs uses same- or adjacent-slab transfers
    retained = {((*t,1),(*first,2)), ((*z,3),(*t,2)), *zip(left,left[1:])}
    assert retained <= strip
    actors = (t,first,z)
    legal = set()
    for roles in product((1,2,3),repeat=3):
        def exposed(port):
            i = port[:2]
            return not port[2] or roles[actors.index(i)] & port[2] == port[2]
        graph = TopologicalSorter()
        for s,d in retained:
            if exposed(s) and exposed(d):
                graph.add(d[:2],s[:2])
        try:
            tuple(graph.static_order())
        except CycleError:
            assert roles == (3,3,3)
            continue
        pos = tuple(int(r==2) for r in roles)
        moving = tuple(i for i,r in enumerate(roles) if r==3)
        legal.add((pos,moving))
    assert len(legal) == 26
    betti = histories([[None]]*3,legal)
    assert betti[:2] == (1,1) and not any(betti[2:])
    return len(retained), tuple(betti[:2])


def check():
    for mask in range(16):
        rows = [[(j,'a')] for j in range(2)]
        cols = [[(j,'b')] for j in range(2)]
        inc = {((j,'a'),(k,'b')) for j,k in product(range(2),repeat=2) if mask & (1<<(2*j+k))}
        assert first_column_cut(rows,cols,inc) == (4,(1,1))
    for length in (1,2,4,8,16,64):
        rows = [[(j,'a0'),(j,'a1')] for j in range(length)]
        cols = [[(j,'b0')] for j in range(length)]
        assert first_column_cut(rows,cols,set()) == (4,(1,1))
    print('16 incidence matrices and six strip lengths through 64: four literal connections, '
          '26 legal cube faces, one strict component with Betti (1,1).')


if __name__ == '__main__':
    check()
