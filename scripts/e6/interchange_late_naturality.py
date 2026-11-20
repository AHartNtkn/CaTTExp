"""A late triangle cannot pass an independent early event by inner naturality on a cycle."""

from collections import Counter
from itertools import combinations

from interchange_filtered_windows import crossing, join_routes
from interchange_path_grading import History, i_faces, word
from interchange_regular_rectangles import find_rank, verify_rank
from interchange_sorting_fiber import raw_histories
from interchange_triangle_carriers import BIT, PACKETS, START, orientation, trajectory
from interchange_triangle_join_interval import gray, ground_interval, restrict_interval


def certify(early, early_left):
    late = ''.join(s for s in sorted(START) if s not in early)
    cut = early + late[::-1] if early_left else late[::-1] + early
    early_events = {a+b for a, b in combinations(sorted(START), 2) if cut.index(a) < cut.index(b)}
    histories = raw_histories(START)
    boundaries = {p for p in histories if cut in trajectory(p)}
    sources = {p for p in boundaries if not orientation(p) & BIT[late]}
    targets = {p for p in boundaries if orientation(p) & BIT[late]}
    assert sources and targets

    def allowed(edge):
        return edge.family == 'K15' or all(len(PACKETS[t] & early_events) in (0,3)
                                           for t in gray(edge))

    classes, at = restrict_interval(START, sources, targets, set(histories), allowed)
    graph, label = ground_interval(classes, at)
    products = {name for g, name in label.items() if g.family == 'i' and
                (g.left_events if early_left else g.right_events) == (early,) and
                len(g.left_events) + len(g.right_events) == 4}
    triangles = {name for g, name in label.items() if late in gray(g)}
    family = 'N_R ' if early_left else 'N_L '
    strict = [(r.source, r.target) for r in graph.rules.values() if r.name.startswith(family)
              and products.intersection(r.source.edges) and triangles.intersection(r.source.edges)]
    if strict:
        rank = find_rank(graph, strict)
        assert rank is not None and not rank.charges and verify_rank(graph, strict, rank)
    return Counter(cuts=1, nonempty=int(bool(strict)), strict=len(strict), rules=len(graph.rules))


def check_join():
    # The right variable B varies the order of two early crossings. The
    # only late moving event g is ab. Complete the right sorting after
    # the inner window so that both source and target visit the cut cdefba.
    a = crossing('a','b')
    before, after = i_faces(crossing('e','f'), crossing('c','d'))
    tail = History(before.end, (('f','c'),('e','c'),('f','d'),('e','d')))
    assert tail.end == word('cdef')
    sources, joined = [], []
    for b in (before.then(tail), after.then(tail)):
        src, dst, _ = join_routes(a, b)
        sources.append(src)
        joined.append(dst)
    g, = a.events
    for pair in (sources, joined):
        p, q = pair
        i = next(i for i,(e,f) in enumerate(zip(p.events,q.events)) if e != f)
        assert p.events[:i] == q.events[:i] and p.events[i+2:] == q.events[i+2:]
        assert set(p.events[i:i+2]) == {('f','e'),('d','c')}
        assert p.events[i:i+2] == q.events[i:i+2][::-1]
        assert (g in p.events[:i]) == (pair is joined)
    print('On the six-strand right join variation the marked early exchange moves past ab.')


def check():
    totals = Counter()
    for e in combinations(sorted(START), 2):
        for left in (True, False):
            totals.update(certify(''.join(e), left))
    assert totals['cuts'] == 20 and totals['nonempty'] == 14 and totals['strict'] == 72
    print(f'Checked {totals["rules"]} grounded rules at 20 cuts, with strict additive '
          f'scores on all {totals["strict"]} candidate naturalities.')
    check_join()


if __name__ == '__main__':
    check()
