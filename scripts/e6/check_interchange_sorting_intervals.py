"""Compare the event-interval solver with typed spatial rules in degrees 3 and 4."""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations
from random import Random

from t_endomorphisms import expansions as spatial_expansions

from check_interchange_slot_refinement import rectangles as spatial_rectangles, steps
from interchange_sorting_fiber import raw_histories
from interchange_sorting_intervals import (candidates, common_partition, equal, next_words,
                                          runs, square_equal, square_sites, wide_equal)


def named(word):
    return tuple(tuple(e) for e in word)


def orbit(start, word):
    todo, seen = [word], {word}
    while todo:
        for w in steps(start, todo.pop(), tuple(range(len(start)))):
            if w not in seen:
                seen.add(w)
                todo.append(w)
    return seen


def closure_key(word):
    before, rects = candidates(word)
    pairs = frozenset((word[i],word[j]) for j in range(len(word))
                      for i in range(j) if before[j] >> i & 1)
    return pairs, frozenset(rects.items())


def square_neighbours(start, path):
    state = start
    for i, event in enumerate(path):
        segment = path[i:i+4]
        for other in spatial_rectangles(state, tuple(range(len(start)))).get(segment, ()):
            if len(segment) == 4:
                yield path[:i] + other + path[i+4:]
        state = state.replace(event[::-1], event)


def check_intervals():
    start = 'edcba'
    reference = {}
    square_classes = {}
    candidate_table = {}
    incidence_groups = defaultdict(list)
    run_sizes = Counter()
    keys = defaultdict(set)
    for raw in raw_histories(start):
        if raw not in reference:
            rep = raw
            reference.update(dict.fromkeys(orbit(start,raw),rep))
        w = named(raw)
        _, rects = candidates(w)
        candidate_table[raw] = rects
        if raw not in square_classes:
            pending = [raw]
            square_classes[raw] = raw
            while pending:
                for v in square_neighbours(start, pending.pop()):
                    if v not in square_classes:
                        square_classes[v] = raw
                        pending.append(v)
        native = {named(v) for v in steps(start, raw, tuple(range(5)))}
        assert set(next_words(w,rects)) == native
        parts,_ = runs(w,rects)
        mixed = [len(p) for p in parts if {a for a,_ in p} & {b for _,b in p}]
        run_sizes[max(mixed,default=0)] += 1
        incidence_groups[tuple(tuple(e for e in w if s in e) for s in start)].append(raw)
        keys[closure_key(w)].add(reference[raw])
    checks = 0
    for group in incidence_groups.values():
        for i,p in enumerate(group):
            for q in group[i:]:
                assert equal(p,q) == (reference[p]==reference[q])
                assert square_equal(named(p), named(q), candidate_table[p]) == (square_classes[p] == square_classes[q])
                checks += 1
    assert len(keys) == len(set(reference.values())) == 422
    assert all(len(values)==1 for values in keys.values())
    print(f"{len(reference)} five-slot histories: every one-step neighbourhood and {checks} same-incidence comparisons agree with typed grounding.")
    print(f"Largest remaining mixed run per input: {dict(sorted(run_sizes.items()))}.")

    p = tuple('ab ac ef bc df af bf de ae ad be cf ce bd cd'.split())
    q = p[:9]+(p[10],p[9])+p[11:]
    assert closure_key(named(p)) != closure_key(named(q))
    # A first-use obstruction freezes every pair in p.
    _, rects = candidates(named(p))
    assert not rects and len(candidates(named(q))[1]) == 3
    assert set(next_words(named(p),rects)) == set()
    assert (len(orbit('fedcba',p)),len(orbit('fedcba',q))) == (1,4)
    assert not equal(p,q)
    # A common rectangular partition is not necessary for equality in a
    # mixed-role run: the three-rectangle detour from Response 8.
    a = named('de ce be ae cd bd bc ad ac ab'.split())
    b = named('de ce cd be bd bc ae ad ac ab'.split())
    assert equal(a,b) and not common_partition(a,b) and not square_equal(a,b,candidates(a)[1])
    print("First-use closure separates the six-slot orbits of sizes 1 and 4, leaving 0 and 3 possible rectangles.")


def check_square_chain():
    # Alternating two rows across successive columns. The middle pairs of
    # neighbouring squares can each flip separately, but cannot both be flipped.
    for n in (3, 5, 9, 64):
        cols = tuple(range(n+1, 1, -1))
        word = tuple((row, col) for col in cols for row in (0, 1))
        boxes = {}
        for left, right in zip(cols, cols[1:]):
            support = frozenset((row, col) for row in (0, 1) for col in (left, right))
            boxes[support] = ((0, 1), (left, right))
        sites = tuple(range(1, len(word)-2, 2))
        def orientation(mask):
            w = list(word)
            for k, pos in enumerate(sites):
                if mask >> k & 1:
                    w[pos:pos+2] = w[pos:pos+2][::-1]
            return tuple(w)
        p = orientation(sum(1 << k for k in range(0, len(sites), 2)))
        assert set(square_sites(p, boxes)) == set(sites)
        masks = range(1 << len(sites)) if n <= 9 else (0, 1, 3, (1 << len(sites))//3)
        for mask in masks:
            assert square_equal(p, orientation(mask), boxes) == (mask & (mask >> 1) == 0)
    print("Guarded-square comparisons agree with the independent-set condition through 63 interacting sites.")


def check_wide_boundary():
    rng = Random(7903)
    n = 15
    cols = tuple(range(n+1, 1, -1))
    word = tuple((row, col) for col in cols for row in (0, 1))
    # One wide box in the middle, with a chain of guarded squares on either
    # side. Independent spatial expansions ground the chosen subpresentation.
    palette = {}
    rules = defaultdict(set)
    for start, width in ([(j, 2) for j in range(n-1)] + [(6, 3)]):
        active = cols[start:start+width]
        support = frozenset((row, col) for row in (0, 1) for col in active)
        palette[support] = ((0, 1), active)
        forms = spatial_expansions((0, 1), active[::-1])
        for form in forms:
            rules[form].update(forms)
    group, pending = {word}, [word]
    while pending:
        path = pending.pop()
        for pos in range(len(path)-3):
            for width in (4, 6):
                for form in rules.get(path[pos:pos+width], ()):
                    other = path[:pos] + form + path[pos+width:]
                    if other not in group:
                        pending.append(other)
                        group.add(other)
    assert len(group) > 1000
    paths = sorted(group)
    # Exercise both directions with different starting mobile pairs.
    tests = [(word, paths[-1]), (paths[-1], word)]
    for _ in range(20):
        source, target = rng.choice(paths), rng.choice(paths)
        tests.append((source, target))
        eligible = [i for i, (e, f) in enumerate(zip(target, target[1:]))
                    if e[0] != f[0] and e[1] != f[1]]
        i = rng.choice(eligible)
        tests.append((source, target[:i]+target[i:i+2][::-1]+target[i+2:]))
    results = []
    for source, target in tests:
        expected = target in group
        assert wide_equal(source, target, palette) == expected
        results.append(expected)
    assert 0 < sum(results) < len(results)
    print(f"{len(group)} typed histories in the one-wide-box component; {len(tests)} comparisons cross its two square-chain boundaries.")


def grid_histories(width):
    """Ground all 3-crossings towards the matching target, including wide blocks."""
    start = tuple((row,j) for j in range(width) for row in (1,0))
    target = tuple((row,j) for j in range(width) for row in (0,1))
    pos = {slot:i for i,slot in enumerate(target)}
    pending, full = [(start, ())], set()
    while pending:
        state, path = pending.pop()
        if state == target:
            full.add(path)
        for cut in range(1,len(state)):
            for lo in range(cut-1,-1,-1):
                if state[lo][0] != 1:
                    break
                for hi in range(cut+1,len(state)+1):
                    if state[hi-1][0] != 0:
                        break
                    right, left = state[lo:cut], state[cut:hi]
                    if all(pos[x] < pos[y] for x in left for y in right):
                        assert len(left)==len(right)==1 and left[0][1]==right[0][1]
                        pending.append((state[:lo]+left+right+state[hi:], path+(left[0][1],)))
    return full


@cache
def native_blocks(order):
    """Temporal subpaths of the 3-history on the two sides of a spatial cut."""
    events = [(2*i,2*i+1) for i in order]
    result = set()
    for cut in range(1,2*len(order)):
        for lo in range(len(order)):
            for mid in range(lo+1,len(order)):
                if any(i < cut for i,_ in events[lo:mid]):
                    continue
                for hi in range(mid+1,len(order)+1):
                    if any(j >= cut for _,j in events[mid:hi]):
                        break
                    result.add((lo,mid,hi))
    return tuple((order[mid:hi], order[lo:mid],
                  order[:lo]+order[mid:hi]+order[lo:mid]+order[hi:])
                 for lo,mid,hi in sorted(result))


@cache
def native_sweeps(f,g,left,right):
    if len(f)==len(g)==1:
        return {((f[0],g[0]),)}
    words = set()
    if left or len(g)==1:
        for cut in range(1,len(f)):
            words.update(u+v for u in native_sweeps(f[:cut],g,left,right)
                         for v in native_sweeps(f[cut:],g,left,right))
    if right or len(f)==1:
        for cut in range(1,len(g)):
            words.update(u+v for u in native_sweeps(f,g[cut:],left,right)
                         for v in native_sweeps(f,g[:cut],left,right))
    # No complete atomic expansion when both axes are wide and both guards fail.
    return words


def check_grid():
    count = 0
    for width in range(1,7):
        orders = grid_histories(width)
        assert orders == set(permutations(range(width)))
        for order in orders:
            actual = set(native_blocks(order))
            expected = set()
            for lo in range(width):
                for mid in range(lo+1,width):
                    for hi in range(mid+1,width+1):
                        f,g = order[mid:hi],order[lo:mid]
                        if max(f)<min(g):
                            expected.add((f,g,order[:lo]+f+g+order[hi:]))
            assert actual == expected
            count += len(actual)
    print(f"{count} contextual 4-blocks on up to six sites agree with the site-order presentation.")

    def options(order, remaining):
        for f,g,_ in native_blocks(order):
            length = len(f)*len(g)
            if length <= len(remaining):
                yield f,g,length

    width = 5
    end = tuple(range(width))
    native_count = Counter()
    for raw in raw_histories('edcba'):
        w = tuple(tuple(ord(c)-97 for c in e) for e in raw)
        order = end[::-1]
        neighbours = set()
        for i,(a,b) in enumerate(w):
            for f,g,length in options(order,w[i:]):
                segment = w[i:i+length]
                for l,r in ((False,False),(False,True),(True,False),(True,True)):
                    sweeps = native_sweeps(f,g,l,r)
                    if segment not in sweeps:
                        continue
                    native_count[l,r] += len(sweeps)-1
                    if l and r:
                        neighbours.update(w[:i]+s+w[i+length:] for s in sweeps if s != segment)
                    else:
                        assert len(sweeps)==1
            j = order.index(b)
            assert order[j+1] == a
            order = order[:j]+(a,b)+order[j+2:]
        assert order == end
        ground = {tuple(tuple(ord(c)-97 for c in e) for e in other)
                  for other in steps('edcba',raw,end)}
        assert neighbours == ground
    assert native_count[True,True]>0
    print(f"Atomic five-site replacements in the four settings: {dict(native_count)}.")


if __name__ == '__main__':
    check_intervals()
    check_square_chain()
    check_wide_boundary()
    check_grid()
