"""Ground the grammar calculations in the spatial presentation of (K15)."""

from collections import Counter, deque
from functools import cache

from check_interchange_slot_refinement import rectangles, steps
from interchange_sorting_fiber import raw_histories
from interchange_sorting_layers import (SortingLayers, parallel_component, square_positions,
                                       square_signature)


def expand(grammar, root):
    @cache
    def read(node):
        rule = grammar.nodes[node]
        if rule[0] == 'literal':
            return {(''.join(rule[1]),)}
        if rule[0] == 'empty_word':
            return {()}
        if rule[0] == 'choice':
            return set.union(*(read(i) for i in rule[1:]))
        return {p + q for p in read(rule[1]) for q in read(rule[2])}
    return read(root)


@cache
def windows(start, word):
    factors = tuple(range(26))
    state, enabled = start, []
    for i, event in enumerate(word):
        for source, alternatives in rectangles(state, factors).items():
            if alternatives and word[i:i+len(source)] == source:
                enabled.append((i, source, alternatives))
        assert event[::-1] in state
        state = state.replace(event[::-1], event)
    return enabled


def square_orbit(start, sources):
    pending, seen = list(sources), set(sources)
    while pending:
        word = pending.pop()
        for i, source, alternatives in windows(start, word):
            if len(source) != 4:
                continue
            for other in alternatives:
                path = word[:i] + other + word[i+4:]
                if path not in seen:
                    seen.add(path)
                    pending.append(path)
    return seen


def wide_layer(start, word):
    forms = [{()}] + [set() for _ in word]
    for i, event in enumerate(word):
        forms[i+1].update(p + (event,) for p in forms[i])
        for j, source, alternatives in windows(start, word):
            if i == j and len(source) > 4:
                forms[i+len(source)].update(p + q for p in forms[i] for q in alternatives)
    return forms[-1]


def has_cover(start, component):
    supports = {frozenset(source) for w in component for _, source, _ in windows(start, w)
                if len(source) > 4}
    maximal = {box for box in supports if not any(box < other for other in supports)}
    if sum(map(len, maximal)) != len(set().union(*maximal)):
        return False
    return any(maximal <= {frozenset(source) for _, source, _ in windows(start, w)}
               for w in component)


def check_layers(start, word):
    layers = SortingLayers(word)
    expected = square_orbit(start, {word})
    assert {square_signature(w) for w in expected} == {square_signature(word)}
    depth = 0
    while True:
        assert expand(layers.grammar, layers.root) == expected
        enabled = {frozenset(tuple(e) for e in source) for w in expected
                   for _, source, _ in windows(start, w) if len(source) > 4}
        assert layers.exposed_boxes() == enabled
        extended = square_orbit(start, set().union(*(wide_layer(start, w) for w in expected)))
        if extended == expected:
            break
        layers.advance()
        expected = extended
        depth += 1
    full = parallel_component(word)
    assert (full is not None) == has_cover(start, expected)
    if full is not None:
        assert expand(full.grammar, full.root) == expected
    return depth, len(expected), full is not None


def distance(start, source, target):
    queue, seen = deque([(source, 0)]), {source}
    while queue:
        w, d = queue.popleft()
        if w == target:
            return d
        for v in steps(start, w, tuple(range(26))):
            if v not in seen:
                queue.append((v, d+1))
                seen.add(v)
    return None


def check_divisors():
    samples = [('fedcba', 'ef ab cd ad bd ac af ae bc bf cf be',
                'ef ab cd ad ac af ae bd bc bf cf be', 'ce df de'),
               ('gfedcba', 'fg eg ef ab dg cg ag bg cd ad ac af ae bd bc bf cf df be',
                'fg eg ef ab dg cg cd ag bg ad ac af ae bd bc bf cf df be', 'ce de')]
    for start, p, q, suffix in samples:
        p, q, suffix = (tuple(w.split()) for w in (p,q,suffix))
        assert p != q and not windows(start,p) and not windows(start,q)
        d = distance(start, p+suffix, q+suffix)
        drops = [distance(start.replace(a,''), tuple(e for e in p if a not in e),
                          tuple(e for e in q if a not in e)) for a in start]
        assert d is not None and None not in drops
        print(f"{len(start)} strands: common multiple in {d} moves, deletion distances {drops}.")


def check_square_radius():
    word = tuple(map(tuple, 'de ce cd be ae bd bc ad ac ab'.split()))
    assert square_positions(word) == {6: 1, 4: 2, 2: 3}
    cols = tuple(range(65, 1, -1))
    base = [(r,c) for c in cols for r in (0,1)]
    for i in range(1, len(base)-2, 4):
        base[i:i+2] = reversed(base[i:i+2])
    profile = square_positions(base)
    assert set(profile) == set(range(1, len(base)-2, 2))
    signature = square_signature(base)
    for i in range(len(base)):
        lo = max(0, i-6)
        assert signature[i] == square_signature(base[lo:i+7])[i-lo]
    print("Three synchronous passes are attained; clipped radius-six codes agree at 128 positions.")


def check_large_and_parallel():
    # Two independent copies both need two successive wide moves.
    p = 'de ce be ae cd bd bc ad ac ab'.split()
    q = 'de ce cd be bd bc ae ad ac ab'.split()
    def second(w):
        return [e.translate(str.maketrans('abcde', 'fghij')) for e in w]
    source, target = tuple(p + second(p)), tuple(q + second(q))
    assert check_layers('edcbajihgf', source)[:2] == (2, 64)
    layers = SortingLayers(source)
    layers.advance()
    assert not layers.contains(target)
    layers.advance()
    assert layers.contains(target)

    # Independent large boxes, using the same width but distinct actual names.
    def sweeps(first, width):
        rows = (first, first+1)
        cols = range(first+2, first+width+2)
        return (tuple((r,c) for r in rows for c in cols),
                tuple((r,c) for c in cols for r in rows))
    a,b = sweeps(0, 24)
    c,d = sweeps(26, 24)
    covered = parallel_component(a+c)
    assert covered is not None and covered.contains(b+d)
    # In one rectangle a two-row schedule that admits no axis cut occurs
    # on its first three columns. Its projection cannot equal a full block.
    bad_prefix = (a[0], a[1], a[24], a[2], a[25], a[26])
    assert not covered.contains(bad_prefix + b[6:] + d)
    print("Two disjoint 2-by-24 boxes tested symbolically; two five-strand detours run in parallel.")


def check_boundary_transport():
    start = 'hgfedcba'
    w = tuple('ef df ab cf af gh cd ad ce ae ac bf ah ag bd be bc de bh bg ch dh cg dg eh fh eg fg'.split())
    region = frozenset(x+y for x in 'bcde' for y in 'gh')
    assert not any(frozenset(src) == region for _,src,_ in windows(start,w))
    language = SortingLayers(w)
    allowed = frozenset(tuple(e) for e in region)
    language.boxes = {box: axes for box,axes in language.boxes.items() if box <= allowed}
    assert allowed in language.exposed_boxes()
    assert any(len(src) == 6 and set(src) <= region for _,src,_ in windows(start,w))
    pending, native = [w], {w}
    while pending:
        path = pending.pop()
        for j, src, alternatives in windows(start,path):
            if len(src) > 4 and not set(src) <= region:
                continue
            for other in alternatives:
                q = path[:j] + other + path[j+len(src):]
                if q not in native:
                    native.add(q)
                    pending.append(q)
    language.advance()
    assert expand(language.grammar, language.root) == native
    print(f"All {len(native)} histories recovered when a square displaces the end of a four-by-two box.")


if __name__ == '__main__':
    counts = Counter()
    square_classes = {}
    for word in raw_histories('edcba'):
        raw_class = square_orbit('edcba', {word})
        code = square_signature(word)
        assert square_classes.setdefault(code, raw_class) == raw_class
        depth, _, covered = check_layers('edcba', word)
        counts[depth, covered] += 1
    print(f"Five-strand complete comparisons by layer depth and coverage: {dict(sorted(counts.items()))}.")
    check_boundary_transport()
    check_square_radius()
    check_large_and_parallel()
    check_divisors()
