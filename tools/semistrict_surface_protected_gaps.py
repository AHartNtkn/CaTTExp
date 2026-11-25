"""Test scalar readings across width-changing circuits at protected vertices."""

from itertools import product

from semistrict_surface_planar_occurrences import component_transport
from semistrict_surface_unary_gap_charts import classes, keep


# p carries the scalars. All other vertices in this example are u.
ENDS = {'l':('u','p'), 'r':('p','u'), 'x':('u','u')}
HALVES = {'l':'L', 'r':'R', 'x':''}
RULES = {'U':('x','xx'), 'K':('l','xl'), 'V':('r','rx'), 'T':('x','x'), 'R':('lr','lrx'),
         'H':('x','x'), 's':('',''), 't':('','')}
NATIVE = {'U','K'}
RODS = {'R','H'}
SCALARS = {'s','t'}


def compress(word):
    return ''.join(HALVES[x] for x in word)


def vertex(word, i):
    return ENDS[word[i-1]][1] if i else ENDS[word[0]][0]


def histories(path, names):
    if not names:
        yield ()
        return
    for name in names:
        src, tgt = RULES[name]
        for offset in range(len(path)-len(src)+1):
            if not path.startswith(src, offset):
                continue
            if name in SCALARS and vertex(path, offset) != 'p':
                continue
            after = path[:offset] + tgt + path[offset+len(src):]
            for tail in histories(after, names-{name}):
                yield ((name,offset),) + tail


def flat_histories(path, names):
    if not names:
        yield ()
        return
    for name in names:
        src = compress(RULES[name][0])
        for offset in range(len(path)-len(src)+1):
            if not path.startswith(src, offset):
                continue
            if name in SCALARS and not (offset and path[offset-1] == 'L'):
                continue
            for tail in flat_histories(path, names-{name}):
                yield ((name, offset),) + tail


def project(path, history):
    out = []
    for g, i in history:
        src, tgt = RULES[g]
        assert path.startswith(src, i)
        if g in SCALARS or (g in RODS and compress(src)):
            out.append((g, len(compress(path[:i]))))
        if g not in RODS and g not in SCALARS:
            assert compress(src) == compress(tgt)
        path = path[:i] + tgt + path[i+len(src):]
    return tuple(out)


def expand(history, marker, steps):
    return tuple(item for g,i in history
                 for item in ([(u,i+j) for u,j in steps] if g == marker else [(g,i)]))


def audit(path, native, scalars):
    central_names = native | RODS
    visible = {g for g in RODS if compress(RULES[g][0])}
    flat_rules = {g: tuple(map(compress, r)) for g,r in RULES.items()}
    central = classes(histories(path, central_names), RULES)
    flat = classes(flat_histories(compress(path), visible | scalars), flat_rules)
    bare = classes(flat_histories(compress(path), visible), flat_rules)
    compatible = {(c, f) for c, f in product(set(central.values()), set(flat.values()))
                  if bare[project(path,c)] == bare[keep(f,visible)]}
    count = total = 0
    fibre = {}
    offsets = set()
    for root, lifts, rigid in component_transport(set(histories(path, central_names | scalars)), RULES):
        assert rigid
        keys = set()
        for h in lifts:
            fp = project(path,h)
            keys.add((central[keep(h,central_names)], flat[fp]))
            for marker, steps in [('R', [('V',1)]), ('R', [('V',1),('T',2)]),
                                  ('H', []), ('H', [('T',0)])]:
                actual = project(path, expand(h, marker, steps))
                assert actual == tuple(row for row in fp if row[0] != marker)
            for g,i in h:
                if g in scalars:
                    offsets.add(i)
        assert len(keys) == 1
        key, = keys
        assert key not in fibre
        fibre[key] = root
        count += 1
        total += len(lifts)
    assert set(fibre) == compatible
    print(path, 'spellings', total, 'positive classes', len(set(central.values())),
          'mixed pullback classes', count, 'concrete scalar offsets', sorted(offsets))


if __name__ == '__main__':
    audit('xlrx', NATIVE, SCALARS)
    audit('xlrlr', {'K'}, SCALARS)
    # If an ordinary gate straddles p, flattening it to an identity loses
    # which side of that gate a scalar occupies; both separate orders are legal.
    offending = {'g': ('lr','lr'), 's': ('','')}
    words = {(('g',0), ('s',1)), (('s',1), ('g',0))}
    assert len(set(classes(words, offending).values())) == 2
    assert len({keep(w, {'s'}) for w in words}) == 1
    print('straddling ordinary gate: two scalar placements with one erased reading')
