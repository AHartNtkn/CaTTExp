"""Check the divisor observations against native two-row grid contractions."""

from itertools import product

from check_interchange_grid_contractions import normal_path
from check_interchange_slot_refinement import steps
from grid_loop_words import states
from interchange_divisor_observers import CornerReader, pair_axes, rigid_coordinates
from interchange_grid_windows import Tile, merge, residual, start
from interchange_shared_whiskers import Words
from t_endomorphisms import expansions


def named_schedule(size, schedule):
    # F on the left row crosses low columns in descending order. G on
    # the right row crosses high columns in descending chronological order.
    return tuple((size-i, size+1+j) for i, j in schedule)


def tile_path(size, events):
    f = [(0, x) for x in range(size, 0, -1)]
    g = [(1, x) for x in range(2*size, size, -1)]
    active = g + f
    before, after = 'u'*size, 'd'*size
    result = []
    for a, b in events:
        i = active.index((1, b))
        assert active[i+1] == (0, a)
        pre = before + ''.join('ud'[r] for r, _ in active[:i])
        post = ''.join('ud'[r] for r, _ in active[i+2:]) + after
        revpost = post[::-1].translate(str.maketrans('ud', 'du'))
        result.append(Tile(pre, (a,), (b,), revpost))
        active[i:i+2] = active[i:i+2][::-1]
    assert active == f+g
    return tuple(result)


def native(word):
    ctx = start(0)
    result = []
    for tile in word:
        result.append(tile)
        while len(result) >= 2:
            parent = merge(*result[-2:], ctx, ctx)
            if parent is None:
                break
            result[-2:] = [parent]
    return tuple((residual(ctx,t.pre), t.f, t.g, residual(ctx,t.revpost)) for t in result)


def expand_word(words, root):
    stack, result = [root], []
    while stack:
        rule = words.rules[stack.pop()]
        if len(rule) == 1:
            result.append(rule[0])
        else:
            stack.extend(~ref for ref in reversed(rule))
    return tuple(result)


def fold(words, labels):
    value = 0
    for label in labels:
        value = words.join(value, words.letter(label))
    return value


def observe(reader, node):
    state, emitted = reader.run((), node)
    return expand_word(reader.output, reader.output.join(emitted, reader.finish(state)))


def check_divisors(size):
    rows = tuple(range(size, 0, -1))
    cols = tuple(range(size+1, 2*size+1))
    schedules = sorted(named_schedule(size, w) for w in expansions(tuple(range(size)), tuple(reversed(range(size)))))
    raw = Words()
    # With 2-by-2 observations everywhere, every singleton count is visible.
    axes = [(a,b) for a in pair_axes(rows) for b in pair_axes(cols)
            if len(a) == len(b) == 2]
    readers = [[CornerReader(raw,a,b,reverse) for a,b in axes] for reverse in (False,True)]
    high = tuple(range(2*size, size, -1))
    low = tuple(range(size, 0, -1))
    base = tuple((row,k) for ks in (high,low) for row in (0,1) for k in ks)
    end = tuple((row,k) for row in (0,1) for k in high+low)
    assert states((2*size,2*size), base)[-1] == states((2*size,2*size), end)[-1] == (0,0)
    def lower(path):
        return residual(start(0), ''.join('ud'[r] for r,_ in path))
    assert lower(base) == lower(end)
    variants = (schedules[0], schedules[-1])
    contexts = tuple(tile_path(size, w) for w in variants)
    maps = [({}, {}) for _ in range(2)]
    words_checked = 0
    for k, w in enumerate(schedules):
        native_tiles = tile_path(size,w)
        for i in range(len(w)+1):
            for suffix in (0,1):
                # Vary the spelling of a whole earlier/later copy of the loop.
                j = (k+i)%2
                if suffix:
                    names = w[i:] + variants[j]
                    trace = native_tiles[i:] + contexts[j]
                else:
                    names = variants[j] + w[:i]
                    trace = contexts[j] + native_tiles[:i]
                node = fold(raw, names)
                observation = tuple(observe(r, node) for r in readers[suffix])
                value = native(trace)
                forward, backward = maps[suffix]
                assert forward.setdefault(value,observation) == observation
                assert backward.setdefault(observation,value) == value
                words_checked += 1
    counts = tuple(len(m[0]) for m in maps)
    print(f"{size}x{size}: {words_checked} contextual divisors of a repeated 4-loop; {counts} native prefix/suffix class counts.")


def check_three_paths():
    rows, cols = (0,1,2), (0,1,2,3)
    raw = Words()
    for suffix in (False,True):
        observers = [CornerReader(raw,a,b,suffix) for a in pair_axes(rows)
                     for b in pair_axes(cols[::-1]) if len(a)==len(b)==2]
        by_value, by_observation = {}, {}
        for word in expansions(rows,cols):
            for i in range(1+len(word)):
                part = word[i:] if suffix else word[:i]
                node = fold(raw,part)
                obs = tuple(observe(reader,node) for reader in observers)
                value = normal_path(part)
                assert by_value.setdefault(value,obs) == obs
                assert by_observation.setdefault(obs,value) == value
    print("The corner observations recover every prefix and suffix class of the 3-by-4 degree-three block.")


def check_boundary_pair():
    # On three corners the two prefixes disagree. Supplying the fourth
    # normalizes them even if a previous copy used the other spelling.
    raw = Words()
    u,x,y,v = (0,0),(0,1),(1,0),(1,1)
    axes = (0,1)
    for reverse in (False, True):
        reader = CornerReader(raw, axes, axes, reverse)
        for seq in product((u,x,y,v), repeat=5):
            word = fold(raw, seq)
            projected = tuple(2*i+j for i,j in seq)
            if reverse:
                projected = tuple(3-c for c in reversed(projected))
            expected = bytes(projected).replace(bytes((0,2,1,3)), bytes((0,1,2,3)))
            assert bytes(observe(reader,word)) == expected
    for suffix in (False,True):
        seq = (x,y,v) if suffix else (u,x,y)
        alt = (y,x,v) if suffix else (u,y,x)
        assert normal_path(tuple((r,1-c) for r,c in seq)) != normal_path(tuple((r,1-c) for r,c in alt))
        # A single observed axis name on either side loses the reversed pair.
        for a,b in product(pair_axes(axes),repeat=2):
            reader=CornerReader(raw,a,b,suffix)
            assert (observe(reader,fold(raw,seq)) == observe(reader,fold(raw,alt))) == (len(a)*len(b)<4)
    print("Both streaming directions checked on 2,048 five-letter inputs; four active site names are necessary for these divisors.")


def check_low_actions():
    # Formal rigid loops on the two extreme 3-corners. The complete
    # underlying 3-sweeps agree. Their partial pads can still differ.
    raw = Words()
    u,x,y,v = (0,2),(0,1),(1,2),(1,1)
    rules = [('head',5,'on final corner'), ('head',5,'on first corner')]
    def pad(node,left,right):
        rules.append(('pad',3,fold(raw,left),node,fold(raw,right)))
        return len(rules)-1
    left = pad(0,(u,x,y),())
    left_alt = pad(0,(u,y,x),())
    right = pad(1,(),(x,y,v))
    right_alt = pad(1,(),(y,x,v))
    directions = [set(),set()]
    for code in rigid_coordinates(rules,raw,{3:(0,1),4:()},{3:(2,1),4:()}):
        for i,(a,b) in enumerate(((left,left_alt),(right,right_alt))):
            if not code.equal_coordinate(a,b):
                directions[i].add((code.base_rank,code.reverse))
    assert directions == [{(3,False)},{(3,True)}]
    print("Rank-three left and right observations detect the respective partial pads of formal upper loops.")


def check_rigid_sweeps():
    # The two doubled blocks in the 2-by-4 grid have 4-loops E and L.
    # Their elementary 5-comparison D changes LE to EL. Its adjacent
    # six-square permutes two neighbouring updates of disjoint copies.
    raw = Words()
    e, l = raw.letter((3,4)), raw.letter((1,2))
    u, v = raw.join(l,e), raw.join(e,l)
    rules = [('empty',), ('head',5,'D'), ('head',6,'square on two D')]
    def add(*rule):
        rules.append(rule)
        return len(rules)-1
    def pad(a,x,b):
        return add('pad',4,a,x,b)
    def cat(a,b):
        return add('join',a,b)
    east = cat(pad(0,1,u),pad(v,1,0))
    west = cat(pad(u,1,0),pad(0,1,v))
    sweep = 1
    for i in range(48):
        if i%2 == 0:
            prev, old_u, old_v = sweep, u, v
        sweep = cat(pad(0,sweep,u),pad(v,sweep,0))
        u, v = raw.join(u,u),raw.join(v,v)
        if i%2:
            steps = [pad(repeat(raw,old_v,j),prev,repeat(raw,old_u,3-j)) for j in range(4)]
            quarter = cat(cat(steps[0],steps[1]),cat(steps[2],steps[3]))
    # Two schedules of disjoint six-squares with four update sites.
    source, target = raw.join(l,e), raw.join(e,l)
    def six(order, pos):
        slots = [source]*len(order)
        moves = []
        for i in order:
            a,b = 0,0
            for item in slots[:i]:
                a=raw.join(a,item)
            for item in slots[i+1:]:
                b=raw.join(b,item)
            moves.append(pad(a,1,b))
            slots[i]=target
        lo=order[pos+1]
        assert order[pos]==lo+1
        old = [target if j in order[:pos] else source for j in range(len(order))]
        a,b=0,0
        for item in old[:lo]:
            a=raw.join(a,item)
        for item in old[lo+2:]:
            b=raw.join(b,item)
        before=after=0
        for move in moves[:pos]:
            before=cat(before,move)
        for move in moves[pos+2:]:
            after=cat(after,move)
        return add('right', add('left',before,pad(a,2,b)),after)
    first = cat(six((1,0,3,2),0),six((0,1,3,2),2))
    second = cat(six((1,0,3,2),2),six((1,0,2,3),0))
    row_names={3:(0,1),4:(3,1)}
    col_names={3:(4,3,2,1),4:(2,4)}
    distinct = [False,False]
    for code in rigid_coordinates(rules,raw,row_names,col_names):
        assert code.equal_coordinate(sweep,quarter)
        for i,(a,b) in enumerate(((east,west),(first,second))):
            distinct[i] |= not code.equal_coordinate(a,b)
    assert all(distinct)
    print("Five-dimensional binary and quaternary sweeps agree at 2^48 sites; distinct five- and six-dimensional update orders separated.")


def check_five_slot_obstruction():
    p = tuple('de ab ce cd ae be ad ac bd'.split())
    q = tuple('de ab ce ae be cd ad ac bd'.split())
    start = 'edcba'
    factors = tuple(range(5))
    assert not set(steps(start,p,factors)) and not set(steps(start,q,factors))
    chain = [p+('bc',), tuple('de ab ce cd ae ad be bd ac bc'.split()),
             tuple('de ab ce ae be cd ad bd ac bc'.split()), q+('bc',)]
    for a,b in zip(chain,chain[1:]):
        assert b in set(steps(start,a,factors))
    for name in start:
        a,b = (tuple(e for e in w if name not in e) for w in (p,q))
        assert a == b or b in set(steps(start.replace(name,''),a,factors))
    print("Five singleton spans: two isolated divisors agree on every four-span restriction and acquire a common multiple in three moves.")


def repeat(raw,node,count):
    result = 0
    for _ in range(count):
        result=raw.join(result,node)
    return result


if __name__=='__main__':
    check_boundary_pair()
    check_three_paths()
    for size in (2,3,4):
        check_divisors(size)
    check_five_slot_obstruction()
    check_low_actions()
    check_rigid_sweeps()
