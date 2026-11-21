"""Check strip divisors against named rectangular contractions and literal walks."""

from itertools import combinations, product
from math import lcm

from check_interchange_compressed_tableaux import fold, repeat
from check_interchange_grid_contractions import normal_path
from check_interchange_row_bounds import moving_halves
from interchange_gray_composition import check_stationary
from interchange_cylinders import generators, tensor_boundary
from interchange_subdivision import cylinder_data, stack_image
from interchange_shared_whiskers import Words
from interchange_strip_divisors import Contacts, Pad, Slice, coordinates
from t_endomorphisms import all_extensions


def vertex(heights, width):
    ordered = (0, *reversed(heights), width)
    return Slice(tuple(reversed(range(len(heights)))),
                 tuple(b-a for a,b in zip(ordered, ordered[1:])))


def spelling(raw, rows):
    return fold(raw, [raw.letter(i) for i in rows])


def contacts(rows, initial):
    height = list(initial)
    observed = {}
    for r in rows:
        for i,j in combinations(range(len(height)), 2):
            if r not in (i,j):
                continue
            if height[i] == height[j]:
                observed[i,j] = height[j]
            if height[i] + (r == i) == height[j] + (r == j):
                observed[i,j] = height[j] + (r == j)
        height[r] += 1
    return tuple(height), tuple(sorted(observed.items()))


def check_divisors(m, n):
    maps = [{}, {}]
    total = 0
    for w in all_extensions(tuple(range(m)), tuple(range(n))):
        ambient = normal_path(w)
        for k in range(len(w) + 1):
            for reverse in (0,1):
                part = w[k:] if reverse else w[:k]
                labels = ([m-1-r for r,_ in reversed(part)] if reverse else [r for r,_ in part])
                obs = contacts(labels, (0,)*m)
                # Collisions matter only between divisors of the same value.
                fwd, back = maps[reverse].setdefault(ambient, ({}, {}))
                value = normal_path(part)
                assert fwd.setdefault(obs, value) == value
                assert back.setdefault(value, obs) == obs
                total += 1
    print(f'{m}x{n}: {total} divisors across {len(maps[0])} ambient normal forms.')


def test_transitions():
    checked = 0
    raw = Words()
    pads = []
    m, n = 3, 3
    # Clip at every pair of symbol boundaries: a padded local history may
    # touch a stationary row outside its window but never advances it.
    for w in all_extensions(tuple(range(m)), tuple(range(n))):
        heights = [0]*m
        for i in range(len(w)):
            if i:
                heights[w[i-1][0]] += 1
            lower = []
            v = vertex(heights, n)
            for run, mark in zip(v.runs, (*v.marks, None)):
                lower.extend([None]*run)
                if mark is not None:
                    lower.append(mark)
            def piece(lo, hi):
                marks, runs = [], [0]
                for x in lower[lo:hi]:
                    if x is None:
                        runs[-1] += 1
                    else:
                        marks.append(x)
                        runs.append(0)
                return Slice(tuple(marks), tuple(runs))
            for a,b in combinations(range(len(lower)+1), 2):
                pre, local, post = piece(0,a),piece(a,b),piece(b,len(lower))
                word, current = [], lower[a:b].copy()
                for r,_ in w[i:]:
                    if r not in current:
                        break
                    idx = current.index(r)
                    if idx+1 == len(current) or current[idx+1] is not None:
                        break
                    current[idx:idx+2] = (None, r)
                    word.append(r)
                    pads.append((pre, post, Pad(local, spelling(raw,word)), tuple(heights), tuple(word)))
    for reverse in (False, True):
        for pair in combinations(range(m),2):
            for mod in (2,5):
                reader = Contacts(raw,pair,mod,reverse)
                for pre,post,pad,h,word in set(pads):
                    expected_word = tuple(m-1-r for r in reversed(word)) if reverse else word
                    heights = (tuple(n-h[r]-word.count(r) for r in reversed(range(m)))
                               if reverse else h)
                    _, seen = contacts(expected_word, heights)
                    key = tuple(m-1-r for r in reversed(pair)) if reverse else pair
                    expected = dict(seen).get(key)
                    state,_ = reader.run((Slice(),Slice(),7), ('flank',pre,post))
                    result,_ = reader.run(state, ('strip',pad))
                    assert result[2] == (7 if expected is None else expected % mod)
                    checked += 1
    print(f'{checked} directional transitions agree with individually placed moving symbols.')


def test_rigid():
    raw = Words()
    rules = [('head',7,'positional middle comparison')]
    def add(*rule):
        rules.append(rule)
        return len(rules)-1
    def sweep(n, by_row):
        u,d = raw.letter(0), raw.letter(1)
        return (raw.join(repeat(raw,u,n), repeat(raw,d,n)) if by_row
                else repeat(raw,raw.join(u,d),n))
    def block(node, width, offset, length, by_row):
        # Embed a loop on 'length' adjacent moving occurrences, and complete
        # both sides to the full width at the base rank.
        end = width-offset-length
        node = add('flank', Slice(runs=(offset,)), node, Slice(runs=(end,)))
        left = Pad(vertex((0,0),width), sweep(offset,by_row))
        right = Pad(vertex((offset+length,)*2,width), sweep(end,by_row))
        return add('strip',left,node,right)
    simple = add('strip',Pad(vertex((0,0),2),raw.letter(0)),0,
                 Pad(vertex((2,1),2),raw.letter(1)))
    width, a, b = 2, simple, simple
    for _ in range(4):
        old = width
        width *= 2
        halves = [(block(x,width,0,old,order),block(x,width,old,old,order))
                  for x,order in ((a,False),(b,True))]
        a,b = (add('join',*v) for v in halves)
    opposite = add('join',*halves[1][::-1])
    # A much larger width at positive offsets, with both initial flanks
    # nonempty. Different spellings are equal in both enclosing base pads.
    huge = 2**88+29
    offset = huge//3
    x = block(simple,huge,offset,2,False)
    y = block(simple,huge,offset,2,True)
    z = block(simple,huge,offset+6,2,True)
    for limit,roots in ((width,(a,b,opposite)), (huge,(x,y,z))):
        first, equal, distinct = roots
        found = False
        for code,initial in coordinates(rules,raw,(0,1),limit,6):
            assert code.equal_coordinate(first,equal,initial)
            found |= not code.equal_coordinate(first,distinct,initial)
        assert found
    print(f'Rigid comparisons distinguish order on {width//2} sites and placement at width {huge}.')


def test_visible_mass():
    # These are proper old right-variable cylinders. Their two positive
    # subdivisions change the spelling but conserve its moving coordinate.
    cuts = 0
    for p, moving, stationary in product((4,5,6), (2,3,4), (2,3)):
        direct = cylinder_data(p,1)[0]
        direct = stack_image(stack_image(direct,p,1,0,moving),1,0,0,stationary)
        mass = len(direct[p+1][0])
        assert mass == moving*stationary
        for i in range(1,moving):
            parts = [stack_image(z,1,0,0,stationary) for z in moving_halves(p,1,i,moving)]
            assert [len(z[p+1][0]) for z in parts] == [(moving-i)*stationary,i*stationary]
            cuts += 1
        for i in range(1,stationary):
            parts = [stack_image(z,p,1,0,moving) for z in check_stationary(p,1,i,stationary)]
            assert [len(z[p+1][0]) for z in parts] == [moving*i,moving*(stationary-i)]
            cuts += 1
    # The refinement uses unequal masses. Erasing all but one column of
    # each slab recovers the quotient, including nonexpanding schedules.
    words = all_extensions((0,1,2),(0,1,2))
    for widths in ((1,2,1),(3,2,4)):
        forward, backward = {}, {}
        for word in words:
            refined = tuple((r,cc) for r,c in word for cc in
                            reversed(range(sum(widths[:c]),sum(widths[:c+1]))))
            source, value = normal_path(word), normal_path(refined)
            assert forward.setdefault(source,value) == value
            assert backward.setdefault(value,source) == source
        assert len(forward) > 1
    print(f'{cuts} native right-variable subdivisions conserve visible mass; unequal column refinements reflect all 3x3 schedule classes.')


def test_gap_projections():
    # Named old spans are 0,1,2 and fresh slots are 3,4,5. A lower left
    # unary has one or more moving grade units carrying old-span charges;
    # a stationary slot must lie strictly after each active moving span.
    # 'right' and '#' represent old right-variable and rigid occurrences.
    layers = ((0,None), (1,None), (None,None), (2,None))
    gap_words = ((('left',(None,),(0,)), ('right',2)),
                 (('left',(0,),(1,)), ('left',(None,),(1,))),
                 (('right',3),),
                 (('left',(1,),(2,)),))
    spans = (0,1,None,2)

    def wt(letter):
        if letter[0] == 'left':
            return len(letter[1])*len(letter[2])
        return letter[1]

    old, layer_at = [], [layers[0]]
    for g, part in enumerate(gap_words):
        for x in part:
            old.append(x)
            layer_at.append(layers[g])
        if g+1 < len(layers):
            old.append(('#',1))
            layer_at.append(layers[g+1])

    def read(word, span):
        result = []
        for x in word:
            if x[0] == '#':
                result.append('#')
            elif x[0] == 'right':
                result.extend('M'*wt(x))
            else:
                _, moving, stationary = x
                scalar = (0 if span is None else
                          len(moving)*sum(s <= span for s in stationary))
                mark = len(moving) if span is None else moving.count(span)
                marks = [s for s in stationary if s >= 3 for _ in range(mark)]
                assert not (scalar and marks)
                result.extend('M'*scalar)
                result.extend(marks)
        return result

    def state(cuts):
        path = []
        for i in range(len(old)+1):
            for j in reversed(range(len(cuts))):
                if cuts[j] == i:
                    path.append(('left',layer_at[i],(3+j,)))
            if i < len(old):
                path.append(old[i])
        return path

    sizes = [0]
    for x in old:
        sizes.append(sizes[-1]+wt(x))
    tested = 0
    for a,b,c in product(range(len(old)+1), repeat=3):
        if a < b or b < c:
            continue
        cuts = (a,b,c)
        path = state(cuts)
        skeleton = read(path,None)
        for j,offset in enumerate(cuts):
            slot = 3+j
            pos = skeleton.index(slot)
            g = skeleton[:pos].count('#')
            trace = read(path,spans[g])
            # The selected span always has positive weight in this gap.
            pos = trace.index(slot)
            assert trace[:pos].count('#') == g
            since = next((i+1 for i in reversed(range(pos)) if trace[i]=='#'),0)
            begin = 0 if not g else [i+1 for i,x in enumerate(old) if x[0]=='#'][g-1]
            assert sizes[begin] + trace[since:pos].count('M') == sizes[offset]
            tested += 1

    # In a binary expansion of a lower left unary whose stationary list
    # visits old and fresh spans, both cut orders have the same images.
    # Discard the relative order of adjacent vector entries, as in the
    # free product. Every permitted support and every internal cut is tried.
    def normal(trace):
        out = []
        for x in trace:
            if isinstance(x,int):
                if not out or not isinstance(out[-1],list):
                    out.append([])
                out[-1].append(x)
            else:
                out.append(x)
        return [sorted(x) if isinstance(x,list) else x for x in out]
    subdivisions = 0
    for support in (None,0,1,2):
        for lo in range(0 if support is None else support+1,5):
            for hi in range(lo+2,7):
                stationary = tuple(range(lo,hi))
                moving = (support,None,support)
                def head(m,b):
                    return ('left',m,b)
                direct = [head(moving,stationary)]
                for span in spans:
                    target = normal(read(direct,span))
                    for i in range(1,len(moving)):
                        parts = [head(moving[:i],stationary),head(moving[i:],stationary)]
                        assert normal(read(parts,span)) == target
                        subdivisions += 1
                    for i in range(1,len(stationary)):
                        parts = [head(moving,stationary[:i]),head(moving,stationary[i:])]
                        assert normal(read(parts,span)) == target
                        subdivisions += 1
    print(f'{tested} slot positions reconstructed across changing rigid faces; {subdivisions} projected lower subdivisions checked.')


def test_gray_span_weights():
    interval = ((),())
    surface = (interval,(),interval)
    solid = (surface,interval)
    four = (solid,surface)
    tested = 0
    for shape in ((four,solid), (surface,interval,solid), (interval,)*4):
        for basis in product(*(generators(x) for x in shape)):
            if sum(len(x)-1 for x in basis) != 4:
                continue
            for s in range(len(shape)):
                assert sum(sign for term,sign in tensor_boundary(basis)
                           if len(term[s]) > 1) == 0
                tested += 1
    # At moving rank five the preceding r on a positive 3-hemisphere
    # reaches every stationary edge. Inspect the two actual rank-four
    # faces and the intermediate face of both native subdivisions.
    for n,m in product(range(2,5), repeat=2):
        variants = [stack_image(z,1,1,0,m) for z in moving_halves(3,0,1,n)]
        variants += [stack_image(z,3,0,0,n) for z in check_stationary(3,0,1,m)]
        for z in variants:
            for chain in z[3]:
                assert sorted(j for _,(d,j) in chain if d) == list(range(m))
    print(f'{tested} span-weight differential evaluations vanish; both rank-five cylinder cuts retain all old stationary marks.')


def test_contacts_needed():
    raw = Words()
    rules = [('head',7,'formal loop on last corner')]
    # Leave the final D as the common carrier of a formal upper loop.
    n = 2**61+7
    u,d = raw.letter(0),raw.letter(1)
    end = Pad(vertex((n,n),n), 0)
    first = raw.join(repeat(raw,u,n),repeat(raw,d,n-1))
    second = raw.join(repeat(raw,raw.join(u,d),n-1),u)
    for word in (first,second):
        rules.append(('strip',Pad(vertex((0,0),n),word),0,end))
    found = set()
    for code, initial in coordinates(rules,raw,(0,1),n,6):
        if not code.equal_coordinate(1,2,initial):
            found.add((type(code.reader).__name__,code.reverse))
    assert found == {('Contacts',False)}
    for bits in range(1,150):
        assert lcm(*range(2,2*(bits+2)+1)) > 2**bits
    print('Only left contacts distinguish the equal-count formal placements at width 2^61+7.')


if __name__ == '__main__':
    for shape in ((2,6),(3,3),(3,4)):
        check_divisors(*shape)
    test_transitions()
    test_rigid()
    test_contacts_needed()
    test_visible_mass()
    test_gap_projections()
    test_gray_span_weights()
