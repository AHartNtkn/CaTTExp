"""Track decorated gate positions through actual exchanges of two planar lenses."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_weight_cut import Selector

RULES = {'B': ('','ab'), 'X': ('',''), 'D': ('ab','')}
ROOT = (('B',0), ('X',1), ('D',0))*2
ID = tuple(range(len(ROOT)))
SWAP = ID[3:]+ID[:3]


def switch(w, i):
    return w[:i]+(w[i+1],w[i])+w[i+2:]


@cache
def steps(word):
    options = []
    for k, ((a,i),(b,j)) in enumerate(zip(word,word[1:])):
        p,q = map(len,RULES[a])
        r,s = map(len,RULES[b])
        if j+r <= i:
            pair = ((b,j),(a,i+s-r))
            options.append((k,1,word[:k]+pair+word[k+2:]))
        if i+q <= j:
            pair = ((b,j-q+p),(a,i))
            options.append((k,-1,word[:k]+pair+word[k+2:]))
    return options


def validate(word):
    path = ''
    for g,i in word:
        src,tgt = RULES[g]
        assert 0 <= i <= len(path)-len(src) and path.startswith(src,i)
        # a : s -> t and b : t -> s. A point X lives at t and B at s.
        if g in ('B','X'):
            assert (i > 0 and path[i-1] == 'a') == (g == 'X')
        path = path[:i]+tgt+path[i+len(src):]
    assert path == ''


def cover():
    state = ROOT,ID
    queue = deque([state])
    # Track the signed crossings of the two birth gates on each tree lift.
    exponent = {state: 0}
    while queue:
        w, ids = queue.popleft()
        validate(w)
        for k,sign,u in steps(w):
            after = u,switch(ids,k)
            n = exponent[w,ids] + (sign if w[k][0] == w[k+1][0] == 'B' else 0)
            if after not in exponent:
                exponent[after] = n
                queue.append(after)
    assert {ids for w,ids in exponent if w == ROOT} == {ID,SWAP}
    words = {w for w,_ in exponent}
    assert len(exponent) == 2*len(words)
    turn = exponent[ROOT,SWAP]
    assert abs(turn) == 1
    print('serial words',len(words),'distinctly tagged words',len(exponent),
          'birth crossing on component exchange and square',turn,2*turn)
    return words


def coloured_components(words):
    # Quotient actual two-colour schedules, independent of the tagged cover.
    unvisited = {(w,tags) for w in words for tags in product(range(2),repeat=len(w))}
    roots = []
    while unvisited:
        first = unvisited.pop()
        queue = [first]
        initial = set()
        while queue:
            w,tags = queue.pop()
            if w == ROOT:
                initial.add(tags)
            for i,_,u in steps(w):
                after = u,switch(tags,i)
                if after in unvisited:
                    unvisited.remove(after)
                    queue.append(after)
        t = next(iter(initial))
        assert initial == {t,t[3:]+t[:3]}
        roots.append(len(initial))
    assert sorted(roots) == [1]*8+[2]*28
    print('two-colour components',len(roots),'fixed colourings',roots.count(1))


def update_test(words):
    # On tagged input gates, children are free paths in two noncommuting
    # letters. Check the square moving an actual child update past each edge.
    tested = 0
    for w in words:
        old = tuple(str(i) for i in range(len(w)))
        for i,_,u in steps(w):
            for j in range(len(w)):
                first = list(old)
                first[j] += 'UV'
                second = list(switch(old,i))
                pos = switch(ID,i).index(j)
                second[pos] += 'UV'
                assert switch(tuple(first),i) == tuple(second)
                if pos != j:
                    assert second[pos] != old[j]+'VU'
                tested += 1
    print('gate updates transported over signed edges',tested)


def child_word(term):
    if term[0] == 'v':
        return (term[1],)
    _, arity, _, labels = term
    # A raw 1-head traverses the directed spine of its linear pasting arity.
    return tuple(letter for ty,label in zip(arity,labels,strict=True) if ty != STAR
                 for letter in child_word(label))


def typed(output):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    ab = comp2(ctx,0,comp2(ctx,0,v(2),identity(ctx,v(1))),v(3))
    unit = identity(ctx,v(0))
    ctx += (arr(infer(ctx,unit),unit,ab),arr(infer(ctx,unit),ab,unit))
    # Use two distinguished copies of the child at the inner gap of a lens.
    pole = identity(ctx,v(1))
    point = arr(infer(ctx,pole),pole,pole)
    child = (STAR,arr(STAR,v(0),v(0)),arr(STAR,v(0),v(0)))
    ctx += (point,point)
    ctx += tuple(arr(point,v(i),v(i)) for i in (6,6,7,7))
    check_ctx(ctx)
    emitter = Emitter()
    def lens(label):
        middle = comp2(ctx,0,comp2(ctx,0,v(2),label),v(3))
        return comp2(ctx,1,comp2(ctx,1,v(4),middle),v(5))

    for name,point_idx,start in [('first',6,8),('second',7,10)]:
        selector = Selector(ctx,2,{point_idx:v(0),start:v(1),start+1:v(2)})
        for a,b in [(start,start+1),(start+1,start)]:
            changes = comp2(ctx,2,v(a),v(b))
            # At weak poles the inserted unit edge stays in the intervening path.
            other = v(7 if point_idx == 6 else 6)
            mixed = comp2(ctx,1,lens(changes),lens(other))
            recovered = selector.read(mixed)
            expected = selector.boundary(infer(ctx,mixed))
            assert infer(child,recovered) == expected
            letters = (1,2) if a == start else (2,1)
            assert child_word(recovered) == letters
            if output and a == start:
                emitter.check_type(name+'Mixed',ctx,mixed,infer(ctx,mixed))
                emitter.check_type(name+'Read',child,recovered,expected)
    if output:
        (output/'BraidedPlanarSubstitution.agda').write_text(
            emitter.module('BraidedPlanarSubstitution',__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    words = cover()
    coloured_components(words)
    update_test(words)
    typed(args.agda_dir)
