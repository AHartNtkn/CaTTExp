"""Check simultaneous tetrahedron exchanges on the twelve signed simplex slices."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import (arr, comp2, fv_tm, fv_ty, infer, maximal_vars, restrict, src, sub_from,
                  subst_tm, subst_ty, tgt, tree_ctx, v)
from emit_agda import Emitter
from rc2 import kappa
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, head, hexagon, steps, string_tree
from relative_coherence_simplex_sweeps import FlagSimplex, POINTS
from relative_coherence_tree_folds import weak_three_skeleton


def interval(flag, label):
    """Enumerate every legal prefix and check its producer-consumer order."""
    initial, final = map(frozenset, label[2])
    events = frozenset(label[3][0])
    assert len(events) == len(label[3][0])
    producers, consumers = {}, {}
    for z in events:
        a, b = flag.atom(z)[2]
        for owner, side in ((producers,b), (consumers,a)):
            for triangle in side:
                assert triangle not in owner
                owner[triangle] = z
    assert initial.isdisjoint(producers) and final.isdisjoint(consumers)
    assert set(producers)-set(consumers) == final-initial
    assert set(consumers)-set(producers) == initial-final
    predecessors = {z: {producers[t] for t in flag.atom(z)[2][0] if t in producers} for z in events}
    states = {}

    def visit(done, state):
        if done in states:
            assert states[done][0] == state
            return states[done][2]
        ready = []
        for z in sorted(events-done):
            a,b = map(frozenset, flag.atom(z)[2])
            if a <= state and not b & state:
                ready.append(z)
        assert set(ready) == {z for z in events-done if predecessors[z] <= done}
        if not ready:
            assert done == events and state == final
        words = 0
        for z in ready:
            a,b = map(frozenset, flag.atom(z)[2])
            words += visit(done | {z}, (state-a) | b)
        states[done] = state, ready, words or 1
        return words or 1

    count = visit(frozenset(), initial)
    return states, count


def path_word(flag, edges):
    # The order of one-atoms is the order of their sources on the first-coordinate line.
    word = tuple(sorted(edges))
    assert all(flag.atom(p)[0][1] == flag.atom(q)[0][0] for p,q in zip(word, word[1:]))
    return word


def joint_layers(flag, label, state, events):
    """Replace all designated tetrahedron inputs by marked layers in one two-diagram."""
    remaining = set(state)
    for z in events:
        a,b = flag.atom(z)[2]
        assert set(a) <= remaining
        remaining.difference_update(a)
    remaining.update(events)
    current, final = [path_word(flag, side) for side in label[1]]
    layers = []
    while remaining:
        choices = []
        for z in remaining:
            a,b = [path_word(flag, side) for side in flag.atom(z)[1]]
            for i in range(len(current)-len(a)+1):
                if current[i:i+len(a)] == a:
                    choices.append((z, current[:i], current[i+len(a):], b))
        z, left, right, b = min(choices)
        remaining.remove(z)
        next_word = left+b+right
        layers.append((z,left,right,current,next_word))
        current = next_word
    assert current == final
    for k in range(len(events)+1):
        for fired in combinations(events,k):
            expected = Counter(state)
            for z in fired:
                expected.update(flag.d[z])
            actual = Counter()
            for z,*_ in layers:
                actual.update(flag.atom(z)[2][z in fired] if z in events else [z])
            assert actual == expected
    return tuple(layers)


@cache
def comparison(dimensions):
    arity = tree_ctx(string_tree(1, dimensions))
    rows = list(map(v, maximal_vars(arity)))
    if dimensions == (3,3,3):
        p, forward = hexagon()
        assert arity == p
        a,b = infer(p,forward)[2:]
    else:
        order = [i for i,d in enumerate(dimensions) if d == 3]
        assert len(order) == 2
        a,b = [composite(arity,2,steps(arity,rows,which)) for which in (order,order[::-1])]
        forward = head(arity,a,b)
    return arity, forward, head(arity,b,a)


def local_substitution(ctx, atoms, layers, arity):
    def path(word):
        return comp2(ctx,0,atoms[word[0]],path(word[1:])) if len(word)>1 else atoms[word[0]]

    slots = []
    for z,left,right,before,after in layers:
        t = atoms[z]
        if left:
            t = comp2(ctx,0,path(left),t)
        if right:
            t = comp2(ctx,0,t,path(right))
        a,b = infer(ctx,t)[2:]
        if len(z) == 4:
            a,b = src(ctx,a),tgt(ctx,b)
        if a != path(before):
            t = comp2(ctx,1,kappa(ctx,path(before),a),t)
        if b != path(after):
            t = comp2(ctx,1,t,kappa(ctx,b,path(after)))
        slots.append(t)
    sigma = sub_from(arity,ctx,dict(zip(maximal_vars(arity),slots)))
    for ty,t in zip(arity,sigma):
        assert infer(ctx,t) == subst_ty(ty,sigma)
    return sigma


def emit_hexagon(file, ctx, arity, sigma, forward, reverse):
    # Only the dependency closure is needed to check the oriented actual substitution.
    keep = set().union(*(fv_tm(t) for t in sigma))
    for i in reversed(range(len(ctx))):
        if i in keep:
            keep.update(fv_ty(ctx[i]))
    small, incl = restrict(ctx,keep)
    ren = tuple(v(sorted(keep).index(i)) if i in keep else None for i in range(len(ctx)))
    restricted = tuple(subst_tm(t,ren) for t in sigma)
    assert tuple(subst_tm(t,incl) for t in restricted) == tuple(sigma)
    em = Emitter()
    target, source = em.ctx(small), em.ctx(arity)
    sub = em.sub(restricted)
    em.checks.extend(['open import CaTTExp.PureMetatheory using (tm[])',
        f'labels : {target} ⊢sub {sub} ∶ {source}',
        f'labels = from-just (checkSub {target} (from-just (checkCtx {target})) {sub} {source})'])
    for name, term in [('forward',forward), ('reverse',reverse)]:
        t, ty = em.tm(term), em.ty(infer(arity,term))
        em.checks.extend([f'{name} : {target} ⊢tm {t} [ {sub} ]tm ∶ {ty} [ {sub} ]ty',
                          f'{name} = tm[] (snd (from-just (infer {source} {t}))) labels'])
    file.write_text(em.module(file.stem, 'Two directions of the actual simplex braid.'))


def verify(file=None):
    flag = FlagSimplex(POINTS)
    flag.check()
    ctx, atoms = weak_three_skeleton(flag)
    top = flag.atom(flag.vertices)
    paths = [flag.sweep(side,*top[4]) for side in top[5]]
    fronts = {q for p in paths for a,_,b in p for q in (a,b)}
    labels = sorted({s for fr in fronts for s in flag.all_slices(fr,top[3])
                     if len({i for row in (*top[:3],(s,s)) for side in row for cell in side for i in cell}) == 7})
    counts, forks, triples = [], Counter(), []
    checked = set()
    for i,row in enumerate(labels,1):
        q = top[:3] + ((row,row),)
        states,num_words = interval(flag,q)
        counts.append(num_words)
        for state,ready,_ in states.values():
            for size in range(2,len(ready)+1):
                for group in combinations(ready,size):
                    layers = joint_layers(flag,q,state,group)
                    forks[size] += 1
                    if size == 3:
                        triples.append((i,layers))
                    if layers in checked:
                        continue
                    checked.add(layers)
                    dims = tuple(len(z)-1 for z,*_ in layers)
                    arity, forward, reverse = comparison(dims)
                    sigma = local_substitution(ctx,atoms,layers,arity)
                    a,b = (subst_tm(t,sigma) for t in infer(arity,forward)[2:])
                    assert infer(arity,reverse)[2:] == infer(arity,forward)[2:][::-1]
                    if size == 2:
                        assert top_counts(ctx,a) == top_counts(ctx,b) == Counter(atoms[z][1] for z in group)
                    if size == 3:
                        for t,start,end in ((forward,a,b),(reverse,b,a)):
                            assert infer(ctx,subst_tm(t,sigma)) == arr(infer(ctx,start),start,end)
                        if file:
                            emit_hexagon(file,ctx,arity,sigma,forward,reverse)
    assert counts == [25,48,12,30,24,33,32,21,78,31,2,5]
    assert forks == {2:86,3:2}
    assert [i for i,_ in triples] == [8,10] and triples[0][1] == triples[1][1]
    print('Serializations per label:', *counts)
    print(f'86 pair forks and two triple forks; {len(checked)} distinct joint substitutions.')
    print('Slices 8 and 10 use one typed five-dimensional braid in both directions.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit the specialized forward and reverse braid judgments')
    verify(parser.parse_args().agda)
