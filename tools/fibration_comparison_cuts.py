"""Factor a positive three-cell's comparison space using actual gate ancestry."""

from functools import cache

from fibration_factor_search import Rule, Stage
from fibration_three_comparison import comparison_groups, unary_signature


def reserialize(stage, named, wanted):
    """Transport occurrence tags to the specified serialization of a strict 2-cell."""
    kinds = {tag:g for g, _, tag in named}
    coloured = Stage(stage.arrows, {tag:stage.rules[g] for tag,g in kinds.items()})
    p = tuple((tag, i) for g,i,tag in named)
    todo, seen = [p], {p}
    while todo:
        p = todo.pop()
        if tuple((kinds[tag],i) for tag,i in p) == wanted:
            return [(kinds[tag],i,tag) for tag,i in p]
        for alt in coloured.exchanges(p):
            if alt not in seen:
                seen.add(alt)
                todo.append(alt)
    raise ValueError('The context starts at a different strict 2-cell')


def compare_in_blocks(stage, disks, vertex, word, start, history):
    """History entries consist of the generator label and its one-hole 2-context."""
    named = [(g,i,(-1,j)) for j,(g,i) in enumerate(start)]
    ancestry = []
    states = [start]
    for current,(label,ctx) in enumerate(history):
        _,_,s,t = disks[label]
        if not s or not t:
            raise ValueError('Gate ancestry requires nonidentity top faces')
        site, = (j for j,(g,i) in enumerate(ctx) if g is None)
        offset = ctx[site][1]
        expanded = ctx[:site]+tuple((g,offset+i) for g,i in s)+ctx[site+1:]
        named = reserialize(stage,named,expanded)
        parents = {tag[0] for g,i,tag in named[site:site+len(s)] if tag[0] >= 0}
        prior = parents.copy()
        for parent in parents:
            prior.update(ancestry[parent])
        ancestry.append(prior)
        inserted = [(g,offset+i,(current,j)) for j,(g,i) in enumerate(t)]
        named[site:site+len(s)] = inserted
        states.append(tuple((g,i) for g,i,tag in named))

    # A cut cannot move if each event on the left precedes each one on the right.
    cuts = [0]
    for j in range(1,len(history)):
        if all(all(i in prior for i in range(j)) for prior in ancestry[j:]):
            cuts.append(j)
    cuts.append(len(history))

    @cache
    def piece(before, after, steps):
        events = tuple(g for g,_ in steps)
        canon = []
        for label, ctx in steps:
            v,w,s,_ = disks[label]
            out = tuple(stage.slices(v,w,s))[-1]
            canon.append(unary_signature(stage,label,None,Rule(v,w,out),ctx))
        matches = [item for item in comparison_groups(stage,disks,vertex,word,before,after,events)
                   if tuple(canon) in item[0]]
        if len(matches) != 1:
            raise ValueError('Expected one strict component for the supplied writing')
        serial, generators, relations, incidence = matches[0]
        return len(serial), len(generators), tuple(relations), incidence

    return [(b-a,piece(states[a],states[b],tuple(history[a:b]))) for a,b in zip(cuts,cuts[1:])]


def check(wide, repeats):
    stage = Stage({c:('x','x') for c in 'fFghH'}, {g:Rule('x',s,t) for g,s,t in
                  [('a','f','F'),('b','f','F'),('p','h','H'),('q','h','H')]})
    ab, bq = (('a',0),('p',2)), (('b',0),('q',2))
    disks = {'A':('x','fg' if wide else 'f',(('a',0),),(('b',0),)),
             'B':('x','gh',(('p',1),),(('q',1),)),
             'C':('x','fgh',bq,ab)}
    h = [('A',((None,0),('p',2))), ('B',(('b',0),(None,1))), ('C',((None,0),))]
    blocks = compare_in_blocks(stage,disks,'x','fgh',ab,h*repeats)
    assert len(blocks) == 2*repeats
    assert all(size == (2 if i%2 == 0 else 1) and serial == size and not rels
               and gs == int(wide and size == 2)
               for i,(size,(serial,gs,rels,_)) in enumerate(blocks))
    if repeats == 2:
        groups = comparison_groups(stage,disks,'x','fgh',ab,ab,'ABCABC')
        assert len(groups) == 1
        serial, gens, relations, _ = groups[0]
        assert len(serial) == 4
        if wide:
            # The two independent circle factors commute in the full presentation.
            assert len(gens) == 2 and len(relations) == 1
            r, = relations
            assert len(r) == 4 and set(r) == gens | {-g for g in gens}
        else:
            assert not gens and not relations
    print(f'{"Wide" if wide else "Narrow"}: {3*repeats} events in {len(blocks)} blocks, '
          f'{2**repeats} serial writings, {sum(v[1] for _,v in blocks)} circle factors.')


if __name__ == '__main__':
    for wide in (False,True):
        for n in (2,60):
            check(wide,n)
