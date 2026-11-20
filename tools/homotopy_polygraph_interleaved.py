"""Classify arbitrary interleavings with at most one release resource after an acquisition."""

from itertools import combinations_with_replacement, product

from homotopy_polygraph_mask_catalogue import catalogue
from homotopy_polygraph_monotone import axes_at, record_homology
from homotopy_polygraph_one_destination import polynomial, sphere_factors
from homotopy_polygraph_parking import acquisition_before_release


def split_axis(axis):
    """Separate departures after the sole arrival from those with a path to it."""
    constant = axis[0] & axis[-1]
    arrivals = axis[-1] & ~constant
    tails = axis[0] & ~constant
    # Before the first departure every arrival has no incoming comparison.
    before = next((old for old,new in zip(axis,axis[1:]) if old & ~new), axis[-1])
    free_arrivals = arrivals & before
    head = arrivals & ~free_arrivals
    if head.bit_count() > 1:
        raise ValueError("more than one arrival resource after a departure")
    early = tails
    if head:
        at_arrival = next(mask for mask in axis if mask & head)
        late = tails & at_arrival
        early &= ~late
    else:
        late = 0
    free_heads = tuple((0,1<<r) for r in range(free_arrivals.bit_length()) if free_arrivals & (1<<r))
    return ((constant | early, constant | head), (late, 0), *free_heads)


def interleaved_factors(axes, resources):
    split = [part for axis in axes for part in split_axis(axis)]
    return sphere_factors(split,resources)


def whole_interleaved(controls, resources):
    options = []
    for states, edges in controls:
        releases = {op for _,op,_ in edges if op is not None and op[0]=='V'}
        for v in releases:
            p = ('P',v[1])
            if acquisition_before_release(edges,p,v) or acquisition_before_release(edges,v,p):
                raise ValueError("one resource is both acquired and released")
        outgoing = {s:[] for s in states}
        for s,op,t in edges:
            outgoing[s].append((op,t))
        # Starting just after any acquisition, remember the first released name.
        pending = [(t,None) for _,op,t in edges if op and op[0]=='P']
        seen = set(pending)
        while pending:
            here, prior = pending.pop()
            for op,t in outgoing[here]:
                head = prior
                if op and op[0]=='V':
                    if head is not None and head != op[1]:
                        raise ValueError("two release resources follow an acquisition")
                    head = op[1]
                if (t,head) not in seen:
                    seen.add((t,head))
                    pending.append((t,head))
        options.append({split_axis(axis) for axis in catalogue(states,edges,resources)})
    for selections in product(*options):
        factors = sphere_factors([axis for pair in selections for axis in pair],resources)
        if factors and max(factors)>0:
            return False, selections
    return True, None


def check():
    types = [
        ((('P',0),('V',1)),(0,1)), ((('P',1),('V',0)),(1,0)),
        ((('V',1),('P',0)),(0,1)), ((('V',0),('P',1)),(1,0)),
        ((('V',1),('P',0),('V',1)),(0,2)), ((),(1,1)),
    ]
    count = 0
    for choices in combinations_with_replacement(types,4):
        words,initial = zip(*choices)
        axes = axes_at(words,initial)
        dims = interleaved_factors(axes,2)
        h0,higher = record_homology(axes,2)
        assert not any(torsion for _,torsion in higher)
        assert ((h0,*(rank for rank,_ in higher)) if h0 else ()) == polynomial(dims)
        count += 1
    print(f'{count} interleaved records agree with the signed witness-product homology.')
    fwd = [types[0]]*2+[types[1]]*2
    rev = [types[2]]*2+[types[3]]*2
    axes = [axes_at(*zip(*family)) for family in (fwd,rev)]
    assert [(x[0],x[-1]) for x in axes[0]] == [(x[0],x[-1]) for x in axes[1]]
    assert [interleaved_factors(a,2) for a in axes] == [(1,),()]
    def controls(family):
        return [(range(len(word)+1),[(i,op,i+1) for i,op in enumerate(word)]) for word,_ in family]
    assert not whole_interleaved(controls(fwd),2)[0]
    assert whole_interleaved(controls(rev),2)[0]
    print('Identical endpoint masks: P-before-V gives a circle; V-before-P gives a point.')

    words = [[('V',2),('P',0),('V',2),('P',1)], [('P',2),('V',0)],
             [('P',2),('V',0)], [('P',0),('V',2)]]
    holds = [(0,0,2),(1,1,0),(1,1,0),(0,1,1)]
    # An extra arrival supplies the late-tail guard; the core obstruction persists.
    words.append([('V',1)])
    holds.append((1,1,1))
    a = axes_at(words,holds)
    dims = interleaved_factors(a,3)
    assert dims == (1,) and record_homology(a,3) == (1,((1,()),))
    print('A release/acquire/release/acquire axis with an early and a late tail gives H1 = Z.')
    words[0] = [('V',3)]+words[0]
    holds = [(*row,1) for row in holds]
    words.append([('P',3)])
    holds.append((1,1,1,0))
    a = axes_at(words,holds)
    assert interleaved_factors(a,4) == (1,) and record_homology(a,4) == (1,((1,()),))
    print('An additional initial release on a different guarded resource preserves the circle.')


if __name__ == '__main__':
    check()
