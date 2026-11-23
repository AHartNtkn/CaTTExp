"""Sort phase words with label-change checkpoints on a distinguished middle step.

Axes 0,1,2 are in spatial order. A directed swap moves the smaller axis left.
A checkpoint (l,r) records the numbers of left and right steps before one fixed
middle occurrence when its next private label change must execute.
"""

from argparse import ArgumentParser
from collections import Counter, deque
from functools import cache
from itertools import product

from semistrict_surface_penultimate_intervals import check
from semistrict_surface_branched_comparisons import query


def tokens(axes):
    n = Counter()
    out = []
    for a in axes:
        out.append((a,n[a]))
        n[a] += 1
    return tuple(out)


def neighbours(word):
    for j,(a,b) in enumerate(zip(word,word[1:])):
        if a[0]>b[0]:
            yield word[:j]+(b,a)+word[j+2:]


def location(word,marked):
    before = Counter(a for a,_ in word[:word.index(marked)])
    return before[0],before[2]


def sort_with_changes(source,target,visits):
    """Return a replay of legal adjacent swaps and changes, or None."""
    if set(source)!=set(target) or any(m not in source or m[0]!=1 for m,_ in visits):
        raise ValueError('incompatible phase words or marked occurrence')
    w = list(source)
    end = {a:i for i,a in enumerate(target)}
    ops = []
    def swap(i):
        a,b = w[i:i+2]
        if a[0]<=b[0] or end[a]<end[b]:
            return False
        w[i:i+2] = b,a
        ops.append(i)
        return True
    # A pair of incompatible requests can be returned in the wrong order
    # by either tie break. Check it explicitly before constructing the replay.
    for i,(a,(l,r)) in enumerate(visits):
        for b,(h,k) in visits[i+1:]:
            if a==b and (l>h or r<k):
                return None
            if (a<b and l>h and r>k) or (b<a and h>l and k>r):
                return None
    for marked,(left,right) in sorted(visits,key=lambda v:v[1][0]-v[1][1]):
        l,r = location(w,marked)
        final_l,final_r = location(target,marked)
        if not (l<=left<=final_l and final_r<=right<=r):
            return None
        for _ in range(left-l):
            cut = w.index(marked)
            j = next(i for i in range(cut+1,len(w)) if w[i][0]==0)
            if not all(swap(i) for i in range(j-1,cut-1,-1)):
                return None
        for _ in range(r-right):
            cut = w.index(marked)
            j = next(i for i in range(cut-1,-1,-1) if w[i][0]==2)
            if not all(swap(i) for i in range(j,cut)):
                return None
        ops.append(('change',marked))
    for i,a in enumerate(target):
        if not all(swap(j) for j in range(w.index(a)-1,i-1,-1)):
            return None
    return ops


def reachable(source):
    seen = {source}
    queue = deque([source])
    while queue:
        for w in neighbours(queue.popleft()):
            if w not in seen:
                seen.add(w)
                queue.append(w)
    return seen


def words(counts, path=()):
    if not any(counts):
        yield tokens(path)
    for a,count in enumerate(counts):
        if count:
            step = list(counts)
            step[a] -= 1
            yield from words(step,path+(a,))


def check_words():
    checked = 0
    for counts in ((1,2,1),(2,1,1),(1,1,2),(2,2,1),(1,2,2)):
        shuffles = list(words(counts))
        after = {w:reachable(w) for w in shuffles}
        locs = list(product(range(counts[0]+1),range(counts[2]+1)))
        for marked in [(1,i) for i in range(counts[1])]:
            for u in shuffles:
                for first,second in product(locs,repeat=2):
                    at_first = {w for w in after[u] if location(w,marked)==first}
                    at_second = {v for w in at_first for v in after[w] if location(v,marked)==second}
                    targets = {v for w in at_second for v in after[w]}
                    for v in shuffles:
                        ops = sort_with_changes(u,v,[(marked,first),(marked,second)])
                        assert (ops is not None)==(v in targets)
                        if ops is not None:
                            w = list(u)
                            visits = []
                            for op in ops:
                                if isinstance(op,tuple):
                                    visits.append(location(w,marked))
                                else:
                                    a,b = w[op:op+2]
                                    assert a[0]>b[0]
                                    w[op:op+2]=b,a
                            assert tuple(w)==v and visits==[first,second]
                        checked += 1
    return checked


def multiple_changes(source,target,needs):
    @cache
    def go(w,left):
        if not left:
            return target in reachable(w)
        for j in left:
            mark,pos = needs[j]
            if location(w,mark)==pos and go(w,tuple(i for i in left if i!=j)):
                return True
        return any(go(v,left) for v in neighbours(w))
    return go(source,tuple(range(len(needs))))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--tableaux',action='store_true',help='also check all faces in two branching charts')
    args = p.parse_args()
    print(f'{check_words():,} two-checkpoint queries compared with independent directed shuffle enumeration')
    u,v = tokens([2,1,1,0]),tokens([0,1,1,2])
    assert not multiple_changes(u,v,[((1,0),(1,1)),((1,1),(0,0))])
    print('The two distinct marked occurrences of Response 117 have incompatible checkpoints.')
    if args.tableaux:
        for middle in ([[[[]],[]]],[[[],[[]]]]):
            answer = check(query([[[[]]],middle,[[[]]]]))
            assert answer=='unsat'
            print(f'All parallel tableaux verified for middle tree {middle}.')
