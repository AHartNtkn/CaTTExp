"""Decide degree-four and degree-five comparisons for two unary-labelled Gray columns."""
import argparse
from itertools import combinations, product


def cut_order(left, right):
    """Number of left/right label steps made before the unique crossing."""
    return left[0] <= right[0] and left[1] >= right[1]


def shuffles(l, r):
    for positions in combinations(range(l+r),l):
        selected=set(positions)
        yield ''.join('L' if i in selected else 'R' for i in range(l+r))


def pair_bits(w):
    rights=w.count('R')
    return frozenset((i,j) for i,k in enumerate(pos for pos,c in enumerate(w) if c=='L')
                     for j in range(w[:k].count('R'),rights))


def steps(w):
    for i in range(len(w)-1):
        if w[i:i+2]=='RL':
            yield i,w[:i]+'LR'+w[i+2:]


def shuffle_path(w,v):
    if any(c not in 'LR' for c in w+v) or sorted(w)!=sorted(v):
        return None
    if not pair_bits(w)<=pair_bits(v):
        return None
    path=[]
    for i,c in enumerate(v):
        if w[i]==c:
            continue
        assert c=='L'
        j=w.index('L',i)
        while j>i:
            j-=1
            assert w[j:j+2]=='RL'
            w=w[:j]+'LR'+w[j+2:]
            path.append(j)
    assert w==v
    return path


def weighted_cost(w,marked_l,marked_r):
    # Selected right changes occur on their strand in reverse slide order.
    i, j, g = 0, 0, 0
    for slide in w:
        if slide=='L':
            if i==marked_l:
                g+=int(j<=marked_r)
            i+=1
        else:
            if j==marked_r:
                g+=int(i>marked_l)
            j+=1
    return g


def square_connected(paths):
    """Top paths agree by interchange of moves on disjoint slide pairs."""
    unseen=set(paths)
    todo=[unseen.pop()]
    while todo:
        p=todo.pop()
        for i,(a,b) in enumerate(zip(p,p[1:])):
            if abs(a-b)>1:
                q=p[:i]+(b,a)+p[i+2:]
                if q in unseen:
                    unseen.remove(q)
                    todo.append(q)
    return not unseen


def checks():
    cut_pairs=schedules=top_paths=0
    for l,r in product(range(5),repeat=2):
        cuts=list(product(range(l+1),range(r+1)))
        words=list(shuffles(l,r))
        for a in cuts:
            reach={a}
            todo=[a]
            while todo:
                i,j=todo.pop()
                for b in ((i+1,j),(i,j-1)):
                    if b in cuts and b not in reach:
                        reach.add(b)
                        todo.append(b)
            for b in cuts:
                assert (b in reach)==cut_order(a,b)
                cut_pairs+=1
        for u in words:
            costs=pair_bits(u)
            for i,j in product(range(l),range(r)):
                assert weighted_cost(u,i,j)==2*((i,j) in costs)
            paths={u:[()]}
            for w in sorted(words,key=lambda t:len(pair_bits(t))):
                if w not in paths:
                    continue
                for i,v in steps(w):
                    if l<=3 and r<=3:
                        paths.setdefault(v,[]).extend(p+(i,) for p in paths[w])
                    else:
                        paths.setdefault(v,[()])
            for v in words:
                cert=shuffle_path(u,v)
                assert (cert is not None)==(v in paths)
                schedules+=1
                if v in paths and l<=3 and r<=3:
                    assert square_connected(paths[v])
                    top_paths+=len(paths[v])
    print(f'{cut_pairs} cut comparisons, {schedules} slide schedule comparisons, '
          f'{top_paths} top pastes joined by distant moves')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cuts',nargs=4,type=int,metavar=('L','R','L2','R2'))
    ap.add_argument('--schedules',nargs=2)
    args=ap.parse_args()
    if args.cuts:
        print('raw and surface',cut_order(args.cuts[:2],args.cuts[2:]))
    elif args.schedules:
        print('directed adjacent swaps',shuffle_path(*args.schedules))
    else:
        checks()
