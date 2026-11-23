"""Decide three-strand triangle insertions and check their infinitely many positive covers."""
from argparse import ArgumentParser
from itertools import product
from math import inf

from semistrict_surface_crossing_insertion import b3_word
from semistrict_surface_monotone_braids import MODULAR, compare, cyclic
from semistrict_surface_shared_edge import inverse

TRIANGLES = [('AAA',(),(1,2)),('AAA',(),(2,1))]


def minimum_factors(signed):
    """Minimum number of conjugates of q in C2*C3, or infinity."""
    syllables = cyclic(tuple(g for x in signed for g in MODULAR[x]), {1:2,2:3})
    gaps = [0]
    for g in syllables:
        if abs(g)==1:
            gaps.append(0)
        else:
            gaps[-1] += 1 if g>0 else -1
    count = len(gaps)-1
    if count%2:
        return inf
    # dp[i,j] records the least cost of closed regions for each residue
    # on the open outside region between the gaps i and j.
    dp, closed = {},{}
    for i,gap in enumerate(gaps):
        dp[i,i] = {gap%3:0}
        closed[i,i] = gap%3
    for length in range(2,count+1,2):
        for i in range(count-length+1):
            j = i+length
            costs = {}
            for k in range(i+2,j+1,2):
                interior = closed[i+1,k-1]
                for e,exterior in dp[k,j].items():
                    residue = (gaps[i]+e)%3
                    costs[residue] = min(costs.get(residue,inf),interior+exterior)
            dp[i,j] = costs
            closed[i,j] = min(e+n for e,n in costs.items())
    return closed[0,count]


def surface(b,c):
    steps, parity = divmod(len(c)-len(b),2)
    if steps<0 or parity:
        return False
    cost = minimum_factors(c+inverse(b))
    return cost<=steps and (steps-cost)%3==0


def apply(vector, word):
    a,b = vector
    for i in word:
        if i==1:
            a += b
        else:
            b -= a
    return a,b


def check():
    short = [w for n in range(5) for w in product((1,2),repeat=n)]
    for b,c in product(short,repeat=2):
        assert surface(b,c) == compare('AAA',b,c,TRIANGLES)
    for k in range(1,26):
        t = (1,)*(2*k-1)+(2,)
        t_next = (1,1)+t
        assert b3_word(t_next+(1,)) == b3_word((1,)+t+(1,2))
        assert minimum_factors(t)==k
        assert not surface((),(1,)*(2*k))
    # Compute the complete positive intervals, grouping only by positive braid equality.
    intermediates = 0
    for k in range(1,7):
        t = (1,)*(2*k-1)+(2,)
        for size in range(0,len(t)+1,2):
            for b in product((1,2),repeat=size):
                if surface((),b) and surface(b,t):
                    assert not b or b3_word(b)==b3_word(t)
                intermediates += 1
    directions = [(a,b) for a,b in product(range(-4,5),repeat=2) if a or b]
    for v in directions:
        a,b = v
        x,y = apply(v,(1,)),apply(v,(2,))
        assert a*x[1]-b*x[0] == -b*b
        assert a*y[1]-b*y[0] == -a*a
        assert apply(v,(1,2,1))==apply(v,(2,1,2))
    assert [apply((1,0),w) for w in [(1,),(1,2),(1,2,1)]]==[(1,0),(1,-1),(0,-1)]
    print(f'{len(short)**2} cubic decisions agreed with the independent planar packet solver.')
    print(f'{intermediates:,} positive intermediate words checked in the first six cover intervals.')
    print(f'25 signed recurrences and {len(directions)} oriented projective directions checked.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces',nargs=2,metavar=('SOURCE','TARGET'))
    args = parser.parse_args()
    if args.faces is None:
        check()
        return
    if any(set(w)-set('12') for w in args.faces):
        parser.error('positive three-strand faces use 1 and 2')
    s,t = (tuple(map(int,w)) for w in args.faces)
    print('surface comparison exists' if surface(s,t) else 'surface comparison absent')


if __name__=='__main__':
    main()
