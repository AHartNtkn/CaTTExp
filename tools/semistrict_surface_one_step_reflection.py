"""Decide uniform reflection for one signed use of a declared braid comparison."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product

from semistrict_surface_single_power import output_order, spellings
from semistrict_surface_shared_edge import inverse


@cache
def reverse_signed(w):
    """Right word reversing in the standard positive braid presentation."""
    w = list(w)
    while True:
        i = next((i for i in range(len(w)-1) if w[i]<0<w[i+1]),None)
        if i is None:
            return tuple(w)
        a,b = -w[i],w[i+1]
        if a==b:
            pair = ()
        elif abs(a-b)==1:
            pair = (b,a,-b,-a)
        else:
            pair = (b,-a)
        w[i:i+2] = pair


@cache
def quotient(prefix,word):
    w = reverse_signed(inverse(prefix)+word)
    return w if all(x>0 for x in w) else None


@cache
def simple_words(width):
    """One positive permutation braid per permutation, in increasing length."""
    identity = tuple(range(width))
    seen = {identity}
    todo = deque([(identity,())])
    result = []
    while todo:
        p,w = todo.popleft()
        result.append(w)
        for i in range(1,width):
            if p[i-1]<p[i]:
                q = p[:i-1]+(p[i],p[i-1])+p[i+1:]
                if q not in seen:
                    seen.add(q)
                    todo.append((q,w+(i,)))
    return result


def placements(order,rules):
    for names,l,r in rules:
        for offset in range(len(order)-len(names)+1):
            if tuple(order[offset:offset+len(names)])==tuple(names):
                yield tuple(i+offset for i in l),tuple(i+offset for i in r)


def raw_one(order,b,c,rules):
    if quotient(b,c)==():
        return True
    for w in spellings(b):
        o = tuple(order)
        for i in range(len(w)+1):
            for l,r in placements(o,rules):
                if len(w)-len(l)+len(r)!=len(c):
                    continue
                tail = quotient(l,w[i:])
                if tail is not None and quotient(w[:i]+r+tail,c)==():
                    return True
            if i<len(w):
                o = tuple(output_order(o,(w[i],)))
    return False


def critical_pair(width,l,r,v):
    for suffix in simple_words(width):
        a = quotient(v,l+suffix)
        if a is not None:
            b = quotient(v,r+suffix)
            if b is not None:
                return a,b,suffix
    raise AssertionError('the half twist always clears a simple prefix')


def distinct_orders(names):
    if not names:
        yield ()
        return
    for name in sorted(set(names)):
        rest = list(names)
        rest.remove(name)
        for suffix in distinct_orders(rest):
            yield (name,)+suffix


def decide(names,rules):
    width = len(names)
    tested = 0
    for order in distinct_orders(names):
        for l,r in placements(order,rules):
            if output_order(order,l)!=output_order(order,r):
                raise ValueError('rule faces must have the same named output')
            for v in simple_words(width):
                a,b,D = critical_pair(width,l,r,v)
                start = tuple(output_order(order,v))
                tested += 1
                if not raw_one(start,a,b,rules):
                    return (start,a,b,order,l,r,v,D),tested
    return None,tested


def independent_raw(order,b,c,rules):
    if c in spellings(b):
        return True
    targets = set(spellings(c))
    for w in spellings(b):
        for i in range(len(w)+1):
            for l,r in placements(output_order(order,w[:i]),rules):
                if any(w[i:i+len(l)]==v for v in spellings(l)):
                    if w[:i]+r+w[i+len(l):] in targets:
                        return True
    return False


def check():
    divisions = 0
    for width in (2,3,4):
        for n in range(5):
            for w in product(range(1,width),repeat=n):
                for v in simple_words(width):
                    tails = [s[len(v):] for s in spellings(w) if s[:len(v)] in spellings(v)]
                    q = quotient(v,w)
                    assert (q is not None) == bool(tails)
                    if q is not None:
                        assert q in spellings(tails[0])
                    divisions += 1
    comparisons = 0
    words = [w for n in range(4) for w in product((1,2),repeat=n)]
    for rule in [[('AAA',(),(1,2))],[('AAA',(1,),(1,2))],[('AA',(1,),())],
                 [('AAA',(1,2),(2,1))]]:
        for b,c in product(words,repeat=2):
            assert raw_one('AAA',b,c,rule) == independent_raw('AAA',b,c,rule)
            comparisons += 1
    for width in (2,3,4):
        n = 'A'*width
        for d in (1,2,3):
            assert decide(n,[('AA',(),(1,)*d)])[0] is None
    assert decide('ABC',[('BA',(),(1,1))])[0] is not None
    assert decide('ABC',[('BA',(),(1,1)),('AB',(),(1,1))])[0] is None
    triangles = [('AAA',(),(1,2)),('AAA',(),(2,1))]
    assert decide('AAA',triangles) == (None,12)
    assert decide('AAAA',triangles)[0] is not None
    assert raw_one('AAAA',(3,2),(3,1,2,3),triangles)
    assert not raw_one('AAAA',(2,),(1,2,3),triangles)
    print(f'{divisions:,} simple prefix divisions agreed with independent positive spellings.')
    print(f'{comparisons:,} direct comparisons cross-checked; single-power charts verified through width four.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--at',help='multiset of strand names at the desired width')
    parser.add_argument('--rule',action='append',default=[],metavar='NAMES:FROM:TO',
                        help='crossing positions are comma-separated, with empty words allowed')
    args = parser.parse_args()
    if args.at is None:
        check()
        return
    try:
        rules = []
        for entry in args.rule:
            n,l,r = entry.split(':')
            def parse(s):
                w = tuple(map(int,s.split(','))) if s else ()
                if any(not 1<=i<len(n) for i in w):
                    raise ValueError('position outside this rule width')
                return w
            rules.append((n,parse(l),parse(r)))
        failure,count = decide(args.at,rules)
    except ValueError as e:
        parser.error(str(e))
    if failure:
        start,a,b,o,l,r,v,D = failure
        print(f'Old boundary at {"".join(start)}: {a} -> {b}; no raw comparison using at most one rule.')
        print(f'Signed witness: remove prefix {v} after applying {l} -> {r} at {"".join(o)} with suffix {D}.')
    else:
        print(f'Every single signed step reflects on this multiset ({count} critical comparisons).')


if __name__=='__main__':
    main()
