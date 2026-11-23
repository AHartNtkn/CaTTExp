"""Find a raw one-power insertion from the orthogonal splitting of a braid quotient."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product

from semistrict_surface_braid_reflection import positive_moves
from semistrict_surface_shared_edge import braid_image


@cache
def spellings(word):
    seen = {word}
    pending = deque([word])
    while pending:
        for v in positive_moves(pending.popleft()):
            if v not in seen:
                seen.add(v)
                pending.append(v)
    return tuple(sorted(seen))


@cache
def terminal_letters(word):
    return {w[-1]:w[:-1] for w in spellings(word) if w}


def coprime_parts(source, target):
    suffix = []
    while True:
        small = terminal_letters(source)
        large = terminal_letters(target)
        candidates = small.keys() & large.keys()
        if not candidates:
            return source,target,tuple(reversed(suffix))
        x = min(candidates)
        suffix.append(x)
        source,target = small[x],large[x]


def output_order(names, prefix):
    order = list(names)
    for i in prefix:
        order[i-1],order[i] = order[i],order[i-1]
    return order


def named_pair(names, prefix, index):
    return ''.join(sorted(output_order(names,prefix)[index-1:index+1]))


def certificate(names, source, target, pairs):
    """Allowed unordered pairs must admit the insertion at both input orders."""
    n = len(names)
    d = len(target)-len(source)
    if d<=0:
        raise ValueError('a single insertion requires a positive length change')
    b,a,suffix = coprime_parts(source,target)
    target_key = braid_image(n,a)
    for j in range(1,n):
        if named_pair(names,b,j) in pairs and braid_image(n,b+(j,)*d) == target_key:
            return b,j,suffix
    return None


def raw_outputs(names, source, d, pairs):
    n = len(names)
    return {braid_image(n,w[:i]+(j,)*d+w[i:])
            for w in spellings(source) for i in range(len(w)+1) for j in range(1,n)
            if named_pair(names,w[:i],j) in pairs}


def check():
    count = 0
    for names, pairs in [('AAA',{'AA'}),('ABC',{'AC'}),('ABCA',{'AA','BC'})]:
        n = len(names)
        for size in range(4):
            sources = product(range(1,n),repeat=size)
            for s in sources:
                for d in ([1,2,3] if names=='AAA' else [2]):
                    possible = raw_outputs(names,s,d,pairs)
                    for t in product(range(1,n),repeat=size+d):
                        cert = certificate(names,s,t,pairs)
                        assert (cert is not None) == (braid_image(n,t) in possible)
                        if cert is not None:
                            l,j,r = cert
                            assert braid_image(n,l+r) == braid_image(n,s)
                            assert braid_image(n,l+(j,)*d+r) == braid_image(n,t)
                        count += 1
    from semistrict_surface_monotone_braids import compare
    signed = 0
    for names,pair,d in [('AAA','AA',1),('AAA','AA',3),('ABC','AC',2),('AAB','AB',2)]:
        rules = [(phase,(),(1,)*d) for phase in {pair,pair[::-1]}]
        for size in range(3):
            for s in product((1,2),repeat=size):
                for t in product((1,2),repeat=size+d):
                    if output_order(names,s)==output_order(names,t):
                        assert compare(names,s,t,rules) == (certificate(names,s,t,{pair}) is not None)
                        signed += 1
    print(f'{signed:,} comparisons agreed independently with the signed three-strand decision.')
    print(f'{count:,} coprime-splitting tests agreed with direct insertion in every positive spelling.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--at',help='strand names in order')
    parser.add_argument('--faces',nargs=2,metavar=('SOURCE','TARGET'),help='comma-separated crossing indices')
    parser.add_argument('--pair',action='append',default=[],help='unordered scalar names permitting this power')
    args = parser.parse_args()
    if args.at is None:
        check()
        return
    try:
        if len(args.at)<2 or not args.faces or not args.pair:
            raise ValueError('supply two faces, at least two strands, and an allowed pair')
        def parse(w):
            return tuple(map(int,w.split(','))) if w else ()
        s,t = map(parse,args.faces)
        if any(not 1<=i<len(args.at) for i in s+t):
            raise ValueError('invalid crossing position')
        if output_order(args.at,s) != output_order(args.at,t):
            raise ValueError('old faces have different named outputs')
        d = len(t)-len(s)
        pairs = {''.join(sorted(p)) for p in args.pair}
        if any(len(p)!=2 or set(p)-set(args.at) or (p[0]!=p[1] and d%2) for p in pairs):
            raise ValueError('allowed pairs must have parallel input and output for the given power')
        cert = certificate(args.at,s,t,pairs)
    except ValueError as err:
        parser.error(str(err))
    if cert is None:
        print('No single signed or positive insertion.')
    else:
        l,j,r = cert
        print(f'Insert crossing {j} to power {d} after {l} and before {r}.')


if __name__=='__main__':
    main()
