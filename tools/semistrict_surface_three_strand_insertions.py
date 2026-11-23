"""Decide universal single-insertion reflection by testing only empty three-strand sources."""
from argparse import ArgumentParser
from itertools import combinations, product

from semistrict_surface_monotone_braids import ThreeStrandOrders, cyclic
from semistrict_surface_one_step_reflection import decide, placements, quotient, spellings
from semistrict_surface_shared_edge import inverse
from semistrict_surface_single_power import coprime_parts


def uncovered(names, rules):
    orders = ThreeStrandOrders(names)
    classes, available = set(),set()
    sizes = set()
    for order in orders.orbit:
        for left,u in placements(order,rules):
            if left:
                raise ValueError('this criterion requires empty-source insertions')
            end,word = orders.path(order,u)
            if end!=order:
                raise ValueError('an insertion must return to its named input')
            sizes.add(len(u))
            classes.add((len(u),cyclic(word,orders.period)))
            available.add((order,spellings(u)[0]))
    for size in sorted(sizes):
        for u in product((1,2),repeat=size):
            if spellings(u)[0]!=u:
                continue
            for order in orders.orbit:
                if (order,u) not in available:
                    end,word = orders.path(order,u)
                    if end==order and (size,cyclic(word,orders.period)) in classes:
                        return order,u
    return None


def check():
    count = 0
    for names in ('AAA','AAB','ABC'):
        orders = ThreeStrandOrders(names)
        for size in range(1,5):
            candidates = []
            for o in orders.orbit:
                for w in product((1,2),repeat=size):
                    if w==spellings(w)[0] and orders.path(o,w)[0]==o:
                        candidates.append((''.join(o),(),w))
            # All individual rules, pairs, and every complete signed conjugacy class.
            families = [(r,) for r in candidates] + list(combinations(candidates,2))
            by_class = {}
            for r in candidates:
                n,_,w = r
                _,v = orders.path(n,w)
                by_class.setdefault(cyclic(v,orders.period),[]).append(r)
            families.extend(by_class.values())
            for rules in families:
                miss = uncovered(names,rules)
                critical,_ = decide(names,rules)
                assert (miss is None)==(critical is None)
                count += 1
    assert uncovered('AAA',[('AAA',(),(1,2))]) == (tuple('AAA'),(2,1))
    assert uncovered('AAA',[('AAA',(),(1,2)),('AAA',(),(2,1))]) is None
    orders = ThreeStrandOrders('AAA')
    words = [w for n in range(6) for w in product((1,2),repeat=n)]
    labels = {w:orders.path('AAA',w)[1] for w in words}
    classes = {(len(w),cyclic(v,orders.period)) for w,v in labels.items()}
    checks = 0
    for b,c in product(words,repeat=2):
        conjugate_positive = (len(c)-len(b),cyclic(labels[c]+inverse(labels[b]),orders.period)) in classes
        bottom,top,_ = coprime_parts(b,c)
        assert conjugate_positive == (quotient(bottom,top) is not None)
        checks += 1
    print(f'{checks:,} orthogonal fractions agreed with positive conjugacy in the modular group.')
    print(f'{count:,} named insertion dictionaries agreed with the independent critical-pair solver.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--at',help='three names, including repeats')
    parser.add_argument('--insert',action='append',default=[],metavar='NAMES:WORD')
    args = parser.parse_args()
    if args.at is None:
        check()
        return
    try:
        if len(args.at)!=3:
            raise ValueError('the empty-source criterion requires exactly three strands')
        rules = []
        for entry in args.insert:
            names,w = entry.split(':')
            if not 1<=len(names)<=3 or set(w)-set('12'[:len(names)-1]):
                raise ValueError('invalid insertion width or crossing position')
            rules.append((names,(),tuple(map(int,w))))
        missing = uncovered(args.at,rules)
    except ValueError as err:
        parser.error(str(err))
    if missing is None:
        print('All single signed insertions reflect at every old boundary on these three names.')
    else:
        o,u = missing
        print(f'Empty-source failure at {"".join(o)}: insert {u}.')


if __name__=='__main__':
    main()
