"""Test multi-occurrence phase checkpoints and the conflict clauses in the tensor query.

--trees accepts JSON as in semistrict_surface_branched_comparisons.py. The query
asks whether any actual parallel boundary passes the strengthened square test
and fails the ordinary raw tableau test. --emit exports the integer sentence.
"""

from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_branched_comparisons import query
from semistrict_surface_decorated_phase_paths import location, reachable, sort_with_changes, words
from semistrict_surface_globular_judgment import Tree, tensor_rows
from semistrict_surface_penultimate_intervals import check


def compatible_query(shapes):
    formula = query(shapes)
    changes = []
    for n,word in enumerate(tensor_rows([Tree(t) for t in shapes],5)):
        if tuple(d for d,x in word)!=(1,3,1):
            continue
        (a,l),(b,(m,_)),(c,r) = (x for d,x in word)
        changes.append((n,(a,b,c),m,l,r))
    clauses = []
    for n,sites,m,l,r in changes:
        for k,s,j,h,v in changes:
            # Phase paths traverse the middle steps in decreasing index order.
            if sites==s and m>j and l>h and r>v:
                clauses.append(f'(assert (or (= y{n} 0) (= y{k} 0)))')
    return formula.replace('(check-sat)','\n'.join([*clauses,'(check-sat)'])),len(clauses)


def compare_visits():
    count = 0
    # Exact independent reachability for two different marked middle letters.
    for counts in ((1,2,1),(2,2,1),(1,3,1)):
        shuffles = list(words(counts))
        after = {s:reachable(s) for s in shuffles}
        positions = list(product(range(counts[0]+1),range(counts[2]+1)))
        for i in range(counts[1]):
            for j in range(i+1,counts[1]):
                a,b = (1,i),(1,j)
                for p,q in product(positions,repeat=2):
                    visits = [(a,p),(b,q)]
                    for u in shuffles:
                        targets = set()
                        for (x,f),(y,g) in (visits,list(reversed(visits))):
                            first = {w for w in after[u] if location(w,x)==f}
                            second = {s for w in first for s in after[w] if location(s,y)==g}
                            targets.update(t for s in second for t in after[s])
                        for v in shuffles:
                            ops = sort_with_changes(u,v,visits)
                            assert (ops is not None)==(v in targets)
                            if ops is not None:
                                w = list(u)
                                seen = []
                                for op in ops:
                                    if isinstance(op,tuple):
                                        mark = op[1]
                                        seen.append((mark,location(w,mark)))
                                    else:
                                        x,y = w[op:op+2]
                                        assert x[0]>y[0]
                                        w[op:op+2] = y,x
                                assert tuple(w)==v and sorted(seen)==visits
                            count += 1
    return count


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--trees',type=json.loads)
    p.add_argument('--emit',type=Path)
    args = p.parse_args()
    default = [[[[]]],[[[[]],[[]]]],[[[]]]]
    if args.trees is not None or args.emit:
        formula,n = compatible_query(default if args.trees is None else args.trees)
        if args.emit:
            args.emit.write_text(formula)
        else:
            print(check(formula),f'({n} conflict clauses)')
    else:
        print(f'{compare_visits():,} marked phase-word judgments verified',flush=True)
        for middle in (default[1],[[[[]],[],[[]]]],[[[[],[]],[[]]]]):
            shapes = [default[0],middle,default[2]]
            formula,n = compatible_query(shapes)
            assert n>0 and check(formula)=='unsat'
            print(f'{middle}: exact on all parallel faces using {n} conflict clauses',flush=True)
