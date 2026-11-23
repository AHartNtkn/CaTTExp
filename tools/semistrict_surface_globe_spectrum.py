"""Compute the Gray interchange failure spectrum on a spatial string of globes.

The calculation uses local dimensions. The output degrees are global.
"""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
from pathlib import Path

from gray_globe_comparison import boundary, globe
from semistrict_surface_penultimate_intervals import check, total
from semistrict_surface_square_quotient_chains import Space, differential


def highest_relations(shape):
    """Basis words at the largest rank in the elementary-square ideal."""
    cut = min(a+b for a,b in zip(shape,shape[1:]))
    rank = sum(shape)+2-cut
    terms = set()
    for i in range(len(shape)-1):
        if shape[i]+shape[i+1] != cut:
            continue
        entries = [(2*d,) for d in shape]
        for j in (i,i+1):
            entries[j] = (2,) if shape[j] == 1 else (2,3)
        terms.update(product(*entries))
    return rank,terms


def highest_cycles(terms):
    image = Space()
    for w in sorted(terms):
        image.insert(differential(w))
    return len(terms)-len(image.rows)


def exception_query(shape):
    """Search all integral parallel tableaux for a quotient-only filler in K+1."""
    rank, _ = highest_relations(shape)
    rank += 1
    cells = defaultdict(list)
    for c in product(*(globe(d) for d in shape)):
        cells[sum(x for x,_ in c)].append(c)
    return tableau_query(cells,rank,lambda cell:boundary(cell).items())


def tableau_query(cells,rank,facets):
    """Compare the square ideal with raw filling when rank is above its top degree."""
    lines = ['(set-logic LIA)']

    def positive(name):
        lines.extend((f'(declare-const {name} Int)', f'(assert (>= {name} 0))'))
        return name

    def image(z):
        rows = defaultdict(list)
        for c,x in z.items():
            for f,n in facets(c):
                if n:
                    rows[f].append(x if n==1 else f'(- {x})')
        return {f:total(terms) for f,terms in rows.items()}

    rhs = {}
    for j in range(rank):
        faces = [{c:positive(f'r{j}{sign}{i}') for i,c in enumerate(cells[j])} for sign in ('p','m')]
        for z in faces:
            if j == 0:
                lines.append(f'(assert (= {total(z.values())} 1))')
            else:
                rows = image(z)
                for f,y in rhs.items():
                    lines.append(f'(assert (= {rows.get(f,"0")} {y}))')
        rhs = {c:f'(- {faces[0][c]} {faces[1][c]})' for c in cells[j]}

    quotient = image({c:positive(f'y{i}') for i,c in enumerate(cells[rank])})
    for c,y in rhs.items():
        active = [d for d,_ in c if d]
        if not any(a==b==1 for a,b in zip(active,active[1:])):
            lines.append(f'(assert (= {quotient.get(c,"0")} {y}))')
    raw = {c:f'z{i}' for i,c in enumerate(cells[rank])}
    rows = image(raw)
    conditions = [f'(>= {x} 0)' for x in raw.values()]
    conditions.extend(f'(= {rows.get(f,"0")} {y})' for f,y in rhs.items())
    binders = ' '.join(f'({x} Int)' for x in raw.values())
    lines.append(f'(assert (not (exists ({binders}) (and {" ".join(conditions)}))))')
    return '\n'.join(lines+['(check-sat)',''])


def spectrum(shape):
    if not shape or min(shape) < 1:
        raise ValueError('supply positive local globe dimensions')
    if len(shape) == 1:
        return []
    k,_ = highest_relations(shape)
    return list(range(3,k+2))


def checks():
    cases = 0
    for n in range(2,7):
        for shape in product(range(1,5),repeat=n):
            k,bad = highest_relations(shape)
            nullity = highest_cycles(bad)
            exceptional = (n==2 and min(shape)>=2) or (n==3 and shape[0]==shape[2]==2 and shape[1]>=2)
            assert nullity == int(exceptional)
            assert all(sum(a//2 for a in w)==k for w in bad)
            cases += 1
    print(f'{cases:,} highest relation groups checked by exact boundary rank',flush=True)
    exceptional = list(product((2,3,4),repeat=2)) + [(2,h,2) for h in range(2,7)]
    for shape in exceptional:
        assert check(exception_query(shape)) == 'unsat'
        print(f'{shape}: no quotient-only comparison',flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('shape',nargs='*',type=int)
    parser.add_argument('--emit-exception',type=Path,help='write the explicit Presburger query')
    args = parser.parse_args()
    if args.emit_exception:
        args.emit_exception.write_text(exception_query(tuple(args.shape)))
    elif args.shape:
        print('Failing degrees:',spectrum(tuple(args.shape)))
    else:
        checks()
