"""Find an explicit substitution to a single pair Hopf at elementary two.

Input masks rank, forms and face use the convention of the Hopf pencil solver.
Output lists linear-form masks for the bottom axes of the target, with unused
axes zero, and middle character masks giving its middle coordinates.
"""
import json
from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement
from pathlib import Path

from semistrict_surface_framed_relations import separate
from semistrict_surface_hopf_pencils import analyze, character_equations
from semistrict_surface_lens_squares import row_reduce


def xor_sum(terms):
    value = 0
    for term in terms:
        value ^= term
    return value


def combination(columns, target):
    pivots = {}
    for j, col in enumerate(columns):
        v, mask = col, 1 << j
        while v:
            i = v.bit_length()-1
            if i not in pivots:
                pivots[i] = v,mask
                break
            a,b = pivots[i]
            v,mask = v^a,mask^b
    mask = 0
    while target:
        i = target.bit_length()-1
        if i not in pivots:
            raise ValueError('target outside linear image')
        a,b = pivots[i]
        target,mask = target^a,mask^b
    return mask


def multiplier(rank):
    pairs = list(combinations_with_replacement(range(rank),2))
    def multiply(a,b):
        return sum(((((a >> i) & (b >> j)) ^ (((a >> j) & (b >> i)) if i != j else 0))
                    & 1) << k for k,(i,j) in enumerate(pairs))
    return multiply


def quadrics(mul, x, y, ls, cs, edges):
    first = mul(x,y) ^ xor_sum(mul(l,c) for l,c in zip(ls,cs,strict=True))
    other = [mul(c,l^c^x^y) for l,c in zip(ls,cs,strict=True)]
    for (i,j),v in zip(combinations(range(len(ls)),2),edges,strict=True):
        other[i] ^= mul(ls[j],v)
        other[j] ^= mul(ls[i],v)
    return [first,*other]


def universal(d):
    if type(d) is not int or d < 0:
        raise ValueError('index must be nonnegative')
    pairs = list(combinations(range(d),2))
    rank = 2+2*d+len(pairs)
    axes = [1 << i for i in range(rank)]
    return rank,quadrics(multiplier(rank),*axes[:2],axes[2:2+d],axes[2+d:2+2*d],axes[2+2*d:])


def substitute(rank, forms, face):
    if type(rank) is not int or rank < 0:
        raise ValueError('rank must be nonnegative')
    width = rank*(rank+1)//2
    if any(type(f) is not int or not 0 < f < 1 << width for f in forms) or len(row_reduce(forms)) != len(forms):
        raise ValueError('supply independent quadratic coefficient masks')
    size = len(forms)
    if type(face) is not int or not 0 <= face < 1 << ((rank+1)*size):
        raise ValueError('face outside operation coordinates')
    char = separate(face,row_reduce(character_equations(rank,forms)))
    if char is None:
        return {'raw_nonzero':False}
    gamma = char % (1 << size)
    ts = [sum(((char >> ((j+1)*size+i)) & 1) << j for j in range(rank)) for i in range(size)]
    pivot = gamma.bit_length()-1
    u = ts[pivot] if gamma else 0
    indices = [i for i in range(size) if i != pivot]
    others = [ts[i] ^ (u if gamma >> i & 1 else 0) for i in indices]
    ls = list(row_reduce(others).values())
    d = len(ls)
    coeffs = [combination(ls,v) for v in others]
    middle = [gamma]+[sum(((m >> s) & 1) << i for i,m in zip(indices,coeffs,strict=True))
                      for s in range(d)]
    active = [xor_sum(f for j,f in enumerate(forms) if g >> j & 1) for g in middle]
    mul = multiplier(rank)
    letters = [1 << j for j in range(rank)]
    columns = [mul(e,e^u) for e in letters]+[mul(l,e) for l in ls for e in letters]
    params = combination(columns,active[0])
    mask = (1 << rank)-1
    a = params & mask
    cs = [(params >> ((s+1)*rank)) & mask for s in range(d)]
    difference = [g^mul(c,l^c^u) for g,c,l in zip(active[1:],cs,ls,strict=True)]
    pairs = list(combinations(range(d),2))
    columns = [(mul(ls[t],e) << (width*s)) ^ (mul(ls[s],e) << (width*t))
               for s,t in pairs for e in letters]
    params = combination(columns,sum(f << (s*width) for s,f in enumerate(difference)))
    edges = [(params >> (j*rank)) & mask for j in range(len(pairs))]
    assert quadrics(mul,a,a^u,ls,cs,edges) == active
    bracket = [xor_sum(g for g,l in zip(middle,[u,*ls],strict=True) if l >> j & 1) for j in range(rank)]
    pulled = gamma ^ xor_sum(b << ((j+1)*size) for j,b in enumerate(bracket))
    assert pulled == char and (face & pulled).bit_count() % 2 == 1
    return dict(raw_nonzero=True, tester_index=max(2,d), x=a,y=a^u, vector_axes=ls,
                square_axes=cs, alternating_axes=edges,middle_coordinates=middle)


def audit():
    for d in range(2,8):
        r,forms = universal(d)
        rels = row_reduce(character_equations(r,forms))
        assert len(rels) == (d+1)*(r+1)-1 and separate(1,rels)
        result = substitute(r,forms,1)
        assert result['tester_index'] == d
    checked = 0
    # Every face in every two-variable quadratic pencil, including relations.
    for f,g in combinations(range(1,8),2):
        if g > f^g:
            continue
        for face in range(64):
            r = substitute(2,[f,g],face)
            assert r['raw_nonzero'] == bool(analyze(2,[f,g],face)['detecting_axes'])
            checked += 1
    # Net with no pair reading, a mixed coordinate change, and a change of
    # bottom variables forcing dependent target axes in the quadratic pullback.
    for forms in ([9216,4128,272],[9216^4128,4128,272]):
        result = substitute(6,forms,8)
        assert result['raw_nonzero'] and result['middle_coordinates'][0] == 0
    r,forms = universal(2)
    forms = [forms[0]^forms[1],forms[2],forms[1]]
    for j in range(24):
        v = 1 << j
        assert substitute(r,forms,v)['raw_nonzero'] == analyze(r,forms,v)['raw_nonzero']
    # A mixed Hopf with no split reading and linearly dependent bottom images.
    mul = multiplier(4)
    forms = quadrics(mul,1,2,[4,8],[1^4,2^8],[3])
    assert substitute(4,forms,1)['raw_nonzero']
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    parser.add_argument('--tester',type=int)
    args = parser.parse_args()
    try:
        if args.input:
            print(json.dumps(substitute(**json.loads(args.input.read_text()))))
        elif args.tester is not None:
            rank,forms = universal(args.tester)
            print(json.dumps(dict(rank=rank,forms=forms,face=1)))
        else:
            print(f'{audit()} pencil faces checked; explicit pullbacks checked through tester index seven.')
    except (ValueError,TypeError) as error:
        parser.error(str(error))
