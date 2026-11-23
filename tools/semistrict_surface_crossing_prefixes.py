"""Recover the forced multiset of native higher Gray cubes from the two old faces.

For local rank k >= 3 a face is a list of (positive crossing prefix, offset)
records for its (k-1)-atoms. Offsets and adjacent crossing positions are zero based.
"""
import argparse
from collections import Counter, defaultdict
from itertools import product
import json

from gray_globe_comparison import atom
from semistrict_surface_odd_cubes import EDGE


def track(width, word):
    order = list(range(width))
    counts = Counter()
    for i in word:
        if not 0 <= i < width-1:
            raise ValueError('crossing outside the temporal history')
        a,b = order[i:i+2]
        counts[min(a,b),max(a,b)] += 1
        order[i:i+2] = b,a
    return order, counts


def record(values, width, rank, prefix, offset, sign):
    order, crossings = track(width,prefix)
    if not 0 <= offset <= width-(rank-1):
        raise ValueError('facet outside the temporal history')
    block = order[offset:offset+rank-1]
    for extra in order[offset+rank-1:]:
        selected = frozenset(block+[extra])
        exponent = sum(count for (a,b),count in crossings.items() if a in selected and b in selected)
        values[tuple(sorted(selected))][exponent] -= sign


def divide(terms, rank):
    """Divide by 1-X+X^2-...+(-X)^(rank-1), checking exact divisibility."""
    if not terms:
        return {}
    remainder = Counter(terms)
    degree = max((i for i,c in remainder.items() if c), default=-1)
    quotient = {}
    for i in range(degree-rank+2):
        c = remainder[i]
        if c:
            quotient[i] = c
            for j in range(rank):
                remainder[i+j] -= c*(-1)**j
    return None if any(remainder.values()) else quotient


def forced_counts(width, rank, source, target):
    if rank < 3:
        raise ValueError('requires local rank at least three')
    differences = defaultdict(Counter)
    for sign,face in [(-1,source),(1,target)]:
        for prefix,offset in face:
            record(differences,width,rank,prefix,offset,sign)
    result = {}
    for selected, diff in differences.items():
        quotient = divide(diff,rank)
        if quotient is None or any(x < 0 for x in quotient.values()):
            return None
        if quotient:
            result[selected] = quotient
    return result


def facet_records(rank, prefix, offset, cells):
    records = []
    for face in cells:
        j = next(i for i,x in enumerate(face) if x != EDGE)
        pos = rank-1-j
        if face[j] == (0,0):
            extra = range(offset+pos,offset+rank-1)
            start = offset
        else:
            extra = range(offset+pos-1,offset-1,-1)
            start = offset+1
        records.append((tuple(prefix)+tuple(extra),start))
    return records


def word_face(word):
    return [(word[:i],a) for i,a in enumerate(word)]


def checks():
    contextual = braid_steps = distant = paths = 0
    for k in range(3,9):
        faces = atom((EDGE,)*k)[-2]
        for n in range(k,k+3):
            for offset in range(n-k+1):
                prefix = ()
                for b in range(10):
                    source,target = [facet_records(k,prefix,offset,face) for face in faces]
                    actual = forced_counts(n,k,source,target)
                    order, counts = track(n,prefix)
                    selected = tuple(sorted(order[offset:offset+k]))
                    exp = sum(c for (a,z),c in counts.items() if a in selected and z in selected)
                    assert actual == {selected:{exp:1}}
                    assert forced_counts(n,k,target,source) is None
                    prefix += ((b*3+offset)%(n-1),)
                    contextual += 1
    for n in [3,4]:
        for length in range(1,7):
            for word in product(range(n-1), repeat=length):
                for j,(a,b) in enumerate(zip(word,word[1:])):
                    if abs(a-b)>1:
                        v = word[:j]+(b,a)+word[j+2:]
                        assert forced_counts(n,3,word_face(word),word_face(v)) == {}
                        distant += 1
                    if b==a+1 and word[j:j+3] == (a,b,a):
                        v = word[:j]+(b,a,b)+word[j+3:]
                        data = forced_counts(n,3,word_face(word),word_face(v))
                        assert sum(sum(p.values()) for p in data.values()) == 1
                        assert forced_counts(n,3,word_face(v),word_face(word)) is None
                        braid_steps += 1
    # A positive path that revisits the same three strands after another half twist.
    w = (0,1,0)*4
    for mask in product((0,1),repeat=4):
        v = tuple(a for use in mask for a in ((1,0,1) if use else (0,1,0)))
        want = {3*i:1 for i,use in enumerate(mask) if use}
        assert forced_counts(3,3,word_face(w),word_face(v)) == ({(0,1,2):want} if want else {})
        paths += 1
    print(f'{contextual} contextual cube boundaries and reverses through rank eight, '
          f'{braid_steps} literal braid moves, {distant} distant exchanges, {paths} repeated-block movies')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--faces',help='JSON with width, rank, source, target; '
                        'each face is a list of [crossing_prefix, offset]')
    args = parser.parse_args()
    if args.faces:
        with open(args.faces) as handle:
            d = json.load(handle)
        result = forced_counts(**d)
        print('impossible' if result is None else result)
    else:
        checks()
