"""Read the raw structural track group at a connected four-strand binary plat.

JSON input gives seam (the middle Artin braid) and track (a proposed pure
middle-cut loop in coordinates immediately after both opening packets).
"""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path
import json

from semistrict_surface_cap_threads import artin
from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_packet_disks import compare
from semistrict_surface_scalar_leaves import swapped
from semistrict_surface_shared_edge import braid_image


def sphere_action(word,n):
    # On filling infinity the ordered product of the terminal meridians is one.
    images = [(j,) for j in range(1,n)] + [inv(tuple(range(1,n)))]
    for g in word:
        artin(images,g)
    return images[:-1]


def sphere_push(word,n=4):
    images = sphere_action(word,n)
    conjugators = []
    for i,w in enumerate(images,1):
        j = 0
        while 2*j+1<len(w) and w[j]==-w[-j-1]:
            j += 1
        if w[j:len(w)-j] != (i,):
            return None
        conjugators.append(w[:j])
    candidate = max(conjugators,key=len)
    # In a common conjugator only the trailing run of one generator can
    # disappear. The other two stripped images recover the whole word.
    if all(w==reduced(candidate+(i,)+inv(candidate)) for i,w in enumerate(images,1)):
        return candidate
    return None


def solve(seam,track):
    if any(type(g) is not int or not 1<=abs(g)<=3 for w in (seam,track) for g in w):
        raise ValueError('expected four-strand Artin words')
    lower = [(0,1),(2,3)]
    order = swapped(range(4),seam)
    upper = [tuple(order[:2]),tuple(order[2:])]
    if set(upper[0]) in [set(pair) for pair in lower]:
        raise ValueError('the two closing pairs must each meet both opening pairs')
    if swapped(range(4),track)!=list(range(4)):
        raise ValueError('the middle loop must return all occurrence names')
    push = sphere_push(track)
    windings = [sum(restrict(4,track,pair))//2 for pair in lower+upper]
    member = push is not None and not any(windings)
    return dict(closing_pairs=upper,paired_windings=windings,infinity_push=push,
                realized_at_both_ends=member,raw_null=(not push) if member else None)


def comm(x,y):
    return reduced(x+y+inv(x)+inv(y))


def peripheral(i,n=4):
    approach = tuple(range(i+1,n))
    return reduced(approach+tuple(range(1,n-1))*(n-1)+inv(approach))


def brunnian(n):
    def bracket(letters):
        if len(letters)==1:
            return letters[0]
        mid = len(letters)//2
        return comm(bracket(letters[:mid]),bracket(letters[mid:]))
    return comm(bracket([peripheral(i,n) for i in range(n-1)]),peripheral(n-1,n))


def audit():
    per = [peripheral(i) for i in range(4)]
    witness = comm(comm(per[0],per[1]),comm(per[2],per[3]))
    for i in range(4):
        projected = restrict(4,witness,set(range(4))-{i})
        # Three-strand identity by the faithful Artin action.
        assert braid_image(3,projected)==braid_image(3,())
    push = sphere_push(witness)
    assert push
    count = 0
    samples = [(),(1,1),(2,2),(3,3),(1,2,3)*4,*per,comm(per[0],per[1]),witness]
    samples += [reduced(x+y) for x,y in product(samples[:9],repeat=2)]
    for seam in ((2,),(2,2,2),(-2,),(1,2,3),(1,1,2,-3,-3)):
        for w in samples:
            result = solve(seam,w)
            lower = compare(0,[2,2],w,[])['same_component']
            upper = compare(0,[2,2],inv(seam)+w+seam,[])['same_component']
            assert result['realized_at_both_ends']==(lower and upper)
            count += 1
        assert solve(seam,witness)['raw_null'] is False
    print(f'{count} middle-loop decisions agree with both independent packet disk tests.')
    print(f'The {len(witness)}-crossing commutator has infinity push of length {len(push)}; every strand deletion is trivial.')
    for b,c in ((2,3),(3,2)):
        n = b*c
        w = brunnian(n)
        order = list(range(n))
        seam = []
        # Reorder the b-by-c rectangle from rows to columns.
        for target,leaf in enumerate(i*c+j for j in range(c) for i in range(b)):
            index = order.index(leaf)
            while index>target:
                seam.append(index)
                order[index-1],order[index] = order[index],order[index-1]
                index -= 1
        assert sphere_push(w,n)
        assert compare(0,[c]*b,w,[])['same_component']
        assert compare(0,[b]*c,inv(seam)+w+tuple(seam),[])['same_component']
        for i in range(n):
            projected = restrict(n,w,set(range(n))-{i})
            assert sphere_push(projected,n-1)==() and not sum(restrict(n-1,projected,{0,1}))
    print('The six-strand construction survives both rectangular packet tests and dies on every five-strand restriction.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    parser.add_argument('--witness',action='store_true',help='emit the Brunnian track for the trefoil seam')
    parser.add_argument('--brunnian',type=int,metavar='N',help='emit a middle-cut track for N strands, N at least four')
    args = parser.parse_args()
    if args.brunnian is not None:
        if args.brunnian<4:
            parser.error('the packet construction needs at least four strands')
        print(json.dumps(brunnian(args.brunnian)))
    elif args.witness:
        p = [peripheral(i) for i in range(4)]
        print(json.dumps(dict(seam=[2,2,2],track=comm(comm(p[0],p[1]),comm(p[2],p[3])))))
    elif args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(solve(data['seam'],tuple(data['track'])),indent=2))
    else:
        audit()
