"""Compare named packet histories at the terminal cut.

JSON fields: through (count), packets (ordered sizes), first and second
(signed terminal Artin words from the same grouped batch). The two braids
must have the same terminal permutation. Omit first to compare to the batch.
"""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
import json

from semistrict_surface_cap_threads import artin, joined
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_scalar_leaves import swapped
from semistrict_surface_serial_gate_tracks import meridian
from semistrict_surface_shared_edge import braid_image


def compare(m, sizes, first, second):
    if type(m) is not int or m < 0 or any(type(k) is not int or k < 1 for k in sizes):
        raise ValueError('expected a nonnegative through count and positive packet sizes')
    n = m + sum(sizes)
    if any(type(g) is not int or not 0 < abs(g) < n for w in (first,second) for g in w):
        raise ValueError('terminal crossing outside the row')
    word = reduced(tuple(first) + inv(second))
    if swapped(range(n),word) != list(range(n)):
        raise ValueError('named terminal rows disagree')
    blocks = []
    live = [(i+1,) for i in range(m)]
    rank = m
    for k in sizes:
        blocks.append(range(len(live),len(live)+k))
        new = [(rank+i+1,) for i in range(k-1)]
        live.extend([*new,inv(joined(new))])
        rank += k-1
    # Read the transported disk boundaries directly in the trace exterior.
    for g in word:
        artin(live,g)
    disks = [joined(live[i] for i in block) for block in blocks]
    def untwisted(block):
        return braid_image(len(block),restrict(n,word,block)) == braid_image(len(block),())
    through = untwisted(range(m))
    internal = [untwisted(block) for block in blocks]
    return dict(same_component=through and all(internal) and not any(disks),
                disk_words=disks, internal_trivial=internal, through_trivial=through)


def push_packet(m, sizes, packet, target):
    """Push an intact packet around one earlier leaf on the grouped row."""
    offset = m+sum(sizes[:packet])
    local = meridian(offset-target-1)
    reflected = tuple((1 if g>0 else -1)*(offset+1-abs(g)) for g in local)
    return cable(reflected,[1]*offset+[sizes[packet]])


def audit():
    accepted = rejected = 0
    for m,sizes in product((0,1,2),((2,2,2),(3,2,2),(2,2,2,2),(2,1,2))):
        offsets = [m+sum(sizes[:j]) for j in range(len(sizes))]
        # A full packet can pass one earlier tip. A turn between just two
        # tips of different nonsingleton packets need not extend over either disk.
        moves = [push_packet(m,sizes,j,offsets[j-1]) for j in range(1,len(sizes))]
        for seq in product(moves,repeat=2):
            for sign in (1,-1):
                word = seq[0] + (seq[1] if sign>0 else inv(seq[1]))
                assert compare(m,sizes,[],word)['same_component']
                # Comparing after the same nonpure exterior path transports
                # both written ends and leaves the answer independent of it.
                assert compare(m,sizes,(1,),word+(1,))['same_component']
                accepted += 2
        for j,k in combinations(range(len(sizes)),2):
            if min(sizes[j],sizes[k]) < 2:
                continue
            i = offsets[j]+sizes[j]-1
            stem = tuple(range(i+1,offsets[k]))
            crossing = stem+(offsets[k],)*2+inv(stem)
            verdict = compare(m,sizes,[],crossing)
            assert all(verdict['internal_trivial']) and verdict['through_trivial'] and any(verdict['disk_words'])
            rejected += 1
        for i,k in zip(offsets,sizes):
            if k > 1:
                verdict = compare(m,sizes,[],(i+1,i+1))
                assert not any(verdict['disk_words']) and not all(verdict['internal_trivial'])
                rejected += 1
        if m==2:
            verdict = compare(m,sizes,[],(1,1))
            assert not any(verdict['disk_words']) and not verdict['through_trivial']
            rejected += 1
    # Forgetting any whole packet loses this obstruction.
    sizes = [2,2,2]
    x,y = (2,2),(4,4)
    stem = (3,3)
    y = stem+y+inv(stem)
    word = x+y+inv(x)+inv(y)
    verdict = compare(0,sizes,[],word)
    assert not verdict['same_component'] and all(verdict['internal_trivial'])
    assert all(not reduced(restrict(6,word,pair)) for pair in combinations(range(6),2))
    for i in (0,2,4):
        kept = set(range(6))-{i,i+1}
        assert braid_image(4,restrict(6,word,kept))==braid_image(4,())
    print(f'{accepted} signed endpoint comparisons accepted; {rejected} independent disk, framing or through failures.')
    print('A three-packet commutator survives, although deleting any packet gives the identity braid.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(compare(data['through'],data['packets'],data.get('first',[]),data['second']),indent=2))
    else:
        audit()
