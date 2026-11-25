"""Convert a nonzero structural track on a complete-incidence plat into a Brunnian track.

Input JSON gives lower and upper ordered packet sizes, seam and track Artin
words, and optional depth (default two). Output brackets the track successively
with the listed test braids. Each step preserves a proposed surface filling.
"""
from argparse import ArgumentParser
from itertools import accumulate
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_packet_disks import compare
from semistrict_surface_plat_tracks import brunnian, comm, peripheral, sphere_action, sphere_push
from semistrict_surface_scalar_leaves import swapped
from semistrict_surface_trefoil_mixed import substitute


def conjugator_family(n):
    seed = brunnian(n)
    movers = [peripheral(i,n) for i in range(n-1)]
    second = reduced(movers[0]+seed+inv(movers[0]))
    for mover in [(),*movers]:
        for w in (seed,second):
            yield reduced(mover+w+inv(mover))


def deepen(lower,upper,seam,track,depth=2):
    if any(type(k) is not int or k < 1 for k in [*lower,*upper]):
        raise ValueError('packet sizes must be positive')
    n = sum(lower)
    if sum(upper)!=n or min(len(lower),len(upper))<2:
        raise ValueError('expected two partitions of the same row, each with at least two packets')
    if any(type(g) is not int or not 0<abs(g)<n for w in (seam,track) for g in w):
        raise ValueError('invalid middle-cut letter')
    if type(depth) is not int or depth<1:
        raise ValueError('depth must be positive')
    row = swapped(range(n),seam)
    cuts = list(accumulate(upper,initial=0))
    starts = list(accumulate(lower,initial=0))
    for a,b in zip(cuts,cuts[1:]):
        packet = set(row[a:b])
        if not all(packet.intersection(range(u,v)) for u,v in zip(starts,starts[1:])):
            raise ValueError('a closing packet misses an opening packet')
    track = tuple(track)
    transported = inv(seam)+track+tuple(seam)
    if not (compare(0,lower,track,[])['same_component'] and compare(0,upper,transported,[])['same_component']):
        raise ValueError('the proposed track fails a packet test')
    action = sphere_action(track,n)
    if action==[(i,) for i in range(1,n)]:
        return dict(raw_null=True)
    steps = []
    push = ()
    for step in range(depth):
        for test in conjugator_family(n):
            s = sphere_push(test,n)
            moved = substitute(s,action) if not step else reduced(push+s+inv(push))
            if moved!=s:
                push = reduced(moved+inv(s))
                steps.append(test)
                break
        else:
            raise AssertionError('nonidentity action fixed the entire test family')
    return dict(raw_null=False, successive_commutator_partners=steps, infinity_push=push)


def audit():
    # One original track has nonzero linking on the unmatched pairs; the
    # other is itself the seed, so the first commutator partner must change.
    turn = (1,2,3)*4
    # Lower 12|34 and upper 13|24. exponents e2=e3=1 and t=-1.
    old = peripheral(1)+peripheral(2)+inv(turn)
    cases = [(old,(2,)),(brunnian(4),(2,2,2))]
    for w,seam in cases:
        res = deepen([2,2],[2,2],seam,w,3)
        for partner in res['successive_commutator_partners']:
            w = comm(w,partner)
            assert sphere_push(w)
            for i in range(4):
                sub = restrict(4,w,set(range(4))-{i})
                assert sphere_push(sub,3)==() and not sum(restrict(3,sub,{0,1}))
        assert sphere_push(w)==res['infinity_push']
    assert deepen([2,2],[2,2],(2,),[])==dict(raw_null=True)
    seam = (3,2,4)  # 0,3,1,4,2,5, the transpose of a 2-by-3 rectangle
    res = deepen([3,3],[2,2,2],seam,brunnian(6))
    assert res['infinity_push'] and len(res['successive_commutator_partners'])==2
    print('Three successive nonzero Brunnian commutators checked at each of two four-strand plats.')
    print('The six-strand rectangular plat passed both packet tests and the depth-two conversion.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(deepen(**json.loads(args.input.read_text())),indent=2))
    else:
        audit()
