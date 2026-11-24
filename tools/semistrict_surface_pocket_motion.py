"""Decide the unmarked degree-five loop group for a pair of caps in a lens.

Input JSON has braid (the three-point seam) and optional turn (the signed
number of turns of both cap sites about their spectator). Output includes the
action of a compatible turn on based meridians of the scalar closure.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_chain_probe import peripheral,transport
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv
from semistrict_surface_pocket_closure import caps,enclose
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_spherical_relations import analyze as spheres


PACKET_TURN = tuple(cable([1,1],[1,2]))
CENTRE = (1,2)*3
# From the anchored bottom caps: the shell and p are opposite meridians,
# as are b and c. Only the three interior meridians cross the seam.
MERIDIANS = [(1,),(2,),(-2,)]


def power(word,n):
    return tuple(word)*n if n>=0 else inv(tuple(word))*(-n)


def analyze(data):
    braid = data['braid']
    k = data.get('turn',1)
    if type(k) is not int:
        raise ValueError('turn must be an integer')
    a,b,c,d = 1,0,0,1
    writhe = 0
    for g in braid:
        if type(g) is not int or abs(g) not in (1,2):
            raise ValueError('use signed three-strand braid letters')
        s = 1 if g>0 else -1
        writhe += s
        if abs(g)==1:
            b,d = b+s*a,d+s*c
        else:
            a,c = a-s*b,c-s*d
    result = dict(matrix=[[a,b],[c,d]],unmarked_loop_rank=int(b==0),
                  compatible_turn=k==0 or b==0)
    if result['compatible_turn']:
        result['unmarked_raw_filler'] = k==0
    if b==0:
        j = -a*c
        assert a*d==1 and (writhe-j)%6==0
        result.update(centre_power=(writhe-j)//6,daughter_half_twists=j)
        # The free presentation on x,y has no terminal cap relations here.
        final = transport(MERIDIANS,braid)
        assert final[0]==(1,) and not peripheral(final[1:])
        action = transport(MERIDIANS,power(PACKET_TURN,k))
        assert action[0]==(1,) and action[2]==inv(action[1])
        result['based_meridian_images'] = action[:2]
    return result


def audit():
    assert braid_image(3,PACKET_TURN)==braid_image(3,CENTRE+(-2,-2))
    checked = compatible = 0
    for length in range(6):
        for word in product((1,-1,2,-2),repeat=length):
            result = analyze(dict(braid=word))
            # Compare the two actual expanded site generators on the seam.
            commutes = braid_image(3,PACKET_TURN+word)==braid_image(3,word+PACKET_TURN)
            assert commutes==bool(result['unmarked_loop_rank'])
            if commutes:
                normal = power(CENTRE,result['centre_power'])+power((2,),result['daughter_half_twists'])
                assert braid_image(3,word)==braid_image(3,normal)
                compatible += 1
            checked += 1
    for q in range(-2,3):
        for j in range(-3,4):
            word = power(CENTRE,q)+power((2,),j)
            for k in range(-3,4):
                result = analyze(dict(braid=word,turn=k))
                assert result['centre_power']==q and result['daughter_half_twists']==j
                x,y = result['based_meridian_images']
                assert x==(1,) and y==power((1,),-k)+(2,)+power((1,),k)
    for word,free in [((),True),((2,-1,1),True),(CENTRE,True),(PACKET_TURN,True),
                      ((1,1),False),((-1,-1),False)]:
        result = analyze(dict(braid=word))
        assert bool(result['unmarked_loop_rank'])==free
        for mode,r in [('wired',int(free)),('anchored',1+int(free))]:
            p = spheres(enclose(caps(word),mode))
            assert p['sphere_orbits']==r and p['generators']==2
            if free:
                assert not p['faces']
    print(f'{checked} three-strand seams agree with the Artin test; {compatible} admit a nonzero cap turn')
    print('245 based actions checked, including both turn signs and nonzero central seam powers')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
