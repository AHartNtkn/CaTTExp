"""Solve directed attachments over a supplied reversible kernel or the open pair.

Input uses coefficient_kernels JSON plus rules and optional counts/face.
The returned unit_rules generate the exact reversible reduction of the context.
"""
import json
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from semistrict_surface_coefficient_kernels import image_rows
from semistrict_surface_deck_monoid import decisions
from semistrict_surface_directed_top_counts import uses
from semistrict_surface_quadratic_image import reduction


def solve(data):
    rows,kernel = image_rows(data)
    rules = data['rules']
    width = len(data['top'])
    if any(len(v) != width or any(type(c) is not int for c in v) for v in rules):
        raise ValueError('each directed rule needs integral top coordinates')
    unit_flags = decisions(rows,rules,[[-x for x in v] for v in rules]) if rules else []
    units = [i for i,flag in enumerate(unit_flags) if flag]
    _,order = reduction(rows+[rules[i] for i in units],width)
    reflects = all(order(v) == 1 for v in kernel)
    pair = data.get('lower') == 'pair'
    answer = dict(unit_rules=units,degree_reflection=('yes' if reflects else
                  'equivalent_to_pair_nonfilling' if pair else 'no'))
    if 'face' in data:
        face = data['face']
        if len(face) != width:
            raise ValueError('face width must match the top group')
        counts = data.get('counts')
        raw = uses(rows,rules,face,counts)
        lifted = raw if raw is not None else uses(rows+kernel,rules,face,counts)
        answer['raw_counts'] = raw
        answer['surface_counts_if_pair_fills' if pair else 'surface_counts'] = lifted
        answer['fills'] = ('no' if lifted is None else 'equivalent_to_pair_filling'
                           if pair and raw is None else 'yes')
    elif 'counts' in data:
        raise ValueError('prescribed counts require a face')
    return answer


def audit():
    base = dict(lower='pair',top=[4,0],evaluation=[[1,0],[0,0],[0,0]])
    rules = [[1,2],[0,3]]
    rows,kernel = image_rows(base)
    faces = [[r,k] for r,k in product(range(4),range(-4,31))]
    raw = decisions(rows,rules,faces)
    possible = decisions(rows+kernel,rules,faces)
    for (residue,t),a,b in zip(faces,raw,possible,strict=True):
        choices = [i for i in range(16) if t >= 2*i and (t-2*i) % 3 == 0]
        assert a == any(i % 4 == residue for i in choices)
        assert b == any((i-residue) % 2 == 0 for i in choices)
    assert [f[1] for f,a,b in zip(faces,raw,possible) if f[0] == 0 and b and not a] == [4,7,10,13]
    # Exhaust the directed graph itself on a finite top. A rule is a unit iff
    # its reverse has a path; all finite top moves satisfy this independently.
    complete = 0
    for left,right in product(range(4),range(2)):
        steps = [[left,right]]
        reached = {((n*left) % 4,(n*right) % 2) for n in range(4)}
        data = dict(lower='pair',top=[4,2],evaluation=[[1,0],[0,0],[0,0]],rules=steps)
        result = solve(data)
        assert result['unit_rules'] == [0]
        assert (result['degree_reflection'] == 'yes') == ((2,0) in reached)
        faces2 = list(product(range(4),range(2)))
        periods,image = image_rows(data)
        lifted = reached | {((a+2) % 4,b) for a,b in reached}
        assert decisions(periods,steps,faces2) == [f in reached for f in faces2]
        assert decisions(periods+image,steps,faces2) == [f in lifted for f in faces2]
        complete += len(faces2)
    data = dict(base,rules=rules,face=[0,4])
    assert solve(dict(data,counts=[2,0]))['fills'] == 'equivalent_to_pair_filling'
    assert solve(dict(data,counts=[0,2]))['fills'] == 'no'
    repaired = solve(dict(base,rules=rules+[[-1,-2],[2,0]]))
    assert repaired['unit_rules'] == [0,1,2,3] and repaired['degree_reflection'] == 'yes'
    only_torsion = solve(dict(base,rules=rules+[[2,0]]))
    assert only_torsion['unit_rules'] == [2] and only_torsion['degree_reflection'] == 'yes'
    return len(faces),complete


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(solve(json.loads(args.input.read_text()))))
        except (KeyError,TypeError,ValueError) as error:
            parser.error(str(error))
    else:
        print('%d infinite-group slice queries and %d finite directed reachability queries checked.' % audit())
