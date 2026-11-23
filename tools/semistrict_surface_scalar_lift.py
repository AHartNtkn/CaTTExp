"""Lift scalar cube atoms at an original positioned history, including nullary rules."""
import argparse
import json

from gray_globe_comparison import atom
from semistrict_surface_coloured_cubes import schedule
from semistrict_surface_odd_cubes import EDGE
from semistrict_surface_return_gaps import exchange_at
from semistrict_surface_interval_degrees import degree_bounds


def cube(history, marks, start, rank):
    if rank < 2 or start < 0 or start+rank > len(history):
        raise ValueError('cube outside temporal history')
    steps = history[start:start+rank]
    for (right,_),(left,b) in zip(steps,steps[1:]):
        if left+len(marks[b][0]) > right:
            return None
    # Original positions are measured before any events in this spatial block.
    shift = 0
    out = []
    for p,b in reversed(steps):
        out.append((p+shift,b))
        shift += len(marks[b][1])-len(marks[b][0])
    return history[:start]+tuple(out)+history[start+rank:]


def execute(history, word, marks):
    for i in word:
        if not 0 <= i < len(history)-1:
            raise ValueError('crossing outside temporal history')
        history = exchange_at(history,i,marks)
        if history is None:
            return None
    return history


def sector(history, word, marks):
    end = execute(history,word,marks)
    if end is None:
        return {'executable':False}
    order = list(range(len(history)))
    pairs = set()
    simple = True
    for i in word:
        a,b = order[i:i+2]
        pair = tuple(sorted((a,b)))
        if pair in pairs:
            simple = False
        pairs.add(pair)
        order[i:i+2] = b,a
    result = {'executable':True,'target':end,'permutation_braid':simple}
    if simple:
        (r,clique),_ = degree_bounds(tuple(range(len(order))),tuple(order),set())
        result.update(failing_higher_degrees=list(range(4,r+2)),
                      all_raw_from=max(4,r+2), reversed_occurrences=clique)
    return result


def checks():
    marks = {'b':('','x'),'d':('x',''),'s':('',''),'f':('x','xx'),'j':('xx','x')}
    examples = total = fits = 0
    # All literal typed histories on a one-edge loop graph up to this event width.
    def histories(n, path, h):
        if not n:
            yield h
            return
        for b,(l,r) in marks.items():
            for p in range(len(path)-len(l)+1):
                yield from histories(n-1,path[:p]+r+path[p+len(l):],h+((p,b),))
    for n in (2,3,4):
        readings = {schedule(n,face,last) for face in atom((EDGE,)*n)[2] for last in (False,True)}
        for h in histories(n,'x',()):
            expected = cube(h,marks,0,n)
            for word in readings:
                assert execute(h,word,marks) == expected
                total += 1
            examples += 1
            fits += expected is not None
    # Larger mixed charts include several zero-length boxes at the very same gap.
    for n in range(5,9):
        h = tuple((0,'s') for _ in range(n))
        for face in atom((EDGE,)*n)[2]:
            for word in (schedule(n,face,False),schedule(n,face,True)):
                assert execute(h,word,marks) == cube(h,marks,0,n)
                total += 1
    h = ((0,'b'),(0,'d'),(0,'s'))
    assert sector(h,(1,0),marks)['permutation_braid']
    assert not sector(((0,'s'),)*3,(0,0,1),marks)['permutation_braid']
    assert not sector(h,(0,),marks)['executable']
    print(f'{examples} literal histories, {fits} spatial cubes, {total} hemisphere readings')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sector', help='JSON with marks, temporal history [offset,name], '
                        'and zero-based adjacent crossing positions')
    args = parser.parse_args()
    if args.sector:
        with open(args.sector) as handle:
            d = json.load(handle)
        print(json.dumps(sector(tuple(map(tuple,d['history'])),d['word'],d['marks'])))
    else:
        checks()
