"""Decide old directed braid comparisons on disjoint two- and three-strand blocks."""
import argparse
from collections import deque
from itertools import product


def steps(word):
    for i in range(len(word)-2):
        a,b,c = word[i:i+3]
        if a==c and abs(a-b)==1:
            yield i, (1 if b>a else -1), word[:i]+(b,a,b)+word[i+3:]


def route(start,goal):
    parents = {start:None}
    todo = deque([start])
    while todo and goal not in parents:
        w = todo.popleft()
        for i,sign,v in steps(w):
            if v not in parents:
                parents[v] = w,i,sign
                todo.append(v)
    if goal not in parents:
        return None
    moves = []
    while parents[goal]:
        goal,i,sign = parents[goal]
        moves.append((i,sign))
    return moves[::-1]


def positive_diagram(start, moves):
    """Cancel consecutive opposite boxes along a full three-port seam."""
    live = [(-1,i) for i in range(len(start))]
    boxes = {}
    for idx,(i,sign) in enumerate(moves):
        inputs = tuple(live[i:i+3])
        creator = inputs[0][0]
        if (creator in boxes and boxes[creator][0] == -sign and
                inputs == tuple((creator,j) for j in range(3))):
            _,old_inputs = boxes.pop(creator)
            live[i:i+3] = old_inputs
        else:
            boxes[idx] = sign,inputs
            live[i:i+3] = [(idx,j) for j in range(3)]
    if any(sign<0 for sign,_ in boxes.values()):
        return None
    live = [(-1,i) for i in range(len(start))]
    result = []
    for idx,(_,inputs) in boxes.items():
        i = live.index(inputs[0])
        assert tuple(live[i:i+3]) == inputs
        result.append(i)
        live[i:i+3] = [(idx,j) for j in range(3)]
    return result


def blocks(start,goal):
    if set(start) != set(goal):
        return False, None
    groups = []
    for a in sorted(set(start)):
        if groups and a == groups[-1][-1]+1:
            groups[-1].append(a)
        else:
            groups.append([a])
    if any(len(g)>2 for g in groups):
        raise ValueError('a connected letter component uses more than three strands')
    result = {}
    for group in groups:
        s,t = (tuple(a for a in w if a in group) for w in (start,goal))
        path = route(s,t)
        if path is None:
            return False, None
        result[tuple(group)] = positive_diagram(s,path)
    return True, result if all(moves is not None for moves in result.values()) else None


def checks():
    comparisons = paths = 0
    for n in range(11):
        remaining = set(product((1,2),repeat=n))
        while remaining:
            base = remaining.pop()
            component = {base:[]}
            todo = [base]
            while todo:
                w = todo.pop()
                for i,sign,v in steps(w):
                    if v not in component:
                        remaining.remove(v)
                        component[v] = component[w]+[(i,sign)]
                        todo.append(v)
            for w,root_path in component.items():
                reached,stack = {w},[w]
                while stack:
                    for _,sign,v in steps(stack.pop()):
                        if sign>0 and v not in reached:
                            reached.add(v)
                            stack.append(v)
                back = [(i,-sgn) for i,sgn in reversed(root_path)]
                for v,tail in component.items():
                    cert = positive_diagram(w,back+tail)
                    assert (cert is not None) == (v in reached)
                    if cert is not None:
                        cur = w
                        for pos in cert:
                            cur = next(u for i,sign,u in steps(cur) if i==pos and sign>0)
                        assert cur==v
                    comparisons += 1
                for i,sgn,v in steps(w):
                    loop = root_path+[(i,sgn)]+[(j,-s) for j,s in reversed(component[v])]
                    assert positive_diagram(base,loop) == []
                    paths += 1
    assert blocks((1,5,2,6,1,5),(6,2,5,1,6,2)) == (True, {(1,2):[0],(5,6):[0]})
    assert blocks((2,1,2),(1,2,1)) == (True,None)
    print(f'{comparisons} signed-diagram decisions against directed reachability, '
          f'{paths} reduced loop diagrams, disjoint block replay passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--words',nargs=2,help='two comma-separated positive braid words')
    args = parser.parse_args()
    if args.words:
        words = [tuple(map(int,w.split(','))) if w else () for w in args.words]
        signed,cert = blocks(*words)
        print('surface',signed,'raw',cert is not None,'directed block certificates',cert)
    else:
        checks()
