"""Realize every height-three witness profile of cost at most eight by pure crossings."""
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product

from interchange_path_grading import History, cross, i_faces, r_faces, t_faces, word


def profiles(n):
    # Read the gaps between consecutive fresh strands. A gap either
    # continues a bundle, starts a new old slot, or starts an outer factor.
    for gaps in product(range(3), repeat=n-1):
        groups = [[[]]]
        for i in range(n):
            if i and gaps[i-1] == 2:
                groups.append([[]])
            elif i and gaps[i-1] == 1:
                groups[-1].append([])
            groups[-1][-1].append(i)
        yield tuple(tuple(tuple(bundle) for bundle in group) for group in groups)


@cache
def layers(bundle):
    small, *rest = bundle
    result = []
    for k in range(len(bundle)):
        cut = len(rest)-k
        result.append(word((*rest[:cut], small, *rest[cut:])))
    return tuple(result)


def step(state, pair):
    a,b = pair
    i = state.index(a)
    assert a > b and state[i+1] == b
    return state[:i] + (b,a) + state[i+2:]


def verify_profile(n, groups):
    counts = Counter(profiles=1)
    for group in groups:
        for block in group:
            faces = layers(block)
            for layer, face in enumerate(faces):
                # The old parallel 2-faces all have the same two 1-words.
                initial = [int(i < block[0]) for i in range(n)]
                terminal = initial.copy()
                for strand,_ in face:
                    assert terminal[strand] == 0
                    terminal[strand] = 1
                assert terminal == [int(i <= block[-1]) for i in range(n)]
                if layer+1 < len(faces):
                    pair = (block[-1-layer], block[0])
                    values = tuple(i for i,_ in face)
                    assert step(values,pair) == tuple(i for i,_ in faces[layer+1])
                    counts['advances'] += 1
    for left,right in combinations(groups,2):
        for a,b in product(left,right):
            for alpha,beta in product(layers(a),layers(b)):
                crossing = cross(alpha,beta)
                assert crossing.mass == len(a)*len(b)
                assert crossing.start == beta+alpha and crossing.end == alpha+beta
                counts['outer faces'] += 1
    return counts


@cache
def completions(state):
    successors = [step(state, pair) for pair in zip(state,state[1:]) if pair[0] > pair[1]]
    return sum(completions(s) for s in successors) if successors else 1


def witness_moves():
    # Two unary events in formerly distinct slots become an inner exchange
    # of actual crossings. A unary variation against a two-strand stationary
    # word has two triangle atoms. The join has the same mixed top chain.
    a = cross(word((0,)),word((1,)))
    b = cross(word((2,)),word((3,)))
    s,t = i_faces(a,b)
    assert s.events != t.events and s.start == t.start and s.end == t.end
    s,t = r_faces(a,b.end)
    assert a.mass * len(b.end) == 2 and s.events != t.events
    s,t = t_faces(a.start,b)
    assert len(a.start)*b.mass == 2 and s.events != t.events
    s = b.pad(right=a.start).then(cross(a.start,b.end)).then(a.pad(right=b.end))
    t = a.pad(left=b.start).then(b.pad(right=a.end)).then(cross(a.end,b.end))
    assert s.start == t.start and s.end == t.end and s.events != t.events


def check_sharp_charge():
    # Equation (15) on five spectator slots and a single moving crossing.
    # Its two routes start and end at the same actual sorting histories.
    first = word(range(5))
    a = cross(word((5,)), word((6,)))
    b = word((7,))
    stationary_block = cross(first,b)
    wide = r_faces(a.pad(left=first),b)
    correction = i_faces(stationary_block,a)
    suffix = cross(a.end,b).pad(left=first)
    correction = tuple(part.then(suffix) for part in correction)
    assert wide[1] == correction[0]
    narrow = tuple(stationary_block.pad(right=a.start).then(face.pad(left=first))
                   for face in r_faces(a,b))
    assert (wide[0], correction[1]) == narrow

    early = set(stationary_block.events)
    late = set(wide[0].events)-early
    assert len(early) == 5 and len(late) == 3
    def weight(selected):
        if a.events[0] not in selected:
            return 0
        return 100 - len(early & selected)
    assert weight(early|late)-weight(early)-weight(late) == -5
    assert len(tuple(product(stationary_block.events,a.events))) == 5

    # Place a proper early inner edge before the stationary block, using
    # only the existing spectator slots. The narrow late triangle survives.
    early_pair = i_faces(cross(word((0,)), word((1,))),
                         cross(word((2,)), word((3,))))
    for face in early_pair:
        padded = face.pad(left=b, right=word((4,))+a.start)
        assert padded.end == narrow[0].start
    for n in range(3,9):
        for u in range(2,n):
            for size in range(1,n-u+1):
                assert 2*(u-2)+size-1 <= 2*(n-3)
    print('The wide triangle has defect -5; its correcting inner edge exchanges five opposite-color pairs.')


def check():
    counts = Counter()
    for n in range(1,9):
        for shape in profiles(n):
            counts.update(verify_profile(n,shape))
    witness_moves()
    check_sharp_charge()
    increasing = tuple(range(8))
    decreasing = increasing[::-1]
    raw = completions(decreasing)
    assert completions.cache_info().currsize == 40320
    # Every permutation lies on a full history. Relabelling in the order
    # dual to a chosen cut gives a sorting path from the reverse permutation.
    for cut in permutations(increasing):
        assert completions(cut) > 0
        pos = {v:i for i,v in enumerate(cut)}
        relative = tuple(pos[v] for v in decreasing)
        assert completions(relative) > 0
    print(dict(sorted(counts.items())))
    print(f'Full eight-strand interval: 40320 permutation states, {raw} raw histories.')


if __name__ == '__main__':
    check()
