"""Check signed simultaneous rod frames decorated by scalar faces with exterior sinks."""
from collections import Counter, defaultdict
from itertools import product

from semistrict_surface_one_sided_frames import ARITY, FACES, Circuits
from semistrict_surface_spatial_frames import flag_check


def faces(diagrams, rows):
    # Identify adjacent slices of the complement by their left and right
    # boundaries, including both incidences of the joined gap after a death.
    graph = defaultdict(set)
    roots = {}
    width = len(diagrams.inputs)
    for h, (node, i) in enumerate(rows):
        n, m = ARITY[node[0]]
        bottom = list(range(i+1)) + list(range(i+n, width+1))
        top = list(range(i+1)) + list(range(i+m, width+m-n+1))
        for b, t in zip(bottom, top, strict=True):
            graph[h,b].add((h+1,t))
            graph[h+1,t].add((h,b))
        for q in range(1,n):
            roots[h,i+q] = (node, q)
        width += m-n
    for q in range(width+1):
        roots[len(rows),q] = ('top',q)
    by_spot = {}
    for start, root in roots.items():
        assert start not in by_spot
        stack = [start]
        while stack:
            p = stack.pop()
            if p not in by_spot:
                by_spot[p] = root
                stack.extend(graph[p])
            else:
                assert by_spot[p] == root
    assert set(by_spot) == set(graph) | roots.keys()
    return by_spot


def expand(diagrams, rows, signs):
    result = []
    image = {}
    live = diagrams.inputs
    for original, i in rows:
        g = original[0]
        if g in FACES:
            g, shift = FACES[g][signs[original]]
            i += shift
        node, live = diagrams.step(live, g, i)
        result.append((node, i))
        image[original] = node
    return result, image


def audit(width, bound):
    diagrams = Circuits(width)
    corners = defaultdict(Counter)
    rejected = merged = 0
    for rows in diagrams.charts(bound):
        marked = [node for node, _ in rows if node[0] in FACES]
        if len({g for g,_ in marked}) < len(marked) or not diagrams.common_slice(rows):
            continue
        by_spot = faces(diagrams, rows)
        roots = set(by_spot.values())
        allowed = {s for s in roots if s[0] not in marked}
        rejected += len(roots - allowed)
        for bits in product((0, 1), repeat=len(marked)):
            signs = dict(zip(marked, bits))
            ordinary, image = expand(diagrams, rows, signs)
            after = faces(diagrams, ordinary)
            germs = frozenset((n[0], signs[n], diagrams.expand(rows, signs, n)) for n in marked)
            end = diagrams.expand(rows, signs)
            read = {}
            for spot, r in by_spot.items():
                if r not in allowed:
                    continue
                wanted = (image.get(r[0], r[0]), r[1])
                assert after[spot] == wanted
                read[r] = wanted
            assert set(read) == allowed and len(set(read.values())) == len(read)
            for root in roots - allowed:
                if any(after[p] in read.values() for p,r in by_spot.items() if r == root):
                    merged += 1
            choices = [None, *allowed]
            for left, right in product(choices, repeat=2):
                scalars = [(s, read[r]) for s,r in zip('xy',(left,right)) if r is not None]
                corners[end][germs.union(scalars)] += 1
    counts = flag_check(corners)
    assert rejected and merged
    print(width, 'inputs,', bound, 'gates: unique corners', counts,
          'marker-rooted faces', rejected, 'expansions joining a retained face', merged)


if __name__ == '__main__':
    audit(3, 2)
    audit(3, 3)
    audit(5, 3)
