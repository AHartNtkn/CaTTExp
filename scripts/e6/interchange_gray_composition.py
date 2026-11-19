"""Check exterior-invariant charges and the generic composition tests for the Gray action."""

from collections import Counter
from itertools import product

from interchange_cylinders import atom, compose, generators, tensor_boundary
from interchange_subdivision import stack_image


def pivot(degrees):
    if max(degrees) > 2 or sum(degrees) != 4:
        return None
    if 2 in degrees:
        return degrees.index(2)
    return [i for i, d in enumerate(degrees) if d][1]


def primitive(basis, ceiling):
    degrees = [len(x)-1 for x in basis]
    result = 0
    for i, x in enumerate(basis):
        upper = degrees.copy()
        upper[i] += 1
        if pivot(upper) == i:
            height = x[-1]
            assert 0 <= height <= ceiling
            result += 2 * (ceiling-height if sum(degrees[:i]) % 2 else height)
    return result


def check_primitive():
    point = ()
    string = (point, point, point)
    surface = (string, point, string)
    solid = (surface, string)
    four = (solid, surface)
    differential_checks = exterior_checks = 0
    patterns = set()
    for shape in [(four,), (four, solid), (surface, string, solid), (string, surface, string, string)]:
        for basis in product(*(generators(t) for t in shape)):
            degrees = tuple(len(x)-1 for x in basis)
            if sum(degrees) == 4:
                value = sum(sign * primitive(face, 4) for face, sign in tensor_boundary(basis))
                assert value == (2 if max(degrees) <= 2 else 0)
                patterns.add(tuple(d for d in degrees if d))
                differential_checks += 1
            if sum(degrees) == 3:
                target = primitive(basis, 4)
                for a, b in product(range(4), repeat=2):
                    assert primitive(((a,),)+basis+((b,),), 4) == target
                    exterior_checks += 1
    assert len(patterns) == 8
    return differential_checks, exterior_checks


def check_stationary(p, slot, mid, end):
    """Carry the actual prefix/suffix around each subcylinder up the unary tower."""
    fixed = 1-slot

    def pair(x, b):
        return (x, b) if slot == 0 else (b, x)

    def chunk(x, part):
        lo, hi = ((0, mid), (mid, end))[part]
        return stack_image(atom(pair(x, (1, 2))), 1, fixed, lo, hi)

    def left(z):
        return compose(chunk((0, 0), 0), z, 0)

    def right(z):
        return compose(z, chunk((0, 1), 1), 0)

    if slot == 0:
        order = [1, 0]
        contexts = {1: left, 0: right}
    else:
        order = [0, 1]
        contexts = {0: right, 1: left}

    for k in range(1, p+1):
        for side in ((0, 1) if k < p else (2,)):
            x = (k, side)
            first, second = (contexts[i](chunk(x, i)) for i in order)
            assert compose(first, second, k) == stack_image(atom(pair(x, (1, 2))), 1, fixed, 0, end)
        if k == p:
            break
        a, b = order
        prefix = contexts[a](chunk((k, 0), a))
        suffix = contexts[b](chunk((k, 1), b))
        old_a, old_b = contexts[a], contexts[b]
        contexts[a] = lambda z, old=old_a, post=suffix, cut=k: compose(old(z), post, cut)
        contexts[b] = lambda z, old=old_b, pre=prefix, cut=k: compose(pre, old(z), cut)
        if slot == 0:
            order.reverse()


def whiskered(p, cut, prefix):
    """Glue the two globes along their indicated i-face and form the top whiskering."""
    def disk(which, dim):
        def label(k, s):
            if k < cut or (k == cut and which == "Z" and s == int(prefix)):
                return ("X", k, 1-s if k == cut else s)
            return (which, k, s)
        return tuple(tuple((label(k, side if k < dim else 2),) for side in range(2))
                     for k in range(dim+1))

    x, z = disk("X", p), disk("Z", cut+1)
    return compose(z, x, cut) if prefix else compose(x, z, cut)


def check_whisker(p, cut, prefix, slot):
    moving = whiskered(p, cut, prefix)

    def retract(g):
        which, k, side = g
        if which == "X":
            return [(k, side)]
        if k == cut:
            return [(k, int(not prefix))]
        assert k == cut+1
        return []

    edge = ((((0, 0),), ((0, 1),)), (((1, 2),), ((1, 2),)))
    tensor = []
    for k in range(p+2):
        rows = []
        for side in range(2):
            chain = []
            for i in range(k+1):
                j = k-i
                a, b = (i, j) if slot == 0 else (j, i)
                if a > p or b > 1:
                    continue
                for x in moving[a][side if slot == 0 else side ^ (i % 2)]:
                    for y in edge[b][side ^ (i % 2) if slot == 0 else side]:
                        chain.append((x, y) if slot == 0 else (y, x))
            rows.append(chain)
        tensor.append(rows)
    assert len(tensor[-1][0]) == 1 and tensor[-1][0][0][slot] == ("X", p, 2)
    expected = atom(((p, 2), (1, 2)) if slot == 0 else ((1, 2), (p, 2)))
    for k, rows in enumerate(tensor):
        for side, chain in enumerate(rows):
            image = Counter()
            for basis in chain:
                for x in retract(basis[slot]):
                    image[basis[:slot]+(x,)+basis[slot+1:]] += 1
            assert image == Counter(expected[k][side])


if __name__ == "__main__":
    d, e = check_primitive()
    print(f"Checked the primitive on {d} differentials and {e} exterior vertex pairs.")
    count = 0
    for p, slot, (mid, end) in product(range(2, 13), range(2), ((1, 2), (2, 5), (4, 6))):
        check_stationary(p, slot, mid, end)
        count += 1
    print(f"Pasted all stationary subdivisions in {count} signed disk tests through degree twelve.")
    count = 0
    for p in range(2, 11):
        for cut, prefix, slot in product(range(p-1), (False, True), range(2)):
            check_whisker(p, cut, prefix, slot)
            count += 1
    print(f"Checked the top atom and all retracted rows on {count} basic whiskerings.")
