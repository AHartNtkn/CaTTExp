"""Check the temporal factorization and inner horn claims of round 3, Response 2."""

from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product


@dataclass(frozen=True)
class Atom:
    source: int
    target: int


@dataclass(frozen=True)
class Row:
    source: int
    factors: tuple = ()

    @property
    def target(self):
        return self.factors[-1].target if self.factors else self.source


@dataclass(frozen=True)
class Box:
    cut: int
    left: Row
    right: Row

    # Both products identify different pairs of component objects.
    @property
    def source(self):
        return self.left.source ^ self.right.source

    @property
    def target(self):
        return self.left.target ^ self.right.target


def lower(cut, left, right):
    box = Box(cut, left, right)
    return Row(box.source, (box,) if left.factors or right.factors else ())


@cache
def compose(left, right):
    assert left.target == right.source
    if left.factors and right.factors:
        a, b = left.factors[-1], right.factors[0]
        if (isinstance(a, Box) and isinstance(b, Box) and a.cut == b.cut
                and a.left.target == b.left.source and a.right.target == b.right.source):
            joined = Box(a.cut, compose(a.left, b.left), compose(a.right, b.right))
            return Row(left.source, left.factors[:-1] + (joined,) + right.factors[1:])
    return Row(left.source, left.factors + right.factors)


def events(row, address=()):
    """Return addresses and strict predecessor indices in normal-form order."""
    result = []
    for factor in row.factors:
        previous = frozenset(range(len(result)))
        if isinstance(factor, Atom):
            result.append((address, previous))
        else:
            for side, child in enumerate((factor.left, factor.right)):
                offset = len(result)
                for path, preds in events(child, address + ((factor.cut, side),)):
                    result.append((path, previous | {offset + i for i in preds}))
    return result


def unit_carries(letters, cuts):
    for letter, cut, value in product(letters, cuts, range(2)):
        yield lower(cut, letter, Row(value))
        yield lower(cut, Row(value), letter)


def order_ideals(poset):
    positions = range(len(poset))
    ideals = {frozenset(choice)
              for size in range(len(poset) + 1) for choice in combinations(positions, size)
              if all(poset[i][1].issubset(choice) for i in choice)}
    return ideals


@cache
def folded_image(row):
    """Identify all objects; erase, duplicate, or box the image of each atom."""
    image = Row(0)
    loop = Row(0, (Atom(0, 0),))
    for factor in row.factors:
        if isinstance(factor, Box):
            part = lower(factor.cut, folded_image(factor.left), folded_image(factor.right))
        elif factor.source == factor.target == 0:
            part = Row(0)
        elif factor.source == factor.target:
            part = lower(1, loop, loop)
        elif factor.source == 0:
            part = compose(loop, loop)
        else:
            part = loop
        image = compose(image, part)
    return image


def check_substituted_cuts(total, cuts):
    image = folded_image(total)
    positions = events(image)
    images = {}
    # Occurrences with the same full box address are ordered in their row.
    # A prefix therefore uses an initial segment at each address.
    for ideal, (prefix, suffix) in cuts.items():
        first, last = folded_image(prefix), folded_image(suffix)
        assert compose(first, last) == image
        counts = Counter(path for path, _ in events(first))
        used = set()
        for i, (path, _) in enumerate(positions):
            if counts[path]:
                used.add(i)
                counts[path] -= 1
        assert not any(counts.values())
        assert all(positions[i][1] <= used for i in used)
        images[ideal] = used

    # Recover the unique original position of each image event from the cuts
    # containing it and check both monotonicity and the inverse-image formula.
    original = events(total)
    marks = []
    for i in range(len(positions)):
        containing = [a for a, b in images.items() if i in b]
        least = frozenset.intersection(*containing)
        tips = [j for j in least if original[j][1] | {j} == least]
        assert len(tips) == 1
        marks.append(tips[0])
    for i, (_, predecessors) in enumerate(positions):
        assert all(marks[j] in original[marks[i]][1] | {marks[i]} for j in predecessors)
    for a, b in images.items():
        assert {i for i, mark in enumerate(marks) if mark in a} == b


def check_rows(letters, length):
    # Enumerate paths before identifying them by the grid laws. Retain the
    # actual factor pairs, even when every underlying object in a path repeats.
    grouped = defaultdict(dict)
    serial_orders = defaultdict(set)
    paths = 0
    for path in product(letters, repeat=length):
        if any(a.target != b.source for a, b in zip(path, path[1:])):
            continue
        paths += 1
        prefixes = [Row(path[0].source)]
        for a in path:
            prefixes.append(compose(prefixes[-1], a))
        suffixes = [Row(path[-1].target)]
        for a in reversed(path):
            suffixes.append(compose(a, suffixes[-1]))
        total = prefixes[-1]
        poset = events(total)
        by_address = defaultdict(list)
        for i, (address, _) in reversed(list(enumerate(poset))):
            by_address[address].append(i)
        order = tuple(by_address[events(a)[0][0]].pop() for a in path)
        assert order not in serial_orders[total]
        serial_orders[total].add(order)
        for k, (prefix, suffix) in enumerate(zip(prefixes, reversed(suffixes))):
            assert compose(prefix, suffix) == total
            ideal = frozenset(order[:k])
            pair = (prefix, suffix)
            assert grouped[total].setdefault(ideal, pair) == pair

    for total, cuts in grouped.items():
        poset = events(total)
        ideals = order_ideals(poset)
        assert cuts.keys() == ideals and len(set(cuts.values())) == len(ideals)
        check_substituted_cuts(total, cuts)
        ways = {frozenset(): 1}
        for ideal in sorted(ideals, key=len)[1:]:
            ways[ideal] = sum(ways.get(ideal - {i}, 0) for i in ideal)
        assert ways[frozenset(range(length))] == len(serial_orders[total])
    return paths, len(grouped)


def check_horns(poset):
    ideals = order_ideals(poset)
    empty, full = frozenset(), frozenset(range(len(poset)))
    proper = ideals - {empty, full}
    # Nondegenerate simplices of the proper ideal poset, including the empty
    # chain. Adding both endpoints will make every paired face an inner face.
    chains = {()}
    for ideal in sorted(proper, key=len):
        chains |= {s + (ideal,) for s in chains if not s or s[-1] < ideal}
    if not any(preds for _, preds in poset):
        assert len(ideals) == 2 ** len(poset)
        return 0
    u = next(i for i, (_, preds) in enumerate(poset)
             if not preds and any(i in above for _, above in poset))
    pairs = []

    def delete_pair(small, large):
        # Any other coface would prevent this collapse from being elementary.
        assert large in chains and small in chains
        assert not any(len(c) == len(large) and c != large and set(small) <= set(c)
                       for c in chains)
        pairs.append((small, large))
        chains.difference_update((small, large))

    for ideal in sorted((i for i in proper if u not in i), key=len, reverse=True):
        tip = ideal | {u}
        for chain in sorted((c for c in chains if ideal in c and tip not in c),
                            key=len, reverse=True):
            delete_pair(chain, tuple(sorted((*chain, tip), key=len)))
    tip = frozenset({u})
    for chain in sorted((c for c in chains if tip not in c), key=len, reverse=True):
        delete_pair(chain, (tip,) + chain)
    assert not chains

    known = set()
    for small, large in reversed(pairs):
        assert small not in known and large not in known
        for i in range(len(large)):
            face = large[:i] + large[i + 1:]
            assert face == small or face in known
        known.update((small, large))
    return len(pairs)


if __name__ == '__main__':
    atoms = [Row(s, (Atom(s, t),)) for s, t in product(range(2), repeat=2)]
    flat = atoms + list(unit_carries(atoms, (0, 1)))
    mixed = flat + list(unit_carries(unit_carries(atoms, (0,)), (1,)))
    for alphabet, length in ((flat, 3), (mixed, 2)):
        paths, arrows = check_rows(alphabet, length)
        print(f'{paths} serial paths, {arrows} normalized arrows: cuts, orders, and substitution agree.')
    loop = atoms[0]
    par = lower(0, loop, loop)
    examples = [lower(1, par, par), compose(par, par),
                lower(1, compose(loop, loop), par), compose(loop, lower(1, par, par))]
    horns = sum(check_horns(events(row)) for row in examples)
    print(f'{horns} elementary inner horn attachments checked on mixed orders.')
