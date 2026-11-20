"""Check the finite examples for excision at a marked strict cell and its increment cover."""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter


def marked_bar(add_extension):
    """Relative to the basepoint section, each circle contributes one marked edge."""
    order = {(0, 1), (1, 2), (1, 3)}
    if add_extension:
        order.add((2, 4))
    while True:
        closure = order | {(x, z) for x, y in order for w, z in order if y == w}
        if closure == order:
            break
        order = closure

    circles = {(0, 2), (1, 3)}
    vertices = sorted({x for pair in order for x in pair})
    basis = []
    for size in range(1, len(vertices) + 1):
        column = []
        for string in combinations(vertices, size):
            pairs = set(zip(string, string[1:]))
            if pairs <= order:
                marks = pairs & circles
                assert len(marks) <= 1
                column.extend((string, mark) for mark in marks)
        basis.append(column)

    # In this example each nonzero differential entry cancels a distinct
    # pair of generators integrally. Check this directly on the face maps.
    cancelled = set()
    for degree in range(1, len(basis)):
        for string, mark in basis[degree]:
            terms = {}
            for i in range(len(string)):
                face = string[:i] + string[i + 1:], mark
                if face in basis[degree - 1]:
                    terms[face] = terms.get(face, 0) + (-1) ** i
            boundary = [(key, n) for key, n in terms.items() if n]
            if boundary:
                (face, coefficient), = boundary
                assert abs(coefficient) == 1
                assert face not in cancelled and (string, mark) not in cancelled
                cancelled.update((face, (string, mark)))
    return [key for column in basis for key in column if key not in cancelled]


def check_words():
    profiles = dict(a="0", b="1", c="2", d="00", e="11", f="12")
    rules = (("aa", "e"), ("d", "bb"), ("d", "e"), ("ab", "f"), ("e", "cc"),
             ("b", "c"), ("a", "b"), ("aa", "ba"), ("e", "f"), ("f", "cc"))

    def expand(word):
        return "".join(profiles[letter] for letter in word)

    def leq(u, v):
        return len(u) == len(v) and all(a <= b for a, b in zip(u, v))

    @cache
    def words(width):
        if width == 0:
            return ("",)
        return tuple(a + w for a, p in profiles.items() if len(p) <= width
                     for w in words(width - len(p)))

    def rewrites(word):
        for i in range(len(word)):
            for source, target in rules:
                if word.startswith(source, i):
                    yield (word[:i] + target + word[i + len(source):],
                           (len(expand(word[:i])), source, target))

    def matches(word, start, fragment):
        return any(len(expand(word[:i])) == start and word.startswith(fragment, i)
                   for i in range(len(word)))

    assert all(leq(expand(a), expand(b)) and expand(a) != expand(b) for a, b in rules)
    intervals = placed_rules = 0
    for width in range(1, 5):
        ordered = sorted(words(width), key=lambda w: sum(map(int, expand(w))))
        moves = {w: tuple(rewrites(w)) for w in ordered}
        reachable = {}
        for w in reversed(ordered):
            reachable[w] = {w}.union(*(reachable[z] for z, _ in moves[w]))
        for u in ordered:
            for v in reachable[u]:
                middle = [w for w in reachable[u] if v in reachable[w]]
                allowed = {step for w in middle for z, step in moves[w] if v in reachable[z]}
                assert all(leq(expand(u), expand(w)) and leq(expand(w), expand(v)) for w in middle)
                assert all(not matches(v, start, a) and not matches(u, start, b)
                           for start, a, b in allowed)
                intervals += 1
                placed_rules += len(allowed)
    return intervals, placed_rules


def check_cover():
    factorizations = 0
    for width in range(5):
        for source in product(range(-1, 2), repeat=width):
            for increment in product(range(3), repeat=width):
                target = tuple(a + b for a, b in zip(source, increment))
                for cut in range(width + 1):
                    parts = ((source[:cut], target[:cut]), (source[cut:], target[cut:]))
                    assert parts[0][0] + parts[1][0] == source
                    assert parts[0][1] + parts[1][1] == target
                    differences = tuple(tuple(b - a for a, b in zip(lo, hi)) for lo, hi in parts)
                    assert differences == (increment[:cut], increment[cut:])
                # Enumerate intermediate words independently from splittings of the increment.
                mids = set(product(*(range(a, b + 1) for a, b in zip(source, target))))
                splits = list(product(*(range(d + 1) for d in increment)))
                lifted = {tuple(a + b for a, b in zip(source, p)) for p in splits}
                assert mids == lifted and len(mids) == len(splits)
                factorizations += len(mids) + width + 1
    return factorizations


def literal_poles():
    class Diagram:
        def __init__(self):
            self.ctx = ()

        def add(self, ty):
            cell = v(len(self.ctx))
            self.ctx += (ty,)
            return cell

        def over(self, left, right):
            ty = infer(self.ctx, left)
            assert ty == infer(self.ctx, right)
            return self.add(arr(ty, left, right))

        def compose(self, cut, left, right):
            return comp2(self.ctx, cut, left, right)

    base = Diagram()
    pole = base.add(STAR)
    edge = base.over(pole, pole)
    word = base.compose(0, edge, edge)
    a, b = base.over(word, word), base.over(word, word)
    mark = base.over(base.compose(1, a, b), base.compose(1, b, a))

    lift = Diagram()
    vertices = [lift.add(STAR) for _ in range(3)]
    projection = [pole] * 3
    paths = []
    for _ in range(3):
        left = lift.over(vertices[0], vertices[1])
        right = lift.over(vertices[1], vertices[2])
        projection.extend((edge, edge))
        paths.append(lift.compose(0, left, right))
    rows = []
    for source, target in zip(paths, paths[1:]):
        rows.append((lift.over(source, target), lift.over(source, target)))
        projection.extend((a, b))
    lifted = lift.over(lift.compose(1, rows[0][0], rows[1][1]),
                       lift.compose(1, rows[0][1], rows[1][0]))
    sigma = tuple(projection) + (mark,)
    for value, ty in zip(sigma, lift.ctx):
        assert infer(base.ctx, value) == subst_ty(ty, sigma)

    globe = tree_ctx(disc_tree(3))
    top, = maximal_vars(globe)
    z = v(top)

    def identity(term, rank):
        arity = tree_ctx(disc_tree(rank))
        last, = maximal_vars(arity)
        x = v(last)
        return ("coh", arity, arr(infer(arity, x), x, x), sub_from(arity, globe, {last: term}))

    def compare(left, right):
        substitution = tuple(v(i) for i in range(len(globe)))
        return "coh", globe, arr(infer(globe, left), left, right), substitution

    padded = comp2(globe, 2, z, identity(infer(globe, z)[3], 2))
    unitor = compare(z, padded)
    reverse = compare(padded, z)
    cancel = compare(comp2(globe, 3, unitor, reverse), identity(z, 3))
    emitter = Emitter()
    for label, term in (("mark", z), ("unitor", unitor), ("reverse", reverse), ("cancel", cancel)):
        above = subst_tm(term, sub_from(globe, lift.ctx, {top: lifted}))
        below = subst_tm(term, sub_from(globe, base.ctx, {top: mark}))
        assert subst_tm(above, sigma) == below
        for kind, ctx, t in (("lift", lift.ctx, above), ("base", base.ctx, below)):
            emitter.check_typed(label + "-" + kind, ctx, t)
            emitter.check_type(label + "-" + kind, ctx, t, infer(ctx, t))
        emitter.check_eq(label + "-projection", above, sigma, below)
    return emitter


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path, help="emit the literal-boundary checks into this module")
    args = parser.parse_args()
    assert marked_bar(False) == [((0, 2), (0, 2))]
    assert marked_bar(True) == []
    print("Marked comparison cone: H3 = Z; after extension: acyclic")
    intervals, rules = check_words()
    print(f"{intervals} word intervals; {rules} placed rules checked at both ends")
    print(f"{check_cover()} horizontal and vertical factorizations checked")
    emitter = literal_poles()
    print("Literal cyclic example: mark, unitor, reverse and cancellation project exactly")
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, "Prescribed poles in the increment cover."))
