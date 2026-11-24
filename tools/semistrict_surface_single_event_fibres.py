"""Read the ordinary hom on one placed event, including an empty polygon window."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, subst_tm, sub_from, tdim, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import columns
from semistrict_surface_weight_cut import Selector, depth_slots


class PlacedTerms(Selector):
    def __init__(self, ctx):
        super().__init__(ctx, 2, {i for i, ty in enumerate(ctx) if tdim(ty) + 1 == 2})
        self.local = []
        self.names = {}

    @cache
    def word(self, term):
        if term[0] == 'v':
            assert self.ctx[term[1]][1] == STAR
            return (term[1],)
        _, _, _, args = term
        return tuple(e for j in columns(term[1])[1] for e in self.word(args[j]))

    def local_type(self, ty, left, right):
        if tdim(ty) + 1 == 2:
            return STAR
        return arr(self.local_type(ty[1], left, right), self.read(ty[2], left, right),
                   self.read(ty[3], left, right))

    @cache
    def read(self, term, left=(), right=()):
        assert self.weight(term) == 1
        if term[0] == 'v':
            ty = self.local_type(self.ctx[term[1]], left, right)
            name = v(len(self.local))
            self.local.append(ty)
            self.names[name] = left, term[1], right
            return name
        _, arity, ty, args = term
        choices = []
        for lower, slots, cuts in depth_slots(arity, 2):
            weights = {self.weight(args[i]) for i, a in zip(slots, lower) if a == STAR}
            assert len(weights) == 1
            if weights == {1}:
                choices.append((slots, cuts))
        (slots, cuts), = choices
        arrows = columns(arity)[1]
        col, = (k for k, i in enumerate(arrows) if i in cuts[0].indices)
        left += tuple(e for i in arrows[:col] for e in self.word(args[i]))
        right = tuple(e for i in arrows[col + 1:] for e in self.word(args[i])) + right
        generic = ('coh', arity, ty, tuple(map(v, range(len(arity)))))
        for cut in cuts:
            generic = cut.term(generic)
        return subst_tm(generic, tuple(self.read(args[i], left, right) for i in slots))


def fixture(scalar):
    ctx = [STAR]

    def declare(s, t):
        base = infer(tuple(ctx), s)
        assert infer(tuple(ctx), t) == base
        cell = v(len(ctx))
        ctx.append(arr(base, s, t))
        return cell

    f = declare(v(0), v(0))
    pole = identity(tuple(ctx), v(0)) if scalar else f
    a = declare(pole, pole)
    c = tuple(ctx)

    def position(on_right):
        placed = comp2(c, 0, f, a) if on_right else comp2(c, 0, a, f)
        if not scalar:
            return placed
        line = tree_ctx(((),))
        z = v(2)
        padded = (comp2(line, 0, z, identity(line, v(1))) if on_right
                  else comp2(line, 0, identity(line, v(0)), z))
        lab = sub_from(line, c, {2: f})
        return composite(c, 1, [subst_tm(head(line, z, padded), lab), placed,
                                subst_tm(head(line, padded, z), lab)])

    a0, a1 = position(False), position(True)
    p, r = declare(a0, a1), declare(a1, a0)
    loop = comp2(tuple(ctx), 2, p, r)
    update = declare(loop, loop)
    twice = comp2(tuple(ctx), 3, update, update)
    change = declare(twice, twice)
    top = declare(change, change)
    ctx = tuple(ctx)
    check_ctx(ctx)
    return ctx, f, a, [a0, a1, p, r, loop, update, twice, change, top]


def check_fibres(out):
    checked = 0
    for scalar in (False, True):
        ctx, f, a, terms = fixture(scalar)
        reading = PlacedTerms(ctx)
        for nl in range(3):
            for nr in range(3):
                left, right = (f[1],) * nl, (f[1],) * nr
                projected = []
                for i, term in enumerate(terms):
                    cell = reading.read(term, left, right)
                    expected = reading.local_type(infer(ctx, term), left, right)
                    assert infer(tuple(reading.local), cell) == expected
                    # Nested spatial actions retained as raw unary heads. Their
                    # underlying occurrence must carry both full exterior words.
                    placed = term
                    for _ in left:
                        placed = comp2(ctx, 0, f, placed)
                    for _ in right:
                        placed = comp2(ctx, 0, placed, f)
                    placed = comp2(ctx, 0, identity(ctx, v(0)), placed)
                    visible = reading.read(placed)
                    assert infer(tuple(reading.local), visible) == reading.local_type(infer(ctx, placed), (), ())
                    if term[0] == 'v':
                        while visible[0] == 'coh':
                            slot, = maximal_vars(visible[1])
                            visible = visible[3][slot]
                        assert visible == cell
                    if out and (nl, nr) == (1, 1) and i in (0, 2, 5, 8):
                        label = f'case{int(scalar)}at{i}'
                        out.check_typed(label + 'raw', ctx, placed)
                        out.check_type(label + 'read', tuple(reading.local), cell, expected)
                    projected.append(cell)
                    checked += 1
                assert reading.names[projected[0]] == (left, a[1], (f[1],) + right)
                assert reading.names[projected[1]] == (left + (f[1],), a[1], right)
        check_ctx(tuple(reading.local))
    print(f'{checked} placed readings checked with nested spatial actions, through degree six')


def tensor_checks():
    # Signed boundary in a tensor of globes. A coordinate (d, sign) is
    # either the chosen top atom or one of its two parallel d-faces.
    def boundary(chain):
        result = Counter()
        for cell, coefficient in chain.items():
            parity = 1
            for i, (degree, _) in enumerate(cell):
                if degree:
                    for direction in (-1, 1):
                        face = cell[:i] + ((degree-1, direction),) + cell[i+1:]
                        result[face] += coefficient * parity * direction
                parity *= (-1) ** degree
        return result

    count = 0
    for arity in range(1, 5):
        for degrees in product(range(4), repeat=arity):
            axes = {i for i, degree in enumerate(degrees) if degree}
            if not axes:
                continue
            for sign in (-1, 1):
                row = {tuple((degree, 0) for degree in degrees): 1}
                for _ in range(sum(degrees)-1):
                    row = {cell: sign*n for cell, n in boundary(row).items() if sign*n > 0}
                crossed = Counter()
                for cell, coefficient in row.items():
                    i, = [i for i, (degree, _) in enumerate(cell) if degree]
                    crossed[i] += coefficient
                assert crossed == Counter({i: 1 for i in axes})
                count += 1
    print(f'{count} signed one-dimensional faces verified for tensor atoms through four factors')


def rice_checks(binary):
    from semistrict_surface_exact_boundary import rejected
    from semistrict_surface_local_generators import Checker, FULL, WIDTH_ONE
    with TemporaryDirectory() as directory:
        check = Checker(binary.resolve(), Path(directory))
        (Path(directory) / 'Units.catt').write_text("""import Heads
def unitor_l = coh [ x{f}y : comp[id(x),f] -> f ]
def unitor_l_inv = coh [ x{f}y : f -> comp[id(x),f] ]
def unitor_r = coh [ x{f}y : comp[f,id(y)] -> f ]
def unitor_r_inv = coh [ x{f}y : f -> comp[f,id(y)] ]
""")
        loop = '(x : *) (f : x -> x)'
        for scalar in (False, True):
            if scalar:
                ctx = loop + ' (a : id(x) -> id(x))'
                # Raw 2-unitors give the same literal edge f on both boundaries.
                left = 'comp[unitor_l_inv(f),comp[[a],f],unitor_l(f)]'
                right = 'comp[unitor_r_inv(f),comp[f,[a]],unitor_r(f)]'
            else:
                ctx = loop + ' (a : f -> f)'
                left, right = 'comp[[a],f]', 'comp[f,[a]]'
            ctx += (f' (p : {left} -> {right}) (r : {right} -> {left})'
                    ' (A : comp[p,r] -> comp[p,r])')
            flat, nested = 'grouped(A,A,A)', 'h(h(A,A),A)'
            ctx += f' (Z : {flat} -> {flat}) (K : Z -> Z)'
            fit = 'comp[flat(A,A,A),Z,unflat(A,A,A)]'
            lift = 'comp[flat(A,A,A),[K],unflat(A,A,A)]'
            for mode in ((), WIDTH_ONE, FULL):
                check.definitions(f'def five {ctx} : {nested} -> {nested} = {fit}\n'
                                  f'def six {ctx} : {fit} -> {fit} = {lift}', mode, 'Units')
            for bound, var, cell, unit in [(nested, 'Z', fit, f'id({flat})'), (fit, 'K', lift, 'id(Z)')]:
                code = f'def direct {ctx} : {bound} -> {bound} = {var}'
                rejected(check.query(code, WIDTH_ONE, 'Units'), 'Check.catt', 'direct')
                check.definitions(code, FULL, 'Units')
                check.equality(cell, var, ctx, FULL, True, 'Units')
                check.equality(cell, unit, ctx, FULL, False, 'Units')
    print('Rice checked fits, direct-use failures and both full classes for two disjoint windows')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rice', type=Path)
    args = parser.parse_args()
    out = Emitter() if args.agda_dir else None
    tensor_checks()
    check_fibres(out)
    if out:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        (args.agda_dir / 'PlacedEventFibres.agda').write_text(out.module('PlacedEventFibres', 'Event fibres without a common spatial cut.'))
    if args.rice:
        rice_checks(args.rice)
