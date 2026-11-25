"""Check explicit ordinary CaTT terms using published equations through a fixed output rank."""
from functools import cache

from catt import STAR, is_ps, side_ok, subst_ty, tdim_tm
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_insertion_cut import Assertions


class RankCut:
    def __init__(self, rank, binary, directory):
        self.rank = rank
        self.binary = binary
        self.directory = directory

    @cache
    def context(self, ctx):
        if ctx:
            self.context(ctx[:-1])
            self.check_type(ctx[:-1], ctx[-1])

    @cache
    def check_type(self, ctx, ty):
        if ty != STAR:
            _, base, source, target = ty
            self.check_type(ctx, base)
            for face in (source, target):
                if not self.equal_type(ctx, self.infer(ctx, face), base):
                    raise ValueError('Arrow face has the wrong type')

    @cache
    def infer(self, ctx, term):
        if term[0] == 'v':
            index = term[1]
            if not 0 <= index < len(ctx):
                raise ValueError('Variable outside context')
            return ctx[index]
        _, arity, ty, labels = term
        if not is_ps(arity) or ty == STAR or len(arity) != len(labels):
            raise ValueError('Invalid coherence arity, type, or tuple length')
        self.check_type(arity, ty)
        if not side_ok(arity, *ty[1:]):
            raise ValueError('Coherence fails the support condition')
        for slot_type, label in zip(arity, labels, strict=True):
            if not self.equal_type(ctx, self.infer(ctx, label), subst_ty(slot_type, labels)):
                raise ValueError('Ill-typed entry in coherence tuple')
        return subst_ty(ty, labels)

    @cache
    def equal_type(self, ctx, left, right):
        if left == right:
            return True
        if left == STAR or right == STAR:
            return False
        return (self.equal_type(ctx, left[1], right[1])
                and self.equal_term(ctx, left[2], right[2])
                and self.equal_term(ctx, left[3], right[3]))

    @cache
    def equal_term(self, ctx, left, right):
        """Equality on formed terms, including generic types and all tuple entries."""
        if left == right:
            return True
        rank = tdim_tm(ctx, left)
        if tdim_tm(ctx, right) != rank:
            return False
        if rank <= self.rank:
            return self.published_equal(ctx, left, right)
        if left[0] == 'v' or right[0] == 'v' or left[1] != right[1]:
            return False
        return (self.equal_type(left[1], left[2], right[2])
                and all(self.equal_term(ctx, a, b) for a, b in zip(left[3], right[3], strict=True)))

    def published_equal(self, ctx, left, right):
        code = Assertions()
        telescope = []
        for i, ty in enumerate(ctx):
            written = '*' if ty == STAR else f'{code.term(ty[2])} -> {code.term(ty[3])}'
            telescope.append(f'(x{i} : {written})')
        query = f'assert {code.term(left)} = {code.term(right)} in ' + ' '.join(telescope)
        name = 'LowRankEquality.catt'
        (self.directory / name).write_text('\n'.join([*code.commands, query]) + '\n')
        result = run(self.binary, self.directory, name, ['--sua'])
        if 'Error: Assertion failed:' in result and 'are not equal' in result:
            return False
        if 'Error: Terms ' in result and 'do not have matching types' in result:
            return False
        accepted(result, name, [])
        if 'are equal' not in result:
            raise ValueError('Expected a checked equality')
        return True

    def checks(self, ctx, term, expected):
        self.context(ctx)
        self.check_type(ctx, expected)
        return self.equal_type(ctx, self.infer(ctx, term), expected)
