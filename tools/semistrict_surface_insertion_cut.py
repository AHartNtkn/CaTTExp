"""Check actual cut terms and their equalities with Rice's catt_strict --sua."""

import argparse
from collections import Counter
from functools import cache
from pathlib import Path
import re
import subprocess
import tempfile

from catt import (STAR, arr, disc_tree, infer, maximal_vars, ps_dim, sub_from,
                  subst_tm, subst_ty, tree_ctx, tree_of, ucomp, v)
from ct_suspension import susp_ctx, susp_tm
from partial_cylinder_steiner import trees
from relative_coherence_cut import Cut


def variables(ctx):
    return tuple(v(i) for i in range(len(ctx)))


@cache
def standard(ctx, rank):
    """The standard coherence (at rank zero, its unique vertex)."""
    height = ps_dim(ctx)
    if rank == height:
        term = ucomp(ctx)
        if rank == 0 or term[0] == 'coh':
            return term
        ty = infer(ctx, term)
    else:
        assert rank > height
        face = ucomp(ctx) if rank == height + 1 else standard(ctx, rank - 1)
        ty = arr(infer(ctx, face), face, face)
    return ('coh', ctx, ty, variables(ctx))


@cache
def shape(ctx):
    # The context order introduces the next target, then its incoming arrow.
    cursor = iter(range(1, len(ctx)))

    def show(tree, source):
        result = 'x' + str(source)
        for child in tree:
            target, arrow = next(cursor), next(cursor)
            result += '{' + show(child, arrow) + '}x' + str(target)
        return result

    return show(tree_of(ctx), 0)


class Assertions:
    def __init__(self):
        self.commands = []
        self.heads = {}
        self.count = Counter()

    def term(self, term):
        if term[0] == 'v':
            return 'x' + str(term[1])
        _, ctx, ty, args = term
        key = ctx, ty
        if key not in self.heads:
            src, tgt = map(self.term, ty[2:])
            name = 'head' + str(len(self.heads))
            self.commands.append(f'def {name} = coh [ {shape(ctx)} : {src} -> {tgt} ]')
            self.heads[key] = name
        labels = ','.join(self.term(args[i]) for i in maximal_vars(ctx))
        return f'{self.heads[key]}({labels})'

    def equal(self, ctx, left, right, case):
        infer(ctx, left)
        infer(ctx, right)
        lterm, rterm = self.term(left), self.term(right)
        self.commands.append(f'assert {lterm} = {rterm} in {shape(ctx)}')
        self.count[case] += 1

    def run(self, binary, mode='--sua'):
        with tempfile.TemporaryDirectory() as scratch:
            program = Path(scratch) / 'cut.catt'
            program.write_text('\n'.join(self.commands) + '\n')
            run = subprocess.run([binary, mode, program], capture_output=True, text=True)
        stdout = re.sub(r'\x1b\[[0-9;]*m', '', run.stdout)
        if run.returncode or stdout.count('are equal') != sum(self.count.values()):
            raise RuntimeError(run.stderr[-4000:] + '\n' + stdout[-2000:])
        for case, count in self.count.items():
            print(f'{count} {case}')


def cuts(ctx):
    objects = [i for i, ty in enumerate(ctx) if ty == STAR]
    for j in range(len(objects) - 1):
        yield Cut(ctx, objects[j + 1:])


def check_standards(checks, limit):
    for size in range(1, limit + 1):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            for rank in range(ps_dim(ctx), ps_dim(ctx) + 3):
                head = standard(ctx, rank)
                for cut in cuts(ctx):
                    lower = cut.context()
                    checks.equal(lower, cut.term(head), standard(lower, rank - 1),
                                 'standard coherence projections')


def check_insertions(checks, tree, extra):
    # Replace the middle disc between two one-edge guards. Include the empty
    # replacement, where its interior maps its unique vertex to the seam.
    inside = tree_ctx(tree)
    degree = max(1, ps_dim(inside)) + extra
    outside = tree_ctx(((), disc_tree(degree - 1), ()))
    joined = tree_ctx(((), *tree, ()))
    embedding = (v(1),) + tuple(v(i + 2) for i in range(1, len(inside)))
    active = subst_tm(standard(inside, degree), embedding)
    old_slots = maximal_vars(outside)
    last = maximal_vars(joined)[-1]
    exterior = sub_from(outside, joined, dict(zip(old_slots, (v(2), active, v(last)))))
    for rank in (degree, degree + 1):
        original = standard(outside, rank)
        left = subst_tm(original, exterior)
        right = ('coh', joined, subst_ty(original[2], exterior), variables(joined))
        checks.equal(joined, left, right, 'root insertions')
        for i, cut in enumerate(cuts(joined)):
            case = 'active column' if 0 < i <= len(tree) else 'stationary insertion'
            checks.equal(cut.context(), cut.term(left), cut.term(right), case)
        # Use actual suspended heads for a branch one level deeper and cut
        # them before sending the resulting two expressions to the verifier.
        deeper = susp_ctx(joined)
        cut, = cuts(deeper)
        checks.equal(cut.context(), cut.term(susp_tm(left)), cut.term(susp_tm(right)),
                     'nested insertions')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('catt_strict', type=Path)
    parser.add_argument('--edges', type=int, default=5)
    args = parser.parse_args()
    checks = Assertions()
    check_standards(checks, args.edges)
    for size in range(args.edges + 1):
        for tree in trees(size):
            for extra in (0, 1):
                check_insertions(checks, tree, extra)
    checks.run(args.catt_strict.resolve())
