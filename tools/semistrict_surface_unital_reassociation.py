"""Check unit pruning and top reassociation on binary words at their raw boundaries."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from catt import chain_tree, comp2, infer, maximal_vars, src, tdim, tdim_tm, tgt, tree_ctx, tree_of, ucomp, v
from ct_suspension import ident
from semistrict_surface_insertion_cut import Assertions


@cache
def core(ctx, term):
    """Erase outer identity rank; retain every surviving binary cut and its parentheses."""
    if term[0] == 'v':
        return term
    arity, args = term[1], term[3]
    slots = maximal_vars(arity)
    if len(slots) == 1:
        return core(ctx, args[slots[0]])
    assert len(slots) == 2
    tree = tree_of(arity)
    cut = 0
    while len(tree) == 1:
        cut += 1
        tree = tree[0]
    left, right = (core(ctx, args[i]) for i in slots)
    if tdim_tm(ctx, left) <= cut:
        return right
    if tdim_tm(ctx, right) <= cut:
        return left
    return comp2(ctx, cut, left, right)


def padded(ctx, term):
    result = core(ctx, term)
    for _ in range(tdim_tm(ctx, term) - tdim_tm(ctx, result)):
        result = ident(ctx, result)
    return result


@cache
def parse(ctx, term, top_only):
    if term[0] == 'v':
        return term
    tree = tree_of(term[1])
    cut = 0
    while len(tree) == 1:
        cut += 1
        tree = tree[0]
    flatten = not top_only or cut == tdim_tm(ctx, term) - 1
    tag = ('list' if flatten else 'binary', cut)
    items = []
    for slot in maximal_vars(term[1]):
        child = parse(ctx, term[3][slot], top_only)
        items.extend(child[1] if flatten and child[0] == tag else [child])
    return (tag, tuple(items))


def check(ctx, rice, counts, size_bound):
    by_size = [set(), set(map(v, range(len(ctx))))]
    groups = {}
    full_only = defaultdict(set)
    quota = Counter()
    for size in range(1, size_bound + 1):
        if size >= 2:
            words = {ident(ctx, a) for a in by_size[-1] if tdim_tm(ctx, a) < 4}
            for i in range(1, size - 1):
                for a, b in product(by_size[i], by_size[size-1-i]):
                    la, lb = infer(ctx, a), infer(ctx, b)
                    for cut in reversed(range(min(tdim(la), tdim(lb)) + 1)):
                        while tdim(la) > cut:
                            la = la[1]
                        while tdim(lb) > cut:
                            lb = lb[1]
                        if la[3] == lb[2]:
                            words.add(comp2(ctx, cut, a, b))
            by_size.append(words)
        for term in sorted(by_size[size]):
            rank = tdim_tm(ctx, term)
            value = core(ctx, term)
            reduced = padded(ctx, term)
            if rank:
                assert src(ctx, reduced) == padded(ctx, src(ctx, term))
                assert tgt(ctx, reduced) == padded(ctx, tgt(ctx, term))
            flat, top = (parse(ctx, value, b) for b in (False, True))
            key = (infer(ctx, term), flat)
            if key in groups:
                assert groups[key] == top
                counts['additional representatives'] += 1
            groups[key] = top
            full_only[rank, flat].add(top)
            counts['raw words'] += 1
            if term != reduced:
                counts['changed by pruning'] += 1
                bucket = (rank, tdim_tm(ctx, value), size)
                if quota[bucket] < 2:
                    rice.equal(ctx, term, reduced, 'unit pruning')
                    quota[bucket] += 1
    counts['flattened groups needing the raw boundary'] += sum(len(x) > 1 for x in full_only.values())


def mixed_cases():
    tree = chain_tree(3)
    ctx = tree_ctx(tree)
    a, b, c = map(v, maximal_vars(ctx))
    yield ctx, ucomp(ctx), comp2(ctx, 0, a, comp2(ctx, 0, b, c))
    for n in range(2, 5):
        tree = (tree,)
        ctx = tree_ctx(tree)
        a, b, c = map(v, maximal_vars(ctx))
        def compose(x, y):
            return comp2(ctx, n-1, x, y)
        for cut in range(n-1):
            unit = a
            for _ in range(n-cut):
                unit = tgt(ctx, unit)
            for _ in range(n-cut):
                unit = ident(ctx, unit)
            def whisker(x):
                return comp2(ctx, cut, x, unit)
            left = whisker(compose(compose(a, b), c))
            right = compose(whisker(a), compose(whisker(b), whisker(c)))
            assert infer(ctx, left) == infer(ctx, right)
            lcore, rcore = core(ctx, left), core(ctx, right)
            assert lcore != rcore and parse(ctx, lcore, True) == parse(ctx, rcore, True)
            yield ctx, left, right


def check_path_model():
    def operation(inputs):
        inputs = tuple(x for x in inputs if x)
        if len(inputs) <= 2:
            return sum(inputs, ())
        return (('head', inputs),)

    x, y, z = ('x',), ('y',), ('z',)
    ternary = operation([x, y, z])
    assert ternary != operation([x, operation([y, z])])
    values = ((), x, y + z, ternary)
    for a, b, c in product(values, repeat=3):
        assert operation([a, operation([b, c])]) == operation([operation([a, b]), c])
    checks = 0
    for arity in range(6):
        for args in product(values, repeat=arity):
            for i in range(arity + 1):
                assert operation(args) == operation((*args[:i], (), *args[i:]))
                checks += 1
    return checks


def check_rice(checks, binary, mode, positive=True):
    with TemporaryDirectory() as folder:
        program = Path(folder) / 'Words.catt'
        program.write_text('\n'.join(checks.commands) + '\n')
        result = subprocess.run([binary, mode, program], capture_output=True, text=True)
    output = re.sub(r'\x1b\[[0-9;]*m', '', result.stdout + result.stderr)
    if positive:
        assert not result.returncode and output.count('are equal') == sum(checks.count.values()), output[-2000:]
    else:
        assert sum(checks.count.values()) == 1 and 'are not equal' in output, output[-2000:]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', type=Path)
    args = parser.parse_args()
    checks = Assertions()
    counts = Counter()
    for tree in (((), (), ()), (((), (), ()),), (((),), ((),), ((),)),
                 (((), ()), ((), ())), ((((), ()),),), (((),), (), ((),))):
        check(tree_ctx(tree), checks, counts, size_bound=8)
    assert counts['flattened groups needing the raw boundary']
    for label, n in counts.items():
        print(f'{label}: {n}')
    print(f'Pruning loci in the path model: {check_path_model()}')
    examples = list(mixed_cases())
    if args.rice_binary:
        binary = args.rice_binary.resolve()
        check_rice(checks, binary, '--su')
        print(f"Rice strict-unit equalities: {sum(checks.count.values())}")
        for ctx, left, right in examples:
            probe = Assertions()
            probe.equal(ctx, left, right, 'boundary comparison')
            check_rice(probe, binary, '--su', positive=False)
            check_rice(probe, binary, '--sua')
        print(f'Strict-unit and insertion comparisons: {len(examples)} in each mode')
