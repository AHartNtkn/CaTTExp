"""Check the state action, contextual rewrites and typed boundary fits of the two-loop encoding."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import arr, coh_between, comp2, disc_tree, infer, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run


def encode(indices):
    return ''.join('P' + 'PQ' * index + 'Q' for index in indices)


def read(state, word, alphabet):
    frames = list(state)  # The first frame is permanent.
    output = []
    for letter in word:
        if letter == 'P':
            frames.append(0)
        elif letter == 'Q':
            if len(frames) > 1:
                count = frames.pop()
                if count == 0:
                    frames[-1] += 1
                elif count <= alphabet:
                    output.append(count)
        else:
            raise ValueError(letter)
    return tuple(frames), tuple(output)


def words(symbols, bound):
    for size in range(bound + 1):
        yield from product(symbols, repeat=size)


def check_actions():
    codes = [(word, encode(word)) for word in words(range(1, 5), 3)]
    states = [state for state in words((0, 1, 3, 5), 4) if state]
    for state, (word, code) in product(states, codes):
        assert read(state, code, 4) == (state, word)

    # The surrounding path can cut through an unfinished code. Check its
    # final state as well as the exact old prefix and suffix of each rewrite.
    patterns = list(words((1, 2), 2))
    fragments = [''.join(w) for w in words('PQ', 4)]
    checks = 0
    for prefix, suffix in product(fragments, repeat=2):
        state, left = read((0,), prefix, 2)
        final, right = read(state, suffix, 2)
        for face in patterns:
            assert read((0,), prefix + encode(face) + suffix, 2) == (final, left + face + right)
        checks += len(patterns) ** 2  # Both faces independently, including the empty face.
    return len(states) * len(codes), checks


def compose(terms):
    result = terms[-1]
    for term in reversed(terms[:-1]):
        result = f'comp[{term},{result}]'
    return result


def write_globe_checks(directory):
    emitter = Emitter()
    tree = disc_tree(1)
    ctx = tree_ctx(tree)
    arrow = v(len(ctx) - 1)
    unit = identity(ctx, ctx[-1][2])
    for i in range(1, 5):
        padded = arrow
        for _ in encode((i,))[:-1]:
            padded = comp2(ctx, 0, unit, padded)
        fits = []
        for name, source, target in (('fit', padded, arrow), ('expand', arrow, padded)):
            term = coh_between(ctx, tree, [arrow], source, target)
            ty = arr(ctx[-1], source, target)
            assert infer(ctx, term) == ty
            emitter.check_type(name + str(i), ctx, term, ty)
            fits.append(term)
        # Test the relative fits one dimension higher in each direction.
        for j, end in enumerate((padded, arrow)):
            composite = comp2(ctx, 1, fits[j], fits[1 - j])
            trivial = identity(ctx, end)
            term = coh_between(ctx, tree, [arrow], composite, trivial)
            emitter.check_type(f'cancel{i}at{j}', ctx, term, arr(infer(ctx, trivial), composite, trivial))
    for prefix, kernel in (('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')):
        module = prefix + 'TwoLoopFits'
        code = emitter.module(module, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
        (directory / (module + '.agda')).write_text(code)


def check_types(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as path:
        folder = Path(path)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        source = 'import examples/monoidal\n'
        names = []
        for i in range(1, 5):
            padded = compose(['id(x)'] * (len(encode((i,))) - 1) + ['f'])
            for name, endpoints in ((f'fit{i}', f'{padded} -> f'), (f'expand{i}', f'f -> {padded}')):
                source += f'def {name} x{{f}}y : {endpoints} = coh [ x{{f}}y : {endpoints} ](f)\n'
                names.append(name)
        ctx = '(x : *) (f : x -> x) (g : x -> x) (z : id(x) -> f) (d : g -> id(x)) (u : z -> z)'
        pf = compose(['id(x)'] * (len(encode((1,))) - 1) + ['f'])
        pg = compose(['id(x)'] * (len(encode((2,))) - 1) + ['g'])
        birth = 'comp[z,expand1(f)]'
        source += f'def birth {ctx} : id(x) -> {pf} = {birth}\n'
        source += f'def death {ctx} : {pg} -> id(x) = comp[fit2(g),d]\n'
        source += f'def update {ctx} : {birth} -> {birth} = horiz(u,id(expand1(f)))\n'
        names.extend(('birth', 'death', 'update'))

        p, q = (compose([symbol.lower() for symbol in encode((i,))]) for i in (1, 2))
        encoded = f'(x : *) (p : x -> x) (q : x -> x) (z : id(x) -> {p}) (d : {q} -> id(x))'
        encoded += ' (u : z -> z) (v : u -> u)'
        source += f'def encodedPaste {encoded} : {q} -> {p} = comp[d,z]\n'
        source += f'def encodedFourth {encoded} : u -> u = comp[v,v]\n'
        names.extend(('encodedPaste', 'encodedFourth'))
        (folder / 'TwoLoops.catt').write_text(source)
        bad = f'def wrong {encoded} : {p} -> {q} = comp[d,z]\n'
        (folder / 'Wrong.catt').write_text('import TwoLoops\n' + bad)
        for mode in ([], ['--su'], ['--sua']):
            accepted(run(binary, folder, 'TwoLoops.catt', mode), 'TwoLoops.catt', names)
            rejected(run(binary, folder, 'Wrong.catt', mode), 'Wrong.catt', 'wrong')
        return len(names), 3


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path, help='built Rice checker checkout')
    parser.add_argument('--agda-dir', type=Path, help='write exact raw globe checks into this directory')
    args = parser.parse_args()
    if args.agda_dir:
        write_globe_checks(args.agda_dir)
    print('State/word actions and contextual rewrite placements:', *check_actions())
    if args.catt_strict:
        print('Typed declarations and modes with a negative control:', *check_types(args.catt_strict.resolve()))
