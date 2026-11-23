"""Check arity retractions, occurrence splitting and exact rehydration in Response 27."""
import argparse
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (comp2, glue_tree, infer, is_ps, maximal_vars, restrict, src,
                  subst_tm, subst_ty, tdim, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_interval_generator import trees
from steiner import Complex, cells_upto, support


RAW = """import examples/eh-common

def padded {f{a}g}{h{b}i} = comp[id(comp[f,h]), swap_src(a,b)]
def enter = coh [ [[a],[b]] : swap_src(a,b) -> padded(a,b) ]
def leave = coh [ [[a],[b]] : padded(a,b) -> swap_src(a,b) ]
def folded (x : *) (f : x -> x) (a : f -> f) : comp[f,f] -> comp[f,f] = swap_src(a,a)
def fitted_two (x : *) (f : x -> x) (a : f -> f) : comp[id(x),comp[f,f]] -> comp[comp[f,f],id(x)] = comp[unitor_l(comp[f,f]),folded(x,f,a),unitor_r_inv(comp[f,f])]
def fitted_three (x : *) (f : x -> x) (a : f -> f) : padded(a,a) -> swap_tgt(a,a) = comp[leave(a,a),swap(a,a)]
def fit_variable (x : *) (f : x -> x) (a : f -> f) : comp[id(x),f] -> f = comp[unitor_l(f),a]
"""

SURFACE = """import Raw
def lift_two (x : *) (f : x -> x) (a : f -> f) : fitted_two(x,f,a) -> folded(x,f,a) = id(folded(x,f,a))
def lift_three (x : *) (f : x -> x) (a : f -> f) : fitted_three(x,f,a) -> swap(a,a) = id(swap(a,a))
def forward_class (x : *) (f : x -> x) (a : f -> f) : enter(a,a) -> id(folded(x,f,a)) = id(enter(a,a))
def reverse_class (x : *) (f : x -> x) (a : f -> f) : leave(a,a) -> id(folded(x,f,a)) = id(leave(a,a))
def extended_lift (x : *) (f : x -> x) (a : f -> f) (k : swap_src(a,a) -> swap_tgt(a,a)) : fitted_three(x,f,a) -> swap(a,a) = id(swap(a,a))
def coloured (x : *) (f : x -> x) (a : comp[f,f] -> comp[f,f]) (b : comp[f,f] -> comp[f,f]) : comp[a,id(comp[f,f]),b] -> comp[a,b] = id(comp[a,b])
def variable_class (x : *) (f : x -> x) (a : f -> f) : fit_variable(x,f,a) -> a = id(a)
"""

POSITIONS = """import Raw
def identify_positions (x : *) (f : x -> x) (a : f -> f) : swap_src(a,a) -> swap_tgt(a,a) = id(swap_src(a,a))
"""

OTHER_CLASS = """import Raw
def different_class (x : *) (f : x -> x) (a : f -> f) (k : swap_src(a,a) -> swap_tgt(a,a)) : k -> swap(a,a) = id(k)
"""


WRONG_ORDER = """import Raw
def wrong_order (x : *) (f : x -> x) (a : comp[f,f] -> comp[f,f]) (b : comp[f,f] -> comp[f,f]) : comp[a,id(comp[f,f]),b] -> comp[b,a] = id(comp[b,a])
"""


def check_retraction(arity, kept):
    subarity, inclusion = restrict(arity, kept)
    assert is_ps(subarity)
    fixed = {entry[1]: v(i) for i, entry in enumerate(inclusion)}
    height = max(tdim(ty) + 1 for ty in arity)
    choices = {}
    for i, ty in enumerate(subarity):
        term = v(i)
        for degree in range(tdim(ty) + 1, height + 1):
            choices.setdefault(infer(subarity, term), []).append(term)
            if degree < height:
                term = identity(subarity, term)

    # Search independently of the interval construction, pinning every generator
    # of the support and allowing only variables or their iterated identities.
    def extend(partial):
        i = len(partial)
        if i == len(arity):
            return partial
        ty = subst_ty(arity[i], partial)
        options = [fixed[i]] if i in fixed else choices.get(ty, [])
        for term in options:
            if infer(subarity, term) == ty:
                result = extend((*partial, term))
                if result is not None:
                    return result
        return None

    projection = extend(())
    assert projection is not None
    assert tuple(subst_tm(entry, projection) for entry in inclusion) == tuple(v(i) for i in range(len(subarity)))
    return subarity, projection


def check_raised_inputs(emitter):
    for rank in range(1, 5):
        cut = rank - 1
        arity = tree_ctx(glue_tree(rank + 1, cut, rank))
        moving, stationary = map(v, maximal_vars(arity))
        raw_faces = []
        for face in infer(arity, moving)[2:]:
            composite = comp2(arity, cut, face, stationary)
            raw_faces.append(comp2(arity, cut, identity(arity, src(arity, composite)), composite))
        lifted = head(arity, *raw_faces)
        actual = infer(arity, lifted)
        assert list(actual[2:]) == raw_faces
        emitter.check_type(f'raised{rank}', arity, lifted, actual)


def check_supports(agda_dir):
    emitter = Emitter()
    count = 0
    for size in range(5):
        for tree in trees(size):
            arity = tree_ctx(tree)
            complex_ = Complex(arity)
            cells = cells_upto(complex_, range(len(arity)), complex_.n)
            supports = {frozenset(support(complex_, cell)) for cell in cells}
            for kept in sorted(supports, key=sorted):
                subarity, projection = check_retraction(arity, kept)
                if agda_dir:
                    source, target = emitter.ctx(subarity), emitter.ctx(arity)
                    labels = emitter.sub(projection)
                    name = f'projection{count}'
                    emitter.checks.append(
                        f'{name} : {source} ⊢sub {labels} ∶ {target}\n'
                        f'{name} = from-just (checkSub {source} (from-just (checkCtx {source})) {labels} {target})\n')
                count += 1
    check_raised_inputs(emitter)
    if agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            module = prefix + 'SupportRetractions'
            code = emitter.module(module, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
            (agda_dir / (module + '.agda')).write_text(code)
    print(f'Checked word retractions of all {count} distinct strict-cell supports through four tree edges.')


def run(binary, directory, file, flags=()):
    result = subprocess.run([binary, *flags, file], cwd=directory, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    return result.stdout


def accepted(output, file, names):
    if 'Error:' in output or f'Finished importing {file}\n' not in output:
        raise ValueError(output)
    for name in names:
        if f'Checking {name}\n' not in output:
            raise ValueError(f'Missing checked declaration {name} in {file}')


def rejected(output, file, name):
    # The checker can exit successfully after reporting an invalid definition.
    _, marker, last = output.partition(f'Checking {name}\n')
    if (not marker or 'Error: Given term' not in last
            or 'does not match inferred term' not in last or f'Finished importing {file}' in last):
        raise ValueError(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built checkout of Rice’s catt-strict')
    parser.add_argument('--agda-dir', type=Path, help='write both certified substitution checks here')
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    check_supports(args.agda_dir)
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for name, source in [('Raw.catt', RAW), ('Surface.catt', SURFACE),
                             ('Positions.catt', POSITIONS), ('OtherClass.catt', OTHER_CLASS),
                             ('Order.catt', WRONG_ORDER)]:
            (directory / name).write_text(source)
        accepted(run(binary, directory, 'Raw.catt'), 'Raw.catt',
                 ['folded', 'fitted_two', 'fitted_three', 'fit_variable'])
        print('Weak CaTT accepted the raw representatives at the declared boundaries.')
        for mode in ('--su', '--sua'):
            accepted(run(binary, directory, 'Surface.catt', [mode]), 'Surface.catt',
                     ['lift_two', 'lift_three', 'forward_class', 'reverse_class',
                      'extended_lift', 'variable_class', 'coloured'])
            for file, name in [('Positions.catt', 'identify_positions'),
                               ('OtherClass.catt', 'different_class'), ('Order.catt', 'wrong_order')]:
                rejected(run(binary, directory, file, [mode]), file, name)
            print(f'{mode} verified seven classes and rejected all three incompatible comparisons.')


if __name__ == '__main__':
    main()
