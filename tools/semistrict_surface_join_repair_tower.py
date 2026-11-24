"""Generate and type-check successive two-sided raw repairs of a scalar diagonal."""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from semistrict_surface_join_bubbles import check_swap


def interfaces(top):
    # Both the product and braid are at the actual composite of the last two
    # repairs. Passing only their types would miss substitution of the repair.
    ctx = '(x : *) (a : id(x) -> id(x))'
    base, bubble = 'x', 'a'
    for rank in range(2, top + 1, 2):
        product = f'comp[{bubble},{bubble}]'
        braid = f'eh({base},{bubble},{bubble})'
        unit = f'id({product})'
        yield rank, ctx, base, bubble, product, braid, unit
        ctx += f' (back{rank} : {unit} -> {braid}) (forth{rank} : {braid} -> {unit})'
        base, bubble = product, f'comp[back{rank},forth{rank}]'


def validate(binary, directory, mode, rows):
    declarations = []
    for rank, ctx, base, bubble, product, braid, unit in rows:
        if mode:
            declarations.append(f'def step{rank} {ctx} : {braid} -> swap({bubble},{bubble}) = id({braid})')
        else:
            declarations.extend([
                f'def bubble{rank} {ctx} : id({base}) -> id({base}) = {bubble}',
                f'def step{rank} {ctx} : {product} -> {product} = {braid}',
                f'def stationary{rank} {ctx} : {product} -> {product} = {unit}'])
    file = directory / ('Converted.catt' if mode else 'Raw.catt')
    file.write_text('\n'.join(['import examples/eh', *declarations, '']))
    run = subprocess.run([binary, *mode, file], text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, check=True)
    if ('Error:' in run.stdout or f'Finished importing {file}' not in run.stdout
            or any('Checking ' + line.split()[1] + '\n' not in run.stdout for line in declarations)):
        raise ValueError(run.stdout[-3500:])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--top', type=int, default=4)
    args = parser.parse_args()
    if args.top < 2 or args.top % 2:
        parser.error('--top must be an even integer at least two')
    checkout = args.checkout.resolve()
    rows = list(interfaces(args.top))
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for flags in ((), ('--su',)):
            validate(checkout / 'target/release/catt_strict', folder, flags, rows)
        for rank, *_ in rows:
            size = 1 if rank == 2 else 2
            print(f'positive rank-{rank} bubble; raw parallel faces at {rank+1}; '
                  f'strict-unit swap checked; position permutation {check_swap(size)}')
