"""Compare a strictly unital presentation and a raw presentation at a marked boundary."""
import argparse
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


HEADS = """import examples/eh-common
def wrap = coh [ x{f}y : x -> y ]
def enter = coh [ x{f}y : f -> wrap(f) ]
"""


def presentation(rank, short):
    # Iterating the source globe suspends the same attachment without identifying poles.
    poles = ['(s0 : *)', '(t0 : *)']
    for i in range(1, rank):
        faces = f's{i - 1} -> t{i - 1}'
        poles.extend([f'(s{i} : {faces})', f'(t{i} : {faces})'])
    seam = 'comp[a,h]' if short else 'comp[a,enter(f),h]'
    args = ' '.join([*poles, f'(f : s{rank - 1} -> t{rank - 1})',
                     '(a : f -> f)', '(h : wrap(f) -> f)',
                     f'(p : {seam} -> a)', f'(b : {seam} -> a)',
                     '(q : comp[p,id(a)] -> b)'])
    return args


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built Rice catt-strict checkout')
    checkout = parser.parse_args().checkout.resolve()
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as temp:
        work = Path(temp)
        (work / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for rank in range(1, 6):
            for short in (False, True):
                args = presentation(rank, short)
                source = HEADS + f'def fitted {args} : p -> b = comp[unitor_r_inv(p),q]\n'
                if short:
                    source += f'def expanded {args} : comp[a,enter(f),h] -> a = p\n'
                name = 'Presentation.catt'
                (work / name).write_text(source)
                for mode in ([], ['--su'], ['--sua']):
                    output = run(binary, work, name, mode)
                    if short and not mode:
                        assert ('Checking fitted' in output and 'Mismatch between inferred terms' in output
                                and 'labelling "{a}{h}"' in output and f'Finished importing {name}' not in output), output
                    else:
                        accepted(output, name, ['fitted', 'expanded'] if short else ['fitted'])
            # Test both marked *new* boundaries on the raw presentation in the published modes.
            args = presentation(rank, False)
            name = 'Query.catt'
            (work / name).write_text(HEADS + f'def compact {args} : comp[a,h] -> a = p\n'
                                     + f'def direct {args} : p -> b = q\n')
            for mode in (['--su'], ['--sua']):
                accepted(run(binary, work, name, mode), name, ['compact', 'direct'])
            name = 'Reverse.catt'
            (work / name).write_text(HEADS + f'def reverse {args} : b -> p = q\n')
            for mode in ([], ['--su'], ['--sua']):
                rejected(run(binary, work, name, mode), name, 'reverse')
    print('Checked 5 ranks, 25 accepted presentation runs, 5 raw formation rejections, '
          '10 published runs at the marked boundaries, and 15 reversed-use rejections.')


if __name__ == '__main__':
    main()
