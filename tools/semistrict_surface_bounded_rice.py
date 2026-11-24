"""Build Rice's pinned checker with the additional --insertion-width B theory."""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryFile

REVISION = '577993375ec7491b1b50c07dc58a0595c5fd58fc'


def replace_once(path, old, new):
    source = path.read_text()
    if source.count(old) != 1:
        raise ValueError(f'{path}: expected one copy of the upstream definition')
    path.write_text(source.replace(old, new))


def unpack_checker(checkout, destination):
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise ValueError(f'build destination must be empty: {destination}')
    with TemporaryFile() as archive:
        subprocess.run(['git', '-C', checkout, 'archive', REVISION], stdout=archive, check=True)
        archive.seek(0)
        subprocess.run(['tar', '-x', '-C', destination], stdin=archive, check=True)


def build(checkout, destination):
    unpack_checker(checkout, destination)
    common = destination/'src/common.rs'
    replace_once(common, 'pub enum Insertion {\n    Pruning,',
                 'pub enum Insertion {\n    Bounded(usize),\n    Pruning,')
    main = destination/'src/main.rs'
    replace_once(main, '    /// Turn off fullness check', '''    /// Strict units and insertion of composites of at most this width
    #[arg(long, conflicts_with_all = ["su", "sua"])]
    insertion_width: Option<usize>,

    /// Turn off fullness check''')
    replace_once(main, '    let mut env = Signature', '''    let strict_units = args.su || args.sua || args.insertion_width.is_some();
    let mut env = Signature''')
    replace_once(main, 'disc_rem: args.su || args.sua,', 'disc_rem: strict_units,')
    replace_once(main, 'endo_coh: args.su || args.sua,', 'endo_coh: strict_units,')
    replace_once(main, 'insertion: if args.sua {', '''insertion: if let Some(width) = args.insertion_width {
                Some(Insertion::Bounded(width))
            } else if args.sua {''')
    evaluator = destination/'src/eval.rs'
    replace_once(evaluator, '''TermN::Other(HeadN::Comp { tree }, args) if insertion == &Insertion::Full => tree
                .has_trunk_height(bh)
                .then_some((p, tree.clone(), args.clone())),''', '''TermN::Other(HeadN::Comp { tree }, args) => {
                let required_trunk = match insertion {
                    Insertion::Pruning => return None,
                    Insertion::Full => bh,
                    Insertion::Bounded(width) => bh.max(tree.dim().saturating_sub(*width)),
                };
                tree.has_trunk_height(required_trunk)
                    .then_some((p, tree.clone(), args.clone()))
            }''')
    subprocess.run(['cargo', 'build', '--release', '--locked'], cwd=destination, check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='local alexarice/catt-strict repository')
    parser.add_argument('destination', type=Path, help='new or empty build directory')
    args = parser.parse_args()
    build(args.checkout.resolve(), args.destination.resolve())
