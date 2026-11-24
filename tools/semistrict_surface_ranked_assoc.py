"""Build Rice's strict-unit checker with binary top associativity at selected ranks."""
import argparse
from pathlib import Path
import subprocess

from semistrict_surface_bounded_rice import replace_once, unpack_checker


def build(checkout, directory):
    unpack_checker(checkout, directory)
    common = directory / 'src/common.rs'
    replace_once(common, 'pub enum Insertion {', 'pub enum Insertion {\n    BinaryTop(usize),')
    main = directory / 'src/main.rs'
    replace_once(main, '    /// Turn off fullness check', '''    /// Use strict units and binary top associativity at or above this positive rank
    #[arg(long, conflicts_with_all = ["su", "sua"])]
    top_assoc_from: Option<std::num::NonZeroUsize>,

    /// Turn off fullness check''')
    replace_once(main, '    let mut env = Signature', '''    let units = args.su || args.sua || args.top_assoc_from.is_some();
    let mut env = Signature''')
    replace_once(main, 'disc_rem: args.su || args.sua,', 'disc_rem: units,')
    replace_once(main, 'endo_coh: args.su || args.sua,', 'endo_coh: units,')
    replace_once(main, 'insertion: if args.sua {', '''insertion: if let Some(rank) = args.top_assoc_from {
                Some(Insertion::BinaryTop(rank.get()))
            } else if args.sua {''')
    evaluator = directory / 'src/eval.rs'
    replace_once(evaluator, 'fn eval_coh<T: Clone>(', '''// At the temporal cut the three elements are source, seam, target.
fn temporal_cut<T>(mut args: &Tree<T>) -> &Tree<T> {
    while args.branches.len() == 1 {
        args = &args.branches[0];
    }
    args
}

fn temporal_cut_mut<T>(mut args: &mut Tree<T>) -> &mut Tree<T> {
    while args.branches.len() == 1 {
        args = &mut args.branches[0];
    }
    args
}

fn right_associate<T: Clone>(
    tree: &Tree<NoDispOption<Name>>,
    mut args: Tree<TermN<T>>,
) -> TermN<T> {
    let cut = temporal_cut_mut(&mut args);
    if let TermN::Other(HeadN::Comp { tree: inner }, inner_args) = &cut.branches[0].elements[0] {
        if inner == tree {
            let inside = temporal_cut(inner_args);
            let first = inside.branches[0].clone();
            let seam = inside.elements[1].clone();
            let start = cut.elements[0].clone();
            cut.branches[0] = inside.branches[1].clone();
            cut.elements[0] = seam.clone();
            let mut prefix = args.clone();
            let suffix = right_associate(tree, args);
            let cut = temporal_cut_mut(&mut prefix);
            cut.elements[0] = start;
            cut.elements[1] = seam;
            cut.branches[0] = first;
            cut.branches[1] = Tree::singleton(suffix);
            return TermN::Other(HeadN::Comp { tree: tree.clone() }, prefix);
        }
    }
    TermN::Other(HeadN::Comp { tree: tree.clone() }, args)
}

fn eval_coh<T: Clone>(''')
    replace_once(evaluator, '        return TermN::Other(HeadN::Comp { tree }, args);', '''        if let Some(Insertion::BinaryTop(first_rank)) = &env.reduction.insertion {
            let cut = temporal_cut(&tree);
            if cut.branches.len() == 2 && cut.branches.iter().all(|b| b.branches.is_empty())
                && tyn.dim() >= *first_rank
            {
                return right_associate(&tree, args);
            }
        }
        return TermN::Other(HeadN::Comp { tree }, args);''')
    subprocess.run(['cargo', 'build', '--release', '--locked'], cwd=directory, check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    build(args.checkout.resolve(), args.destination.resolve())
