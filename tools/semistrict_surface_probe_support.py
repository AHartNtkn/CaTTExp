"""Count pure Hilton factors surviving every single-probe deletion.

Pass --probes M --sphere-degree K for ordered probes in an open ball.
The last point moves around the first M-1. Factor counts are integral and
independent of the coefficient groups of the respective spheres.
"""
from argparse import ArgumentParser
from itertools import product
import json
from math import comb, factorial

from semistrict_surface_face_whitehead import evaluate, nested


def supported_necklaces(letters, max_length):
    """Count primitive necklaces using all letters by their least word period."""
    primitive_words = {}
    for length in range(letters, max_length + 1):
        onto_words = sum((-1)**(letters-a) * comb(letters,a) * a**length
                         for a in range(letters+1))
        repetitions = sum(count for period,count in primitive_words.items()
                          if length % period == 0)
        primitive_words[length] = onto_words - repetitions
    return {length: count//length for length,count in primitive_words.items() if count}


def analyze(probes, sphere_degree):
    if probes < 2 or sphere_degree < 2:
        raise ValueError('both dimensions and probe counts must be at least two')
    counts = supported_necklaces(probes-1, sphere_degree-1)
    factors = [{'target_sphere': length+1, 'copies': count,
                'stem': sphere_degree-length-1}
               for length,count in counts.items()]
    result = dict(probes=probes, sphere_degree=sphere_degree, factors=factors)
    if sphere_degree > 2*probes-1:
        return dict(result, stable_adjoint_kernel='outside the computed range')
    rank = 0
    if sphere_degree == 2*probes-1 and probes % 2 and probes not in (3,7):
        rank = counts[probes-1]
    return dict(result, stable_adjoint_kernel_2_rank=rank)


def audit():
    checked = 0
    for letters in range(1,5):
        # Independently enumerate strict lexicographic rotation minima.
        counts = supported_necklaces(letters,7)
        for length in range(1,8):
            total = 0
            for word in product(range(letters),repeat=length):
                if len(set(word))==letters and all(word < word[i:]+word[:i]
                                                    for i in range(1,length)):
                    total += 1
            assert total==counts.get(length,0)
            checked += 1
    for probes in range(2,18):
        for k in range(2,2*probes):
            report = analyze(probes,k)
            assert bool(report['factors']) == (k>=probes)
            expected = (factorial(probes-2) if k==2*probes-1 and
                        probes%2 and probes not in (3,7) else 0)
            assert report['stable_adjoint_kernel_2_rank']==expected
    # Read an actual multilinear bracket and its square on meridians,
    # also at each puncture pinch. Integral tensor words see the square
    # in even sphere dimension. Odd squares need the unstable sphere input.
    for probes in range(2,9):
        letters = list(range(probes-1))
        tree = nested(letters)
        _, original = evaluate(tree,letters)
        assert original and original[tuple(letters)]==1
        for i in letters:
            assert not evaluate(tree,[None if a==i else a for a in letters])[1]
        _, square = evaluate([tree,tree],letters)
        assert square.get(tuple(letters)*2,0)==(2 if probes%2==0 else 0)
        assert bool(square)==(probes%2==0)
    print(f'Checked {checked} full-support counts by rotation, the first unstable '
          'degree for 2 through 17 probes, and signed squares and deletions for 2 through 8 probes.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('--probes',type=int)
    cli.add_argument('--sphere-degree',type=int)
    args = cli.parse_args()
    if args.probes is None and args.sphere_degree is None:
        audit()
    elif args.probes is None or args.sphere_degree is None:
        cli.error('supply both --probes and --sphere-degree')
    else:
        print(json.dumps(analyze(args.probes,args.sphere_degree),indent=2))
