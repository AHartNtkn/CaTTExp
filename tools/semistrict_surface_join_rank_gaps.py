"""Check the raw rank-gap transport and a compound bubble's marked repair slides."""
import argparse
from itertools import permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_component_braids import Components, cabling, restrict
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_history_group import exchange
from semistrict_surface_join_bubbles import check_swap


def compose(*factors):
    result = tuple(range(len(factors[0])))
    for factor in factors:
        result = tuple(result[i] for i in factor)
    return result


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def marked_checks():
    # Two events per bubble. Its block transposition is an even permutation.
    cross = tuple(check_swap(2))
    unit = tuple(range(4))
    cases = 0
    for left, right in product(permutations(unit), repeat=2):
        before = compose(left, cross, inverse(left))
        after = compose(inverse(right), cross, right)
        for source, target in ((unit, cross), (cross, unit)):
            left_mark = (compose(before, left), right)
            right_mark = (left, compose(right, after))
            assert left_mark != right_mark
            for face in (source, target):
                assert compose(left_mark[0], face, left_mark[1]) == compose(
                    right_mark[0], face, right_mark[1])
            cases += 1
    return cases


def decorated_checks():
    ports = {'birth': ('', 'ff'), 'death': ('ff', ''), 'scalar': ('', '')}
    count = 0
    for first, second, gap in product(range(4), range(4), (0, 1)):
        def shell(size):
            return [(gap, 'birth'), *[(gap + 1, 'scalar')]*size, (gap, 'death')]

        spells = shell(first) + shell(second)
        history = tuple((pos, i) for i, (pos, _) in enumerate(spells))
        marks = {i: ports[name] for i, (_, name) in enumerate(spells)}
        parts = Components(history, marks, gap)
        packets = parts.packets(history, marks)
        outside = {0, first + 2}
        for packet in packets:
            if len(packet) < 2:
                continue
            exterior = {c for c, _, _ in packet} == outside
            for sign, power in product((-1, 1), (1, 2)):
                word = cabling(packet, (sign,)*power)
                current = history
                for move in word:
                    current = exchange(current, move, marks)
                    assert current is not None
                assert restrict(len(history), word, outside) == ((sign,)*power if exterior else ())
                actual = [(pos, spells[i][1]) for pos, i in current]
                expected = shell(second) + shell(first) if exterior and power == 1 else spells
                assert actual == expected
                count += 1
    return count


def rice(checkout):
    def attachment(var):
        pole = f'comp[comp[{var},{var}],{var}]'
        p = f'p({var},{var},{var})'
        return pole, f'(k : {p} -> comp[id({pole}),{p}])'

    pole, boundary = attachment('f')
    r = 'r(f,f,f)'
    args = f'(x : *) (f : x -> x) {boundary}'
    lines = [
        'def p = coh [[f,g,h] : comp[comp[f,g],h] -> comp[f,comp[g,h]]]',
        'def r = coh [[f,g,h] : comp[f,comp[g,h]] -> comp[comp[f,g],h]]',
        'def enter = coh [[f,g,h] : id(comp[comp[f,g],h]) -> comp[p(f,g,h),r(f,g,h)]]',
        'def leave = coh [[f,g,h] : comp[comp[id(comp[comp[f,g],h]),p(f,g,h)],r(f,g,h)] -> id(comp[comp[f,g],h])]',
        f'def closegap {args} : id({pole}) -> id({pole}) = comp[enter(f,f,f),comp[[k],{r}],leave(f,f,f)]',
    ]
    ctx = '(x : *) (g : x -> x)'
    base = 'g'
    for var in ('a', 'b'):
        ctx += f' ({var} : {base} -> {base})'
        pole, boundary = attachment(var)
        lines.append(f'def close{var} {ctx} {boundary} : id({pole}) -> id({pole}) = closegap({base},{var},k)')
        base = var

    ctx = '(x : *) (f : x -> x) (u : id(x) -> f) (d : f -> id(x))'
    bubble = 'comp[u,d]'
    word = f'comp[{bubble},{bubble}]'
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for raw in (True, False):
            braid = f'eh(x,{bubble},{bubble})' if raw else f'id({word})'
            args = f'{ctx} (k : {braid} -> id({word}))'
            left = f'comp[comp[{braid},[k]],unitor_r({braid})]'
            right = f'comp[comp[[k],{braid}],unitor_l({braid})]'
            declarations = lines.copy() if raw else []
            for name, term in (('leftslide', left), ('rightslide', right)):
                ty = f'comp[{braid},{braid}] -> {braid}' if raw else f'{term} -> k'
                body = term if raw else 'id(k)'
                declarations.append(f'def {name} {args} : {ty} = {body}')
            file = 'Raw.catt' if raw else 'Units.catt'
            (folder / file).write_text('\n'.join(['import examples/eh', *declarations, '']))
            output = run(binary, folder, file, () if raw else ('--su',))
            accepted(output, file, [line.split()[1] for line in declarations if '= coh' not in line])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    args = parser.parse_args()
    rice(args.checkout.resolve())
    print('Rice checked gap transports in degrees 3, 4 and 5, both compound raw slides, '
          'and their strict-unit reductions with identity crossing.')
    print(f'{marked_checks()} translated marked slides have equal faces and distinct marks.')
    print(f'{decorated_checks()} positioned exchanges distinguish exterior and internal windings.')
