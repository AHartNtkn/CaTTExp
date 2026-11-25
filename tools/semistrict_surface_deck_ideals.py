"""Check two-probe deck translations and build common tests for deck polynomials.

With a JSON file, use {"holes": h, "factors": [[[coefficient, signed_word], ...], ...]}.
The output gives the actual integral sphere coefficients and separating cover.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_gap_linking import cover, lift
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_mixed_word_tests import point_push, read_push


def collect(terms):
    out = Counter()
    for word, coefficient in terms:
        out[reduced(word)] += coefficient
    return {word: value for word, value in out.items() if value}


def multiply(left, right):
    return collect((u + v, a * b) for u, a in left.items() for v, b in right.items())


def erase(polynomial, hole):
    return collect((tuple(x for x in w if abs(x) != hole), a) for w, a in polynomial.items())


def test_polynomial(holes, factors):
    value = {(): 1}
    for hole in range(1, holes + 1):
        value = multiply(value, {(hole,): 1, (): -1})
    for factor in factors:
        if not factor:
            raise ValueError('the zero polynomial cannot be a test factor')
        value = multiply(value, factor)
    assert value and all(not erase(value, i) for i in range(1, holes + 1))
    return value


def sheet_matrix(polynomial, sheets, permutations):
    matrix = Counter()
    for w, coefficient in polynomial.items():
        for i in range(len(sheets)):
            matrix[i, lift(w, i, permutations)] += coefficient
    return {pair: n for pair, n in matrix.items() if n}


def check_transport(holes, value, u, v):
    transported = collect((u + w + inv(v), a) for w, a in value.items())
    sheets, permutations = cover([*value, *transported], holes)
    original = sheet_matrix(value, sheets, permutations)
    # A point-push on either probe permutes its sheet in the pair linking
    # table. Pull both indices back independently before reading the entry.
    reindexed = {(lift(inv(u), i, permutations), lift(inv(v), j, permutations)): a
                 for (i, j), a in original.items()}
    assert reindexed == sheet_matrix(transported, sheets, permutations)
    assert {sheets[j]: a for (i, j), a in reindexed.items() if i == 0} == transported
    return len(sheets)


def audit():
    cases = 0
    for holes in range(1, 4):
        pushes = [()] + [(i,) for i in range(1, holes + 1)]
        pushes.extend((tuple(range(1, holes + 1)), tuple(range(-holes, 0))))
        for w in pushes:
            assert read_push(holes, point_push(w)) == w
        value = collect([((), 2), ((1,), -1), ((-holes, 1), 3)])
        for u, v in product(pushes, repeat=2):
            check_transport(holes, value, u, v)
            cases += 1

    # The degree-five test loop is invisible to abelian winding. Its action
    # separates two lifts of the parked probe even in a finite cover.
    commutator = (1, 2, -1, -2)
    assert read_push(2, point_push(commutator)) == commutator
    powers = [commutator * n for n in range(1, 9)]
    sheets, permutations = cover([(), *powers], 2)
    assert len({lift(w, 0, permutations) for w in [(), *powers]}) == len(powers) + 1
    for w in powers:
        assert sheet_matrix({w: 1, (): -1}, sheets, permutations)[0, lift(w, 0, permutations)] == 1

    # Both orders of multiplication matter. Project the product into
    # a quotient where the commutator factor vanishes.
    factors = [{(): -2, (1,): 1, (2,): 1}, {(): 3, (2, -1): -4}, {(1, 2): 1, (2, 1): -1}]
    value = test_polynomial(2, factors)
    assert multiply(factors[0], factors[1]) != multiply(factors[1], factors[0])
    # Kill the commutator factor in an abelian representation.
    degrees = Counter()
    for w, a in value.items():
        degrees[w.count(1) - w.count(-1), w.count(2) - w.count(-2)] += a
    assert all(n == 0 for n in degrees.values())
    # Kill t^2-t-1 in the integral Laurent quotient, where t is a unit.
    # Multiplication by t sends (a,b) to (b,a+b) on the basis (1,t).
    def remainder(poly):
        a = b = 0
        for word, coef in poly.items():
            c, d = 1, 0
            for x in word:
                c, d = (d, c + d) if x == 1 else (d - c, c)
            a, b = a + coef * c, b + coef * d
        return a, b

    fibonacci = {(1, 1): 1, (1,): -1, (): -1}
    for n in range(1, 13):
        assert remainder({(1,) * n: 1, (): -1}) != (0, 0)
    assert remainder(test_polynomial(1, [fibonacci, {(-1,): 2, (): -3}])) == (0, 0)
    # The Laurent module on a double orbit need not be free. Here u*g
    # equals g*v, so a diagonal shift fixes the seed despite u != v.
    u, g, v = (1,), (2,), (-2, 1, 2)

    def power(w, n):
        return (w if n >= 0 else inv(w)) * abs(n)

    shifts = 0
    for p, q in product(range(-3, 4), repeat=2):
        base = reduced(power(u, p) + g + power(v, -q))
        assert base == reduced(power(u, p + 1) + g + power(v, -q - 1))
        shifts += 1
    print(f'{shifts} diagonal shifts preserve the deck label of a nonfree double orbit.')
    print(f'{cases} independent probe transports matched both sheet permutations.')
    print(f'Eight deck differences separated in a {len(sheets)}-sheet cover.')
    print(f'The two-hole product has {len(value)} nonzero coefficients and vanishes on either erasure.')


def check_boundaries(checkout):
    template = (checkout / 'examples/syllepsis-su.catt').read_text()
    definitions = template[template.index('def swap ='):template.index('def left u')]
    context = '(x : *) (q : id(id(x)) -> id(id(x))) (r : id(id(x)) -> id(id(x))) (b : id(x) -> id(x))'
    base = 'state(x,q,r,b)'
    definitions += f"""
def winding (x : *) (q : id(id(x)) -> id(id(x))) (b : id(x) -> id(x))
  : comp[[q],b] -> comp[[q],b] = comp[swapnatleft(q,b),swapnatright(b,q)]
def state {context} = comp[comp[[q],b],comp[[r],b]]
def first {context} : {base} -> {base} = comp[[winding(x,q,b)],comp[[r],b]]
def second {context} : {base} -> {base} = comp[comp[[q],b],[winding(x,r,b)]]
"""
    for side in ('first', 'second'):
        loop = f'{side}(x,q,r,b)'
        pair = f'comp[{loop},back]'
        definitions += f"""
def act_{side} {context} (back : {base} -> {base})
  (enter : id({base}) -> {pair}) (leave : {pair} -> id({base}))
  (a : id({base}) -> id({base})) : id({base}) -> id({base})
  = comp[enter,comp[{loop},[a],back],leave]
"""
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'DeckAction.catt').write_text(definitions)
        for mode in ('--su', '--sua'):
            output = run(checkout / 'target/release/catt_strict', folder, 'DeckAction.catt', [mode])
            accepted(output, 'DeckAction.catt', ['winding', 'first', 'second', 'act_first', 'act_second'])


def read_test(data):
    holes = data['holes']
    if type(holes) is not int or holes < 0:
        raise ValueError('expected a nonnegative number of holes')
    factors = []
    for factor in data['factors']:
        for coef, word in factor:
            if type(coef) is not int or any(type(x) is not int or not 1 <= abs(x) <= holes for x in word):
                raise ValueError('invalid deck coefficient or puncture label')
        factors.append(collect((word, coef) for coef, word in factor))
    value = test_polynomial(holes, factors)
    sheets, permutations = cover(list(value), holes)
    matrix = sheet_matrix(value, sheets, permutations)
    assert {sheets[j]: n for (i, j), n in matrix.items() if i == 0} == value
    return {'coefficients': [[n, w] for w, n in sorted(value.items())], 'sheets': sheets,
            'permutations': permutations}


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    parser.add_argument('input', nargs='?', type=Path)
    options = parser.parse_args()
    if options.input:
        print(json.dumps(read_test(json.loads(options.input.read_text())), indent=2))
    else:
        audit()
    if options.catt_strict:
        check_boundaries(options.catt_strict.resolve())
        print('Strict units and insertion checked both actions on the same 5-sphere boundary.')
