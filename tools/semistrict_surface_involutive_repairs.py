"""Check directed scalar repairs against a two-particle disk and a finite separating model."""
import argparse
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_ambient_repairs import then
from semistrict_surface_exact_boundary import accepted, run


def square_disk():
    # With centre fixed, the ordered pair is {-v, v} with a choice of first
    # particle. A half equator interchanges the two. Cap the full equator by
    # four affine triangles whose barycentres need never be used as particles.
    equator = [(1, 0, 0), (0, 1, 0), (-1, 0, 0), (0, -1, 0)]
    pole = (0, 0, 1)
    for index, a in enumerate(equator):
        b = equator[(index + 1) % 4]
        assert equator[(index + 2) % 4] == tuple(-x for x in a)
        # A strict separating linear functional on this entire closed face.
        normal = tuple(x + y + z for x, y, z in zip(a, b, pole))
        assert all(sum(x * y for x, y in zip(normal, v)) == 1 for v in (a, b, pole))
        assert a[0] * b[1] - a[1] * b[0] == 1
    print('The exchange lifts to opposite endpoints; its square bounds four collision-free triangles.')


def finite_presentation():
    identity = tuple(range(4))
    v, t, h = (0, 1, 3, 2), (0, 2, 1, 3), (1, 0, 3, 2)
    z = (2, 3, 0, 1)

    def inverse(p):
        return tuple(p.index(i) for i in identity)

    def product(*word):
        value = identity
        for letter in word:
            value = then(value, letter)
        return value

    def commutator(a, b):
        return product(inverse(a), inverse(b), a, b)

    u = commutator(v, t)
    assert product(inverse(h), u, h) == product(u, z)
    assert product(z, z) == identity and z != identity
    assert product(z, v) != product(v, z)
    assert commutator(identity, t) == identity
    assert product(inverse(h), identity, h) != product(identity, z)
    print('S4 realizes the defining relator with a noncentral involution, and separates the two faces.')


def raw_repairs(checkout, ranks):
    declarations = []
    for m in ranks:
        pole = 'x'
        for _ in range(m - 2):
            pole = f'id({pole})'
        ctx = f'(x : *) (a : id({pole}) -> id({pole}))'
        e, i = f'eh({pole},a,a)', 'id(comp[a,a])'
        square = f'comp[{e},{e}]'
        # Supply the disk at its two orientations. Only one directed ambient
        # repair may occur in each term. The unitors fit the written endpoints.
        declarations.extend([
            f'def introduce{m} {ctx} (disk : {i} -> {square}) (k : {e} -> {i})'
            f' : {i} -> {e} = comp[disk,comp[{e},[k]],unitor_r({e})]',
            f'def contract{m} {ctx} (disk : {square} -> {i}) (k : {i} -> {e})'
            f' : {e} -> {i} = comp[unitor_r_inv({e}),comp[{e},[k]],disk]',
        ])
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        file = 'Directed.catt'
        (folder / file).write_text('\n'.join(['import examples/eh', *declarations, '']))
        accepted(run(checkout / 'target/release/catt_strict', folder, file),
                 file, [line.split()[1] for line in declarations])
    print(f'Rice checked both directed constructions at scalar ranks {", ".join(map(str, ranks))}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    args = parser.parse_args()
    square_disk()
    finite_presentation()
    raw_repairs(args.checkout.resolve(), (3, 4, 5))
