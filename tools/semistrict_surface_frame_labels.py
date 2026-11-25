"""Construct tangent frames used by the odd-shell sphere-bundle labels."""

from argparse import ArgumentParser
from itertools import combinations


def dot(x, z):
    return (x & z).bit_count() % 2


def anticommutes(left, right):
    x, z = left
    y, w = right
    return dot(x, w) ^ dot(y, z)


def small_frame(bits):
    """Find the real, complex, quaternionic or octonionic signed permutations."""
    size = 1 << bits
    candidates = [(x, z) for x in range(size) for z in range(size) if dot(x, z)]

    def extend(remaining, needed):
        if needed == 0:
            return []
        for i, op in enumerate(remaining):
            others = [v for v in remaining[i+1:] if anticommutes(op, v)]
            if len(others) >= needed - 1:
                tail = extend(others, needed - 1)
                if tail is not None:
                    return [op, *tail]
        return None

    result = extend(candidates, size - 1)
    assert result is not None
    return result


def frame(length):
    """An operator (x,z) sends basis v to (-1)^(z.v) times basis v xor x."""
    twos = (length & -length).bit_length() - 1
    blocks, bits = divmod(twos, 4)
    generators = small_frame(bits)
    # Z tensor Cl(7), together with the two-dimensional skew swap tensor I.
    eight = [(x, z | 8) for x, z in small_frame(3)] + [(8, 8)]
    volume_x = volume_z = 0
    for x, z in eight:
        volume_x ^= x
        volume_z ^= z
    for _ in range(blocks):
        periodic = [(x << bits, z << bits) for x, z in eight]
        generators = periodic + [((volume_x << bits) | x, (volume_z << bits) | z)
                                 for x, z in generators]
        bits += 4
    assert len(generators) == 8 * blocks + (1 << (twos % 4)) - 1
    return generators


def act(op, index):
    x, z = op
    return index ^ x, (-1 if dot(z, index) else 1)


def audit(length):
    operators = frame(length)
    for op in operators:
        for i in range(length):
            j, s = act(op, i)
            assert 0 <= j < length and act(op, j) == (i, -s)
    for left, right in combinations(operators, 2):
        for i in range(length):
            j, s = act(left, i)
            k, t = act(right, j)
            a, p = act(right, i)
            b, q = act(left, a)
            assert k == b and s*t == -p*q
    return len(operators)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--rank", type=int)
    parser.add_argument("--bottom", type=int)
    args = parser.parse_args()
    if args.rank is None and args.bottom is None:
        for length in (6, 10, 12, 16, 24, 32, 48, 64, 128, 256, 384):
            fields = audit(length)
            print(f"S^{length - 1}: {fields} independent tangent fields")
        return
    if args.rank is None or args.bottom is None or not 2 <= args.rank < args.bottom or args.bottom % 2 != 1:
        parser.error("supply an odd bottom and 2 <= rank < bottom")
    m, n = args.bottom, args.rank
    fields = audit(m + 1)
    if fields < n - 1:
        print(f"The construction requires {n - 1} independent fields; this sphere has {fields}.")
        return
    d = m - n
    print(f"Using {n - 1} of the {fields} available tangent fields on S^{m}.")
    print(f"The S^{d}-bundle has dimension {m+d}.")
    print(f"The bundle label and every local K(G,{d}) type reflect in degree {n+2*m-1}.")
    if n == 2 and (m + 1) % 4 == 2:
        print(f"All label models through dimension {m+d-1} have exact kernel H_{d}/2.")


if __name__ == "__main__":
    main()
