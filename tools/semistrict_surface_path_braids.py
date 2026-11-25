"""Read a braid of closed paths after specializing selected paths to the tensor unit."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
from pathlib import Path

from semistrict_surface_shared_edge import braid_image, inverse
from semistrict_surface_planar_tiers import reduce_letters


def restrict_braid(keep, braid):
    """Keep tracks by their initial names, updating their positions at each crossing."""
    live = list(keep)
    out = []
    for generator in braid:
        i = abs(generator) - 1
        if not 0 <= i < len(live) - 1:
            raise ValueError(f"invalid crossing {generator} on {len(live)} paths")
        if live[i] and live[i + 1]:
            position = sum(live[:i]) + 1
            out.append(position if generator > 0 else -position)
        live[i], live[i + 1] = live[i + 1], live[i]
    return tuple(out), tuple(live)


def brunnian(strands):
    """Iterated commutator of loops of the last point around the other points."""
    if strands < 2:
        raise ValueError("a Brunnian braid needs at least two strands")
    word = ()
    for i in range(1, strands):
        route = tuple(range(strands - 1, i, -1))
        loop = route + (i, i) + inverse(route)
        word = word + loop + inverse(word) + inverse(loop) if word else loop
    return word


def unary_coverage(tails, closed, erasable):
    """Do the listed exponent classes cover N? Tail pairs also act at every translate."""
    shifts = [(min(i, j), abs(j - i)) for i, j in tails if i != j]
    if not shifts:
        return False
    start, period = min(shifts, key=lambda pair: sum(pair))

    def fold(k):
        return k if k < start else start + (k - start) % period

    edges = defaultdict(set)

    def connect(i, j):
        i, j = fold(i), fold(j)
        edges[i].add(j)
        edges[j].add(i)

    for i, j in tails:
        # Once both endpoints reach the periodic part, offsets repeat.
        for offset in range(max(0, start - min(i, j)) + period):
            connect(i + offset, j + offset)
    for i, j in closed:
        connect(i, j)
    seen = {fold(k) for k in erasable}
    todo = list(seen)
    while todo:
        for neighbour in edges[todo.pop()] - seen:
            seen.add(neighbour)
            todo.append(neighbour)
    return len(seen) == start + period


def code(letter):
    return '11' + '0' * letter


def forbidden_factors(types):
    """types are 0 for left letters, 1 for heads, 2 for right letters."""
    result = {'<>', '<0', '<10', '<1>', '1>', '111', '010', '0' * (len(types) + 1)}
    for a, ta in enumerate(types, 1):
        if ta == 2:
            result.update('<' + code(a) + end for end in ('11', '>'))
        if ta == 0:
            result.add(code(a) + '>')
        for b, tb in enumerate(types, 1):
            if (ta, tb) not in {(0, 0), (0, 1), (1, 2), (2, 2)}:
                result.update(code(a) + code(b) + end for end in ('11', '>'))
    return result


def audit_path_equations():
    # The internal Coxeter relations present S3. Opening a fixes the initial
    # state and closing after b preserves the label at every possible prefix.
    letters = {'a': (0, 2, 1), 'b': (1, 0, 2)}
    states = {}
    edges = defaultdict(set)
    for length in range(9):
        for word in product(letters, repeat=length):
            w = ''.join(word)
            state = 0
            for letter in w:
                state = letters[letter][state]
            states[w] = state
            marked = '<' + w + '>'
            for lhs, rhs in (('aa', ''), ('bb', ''), ('aba', 'bab'),
                             ('<a', '<'), ('b>', '>')):
                for i in range(len(marked) - len(lhs) + 1):
                    if marked.startswith(lhs, i):
                        changed = (marked[:i] + rhs + marked[i + len(lhs):])[1:-1]
                        edges[w].add(changed)
                        edges[changed].add(w)
    equivalent = {''}
    todo = ['']
    while todo:
        for neighbour in edges[todo.pop()] - equivalent:
            equivalent.add(neighbour)
            todo.append(neighbour)
    assert equivalent == {w for w, state in states.items() if state in (0, 1)}
    print(f"Compared {len(states)} closed words with reversible internal, prefix and suffix moves.")


def audit_codes():
    types = (0, 1, 2)
    illegal = forbidden_factors(types)
    # Enumerate genuine tape strings independently of the forbidden-window rules.
    valid = {'<' + code(1) * left + code(2) + code(3) * right + '>'
             for left in range(6) for right in range(6)}
    checked = 0
    for size in range(15):
        for bits in product('01', repeat=size):
            w = '<' + ''.join(bits) + '>'
            assert (w in valid) == all(f not in w for f in illegal)
            checked += 1
    # A headed replacement before another symbol must not consume the prefix of
    # the longer symbol code. Compare its matching positions with decoded ones.
    for left, right in product(range(4), repeat=2):
        tokens = [1] * left + [2] + [3] * right
        w = ''.join(map(code, tokens)) + '>'
        cursor = 0
        for token in tokens:
            for other in range(1, 4):
                matches = any(w.startswith(code(other) + end, cursor) for end in ('>', '11'))
                assert matches == (other == token)
            cursor += len(code(token))
    assert unary_coverage([(4, 6), (0, 2)], [(0, 1)], [0])
    assert not unary_coverage([(4, 6), (0, 2)], [], [0])
    assert unary_coverage([(2, 5)], [(0, 6), (1, 7)], [2, 3, 4])
    assert not unary_coverage([], [(0, 5)], [0, 1, 2, 3, 4])
    print(f"Checked the binary error rules on all {checked} words through length 14 "
          "and the unary periodic quotient on four presentations.")


def emit_context(directory):
    """Check two loop letters, one path equation, and a closed path contracted to the unit."""
    from catt import STAR, arr, comp2, infer, v
    from ct_suspension import ident
    from emit_agda import Emitter

    ctx = (STAR,)

    def declare(source, target):
        nonlocal ctx
        ty = infer(ctx, source)
        assert ty == infer(ctx, target)
        cell = v(len(ctx))
        ctx += (arr(ty, source, target),)
        return cell

    def reversible(source, target):
        first, back = declare(source, target), declare(target, source)
        for x, y, base in ((first, back, source), (back, first, target)):
            path, unit = comp2(ctx, 2, x, y), ident(ctx, base)
            declare(path, unit)
            declare(unit, path)
        return first, back

    wire = declare(v(0), v(0))
    edge_unit = ident(ctx, v(0))
    opening, closing = declare(edge_unit, wire), declare(wire, edge_unit)
    a, b = declare(wire, wire), declare(wire, wire)
    reversible(comp2(ctx, 1, a, b), comp2(ctx, 1, b, a))
    closed = comp2(ctx, 1, comp2(ctx, 1, opening, a), closing)
    blank = ident(ctx, edge_unit)
    shrink, grow = reversible(closed, blank)
    bubble = comp2(ctx, 2, grow, shrink)
    expected = arr(infer(ctx, blank), blank, blank)
    assert infer(ctx, bubble) == expected
    writer = Emitter()
    g, term, ty = writer.ctx(ctx), writer.tm(bubble), writer.ty(expected)
    writer.checks.extend([f'valid : {g} ⊢ctx\nvalid = from-just (checkCtx {g})',
                          f'round-trip : Σ Ty ({g} ⊢tm {term} ∶_)\n'
                          f'round-trip = from-just (infer {g} {term})',
                          f'faces : fst round-trip ≡ {ty}\nfaces = refl'])
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'PathBraidContext.agda').write_text(
        writer.module('PathBraidContext', 'Binary string attachments and the positive 3-bubble.'))


def audit():
    # Quotient the full Artin action on initial meridians independently of
    # restricting the crossing movie. Its output is indexed by terminal slots.
    total = 0
    for strands in range(2, 5):
        alphabet = tuple(j for i in range(1, strands) for j in (i, -i))
        for length in range(4):
            for word in product(alphabet, repeat=length):
                image = braid_image(strands, word)
                for keep in product((False, True), repeat=strands):
                    subword, terminal = restrict_braid(keep, word)
                    labels = {j + 1: sum(keep[:j + 1]) for j in range(strands) if keep[j]}
                    quotient = tuple(
                        reduce_letters(tuple(labels[abs(g)] * (1 if g > 0 else -1)
                                             for g in meridian if abs(g) in labels))
                        for meridian, retained in zip(image, terminal) if retained)
                    assert quotient == braid_image(sum(keep), subword)
                    total += 1
    clauses = 0
    for strands in range(2, 6):
        word = brunnian(strands)
        for keep in product((False, True), repeat=strands):
            subword, terminal = restrict_braid(keep, word)
            assert terminal == keep
            assert (braid_image(sum(keep), subword) == braid_image(sum(keep), ())) == (not all(keep))
            clauses += 1
    # The two clauses (a OR b) AND (b OR c) occupy disjoint strand blocks.
    word = (1, 1, 3, 3)
    for a, b, c in product((False, True), repeat=3):
        keep = tuple(not erased for erased in (a, b, b, c))
        out, _ = restrict_braid(keep, word)
        assert (braid_image(sum(keep), out) == braid_image(sum(keep), ())) == ((a or b) and (b or c))
    print(f"Verified {total} meridian quotient readings, {clauses} Brunnian readings, "
          "and all 8 inputs of a two-clause comparison.")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--keep', help='one bit per initial strand, with 1 retaining its path')
    parser.add_argument('crossings', type=int, nargs='*')
    args = parser.parse_args()
    if args.keep is None:
        if args.crossings:
            parser.error('supply --keep for a braid query')
        audit()
        audit_codes()
        audit_path_equations()
    else:
        if any(bit not in '01' for bit in args.keep):
            parser.error('--keep accepts only 0 and 1')
        keep = [bit == '1' for bit in args.keep]
        try:
            out, _ = restrict_braid(keep, args.crossings)
        except ValueError as exc:
            parser.error(str(exc))
        print('Remaining braid:', list(out))
        print('Trivial:', braid_image(sum(keep), out) == braid_image(sum(keep), ()))

    if args.agda_dir:
        emit_context(args.agda_dir)
