"""Check the typed string moves and raw attachments in the configuration-braid reduction."""
import argparse
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, run


BLANK = '_'
SYMBOLS = (BLANK, 'a')
BIRTH, DEATH, CLEAN = 'birth', 'death', 'clean'


def head(state, symbol):
    return f'head_{state}_{symbol}'


def encode(left, state, scanned, right):
    return (BIRTH, *('l' + c for c in left), head(state, scanned),
            *('r' + c for c in right), DEATH)


def rules(states, machine):
    result = []
    for state, read in product(states, SYMBOLS):
        h = head(state, read)
        if (state, read) not in machine:
            result.append(((h,), (CLEAN,)))
            continue
        target, write, direction = machine[state, read]
        if direction == 'R':
            for c in SYMBOLS:
                result.append(((h, 'r' + c), ('l' + write, head(target, c))))
            result.append(((h, DEATH), ('l' + write, head(target, BLANK), DEATH)))
        else:
            for c in SYMBOLS:
                result.append((('l' + c, h), (head(target, c), 'r' + write)))
            result.append(((BIRTH, h), (BIRTH, head(target, BLANK), 'r' + write)))
    for c in SYMBOLS:
        result.append((('l' + c, CLEAN), (CLEAN,)))
        result.append(((CLEAN, 'r' + c), (CLEAN,)))
    return result


def rewrites(word, table):
    for src, tgt in table:
        for i in range(len(word) - len(src) + 1):
            if word[i:i + len(src)] == src:
                yield word[:i] + tgt + word[i + len(src):]


def tape_data(left, scanned, right):
    symbols = left + (scanned,) + right
    return {i - len(left): c for i, c in enumerate(symbols) if c != BLANK}


def decode(word, states):
    assert word[0] == BIRTH and word[-1] == DEATH
    for i, gate in enumerate(word):
        for q, c in product(states, SYMBOLS):
            if gate == head(q, c):
                left, right = word[1:i], word[i + 1:-1]
                assert all(g.startswith('l') for g in left)
                assert all(g.startswith('r') for g in right)
                return q, tape_data(tuple(g[1:] for g in left), c, tuple(g[1:] for g in right))
    raise AssertionError(f'Missing head in {word}')


def check_transitions():
    states = ('s', 't')
    wings = [w for n in range(3) for w in product(SYMBOLS, repeat=n)]
    tests = 0
    for q, c, target, write, move in product(states, SYMBOLS, states, SYMBOLS, ('L', 'R')):
        table = rules(states, {(q, c): (target, write, move)})
        for left, right in product(wings, repeat=2):
            word = encode(left, q, c, right)
            step, = rewrites(word, table)
            tape = tape_data(left, c, right)
            tape[0] = write
            offset = 1 if move == 'R' else -1
            expected = {i - offset: letter for i, letter in tape.items() if letter != BLANK}
            assert decode(step, states) == (target, expected)
            backward = [(tgt, src) for src, tgt in table]
            assert word in rewrites(step, backward)
            tests += 1

    table = rules(states, {})
    for left, right in product(wings, repeat=2):
        word = encode(left, 's', BLANK, right)
        frontier = {word}
        for _ in range(1 + len(left) + len(right)):
            frontier = {step for w in frontier for step in rewrites(w, table)}
        assert frontier == {(BIRTH, CLEAN, DEATH)}
    print(f'Checked {tests} transitions against recentered finite tapes and {len(wings)**2} cleanup inputs.')


def check_nonhalting_component():
    # State s cycles to its right neighbour and back precisely when it reads a.
    # In state t it tests the neighbour on its left by returning to s.
    states = ('s', 't')
    machine = {('s', 'a'): ('t', 'a', 'R'),
               **{('t', c): ('s', c, 'L') for c in SYMBOLS}}
    table = rules(states, machine)

    def halts(word):
        if CLEAN in word:
            return True
        state, tape = decode(word, states)
        return tape.get(0 if state == 's' else -1, BLANK) == BLANK

    wings = [w for n in range(3) for w in product(SYMBOLS, repeat=n)]
    directions = table + [(tgt, src) for src, tgt in table]
    edges = 0
    for left, right in product(wings, repeat=2):
        words = [encode(left, q, c, right) for q, c in product(states, SYMBOLS)]
        words.append((BIRTH, *('l' + c for c in left), CLEAN, *('r' + c for c in right), DEATH))
        for word in words:
            for neighbour in rewrites(word, directions):
                assert halts(word) == halts(neighbour)
                edges += 1
    print(f'Checked the halting invariant on {edges} signed moves of a machine with a two-state cycle.')


def check_binary_windows():
    # Use a non-power-of-two alphabet so invalid blocks and incomplete
    # end blocks occur alongside genuine blanks. Q marks the head.
    alphabet = ('_', 'a', 'b')
    pairs = tuple(product(('s', 't'), alphabet))
    tape = {c: format(i, '02b') for i, c in enumerate(alphabet)}
    codes = {pair: format(i, '03b') for i, pair in enumerate(pairs)}
    codewords = tuple(codes.values())
    windows = ['', '0', '1', *tape.values(), '11']
    cases = 0
    for move in ('L', 'R'):
        table = []
        for q, read in pairs:
            target = 's' if q == 't' else 't'
            write = alphabet[(alphabet.index(read) + 1) % len(alphabet)]
            prefix = codes[q, read] + 'Q'
            for c, bits in tape.items():
                out_head = codes[target, c] + 'Q'
                if move == 'R':
                    table.append((prefix + bits, tape[write] + out_head))
                else:
                    table.append((bits + prefix, out_head + tape[write]))
            if move == 'R':
                table.append((prefix + 'z', tape[write] + codes[target, BLANK] + 'Qz'))
                table.append((prefix + '11', 'H'))
                table.extend((prefix + bad + 'z', 'Hz') for bad in ('0', '1'))
            else:
                table.append(('d' + prefix, 'd' + codes[target, BLANK] + 'Q' + tape[write]))
                table.append(('11' + prefix, 'H'))
                table.extend(('d' + bad + prefix, 'dH') for bad in ('0', '1'))
        table.extend((bad + 'Q', 'H') for bad in ('110', '111'))
        for n in range(3):
            table.extend(('d' + ''.join(bits) + 'Q', 'dH') for bits in product('01', repeat=n))
        for left, right in product(windows, repeat=2):
            for q, read in pairs:
                word = 'd' + left + codes[q, read] + 'Q' + right + 'z'
                step, = rewrites(word, table)
                neighbour = right if move == 'R' else left
                if neighbour and neighbour not in tape.values():
                    assert 'H' in step
                else:
                    value = next((c for c in alphabet if tape[c] == neighbour), BLANK)
                    target = 's' if q == 't' else 't'
                    write = alphabet[(alphabet.index(read) + 1) % len(alphabet)]
                    next_head = codes[target, value] + 'Q'
                    expected = (left + tape[write] + next_head if move == 'R'
                                else next_head + tape[write] + right)
                    assert step == 'd' + expected + 'z'
                cases += 1
        for n in range(4):
            for bits in product('01', repeat=n):
                suffix = ''.join(bits)
                if suffix not in codewords:
                    step, = rewrites('d' + suffix + 'Qz', table)
                    assert step == 'dHz'
    print(f'Checked {cases} binary-head windows plus all incomplete and invalid state codes.')


def paste(letters):
    return letters[0] if len(letters) == 1 else 'comp[' + ','.join(letters) + ']'


def check_rice(checkout):
    # Generate the typed declaration for each local rule shape. At an interior
    # segment the prefix and suffix bring it to an actual empty-path boundary.
    ctx = ('(x : *) (l : x -> x) (r : x -> x) (birth : id(x) -> l) '
           '(death : r -> id(x)) (leftsym : l -> l) (rightsym : r -> r) '
           '(current : l -> r) (next : l -> r)')
    cases = (
        (['current', 'rightsym'], ['leftsym', 'next'], ['birth'], ['death']),
        (['current', 'death'], ['leftsym', 'next', 'death'], ['birth'], []),
        (['leftsym', 'current'], ['next', 'rightsym'], ['birth'], ['death']),
        (['birth', 'current'], ['birth', 'next', 'rightsym'], [], ['death']),
        (['current'], ['next'], ['birth'], ['death']),
        (['leftsym', 'current'], ['current'], ['birth'], ['death']),
        (['current', 'rightsym'], ['current'], ['birth'], ['death']),
    )
    lines = ['import examples/eh']
    names = []
    for i, (before, after, left, right) in enumerate(cases):
        src, tgt = paste(before), paste(after)
        args = (f'{ctx} (p : {src} -> {tgt}) (q : {tgt} -> {src}) '
                f'(k : comp[p,q] -> id({src})) (j : id({src}) -> comp[p,q])')
        for suffix, start, end, term in (
                ('forward', src, tgt, 'p'), ('back', tgt, src, 'q'),
                ('cancel', 'comp[p,q]', f'id({src})', 'k'),
                ('expand', f'id({src})', 'comp[p,q]', 'j')):
            layers = 2 if suffix in ('cancel', 'expand') else 1

            def whisker(value, depth):
                return paste([*left, '[' * depth + value + ']' * depth, *right])

            name = f'move{i}{suffix}'
            names.append(name)
            # Prefix, suffix and middle are one unbiased composition.
            start_face, end_face = (whisker(v, layers - 1) for v in (start, end))
            lines.append(f'def {name} {args} : {start_face} -> {end_face} = {whisker(term, layers)}')

    component = 'comp[birth,current,death]'
    cross = f'eh(x,{component},{component})'
    unit = f'id(comp[{component},{component}])'
    args = f'{ctx} (repair : {cross} -> {unit})'
    for name, expr in (
            ('leftslide', f'comp[comp[{cross},[repair]],unitor_r({cross})]'),
            ('rightslide', f'comp[comp[[repair],{cross}],unitor_l({cross})]')):
        names.append(name)
        lines.append(f'def {name} {args} : comp[{cross},{cross}] -> {cross} = {expr}')
        for degree in (1, 2):
            poles = '(u : *) (v : *)'
            ty = 'u -> v'
            if degree == 2:
                poles += ' (f : u -> v) (g : u -> v)'
                ty = 'f -> g'
            suspended = args.replace('(x : *)', f'{poles} (x : {ty})', 1)
            shifted_name = f'{name}shift{degree}'
            names.append(shifted_name)
            lines.append(f'def {shifted_name} {suspended} : comp[{cross},{cross}] -> {cross} = {expr}')
    with TemporaryDirectory() as temp:
        directory = Path(temp)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (directory / 'Config.catt').write_text('\n'.join(lines) + '\n')
        accepted(run(checkout / 'target/release/catt_strict', directory, 'Config.catt'),
                 'Config.catt', names)
    print(f'Rice checked {len(names)} raw placements, cancellations, expansions and marked slides.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    args = parser.parse_args()
    check_transitions()
    check_nonhalting_component()
    check_binary_windows()
    check_rice(args.checkout.resolve())
