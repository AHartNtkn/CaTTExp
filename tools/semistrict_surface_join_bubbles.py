"""Search a finite 2-computad for a positive empty-to-empty rewrite history.

JSON format: edges map single-character names to pairs of objects, and rules
map names to [start object, input word, output word]. The width bound limits
intermediate edge words. A returned witness is unconditional.
"""
import argparse
from collections import deque
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from semistrict_surface_braid_reflection import end_vertex
from semistrict_surface_bubble_transfer import block_word
from semistrict_surface_first_events import occurrences


def bubble(edges, rules, width, *, roots=None):
    if width < 0 or any(len(edge) != 1 for edge in edges):
        raise ValueError('expected nonnegative width and single-character edges')
    for root, source, target in rules.values():
        if end_vertex(edges, root, source) != end_vertex(edges, root, target):
            raise ValueError('nonparallel rule')
    starts = {v for v, source, _ in rules.values() if not source}
    if roots is not None:
        starts.intersection_update(roots)
    for root in sorted(starts):
        queue = deque([''])
        parent = {'': None}
        while queue:
            path = queue.popleft()
            for name, (vertex, source, target) in rules.items():
                for pos in occurrences(path, source):
                    if end_vertex(edges, root, path[:pos]) != vertex:
                        continue
                    dest = path[:pos] + target + path[pos + len(source):]
                    step = (pos, name)
                    if not dest:
                        trail = [step]
                        while parent[path] is not None:
                            path, previous = parent[path]
                            trail.append(previous)
                        return root, trail[::-1]
                    if len(dest) <= width and dest not in parent:
                        queue.append(dest)
                        parent[dest] = (path, step)
    return None


def guarded_system(rules, source, target):
    # The four special identifiers are private to this test alphabet.
    edges = {edge: ('x', 'x') for edge in 'abLR'}
    guarded = {str(i): ('x', left, right) for i, (left, right) in enumerate(rules)}
    guarded.update(birth=('x', '', 'L' + source + 'R'),
                   death=('x', 'L' + target + 'R', ''))
    return edges, guarded


def check_reductions():
    # Independent finite transitive closure on the two-letter interior words.
    words = [''.join(w) for w in product('ab', repeat=2)]
    tests = positives = 0
    for count in range(4):
        for rules in combinations([('a', 'b'), ('b', 'a'), ('ab', 'ba')], count):
            reach = {(w, w) for w in words}
            for w in words:
                for left, right in rules:
                    for i in range(len(w) - len(left) + 1):
                        if w[i:i + len(left)] == left:
                            reach.add((w, w[:i] + right + w[i + len(left):]))
            for middle in words:
                reach |= {(a, b) for a in words for b in words
                          if (a, middle) in reach and (middle, b) in reach}
            for start, end in product(words, repeat=2):
                edges, guarded = guarded_system(rules, start, end)
                # Width eight permits nested and adjacent pairs of guarded blocks.
                result = bubble(edges, guarded, 8)
                assert bool(result) == ((start, end) in reach)
                if result:
                    root, history = result
                    path = ''
                    for pos, name in history:
                        vertex, left, right = guarded[name]
                        assert path.startswith(left, pos) and end_vertex(edges, root, path[:pos]) == vertex
                        path = path[:pos] + right + path[pos + len(left):]
                    assert not path
                    positives += 1
                    check_swap(len(history))
                tests += 1
    # The source object of an empty left side matters, even with a loop edge.
    assert bubble({'f': ('x', 'x')}, {'b': ('x', '', 'f'), 'd': ('y', '', '')}, 1) == ('y', [(0, 'd')])
    assert bubble({'f': ('x', 'x'), 'g': ('y', 'y')},
                  {'b': ('x', '', 'f'), 'd': ('y', 'g', '')}, 2) is None
    return tests, positives


def check_swap(size):
    order = list(range(2 * size))
    for adjacent in block_word(size, (1,)):
        i = adjacent - 1
        order[i], order[i + 1] = order[i + 1], order[i]
    assert order == list(range(size, 2 * size)) + list(range(size))
    return order


def rice_example(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        temp = Path(folder)
        (temp / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        args = '(x : *) (f : x -> x) (u : id(x) -> f) (d : f -> id(x))'
        b = 'comp[u,d]'
        raw = temp / 'Raw.catt'
        raw.write_text(f'import examples/eh\ndef compositeEH {args} : comp[{b},{b}] -> comp[{b},{b}] = eh(x,{b},{b})\n')
        strict = temp / 'Strict.catt'
        strict.write_text(f'import examples/eh\ndef compositeSwap {args} : eh(x,{b},{b}) -> swap({b},{b}) = id(eh(x,{b},{b}))\n')
        for flags, file, name in [((), raw, 'compositeEH'), (('--su',), strict, 'compositeSwap')]:
            log = subprocess.run([binary, *flags, file], text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, check=True).stdout
            if f'Checking {name}\n' not in log or f'Finished importing {file}' not in log or 'Error:' in log:
                raise ValueError(log[-3500:])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path)
    parser.add_argument('--width', type=int, default=8)
    parser.add_argument('--rice-dir', type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = bubble(data['edges'], data['rules'], args.width)
        if result:
            root, history = result
            print(json.dumps(dict(root=root, history=history, permutation=check_swap(len(history)))))
        else:
            print(f'No positive bubble with intermediate width at most {args.width}')
    else:
        total, positive = check_reductions()
        print(f'{total} guarded reachability comparisons, {positive} positive histories and block swaps')
    if args.rice_dir:
        rice_example(args.rice_dir.resolve())
        print('Rice checked the raw composite diagonal and its strict-unit swap conversion')
