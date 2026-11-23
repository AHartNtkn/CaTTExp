"""Check fixed-end schedule refinement and suspended directed labels on scalar rules."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_private_ports import Network, subsets


def schedules(net):
    moves = {}
    for cut, batch, _ in net.cubes():
        if batch:
            moves.setdefault(cut, []).append(tuple(sorted(batch)))

    def finish(cut):
        if cut == net.events:
            yield ()
        for batch in moves.get(cut, []):
            for tail in finish(cut.union(batch)):
                yield (batch, *tail)

    return set(finish(frozenset()))


def decorate(schedule, labels):
    return tuple(tuple((event, labels[event]) for event in batch) for batch in schedule)


def neighbours(word, allowed):
    # Work on local batch entries. There is one directed relation ab -> h
    # between parallel paths. The third path c has no comparisons.
    for i, batch in enumerate(word):
        for j, (event, label) in enumerate(batch):
            if label == 'ab':
                yield (*word[:i], (*batch[:j], (event, 'h'), *batch[j+1:]), *word[i+1:])
        for first in subsets(batch):
            if first and len(first) < len(batch):
                second = tuple(entry for entry in batch if entry not in first)
                yield (*word[:i], tuple(sorted(first)), second, *word[i+1:])
        if i + 1 < len(word):
            merged = tuple(sorted(batch + word[i+1]))
            candidate = (*word[:i], merged, *word[i+2:])
            plain = tuple(tuple(event for event, _ in part) for part in candidate)
            if plain in allowed:
                yield candidate


def check_schedules():
    pairs = positive = 0
    for arcs in subsets(combinations(range(3), 2)):
        # A vertex with no incident arc is a rule with two empty ports.
        net = Network(range(3), enumerate(sorted(arcs)))
        plain = schedules(net)
        states = {decorate(schedule, labels): labels for schedule in plain
                  for labels in product(('ab', 'h', 'c'), repeat=3)}
        edges = {word: set(neighbours(word, plain)) for word in states}
        for start, source in states.items():
            reached = {start}
            todo = [start]
            while todo:
                for target in edges[todo.pop()] - reached:
                    reached.add(target)
                    todo.append(target)
            expected = {word for word, target in states.items()
                        if all(a == b or (a, b) == ('ab', 'h') for a, b in zip(source, target))}
            assert expected == reached
            pairs += len(states)
            positive += len(reached)
    return pairs, positive


def check_typed(checkout):
    binary = checkout / 'target/release/catt_strict'
    count = 0
    with TemporaryDirectory() as directory:
        folder = Path(directory)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for rank in (2, 3, 4):
            pole = 'x'
            for _ in range(rank - 1):
                pole = f'id({pole})'
            unit = f'id({pole})'
            for u, v in [(unit, unit), (unit, 'comp[a,b]'), ('comp[a,b]', unit), ('comp[a,b]', 'b')]:
                ctx = (f'(x : *) (a : {pole} -> {pole}) (b : {pole} -> {pole}) '
                       f'(e : {u} -> {v}) (f : {u} -> {v}) (g : {u} -> {v}) '
                       f'(i : e -> f) (j : f -> g) (k : e -> g) (r : comp[i,j] -> k) '
                       f'(s : {v} -> a)')
                args = '(x,a,b,e,f,g,i,j,k,r,s)'
                left, right = 'comp[[comp[i,j]],s]', 'comp[[k],s]'
                (folder / 'Rule.catt').write_text('import examples/eh-common\n'
                    f'def carried {ctx} : {left} -> {right} = comp[[[r]],s]\n'
                    f'def padded {ctx} : comp[{left},id(comp[g,s])] -> {right} '
                    f'= comp[unitor_r({left}),carried{args}]\n')
                accepted(run(binary, folder, 'Rule.catt'), 'Rule.catt', ['carried', 'padded'])
                (folder / 'Class.catt').write_text('import Rule\n'
                    f'def agrees {ctx} : padded{args} -> carried{args} = id(carried{args})\n')
                accepted(run(binary, folder, 'Class.catt', ['--sua']), 'Class.catt', ['agrees'])
                (folder / 'Reverse.catt').write_text('import Rule\n'
                    f'def reversed {ctx} : {right} -> {left} = carried{args}\n')
                rejected(run(binary, folder, 'Reverse.catt', ['--sua']), 'Reverse.catt', 'reversed')
                count += 4
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    pairs, hits = check_schedules()
    print(f'{pairs} schedule pairs checked, {hits} reachable')
    if args.catt_strict:
        print(f'{check_typed(args.catt_strict.resolve())} typed declaration checks')
