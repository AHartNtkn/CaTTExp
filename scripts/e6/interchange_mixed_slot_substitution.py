"""Check the globular substitutions from the exceptional H_R cuts to five factors.

Each unary 3-generator may be replaced along with its two 2-faces by the
crossing of two consecutive new 2-slots and its actual boundary words.
The three early factors carry cde; the late varying event is ab.
"""
from itertools import product

from interchange_free import tree_generators
from interchange_right_witness import RightEvaluator
from interchange_sorting_fiber import native_generators, native_triangle


def substitution(parts, evaluate, target):
    source_tree = [[[]] if len(p) == 1 else [[[]]] for p in parts]
    data, _ = tree_generators(source_tree)
    images, top = {}, []
    for i, part in enumerate(parts):
        cells = [target[f"{'abcde'.index(s)}/0/0"] for s in part]
        cell = cells[0] if len(cells) == 1 else evaluate.apply('chi', tuple(cells))
        top.append(cell)
        first = cell.source if cell.dim == 3 else cell
        images.update({f'{i}/0': first.source, f'{i}/1': first.target,
                       f'{i}/0/0': first})
        if cell.dim == 3:
            images[f'{i}/0/1'] = cell.target
            images[f'{i}/0/0/0'] = cell
    for i in range(len(parts) + 1):
        images[str(i)] = target[str(sum(map(len, parts[:i])))]
    assert images.keys() == data.keys()
    for name, (degree, bounds) in data.items():
        value = images[name]
        assert value.dim == degree
        if bounds:
            assert (value.source, value.target) == tuple(images[b] for b in bounds)
    return top


def check():
    evaluate, target = RightEvaluator(), native_generators('abcde')
    count = 0
    for left, right in product((('a', 'b'), ('ab',)),
                               (('c', 'd', 'e'), ('cd', 'e'), ('c', 'de'))):
        top = substitution(left + right, evaluate, target)
        left_cells, right_cells = top[:len(left)], top[len(left):]
        varied = left_cells[0] if len(left) == 1 else evaluate.apply('chi', tuple(left_cells))
        early = list(right_cells)
        if len(early) == 3:
            early = [evaluate.apply('chi', tuple(early[:2])), early[2]]
        mark = evaluate.apply('r' if early[0].dim == 3 else 't', tuple(early))
        raw = [tuple(b+a for a,b in h.events) for h in mark.trace.states]
        assert native_triangle('edc', *raw)
        for part, cell in zip(right, right_cells):
            # A right slot carrying an early unary is at its target 2-face
            # when the late mark acts. Fill any intervening outer factors.
            stationary = cell.target if cell.dim == 3 else cell
            for j in reversed(range(2, 'abcde'.index(part[0]))):
                stationary = evaluate.apply('left1_2', (target[f'{j}/1'], stationary))
            late = evaluate.apply('r', (varied, stationary))
            before, after = late.trace.states
            assert varied.trace.events == (('b', 'a'),)
            assert before.events[-1] == after.events[0] == ('b', 'a')
            for s in part:
                required = {(s,'a'), (s,'b')}
                assert required <= set(before.events[:-1]) and required <= set(after.events[1:])
            count += 1
    print(f'Six globular substitutions, {count} placements of the common slot; '
          'all early triangle and late variation faces checked.')


if __name__ == '__main__':
    check()
