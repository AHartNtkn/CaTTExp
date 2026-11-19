"""Execute the asymmetric right-variation laws on the four-slot grounding.

Each check substitutes concrete cells into the native equation or directed
schema, follows its 4-updates and looks up the resulting oriented rule in
the shared graph. The shifted join has a positive t in each spatial input.
"""

from functools import cache

from check_two_moving_native import Evaluator, Route, Value, complete_route
from interchange_bilateral_ground import LETTER, ground_all, native_operand, state_at
from interchange_four_slot_ground import hist
from interchange_reachability import Path, solve, verify
from reachability_theory import Cell, EQUATIONS, OPERATIONS, RULES
from response12_degree_five import EXTRA_RULES


class RightEvaluator(Evaluator):
    @cache
    def apply(self, name, args):
        if name != 't':
            return super().apply(name, args)
        op = OPERATIONS[name]
        env = dict(zip(('x0', 'x1'), args))
        assert tuple(v.dim for v in args) == op.inputs
        assert all(self.read(l, env) == self.read(r, env) for l, r in op.guards)
        source, target = self.read(op.source, env), self.read(op.target, env)
        return Value(4, source, target, Route((source.trace, target.trace), ('t',)))


SCHEMAS = {s.name: s for s in (*EQUATIONS, *RULES, *EXTRA_RULES)}


def projected_paths(graph, faces, prefix='', suffix=''):
    lookup = {}
    for key, edge in graph.edges.items():
        kind = key.rsplit('/', 1)[1].split(':', 1)[0]
        assert (edge.source, edge.target, kind) not in lookup
        lookup[edge.source, edge.target, kind] = key

    def path(route):
        states = [hist(prefix + ''.join(LETTER[e] for e in h.events) + suffix) for h in route.states]
        names = tuple(lookup[a, b, 'i' if k == 'iota' else k]
                      for a, b, k in zip(states, states[1:], route.labels))
        return Path(states[0], names)

    return tuple(map(path, faces))


def check_rule(evaluate, label, args, pair, prefix='', suffix=''):
    schema = SCHEMAS[label]
    assert tuple(v.dim for v in args) == tuple(d for _, d in schema.variables)
    env = {key: v for (key, _), v in zip(schema.variables, args)}
    assert all(evaluate.read(l, env) == evaluate.read(r, env) for l, r in schema.guards)
    faces = [evaluate.read(term, env).trace for term in (schema.left, schema.right)]
    graph = ground_all(*pair)
    source, target = projected_paths(graph, faces, prefix, suffix)
    assert any(step.rule.split()[0] == label and not step.backwards and other == target
               for step, other in graph.successors(source)), label
    return faces


def check_four_t_rectangle(evaluate):
    # The early W crosses x,y and then the late Z crosses x,y. Build the
    # four narrow variations on their own halves with the actual 2-whiskers.
    def piece(earlier, prefix, unary, row, suffix):
        state = state_at(earlier + prefix)
        order = [slot for slot, _ in state]
        lo = order.index(unary.lower())
        assert order[lo+1] == row
        focus = evaluate.apply('t', (native_operand(state, lo+1, lo+2, (0,)),
                                     native_operand(state, lo, lo+1, (1,), unary)))
        if lo:
            focus = evaluate.apply('left2_4', (native_operand(state, 0, lo, (0, 1)), focus))
        if lo + 2 < len(state):
            focus = evaluate.apply('right2_4', (focus, native_operand(state, lo+2, len(state), (0, 1))))
        if prefix:
            pre = native_operand(state_at(earlier), 0, 4, (0, 1), prefix)
            focus = evaluate.apply('left3_4', (pre, focus))
        if suffix:
            end = focus.source.trace.end
            post = native_operand(end, 0, 4, (0, 1), suffix)
            focus = evaluate.apply('right3_4', (focus, post))
        return focus

    args = {'A': piece('', '', 'W', 'x', 'r'), 'B': piece('', 'p', 'W', 'y', ''),
            'C': piece('Wpr', '', 'Z', 'x', 's'), 'D': piece('Wpr', 'q', 'Z', 'y', '')}
    check_rule(evaluate, 'delta', (args['A'], args['D']), 'ZW')
    names = {k: Cell(4, k) for k in args}
    faces = [evaluate.read(complete_route(order, names).term, args).trace
             for order in ('CDAB', 'CADB')]
    graph = ground_all('Z', 'W')
    source, target = projected_paths(graph, faces)
    assert source.start == 'WprZqs' and graph.end(source) == 'prWqsZ'
    assert any(other == target and step.rule.startswith('delta ') and step.offset == 1
               for step, other in graph.successors(source))
    reverse = solve(graph, target, source)
    assert not reverse.reachable and verify(graph, target, source, reverse)
    print(f'Four positive t inputs from WprZqs to prWqsZ, {len(reverse.visited)} reverse-cut paths.')


def check():
    evaluate = RightEvaluator()
    start = state_at('')

    def col(lo, hi, letters=None, prefix=''):
        return native_operand(state_at(prefix), lo, hi, (1,), letters)

    x, y, xy = [native_operand(start, lo, hi, (0,)) for lo, hi in ((2, 3), (3, 4), (2, 4))]
    # Each full 3-history contains both advances. The x-only test cases
    # have a spatial spectator y followed by its fixed two crossings.
    for pair in ('ZZ', 'ZW', 'WZ', 'WW'):
        b = col(0, 2, pair[0])
        bb = col(0, 2, pair[1], prefix=pair[0])
        check_rule(evaluate, '11', (x, b, bb), pair, suffix='rs')
        check_rule(evaluate, '13', (x, y, col(0, 2, pair)), pair)
    check_rule(evaluate, '16', (x, col(0, 1, 'ZZ'), col(1, 2)), 'ZZ', suffix='rs')
    check_rule(evaluate, '17', (x, col(0, 1), col(1, 2, 'WW')), 'WW', suffix='rs')

    variation = evaluate.apply('iota', (col(0, 1, 'Z'), col(1, 2, 'W')))
    check_rule(evaluate, 'U_t', (xy, variation), 'ZW')

    # Immediately after p the spatial intervals zx and wy have their own t.
    # At the end of the comparison the remaining crossing is s.
    mid = state_at('p')

    def local_t(lo, unary):
        row = native_operand(mid, lo+1, lo+2, (0,))
        moving = native_operand(mid, lo, lo+1, (1,), unary)
        return evaluate.apply('t', (row, moving))

    left, right = local_t(0, 'Z'), local_t(2, 'W')
    faces = check_rule(evaluate, 'shifted_join', (left, right), 'ZW', 'p', 's')
    assert tuple(route.labels for route in faces) == (('t', 'iota', 't'), ('t', 't', 'iota'))
    print('Replayed native (11), (13), (16), (17), U_t and the two-positive-input shifted join.')
    check_four_t_rectangle(evaluate)


if __name__ == '__main__':
    check()
