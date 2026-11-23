"""Check occurrence recovery and configuration probes for overlapping scalar rules."""
from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import combinations, permutations
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_forest_expansion import graph, substitute


@dataclass(frozen=True)
class Rule:
    name: str
    inputs: str
    outputs: str


@dataclass(frozen=True)
class Port:
    colour: str
    index: int
    # Every output records the whole event, including its ordered inputs.
    event: tuple | None = None


def outputs(rule, inputs):
    return tuple(Port(c, i, (rule, inputs)) for i, c in enumerate(rule.outputs))


def recover(ports):
    stages = []
    while ports[0].event is not None:
        rule, inputs = ports[0].event
        assert len(ports) == len(rule.outputs)
        assert set(ports) == set(outputs(rule, inputs))
        stages.append((rule, inputs))
        ports = inputs
    return list(reversed(stages))


def check_probe(layers, j):
    names = tuple(range(len(layers[j])))
    for i, layer in enumerate(layers):
        # Each copied colour in the distinguished layer expands to one name.
        # In the other layers a single port carries all of them.
        blocks = ([graph([k], 0) for k in names] if i == j
                  else [graph(names, 0)] + [graph([], 0)] * (len(layer)-1))
        for order in permutations(range(len(layer))):
            for level in (0, 1):
                projected = substitute(graph(order, level), dict(enumerate(blocks)))
                expected = graph(order, level) if i == j else graph(names, 0)
                assert projected == expected


def check_histories():
    # a has weight three and b weight two. Both aa and bbb have weight six.
    rules = (Rule('f', 'aa', 'bbb'), Rule('g', 'bbb', 'aa'), Rule('h', 'aa', 'aa'))
    initial = tuple(Port('a', i) for i in range(2))
    frontier = [((), [initial])]
    seen = set()
    probes = histories = 0
    for _ in range(4):
        following = []
        for story, layers in frontier:
            for rule in rules:
                for inputs in permutations(layers[-1]):
                    if ''.join(p.colour for p in inputs) != rule.inputs:
                        continue
                    result = outputs(rule, inputs)
                    extended = story + ((rule, inputs),)
                    assert recover(result[::-1]) == list(extended)
                    # Testing injectivity includes different uses of the same rule.
                    assert result not in seen
                    seen.add(result)
                    new_layers = layers + [result]
                    for j in range(len(new_layers)):
                        check_probe(new_layers, j)
                        probes += 1
                    following.append((extended, new_layers))
                    histories += 1
        frontier = following
    return histories, probes


def recover_with_spectators(initial, final):
    # Each chronological predecessor feeds the next event. Read the DAG in
    # depth order and replay it with the actual ordered ports.
    depth = {p: 0 for p in initial}
    events = {}

    def visit(port):
        if port not in depth:
            rule, inputs = port.event
            d = 1 + max(visit(i) for i in inputs)
            assert events.setdefault(d, port.event) == port.event
            depth.update(dict.fromkeys(outputs(rule, inputs), d))
        return depth[port]

    for port in final:
        visit(port)
    live = set(initial)
    story = []
    for _, (rule, inputs) in sorted(events.items()):
        assert set(inputs) <= live
        live.difference_update(inputs)
        live.update(outputs(rule, inputs))
        story.append((rule, inputs))
    assert live == set(final)
    return tuple(story)


def check_spectators():
    rules = (Rule('f', 'aa', 'bbb'), Rule('g', 'bbb', 'aa'))
    initial = tuple(Port(c, i) for i, c in enumerate('aab'))
    frontier = [((), initial)]
    total = 0
    for _ in range(3):
        following = []
        for story, live in frontier:
            for rule in rules:
                for ports in permutations(live, len(rule.inputs)):
                    if ''.join(p.colour for p in ports) != rule.inputs:
                        continue
                    remaining = tuple(p for p in live if p not in ports)
                    assert len(remaining) == 1
                    result = remaining + outputs(rule, ports)
                    step = story + ((rule, ports),)
                    assert recover_with_spectators(initial, result[::-1]) == step
                    following.append((step, result))
                    total += 1
        frontier = following
    return total


def check_pair_coordinates():
    # Work in even scalar rank, so transposing an ordered pair has degree +1.
    # A block substitution takes a pair sphere to the sum of the spheres
    # between the two sets of substituted names.
    from sympy import Matrix, zeros

    def action(domain, codomain, blocks):
        src = list(combinations(sorted(domain), 2))
        tgt = list(combinations(sorted(codomain), 2))
        return Matrix(len(tgt), len(src), lambda i, j: int(any(
            {x, y} == set(tgt[i]) for x in blocks[src[j][0]] for y in blocks[src[j][1]])))

    ports = [({0, 1}, {3, 4, 5}), ({2, 3, 4}, {6, 7}), ({5, 6, 7}, {8, 9})]
    layers = [{0, 1, 2}]
    edges, forward, backward = [], [], []
    for consumed, created in ports:
        old = layers[-1]
        kept = old - consumed
        new = kept | created
        site = kept | {-1}
        before = {p: {p} for p in kept}
        a = action(site, old, before | {-1: consumed})
        b = action(site, new, before | {-1: created})
        def retain(group):
            return before | {p: ({-1} if p == min(group) else set()) for p in group}
        ra = action(old, site, retain(consumed))
        rb = action(new, site, retain(created))
        assert ra*a == rb*b == Matrix.eye(a.cols)
        edges.append((a, b))
        forward.append(b*ra)
        backward.append(a*rb)
        layers.append(new)

    sizes = [len(list(combinations(s, 2))) for s in layers]
    rows = []
    for j, size in enumerate(sizes):
        blocks = [Matrix.eye(size)]
        for i in reversed(range(j)):
            blocks.insert(0, blocks[0]*forward[i])
        for i in range(j, len(edges)):
            blocks.append(blocks[-1]*backward[i])
        rows.append(Matrix.hstack(*blocks))
    probes = Matrix.vstack(*rows)
    cols = []
    for i, (a, b) in enumerate(edges):
        blocks = [zeros(s, a.cols) for s in sizes]
        blocks[i:i+2] = [a, -b]
        cols.append(Matrix.vstack(*blocks))
    incidence = Matrix.hstack(*cols)
    assert (probes*incidence).is_zero_matrix
    assert incidence.rank() == incidence.cols == probes.cols-probes.rank()
    return probes.cols, incidence.rank(), probes.rank()


def check_jump_profiles():
    # Enumerate multisets with two colours, two rules and three possible
    # jump indices per rule. In weight twelve two different jumps first fit.
    from itertools import combinations_with_replacement

    weights = (3, 2) + (6,)*6
    single = double = 0
    for arity in range(7):
        for profile in combinations_with_replacement(range(len(weights)), arity):
            weight = sum(weights[p] for p in profile)
            jumps = [p for p in profile if p >= 2]
            if weight < 12:
                assert len(jumps) <= 1
                single += bool(jumps)
            elif weight == 12 and len(jumps) == 2:
                double += 1
    assert double == 21
    return single, double


def check_typing(checkout):
    exe = checkout / 'target/release/catt_strict'
    ctx = ('(x : *) (a : id(id(x)) -> id(id(x))) (b : id(id(x)) -> id(id(x)))'
           ' (f : comp[a,a] -> comp[b,b,b]) (g : comp[b,b,b] -> comp[a,a])')
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        tests = {
            'Raw': f"""def reassoc = coh [ x{{u}}y{{v}}z{{w}}t : comp[comp[u,v],w] -> comp[u,comp[v,w]] ]
def fitted {ctx} : comp[comp[f,g],f] -> comp[f,comp[g,f]] = reassoc(f,g,f)
""",
            'Surface': f'def converted {ctx} : comp[comp[f,g],f] -> comp[f,comp[g,f]] = id(comp[f,comp[g,f]])\n',
            'Other': f'def wrong {ctx} : f -> comp[f,comp[g,f]] = id(f)\n',
        }
        for name, body in tests.items():
            file = name + '.catt'
            (folder / file).write_text(body)
            raw = run(exe, folder, file)
            sua = run(exe, folder, file, ['--sua'])
            if name == 'Raw':
                accepted(raw, file, ['fitted'])
                accepted(sua, file, ['fitted'])
            elif name == 'Surface':
                rejected(raw, file, 'converted')
                accepted(sua, file, ['converted'])
            else:
                rejected(raw, file, 'wrong')
                rejected(sua, file, 'wrong')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Recovered histories and tested layer probes:', *check_histories())
    print('Histories with a spectator:', check_spectators())
    print('Pair coordinates, incidence rank and probe rank:', *check_pair_coordinates())
    print('One-jump profiles below twelve and two-jump profiles at twelve:', *check_jump_profiles())
    if args.catt_strict:
        check_typing(args.catt_strict.resolve())
        print('Checked a literal degree-five comparison over repeated two-to-three and three-to-two rules.')
