"""Exact directed reachability on a finite, grounded degree-four path presentation.

Ground rules contain the lower whiskers. This module supplies every chronological
prefix and suffix at run time. The weight of each equation is preserved and a
directed rule can only lower it. No path-length or search-depth option is needed.
"""
import argparse
import json
from collections import defaultdict, deque
from dataclasses import asdict, dataclass
from pathlib import Path as FilePath


@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    weight: int


@dataclass(frozen=True, order=True)
class Path:
    start: str
    edges: tuple[str, ...]


@dataclass(frozen=True)
class Rule:
    name: str
    source: Path
    target: Path
    equation: bool = False


@dataclass(frozen=True)
class Step:
    rule: str
    offset: int
    backwards: bool


@dataclass(frozen=True)
class Certificate:
    reachable: bool
    visited: tuple[Path, ...]
    steps: tuple[Step, ...]


class Presentation:
    def __init__(self, vertices, edges, rules):
        self.vertices = frozenset(vertices)
        self.edges = dict(edges)
        self.rules = {}
        self.matches = defaultdict(list)
        for name, edge in self.edges.items():
            if edge.source not in self.vertices or edge.target not in self.vertices:
                raise ValueError(f'{name} has an unknown endpoint')
            if type(edge.weight) is not int or edge.weight <= 0:
                raise ValueError(f'{name} requires a positive integer weight')
        for rule in rules:
            if type(rule.equation) is not bool:
                raise ValueError(f'{rule.name} requires a boolean equation flag')
            if rule.name in self.rules:
                raise ValueError(f'duplicate rule {rule.name}')
            self.parallel(rule.source, rule.target)
            drop = self.weight(rule.source) - self.weight(rule.target)
            if drop < 0 or (rule.equation and drop != 0):
                raise ValueError(f'{rule.name} violates the grading')
            self.rules[rule.name] = rule
            if rule.source == rule.target:
                continue
            self.index(rule.name, False, rule.source, rule.target)
            if rule.equation:
                self.index(rule.name, True, rule.target, rule.source)

    def index(self, name, backwards, lhs, rhs):
        # A nontrivial rule must consume a positive edge, by the grading.
        self.matches[lhs.edges[0]].append((name, backwards, lhs.edges, rhs.edges))

    def end(self, path):
        vertex = path.start
        if vertex not in self.vertices:
            raise ValueError(f'unknown path source {vertex}')
        for name in path.edges:
            if name not in self.edges or self.edges[name].source != vertex:
                raise ValueError(f'edge {name} is not defined at {vertex}')
            vertex = self.edges[name].target
        return vertex

    def parallel(self, source, target):
        if self.end(source) != self.end(target) or source.start != target.start:
            raise ValueError('the two paths are not parallel')

    def weight(self, path):
        return sum(self.edges[e].weight for e in path.edges)

    def successors(self, path):
        for offset, edge in enumerate(path.edges):
            for name, backwards, lhs, rhs in self.matches.get(edge, ()):
                end = offset + len(lhs)
                if path.edges[offset:end] == lhs:
                    result = Path(path.start, path.edges[:offset] + rhs + path.edges[end:])
                    yield Step(name, offset, backwards), result


def solve(presentation, source, target):
    """Return a derivation, or a set closed under all moves still able to reach target."""
    presentation.parallel(source, target)
    floor = presentation.weight(target)
    queue = deque([source])
    parents = {source: None}
    while queue:
        current = queue.popleft()
        if current == target:
            trace = []
            while parents[current] is not None:
                current, step = parents[current]
                trace.append(step)
            return Certificate(True, (), tuple(reversed(trace)))
        for step, other in presentation.successors(current):
            if other not in parents and presentation.weight(other) >= floor:
                parents[other] = current, step
                queue.append(other)
    return Certificate(False, tuple(sorted(parents)), ())


def verify(presentation, source, target, certificate):
    """Check the trace or verify closure of the supplied cut, without rerunning BFS."""
    presentation.parallel(source, target)
    if type(certificate.reachable) is not bool:
        return False
    if certificate.reachable:
        if certificate.visited:
            return False
        current = source
        for step in certificate.steps:
            if type(step.offset) is not int or type(step.backwards) is not bool:
                return False
            rule = presentation.rules.get(step.rule)
            if rule is None or step.backwards and not rule.equation:
                return False
            lhs, rhs = (rule.target, rule.source) if step.backwards else (rule.source, rule.target)
            offset = step.offset
            if offset < 0 or offset > len(current.edges):
                return False
            if presentation.end(Path(current.start, current.edges[:offset])) != lhs.start:
                return False
            end = offset + len(lhs.edges)
            if current.edges[offset:end] != lhs.edges:
                return False
            current = Path(current.start, current.edges[:offset] + rhs.edges + current.edges[end:])
        return current == target

    if certificate.steps:
        return False
    cut = set(certificate.visited)
    if source not in cut or target in cut:
        return False
    floor = presentation.weight(target)
    for path in cut:
        presentation.parallel(source, path)
        for _, other in presentation.successors(path):
            if presentation.weight(other) >= floor and other not in cut:
                return False
    return True


def read_path(data):
    return Path(data['start'], tuple(data['edges']))


def read_ground(data):
    edges = {name: Edge(**edge) for name, edge in data['edges'].items()}
    rules = [Rule(r['name'], read_path(r['source']), read_path(r['target']),
                  r.get('equation', False)) for r in data['rules']]
    return Presentation(data['vertices'], edges, rules), read_path(data['source']), read_path(data['target'])


def query_cli(load_query, description):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('query', type=FilePath, help='path to the JSON query')
    output = parser.add_mutually_exclusive_group()
    output.add_argument('--certificate', type=FilePath, help='write a replayable certificate')
    output.add_argument('--verify', type=FilePath, help='verify a saved certificate')
    args = parser.parse_args()
    presentation, source, target = load_query(json.loads(args.query.read_text()))
    if args.verify:
        data = json.loads(args.verify.read_text())
        cert = Certificate(data['reachable'], tuple(map(read_path, data['visited'])),
                           tuple(Step(**s) for s in data['steps']))
    else:
        cert = solve(presentation, source, target)
    if not verify(presentation, source, target, cert):
        raise SystemExit('invalid certificate')
    if args.certificate:
        args.certificate.write_text(json.dumps(asdict(cert), indent=2) + '\n')
    print('reachable' if cert.reachable else 'unreachable',
          f'({len(cert.steps)} derivation steps)' if cert.reachable
          else f'({len(cert.visited)} states in the closed cut)')


if __name__ == '__main__':
    query_cli(read_ground, __doc__)
