#!/usr/bin/env python3
"""Exhaust strict middle 2-cells by backwards rewriting and match globular 3-rules.

Words are in right-to-left composition order. A rule stores its source object
as well as both words, so nullary applications at different vertices are distinct.
backwards() terminates under the fibre termination hypothesis of Response 8.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Rule:
    vertex: str
    source: str
    target: str


class Stage:
    def __init__(self, arrows, rules):
        self.arrows = arrows
        self.rules = rules
        for rule in rules.values():
            assert self.cuts(rule.vertex, rule.source)[0] == self.cuts(rule.vertex, rule.target)[0]

    def cuts(self, vertex, word):
        vertices = [vertex]
        for letter in reversed(word):
            src, tgt = self.arrows[letter]
            if src != vertices[-1]:
                raise ValueError(f"ill-typed word {word!r} from {vertex}")
            vertices.append(tgt)
        return tuple(reversed(vertices))

    def sites(self, vertex, word, pattern, pole):
        cuts = self.cuts(vertex, word)
        for i in range(len(word) - len(pattern) + 1):
            if word.startswith(pattern, i) and cuts[i + len(pattern)] == pole:
                yield i

    def slices(self, vertex, word, path):
        yield word
        for name, i in path:
            rule = self.rules[name]
            if i not in self.sites(vertex, word, rule.source, rule.vertex):
                raise ValueError(f"{name}@{i} does not apply to {word!r}")
            word = word[:i] + rule.target + word[i + len(rule.source):]
            yield word

    def backwards(self, vertex, source, target, objects, budget, object_site=None):
        return (path for word, path in self.ending_at(vertex, target, objects, budget, object_site)
                if word == source)

    def ending_at(self, vertex, target, objects, budget, object_site=None):
        """Yield (initial word, writing) for every allowed source at a specified target."""
        stack = [(target, budget, ())]
        while stack:
            word, remaining, path = stack.pop()
            if remaining == 0:
                yield word, path
            for name, rule in self.rules.items():
                cost = int(name in objects)
                if cost > remaining:
                    continue
                for i in self.sites(vertex, word, rule.target, rule.vertex):
                    if cost and object_site is not None and not object_site(remaining, name, word, i):
                        continue
                    prev = word[:i] + rule.source + word[i + len(rule.target):]
                    stack.append((prev, remaining - cost, ((name, i),) + path))

    def exchanges(self, path):
        for k, ((a, i), (b, j)) in enumerate(zip(path, path[1:])):
            first, second = self.rules[a], self.rules[b]
            # Both disjoint placements can occur at coincident empty windows.
            if j + len(second.source) <= i:
                pair = ((b, j), (a, i + len(second.target) - len(second.source)))
                yield path[:k] + pair + path[k + 2:]
            if j >= i + len(first.target):
                pair = ((b, j + len(first.source) - len(first.target)), (a, i))
                yield path[:k] + pair + path[k + 2:]

    def quotient(self, paths):
        todo = set(paths)
        cells, index = [], {}
        for p in sorted(todo):
            if p in index:
                continue
            idx = len(cells)
            stack, members = [p], []
            index[p] = idx
            while stack:
                q = stack.pop()
                members.append(q)
                for r in self.exchanges(q):
                    if r not in todo:
                        raise ValueError("path set not closed under interchange")
                    if r not in index:
                        stack.append(r)
                        index[r] = idx
            cells.append(members)
        return cells, index

    def edges(self, vertex, start, cells, index, prisms):
        for pole, word, src, tgt in prisms.values():
            assert tuple(self.slices(pole, word, src))[-1] == tuple(self.slices(pole, word, tgt))[-1]
        edges = set()
        for ci, paths in enumerate(cells):
            for p in paths:
                for k, word in enumerate(self.slices(vertex, start, p)):
                    for name, (pole, base, src, tgt) in prisms.items():
                        for i in self.sites(vertex, word, base, pole):
                            before = tuple((g, j + i) for g, j in src)
                            if p[k:k + len(src)] != before:
                                continue
                            after = tuple((g, j + i) for g, j in tgt)
                            q = p[:k] + after + p[k + len(src):]
                            if q in index:
                                edges.add((ci, name, index[q]))
        return edges
