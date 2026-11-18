#!/usr/bin/env python3
"""Checks for fixed-graph inner-factorization completion.

Run beside the unchanged sixth-round triple_tensor_check.py:
    python3 r7_join_closure_check.py

This file verifies actual tensor-generator witnesses and finite history counts.
The source-only termination/confluence theorem is a separate mathematical
argument; finite examples do not substitute for that argument.
"""

from collections import defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache

from triple_tensor_check import apply_repairs, base_edges, tensor_label, vertices


@dataclass(frozen=True)
class Positive:
    root: tuple[str, str, str]
    left: tuple[tuple[str, str, str], ...] = ()
    right: tuple[tuple[str, str, str], ...] = ()

    @property
    def source(self):
        return self.left[-1][1] if self.left else self.root[0]

    @property
    def target(self):
        return self.right[0][0] if self.right else self.root[1]


def endpoints(letter):
    if isinstance(letter, Positive):
        return letter.source, letter.target
    assert letter[2] == "I"
    return letter[:2]


def check_word(word):
    for a, b in zip(word, word[1:]):
        assert endpoints(a)[1] == endpoints(b)[0]


def contraction_steps(word, both=False):
    check_word(word)
    results = set()
    for i, (a, b) in enumerate(zip(word, word[1:])):
        if isinstance(a, Positive) and not isinstance(b, Positive):
            if a.right and a.right[0] == b:
                shortened = Positive(a.root, a.left, a.right[1:])
                results.add(word[:i] + (shortened,) + word[i + 2:])
        if both and not isinstance(a, Positive) and isinstance(b, Positive):
            if b.left and b.left[-1] == a:
                shortened = Positive(b.root, b.left[:-1], b.right)
                results.add(word[:i] + (shortened,) + word[i + 2:])
    for result in results:
        assert len(result) == len(word) - 1
        check_word(result)
    return results


def normal_forms(word, both=False):
    steps = contraction_steps(word, both)
    if not steps:
        return {word}
    return set().union(*(normal_forms(step, both) for step in steps))


def history_records(vs, es, both=False):
    predecessors, successors = defaultdict(list), defaultdict(list)
    for edge in es:
        s, t, kind = edge
        if kind == "I":
            predecessors[t].append(edge)
            successors[s].append(edge)

    @lru_cache(None)
    def paths_ending_at(v):
        return ((),) + tuple(
            path + (edge,)
            for edge in predecessors[v]
            for path in paths_ending_at(edge[0])
        )

    @lru_cache(None)
    def paths_starting_at(v):
        return ((),) + tuple(
            (edge,) + path
            for edge in successors[v]
            for path in paths_starting_at(edge[1])
        )

    records = {
        Positive(root, left, right)
        for root in es if root[2] != "I"
        for left in (paths_starting_at(root[0]) if both else ((),))
        for right in paths_ending_at(root[1])
    }

    # Independent worklist construction; every generator/edge pair is visited
    # once. FIFO and LIFO must produce the same exact record identities.
    for fifo in (False, True):
        seen = {Positive(edge) for edge in es if edge[2] != "I"}
        pending = deque(seen)
        while pending:
            record = pending.popleft() if fifo else pending.pop()
            children = {
                Positive(record.root, record.left, (edge,) + record.right)
                for edge in predecessors[record.target]
            }
            if both:
                children.update(
                    Positive(record.root, record.left + (edge,), record.right)
                    for edge in successors[record.source]
                )
            for child in children - seen:
                seen.add(child)
                pending.append(child)
        assert seen == records

    # Full completed graph remains acyclic in this actual tensor instance.
    outgoing = defaultdict(list)
    indegree = {v: 0 for v in vs}
    for s, t, kind in es:
        if kind == "I":
            outgoing[s].append(t)
            indegree[t] += 1
    for record in records:
        outgoing[record.source].append(record.target)
        indegree[record.target] += 1
    ready = deque(v for v in vs if indegree[v] == 0)
    visited = set()
    while ready:
        v = ready.popleft()
        visited.add(v)
        for t in outgoing[v]:
            indegree[t] -= 1
            if indegree[t] == 0:
                ready.append(t)
    assert visited == vs
    return records


def check_pre_repair_diamond(es):
    x, u, w1, w2, v = (
        "bacrqp", "abpcqr", "abcpqr", "bapcqr", "bacpqr"
    )
    tau = (x, v, "tau")
    p = ((u, w1, "I"), (w1, v, "I"))
    q = ((u, w2, "I"), (w2, v, "I"))
    assert {tau, *p, *q} <= es
    assert tensor_label(tau) == ((1, "+"), (1, "+"), (1, "+"))
    assert not any(t == u and kind == "I" for s, t, kind in es)

    # Distinct reverse-inner histories remain distinct actual join generators.
    hp, hq = Positive(tau, right=p), Positive(tau, right=q)
    assert hp != hq
    assert normal_forms((hp,) + p) == {(Positive(tau),)}
    assert normal_forms((hq,) + q) == {(Positive(tau),)}
    assert normal_forms((hp,) + q) == {(hp,) + q}
    assert normal_forms((hp,) + q) != normal_forms((hp,) + p)
    print("PASS: the pre-repair tensor tau diamond is generator-supported.")
    print("PASS: history joins preserve the two differently whiskered I paths.")
    print("PASS: forward factor expansion has two terminal words in this diamond.")


def check_two_sided_k14_critical_pair(es):
    alpha = ("bapcqr", "bapqcr", "T")
    e = ("abpqcr", "bapqcr", "I")
    beta = ("abpqcr", "abpqrc", "T")
    assert {alpha, e, beta} <= es
    h = Positive(alpha, right=(e,))
    k = Positive(beta, left=(e,))
    word = (h, e, k)
    left_result = (Positive(alpha), k)
    right_result = (h, Positive(beta))
    assert left_result != right_result
    assert contraction_steps(word, both=True) == {left_result, right_result}
    assert normal_forms(word, both=True) == {left_result, right_result}
    print("PASS: two-sided absorption has an actual surviving-K14 critical pair.")
    print("      h ; e ; k reduces to alpha ; k and h ; beta, both irreducible.")


def all_paths(positive_records, inner_edges, source, target):
    outgoing = defaultdict(list)
    for letter in tuple(positive_records) + tuple(inner_edges):
        outgoing[endpoints(letter)[0]].append(letter)
    result = []

    def visit(v, path, visited):
        if v == target:
            result.append(path)
        for edge in outgoing[v]:
            t = endpoints(edge)[1]
            assert t not in visited
            visit(t, path + (edge,), visited | {t})

    visit(source, (), {source})
    return result


def verify_vertex_grading(vs, es):
    """Verify the theorem's stronger rank hypothesis on the actual input."""
    parent = {v: v for v in vs}

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for s, t, kind in es:
        if kind == "I":
            parent[root(s)] = root(t)
    classes = {root(v) for v in vs}
    positive = {(root(s), root(t)) for s, t, kind in es if kind != "I"}
    assert len(classes) == 54 and len(positive) == 116
    assert all(s != t for s, t in positive)
    outgoing = defaultdict(list)
    indegree = {v: 0 for v in classes}
    for s, t in positive:
        outgoing[s].append(t)
        indegree[t] += 1
    rank = {v: 0 for v in classes}
    ready = deque(v for v in classes if indegree[v] == 0)
    visited = set()
    while ready:
        v = ready.popleft()
        visited.add(v)
        for t in outgoing[v]:
            rank[t] = max(rank[t], rank[v] + 1)
            indegree[t] -= 1
            if indegree[t] == 0:
                ready.append(t)
    assert visited == classes
    phi = {v: rank[root(v)] for v in vs}
    assert max(phi.values()) == 7
    assert all(phi[s] == phi[t] if kind == "I" else phi[s] < phi[t]
               for s, t, kind in es)
    return phi


def check_actual_base_functor_failure(k14):
    x, u, w1, w2, v = (
        "bacrqp", "abpcqr", "abcpqr", "bapcqr", "bacpqr"
    )
    tau = (x, v, "tau")
    a = (x, w2, "h_z")
    p1, e = (u, w1, "I"), (w1, v, "I")
    q1, c = (u, w2, "I"), (w2, v, "I")
    inner = {p1, e, q1, c}
    local_vertices = {x, u, w1, w2, v}
    source_edges = inner | {tau}
    target_edges = inner | {a}
    assert target_edges <= k14
    assert e != c

    # This is an actual finite comparison-category functor: all inner arrows
    # are fixed, and the source tau is sent to the K14 path h_z ; c.
    source_records = history_records(local_vertices, source_edges)
    target_records = history_records(local_vertices, target_edges)
    assert len(source_records) == 5 and len(target_records) == 2
    domain_h = Positive(tau, right=(e,))
    assert domain_h in source_records
    assert normal_forms((domain_h, e)) == {(Positive(tau),)}
    image_tau = (Positive(a), c)
    assert normal_forms(image_tau) == {image_tau}

    candidates = all_paths(target_records, inner, x, w1)
    assert candidates == [(Positive(a, right=(q1,)), p1)]
    assert all(normal_forms(h + (e,)) != {image_tau} for h in candidates)

    # In the full K14 completion, contraction preserves the ordered sequence
    # of positive-root generator IDs. Any possible lift of domain_h must
    # therefore use root h_z exactly once and no other positive root.
    full_records = history_records(vertices("abc"), k14)
    full_inner = {edge for edge in k14 if edge[2] == "I"}
    a_records = {record for record in full_records if record.root == a}
    full_candidates = all_paths(a_records, full_inner, x, w1)
    assert full_candidates == candidates
    assert all(normal_forms(h + (e,)) != {image_tau}
               for h in full_candidates)
    print("PASS: actual five-vertex base functor tau -> h_z ; c has no lift")
    print("      between the source-only history completions.")
    print("      Exactly one candidate H exists; NF(H ; e) != NF(h_z ; c).")
    print("PASS: the positive-root invariant gives the same failure for full K14.")


def main():
    vs = vertices("abc")
    original = base_edges(vs)
    repaired, _ = apply_repairs(vs, original, True)
    assert len(vs) == 240 and len(original) == len(repaired) == 504
    check_pre_repair_diamond(original)
    check_two_sided_k14_critical_pair(repaired)
    check_actual_base_functor_failure(repaired)
    expected = {
        ("original", False): 994,
        ("original", True): 2458,
        ("K14", False): 877,
        ("K14", True): 2203,
    }
    for name, es in (("original", original), ("K14", repaired)):
        verify_vertex_grading(vs, es)
        print(f"PASS: {name}: 54 inner classes, 116 distinct positive endpoint pairs, rank 0..7.")
        for both in (False, True):
            records = history_records(vs, es, both)
            assert len(records) == expected[name, both]
            side = "two-sided" if both else "source-only"
            print(f"PASS: {name} {side}: {len(records)} positive records; "
                  "FIFO=LIFO; completed quiver is acyclic.")
            if name == "K14" and not both:
                seeds = sum(kind != "I" for _, _, kind in es)
                inner_count = sum(kind == "I" for _, _, kind in es)
                assert (seeds, len(records) - seeds,
                        len(records) + inner_count) == (264, 613, 1117)
                print("      264 seed arrows; 613 new joins; 1117 total arrows.")


if __name__ == "__main__":
    main()
