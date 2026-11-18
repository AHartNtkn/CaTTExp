#!/usr/bin/env python3
"""Finite check of the stated sequential presentation of D2 x D2 x D2.

Conventions: initial one-path is z y x; p swaps y x, q swaps z x,
r swaps z y. Updates a,b,c change the x,y,z one-cell respectively.
An inner interchange moves a right event followed by a disjoint left
event to left then right. The tensor cube is r q p -> p q r.

This checks this exact word presentation. It does not assert that every
syntax of a less specified weak-interchange theory has this normal form.
"""

from collections import Counter, defaultdict, deque
from itertools import combinations, permutations


UPDATES = {"a": 0, "b": 1, "c": 2}
CROSSES = {"p": (0, 1), "q": (0, 2), "r": (1, 2)}

# lhs -> middle is new; lhs -> rhs = (lhs -> middle);(middle -> rhs).
# The final factor is an existing inner interchange.
REPAIRS = (
    ("bpa", "abp", "bap", "h_p", "T"),
    ("cqa", "acq", "caq", "h_q", "T"),
    ("crb", "bcr", "cbr", "h_r", "T"),
    ("rqa", "arq", "raq", "lambda_x", "T"),
    ("crqp", "pcqr", "cpqr", "h_z", "tau"),
    ("crqa", "acrq", "carq", "mu", "lambda_x"),
)


def vertices(update_letters):
    return {
        "".join(w)
        for w in permutations(tuple(update_letters) + tuple(CROSSES))
        if "".join(x for x in w if x in CROSSES) in ("pqr", "rqp")
    }


def base_edges(vs):
    es = set()
    for w in vs:
        wires = [2, 1, 0]
        for j, x in enumerate(w[:-1]):
            y = w[j + 1]
            target = w[:j] + y + x + w[j + 2 :]
            allowed = False
            kind = None
            if target in vs:
                if x in UPDATES and y in UPDATES:
                    allowed = wires.index(UPDATES[x]) > wires.index(UPDATES[y])
                    kind = "I"
                elif x in UPDATES and y in CROSSES:
                    i = UPDATES[x]
                    if i in CROSSES[y]:
                        allowed = i == max(CROSSES[y])
                        kind = "T"
                    else:
                        allowed = wires.index(i) > min(
                            wires.index(k) for k in CROSSES[y]
                        )
                        kind = "I"
                elif x in CROSSES and y in UPDATES:
                    i = UPDATES[y]
                    if i in CROSSES[x]:
                        allowed = i == min(CROSSES[x])
                        kind = "T"
                    else:
                        allowed = min(
                            wires.index(k) for k in CROSSES[x]
                        ) > wires.index(i)
                        kind = "I"
                if allowed:
                    es.add((w, target, kind))
            if x in CROSSES:
                i, k = CROSSES[x]
                ii, kk = wires.index(i), wires.index(k)
                assert abs(ii - kk) == 1
                assert wires[min(ii, kk)] == max(i, k)
                wires[ii], wires[kk] = wires[kk], wires[ii]
        if "rqp" in w:
            es.add((w, w.replace("rqp", "pqr"), "tau"))
    return es


def apply_repairs(vs, original_edges, include_mu):
    all_edges = set(original_edges)
    eliminated = set()
    relations = []
    for lhs, middle, rhs, name, old_name in REPAIRS:
        if name == "mu" and not include_mu:
            continue
        for w in vs:
            if lhs not in w:
                continue
            m = w.replace(lhs, middle)
            t = w.replace(lhs, rhs)
            if m not in vs:
                continue
            old = (w, t, old_name)
            new = (w, m, name)
            inner = (m, t, "I")
            assert old in all_edges, (name, old)
            assert inner in all_edges, (name, inner)
            assert old not in eliminated
            eliminated.add(old)
            all_edges.add(new)
            relations.append((old, new, inner))
    return all_edges - eliminated, relations


def graph_data(vs, edges):
    outgoing = defaultdict(list)
    indegree = {v: 0 for v in vs}
    for s, t, name in edges:
        outgoing[s].append((t, name))
        indegree[t] += 1
    sources = sorted(v for v in vs if not indegree[v])
    sinks = sorted(v for v in vs if not outgoing[v])
    queue = list(sources)
    seen = 0
    while queue:
        s = queue.pop()
        seen += 1
        for t, _ in outgoing[s]:
            indegree[t] -= 1
            if not indegree[t]:
                queue.append(t)
    return sources, sinks, seen == len(vs)


def find_path(edges, source, target):
    outgoing = defaultdict(list)
    for s, t, name in edges:
        outgoing[s].append((t, name))
    queue = deque([source])
    previous = {source: None}
    while queue:
        s = queue.popleft()
        if s == target:
            route = []
            while previous[s] is not None:
                p, name = previous[s]
                route.append((p, name, s))
                s = p
            return list(reversed(route))
        for t, name in outgoing[s]:
            if t not in previous:
                previous[t] = (s, name)
                queue.append(t)
    return None


def tensor_label(edge):
    """Return the actual three-dimensional tensor basis label of T/tau."""
    s, t, kind = edge
    if kind == "I":
        return None
    assert kind in ("T", "tau")
    j = next(i for i, (x, y) in enumerate(zip(s, t)) if x != y)
    states = {i: "-" for i in range(3)}
    wires = [2, 1, 0]
    for x in s[:j]:
        if x in UPDATES:
            states[UPDATES[x]] = "+"
        else:
            i, k = CROSSES[x]
            ii, kk = wires.index(i), wires.index(k)
            wires[ii], wires[kk] = wires[kk], wires[ii]
    if kind == "tau":
        return tuple((1, states[i]) for i in range(3))
    x, y = s[j : j + 2]
    update = x if x in UPDATES else y
    cross = x if x in CROSSES else y
    i = UPDATES[update]
    k = next(k for k in CROSSES[cross] if k != i)
    spectator = next(k for k in range(3) if k not in CROSSES[cross])
    sign = "+" if wires.index(spectator) < wires.index(i) else "-"
    label = [(0, sign)] * 3
    label[i] = (2, "")
    label[k] = (1, states[k])
    return tuple(label)


def differential(label):
    result = Counter()
    prefix_degree = 0
    for i, (degree, sign) in enumerate(label):
        if degree:
            for endpoint, endpoint_sign in (("+", 1), ("-", -1)):
                face = list(label)
                face[i] = (degree - 1, endpoint)
                result[tuple(face)] += (-1) ** prefix_degree * endpoint_sign
        prefix_degree += degree
    return result


def route_edges(route, edges):
    result = []
    for s, t in zip(route, route[1:]):
        matches = [edge for edge in edges if edge[:2] == (s, t)]
        assert len(matches) == 1, (s, t, matches)
        result.append(matches[0])
    return result


def verify_octagons():
    # Positive fragments omit the newly joined step and all inner edges.
    data = {
        "a": (
            ["rqpa", "pqra", "pqar", "paqr", "apqr"],
            [["rqpa", "rqap", "raqp"], ["arqp", "apqr"]],
            ((2, ""), (1, "-"), (1, "-")),
        ),
        "b": (
            ["rqbp", "rbqp", "brqp", "bpqr", "pbqr", "pqbr"],
            [["rqbp", "rqpb", "pqrb", "pqbr"]],
            ((1, "-"), (2, ""), (1, "-")),
        ),
        "c": (
            ["crqp", "rcqp", "rqcp", "rqpc", "pqrc"],
            [["crqp", "cpqr"], ["pcqr", "pqcr", "pqrc"]],
            ((1, "-"), (1, "-"), (2, "")),
        ),
    }
    for update, (negative, positive, label) in data.items():
        es = base_edges(vertices(update))
        boundary = Counter()
        for edge in route_edges(negative, es):
            atom = tensor_label(edge)
            if atom is not None:
                boundary[atom] -= 1
        for route in positive:
            for edge in route_edges(route, es):
                atom = tensor_label(edge)
                if atom is not None:
                    boundary[atom] += 1
        assert dict(boundary) == dict(differential(label)), (
            update, boundary, differential(label)
        )


def verify_independent_update():
    """The actual 24-path interval with an independent third update D."""
    vs = {"".join(w) for w in permutations("ABCD")}

    def edges(flip):
        es = set()
        for w in vs:
            for i in range(3):
                pair = w[i:i + 2]
                ordinary = pair in ("BC", "CA") or pair[0] == "D"
                ab = pair == "BA"
                if flip:
                    ab = (pair == "AB" and w.index("C") > i + 1) or (
                        pair == "BA" and w.index("C") < i
                    )
                if ordinary or ab:
                    es.add((w, w[:i] + pair[::-1] + w[i + 2:], "face"))
        return es

    baseline, flipped = edges(False), edges(True)
    assert len(vs) == 24 and len(baseline) == len(flipped) == 36
    assert graph_data(vs, baseline)[:2] == (["DBCA"], ["ACBD"])
    assert graph_data(vs, flipped)[:2] == (
        ["DABC", "DBCA"], ["ACBD", "BACD"]
    )
    changes = {}
    for e in baseline - flipped:
        trial = (baseline - {e}) | {(e[1], e[0], e[2])}
        sources, sinks, acyclic = graph_data(vs, trial)
        assert acyclic
        changes[e[:2]] = (len(sources) - 1, len(sinks) - 1)
    assert changes == {
        ("BACD", "ABCD"): (0, 1),
        ("BADC", "ABDC"): (0, 0),
        ("DBAC", "DABC"): (1, 0),
    }
    assert graph_data(vs, flipped)[2]
    print("24-path interval: edge-reversal changes", sorted(changes.items()))


def verify_path_supports(vs, edges):
    """Enumerate all paths and their top contextual edge sets.

    Nonempty paths have a top-dimensional label, and these labels determine
    their boundaries. Identity paths are distinguished by the lower cell.
    The printed support count uses that inductive identity convention.
    """
    outgoing = defaultdict(list)
    for i, (s, t, _) in enumerate(sorted(edges)):
        outgoing[s].append((t, 1 << i))
    supports = set()
    count = 0

    def visit(source, current, mask):
        nonlocal count
        signature = (3, mask) if mask else (2, source)
        assert signature not in supports, (source, current, mask)
        supports.add(signature)
        count += 1
        for target, bit in outgoing[current]:
            assert not mask & bit
            visit(source, target, mask | bit)

    for source in sorted(vs):
        visit(source, source, 0)
    return count, len(supports)


def main():
    verify_independent_update()
    verify_octagons()
    print("All three octagon signs agree with the tensor differential.")
    for n in (1, 2, 3):
        for us in combinations(UPDATES, n):
            vs = vertices(us)
            original = base_edges(vs)
            before_mu, _ = apply_repairs(vs, original, False)
            after_mu, relations = apply_repairs(vs, original, True)
            original_data = graph_data(vs, original)
            before_data = graph_data(vs, before_mu)
            after_data = graph_data(vs, after_mu)
            assert original_data[2] and before_data[2] and after_data[2]
            print(
                "updates", "".join(us), "vertices", len(vs),
                "original sources/sinks", original_data[:2],
                "sources before mu", before_data[0],
                "sources after mu", after_data[0],
                "acyclic", after_data[2],
            )
            if us == ("a", "c"):
                assert before_data[0] == ["acrqp", "crqpa"]
                assert find_path(before_mu, "acrqp", "crqap") is None
                assert find_path(before_mu, "crqpa", "acrqp") is None
                assert find_path(after_mu, "crqpa", "acrqp") is not None
            if us == ("a", "b", "c"):
                assert len(vs) == 240 and len(original) == 504
                assert len(after_mu) == 504 and len(relations) == 45
                assert before_data[0] == ["acrqbp", "crqbpa"]
                assert after_data[0] == ["crqbpa"]
                print("Original edge families:", Counter(e[2] for e in original))
                print("Repair instances:", Counter(r[1][2] for r in relations))
                cells, supports = verify_path_supports(vs, after_mu)
                assert cells == supports == 40412
                print("Nonidentity three-paths with distinct contextual supports:",
                      cells - len(vs))
                print("Identity three-paths distinguished by their two-paths:",
                      len(vs))
    print("All assertions passed.")


if __name__ == "__main__":
    main()
