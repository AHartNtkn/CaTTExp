#!/usr/bin/env python3
"""Exact finite checks for the stated D2^3 three-skeleton.

This file is self-contained and does not import or alter triple_tensor_check.py.
It verifies the I-quotient on two-words and builds a finite globular lift of the
tensor top by allowing additional four-generators.  It does not claim that the
original prescribed four-generators alone give this lift.
Of the 24 selected four-operations, nine are exact three-whiskerings of the
prescribed four-cells and 15 are freshly adjoined generators.

Run: python r6_endpoint_lifts_check.py
Optional complete witnesses: python r6_endpoint_lifts_check.py --json PATH

An n-chain is a nonnegative integer combination of tensor basis labels.
For a basis label l, d(l) uses the Koszul tensor sign.  The exact chain-tableau
model nu(K) specifies a cell by its chains in each dimension.  The constructed
higher boundaries satisfy these tableau identities, and their raw globular
boundaries are equal, not merely I-equivalent.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import permutations, product
import json

UPDATES = {"a": 0, "b": 1, "c": 2}
CROSSES = {"p": (0, 1), "q": (0, 2), "r": (1, 2)}
REPAIRS = (
    ("bpa", "abp", "bap", "h_p", "T"),
    ("cqa", "acq", "caq", "h_q", "T"),
    ("crb", "bcr", "cbr", "h_r", "T"),
    ("rqa", "arq", "raq", "lambda_x", "T"),
    ("crqp", "pcqr", "cpqr", "h_z", "tau"),
    ("crqa", "acrq", "carq", "mu", "lambda_x"),
)
SOURCE, TARGET = "crqbpa", "apqbrc"
TOP = ((2, ""), (2, ""), (2, ""))


def signature(chain):
    return tuple(sorted((label, n) for label, n in chain.items() if n))


def chain(signature_):
    return Counter(dict(signature_))


def differential(label):
    result = Counter()
    degree_before = 0
    for i, (degree, _) in enumerate(label):
        if degree:
            for endpoint, endpoint_sign in (("+", 1), ("-", -1)):
                face = list(label)
                face[i] = (degree - 1, endpoint)
                result[tuple(face)] += (-1) ** degree_before * endpoint_sign
        degree_before += degree
    return Counter({label: n for label, n in result.items() if n})


def dchain(c):
    result = Counter()
    for label, n in c.items():
        for face, m in differential(label).items():
            result[face] += n * m
    return Counter({label: n for label, n in result.items() if n})


def signed_boundary(c, sign):
    return Counter({label: sign * n for label, n in dchain(c).items()
                    if sign * n > 0})


def atom_boundary(label, sign, dimension):
    result = Counter({label: 1})
    for _ in range(sum(degree for degree, _ in label) - dimension):
        result = signed_boundary(result, sign)
    return signature(result)


def basis(dimension):
    result = []
    for degrees in product(range(3), repeat=3):
        if sum(degrees) == dimension:
            for signs in product(*[("",) if n == 2 else ("-", "+")
                                   for n in degrees]):
                result.append(tuple(zip(degrees, signs)))
    return result


def swap_wires(wires, event):
    i, j = CROSSES[event]
    ii, jj = wires.index(i), wires.index(j)
    assert abs(ii - jj) == 1 and wires[min(ii, jj)] == max(i, j)
    wires[ii], wires[jj] = wires[jj], wires[ii]


def word_chain(word):
    result = Counter()
    wires = [2, 1, 0]
    states = ["-", "-", "-"]
    for event in word:
        if event in UPDATES:
            i = UPDATES[event]
            label = tuple((2, "") if j == i else
                          (0, "+" if wires.index(j) < wires.index(i) else "-")
                          for j in range(3))
            states[i] = "+"
        else:
            i, j = CROSSES[event]
            k = next(k for k in range(3) if k not in (i, j))
            label = tuple((1, states[h]) if h in (i, j) else
                          (0, "+" if wires.index(k) <
                           min(wires.index(i), wires.index(j)) else "-")
                          for h in range(3))
            swap_wires(wires, event)
        result[label] += 1
    return result


def original_edge_label(edge):
    source, target, kind = edge
    if kind == "I":
        return None
    index = next(i for i, (x, y) in enumerate(zip(source, target)) if x != y)
    wires = [2, 1, 0]
    states = ["-", "-", "-"]
    for event in source[:index]:
        if event in UPDATES:
            states[UPDATES[event]] = "+"
        else:
            swap_wires(wires, event)
    if kind == "tau":
        return tuple((1, states[i]) for i in range(3))
    x, y = source[index:index + 2]
    update = x if x in UPDATES else y
    crossing = x if x in CROSSES else y
    i = UPDATES[update]
    j = next(j for j in CROSSES[crossing] if j != i)
    k = next(k for k in range(3) if k not in CROSSES[crossing])
    label = [(0, "+" if wires.index(k) < wires.index(i) else "-")] * 3
    label[i], label[j] = (2, ""), (1, states[j])
    return tuple(label)


def make_graph():
    vertices = {"".join(p) for p in permutations("abcpqr")
                if "".join(x for x in p if x in CROSSES) in ("pqr", "rqp")}
    original = set()
    for word in sorted(vertices):
        wires = [2, 1, 0]
        for j, x in enumerate(word[:-1]):
            y = word[j + 1]
            target = word[:j] + y + x + word[j + 2:]
            allowed, kind = False, None
            if target in vertices:
                if x in UPDATES and y in UPDATES:
                    allowed = wires.index(UPDATES[x]) > wires.index(UPDATES[y])
                    kind = "I"
                elif x in UPDATES and y in CROSSES:
                    i = UPDATES[x]
                    if i in CROSSES[y]:
                        allowed, kind = i == max(CROSSES[y]), "T"
                    else:
                        allowed = wires.index(i) > min(wires.index(k)
                                                       for k in CROSSES[y])
                        kind = "I"
                elif x in CROSSES and y in UPDATES:
                    i = UPDATES[y]
                    if i in CROSSES[x]:
                        allowed, kind = i == min(CROSSES[x]), "T"
                    else:
                        allowed = min(wires.index(k) for k in CROSSES[x]) > wires.index(i)
                        kind = "I"
                if allowed:
                    original.add((word, target, kind))
            if x in CROSSES:
                swap_wires(wires, x)
        if "rqp" in word:
            original.add((word, word.replace("rqp", "pqr"), "tau"))
    all_edges, eliminated, relations = set(original), set(), {}
    labels = {edge: original_edge_label(edge) for edge in original}
    for lhs, middle, rhs, name, old_name in REPAIRS:
        for word in sorted(vertices):
            if lhs not in word:
                continue
            m, t = word.replace(lhs, middle), word.replace(lhs, rhs)
            if m not in vertices:
                continue
            old, new, inner = (word, t, old_name), (word, m, name), (m, t, "I")
            assert old in all_edges and inner in all_edges and old not in eliminated
            eliminated.add(old)
            all_edges.add(new)
            relations[old] = (new, inner)
            labels[new] = labels[old]
    edges = all_edges - eliminated
    assert (len(vertices), len(original), len(edges), len(relations)) == (240, 504, 504, 45)
    for s, t, kind in edges:
        difference = word_chain(t)
        difference.subtract(word_chain(s))
        expected = differential(labels[s, t, kind]) if labels[s, t, kind] else Counter()
        assert signature(difference) == signature(expected)
    return vertices, original, edges, all_edges, labels, relations


def label_text(label):
    return "".join(str(n) + sign for n, sign in label)


def chain_text(sig):
    return " + ".join((str(n) + "*" if n != 1 else "") + label_text(label)
                      for label, n in sig) or "0"


def tableau_json(levels):
    """Validate every chain-tableau equation, including dimensions zero and one."""
    assert levels[-1][0] == levels[-1][1]
    for dimension, (negative, positive) in enumerate(levels):
        for side in (negative, positive):
            assert all(n > 0 and sum(d for d, _ in label) == dimension
                       for label, n in side)
        if dimension == 0:
            assert sum(n for _, n in negative) == sum(n for _, n in positive) == 1
        else:
            expected = chain(levels[dimension - 1][1])
            expected.subtract(chain(levels[dimension - 1][0]))
            assert signature(dchain(chain(negative))) == signature(expected)
            assert signature(dchain(chain(positive))) == signature(expected)
    return [dict(dimension=i, negative=[dict(basis=label, coefficient=n) for label, n in neg],
                 positive=[dict(basis=label, coefficient=n) for label, n in pos])
            for i, (neg, pos) in enumerate(levels)]


def route_chain(route, labels):
    return Counter(labels[e] for e in route if labels[e] is not None)


def enumerate_paths(outgoing, source, target):
    result = []
    active = set()
    def visit(current, route):
        assert current not in active, "A directed cycle was found"
        if current == target:
            result.append(tuple(route))
        active.add(current)
        for edge in outgoing[current]:
            visit(edge[1], route + [edge])
        active.remove(current)
    visit(source, [])
    return result


def make_chain_graph(signatures, labels):
    indices = {sig: i for i, sig in enumerate(signatures)}
    outgoing = defaultdict(list)
    for i, sig in enumerate(signatures):
        for j, label in enumerate(labels):
            target = chain(sig)
            target.update(differential(label))
            if any(n < 0 for n in target.values()):
                continue
            target_sig = signature(target)
            if target_sig in indices:
                outgoing[i].append((i, indices[target_sig], j))
    return outgoing, indices


def prescribed_contexts(vertices, edges, all_edges, labels, relations, ancestors):
    schemes = {
        "W_x": (["rqpa", "pqra", "pqar", "paqr", "apqr"],
                ["rqpa", "rqap", "arqp", "apqr"]),
        "W_y": (["rqbp", "rbqp", "brqp", "bpqr", "pbqr", "pqbr"],
                ["rqbp", "rqpb", "pqrb", "pqbr"]),
        "W_z": (["crqp", "rcqp", "rqcp", "rqpc", "pqrc"],
                ["crqp", "pcqr", "pqcr", "pqrc"]),
        "W_xy": (["bpa", "pba", "pab", "apb"], ["bpa", "abp", "apb"]),
        "W_xz": (["cqa", "qca", "qac", "aqc"], ["cqa", "acq", "aqc"]),
        "W_yz": (["crb", "rcb", "rbc", "brc"], ["crb", "bcr", "brc"]),
    }
    by_endpoints = defaultdict(list)
    for edge in all_edges:
        by_endpoints[edge[:2]].append(edge)
    def expand(edge):
        if edge in edges:
            return [edge]
        new, inner = relations[edge]
        return expand(new) + expand(inner)
    def route(words):
        result = []
        for s, t in zip(words, words[1:]):
            candidates = by_endpoints[s, t]
            assert len(candidates) == 1
            result += expand(candidates[0])
        return result
    records = []
    for name, (negative, positive) in schemes.items():
        residual = sorted(set("abcpqr") - set(negative[0]))
        for perm in permutations(residual):
            for cut in range(len(perm) + 1):
                prefix, suffix = "".join(perm[:cut]), "".join(perm[cut:])
                neg_words = [prefix + w + suffix for w in negative]
                pos_words = [prefix + w + suffix for w in positive]
                if not all(w in vertices for w in neg_words + pos_words):
                    continue
                neg, pos = route(neg_words), route(pos_words)
                delta = route_chain(pos, labels)
                delta.subtract(route_chain(neg, labels))
                matches = [w for w in basis(4) if signature(differential(w)) == signature(delta)]
                assert len(matches) == 1
                records.append(dict(scheme=name, prefix=prefix, suffix=suffix,
                                    source=neg_words[0], target=neg_words[-1],
                                    tensor_label=label_text(matches[0]),
                                    can_reach_top_target=neg_words[-1] in ancestors,
                                    negative=neg, positive=pos))
    return records


def exact_reuse_certificates(selected4, representatives3, contexts, labels4):
    """Recognize literal raw route substitution, without any I-equivalence."""
    result = []
    for s, t, k in selected4:
        source, target = representatives3[s], representatives3[t]
        matches = []
        for context_index, context in enumerate(contexts):
            if context["tensor_label"] != label_text(labels4[k]):
                continue
            negative, positive = tuple(context["negative"]), tuple(context["positive"])
            for cut in range(len(source) - len(negative) + 1):
                if source[cut:cut + len(negative)] != negative:
                    continue
                prefix, suffix = source[:cut], source[cut + len(negative):]
                if prefix + positive + suffix != target:
                    continue
                assert source == prefix + negative + suffix
                assert target == prefix + positive + suffix
                matches.append(dict(
                    source=s, target=t, basis_index=k,
                    tensor_label=label_text(labels4[k]),
                    prescribed_context_index=context_index,
                    prescribed_scheme=context["scheme"],
                    prescribed_word_prefix=context["prefix"],
                    prescribed_word_suffix=context["suffix"],
                    left_cut=cut,
                    common_three_prefix=prefix,
                    common_three_suffix=suffix,
                ))
        if matches:
            result.append(min(matches, key=lambda m:
                              (m["prescribed_context_index"], m["left_cut"])))
    return result


def main():
    parser = ArgumentParser()
    parser.add_argument("--json", help="Write all witnesses as JSON")
    args = parser.parse_args()
    vertices, original, edges, all_edges, labels, relations = make_graph()
    outgoing, incoming = defaultdict(list), defaultdict(list)
    for edge in sorted(edges):
        outgoing[edge[0]].append(edge)
        incoming[edge[1]].append(edge)
    sinks = sorted(w for w in vertices if not outgoing[w])
    assert sinks == ["apqbrc", "apqcbr", "bapqrc", "braqpc", "brcaqp",
                     "capqbr", "cbapqr", "cbraqp", "raqpbc", "rcaqpb"]
    parent = {v: v for v in vertices}
    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for s, t, kind in original:
        if kind == "I":
            parent[root(s)] = root(t)
    classes = defaultdict(set)
    signatures_to_words = defaultdict(set)
    for word in vertices:
        classes[root(word)].add(word)
        signatures_to_words[signature(word_chain(word))].add(word)
    assert len(classes) == len(signatures_to_words) == 54
    assert {frozenset(c) for c in classes.values()} == {
        frozenset(c) for c in signatures_to_words.values()}
    source_two, target_two = atom_boundary(TOP, -1, 2), atom_boundary(TOP, 1, 2)
    assert signatures_to_words[source_two] == {"crqbpa", "crbqpa"}
    assert signatures_to_words[target_two] == {"apbqrc", "apqbrc"}
    assert ("crqbpa", "crbqpa", "I") in edges
    assert ("apbqrc", "apqbrc", "I") in edges
    common_levels = [(atom_boundary(TOP, -1, i), atom_boundary(TOP, 1, i))
                     for i in range(3)]
    for word in vertices:
        # Every raw two-word has the same actual one-source and one-target.
        word_sig = signature(word_chain(word))
        tableau_json(common_levels[:2] + [(word_sig, word_sig)])
    for edge in edges:
        s, t, _ = edge
        edge_sig = signature(Counter({labels[edge]: 1})) if labels[edge] else ()
        tableau_json(common_levels[:2] +
                     [(signature(word_chain(s)), signature(word_chain(t))),
                      (edge_sig, edge_sig)])

    ancestors, todo = {TARGET}, [TARGET]
    while todo:
        current = todo.pop()
        for source, _, _ in incoming[current]:
            if source not in ancestors:
                ancestors.add(source)
                todo.append(source)
    ancestor_edges = {e for e in edges if e[0] in ancestors and e[1] in ancestors}
    assert (len(ancestors), len(ancestor_edges)) == (126, 244)
    ancestor_outgoing = defaultdict(list)
    for edge in sorted(ancestor_edges):
        ancestor_outgoing[edge[0]].append(edge)
    paths = enumerate_paths(ancestor_outgoing, SOURCE, TARGET)
    assert len(paths) == 1226
    groups = defaultdict(list)
    for path in paths:
        groups[signature(route_chain(path, labels))].append(path)
    assert len(groups) == 25
    signatures3 = sorted(groups)
    representatives3 = [min(groups[sig], key=lambda p: (len(p), p)) for sig in signatures3]
    negative3, positive3 = atom_boundary(TOP, -1, 3), atom_boundary(TOP, 1, 3)
    assert (len(groups[negative3]), len(groups[positive3])) == (252, 2)

    labels4, labels5 = basis(4), basis(5)
    outgoing4, indices3 = make_chain_graph(signatures3, labels4)
    assert sum(map(len, outgoing4.values())) == 39
    source3, target3 = indices3[negative3], indices3[positive3]
    paths4 = enumerate_paths(outgoing4, source3, target3)
    assert len(paths4) == 17
    groups4 = defaultdict(list)
    for path in paths4:
        groups4[signature(Counter(labels4[e[2]] for e in path))].append(path)
    assert len(groups4) == 6
    signatures4 = sorted(groups4)
    assert atom_boundary(TOP, -1, 4) in groups4 and atom_boundary(TOP, 1, 4) in groups4

    # Pick an economical certificate among these choices. No global minimality
    # of the number of four-generators is claimed.
    choices = product(*(sorted(groups4[sig]) for sig in signatures4))
    def selection_score(selection):
        selected_edges = {edge for path in selection for edge in path}
        selected_vertices = {v for edge in selected_edges for v in edge[:2]}
        return len(selected_edges), len(selected_vertices), selection
    representatives4 = min(choices, key=selection_score)
    selected4 = sorted({edge for path in representatives4 for edge in path})
    needed3 = sorted({v for edge in selected4 for v in edge[:2]})
    assert (len(selected4), len(needed3), len({e[2] for e in selected4})) == (24, 20, 18)

    outgoing5, indices4 = make_chain_graph(signatures4, labels5)
    added5 = sorted(edge for bucket in outgoing5.values() for edge in bucket)
    assert len(added5) == 6
    source4 = indices4[atom_boundary(TOP, -1, 4)]
    target4 = indices4[atom_boundary(TOP, 1, 4)]
    paths5 = enumerate_paths(outgoing5, source4, target4)
    assert len(paths5) == 2
    groups5 = {signature(Counter(labels5[e[2]] for e in path)): path for path in paths5}
    negative5, positive5 = atom_boundary(TOP, -1, 5), atom_boundary(TOP, 1, 5)
    assert set(groups5) == {negative5, positive5}

    # Raw parallelity, in addition to every chain identity above.
    for i in needed3:
        assert representatives3[i][0][0] == SOURCE
        assert representatives3[i][-1][1] == TARGET
    for path in representatives4:
        assert path[0][0] == source3 and path[-1][1] == target3
        assert all(a[1] == b[0] for a, b in zip(path, path[1:]))
    for path in paths5:
        assert path[0][0] == source4 and path[-1][1] == target4
        assert all(a[1] == b[0] for a, b in zip(path, path[1:]))
    tableaux3 = [tableau_json(common_levels + [(sig, sig)]) for sig in signatures3]
    tableaux4 = {}
    for s, t, k in selected4:
        top_sig = signature(Counter({labels4[k]: 1}))
        tableaux4[s, t, k] = tableau_json(
            common_levels + [(signatures3[s], signatures3[t]), (top_sig, top_sig)])
    tableaux4_paths = [tableau_json(common_levels + [(negative3, positive3), (sig, sig)])
                      for sig in signatures4]
    tableaux5 = {}
    for s, t, k in added5:
        top_sig = signature(Counter({labels5[k]: 1}))
        tableaux5[s, t, k] = tableau_json(common_levels + [(negative3, positive3),
                                       (signatures4[s], signatures4[t]), (top_sig, top_sig)])
    tableau6 = tableau_json(common_levels + [(negative3, positive3),
                           (signatures4[source4], signatures4[target4]),
                           (negative5, positive5), (((TOP, 1),), ((TOP, 1),))])
    contexts = prescribed_contexts(vertices, edges, all_edges, labels, relations, ancestors)
    reused4 = exact_reuse_certificates(selected4, representatives3, contexts, labels4)
    reuse_by_edge = {(r["source"], r["target"], r["basis_index"]): i
                     for i, r in enumerate(reused4)}
    assert set(reuse_by_edge) == {
        (8, 6, 10), (9, 0, 1), (12, 3, 1), (13, 9, 4), (16, 15, 16),
        (18, 4, 5), (21, 18, 0), (24, 20, 0), (24, 23, 17),
    }
    fresh4 = [edge for edge in selected4 if edge not in reuse_by_edge]
    assert len(reused4) == 9 and len(fresh4) == 15

    print("I-quotient: 54 classes; tensor 2chains distinguish all 54.")
    print("Top 2source:", chain_text(source_two), sorted(signatures_to_words[source_two]))
    print("Top 2target:", chain_text(target_two), sorted(signatures_to_words[target_two]))
    print("Target ancestor graph: 126 vertices, 244 edges, 1226 source-to-target paths.")
    print("These paths have 25 tensor 3chains; top 3boundaries have 252 and 2 raw lifts.")
    print("Complete possible 4lift graph: 25 vertices, 39 edges.")
    print("Between top 3boundaries: 17 four-paths, 6 four-chain signatures.")
    print("Construction: 20 existing three-paths, 24 selected four-operations:")
    print("              9 reused exact whiskerings, 15 fresh four-generators;")
    print("              6 added five-generators, 1 added six-generator.")
    print("Four-basis labels:", ", ".join(f"{i}={label_text(w)}" for i, w in enumerate(labels4)))
    print("Selected 4operations (source path index, target path index, 4basis index):", selected4)
    print("Fresh 4generators:", fresh4)
    print("Exact reuse certificates (selected operation, context index, scheme,")
    print("                          word prefix, word suffix, 3prefix length, 3suffix length):")
    for record in reused4:
        print((record["source"], record["target"], record["basis_index"]),
              record["prescribed_context_index"], record["prescribed_scheme"],
              repr(record["prescribed_word_prefix"]), repr(record["prescribed_word_suffix"]),
              len(record["common_three_prefix"]), len(record["common_three_suffix"]))
    for i, path in enumerate(representatives4):
        print("R" + str(i), path, "chain", chain_text(signatures4[i]))
    print("Added 5generators:", [(s, t, label_text(labels5[k])) for s, t, k in added5])
    print("Six-source:", [(s, t, label_text(labels5[k])) for s, t, k in groups5[negative5]])
    print("Six-target:", [(s, t, label_text(labels5[k])) for s, t, k in groups5[positive5]])
    print("Prescribed contexts (total, can reach top target):")
    for name in ("W_x", "W_y", "W_z", "W_xy", "W_xz", "W_yz"):
        selected = [r for r in contexts if r["scheme"] == name]
        print(name, len(selected), sum(r["can_reach_top_target"] for r in selected))
    print("All assertions passed. The construction allows additional four-data.")
    if args.json:
        result = dict(
            source=SOURCE, target=TARGET,
            classes2=[dict(chain=chain_text(sig), words=sorted(words))
                      for sig, words in sorted(signatures_to_words.items())],
            source2=chain_text(source_two), target2=chain_text(target_two),
            ancestors=sorted(ancestors), ancestor_edges=sorted(ancestor_edges),
            prescribed_contexts=contexts,
            labels4=[label_text(w) for w in labels4],
            labels5=[label_text(w) for w in labels5],
            paths3=[dict(index=i, chain=chain_text(signatures3[i]),
                         multiplicity=len(groups[signatures3[i]]), path=representatives3[i],
                         used=i in needed3, tableau=tableaux3[i])
                    for i in range(len(signatures3))],
            source3=source3, target3=target3,
            selected4=selected4, fresh4=fresh4, added4=fresh4, reused4=reused4,
            generators4=[dict(source=s, target=t, basis_index=k, tensor_label=label_text(labels4[k]),
                              status="reused" if (s, t, k) in reuse_by_edge else "fresh",
                              reuse_certificate_index=reuse_by_edge.get((s, t, k)),
                              tableau=tableaux4[s, t, k]) for s, t, k in selected4],
            paths4=[dict(index=i, chain=chain_text(signatures4[i]), path=path)
                    | dict(tableau=tableaux4_paths[i])
                    for i, path in enumerate(representatives4)],
            source4=source4, target4=target4, added5=added5,
            generators5=[dict(source=s, target=t, basis_index=k, tensor_label=label_text(labels5[k]),
                              tableau=tableaux5[s, t, k]) for s, t, k in added5],
            negative6=groups5[negative5], positive6=groups5[positive5],
            tableau6=tableau6,
        )
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2)


if __name__ == "__main__":
    main()
