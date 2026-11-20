"""Equality of chronological path SLPs relative to equality of their unary runs.

Inputs are topologically sorted binary grammars. Nonnegative integers are
terminals, ~i references rule i, and an empty right side is an identity.
Terminals name contextual letters with their lower labels already classified.
Both input roots must be parallel; their endpoints are supplied by the caller.
"""

from dataclasses import dataclass


def compressed_equal(rules, left, right):
    """Exact equality by block and pair recompression, with protected root rules."""
    # Work only on ancestors of the query. Slice and prefix queries commonly
    # share an arena containing many unrelated path or context grammars.
    used = set()
    pending = [left, right]
    while pending:
        i = pending.pop()
        if i not in used:
            used.add(i)
            pending.extend(~x for x in rules[i] if x < 0)
    ordered = sorted(used)
    indices = {old: i for i, old in enumerate(ordered)}
    grammar = [[x if x >= 0 else ~indices[~x] for x in rules[i]] for i in ordered]
    count = len(grammar)
    grammar.extend(([~indices[left]], [~indices[right]]))
    limit = max((x for row in grammar for x in row if x >= 0), default=-1) + 1
    fresh = limit

    def phase(partition=None):
        # Pop boundaries bottom up. Emitted blocks use binary multiplicities.
        nonlocal fresh
        pops = []
        names = {}

        def name(key):
            nonlocal fresh
            if key not in names:
                names[key] = fresh
                fresh += 1
            return names[key]

        for i, row in enumerate(grammar):
            parts = []

            def append(x, amount=1):
                if x >= 0 and partition is None and parts and parts[-1][0] == x:
                    parts[-1] = (x, parts[-1][1] + amount)
                else:
                    parts.append((x, amount))

            for x in row:
                if x >= 0:
                    append(x)
                    continue
                prefix, suffix = pops[~x]
                if prefix:
                    append(*prefix)
                if grammar[~x]:
                    append(x)
                if suffix:
                    append(*suffix)

            prefix = suffix = None
            if i < count:
                if parts and parts[0][0] >= 0 and (
                        partition is None or partition(parts[0][0]) == 1):
                    prefix = parts.pop(0)
                if parts and parts[-1][0] >= 0 and (
                        partition is None or partition(parts[-1][0]) == 0):
                    suffix = parts.pop()
            pops.append((prefix, suffix))
            if partition is None:
                grammar[i] = [x if k == 1 else name((x, k)) for x, k in parts]
            else:
                result = []
                for x, _ in parts:
                    if (result and result[-1] >= 0 and x >= 0 and
                            partition(result[-1]) == 0 and partition(x) == 1):
                        result[-1] = name((result[-1], x))
                    else:
                        result.append(x)
                grammar[i] = result

    def lengths():
        sizes = []
        for row in grammar:
            sizes.append(sum(1 if x >= 0 else sizes[~x] for x in row))
        return sizes[-2:]

    while True:
        a, b = lengths()
        if a != b:
            return False
        if a <= 1:
            first = []
            for row in grammar:
                first.append(next((x if x >= 0 else first[~x] for x in row
                                   if x >= 0 or first[~x] is not None), None))
            return first[-2] == first[-1]
        phase()
        # Every distinct old pair is separated by one bit in one orientation.
        # Symbols coined during the pair sweep are excluded from its partitions.
        old = fresh
        for bit in range((old - 1).bit_length()):
            for flip in (0, 1):
                phase(lambda x: (((x >> bit) & 1) ^ flip) if x < old else -1)


@dataclass(frozen=True)
class Split:
    prefix: int
    core: int | None
    suffix: int


def separated_equal(rules, left, right, unary, same_run):
    """Compare parallel paths. same_run(grammar, a, b) compares unary-only SLPs.

    The grammar passed to same_run has the same unary terminal identifiers as
    the input. Empty runs at adjacent rigid occurrences are implicit. A proper
    unary word cannot equal an identity by positivity.
    """
    runs = [()]
    tokens = [()]
    representatives = []
    run_names = {0: 0}
    rigid_names = {}

    def leaf(grammar, symbol):
        grammar.append((symbol,))
        return len(grammar) - 1

    def cat(grammar, a, b):
        if not a or not b:
            return a or b
        grammar.append((~a, ~b))
        return len(grammar) - 1

    def gap(a):
        if a not in run_names:
            for b, token in representatives:
                if same_run(runs, a, b):
                    break
            else:
                token = leaf(tokens, 2 * len(representatives))
                representatives.append((a, token))
            run_names[a] = token
        return run_names[a]

    summaries = []
    for rule in rules:
        if not rule:
            summary = Split(0, None, 0)
        elif len(rule) == 1 and rule[0] >= 0:
            x, = rule
            if x in unary:
                summary = Split(leaf(runs, x), None, 0)
            else:
                if x not in rigid_names:
                    rigid_names[x] = leaf(tokens, 2 * len(rigid_names) + 1)
                summary = Split(0, rigid_names[x], 0)
        else:
            a, b = (summaries[~x] for x in rule)
            if a.core is None:
                summary = Split(cat(runs, a.prefix, b.prefix), b.core, b.suffix)
            elif b.core is None:
                summary = Split(a.prefix, a.core, cat(runs, a.suffix, b.prefix))
            else:
                seam = gap(cat(runs, a.suffix, b.prefix))
                core = cat(tokens, cat(tokens, a.core, seam), b.core)
                summary = Split(a.prefix, core, b.suffix)
        summaries.append(summary)

    def finish(s):
        core = s.core or 0
        return cat(tokens, cat(tokens, gap(s.prefix), core), gap(s.suffix))

    return compressed_equal(tokens, finish(summaries[left]), finish(summaries[right]))
