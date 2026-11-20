"""Check occurrence stabilizers by literal two-dimensional strict exchanges."""

from itertools import permutations, product


def exchange_class(history, rules):
    """A step gives the name and left cut of a rewrite of a word of wires."""
    reached = {history}
    pending = [history]
    while pending:
        current = pending.pop()
        for k, ((first, i), (second, j)) in enumerate(zip(current, current[1:])):
            before, after = rules[first]
            other_before, other_after = rules[second]
            swaps = []
            if i + len(after) <= j:
                # The first marker is spatially left in the two-marker word.
                swaps.append(((second, j - len(after) + len(before)), (first, i)))
            if j + len(other_before) <= i:
                # The second marker is spatially left. Both tests may hold at an empty gap.
                swaps.append(((second, j), (first, i - len(other_before) + len(other_after))))
            for pair in swaps:
                neighbor = current[:k] + pair + current[k + 2:]
                if neighbor not in reached:
                    reached.add(neighbor)
                    pending.append(neighbor)
    return reached


def endpoint(wires, history, rules):
    for event, i in history:
        source, target = rules[event]
        assert 0 <= i <= len(wires) and wires[i:i + len(source)] == source
        wires = wires[:i] + target + wires[i + len(source):]
    return wires


def analyse(name, wires, groups, history, rules):
    reached = exchange_class(history, rules)
    target = endpoint(wires, history, rules)
    assert all(endpoint(wires, h, rules) == target for h in reached)
    stabilizer = set()
    for images in product(*(permutations(group) for group in groups)):
        mapping = {a: b for domain, image in zip(groups, images) for a, b in zip(domain, image)}
        lifted = tuple((mapping[event], cut) for event, cut in history)
        if lifted in reached:
            stabilizer.add(images)
    print(f'{name}: {len(reached)} serial histories, stabilizer order {len(stabilizer)}.')
    return stabilizer


def closed_components(count):
    cups = 'ABC'[:count]
    caps = 'abc'[:count]
    rules = dict.fromkeys(cups, ('', 'x')) | dict.fromkeys(caps, ('x', ''))
    # Each successive closed component is a birth followed immediately by its death.
    history = tuple((event, 0) for pair in zip(cups, caps) for event in pair)
    actual = analyse('closed components', '', (cups, caps), history, rules)
    diagonal = {(p, tuple(c.lower() for c in p)) for p in permutations(cups)}
    assert actual == diagonal


def anchored_components():
    cups, caps, markers = 'AB', 'ab', 'XY'
    rules = (dict.fromkeys(cups, ('', 'f')) | dict.fromkeys(caps, ('g', '')) |
             dict.fromkeys(markers, ('g', 'f')))
    history = (('A', 0), ('a', 1), ('X', 1), ('Y', 2), ('B', 3), ('b', 4))
    groups = (cups, caps, markers)
    actual = analyse('two marked and four ordinary anchored gates', 'gggg', groups, history, rules)
    assert actual == {tuple(map(tuple, groups))}
    # Substitute the old composite (consume g, then produce f) for each marker.
    # New occurrences receive their own names here so the old ones can still be tracked.
    expanded_rules = rules | dict.fromkeys('xy', ('g', '')) | dict.fromkeys('UV', ('', 'f'))
    expansion = {'X': 'xU', 'Y': 'yV'}
    shorter = history[:4]
    expanded = tuple((piece, cut) for event, cut in shorter for piece in expansion.get(event, event))
    groups = ('AUV', 'axy')
    actual = analyse('substituted anchored gates', 'ggg', groups, expanded, expanded_rules)
    assert actual == {tuple(map(tuple, groups))}


if __name__ == '__main__':
    closed_components(2)
    closed_components(3)
    anchored_components()
