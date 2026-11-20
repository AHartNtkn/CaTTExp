"""Degree-three K15 equality on a run of named adjacent inversion swaps.

Inputs are typed histories on the same one-slot interval, using distinct
ordered pairs. Each possible rectangle is an interval of event precedences.
"""


from marked_swap_schedules import expansions


def block(word):
    """Return the axes in processing order if the factor is a binary expansion."""
    if not word:
        return None
    rows = tuple(dict.fromkeys(e[0] for e in word))
    cols = tuple(dict.fromkeys(e[1] for e in word))
    if max(rows) >= min(cols) or len(rows)*len(cols) != len(word):
        return None
    time = {tuple(e): i for i, e in enumerate(word)}
    # Distinct named pairs in the input imply all product entries are present.
    t = [[time[a,b] for b in cols] for a in rows]
    if any(x >= y for line in (*t, *zip(*t)) for x, y in zip(line, line[1:])):
        return None
    pending = [(0, len(rows)-1, 0, len(cols)-1)]
    while pending:
        a, b, c, d = pending.pop()
        if a == b or c == d:
            continue
        for i in range(a,b):
            if t[i][d] < t[i+1][c]:
                pending.extend(((a,i,c,d), (i+1,b,c,d)))
                break
        else:
            for j in range(c,d):
                if t[b][j] < t[a][j+1]:
                    pending.extend(((a,b,c,j), (a,b,j+1,d)))
                    break
            else:
                return None
    return rows, cols


def incidence(word):
    before = []
    previous = {}
    for i, event in enumerate(word):
        bits = 1 << i
        for slot in event:
            if slot in previous:
                bits |= before[previous[slot]]
            previous[slot] = i
        before.append(bits)
    return before


def possible_boxes(word):
    """Intervals of the invariant same-strand order with a full box projection."""
    before = incidence(word)
    boxes = {}
    for first in range(len(word)):
        after = sum(1 << j for j in range(first, len(word)) if before[j] >> first & 1)
        for last in range(first + 3, len(word)):
            mask = after & before[last]
            if mask.bit_count() < 4:
                continue
            ids = [i for i in range(first, last + 1) if mask >> i & 1]
            axes = block(tuple(word[i] for i in ids))
            if axes is None or min(map(len, axes)) < 2:
                continue
            rows, cols = axes
            coords = [(rows.index(word[i][0]), cols.index(word[i][1])) for i in ids]
            movable = [(i, j) for n, (i, (a, b)) in enumerate(zip(ids, coords))
                       for j, (c, d) in zip(ids[n+1:], coords[n+1:])
                       if (a-c)*(b-d) < 0]
            if any(before[j] >> i & 1 for i, j in movable):
                continue
            support = frozenset(word[i] for i in ids)
            boxes[support] = (axes, mask, first, last, movable)
    return boxes


def forced_order(length, allowed, boxes):
    before = [(1 << (j+1)) - 1 for j in range(length)]
    for support in allowed:
        for i, j in boxes[support][4]:
            before[j] &= ~(1 << i)
    for j in range(length):
        for i in range(j):
            if before[j] >> i & 1:
                before[j] |= before[i]
    return before


def candidates(word):
    """Bound first use from below in time and eliminate impossible supports."""
    boxes = possible_boxes(word)
    allowed = set(boxes)
    while True:
        reached = set()
        while True:
            before = forced_order(len(word), reached, boxes)
            additions = set()
            for support in allowed - reached:
                _, mask, first, last, _ = boxes[support]
                # A forced outsider between opposite corners prevents first use.
                if all(mask >> j & 1 or not ((before[j] >> first & 1) and (before[last] >> j & 1))
                       for j in range(first + 1, last)):
                    additions.add(support)
            if not additions:
                break
            reached.update(additions)
        viable = {support for support in reached
                  if all(not (before[j] >> i & 1) for i, j in boxes[support][4])}
        if viable == allowed:
            return before, {s: boxes[s][0] for s in viable}
        allowed = viable


def runs(word, rectangles):
    """Each nontrivial replacement is inside one run of component labels."""
    owner = {e: i for i,e in enumerate(word)}
    for rect in rectangles:
        labels = {owner[e] for e in rect}
        if len(labels) > 1:
            merged = min(labels)
            for e in owner:
                if owner[e] in labels:
                    owner[e] = merged
    result = []
    for event in word:
        if not result or owner[event] != owner[result[-1][0]]:
            result.append([])
        result[-1].append(event)
    return tuple(map(tuple, result)), owner


def common_partition(left, right):
    """A common chronological list of rectangular blocks, by interval DP."""
    cuts = {0}
    for end in range(1,len(left)+1):
        for start in range(end):
            if start not in cuts:
                continue
            a, b = left[start:end], right[start:end]
            if a == b or (set(a) == set(b) and (axes := block(a)) is not None and axes == block(b)):
                cuts.add(end)
                break
    return len(left) in cuts


def square_sites(word, rectangles):
    """Find exactly the middle pairs that can flip using 2-by-2 boxes."""
    guards = _square_guards(rectangles)
    sites = {}
    while True:
        previous_size = len(sites)
        for i in range(1, len(word)-2):
            if any(j in sites for j in (i-1, i, i+1)):
                continue
            pair = frozenset(word[i:i+2])
            if pair not in guards:
                continue
            first, last = guards[pair]
            left = word[i-2:i] if i-2 in sites else (word[i-1],)
            right = word[i+2:i+4] if i+2 in sites else (word[i+2],)
            if first in left and last in right:
                sites[i] = (first, last)
        if len(sites) == previous_size:
            return sites


def square_equal(word, target, rectangles):
    """Equality under 2-by-2 moves, including their full contextual guards."""
    sites = square_sites(word, rectangles)
    i = 0
    while i < len(word):
        if i in sites:
            if set(word[i:i+2]) != set(target[i:i+2]):
                return False
            i += 2
        else:
            if word[i] != target[i]:
                return False
            i += 1
    for i, (_, last) in sites.items():
        if i+2 in sites:
            first = sites[i+2][0]
            if target[i+2] != last and target[i+1] != first:
                return False
    return True


def next_words(word, rectangles):
    for support, axes in rectangles.items():
        if not support.issubset(word):
            continue
        positions = [i for i,e in enumerate(word) if e in support]
        i, j = positions[0], positions[-1]+1
        if j-i == len(positions) and block(word[i:j]) == axes:
            # The expansion grammar takes columns in spatial order.
            for other in expansions(axes[0], axes[1][::-1]):
                if other != word[i:j]:
                    yield word[:i]+other+word[j:]


def _square_guards(rectangles):
    guards = {}
    for _, (rows, cols) in rectangles.items():
        if len(rows) == len(cols) == 2:
            middle = frozenset(((rows[0], cols[1]), (rows[1], cols[0])))
            guards[middle] = (rows[0], cols[0]), (rows[1], cols[1])
    return guards


class _SquareFibre:
    """Read tracked positions literally and solve the remaining path of bits."""

    def __init__(self, word, tracked, sites):
        self.original = word
        self.sites = sites
        self.interface = {i for i in sites if any(j in tracked for j in range(i-1, i+3))}
        self.indices = sorted(tracked | {pos for i in self.interface for pos in (i, i+1)})
        self.owner = {pos: i for i in sites for pos in (i, i+1)}

    def pack(self, word):
        return tuple(word[i] for i in self.indices)

    def read(self, state, required=()):
        """Produce a reachable spelling in this fibre meeting position constraints."""
        fixed = dict(zip(self.indices, state))
        bits = {}
        for pos, event in (*fixed.items(), *required):
            if pos in fixed and fixed[pos] != event:
                return None
            if pos not in self.owner:
                if pos not in fixed and event != self.original[pos]:
                    return None
                continue
            i = self.owner[pos]
            if event == self.original[pos]:
                value = 0
            elif event == self.original[2*i+1-pos]:
                value = 1
            else:
                return None
            if i in bits and bits[i] != value:
                return None
            bits[i] = value

        # One forbidden orientation pair per link. Store a predecessor for
        # each feasible orientation rather than enumerating all assignments.
        parents = {}
        previous = None
        for i in sorted(self.sites):
            choices = (bits[i],) if i in bits else (0, 1)
            parents[i] = {}
            for value in choices:
                if previous is None:
                    parents[i][value] = None
                    continue
                for earlier in parents[previous]:
                    if previous+2 == i:
                        left_supplies = self.original[i-1-earlier] == self.sites[i][0]
                        right_supplies = self.original[i+value] == self.sites[previous][1]
                        if not (left_supplies or right_supplies):
                            continue
                    parents[i][value] = earlier
                    break
            if not parents[i]:
                return None
            previous = i

        result = list(self.original)
        for pos, event in fixed.items():
            result[pos] = event
        value = next(iter(parents[previous])) if previous is not None else None
        for i in reversed(sorted(self.sites)):
            result[i:i+2] = self.original[i:i+2][::-1] if value else self.original[i:i+2]
            value = parents[i][value]
        return tuple(result)


def wide_equal(word, target, rectangles):
    """Exact comparison, exponential only in the number of wide-box events."""
    wide = {box: axes for box, axes in rectangles.items() if len(box) > 4}
    if not wide:
        return square_equal(word, target, rectangles)
    exceptional = set().union(*wide)
    def around(positions, distance):
        return {j for i in positions
                for j in range(max(0, i-distance), min(len(word), i+distance+1))}
    core = around((i for i, e in enumerate(word) if e in exceptional), 1)
    tracked = around(core, 3)
    guards = _square_guards(rectangles)
    inside, outside = [], {}
    for i in range(1, len(word)-2):
        if any(j in core for j in range(i-1, i+3)):
            inside.append(i)
        else:
            pair = frozenset(word[i:i+2])
            if pair in guards:
                outside[i] = guards[pair]

    sites = {}
    while True:
        fibre = _SquareFibre(word, tracked, sites)
        missing = {i: pair for i, pair in outside.items()
                   if all(j not in sites for j in (i-1, i, i+1))}
        start = fibre.pack(word)
        todo, seen = [start], {start}
        while todo:
            state = todo.pop()
            if state == fibre.pack(target) and fibre.read(state, enumerate(target)) is not None:
                return True
            current = fibre.read(state)
            assert current is not None
            # Look for the first flip at a new exterior pair. Resolving its
            # guards may require a different assignment in the current fibre.
            discovered = None
            for i, (first, last) in missing.items():
                wanted = ((i-1, first), (i, word[i]), (i+1, word[i+1]), (i+2, last))
                if fibre.read(state, wanted) is not None:
                    discovered = i
                    break
            if discovered is not None:
                sites[discovered] = missing[discovered]
                break
            for other in next_words(current, wide):
                result = fibre.pack(other)
                if result not in seen:
                    seen.add(result)
                    todo.append(result)
            for i in (*inside, *fibre.interface):
                pair = frozenset(current[i:i+2])
                if pair not in guards:
                    continue
                first, last = guards[pair]
                available = fibre.read(state, ((i-1, first), (i+2, last)))
                if available is None:
                    continue
                other = available[:i] + available[i:i+2][::-1] + available[i+2:]
                result = fibre.pack(other)
                if result not in seen:
                    seen.add(result)
                    todo.append(result)
        else:
            return False


def equal(left, right):
    """Exact, with exponential search confined to the residual mixed-role runs."""
    left, right = (tuple(tuple(e) for e in w) for w in (left, right))
    if left == right:
        return True
    if len(left) != len(right) or set(left) != set(right):
        return False
    before, rects = candidates(left)
    position = {e:i for i,e in enumerate(right)}
    if any(position[left[i]] > position[left[j]] for j in range(len(left))
           for i in range(j) if before[j] >> i & 1):
        return False
    if any(block(tuple(e for e in right if e in rect)) != axes for rect,axes in rects.items()):
        return False
    pieces, owner = runs(left, rects)
    if any(owner[a] != owner[b] for a,b in zip(left,right)):
        return False
    offset = 0
    for piece in pieces:
        target = right[offset:offset+len(piece)]
        offset += len(piece)
        if set(piece) != set(target):
            return False
        if common_partition(piece, target):
            continue
        small = {e[0] for e in piece}
        large = {e[1] for e in piece}
        if small.isdisjoint(large):
            return False
        local = {box: axes for box,axes in rects.items() if box.issubset(piece)}
        if square_equal(piece, target, local):
            continue
        if not wide_equal(piece, target, local):
            return False
    return True
