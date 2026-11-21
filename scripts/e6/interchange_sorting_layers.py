"""Languages of degree-three sorting histories reachable in boundedly many layers.

Each layer allows disjoint binary rectangle re-spellings of arbitrary area.
An arbitrary number of guarded four-event flips is free before and after it.
Inputs are typed atomic histories with distinct named swap events.
"""

from collections import defaultdict

from interchange_sorting_intervals import candidates


class HistoryGrammar:
    """Shared finite languages. Each node has a single output length."""

    def __init__(self):
        self.nodes = []
        self.length = []
        self.indices = {}
        self.empty_word = self._intern(('empty_word',), 0)

    def _intern(self, rule, length):
        if rule not in self.indices:
            self.indices[rule] = len(self.nodes)
            self.nodes.append(rule)
            self.length.append(length)
        return self.indices[rule]

    def literal(self, event):
        return self._intern(('literal', event), 1)

    def join(self, left, right):
        if left == self.empty_word:
            return right
        if right == self.empty_word:
            return left
        return self._intern(('join', left, right), self.length[left] + self.length[right])

    def choice(self, nodes):
        choices = tuple(sorted(set(nodes)))
        if len(choices) == 1:
            return choices[0]
        size = self.length[choices[0]]
        assert all(self.length[i] == size for i in choices)
        return self._intern(('choice', *choices), size)

    def word(self, word):
        nodes = [self.literal(e) for e in word]
        while len(nodes) > 1:
            paired = [self.join(a, b) for a, b in zip(nodes[::2], nodes[1::2])]
            nodes = paired + (nodes[-1:] if len(nodes) % 2 else [])
        return nodes[0] if nodes else self.empty_word

    def rectangle(self, rows, cols):
        # Both axes are already in processing order.
        pieces = {}
        for h in range(1, len(rows) + 1):
            for w in range(1, len(cols) + 1):
                for i in range(len(rows) - h + 1):
                    for j in range(len(cols) - w + 1):
                        if h == w == 1:
                            node = self.literal((rows[i], cols[j]))
                        else:
                            cuts = [self.join(pieces[i,j,a,w], pieces[i+a,j,h-a,w])
                                    for a in range(1, h)]
                            cuts.extend(self.join(pieces[i,j,h,b], pieces[i,j+b,h,w-b])
                                        for b in range(1, w))
                            node = self.choice(cuts)
                        pieces[i,j,h,w] = node
        return pieces[0,0,len(rows),len(cols)]

    @staticmethod
    def _evaluate(key, production):
        """Sparse acyclic tabulation, including for deeply nested grammars."""
        table = {}
        stack = [(key, production(key, table))]
        while stack:
            current, work = stack[-1]
            try:
                dep = next(work)
            except StopIteration as result:
                table[current] = result.value
                stack.pop()
            else:
                if dep not in table:
                    stack.append((dep, production(dep, table)))
        return table[key]

    def image(self, root, initial, step, accepts):
        """Transducer image; an arc may output another grammar node."""
        def production(key, table):
            node, state = key
            rule = self.nodes[node]
            outputs = defaultdict(list)
            if rule[0] == 'empty_word':
                return {state: self.empty_word}
            if rule[0] == 'literal':
                for end, output in step(state, rule[1]):
                    outputs[end].append(output)
            elif rule[0] == 'choice':
                for child in rule[1:]:
                    yield child, state
                    for end, output in table[child,state].items():
                        outputs[end].append(output)
            else:
                _, left, right = rule
                yield left, state
                for middle, prefix in table[left,state].items():
                    yield right, middle
                    for end, suffix in table[right,middle].items():
                        outputs[end].append(self.join(prefix, suffix))
            return {end: self.choice(forms) for end, forms in outputs.items()}

        ends = self._evaluate((root, initial), production)
        return self.choice(node for state, node in ends.items() if accepts(state))

    def contains(self, root, word):
        if self.length[root] != len(word):
            return False

        return self.accepts_positions(root, lambda pos, event: word[pos] == event)

    def accepts_positions(self, root, permits):
        """Match one positional constraint per terminal without listing words."""
        def match(key, table):
            node, pos = key
            rule = self.nodes[node]
            if rule[0] == 'empty_word':
                return True
            if rule[0] == 'literal':
                return permits(pos, rule[1])
            if rule[0] == 'choice':
                for child in rule[1:]:
                    yield child, pos
                    if table[child,pos]:
                        return True
                return False
            _, left, right = rule
            yield left, pos
            if not table[left,pos]:
                return False
            second = pos + self.length[left]
            yield right, second
            return table[right,second]

        return self._evaluate((root, 0), match)

    def exposes(self, root, support):
        """Does a word contain the entire support as one contiguous factor?"""
        def summary(node, table):
            rule = self.nodes[node]
            if rule[0] == 'empty_word':
                return 0, 0, 0
            if rule[0] == 'literal':
                hit = int(rule[1] in support)
                return hit, hit, hit
            for child in rule[1:]:
                yield child
            if rule[0] == 'choice':
                return tuple(map(max, zip(*(table[i] for i in rule[1:]))))
            _, left, right = rule
            lp, ls, longest_left = table[left]
            rp, rs, longest_right = table[right]
            return (lp + rp if lp == self.length[left] else lp,
                    rs + ls if rs == self.length[right] else rs,
                    max(longest_left, longest_right, ls + rp))

        return self._evaluate(root, summary)[2] == len(support)


def square_positions(word):
    """First-use round of each mobile pair in a typed sorting word."""
    mobile = {}
    for depth in (1, 2, 3):
        fresh = {}
        for i in range(1, len(word)-2):
            if any(j in mobile for j in (i-1, i, i+1)):
                continue
            x, y = word[i:i+2]
            a, b = x
            c, d = y
            if len({a,b,c,d}) != 4 or max(a,c) >= min(b,d):
                continue
            left = word[i-2:i] if i-2 in mobile else word[i-1:i]
            right = word[i+2:i+4] if i+2 in mobile else word[i+2:i+3]
            if any(f in left and l in right
                   for f,l in (((a,d),(c,b)), ((c,b),(a,d)))):
                fresh[i] = depth
        if not fresh:
            break
        mobile.update(fresh)
    return mobile


def square_signature(word):
    word = tuple(tuple(e) for e in word)
    mobile = square_positions(word)
    return tuple(tuple(sorted(word[i:i+2])) if i in mobile else
                 () if i-1 in mobile else (event,) for i, event in enumerate(word))


def square_closure(grammar, root):
    # A chunk copies one event or exchanges two. Keep the preceding chunk
    # to check the shared guard before allowing the next chunk to finish.
    start = ('start',)

    def step(state, event):
        if state[0] == 'pending':
            _, previous, x = state
            y = event
            a, b = x
            c, d = y
            if len({a,b,c,d}) != 4 or max(a,c) >= min(b,d):
                return
            for first, last in (((a,d),(c,b)), ((c,b),(a,d))):
                if previous[0] == 'fixed':
                    legal = previous[1] == first
                else:
                    _, prev_x, prev_y, prev_last = previous
                    left_first = prev_last == x and prev_x == first
                    right_first = prev_y == first and prev_last == y
                    legal = left_first or right_first
                if legal:
                    yield ('flip', x, y, last), grammar.join(grammar.literal(y), grammar.literal(x))
        else:
            if state[0] != 'flip' or state[3] == event:
                yield ('fixed', event), grammar.literal(event)
            if state != start:
                yield ('pending', state, event), grammar.empty_word

    return grammar.image(root, start, step, lambda s: s[0] in ('start', 'fixed'))


def wide_layer(grammar, root, boxes):
    # The first event of a full factor is its northwest corner. All input
    # words are reachable, so its projected spelling already passes the
    # binary expansion test for every candidate from the original word.
    starts = defaultdict(list)
    replacements = {}
    for box, (rows, cols) in boxes.items():
        starts[rows[0],cols[0]].append(box)
    def step(state, event):
        if state is None:
            yield None, grammar.literal(event)
            for box in starts[event]:
                yield (box, len(box) - 1), grammar.empty_word
        else:
            box, remaining = state
            if event in box:
                if remaining == 1:
                    if box not in replacements:
                        replacements[box] = grammar.rectangle(*boxes[box])
                    yield None, replacements[box]
                else:
                    yield (box, remaining - 1), grammar.empty_word

    return grammar.image(root, None, step, lambda s: s is None)


class SortingLayers:
    def __init__(self, word):
        word = tuple(tuple(e) for e in word)
        self.boxes = {s: axes for s, axes in candidates(word)[1].items() if len(s) > 4}
        self.grammar = HistoryGrammar()
        self.root = square_closure(self.grammar, self.grammar.word(word))

    def advance(self):
        self.root = square_closure(self.grammar, wide_layer(self.grammar, self.root, self.boxes))

    def contains(self, word):
        return self.grammar.contains(self.root, tuple(tuple(e) for e in word))

    def exposed_boxes(self):
        return {s for s in self.boxes if self.grammar.exposes(self.root, s)}


def parallel_component(word):
    """Recognize components covered by simultaneously exposed disjoint boxes.

    On success the returned grammar describes the whole equality class.
    """
    word = tuple(tuple(e) for e in word)
    layers = SortingLayers(word)
    exposed = layers.exposed_boxes()
    maximal = [box for box in exposed if not any(box < other for other in exposed)]
    if not maximal:
        return layers
    covered = set()
    required = {}
    for box in maximal:
        if not covered.isdisjoint(box):
            return None
        covered.update(box)
        rows, cols = layers.boxes[box]
        first = word.index((rows[0], cols[0]))
        for start in range(max(0, first-1), min(first+1, len(word)-len(box)) + 1):
            def permits(pos, event):
                return not start <= pos < start + len(box) or event in box

            if layers.grammar.accepts_positions(layers.root, permits):
                break
        else:
            raise AssertionError("An exposed rectangle needs its first corner")
        for i in range(start, start+len(box)):
            if i in required:
                return None
            required[i] = box
    if not layers.grammar.accepts_positions(
            layers.root, lambda i, e: i not in required or e in required[i]):
        return None
    layers.advance()
    for box in layers.boxes:
        if (not any(box <= region for region in maximal)
                and layers.grammar.exposes(layers.root, box)):
            return None
    return layers
