"""Two base-pad readers lifted through shared rigid paths of arbitrary rank.

The prepared input has classified head names, classified fixed contexts below
the base, and typed base-pad SLPs. Compare upper paths at a common source.
Each reader supplies run(state, word) and finish(state) as in GridReader.
"""

from interchange_rigid_group import RigidGroup


class ReaderCodes:
    def __init__(self, rules, reader, base_rank, reverse):
        self.rules = rules
        self.reader = reader
        self.base_rank = base_rank
        self.reverse = reverse
        self.group = RigidGroup()
        self.emitted = {0: self.group.unit}
        self.values = {}

    def output_code(self, word):
        """Embed the reader's output SLP into the base free subgroup."""
        stack = [word]
        while stack:
            root = stack[-1]
            if root in self.emitted:
                stack.pop()
                continue
            rule = self.reader.output.rules[root]
            if len(rule) == 1:
                value = self.group.head(self.base_rank, rule[0])
            else:
                a, b = (~ref for ref in rule)
                if a not in self.emitted or b not in self.emitted:
                    stack.append(a if a not in self.emitted else b)
                    continue
                value = self.group.join(self.emitted[a], self.emitted[b])
            self.emitted[root] = value
        return self.emitted[word]

    def value(self, root, initial=()):
        stack = [(root, initial)]
        while stack:
            key = stack[-1]
            if key in self.values:
                stack.pop()
                continue
            node, state = key
            rule = self.rules[node]
            kind = rule[0]
            if kind == 'empty':
                result = self.group.unit
            elif kind == 'head':
                _, rank, name = rule
                suffix = self.output_code(self.reader.finish(state))
                result = self.group.left_action(suffix, self.group.head(rank, name))
            elif kind == 'base':
                _, left, child, right = rule
                next_state, out = self.reader.run(state, right if self.reverse else left)
                dep = child, next_state
                if dep not in self.values:
                    stack.append(dep)
                    continue
                result = self.group.left_action(self.output_code(out), self.values[dep])
            elif kind == 'right':
                _, child, _pad = rule
                dep = child, state
                if dep not in self.values:
                    stack.append(dep)
                    continue
                result = self.values[dep]
            elif kind in ('join', 'left'):
                a, b = (rule[1], state), (rule[2], state)
                if a not in self.values or b not in self.values:
                    stack.append(a if a not in self.values else b)
                    continue
                op = self.group.join if kind == 'join' else self.group.left_action
                result = op(self.values[a], self.values[b])
            else:
                raise ValueError(f'unknown rigid instruction {kind!r}')
            self.values[key] = result
        return self.values[root, initial]

    def equal_coordinate(self, a, b, initial=()):
        return self.group.equal_at_source(self.value(a, initial), self.value(b, initial))


class Occurrences:
    """Descend to one nested field using original references and exterior actions.

    This prepared grammar has incorporated actions below the base. A base
    operand is a raw-word reference, and an upper pad is another path node.
    Empty nodes have the degree required at their occurrence.
    """

    def __init__(self, rules, base_rank):
        self.rules = rules
        self.base_rank = base_rank
        self.count = []
        self.degree = []
        for rule in rules:
            kind = rule[0]
            if kind == 'head':
                size, degree = 1, rule[1]
            elif kind == 'empty':
                size, degree = 0, None
            elif kind == 'join':
                a, b = rule[1:]
                size, degree = self.count[a]+self.count[b], self.degree[a] or self.degree[b]
            else:
                child = rule[2] if kind in ('left', 'base') else rule[1]
                size, degree = self.count[child], self.degree[child]
            self.count.append(size)
            self.degree.append(degree)

    def occurrence(self, field, index):
        """A field is an ordered list of (path node, inherited action list)."""
        if index < 0:
            raise IndexError(index)
        for node, inherited in field:
            if index < self.count[node]:
                break
            index -= self.count[node]
        else:
            raise IndexError(index)
        actions = list(inherited)
        while True:
            rule = self.rules[node]
            kind = rule[0]
            if kind == 'head':
                return rule[1:], actions
            if kind == 'join':
                left, right = rule[1:]
                if index < self.count[left]:
                    node = left
                else:
                    index -= self.count[left]
                    node = right
            elif kind == 'base':
                left, node, right = rule[1:]
                actions.extend(((self.base_rank, 'left', left), (self.base_rank, 'right', right)))
            else:
                if kind == 'left':
                    _, pad, child = rule
                else:
                    _, child, pad = rule
                if self.count[pad]:
                    actions.append((self.degree[pad], kind, pad))
                node = child

    @staticmethod
    def field(actions, degree, side):
        result = [(pad, tuple(a for a in actions[:i] if a[0] < degree))
                  for i, (rank, which, pad) in enumerate(actions)
                  if rank == degree and which == side]
        return result if side == 'left' else result[::-1]
