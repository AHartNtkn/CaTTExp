"""Equality of binary row-word grammars for two-chain rectangular subdivision.

Row numbers increase in processing order. initial[r] is the number of columns
already crossed in row r, so initial is weakly decreasing. The alphabet of
rows is explicit; the column numbers and expanded lengths can be exponential.
"""

from dataclasses import dataclass

from interchange_shared_whiskers import Words


@dataclass(frozen=True)
class Block:
    lo: int
    hi: int
    width: int

    @property
    def area(self):
        return (self.hi - self.lo) * self.width


class Records:
    """SLPs of block labels or blanks, indexed by their atomic area."""

    def __init__(self):
        self.nodes = [()]
        self.weight = [0]
        self.ids = {(): 0}

    def _add(self, rule, weight):
        if rule not in self.ids:
            self.ids[rule] = len(self.nodes)
            self.nodes.append(rule)
            self.weight.append(weight)
        return self.ids[rule]

    def blank(self, length):
        return self._add(('blank', length), length) if length else 0

    def label(self, block):
        return self._add(('block', block), block.area)

    def join(self, a, b):
        if not a or not b:
            return a or b
        return self._add(('join', a, b), self.weight[a] + self.weight[b])

    def at(self, node, i):
        while self.nodes[node][0] == 'join':
            _, a, b = self.nodes[node]
            if i < self.weight[a]:
                node = a
            else:
                i -= self.weight[a]
                node = b
        tag, block = self.nodes[node]
        assert tag == 'block'
        return block, i

    def cut(self, node, k, prefix):
        """Keep [0,k) or [k,end); a cut may land inside a blank."""
        pieces = []
        while 0 < k < self.weight[node]:
            rule = self.nodes[node]
            if rule[0] == 'blank':
                node = self.blank(k if prefix else self.weight[node]-k)
                break
            assert rule[0] == 'join'
            _, a, b = rule
            if k < self.weight[a]:
                if not prefix:
                    pieces.append(b)
                node = a
            else:
                if prefix:
                    pieces.append(a)
                k -= self.weight[a]
                node = b
        else:
            if (prefix and k == 0) or (not prefix and k == self.weight[node]):
                node = 0
        for part in reversed(pieces):
            node = self.join(part, node) if prefix else self.join(node, part)
        return node

    def spell(self, roots, words, labels):
        """One label at the block start; pad its remaining area with zeros."""
        powers = [words.letter(0)]
        def zeros(count):
            result = 0
            while len(powers) < count.bit_length():
                powers.append(words.join(powers[-1], powers[-1]))
            for bit in range(count.bit_length()):
                if count >> bit & 1:
                    result = words.join(result, powers[bit])
            return result
        used = set()
        pending = list(roots)
        while pending:
            i = pending.pop()
            if i in used:
                continue
            used.add(i)
            if i and self.nodes[i][0] == 'join':
                pending.extend(self.nodes[i][1:])
        values = {0: 0}
        for i in sorted(used - {0}):
            tag, *args = self.nodes[i]
            if tag == 'join':
                values[i] = words.join(values[args[0]], values[args[1]])
            elif tag == 'blank':
                values[i] = zeros(self.weight[i])
            else:
                label = labels.setdefault(args[0], len(labels)+1)
                values[i] = words.join(words.letter(label), zeros(self.weight[i]-1))
        return tuple(values[i] for i in roots)


def bands(heights, need, lo, hi):
    """Active row component at each row of this interval."""
    result = {}
    start = lo
    for i in range(lo, hi):
        if i+1 < hi:
            difference = heights[i] - heights[i+1]
            if difference < need[i]:
                raise ValueError('row schedule crosses an unavailable column')
            if difference == need[i]:
                continue
        result.update(dict.fromkeys(range(start,i+1), (start,i+1)))
        start = i+1
    return result


class Tableaux:
    def __init__(self, raw, rows):
        self.raw = raw
        self.rec = Records()
        self.rows = rows
        self.counts = []
        self.need = []
        self.codes = {}
        for i, rule in enumerate(raw.rules):
            if len(rule) == 2:
                a, b = (~j for j in rule)
                left, right = self.counts[a], self.counts[b]
                count = tuple(x+y for x,y in zip(left, right))
                required = tuple(max(self.need[a][r], self.need[b][r]-left[r]+left[r+1])
                                 for r in range(rows-1))
            else:
                if rule and not 0 <= rule[0] < rows:
                    raise ValueError('unknown row')
                count = tuple(int(bool(rule) and rule[0] == r) for r in range(rows))
                required = tuple(max(0,count[r+1]-count[r]) for r in range(rows-1))
            self.counts.append(count)
            self.need.append(required)
            for lo in range(rows):
                for hi in range(lo+1, rows+1):
                    if len(rule) == 2:
                        self._junction(i, a, b, lo, hi)
                    else:
                        for row in range(lo, hi):
                            value = self.rec.blank(int(bool(rule)))
                            if rule and row == rule[0]:
                                value = self.rec.label(Block(row, row+1, 1))
                            self.codes[i,lo,hi,row] = value

    def _row_at(self, node, pos):
        while len(self.raw.rules[node]) == 2:
            a,b = (~i for i in self.raw.rules[node])
            if pos < self.raw.length[a]:
                node = a
            else:
                pos -= self.raw.length[a]
                node = b
        return self.raw.rules[node][0]

    def _count_before(self, node, row, pos):
        result = 0
        while 0 < pos < self.raw.length[node]:
            a,b = (~i for i in self.raw.rules[node])
            if pos < self.raw.length[a]:
                node = a
            else:
                pos -= self.raw.length[a]
                result += self.counts[a][row]
                node = b
        return result + (self.counts[node][row] if pos else 0)

    def _junction(self, node, a, b, lo, hi):
        # Only differences within [lo,hi) matter. Set its last height to zero.
        base = {hi-1: 0}
        for row in reversed(range(lo, hi-1)):
            base[row] = base[row+1] + self.need[node][row]
        later = {r: base[r]+self.counts[a][r] for r in base}
        left = bands(base, self.need[a], lo, hi)
        right = bands(later, self.need[b], lo, hi)
        boundary = self.raw.length[a]
        length = self.raw.length[node]

        def child_at(child, partition, pos):
            row = self._row_at(child,pos)
            if row not in partition:
                return None
            code = self.codes[child,*partition[row],row]
            return self.rec.at(code,pos)[0]

        def merged(x, y, start):
            if x is None or y is None:
                return None
            if (x.lo,x.hi) == (y.lo,y.hi):
                return Block(x.lo,x.hi,x.width+y.width)
            if x.hi == y.lo and x.width == y.width:
                xcol = base[x.lo] + self._count_before(node,x.lo,start)
                ycol = base[y.lo] + self._count_before(node,y.lo,start)
                if xcol == ycol:
                    return Block(x.lo,y.hi,x.width)
            return None

        x = child_at(a,left,boundary-1)
        y = child_at(b,right,0)
        start = boundary - x.area if x is not None else boundary
        center = merged(x,y,start)
        if center is not None:
            end = boundary + y.area
            while True:
                if start:
                    x = child_at(a,left,start-1)
                    if x is not None:
                        combined = merged(x,center,start-x.area)
                        if combined is not None:
                            start -= x.area
                            center = combined
                            continue
                if end < length:
                    y = child_at(b,right,end-boundary)
                    combined = merged(center,y,start)
                    if combined is not None:
                        center = combined
                        end += y.area
                        continue
                break
        for r in range(lo, hi):
            p = self.codes[a,*left[r],r]
            q = self.codes[b,*right[r],r]
            if center is not None:
                p = self.rec.cut(p, start, True)
                q = self.rec.cut(q, end-boundary, False)
                mid = (self.rec.label(center) if center.lo <= r < center.hi
                       else self.rec.blank(center.area))
                p = self.rec.join(p,mid)
            self.codes[node,lo,hi,r] = self.rec.join(p,q)

    def coordinates(self, node, initial):
        if len(initial) != self.rows or any(h < 0 for h in initial):
            raise ValueError('expected one nonnegative initial column count per row')
        parts = bands(initial, self.need[node], 0, self.rows)
        return tuple(self.codes[node,*parts[r],r] for r in range(self.rows))

    def equal(self, a, b, initial):
        x,y = (self.coordinates(i,initial) for i in (a,b))
        if self.counts[a] != self.counts[b]:
            return False
        words, names = Words(), {}
        p,q = (self.rec.spell(roots,words,names) for roots in (x,y))
        return all(words.equal(i,j) for i,j in zip(p,q))
