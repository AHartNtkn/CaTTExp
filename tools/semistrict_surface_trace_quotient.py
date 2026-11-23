"""Test generated square-quotient pastes while retaining ordered private updates.

The default test is the concrete degree-six old boundary of Response 117.
Successful searches produce native-atom pastes internally. A negative search
exhausts top composition and both directions of whiskering at every lower cut.
"""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations

from gray_globe_comparison import atom
from semistrict_surface_branched_comparisons import certificate_rows
from semistrict_surface_generated_quotient import Chart, Pasting, only_these_rows


class Traces:
    def __init__(self,chart):
        self.chart = chart
        self.spans = []
        self.steps = []
        for w in chart.layers[2]:
            lo,hi = [],[]
            for d,x in w:
                lo.append(x[0] if d else x)
                hi.append(x[0]+1 if d else x)
            self.spans.append((lo,hi))
            self.steps.append(chart.boundary(w))
        assert all(not g or g==((i,1),) for i,g in enumerate(chart.generators[2]))
        self.atomic = defaultdict(set)
        for r,layer in enumerate(chart.layers[:-1]):
            for i,w in enumerate(layer):
                raw = atom(w,chart.boundary)
                self.atomic[chart.atom_table(r,i)].add(self.read(raw))

    @cache
    def commute(self,a,b):
        lo,hi = self.spans[a]
        start,end = self.spans[b]
        return all(x<=y for x,y in zip(hi,start)) or all(x<=y for x,y in zip(end,lo))

    @cache
    def normal(self,word):
        remaining = list(word)
        out = []
        while remaining:
            _,i = min((a,i) for i,a in enumerate(remaining)
                      if all(self.commute(a,b) for b in remaining[:i]))
            out.append(remaining.pop(i))
        return tuple(out)

    def reading(self,src,steps,tgt):
        if not steps:
            return () if src==tgt else None
        for j,i in enumerate(steps):
            delta = self.steps[i]
            if any(src[f]<1 for f,n in delta.items() if n<0):
                continue
            state = src.copy()
            state.update(delta)
            later = self.reading(state,steps[:j]+steps[j+1:],tgt)
            if later is not None:
                return ((i,) if self.chart.generators[2][i] else ())+later
        return None

    def read(self,rows):
        if len(rows)<3:
            return ((),())
        traces = []
        for face in rows[2]:
            indices = tuple(self.chart.indices[2][w] for w in face)
            word = self.reading(Counter(rows[1][0]),indices,Counter(rows[1][1]))
            if word is None:
                raise ValueError('invalid old two-row')
            traces.append(self.normal(word))
        return tuple(traces)

    @cache
    def possibilities(self,row):
        letters = tuple(i for i,n in row for _ in range(n))
        return tuple(sorted({self.normal(w) for w in permutations(letters)}))

    @cache
    def split(self,word,first_row):
        needed = dict(first_row)
        first,last = [],[]
        for i in word:
            if needed.get(i,0):
                first.append(i)
                needed[i] -= 1
            else:
                last.append(i)
        if any(needed.values()) or self.normal(tuple(first+last))!=word:
            return None
        return self.normal(tuple(first)),self.normal(tuple(last))


def row_two(cell,side):
    return cell[2][side] if len(cell)>2 else ()


class TracePasting:
    def __init__(self,chart,from_target=False):
        self.plain = Pasting(chart,from_target=from_target)
        self.traces = Traces(chart)
        self.visited = 0

    def decorations(self,cut,left,desired):
        if cut>2:
            yield desired,desired
        elif cut==2:
            for seam in self.traces.possibilities(row_two(left,1)):
                yield (desired[0],seam),(seam,desired[1])
        else:
            a = self.traces.split(desired[0],row_two(left,0))
            b = self.traces.split(desired[1],row_two(left,1))
            if a is not None and b is not None:
                yield (a[0],b[0]),(a[1],b[1])

    @cache
    def generated(self,c,trace):
        self.visited += 1
        if trace in self.traces.atomic.get(c,()):
            return True
        if c[-1]==((),()) and len(c)>1:
            return self.generated(c[:-1],trace)
        if len(c)<3 and trace!=((),()):
            return False
        if len(c)==3 and trace[0]!=trace[1]:
            return False
        for k,a,b in self.plain.splits(c):
            for first,second in self.decorations(k,a,trace):
                pieces = ((b,second),(a,first)) if self.plain.from_target else ((a,first),(b,second))
                if all(self.generated(cell,marks) for cell,marks in pieces):
                    return True
        return False


def reduced_checks():
    # Independently close all strict two-cells of a small quotient under both
    # cuts. Compare every decoration of every resulting underlying tableau.
    from semistrict_surface_generated_quotient import compose
    chart = Chart([[[[]]],[[[]]]],2)
    search = TracePasting(chart)
    cells = set()
    for rows,decorations in search.traces.atomic.items():
        for t in decorations:
            cells.add((rows+(((),()),)*(3-len(rows)),t[0]))
    while True:
        additional = set()
        for c,x in cells:
            for d,y in cells:
                for k in (0,1):
                    if c[:k]!=d[:k] or c[k][1]!=d[k][0]:
                        continue
                    joined = compose(c,d,k)
                    additional.add((joined,search.traces.normal(x+y)))
        if additional<=cells:
            break
        cells |= additional
    checked = 0
    for c in {c for c,x in cells}:
        for t in search.traces.possibilities(c[2][0]):
            assert search.generated(c,(t,t))==((c,t) in cells)
            checked += 1
    return checked


def run():
    print(f'{reduced_checks()} small trace judgments checked by independent forward closure',flush=True)
    chart = Chart([[[[]]],[[[[]],[[]]]],[[[]]]],5)
    search = TracePasting(chart)
    raw = tuple(tuple(tuple(chart.layers[r][i] for i in s) for s in pair)
                for r,pair in enumerate(certificate_rows()))
    old = tuple(tuple(chart.row(r,s) for s in pair) for r,pair in enumerate(certificate_rows()))
    trace = search.traces.read(raw)
    assert trace==((0,8,12,52),(55,27,31,17))
    # Positive controls at both exact old faces.
    for face in old[4]:
        assert search.generated(old[:4]+((face,face),),trace)
    choices = [[5,8,14,19,k,23,30] for k in (20,21,22)]
    assert only_these_rows(chart,old[-1],choices)
    for s in choices:
        top = chart.row(5,s)
        assert not search.generated(old+((top,top),),trace)
        print(f'Excluded top row {s} at the two old traces',flush=True)
    print(f'{search.visited:,} distinct decorated tableau states checked')


if __name__=='__main__':
    run()
