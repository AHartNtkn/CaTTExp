"""Reconstruct temporal chart strings and their refinements in the nullary four-prism."""

from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product
from math import comb

from fibration_factor_search import Rule, Stage


def old_comparison_window():
    names = {label: Rule('x',s,t) for label,s,t in (
        ('u','','t'),('h','','g'),('c','gt','tg'),('D','t','tg'),('M','g','tg'),('X','','tg'))}
    stage = Stage({'g':('x','x'),'t':('x','x')},names)
    words = [''.join(w) for k in range(3) for w in product('tg',repeat=k)]
    unary = Counter()
    for w, z in product(words,repeat=2):
        assert not list(stage.backwards('x', w, z, {'D','M','X'}, 2))
        groups, _ = stage.quotient(stage.backwards('x', w, z, {'D','M','X'}, 1))
        for group in groups:
            slot, = [g for g,_ in group[0] if g in {'D','M','X'}]
            unary[w,z,slot] += 1
    assert unary == Counter({('','tg','D'):1, ('','tg','M'):1, ('','tg','X'):1,
                             ('g','tg','M'):1, ('t','tg','D'):1})
    print(f'{len(words)**2} pairs of lower word poles; five unary charts and no binary charts.')


@cache
def weak_compositions(n,k):
    if k == 1:
        return [(n,)]
    return [(i,)+rest for i in range(n+1) for rest in weak_compositions(n-i,k-1)]


def ordered_partitions(items):
    if not items:
        yield ()
        return
    for n in range(1,len(items)+1):
        for first in combinations(items,n):
            for remainder in ordered_partitions(tuple(i for i in items if i not in first)):
                yield (first,) + remainder


def check_window(r, added):
    # A decorated temporal bead is a word in ordinary DM tokens and ordered X
    # markers in their gaps. Expanding all X to DM makes the next 3-state.
    groups = defaultdict(dict)
    def visit(state, remaining, beads):
        if remaining == 0:
            injection = tuple(i for i,step in enumerate(state) if step == -1)
            partition = tuple(tuple(i for i,step in enumerate(state) if step == t)
                              for t in range(len(beads)))
            assert partition not in groups[injection]
            groups[injection][partition] = beads
            return
        for n in range(1,remaining+1):
            for gaps in weak_compositions(n,len(state)+1):
                after = []
                for j,k in enumerate(gaps):
                    after.extend([len(beads)]*k)
                    if j < len(state):
                        after.append(state[j])
                visit(after,remaining-n,beads+(gaps,))
    visit([-1]*r, added, ())
    assert len(groups) == comb(r+added,r)
    for injection, flags in groups.items():
        free = tuple(i for i in range(r+added) if i not in injection)
        assert set(flags) == set(ordered_partitions(free))
        # Verify actual ordered restrictions of every bead, not just the counts.
        for partition,beads in flags.items():
            for time,block in enumerate(partition):
                old = sorted(set(injection).union(*partition[:time]))
                for n in range(1,len(block)):
                    for early in combinations(block,n):
                        late = tuple(i for i in block if i not in early)
                        def restrictions(positions, current):
                            gaps = [0]*(len(current)+1)
                            for i in positions:
                                gaps[sum(j < i for j in current)] += 1
                            return tuple(gaps)
                        a = restrictions(early,old)
                        b = restrictions(late,sorted(old+list(early)))
                        refined = partition[:time]+(early,late)+partition[time+1:]
                        assert flags[refined] == beads[:time]+(a,b)+beads[time+1:]
    return len(groups), sum(map(len,groups.values()))


if __name__ == '__main__':
    old_comparison_window()
    totals = [check_window(r,k) for r in range(4) for k in range(5)]
    print(f'{sum(x for x,y in totals)} strict injections, {sum(y for x,y in totals)} '
          'chart strings, all ordered refinements verified.')
