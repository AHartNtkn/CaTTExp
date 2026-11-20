"""Check binary charts on a genuine 3-cycle and records on mixed globe boundaries."""

from collections import Counter
from itertools import product

from fibration_factor_search import Rule, Stage
from gray_globe_comparison import atom


def charts():
    rules = {label: Rule('x', s, t) for label, s, t in (
        ('u', '', 't'), ('h', '', 'g'), ('c', 'gt', 'tg'),
        ('D', 't', 'tg'), ('M', 'g', 'tg'))}
    stage = Stage({c: ('x', 'x') for c in 'gt'}, rules)

    def marked(source, target, slots):
        cells, _ = stage.quotient(stage.backwards('x', source, target, {'D', 'M'}, slots))
        return [tuple(sorted(g for g,_ in c[0] if g in ('D','M'))) for c in cells]

    assert Counter(marked('', 'tg', 0)) == {(): 2}
    assert Counter(marked('', 'tg', 1)) == {('D',): 1, ('M',): 1}
    assert not marked('', 'tg', 2)
    # At different outer poles the same stage admits a genuine simultaneous chart.
    pairs = marked('tt', 'tgtg', 2)
    assert ('D','D') in pairs
    print(f'Circuit poles: two states, two unary charts, no binary charts. '
          f'Parallel control: {len(pairs)} binary charts.')


def records(k, source, target):
    top = atom(((2, 2), (k, 2)))
    arrow_images = {0: source, 1: target}
    ends = []
    for row in top[-2]:
        # The proper-fibre part records exactly the fibre arrow over this base occurrence.
        ends.append(''.join(arrow_images[side] for (j,side), base in row
                            if j == 1 and base == (k,2)))
    assert ends == [source, target]
    return ends


def check_records():
    # The fibre admits 1 -> g and g -> g. It has unbounded histories after g,
    # and has no nonidentity 2-cell taking the empty word to itself.
    checks = 0
    for k in range(1, 10):
        rules = [records(k, '', 'g'), records(k, 'g', 'g')]
        for s, t in rules:
            for left, right in product(range(4), repeat=2):
                a, b = 'g'*left+s+'g'*right, 'g'*left+t+'g'*right
                assert b and (not a or len(b) >= len(a))
                checks += 1
        # Reversing the creating generator's fibre boundary enables a return to empty.
        reverse = records(k, 'g', '')
        assert rules[0][1] == reverse[0] and reverse[1] == rules[0][0]
    print(f'{checks} contextual record transitions through total rank 11; '
          'the nonempty self-loop persists and a return to empty requires the extra rule.')


if __name__ == '__main__':
    charts()
    check_records()
