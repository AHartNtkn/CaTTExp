"""Exact individual private mark transport in scalar braids of any width.

With --faces FILE decides the full judgment when the order of updates agrees.
For different orders a failed individual test still excludes a filler.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path

from semistrict_surface_planar_tiers import artin_step, reduce_letters
from semistrict_surface_private_winding import solve as winding
from semistrict_surface_shared_edge import inverse


def prod(*words):
    return reduce_letters(x for w in words for x in w)


def content(word):
    result = Counter()
    for x in word:
        result[abs(x)] += 1 if x > 0 else -1
    return {e: k for e, k in result.items() if k}


def quasi(word):
    """Deletion of positive letters with noncrossing inverse pairs on the rest."""
    if any(k < 0 for k in content(word).values()):
        return False
    n = len(word)
    ends = [{i} for i in range(n+1)]
    for i in reversed(range(n)):
        if word[i] > 0:
            ends[i].update(ends[i+1])
        for j in ends[i+1]:
            if j < n and word[j] == -word[i]:
                ends[i].update(ends[j+1])
    return n in ends[0]


@dataclass(frozen=True)
class Cut:
    before: tuple
    atom: tuple

    @property
    def after(self):
        return prod(self.before, self.atom)


def meridian(atom):
    k = len(atom)//2
    assert len(atom) == 2*k+1 and atom[k] > 0 and atom[k+1:] == inverse(atom[:k])
    return atom[:k], atom[k]


def cuts(n, movie):
    frame = tuple((i+1,) for i in range(n))
    counts, marks = defaultdict(int), {}
    for label, i in movie:
        if label == 'X':
            frame = artin_step(frame, i)
        else:
            _, e = meridian(frame[i])
            marks[e, counts[e]] = Cut(prod(*frame[:i]), frame[i])
            counts[e] += 1
    return marks, frame


def transport(source, target):
    u, e = meridian(source.atom)
    v, f = meridian(target.atom)
    if e != f:
        return False
    # Every conjugator from u e u^-1 to v e v^-1 has form u e^d v^-1.
    # Gained strands exclude e, forcing its e-coordinate to vanish.
    d = content(v).get(e, 0)-content(u).get(e, 0)
    negative = prod(u, ((e if d >= 0 else -e),)*abs(d), inverse(v))
    total = prod(inverse(source.after), target.after)
    positive = prod(inverse(negative), total)
    gained = content(total)
    if e in gained or any(k != 1 for k in gained.values()):
        return False
    return quasi(negative) and quasi(positive)


def compatible(s, t):
    # Insert the missing factors between the two marked cuts in one frame.
    def precedes(x, y):
        return quasi(prod(inverse(x.after), y.before))
    return meridian(s.atom)[1] != meridian(t.atom)[1] and (precedes(s, t) or precedes(t, s))


def solve(data):
    base = winding(data)
    if base['obstruction']:
        return base
    if any(any(data['marks'][a]) for _, a in data['history']) or len({p for p, _ in data['history']}) > 1:
        raise ValueError('expected scalar events at one common spatial gap')
    n = len(data['history'])
    left, a = cuts(n, data['source'])
    right, b = cuts(n, data['target'])
    if a != b:
        return dict(surface_filler=False, obstruction='total braid')
    for key in left:
        if not transport(left[key], right[key]):
            return dict(surface_filler=False, obstruction='meridian transport', mark=key)
    order = {mark: i for i, mark in enumerate(right)}
    inversions = [(e, f) for i, e in enumerate(left) for f in tuple(left)[i+1:]
                  if order[e] > order[f]]
    # At fixed checkpoints, a pair commutes exactly when they share a frame.
    # These two complete endpoint reorderings give additional positive answers.
    if any(all(compatible(c[e], c[f]) for e, f in inversions) for c in (left, right)):
        return dict(surface_filler=True)
    if all(left[e] == right[e] for e in left):
        return dict(surface_filler=False, obstruction='stationary update order')
    return dict(surface_filler=None, reason='intermediate update commutations')


def checks():
    from semistrict_surface_private_three_windings import solve as three
    from semistrict_surface_single_power import spellings
    from semistrict_surface_private_braid_windows import factor, join
    from semistrict_surface_signed_private_model import Ball
    from semistrict_surface_private_histories import closure
    from semistrict_surface_shared_edge import braid_image
    data = dict(edges={}, initial=[], start_vertex=0, scalar_at={'s': 0},
                marks={'s': [[], []]}, higher=[{'p': ['s', 's']}], history=[(0, 's')]*3)
    beta = (1, 2, 1)*2
    records = {}
    for path in spellings(beta):
        for k in range(len(path)+1):
            for i in range(3):
                movie = [('X', x-1) for x in path]
                movie.insert(k, ('p', i))
                cuts_at, _ = cuts(3, movie)
                key, cut = next(iter(cuts_at.items()))
                records[key, cut] = movie
    pairs = 0
    for (m, a), s in records.items():
        for (q, b), t in records.items():
            if m != q:
                continue
            expected = three(dict(data, source=s, target=t))['surface_filler']
            assert transport(a, b) == expected
            pairs += 1

    # Compare signed four-event paths against the unrestricted cut test. Every
    # ball witness must pass. Negative answers are independent of ball radius.
    n = 4
    ball = Ball(((0, 's'),)*n, data['marks'], 3)
    frames = [braid_image(n, path) for path in ball.paths]
    instances = {}
    for h, frame in enumerate(frames):
        for i in range(n):
            cut = Cut(prod(*frame[:i]), frame[i])
            e = meridian(frame[i])[1]-1
            instances[h, e] = cut
    positives = negatives = 0
    for (h, e), s in instances.items():
        start = ((e, 0, h),)
        reach = closure(start, lambda w: (q for _, q in ball.steps(w)))
        for (k, f), t in instances.items():
            if e == f:
                good = transport(s, t)
                if ((e, 0, k),) in reach:
                    assert good
                    positives += 1
                elif not good:
                    negatives += 1
    # A nonsimple width-nine comparison requires all eight gains. A second
    # update on the same occurrence has independently prescribed old endpoints.
    data['history'] = [(0, 's')]*9
    sweep = [('X', i) for i in range(8)]
    twist = [('X', 0)]*8
    s = [('p', 0)]*2+sweep+twist
    t = sweep+[('p', 8)]*2+twist
    assert solve(dict(data, source=s, target=t))['surface_filler']
    from semistrict_surface_one_step_reflection import reverse_signed
    signed = tuple(i if i%2 else -i for i in range(1, 9))
    turned = reverse_signed(signed[::-1])[::-1]
    split = next(i for i, x in enumerate(turned) if x > 0)
    a, b = inverse(turned[:split]), turned[split:]
    beta = join(a, b)
    def face(prefix, position):
        return ([('X', x-1) for x in prefix]+[('p', position)]
                +[('X', x-1) for x in factor(prefix, beta)])
    mixed = dict(data, source=face(a, 0), target=face(b, 8))
    assert solve(mixed)['surface_filler']
    assert braid_image(9, a+signed) == braid_image(9, b)
    # Directly check the deletion recurrence on every signed two-letter word
    # through length five, including words with adjacent inverse pairs.
    for length in range(6):
        for word in product((1, -1, 2, -2), repeat=length):
            residuals = {()}
            for x in word:
                kept = {prod(w, (x,)) for w in residuals}
                residuals = kept | residuals if x > 0 else kept
            assert quasi(word) == (() in residuals)
    # Embed a winding-invisible obstruction, with six additional passive strands.
    def crossing(w):
        return [('X', i-1) for i in w]
    a, b = (1,), (2, 1, 1, 1, 2, 2)
    beta = join(a, b)
    d = dict(data, source=crossing(a)+[('p', 0)]+crossing(factor(a, beta)),
             target=crossing(b)+[('p', 2)]+crossing(factor(b, beta)))
    assert not winding(d)['obstruction'] and not solve(d)['surface_filler']
    print(f'{pairs} width-three cut comparisons agree with the complete solver; '
          f'{positives} signed width-four witnesses and {negatives} cut obstructions. '
          'Width-nine repeated-update transport and winding-invisible obstruction checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
