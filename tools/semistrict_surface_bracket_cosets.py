"""Signed bracket orbits in permutation modules over a free deck.

Arguments in JSON: deck_rank, left, right (lists of subgroup words), reps
(the relative words of bracket orbits already touched), same_color (boolean).
Outputs a missing relative word or null if all positions are covered, and the
ordered stabilizer generators and optional orientation-reverser for each rep.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
from itertools import product
from math import gcd
from pathlib import Path
import json

from semistrict_surface_free_module_kernels import analyze
from semistrict_surface_free_tree_placements import reduced


def inv(w):
    return tuple(-a for a in reversed(w))


def core(words, rank):
    # Fold a bouquet of signed loops by identifying the targets of any
    # two equally labelled transitions with the same source.
    edges = []
    parent = [0]
    def new():
        i = len(parent)
        parent.append(i)
        return i
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for w in words:
        w = reduced(w, rank)
        q = 0
        for i, a in enumerate(w):
            r = new() if i+1 < len(w) else 0
            edges.extend([(q,a,r), (r,-a,q)])
            q = r
    while True:
        old = {}
        for q, a, r in edges:
            q, r = root(q), root(r)
            key = q,a
            if key in old and root(old[key]) != r:
                parent[r] = root(old[key])
                break
            old[key] = r
        else:
            base = root(0)
            nodes = [base, *sorted(set(map(root, range(len(parent)))) - {base})]
            ids = {q:i for i,q in enumerate(nodes)}
            return {(ids[q],a):ids[root(r)] for (q,a),r in old.items()}


def double_cosets(rank, left, reps, right):
    # Union of H w K as a word automaton. Epsilon additions implement
    # arbitrary free cancellations across the interfaces.
    lc, rc = core(left, rank), core(right, rank)
    end_left = 1+max((r for r in lc.values()), default=0)
    end_right = end_left+1+max((r for r in rc.values()), default=0)
    edges = [(q,a,r) for (q,a),r in lc.items()] + [
        (end_left+q,a,end_left+r) for (q,a),r in rc.items()]
    eps = set()
    n = end_right
    for w in reps:
        q = 0
        for a in reduced(w, rank):
            edges.append((q,a,n))
            q = n
            n += 1
        eps.add((q,end_left))
    close = [{j} for j in range(n)]
    for q,r in eps:
        close[q].add(r)
    by_letter = defaultdict(list)
    for q,a,r in edges:
        by_letter[a].append((q,r))
    while True:
        prev = sum(map(len,close))
        for q in range(n):
            close[q].update(set().union(*(close[r] for r in close[q])))
        for q,a,r in edges:
            close[q].update(t for s,t in by_letter[-a] if s in close[r])
        if sum(map(len,close)) == prev:
            break
    start = frozenset(close[0])
    def step(states, a):
        return frozenset(t for q,r in by_letter[a] if q in states for t in close[r])
    def accepts(w):
        states = start
        for a in reduced(w, rank):
            states = step(states, a)
        return end_left in states
    # Search all *states* of the complement intersected with reduced words.
    def missing():
        queue = deque([(start,0,())])
        seen = {(start,0)}
        while queue:
            states,last,w = queue.popleft()
            if end_left not in states:
                return w
            for a in by_letter_keys(rank):
                if a != -last:
                    nxt = step(states,a),a
                    if nxt not in seen:
                        seen.add(nxt)
                        queue.append((*nxt,w+(a,)))
        return None
    return accepts,missing


def by_letter_keys(rank):
    return tuple(a for k in range(1,rank+1) for a in (k,-k))


def intersection(left, right, rank):
    lc, rc = core(left, rank), core(right, rank)
    paths = {(0,0): ()}
    vertices = [(0,0)]
    gens = set()
    for q,r in vertices:
        w = paths[q,r]
        for a in by_letter_keys(rank):
            if (q,a) not in lc or (r,a) not in rc:
                continue
            nxt = lc[q,a],rc[r,a]
            if nxt not in paths:
                paths[nxt] = w+(a,)
                vertices.append(nxt)
            else:
                loop = reduced(w+(a,)+inv(paths[nxt]),rank)
                if loop:
                    gens.add(min(loop,inv(loop)))
    return sorted(gens)


def accepted(core_graph, word):
    q = 0
    for a in word:
        q = core_graph.get((q,a))
        if q is None:
            return False
    return q == 0


def certificate(deck_rank, left, right, reps, same_color=False):
    if same_color and core(left,deck_rank) != core(right,deck_rank):
        # Folded state numbering may differ for equivalent generating lists.
        lc, rc = core(left,deck_rank), core(right,deck_rank)
        if not all(accepted(rc,reduced(w,deck_rank)) for w in left) or not all(
                accepted(lc,reduced(w,deck_rank)) for w in right):
            raise ValueError("one color must have the same subgroup on both ends")
    orbits = []
    cover = []
    for w in reps:
        w = reduced(w, deck_rank)
        diag = same_color and accepted(core(left,deck_rank),w)
        cover.append(w)
        if same_color:
            cover.append(inv(w))
        if diag:
            orbits.append({"diagonal":True})
            continue
        stabilizer = intersection(left, [w+tuple(k)+inv(w) for k in right], deck_rank)
        swap = None
        if same_color and double_cosets(deck_rank,left,[w],right)[0](inv(w)):
            # Find u=w h, h in H, with u w in H, by enumerating H.
            graph = core(left,deck_rank)
            queue = deque([()])
            seen = {()}
            while swap is None:
                h = queue.popleft()
                if accepted(graph, reduced(w+h+w,deck_rank)):
                    swap = reduced(w+h,deck_rank)
                    break
                for gen in left:
                    for z in (tuple(gen),inv(gen)):
                        nxt = reduced(h+z,deck_rank)
                        if nxt not in seen:
                            seen.add(nxt)
                            queue.append(nxt)
        orbits.append(dict(stabilizer=stabilizer,swap=swap))
    if same_color:
        cover.append(())
    return dict(orbits=orbits, missing=double_cosets(deck_rank,left,cover,right)[1]())


def presentation(orbits, order):
    rows = []
    for i, orbit in enumerate(orbits):
        if orbit.get("diagonal"):
            rows.append([((),i,1)])
            continue
        if order:
            rows.append([((),i,order)])
        for w in orbit["stabilizer"]:
            rows.append([(w,i,1),((),i,-1)])
        if orbit["swap"] is not None:
            rows.append([(orbit["swap"],i,1),((),i,1)])
    return rows


def finite_action(rank, size, shift):
    # Permutation representation and Schreier generators of point 0.
    letters = by_letter_keys(rank)
    actions = {}
    for i, perm in enumerate(shift, 1):
        actions[i] = perm
        actions[-i] = [perm.index(j) for j in range(size)]
    path = {0: ()}
    queue = [0]
    gens = []
    for x in queue:
        for a in letters:
            y = actions[a][x]
            if y not in path:
                path[y] = path[x]+(a,)
                queue.append(y)
            else:
                w = reduced(path[x]+(a,)+inv(path[y]),rank)
                if w:
                    gens.append(w)
    def act(x,w):
        for a in w:
            x = actions[a][x]
        return x
    return gens,act


def audit():
    # In right-action coordinates the ordered pair (H,wH) is represented
    # by (0, 0.w^-1); left translation by g acts on both points by g^-1.
    H, act = finite_action(2, 4, [[1,2,3,0],[1,0,2,3]])
    K, other = finite_action(2, 3, [[1,2,0],[0,2,1]])
    words = [w for n in range(4) for w in product(by_letter_keys(2),repeat=n) if reduced(w,2)==w]
    checks = 0
    for same, right, action in ((False,K,other),(True,H,act)):
        for w in [(), (1,), (1,1), (1,2), (2,1,1)]:
            test = certificate(2,H,right,[w],same)
            pos = action(0,inv(w))
            orbit = {(0,pos)}
            queue = [(0,pos)]
            for x,y in queue:
                for a in by_letter_keys(2):
                    dest = act(x,(a,)),action(y,(a,))
                    if dest not in orbit:
                        orbit.add(dest)
                        queue.append(dest)
            is_diag = same and pos == 0
            row = test["orbits"][0]
            covered = double_cosets(2,H,[w],right)[0]
            stabilizer = None if is_diag else core(row["stabilizer"],2)
            for v in words:
                assert covered(v) == ((0,action(0,inv(v))) in orbit)
                if stabilizer is not None:
                    assert accepted(stabilizer,v) == (act(0,v)==0 and action(pos,v)==pos)
                checks += 1
            missing = test["missing"]
            def in_cover(z):
                return ((0,z) in orbit or (same and (z==0 or (z,0) in orbit)))
            assert (missing is None) == all(in_cover(z) for z in range(4 if same else 3))
            if missing is not None:
                assert not in_cover(action(0,inv(missing)))
            if same and not is_diag:
                assert (row["swap"] is not None) == ((pos,0) in orbit)
                if row["swap"] is not None:
                    u = row["swap"]
                    assert (act(0,inv(u)),act(pos,inv(u))) == (pos,0)
    # Both subgroups of infinite index. H=a, K=b; double coset of 1
    # consists precisely of a-powers followed by b-powers in reduced words.
    cover, gap = double_cosets(2, [(1,)], [()], [(2,)])
    for w in words:
        assert cover(w) == not_returning(w)
    assert not cover(gap())
    # On a Moore color stabilized by <a^2>, a swaps the first pair and
    # the second pair lies in a different orbit. Read both after a disk on
    # (a-1) times the first bracket, using the actual signed module rows.
    cert = certificate(2, [(1,1)], [(1,1)], [(1,), (2,)], True)
    assert cert["orbits"][0]["swap"] is not None and cert["orbits"][1]["swap"] is None
    assert not double_cosets(2, [(1,1)], [(1,),(-1,)], [(1,1)])[0]((2,))
    for order in (0, 3, 4, 5):
        rows = presentation(cert["orbits"], order)
        rows.append([((1,),0,1),((),0,-1)])
        got = analyze(2,2,rows,[[((),0,1)],[((),1,1)]],[])
        assert got["orders"] == [gcd(order,2),order]
    print(f"{checks} finite coset action checks, orientation reversals and complement witnesses;"
          f" {len(words)} infinite-index double-coset tests and four signed attachment calculations passed")


def not_returning(w):
    seen_b = False
    for a in w:
        seen_b |= abs(a)==2
        if seen_b and abs(a)==1:
            return False
    return True


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--order", type=int, help="emit integral rows for distinct orbit representatives")
    args = parser.parse_args()
    if args.input:
        result = certificate(**json.loads(args.input.read_text()))
        if args.order is not None:
            result["relations"] = presentation(result["orbits"], args.order)
        print(json.dumps(result))
    else:
        audit()
