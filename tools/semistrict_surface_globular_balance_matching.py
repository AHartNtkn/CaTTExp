"""Decide compatible cut placements and fit two changing tuples at a shared globular face."""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import combinations_with_replacement, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, comp_tree, infer, maximal_vars, ps_boundary_vars,
                  restrict, src, sub_from, subst_tm, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_insertion_cut import Assertions


def solve(bounds, arcs):
    """Return the least placement, or an implication path to a forbidden level."""
    outgoing = {}
    for u, target, f in arcs:
        for rank, value in enumerate(f):
            outgoing.setdefault((u, rank), []).append((target, value))
    queue = deque((u, lo) for u, (lo, _) in enumerate(bounds))
    reached = dict.fromkeys(queue)
    current = [lo for lo, _ in bounds]
    while queue:
        node = queue.popleft()
        u, rank = node
        if rank > bounds[u][1]:
            path = [node]
            while reached[path[-1]] is not None:
                path.append(reached[path[-1]])
            return None, tuple(reversed(path))
        current[u] = max(current[u], rank)
        lower = [(u, rank - 1)] if rank else []
        for nxt in [*lower, *outgoing.get(node, ())]:
            if nxt not in reached:
                reached[nxt] = node
                queue.append(nxt)
    return tuple(current), None


def restrictions(u, target, prefix):
    first, inverse = 0, []
    for q in range(prefix[-1] + 1):
        while prefix[first] < q:
            first += 1
        inverse.append(first)
    return [(u, target, prefix), (target, u, inverse)]


def matching_checks():
    counts = Counter()
    prefixes = [(0, a, b, 3) for a,b in combinations_with_replacement(range(4), 2)]
    cuts = tuple(combinations_with_replacement(range(4), 2))
    # Two arms, two seams per word, and a common face. A cospan followed
    # by a parallel-arrow equalizer also tests constraints on a cycle.
    for i,f in enumerate(prefixes):
        for j,g in enumerate(prefixes):
            for cyclic in (False, True):
                maps = [(0, 2, f), (1, 2, g)]
                if cyclic:
                    maps += [(1, 0, prefixes[(i+2*j)%len(prefixes)])]
                arcs = [(2*n, 2*n+1, tuple(range(4))) for n in range(3)]
                for u,t,p in maps:
                    for s in range(2):
                        arcs += restrictions(2*u+s, 2*t+s, p)
                # Independent direct enumeration of all simultaneous tuples,
                # using equality of restricted cuts in each actual face.
                candidates = [a+b+c for a,b,c in product(cuts, repeat=3)
                              if all(tuple(p[x] for x in (a,b,c)[u]) == (a,b,c)[t] for u,t,p in maps)]
                for l,h,k in product(range(4), repeat=3):
                    bounds = [(l,3), (0,3), (0,3), (0,h), (0,k), (0,3)]
                    possible = [c for c in candidates if all(lo <= x <= hi for (lo,hi),x
                                                            in zip(bounds,c,strict=True))]
                    expected = tuple(map(min,zip(*possible,strict=True))) if possible else None
                    actual, path = solve(bounds, arcs)
                    if path:
                        u, level = path[0]
                        assert level == bounds[u][0] and path[-1][1] > bounds[path[-1][0]][1]
                        for (vtx,n), (w,m) in zip(path,path[1:]):
                            assert (vtx == w and n == m+1 or
                                    any((src,dst) == (vtx,w) and f[n] == m for src,dst,f in arcs))
                    assert actual == expected and (actual is None or actual in possible)
                    counts['feasible' if possible else 'infeasible'] += 1
    return counts


def anchors():
    def floor(grades, threshold, end):
        return max((i+1 for i,g in enumerate(grades[:end]) if g > threshold), default=0)

    counts = Counter()
    for target in product(range(1,4), repeat=4):
        for a,b in combinations_with_replacement(range(5),2):
            f = (0,a,b,4)
            degrees = [max(target[start:end], default=1) for start,end in zip(f,f[1:])]
            for source in product(*(range(d,4) for d in degrees)):
                for m in (1,2):
                    valid = all(f[i+1] == 0 or target[f[i+1]-1] > m
                                for i,g in enumerate(source) if g > m)
                    actual = all(f[floor(source,m,e)] == floor(target,m,f[e]) for e in range(4))
                    assert valid == actual
                    counts['anchored' if valid else 'non-anchored'] += 1
    return counts


def product_at(ctx, cut, *terms):
    return comp_tree(string_tree(cut, [tdim_tm(ctx,t) for t in terms]), ctx, terms)


def boundary_head(ctx, degree, sign, left, right):
    subctx, inc = restrict(ctx, ps_boundary_vars(ctx, degree, sign))
    rename = {x[1]:v(i) for i,x in enumerate(inc)}
    return subst_tm(head(subctx, subst_tm(left,rename), subst_tm(right,rename)), inc)


def layers(ctx, a, t, b, early):
    act = lambda *ts: product_at(ctx, 0, *ts)
    if early:
        return comp2(ctx, 1, act(a,t,src(ctx,b)), act(tgt(ctx,a),tgt(ctx,t),b))
    return comp2(ctx, 1, act(a,src(ctx,t),src(ctx,b)), act(tgt(ctx,a),t,b))


def slab(early):
    # Each cell changes at the same fine middle position; the two coarse
    # temporal readings perform its 2-event at opposite ends of the order.
    ctx = tree_ctx(string_tree(0,[2,3,2]))
    a, change, b = map(v, maximal_vars(ctx))
    before, after = src(ctx,change), tgt(ctx,change)
    lower = layers(ctx,a,before,b,early)
    upper = layers(ctx,a,after,b,early)
    cat = lambda c,x,y: comp2(ctx,c,x,y)
    if early:
        moving = cat(0,a,change)
        raw = cat(1,cat(0,moving,src(ctx,b)),cat(0,tgt(ctx,src(ctx,moving)),b))
    else:
        moving = cat(0,change,b)
        raw = cat(1,cat(0,a,src(ctx,src(ctx,moving))),cat(0,tgt(ctx,a),moving))
    # First fit the 1-frame, then fit the two 2-faces at that literal frame.
    start = boundary_head(ctx,1,'-',src(ctx,lower),src(ctx,src(ctx,raw)))
    end = boundary_head(ctx,1,'+',tgt(ctx,tgt(ctx,raw)),tgt(ctx,upper))
    middle = product_at(ctx,1,start,raw,end)
    enter = boundary_head(ctx,2,'-',lower,src(ctx,middle))
    leave = boundary_head(ctx,2,'+',tgt(ctx,middle),upper)
    fitted = product_at(ctx,2,enter,middle,leave)
    assert infer(ctx,fitted) == arr(infer(ctx,lower),lower,upper)
    return ctx, raw, fitted


def junction_checks(binary, agda_dir):
    base = tree_ctx(string_tree(0,[2,1,2]))
    a,h,b = map(v,maximal_vars(base))
    unit = ident(base,h)
    middle_l, middle_r = (layers(base,a,unit,b,side) for side in (True,False))
    join = head(base,middle_l,middle_r)
    # Attach actual changes with one identity face. All names in the middle
    # are in the same ordinary context; no comparison identifies its 3-cells.
    two = arr(infer(base,h),h,h)
    u,t = v(len(base)),v(len(base)+1)
    ctx = (*base,two,two,arr(two,u,unit),arr(two,unit,t))
    p,q = v(len(base)+2),v(len(base)+3)
    raw, fit = [], []
    for side, step in ((True,p),(False,q)):
        pat, original, aligned = slab(side)
        lab = sub_from(pat,ctx,dict(zip(maximal_vars(pat),(a,step,b),strict=True)))
        raw.append(subst_tm(original,lab))
        fit.append(subst_tm(aligned,lab))
    assert tgt(ctx,fit[0]) == middle_l and src(ctx,fit[1]) == middle_r and middle_l != middle_r
    witness = product_at(ctx,2,fit[0],join,fit[1])
    old_type = arr(infer(ctx,src(ctx,fit[0])),src(ctx,fit[0]),tgt(ctx,fit[1]))
    assert infer(ctx,witness) == old_type
    name = 'GlobularBalanceJunction'
    emitter = Emitter() if agda_dir else None
    for cut in range(3):
        if emitter:
            emitter.check_typed(f'fitted{cut}',ctx,witness)
            emitter.check_type(f'fitted{cut}',ctx,witness,old_type)
        verify_class(binary,ctx,raw,witness,old_type,cut)
        if cut < 2:
            ctx, raw = susp_ctx(ctx), list(map(susp_tm,raw))
            witness, old_type = susp_tm(witness), susp_ty(old_type)
            assert infer(ctx,witness) == old_type
    if emitter:
        agda_dir.mkdir(parents=True,exist_ok=True)
        (agda_dir/(name+'.agda')).write_text(emitter.module(name,__doc__))


def verify_class(binary,ctx,raw,witness,old_type,cut):
    assert tdim_tm(ctx,witness) == cut + 3
    code = Assertions()
    def show(ty):
        return '*' if ty == STAR else ' -> '.join(code.term(t) for t in ty[2:])
    decl = ' '.join(f'(x{i} : {show(ty)})' for i,ty in enumerate(ctx))
    direct = f'comp[{code.term(raw[0])},{code.term(raw[1])}]'
    old = show(old_type)
    full = ','.join('x'+str(i) for i in range(len(ctx)))
    # General context definitions take their whole argument telescope explicitly.
    definitions = [f'def direct {decl} : {old} = {direct}',
                   f'def lifted {decl} : {old} = {code.term(witness)}',
                   f'assert direct({full}) = lifted({full}) in {decl}']
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder/'Heads.catt').write_text('\n'.join(code.commands)+'\n')
        (folder/'Fit.catt').write_text('import Heads\n'+definitions[1]+'\n')
        (folder/'Join.catt').write_text('import Heads\n'+'\n'.join(definitions)+'\n')
        accepted(run(binary,folder,'Fit.catt'),'Fit.catt',['lifted'])
        for flags in (['--insertion-width','2'],['--sua']):
            output = run(binary,folder,'Join.catt',flags)
            accepted(output,'Join.catt',['direct','lifted'])
            assert 'are equal' in output
        for flags in ([],['--insertion-width','1']):
            output = run(binary,folder,'Join.catt',flags)
            assert 'Checking direct\n' in output and 'Error:' in output and 'Finished importing Join.catt' not in output, output[-1000:]


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', required=True, type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print(dict(matching_checks()),dict(anchors()),flush=True)
    junction_checks(args.rice_binary.resolve(),args.agda_dir)
    print('Verified the changing middle column at the literal old type and in the designated width-two class.')
