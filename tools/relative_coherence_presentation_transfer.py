"""Check canonical loop problems, changes of generator boundaries, and low whisker reflection."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars, ps_dim,
                  restrict, src, sub_from, subst_tm, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_boundary_modes import columns
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_frame_module import unary
from relative_coherence_globe_padding import face
from relative_coherence_state_paths import promote


@cache
def disk(d):
    ctx = tree_ctx(disc_tree(d))
    return ctx, v(len(ctx)-1)


def specialize(ctx, template, arg):
    shape, top = disk(tdim_tm(ctx, arg))
    return subst_tm(template, sub_from(shape, ctx, {top[1]: arg}))


def full_on_support(ctx, a, b):
    """Build the head on the common support when that support is a pasting tree."""
    ty = infer(ctx, a)
    support = fv_tm(a) | fv_ty(ty)
    assert infer(ctx, b) == ty and support == fv_tm(b) | fv_ty(ty)
    smaller, inc = restrict(ctx, support)
    ren = [None]*len(ctx)
    for j, old in enumerate(inc):
        ren[old[1]] = v(j)
    return subst_tm(head(smaller, subst_tm(a, ren), subst_tm(b, ren)), inc)


def check(ctx, label, proof, a, b, emitter):
    ty = arr(infer(ctx, a), a, b)
    assert infer(ctx, proof) == ty
    if emitter:
        emitter.check_type(label, ctx, proof, ty)


def weak_globe(emitter):
    standard, z = disk(2)
    lower = standard[:-1]
    f, g = infer(standard, z)[2:]
    uf, ug = unary(lower, f), unary(lower, g)
    weak = lower + (arr(infer(lower, uf), uf, ug),)
    check_ctx(weak)
    a, b, c, d = (full_on_support(lower, x, y) for x, y in ((uf,f),(f,uf),(ug,g),(g,ug)))
    left = tuple(map(v, range(len(lower))))
    forward = left + (composite(standard, 1, (a, z, d)),)
    backward = left + (composite(weak, 1, (b, z, c)),)
    round_trip = subst_tm(forward[-1], backward)
    q = tree_ctx(string_tree(1, [2]*5))
    j, k, x, l, m = map(v, maximal_vars(q))
    before = composite(q, 1, (j, composite(q, 1, (k,x,l)), m))
    after = composite(q, 1, (comp2(q,1,j,k), x, comp2(q,1,l,m)))
    labels = sub_from(q, weak, dict(zip(maximal_vars(q), (a,b,z,c,d), strict=True)))
    assert subst_tm(before, labels) == round_trip
    for rev in (False, True):
        def arrow(ctx, s, t):
            return full_on_support(ctx, t, s) if rev else full_on_support(ctx, s, t)
        reassoc = subst_tm(arrow(q,before,after), labels)
        left_unit = arrow(lower, comp2(lower,1,a,b), ident(lower,uf))
        right_unit = arrow(lower, comp2(lower,1,c,d), ident(lower,ug))
        cancel = composite(weak, 1, (left_unit,z,right_unit))
        generic_pads = composite(standard, 1, (ident(standard,f),z,ident(standard,g)))
        finish = specialize(weak, arrow(standard,generic_pads,z), z)
        steps = (finish,cancel,reassoc) if rev else (reassoc,cancel,finish)
        bridge = composite(weak, 2, steps)
        ends = (z,round_trip) if rev else (round_trip,z)
        check(weak, 'expandAtom' if rev else 'restoreAtom', bridge, *ends, emitter)

    # A rank-four challenge at distinct three-poles and a noncanonical two-pole.
    unit = ident(standard,z)
    other = unary(standard,unit)
    raw_a = head(standard,unit,other)
    raw_b = comp2(standard,3,raw_a,ident(standard,other))
    originals = [specialize(weak, t, z) for t in (raw_a,raw_b)]
    images = [subst_tm(t,forward) for t in originals]
    p, q = images
    for j in (1,2,3):
        below = (f,g) if j == 1 else (z,z) if j == 2 else (unit,unit)
        start, end = (face(standard,p,j,sign) for sign in (False,True))
        lpad = full_on_support(standard,below[0],start)
        rpad = full_on_support(standard,end,below[1])
        p,q = (composite(standard,j,(lpad,t,rpad)) for t in (p,q))
    assert infer(standard,p) == infer(standard,q) == arr(infer(standard,unit),unit,unit)
    mirror = head(standard,unit,unit)
    demand = comp2(standard,3,p,mirror)
    idle = ident(standard,unit)
    oracle = head(standard,demand,idle)
    check(standard,'canonicalDemand',oracle,demand,idle,emitter)

    # Multiply the contraction by q and cancel its mirror, retaining the oracle term.
    middle = comp2(standard,3,oracle,q)
    start = head(standard,p,src(standard,middle))
    finish = head(standard,tgt(standard,middle),q)
    proof = composite(standard,4,(start,middle,finish))
    for j in range(1,5):
        start,end = (face(standard,t,j,sign) for t,sign in zip(images,(False,True)))
        a,b = (face(standard,proof,j,sign) for sign in (False,True))
        if (a,b) != (start,end):
            proof = composite(standard,j,(full_on_support(standard,start,a),proof,
                                          full_on_support(standard,b,end)))
    returned = subst_tm(proof,backward)
    check(weak,'pulledComparison',returned,*(subst_tm(t,backward) for t in images),emitter)
    assert all(subst_tm(t,backward) != orig for t,orig in zip(images,originals))


def contract_return(ctx, base, term, excursion):
    """Reduce a loop at a written disk identity to excursions away from it."""
    r = tdim_tm(ctx, base)
    assert src(ctx, term) == tgt(ctx, term) == base
    assert base == ident(ctx, src(ctx, base))
    _, arity, ty, args = term
    variables = tuple(map(v, range(len(arity))))
    generic = (*term[:3],variables)
    if ps_dim(arity) <= r:
        assert ty[2] == ty[3]
        return subst_tm(head(arity,generic,ident(arity,ty[2])),args)
    first,last,strings = columns(arity,ty,variables,r)
    disk_r,top = disk(r)
    assert first.arity == last.arity == disk_r and first.term == last.term == top
    cells = strings[top[1]]
    writing = composite(arity,r,[v(i) for i in cells])
    unpack = subst_tm(head(arity,generic,writing),args)
    pieces = []
    start = 0
    word = [args[i] for i in cells]
    for end,t in enumerate(word,1):
        if tgt(ctx,t) != base:
            continue
        block = word[start:end]
        block_term = composite(ctx,r,block)
        filler = contract_return(ctx,base,t,excursion) if len(block) == 1 else excursion(block_term)
        assert infer(ctx,filler)[2:] == (block_term,ident(ctx,base))
        pieces.append((start,end,filler))
        start = end
    assert start == len(word)
    grouped = composite(arity,r,[composite(arity,r,[v(i) for i in cells[lo:hi]])
                                 for lo,hi,_ in pieces])
    regroup = subst_tm(head(arity,writing,grouped),args)
    replace = composite(ctx,r,[filler for _,_,filler in pieces])
    units = composite(disk_r,r,[ident(disk_r,top)]*len(pieces))
    finish = specialize(ctx,head(disk_r,units,ident(disk_r,top)),base)
    return composite(ctx,r+1,(unpack,regroup,replace,finish))


def return_test(emitter):
    chart,z = disk(2)
    base = ident(chart,z)
    other = unary(chart,base)
    idle = head(chart,base,base)
    enter,leave = head(chart,base,other),head(chart,other,base)
    sequence = [idle,enter,head(chart,other,other),leave,idle]
    shape = tree_ctx(string_tree(3,[4]*len(sequence)))
    args = sub_from(shape,chart,dict(zip(maximal_vars(shape),sequence,strict=True)))
    term = subst_tm(head(shape,src(shape,v(maximal_vars(shape)[0])),tgt(shape,v(maximal_vars(shape)[-1]))),args)
    calls = []
    def excursion(t):
        calls.append(t)
        return head(chart,t,ident(chart,base))
    proof = contract_return(chart,base,term,excursion)
    assert calls == [composite(chart,3,sequence[1:4])]
    check(chart,'splitReturn',proof,term,ident(chart,base),emitter)


def polygon_chain(length, suspensions, emitter):
    path = tree_ctx(((), ()))
    f,g = map(v, maximal_vars(path))
    row = comp2(path,0,f,g)
    ctx = path
    rows = [row]
    for _ in range(length):
        rows.append(v(len(ctx)))
        ctx += (infer(path,row),)
    atoms = []
    for a,b in zip(rows,rows[1:]):
        atoms.append(v(len(ctx)))
        ctx += (arr(infer(ctx,a),a,b),)
    check_ctx(ctx)
    shape = tree_ctx(string_tree(1,[2]*length))
    slots = maximal_vars(shape)
    section = sub_from(shape,ctx,dict(zip(slots,atoms,strict=True)))
    strict_word = composite(shape,1,list(map(v,slots)))
    total = subst_tm(strict_word,section)
    s = src(shape,v(slots[0]))

    def tower(target, t, k):
        for _ in range(k):
            t = ident(target,t)
        return t

    fixed = tower(path,row,2)
    hidden = head(path,fixed,fixed)
    unit = ident(path,fixed)
    # The old generator named by this head cannot decompose in the pullback:
    # its own path arity labels the interior object, outside the two globe objects.
    assert hidden[3][src(path,g)[1]] == src(path,g) and src(path,g) not in (src(path,row),tgt(path,row))
    projected = tower(shape,s,3)
    first = comp2(shape,1,projected,strict_word)
    second = comp2(shape,1,unary(shape,projected),strict_word)
    central = subst_tm(head(shape,first,second),section)
    u = comp2(ctx,1,hidden,total)
    vterm = comp2(ctx,1,unary(ctx,hidden),total)
    start = comp2(ctx,1,head(path,hidden,unit),total)
    unary_unit = unary(path,unit)
    slot, = maximal_vars(unary_unit[1])
    restored = promote(path,unary_unit,slot,head(path,unit,hidden))
    finish = comp2(ctx,1,restored,total)
    result = composite(ctx,4,(start,central,finish))
    assert src(ctx,central) != u and tgt(ctx,central) != vterm
    for _ in range(suspensions):
        u,vterm,result = (susp_tm(t) for t in (u,vterm,result))
        ctx = susp_ctx(ctx)
    check(ctx,'polygonTransfer',result,u,vterm,emitter)


def disk_pass(ctx, a, b, proof, floor, left, right):
    """Transfer proof between disk operations that agree through floor at the two ends."""
    n = tdim_tm(ctx,a)
    assert infer(ctx,proof)[2:] == (specialize(ctx,left(n),a), specialize(ctx,left(n),b))

    @cache
    def bridge(d, reverse=False):
        arity, z = disk(d)
        x,y = left(d),right(d)
        for j in range(floor+1,d):
            lo,hi = (face(arity,z,j,sign) for sign in (False,True))
            x = comp2(arity,j,x,specialize(arity,bridge(j),hi))
            y = comp2(arity,j,specialize(arity,bridge(j),lo),y)
        return head(arity,y,x) if reverse else head(arity,x,y)

    middle = proof
    for j in range(floor+1,n):
        middle = comp2(ctx,j,middle,specialize(ctx,bridge(j),face(ctx,a,j,True)))
    result = composite(ctx,n,(specialize(ctx,bridge(n,True),a),middle,specialize(ctx,bridge(n),b)))

    def with_prefixes(d, stop):
        arity,z = disk(d)
        value = right(d)
        for k in range(floor+1,stop):
            pref = specialize(arity,bridge(k),face(arity,z,k,False))
            value = comp2(arity,k,pref,value)
        return value

    for j in reversed(range(floor+1,n)):
        rev = specialize(ctx,bridge(j,True),face(ctx,a,j,False))
        result = comp2(ctx,j,rev,result)
        def padded(d):
            arity,z = disk(d)
            rev_j = specialize(arity,bridge(j,True),face(arity,z,j,False))
            return comp2(arity,j,rev_j,with_prefixes(d,j+1))
        result = disk_pass(ctx,a,b,result,j,padded,lambda d: with_prefixes(d,j))
    expected = arr(infer(ctx,specialize(ctx,right(n),a)),specialize(ctx,right(n),a),
                   specialize(ctx,right(n),b))
    assert infer(ctx,result) == expected
    return result


def reflect_lower(n, emitter):
    base = disk(n+1)[0][:-1]
    a,b = map(v,(len(base)-2,len(base)-1))
    k = 1
    line,f = disk(k)
    lift = head(line,unary(line,f),f)
    back = head(line,f,unary(line,f))
    lower_face = face(base,a,k,False)
    def attach(term, cell):
        return comp2(base,k,specialize(base,term,lower_face),cell)
    p,q = attach(lift,a),attach(lift,b)
    ctx = base+(arr(infer(base,p),p,q),)
    check_ctx(ctx)
    supplied = v(len(base))
    initial = comp2(ctx,k,specialize(ctx,back,lower_face),supplied)
    def padded(d):
        arity,z = disk(d)
        low = face(arity,z,k,False)
        return comp2(arity,k,specialize(arity,back,low),comp2(arity,k,specialize(arity,lift,low),z))
    result = disk_pass(ctx,a,b,initial,k,padded,lambda d: disk(d)[1])
    assert supplied[1] in fv_tm(result)
    check(ctx,'reflectLow',result,a,b,emitter)



if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank',type=int,default=4)
    parser.add_argument('--agda',type=Path)
    parser.add_argument('--length',type=int,default=2)
    parser.add_argument('--suspend',type=int,default=0)
    args = parser.parse_args()
    if args.length < 1 or args.suspend < 0:
        parser.error('length must be positive and suspension count nonnegative')
    if args.rank < 3:
        parser.error('rank must be at least three')
    emitter = Emitter() if args.agda else None
    return_test(emitter)
    weak_globe(emitter)
    reflect_lower(args.rank,emitter)
    polygon_chain(args.length,args.suspend,emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem,'Changing presentations and reflecting a low whisker.'))
    print(f'Checked the canonical loop, weak-globe maps, rank-{args.rank} reflection, '
          f'and rank-{4+args.suspend} comparison across {args.length} polygons.')
