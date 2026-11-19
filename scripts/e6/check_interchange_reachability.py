"""Check the native reachability compiler, directed schemas and certificate replay."""
from dataclasses import dataclass, replace

from interchange_reachability import Certificate, Edge, Path, Presentation, Rule, solve, verify
from reachability_theory import OPERATIONS, RULES


@dataclass(frozen=True)
class Cell:
    dim: int
    s: object
    t: object
    chain: tuple
    length: int = 0
    moment: int = 0


def unit(x):
    return Cell(x.dim+1, x, x, ())


def face(x, dim, target=False):
    while x.dim > dim:
        x = x.t if target else x.s
    return x


def glue(x, y, cut):
    """Compute strict chains, both globular faces and the independent Response 4 invariants."""
    while x.dim < y.dim:
        x = unit(x)
    while y.dim < x.dim:
        y = unit(y)
    assert face(x, cut, True) == face(y, cut), (cut, x, y)
    n = x.dim
    if n == cut+1:
        s, t = x.s, y.t
    else:
        s, t = glue(x.s,y.s,cut), glue(x.t,y.t,cut)
    moment = x.moment + y.moment
    if n == 3 and cut == 1:
        moment += x.length*y.s.length - x.s.length*y.length
    return Cell(n, s, t, tuple(sorted(x.chain+y.chain)), x.length+y.length, moment)


def globe_chain(degrees, cut):
    """Give the generic generators disjoint names, sharing precisely the glued faces."""
    cells, previous = [], None
    for i, n in enumerate(degrees):
        sides = []
        for d in range(n+1):
            s, t = sides[-1] if sides else (None,None)
            pair = [Cell(d,s,t,((i,d,side),),int(d >= 2)) for side in (0,1)]
            if previous is not None and d < cut:
                pair = previous[d]
            elif previous is not None and d == cut:
                pair[0] = previous[d][1]
            sides.append(pair)
        cells.append(sides[-1][0])
        previous = sides
    return cells


def evaluate(expr, env):
    if isinstance(expr,str):
        return env[expr]
    name, *raw = expr
    args = [evaluate(a, env) for a in raw]
    op = OPERATIONS[name]
    assert tuple(a.dim for a in args) == op.inputs
    if name[0] in "st" and name[1:].isdigit():
        return args[0].s if name[0] == "s" else args[0].t
    if name.startswith("id"):
        return unit(args[0])
    x,y = args
    if name.startswith("comp"):
        return glue(x,y,x.dim-1)
    if name.startswith(("left", "right")):
        return glue(x,y,min(x.dim,y.dim)-1)

    operands = {"x0":x, "x1":y}
    assert all(evaluate(a,operands) == evaluate(b,operands) for a,b in op.guards)
    s,t = evaluate(op.source,operands),evaluate(op.target,operands)
    assert (s.s,s.t,s.chain) == (t.s,t.t,t.chain)
    base = 100  # exceeds the largest absolute slot moment plus 3-mass here
    if name == "chi":
        length = x.length*y.length
    elif name == "iota":
        length = x.length*y.length
    elif name == "r":
        length = (base*x.length+x.moment)*y.length
    elif name == "t":
        length = x.length*(base*y.length-y.moment)
    elif name == "h":
        length = (base*x.length+x.moment)*y.t.length-x.length*y.length
    else:
        raise ValueError(name)
    return Cell(op.output,s,t,(),length)


def check_rule(schema, args):
    env = dict(zip((v for v,_ in schema.variables), args))
    assert all(evaluate(a, env) == evaluate(b, env) for a,b in schema.guards)
    source, target = evaluate(schema.left,env), evaluate(schema.right,env)
    assert (source.s,source.t,source.chain) == (target.s,target.t,target.chain), schema.name
    x,y = args
    drop = 0
    if schema.name == "U_r":
        drop = y.length*(x.s.moment-x.t.moment)
    elif schema.name == "U_t":
        drop = x.length*(y.s.moment-y.t.moment)
    elif schema.name == "W":
        drop = 2*x.length*y.length
    assert source.length - target.length == drop, schema.name
    return drop


def check_schemas():
    by_name = {r.name:r for r in RULES}
    cuts = {"W":0,"U_r":0,"U_t":0,"N_L":1,"N_R":1,"delta":2}
    assert by_name.keys() == cuts.keys()
    for name, rule in by_name.items():
        check_rule(rule,globe_chain([d for _,d in rule.variables],cuts[name]))
    # A mixed varying 4-argument gives a strictly decreasing outer unary 5-step.
    a,b,c = globe_chain((3,2,2),0)
    mixed = evaluate(("r","a","b"), {"a":a,"b":b})
    assert check_rule(by_name["U_r"],(mixed,c)) == 2
    a,b,c = globe_chain((2,2,3),0)
    mixed = evaluate(("t","b","c"), {"b":b,"c":c})
    assert check_rule(by_name["U_t"],(a,mixed)) == 2


def check_grounded_loops():
    p = lambda *letters: Path("v",letters)
    letters = {x:Edge("v","v",1) for x in "abc"}
    letters["u"] = Edge("v","v",2)
    rules = (Rule("tile",p("a","a"),p("u"),True),
             Rule("advance",p("a","a"),p("b","b")),
             Rule("drop",p("c"),p()))
    model = Presentation(["v"],letters,rules)
    lhs,rhs = p("b","u","a"),p("b","b","b","a")
    yes = solve(model,lhs,rhs)
    assert yes.reachable and verify(model,lhs,rhs,yes)
    assert any(step.backwards and step.offset == 1 for step in yes.steps)
    invalid = replace(yes, steps=(replace(yes.steps[0],offset=2),*yes.steps[1:]))
    assert not verify(model,lhs,rhs,invalid)
    no = solve(model,p("c","u"),p("b","a"))
    assert not no.reachable and len(no.visited) >= 4
    assert verify(model,p("c","u"),p("b","a"),no)
    assert not verify(model,p("c","u"),p("b","a"),replace(no,visited=(p("c","u"),)))
    false_reverse = Certificate(True,(),(replace(yes.steps[-1],backwards=True),))
    assert not verify(model,rhs,lhs,false_reverse)


def disk(dimension):
    tree = []
    for _ in range(dimension):
        tree = [tree]
    return tree


def instantiate(expr, assignment):
    if isinstance(expr,str):
        return assignment[expr]
    return (expr[0], *(instantiate(child,assignment) for child in expr[1:]))


def check_native_rule(rule, cut):
    from interchange_free import FreeAlgebra
    from reachability_theory import EQUATIONS

    tree = [disk(dim-cut-1) for _,dim in rule.variables]
    for _ in range(cut):
        tree = [tree]
    env = {v:"/".join(["0"]*cut + [str(i)] + ["0"]*(dim-cut))
           for i,(v,dim) in enumerate(rule.variables)}
    lhs,rhs = (instantiate(x,env) for x in (rule.left,rule.right))
    free = FreeAlgebra(tree)
    model,a,b = free.query(lhs,rhs)
    yes,no = solve(model,a,b), solve(model,b,a)
    assert a != b and yes.reachable and verify(model,a,b,yes), rule.name
    assert not no.reachable and verify(model,b,a,no), rule.name
    if rule.name == "W":
        factor = next(e for e in EQUATIONS if e.name == "binary join factorization")
        left, right = (instantiate(e,env) for e in (factor.left,factor.right))
        x,y = free.query_term(left),free.query_term(right)
        assert left != right and x == y and free.data[x].size > 0


def check_native_queries():
    from interchange_free import compile_query
    from reachability_theory import EQUATIONS

    # Two consecutive input 5-globes have three parallel primitive 4-faces.
    tree = [[],[]]
    for _ in range(4):
        tree = [tree]
    first,middle,last = [f"0/0/0/0/{i}" for i in range(3)]
    model,a,b = compile_query(tree,first,last)
    yes = solve(model,a,b)
    assert yes.reachable and len(yes.steps) == 2 and verify(model,a,b,yes)
    invalid = replace(yes,steps=tuple(reversed(yes.steps)))
    assert not verify(model,a,b,invalid)
    model,a,b = compile_query(tree,middle,first)
    no = solve(model,a,b)
    assert not no.reachable and len(no.visited) == 2 and verify(model,a,b,no)
    assert not verify(model,a,b,replace(no,visited=(a,)))
    # Both query weights are zero. The face selector still sees the weight-one
    # input used inside the source term, which belongs outside the final cap.
    model,a,b = compile_query(tree,("id3",("s4",first)),("id3","0/0/0/0"))
    assert a == b and model.weight(a) == 0 and solve(model,a,b).reachable

    # The input 5-globe changes the second 4-arrow of a chronological pair.
    contextual_tree = [[],[[]]]
    for _ in range(3):
        contextual_tree = [contextual_tree]
    x,y = (("comp4","0/0/0/0/0",f"0/0/0/1/{i}") for i in (0,1))
    model,a,b = compile_query(contextual_tree,x,y)
    yes,no = solve(model,a,b),solve(model,b,a)
    assert model.weight(a) == 2 and yes.reachable and verify(model,a,b,yes)
    assert not no.reachable and verify(model,b,a,no)

    # A 3-dimensional K15 substitution appears inside a 4-cell boundary.
    eq = next(eq for eq in EQUATIONS if eq.name == "7a")
    env = {"a1":"0/0/0","a2":"0/1/0","b":"1/0/0"}
    x,y = (("id3",instantiate(e,env)) for e in (eq.left,eq.right))
    model,a,b = compile_query([[[],[]],[[]]],x,y)
    assert x != y and a == b and solve(model,a,b).reachable

    for x,y in ((("comp4",first,last),first),
                (("id3","0"),first),
                (("id3","0/0/0/0"),first)):
        try:
            compile_query(tree,x,y)
        except ValueError:
            continue
        raise AssertionError(f"accepted invalid query {x!r}, {y!r}")


def check_native_loop():
    from interchange_free import compile_query
    from reachability_theory import Block, Cell as TermCell, c, chi, inner, paste, word

    a1,a2,b1,b2 = [Block.var(TermCell(2,f"{i}/{j}/0"),i)
                   for i in (0,1) for j in (0,1)]
    prefix = word(word(b1,chi(a1,b2)),a2)
    suffix = word(word(a1,chi(a2,b1)),b2)
    loop = c(prefix,inner(chi(a1,b1),chi(a2,b2)),suffix)
    # K34 is an endomorphism only after the two block schedules are identified.
    model,square,single = compile_query([[[],[]],[[],[]]],paste(loop,loop).term,loop.term)
    assert square.start == model.end(square) == single.start == model.end(single)
    assert (model.weight(square),model.weight(single)) == (2,1)
    for a,b in ((square,single),(single,square)):
        cert = solve(model,a,b)
        assert not cert.reachable and verify(model,a,b,cert)


def main():
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-disks", action="store_true",
                        help="also compile the complete native arities of the two outer unary rules and W")
    parser.add_argument("--loop", action="store_true",
                        help="also compile H and its square on the native two-by-two grid")
    args = parser.parse_args()
    check_schemas()
    check_grounded_loops()
    check_native_queries()
    cuts = {"delta":2,"N_L":1,"N_R":1}
    if args.all_disks:
        cuts.update({"U_r":0,"U_t":0,"W":0})
    for rule in RULES:
        if rule.name in cuts:
            check_native_rule(rule,cuts[rule.name])
    if args.loop:
        check_native_loop()
        print("Verified both non-reachability certificates between H and its square.")
    print(f"Verified 6 graded disk rules, 2 mixed unary instances, {len(cuts)} native disk arities, "
          "a composable pair of 5-globes, K15, typed queries and certificate replay.")


if __name__ == "__main__":
    main()
