"""Read quantified Boolean values from column sweeps of compressed row histories."""

from functools import cache
from itertools import permutations, product

from check_interchange_compressed_tableaux import fold
from check_interchange_grid_contractions import normal_path
from interchange_shared_whiskers import Words

IDENTITY = tuple(range(5))


def mul(g,h):
    return tuple(g[i] for i in h)


def inv(g):
    return tuple(g.index(i) for i in IDENTITY)


def cycles():
    result = []
    for g in permutations(IDENTITY):
        x = g[0]
        length = 1
        while x:
            x = g[x]
            length += 1
        if length == 5:
            result.append(g)
    return result


CYCLES = cycles()
SPLIT = {mul(mul(a,b),mul(inv(a),inv(b))): (a,b) for a,b in product(CYCLES,repeat=2)}
assert all(c in SPLIT for c in CYCLES)


def program(expr,n):
    raw = Words()
    def row(r):
        return raw.letter(r)

    def instruction(c, var=None):
        # Marker rows for constant, test, zero digit, one digit and end.
        digits = format(CYCLES.index(c),'05b')
        code = [row(2*n + int(var is not None))]
        code.extend(row(2*n+2+int(d)) for d in digits)
        if var is not None:
            code.extend(row(2*var+i) for i in (0,0,1,1))
        code.append(row(2*n+4))
        return fold(raw,code)

    @cache
    def build(e,c):
        if isinstance(e,int):
            return instruction(c,e)
        op, *args = e
        if op == 'not':
            return raw.join(instruction(c),build(args[0],inv(c)))
        a,b = SPLIT[c]
        if op == 'all':
            var,child = args
            def right(g):
                return fold(raw,[row(2*var),build(child,g),row(2*var+1)])
            left = child
        else:
            assert op == 'and'
            left,other = args
            def right(g):
                return build(other,g)
        return fold(raw,[build(left,a),right(b),build(left,inv(a)),right(inv(b))])

    root = build(expr,CYCLES[0])
    stride = 2*raw.length[root]+1
    initial = [stride*(n+5-r//2) for r in range(2*n)]
    initial.extend(stride*j for j in reversed(range(5)))
    return raw,root,initial


def evaluate(expr,env):
    if isinstance(expr,int):
        return env[expr]
    op, a, *rest = expr
    if op == 'not':
        return not evaluate(a,env)
    if op == 'and':
        return evaluate(a,env) and evaluate(rest[0],env)
    return all(evaluate(rest[0], {**env,a:b}) for b in (False,True))


def read_schedule(raw,root,initial,n):
    state = list(initial)
    events, pending = [], [root]
    while pending:
        rule = raw.rules[pending.pop()]
        if len(rule) == 2:
            pending.extend(~x for x in reversed(rule))
        else:
            r, = rule
            events.append((r,-state[r]))
            state[r] += 1
    canonical = iter(r for rs,cols in normal_path(events) for _ in cols for r in rs)
    value = IDENTITY
    for r in canonical:
        if r < 2*n:
            continue
        assert r in (2*n,2*n+1)
        index = int(''.join(str(next(canonical)-2*n-2) for _ in range(5)),2)
        active = True
        if r == 2*n+1:
            pattern = tuple(next(canonical)%2 for _ in range(4))
            assert pattern in ((0,0,1,1),(0,1,0,1))
            active = pattern == (0,0,1,1)
        assert next(canonical) == 2*n+4
        if active:
            value = mul(value,CYCLES[index])
    return value


if __name__=='__main__':
    tests = 0
    for a,b in product(range(2),repeat=2):
        for child in (('and',a,b), ('not',('and',a,('not',b)))):
            for first,second in product(('all','exists'),repeat=2):
                e = child
                for var,kind in ((1,second),(0,first)):
                    e = ('all',var,e) if kind=='all' else ('not',('all',var,('not',e)))
                raw,root,initial = program(e,2)
                assert read_schedule(raw,root,initial,2) == (CYCLES[0] if evaluate(e,{}) else IDENTITY)
                tests += 1
    e = 0
    for i in range(32):
        e = ('all',i,('not',e))
    raw,root,_ = program(e,32)
    print(f"{tests} quantified formulas agree with direct evaluation; 32 quantifiers use "
          f"{len(raw.rules)} productions for a schedule of bit length {raw.length[root].bit_length()} in its event count.")
