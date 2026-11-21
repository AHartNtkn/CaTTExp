"""
Bridge between Agda modules and the Python generators.

  normalize(path, expr)  ->  the printed normal form of `expr` in the
                             module at `path` (agda --interaction).
  parse(text)            ->  Python values: catt.py terms for Ctx/Ty/Tm/Sub,
                             lists, and records Query/Entry as tuples.
  queries(path, expr)    ->  [(G, A, t, u)] for a closed `List Query`.

Usage, answering every rc call a module lists and writing a table:

  python3 tools/agda_bridge.py answer <module.agda> <expr> <TableModuleName>

writes src/CaTTExp/Generated/<TableModuleName>.agda (see rc_oracle.emit_table).
"""
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import STAR, arr, v

SRC = os.environ.get('CATT_SRC') or os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src')

def normalize(path, expr, includes=()):
    path = os.path.abspath(path)
    inc = ['-i', os.path.abspath(SRC), '-i', os.path.dirname(path)]
    for d in includes:
        inc += ['-i', os.path.abspath(d)]
    args = '[' + ','.join('"%s"' % a for a in inc) + ']'
    cmds = ('IOTCM "%s" None Indirect (Cmd_load "%s" %s)\n'
            'IOTCM "%s" None Indirect (Cmd_compute_toplevel DefaultCompute "%s")\n'
            % (path, path, args, path, expr.replace('"', '\\"')))
    env = dict(os.environ, LC_ALL='C.UTF-8')
    out = subprocess.run(['agda', '--interaction'], input=cmds, capture_output=True,
                         text=True, env=env).stdout
    m = re.search(r'\(agda2-info-action "\*Normal Form\*" "((?:[^"\\]|\\.)*)"', out)
    if not m:
        raise RuntimeError('agda did not normalize %r:\n%s' % (expr, out[-3000:]))
    return m.group(1).encode().decode('unicode_escape').encode('latin-1').decode('utf-8')

# ---------------------------------------------------------------- parser

def _tokens(s):
    toks = re.findall(r'\(|\)|[^\s()]+', s)
    out = []
    for t in toks:
        if t not in '()' and '.' in t and not t[0].isdigit():
            t = t.rsplit('.', 1)[1] if not t.endswith('.') else t
        out.append(t)
    return out

INFIX = {'▸': 'l', ',ₛ': 'l', '∷': 'r', ',': 'r'}

def parse(text):
    toks = _tokens(text)
    val, i = _expr(toks, 0)
    assert i == len(toks), toks[i:]
    return val

PREC = [',', '∷', '▸', ',ₛ']      # loosest first: _,_ is infixr 4, the others level 5

def _expr(toks, i):
    parts, ops = [], []
    app, i = _app(toks, i)
    parts.append(app)
    while i < len(toks) and toks[i] in INFIX:
        ops.append(toks[i])
        app, i = _app(toks, i + 1)
        parts.append(app)
    return _combine(parts, ops), i

def _combine(parts, ops):
    if not ops:
        return parts[0]
    for op in PREC:
        if op in ops:
            break
    groups, cur_p, cur_o = [], [parts[0]], []
    for o, p in zip(ops, parts[1:]):
        if o == op:
            groups.append(_combine(cur_p, cur_o))
            cur_p, cur_o = [p], []
        else:
            cur_o.append(o); cur_p.append(p)
    groups.append(_combine(cur_p, cur_o))
    if op == ',':
        return ('tuple', tuple(groups))
    if op == '∷':
        assert groups[-1] == ('con', '[]', ()), groups[-1]
        return ('list', tuple(groups[:-1]))
    return (op, tuple(groups))

def _app(toks, i):
    head, i = _atom(toks, i)
    args = []
    while i < len(toks) and toks[i] not in INFIX and toks[i] != ')':
        a, i = _atom(toks, i)
        args.append(a)
    if head[0] == 'con':
        return ('con', head[1], tuple(args)), i
    assert not args, (head, args)
    return head, i

def _atom(toks, i):
    t = toks[i]
    if t == '(':
        e, i = _expr(toks, i + 1)
        assert toks[i] == ')'
        return e, i + 1
    if t.isdigit():
        return ('num', int(t)), i + 1
    return ('con', t, ()), i + 1

# ---------------------------------------------------------------- to catt.py values

def to_ctx(e):
    if e == ('con', 'ε', ()):
        return ()
    assert e[0] == '▸', e
    parts = e[1]
    assert parts[0] == ('con', 'ε', ()), parts[0]
    return tuple(to_ty(p) for p in parts[1:])

def to_ty(e):
    if e == ('con', '⋆', ()):
        return STAR
    assert e[0] == 'con' and e[1] == 'arr', e
    A, s, t = e[2]
    return arr(to_ty(A), to_tm(s), to_tm(t))

def to_tm(e):
    assert e[0] == 'con', e
    if e[1] == 'var':
        return v(e[2][0][1])
    if e[1] == 'coh':
        P, A, s = e[2]
        return ('coh', to_ctx(P), to_ty(A), to_sub(s))
    raise ValueError(e)

def to_sub(e):
    if e == ('con', '⟨⟩', ()):
        return ()
    assert e[0] == ',ₛ', e
    parts = e[1]
    assert parts[0] == ('con', '⟨⟩', ())
    return tuple(to_tm(p) for p in parts[1:])

def to_list(e):
    if e == ('con', '[]', ()):
        return ()
    assert e[0] == 'list', e
    return e[1]

def queries(path, expr):
    out = []
    for q in to_list(parse(normalize(path, expr))):
        assert q[0] == 'con' and q[1] == 'query', q
        G, A, t, u = q[2]
        out.append((to_ctx(G), to_ty(A), to_tm(t), to_tm(u)))
    return out

def maybe_query(path, expr):
    """A closed `Maybe Query`, with ConeRC's Query = Ctx × (Ty × (Tm × Tm))."""
    e = parse(normalize(path, expr))
    if e == ('con', 'nothing', ()):
        return None
    assert e[0] == 'con' and e[1] == 'just', e
    tup = e[2][0]
    assert tup[0] == 'tuple' and len(tup[1]) == 4, tup
    G, A, t, u = tup[1]
    return (to_ctx(G), to_ty(A), to_tm(t), to_tm(u))

if __name__ == '__main__':
    if sys.argv[1] == 'answer':
        import rc_oracle
        path, expr, name = sys.argv[2:5]
        qs = queries(path, expr)
        rc_oracle.write_table(name, qs)
    elif sys.argv[1] == 'show':
        for q in queries(sys.argv[2], sys.argv[3]):
            print(q)
