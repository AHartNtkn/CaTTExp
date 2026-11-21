"""
Answer the rc calls of an Agda construction whose later calls depend on
earlier answers (e.g. CaTTExp.ConeRC.firstMiss).

  python3 tools/rc_loop.py <TableName> <expr> [import ...]

<expr> is an Agda expression of type `List (Maybe Query)` (ConeRC's Query)
that may mention `TBL` for the current oracle table, e.g.

  "map (λ Γ → ConeRC.firstMiss (TBL orRC rc1) Γ) TermCones2.twoTerm"

Each round normalizes <expr>, answers every distinct miss with
rc_oracle.rc, appends it to the table CaTTExp.Generated.<TableName>, and
repeats until no miss is left or a miss cannot be answered. The table's
certification module (<TableName>Check) is written at the end; check it
with Agda separately (it runs the certified checker on every entry).

Set CATT_SRC to the src/ directory to work in (default: this repo's src/).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import agda_bridge as B
import rc_oracle as R

def driver(path, table, expr, imports):
    lines = ['module RCLoopDriver where', '',
             'open import CaTTExp.Prelude', 'open import CaTTExp.Pure hiding (build)',
             'open import CaTTExp.RCOracle using (fromTable)',
             'import CaTTExp.Generated.%s as T' % table]
    lines += ['open import %s' % m for m in imports]
    lines += ['', 'TBL = T.rc', '', 'misses = %s' % expr, '']
    with open(path, 'w') as f:
        f.write('\n'.join(lines))

def list_maybe_query(path, expr):
    e = B.parse(B.normalize(path, expr))
    out = []
    for m in B.to_list(e):
        if m == ('con', 'nothing', ()):
            out.append(None)
            continue
        assert m[0] == 'con' and m[1] == 'just', m
        tup = m[2][0]
        G, A, t, u = tup[1]
        out.append((B.to_ctx(G), B.to_ty(A), B.to_tm(t), B.to_tm(u)))
    return out

BASE = 1000000   # placeholder answers are var (BASE + i)

def expand_tm(t, real):
    if t[0] == 'v':
        return real.get(t[1], t)
    return ('coh', t[1], t[2], tuple(expand_tm(a, real) for a in t[3]))

def expand_ty(A, real):
    if A == R.STAR:
        return A
    return R.arr(expand_ty(A[1], real), expand_tm(A[2], real), expand_tm(A[3], real))

def expand_q(q, real):
    G, A, t, u = q
    return (tuple(expand_ty(B, real) for B in G), expand_ty(A, real), expand_tm(t, real), expand_tm(u, real))

def main(table, expr, imports, workdir, max_rounds=50):
    """Rounds run against a *placeholder* table: the i-th answer is the
    fresh variable `var (BASE + i)`, so the normal forms Agda prints stay
    small. The construction treats rc answers as opaque raw terms (ConeRC's
    `raw w a b` takes its type from a, b), so substituting the real answers
    for the placeholders gives exactly the queries the real table meets.
    The real table is written at the end."""
    import pickle
    ph = table + 'Placeholders'
    ph_rows = []          # (placeholder query, var BASE+i)
    real = {}             # BASE+i -> real answer
    answered = []         # (expanded query, real answer)
    seen = set()
    dpath = os.path.join(workdir, 'RCLoopDriver.agda')
    def write_ph():
        with open(os.path.join(R.GEN, ph + '.agda'), 'w') as f:
            f.write(R.emit_table(ph, ph_rows, 'Placeholder answers for rc_loop.py.'))
    write_ph()
    for rnd in range(max_rounds):
        driver(dpath, ph, expr, imports)
        misses = list_maybe_query(dpath, 'misses')
        todo = []
        for q in misses:
            if q is not None and q not in seen:
                seen.add(q); todo.append(q)
        print('round %d: %d misses, %d new' % (rnd, sum(q is not None for q in misses), len(todo)), flush=True)
        if not todo:
            break
        stuck = []
        for q in todo:
            G, A, t, u = eq = expand_q(q, real)
            w = R.rc(G, A, t, u)
            if w is None:
                stuck.append(eq)
                continue
            i = BASE + len(ph_rows)
            ph_rows.append(q + (R.v(i),))
            real[i] = w
            answered.append(eq + (w,))
        with open(os.path.join(workdir, 'answered.pkl'), 'wb') as f:
            pickle.dump((answered, stuck), f)
        write_ph()
        if stuck:
            print('unanswerable queries: %d (saved in answered.pkl)' % len(stuck), flush=True)
            break
    with open(os.path.join(R.GEN, table + '.agda'), 'w') as f:
        f.write(R.emit_table(table, answered))
    with open(os.path.join(R.GEN, table + 'Check.agda'), 'w') as f:
        f.write(R.emit_check(table))
    print('wrote %s with %d entries' % (table, len(answered)))
    return answered

if __name__ == '__main__':
    table, expr = sys.argv[1], sys.argv[2]
    imports = sys.argv[3:]
    wd = os.environ.get('RC_WORKDIR') or os.path.join(R.GEN, '..', '..')
    main(table, expr, imports, wd)
