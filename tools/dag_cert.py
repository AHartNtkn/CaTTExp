"""
Export a CaTT typing problem (G, A, w) as a sharing-aware certificate for the
Agda DAG checker (src/CaTTExp/Dag/).

A certificate is one table of items in a single id space, every reference
pointing to a smaller id (so the table is a topologically sorted DAG):

  ('V', i)          the variable of level i
  ('C', h, args)    coh over head h, applied to the nodes args
  ('E',)            the empty context
  ('S', c, T)       context c extended by the type T
  ('H', c, T)       a coherence head: pasting context c, type T (T nonempty)

A type T is a tuple of (source, target) node pairs, bottom dimension first:
() is *, T + ((s, t),) is s ->_T t.

Next to the table: typing claims J[(c, n)] = T ("in context c, node n has type
T"), closed under what checking them needs, and free-variable claims F[n]
(sorted) for the nodes the side conditions of heads look at. The claims are
untrusted hints: the Agda checker verifies each one locally.
"""
import sys
sys.setrecursionlimit(1000000)

NVARS = 256

class Cert:
    def __init__(self):
        self.items = []          # id -> item
        self.key = {}            # item -> id   (hash-consing by value)
        self.ctx_entries = {}    # ctx id -> list of type tuples (level order)
        self.J = {}              # (c, n) -> T
        self.F = {}              # n -> tuple of levels (sorted)
        self.tm_memo = {}        # id(python term) -> (term, node id)
        self.ty_memo = {}
        self.ctx_memo = {}
        # ids 0..NVARS-1 are the variables of those levels (the checker
        # recognises them without a lookup)
        for i in range(NVARS):
            self.mk(('V', i))

    def mk(self, it):
        i = self.key.get(it)
        if i is None:
            i = len(self.items)
            self.items.append(it)
            self.key[it] = i
            if it[0] == 'E':
                self.ctx_entries[i] = ()
            elif it[0] == 'S':
                self.ctx_entries[i] = self.ctx_entries[it[1]] + (it[2],)
        return i

    # ---------------------------------------------------------- interning
    def tm(self, t):
        st = [t]
        memo = self.tm_memo
        while st:
            x = st[-1]
            h = memo.get(id(x))
            if h is not None and h[0] is x:
                st.pop(); continue
            if x[0] == 'v':
                memo[id(x)] = (x, self.mk(('V', x[1]))); st.pop(); continue
            pend = [u for u in x[3] if not (memo.get(id(u)) and memo[id(u)][0] is u)]
            if pend:
                st.extend(pend); continue
            st.pop()
            hd = self.head(x[1], x[2])
            memo[id(x)] = (x, self.mk(('C', hd, tuple(memo[id(u)][1] for u in x[3]))))
        return memo[id(t)][1]

    def ty(self, A):
        h = self.ty_memo.get(id(A))
        if h is not None and h[0] is A:
            return h[1]
        if A == ('*',):
            r = ()
        else:
            r = self.ty(A[1]) + ((self.tm(A[2]), self.tm(A[3])),)
        self.ty_memo[id(A)] = (A, r)
        return r

    def ctx(self, P):
        h = self.ctx_memo.get(id(P))
        if h is not None and h[0] is P:
            return h[1]
        c = self.mk(('E',))
        for B in P:
            T = self.ty(B)
            c = self.mk(('S', c, T))
        self.ctx_memo[id(P)] = (P, c)
        return c

    def head(self, P, A):
        c = self.ctx(P)
        T = self.ty(A)
        assert T, 'coh at *'
        return self.mk(('H', c, T))

    # ---------------------------------------------------------- instantiation
    def inst_ty(self, T, sigma, memo):
        return tuple((self.inst(s, sigma, memo), self.inst(t, sigma, memo)) for (s, t) in T)

    def inst(self, n, sigma, memo):
        r = memo.get(n)
        if r is not None:
            return r
        st = [n]
        while st:
            x = st[-1]
            if x in memo:
                st.pop(); continue
            it = self.items[x]
            if it[0] == 'V':
                memo[x] = sigma[it[1]]; st.pop(); continue
            pend = [a for a in it[2] if a not in memo]
            if pend:
                st.extend(pend); continue
            st.pop()
            memo[x] = self.mk(('C', it[1], tuple(memo[a] for a in it[2])))
        return memo[n]

    # ---------------------------------------------------------- claims
    def close(self, c0, n0=None):
        """Add the typing claims needed to check (c0, n0), and the contexts
        (with n0 None: the claims needed to check the context c0)."""
        todo = [('J', c0, n0)] if n0 is not None else [('X', c0)]
        done_ctx, done_head = set(), set()
        while todo:
            k = todo.pop()
            if k[0] == 'J':
                _, c, n = k
                if (c, n) in self.J:
                    continue
                todo.append(('X', c))
                it = self.items[n]
                if it[0] == 'V':
                    ents = self.ctx_entries[c]
                    assert it[1] < len(ents), 'variable out of range'
                    self.J[(c, n)] = ents[it[1]]
                else:
                    _, h, args = it
                    _, ch, T = self.items[h]
                    assert len(args) == len(self.ctx_entries[ch]), 'substitution length'
                    self.J[(c, n)] = self.inst_ty(T, args, {})
                    for a in args:
                        todo.append(('J', c, a))
                    if h not in done_head:
                        done_head.add(h)
                        todo.append(('X', ch))
                        for (s, t) in T:
                            todo.append(('J', ch, s)); todo.append(('J', ch, t))
                            self.fv(s); self.fv(t)
            else:
                _, c = k
                if c in done_ctx:
                    continue
                done_ctx.add(c)
                it = self.items[c]
                if it[0] == 'S':
                    todo.append(('X', it[1]))
                    for (s, t) in it[2]:
                        todo.append(('J', it[1], s)); todo.append(('J', it[1], t))

    def fv(self, n):
        st = [n]
        while st:
            x = st[-1]
            if x in self.F:
                st.pop(); continue
            it = self.items[x]
            if it[0] == 'V':
                self.F[x] = (it[1],); st.pop(); continue
            pend = [a for a in it[2] if a not in self.F]
            if pend:
                st.extend(pend); continue
            st.pop()
            s = set()
            for a in it[2]:
                s.update(self.F[a])
            self.F[x] = tuple(sorted(s))
        return self.F[n]


def build(G, A, w):
    C = Cert()
    g = C.ctx(G)
    n = C.tm(w)
    T = C.ty(A)
    C.close(g, n)
    C.close_ctx = g
    return C, g, n, T

def stats(C):
    from collections import Counter
    kinds = Counter(it[0] for it in C.items)
    nargs = sum(len(C.items[n][2]) for (c, n) in C.J if C.items[n][0] == 'C')
    ctxs = Counter(c for (c, n) in C.J)
    fsz = sum(len(v) for v in C.F.values())
    fwork = sum(sum(len(C.F[a]) for a in C.items[n][2]) for n in C.F if C.items[n][0] == 'C')
    # instantiation work: DAG size of each judged coh node's head type
    hsz = {}
    def dagsize(T):
        seen = set(); st = [x for p in T for x in p]
        while st:
            x = st.pop()
            if x in seen: continue
            seen.add(x)
            it = C.items[x]
            if it[0] == 'C': st.extend(it[2])
        return len(seen)
    iw = 0
    for (c, n) in C.J:
        it = C.items[n]
        if it[0] == 'C':
            h = it[1]
            if h not in hsz: hsz[h] = dagsize(C.items[h][2])
            iw += hsz[h]
    return dict(items=len(C.items), kinds=dict(kinds), judgments=len(C.J), contexts_judged=len(ctxs),
                arg_slots=nargs, F=len(C.F), F_total=fsz, F_merge_work=fwork, inst_work=iw)

if __name__ == '__main__':
    import pickle, time
    t0 = time.time()
    G, A, t, u, w = pickle.load(open(sys.argv[1], 'rb'))
    sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
    from catt import arr
    C, g, n, T = build(G, arr(A, t, u), w)
    print('built in %.0f s' % (time.time() - t0))
    print(stats(C))
    print('root claim matches query:', C.J[(g, n)] == T)
    pickle.dump((C.items, C.J, C.F, g, n, T), open(sys.argv[2], 'wb'))


# ---------------------------------------------------------------- Agda emission
#
# Everything is a stream of naturals, each written in base 32, most
# significant digit first: digits that continue the number are the
# characters ']'..'|' (codes 93..124), the last digit of a number is one
# of '0'..'O' (codes 48..79). The stream is cut into string literals of
# at most CHUNK characters.

CHUNK = 1 << 20

def enc(n):
    ds = [n & 31]
    n >>= 5
    while n:
        ds.append(n & 31); n >>= 5
    ds.reverse()
    return ''.join(chr(93 + d) for d in ds[:-1]) + chr(48 + ds[-1])

def rty_nums(T):
    out = [len(T)]
    for (s, t) in T:
        out += [s, t]
    return out

# Packed entries (CaTTExp.Dag.Run.unpack): the list x0, x1, ... as the
# number (x0+1) + PB*((x1+1) + PB*(...)), 0 for the empty list. Every
# table entry is one such number, kept in a bucket map
# (CaTTExp.Dag.NatMap): one big number per entry costs far less memory
# in Agda's evaluator than a list or a trie node.
PB = 1 << 24
BUCKET = 16

def pack(xs):
    r = 0
    for x in reversed(list(xs)):
        assert 0 <= x < PB - 1
        r = r * PB + x + 1
    return r

def flat(T):
    return [v for st in T for v in st]

def item_list(it):
    k = it[0]
    if k == 'V': return [0, it[1]]
    if k == 'C': return [1, it[1]] + list(reversed(it[2]))
    if k == 'E': return [2]
    if k == 'S': return [3, it[1]] + flat(it[2])
    if k == 'H': return [4, it[1]] + flat(it[2])
    raise ValueError(k)

def bucket_stream(entries):
    """entries: dict key -> packed value (non-zero). Stream of buckets
    "q v0 ... v15" (Run.bucketsGo)."""
    by = {}
    for k, v in entries.items():
        assert v != 0
        by.setdefault(k // BUCKET, [0] * BUCKET)[k % BUCKET] = v
    out = []
    for q in sorted(by):
        out += [q] + by[q]
    return out, len(by)

def chunks(nums):
    s = ''.join(enc(n) for n in nums)
    return [s[i:i + CHUNK] for i in range(0, len(s), CHUNK)] or ['']

def items_stream(items):
    return bucket_stream({i: pack(item_list(it)) for i, it in enumerate(items)})[0]

def streams(items, J, F):
    R = items_stream(items)
    by = {}
    for (c, n), T in J.items():
        by.setdefault(c, {})[n] = pack([1] + flat(T))
    Js = []
    for c in sorted(by):
        bs, m = bucket_stream(by[c])
        Js += [c, m] + bs
    Fs = bucket_stream({n: pack([1] + list(xs)) for n, xs in F.items()})[0]
    return R, Js, Fs

def agda_strlist(name, cs):
    return '%s : List String\n%s =\n' % (name, name) + ''.join('  "%s" ∷\n' % c for c in cs) + '  []\n'

# Chunks per data module. Agda needs memory proportional to a module's
# source size to check it (an 82 MB module took 6 GB), so large tables
# are split over part modules, checked one at a time.
PART_CHUNKS = 8

def data_hdr(m):
    return ['-- Generated by tools/dag_cert.py. Do not edit.',
            'module %s where' % m, '',
            'open import CaTTExp.Prelude',
            'open import Agda.Builtin.String using (String)', '']

def emit_streams(modname, named):
    """Header and definitions of a module defining the given string lists
    (name, stream), with large ones in part modules (returned too)."""
    parts = {}
    out = data_hdr(modname)
    defs = []
    for name, stream in named:
        cs = chunks(stream)
        if len(cs) <= PART_CHUNKS:
            defs.append(agda_strlist(name, cs))
            continue
        names = []
        for k in range(0, len(cs), PART_CHUNKS):
            pm = '%s%s%d' % (modname, name[0].upper() + name[1:], k // PART_CHUNKS)
            pn = '%s%d' % (name, k // PART_CHUNKS)
            parts[pm] = '\n'.join(data_hdr(pm) + [agda_strlist(pn, cs[k:k + PART_CHUNKS])])
            out.append('open import %s' % pm)
            names.append(pn)
        defs.append('%s : List String\n%s = %s\n' % (name, name, ' ++ '.join(names)))
    out.append('')
    return out + defs, parts

def emit_data(modname, items, J, F, g, n, T):
    """The data module, and the part modules it imports (name -> source)."""
    R, Js, Fs = streams(items, J, F)
    out, parts = emit_streams(modname, (('itemsS', R), ('claimsS', Js), ('fvS', Fs)))
    out.append('varsK rootCtx rootTm : Nat\nvarsK = %d\nrootCtx = %d\nrootTm = %d\n' % (NVARS, g, n))
    out.append('rootTy : List Nat\nrootTy = %s[]\n' % ''.join('%d ∷ ' % x for x in rty_nums(T)))
    return '\n'.join(out), parts

def emit_query(modname, G, A):
    """The query in ordinary syntax (hash-consed into top-level Agda
    definitions, which Agda unfolds as trees: fine for a query)."""
    from emit_agda import Emitter
    E = Emitter()
    g = E.ctx(G); a = E.ty(A)
    out = ['-- Generated by tools/dag_cert.py. Do not edit.',
           'module %s where' % modname, '',
           'open import CaTTExp.Prelude', 'open import CaTTExp.Pure', '',
           'v : Nat → Tm', 'v = var', '']
    out += E.defs
    out += ['queryCtx : Ctx', 'queryCtx = %s' % g, '',
            'queryTy : Ty', 'queryTy = %s' % a, '']
    return '\n'.join(out)

def emit_qtable(modname, G, A):
    """The query as its own hash-consed table, in the item format. The
    statement proved is about its unfolding (Run.queryCtxOf/queryTyOf);
    the checker compares it with the certificate's root by ids."""
    Q = Cert()
    qg = Q.ctx(G)
    T = Q.ty(A)
    out, parts = emit_streams(modname, (('queryS', items_stream(Q.items)),))
    out.append('qCtx : Nat\nqCtx = %d\n' % qg)
    out.append('qTy : List Nat\nqTy = %s[]\n' % ''.join('%d ∷ ' % x for x in rty_nums(T)))
    return '\n'.join(out), len(Q.items), parts

def emit_check(modname, data, query, qtable, tree_query):
    imports = ['open import %s' % data, 'open import %s' % qtable]
    if tree_query:
        imports.append('open import %s' % query)
    out = [
        '-- Generated by tools/dag_cert.py. Do not edit.',
        '-- The DAG checker accepts the certificate: by evaluation (refl).',
        'module %s where' % modname, '',
        'open import CaTTExp.Prelude', 'open import CaTTExp.Pure',
        'open import CaTTExp.Dag.Run',
        'open import CaTTExp.Dag.Sound using (certifiedQ; queryMatches-sound)'] + imports + ['',
        'accepted : runCertQ varsK itemsS claimsS fvS queryS rootCtx rootTm rootTy qCtx qTy ≡ true',
        'accepted = refl', '',
        '-- A genuine CaTT derivation of the query (the unfolding of the query table).',
        'answer : Σ Tm (λ w → queryCtxOf queryS qCtx ⊢tm w ∶ queryTyOf queryS qTy)',
        'answer = certifiedQ varsK itemsS claimsS fvS queryS rootCtx rootTm rootTy qCtx qTy accepted', '']
    if tree_query:
        out += [
            '-- The query table unfolds to the query in ordinary syntax.',
            'query-ok : queryMatches queryS qCtx qTy queryCtx queryTy ≡ true',
            'query-ok = refl', '',
            'answer′ : Σ Tm (λ w → queryCtx ⊢tm w ∶ queryTy)',
            'answer′ with queryMatches-sound queryS qCtx qTy queryCtx queryTy query-ok',
            '... | eΓ , eB = subst₂ (λ Γ B → Σ Tm (λ w → Γ ⊢tm w ∶ B)) eΓ eB answer',
            '  where',
            '  subst₂ : ∀ {X Y : Set} (P : X → Y → Set) {x x\' y y\'} → x ≡ x\' → y ≡ y\' → P x y → P x\' y\'',
            '  subst₂ P refl refl q = q', '']
    return '\n'.join(out)

def emit_all(prefix, G, A, w, outdir, tree_query=True):
    import os
    C, g, n, T = build(G, A, w)
    base = 'CaTTExp.Generated.' + prefix
    qsrc, qn, qparts = emit_qtable(base + 'QTable', G, A)
    dsrc, parts = emit_data(base + 'Data', C.items, C.J, C.F, g, n, T)
    files = {prefix + 'Data': dsrc,
             prefix + 'QTable': qsrc,
             prefix + 'Check': emit_check(base + 'Check', base + 'Data', base + 'Query',
                                          base + 'QTable', tree_query)}
    if tree_query:
        files[prefix + 'Query'] = emit_query(base + 'Query', G, A)
    for m, src in list(parts.items()) + list(qparts.items()):
        files[m[len('CaTTExp.Generated.'):]] = src
    for k, s in files.items():
        with open(os.path.join(outdir, k + '.agda'), 'w') as f:
            f.write(s)
    st = stats(C)
    st['query_items'] = qn
    return C, st


def emit_ctx_all(prefix, G, outdir):
    """A certificate that the context G is well formed (Sound.certifiedCtxQ)."""
    import os
    C = Cert()
    g = C.ctx(G)
    C.close(g)
    base = 'CaTTExp.Generated.' + prefix
    qsrc, qn, qparts = emit_qtable(base + 'QTable', G, ('*',))
    dsrc, parts = emit_data(base + 'Data', C.items, C.J, C.F, g, 0, ())
    check = '\n'.join([
        '-- Generated by tools/dag_cert.py. Do not edit.',
        '-- The DAG checker accepts the certificate: by evaluation (refl).',
        'module %s where' % (base + 'Check'), '',
        'open import CaTTExp.Prelude', 'open import CaTTExp.Pure',
        'open import CaTTExp.Dag.Run',
        'open import CaTTExp.Dag.Sound using (certifiedCtxQ)',
        'open import %s' % (base + 'Data'), 'open import %s' % (base + 'QTable'), '',
        'accepted : runCtxQ varsK itemsS claimsS fvS queryS rootCtx qCtx ≡ true',
        'accepted = refl', '',
        '-- The context (the unfolding of the query table) is well formed.',
        'wf : queryCtxOf queryS qCtx ⊢ctx',
        'wf = certifiedCtxQ varsK itemsS claimsS fvS queryS rootCtx qCtx accepted', ''])
    files = {prefix + 'Data': dsrc, prefix + 'QTable': qsrc, prefix + 'Check': check}
    for m, src in list(parts.items()) + list(qparts.items()):
        files[m[len('CaTTExp.Generated.'):]] = src
    for k, src in files.items():
        with open(os.path.join(outdir, k + '.agda'), 'w') as f:
            f.write(src)
    st = stats(C)
    st['query_items'] = qn
    return C, st
