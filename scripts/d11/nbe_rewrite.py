"""D11: the N/beta/eta rewriting system for 1-cells of the free Gray-monoidal biclosed 2-category G
(answered/gray-biclosed-coherence-2026-11-19.md, Followup 2 section 1).

Syntax.
  formula = nonempty tuple of factors; factor = ('a',name) | ('L',A,Z) for A\\Z | ('R',Z,A) for Z/A
  triple  = (Lctx, q, Rctx), with contexts tuples of factors
  q       = ('g',name,src,tgt) | ('e',d,A,Z) | ('k',d,A,Z,X,body)   (body: tuple of triples, T_a X -> Z)
  word    = tuple of triples, with its source carried separately

Checks, on random terms built from a seed by random inverse reductions (N-, beta-, eta-expansions,
generator insertions, also inside curry bodies):
  1. every expansion and every reduction step type-checks;
  2. every reduction step preserves the weight in the polarized model P (closed-structure.md F.6 item 4),
     i.e. the rules are sound in a nontrivial model;
  3. confluence: all normal forms coincide (exhaustively for small terms, otherwise many random strategies),
     and they equal the normal form of the seed;
  4. every reduction sequence followed has length <= C(n,2) + floor(n/2).
"""
import random, sys, itertools
sys.setrecursionlimit(10000)

def T(d,A,X): return A+X if d=='L' else X+A
def H(d,A,Z): return (('L',A,Z),) if d=='L' else (('R',Z,A),)
def srcq(q):
    if q[0]=='g': return q[2]
    if q[0]=='e': return T(q[1],q[2],H(q[1],q[2],q[3]))
    return q[4]
def tgtq(q):
    if q[0]=='g': return q[3]
    if q[0]=='e': return q[3]
    return H(q[1],q[2],q[3])
def tsrc(t): return t[0]+srcq(t[1])+t[2]
def ttgt(t): return t[0]+tgtq(t[1])+t[2]
def wrap(d,A,t):          # T_a[t]
    return (A+t[0],t[1],t[2]) if d=='L' else (t[0],t[1],t[2]+A)
def strip(d,A,t):
    L,q,R=t
    if d=='L':
        return (L[len(A):],q,R) if L[:len(A)]==A else None
    return (L,q,R[:len(R)-len(A)]) if len(R)>=len(A) and R[len(R)-len(A):]==A else None
def ctx(C,t): return (C[0]+t[0],t[1],t[2]+C[1])

class TypeErr(Exception): pass
def check(word,src):
    cur=src
    for t in word:
        if not t[0]+srcq(t[1])+t[2]==cur: raise TypeErr((cur,t))
        if t[1][0]=='k':
            _,d,A,Z,X,body=t[1]
            if len(X)==0 or len(Z)==0: raise TypeErr('empty')
            if check(body,T(d,A,X))!=Z: raise TypeErr('body')
        cur=ttgt(t)
    return cur

def nodes(word):
    n=0
    for t in word:
        n+=1
        if t[1][0]=='k': n+=nodes(t[1][5])
    return n

# ---------- reductions ----------
def reducts(word):
    out=[]
    for i,t in enumerate(word):
        q=t[1]
        if q[0]=='k':
            _,d,A,Z,X,body=q
            for b2 in reducts(body):
                out.append(word[:i]+((t[0],('k',d,A,Z,X,b2),t[2]),)+word[i+1:])
            # eta
            if body and body[-1]==((),('e',d,A,Z),()):
                g=[strip(d,A,b) for b in body[:-1]]
                if all(x is not None for x in g):
                    out.append(word[:i]+tuple(ctx((t[0],t[2]),x) for x in g)+word[i+1:])
        if i+1<len(word):
            t2=word[i+1]; q2=t2[1]
            CL,CR=t2[0],t2[2]
            # N
            if q2[0]=='k' and t[0][:len(CL)]==CL and len(t[2])>=len(CR) and t[2][len(t[2])-len(CR):]==CR:
                _,d,A,Z,X,body=q2
                D0=(t[0][len(CL):],t[1],t[2][:len(t[2])-len(CR)])
                Xn=tsrc(D0)
                if len(Xn)>0:
                    out.append(word[:i]+((CL,('k',d,A,Z,Xn,(wrap(d,A,D0),)+body),CR),)+word[i+2:])
            # beta
            if q2[0]=='e' and q[0]=='k' and q[1:4]==q2[1:4]:
                d,A=q2[1],q2[2]
                ok = (t[0]==CL+A and t[2]==CR) if d=='L' else (t[0]==CL and t[2]==A+CR)
                if ok:
                    out.append(word[:i]+tuple(ctx((CL,CR),b) for b in q[5])+word[i+2:])
    return out

# ---------- polarized weight model (F.6 item 4) ----------
VEC={}
def vec(F):
    p=n=0
    for f in F:
        if f[0]=='a':
            if f[1] not in VEC: k=random.randint(0,3); VEC[f[1]]=(k,k)
            a,b=VEC[f[1]]
        elif f[0]=='L': (za,zb),(aa,ab)=vec(f[2]),vec(f[1]); a,b=za+ab,zb+aa
        else: (za,zb),(aa,ab)=vec(f[1]),vec(f[2]); a,b=za+ab,zb+aa
        p+=a; n+=b
    return (p,n)
GW={}
def P(F): return vec(F)[0]
def wq(q):
    if q[0]=='g':
        if q[1] not in GW: GW[q[1]]=random.randint(-5,5)
        return GW[q[1]]
    if q[0]=='e':
        d,A,Z=q[1],q[2],q[3]
        return P(A)*(P(srcq(q))-P(Z)) if d=='L' else 0
    _,d,A,Z,X,body=q
    wf=weight(body); df=P(T(d,A,X))-P(Z)
    return wf-P(A)*df if d=='L' else wf
def weight(word):
    return sum(wq(t[1])+P(t[0])*(P(srcq(t[1]))-P(tgtq(t[1]))) for t in word)

# ---------- random terms via expansions ----------
NAMES=itertools.count()
def ratom(): return (('a','x%d'%random.randint(0,3)),)
def rformula(depth=0):
    r=random.random()
    if depth>1 or r<0.55: return ratom()
    if r<0.7: return rformula(depth+1)+rformula(depth+1)
    A,Z=rformula(depth+1),rformula(depth+1)
    return (('L',A,Z),) if r<0.85 else (('R',Z,A),)
def objs(word,src):
    o=[src]
    for t in word: o.append(ttgt(t))
    return o
def common(seg):
    L=seg[0][0]; R=seg[0][2]
    for t in seg[1:]:
        k=0
        while k<min(len(L),len(t[0])) and L[k]==t[0][k]: k+=1
        L=L[:k]
        k=0
        while k<min(len(R),len(t[2])) and R[len(R)-1-k]==t[2][len(t[2])-1-k]: k+=1
        R=R[len(R)-k:]
    return L,R
def expand(word,src):
    """one random expansion; returns new word (same src)"""
    o=objs(word,src)
    kind=random.choice(['beta','beta','eta','eta','N','inner'])
    if kind=='inner':
        ks=[i for i,t in enumerate(word) if t[1][0]=='k']
        if not ks: kind='beta'
        else:
            i=random.choice(ks); t=word[i]; _,d,A,Z,X,body=t[1]
            nb=expand(body,T(d,A,X))
            return word[:i]+((t[0],('k',d,A,Z,X,nb),t[2]),)+word[i+1:]
    if kind=='gen':                      # not an equation: only used to build the seed
        i=len(word); ob=o[i]
        p=random.randint(0,len(ob)-1); q=random.randint(p+1,len(ob))
        g=('g','g%d'%next(NAMES),ob[p:q],rformula())
        return word[:i]+((ob[:p],g,ob[q:]),)+word[i:]
    if kind=='N':
        cands=[]
        for i,t in enumerate(word):
            if t[1][0]=='k' and t[1][5]:
                _,d,A,Z,X,body=t[1]
                b=strip(d,A,body[0])
                if b is not None and not (body[0][1][0]=='e' and len(body)==1): cands.append((i,b))
        if not cands: kind='beta'
        else:
            i,b=random.choice(cands); t=word[i]; _,d,A,Z,X,body=t[1]
            Xn=ttgt(b)
            if len(Xn)==0: return word
            return word[:i]+(ctx((t[0],t[2]),b),(t[0],('k',d,A,Z,Xn,body[1:]),t[2]))+word[i+1:]
    i=random.randint(0,len(word)); j=random.randint(i,min(len(word),i+3))
    seg=word[i:j]
    if kind=='beta':
        if seg: CL,CR=common(seg)
        else: CL,CR=(),()
        ob=o[i]
        lp=random.randint(0,len(CL)) if seg else random.randint(0,len(ob)-1)
        rp=random.randint(0,len(CR)) if seg else random.randint(0,len(ob)-lp-1)
        CL=CL[:lp] if seg else ob[:lp]
        CR=(CR[len(CR)-rp:] if rp else ()) if seg else (ob[len(ob)-rp:] if rp else ())
        f=tuple((t[0][len(CL):],t[1],t[2][:len(t[2])-len(CR)]) for t in seg)
        S=ob[len(CL):len(ob)-len(CR)]; Z=o[j][len(CL):len(o[j])-len(CR)]
        if len(S)<2 or not Z: return word
        d=random.choice('LR'); m=random.randint(1,len(S)-1)
        A,X=(S[:m],S[m:]) if d=='L' else (S[len(S)-m:],S[:len(S)-m])
        k=('k',d,A,Z,X,f)
        t1=(CL+A,k,CR) if d=='L' else (CL,k,A+CR)
        return word[:i]+(t1,(CL,('e',d,A,Z),CR))+word[j:]
    # eta
    ob=o[j]; pos=[p for p,f in enumerate(ob) if f[0] in 'LR']
    random.shuffle(pos)
    for p in pos:
        CL,CR=ob[:p],ob[p+1:]
        if all(t[0][:len(CL)]==CL and len(t[2])>=len(CR) and t[2][len(t[2])-len(CR):]==CR for t in seg):
            f=ob[p]
            d,A,Z=('L',f[1],f[2]) if f[0]=='L' else ('R',f[2],f[1])
            g=tuple((t[0][len(CL):],t[1],t[2][:len(t[2])-len(CR)]) for t in seg)
            X=o[i][len(CL):len(o[i])-len(CR)]
            if not X: continue
            body=tuple(wrap(d,A,b) for b in g)+(((),('e',d,A,Z),()),)
            return word[:i]+((CL,('k',d,A,Z,X,body),CR),)+word[j:]
    return word

def gen_append(word,src):
    ob=objs(word,src)[-1]
    p=random.randint(0,len(ob)-1); q=random.randint(p+1,len(ob))
    g=('g','g%d'%next(NAMES),ob[p:q],rformula())
    return word+((ob[:p],g,ob[q:]),)
def random_nf(word,src,rng,count):
    steps=0
    while True:
        rs=reducts(word)
        if not rs: return word,steps
        nw=rng.choice(rs); steps+=1
        assert check(nw,src)==count[1], "type changed"
        assert weight(nw)==count[0], "weight changed"
        word=nw
def all_nfs(word,limit=20000):
    seen={word}; stack=[word]; nfs=set()
    while stack:
        w=stack.pop(); rs=reducts(w)
        if not rs: nfs.add(w)
        for r in rs:
            if r not in seen:
                seen.add(r); stack.append(r)
                if len(seen)>limit: return None
    return nfs

def main(trials=3000, seed=1):
    random.seed(seed); rng=random.Random(seed+1)
    stats=dict(terms=0,exhaustive=0,maxn=0,maxsteps=0,redexes=0,fail=0)
    for _ in range(trials):
        src=rformula()
        word=()
        for _ in range(random.randint(0,3)): word=gen_append(word,src)
        seedw=word
        tg0=check(word,src); w00=weight(word)
        for _ in range(random.randint(1,16)):
            word=expand(word,src)
            assert check(word,src)==tg0 and weight(word)==w00, 'expansion changed type or weight'
        tg=check(word,src); w0=weight(word); n=nodes(word)
        stats['terms']+=1; stats['maxn']=max(stats['maxn'],n)
        stats['redexes']+=len(reducts(word))
        bound=n*(n-1)//2+n//2
        nfs=set()
        for _ in range(8):
            nf,steps=random_nf(word,src,rng,(w0,tg))
            stats['maxsteps']=max(stats['maxsteps'],steps)
            if steps>bound: stats['fail']+=1; print('BOUND',steps,bound)
            nfs.add(nf)
        if n<=14:
            ex=all_nfs(word)
            if ex is not None:
                stats['exhaustive']+=1; nfs|=ex
        snf,_=random_nf(seedw,src,rng,(weight(seedw),check(seedw,src)))
        nfs.add(snf)
        if len(nfs)!=1:
            stats['fail']+=1
            if stats['fail']<3: print('NONCONFLUENT', word, nfs)
    print(stats)
    return stats['fail']==0
if __name__=='__main__':
    ok=main(int(sys.argv[1]) if len(sys.argv)>1 else 3000)
    sys.exit(0 if ok else 1)
