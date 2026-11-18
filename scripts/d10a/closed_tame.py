import random, sys, itertools
sys.setrecursionlimit(10000)
# formulas: ('a',name) | ('I',) | ('*',A,B) | ('\\',B,A)=B\A | ('/',A,B)=A/B
I=('I',)
cnt=[0]
def fresh():
    cnt[0]+=1; return ('a','v%d'%cnt[0])
from functools import lru_cache
# ---- L*_I provability (cut-free, empty antecedents) on hashable formulas
@lru_cache(maxsize=None)
def prov(ctx,goal):
    n=len(ctx)
    if n==1 and ctx[0]==goal and goal[0]=='a': return True
    if n==0 and goal==I: return True
    if goal[0]=='\\' and prov((goal[1],)+ctx,goal[2]): return True
    if goal[0]=='/' and prov(ctx+(goal[2],),goal[1]): return True
    if goal[0]=='*':
        for k in range(n+1):
            if prov(ctx[:k],goal[1]) and prov(ctx[k:],goal[2]): return True
    for i,H in enumerate(ctx):
        if H==I and prov(ctx[:i]+ctx[i+1:],goal): return True
        if H[0]=='*' and prov(ctx[:i]+(H[1],H[2])+ctx[i+1:],goal): return True
        if H[0]=='\\':
            for j in range(i+1):
                if prov(ctx[j:i],H[1]) and prov(ctx[:j]+(H[2],)+ctx[i+1:],goal): return True
        if H[0]=='/':
            for j in range(i+1,n+1):
                if prov(ctx[i+1:j],H[2]) and prov(ctx[:i]+(H[1],)+ctx[j:],goal): return True
    return False
def nf(f):
    if f[0] in ('a','I'): return f
    a=nf(f[1]); b=nf(f[2])
    if f[0]=='*':
        if a==I: return b
        if b==I: return a
        return ('*',a,b)
    if f[0]=='\\':
        if a==I: return b
        return ('\\',a,b)
    if f[0]=='/':
        if b==I: return a
        return ('/',a,b)
def N(ctx,goal):
    ctx=[nf(h) for h in ctx]; goal=nf(goal)
    changed=True
    while changed:
        changed=False
        ctx=[h for h in ctx if h!=I]
        for i,h in enumerate(ctx):
            if h[0]=='*': ctx=ctx[:i]+[h[1],h[2]]+ctx[i+1:]; changed=True; break
        if goal[0]=='\\': ctx=[goal[1]]+ctx; goal=goal[2]; changed=True
        elif goal[0]=='/': ctx=ctx+[goal[2]]; goal=goal[1]; changed=True
    return ctx,goal
def hasI(f):
    if f==I: return True
    if f[0]=='a': return False
    return hasI(f[1]) or hasI(f[2])
def tame(ctx,goal):
    c,g=N(ctx,goal)
    if not c and g==I: return True
    return not any(hasI(h) for h in c+[g])
def atoms(f,acc):
    if f[0]=='a': acc.append(f[1])
    elif f[0]!='I': atoms(f[1],acc); atoms(f[2],acc)
def balanced_atoms(ctx,goal):
    occ={}
    def go(f,p):
        if f[0]=='a': occ.setdefault(f[1],[]).append(p)
        elif f[0]=='*': go(f[1],p); go(f[2],p)
        elif f[0]=='\\': go(f[1],-p); go(f[2],p)
        elif f[0]=='/': go(f[1],p); go(f[2],-p)
    for h in ctx: go(h,-1)
    go(goal,1)
    return all(sorted(v)==[-1,1] for v in occ.values())
# ---- random formula shapes
def rshape(d):
    if d==0 or random.random()<0.35: return ['L']
    return [random.choice('*\\/'),rshape(d-1),rshape(d-1)]
def decorate(f):
    # randomly wrap subformulas with removable units
    if random.random()<0.25:
        k=random.randrange(4)
        f=[('*',I,f),('*',f,I),('\\',I,f),('/',f,I)][k]
    if f[0] in ('a','I'): return f
    return (f[0],decorate(f[1]),decorate(f[2]))
def gen_coh(maxtries=200):
    for _ in range(maxtries):
        nh=random.choice([0,0,1,1,2])
        shapes=[rshape(2) for _ in range(nh+1)]
        leaves=[]
        def cnt_(s): return 1 if s[0]=='L' else cnt_(s[1])+cnt_(s[2])
        L=sum(cnt_(s) for s in shapes)
        if L%2: continue
        names=list(range(L//2))*2; random.shuffle(names)
        it=iter(names)
        def fill(s):
            if s[0]=='L': return ('a','x%d'%next(it))
            return (s[0],fill(s[1]),fill(s[2]))
        fs=[fill(s) for s in shapes]
        ctx,goal=tuple(fs[:-1]),fs[-1]
        if not balanced_atoms(ctx,goal): continue
        if not prov(ctx,goal): continue
        # decorate with units
        ctx=tuple(decorate(h) for h in ctx); goal=decorate(goal)
        if random.random()<0.2:
            k=random.randrange(len(ctx)+1); ctx=ctx[:k]+(I,)+ctx[k:]
        assert tame(ctx,goal)
        return ctx,goal
    return None
def rename(ctx,goal):
    m={}
    def r(f):
        if f[0]=='a':
            if f[1] not in m: m[f[1]]=fresh()
            return m[f[1]]
        if f[0]=='I': return f
        return (f[0],r(f[1]),r(f[2]))
    return tuple(r(h) for h in ctx), r(goal)
# unification
def walk(t,s):
    while t[0]=='a' and t[1] in s: t=s[t[1]]
    return t
def occurs(v,t,s):
    t=walk(t,s)
    if t[0]=='a': return t[1]==v
    if t[0]=='I': return False
    return occurs(v,t[1],s) or occurs(v,t[2],s)
def unify(a,b,s):
    a=walk(a,s); b=walk(b,s)
    if a==b: return True
    if a[0]=='a':
        if occurs(a[1],b,s): return False
        s[a[1]]=b; return True
    if b[0]=='a': return unify(b,a,s)
    if a[0]!=b[0]: return False
    if a[0]=='I': return True
    return unify(a[1],b[1],s) and unify(a[2],b[2],s)
def res(t,s):
    t=walk(t,s)
    if t[0] in ('a','I'): return t
    return (t[0],res(t[1],s),res(t[2],s))
COHS=[]
def closed_tree(depth,s):
    """returns goal formula (unresolved) of a random closed tree, or None"""
    cands=[c for c in COHS if (depth>0 or len(c[0])==0)]
    ctx,goal=rename(*random.choice(cands))
    for h in ctx:
        g=closed_tree(depth-1,s) if depth>0 else None
        if g is None: return None
        if not unify(h,g,s): return None
    return goal
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
while len(COHS)<400:
    c=gen_coh()
    if c: COHS.append(c)
COHS += [((),I),((I,),I),((I,('a','y')),('a','y'))]
print("cohs",len(COHS),"nullary",sum(1 for c in COHS if not c[0]))
tries=ok=bad=0
for _ in range(200000):
    s={}
    g=closed_tree(random.choice([1,2,3]),s)
    if g is None: continue
    G=res(g,s); tries+=1
    if not balanced_atoms((),G): print("UNBALANCED",G); break
    if tame((),G): ok+=1
    else:
        bad+=1
        if bad<=5: print("UNTAME closed generalization:",G)
print("closed trees:",tries,"tame:",ok,"untame:",bad)
