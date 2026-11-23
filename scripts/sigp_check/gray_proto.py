"""Python prototype of the Gray support model of P (src/CaTTExp/Uniform/FreeGray.agda).

Reads every term of reachability_theory.py's presentation (as dumped in py.txt) as a
table of symbolic supports and checks every operation boundary and equation schema.
Run: python3 scripts/sigp_check/gray_proto.py   (expects "166 checked 0 fail").
"""
import re, sys
lines=[l for l in open(__import__('pathlib').Path(__file__).with_name('py.txt')).read().split('\n') if l]
def parse(s):
    toks=re.findall(r'\(|\)|[^\s()]+',s); pos=[0]
    def go():
        t=toks[pos[0]]; pos[0]+=1
        if t=='(':
            head=toks[pos[0]]; pos[0]+=1; args=[]
            while toks[pos[0]]!=')': args.append(go())
            pos[0]+=1; return (head,*args)
        return t
    return go()
# supports: frozenset of tuples of symbols. Table: dict lo,hi,lv:list of (s,t) for i=1..n-1, top, n
def sym(x): return frozenset({(x,)})
EMPTY=frozenset(); UNIT=frozenset({()})
def prod(A,B): return frozenset(a+b for a in A for b in B)
def un(A,B): return A|B
def var(name,d):
    if d==0: return dict(n=0,lo='lo:'+name,hi='lo:'+name)
    return dict(n=d,lo='lo:'+name,hi='hi:'+name,lv=[(sym(f's{i}:{name}'),sym(f't{i}:{name}')) for i in range(1,d)],top=sym('top:'+name))
def face(x,tgt):
    n=x['n']; assert n>=1
    if n==1: o=x['hi'] if tgt else x['lo']; return dict(n=0,lo=o,hi=o)
    return dict(n=n-1,lo=x['lo'],hi=x['hi'],lv=x['lv'][:n-2],top=x['lv'][n-2][1 if tgt else 0])
def ident(x):
    n=x['n']
    if n==0: return dict(n=1,lo=x['lo'],hi=x['hi'],lv=[],top=UNIT)
    return dict(n=n+1,lo=x['lo'],hi=x['hi'],lv=x['lv']+[(x['top'],x['top'])],top=EMPTY)
def comp(x,y):
    n=x['n']; assert y['n']==n
    if n==1: return dict(n=1,lo=x['lo'],hi=y['hi'],lv=[],top=prod(x['top'],y['top']))
    return dict(n=n,lo=x['lo'],hi=y['hi'],lv=[(a[0],b[1]) for a,b in zip(x['lv'],y['lv'])],top=un(x['top'],y['top']))
def whisk(a,x,left):
    k=a['n']; n=x['n']; assert k<n
    L,R=(a,x) if left else (x,a)
    lv=[]
    for i in range(1,n):
        if i<k: lv.append((L['lv'][i-1][0],R['lv'][i-1][1]))
        elif k==1: lv.append(tuple(prod(a['top'],x['lv'][i-1][j]) if left else prod(x['lv'][i-1][j],a['top']) for j in (0,1)))
        elif i==k: lv.append(tuple(un(a['top'],x['lv'][i-1][j]) for j in (0,1)))
        else: lv.append(x['lv'][i-1])
    top = (prod(a['top'],x['top']) if left else prod(x['top'],a['top'])) if k==1 else x['top']
    return dict(n=n,lo=L['lo'],hi=R['hi'],lv=lv,top=top)
OPS={}
for l in lines:
    if l.startswith('OP'):
        nm,g,s,t=l[3:].split('|'); OPS[nm]=(s,t)
CDIM={'chi':3,'r':4,'t':4,'iota':4,'h':4}
def cmpop(o,x,y):
    s,t=OPS[o]; env={'x0':x,'x1':y}
    S=ev(parse(s),env); T=ev(parse(t),env)
    n=CDIM[o]; assert S['n']==n-1==T['n']
    if o=='iota': top=EMPTY
    elif o=='h': top=prod(x['top'],face(y,True)['top'])
    else: top=prod(x['top'],y['top'])
    lv=[(a[0],b[1]) for a,b in zip(S['lv'],T['lv'])]+[(S['top'],T['top'])]
    return dict(n=n,lo=S['lo'],hi=T['hi'],lv=lv,top=top)
def ev(t,env):
    if isinstance(t,str): return env[t]
    h=t[0]; a=[ev(u,env) for u in t[1:]]
    m=re.fullmatch(r'([st])(\d+)',h)
    if m: assert a[0]['n']==int(m.group(2)); return face(a[0],m.group(1)=='t')
    if h.startswith('id'): return ident(a[0])
    if h.startswith('comp'): return comp(*a)
    if h.startswith('left'): return whisk(a[0],a[1],True)
    if h.startswith('right'): return whisk(a[1],a[0],False)
    return cmpop(h,*a)
# guards -> substitution (union-find on symbols, plus symbol:=expr)
def flatten(x):
    out=[('obj',x['lo']),('obj',x['hi'])]
    if x['n']>0:
        for s,t in x['lv']: out+=[('sup',s),('sup',t)]
        out.append(('sup',x['top']))
    return out
def apply(subst,x):
    def so(o):
        while o in subst['obj']: o=subst['obj'][o]
        return o
    def ss(S):
        changed=True
        while changed:
            changed=False; new=set()
            for w in S:
                ws=[frozenset({()})]
                for c in w:
                    if c in subst['sup']: ws.append(subst['sup'][c]); changed=True
                    else: ws.append(frozenset({(c,)}))
                acc=frozenset({()})
                for W in ws[1:]: acc=prod(acc,W)
                new|=acc
            S=frozenset(new)
        return S
    if x['n']==0: return dict(n=0,lo=so(x['lo']),hi=so(x['hi']))
    return dict(n=x['n'],lo=so(x['lo']),hi=so(x['hi']),lv=[(ss(a),ss(b)) for a,b in x['lv']],top=ss(x['top']))
def solve(pairs):
    subst={'obj':{},'sup':{}}
    for _ in range(20):
        for L,R in pairs:
            L=apply(subst,L); R=apply(subst,R)
            assert L['n']==R['n']
            for (k1,a),(k2,b) in zip(flatten(L),flatten(R)):
                if a==b: continue
                if k1=='obj':
                    subst['obj'][a]=b
                else:
                    if len(a)==1 and len(next(iter(a)))==1 and next(iter(a))[0] not in str(b): subst['sup'][next(iter(a))[0]]=b
                    elif len(b)==1 and len(next(iter(b)))==1: subst['sup'][next(iter(b))[0]]=a
                    else: return subst,('stuck',a,b)
    return subst,None
fails=0;total=0
for l in lines:
    if not l.startswith('EQ') and not l.startswith('OP'): continue
    if l.startswith('OP'):
        nm,g,s,t=l[3:].split('|')
        if s=='?' or nm in CDIM: continue
        m=re.fullmatch(r'(id|comp|left|right)(\d+)(?:_(\d+))?',nm); kind=m.group(1)
        dims={'id':[int(m.group(2))],'comp':[int(m.group(2))]*2}.get(kind) or ([int(m.group(2)),int(m.group(3))] if kind=='left' else [int(m.group(3)),int(m.group(2))])
        vs=[f'x{i}:{d}' for i,d in enumerate(dims)]
        app='('+nm+' '+' '.join(f'x{i}' for i in range(len(dims)))+')'
        n=ev(parse(app),{f'x{i}':var(f'x{i}',d) for i,d in enumerate(dims)})['n']
        cases=[(f'(s{n} {app})',s),(f'(t{n} {app})',t)]
        name=nm
    else:
        name,vs,g,L,R=l[3:].split('|'); vs=vs.split(','); cases=[(L,R)]
    env={v.split(':')[0]:var(v.split(':')[0],int(v.split(':')[1])) for v in vs}
    pairs=[(ev(parse(a),env),ev(parse(b),env)) for a,b in (x.split('=') for x in filter(None,g.split(';')))]
    subst,err=solve(pairs)
    for L,R in cases:
        total+=1
        A=apply(subst,ev(parse(L),env)); B=apply(subst,ev(parse(R),env))
        if err or A!=B:
            fails+=1; print('FAIL',name,err if err else '')
            if not err:
                for (k,a),(k2,b) in zip(flatten(A),flatten(B)):
                    if a!=b: print('   ',sorted(a) if k=='sup' else a,'  vs  ',sorted(b) if k=='sup' else b)
print(total,'checked',fails,'fail')
