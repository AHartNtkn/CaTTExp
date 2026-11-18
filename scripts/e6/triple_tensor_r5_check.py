"""Independent re-check of the E6 round-5 researcher response (triple tensor, hom-3).

Rebuilds the 240-word hom-2 interval of lambda D2 (x) lambda D2 (x) lambda D2 from the stated
rules (tensor naturalities, positional inner interchangers, contextual tau), applies the six
joining-factorization families h_p, h_q, h_r, lambda_x, h_z, mu, and checks the counts,
acyclicity, sources, the 40,172 path count, and the 24-word source/sink table (4).
Run: python3 scripts/e6/triple_tensor_r5_check.py
"""
import itertools, sys
from collections import defaultdict
FAC={'a':'x','b':'y','c':'z'}
IDX={'x':1,'y':2,'z':3}
CROSS={'p':('y','x'),'q':('z','x'),'r':('z','y')}
def states(w):
    st=['z','y','x']; out=[]
    for l in w:
        out.append(tuple(st))
        if l in CROSS:
            L,R=CROSS[l]; i=st.index(L); assert st[i+1]==R,(w,l,st); st[i],st[i+1]=R,L
    out.append(tuple(st)); return out
def words(ups):
    res=[]
    for perm in itertools.permutations(list(ups)+['p','q','r']):
        cs=''.join(l for l in perm if l in CROSS)
        if cs in('rqp','pqr'): res.append(''.join(perm))
    return res
def pos(st,f): return st.index(f)
def arrow(w,i,st):
    """direction for adjacent swap at i: returns (kind, forward?) forward means w -> swapped"""
    u,v=w[i],w[i+1]
    if u in FAC and v in FAC:
        return ('inner', pos(st,FAC[u])>pos(st,FAC[v]))
    if u in CROSS and v in CROSS: return None
    if u in FAC: upd,cr,updfirst=u,v,True
    else: upd,cr,updfirst=v,u,False
    f=FAC[upd]; pair=CROSS[cr]
    if f in pair:
        other=[g for g in pair if g!=f][0]
        lower=IDX[f]<IDX[other]
        # lower moves earlier: (cr,upd)->(upd,cr); higher moves later: (upd,cr)->(cr,upd)
        return ('nat', (not updfirst) if lower else updfirst)
    right = pos(st,f)>pos(st,pair[0])
    return ('inner', updfirst if right else not updfirst)
def graph(ups):
    W=words(ups); E=[]
    for w in W:
        st=states(w)
        for i in range(len(w)-1):
            a=arrow(w,i,st[i])
            if a and a[1]:
                E.append((a[0],w,w[:i]+w[i+1]+w[i]+w[i+2:],i))
        j=w.find('rqp')
        if j>=0: E.append(('tau',w,w[:j]+'pqr'+w[j+3:],j))
    return W,E
import sys
from collections import defaultdict
W,E=graph('abc')
arr=set((e[1],e[2]) for e in E)
label={(e[1],e[2]):e[0] for e in E}
ROWS=[('h_p','bpa','abp','bap'),('h_q','cqa','acq','caq'),('h_r','crb','bcr','cbr'),
      ('lam','rqa','arq','raq'),('h_z','crqp','pcqr','cpqr'),('mu','crqa','acrq','carq')]
def apply(rows):
    cnt={}
    for name,X,Y,Z in rows:
        n=0
        for w in W:
            for i in range(len(w)-len(X)+1):
                if w[i:i+len(X)]!=X: continue
                pre,suf=w[:i],w[i+len(X):]
                old=(w,pre+Z+suf); inn=(pre+Y+suf,pre+Z+suf); new=(w,pre+Y+suf)
                if old in arr and inn in arr:
                    arr.remove(old); arr.add(new); label[new]=name; n+=1
                else:
                    print('  skip',name,w,old in arr,inn in arr)
        cnt[name]=n
    return cnt
def sources():
    tg=set(t for _,t in arr); return sorted(set(W)-tg)
first=apply(ROWS[:5])
print(first,len(arr))
print('sources before mu', sources())
print(apply(ROWS[5:]),len(arr))
print('sources after', sources(), 'sinks', sorted(set(W)-set(s for s,_ in arr)))
# acyclicity and path counting
succ=defaultdict(list)
for s,t in arr: succ[s].append(t)
import functools
sys.setrecursionlimit(10000)
color={}
def dfs(u):
    color[u]=1
    for v in succ[u]:
        if color.get(v)==1: raise Exception('cycle')
        if v not in color: dfs(v)
    color[u]=2
for w in W:
    if w not in color: dfs(w)
@functools.lru_cache(None)
def npaths(u): return sum(1+npaths(v) for v in succ[u])
print('acyclic; nonidentity paths', sum(npaths(w) for w in W))

# 24-word interval of section 1 (A,B updates, C crossing, D third-factor update)
def arrows24(rule):
    E=[]
    for w in map(''.join,itertools.permutations('ABCD')):
        for i in range(3):
            u,v=w[i],w[i+1]; s=w[:i]+v+u+w[i+2:]; pair={u,v}
            if pair=={'B','C'}: fwd=(u,v)==('B','C')
            elif pair=={'C','A'}: fwd=(u,v)==('C','A')
            elif 'D' in pair: fwd=u=='D'
            elif rule=='const': fwd=(u,v)==('B','A')
            else: fwd=(u,v)==(('A','B') if 'C' in w[i+2:] else ('B','A'))
            if fwd: E.append((w,s))
    return E
for rule in('const','pos'):
    E24=arrows24(rule); V=set(map(''.join,itertools.permutations('ABCD')))
    print('24-word',rule,'sources',sorted(V-set(t for _,t in E24)),'sinks',sorted(V-set(s for s,_ in E24)))
