# Checks the tensor-atom tableau formula (4) of answered/gray-tensor-of-contexts-rule-2026-11-18.md:
# rows of the atom a_p (x) b_q in lambda D^p (x) lambda D^q, Steiner sign convention, p, q <= 4.
from collections import defaultdict
def globe(p):
    gens={}  # name->(dim)
    for i in range(p):
        gens[('a',i,'-')]=i; gens[('a',i,'+')]=i
    gens[('a',p,'*')]=p
    def bd(g):
        _,i,_s=g
        if i==0: return {}
        top=(i-1==p) 
        return {('a',i-1,'+'):1,('a',i-1,'-'):-1}
    return gens,bd
def tensor(G1,G2):
    g1,b1=G1; g2,b2=G2
    def bd(x):
        u,v=x; out=defaultdict(int)
        for k,c in b1(u).items(): out[(k,v)]+=c
        s=(-1)**g1[u]
        for k,c in b2(v).items(): out[(u,k)]+=s*c
        return {k:c for k,c in out.items() if c}
    dim=lambda x: g1[x[0]]+g2[x[1]]
    return bd,dim
def atom_rows(bd,dim,x):
    n=dim(x); rows={}
    rows[(n,'-')]={x:1}; rows[(n,'+')]={x:1}
    for k in range(n,0,-1):
        for e in '-+':
            d=defaultdict(int)
            for g,c in rows[(k,e)].items():
                for h,cc in bd(g).items(): d[h]+=c*cc
            if e=='+': part={h:c for h,c in d.items() if c>0}
            else: part={h:-c for h,c in d.items() if c<0}
            rows[(k-1,e)]=part
    return rows
def claimed(p,q,k,e):
    out={}
    for i in range(0,p+1):
        j=k-i
        if j<0 or j>q: continue
        ea = '*' if i==p else e
        sgn = e if i%2==0 else ('+' if e=='-' else '-')
        eb = '*' if j==q else sgn
        out[(('a',i,ea),('a',j,eb))]=1
    return out
bad=0
for p in range(0,5):
  for q in range(0,5):
    bd,dim=tensor(globe(p),globe(q))
    rows=atom_rows(bd,dim,(('a',p,'*'),('a',q,'*')))
    for k in range(p+q+1):
      for e in '-+':
        if rows[(k,e)]!=claimed(p,q,k,e): bad+=1; print('mismatch',p,q,k,e,rows[(k,e)],claimed(p,q,k,e))
print('mismatches',bad)
