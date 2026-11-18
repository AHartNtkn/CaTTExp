"""Independent check of the E6 round-8 degeneration obstruction (section 1 of the response).

Rebuilds the K14 triple-tensor graph (via triple_tensor_r5_check.py) and the K10 binary graph,
erases c, q, r, and checks: every K14 arrow has an image; h_z and the inner arrow e exist;
the K18 join j_{h_z,e} would need bap -> abp, which K10 lacks; counts one-step K18 joins without image.
Run: python3 scripts/e6/r8_degeneration_check.py
"""
import sys,io,contextlib,itertools
from collections import defaultdict
src=open('/home/user/CaTTExp/scripts/e6/triple_tensor_r5_check.py').read()
src=src.split('# acyclicity and path counting')[0]
g={}
with contextlib.redirect_stdout(io.StringIO()): exec(src,g)
arr,label,W=g['arr'],g['label'],g['W']
# binary K10 graph on a,b with crossing p (yx -> xy)
FAC={'a':'x','b':'y'}; IDX={'x':1,'y':2}
def st2(w):
    st=['y','x'];out=[]
    for l in w:
        out.append(tuple(st))
        if l=='p': i=st.index('y'); st[i],st[i+1]=st[i+1],st[i]
    out.append(tuple(st));return out
B=[''.join(p) for p in itertools.permutations('abp')]
barr={}
for w in B:
    st=st2(w)
    for i in range(2):
        u,v=w[i],w[i+1]; s=st[i]
        if u in FAC and v in FAC: kind='inner'; fwd=s.index(FAC[u])>s.index(FAC[v])
        else:
            upd,updfirst=(u,True) if u in FAC else (v,False)
            f=FAC[upd]; other='y' if f=='x' else 'x'
            kind='nat'; fwd=(not updfirst) if IDX[f]<IDX[other] else updfirst
        if fwd: barr[(w,w[:i]+w[i+1]+w[i]+w[i+2:])]=kind
# K10 repair: h_p : bpa -> abp with old bpa->bap = h_p ; (abp->bap)
assert ('bpa','bap') in barr and ('abp','bap') in barr
del barr[('bpa','bap')]; barr[('bpa','abp')]='h_p'
print('K10 arrows', sorted(barr))
sinks=[w for w in B if not any(s==w for s,_ in barr)]; print('binary sinks',sinks)
bs=defaultdict(set)
for s,t in barr: bs[s].add(t)
def reach(a,b):
    seen={a};st=[a]
    while st:
        x=st.pop()
        for y in bs[x]:
            if y not in seen: seen.add(y);st.append(y)
    return b in seen
er=lambda w:''.join(l for l in w if l in 'abp')
# every K14 arrow maps to identity or a K10 path
bad=[(s,t) for s,t in arr if er(s)!=er(t) and not reach(er(s),er(t))]
print('K14 arrows with no image:',len(bad))
A=('bacrqp','bapcqr'); e=('abpcqr','bapcqr')
print('h_z arrow present:',A in arr, label.get(A)); print('inner e present:',e in arr,label.get(e))
print('J image needed:',er('bacrqp'),'->',er('abpcqr'),'exists:',reach(er('bacrqp'),er('abpcqr')))
# all K18 single-step joins j_{alpha,e}: positive alpha:s->t, inner e:u->t
inn=defaultdict(list)
for (s,t) in arr:
    if label[(s,t)]=='inner': inn[t].append(s)
pos=[(s,t) for (s,t) in arr if label[(s,t)]!='inner']
fail=0;tot=0
for s,t in pos:
    for u in inn[t]:
        tot+=1
        if er(s)!=er(u) and not reach(er(s),er(u)): fail+=1
print('one-step K18 joins:',tot,'with no image under the degeneration:',fail)
