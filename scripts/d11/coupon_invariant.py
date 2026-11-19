"""D11: the coupon length invariant L(D) (answered/gray-biclosed-coherence-2026-11-19.md, Followup 3 section 2).
Diagrams are layer sequences on a row of wires: ('X',i) is a positive crossing of positions i,i+1;
('C',i,name,a,b) is a coupon reading a>=1 wires at positions i..i+a-1 and writing b>=1 wires.
Random walks apply the defining equations (disjoint interchange, Yang-Baxter, both coupon naturalities)
in both directions. Checks: L(D) is invariant, the labelled coupon graph is invariant, the flow law (5)
holds at every coupon, and #crossings <= L. A control confirms that the plain crossing count is NOT
invariant, so the walks really exercise the naturality moves."""
import random, sys, collections

def width_after(layer,w):
    return w if layer[0]=='X' else w-layer[3]+layer[4]

def graph(D,w):
    """wires as ids; returns crossings (pairs of wire ids), coupons (name, in ids, out ids), boundary in/out ids"""
    pos=list(range(w)); nxt=w; cross=[]; coup=[]
    for lay in D:
        if lay[0]=='X':
            i=lay[1]; cross.append((pos[i],pos[i+1])); pos[i],pos[i+1]=pos[i+1],pos[i]
        else:
            _,i,name,a,b=lay; ins=pos[i:i+a]; outs=list(range(nxt,nxt+b)); nxt+=b
            coup.append((name,tuple(ins),tuple(outs))); pos[i:i+a]=outs
    return cross,coup,list(range(w)),pos

def rvals(D,w):
    cross,coup,bin_,bout=graph(D,w)
    src={}; tgt={}
    for k,(_,ins,outs) in enumerate(coup):
        for e in ins: tgt[e]=k
        for e in outs: src[e]=k
    ain={}
    def fin(e):
        if e in ain: return ain[e]
        v=1 if e not in src else sum(fin(x) for x in coup[src[e]][1])
        ain[e]=v; return v
    aout={}
    def fout(e):
        if e in aout: return aout[e]
        v=1 if e not in tgt else sum(fout(x) for x in coup[tgt[e]][2])
        aout[e]=v; return v
    allw=set(bin_)|{e for c in coup for e in c[1]+c[2]}
    r={e:fin(e)*fout(e) for e in allw}
    return r,cross,coup

def L(D,w):
    r,cross,coup=rvals(D,w)
    for _,ins,outs in coup: assert sum(r[e] for e in ins)==sum(r[e] for e in outs), 'flow law (5)'
    return sum(r[a]*r[b] for a,b in cross)

def canon_graph(D,w):
    """coupon multiset with port structure up to wire renaming: sequence of coupons in topological layer order
    is not invariant, so compare the multiset of (name, a, b) plus path counts of each coupon."""
    r,cross,coup=rvals(D,w)
    return collections.Counter((n,len(i),len(o),tuple(r[e] for e in i),tuple(r[e] for e in o)) for n,i,o in coup)

def span(lay):
    return (lay[1],lay[1]+2) if lay[0]=='X' else (lay[1],lay[1]+lay[3])
def outspan(lay):
    return (lay[1],lay[1]+2) if lay[0]=='X' else (lay[1],lay[1]+lay[4])
def shift(lay,k): return (lay[0],lay[1]+k)+lay[2:]

def moves(D):
    out=[]
    for j in range(len(D)-1):
        p,q=D[j],D[j+1]
        # disjoint interchange p;q -> q';p'
        po=outspan(p); qi=span(q)
        if qi[1]<=po[0]:            # q entirely left of p's output: swap, p shifts by delta of q
            dq=(q[4]-q[3]) if q[0]=='C' else 0
            out.append(D[:j]+[q,shift(p,dq)]+D[j+2:])
        elif qi[0]>=po[1]:         # q entirely right: q shifts back by delta of p
            dp=(p[4]-p[3]) if p[0]=='C' else 0
            out.append(D[:j]+[shift(q,-dp),p]+D[j+2:])
    for j in range(len(D)-2):
        a,b,c=D[j:j+3]
        if a[0]=='X' and b[0]=='X' and c[0]=='X':
            i=a[1]
            if c[1]==i and b[1]==i+1: out.append(D[:j]+[('X',i+1),('X',i),('X',i+1)]+D[j+3:])
            if c[1]==i and b[1]==i-1: out.append(D[:j]+[('X',i-1),('X',i),('X',i-1)]+D[j+3:])
    # coupon naturality: coupon at i (a->b), then letter at i+b crosses v leftwards: X_{i+b-1}..X_i
    for j,lay in enumerate(D):
        if lay[0]!='C': continue
        _,i,name,a,b=lay
        left=[('X',i+b-1-k) for k in range(b)]          # c_{v,x}: x moves left across v
        if D[j+1:j+1+b]==left:
            new=[('X',i+a-1-k) for k in range(a)]+[('C',i+1,name,a,b)]
            out.append(D[:j]+new+D[j+1+b:])
        right=[('X',i-1+k) for k in range(b)]           # c_{x,v} with x at i-1 moving right across v
        if i>=1 and D[j+1:j+1+b]==right:
            new=[('X',i-1+k) for k in range(a)]+[('C',i-1,name,a,b)]
            out.append(D[:j]+new+D[j+1+b:])
    # reverse naturality (the same equations right-to-left)
    for j,lay in enumerate(D):
        if lay[0]!='C': continue
        _,i,name,a,b=lay
        pre=[('X',i-1+a-1-k) for k in range(a)]          # c_{u,x}, coupon now at i (x was at i-1+a)
        if j>=a and D[j-a:j]==pre:
            out.append(D[:j-a]+[('C',i-1,name,a,b)]+[('X',i-1+b-1-k) for k in range(b)]+D[j+1:])
        pre2=[('X',i+k) for k in range(a)]               # c_{x,u}: x moved right across u, coupon at i
        if j>=a and D[j-a:j]==pre2:
            out.append(D[:j-a]+[('C',i+1,name,a,b)]+[('X',i+k) for k in range(b)]+D[j+1:])
    return out

def valid(D,w):
    cur=w
    for lay in D:
        s,t=span(lay)
        if s<0 or t>cur: return False
        cur=width_after(lay,cur)
    return True

def rdiagram(w,n,ncoup):
    D=[]; cur=w
    for _ in range(n):
        if random.random()<ncoup and cur>=1:
            a=random.randint(1,min(3,cur)); b=random.randint(1,3); i=random.randint(0,cur-a)
            D.append(('C',i,'r%d'%random.randint(0,2),a,b)); cur=cur-a+b
        elif cur>=2:
            D.append(('X',random.randint(0,cur-2)))
    return D

def main(trials=2000,walk=200,seed=1):
    random.seed(seed); fails=0; nat=0; countchange=0; used=collections.Counter()
    for _ in range(trials):
        w=random.randint(2,5); D=rdiagram(w,random.randint(3,14),0.35)
        L0=L(D,w); G0=canon_graph(D,w); c0=sum(1 for l in D if l[0]=='X')
        for _ in range(walk):
            ms=moves(D)
            if not ms: break
            D2=random.choice(ms)
            assert valid(D2,w), 'invalid move'
            if L(D2,w)!=L0 or canon_graph(D2,w)!=G0: fails+=1; print('FAIL',D,D2); break
            if len(D2)!=len(D): nat+=1
            D=D2
            c=sum(1 for l in D if l[0]=='X')
            if c>L0: fails+=1; print('BOUND',c,L0)
            if c!=c0: countchange+=1
    print({'trials':trials,'fails':fails,'naturality_steps_changing_length':nat,'steps_where_plain_crossing_count_changed':countchange})
    return fails==0 and countchange>0
if __name__=='__main__':
    sys.exit(0 if main() else 1)
