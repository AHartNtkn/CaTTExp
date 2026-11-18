# Random test of the plugging lemma: S=(B1..Bn |- B) and S_i=(G_i |- C_i) balanced, disjoint atoms;
# if B_i =? C_i unifiable, then (G_1..G_n |- B)[mgu] is balanced (each atom twice, opposite polarity).
import random
cnt=0
def fresh():
    global cnt; cnt+=1; return ('v',cnt)
def rand_shape(d):
    if d==0 or random.random()<0.3: return ['L']
    return [random.choice('*\\/'), rand_shape(d-1), rand_shape(d-1)]
def leaves(f,pol,acc,path=()):
    if f[0]=='L': acc.append((path,pol)); return
    op=f[0]
    if op=='*': leaves(f[1],pol,acc,path+(1,)); leaves(f[2],pol,acc,path+(2,))
    else:  # f[1]=argument (flips), f[2]=result
        leaves(f[1],-pol,acc,path+(1,)); leaves(f[2],pol,acc,path+(2,))
def fill(f,names,it):
    if f[0]=='L': return ('a',next(it))
    return (f[0],fill(f[1],names,it),fill(f[2],names,it))
def rand_balanced(nh):
    shapes=[rand_shape(2) for _ in range(nh+1)]
    occ=[]
    for k,s in enumerate(shapes):
        acc=[]; leaves(s,1 if k==nh else -1,acc); occ.append(acc)
    flat=[(k,i,p) for k,a in enumerate(occ) for i,(path,p) in enumerate(a)]
    pos=[x for x in flat if x[2]>0]; neg=[x for x in flat if x[2]<0]
    if len(pos)!=len(neg): return None
    random.shuffle(neg); names={}
    for a,b in zip(pos,neg):
        v=fresh(); names[a[:2]]=v; names[b[:2]]=v
    forms=[fill(s,names,iter([names[(k,i)] for i in range(len(occ[k]))])) for k,s in enumerate(shapes)]
    return forms[:-1],forms[-1]
def walk(t,s):
    while t[0]=='a' and t[1] in s: t=s[t[1]]
    return t
def occurs(v,t,s):
    t=walk(t,s)
    if t[0]=='a': return t[1]==v
    return occurs(v,t[1],s) or occurs(v,t[2],s)
def unify(a,b,s):
    a=walk(a,s); b=walk(b,s)
    if a[0]=='a' and b[0]=='a' and a[1]==b[1]: return True
    if a[0]=='a':
        if occurs(a[1],b,s): return False
        s[a[1]]=b; return True
    if b[0]=='a': return unify(b,a,s)
    if a[0]!=b[0]: return False
    return unify(a[1],b[1],s) and unify(a[2],b[2],s)
def resolve(t,s):
    t=walk(t,s)
    if t[0]=='a': return t
    return (t[0],resolve(t[1],s),resolve(t[2],s))
def atom_occ(f,pol,acc):
    if f[0]=='a': acc.append((f[1],pol)); return
    if f[0]=='*': atom_occ(f[1],pol,acc); atom_occ(f[2],pol,acc)
    else: atom_occ(f[1],-pol,acc); atom_occ(f[2],pol,acc)
tests=fails=0
for _ in range(200000):
    n=random.randint(1,3)
    S=rand_balanced(n)
    if not S: continue
    subs=[]
    for i in range(n):
        Si=rand_balanced(random.randint(1,2))
        if not Si: break
        subs.append(Si)
    if len(subs)<n: continue
    s={}
    if not all(unify(S[0][i],subs[i][1],s) for i in range(n)): continue
    hyps=[resolve(h,s) for Si in subs for h in Si[0]]; goal=resolve(S[1],s)
    acc=[]
    for h in hyps: atom_occ(h,-1,acc)
    atom_occ(goal,1,acc)
    d={}
    for v,p in acc: d.setdefault(v,[]).append(p)
    tests+=1
    if any(sorted(ps)!=[-1,1] for ps in d.values()): fails+=1
print("unifiable instances:",tests,"failures:",fails)
