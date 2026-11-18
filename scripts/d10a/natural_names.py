"""D10b: the naturality-in-Y step for the generalized names T_u (closed-structure.md B.4).
For a UP* coh S = (B1..Bk |- C), check that  Z\\W |- (B1*...*Bk*Z) \\ (C*W)  and its mirror are UP*."""
import os
src=open(os.path.join(os.path.dirname(__file__),'closed_tame.py')).read().split("random.seed(")[0]
exec(src)
random.seed(11)
cs=[]
while len(cs)<3000:
    c=gen_coh()
    if c: cs.append(c)
cs+=[((),I),((I,),I),((I,('a','y')),('a','y'))]
Z=('a','ZZ'); W=('a','WW')
bad=0
for ctx,goal in cs:
    L=Z
    for b in reversed(ctx): L=('*',b,L)
    T1=((('\\',Z,W),),('\\',L,('*',goal,W)))
    R=Z
    for b in ctx: R=('*',R,b)
    T2=((('/',W,Z),),('/',('*',W,goal),R))
    for T in (T1,T2):
        c2,g2=N(*T)
        if not (balanced_atoms(*T) and tame(*T) and prov(tuple(c2),g2)):
            bad+=1
            if bad<5: print("FAIL",ctx,goal)
print("checked",len(cs),"cohs; failures",bad)
