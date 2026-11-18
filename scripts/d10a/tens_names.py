import sys
src=open(__import__('os').path.join(__import__('os').path.dirname(__file__),'closed_tame.py')).read().split("random.seed(")[0]
exec(src)
random.seed(7)
cs=[]
while len(cs)<3000:
    c=gen_coh()
    if c: cs.append(c)
cs+=[((),I),((I,),I),((I,('a','y')),('a','y'))]
Y=('a','YY')
bad=0
for ctx,goal in cs:
    L=Y
    for b in reversed(ctx): L=('*',b,L)
    T1=((),('\\',L,('*',goal,Y)))
    Rr=Y
    for b in ctx: Rr=('*',Rr,b)
    T2=((),('/',('*',Y,goal),Rr))
    for T in (T1,T2):
        c2,g2=N(*T)
        ok=balanced_atoms(*T) and tame(*T) and prov(tuple(c2),g2)
        if not ok:
            bad+=1
            if bad<5: print("FAIL",ctx,goal)
print("checked",len(cs),"cohs; failures",bad)
