import importlib.util,sys
sys.argv=['x','0']
src=open(__import__('os').path.join(__import__('os').path.dirname(__file__),'closed_tame.py')).read().split("random.seed(")[0]
exec(src)
a=lambda n:('a',n)
Z,X,W,P,Q,R=map(a,'ZXWPQR')
C=('/',('\\',('*',Z,('\\',Z,X)),('*',X,W)),W)   # ((Z⊗(Z\X))\(X⊗W))/W
print("child closed: balanced",balanced_atoms((),C),"provable",prov((),C),"tame",tame((),C))
B=('/',('\\',P,('*',I,Q)),R)
S=((B,),('/',('\\',P,Q),R))
print("parent S: balanced",balanced_atoms(*S),"provable",prov(*S),"tame",tame(*S), "N(S)=",N(*S))
s={}
print("unify",unify(B,C,s))
G=res(S[1],s); print("result goal",G,"balanced",balanced_atoms((),G),"tame",tame((),G),"N=",N((),G))
