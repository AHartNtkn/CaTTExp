"""D11 / F.6: the polarized weight model 𝓟 (closed-structure.md F.6, item 4).
Objects: (P, N) in Z^2, with A⊗B = A+B and A\\C = C + swap(A) = C/A.
A 1-cell X -> Y exists iff (P-N)(X) = (P-N)(Y). It is an integer weight, and homs are codiscrete.
  d(u)      = P(source) - P(target)
  w(A⊗u)    = w(u) + P(A) d(u),     w(u⊗B) = w(u)
  Phi_A(u)  = w(u) - P(A) d(u)      (left currying),   Phi'_A(u) = w(u)  (right currying)
Checks the laws on random data and computes the weights of the two sides of chi_{g,ev}."""
import random
random.seed(1)
def P(x): return x[0]
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def sw(a): return (a[1],a[0])
def lres(a,c): return add(c,sw(a))
def cell(s,t,w):
    assert s[0]-s[1]==t[0]-t[1]; return (s,t,w)
def d(u): return P(u[0])-P(u[1])
def comp(u,v):                        # u ∘ v
    assert v[1]==u[0]; return (v[0],u[1],u[2]+v[2])
def lw(A,u): return (add(A,u[0]),add(A,u[1]),u[2]+P(A)*d(u))
def rw(u,B): return (add(u[0],B),add(u[1],B),u[2])
def Phi(A,u,B):                       # u : A⊗B -> C   |->   B -> A\C
    C=u[1]; return (B,lres(A,C),u[2]-P(A)*d(u))
def Phiinv(A,k):                      # k : B -> A\C  |->  A⊗B -> C   (C recovered)
    B,AC,w=k; C=add(AC,(-A[1],-A[0])); return (add(A,B),C,w+P(A)*(P(add(A,B))-P(C)))
def rv(): return (random.randint(-3,3),random.randint(-3,3))
def rcell(s):
    t0=rv(); t=(t0[0],t0[0]-(s[0]-s[1])); return cell(s,t,random.randint(-5,5))
bad=0
for _ in range(20000):
    A,A2,B=rv(),rv(),rv()
    v=rcell(B); u=rcell(add(A,v[1])); h=rcell(u[1])
    bad+= lw(A,comp(u2:=rcell(v[1]),v))!=comp(lw(A,u2),lw(A,v))      # A⊗– functor
    bad+= lw(A,lw(A2,v))!=lw(add(A,A2),v)                            # strict assoc
    bad+= rw(lw(A,v),A2)!=lw(A,rw(v,A2))                             # (A⊗v)⊗B = A⊗(v⊗B)
    bad+= Phiinv(A,Phi(A,u,v[1]))!=u                                 # bijection
    bad+= Phi(A,comp(u,lw(A,v)),v[0])!=comp(Phi(A,u,v[1]),v)         # natural in context
    hA=Phi(A,comp(h,Phiinv(A,(lres(A,u[1]),lres(A,u[1]),0))),lres(A,u[1]))  # A\h
    bad+= Phi(A,comp(h,u),v[1])!=comp(hA,Phi(A,u,v[1]))              # natural in target
print("law failures:",bad)
A=(1,0); C=(0,0); X=(1,1); Xp=(0,0)
g=cell(X,Xp,0); ev=Phiinv(A,(lres(A,C),lres(A,C),0))
lhs=comp(lw(Xp,ev),rw(g,add(A,lres(A,C))))   # (X'⊗ev)∘(g⊗A⊗A\C)
rhs=comp(rw(g,C),lw(X,ev))                    # (g⊗C)∘(X⊗ev)
print("d(ev)=",d(ev)," weights of the two sides of chi_{g,ev}:",lhs[2],rhs[2])
