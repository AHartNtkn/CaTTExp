"""D10b, revised bracket abstraction (closed-structure.md B.4): [x]t := coh_F(γ, Ť_t[Y:=I]).
Checks that the coh types used are UP*, for |Γ'| = 0..4:
  F : Γ', (X⊗Γ'⊗I)\\(A⊗I) ⊢ X\\A     (definition)
  U : X, Γ', (X⊗Γ'⊗I)\\(A⊗I) ⊢ A     (β step)
and the mirror F' : (I⊗Γ'⊗X)/... is checked by the symmetric construction."""
import os
src=open(os.path.join(os.path.dirname(__file__),'closed_tame.py')).read().split("random.seed(")[0]
exec(src)
def at(n): return ('a',n)
def tens(xs):
    r=xs[-1]
    for b in reversed(xs[:-1]): r=('*',b,r)
    return r
bad=0; n=0
for k in range(0,5):
    G=[at('g%d'%i) for i in range(k)]; X=at('x'); A=at('aa')
    Nn=('\\',tens([X]+G+[I]),('*',A,I))
    Nm=('/',('*',I,A),tens([I]+G[::-1]+[X]))    # mirror: name in the / direction
    for T in [(tuple(G+[Nn]),('\\',X,A)), (tuple([X]+G+[Nn]),A),
              (tuple([Nm]+G[::-1]),('/',A,X)), (tuple([Nm]+G[::-1]+[X]),A)]:
        n+=1; c2,g2=N(*T)
        ok=balanced_atoms(*T) and tame(*T) and prov(tuple(c2),g2)
        if not ok: bad+=1; print("FAIL",k,T)
print("checked",n,"types; failures",bad)
