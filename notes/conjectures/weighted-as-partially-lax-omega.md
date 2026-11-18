# Weighted (co)limits as partially lax (co)limits in (∞,ω)-categories

> **Status (2026-11-18): SOLVED in Loubaton's model (researcher proof, verified below), in both directions and for all dimensions. The cone categories are Loubaton's marked lax transformations, and the variance alternates by dimension as in the response's §4. The computad-level condition is an exact but infinite lifting schema; a finite generator-level test is open.**

## Background

Abellán–Haugseng–Martini ([2602.07604](https://arxiv.org/abs/2602.07604), Thm F and surrounding results) prove, for (∞,2)-categories:
- The I-lax colimit of `F : A → Cat_{(∞,2)}` is the total space of the classifying fibration, with the cartesian 2-morphisms and the cocartesian 1-morphisms over a marked class I inverted.
- **Weighted (co)limits can be expressed as partially lax (co)limits over the fibration classified by the weight, and conversely.**

Loubaton ([2406.05425](https://arxiv.org/abs/2406.05425)) proves:
- a lax Grothendieck construction for (∞,ω)-categories (Thm 4.1.4.2), in which "the extent of laxness is adjustable";
- results on marked (∞,ω)-categories and cartesian fibrations (Ch. 3).

## Statement

Let 𝒞 be an (∞,ω)-category. Let `W : I → (∞,ω)Cat` be a weight and `F : I → 𝒞` a diagram. Let `p : ∫W → I` be the (lax) Grothendieck construction of W, with its (co)cartesian cells marked.

**Show that the W-weighted limit of F, when it exists, is the partially lax limit of `F ∘ p` over `∫W`.** Here "partially lax" means: the cone cells over marked cells are invertible, and the cone cells over unmarked cells may be non-invertible. Show the converse as well. State the variance conventions precisely.

**Syntactic corollary (for finite I).** Suppose I is presented by a finite computad Γ and W by a finite computad Ψ with a map `π : Ψ → Γ` and a marking μ of Ψ. Then the marked lax limit `lim_{Ψ^μ}(γ ∘ π)` is the weighted limit. This needs:
- a condition on π making it present a (co)cartesian fibration;
- the dimension in which "partially lax" applies.

## What is known

- Dimension 2: AHM.
- Dimension ω: Loubaton's lax Grothendieck construction appears to be the main ingredient. The question is whether his partial-laxness parameter matches marked cones.
- **Side result, settled in the design note.** For marked cones, no closure condition on the marking is needed. Cone cells over composites of marked generators, over identities and over coherences are composites of invertible cells, hence invertible.

### Literature search (2026-11-18)
- **Known in dimension 2:** Abellán–Haugseng–Martini, as above.
- *The higher algebra of weighted colimits* ([arXiv 2406.08925](https://arxiv.org/abs/2406.08925)) treats (op)lax colimits of (∞,n)-categories, for all n, as weighted colimits (its Cor. 1.4). That is the easy direction. It does not express general weighted colimits as partially lax ones.
- **Open for n > 2 and for ω:** the converse (weighted ⇒ partially lax over the Grothendieck construction). Nothing found.

## Why it matters

If true, a type theory with lax limits and a per-variable "this cell must be invertible" flag gets all weighted limits with no further rule.

## What would count as a solution

A proof or reference in a model of (∞,ω)-categories, together with a computad-level characterisation of the π's that present fibrations.

# Researcher Response

**The statement follows in Loubaton’s model, provided the higher transformations between cones are those of his marked Gray construction \(\operatorname{Hom}_{\ominus}\).** The key additional result is his enriched adjunction in Corollary 4.2.2.6. Combined with the Grothendieck equivalence and his characterization of lax limits, it gives the comparison you ask for. Thus the \(\omega\)-dimensional direction can be proved under these conventions. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For computads, there is an explicit necessary-and-sufficient lifting schema. It is an infinite schema on a specified realization of the computads; the argument does not provide a finite test of their generator lists.

## 1. Conventions

Work in Loubaton’s \(\Theta\)-space model. Write \(\Omega\) for his \((\infty,\omega)\)-category of small \((\infty,\omega)\)-categories, and choose universes large enough for the diagrams below.

Use these notations:

- \(A^\sharp\): every positive-dimensional cell is marked.
- \(A^\flat\): the minimal marking.
- \(\operatorname{Fun}(A,B)\): the cartesian internal hom.
- \(\operatorname{Fun}_{M}(A,B):=\operatorname{Hom}_{\ominus}(A^M,B)\): Loubaton’s category of marked lax transformations.
- \(A^t\): reverse **only \(1\)-cells**.
- \(A^\circ\): reverse cells in every positive dimension.

The distinction between \(t\) and full duality matters at dimension \(\omega\). In particular, the hom functor has variance
\[
\mathcal C(-,-):\mathcal C^t\times\mathcal C\longrightarrow\Omega.
\]

For \(U,V:I\to\Omega\), abbreviate
\[
\operatorname{Nat}_I(U,V)
:=
\operatorname{hom}_{\operatorname{Fun}(I,\Omega)}(U,V).
\]
Similarly, \(\operatorname{Nat}^{M}_J\) denotes the hom in \(\operatorname{Fun}_{M}(J,\Omega)\). These are full \((\infty,\omega)\)-categories.

### Weighted limits

For
\[
F:I\to\mathcal C,\qquad W:I\to\Omega,
\]
the coherent \(W\)-weighted limit represents
\[
x\longmapsto
\operatorname{Nat}_I\!\left(W,\mathcal C(x,F-)\right).
\]
Thus
\[
\mathcal C\!\left(x,\lim_I^W F\right)
\simeq
\operatorname{Nat}_I\!\left(W,\mathcal C(x,F-)\right),
\tag{1}
\]
naturally in \(x:\mathcal C^t\).

### Marked lax cones

For \(D:J\to\mathcal C\), a cone with vertex \(x\) has arrows
\[
\lambda_j:x\to D(j)
\]
and, for \(u:j\to j'\), comparisons directed as
\[
D(u)\lambda_j\Longrightarrow\lambda_{j'}.
\tag{2}
\]

Marking a \(k\)-cell of \(J\) requires its associated **\((k+1)\)-dimensional cone comparison** to be an equivalence. Loubaton states this explicitly in Remark 4.2.3.7. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The higher transformations are fixed by Definition 4.1.4.1:
\[
\operatorname{Map}\!\left(a,\operatorname{Fun}_{M}(J,\mathcal C)\right)
\simeq
\operatorname{Map}_{m}\!\left(J^M\ominus a^\sharp,\mathcal C^\sharp\right)
\tag{3}
\]
for globular test shapes \(a\). Here \(\operatorname{Map}_m\) is the mapping space of marked functors. At the level of individual cones, this gives precisely condition (2) and the specified invertibility flags. Equation (3) also specifies their higher morphisms. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

## 2. The comparison theorem

The following slightly more general statement proves both directions.

**Theorem.** Let
\[
q:J^M\longrightarrow I^\sharp
\]
be any marked functor. There is a weight
\[
W_q:I\longrightarrow\Omega
\]
such that, for every \(F:I\to\mathcal C\),
\[
\boxed{
\lim_{J^M}^{\mathrm{lax}}Fq
\simeq
\lim_I^{W_q}F.
}
\tag{4}
\]
Either side exists if and only if the other does.

If \(q=p\) is the left cartesian fibration classified by \(W:I\to\Omega\), with its fibration marking, then
\[
W_p\simeq W.
\tag{5}
\]

### Proof

Loubaton’s Corollary 4.2.2.6 gives an adjunction of \((\infty,\omega)\)-categories
\[
q_!:
\operatorname{Fun}_{M}(J,\Omega)
\;\rightleftarrows\;
\operatorname{Fun}(I,\Omega)
:q^*.
\tag{6}
\]
Define
\[
W_q:=q_!\underline{\mathbf1},
\tag{7}
\]
where \(\underline{\mathbf1}\) is the constant diagram at the terminal category. The enriched adjunction gives
\[
\operatorname{Nat}_I(W_q,H)
\simeq
\operatorname{Nat}^{M}_J(\underline{\mathbf1},Hq)
\tag{8}
\]
for every \(H:I\to\Omega\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Now put
\[
H_x(i):=\mathcal C(x,F(i)).
\]
Loubaton’s Corollary 4.2.3.18 identifies the right side of
\[
\operatorname{Nat}_I(W_q,H_x)
\simeq
\operatorname{Nat}^{M}_J(\underline{\mathbf1},H_xq)
\tag{9}
\]
as the functor represented by the marked lax limit of \(Fq\). The left side is the functor represented by the \(W_q\)-weighted limit. Both equivalences are natural in \(x:\mathcal C^t\). Therefore they have the same representing vertices, proving (4), including the existence assertion. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

It remains to prove (5). Under the Grothendieck equivalence:

1. The constant terminal diagram on \(J^M\) corresponds to
   \[
   \operatorname{id}_{J^M}:J^M\to J^M.
   \]
2. The functor \(q_!\) is postcomposition with \(q\), followed by left cartesian replacement.

Consequently,
\[
\int_I W_q
\simeq
R_{\mathrm L}(q),
\tag{10}
\]
where \(R_{\mathrm L}(q)\) denotes the left cartesian replacement of the marked map \(q\). This is the pushforward construction transported through Theorem 4.1.4.2 and Corollary 4.1.4.3. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

If \(q=p\) is already the left cartesian fibration classified by \(W\), its replacement is equivalent to \(p\). Straightening (10) therefore gives \(W_p\simeq W\). Substituting this into (4) yields
\[
\boxed{
\lim_I^W F
\simeq
\lim_{(\int_I W)^M}^{\mathrm{lax}}Fp.
}
\tag{11}
\]

This is an equivalence of universal properties involving the full hom \((\infty,\omega)\)-categories.

### Why the marking is exactly the required one

There is also a direct description of the central equivalence. Let \(E_W\to I^\sharp\) and \(E_H\to I^\sharp\) classify \(W,H\). A map
\[
E_W\longrightarrow E_H
\quad\text{over }I^\sharp
\]
corresponds to a section of
\[
E_W\times_{I^\sharp}E_H\longrightarrow E_W.
\]

Preservation of the marked fibration cells by the first map is exactly preservation of the marking by the section. This correspondence extends to every globular parameter \(a\):
\[
\operatorname{Map}_{/I^\sharp}
   (E_W^M\times a^\flat,E_H)
\simeq
\operatorname{Map}_{/E_W^M}
   (E_W^M\times a^\flat,E_W^M\times_{I^\sharp}E_H).
\tag{12}
\]
It sends \(u\) to \((\operatorname{pr}_{E_W},u)\), naturally in \(a\). Remark 3.2.6.7 identifies these parameterized maps with the hom categories of fibrations. Thus the comparison respects all higher transformations. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

## 3. The converse, with an explicit weight

Suppose the starting datum is a marked diagram
\[
D:J\to\mathcal C,\qquad M\text{ a marking on }J.
\]
Take the marking inclusion
\[
\iota:J^M\longrightarrow J^\sharp
\]
and define
\[
\boxed{
W_M:=\iota_!\underline{\mathbf1}:J\to\Omega.
}
\tag{13}
\]
Equation (4) gives
\[
\boxed{
\lim_{J^M}^{\mathrm{lax}}D
\simeq
\lim_J^{W_M}D.
}
\tag{14}
\]

A fibrational construction of this weight is:

1. Factor the marked map \(\iota\) as an initial map followed by a left cartesian fibration:
   \[
   J^M\longrightarrow P_M\longrightarrow J^\sharp.
   \]
2. Straighten \(P_M\to J^\sharp\).

The resulting functor is \(W_M\), by (10). The required factorization is Loubaton’s Construction 3.2.2.4. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

This construction also applies to an arbitrary \(q:J^M\to I^\sharp\), giving the more general converse (4).

## 4. Variance and colimits

For the convention above, the relevant choices are:

| Construction | Weight | Classifying fibration over \(I\) | Marked cells, by dimension |
|---|---|---|---|
| Weighted limit | \(W:I\to\Omega\) | Left cartesian | Cocartesian \(1\)-cells, cartesian \(2\)-cells, cocartesian \(3\)-cells, continuing alternately |
| Weighted colimit | \(W:I^t\to\Omega\) | Right cartesian | Cartesian \(1\)-cells, cocartesian \(2\)-cells, cartesian \(3\)-cells, continuing alternately |

The alternating condition is recursive: a left cartesian fibration induces right cartesian fibrations on hom categories, and conversely. Thus “mark its \((\mathrm{co})\)cartesian cells” must use a specified variance in every dimension. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For limits, a chosen marked lift of \(f:i\to j\) at \(w\in W(i)\) has direction
\[
(i,w)\longrightarrow(j,W(f)w).
\]
Its cone comparison is
\[
F(f)\lambda_{i,w}
\Longrightarrow
\lambda_{j,W(f)w},
\]
and is invertible. A vertical arrow \(\beta:w\to w'\) of \(W(i)\) instead gives
\[
\lambda_{i,w}\Longrightarrow\lambda_{i,w'},
\]
which may be non-invertible. These are the data needed for a functor
\[
W(i)\longrightarrow\mathcal C(x,F(i)).
\]

For colimits, use
\[
\mathcal C\!\left(\operatorname{colim}_I^W F,x\right)
\simeq
\operatorname{Nat}_{I^t}\!\left(W,\mathcal C(F-,x)\right).
\tag{15}
\]
If
\[
r:E^M\longrightarrow I^\sharp
\]
is the corresponding **right** cartesian construction, the dual conclusion is
\[
\boxed{
\operatorname{colim}_I^W F
\simeq
\operatorname{colim}_{E^M}^{\mathrm{lax}}Fr.
}
\tag{16}
\]

Here is a precise construction of \(r\) that fixes the higher variance. Put
\[
S=\{2,3,4,\ldots\}.
\]
Full duality on the values defines
\[
D_\circ:\Omega\longrightarrow\Omega^S,
\qquad A\longmapsto A^\circ.
\]
Given \(W:I^t\to\Omega\), form
\[
W^\dagger
:=
D_\circ^S\circ W^S:
I^\circ\longrightarrow\Omega.
\tag{17}
\]
Its value at \(i\) is \(W(i)^\circ\). Let
\[
q:P^N\longrightarrow(I^\circ)^\sharp
\]
be its left cartesian construction, and set
\[
r=q^\circ:(P^\circ)^{N^\circ}\longrightarrow I^\sharp.
\tag{18}
\]
This is right cartesian, with fibre \(W(i)\). The dualities used here are Construction 4.1.1.25 and Remark 3.2.2.3. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

To verify (16), full duality gives
\[
\operatorname{Nat}(W,H)^\circ
\simeq
\operatorname{Nat}(W^\dagger,H^\dagger),
\qquad
\mathcal C^\circ(x,F^\circ i)
\simeq
\mathcal C(Fi,x)^\circ.
\]
Thus (15) becomes the \(W^\dagger\)-weighted-limit property for \(F^\circ\) in \(\mathcal C^\circ\). Apply (11) and dualize back. Full duality exchanges Loubaton’s lax limits and lax colimits. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

## 5. An exact condition on the computad map

A computadic formulation must specify its realization. Write
\[
E=\llbracket\Psi\rrbracket,\qquad
I=\llbracket\Gamma\rrbracket,\qquad
p=\llbracket\pi\rrbracket:E\to I,
\]
in the model used above.

Let \(M\) be the marking generated by the flagged generators \(\mu\). This completion is automatic: identities, composites, whiskerings and equivalent cells receive the induced marking. It imposes no closure requirement on the initial list of flags.

### The lifting schema

Let \(D_n^\flat\) be the minimally marked \(n\)-globe. For \(n\geq1\), let \(D_n^\bullet\) be the \(n\)-globe with its generating \(n\)-cell marked. Set
\[
\mathcal G_m
=
\{D_n^\flat:n\geq0\}
\;\cup\;
\{D_n^\bullet:n\geq1\}.
\]

Then \(p:E^M\to I^\sharp\) is a left cartesian fibration **if and only if**, for every \(K\in\mathcal G_m\), restriction at endpoint \(0\) induces an equivalence of spaces
\[
\boxed{
\begin{aligned}
\operatorname{Map}_m(K\otimes[1]^\sharp,E^M)
\;\xrightarrow{\ \simeq\ }\;&
\operatorname{Map}_m(K,E^M)
\\[-2pt]
&\times_{\operatorname{Map}_m(K,I^\sharp)}
\operatorname{Map}_m(K\otimes[1]^\sharp,I^\sharp).
\end{aligned}
}
\tag{19}
\]

For a right cartesian fibration, use endpoint \(1\).

**Proof of the criterion.** Definition 3.2.1.1 generates the initial maps from the inclusions
\[
K\otimes\{0\}\longrightarrow K\otimes[1]^\sharp,
\qquad K\in\mathcal G_m.
\]
Definition 3.2.2.1 defines left cartesian fibrations by right orthogonality to those initial maps. Equation (19) is exactly that orthogonality condition, expressed through mapping spaces. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

In particular, every prescribed lifting problem must have a **contractible space of solutions**. Mere existence of lifts is weaker.

This is an explicit schema indexed by marked globes and their marked Gray cylinders. It tests the realized computad map, including the higher coherence of its lifts.

### Its universal-property interpretation

An equivalent recursive formulation begins with the following requirements:

1. Every base \(1\)-cell has a marked lift with prescribed source, unique up to a contractible space of choices.
2. Every marked \(u:x\to x'\) satisfies, for every \(z\),
   \[
   \mathcal E(x',z)
   \simeq
   \mathcal E(x,z)
   \times_{\mathcal I(px,pz)}
   \mathcal I(px',pz),
   \tag{20}
   \]
   where the maps are induced by precomposition with \(u\) and \(p(u)\).
3. Every hom functor
   \[
   \mathcal E(x,y)\longrightarrow\mathcal I(px,py)
   \]
   is right cartesian.

The right-handed version uses prescribed targets, postcomposition, and left cartesian hom functors. This is Theorem 3.2.2.24(5). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For example, consider
\[
I=(0\xrightarrow f1)
\]
and a free category \(E\) with arrows
\[
x\xrightarrow u y,\qquad x\xrightarrow v z,
\]
both mapped to \(f\). A lift of the base generator exists at \(x\), but \(u\) is not cocartesian: factoring \(v\) through \(u\) would require an arrow \(y\to z\), which does not exist. This shows why a condition merely requiring flagged lifts of base generators would not suffice.

### Identifying the specified weight

Condition (19) makes \(p\) classify **some** weight \(W_p\). To identify it with a previously specified \(W\), one also needs
\[
\operatorname{St}(p)\simeq W.
\tag{21}
\]
This includes compatibility with transport, beyond equivalences of the individual fibres.

With (19) and (21), and with
\[
\gamma:\llbracket\Gamma\rrbracket\to\mathcal C,
\]
the requested syntactic equation is
\[
\boxed{
\lim_{\llbracket\Psi\rrbracket^{M}}^{\mathrm{lax}}
   \bigl(\gamma\llbracket\pi\rrbracket\bigr)
\simeq
\lim_{\llbracket\Gamma\rrbracket}^{W}\gamma.
}
\tag{22}
\]

## 6. What the per-variable flag must mean

The dimension shift is:

| Flagged index generator | Comparison required to be invertible |
|---|---|
| \(1\)-generator | Cone \(2\)-cell |
| \(2\)-generator | Cone \(3\)-cell |
| \(k\)-generator | Cone \((k+1)\)-cell |

The flag constrains the associated cone comparison. It does **not** make the flagged generator invertible in the indexing category.

Consequently, the semantic result supports your proposed rule under two precise premises:

- The type theory presents Loubaton’s marked cone categories, including their higher transformations.
- Its permitted index presentations include the required classifying fibrations.

For finite \(\Gamma,\Psi\), equation (22) is the desired finite-presentation corollary once the lifting schema holds. Finiteness of those presentations does not itself prove the schema, nor does finiteness of \(\Gamma\) guarantee a finite presentation of the total category of an arbitrary weight. A comparison with an independently defined computad or type-theoretic semantics remains an additional premise; the proof above establishes the result in Loubaton’s model.

# Verification of the researcher response (2026-11-18)

**Verdict: correct. The (∞,ω) statement holds in Loubaton's model, in both directions, with the variance fixed as in the response's §4.** Here the cone categories are Loubaton's marked lax transformations Hom_⊖, and weighted limits are defined with the cartesian (strong) functor category. The finite-computad criterion is an exact but infinite lifting schema; a *finite* test on generator lists is still open.

Each cited result was checked in Loubaton, [arXiv 2406.05425](https://arxiv.org/abs/2406.05425):

1. **Cor. 4.2.2.6.** For i : I → A♯, the restriction i* : Hom(A, ω) → Hom_⊖(I, ω) has a left adjoint i_!, as an adjunction of (∞,ω)-categories (Thm 4.2.2.4). This is what gives the equivalence of hom (∞,ω)-categories in (8). Confirmed.
2. **Cor. 4.2.3.18.** A lax limit of F : I → A♯ is an object l with hom_A(a, l) ≃ hom_{Hom_⊖(I,ω)}(cst 1, hom_A(a, F−)), naturally in a : Aᵗ. This is the right-hand side of (9). Confirmed.
3. **Definition (1) of weighted limits** uses Nat in the cartesian Fun(I, Ω). This is the left-hand side of (9). So (4) follows by Yoneda, including "one exists iff the other does". Confirmed.
4. **W_p ≃ W.**
   - i_! is induced on fibrations by Li_! (Construction 4.1.4.4, via (3.2.6.19)): postcompose with i, then take the left cartesian replacement (Construction 3.2.2.4).
   - The constant diagram 1 on J^M corresponds to id_{J^M} (Thm 4.1.4.2).
   - If q = p is already the left cartesian fibration classifying W, its replacement is p, and straightening returns W (Cor. 4.1.4.3).
   - Confirmed.
5. **Marking ↔ invertibility (Remark 4.2.3.7).** Marking a k-cell of the index makes the corresponding (k+1)-dimensional cone cell an equivalence. This is the "dimension shift" table of §6. Confirmed.
6. **Variance (§4).**
   - The hom maps of a left cartesian fibration are right cartesian, and conversely (Prop. 3.2.2.6, Thm 3.2.2.24(5)). This gives the alternating marking table.
   - Full duality (Construction 4.1.1.25) exchanges left and right cartesian fibrations (Remark 3.2.2.3), and lax limits with lax colimits.
   - Confirmed. The colimit statement (16) is the formal dual and was not re-derived line by line.
7. **Lifting schema (§5).**
   - Initial maps are generated by X ⊗ {0} → X ⊗ [1]♯ for X = Dₙ♭ or Dₙᵗ (the top cell marked) (Def. 3.2.1.1).
   - Left cartesian fibrations are the maps with unique right lifting against initial maps (Def. 3.2.2.1).
   - Unique lifting against generators implies unique lifting against their saturation, so (19) is necessary and sufficient. Confirmed.
   - The two-arrow example correctly shows that "flagged lifts exist" is weaker than cocartesianness.
8. **Free completion of the marking.** "Marked cells closed under composition, identities and equivalence" is automatic. This agrees with the design note's side result.

**Premises to keep in view.**
- The type theory's cone categories must present Loubaton's Hom_⊖, including its higher transformations given by the marked Gray product ⊖.
- The comparison is in Loubaton's model of (∞,ω)-categories. Relating it to a CaTT-style syntax is a separate step, as for every semantic statement in this project.

**What remains.** A finite, generator-level criterion on π : Ψ → Γ that implies the schema (19), for example a "cocartesian lift of each generator, with unique factorisation through generators" condition checked on the computad. The infinite schema is an answer; a finite test would be a convenience, and its existence is open.
