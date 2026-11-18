# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n), round 2

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. Round 1 and its verified answer are in `answered/finite-fibration-test-higher-base-2026-11-18.md`. The questions are in §4, smallest first.*

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (F. Loubaton, *Categorical theory of (∞,ω)-categories*, [arXiv 2406.05425](https://arxiv.org/abs/2406.05425)).

- A **marked** (∞,ω)-category has a chosen class of positive-dimensional cells. The class contains the equivalences and is closed under composition.
  - A^♯ marks every cell, and A^♭ marks only the equivalences.
  - D_n^t is the n-globe with its top cell marked.
  - ⊗ is the marked Gray tensor.
- **Left cartesian fibrations** (Def. 3.2.2.1). A map p : E → B is a left cartesian fibration if it has the *unique* right lifting property against

  ```
  K ⊗ {0} → K ⊗ [1]^♯,     K ∈ { D_n^♭ : n ≥ 0 } ∪ { D_n^t : n ≥ 1 }.        (★)
  ```

  Equivalently (Thm 3.2.2.24(5)), three conditions hold:
  1. every 1-cell of B has a marked lift with prescribed source, unique up to a contractible space;
  2. for marked u : x → x′ and every z, `E(x′, z) ≃ E(x, z) ×_{B(px,pz)} B(px′, pz)`;
  3. every hom map `E(x, y) → B(px, py)` is a **right** cartesian fibration (lifts with prescribed *target*).

  So the variance alternates: cocartesian 1-cells, cartesian 2-cells, and so on.
- **Straightening** (Thm 4.1.4.2). Left cartesian fibrations over B^♯ correspond to functors B → ω.

### 1.2 Why finite presentations matter

The W-weighted limit of a diagram F is the marked lax limit of F∘p over the total space of the left cartesian fibration p classifying W (Loubaton Cor. 4.2.2.6, Cor. 4.2.3.18, Thm 4.1.4.2). If p is presented by a map of *finite* computads with a marking, a proof checker can accept the weighted limit as a marked lax limit over the finite index, provided it can check (★) by a finite test.

### 1.3 Computads, markings and localisation

- `Free(Ψ)` is the free (∞,ω)-category on a finite computad Ψ: generators are freely adjoined along their boundaries.
- A **marking** μ is a set of positive-dimensional generators, closed up as in §1.1.
- `J[S⁻¹]` is the coherent localisation of a marked (∞,ω)-category J at a set S of marked cells.

## 2. What is known (all proved)

1. **Localisation lemma (Loc).** If S is a set of marked positive-dimensional cells of a marked (∞,ω)-category J and q : J → J[S⁻¹], then restriction is an equivalence of (∞,ω)-categories of marked cones, natural in the apex. So a marked index cell that every diagram inverts may be inverted without changing marked lax limits.
2. **Base a graph (FT₂).** For a finite graph Γ and a functor T : Free(Γ) → Cat with values free on finite graphs, a finite computad Ψ_T (unmarked vertical generators, marked horizontal lifts u_e : e → T_u(e), marked 2-generators θ_{u,β} : β ; u_{e′} ⇒ u_e ; T_u(β)) presents the Grothendieck construction after inverting the θ's. This is complete for that class.
3. **Positive 2-dimensional bases (FT₃).** Call a 2-computad *positive* when both boundary paths of every 2-generator are nonempty. Then Free(Γ) ≃ F₂(Γ), the free strict 2-category (Chanavat, arXiv 2603.22242, Cor. 3.39: positive 2-polygraphs are homotopy polygraphs). For T : F₂(Γ) → Cat with values free on finite graphs, add to the FT₂ data, for each base 2-generator α : u ⇒ v and fibre vertex e, a marked 2-generator λ_{α,e} : τ_{u,e} ; a_{α,e} ⇒ τ_{v,e} (prescribed target, as in the strict Grothendieck construction), and for each vertical β a marked 3-generator Ξ_{α,β} filling the naturality square of λ against θ. Inverting the θ's and Ξ's presents ∫T as a left cartesian fibration over F₂(Γ)^♯. The proof computes the homs of the walking 2-cell case directly (they are intervals or points) and extends by Loubaton's pullback-preserves-colimits theorem (arXiv 2406.05425, Thm 3.2.3.15).
4. **Non-positive bases admit no finite presentation.** For Γ = {x; σ : 1_x ⇒ 1_x}, F₂(Γ) = B²ℕ with groupoidification K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight on B²ℕ has no presentation of this form, with any finite number of higher generators.
5. **Regular 3-polygraphs.** Chanavat (same paper, Cor. 3.38) also proves that all regular 3-polygraphs (Henry's sense) are homotopy polygraphs, and Thm 3.17 gives a general criterion.
6. **Walking 3-cell base, Cat-valued weight (round 1, proved).** Let B be the walking 3-cell (u, v : 0 → 1, α, β : u ⇒ v, Ω : α ⇛ β) and T : B → Cat with T(0) = A and T(1) = C free on finite graphs, T(u) = U, T(v) = V and T(α) = T(β) = a. Then ∫T is presented by the following generators:
   - the FT₃ data: u_e, v_e, θ_{u,f}, θ_{v,f}, λ_{γ,e} : u_e ; a_e ⇒ v_e and Ξ_{γ,f};
   - one marked 3-generator ω_e : λ_{α,e} ⇛ λ_{β,e} per vertex e of A;
   - one marked 4-generator K_{Ω,f} : Ξ_{α,f} ; L_{ω,f} ⇛ R_{ω,f} ; Ξ_{β,f} per generating arrow f of A, where L_ω and R_ω are ω whiskered into the two sides of the Ξ square.
   
   Localise at the θ's, Ξ's and K's. The proof is a pattern:
   - Write ∫T ≃ (K × A) ∐_{I×A} C, where K is the total of the universal weight (x; y₀ —a→ y₁; u, v; λ_α, λ_β; ω) and I = [1].
   - Present K × A as K ⊗ A localised at the mixed generators k ⊗ f.
   - The generators of Ψ_T are then exactly the relative Gray-tensor generators k ⊗ a for k ∈ K ∖ I and a a generator of A.
   
   **Without the 4-generators the presentation is wrong.** For A = C = [1] with identity functors, the generator counts (4, 6, 6, 4) give Euler characteristic 0, while ∫T = B × [1] groupoidifies to a point.
7. **A 4-generator is needed for 2-category-valued weights (round 1, proved).** For the walking 2-cell base and the constant weight D₂, the product D₂ × D₂ needs its 4-cell (α ⊗ fibre 2-cell): without it the counts (4, 8, 8, 4) give χ = 0 ≠ 1.
8. **Regularity is not necessary (round 1, proved).** The positive, non-regular 3-computad x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r has Free ≃ F₃. The Θ-nerve of F₃ is the union of the nerve of F₂ and of the full sub-3-globe on x, z, intersecting in ∂D₃, so the attachment of ζ is a homotopy pushout.

## 3. The shape of FT_n (revised)

The generators of a presentation are the relative Gray-tensor generators: for a base cell k of the universal total and a fibre generator a, one marked generator k ⊗ a of dimension dim k + dim a. Lifts of base cells have alternating variance. The generators lying over identities are inverted. The top dimension is the base dimension plus the fibre dimension.

## 4. Questions

1. **2-dimensional base, 2-category-valued weight.** Let Γ = (u, v : 0 → 1, α : u ⇒ v) and T valued in free 2-categories on finite positive 2-computads. Prove that the relative Gray-tensor generators (including the 4-generators of item 7) present ∫T, for example by the method of item 6. What replaces "K × A ≃ (K ⊗ A) localised at mixed generators" when A is a 2-category?
2. **General FT_n over positive or regular bases.** For a finite base computad Γ with Free(Γ) ≃ Fₙ(Γ) and a weight valued in free m-categories with homotopical presentations, prove that the relative Gray-tensor generators present ∫T, by induction on the cells of Γ using pushouts of universal totals. State the finite check.
3. **Which 3-computads are homotopical?** Item 8 shows that a whiskered boundary is harmless in one example. Is every positive 3-computad homotopical (Free(Γ) ≃ F₃(Γ))? If not, give a positive counterexample. Is there a criterion covering both item 8 and Chanavat's regular 3-polygraphs?
4. **Necessity of positivity in dimension ≥ 3.** Is there a non-positive 3-computad whose strict free object has a finite presentation, or does every non-positive one have a groupoidification of infinite homological type, as in known item 4?

## 5. What would count as an answer

A proof or counterexample for any question; a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs.

# Researcher Response

**Question 1 has an affirmative answer. Question 4 also has an affirmative answer: positivity is not necessary, even for a computad with a nonidentity 3-generator.**

For Question 1, the required presentation has one 4-generator for each generating fibre 2-cell. The missing localization statement follows from a lemma about tensoring a localization with the Gray interval. I give that lemma and the complete presentation below.

For Question 4, the example is
\[
0,1;\qquad f:0\to1;\qquad
\alpha:f\Rightarrow f;\qquad
T:1_f\Rrightarrow\alpha.
\]
Its strict free 3-category is already its coherent free \((\infty,\omega)\)-category, and its groupoidification is contractible.

I do not settle Question 3. For Question 2, the local relative construction works, but turning the resulting gluing diagram into the asserted finite computad requires an additional compatibility argument described in §4 below.

## 1. Question 1: the finite presentation

Write
\[
A=T(0),\qquad C=T(1),\qquad
U=T(u),\qquad V=T(v),\qquad a=T(\alpha):U\Rightarrow V.
\]

Use the given positive finite 2-computad presentations of \(A\) and \(C\). Write \(x,y\) for vertices of \(A\), \(f:x\to y\) for a generating arrow, and
\[
\rho:p\Rightarrow q,\qquad p,q:x\to y,
\]
for a generating 2-cell.

The equations expressing strict 2-naturality are
\[
Uf;a_y=a_x;Vf,
\qquad
U\rho*a_y=a_x*V\rho.
\tag{1}
\]
Here and below, \(;\) denotes 1-cell composition in execution order, \(\cdot\) denotes vertical composition of 2-cells in execution order, and \(*\) denotes whiskering.

These equations also describe the weight when interpreted through \(\omega\): the coherence comparisons for strong functors and strong transformations take values in invertible 2-cells of \(C\), and a free strict 2-category has no nonidentity invertible 2-cells. Indeed, the number of generating 2-cells in a composite is additive and is unchanged by interchange.

### 1.1 Generators and marking

The computad \(\Psi_T\) has the following generators.

| Dimension | Generators |
|---|---|
| \(0\) | The vertices of \(A\) and \(C\) |
| \(1\) | Their generating arrows, and \(u_x:x\to Ux,\ v_x:x\to Vx\) |
| \(2\) | Their generating 2-cells, and \(\eta^u_f,\eta^v_f,\lambda_x\) |
| \(3\) | \(\kappa^u_\rho,\kappa^v_\rho,\Xi_f\) |
| \(4\) | \(\Omega_\rho\) |

Mark \(u_x,v_x,\lambda_x\), and all the structural generators
\[
S=\{\eta^u_f,\eta^v_f,\kappa^u_\rho,\kappa^v_\rho,\Xi_f,\Omega_\rho\}.
\tag{2}
\]
The fibre generators retain the flat marking. Localize precisely at \(S\).

The result is
\[
\boxed{
\operatorname{Free}(\Psi_T)[S^{-1}]
\simeq
\int_B T
}
\tag{3}
\]
as marked \((\infty,\omega)\)-categories over \(B^\sharp\).

Here are all the boundaries.

### 1.2 The 2-generators

For \(w=u,v\), with \(W=U,V\), respectively, put
\[
\eta^w_f:
w_x;Wf\Longrightarrow f;w_y.
\tag{4}
\]
Thus \(\eta\) has the inverse orientation to the \(\theta\) in the question.

The lift of the base 2-cell is
\[
\lambda_x:u_x;a_x\Longrightarrow v_x.
\tag{5}
\]
It has prescribed target, as required.

Extend \(\eta\) to paths by
\[
\eta^w_{1_x}=1_{w_x},
\qquad
\eta^w_{pq}
=
(\eta^w_p*Wq)\cdot(p*\eta^w_q).
\tag{6}
\]

### 1.3 The 3-generators

For each generating fibre 2-cell \(\rho:p\Rightarrow q\), add
\[
\kappa^w_\rho:
\eta^w_p\cdot(\rho*w_y)
\Rrightarrow
(w_x*W\rho)\cdot\eta^w_q,
\qquad w=u,v.
\tag{7}
\]

These are the compatibility cells for transporting fibre 2-cells. Their orientation is determined by the next step of the Gray cylinder.

For any path \(p:x\to y\), define
\[
P_p=(\lambda_x*Vp)\cdot\eta^v_p,
\qquad
Q_p=(\eta^u_p*a_y)\cdot(p*\lambda_y).
\tag{8}
\]
By (1), these are parallel 2-cells. For each generating arrow \(f\), add
\[
\Xi_f:P_f\Rrightarrow Q_f.
\tag{9}
\]

The extension \(\Xi_p\) to arbitrary paths is determined by pasting. Explicitly, \(\Xi_{1_x}\) is an identity, and for \(p:x\to y,\ q:y\to z\), use
\[
P_{pq}
=
(P_p*Vq)\cdot(p*\eta^v_q).
\]
First apply \(\Xi_p\), obtaining
\[
(Q_p*Vq)\cdot(p*\eta^v_q)
=
(\eta^u_p*a_y*Vq)\cdot(p*P_q).
\]
Then apply \(p*\Xi_q\), obtaining \(Q_{pq}\). This specifies the whiskerings in \(\Xi_{pq}\).

### 1.4 The 4-generators

For a generating \(\rho:p\Rightarrow q\), there are two parallel 3-cells with common 2-source and 2-target
\[
P_p\cdot(\rho*v_y),
\qquad
(u_x*a_x*V\rho)\cdot Q_q.
\tag{10}
\]

The first route applies \(\Xi_p\), then \(\kappa^u_\rho\):
\[
\begin{aligned}
P_p\cdot(\rho*v_y)
&\xRightarrow{\ \Xi_p\ }
Q_p\cdot(\rho*v_y)\\
&=
(\eta^u_p*a_y)\cdot(\rho*u_y*a_y)\cdot(q*\lambda_y)\\
&\xRightarrow{\ \kappa^u_\rho*a_y\ }
(u_x*U\rho*a_y)\cdot Q_q\\
&=
(u_x*a_x*V\rho)\cdot Q_q.
\end{aligned}
\tag{11}
\]

The second route applies \(\kappa^v_\rho\), then \(\Xi_q\):
\[
\begin{aligned}
P_p\cdot(\rho*v_y)
&=
(\lambda_x*Vp)\cdot\eta^v_p\cdot(\rho*v_y)\\
&\xRightarrow{\ \kappa^v_\rho\ }
(\lambda_x*Vp)\cdot(v_x*V\rho)\cdot\eta^v_q\\
&=
(u_x*a_x*V\rho)\cdot P_q\\
&\xRightarrow{\ \Xi_q\ }
(u_x*a_x*V\rho)\cdot Q_q.
\end{aligned}
\tag{12}
\]
Each arrow is whiskered by the adjacent displayed 2-cells. The equalities use interchange and (1).

Adjoin one 4-generator
\[
\Omega_\rho:
\bigl[\text{route }(11)\bigr]
\Longrightarrow
\bigl[\text{route }(12)\bigr].
\tag{13}
\]

This specifies the entire finite computad. In particular, there are no additional generators above dimension \(4\).

## 2. Why this presentation works

The proof uses two interval cylinders. This supplies the attaching maps before localization and avoids assuming a pasting theorem for arbitrary positive 4-computads.

### 2.1 A tensor-localization lemma

Let \(I=D_1\), with generating arrow \(i\). If \(s:D_n\to X\) is a positive-dimensional cell, write
\[
s\otimes0,\qquad s\otimes1,\qquad s\otimes i
\]
for its two endpoint copies and its cylinder comparison.

**Lemma.** For any family \(S\) of positive-dimensional cells,
\[
\boxed{
X[S^{-1}]\otimes I
\simeq
(X\otimes I)
\left[
\{s\otimes0,s\otimes1,s\otimes i:s\in S\}^{-1}
\right].
}
\tag{14}
\]

Thus tensoring a localization with the Gray interval requires inverting both endpoint copies and the comparison between them.

#### Proof

Let \(\pi_n:D_n\to D_{n-1}\) collapse the top cell. It is the coherent localization at that cell: for \(n=1\), the walking equivalence is equivalent to a point; higher cases follow by suspension.

Put \(C_n=D_n\otimes I\). It suffices to prove that
\[
\pi_n\otimes I:C_n\longrightarrow C_{n-1}
\tag{15}
\]
localizes exactly the two endpoint \(n\)-cells and the mixed \((n+1)\)-cell.

For \(n=1\), first invert the square’s 2-cell. This gives \(I\times I\). Next invert the two arrows in the first coordinate. A map \(I\times I\to Z\) is a natural transformation between two arrows of \(Z\); it is an equivalence precisely when its two evaluations are equivalences. The resulting mapping space is therefore \(\operatorname{Map}(I,Z)\). This proves (15) for \(n=1\). The Cartesian comparison and the pointwise equivalence criterion used here are Loubaton’s Propositions 3.1.3.1 and 2.2.1.59. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For \(n\ge2\), use the cylinder decomposition
\[
C_n\simeq
(I\vee D_n)
\amalg_{D_n}
\Sigma C_{n-1}
\amalg_{D_n}
(D_n\vee I).
\tag{16}
\]
The outer attaching maps are whiskerings. This is Loubaton’s Proposition 2.3.1.10. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Inverting the two outer \(n\)-cells makes their whiskered images invertible. Consequently, the two endpoint conditions on the middle term are already forced. Inverting the mixed \((n+1)\)-cell supplies its remaining condition. By induction, the middle term becomes \(\Sigma C_{n-2}\); the outer terms become \(I\vee D_{n-1}\) and \(D_{n-1}\vee I\).

Naturality of (16) identifies the resulting diagram with the diagram for \(C_{n-1}\). To check that this imposes exactly the stated localization, map the diagrams into an arbitrary \(Z\). The mapping spaces are limits, and the interface invertibility conditions follow from the outer ones by whiskering. Hence no additional condition has been imposed.

Finally, express \(X[S^{-1}]\) by pushing out the maps \(\pi_{\dim s}\), and tensor that pushout with \(I\). The Gray cylinder preserves colimits, so the globe calculation proves (14). ∎

### 2.2 The replacement for the mixed-localization formula

Let
\[
K=1^{\mathrm{co}}\!\star I.
\]
Concretely, \(K\) has vertices \(x,y_0,y_1\), arrows
\[
u:x\to y_0,\qquad v:x\to y_1,\qquad a:y_0\to y_1,
\]
and a 2-cell \(u;a\Rightarrow v\).

For the present \(A\), the needed formula **does remain true**, with all positive-dimensional fibre generators included:
\[
\boxed{
(A\otimes K)
\left[
(g\otimes k)^{-1}:
\dim g>0,\ \dim k>0
\right]
\simeq A\times K.
}
\tag{17}
\]
Here \(g\) and \(k\) range over generators in the specified presentations. I have ordered tensor factors as fibre first; the explicit boundaries in §1 fix the convention.

To prove (17), write
\[
Q=(A\otimes I_{\mathrm{in}})\otimes I_{\mathrm{out}}.
\]
Consider
\[
Q
\longrightarrow
(A\times I_{\mathrm{in}})\otimes I_{\mathrm{out}}
\longrightarrow
A\times(I_{\mathrm{in}}\otimes I_{\mathrm{out}}).
\tag{18}
\]

The first arrow localizes at
\[
g\otimes i_{\mathrm{in}}\otimes0,\quad
g\otimes i_{\mathrm{in}}\otimes1,\quad
g\otimes i_{\mathrm{in}}\otimes i_{\mathrm{out}},
\tag{19}
\]
by (14) and the marked interval comparison.

For the second arrow, apply
\[
(D^\sharp\times C)\otimes I^\sharp
\simeq
D^\sharp\times(C\otimes I^\sharp)
\]
with \(D=A\) and \(C=I_{\mathrm{in}}^\flat\). The remaining localization generators are
\[
g\otimes0\otimes i_{\mathrm{out}},
\qquad
g\otimes1\otimes i_{\mathrm{out}}.
\tag{20}
\]
Indeed, the marking of \(A^\sharp\times I_{\mathrm{in}}^\flat\) is generated by the positive \(A\)-generators at the interval’s vertices, together with equivalences and their composites and whiskerings. This uses Loubaton’s marked-cylinder construction and Proposition 3.1.3.2. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Now collapse the \(0\)-face of the outer interval. Since
\[
K=1\amalg_{I_{\mathrm{in}}\otimes\{0\}}
(I_{\mathrm{in}}\otimes I_{\mathrm{out}}),
\]
the localization generators surviving the collapse are exactly those in (17).

For a generating fibre 2-cell, this argument includes its mixed cells of dimensions \(3\) and \(4\). Omitting the latter is precisely what would invalidate the comparison.

### 2.3 The double-cylinder presentation

Set
\[
H=A\otimes I_{\mathrm{in}}.
\]
There are strict maps
\[
r:H\to A,\qquad h:H\to C.
\]
The first is projection. The second is
\[
A\otimes I_{\mathrm{in}}
\longrightarrow A\times I_{\mathrm{in}}
\xrightarrow{\,a\,}C,
\]
where the last map is evaluation of the transformation \(a\).

Form the homotopy pushout
\[
P=
A\amalg_{H\otimes\{0\}}
(H\otimes I_{\mathrm{out}})
\amalg_{H\otimes\{1\}}C.
\tag{21}
\]

The relative cylinder adjoins one \((d+1)\)-generator for each \(d\)-generator of \(H\). Substituting \(r\) and \(h\) into its boundaries gives exactly the generators and boundaries of §1:

| Generator of \(H\) | Generator after the outer gluing |
|---|---|
| \(x\otimes0,\ x\otimes1\) | \(u_x,v_x\) |
| \(f\otimes0,\ f\otimes1\) | \(\eta^u_f,\eta^v_f\) |
| \(x\otimes i_{\mathrm{in}}\) | \(\lambda_x\) |
| \(\rho\otimes0,\ \rho\otimes1\) | \(\kappa^u_\rho,\kappa^v_\rho\) |
| \(f\otimes i_{\mathrm{in}}\) | \(\Xi_f\) |
| \(\rho\otimes i_{\mathrm{in}}\) | \(\Omega_\rho\) |

This is a homotopy cellular presentation. To justify that assertion, filter \(A\) by its generating-cell attachments. At each relative cylinder step, the map
\[
(\partial D_d\otimes I)
\amalg_{\partial D_d\otimes\partial I}
(D_d\otimes\partial I)
\longrightarrow D_d\otimes I
\tag{22}
\]
adjoins its unique top \((d+1)\)-cell. Globe tensors are acyclic atoms, so Chanavat’s Corollary 3.27 and Theorem 3.29 identify these cellular attachments with homotopy attachments. Pushing their finite filtration out along \(r,h\) preserves it. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

There is also a strictness check: Loubaton’s Theorem 2.3.3.22 makes (21) strict. Applying the strict reflector computes it as the ordinary strict pushout of the cylinder polygraphs, which is the displayed computad. Thus
\[
P\simeq\operatorname{Free}(\Psi_T).
\]
No general assertion about positive 4-polygraphs is needed. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 2.4 Localization identifies the total

Push the localization (18) through (21).

The generators in (19) lying on the two outer endpoint faces already map to identities under \(r\) and \(h\). The surviving generators are precisely
\[
\eta^u_f,\eta^v_f,\kappa^u_\rho,\kappa^v_\rho,\Xi_f,\Omega_\rho.
\]
Consequently,
\[
P[S^{-1}]
\simeq
(A\times K)\amalg_{A\times I}C.
\tag{23}
\]

Equip \(K\) with its universal cartesian marking: \(u,v,\lambda\) are marked, and the arrow \(a\) in the target fibre is unmarked. The marking on (23) then agrees with the marking specified in §1.

Loubaton’s suspension-base classification, Corollary 4.1.2.19, identifies the right-hand side of (23) with the left cartesian fibration classified by
\[
A\times I\xrightarrow{a}C.
\]
Since \(B=\Sigma I\), this is \(\int_B T\), proving (3). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 2.5 The finite check in this case

A certificate consists of:

1. The finite positive 2-computads presenting \(A,C\).
2. Images of their relevant generators specifying \(U,V\), with boundary certificates.
3. The arrows \(a_x\), together with the finitely many equations (1), for generating arrows and generating 2-cells.
4. The computad of §1, its projection to \(B\), the stated marking, and the localization set (2).

Equations on composite paths and composite 2-cells follow by pasting. Equality certificates may explicitly use associativity, units and interchange; an unrestricted equality-decision algorithm is not required.

The proof above then certifies all of \((★)\). This is a recognition criterion for this constructed class of presentations.

## 3. Question 4: a non-positive example with a finite presentation

Consider the 3-computad
\[
\Gamma_0=\{0,1\},\qquad
\Gamma_1=\{f:0\to1\},\qquad
\Gamma_2=\{\alpha:f\Rightarrow f\},\qquad
\Gamma_3=\{T:1_f\Rrightarrow\alpha\}.
\tag{24}
\]
The source of \(T\) is an identity **2-cell**, so this is non-positive in dimension \(3\).

Nevertheless,
\[
\boxed{
\operatorname{Free}_{(\infty,\omega)}(\Gamma)
\simeq F_3(\Gamma).
}
\tag{25}
\]
In particular, no localization or extra generators are necessary.

### 3.1 A two-dimensional precursor

Let \(Q\) be
\[
*;\qquad t:*\to*;\qquad \eta:1_*\Rightarrow t.
\tag{26}
\]
Let \(\mathcal I=\Delta_+^{\mathrm{inj}}\), described using finite ordinals
\[
\underline n=\{1,\ldots,n\},\qquad n\ge0,
\]
and order-preserving injections. Give \(\mathcal I\) the concatenation monoidal structure, with unit \(\underline0\).

There is a strict identification
\[
F_2(Q)=B\mathcal I.
\tag{27}
\]
Indeed, the 1-cells are \(t^n\), and
\[
\operatorname{Hom}_2(t^n,t^m)
=
\{\text{order-preserving injections }\underline n\hookrightarrow\underline m\}.
\tag{28}
\]
A whiskered \(\eta\) inserts a letter \(t\). A composite records the positions of the original letters in the final word. Interchange identifies different orders of independent insertions. Conversely, insert the new letters from left to right to obtain a normal form for each injection. Vertical composition is composition of injections; horizontal composition is concatenation.

The substantive point is that (27) is also coherently free.

Blans–Linskens’ monoidal-envelope universal property gives
\[
\operatorname{Env}_{\mathbb E_1}(\mathbb E_0)
\simeq
\Delta_+^{\mathrm{inj}},
\tag{29}
\]
where an \(\mathbb E_0\)-algebra in a monoidal \(\infty\)-category \(\mathcal M\) is an arrow \(\mathbb1_{\mathcal M}\to X\). Thus \(\mathcal I\) is the free monoidal \(\infty\)-category on such an arrow. See their Lemma 2.2, Remark 2.3, and Examples 2.4–2.5. [arxiv.org](https://arxiv.org/html/2605.03150v1?utm_source=chatgpt.com)

For an arbitrary \((\infty,2)\)-category \(\mathcal D\) and \(d\in\mathcal D\), it follows that
\[
\begin{aligned}
\operatorname{hofib}_{d}\!\left(
\operatorname{Map}(B\mathcal I,\mathcal D)\to\mathcal D_0
\right)
&\simeq
\operatorname{Map}_{\mathrm{Mon}_\infty}
\bigl(\mathcal I,\operatorname{End}_{\mathcal D}(d)\bigr)\\
&\simeq
\left(\operatorname{End}_{\mathcal D}(d)_{1_d/}\right)^\simeq.
\end{aligned}
\tag{30}
\]
The first equivalence follows by viewing a one-object Segal category as a monoidal \(\infty\)-category. The homotopy fibre fixes an identification of the image of \(*\) with \(d\).

The last space is exactly the space of generator data
\[
t:d\to d,\qquad \eta:1_d\Rightarrow t.
\]
For each such datum, the space of coherent extensions is contractible. Therefore the canonical comparison is an equivalence:
\[
\operatorname{Free}_{(\infty,2)}(Q)\simeq F_2(Q).
\tag{31}
\]

This remains an equivalence in Loubaton’s \((\infty,\omega)\)-theory: the finite-level inclusion is fully faithful and preserves colimits, by his adjunction (2.2.1.42) and Proposition 2.2.1.43. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 3.2 Suspension gives the 3-dimensional example

The computad (24) is \(\Sigma Q\):
\[
*\longmapsto f,\qquad t\longmapsto\alpha,\qquad\eta\longmapsto T.
\]

Suspension is a left adjoint into the category with two distinguished vertices, so it preserves the cellular attaching pushouts. Its nontrivial hom is the category being suspended. Hence
\[
\begin{aligned}
\operatorname{Free}_{(\infty,\omega)}(\Gamma)
&\simeq
\Sigma\operatorname{Free}_{(\infty,\omega)}(Q)\\
&\simeq
\Sigma F_2(Q)\\
&\cong F_3(\Gamma).
\end{aligned}
\]
These suspension facts are Loubaton’s Construction 2.2.1.18 and Proposition 2.2.1.20. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Explicitly, the 2-cells \(f\Rightarrow f\) are \(\alpha^n\), and
\[
\operatorname{Hom}_3(\alpha^n,\alpha^m)
=
\{\text{order-preserving injections }\underline n\hookrightarrow\underline m\}.
\tag{32}
\]
The generator \(T\) is the unique injection \(\underline0\to\underline1\).

### 3.3 Groupoidification

Having proved coherent freeness, groupoidification can be computed from the finite cells.

For \(Q\), the loop \(t\) gives a circle, and \(\eta:1\Rightarrow t\) attaches a disk with degree-one boundary:
\[
|F_2(Q)|\simeq S^1\cup_{\mathrm{id}}D^2\simeq *.
\tag{33}
\]

For \(\Gamma\), the 1-skeleton is an interval. After contracting it, \(\alpha\) gives a 2-sphere, and \(T\) attaches a 3-cell by a degree-one map. Thus
\[
|F_3(\Gamma)|\simeq *.
\tag{34}
\]

The terminal weight on this base therefore has the finite presentation
\[
\Psi=\Gamma,\qquad S=\varnothing,
\]
with all positive generators marked. Further suspensions give examples in every dimension \(n\ge3\).

Thus non-positivity implies neither failure of finite coherent presentation nor infinite homological type.

## 4. What remains for Questions 2 and 3

### 4.1 The local relative step in Question 2

For a walking \(k\)-cell, write
\[
D_k=\Sigma D_{k-1}.
\]
A restricted weight is specified by
\[
F:A\times D_{k-1}\to C.
\]
Set
\[
L_k=1^{\mathrm{co}}\!\star D_{k-1},
\qquad
R_k=
D_{k-1}
\amalg_{\partial D_{k-1}}
\bigl(1^{\mathrm{co}}\!\star\partial D_{k-1}\bigr).
\tag{35}
\]

The map \(R_k\to L_k\) adjoins exactly one \(k\)-generator: the cone on the top \((k-1)\)-cell. The local total has the form
\[
E_{D_k}\simeq
(A\times L_k)\amalg_{A\times D_{k-1}}C.
\tag{36}
\]
Its boundary restriction is obtained using \(R_k\) in place of \(L_k\).

Consequently, the relative Gray construction has the proposed local count: one generator of dimension \(k+j\) for each generating \(j\)-cell of \(A\). For \(j=0\), it is the marked lift of the base cell. For \(j>0\), it is a structural generator to be inverted.

### 4.2 Why categorical gluing does not yet prove the global finite statement

Suppose the previous stage has been presented as
\[
E_{\mathrm{old}}\simeq\operatorname{Free}(\Psi)[S^{-1}].
\]
Gluing the actual totals gives attaching maps into this **localized** category. To adjoin the proposed generators to \(\Psi\), one needs compatible attaching maps into \(\operatorname{Free}(\Psi)\), expressed by literal pastings before localization.

Such lifts are not automatic. With the vertices fixed, the inverse of a marked arrow
\[
s:x\to y
\]
exists in \(\operatorname{Free}(s)[s^{-1}]\), but no arrow \(y\to x\) exists in \(\operatorname{Free}(s)\).

This example does not refute the general FT claim. It shows what its proposed induction must additionally prove. One needs either:

- a compatible construction of the unlocalized presentations that lifts every required boundary map; or
- a finite relative rectification theorem, controlling extra generators, their markings, and the bound \(n+m\).

The walking 2-cell proof supplies that compatibility explicitly through (21). Preservation of colimits alone does not supply it for arbitrary base attachments.

### 4.3 Question 3

I do not prove that every positive 3-computad is homotopical, and I do not have a positive counterexample. The non-positive example in §3 answers the necessity question but does not decide that sufficiency question.
