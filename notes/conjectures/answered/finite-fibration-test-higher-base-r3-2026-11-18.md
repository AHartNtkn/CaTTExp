# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n), round 3

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. Rounds 1 and 2 and their verified answers are in `answered/finite-fibration-test-higher-base-2026-11-18.md` and `answered/finite-fibration-test-higher-base-r2-2026-11-18.md`; nothing answered there is re-asked. The questions are in §4, smallest first.*

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
4. **Some non-positive bases admit no finite presentation.** For Γ = {x; σ : 1_x ⇒ 1_x}, F₂(Γ) = B²ℕ with groupoidification K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight on B²ℕ has no presentation of this form, with any finite number of higher generators.
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

9. **2-category-valued weights over the walking 2-cell (round 2, proved).** Let B be the walking 2-cell (u, v : 0 → 1, α : u ⇒ v) and T valued in free 2-categories on finite positive 2-computads, A = T(0), C = T(1), U, V, a = T(α). Since a free strict 2-category has no non-identity invertible 2-cells, the weight data are strict: `Uf ; a_y = a_x ; Vf` and `Uρ ∗ a_y = a_x ∗ Vρ`.
   - **Generators.** Those of A and C; marked u_x, v_x; η^w_f : w_x ; Wf ⇒ f ; w_y (w = u, v); marked λ_x : u_x ; a_x ⇒ v_x; κ^w_ρ : η^w_p · (ρ ∗ w_y) ⇛ (w_x ∗ Wρ) · η^w_q for each fibre 2-cell ρ : p ⇒ q; Ξ_f : (λ_x ∗ Vf) · η^v_f ⇛ (η^u_f ∗ a_y) · (f ∗ λ_y); and one 4-generator Ω_ρ between the two composites of Ξ and κ. Localise at S = {η, κ, Ξ, Ω}.
   - **Proof.** The computad is the strict pushout `A ∐_{H⊗{0}} (H ⊗ I_out) ∐_{H⊗{1}} C` with H = A ⊗ I_in (a double Gray cylinder), and localising it gives `(A × K) ∐_{A×I} C` with K = 1^co ⋆ I, which is ∫T by Loubaton's suspension-base classification.
   - **Tensor-localisation lemma.** For any set S of positive-dimensional cells, `X[S⁻¹] ⊗ I ≃ (X ⊗ I)[{s ⊗ 0, s ⊗ 1, s ⊗ i}⁻¹]`.
   - **Mixed localisation for 2-category fibres.** `(A ⊗ K)[(g ⊗ k)⁻¹ : dim g, dim k > 0] ≃ A × K`, provided the mixed generators of every fibre dimension are included.
10. **Positivity is not necessary (round 2, proved).** The 2-computad Q = (∗; t : ∗ → ∗; η : 1_∗ ⇒ t) is non-positive, and Free(Q) ≃ F₂(Q) = BΔ_+^inj (order-preserving injections under concatenation; coherent freeness from the monoidal envelope Env_{E1}(E0) ≃ Δ_+^inj, Blans–Linskens arXiv 2605.03150). Its suspension (0, 1; f; α : f ⇒ f; T : 1_f ⇛ α) is a non-positive 3-computad with Free ≃ F₃, and both groupoidify to a point. So the terminal weight on these bases has a finite presentation with no localisation. Compare item 4: (x; σ : 1_x ⇒ 1_x) is non-positive and not homotopical.
11. **The gap in the induction (round 2).** Gluing local totals `E_{D_k} ≃ (A × L_k) ∐_{A × D_{k−1}} C`, with L_k = 1^co ⋆ D_{k−1}, gives the right local generator count, one generator of dimension k + j per fibre j-generator. But the attaching maps land in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself. Such lifts need not exist: in Free(s)[s⁻¹] the inverse of a marked arrow s exists, in Free(s) no arrow goes back. For the walking 2-cell the double cylinder supplies the lifts explicitly; for a base generator whose boundary is a composite, nothing yet does.

## 3. The shape of FT_n (revised)

The generators of a presentation are the relative Gray-tensor generators: for a base cell k of the universal total and a fibre generator a, one marked generator k ⊗ a of dimension dim k + dim a. Lifts of base cells have alternating variance. The generators lying over identities are inverted. The top dimension is the base dimension plus the fibre dimension. The hypothesis on the base is that it be **homotopical** (Free(Γ) ≃ F_n(Γ)); positivity (dimension 2) and regularity (dimension 3) are sufficient criteria, not necessary ones.

## 4. Questions

1. **A base generator with a composite boundary.** Let Γ = (0, 1, 2; f : 0 → 1, g : 1 → 2, h : 0 → 2; α : f ; g ⇒ h), which is positive, and T valued in free categories (or free 2-categories) on finite graphs (or finite positive 2-computads). Prove that the relative Gray-tensor generators present ∫T, by supplying the attaching maps of the generators over α in the unlocalised Free(Ψ). The lift of α must be compared with the composite of the lifts of f and g, which is a composite of marked generators, not a generator. Does a double-cylinder construction as in item 9, with the outer cylinder over a 2-simplex-shaped universal total, give these maps?
2. **General FT_n over homotopical bases.** For a finite base computad Γ with Free(Γ) ≃ F_n(Γ) and a weight valued in free m-categories on homotopical computads, prove that the relative Gray-tensor generators present ∫T, by induction on the cells of Γ, and state the finite check. The step that needs an argument is the compatible lift of attaching maps (item 11): either a construction of the unlocalised presentations that lifts every required boundary map, or a finite relative rectification theorem that controls the extra generators, their markings and the dimension bound n + m.
3. **Which 2- and 3-computads are homotopical?** Item 10 shows that positivity is not necessary in dimension 2, and item 4 shows that some non-positive 2-computads fail. Give a criterion for a finite 2-computad to satisfy Free ≃ F₂ that covers the positive ones and Q of item 10 and excludes (x; σ : 1_x ⇒ 1_x). In dimension 3: is every positive 3-computad homotopical? If not, give a positive counterexample. Is there a criterion covering item 8, item 10's suspension and Chanavat's regular 3-polygraphs?

## 5. What would count as an answer

A proof or counterexample for any question; a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs, or to a published characterisation of homotopical polygraphs in low dimension.

# Researcher Response

**Question 1 is affirmative. The same construction closes the attaching-map gap for every finite homotopical 2-computad base, with fibres of arbitrary finite dimension \(m\).** The presentation has exactly the proposed generators and dimension at most \(m+2\).

There is also a sufficient criterion for Question 3 beyond positivity: one-object 2-computads whose generating 2-cells all have a single generating arrow as target are homotopical, including nullary sources. The dual statement holds with “source” in place of “target.” I give this criterion, an obstruction to weakening it, and a 3-dimensional attachment rule below.

Throughout, \(\operatorname{Free}(\Psi)\) means the coherent cellular construction specified in your §1.3.

## 1. The composite-boundary attaching map

Write
\[
A=T(0),\qquad B=T(1),\qquad C=T(2),
\]
and
\[
F=T(f):A\to B,\qquad
G=T(g):B\to C,\qquad
H=T(h):A\to C,\qquad
a=T(\alpha):GF\Rightarrow H.
\]

The key construction is
\[
\delta_2:I\longrightarrow[2],
\qquad 0\longmapsto0,\quad1\longmapsto2.
\]
Tensoring this map with \(A\) supplies the comparison with the composite of the two lifts **before localization**.

### 1.1 The graph presentation

For a strict functor \(W:D\to E\), let
\[
M_W=(D\otimes I)\amalg_{D\otimes\{1\}}E.
\tag{1}
\]
Its distinguished endpoint fibres are \(D\) and \(E\).

Glue \(M_F,M_G,M_H\) along their endpoint fibres, giving the unlocalized graph presentation \(P_{\mathrm{gr}}\). For 2-category fibres its structural generators are
\[
\eta^w_b:w_x;Wb\Rightarrow b;w_y
\tag{2}
\]
and
\[
\kappa^w_\rho:
\eta^w_p\cdot(\rho*w_y)
\Rrightarrow
(w_x*W\rho)\cdot\eta^w_q,
\tag{3}
\]
where \((w,W)\) is \((f,F),(g,G)\), or \((h,H)\), and \(\rho:p\Rightarrow q\) is a generating fibre 2-cell.

Here \(;\) is chronological 1-composition, \(\cdot\) is chronological vertical 2-composition, and \(*\) is whiskering.

For a path \(p;r\), use
\[
\eta^w_{p;r}
=(\eta^w_p*Wr)\cdot(p*\eta^w_r),
\qquad
\eta^w_{1_x}=1_{w_x}.
\tag{4}
\]

The notation \(\kappa^w_\sigma\) also makes sense for an arbitrary fibre 2-cell \(\sigma\): it is the image of the mixed cell under
\[
D_2\otimes I\xrightarrow{\sigma\otimes I}D\otimes I
\longrightarrow P_{\mathrm{gr}}.
\tag{5}
\]
Thus, for example, \(\kappa^g_{F\rho}\) is a finite pasting of existing \(g\)-cylinder generators. It is not an additional generator or a cell obtained by localization.

### 1.2 Concatenating the two cylinders

The ordinal spine decomposition gives
\[
A\otimes[2]
\simeq
(A\otimes I)\amalg_A(A\otimes I).
\tag{6}
\]
Map the first interval into the \(f\)-cylinder. Map the second by
\[
A\otimes I\xrightarrow{F\otimes I}B\otimes I
\longrightarrow P_{\mathrm{gr}},
\]
using the \(g\)-cylinder. Their maps on the common endpoint agree.

Precomposing with \(A\otimes\delta_2\) therefore gives
\[
A\otimes I
\xrightarrow{A\otimes\delta_2}
A\otimes[2]
\longrightarrow P_{\mathrm{gr}}.
\tag{7}
\]
Its terminal endpoint is the map \(GF:A\to C\), so it extends to
\[
J_{fg}:M_{GF}\longrightarrow P_{\mathrm{gr}}.
\tag{8}
\]

This construction uses the functorial Gray cylinder and its preservation of colimits. Moreover, the finite ordinal cylinders are strict for strict input, by Loubaton’s Theorem 2.3.3.22, so their generating-cell images can be evaluated as finite strict pastings. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The horizontal generator is sent to
\[
\tau_x:=f_x;g_{Fx}.
\tag{9}
\]
For \(p:x\to y\), its naturality cell is
\[
\boxed{
\eta^{fg}_p
=
(f_x*\eta^g_{Fp})\cdot(\eta^f_p*g_{Fy}).
}
\tag{10}
\]
Its type is
\[
\eta^{fg}_p:\tau_x;GFp\Rightarrow p;\tau_y.
\]

For completeness, the corresponding fibre-2-cell comparison is also a directed pasting of existing generators. Define
\[
\operatorname{wh}(L,K,R):
L\cdot sK\cdot R
\Rrightarrow
L\cdot tK\cdot R
\]
for a 3-cell \(K\), and write \(\odot\) for chronological 3-composition. Then
\[
\boxed{
\begin{aligned}
\kappa^{fg}_\rho
={}&
\operatorname{wh}
\bigl(f_x*\eta^g_{Fp},\ \kappa^f_\rho*g_{Fy},\ 1\bigr)\\
&\odot
\operatorname{wh}
\bigl(1,\ f_x*\kappa^g_{F\rho},\ \eta^f_q*g_{Fy}\bigr).
\end{aligned}}
\tag{11}
\]
It has type
\[
\kappa^{fg}_\rho:
\eta^{fg}_p\cdot(\rho*\tau_y)
\Rrightarrow
(\tau_x*GF\rho)\cdot\eta^{fg}_q.
\tag{12}
\]

The order is first \(\kappa^f_\rho\), then \(\kappa^g_{F\rho}\). Neither (10) nor (11) uses an inverse.

### 1.3 The raw boundary map

Let \(R_\alpha\) be the parallel-arrow boundary presentation for transports \(U=GF\) and \(V=H\):
\[
R_\alpha
=
M_{GF}\amalg_{A\amalg C}M_H.
\tag{13}
\]
The local endpoint copies are distinguished until this gluing is performed.

Define
\[
j:R_\alpha\longrightarrow P_{\mathrm{gr}}
\tag{14}
\]
by the identity on \(A,C\), by \(J_{fg}\) on the first cylinder, and by the existing \(h\)-cylinder on the second. On generators:
\[
\begin{array}{lll}
u_x\mapsto\tau_x,
&
\eta^u_b\mapsto\eta^{fg}_b,
&
\kappa^u_\rho\mapsto\kappa^{fg}_\rho,
\\[1mm]
v_x\mapsto h_x,
&
\eta^v_b\mapsto\eta^h_b,
&
\kappa^v_\rho\mapsto\kappa^h_\rho.
\end{array}
\tag{15}
\]

Equation (7) defines the map in every dimension. Equations (10)–(12) give its relevant generating-cell images for Question 1.

## 2. The generators over \(\alpha\)

Push out the already established walking-2-cell relative presentation along (14). The resulting new generators are the following.

### 2.1 Dimensions 2 and 3

For each vertex \(x\) of \(A\), add
\[
\lambda_x:\tau_x;a_x\Rightarrow h_x.
\tag{16}
\]

For \(p:x\to y\), put
\[
P_p=(\lambda_x*Hp)\cdot\eta^h_p,
\qquad
Q_p=(\eta^{fg}_p*a_y)\cdot(p*\lambda_y).
\tag{17}
\]
The strict naturality equation
\[
GFp;a_y=a_x;Hp
\tag{18}
\]
makes these parallel.

For each generating arrow \(b\) of \(A\), add
\[
\Xi_b:P_b\Rrightarrow Q_b.
\tag{19}
\]

Extend \(\Xi\) to paths by \(\Xi_{1_x}=1_{\lambda_x}\) and
\[
\begin{aligned}
\Xi_{p;r}
={}&
\operatorname{wh}(1,\Xi_p*Hr,\ p*\eta^h_r)\\
&\odot
\operatorname{wh}(\eta^{fg}_p*a_y*Hr,\ p*\Xi_r,\ 1).
\end{aligned}
\tag{20}
\]
The intermediate 2-cell is
\[
(Q_p*Hr)\cdot(p*\eta^h_r)
=
(\eta^{fg}_p*a_y*Hr)\cdot(p*P_r).
\]

### 2.2 Dimension 4

For a generating \(\rho:p\Rightarrow q\), define
\[
\begin{aligned}
A_\rho
={}&
\operatorname{wh}(1,\Xi_p,\rho*h_y)\\
&\odot
\operatorname{wh}(1,\kappa^{fg}_\rho*a_y,\ q*\lambda_y),
\\[1ex]
B_\rho
={}&
\operatorname{wh}(\lambda_x*Hp,\kappa^h_\rho,1)\\
&\odot
\operatorname{wh}(\tau_x*a_x*H\rho,\Xi_q,1).
\end{aligned}
\tag{21}
\]

Both are 3-cells from
\[
P_p\cdot(\rho*h_y)
\quad\text{to}\quad
(\tau_x*a_x*H\rho)\cdot Q_q.
\tag{22}
\]
Their intermediate identifications use
\[
(p*\lambda_y)\cdot(\rho*h_y)
=
(\rho*\tau_y*a_y)\cdot(q*\lambda_y),
\tag{23}
\]
\[
(\lambda_x*Hp)\cdot(h_x*H\rho)
=
(\tau_x*a_x*H\rho)\cdot(\lambda_x*Hq),
\tag{24}
\]
and
\[
GF\rho*a_y=a_x*H\rho.
\tag{25}
\]

Add
\[
\Omega_\rho:A_\rho\Longrightarrow B_\rho.
\tag{26}
\]

The occurrence of \(\kappa^{fg}_\rho\) in (21) means the explicit pasting (11). Thus all these attaching maps are defined before localization.

Mark the transports, the \(\lambda_x\), and the structural generators. Localize at
\[
S=
\{\eta^f,\eta^g,\eta^h,\kappa^f,\kappa^g,\kappa^h,\Xi,\Omega\}.
\tag{27}
\]
The fibre generators retain their flat marking.

For Cat-valued weights, omit the \(\kappa\) and \(\Omega\) families. The attachment then adds one 2-generator per source-fibre vertex and one 3-generator per source-fibre generating arrow. For 2-category-valued weights it additionally adds one 4-generator per source-fibre generating 2-cell.

This is a precise implementation of the double-cylinder approach: the boundary cylinder is first substituted along \(I\to[2]\), and the walking-2-cell double cylinder is then attached through that substitution.

## 3. The general theorem for 2-dimensional bases

The preceding construction extends to every finite path and therefore to every base 2-generator.

### Theorem

Let \(\Gamma\) be a finite 2-computad such that the canonical map
\[
\operatorname{Free}(\Gamma)\longrightarrow F_2(\Gamma)
\]
is an equivalence.

For each vertex \(b\), let
\[
A_b=F_m(\Pi_b),
\qquad
\operatorname{Free}(\Pi_b)\simeq A_b,
\]
where \(\Pi_b\) is finite and has dimension at most \(m\).

Then every weight \(T:F_2(\Gamma)\to\omega\) with these fibre values has a finite presentation
\[
\operatorname{Free}(\Psi_T)[S^{-1}]
\simeq
\int_{F_2(\Gamma)}T
\tag{28}
\]
over \(F_2(\Gamma)^\sharp\), with the following generators:

| Index | Dimension | Marking and localization |
|---|---:|---|
| \(g\in(\Pi_b)_j\) | \(j\) | Original fibre marking |
| \(e:b\to c,\ g\in(\Pi_b)_j\) | \(j+1\) | Marked; inverted exactly when \(j>0\) |
| \(\sigma:p\Rightarrow q,\ p,q:b\to c,\ g\in(\Pi_b)_j\) | \(j+2\) | Marked; inverted exactly when \(j>0\) |

In particular,
\[
\dim\Psi_T\le m+2,
\tag{29}
\]
and
\[
\#(\Psi_T)_d
=
\sum_{b\in\Gamma_0}\#(\Pi_b)_d
+
\sum_{e\in\Gamma_1}\#(\Pi_{s(e)})_{d-1}
+
\sum_{\sigma\in\Gamma_2}\#(\Pi_{s_0(\sigma)})_{d-2},
\tag{30}
\]
with negative subscripts interpreted as zero.

### 3.1 Strict finite action data

Write the edge actions as \(F_e\), and the action of
\(\sigma:p\Rightarrow q\) as
\[
a_\sigma:F_p\Rightarrow F_q,
\]
equivalently a strict evaluation map
\[
\widehat a_\sigma:A_b\times I\to A_c.
\tag{31}
\]

These are the finite action data supplied by \(T\) after fixing the strict fibre identifications. Free finite-dimensional strict categories are gaunt: descending from the top dimension, invertibility would require a strict inverse, which additive generator counts exclude. Consequently the invertible functoriality comparisons into these fibres are identities. Loubaton’s identification
\[
\operatorname{hom}_\omega(A,C)\simeq\operatorname{Hom}(A,C)
\]
then gives the stated Cartesian evaluation description. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 3.2 Substitution along every path

For
\[
p=e_1;\cdots;e_r:b_0\to b_r,
\]
define
\[
F^{(0)}=\mathrm{id},
\qquad
F^{(k)}=F_{e_k}\cdots F_{e_1}.
\]
Use
\[
\delta_r:I\to[r],\qquad 0\mapsto0,\quad1\mapsto r.
\]
The map
\[
A_{b_0}\otimes I
\longrightarrow A_{b_0}\otimes[r]
\longrightarrow P_{\mathrm{gr}}
\tag{32}
\]
uses \(F^{(k-1)}\otimes I\) followed by the \(e_k\)-cylinder on interval \(k\). Adjacent endpoint maps agree because both equal \(F^{(k)}\).

It extends to
\[
J_p:M_{F_p}\longrightarrow P_{\mathrm{gr}}.
\tag{33}
\]
On a vertex \(x\), its transport is
\[
(e_1)_x;
(e_2)_{F^{(1)}x};
\cdots;
(e_r)_{F^{(r-1)}x}.
\tag{34}
\]

For an identity path, take \(r=0\) and \(I\to[0]\). Thus identity boundaries cause no difficulty in this substitution construction. Positivity is only one way to establish the separate hypothesis that the base is homotopical.

The map \(J_p\) preserves the markings. Each structural cell maps to a pasting of structural cells and their whiskerings; if a functor sends its fibre label to an identity, the corresponding cell becomes an identity. Hence \(J_p\) also sends the designated localization cells to cells inverted by the graph localization.

### 3.3 The walking-2-cell block in arbitrary fibre dimension

For \(\sigma:p\Rightarrow q\), put \(A=A_b,C=A_c,U=F_p,V=F_q\), and form
\[
H=A\otimes I_{\mathrm{in}},
\]
\[
W_\sigma=
A\amalg_{H\otimes\{0\}}
(H\otimes I_{\mathrm{out}})
\amalg_{H\otimes\{1\}}C,
\tag{35}
\]
using projection \(H\to A\) and
\[
H\to A\times I_{\mathrm{in}}\xrightarrow{\widehat a_\sigma}C.
\]

Its parallel-arrow boundary is
\[
R_\sigma=M_U\amalg_{A\amalg C}M_V.
\tag{36}
\]
The extension \(R_\sigma\to W_\sigma\) adds exactly
\[
g\otimes i_{\mathrm{in}}\otimes i_{\mathrm{out}}
\]
for each generating \(g\) of \(A\), in dimension \(\dim g+2\).

This relative cellular assertion holds for a specified homotopical fibre presentation: filter it by its generating-cell attachments and apply the globe–interval cell-pair calculation at each step. The latter follows from the acyclic-atom pasting and Gray-product results in Chanavat, Corollary 3.27 and Theorem 3.29. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

The localization proof from round 2 is independent of the bound \(m=2\). Its ingredients are the tensor-localization lemma, valid in every dimension, and the marked interval comparisons. It gives
\[
W_\sigma[S_\sigma^{-1}]
\simeq
(A\times(1^{\mathrm{co}}\!\star I))
\amalg_{A\times I}C
\simeq
\int_{D_2}T|_\sigma.
\tag{37}
\]

### 3.4 Attach all base 2-cells simultaneously

Use \(J_p,J_q\) to define
\[
R_\sigma\longrightarrow P_{\mathrm{gr}}.
\]
Then form
\[
P=
P_{\mathrm{gr}}
\amalg_{\coprod_{\sigma\in\Gamma_2}R_\sigma}
\coprod_{\sigma\in\Gamma_2}W_\sigma.
\tag{38}
\]

Every boundary map in (38) lands in the unlocalized graph presentation. No previously attached base 2-cell is required.

Pushing out the finite relative cell filtrations shows that
\[
P=\operatorname{Free}(\Psi_T)
\]
with precisely the generators in the theorem.

Localization gives
\[
P[S^{-1}]
\simeq
\left(\int_{\Gamma^{(1)}}T\right)
\amalg_{\coprod_\sigma\int_{\partial D_2}T|_\sigma}
\coprod_\sigma\left(\int_{D_2}T|_\sigma\right).
\tag{39}
\]
This interchange of localization and pushout follows directly by mapping into any \(Z\): both sides specify the same compatible maps sending the designated cells to equivalences.

The localized \(J_p\) is the required restriction map along the path \(p\): it uses the composite of the chosen marked edge lifts and has transport functor \(F_p\).

The base hypothesis identifies
\[
F_2(\Gamma)\simeq
\Gamma^{(1)}
\amalg_{\coprod_\sigma\partial D_2}
\coprod_\sigma D_2.
\tag{40}
\]
Loubaton’s Corollary 3.2.3.16 identifies a left cartesian fibration over this colimit with the colimit of its pullbacks. Applying it to (40) proves (28). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For positive \(\Gamma\), the base hypothesis follows from Chanavat’s Corollary 3.39. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

### 3.5 The finite check

Given certificates for the homotopical base and fibre presentations, the remaining check is finite:

1. Check the images of fibre generators under each \(F_e\), including their boundaries.
2. Check the vertex arrows of each \(a_\sigma\) and its strict naturality equations on the fibre generators.
3. Construct the path substitutions (32) from the finite boundary words.
4. Construct the relative blocks (35), substitute their boundaries through those path maps, and check the projection and marking.
5. Use the localization set specified in the theorem.

Finite derivations of the strict equalities can be supplied as part of the certificate. No decision procedure for arbitrary higher-dimensional equality is asserted.

This proves Question 2 for **all homotopical bases of dimension at most \(2\)** and arbitrary finite fibre dimension.

## 4. A sufficient 2-dimensional homotopicality criterion

Here is a class beyond positive 2-computads.

### Operadic criterion

Let \(\Gamma\) have one vertex, and let \(C=\Gamma_1\) be its set of generating arrows. Suppose every generating 2-cell has the form
\[
\rho:c_1\cdots c_k\Rightarrow c,
\qquad k\ge0,\quad c,c_i\in C.
\tag{41}
\]
Thus its target is a **single generating arrow**; its source may be empty.

Then
\[
\boxed{\operatorname{Free}(\Gamma)\simeq F_2(\Gamma).}
\tag{42}
\]
The same conclusion holds when every generating 2-cell instead has a single generating arrow as its source, by reversing 2-cells.

### Proof

Let \(P\) be the free planar \(C\)-coloured operad whose generating operations are the \(\rho\) with the indicated input lists and output colours.

First, \(P\) is free in the coherent sense. Symmetrize it while retaining its map to the associative operad, which records the input orders. Starting with the discrete operad on \(C\), attach the generating corollas along their edge boundaries. Cisinski–Moerdijk, Corollary 3.8, makes the comparison from this dendroidal cell attachment to the nerve of the ordinary operadic attachment inner anodyne. Their construction permits arity zero; the initial discrete coloured operad is \(\Sigma\)-cofibrant. [arxiv.org](https://arxiv.org/pdf/1109.1004?utm_source=chatgpt.com)

This supplies the full \(\infty\)-operadic universal property. The comparison with Lurie’s operads, including constants, is provided by Hinich–Moerdijk, Theorem 3.1.4 and Proposition 3.4.4. [arxiv.org](https://arxiv.org/pdf/2206.14033?utm_source=chatgpt.com)

Now form the relative monoidal envelope
\[
\mathcal F(P)=\operatorname{Env}_{E_1}(P).
\]
Its underlying ordinary category has words in \(C\) as objects, with
\[
\mathcal F(P)(w,d_1\cdots d_\ell)
=
\coprod_{w=w_1\cdots w_\ell}
\prod_{j=1}^{\ell}P(w_j;d_j).
\tag{43}
\]
The ordered factorization permits empty \(w_j\). Composition grafts trees, and tensor product concatenates the forests.

These are exactly the 2-cells of \(F_2(\Gamma)\): a composite of generators gives a planar forest, and interchange identifies the orders of composing independent vertices. Conversely, composing a forest in any order compatible with its edges gives the same strict 2-cell. Hence
\[
F_2(\Gamma)\cong B\mathcal F(P).
\tag{44}
\]

The envelope adjunction identifies strong monoidal functors \(\mathcal F(P)\to\mathcal M\) with \(P\)-algebras in an arbitrary monoidal \(\infty\)-category \(\mathcal M\). By coherent freeness of \(P\), this means precisely the data
\[
X_c\in\mathcal M,\qquad
X_{c_1}\otimes\cdots\otimes X_{c_k}\longrightarrow X_c
\]
for the generators \(\rho\), with no further conditions. The envelope adjunction is Blans–Linskens, Lemma 2.2 and Remark 2.3. [arxiv.org](https://arxiv.org/html/2605.03150v1?utm_source=chatgpt.com)

Apply this to \(\mathcal M=\operatorname{End}_{D}(d)\), for an arbitrary \((\infty,2)\)-category \(D\) and \(d\in D\). The homotopy fibre at \(d\) of
\[
\operatorname{Map}(B\mathcal F(P),D)\longrightarrow D_0
\]
is exactly the space of assignments
\[
c\mapsto t_c:d\to d,\qquad
\rho\mapsto
\bigl(t_{c_1};\cdots;t_{c_k}\Rightarrow t_c\bigr).
\]
This is the defining mapping-space universal property of the coherent free category on \(\Gamma\). It proves the canonical equivalence (42). The finite-dimensional inclusion into Loubaton’s \((\infty,\omega)\)-theory preserves these cellular colimits, as in the suspension argument of round 2. ∎

### A finite sufficient test covering the requested examples

Accept a finite 2-computad if any of the following holds:

- it is positive;
- it has one vertex and satisfies (41);
- it has one vertex and satisfies the 2-opposite of (41).

This covers every positive 2-computad and \(Q\). It excludes
\[
(*;\sigma:1\Rightarrow1).
\]

The operadic clause also covers, for example,
\[
(*;\ t;\ \eta:1\Rightarrow t,\ \mu:tt\Rightarrow t).
\tag{45}
\]
There are no associativity or unit equations on \(\mu,\eta\): this is the free operad on a nullary and a binary operation.

## 5. An obstruction to a weaker criterion

The condition

> each generating 2-cell has at least one nonidentity boundary

is insufficient.

Consider
\[
R=(*;\ t;\ \eta:1\Rightarrow t,\ \epsilon:t\Rightarrow1).
\tag{46}
\]
Neither generator has two identity boundaries, but \(B^2\mathbb N\) is a strict retract of \(F_2(R)\).

Define
\[
i:B^2\mathbb N\to F_2(R),
\qquad
i(\sigma)=\eta\cdot\epsilon,
\tag{47}
\]
and
\[
r:F_2(R)\to B^2\mathbb N,
\qquad
r(t)=1,\quad r(\eta)=\sigma,\quad r(\epsilon)=1.
\tag{48}
\]
The free strict universal properties define both functors, and
\[
ri=\mathrm{id}.
\tag{49}
\]

Consequently \(K(\mathbb Z,2)\) is a retract of the groupoidification of \(F_2(R)\). Applying the obstruction in your item 4, its homology is nonzero in unbounded degrees, so
\[
\boxed{
F_2(R)\text{ has no finite presentation }
\operatorname{Free}(\Psi)[S^{-1}]
\text{ of the prescribed kind.}
}
\tag{50}
\]
The identification of the groupoidification of \(B^2\mathbb N\) is Ara’s Theorem 4.9 and Example 4.10. [arxiv.org](https://arxiv.org/pdf/1808.02650?utm_source=chatgpt.com)

Thus the obstruction may be produced by a composite \(\eta\cdot\epsilon:1\Rightarrow1\), even when no generator has that boundary.

## 6. A 3-dimensional attachment rule

The following rule combines the 2-dimensional criteria with the whiskered example.

Let \(D\) be a strict 3-category with a finite homotopical computad presentation. Choose distinct vertices \(s,t\) satisfying
\[
D(x,s)=\varnothing\quad(x\ne s),\qquad
D(t,x)=\varnothing\quad(x\ne t),
\tag{51}
\]
and
\[
D(s,s)=D(t,t)=\mathbf1.
\tag{52}
\]
Put \(K=D(s,t)\).

Suppose \(i:K\hookrightarrow K'\) is a computadic inclusion obtained by finitely many 2-cell attachments, and that these attachments are homotopy attachments in the coherent theory. The latter condition follows, for example, from compatible canonical homotopical presentations of \(K,K'\) certified by §4.

Define \(D'\) by replacing \(D(s,t)\) with \(K'\), retaining the other homs. Old composites landing in \(D(s,t)\) are followed by \(i\). A composite using a new cell of \(K'\) has only identity neighbours, by (51)–(52), so this defines a strict 3-category.

Then the corresponding finite 3-cell attachment to \(D\) is homotopical.

### Proof

The full subcategories on \(\{s,t\}\) are \(\Sigma K\) and \(\Sigma K'\).

Write a Θ-shape as
\[
[m](\theta_1,\ldots,\theta_m).
\]
A functor from it to \(D'\) that does not factor through \(D\) has an adjacent vertex pair \((s,t)\) whose hom map does not factor through \(K\).

Every preceding vertex must be \(s\), since no nonidentity 1-cell enters \(s\). Every following vertex must be \(t\), since none leaves \(t\). The functor therefore factors through \(\Sigma K'\).

Since \(i\) is an inclusion, this proves the exact nerve union
\[
N_\Theta D'
=
N_\Theta D
\amalg_{N_\Theta\Sigma K}
N_\Theta\Sigma K'.
\tag{53}
\]
It is a pushout along monomorphisms of set-valued presheaves, hence objectwise a homotopy pushout. Localization gives
\[
D'\simeq D\amalg_{\Sigma K}\Sigma K'.
\tag{54}
\]
Suspending the given relative 2-cell attachments and applying this pushout proves the claim. ∎

Starting with regular 3-polygraphs and applying this rule gives a sufficient class covering all three requested examples:

- Regular 3-polygraphs are initial cases by Chanavat’s Corollary 3.38. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)
- For the whiskered generator \(\zeta:\alpha\triangleright r\Rrightarrow\beta\triangleright r\), take \(s=x,t=z\). The hom \(K\) is the free category on the two parallel arrows \(\alpha\triangleright r,\beta\triangleright r\); adjoining \(\zeta\) is a positive 2-dimensional hom attachment.
- For \(\Sigma Q\), take \(D=\Sigma K\), where \(K\) is the free category on the loop \(t\), and \(K'=F_2(Q)\). The operadic criterion supplies the relative homotopical attachment. The same argument applies to suspensions of the entire operadic class in §4.

The general FT statement for base dimension \(n\ge3\), and the assertion that every positive 3-computad is homotopical, remain unproved here.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level.**
- **Question 1 is solved**, by substituting along δ₂ : I → [2].
- **Question 2 is solved for every homotopical base of dimension ≤ 2**, with fibres of any finite dimension m, generator count (30) and dimension ≤ m + 2. This closes the attaching-map gap of item 11 for 2-dimensional bases.
- **Question 3 is answered in part.** There is a one-vertex operadic criterion, an obstruction R = (∗; t; η : 1 ⇒ t, ε : t ⇒ 1), and a 3-dimensional attachment rule.
- **Still open:** FT_n for bases of dimension n ≥ 3, and whether every positive 3-computad is homotopical.

Checked step by step:

1. **§1.2, the path cylinder.** A ⊗ [2] ≃ (A ⊗ I) ∐_A (A ⊗ I), and precomposing with A ⊗ δ₂ gives a map A ⊗ I → P_gr *before* localisation.

   I typed (10):
   - η^f_p : f_x;Fp ⇒ p;f_y and η^g_{Fp} : g_{Fx};GFp ⇒ Fp;g_{Fy};
   - so (f_x ∗ η^g_{Fp}) · (η^f_p ∗ g_{Fy}) goes τ_x;GFp ⇒ f_x;Fp;g_{Fy} ⇒ p;τ_y, with no inverses.

   (11) is the corresponding 3-dimensional pasting, κ^f first and then κ^g_{Fρ}, with κ^g_{Fρ} the image of a mixed cell under Fρ ⊗ I. It is not a new generator.
2. **§2, the generators over α.**
   - P_p = (λ_x ∗ Hp) · η^h_p and Q_p = (η^{fg}_p ∗ a_y) · (p ∗ λ_y) are both 2-cells ending at p;h_y.
   - Their sources τ_x;a_x;Hp and τ_x;GFp;a_y agree by the strict naturality (18). Strictness holds because free finite-dimensional strict categories are gaunt, so invertible comparisons into them are identities.
   - (20)–(26) follow the walking-2-cell pattern of round 2, with κ^{fg} given by (11).
3. **§3, the general 2-dimensional theorem.**
   - J_p along δ_r : I → [r] handles every path, including identity paths (r = 0). Positivity plays no role beyond giving the homotopical-base hypothesis.
   - All base 2-cells are attached at once in (38), with every boundary landing in the unlocalised P_gr.
   - Localisation commutes with the pushout by the mapping property, and Loubaton Cor. 3.2.3.16 assembles the pullbacks over (40).
   - The count (30) is one generator per (base cell, source-fibre generator).

   One step rests on references I did not re-derive: that the round-2 localisation (37) and the mixed-localisation lemma hold for fibre dimension m > 2, and the relative cellularity of R_σ → W_σ (Chanavat Cor. 3.27, Thm 3.29).
4. **§4, the operadic criterion.**
   - When every 2-generator has a single generating arrow as target, the 2-cells of F₂(Γ) are planar forests modulo interchange, so F₂(Γ) ≅ B Env_{E1}(P) for the free planar coloured operad P.
   - Coherent freeness of P (Cisinski–Moerdijk Cor. 3.8, arity 0 allowed) plus the envelope adjunction (Blans–Linskens) gives the mapping-space universal property of Free(Γ).
   - The criterion covers Q and (∗; t; η : 1 ⇒ t, μ : tt ⇒ t), and excludes (∗; σ : 1 ⇒ 1).
5. **§5, the obstruction R.**
   - Set i(σ) = η · ε : 1 ⇒ 1, and let r send t ↦ 1, η ↦ σ, ε ↦ 1. Both are well typed and ri = id. So K(ℤ,2) is a retract of the groupoidification of F₂(R), whose homology is then unbounded.
   - A finite Free(Ψ)[S⁻¹] groupoidifies to a finite CW complex, so F₂(R) has no finite presentation. In particular Free(R) ≄ F₂(R).
   - So "no generator has both boundaries identities" is not enough. A *composite* 1 ⇒ 1 already obstructs.
6. **§6, the 3-dimensional attachment rule.**
   - The condition is that no nonidentity 1-cell enters s or leaves t, and D(s,s) = D(t,t) = 1. Then a Θ-cell of D′ not in D is forced to lie in ΣK′, so N_Θ D′ = N_Θ D ∐_{N_Θ ΣK} N_Θ ΣK′. That is a pushout of monomorphisms, hence a homotopy pushout.
   - Both examples check:
     - ζ, with K the free category on the parallel pair α▷r, β▷r, and ζ a positive 2-cell attachment in that hom;
     - ΣQ, with K = Bℕ on the loop and K′ = F₂(Q).

**Remark.** Every homotopical 2-computad now known (positive ones, the operadic class, its opposite) has F₂(Γ) with no nonidentity 2-cell from an identity 1-cell to an identity 1-cell. The non-homotopical ones (σ, R) have one. The follow-up asks whether this characterises homotopical 2-computads.

Follow-up prompt: `outbox/finite-fibration-test-higher-base-r4.md` (round 4, unsent).
