# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n), round 4

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. Rounds 1–3 and their verified answers are in `answered/finite-fibration-test-higher-base-2026-11-18.md`, `answered/finite-fibration-test-higher-base-r2-2026-11-18.md` and `answered/finite-fibration-test-higher-base-r3-2026-11-18.md`; nothing answered there is re-asked. The questions are in §4, smallest first.*

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
11. **The gap in the induction (round 2; closed for 2-dimensional bases by item 12).** Gluing local totals `E_{D_k} ≃ (A × L_k) ∐_{A × D_{k−1}} C`, with L_k = 1^co ⋆ D_{k−1}, gives the right local generator count, one generator of dimension k + j per fibre j-generator. But the attaching maps land in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself. Such lifts need not exist: in Free(s)[s⁻¹] the inverse of a marked arrow s exists, in Free(s) no arrow goes back. For the walking 2-cell the double cylinder supplies the lifts explicitly; for a base generator whose boundary is a composite, nothing yet does.

12. **FT for every homotopical base of dimension ≤ 2 (round 3, proved).**
    - *Paths.* For a base path p = e₁; … ; e_r, the map δ_r : I → [r] (0 ↦ 0, 1 ↦ r) and A ⊗ [r] ≃ (A ⊗ I) ∐_A … ∐_A (A ⊗ I) give a map M_{F_p} → P_gr from the cylinder of F_p into the *unlocalised* graph presentation. It sends the transport to the composite of the edge lifts. Its naturality cells are explicit pastings without inverses, for example η^{fg}_p = (f_x ∗ η^g_{Fp}) · (η^f_p ∗ g_{Fy}).
    - *Theorem.* Let Γ be a finite 2-computad with Free(Γ) ≃ F₂(Γ), and let the fibres be A_b = F_m(Π_b) with Π_b finite and homotopical. Then ∫T is presented by one marked generator of dimension j + 1 (respectively j + 2) for each base edge (respectively base 2-cell) and each source-fibre j-generator, besides the fibre generators. Those with j > 0 are inverted, and the dimension is ≤ m + 2.
    - *Proof.* Attach the walking-2-cell double-cylinder blocks for all base 2-cells at once, along these path maps. Then use Loubaton Cor. 3.2.3.16.
13. **Homotopical 2-computads beyond positivity (round 3, proved).**
    - *Operadic criterion.* If Γ has one vertex and every 2-generator has a single generating arrow as target (any source, possibly empty), then F₂(Γ) ≅ B Env_{E1}(P) for the free planar coloured operad P, and Free(Γ) ≃ F₂(Γ). The same holds with "source" in place of "target". Examples: Q of item 10, and (∗; t; η : 1 ⇒ t, μ : tt ⇒ t).
    - *An obstruction.* For R = (∗; t; η : 1 ⇒ t, ε : t ⇒ 1), the composite η · ε makes B²ℕ a retract of F₂(R). So F₂(R) has no finite presentation, and R is not homotopical.
14. **A 3-dimensional attachment rule (round 3, proved).** Let D be a strict 3-category with a finite homotopical presentation and with vertices s, t such that no nonidentity 1-cell enters s or leaves t, and D(s,s) = D(t,t) = 1. Then replacing K = D(s,t) by K′, obtained from K by homotopical 2-cell attachments, is a homotopical 3-cell attachment, via an exact union of Θ-nerves. This covers item 8's ζ, the suspension of Q, and suspensions of the operadic class.

## 3. Questions

1. **FT₃: a base 3-generator with composite boundary, the smallest case.** Take the base Γ with vertices 0, 1; arrows u, w, v : 0 → 1; 2-cells β : u ⇒ w, γ : w ⇒ v, α : u ⇒ v; and the 3-cell Ω : α ⇛ β · γ. This is a positive, regular 3-computad.
   - Use T valued in free categories on finite graphs.
   - Supply the attaching maps of the generators over Ω in the unlocalised presentation, by substituting along a 2-dimensional analogue of δ_r: a map from the walking 2-cell to the walking pair of composable 2-cells, tensored with the fibre.
   - Prove that the relative Gray-tensor generators present ∫T.
2. **FT_n over homotopical bases of any dimension.** Generalise item 12 to a finite base computad Γ of dimension n with Free(Γ) ≃ F_n(Γ). The natural route is to substitute along maps from the globe D_k into the pasting diagram of each generator's boundary. State the finite check and the dimension bound n + m.
3. **A characterisation of homotopical 2-computads.** Every homotopical example known has no nonidentity 2-cell in F₂(Γ) from an identity 1-cell to an identity 1-cell, and the two non-homotopical examples have one. Is a finite 2-computad homotopical **if and only if** F₂(Γ) has no such 2-cell? Is that property decidable from Γ? If not, give a counterexample in either direction, for example with several vertices or with 2-generators whose source and target are both composite.
4. **Positive 3-computads.** Call a 3-computad positive when every 3-generator has non-identity 2-cells as both boundaries. Is every positive 3-computad homotopical? Or give a positive counterexample. Does item 14 extend to attachments in a hom D(s,t) when s has incoming 1-cells?

## 4. What would count as an answer

Any of the following:
- a proof or counterexample for any question;
- a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs;
- a reference to a published characterisation of homotopical polygraphs in low dimension.

# Research Response

**Question 1 has an affirmative answer.** The required attaching map is induced by
\[
\Sigma\delta_2:D_2=\Sigma I\longrightarrow\Sigma[2].
\]
It gives explicit pastings before localization.

There are also three further results:

- For **every homotopical suspension base**, in any finite dimension, the proposed presentation works for free category fibres, with dimension bound \(n+1\).
- The condition in question 3 is **necessary and undecidable**. Its sufficiency is not proved here.
- Question 4’s stated positivity condition has a connected counterexample. If positivity is also required in dimension \(2\), that counterexample does not apply.

## 1. The composite boundary \(\Omega:\alpha\Rrightarrow\beta\cdot\gamma\)

Write
\[
A=T(0),\qquad C=T(1),
\]
\[
U=T(u),\quad W=T(w),\quad V=T(v),
\]
and
\[
b=T(\beta):U\Rightarrow W,\qquad
c=T(\gamma):W\Rightarrow V,\qquad
a=T(\alpha):U\Rightarrow V.
\]
Since \(T(\Omega)\) is an identity,
\[
a=b;c,\qquad a_x=b_x;c_x.
\]

Use chronological composition: \(;\) for \(1\)-cells, \(\cdot\) for \(2\)-cells, and \(\odot\) for \(3\)-cells. Write \(*\) for whiskering. For a \(3\)-cell \(H:p\Rightarrow q\), put
\[
\operatorname{wh}(L,H,R):
L\cdot p\cdot R\Longrightarrow L\cdot q\cdot R.
\]

All tensor constructions below are formed before imposing the specified markings and localizations.

### 1.1 The existing presentation in dimensions at most \(3\)

Use the orientation from known item 9. For each generating arrow \(f:x\to y\) of \(A\), the edge comparisons are
\[
\eta^e_f:e_x;T(e)f\Longrightarrow f;e_y,
\qquad e\in\{u,w,v\}.
\]

The three families of marked lifts are
\[
\lambda_{\beta,x}:u_x;b_x\Longrightarrow w_x,
\]
\[
\lambda_{\gamma,x}:w_x;c_x\Longrightarrow v_x,
\]
\[
\lambda_{\alpha,x}:u_x;a_x\Longrightarrow v_x.
\]

For \(\sigma:e\Rightarrow e'\), let \(d=T(\sigma)\) and define
\[
\begin{aligned}
P_{\sigma,f}
&=(\lambda_{\sigma,x}*T(e')f)\cdot\eta^{e'}_f,\\
Q_{\sigma,f}
&=(\eta^e_f*d_y)\cdot(f*\lambda_{\sigma,y}).
\end{aligned}
\]
Naturality,
\[
d_x;T(e')f=T(e)f;d_y,
\]
makes these parallel \(2\)-cells. The existing structural generator is
\[
\Xi_{\sigma,f}:P_{\sigma,f}\Longrightarrow Q_{\sigma,f}.
\]

Let \(P_{\leq2}\) denote this unlocalised presentation.

### 1.2 The composite lift and its naturality cell

Put \(\delta=\beta\cdot\gamma\). Define the following **composites of existing cells**:
\[
\boxed{
\lambda_{\delta,x}
=(\lambda_{\beta,x}*c_x)\cdot\lambda_{\gamma,x}.
}
\tag{1}
\]
Its boundary is
\[
u_x;a_x=u_x;b_x;c_x\Longrightarrow v_x.
\]

For a generating arrow \(f:x\to y\), define
\[
\boxed{
\begin{aligned}
\Xi_{\delta,f}
={}&
\operatorname{wh}
\bigl(\lambda_{\beta,x}*c_x*Vf,\ \Xi_{\gamma,f},\ 1\bigr)\\
&\odot
\operatorname{wh}
\bigl(1,\ \Xi_{\beta,f}*c_y,\ f*\lambda_{\gamma,y}\bigr).
\end{aligned}}
\tag{2}
\]

Thus the first step uses \(\Xi_{\gamma,f}\), and the second uses \(\Xi_{\beta,f}\).

Here is the boundary verification. Expanding (1),
\[
P_{\delta,f}
=(\lambda_{\beta,x}*c_x*Vf)\cdot P_{\gamma,f}.
\]
The first step of (2) produces
\[
(\lambda_{\beta,x}*c_x*Vf)\cdot Q_{\gamma,f}.
\]
Using the literal equality of paths in \(C\)
\[
c_x;Vf=Wf;c_y,
\]
this is
\[
(P_{\beta,f}*c_y)\cdot(f*\lambda_{\gamma,y}).
\]
The second step produces
\[
\begin{aligned}
(Q_{\beta,f}*c_y)\cdot(f*\lambda_{\gamma,y})
&=(\eta^u_f*b_y*c_y)
  \cdot(f*\lambda_{\beta,y}*c_y)
  \cdot(f*\lambda_{\gamma,y})\\
&=(\eta^u_f*a_y)\cdot(f*\lambda_{\delta,y})\\
&=Q_{\delta,f}.
\end{aligned}
\]
Consequently,
\[
\Xi_{\delta,f}:P_{\delta,f}\Longrightarrow Q_{\delta,f}
\]
is defined in \(P_{\leq2}\), without inverses.

### 1.3 The actual map of double cylinders

The formulas above arise from a functor between the unlocalised constructions.

Let
\[
d=\delta_2:I\longrightarrow[2],
\qquad d(0)=0,\quad d(1)=2.
\]
Its suspension
\[
\Sigma d:\Sigma I\longrightarrow\Sigma[2]
\]
sends the walking \(2\)-cell to the composite of the two generating \(2\)-cells.

For \(D=I\) or \([2]\), set
\[
H_D=A\otimes D.
\]
There are maps
\[
r_D:H_D\longrightarrow A
\]
and
\[
\epsilon_D:H_D\longrightarrow A\times D\longrightarrow C.
\]
For \(I\), the evaluation uses \(a:U\Rightarrow V\). For \([2]\), it uses
\[
U\xRightarrow{b}W\xRightarrow{c}V.
\]
The equality \(a=b;c\) gives
\[
r_I=r_{[2]}(A\otimes d),
\qquad
\epsilon_I=\epsilon_{[2]}(A\otimes d).
\tag{3}
\]

Form the raw double-cylinder pushouts
\[
\mathcal P_D
=
A\amalg_{H_D\otimes\{0\}}
(H_D\otimes I_{\mathrm{out}})
\amalg_{H_D\otimes\{1\}}C.
\tag{4}
\]
Equation (3) induces
\[
\boxed{\Phi_d:\mathcal P_I\longrightarrow\mathcal P_{[2]}.}
\tag{5}
\]

The relative generators of \(\mathcal P_{[2]}\) are precisely the existing \(u,w,v\) transports, their \(\eta\)-cells, the \(\beta,\gamma\) lifts, and their \(\Xi\)-cells. On the two relevant families, (5) is
\[
\lambda_{a,x}\longmapsto\lambda_{\delta,x},
\qquad
\Xi_{a,f}\longmapsto\Xi_{\delta,f}.
\]
It fixes the \(u,v\) transports and their comparisons.

Equivalently, this is the functoriality of
\[
D\longmapsto1^{\mathrm{co}}\star D
\]
under \(d\), followed by tensoring and evaluation. Loubaton defines this co-cone by collapsing \(D\otimes\{0\}\) in \(D\otimes I\), in Construction 2.3.1.21. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Because (5) is an actual functor before localization, it supplies the compatibilities for composite fibre paths as well.

### 1.4 The generators over \(\Omega\)

Take the raw boundary of the established walking-\(3\)-cell construction. Map its first \(2\)-face to the \(\alpha\)-construction and its second \(2\)-face by
\[
\mathcal P_I\xrightarrow{\Phi_d}\mathcal P_{[2]}
\longrightarrow P_{\leq2}.
\]
These maps agree on the raw \(u,v\) edge presentation. This defines the required attaching map before localization.

For each vertex \(x\) of \(A\), adjoin the marked \(3\)-generator
\[
\boxed{
\omega_x:\lambda_{\alpha,x}\Longrightarrow\lambda_{\delta,x}.
}
\tag{6}
\]

For each generating arrow \(f:x\to y\), define
\[
\begin{aligned}
P^\omega_f
&=\operatorname{wh}(1,\omega_x*Vf,\eta^v_f):
P_{\alpha,f}\Longrightarrow P_{\delta,f},\\
Q^\omega_f
&=\operatorname{wh}(\eta^u_f*a_y,f*\omega_y,1):
Q_{\alpha,f}\Longrightarrow Q_{\delta,f}.
\end{aligned}
\]
Adjoin the marked \(4\)-generator
\[
\boxed{
K_f:
P^\omega_f\odot\Xi_{\delta,f}
\Longrightarrow
\Xi_{\alpha,f}\odot Q^\omega_f.
}
\tag{7}
\]
Both sides are \(3\)-cells from \(P_{\alpha,f}\) to \(Q_{\delta,f}\). In (7), \(\Xi_{\delta,f}\) means the explicit pasting (2).

The projection sends
\[
\omega_x\longmapsto\Omega,
\qquad
K_f\longmapsto1_\Omega.
\]
Localize at
\[
\boxed{
S=
\{\eta^u_f,\eta^w_f,\eta^v_f,\,
  \Xi_{\alpha,f},\Xi_{\beta,f},\Xi_{\gamma,f},\,
  K_f\}.
}
\tag{8}
\]
The transports, \(\lambda\)-cells and \(\omega\)-cells remain marked without being inverted.

There are exactly \(|A_0|\) new \(3\)-generators and \(|A_1|\) new \(4\)-generators. Neither \(\lambda_\delta\) nor \(\Xi_\delta\) is an additional generator.

### 1.5 Identification with the Grothendieck construction

Let \(R_\Omega\to W_\Omega\) be the raw boundary inclusion for the walking-\(3\)-cell construction from known item 6. The presentation just constructed is
\[
P=P_{\leq2}\amalg_{R_\Omega}W_\Omega.
\tag{9}
\]

The base attachment
\[
B=B_{\leq2}\amalg_{\partial D_3}D_3
\tag{10}
\]
is a homotopy pushout: this is a regular \(3\)-polygraph, so Chanavat’s Corollary 3.38 applies. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

After localization, the three terms on the right of (9) are the Grothendieck totals over the three terms on the right of (10), by known items 6 and 12. Their attaching maps agree with the restriction maps of \(T\), by the raw construction (5).

Localization commutes with (9) by its mapping-out universal property. The required compatibility holds because the image of a structural \(\Xi\)-generator under (5) is the composite (2) of structural cells already being inverted.

Loubaton’s Corollary 3.2.3.16 identifies the total over a colimit base with the colimit of its pullbacks. Applying it to (10) gives
\[
\boxed{
\operatorname{Free}(\Psi_T)[S^{-1}]
\simeq
\int_B T
}
\]
as marked categories over \(B^\sharp\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For this case, the finite certificate consists of:

1. The finite functor data \(U,W,V\), naturality equalities for \(a,b,c\) on generating arrows, and \(a_x=b_x;c_x\) on vertices.
2. The prescribed lower generators and the boundaries (1), (2), (6), (7).
3. The marking and localization set (8), with the stated projections.

All equalities in the fibre \(C\) are equalities of finite words in a free category. The theorem above then supplies \((★)\); the presentation has dimension at most \(4=3+1\).

## 2. An all-dimensional result for suspension bases

The same construction gives a class of cases of question 2 beyond the particular composite boundary.

### Theorem

Let \(\Lambda\) be a finite homotopical \(d\)-computad, put
\[
Q=F_d(\Lambda),\qquad B=\Sigma Q,\qquad n=d+1,
\]
and let \(T:B\to\omega\) have fibres \(A,C\) free on finite graphs.

Then \(\int_B T\) has a finite presentation with the fibre generators and, for each \(q\in\Lambda_i\),

- one marked generator of dimension \(i+1\) for each vertex of \(A\);
- one marked generator of dimension \(i+2\) for each generating arrow of \(A\), which is inverted.

Its dimension is at most
\[
\boxed{d+2=n+1.}
\]

### Construction and proof

The weight gives an evaluation
\[
h:Q\times A\longrightarrow C.
\]
Form
\[
K=1^{\mathrm{co}}\star Q
  =1\amalg_{Q\otimes\{0\}}(Q\otimes I).
\tag{11}
\]
The inclusion \(Q\to K\) uses \(Q\otimes\{1\}\).

For each \(q\in\Lambda_i\), the relative cylinder filtration gives one cone generator
\[
\kappa_q,\qquad \dim\kappa_q=i+1.
\]
Besides these, \(K\) has the generators of \(Q\) and the cone vertex. The homotopical presentation of \(Q\) and the globe-cylinder filtration give this finite presentation of \(K\). Loubaton’s Theorem 2.3.3.22 identifies the coherent cone with the strict cone. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For this construction, take the fibre as the second tensor factor and define
\[
P=(K\otimes A)\amalg_{Q\otimes A}C,
\tag{12}
\]
using the raw attaching map
\[
Q\otimes A\longrightarrow Q\times A\xrightarrow{h}C.
\tag{13}
\]

The relative generators surviving (12) are exactly:

| Generator | Dimension | Treatment |
|---|---:|---|
| Fibre generators of \(A,C\) | \(0,1\) | Vertical arrows unmarked |
| \(\kappa_q\otimes x\), \(x\in A_0\) | \(i+1\) | Marked |
| \(\kappa_q\otimes f\), \(f\in A_1\) | \(i+2\) | Marked and inverted |

Set
\[
S=\{\kappa_q\otimes f\}.
\]
The projection sends
\[
\kappa_q\otimes x\longmapsto\Sigma q,
\qquad
\kappa_q\otimes f\longmapsto1_{\Sigma q}.
\tag{14}
\]

The mixed-localization lemma for a category fibre gives
\[
(K\otimes A)[M_K^{-1}]\simeq K\times A,
\qquad
(Q\otimes A)[M_Q^{-1}]\simeq Q\times A.
\]
Here \(M_K,M_Q\) are the positive-dimensional first-factor generator/arrow pairs. This follows from the interval comparison in Loubaton’s Proposition 3.1.3.1 and the decomposition of \(A\) into its generating intervals. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The map (13) already sends \(M_Q\) to identities. Therefore the universal property of localization gives
\[
\begin{aligned}
P[S^{-1}]
&\simeq
(K\times A)\amalg_{Q\times A}C\\
&\simeq
\int_{\Sigma Q}T.
\end{aligned}
\tag{15}
\]
The second equivalence is the suspension-base classification, Loubaton’s Corollary 4.1.2.19. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For the marking, equip \(K\) with
\[
1^{\mathrm{co}}\star Q^\flat.
\]
Its marking is generated by the cone cells \(\kappa_q\). After mixed localization, the specified marking becomes that of
\[
(1^{\mathrm{co}}\star Q^\flat)\times A^\flat,
\]
and then the marked pushout along \(Q^\flat\times A^\flat\to C^\flat\). This is the marking in the suspension classification.

Every attaching map in this proof is supplied by the cone functor and the raw evaluation (13). No lift from a previously localized presentation is required.

This proves the expected bound \(n+m\) for this class with \(m=1\). **It does not prove question 2 for arbitrary bases or arbitrary \(m\).** In that generality, compatible substitution across different fibres and higher compositions still needs a construction or a bounded relative rectification theorem.

## 3. The proposed \(2\)-computad criterion

Call a nonidentity \(2\)-cell
\[
q:1_x\Longrightarrow1_x
\]
a *bubble*. This is Guetta’s terminology, Definitions 6.6.1 and 6.6.3. [arxiv.org](https://arxiv.org/pdf/2104.12662?utm_source=chatgpt.com)

### 3.1 A bubble obstructs every finite coherent presentation

Let \(C=F_2(\Gamma)\), and suppose \(q\) is a bubble.

Define a strict \(2\)-functor
\[
r:C\longrightarrow B^2\mathbb N
\]
by sending every vertex to the unique vertex, every generating arrow to the identity, and every generating \(2\)-cell to \(1\in\mathbb N\).

Then
\[
r(q)=k>0.
\]
Indeed, \(k\) is the total number of generating \(2\)-cells in an expression for \(q\). Associativity, units and interchange preserve this number, and a term with count zero is an identity \(2\)-cell.

The bubble also defines a strict functor
\[
i:B^2\mathbb N\longrightarrow C,\qquad i(1)=q.
\]
This is well-defined because the two compositions of \(2\)-endomorphisms of \(1_x\) coincide and commute by interchange. Thus
\[
ri=[k],
\tag{16}
\]
where \([k]\) is multiplication by \(k\).

Write \(|C|\) for groupoidification. Ara’s Theorem 4.9 and Example 4.10 identify \(|B^2\mathbb N|\) with \(K(\mathbb Z,2)\), naturally through \(B^2\mathbb N\to B^2\mathbb Z\). Hence (16) gives
\[
K(\mathbb Z,2)\xrightarrow{|i|}|C|
\xrightarrow{|r|}K(\mathbb Z,2),
\]
with composite multiplication by \(k\) on \(\pi_2\). [arxiv.org](https://arxiv.org/pdf/1808.02650?utm_source=chatgpt.com)

Now
\[
H^*(K(\mathbb Z,2);\mathbb Q)=\mathbb Q[c],
\qquad |c|=2.
\]
This is the cohomology calculation for \(\mathbb{CP}^{\infty}\), which is a \(K(\mathbb Z,2)\). [pi.math.cornell.edu](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf?utm_source=chatgpt.com)

Consequently, \([k]\) acts by \(k^j\) on \(H_{2j}(-;\mathbb Q)\). Since \(k^j\ne0\), the factorization through \(|C|\) implies
\[
\boxed{
H_{2j}(|C|;\mathbb Q)\ne0
\quad\text{for every }j\ge1.
}
\tag{17}
\]

The groupoidification of a coherent free \(2\)-computad is a \(2\)-dimensional CW complex. Thus \(\Gamma\) cannot be homotopical. More strongly, by the finite-CW obstruction in known item 4, \(C\) cannot have **any** finite coherent presentation of the stipulated form, in any finite dimension and with any additional localizations.

Therefore
\[
\boxed{
\Gamma\text{ homotopical}
\ \Longrightarrow\
F_2(\Gamma)\text{ bubble-free}.
}
\tag{18}
\]

A strict retraction onto \(B^2\mathbb N\) is unnecessary; the positive multiplication map (16) suffices.

### 3.2 Bubble-freeness is undecidable

Reduce from reachability for a finite positive semi-Thue system \(R\): given words \(w,v\), determine whether
\[
w\Longrightarrow_R^*v.
\]
Here every rule has nonempty source and target. This problem is undecidable; Kaminski’s Theorem 7 states the reachability result, and its footnote 5 explicitly records that the system used in Post’s undecidability result is positive. [Springer Nature Link](https://link.springer.com/article/10.1007/s00153-024-00921-w?utm_source=chatgpt.com)

Adjoin fresh letters \(L,Z\), absent from the alphabet of \(R\), and two rules
\[
\mathrm{ins}:1\Longrightarrow LwZ,
\qquad
\mathrm{del}:LvZ\Longrightarrow1,
\tag{19}
\]
where \(1\) is the empty word.

Regard the resulting finite rewriting system as a one-vertex \(2\)-computad \(\Gamma_{R,w,v}\). Then
\[
\boxed{
F_2(\Gamma_{R,w,v})\text{ has a bubble}
\quad\Longleftrightarrow\quad
w\Longrightarrow_R^*v.
}
\tag{20}
\]

**If reachability holds**, there is a nonempty derivation
\[
1\xRightarrow{\mathrm{ins}}LwZ
\Longrightarrow_R^*LvZ
\xRightarrow{\mathrm{del}}1.
\]
Its generating-cell count is positive, so it is a bubble.

**Conversely**, express a bubble as a vertical composite of whiskered generating \(2\)-cells. This gives a nonempty rewriting derivation \(1\Rightarrow^+1\).

The original rules cannot apply to the initial empty word. Thus the derivation uses \(\mathrm{ins}\), and it must eventually use \(\mathrm{del}\), since only \(\mathrm{del}\) removes marker letters.

Consider its **first** use of \(\mathrm{del}\). Before that step, the marker sequence is formed solely by insertions of balanced pairs \(LZ\). In the factor \(LvZ\) being deleted, the two displayed markers must therefore be a matched pair created by one application of \(\mathrm{ins}\).

No subsequent insertion can have taken place between that pair: its markers would still be present, since no earlier deletion occurred. Original rules cannot cross either marker. Thus the word between the pair evolved from \(w\) to \(v\) using only \(R\)-rules. This proves the reverse implication in (20).

It follows that bubble-freeness is undecidable even for finite one-vertex \(2\)-computads **with no generating bubble**. Bubble existence is semidecidable by enumerating finite derivations.

### 3.3 What remains of the proposed equivalence

Guetta’s Conjecture 6.6.5 states that a free strict \(2\)-category is *homologically coherent* if and only if it is bubble-free. Homological coherence compares polygraphic homology with the homology of the Street nerve. [arxiv.org](https://arxiv.org/pdf/2104.12662?utm_source=chatgpt.com)

Your proposed sufficiency statement is stronger. An equivalence
\[
\operatorname{Free}(\Gamma)\simeq F_2(\Gamma)
\]
would identify the strict realization’s homology with that of the cellular \(2\)-complex, whose cellular chain complex is the polygraphic chain complex.

I do not have a proof or counterexample for
\[
F_2(\Gamma)\text{ bubble-free}
\ \Longrightarrow\
\Gamma\text{ homotopical}.
\]
The undecidability result above concerns bubble-freeness; without the converse, it does not establish undecidability of homotopicality.

## 4. Positive \(3\)-computads and incoming arrows

### 4.1 Counterexample under the stated definition of positivity

Consider the connected \(3\)-computad
\[
\Gamma_0=\{*\},\qquad
\Gamma_1=\varnothing,
\]
\[
\Gamma_2=\{b:1_*\Rightarrow1_*\},
\qquad
\Gamma_3=\{\Omega:b\Rrightarrow b\}.
\tag{21}
\]
Both \(2\)-boundaries of \(\Omega\) are nonidentity. Thus (21) is positive under question 4’s definition.

Let \(D=F_3(\Gamma)\). There are strict functors
\[
B^2\mathbb N\xrightarrow{i}D\xrightarrow{r}B^2\mathbb N,
\qquad ri=1,
\]
where \(i\) includes the \(2\)-skeleton and
\[
r(\Omega)=1_b.
\]
Therefore \(|D|\) has \(K(\mathbb Z,2)\) as a retract. In particular,
\[
H_4(|D|;\mathbb Q)\ne0.
\]

On the other hand, \(|\operatorname{Free}(\Gamma)|\) is a CW complex of dimension at most \(3\), so its fourth homology vanishes. Hence
\[
\boxed{
\operatorname{Free}(\Gamma)\not\simeq F_3(\Gamma).
}
\]
The same retract shows that \(D\) has no finite coherent presentation in any dimension.

This example has a non-positive \(2\)-skeleton. **If positivity is required in every dimension, it does not answer that stronger question.** I have no proof or counterexample for that version. Chanavat’s Comment 3.40 states the expected extension to arbitrary positive polygraphs; the proved results immediately preceding it concern regular \(3\)-polygraphs and positive \(2\)-polygraphs. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

### 4.2 An incoming arrow forces other homs to change

Start with the free \(2\)-category generated by
\[
k:r\to s,\qquad f,g:s\to t,\qquad
\alpha,\beta:f\Rightarrow g,
\]
and attach
\[
\Omega:\alpha\Rrightarrow\beta.
\]

Replacing only \(D(s,t)\), while retaining the old \(D(r,t)\), does not define a strict \(3\)-category. Precomposition by \(k\) must send \(\Omega\) to
\[
k*\Omega:k*\alpha\Rrightarrow k*\beta,
\]
but the old \(D(r,t)\) has no such \(3\)-cell.

The correctly extended attachment is nevertheless homotopical in this example. It is
\[
I\vee\partial D_3\longrightarrow I\vee D_3.
\]
More generally, for a homotopical attachment \(Q\to Q'\), the functor
\[
Q\longmapsto I\vee\Sigma Q
\]
carries its homotopy pushout to a homotopy pushout. The relevant colimit-preserving wedge-suspension functor is Loubaton’s Lemma 2.2.1.32. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Thus item 14 extends to this incoming-arrow class, with both \(D(s,t)\) and \(D(r,t)\) updated. An extension for arbitrary incoming contexts would need to account for every forced whiskering and prove that the resulting strict attachment is homotopical; the single-hom replacement argument does not establish that.
