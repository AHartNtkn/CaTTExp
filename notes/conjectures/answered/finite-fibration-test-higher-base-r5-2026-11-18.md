# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n), round 5

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. Everything in §2 is proved and is not re-asked. The questions are in §3, smallest first.*

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
6. **Walking 3-cell base, Cat-valued weight.** Let B be the walking 3-cell (u, v : 0 → 1, α, β : u ⇒ v, Ω : α ⇛ β) and T : B → Cat with T(0) = A and T(1) = C free on finite graphs, T(u) = U, T(v) = V and T(α) = T(β) = a. Then ∫T is presented by the following generators:
   - the FT₃ data: u_e, v_e, θ_{u,f}, θ_{v,f}, λ_{γ,e} : u_e ; a_e ⇒ v_e and Ξ_{γ,f};
   - one marked 3-generator ω_e : λ_{α,e} ⇛ λ_{β,e} per vertex e of A;
   - one marked 4-generator K_{Ω,f} : Ξ_{α,f} ; L_{ω,f} ⇛ R_{ω,f} ; Ξ_{β,f} per generating arrow f of A, where L_ω and R_ω are ω whiskered into the two sides of the Ξ square.
   
   Localise at the θ's, Ξ's and K's. The proof is a pattern:
   - Write ∫T ≃ (K × A) ∐_{I×A} C, where K is the total of the universal weight (x; y₀ —a→ y₁; u, v; λ_α, λ_β; ω) and I = [1].
   - Present K × A as K ⊗ A localised at the mixed generators k ⊗ f.
   - The generators of Ψ_T are then exactly the relative Gray-tensor generators k ⊗ a for k ∈ K ∖ I and a a generator of A.
   
   **Without the 4-generators the presentation is wrong.** For A = C = [1] with identity functors, the generator counts (4, 6, 6, 4) give Euler characteristic 0, while ∫T = B × [1] groupoidifies to a point.
7. **A 4-generator is needed for 2-category-valued weights.** For the walking 2-cell base and the constant weight D₂, the product D₂ × D₂ needs its 4-cell (α ⊗ fibre 2-cell): without it the counts (4, 8, 8, 4) give χ = 0 ≠ 1.
8. **Regularity is not necessary.** The positive, non-regular 3-computad x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r has Free ≃ F₃. The Θ-nerve of F₃ is the union of the nerve of F₂ and of the full sub-3-globe on x, z, intersecting in ∂D₃, so the attachment of ζ is a homotopy pushout.

9. **2-category-valued weights over the walking 2-cell.** Let B be the walking 2-cell (u, v : 0 → 1, α : u ⇒ v) and T valued in free 2-categories on finite positive 2-computads, A = T(0), C = T(1), U, V, a = T(α). Since a free strict 2-category has no non-identity invertible 2-cells, the weight data are strict: `Uf ; a_y = a_x ; Vf` and `Uρ ∗ a_y = a_x ∗ Vρ`.
   - **Generators.** Those of A and C; marked u_x, v_x; η^w_f : w_x ; Wf ⇒ f ; w_y (w = u, v); marked λ_x : u_x ; a_x ⇒ v_x; κ^w_ρ : η^w_p · (ρ ∗ w_y) ⇛ (w_x ∗ Wρ) · η^w_q for each fibre 2-cell ρ : p ⇒ q; Ξ_f : (λ_x ∗ Vf) · η^v_f ⇛ (η^u_f ∗ a_y) · (f ∗ λ_y); and one 4-generator Ω_ρ between the two composites of Ξ and κ. Localise at S = {η, κ, Ξ, Ω}.
   - **Proof.** The computad is the strict pushout `A ∐_{H⊗{0}} (H ⊗ I_out) ∐_{H⊗{1}} C` with H = A ⊗ I_in (a double Gray cylinder), and localising it gives `(A × K) ∐_{A×I} C` with K = 1^co ⋆ I, which is ∫T by Loubaton's suspension-base classification.
   - **Tensor-localisation lemma.** For any set S of positive-dimensional cells, `X[S⁻¹] ⊗ I ≃ (X ⊗ I)[{s ⊗ 0, s ⊗ 1, s ⊗ i}⁻¹]`.
   - **Mixed localisation for 2-category fibres.** `(A ⊗ K)[(g ⊗ k)⁻¹ : dim g, dim k > 0] ≃ A × K`, provided the mixed generators of every fibre dimension are included.
10. **Positivity is not necessary.** The 2-computad Q = (∗; t : ∗ → ∗; η : 1_∗ ⇒ t) is non-positive, and Free(Q) ≃ F₂(Q) = BΔ_+^inj (order-preserving injections under concatenation; coherent freeness from the monoidal envelope Env_{E1}(E0) ≃ Δ_+^inj, Blans–Linskens arXiv 2605.03150). Its suspension (0, 1; f; α : f ⇒ f; T : 1_f ⇛ α) is a non-positive 3-computad with Free ≃ F₃, and both groupoidify to a point. So the terminal weight on these bases has a finite presentation with no localisation. Compare item 4: (x; σ : 1_x ⇒ 1_x) is non-positive and not homotopical.
11. **The gap in the induction (closed for 2-dimensional bases by item 12, and for suspension bases by items 15–16).** Gluing local totals `E_{D_k} ≃ (A × L_k) ∐_{A × D_{k−1}} C`, with L_k = 1^co ⋆ D_{k−1}, gives the right local generator count, one generator of dimension k + j per fibre j-generator. But the attaching maps land in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself. Such lifts need not exist: in Free(s)[s⁻¹] the inverse of a marked arrow s exists, in Free(s) no arrow goes back. For the walking 2-cell the double cylinder supplies the lifts explicitly; for a base generator whose boundary is a composite, nothing in this item does (items 12, 15 and 16 supply them in their cases).

12. **FT for every homotopical base of dimension ≤ 2.**
    - *Paths.* For a base path p = e₁; … ; e_r, the map δ_r : I → [r] (0 ↦ 0, 1 ↦ r) and A ⊗ [r] ≃ (A ⊗ I) ∐_A … ∐_A (A ⊗ I) give a map M_{F_p} → P_gr from the cylinder of F_p into the *unlocalised* graph presentation. It sends the transport to the composite of the edge lifts. Its naturality cells are explicit pastings without inverses, for example η^{fg}_p = (f_x ∗ η^g_{Fp}) · (η^f_p ∗ g_{Fy}).
    - *Theorem.* Let Γ be a finite 2-computad with Free(Γ) ≃ F₂(Γ), and let the fibres be A_b = F_m(Π_b) with Π_b finite and homotopical. Then ∫T is presented by one marked generator of dimension j + 1 (respectively j + 2) for each base edge (respectively base 2-cell) and each source-fibre j-generator, besides the fibre generators. Those with j > 0 are inverted, and the dimension is ≤ m + 2.
    - *Proof.* Attach the walking-2-cell double-cylinder blocks for all base 2-cells at once, along these path maps. Then use Loubaton Cor. 3.2.3.16.
13. **Homotopical 2-computads beyond positivity.**
    - *Operadic criterion.* If Γ has one vertex and every 2-generator has a single generating arrow as target (any source, possibly empty), then F₂(Γ) ≅ B Env_{E1}(P) for the free planar coloured operad P, and Free(Γ) ≃ F₂(Γ). The same holds with "source" in place of "target". Examples: Q of item 10, and (∗; t; η : 1 ⇒ t, μ : tt ⇒ t).
    - *An obstruction.* For R = (∗; t; η : 1 ⇒ t, ε : t ⇒ 1), the composite η · ε makes B²ℕ a retract of F₂(R). So F₂(R) has no finite presentation, and R is not homotopical.
14. **A 3-dimensional attachment rule.** Let D be a strict 3-category with a finite homotopical presentation and with vertices s, t such that no nonidentity 1-cell enters s or leaves t, and D(s,s) = D(t,t) = 1. Then replacing K = D(s,t) by K′, obtained from K by homotopical 2-cell attachments, is a homotopical 3-cell attachment, via an exact union of Θ-nerves. This covers item 8's ζ, the suspension of Q, and suspensions of the operadic class.

15. **FT₃ for a base 3-generator with composite boundary (proved).** Base: vertices 0, 1; arrows u, w, v : 0 → 1; 2-cells β : u ⇒ w, γ : w ⇒ v, α : u ⇒ v; 3-cell Ω : α ⇛ β · γ. For T valued in free categories on finite graphs (so T(Ω) is an identity and a_x = b_x ; c_x), ∫T is presented by the FT₃ data for α, β, γ together with one marked 3-generator ω_x per fibre vertex and one inverted 4-generator K_f per fibre arrow, where the data for the composite face δ = β · γ are explicit pastings without inverses: λ_δ = (λ_β ∗ c_x) · λ_γ and Ξ_δ built from Ξ_β, Ξ_γ. The attaching maps exist before localisation because they are induced by an actual functor of unlocalised double cylinders along δ₂ : I → [2]; the base pushout is a homotopy pushout (regular 3-polygraph). Dimension ≤ 4.
16. **FT over suspension bases (proved).** Let Q = F_d(Λ) with Λ a finite homotopical d-computad, and let the base be ΣQ. For T valued in categories free on finite graphs, with A = T(0) and C = T(1), ∫T is presented by A, C, one marked (i+1)-generator κ_q ⊗ x per vertex x of A and one inverted (i+2)-generator κ_q ⊗ f per arrow f of A, for each i-generator q of Λ. Proof: K = 1^co ⋆ Q, and (K × A) ∐_{Q×A} C ≃ ∫_{ΣQ} T by the suspension-base classification, after mixed localisation. Dimension ≤ d + 2. Item 15 is the case Λ = (u, w, v; β, γ, α; Ω).
17. **Bubbles are an obstruction, and detecting them is undecidable (proved).** Call a nonidentity 2-cell 1_x ⇒ 1_x of F₂(Γ) a *bubble*.
    - If F₂(Γ) has a bubble q, then sending every generating 2-cell to 1 gives a strict 2-functor r : F₂(Γ) → B²ℕ with r(q) = k > 0, and i : B²ℕ → F₂(Γ), 1 ↦ q, is well defined by Eckmann–Hilton. Since ri = [k] acts by kʲ on H_{2j}(K(ℤ,2); ℚ), the rational homology of |F₂(Γ)| is nonzero in every even degree, so F₂(Γ) has no finite coherent presentation. Hence homotopical ⇒ bubble-free, with no retraction hypothesis.
    - Bubble-freeness is undecidable, already for one-vertex 2-computads with no generating bubble: reachability w ⇒* v in a positive semi-Thue system R reduces to the existence of a bubble in R plus an insertion rule ins : 1 ⇒ L w Z and a deletion rule del : L v Z ⇒ 1 with fresh markers L, Z.
18. **Positivity only in the top dimension is not enough (proved).** The 3-computad with one vertex, b : 1 ⇒ 1 and Ω : b ⇛ b is positive in the sense "both boundaries of every 3-generator are non-identity 2-cells", yet its 2-skeleton has a bubble and it is not homotopical.
19. **Item 14 with an incoming arrow (proved).** If an arrow k enters s, replacing only D(s, t) does not give a strict 3-category. The correct attachment is I ∨ ∂D₃ → I ∨ D₃, which updates both homs; it is homotopical, since the wedge-suspension functor preserves homotopy pushouts.
20. **FT₃ over every homotopical 3-computad base (proved).** Orient the inverted naturality cells as `η^w_f : w_e ; Wf ⇒ f ; w_{e′}` (as in item 9). Then the FT₃ data lift along right whiskering without inverses: for α : p ⇒ q : x → y and r : y → z,
    - `λ_{α▷r,e} := (p_e ∗ η^r_{a_e}) · (λ_{α,e} ∗ r_{Qe})`, where η^r of a fibre path is pasted from the η^r of its arrows;
    - `Ξ_{α▷r,f} := (p_e ∗ η^r_{a_e;Qf}) · (Ξ_{α,f} ∗ r)`, up to interchangers. This uses `a_e ; Qf = Pf ; a_{e′}` as words in the free fibre.
    
    Together with identities, vertical composites (item 15) and left whiskering (`λ_{w▷α,e} = w_e ∗ λ_{α,We}`), every 2-cell s of F₂(Γ₂) gets unlocalised lifts λ_s, Ξ_s.
    - *Theorem.* Let Γ be a finite 3-computad with Free(Γ) ≃ F₃(Γ) and Free(Γ₂) ≃ F₂(Γ₂), and T valued in categories free on finite graphs. Then ∫T is presented by item 12's data over Γ₂, plus, for each 3-generator Ω : s ⇛ t, a marked ω_{Ω,e} : λ_{s,e} ⇛ λ_{t,e} per source-fibre vertex and an inverted 4-generator K_{Ω,f} (shaped as in item 6) per source-fibre arrow. Localise at the η, Ξ and K. Dimension ≤ 4. This covers item 8's base ζ : α ▷ r ⇛ β ▷ r, where a_e ≠ b_e is allowed (only R a_e = R b_e is forced).
    - *Proof.* Write the base as `Free(Γ₂) ∐_{∐∂D₃} ∐ D₃`, and decompose ∫T by Loubaton Cor. 3.2.3.16. Present the pieces by items 12 and 6. The lifts give an attaching map from the presentation over ∂D₃ into the unlocalised presentation over Γ₂. After localisation this map preserves cartesian cells, and it is the identity on fibres over the two vertices, so by straightening it is an equivalence onto the pullback.

## 3. Questions

1. **FT_n over homotopical bases with higher-dimensional fibres.** For Cat-valued fibres, the induction of item 20 extends to every finite n-computad base with all skeleta homotopical. Use item 16 blocks over D_k and ∂D_k. Above dimension 2 the lifts of composites are formed from lower ones, and every cell is cartesian since the fibres are 1-categories. Generalise to fibres A_b = F_m(Π_b) with Π_b finite and homotopical, using the double-cylinder blocks of item 9 at every level. State the finite check and the dimension bound n + m. A first target is ΣQ with 2-category-valued fibres, then item 8's base ζ with 2-category-valued fibres.
2. **Is bubble-freeness sufficient?** Is every finite bubble-free 2-computad homotopical (Free(Γ) ≃ F₂(Γ))? Or give a counterexample, for example with several vertices or with 2-generators whose source and target are both composite.
   - *Context.* Homotopical implies homologically coherent (polygraphic homology = homology of the Street nerve), so a positive answer implies the "if" half of Guetta's Conjecture 6.6.5 (L. Guetta, *Homology of strict ω-categories*, PhD thesis 2021, arXiv 2104.12662, §6.6). The argument of item 17 gives the "only if" half of that conjecture for every free 2-category.
   - *Reformulation.* Let Γ⁺ add an endo-1-generator e_x at each vertex x and replace each empty boundary path at x by e_x. Then Γ⁺ is positive, hence homotopical, and `Free(Γ) ≃ Free(Γ⁺) ∐_{∐ C_x} ∐ {x}` with C_x the free category on a loop. So Γ is homotopical iff the strict collapse of the loops e_x in F₂(Γ⁺) is a homotopy pushout of (∞,2)-categories. When is collapsing an endo-1-cell of a positive free 2-category homotopically correct?
3. **One-sided 2-computads.** Call Γ *one-sided* if every 2-generator has a nonempty target path, or every 2-generator has a nonempty source path. One-sided computads are bubble-free (the last factor of a bubble would need an empty target, respectively the first an empty source). The class is decidable and contains:
   - positive computads;
   - both operadic classes of item 13;
   - Q of item 10.
   
   It excludes (x; σ : 1 ⇒ 1) and R of item 13. **Is every finite one-sided 2-computad homotopical?** In the reformulation of Question 2, for target-nonempty Γ the loop e_x occurs only in sources of Γ⁺, so it is consumed and never produced.
4. **Positive 3-computads.** Call a 3-computad *positive in every dimension* when its 2-skeleton is positive (both boundary paths of every 2-generator nonempty) and both boundaries of every 3-generator are non-identity 2-cells. Is every such 3-computad homotopical? Or give a counterexample.
5. **General hom attachments.** Extend item 14 to attachments in a hom D(s, t) when s has incoming 1-cells and t has outgoing ones, or when D(s, s) or D(t, t) is nontrivial, generalising item 19.

## 4. What would count as an answer

Any of the following:
- a proof or counterexample for any question;
- a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs;
- a reference to a published characterisation of homotopical polygraphs in low dimension.

# Researcher Response

**Question 1 has the expected presentation in dimension \(4\).** The attaching map is obtained by subdividing the **outer** cylinder. It requires only
\[
T(r)T(\alpha)=T(r)T(\beta),
\]
not \(T(\alpha)=T(\beta)\).

The construction also gives three further results:

- FT for Cat-valued weights over finite homotopical \(3\)-computads whose \(2\)-skeleton is homotopical;
- FT over arbitrary finite homotopical suspension bases with homotopical \(2\)-category fibres, with dimension bound \(n+2\);
- a decidable sufficient condition for homotopical \(2\)-computads, and a class of hom attachments allowing incoming arrows, outgoing arrows, and nontrivial endpoint endomorphisms.

I use the results in your §2 as hypotheses. The arguments below do not establish the full \(n,m\) theorem, bubble-free sufficiency, or homotopicality of every positive \(3\)-computad.

## 1. The whiskered \(3\)-generator

### 1.1 Data and composition conventions

Write
\[
A=T(x),\qquad B=T(y),\qquad C=T(z),
\]
and
\[
P=T(p),\quad Q=T(q):A\to B,\qquad R=T(r):B\to C.
\]
Let
\[
a=T(\alpha),\qquad b=T(\beta):P\Rightarrow Q.
\]
The existence of \(T(\zeta)\), with category-valued fibres, says exactly that
\[
Ra=Rb=:c.
\tag{1}
\]

Use chronological composition: \(f;g\) means first \(f\), then \(g\). Write \(\cdot\) for chronological composition of \(2\)-cells, \(\odot\) for that of \(3\)-cells, and \(*\) for whiskering.

Start with the unlocalised presentation \(\mathcal P_{\leq2}\) supplied by your item 12 for the \(2\)-skeleton. Use the comparison-cell convention
\[
\eta^p_f:p_e;Pf\Rightarrow f;p_{e'},
\]
and likewise for \(q,r\). Its other relevant generators are
\[
\lambda_{\sigma,e}:p_e;d^\sigma_e\Rightarrow q_e,
\qquad
d^\alpha=a,\quad d^\beta=b,
\]
and
\[
\Xi_{\sigma,f}:X_{\sigma,f}\Rrightarrow Y_{\sigma,f},
\]
where
\[
\begin{aligned}
X_{\sigma,f}
  &=(\lambda_{\sigma,e}*Qf)\cdot\eta^q_f,\\
Y_{\sigma,f}
  &=(\eta^p_f*d^\sigma_{e'})
       \cdot(f*\lambda_{\sigma,e'}).
\end{aligned}
\tag{2}
\]

Here \(f:e\to e'\) is a generating arrow of \(A\).

### 1.2 Derived comparisons for paths

Extend \(\eta^r\) from generating arrows of \(B\) to all finite paths by
\[
\eta^r_{1_d}=1_{r_d},
\qquad
\eta^r_{\ell;m}
 =(\eta^r_\ell*Rm)\cdot(\ell*\eta^r_m).
\tag{3}
\]
These are pastings in the unlocalised presentation.

Set
\[
U=RP,\qquad V=RQ,
\]
and define the composite transports
\[
u_e=p_e;r_{Pe},
\qquad
v_e=q_e;r_{Qe}.
\]
Their comparison cells are
\[
\begin{aligned}
\eta^u_f
  &=(p_e*\eta^r_{Pf})\cdot(\eta^p_f*r_{Pe'}),\\
\eta^v_f
  &=(q_e*\eta^r_{Qf})\cdot(\eta^q_f*r_{Qe'}).
\end{aligned}
\tag{4}
\]

The required lifts of the whiskered faces are
\[
\boxed{
\bar\lambda_{\sigma,e}
  =(p_e*\eta^r_{d^\sigma_e})
       \cdot(\lambda_{\sigma,e}*r_{Qe}).
}
\tag{5}
\]
Their types, using (1), are
\[
\bar\lambda_{\sigma,e}:u_e;c_e\Rightarrow v_e.
\]

Thus (5) first moves \(d^\sigma_e\) across the transport for \(r\), then applies the lift of \(\sigma\). No inverse is used.

For their naturality cells, put
\[
\ell^\sigma_f=d^\sigma_e;Qf=Pf;d^\sigma_{e'},
\qquad
J_{\sigma,f}=p_e*\eta^r_{\ell^\sigma_f}.
\tag{6}
\]
The equality in (6) is naturality in the free category \(B\).

For a \(3\)-cell \(H:X\Rrightarrow Y\), write
\[
[L,H,R]:L\cdot X\cdot R\Rrightarrow L\cdot Y\cdot R.
\]
Define
\[
\boxed{
\bar\Xi_{\sigma,f}
  =[J_{\sigma,f},\,\Xi_{\sigma,f}*r_{Qe'},\,1].
}
\tag{7}
\]
Its boundaries are
\[
\begin{aligned}
\bar X_{\sigma,f}
  &=(\bar\lambda_{\sigma,e}*Vf)\cdot\eta^v_f,\\
\bar Y_{\sigma,f}
  &=(\eta^u_f*c_{e'})
       \cdot(f*\bar\lambda_{\sigma,e'}).
\end{aligned}
\tag{8}
\]

To check (7), expand (3)–(5) and interchange the indicated whiskerings. The resulting identities are
\[
\begin{aligned}
\bar X_{\sigma,f}
   &=J_{\sigma,f}\cdot(X_{\sigma,f}*r_{Qe'}),\\
\bar Y_{\sigma,f}
   &=J_{\sigma,f}\cdot(Y_{\sigma,f}*r_{Qe'}).
\end{aligned}
\tag{9}
\]
The cylinder construction below supplies these identifications coherently. In particular, one does **not** need an equality
\(J_{\alpha,f}=J_{\beta,f}\).

### 1.3 The actual unlocalised substitution map

Here is a construction of the map underlying all these formulas.

For \(d:P\Rightarrow Q\), let
\[
H=A\otimes I_{\mathrm{in}},
\]
with evaluation
\[
h_d:H\longrightarrow B.
\]
It sends the endpoint copies of \(A\) by \(P,Q\), sends the bridge at \(e\) to \(d_e\), and sends the mixed \(2\)-cells to identities witnessing naturality.

The double-cylinder presentation is
\[
W_d=
A\amalg_{H\otimes\{0\}}
(H\otimes I_{\mathrm{out}})
\amalg_{H\otimes\{1\}}B,
\tag{10}
\]
where the first endpoint map is projection \(H\to A\). Also put
\[
M_R=(B\otimes I)\amalg_{B\otimes\{1\}}C.
\]

Subdivide the outer interval:
\[
H\otimes[2]
 \simeq
(H\otimes I)\amalg_H(H\otimes I).
\]
Map its first interval into \(W_d\), and its second by
\[
h_d\otimes I:H\otimes I\longrightarrow B\otimes I
\longrightarrow M_R.
\]
They agree on their common \(H\). Precomposition with
\[
H\otimes\delta_2:H\otimes I\longrightarrow H\otimes[2]
\]
therefore gives
\[
\boxed{
W_{Rd}\longrightarrow W_d\amalg_B M_R.
}
\tag{11}
\]

This is an unlocalised map. Its images of the generating lift and naturality cells are exactly (5) and (7).

Apply (11) separately to \(a\) and \(b\). Equation (1) gives the same source double cylinder \(W_c\), while the restrictions to its two edge cylinders agree: they depend only on \(P,Q,R\). Consequently, the two maps glue along the entire parallel-arrow boundary.

### 1.4 The new generators

Adjoin precisely the following generators to \(\mathcal P_{\leq2}\).

For each vertex \(e\) of \(A\), a marked \(3\)-generator
\[
\omega_e:
\bar\lambda_{\alpha,e}
\Rrightarrow
\bar\lambda_{\beta,e}.
\tag{12}
\]

For each generating arrow \(f:e\to e'\) of \(A\), define
\[
\begin{aligned}
L_f
 &=[1,\omega_e*Vf,\eta^v_f]\odot\bar\Xi_{\beta,f},\\
R_f
 &=\bar\Xi_{\alpha,f}\odot
       [\eta^u_f*c_{e'},\,f*\omega_{e'},\,1].
\end{aligned}
\tag{13}
\]
Both are \(3\)-cells
\[
\bar X_{\alpha,f}\Rrightarrow\bar Y_{\beta,f}.
\]
Adjoin a marked \(4\)-generator
\[
K_f:L_f\Rrightarrow R_f.
\tag{14}
\]

The projections are
\[
\omega_e\longmapsto\zeta,
\qquad
K_f\longmapsto1_\zeta.
\]
Localise at
\[
S=
\{\eta^p_f,\eta^q_f,\eta^r_g,
  \Xi_{\alpha,f},\Xi_{\beta,f},K_f\},
\tag{15}
\]
with \(f\) ranging over generating arrows of \(A\) and \(g\) over those of \(B\).

### 1.5 Correctness

Use the compatible walking-\(3\)-cell block proved in §2.2 below. Its boundary is literally the union of the two double cylinders in (10), glued along their edge cylinders. Thus (11) supplies its attaching map into \(\mathcal P_{\leq2}\).

After localisation:

- \(\mathcal P_{\leq2}\) presents the total over the \(2\)-skeleton, by your item 12;
- the attached block presents the total over \(D_3\);
- its boundary presents the total over \(\partial D_3\);
- (11) becomes the restriction map associated with the whiskered faces.

Your item 8 supplies the homotopy pushout for the base attachment. Loubaton’s Corollary 3.2.3.16 then identifies the corresponding pushout of totals with the total over the attached base. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com) Hence
\[
\boxed{
\operatorname{Free}(\Psi_T)[S^{-1}]
 \simeq \int T
}
\]
as marked categories over the base. The dimension is at most \(4\).

## 2. Extensions of FT

### 2.1 A mixed-localisation lemma for a \(2\)-dimensional second factor

Let \(X\) have a finite homotopical computad presentation, of arbitrary finite dimension. Let
\[
A=F_2(\Pi)
\]
for a finite homotopical \(2\)-computad \(\Pi\).

There is a finite cellular model \(\mathcal R_A(X)\), with one generator \(x\otimes g\) for every pair of generators, such that
\[
\boxed{
\mathcal R_A(X)
 \big[(x\otimes g)^{-1}:
       \dim x>0,\ \dim g>0\big]
 \simeq X\times A.
}
\tag{16}
\]
It is natural in \(X\), and has the corresponding relative cellular description. This is the comparison needed for \(2\)-category fibres.

#### Construction and proof

Let \(A_1\) be the free category on the generating graph of \(\Pi\). Homotopicality gives the pushout
\[
A\simeq
A_1\amalg_{\coprod_{\rho\in\Pi_2}\partial D_2}
          \coprod_{\rho\in\Pi_2}D_2.
\tag{17}
\]

Put \(H_X=X\otimes I_{\mathrm{in}}\), and define
\[
C_2(X)=
X\amalg_{H_X\otimes\{0\}}
(H_X\otimes I_{\mathrm{out}})
\amalg_{H_X\otimes\{1\}}X,
\tag{18}
\]
using projection \(H_X\to X\) at both ends.

Apply your item 12 to the **constant weight \(X\) over \(D_2\)**. It identifies (18), after inversion of every mixed generator, with \(X\times D_2\). Its two boundary cylinders give the corresponding comparison for \(X\times\partial D_2\).

Now form
\[
\mathcal R_A(X)=
(X\otimes A_1)
\amalg_{\coprod_{\rho}X\otimes\partial D_2}
\coprod_{\rho}C_2(X).
\tag{19}
\]
All maps in (19) exist before localisation. In particular, the maps
\(\partial D_2\to A_1\) are functors between categories, so their tensors with \(X\) give the attaching maps directly.

For any target \(Z\), a map from (19) inverting the graph-stage mixed generators factors on that stage through \(X\times A_1\). Naturality of the graph comparison makes its boundary restrictions factor through \(X\times\partial D_2\). Inverting the additional mixed generators in each copy of \(C_2(X)\) makes that restriction factor through \(X\times D_2\). Therefore its space of maps to \(Z\) is
\[
\begin{aligned}
&\operatorname{Map}(X\times A_1,Z)\\
&\quad\times_{\prod_{\rho}
 \operatorname{Map}(X\times\partial D_2,Z)}
 \prod_{\rho}\operatorname{Map}(X\times D_2,Z)
 \;\simeq\;
 \operatorname{Map}(X\times A,Z).
\end{aligned}
\]
This proves (16), including its naturality.

For the generator count, the relative Gray product of a \(p\)-globe and a \(j\)-globe adds one \((p+j)\)-cell, for \(j=0,1,2\). The required atomic pasting statements follow from Chanavat’s acyclic-atom and monoidal comparison results, Corollary 3.27, Proposition 3.28 and Theorem 3.29. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com) Since (19) preserves cellular pushouts in \(X\), this gives the stated relative version.

### 2.2 A walking-\(3\)-cell block with the required raw boundary

The orientation of the tensor factors matters here: a localised cone-first presentation cannot simply be identified with the fibre-first double cylinders used in (11).

Let \(A,C\) be free categories, let \(U,V:A\to C\), and let \(d:U\Rightarrow V\). Write the inner walking \(2\)-cell as
\[
D_2=(u,v;\alpha,\beta:u\to v;\Omega:\alpha\Rightarrow\beta).
\]
Set
\[
H=A\otimes D_2,
\]
using the cellular construction of §2.1, and let
\[
h:H\longrightarrow A\times D_2\longrightarrow C
\]
send both inner arrows to \(d\) and the inner \(2\)-cell to an identity.

Define
\[
W_3=
A\amalg_{H\otimes\{0\}}
(H\otimes I)
\amalg_{H\otimes\{1\}}C.
\tag{20}
\]
Its boundary is
\[
W_d^\alpha
 \amalg_{M_U\amalg_{A\amalg C}M_V}
W_d^\beta.
\tag{21}
\]
This follows by restricting \(H\) to \(A\otimes\partial D_2\), before taking the outer cylinder.

Relative to (21), the new cells are exactly a \(3\)-cell per vertex of \(A\) and a \(4\)-cell per generating arrow.

To verify localisation, first use (16):
\[
A\otimes D_2\longrightarrow A\times D_2
\]
inverts
\[
f\otimes\alpha,\quad f\otimes\beta,\quad f\otimes\Omega.
\]
Tensor-localisation along the outer interval leaves their outer comparison cells
\[
\Xi_{\alpha,f},\quad\Xi_{\beta,f},\quad K_{\Omega,f};
\]
their endpoint copies map to identities.

Next apply Loubaton’s Proposition 3.1.3.2 with the auxiliary marking
\(A^\sharp\times D_2^\flat\). This adds precisely the inversions of the two transport comparisons \(\eta^u_f,\eta^v_f\). In dimension at least \(2\), every marked cell of this auxiliary product is an identity, since \(A\) is a category. Thus there are no further independent comparison generators. The auxiliary marking specifies this underlying localisation; the vertical fibre arrows retain their original marking. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The result is
\[
\bigl(A\times(1^{\mathrm{co}}\star D_2)\bigr)
 \amalg_{A\times D_2}C,
\]
which is the required total by the suspension-base classification. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com) This proves the local lemma used in §1.

### 2.3 Cat fibres over general \(3\)-dimensional bases

**Theorem.** Let \(\Gamma\) be a finite \(3\)-computad. Suppose its \(2\)-skeleton is homotopical and its displayed attachment of generating \(3\)-cells is a homotopy pushout. Then every strict Cat-valued weight with fibres free on finite graphs has the relative Gray-generator presentation, in dimension at most \(4\).

In particular, the hypotheses hold if both \(\Gamma\) and \(\Gamma_{\leq2}\) are homotopical, with their canonical comparisons.

#### Substitution for arbitrary \(2\)-cell expressions

Fix the path-cylinder maps from your item 12. For every chosen finite expression
\[
\delta:p\Rightarrow q
\]
in the free strict \(2\)-category, construct
\[
J_\delta:W_{T\delta}\longrightarrow\mathcal P_{\leq2}
\tag{22}
\]
under the fixed cylinders for \(p,q\).

There are four operations:

1. **Identity:** collapse the inner interval:
   \[
   W_{1_U}\longrightarrow M_U.
   \]

2. **Vertical composition:** subdivide the inner interval:
   \[
   W_{e\circ d}\longrightarrow W_d\amalg_{M_V}W_e.
   \]

3. **Right whiskering:** use (11):
   \[
   W_{Rd}\longrightarrow W_d\amalg_C M_R.
   \]

4. **Left whiskering:** subdivide the outer interval:
   \[
   W_{dF}\longrightarrow M_F\amalg_A W_d.
   \]
   On its first interval use projection
   \(H_D\otimes I\to D\otimes I\to M_F\); on its second use
   \[
   (F\otimes I_{\mathrm{in}})\otimes I:
   H_D\otimes I\longrightarrow H_A\otimes I\longrightarrow W_d.
   \]
   The interface agrees because projection commutes with \(F\).

Horizontal composition is a composite of whiskering and vertical composition.

These operations preserve the fixed path-cylinder boundary. For concatenated paths of lengths \(r,s\), this is an equality of maps on the whole cylinder: the composite
\[
I\xrightarrow{\delta_2}[2]\longrightarrow[r+s],
\qquad
0\mapsto0,\quad1\mapsto r,\quad2\mapsto r+s,
\]
is \(\delta_{r+s}\).

Now take a generating \(3\)-cell
\[
\Omega:\delta\Rrightarrow\epsilon.
\]
Choose one finite expression for each boundary. Since
\(T\delta=T\epsilon\), the two maps (22) have the common boundary needed to attach (20).

There is no requirement that different expressions for the same \(2\)-cell induce equal raw maps. After localisation they induce the same map: in the strict Grothendieck \(2\)-category of a Cat-valued weight, a \(2\)-cell over \(\delta:p\Rightarrow q\), between
\[
(p,r)\quad\text{and}\quad(q,s),
\]
exists exactly when
\[
r=T(\delta)_e;s,
\]
and is then uniquely determined. Thus the localised map depends only on the denoted base \(2\)-cell. Strict interchange creates no additional attaching obligation.

Attach all blocks (20), then localise. The same pullback-colimit argument as in §1.5 proves the theorem.

The generator families are:

| Base-generator dimension \(k\) | Fibre vertices | Fibre generating arrows |
|---|---:|---:|
| \(1\) | marked \(1\)-generators | inverted \(2\)-generators |
| \(2\) | marked \(2\)-generators | inverted \(3\)-generators |
| \(3\) | marked \(3\)-generators | inverted \(4\)-generators |

The vertical fibre generators are also retained.

### 2.4 Suspension bases with \(2\)-category fibres

**Theorem.** Let \(Q=F_d(\Lambda)\), where \(\Lambda\) is finite and homotopical. Let the base be \(\Sigma Q\), of dimension \(n=d+1\), and let its two fibres \(A,C\) have finite homotopical \(2\)-computad presentations. Then the expected relative Gray-generator presentation exists, with dimension at most
\[
d+3=n+2.
\]

Let
\[
h:Q\times A\longrightarrow C
\]
be the evaluation map associated with the weight, and put
\[
K=1^{\mathrm{co}}\star Q.
\]
Relative to \(Q\), this cone has its apex and one cell
\[
\kappa_q,\qquad \dim\kappa_q=i+1,
\]
for every generating \(i\)-cell \(q\) of \(\Lambda\).

Use §2.1 to form the unlocalised pushout
\[
\boxed{
\mathcal P=
\mathcal R_A(K)
 \amalg_{\mathcal R_A(Q)}C,
}
\tag{23}
\]
where the attaching map is the actual composite
\[
\mathcal R_A(Q)\longrightarrow Q\times A\xrightarrow{h}C.
\tag{24}
\]
Thus no lift out of a localisation is required.

The generators of (23) are those of \(A,C\), together with
\[
\kappa_q\otimes g,
\qquad
\dim(\kappa_q\otimes g)=i+1+j,
\qquad g\in\Pi_j,\quad j=0,1,2.
\tag{25}
\]
Mark all generators in (25), and invert precisely those with \(j>0\).

The mixed boundary generators in \(\mathcal R_A(Q)\) map to identities under (24). By (16) and the localisation universal property,
\[
\mathcal P[S^{-1}]
 \simeq
(K\times A)\amalg_{Q\times A}C
 \simeq
\int_{\Sigma Q}T.
\tag{26}
\]
The final equivalence is the same suspension classification used above.

The marking is also the required one. The marked cone cells at fibre vertices generate the Cartesian marking after localisation: whiskering them by identities on fibre cells gives the remaining marked product cells. The construction therefore proves a marked equivalence over \((\Sigma Q)^\sharp\).

### 2.5 The finite certificate

For these two FT extensions, a checker needs:

1. the stipulated homotopicality certificates for the base attachments and fibre presentations;
2. the finite functor and transformation data of \(T\), with their boundary equalities;
3. finite expressions for the attaching boundaries;
4. the cylinder substitutions above and the prescribed generator families;
5. the marking and localisation list: the relative pairs with positive fibre dimension are precisely those inverted.

For category fibres, the necessary equalities are finite word equalities in the free fibre categories. For \(2\)-category fibres, finite derivations of the required pasting equalities can be supplied.

This is a finite recognition certificate for the constructed presentations. It is not a decision procedure for homotopicality of arbitrary input computads.

## 3. A decidable sufficient condition for homotopical \(2\)-computads

The following answers the sufficient-condition alternative in question 3.

### 3.1 Closure under adjoining \(1\)-generators

**Lemma.** If a \(2\)-computad is homotopical, freely adjoining finitely many \(1\)-generators, without changing its \(2\)-generators or their boundaries, preserves homotopicality. The new arrows may be loops or form cycles.

Here is a coherent calculation proving the lemma.

Fix the vertex set \(X\). Use the monoidal category
\[
\mathcal V_X=\operatorname{Fun}(X\times X,\operatorname{Cat}_\infty),
\qquad
(F\star G)(x,z)=\coprod_yF(x,y)\times G(y,z).
\]
Associative algebras describe enriched categories with specified vertices. Haugseng gives this matrix construction and its comparison with enriched categorical algebras. [arxiv.org](https://arxiv.org/pdf/1312.3881?utm_source=chatgpt.com)

Let \(C\) be the algebra corresponding to the existing category. To adjoin
\(f:s\to t\), let \(G\) have value \(*\) at \((s,t)\) and be empty elsewhere. The free \(C\)-bimodule is
\[
M=C\star G\star C.
\]
The coherent extension under \(C\) is the tensor algebra
\[
T_C(M)=\coprod_{r\geq0}M^{\otimes_C r}.
\tag{27}
\]
This uses the equivalence between algebras in \(C\)-bimodules and algebras under \(C\), together with the free associative algebra formula. The relevant results are *Higher Algebra*, Corollary 3.4.1.7, Proposition 4.1.1.18 and Proposition 4.4.3.12. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

Because \(M\) is free on both sides, unitality of relative tensor products gives
\[
M^{\otimes_C r}
 \simeq C\star G\star C\star\cdots\star G\star C.
\]
Consequently,
\[
\boxed{
C[f](x,y)\simeq
C(x,y)\amalg
\coprod_{r\geq1}
C(x,s)\times C(t,s)^{r-1}\times C(t,y).
}
\tag{28}
\]

The ordinary strict extension has exactly the same hom categories. A \(1\)-cell using \(f\) exactly \(r\) times has a unique expression
\[
c_0\,f\,c_1\,f\cdots f\,c_r,
\]
with
\[
c_0:x\to s,\quad c_i:t\to s\ (0<i<r),\quad c_r:t\to y.
\]
A \(2\)-cell is a tuple of \(2\)-cells between the corresponding \(c_i\). Composition concatenates expressions and composes the adjacent \(C\)-factors. Products and disjoint unions of ordinary categories compute the corresponding constructions in \(\operatorname{Cat}_\infty\), so (28) identifies the strict extension with the coherent one.

For compatibility with the model in the question, the enriched Segal nerve has values
\[
[m]\longmapsto
\coprod_{x_0,\ldots,x_m}
\prod_i C(x_{i-1},x_i).
\]
Haugseng’s comparison identifies its completion with the complete iterated-Segal model; restriction along
\[
([m],[n])\longmapsto[m]([n],\ldots,[n])
\]
identifies the strict nerve here with the corresponding \(\Theta_2\)-nerve. Thus this calculation proves the required coherent pushout statement, not merely an ordinary enriched pushout statement. [arxiv.org](https://arxiv.org/pdf/1312.3881?utm_source=chatgpt.com)

The lemma follows by adjoining the new arrows successively.

### 3.2 The finite test

Let \(\Gamma\) be a finite \(2\)-computad. Require a partition
\[
\Gamma_0=\coprod_i X_i
\]
with these properties:

- No boundary of a generating \(2\)-cell uses an arrow joining different parts.
- For each induced internal computad \(\Gamma_i\), one of the following holds:
  - both boundaries of every \(2\)-generator are nonempty;
  - \(X_i\) is a singleton and every \(2\)-generator has one generating arrow as target;
  - \(X_i\) is a singleton and every \(2\)-generator has one generating arrow as source.

Then \(\Gamma\) is homotopical.

Indeed, the internal computads are homotopical by the positive and operadic criteria in your §2. Take their coproduct and freely adjoin the arrows joining different parts. The lemma applies, and no \(2\)-cell boundary is changed.

The condition is decidable: enumerate the finitely many partitions and inspect the finite boundary words. It covers all positive \(2\)-computads and both accepted operadic classes, including \(Q\). The identity-to-identity generator fails all three internal tests.

The condition also gives examples beyond the disjunction of those classes. Take vertices \(x,z\), arrows
\[
a,b:x\to x,\qquad t:z\to z,\qquad
h:x\to z,\qquad k:z\to x,
\]
and \(2\)-generators
\[
\theta:aa\Rightarrow bb,\qquad
\eta:1_z\Rightarrow t.
\]
The partition \(\{x\}\amalg\{z\}\) passes. The entire computad is neither positive nor single-source nor single-target. The cross arrows \(h,k\) may be retained, including the cycle they form.

This establishes a sufficient test; it does not establish bubble-free sufficiency.

## 4. Hom attachments with incoming and outgoing arrows and endomorphisms

There is a direct extension of the attachment argument for the following class.

Let \(J,L\) be gaunt ordinary categories, with chosen vertices \(s\in J\), \(t\in L\), and disjoint vertex sets. Let \(H\) be a gaunt strict \(2\)-category. Define the strict wedge
\[
D(H)=J\amalg_{\{s\}}\Sigma H\amalg_{\{t\}}L.
\tag{29}
\]

### 4.1 The strict wedge is a coherent wedge

Apply Loubaton’s Theorem 2.3.3.22 to the constant maps
\[
H\to J,\qquad H\to L
\]
at \(s,t\). It says that the coherent double mapping cylinder
\[
J\amalg_{H\otimes\{0\}}
(H\otimes I)
\amalg_{H\otimes\{1\}}L
\tag{30}
\]
is strict. Proposition 2.3.3.6 identifies the cylinder with its ends collapsed as \(\Sigma H\), so (30) is the coherent version of (29). Applying the strict reflector computes the ordinary strict wedge, proving the comparison. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The gaunt qualification is needed for this invocation: Loubaton’s strict categories are gaunt strict \(\omega\)-categories. Free graph categories, including those with loops, satisfy it. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 4.2 Every affected hom is explicit

For \(j\in J\) and \(\ell\in L\),
\[
\boxed{
D(H)(j,\ell)
  =J(j,s)\times H\times L(t,\ell).
}
\tag{31}
\]
The outer factors are discrete. Homs entirely in \(J\) or \(L\) are unchanged, and homs from \(L\) to \(J\) are empty.

A cross arrow has a unique expression consisting of an arrow \(j\to s\), an arrow of the suspended \(H\), and an arrow \(t\to\ell\). It can cross from \(J\) to \(L\) only once. Higher cells are cells of \(H\) with those two outer arrows fixed. This proves (31).

In particular,
\[
D(H)(s,t)=J(s,s)\times H\times L(t,t).
\tag{32}
\]
Thus \(H\) need not equal the entire hom \(D(H)(s,t)\).

### 4.3 Transporting an attachment

Put \(A_0=J\amalg L\). The coherent functor
\[
\Phi(H)=A_0\amalg_{\partial D_1}\Sigma H
\]
takes values under \(A_0\), and satisfies
\[
\operatorname{Map}_{A_0/}(\Phi(H),X)
 \simeq
\operatorname{Map}(H,X(s,t)).
\tag{33}
\]
It is therefore a left adjoint.

Suppose
\[
H'=H\amalg_{\partial D_2}D_2
\]
is a homotopical \(2\)-cell attachment. Applying \(\Phi\) and pasting pushouts gives
\[
\boxed{
D(H')\simeq D(H)\amalg_{\partial D_3}D_3.
}
\tag{34}
\]
Naturality of the strictness comparison in §4.1 identifies this with the strict attachment.

This changes every cross hom in (31) to
\[
J(j,s)\times H'\times L(t,\ell).
\]
No additional independent generators are needed for these whiskered cells.

### 4.4 A finite example exhibiting all the requested phenomena

Let \(J\) be freely generated by
\[
i\xrightarrow{\iota}s,\qquad a:s\to s,
\]
and \(L\) by
\[
b:t\to t,\qquad t\xrightarrow{\pi}o.
\]
Take
\[
H=\partial D_2=(u,v;\alpha,\beta:u\to v),
\]
and attach \(\zeta:\alpha\Rightarrow\beta\) to obtain \(H'=D_2\).

Then \(D(H')\) has generators
\[
\begin{array}{c|l}
0&i,s,t,o\\
1&\iota,\ a,\ u,v:s\to t,\ b,\ \pi\\
2&\alpha,\beta:u\Rightarrow v\\
3&\zeta:\alpha\Rrightarrow\beta.
\end{array}
\]
The attachment of \(\zeta\) is homotopical by (34). Both endpoint endomorphism monoids are nontrivial, and there are distinct incoming and outgoing arrows. The single \(3\)-generator yields all whiskerings
\[
\iota a^m*\zeta*b^n\pi,
\qquad m,n\geq0.
\]

This proves an attachment theorem with all those features. It does not assert that an arbitrary \(D\), without the wedge decomposition (29), permits arbitrary replacement of one hom.

## 5. Remaining scope

The results above leave three issues unresolved here:

- the full FT theorem for arbitrary \(n,m\), including compatibility along higher-dimensional common boundaries;
- whether every finite bubble-free \(2\)-computad is homotopical;
- whether every \(3\)-computad positive in every dimension is homotopical.

For question 1, however, the unlocalised attaching map and every new boundary are given explicitly by (3)–(14), and the resulting presentation has exactly the predicted \(3\)- and \(4\)-generators.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level.**
- **Settled:** part of Question 1.
  - §1 makes item 20's treatment of item 8's whiskered base 3-generator ζ : α ▷ r ⇛ β ▷ r (Cat-valued fibres) explicit. The outer cylinder is subdivided, W_{Rd} → W_d ⊔_B M_R (11), so the attaching map is an actual unlocalised map. It needs only R a = R b. This is not the 2-category-fibre version of ζ that Question 1 named as a second target.
  - Cat fibres over every finite 3-computad base whose 2-skeleton is homotopical and whose 3-cell attachment is a homotopy pushout (§2.3).
  - Suspension bases ΣQ with homotopical 2-category fibres, dimension ≤ n + 2 (§2.4).
  - A finite recognition certificate (§2.5).
- **New, Question 3 direction:** a decidable sufficient condition for homotopical 2-computads (§3).
  - Adjoining 1-generators preserves homotopicality (Lemma 3.1, via Haugseng's matrix enrichment and the tensor algebra (27)–(28)).
  - Hence any partition of the vertices into parts that are internally positive or single-vertex operadic, with no 2-cell boundary crossing parts, gives a homotopical computad.
- **New, Question 5:** hom attachments D(H) = J ⊔ ΣH ⊔ L with incoming and outgoing arrows and endpoint endomorphisms (§4).
- **Open:**
  - the full FT_{n,m} with compatibility along higher common boundaries, including item 8's ζ with 2-category fibres;
  - Question 2 (is bubble-free sufficient?);
  - Question 3 in full (is every one-sided computad homotopical?);
  - Question 4 (positive 3-computads).

Checked:

1. **§1.** This section uses Cat-valued fibres: A is generated by arrows f, and the new generators are ω_e per vertex and K_f per arrow. The data (1) Ra = Rb = c is exactly what T(ζ) needs for category-valued fibres. The walking-3-cell block (§2.2) has as raw boundary the union of the two double cylinders along their edge cylinders, so (11) is a genuine unlocalised attaching map. The correctness argument (item 12 for the 2-skeleton, a block over D₃, Loubaton Cor. 3.2.3.16) is the same pattern as item 20.
2. **Mixed localisation, §2.1.** 𝓡_A(X) is built from the pushout presentation of A = F₂(Π) over its free category on the 1-skeleton, plus the tensor-localisation lemma. The argument is the item-9 argument with X general. I did not check every cell of the cellular model.
3. **§3.1.**
   - The coherent free extension is T_C(C ⋆ G ⋆ C), using HA Cor. 3.4.1.7 and Props. 4.1.1.18 and 4.4.3.12.
   - Its homs (28) match the strict extension's homs: 1-cells c₀ f c₁ … f c_r with unique factorisation, and 2-cells as tuples.
   - Products and coproducts of 1-categories are computed the same way in Cat_∞, so the coherent and strict pushouts agree.
   - I checked the unique-factorisation claim: f is a free generator, and its occurrences split a 1-cell uniquely.
4. **§3.2.** The test is decidable, since there are finitely many partitions and finite boundary words. The example (θ : aa ⇒ bb at x, η : 1_z ⇒ t at z, cross arrows h, k) is neither positive nor one-vertex operadic, and it passes.
5. **§4.** The wedge decomposition puts all composites through ΣH in the explicit form ι a^m ∗ ζ ∗ b^n π, so replacing H by H′ along a homotopical attachment is a homotopy pushout. The response limits the claim to wedge-shaped D, correctly.

Follow-up prompt: `outbox/finite-fibration-test-higher-base-r6.md` (round 6, unsent).
