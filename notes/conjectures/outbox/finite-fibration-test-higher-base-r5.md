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

