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
