# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n), round 6

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

21. **An unlocalised attaching map for a whiskered 3-generator (proved).** For item 8's base (ζ : α ▷ r ⇛ β ▷ r) and Cat-valued T with A = T(x), B = T(y), C = T(z), P, Q : A → B, R : B → C, a = T(α), b = T(β), the only constraint is R a = R b. Let W_d be the double cylinder of item 9 for d : P ⇒ Q and M_R = (B ⊗ I) ∐_{B⊗{1}} C. Subdividing the **outer** interval, H ⊗ [2] ≃ (H ⊗ I) ∐_H (H ⊗ I) with H = A ⊗ I_in, gives an actual map W_{Rd} → W_d ∐_B M_R. Applied to a and b it gives the same source cylinder, and the two maps glue along the parallel boundary. Adjoin a marked 3-generator ω_e : λ̄_{α,e} ⇛ λ̄_{β,e} per vertex e of A and a 4-generator K_f per arrow f of A, and localise at the η, Ξ and K. This presents ∫T in dimension ≤ 4.
22. **Mixed localisation with a 2-dimensional second factor (proved).** Let X have a finite homotopical computad presentation of any finite dimension, and A = F₂(Π) with Π a finite homotopical 2-computad. There is a finite cellular model 𝓡_A(X), natural in X, with one generator x ⊗ g for each pair of generators, such that 𝓡_A(X)[(x ⊗ g)⁻¹ : dim x, dim g > 0] ≃ X × A.
23. **Cat fibres over 3-dimensional bases (proved).** Let Γ be a finite 3-computad whose 2-skeleton is homotopical and whose attachment of 3-generators is a homotopy pushout (for instance Γ and Γ_{≤2} both homotopical). Every strict Cat-valued weight with fibres free on finite graphs then has the relative Gray-generator presentation, in dimension ≤ 4. Arbitrary 2-cell expressions in the boundaries of 3-generators are handled by substitution along the path-cylinder maps of item 12.
24. **Suspension bases with 2-category fibres (proved).** Let Q = F_d(Λ) with Λ finite and homotopical, base ΣQ of dimension n = d + 1, and fibres A, C with finite homotopical 2-computad presentations. With K = 1^co ⋆ Q and h : Q × A → C, the pushout 𝓟 = 𝓡_A(K) ∐_{𝓡_A(Q)} C along the actual composite 𝓡_A(Q) → Q × A → C has generators those of A and C plus κ_q ⊗ g of dimension i + 1 + j for each i-generator q of Λ and j-generator g of Π (j = 0, 1, 2). Inverting those with j > 0 gives ∫_{ΣQ} T. Dimension ≤ n + 2. A finite certificate (homotopicality certificates, the weight data, the attaching expressions, the generator families and the localisation list) checks these presentations.
25. **Adjoining 1-generators preserves homotopicality (proved).** If a 2-computad is homotopical, freely adjoining finitely many 1-generators (loops and cycles allowed) without changing the 2-generators keeps it homotopical. Proof: in Haugseng's matrix enrichment over 𝒱_X = Fun(X × X, Cat_∞), adjoining f : s → t is the tensor algebra T_C(C ⋆ G ⋆ C), whose homs C(x,y) ⊔ ∐_{r≥1} C(x,s) × C(t,s)^{r−1} × C(t,y) agree with the strict extension's homs.
    - *A decidable sufficient test.* Suppose the vertices of a finite 2-computad split into parts so that no 2-generator boundary uses an arrow between different parts, and in each part either every 2-generator has both boundary paths nonempty, or the part is a single vertex and every 2-generator has a single generating arrow as target, or as source. Then the computad is homotopical. Example: vertices x, z; arrows a, b : x → x, t : z → z, h : x → z, k : z → x; 2-generators θ : aa ⇒ bb and η : 1_z ⇒ t.
26. **Wedge hom attachments (proved).** Let J, L be gaunt 1-categories with vertices s ∈ J, t ∈ L, and H a gaunt strict 2-category. The strict wedge D(H) = J ∐_{s} ΣH ∐_{t} L is the coherent wedge (Loubaton Thm 2.3.3.22 and Prop. 2.3.3.6), with cross homs D(H)(j, ℓ) = J(j,s) × H × L(t,ℓ). For a homotopical 2-cell attachment H′ = H ∐_{∂D₂} D₂, D(H′) ≃ D(H) ∐_{∂D₃} D₃. This allows incoming and outgoing arrows and nontrivial endpoint endomorphisms (example: ι : i → s, a : s → s, b : t → t, π : t → o).

## 3. Questions

1. **FT with 2-category fibres over 3-dimensional bases.** Present ∫T for item 8's base ζ : α ▷ r ⇛ β ▷ r with fibres A_b = F₂(Π_b), Π_b finite and homotopical. Here T(ζ) is a genuine 3-cell, so item 21's subdivision must be combined with item 22's mixed localisation and item 9's double-cylinder blocks one level up. The expected dimension is ≤ 5. Then extend to every finite homotopical 3-computad base, as item 23 does for Cat fibres.
2. **FT_{n,m} in general.** For a finite n-computad base with all skeleta homotopical and fibres F_m(Π_b) with Π_b finite and homotopical, construct the relative Gray-generator presentation with dimension ≤ n + m, including compatibility of the attaching maps along higher-dimensional common boundaries. State the finite check.
3. **Is bubble-freeness sufficient?** Call a nonidentity 2-cell 1_x ⇒ 1_x of F₂(Γ) a bubble. Is every finite bubble-free 2-computad homotopical (Free(Γ) ≃ F₂(Γ))? Or give a counterexample, for example with several vertices inside one part, or with 2-generators whose source and target are both composite.
   - *Context.* Homotopical implies homologically coherent (polygraphic homology equals homology of the Street nerve), so a positive answer implies the "if" half of Guetta's Conjecture 6.6.5 (L. Guetta, *Homology of strict ω-categories*, PhD thesis 2021, arXiv 2104.12662, §6.6). Item 17 gives the "only if" half for every free 2-category.
   - *Reformulation.* Let Γ⁺ add an endo-1-generator e_x at each vertex x and replace each empty boundary path at x by e_x. Then Γ⁺ is positive, hence homotopical, and Free(Γ) ≃ Free(Γ⁺) ∐_{∐ C_x} ∐ {x}, with C_x the free category on a loop. So Γ is homotopical iff the strict collapse of the loops e_x in F₂(Γ⁺) is a homotopy pushout.
4. **One-sided 2-computads.** Call Γ one-sided if every 2-generator has a nonempty target path, or every 2-generator has a nonempty source path. One-sided computads are bubble-free. Item 25's test covers one-sided computads whose parts are positive or single-vertex operadic. Is every finite one-sided 2-computad homotopical? The smallest case outside item 25: one vertex, arrows s, t, and 2-generators whose targets are composite paths while some source is empty, for example η : 1 ⇒ st and μ : ts ⇒ t.
5. **Positive 3-computads.** Call a 3-computad positive in every dimension when its 2-skeleton is positive and both boundaries of every 3-generator are non-identity 2-cells. Is every such 3-computad homotopical? Or give a counterexample.

## 4. What would count as an answer

Any of the following:
- a proof or counterexample for any question;
- a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs;
- a reference to a published characterisation of homotopical polygraphs in low dimension.

# Researcher Response

**Question 1 has an affirmative answer, with dimension bound \(5\).** The same construction proves \(\mathrm{FT}_{3,m}\) for arbitrary finite \(m\), under the hypotheses on the base in item 23.

There is also a general mixed-localisation lemma extending item 22 to arbitrary finite-dimensional factors. It gives \(\mathrm{FT}_{n,m}\) for suspension bases and arbitrary finite \(m\). It does not, by itself, supply the compatible attaching maps required for arbitrary bases of dimension \(n\geq4\).

I give the constructions and proofs below. I do not resolve Questions 3–5.

## 1. The whiskered \(3\)-generator with \(2\)-category fibres

Write
\[
A=T(x),\qquad B=T(y),\qquad C=T(z),
\]
and
\[
P,Q:A\to B,\qquad R:B\to C,
\qquad a,b:P\Rightarrow Q.
\]
Set
\[
F=RP,\qquad G=RQ,\qquad d_0=Ra,\qquad d_1=Rb.
\]
The new datum is the modification
\[
z=T(\zeta):d_0\Rightarrow d_1,
\]
whose component at a vertex \(e\in A\) is a genuine \(2\)-cell
\[
z_e:Ra_e\Rightarrow Rb_e
\]
in \(C\).

In the formulas below, tensors used to specify unlocalised presentations are the underlying Gray tensors. Markings are specified separately. Tensor factors remain in the indicated order.

### 1.1 Mapping cylinders and double cylinders

For a functor \(U:A\to B\), let
\[
M_U=(A\otimes I)\amalg_{A\otimes\{1\}}B.
\]

For a transformation \(d:U\Rightarrow V\), put
\[
H=A\otimes I_{\mathrm{in}},
\qquad
h_d:H\longrightarrow A\times I_{\mathrm{in}}
\xrightarrow{\operatorname{ev}_d}B,
\]
and define
\[
W_d=
A\amalg_{H\otimes\{0\}}
(H\otimes I_{\mathrm{out}})
\amalg_{H\otimes\{1\}}B.
\tag{1}
\]
The first endpoint map is the projection \(H\to A\); the second is \(h_d\). Its two inner faces are the specified cylinders \(M_U\) and \(M_V\).

Thus an unlocalised presentation over the \(2\)-skeleton of the base is
\[
\mathcal P_2=
\left(
W_a\amalg_{\,M_P\amalg_{A\amalg B}M_Q}W_b
\right)\amalg_B M_R.
\tag{2}
\]
This is the instance of the construction in item 12 that we will use.

### 1.2 The attaching map for right whiskering

For \(d=a,b\), there is an actual map
\[
\Psi_d:W_{Rd}\longrightarrow W_d\amalg_B M_R.
\tag{3}
\]

Here is its complete construction. Use the outer subdivision
\[
H\otimes I
\xrightarrow{1\otimes\delta_2}
H\otimes[2]
\simeq
(H\otimes I)\amalg_H(H\otimes I).
\]
Map the first interval to \(W_d\). Map the second by
\[
H\otimes I
\xrightarrow{h_d\otimes I}
B\otimes I
\longrightarrow M_R.
\]
At the subdivision vertex both maps are \(h_d:H\to B\). At the two outer endpoints they are the source projection and \(Rh_d\). Consequently they descend to (3).

The restrictions of \(\Psi_a\) and \(\Psi_b\) to \(M_F\) and \(M_G\) agree: those restrictions use only \(P,Q,R\), with the same outer subdivision. This agreement holds on the entire cylinders, including the cells indexed by fibre \(2\)-generators.

### 1.3 The triple cylinder for \(z\)

Let \(D_2\) have vertices \(0,1\), parallel arrows
\[
\sigma_0,\sigma_1:0\to1,
\]
and top cell
\[
\vartheta:\sigma_0\Rightarrow\sigma_1.
\]
The modification gives the evaluation
\[
\operatorname{ev}_z:A\times D_2\longrightarrow C
\]
determined by \(F,G,d_0,d_1,z\). Put
\[
H_z=A\otimes D_2,
\qquad
h_z:H_z\longrightarrow A\times D_2
\xrightarrow{\operatorname{ev}_z}C.
\]
Define
\[
W_z=
A\amalg_{H_z\otimes\{0\}}
(H_z\otimes I_{\mathrm{out}})
\amalg_{H_z\otimes\{1\}}C.
\tag{4}
\]

Its boundary obtained from \(\partial D_2\subset D_2\) is
\[
\partial W_z
=
W_{d_0}\amalg_{\,M_F\amalg_{A\amalg C}M_G}W_{d_1}.
\tag{5}
\]
The maps (3) therefore glue to an unlocalised map
\[
\Psi:\partial W_z\longrightarrow\mathcal P_2.
\tag{6}
\]

The required presentation is
\[
\boxed{\mathcal P=\mathcal P_2\amalg_{\partial W_z}W_z.}
\tag{7}
\]

Every map used in (7) has now been specified before localisation.

### 1.4 The new \(3\)-cell and its actual boundary

Write the marked transports as
\[
p_e:e\to Pe,\qquad q_e:e\to Qe,\qquad r_b:b\to Rb.
\]
Use the naturality orientation from item 20:
\[
\eta^r_f:r_b;Rf\Rightarrow f;r_{b'}.
\]
For a fibre path, extend this by
\[
\eta^r_{\ell;m}
=
(\eta^r_\ell*Rm)\cdot(\ell*\eta^r_m),
\qquad
\eta^r_{1}=1.
\]

For \(d=a,b\), let
\[
\lambda_{d,e}:p_e;d_e\Rightarrow q_e,
\]
and define
\[
L^R_{d,e}
=
(p_e*\eta^r_{d_e})\cdot
(\lambda_{d,e}*r_{Qe}).
\tag{8}
\]
With
\[
u_e=p_e;r_{Pe},\qquad v_e=q_e;r_{Qe},
\]
its type is
\[
L^R_{d,e}:u_e;Rd_e\Rightarrow v_e.
\]

The new marked \(3\)-generator is
\[
\boxed{
\chi_e:
L^R_{a,e}
\Rrightarrow
(u_e*z_e)\cdot L^R_{b,e}.
}
\tag{9}
\]
Both sides are \(2\)-cells from \(u_e;Ra_e\) to \(v_e\). Its projection is \(\zeta\).

The factor \(u_e*z_e\) is essential. It is precisely what changes when the fibres are \(2\)-categories.

### 1.5 Complete attaching maps for the \(4\)- and \(5\)-generators

The tensor prescription determines all higher boundaries, including their whiskerings.

For \(j=0,1,2\), set
\[
T_j=D_j\otimes D_2\otimes I
\]
and
\[
B_j=
(\partial D_j\otimes D_2\otimes I)
\cup
(D_j\otimes\partial D_2\otimes I)
\cup
(D_j\otimes D_2\otimes\partial I),
\tag{10}
\]
with \(\partial D_0=\varnothing\).

There is one generating cell of dimension \(j+3\) in \(T_j\):
\[
d_j\otimes\vartheta\otimes i.
\]
Let
\[
\delta_j:\partial D_{j+3}\longrightarrow B_j
\tag{11}
\]
be its Gray-computad boundary map.

For each generating \(j\)-cell \(g:D_j\to A\), attach
\[
\chi_g=g\otimes\vartheta\otimes i
\]
along
\[
\partial D_{j+3}\xrightarrow{\delta_j}B_j
\xrightarrow{\phi_g}\mathcal P^{[j-1]},
\tag{12}
\]
where \(\mathcal P^{[-1]}=\mathcal P_2\), and \(\phi_g\) is defined as follows.

- On \(\partial D_j\otimes D_2\otimes I\), use \(\partial g\) and the triple-cylinder map already constructed for the lower-dimensional fibre generators.
- On \(D_j\otimes\partial D_2\otimes I\), use \(g\) and the boundary map \(\Psi\) in (6).
- On the outer endpoint \(0\), use the projection
  \[
  D_j\otimes D_2\longrightarrow D_j\xrightarrow g A.
  \]
- On the outer endpoint \(1\), use
  \[
  D_j\otimes D_2\xrightarrow{g\otimes1}A\otimes D_2
  \xrightarrow{h_z}C.
  \]

These maps agree on their intersections. Attach the cells in increasing \(j\). This gives a finite recursive specification of every boundary in (7).

The globular tensor cells used here admit the stated cellular interpretation: products of globes are acyclic Gray atoms, and their coherent realisations agree with their strict Gray tensors by Chanavat’s Corollary 3.27 and Theorem 3.29. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Thus the new families are exactly:

| Fibre generator | New generator | Dimension | Invert? |
|---|---|---:|---|
| Vertex \(e\) | \(\chi_e\) | \(3\) | No |
| Generating arrow \(f\) | \(\chi_f\) | \(4\) | Yes |
| Generating \(2\)-cell \(\rho\) | \(\chi_\rho\) | \(5\) | Yes |

Mark all three families. Retain the fibre generators and the relative generators already present in \(\mathcal P_2\).

## 2. Mixed localisation in arbitrary finite dimensions

The following lemma proves correctness of the preceding construction and extends item 22.

### Lemma

Let \(X\) and \(Y\) have finite homotopical computad presentations. Form their **coherent cellular Gray tensor** from those presentations, with one generating cell \(x\otimes y\) for each pair of generators. Then the canonical comparison induces an equivalence
\[
\boxed{
(X\otimes Y)
\bigl[
(x\otimes y)^{-1}:\dim x>0,\ \dim y>0
\bigr]
\simeq X\times Y.
}
\tag{13}
\]

The equivalence is natural, including with respect to cellular attaching maps.

The qualification “coherent cellular” matters: the proof does not assume that an arbitrary strict tensor of polygraphs is homotopical.

### Proof, step 1: adding a mark changes the cylinder by a localisation

Suppose a marking on \(Z\) is generated by positive-dimensional cells \(M\). The underlying map
\[
Z\otimes I\longrightarrow
(Z^M\otimes I^\sharp)^\natural
\]
localises at
\[
\{m\otimes i:m\in M\}.
\tag{14}
\]

Indeed, adjoining a mark on \(m:D_r\to Z\) is a pushout of \(D_r^\flat\to D_r^t\). In Loubaton’s marked-cylinder construction, the corresponding underlying pushout replaces \(D_r\otimes I\) by \(\tau_r^i(D_r\otimes I)\), which inverts its top \((r+1)\)-generator. Marked tensoring preserves these pushouts. This is Construction 3.1.2.1 and Proposition 3.1.2.3. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### Step 2: the second factor is a globe

Fix \(X\), and argue inductively for \(Y=D_k\). The case \(k=0\) is immediate.

Put \(E=D_{k-1}\). Use the suspension presentation
\[
D_k\simeq
(E\otimes I)\amalg_{E\amalg E}(*\amalg *).
\]
Consequently,
\[
X\otimes D_k
\simeq
\bigl((X\otimes E)\otimes I\bigr)
\amalg_{(X\otimes E)\amalg(X\otimes E)}
(X\amalg X).
\tag{15}
\]

By induction,
\[
X\otimes E\longrightarrow X\times E
\]
localises at the mixed generators \(g\otimes h\) with both dimensions positive. The tensor-localisation lemma from item 9 says that tensoring this map with \(I\) localises at
\[
g\otimes h\otimes0,\qquad
g\otimes h\otimes1,\qquad
g\otimes h\otimes i.
\]
In the endpoint pushout (15), the first two families already map to identities. The remaining family is
\[
g\otimes h\otimes i,
\qquad \dim g>0,\quad \dim h>0.
\tag{16}
\]

It remains to compare the outer cylinder of \(X\times E\) with \(X\times(E\otimes I)\). Give \(X\times E\) the auxiliary marking
\[
X^\sharp\times E^\flat.
\]
This marking is generated by
\[
(g,v),
\qquad
g\text{ a positive-dimensional generator of }X,\quad v\in E_0.
\tag{17}
\]

To check that assertion, \(E\) is gaunt, so a marked \(r\)-cell has the form
\[
(a,\operatorname{id}^{(r)}b),\qquad \dim b<r.
\]
It factors as
\[
(a,\operatorname{id}^{(r)}s_0b)
*_0
(\operatorname{id}^{(r)}t_0a,\operatorname{id}^{(r)}b).
\tag{18}
\]
The second factor is an identity \(r\)-cell. The first is generated by the cells in (17), using an expression for \(a\) in the generators of \(X\).

By (14), imposing this auxiliary marking on the outer cylinder adds exactly the localisations
\[
(g,v)\otimes i.
\tag{19}
\]
Loubaton’s Proposition 3.1.3.2 identifies the resulting underlying category with
\[
X\times(E\otimes I):
\qquad
(X^\sharp\times E^\flat)\otimes I^\sharp
\simeq
X^\sharp\times(E^\flat\otimes I^\sharp).
\] :chatgpt-content-reference{index="2"}

Collapsing the two endpoints now gives \(X\times D_k\). The families (16) and (19), together, are exactly the mixed generators between \(X\) and the positive-dimensional generators of \(D_k\). This proves the globe case.

### Step 3: cellular attachment of the second factor

The Gray tensor preserves colimits in each variable; the globular tensor calculations therefore give a cellular tensor with the asserted pair generators. The required cocontinuity and compatibility with strict globular tensors follow from Campion’s Theorem 3.4 and Corollary 3.5. :chatgpt-content-reference{index="3"}

Suppose a stage of the chosen coherent presentation is
\[
Y'=Y_0\amalg_{\partial D_r}D_r.
\]
Assume the assertion for \(Y_0\), for \(D_r\), and for its boundary.

Consider a map
\[
f:X\otimes Y'\longrightarrow Z
\]
inverting the prescribed mixed generators. Its restriction to \(X\otimes Y_0\) factors through \(X\times Y_0\). By naturality of the comparison, that factorisation already inverts the images of every mixed generator from \(X\otimes\partial D_r\). Therefore the restriction to \(X\otimes D_r\) inverts all its mixed generators, including those on its boundary, and factors through \(X\times D_r\).

The two factorisations agree over \(X\times\partial D_r\): precomposition with a localisation is fully faithful on the corresponding mapping spaces. Thus \(f\) factors uniquely, in the localisation sense, through
\[
(X\times Y_0)
\amalg_{X\times\partial D_r}
(X\times D_r)
\simeq X\times Y'.
\]
This is exactly the universal property of (13). Induction over the finite cellular presentation proves the lemma. ∎

## 3. Correctness of the whiskered presentation

Apply (13) to
\[
A\otimes(D_2\otimes I).
\]
Its mixed generators are those with positive \(A\)-dimension and positive dimension in \(D_2\otimes I\).

After the endpoint pushouts defining \(W_z\), every generator
\[
g\otimes t\otimes\epsilon,
\qquad \dim g>0,\quad \dim t>0,\quad \epsilon=0,1,
\]
already maps to an identity. At endpoint \(0\) this follows from the projection; at endpoint \(1\) it follows because \(h_z\) factors through \(A\times D_2\).

The surviving localisation set is therefore
\[
S_z=
\{g\otimes t\otimes i:
\dim g>0,\ t\text{ a generator of }D_2\}.
\tag{20}
\]
Here \(t\) may have dimension \(0,1,\) or \(2\). These are precisely the existing edge and \(2\)-cell naturality generators, together with the new \(4\)- and \(5\)-generators.

Writing
\[
K=1^{\mathrm{co}}\star D_2,
\]
we obtain
\[
W_z[S_z^{-1}]
\simeq
(A\times K)\amalg_{A\times D_2}C.
\tag{21}
\]
By the suspension classification, this is the total fibration over \(D_3=\Sigma D_2\) classified by the actual evaluation \(\operatorname{ev}_z\). This is the application of Loubaton’s Corollary 4.1.2.19. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

This identification also respects the Cartesian marking. Before localisation, mark all outer-cylinder generators \(h\otimes i\). After localisation, the generators with positive fibre dimension are equivalences; those with fibre dimension zero give the marked lifts of the base cells.

We must also check the map \(\Psi\).

First, outer subdivision sends every marked outer-cylinder generator to a pasting of marked outer-cylinder generators. Second, it preserves the required localisation:

- If an inner generator is \(g\otimes v\), where \(v\) is an inner vertex and \(\dim g>0\), its image under \(h_d\) is \(P(g)\) or \(Q(g)\). Its outer cylinder is a pasting of positive-fibre naturality cells.
- If the inner generator is \(g\otimes t\) with both dimensions positive, then \(h_d(g\otimes t)\) is an identity. Its outer top cell is consequently degenerate.

Thus the localised boundary map is a map of marked Cartesian fibrations. Its evaluation is the prescribed \(Rd\), and it is the identity on the endpoint fibres. It is therefore an equivalence onto the corresponding pullback; equivalence of such maps is detected on fibres by Loubaton’s Corollary 3.2.2.8. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Finally, the base’s \(3\)-cell attachment is a homotopy pushout by item 8. Pulling this pushout back along the classified fibration and using Corollary 3.2.3.16 gives
\[
\boxed{\mathcal P[S^{-1}]\simeq\int T}
\]
over the fully marked base. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The complete generator count is therefore:

| Base generator | Fibre generators used | Total dimensions |
|---|---|---|
| \(p,q\) | \(g\in\Pi_j(A)\) | \(1+j\) |
| \(r\) | \(g\in\Pi_j(B)\) | \(1+j\) |
| \(\alpha,\beta\) | \(g\in\Pi_j(A)\) | \(2+j\) |
| \(\zeta\) | \(g\in\Pi_j(A)\) | \(3+j\) |

Here \(j=0,1,2\). Mark every displayed relative generator and invert precisely those with \(j>0\). The dimension is at most \(5\).

## 4. Extension to arbitrary \(3\)-dimensional bases

### Theorem: \(\mathrm{FT}_{3,m}\)

Let \(\Gamma\) be a finite \(3\)-computad such that:

1. its \(2\)-skeleton is homotopical;
2. adjoining its \(3\)-generators is a homotopy pushout.

Let the fibres have finite homotopical \(m\)-computad presentations. Then the relative Gray-generator presentation exists in dimension at most
\[
m+3.
\]
Besides the fibre generators, it has one marked generator of dimension \(k+j\) for every base \(k\)-generator, \(k=1,2,3\), and every source-fibre \(j\)-generator. Invert precisely those with \(j>0\).

### Proof

Item 12 supplies the presentation \(\mathcal P_2\) over the \(2\)-skeleton.

For each \(3\)-generator
\[
\Omega:s\Rrightarrow t,
\]
choose finite expressions for its two \(2\)-cell boundaries. We require actual maps
\[
W_{T(s)}\longrightarrow\mathcal P_2,
\qquad
W_{T(t)}\longrightarrow\mathcal P_2
\tag{22}
\]
agreeing on their two path-cylinder boundaries.

These maps are obtained recursively by the following operations.

**Identities.** Collapse the inner interval. This sends the double cylinder of an identity transformation to its mapping cylinder.

**Vertical composition.** Apply
\[
I_{\mathrm{in}}\xrightarrow{\delta_2}[2]
\]
and glue the double cylinders of the two transformations along their common mapping cylinder.

**Right whiskering.** Use the outer subdivision (3), in arbitrary fibre dimension.

**Left whiskering.** Suppose \(F:D\to A\) and \(d:U\Rightarrow V\) has source fibre \(A\). Put \(H_D=D\otimes I_{\mathrm{in}}\). Subdivide
\[
H_D\otimes I_{\mathrm{out}}\longrightarrow H_D\otimes[2].
\]
Map the first interval through
\[
H_D\otimes I\longrightarrow D\otimes I\longrightarrow M_F
\]
using the inner projection. Map the second through
\[
H_D\otimes I
\xrightarrow{(F\otimes I_{\mathrm{in}})\otimes I}
(A\otimes I_{\mathrm{in}})\otimes I
\longrightarrow W_d.
\]
At the subdivision vertex both maps are \(F\) after the inner projection. This gives
\[
W_{dF}\longrightarrow M_F\amalg_A W_d.
\]

Horizontal composition is expressed using whiskering and vertical composition.

The restrictions of these operations to a path boundary are the path-cylinder maps of item 12. They depend on the resulting path: successive subdivisions compose to the single map
\[
\delta_r:I\to[r].
\]
Consequently the two maps in (22) agree on their complete common path cylinders, in every fibre dimension.

For each \(\Omega\), now use the triple cylinder (4), evaluated by the genuine modification \(T(\Omega)\), and attach it along (22). Its relative generators are
\[
g\otimes\vartheta\otimes i,
\qquad \dim g+3\leq m+3,
\]
with the boundary prescription (10)–(12).

The marking and localisation checks in §3 apply without a bound of \(2\) on the fibre dimension. In particular, the evaluation of a positive-positive mixed generator is an identity because the evaluation factors through a Cartesian product.

After localisation, all these maps are the boundary maps of the corresponding classified local totals. The assumed base pushout and pullback-preserves-colimits then identify their pushout with \(\int T\). ∎

This proof uses one chosen expression for each attaching \(2\)-cell. It does not require the unlocalised presentation to identify the maps produced by every pair of expressions related by interchange. The compatibility required for a \(3\)-cell attachment is compatibility on its common **\(1\)-dimensional** boundaries, and the path-cylinder construction supplies exactly that.

## 5. Suspension bases with arbitrary finite-dimensional fibres

The mixed-localisation lemma also removes the fibre-dimension restriction from item 24.

Let
\[
Q=F_d(\Lambda),\qquad B=\Sigma Q,\qquad n=d+1,
\]
with \(\Lambda\) finite and homotopical. Let the two fibres \(A,C\) have finite homotopical \(m\)-computad presentations, and write the weight as its evaluation
\[
h:A\times Q\longrightarrow C.
\]
Put
\[
K=1^{\mathrm{co}}\star Q.
\]

The cone has the cellular presentation consisting of the generators of \(Q\), its apex, and one generator
\[
\kappa_q,\qquad \dim\kappa_q=\dim q+1,
\]
for each generator \(q\) of \(Q\). This follows by applying the cylinder-and-endpoint-collapse construction to the chosen cellular presentation of \(Q\).

Form the unlocalised pushout
\[
\boxed{
\mathcal P_T=(A\otimes K)\amalg_{A\otimes Q}C,
}
\tag{23}
\]
where the attaching map is the actual composite
\[
A\otimes Q\longrightarrow A\times Q\xrightarrow h C.
\]

The relative generators are
\[
g\otimes\kappa_q,
\qquad
\dim(g\otimes\kappa_q)=j+i+1,
\]
for \(g\in\Pi_j(A)\) and \(q\in\Lambda_i\). Mark all of them and invert those with \(j>0\).

The mixed generators belonging to \(A\otimes Q\) already map to identities in \(C\). Therefore (13), followed by the pushout, gives
\[
\mathcal P_T[S^{-1}]
\simeq
(A\times K)\amalg_{A\times Q}C
\simeq
\int_{\Sigma Q}T.
\tag{24}
\]
The final equivalence is the same suspension classification used in (21). The dimension bound is
\[
i+1+j\leq d+1+m=n+m.
\]

Thus **\(\mathrm{FT}_{n,m}\) holds for finite homotopical suspension bases, for every finite \(m\)**.

## 6. The finite certificate and the remaining scope

For the two classes just proved—bases of dimension at most \(3\), and suspension bases—the finite certificate consists of:

1. **Homotopicality certificates** for the chosen fibre presentations and the required base attachments.
2. **Weight data**, given by the finite evaluation maps on the relevant cellular presentations, with derivations of their boundary equations.
3. **Attaching expressions**, using the cylinder substitutions above; for \(3\)-bases these include chosen expressions for the \(2\)-cell boundaries.
4. **The generator list**, indexed by the prescribed base–fibre pairs, with dimension \(k+j\).
5. **The marking and localisation lists**: mark all relative generators and invert exactly those of positive fibre degree.
6. **Face-compatibility checks**, verifying the maps on the intersections in (10) and on the common path cylinders.

This is a finite certificate for the stated construction. It does not require a decision procedure for arbitrary homotopicality or arbitrary equality problems: where an equality is needed, the certificate supplies a finite derivation.

For general bases of dimension \(n\geq4\), the unresolved step is now specifically the compatible substitution of higher-dimensional boundary expressions into the unlocalised presentations. The mixed-localisation lemma supplies the local tensor models and their dimension bounds, but does not establish that compatibility.

I have no proof or counterexample for bubble-free or one-sided \(2\)-computads, including
\[
(*;s,t;\eta:1\Rightarrow st,\ \mu:ts\Rightarrow t).
\]
I also have none for positivity in every dimension in the \(3\)-dimensional question. Chanavat’s Comment 3.40 describes the extension to arbitrary regular and positive polygraphs as an expected extension; it does not prove that case. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)


# Verification of the researcher response (2026-11-18)

**Verdict: correct at the level of a paper proof.**
- **Question 1 is answered.** Item 8's ζ admits 2-category fibres, with generators of dimension ≤ 5.
  - The triple cylinder W_z (4) is attached along Ψ (6).
  - The new generators are χ_e (dim 3, marked), χ_f (dim 4, inverted) and χ_ρ (dim 5, inverted), with χ_e : L^R_{a,e} ⇛ (u_e ∗ z_e) · L^R_{b,e}.
- **General mixed-localisation lemma (13)** for finite homotopical X and Y.
- **FT_{3,m}** holds for 3-dimensional bases satisfying item 23's hypotheses, with generators of dimension ≤ m + 3.
- **FT_{n,m}** holds for suspension bases, for every m.

Checked:

1. **Attaching data.** The boundary of χ_e is well typed. Both sides go from the left-whiskered to the right-whiskered lift over e. χ_f and χ_ρ fill the next two boundaries of the triple cylinder.
   - The dimension count is dim fibre (2) + dim base cell + 1, which gives ≤ 5.
   - This matches the r2 pattern (one Ω_ρ per fibre 2-cell) lifted one cylinder level.
2. **Lemma (13).** It generalises the r5 𝓡_A(X) to arbitrary finite homotopical X and Y. The proof is the tensor-localisation lemma of r2 applied factorwise. The finiteness and homotopicality hypotheses are exactly the ones used.
3. **FT_{3,m}.** The left/right whiskering subdivisions reduce every 3-generator of the base to a cylinder over its 2-dimensional boundary data, where the r3 2-dimensional theorem applies. Item 23's hypotheses are what make the subdivision finite.
4. **Suspension bases.** These reduce to the hom-level case via Loubaton Cor. 4.1.2.19 and 3.2.3.16, as in r4, now for all fibre dimensions.

**Open.**
- General n ≥ 4. The obstacle is compatible substitution of higher boundary expressions.
- Whether bubble-freeness is sufficient.
- One-sided 2-computads beyond the partition test (for example η : 1 ⇒ st, μ : ts ⇒ t).
- Positive 3-computads.

Follow-up: no incremental round-7 prompt. The open items pass to the consolidation thread ("Consolidate researcher prompts into ambitious asks").
