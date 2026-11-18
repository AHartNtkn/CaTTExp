# Problem: finite presentations of cartesian fibrations over a 2-dimensional base

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and 2-categorical Grothendieck constructions, and nothing else. The questions are in §4, smallest first.*

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

## 2. What is known

1. **Localisation lemma (Loc), proved.** Let S be a set of marked positive-dimensional cells of a marked (∞,ω)-category J, and q : J → J[S⁻¹]. For every diagram F̄ on J[S⁻¹], restriction is an equivalence of whole (∞,ω)-categories of marked cones, natural in the apex: `Cone^m_{J[S⁻¹]}(c, F̄) ≃ Cone^m_J(c, F̄ q)`.
   - *Proof:* q is a pushout of Loubaton's generating trivialisations `D_{k+1}^t → D_k^♭`, so it is initial and final (Def. 3.2.1.6, Prop. 3.2.1.7). Then apply Lemmas 4.2.3.15 and 4.2.3.23.
   - So a marked index cell that every diagram sends to an equivalence may be inverted without changing marked lax limits.
2. **Base a graph: solved.** Let Γ be a finite graph, so `Free(Γ)` is the free category on it. A finite datum **FT₂** consists of:
   - fibre graphs `G_b`, one per vertex b, whose edges are the *vertical* generators (unmarked);
   - for each base edge u : b → c and each vertex e of G_b, a *horizontal* marked generator `u_e : e → T_u(e)`;
   - for each vertical β : e → e′ and each base edge u, a marked 2-generator `θ_{u,β} : β ; u_{e′} ⇒ u_e ; T_u(β)`, where `T_u(β)` is a path in G_c (possibly empty);
   - nothing else.

   With marking μ = horizontals ∪ θ's, `Free(Ψ)^μ[θ⁻¹] → Free(Γ)^♯` is a left cartesian fibration. It is equivalent to the Grothendieck construction of the functor `T : Free(Γ) → Cat` that the data define. Every weight `Free(Γ) → Cat` with values free on finite graphs has such a presentation. By (Loc), weighted limits may be computed over the *unlocalised* computad. Vertical generators must be unmarked: a marked vertical arrow over a point is a counterexample.
3. **What a base 2-generator needs** (proved necessary). Let α : u ⇒ v, with u, v : b → c paths in Γ, and let T send α to a natural transformation `a_α : T_u ⇒ T_v`.
   - For each fibre vertex e over b, there is a vertical path `a_{α,e} : T_u(e) → T_v(e)` with, for each vertical generator β : e → e′, the **path equality**
     ```
     T_u(β) ; a_{α,e′}  =  a_{α,e} ; T_v(β).                               (16)
     ```
   - Let `τ_{u,e}` be the composite of horizontal lifts along the path u, and `θ_{u,β} : β;τ_{u,e′} ⇒ τ_{u,e};T_u(β)` the pasted comparison. The marked cartesian lift of α at e must have **prescribed target**:
     ```
     λ_{α,e} :  τ_{u,e} ; a_{α,e}  ⇒  τ_{v,e}.                              (17)
     ```
     This matches the strict Grothendieck construction (Hörmann, *Six functor formalisms and fibered multiderivators*, Def. 2.14 and Prop. 2.16): a 2-cell `(u, r) ⇒ (v, s)` over α exists iff `r = a_{α,e} ; s`. λ projects to α, so it need not be invertible.
   - Naturality of the lifted 2-cell requires, for each (α, β), the **3-dimensional relation**
     ```
     (θ_{u,β} ⋆ a_{α,e′}) ; (λ_{α,e} ⋆ T_v(β))  =  (β ⋆ λ_{α,e′}) ; θ_{v,β},     (19)
     ```
     both sides running from `β;τ_{u,e′};a_{α,e′}` to `τ_{v,e};T_v(β)`.
   - **Without (19) the λ's are not cartesian.** Take u, v : 0 → 1, α : u ⇒ v, fibres `x →h y` and `z →k w`, T_u = T_v, and a_α = id. The two pastings `θ_u;(λ_x⋆k)` and `(h⋆λ_y);θ_v` have λ-counts (1,0) and (0,1). Counting λ's is a 2-functor to ℤ² that inverting θ preserves. So they are distinct, and the second does not factor through the first over an identity.
4. **Strict references.** Hörmann Def. 2.14; Gurski–Johnson–Osorno, *2-categorical opfibrations, Quillen's Theorem B, and S⁻¹S*, Def. 2.14 (mixed-variance 2-opfibrations); Warren, *The strict ω-groupoid interpretation of type theory*, §3 and App. B (strict ω-categorical Grothendieck construction). These give constructions and axioms, not finite recognition theorems for polygraph presentations.

## 3. The candidate FT₃

Let Γ be a finite 2-computad. Let B be the free **strict** 2-category on Γ, viewed as an (∞,ω)-category, and give it the marking B^♯. Let T : B → Cat be a strict 2-functor whose values are free categories on finite graphs `G_b`. T is determined by finite data: the paths T_u(β) for base edges u, and the paths a_{α,e} satisfying (16) for base 2-generators α.

**The presentation Ψ_T** has:
- the generators of §2 item 2 (vertical, horizontal `u_e`, comparisons `θ_{u,β}`), for the base *edges*;
- for each base 2-generator α and each fibre vertex e over its source, a 2-generator `λ_{α,e}` as in (17);
- for each base 2-generator α and each vertical generator β over its source, a 3-generator `Ξ_{α,β}` between the two sides of (19).

π sends vertical generators, θ's and Ξ's to identities, `u_e` to u, and `λ_{α,e}` to α.

**Marking:** μ = horizontals ∪ θ's ∪ λ's ∪ Ξ's. Vertical generators are unmarked.

**Localisation:** S = θ's ∪ Ξ's, the marked cells over identities.

**Conjecture FT₃.** `Free(Ψ_T)^μ[S⁻¹]` is equivalent over B^♯, as a marked (∞,ω)-category, to the marked Grothendieck construction of T. In particular it is a left cartesian fibration over B^♯. By (Loc), weighted limits with weight T can then be computed over the finite, unlocalised marked computad Ψ_T.

## 4. Questions

1. **Is the base right?** Let Γ be a finite 2-computad. Is `Free(Γ)`, the free (∞,ω)-category, equivalent to the free strict 2-category F₂(Γ)? If not in general, under what condition on Γ? A natural candidate condition is that no 2-generator has an identity 1-cell in its boundary, which rules out Eckmann–Hilton braidings. If the answer is no, take B := F₂(Γ) as the base and present π as a map `Free(Ψ) → B`, as in §3.
2. **Smallest case.** Let Γ = (u, v : 0 → 1, α : u ⇒ v), with fibres free on finite graphs. Prove or refute FT₃.
   - The specific worry: Free(Ψ_T) is a free *weak* structure. Its interchange and associativity cells between λ's and θ's are invertible but not identities, so they could leave non-trivial 3-cells after inverting S. ∫T is a (2,2)-category.
   - Is inverting the Ξ's enough to make the hom maps of `Free(Ψ_T)^μ[S⁻¹]` equivalent to those of ∫T?
3. **General 2-computad bases.** Prove FT₃ for every finite 2-computad Γ satisfying question 1's condition. This includes composite boundary paths u, v and base 2-cells whose boundaries share edges.
4. **Completeness.** Is every strict 2-functor T : F₂(Γ) → Cat with values free on finite graphs presented by some FT₃ datum? The data (16) are finitely many path equalities, so this should reduce to question 3.
5. **Higher.** Is there a finite criterion FT_n for bases that are n-computads and weights valued in free n-categories, alternating the variance in each dimension? If not, give an obstruction.

## 5. Literature search (2026-11-18)

- Loubaton (arXiv 2406.05425): exact infinite criterion (★); localisation via marked trivialisations (Def. 3.2.1.6, Prop. 3.2.1.7); cones (Lemmas 4.2.3.15, 4.2.3.23).
- Hörmann, Gurski–Johnson–Osorno and Warren (above): strict constructions and axioms.
- Abellán–Haugseng–Martini (arXiv 2602.07604) and Gagna–Harpaz–Lanari (arXiv 2012.04537): (∞,2)-dimensional fibrations and partially lax limits. No generator-level criteria.
- **Nothing found** on finite recognition of cartesian fibrations between polygraph-presented higher categories, nor on when the free weak ω-category on a 2-computad is equivalent to the free strict 2-category (question 1).

## 6. What would count as an answer

Any one of:
- an answer to question 1;
- a proof or counterexample for question 2;
- a corrected FT₃ with a proof;
- an obstruction showing that no finite presentation scheme of this kind can work over 2-dimensional bases.
