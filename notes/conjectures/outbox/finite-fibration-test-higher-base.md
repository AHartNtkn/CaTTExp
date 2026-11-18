**Status: unsent** (written 2026-11-18; follows `answered/finite-fibration-test-2d-base-2026-11-18.md`).

# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n)

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. The questions are in §4, smallest first.*

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

## 3. The shape of FT_n

For a base n-computad Γ and a weight T valued in free m-categories, the natural candidate adds, for each base k-generator and each fibre generator, a marked lift with prescribed target (in odd fibre dimensions) or source (in even ones), following the alternating variance of §1.1, plus one marked (k+1)-generator for each naturality square, and inverts the generators lying over identities.

## 4. Questions

1. **Smallest new case: a 3-dimensional base, Cat-valued weight.** Let Γ be the walking 3-cell (u, v : 0 → 1, α, β : u ⇒ v, Ω : α ⇛ β), which is regular and positive. A strict functor T : F₃(Γ) → Cat with free values must send Ω to an identity, so a_α = a_β. Which generators over Ω present ∫T (one marked 3-generator λ_{α,e} ⇛ λ_{β,e} per fibre vertex?), and does inverting the cells over identities give the right homs?
2. **2-dimensional base, 2-category-valued weight.** Let Γ = (u, v : 0 → 1, α : u ⇒ v) and T valued in free 2-categories on finite 2-computads (positive ones). Give the FT data (lifts of fibre 2-cells with the alternating variance) and prove or refute that it presents ∫T.
3. **General FT_n over regular bases.** For a finite regular (or positive, in a suitable sense) n-computad Γ, so that Free(Γ) is the free strict n-category, give a finite criterion FT_n and prove it, or give an obstruction.
4. **Necessity of the hypothesis.** Is regularity (or positivity) also necessary for a finite presentation in dimension ≥ 3? The finite-CW argument of §2 item 4 shows necessity whenever the strict free object has infinite homological dimension after groupoidification. Is there a non-regular 3-computad whose strict free object nevertheless has a finite presentation?

## 5. What would count as an answer

A proof or counterexample for any question; a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs.
