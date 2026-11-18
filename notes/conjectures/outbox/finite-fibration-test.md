# Problem: a finite test for when a map of computads presents a cartesian fibration

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product and computads (polygraphs), and nothing else. The questions are in §4, smallest first.*

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (F. Loubaton, *Categorical theory of (∞,ω)-categories*, [arXiv 2406.05425](https://arxiv.org/abs/2406.05425)).

- A **marked** (∞,ω)-category is one with a chosen class of positive-dimensional cells. The class contains the equivalences and is closed under composition.
  - A^♯ marks every cell, and A^♭ marks only the equivalences.
  - D_n is the n-globe, and D_n^t is the n-globe with its top cell marked.
  - ⊗ is the marked Gray tensor product.
- **Left cartesian fibrations** (Loubaton Def. 3.2.2.1). A map p : E → B is a left cartesian fibration if it has the *unique* right lifting property against

  ```
  K ⊗ {0} → K ⊗ [1]^♯,        K ∈ { D_n^♭ : n ≥ 0 } ∪ { D_n^t : n ≥ 1 }.        (★)
  ```

  Equivalently (Thm 3.2.2.24(5)), three conditions hold:
  1. Every 1-cell of B has a marked lift with prescribed source, unique up to a contractible space.
  2. For every marked u : x → x′ and every z, `E(x′, z) ≃ E(x, z) ×_{B(px, pz)} B(px′, pz)`.
  3. Every hom map `E(x, y) → B(px, py)` is a *right* cartesian fibration (the dual notion, lifting from endpoint 1).

  Condition 3 makes the variance **alternate with dimension**: cocartesian 1-cells, cartesian 2-cells, cocartesian 3-cells, and so on.
- **Straightening** (Loubaton Thm 4.1.4.2). Left cartesian fibrations over B^♯ correspond to functors B → ω, where ω is the (∞,ω)-category of (∞,ω)-categories.

### 1.2 Computads with markings

- A **finite computad** Ψ is a finite list of generating cells. Each generator has a boundary built from earlier generators. `Free(Ψ)` is the free weak ω-category on Ψ.
- A **map** `π : Ψ → Γ` sends each generator of Ψ to a cell of `Free(Γ)`. That cell may be an identity.
- A **marking** μ is a subset of the positive-dimensional generators of Ψ. It generates a marking of `Free(Ψ)` by closure under identities, composites and equivalences. No condition on μ is needed for this closure to make sense.

### 1.3 Why such maps matter

Let W : I → ω be a weight and F : I → 𝒞 a diagram. The W-weighted limit of F is the **marked lax limit** of F∘p over the total space ∫W, where p : ∫W → I is the left cartesian fibration classifying W, with its fibration marking. This holds in Loubaton's model, in all dimensions (via Cor. 4.2.2.6, Cor. 4.2.3.18 and Thm 4.1.4.2). In a marked lax limit, marking a k-cell of the index makes the corresponding (k+1)-dimensional cone cell invertible (Remark 4.2.3.7).

So if a weight is presented by a finite computad map `(π : Ψ → Γ, μ)`, the weighted limit becomes a marked lax limit over Ψ. A proof checker can then accept weighted limits, provided it can check that π presents a left cartesian fibration. (★) is exact, but it is an infinite schema.

## 2. What is known

1. **(★) is exact but infinite.** It quantifies over all globes and all lifting problems in `Free(Ψ)`.
2. **Existence of marked lifts of generators is not enough.** Let I = (0 → 1), and let E be the free category on arrows u : x → y and v : x → z, both sent to the generator. A lift exists at x, but u is not cocartesian, since factoring v through u needs an arrow y → z.
3. **Solved: set-valued weights over graphs.** Let Γ and Ψ be graphs, π send vertices to vertices and edges to edges, and every edge of Ψ be marked. Then (★) holds **iff π is a discrete opfibration of graphs**: for every vertex e of Ψ and every edge u of Γ out of π(e), there is exactly one edge of Ψ over u out of e.
   - *Proof.* Unique edge lifting gives unique path lifting. The free weak ω-category on a graph is equivalent to the free 1-category on it, because the comparison map is a trivial fibration (via Leinster, Dean–Finster–Markakis–Reutter–Vicary, and Benjamin–Markakis). So homs are discrete and condition 3 is trivial. Condition 2 is unique factorisation. For the converse, a lift of a length-1 path must be a single edge.
   - *Completeness.* Every functor Free(Γ) → FinSet has a presentation of this form, since its category of elements is free on the covering graph.
4. **Where it gets hard.** Let `W : Free(Γ) → Cat`, with Γ a graph.
   - The total space ∫W is a 1-category in which squares `β ; u_{e′} = u_e ; W(u)(β)` commute. Here β : e → e′ is a vertical arrow in a fibre, and u_e is the marked lift of u at e.
   - So ∫W is **not free**. A computad presentation needs 2-generators `θ_{u,β}` filling these squares, and they must be marked: they are the "cartesian 2-cells" of the alternating pattern.
   - Since `π(θ_{u,β})` is an identity, marking θ makes its cone cell invertible. The marked lax limit should therefore not see the difference between θ and an invertible cell. That is not proved.

## 3. The candidate

**FT₂.** Let Γ be a graph and Ψ a computad of dimension ≤ 2, with a map π : Ψ → Γ and a marking μ. Say (π, μ) satisfies FT₂ if:
1. π sends each 1-generator to an edge or an identity (call these *horizontal* and *vertical*), and each 2-generator to an identity.
2. For each vertex e of Ψ and each edge u of Γ out of π(e), there is exactly one marked horizontal generator `u_e` over u out of e.
3. For each vertical generator β : e → e′ and each such u, there is exactly one marked 2-generator `θ_{u,β} : β ; u_{e′} ⇒ u_e ; t_{u,β}`, where t_{u,β} is a vertical path (the *transport*).
4. There are no other generators.

**Localisation lemma (Loc).** Let J be a marked (∞,ω)-category and θ a marked k-cell, k ≥ 2, sent to an equivalence by every diagram under consideration. Then marked lax limits over J and over J[θ⁻¹] agree. In J[θ⁻¹], the inverse of θ and its witnesses are marked.

*Sketch.* A marked cone over J has an invertible cone cell over θ. It extends to J[θ⁻¹] by inverting that cell, and the space of extensions should be contractible.

## 4. Questions

1. **(Loc)** Prove or refute the localisation lemma. Start with k = 2 and J a 2-category.
2. **FT₂.** Show that FT₂ implies that `Free(Ψ)^μ[θ⁻¹] → Free(Γ)^♯` is a left cartesian fibration, where θ ranges over the marked 2-generators. With (Loc), this means FT₂ correctly presents Cat-valued weights. Is every weight `Free(Γ) → Cat` with values free on finite graphs presented by some FT₂ datum?
3. **Higher bases.** Extend the criterion to a base Γ with 2-generators. A 2-generator α : u ⇒ u′ of Γ needs lifted 2-cells between the lifts u_e and u′_e, with the variance of condition 3 in §1.1 (cartesian on hom maps).
4. **All dimensions.** Is there a finite criterion FT_n for weights valued in free n-categories, alternating the variance in each dimension? If not, give an obstruction. For example, transports might fail to be finitely presentable.
5. **Strict analogue.** For strict ω-categories and polygraphs, with Grothendieck fibrations of strict ω-categories, is there a known finite criterion? A reference would answer questions 2–4 in the strict setting.

## 5. Literature search (2026-11-18)

- **Loubaton** (arXiv 2406.05425): the exact criterion (Def. 3.2.1.1, Def. 3.2.2.1, Thm 3.2.2.24), stated for arbitrary marked (∞,ω)-categories. It gives no computad-level test.
- **Abellán–Haugseng–Martini** (arXiv 2602.07604) and **Gagna–Harpaz–Lanari** (arXiv 2012.04537): (∞,2)-dimensional fibrations and partially lax limits. Generator-level criteria are not discussed.
- That discrete opfibrations over a free category are free on a covering graph is folklore for 1-categories.
- **Nothing found** on finite criteria for cocartesian fibrations between free higher categories presented by polygraphs.

## 6. What would count as an answer

Any one of:
- a proof of (Loc);
- a proof of FT₂ ⟹ (★), possibly after localisation;
- a different finite criterion, with a proof that it implies (★);
- a proof that no finite criterion is complete for Cat-valued weights.
