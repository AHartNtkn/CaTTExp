# Grothendieck constructions over free bases: which bases admit Gray-generator presentations, and a uniform localised presentation

*A self-contained problem. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, polygraphs (computads) and Grothendieck constructions, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** Two exact answers valid in **every** dimension:
- a characterization of the bases (and weights) for which the relative Gray-generator presentation of §2, or any presentation of bounded dimension, presents the fibration;
- one uniform, explicitly described localised presentation that works for every homotopical base.

The expected presentation is now known to fail from base dimension 4 (§3 item 9), and existence of *some* finite presentation is known (item 10). Neither is the answer: the counterexample is one shape, and the existence proof goes through complicial models with no control on generators or dimension. A further counterexample, or a further special class, is not what we want.

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (*Categorical theory of (∞,ω)-categories*, arXiv 2406.05425).
- A **marked** (∞,ω)-category has a chosen class of positive-dimensional cells containing the equivalences and closed under composition. A^♯ marks every cell. D_n^t is the n-globe with its top cell marked. ⊗ is the marked Gray tensor.
- A map p : E → B is a **left cartesian fibration** (Def. 3.2.2.1) when it has the unique right lifting property against `K ⊗ {0} → K ⊗ [1]^♯` for `K ∈ {D_n^♭ : n ≥ 0} ∪ {D_n^t : n ≥ 1}`. Straightening (Thm 4.1.4.2) identifies left cartesian fibrations over B^♯ with functors B → ω (the (∞,ω)-category of (∞,ω)-categories). The fibration classifying T is written ∫T.

### 1.2 Polygraphs and localisation

- For a finite polygraph Ψ, `Free(Ψ)` is the free (∞,ω)-category on Ψ and `F(Ψ)` the free strict ω-category. Ψ is **homotopical** when the comparison Free(Ψ) → F(Ψ) is an equivalence. `F_m(Π)` is the free strict m-category on an m-polygraph Π.
- A marking is a set of generators. `J[S⁻¹]` is the localisation of J at a set S of cells.
- A **presentation** of a fibration p : E → B over a polygraph base Γ is a finite marked polygraph Ψ with a map to Γ and a set S of marked generators such that `Free(Ψ)[S⁻¹] → Free(Γ)` is equivalent to p.

### 1.3 Why it matters

A W-weighted limit of a diagram F is the marked lax limit of F ∘ p over the total space of the fibration p classifying W (Loubaton, Cor. 4.2.2.6, Cor. 4.2.3.18). If p has a finite presentation with a finite correctness certificate, a proof checker can accept the weighted limit as a marked lax limit over a finite index. So a theorem for all dimensions gives checkable weighted limits for every finite weight with free values over every homotopical finite base.

## 2. The expected answer

For a base n-polygraph Γ and a strict weight T : F(Γ) → strict ω-categories with each value T(b) = F_m(Π_b), Π_b finite and homotopical, the expected presentation is the **relative Gray-generator presentation**:
- the generators of every fibre Π_b over the base vertices b;
- for each base k-generator q (k ≥ 1) with source vertex b and each j-generator g of Π_b, one marked generator `q ⊗ g` of dimension k + j, with boundary given by the Leibniz formula `∂(q ⊗ g) = ∂q ⊗ g ± q ⊗ ∂g`, read through T;
- localisation at the generators q ⊗ g with j > 0.

So the presentation has dimension ≤ n + m.

## 3. What is known

1. **Localisation lemma.** If S is a set of marked cells of J and q : J → J[S⁻¹], restriction is an equivalence of (∞,ω)-categories of marked cones, natural in the apex.
2. **Tensor-localisation and mixed localisation.** For any set S of positive-dimensional cells, `X[S⁻¹] ⊗ I ≃ (X ⊗ I)[{s ⊗ 0, s ⊗ 1, s ⊗ i}⁻¹]`. For finite homotopical X and Y there is a finite cellular model 𝓡_Y(X), natural in X, with one generator x ⊗ y per pair of generators, and `𝓡_Y(X)[(x ⊗ y)⁻¹ : dim x, dim y > 0] ≃ X × Y`.
3. **Bases of dimension ≤ 2.** For every finite homotopical 2-polygraph base and fibres F_m(Π_b) with Π_b finite homotopical, the expected presentation is correct. Proof: for a base path p = e₁; …; e_r the map δ_r : I → [r] (0 ↦ 0, 1 ↦ r) and A ⊗ [r] ≃ (A ⊗ I) ∐_A ⋯ ∐_A (A ⊗ I) give a map from the cylinder of T(p) into the **unlocalised** graph presentation; attach a double Gray cylinder block for each base 2-generator along these maps; conclude with Loubaton's theorem that pullback preserves colimits (Thm 3.2.3.15, Cor. 3.2.3.16).
4. **Bases of dimension 3.** For a finite 3-polygraph base Γ such that Γ and its 2-skeleton are homotopical (more precisely: the 2-skeleton is homotopical and attaching the 3-generators is a homotopy pushout), the expected presentation is correct for every fibre dimension m, with generators of dimension ≤ m + 3. The 3-generators of the base are handled by left and right whiskering subdivisions of the outer interval, which reduce each 3-generator to a cylinder over its 2-dimensional boundary data, where item 3 applies.
5. **Suspension bases.** For Q = F_d(Λ) with Λ finite homotopical and base ΣQ, the expected presentation is correct for every fibre dimension, via K = 1^co ⋆ Q and the suspension-base classification (Loubaton, Cor. 4.1.2.19).
6. **The obstacle in base dimension ≥ 4.** Gluing the local totals over the base generators gives the right generators. But the attaching maps are first obtained in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself, and such lifts need not exist (in Free(s)[s⁻¹] the inverse of s exists; in Free(s) no arrow goes back). For bases of dimension ≤ 3 the lifts were constructed by hand, by subdividing cylinders along composites in the boundary of each generator. For base dimension ≥ 4 what is missing is a **compatible** choice of such lifts for all higher-dimensional boundary expressions at once.
7. **A finite certificate exists for the proved cases:** homotopicality certificates for the fibres and base attachments, the weight data, the attaching expressions, the generator list indexed by base–fibre pairs, the marking and localisation lists, and face-compatibility checks on the intersections of the cylinders.
8. **Homotopicality of the base is needed.** For the base (x; σ : 1_x ⇒ 1_x), F(Γ) = B²ℕ groupoidifies to K(ℤ,2), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight has no finite presentation.
9. **The expected presentation fails from base dimension 4.** Base Γ: one vertex b, a : b → b, μ : aa ⇒ a, an associator α : (μ₁;μ₀) ⇛ (μ₀;μ₀) (words in right-to-left order; a subscript is the position of the rewrite), and a pentagon 4-generator P. Fibre Π: x, g : x → x, δ : g ⇒ gg, κ : (δ₀;δ₁) ⇛ (δ₀;δ₀). Weight: T(b) = F₃(Π), T(a) = Z the constant functor at x, T(μ)_x = g, T(α)_x = δ, T(P)_x = κ.
   - Both polygraphs and all their skeleta are homotopical: Π is the oriental polygraph of the semisimplicial set with one simplex in each dimension ≤ 3, and Γ is the even dual of the one for dimension ≤ 4 (Chanavat, arXiv 2603.22242, Thm 3.35).
   - With the fibre-first Leibniz convention ∂(g ⊗ q) = ∂g ⊗ q + (−1)^{|g|} g ⊗ ∂q, the mixed generators are t = a ⊗ x, c : t ⇒ tg, u : gtt ⇒ t, and the 3-generators D = a ⊗ δ, M = μ ⊗ g : (u₀;c₀) ⇛ (c₂;u₀), V = α ⊗ x : (c₁;u₂;u₀) ⇛ (δ₀;u₁;u₀), together with κ.
   - The 2-cells gt⁴ ⇒ t are 8 (18 rewriting paths up to interchange). Every contextual instance of a 3-generator gives exactly 8 edges. Over the short side R → E → L of the pentagon, the only V-step out of the lift of R lands at a vertex with no outgoing edge. So the target face of P ⊗ x does not exist in the unlocalised category: it would need M⁻¹, which exists only after localisation. No weak attaching map can repair this, since it would project to the missing strict 3-cell.
   - Reversing M repairs this pentagon but changes M's Gray boundary.
10. **Finite presentations exist, with auxiliary generators.** For every finite polygraph Γ with homotopical skeleta, and every (∞,ω)-functor T : F(Γ) → ω whose values have finite weak polygraphic presentations (localisations allowed), ∫T has a presentation (Free(Ψ), ⟨Q ∪ S⟩)[S⁻¹] with Ψ finite and homotopical and Q, S finite sets of positive-dimensional generators, keeping the cartesian marking. The proof gives no dimension bound and no control of the generators. It goes through finite complicial models: closure under finite homotopy pushouts and products, and a conversion L_d of a finite stratified simplicial set into a finite semisimplicial set whose oriental polygraph is homotopical. It then inducts over the base cells with Loubaton's pullback–colimit theorem and the suspension classification for globes. For weights whose values are ≃ F(Π_b), the weight can moreover be made strict, since the homs of ω between gaunt strict categories are gaunt.
11. **Homotopicality of the base passes to skeleta.** The inclusion F(Γ_{≤r}) ↪ F(Γ) is discrete Conduché (the generator support of a strict cell is well defined and additive), so pulling back along it preserves colimits (Loubaton Thm 2.2.2.10), and the comparison for Γ_{≤r} is a pullback of the comparison for Γ. Hence Γ is homotopical iff all its skeleta are.

## 4. Questions

**Question 1 (main: characterization).** For which finite homotopical polygraphs Γ (and strict weights T with values F_m(Π_b), Π_b finite and homotopical) is the relative Gray-generator presentation of §2 well defined, meaning that every generator q ⊗ g has an attaching map in the unlocalised Free(Ψ), and correct? Give an exact criterion that can be checked on finite data in every dimension. Two natural forms:
- (a) a condition on Γ alone that makes the presentation work for every such weight (for example a positivity or orientation condition on how the generators' boundaries compose, ruling out item 9's mismatch between the base associator's direction and the fibre correction);
- (b) a condition on the pair (Γ, T).

Prove necessity and sufficiency. If no condition on Γ alone suffices, show it, and give the criterion on pairs.

**Question 2 (bounded dimension).** Characterize the pairs (Γ, T) admitting *some* finite presentation of dimension ≤ n + m, or of dimension bounded by a function of n and m. In particular, does item 9's base and weight have a presentation of dimension ≤ 7? Is there a uniform bound for all pairs?

**Question 3 (a uniform localised presentation).** Give one explicit presentation, defined for every finite homotopical Γ and every weight with finite homotopical fibres, built from the Gray generators q ⊗ g plus **explicitly described** auxiliary generators, with an explicit localisation set and a dimension bound, and prove it presents ∫T. Natural candidates:
- adjoin inverse data (a reverse cell and two cancellation cells) for the mixed generators that are inverted anyway, before attaching higher generators;
- use a resolution of the base (for example a homotopically equivalent polygraph with better orientation properties) and transport the fibration;
- construct the unlocalised presentation as a strict, functorial lax Grothendieck construction on F(Γ) and prove once, by cellular induction, that localisation gives ∫T.

State the finite certificate: the data a proof checker must check.

**Question 4 (weights with non-free values).** Extend Question 3 to weights whose values are finite localisations Free(Π_b)[W_b⁻¹] and whose transport functors are given only up to equivalence.

## 5. What counts as a solution

A characterization with proof for Question 1 or 2; an explicit uniform presentation with proof and certificate for Question 3; or a published reference.

## 6. Literature (searched 2026-11-19)

- Loubaton, arXiv 2406.05425 (left cartesian fibrations, straightening, pullback preserves colimits, discrete Conduché functors); Loubaton, arXiv 2207.08504 (complicial model).
- Campion, arXiv 2311.00205 and 2311.00200; Chanavat, arXiv 2603.22242 (homotopy polygraphs, semisimplicial pasting theorem).
- Ara–Guetta, arXiv 2503.08832, §7 (strict Grothendieck construction with Gray functoriality; its total is the strict, not the Gray, construction).
- No published recognition theorem for Gray-generator presentations of Grothendieck constructions over polygraphs was found.
