# Finite presentations of Grothendieck constructions over free bases of any dimension

*A self-contained problem. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, polygraphs (computads) and Grothendieck constructions, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem for bases and fibres of **every** finite dimension, with its finite check. The cases of base dimension ≤ 3 and of suspension bases are done (§3), each by a construction tailored to its dimension. A further case such as "base dimension 4" is not what we want; the point is a construction whose correctness does not depend on the dimension.

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

## 4. Questions

**Question 1 (main).** Let Γ be a finite n-polygraph all of whose skeleta are homotopical, and T : F(Γ) → strict ω-categories a strict functor with values F_m(Π_b), Π_b finite and homotopical. Prove that the relative Gray-generator presentation of §2 presents ∫T, for all n and m. State the finite certificate.

A uniform proof will probably need attaching maps that are functorial in the base cell, so that compatibility along common boundaries is automatic rather than checked shape by shape. Two possible routes, offered only as suggestions:
- **(a) A strict model.** Build the unlocalised presentation as a strict construction on F(Γ) itself, for example a strict lax Grothendieck construction of T (or of a cofibrant replacement of T) computed in strict ω-categories with the Gray tensor, natural in maps of bases. Then show once, by cellular induction on Γ, that localising it gives ∫T. Naturality would replace the hand-made lifts of item 6.
- **(b) Cylinder functors on pasting shapes.** Define, for every globular pasting shape P and every strict functor P → strict ω-categories, an unlocalised cylinder presentation that is natural in maps of pasting shapes (including degeneracies and composites). Every base generator's boundary is a composite of pasting shapes, so the attaching maps are images of this natural construction.

**Question 2 (weights with non-free values).** Extend Question 1 to weights whose values are themselves given by finite homotopical polygraphs Π_b but whose functors T(q) are only given up to equivalence (an (∞,ω)-functor F(Γ) → ω rather than a strict one). Is there a finite presentation, and what extra data must the certificate contain?

**Question 3 (sharpness).** Is homotopicality of all skeleta of the base necessary, or is homotopicality of Γ itself enough? Give a base Γ that is homotopical with a non-homotopical skeleton, and decide whether the terminal weight on it has a finite presentation.

## 5. What counts as a solution

A proof of Question 1 (with the certificate); a counterexample, i.e. a base and weight in the class of Question 1 for which the expected presentation is wrong (for example by an Euler-characteristic or homology count after groupoidification); answers to Questions 2–3; or a published reference.

## 6. Literature (searched 2026-11-18)

- Loubaton, arXiv 2406.05425 (left cartesian fibrations, straightening, weighted limits as marked lax limits, pullback preserves colimits).
- Campion, *The Gray tensor product of (∞,n)-categories*, arXiv 2311.00205; Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (homotopy polygraphs).
- Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*, Mém. SMF (joins and Gray tensor of strict ω-categories).
- No published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs was found.
