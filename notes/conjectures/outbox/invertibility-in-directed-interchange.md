# Invertible cells in free higher categories with directed interchange

*A self-contained problem. The theories below are defined in full in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r5-2026-11-20.md` (Responses 1–34) and `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md` (Response 1); §1 fixes the notation and lists what is proved.*

**What we are asking for.** Free algebras of the admissible theories below have no non-identity invertible cells, and their interchangers are directed. We want to know what happens when some cells *are* invertible: (Q1) which structural cells become invertible when their inputs are, in every algebra; and (Q2) whether formally inverting all interchangers at cuts ≥ k makes cells with equal image in the k-quotient connected by invertible cells, i.e. a relative coherence theorem for each quotient of requirement 4. The main questions ask for the general statement, for every pasting diagram, every dimension, every cut and every setting of the two switches, or a counterexample.

## 1. Setting

**Composition.** Reflexive globular sets with partial compositions ∗ₖ of n-cells along k-cells (k < n), written in diagrammatic order, strictly associative and unital, with whiskering by lower-dimensional cells strictly functorial (ω-sesquicategories). For n-cells in interchange position along k < l, `L = (a ∗ₗ b) ∗ₖ (c ∗ₗ d)` and `R = (a ∗ₖ c) ∗ₗ (b ∗ₖ d)`. A strict ω-category requires L = R.

**The signature.** The T₁₂ signature of the cited round-5 answers: the sesquicategory operations; for every k < l an elementary interchanger, which for (l+1)-cells F : f ⇒ f′ and G : g ⇒ g′ in interchange position along a k-cell is the (l+2)-cell
```
ι(F, G) : (f ◁ G) ∗ₗ (F ▷ g′)  ⇛  (F ▷ g) ∗ₗ (f′ ◁ G);
```
one naturality cell per varying argument, with Leibniz-signed orientations; higher cells between routes of lower ones; and the auxiliary operations of the completion (binary joins h(A, B), lifts W(A, B) of binary globe tensors, H_L, H_R, K, J, shifted joins).

**Requirements.** A strict theory on this signature is *admissible* if its free objects F(Γ) on finite globular pasting diagrams Γ satisfy:
1. an explicit combinatorial description by generators with explicit boundaries;
2. two cells of the same dimension using the same generators, in an expanded basis, are equal;
3. every elementary interchanger exists and its reverse does not;
4. making every interchanger along a k-cell with k ≥ 1 an identity gives the free Gray-enriched category 𝔉(Γ) (homs ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ) for Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, Steiner's λ, ⊗, ν), and making every interchanger an identity gives the free strict ω-category ν(λΓ);
5. closure under substitution of cells for generators.

Write π₁ : F(Γ) → 𝔉(Γ) and π₀ : F(Γ) → ν(λΓ) for the two quotient maps of requirement 4, and π_G : 𝔉(Γ) → ν(λΓ) for the Gray-to-strict collapse.

**Letters.** Every d-cell of F(Γ) is a ∗_{d−1}-path of *contextual letters* (a d-dimensional operation applied to arguments, whiskered by lower cells). π₁ sends each letter to a whiskered generator of 𝔉(Γ) (an **outer** letter) or to an identity (an **inner** letter). Inner letters include the elementary interchangers along k ≥ 1 and their naturality and route cells. Outer letters include the whiskered variables, the cylinders of a moving globe against an edge (naturality cells r, t of the cut-0 crossing), the joins h(A, B) and the lifts W(A, B).

**Known results (all proved).**
- **(M1) The least theory V.** There is an admissible theory V (the forced base B plus the guarded round-5 equations) such that for every admissible E and every Γ the identity on letters gives a generator-preserving map F_V(Γ) → F_E(Γ) sending cells to cells and equalities to equalities. B contains the structural theory, the support-free presentation P of the cited answers, the face and unit declarations (an interchanger with an identity input is an identity), and the outer unary subdivisions in both variables at cut 0 (a cylinder of a composite moving globe, or against a composite edge, is the paste of the cylinders). (r8 Response 1.)
- **(M2) The two visible switches.** The left split of the inner interchanger ("inner composite-crossing law": ι(F₁ ∗ F₂, G) is the paste of ι(F₁, G) and ι(F₂, G)) and the right split R (the same for a composite right input) are each visible on pasting diagrams and independent. For S ⊆ {left split, R}, V + S is admissible. In V the binary splits at inner cuts are absent and the outer binary subdivisions are present only in guarded form. (r8 Response 1; r9 Responses 2–5.)
- **(M3) The strip.** On the strip C_{2,1} (inner cells A₁, A₂ composable, B in interchange position), the direct crossing u = W(A₁ ∗ A₂, B) and the paste v of W(A₁, B) and W(A₂, B) are parallel, π₁(u) = π₁(v), and in F_{V+S}(C_{2,1}) with the left split not in S there is no cell u ⇛ v and no cell v ⇛ u. A tagged algebra (tags in subsets of operand-length pairs, union under composition) separates u and v. (r5 (K44), (K51); r8.)
- **(M4) The binary join.** On ΣD² ∨ ΣD² with 2-cells A (first hom) and B (second hom), the join h(A, B) : S ⇛ U₀ satisfies r̄₁ = h(A, B) ∗ ῑ₋, where r̄₁ is a whiskered cylinder of A against the edge β₁ and ῑ₋ is a whiskered inner interchanger whose inputs are a whiskered A and a whiskered B. (r5 (K45); round-3 repair (F).)
- **(M5) Positivity.** Every non-identity cell of F_{V+S}(Γ) has positive conserved weight, so F_{V+S}(Γ) has no non-identity invertible cell. (r5 (K50).)
- **(M6) Elementary propagation.** In every algebra of every admissible theory: a cylinder with an invertible moving input is invertible (from (M1)'s unary subdivisions and unit laws); an inner interchanger ι(F, G) with F invertible is invertible if the left split holds in the algebra, and with G invertible if R holds (the inverse is (F ▷ g) ◃ (ι(F⁻¹, G) ▹ (F ▷ g′)), respectively ((f ◁ G) ◃ ι(F, G⁻¹)) ▹ (f′ ◁ G)). Consequently, by (M4), if A is invertible then h(A, B) is invertible iff ῑ₋ is, and both are when the matching split holds.
- **(M7) The Gray-to-strict level.** For strict Gray-enriched categories, an interchanger (mixed Gray generator) with an invertible positive-dimensional factor is invertible. In the (∞,ω) setting, Gray-enriched (oriented) categories whose composition inverts all mixed cells are exactly the Cat_ω-enriched ones (change of base along A ⊗ B → A × B).

**Definitions for the questions.**
- For an algebra 𝒦 of an admissible theory E and a map σ : F_E(Γ) → 𝒦, a cell is *invertible* if it has a strict two-sided inverse.
- For a pasting diagram Γ and a cut k ∈ {0, 1}, let I_k be the set of letters of F_{V+S}(Γ) sent to identities by π_k (for k = 1, the inner letters; for k = 0, every interchanger-type letter). Let F_{V+S}(Γ)[I_k⁻¹] be the algebra presented by F_{V+S}(Γ) together with, for each ℓ ∈ I_k, a new cell ℓ⁻ with the boundary of ℓ reversed and the equations ℓ ∗ ℓ⁻ = 1, ℓ⁻ ∗ ℓ = 1 (the free algebra on Γ in which the letters of I_k are inverted).
- For each tuple x₁, …, xₙ of cells in consecutive homs, the *Gray cell* G(x₁, …, xₙ) is the image under substitution of the top cell of F_{V+S}(ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}) lying over the top atom of 𝔉 (for ΣD² ∨ ΣD², the lift W).

## 2. Questions

**Q1 (main: propagation of invertibility).** Fix S ⊆ {left split, R}. Characterize the letters ℓ and argument positions for which "the argument is invertible ⇒ σ(ℓ) is invertible" holds for every algebra of every admissible theory satisfying V + S. In particular, decide, for every pasting diagram and every dimension:
- (a) whether, for every outer letter ℓ with π₁(ℓ) a whiskering of x₁ ⊗ … ⊗ xₙ, σ(ℓ) is invertible whenever σ(G(x₁, …, xₙ)) is (call this (IL));
- (b) whether an inner interchanger with an invertible input is invertible in setting S without the matching split (that is: is the converse of (M6) true, or is there an algebra of an admissible theory satisfying V + S, with F invertible and ι(F, G) not invertible?);
- (c) whether invertibility of all elementary inner interchangers whose cells lie in homs into a fixed object C implies invertibility of every inner letter in those homs (naturality cells, joins, route cells).

A complete answer for S = ∅ is the main result wanted; the other three settings next.

**Q2 (main: relative coherence for the quotients of requirement 4).** For which S does the following hold for every finite pasting diagram Γ and k = 1: if p, q are parallel cells of F_{V+S}(Γ) with π₁(p) = π₁(q), then F_{V+S}(Γ)[I₁⁻¹] has an invertible cell p ⇛ q? And the same for k = 0 with π₀, and for the Gray level: if p, q are parallel in 𝔉(Γ) with π_G(p) = π_G(q), does 𝔉(Γ)[mixed⁻¹] have an invertible cell p ⇛ q? A uniform answer for all three quotient maps (every dimension, every Γ), or a description of exactly which pairs fail, is the main result wanted.
- By (M3), for k = 1 and S without the left split the strip pair (u, v) has no cell either way before inverting; the question is whether inversion creates one.

**Q3 (invisibility).** For S = ∅ and every Γ: is every outer letter instance σ(ℓ) in F_{V+S}(Γ′) (σ a substitution between pasting diagrams) whose Gray cell is an identity itself an identity? Equivalently by (M5): does adjoining (IL) to V, as partial inverse operations defined when the Gray cell is invertible, leave every free algebra on a pasting diagram unchanged?

**Q4 (fallback).** Does the tagged algebra of (M3) remain an algebra of an admissible theory satisfying V when the tags are taken in the free abelian group on operand-length pairs (composition adding tags), instead of subsets under union? If so, in it every inner letter is invertible while u ≠ v and no cell connects them, which answers Q2 negatively for k = 1 and S ∌ left split. A proof that some law of V forces idempotent tags would also settle this.

## 3. What counts as a solution

A complete answer to Q1 or Q2 in every dimension, positive or negative (a countermodel that is an algebra of an admissible theory counts); an answer to Q3; or an answer to Q4.

## 4. Literature (searched 2026-11-21)

- Ara–Maltsiniotis, arXiv 1607.00668 (lax Gray tensor); Steiner, *Omega-categories and chain complexes*, HHA 2004.
- Gepner–Heine, arXiv 2510.10504, Thm 4.1.9 (Fun → Fun^lax is an inclusion); Campion, arXiv 2311.00205 (Gray tensor of (∞,n)-categories).
- Benjamin–Markakis–Sarti (invertibility of coherences in CaTT); Benjamin–Champin–Markakis (inverses in CaTT).
- Bourke–Lobbia, arXiv 2610.31448 (sharp coherence for lax interchange).
- Forest–Mimram, arXiv 2109.05369 (rewriting in Gray categories presented as 3-sesquicategories with interchangers); arXiv 2310.03503 (remarks on the interchange in Gray-categories). In both the interchangers are invertible from the start, which is the situation Q2 asks to reach by localization.
None of these treats invertibility in theories with directed interchange at inner cuts.
