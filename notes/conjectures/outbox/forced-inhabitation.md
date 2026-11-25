# Inhabitation by forced lifts in free higher categories with directed interchange

*A self-contained problem. The theories below are defined in full in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r5-2026-11-20.md` (Responses 1–34, in particular Response 10 for the raising recursion), `-r8-` (Response 1) and `-r10-` (Responses 1–3, 15); §1 fixes the notation and lists what is proved.*

**What we are asking for.** In the free algebras F_{V+S}(Γ) below, the cells obtained from *forced* lifts (§2) by composition and substitution do not exhaust all cells: from degree six on, an auxiliary bridge of the raising recursion is missed (known result (N1) below). We ask whether they nevertheless reach **some** cell between every pair of generated cells that F_{V+S}(Γ) connects, i.e. whether every hom-type between generated cells that is inhabited in F_{V+S}(Γ) is inhabited by a generated cell. The main question asks for the general statement, for every pasting diagram, every dimension and every setting, or a counterexample.

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
- **(M3) The strip.** On the strip C_{2,1} (inner cells A₁, A₂ composable along a cell, B in interchange position with both), the direct crossing u = ι(A₁ ∗ A₂, B) and the paste v of ι(A₁, B) and ι(A₂, B) are parallel, π₁(u) = π₁(v), and in F_{V+S}(C_{2,1}) with the left split not in S there is no cell u ⇛ v and no cell v ⇛ u. This persists after formally inverting every letter sent to an identity by π₁.
- **(M4) Loops.** On Σ[2] ∨ Σ[2] (two composable 2-cells a₁, a₂ in one hom and b₁, b₂ in the next), V has a 4-cell H : w ⇛ w, a whiskered elementary inner interchanger, where w is the composite interchanger of a₁a₂ past b₁b₂. Its powers are pairwise distinct, and H and 1_w are not connected by any cell, even after formally inverting every letter sent to an identity by π₁.
- **(M5) Positivity.** Every non-identity cell of F_{V+S}(Γ) has positive conserved weight, so F_{V+S}(Γ) has no non-identity invertible cell. (r5 (K50).)
- **(M6) Decidability.** For every S, Γ and degree, the vertices (cells of F_{V+S}(Γ) of a given dimension with fixed lower faces and weight) form a finite computable set, the generating letters between them are finite and listable, and equality of cells is decidable. (r10 Response 3.)
- **(N1) Forced generation fails from degree six.** Every native letter through degree five is forced on its own arity, and every cell through degree five is generated (G below). On Γ = ΣD⁴ ∨ ΣD⁴ with hom-degree-4 inputs X, Y, the auxiliary bridge B = b₄¹ of the raising recursion (r5 Response 10) is a hom-5 letter with boundary (1) D⁰⁰Y_v⁰X_v¹ → X_u⁰D¹⁰Y_v¹ (D the positive hom-4 face of the (3,3) seed, X_u, X_v, Y_v pure insertions, superscripts layers). A second simple witness of the same boundary is (2): the forward elementary exchange D⁰⁰Y_v⁰X_v¹ → D⁰⁰X_v⁰Y_v¹ followed by b Y_v¹, where b : D⁰⁰X_v⁰ → X_u⁰D¹⁰ is the bridge of the same row on the smaller arity ΣD⁴ ∨ ΣD³. Both have the same Gray image and full support; by rigid factorization (r10 Response 2) the number of proper occurrences of the constructor B is an invariant, 1 for (1) and 0 for (2). Every generated cell of degree six has B-count 0, so B ∉ G although its faces are in G. Suspension gives failures in every degree ≥ 6.
- **(N2) Unrestricted generation holds.** If clause 3 below is weakened to allow the value of any witness, every cell is generated (G⁺ = F), because each native letter's single step is a witness on its own arity.
- **(N3) Generic forcedness is decidable per letter.** For a native tag L, form the finite (M6) multigraph at its generic source and target, delete the direct edges whose value equals L, and test reachability of the target: L is forced iff the target is unreachable (and the endpoints differ).

## 2. Definitions

Fix S and a finite pasting diagram Γ, and write F = F_{V+S}(Γ) and π = π₁ : F → 𝔉(Γ).

- **Support.** For a cell e of 𝔉(Γ), supp(e) is the downward-closed set of Steiner basis elements of 𝔉(Γ) used by e and its iterated faces. A cell e has *full support* if supp(e) contains every generator of Γ.
- **Witness.** For (d−1)-cells x, y of F, a *witness* x → y is a ∗_{d−1}-path of d-dimensional contextual letters ℓ₁ ⋯ ℓ_m from x to y (m ≥ 0) such that the union of supp(π x), supp(π ℓᵢ) and supp(π y) is full. Its *value* is the composite cell of F. It is *simple* if its vertices x, ∂⁺ℓ₁, …, ∂⁺ℓ_m are pairwise distinct. (Every witness becomes a simple witness by deleting cycles: a cycle projects to an identity of the loop-free 𝔉(Γ), so the support is unchanged.)
- **Forced.** The pair (x, y) is *forced*, with value c, if a witness x → y exists and every simple witness x → y has value c. If x = y, the empty path is the only simple witness, so (x, x) is forced with value 1_x whenever supp(π x) is full.
- **Generated cells.** Let G(Γ) be the smallest family of cells of the free algebras F_{V+S}(Δ), over all finite pasting diagrams Δ, such that:
  1. every generator of Δ is in G(Δ);
  2. G is closed under the compositions ∗ₖ and under whiskering;
  3. if (x, y) is forced in F_{V+S}(Δ) with value c, and x, y ∈ G(Δ), then c ∈ G(Δ);
  4. if c ∈ G(Δ) and σ : F_{V+S}(Δ) → F_{V+S}(Γ) is the substitution sending each generator of Δ to a cell of G(Γ) of the right boundary, then σ(c) ∈ G(Γ).

  Write G⁺(Γ) for the family defined in the same way with "forced" dropped from clause 3 (c the value of any witness x → y).


## 3. Questions

**Q1 (main: inhabitation by generated cells).** For every setting S ⊆ {left split, R}, every finite pasting diagram Γ and every dimension d: if x, y ∈ G(Γ) are parallel (d−1)-cells and F_{V+S}(Γ) has a witness x → y (a full-support cell; more generally, any cell x → y), does G(Γ) contain a cell x → y? A proof for all Γ, d and S, or a description of exactly which pairs (x, y) fail, is the main result wanted. A negative answer should give a pair (x, y) in G(Γ), with a cell x → y in F_{V+S}(Γ) and none in G(Γ).

**Q2 (main, the expected route).** Is every native letter of V + S either forced on its own arity, or such that its boundary pair on its arity is joined in F_{V+S} by a witness that is a composite of whiskered instances of letters of strictly smaller rank or of forced letters (so that the pair is inhabited in G by induction)? In particular: does every raising bridge b_a^ε of r5 Response 10 factor, up to a cell of F with the same endpoints, as an exchange followed by a smaller bridge, down to the seed, as B does in (N1)? If this holds, explain whether Q1 follows; if it fails, give the first failing letter.

**Q3 (fallback).** Is the bridge b : D⁰⁰X_v⁰ → X_u⁰D¹⁰ on ΣD⁴ ∨ ΣD³ of (N1) forced on its arity (by the test (N3))? If not, is its boundary pair inhabited in G? Equivalently for (N1): is the boundary pair of B inhabited in G?

## 4. What counts as a solution

A complete answer to Q1, positive or negative, in every dimension and setting; or a complete answer to Q2; or an answer to Q3.
