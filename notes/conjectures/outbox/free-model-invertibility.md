# Invertibility in free higher categories with directed interchange, after inverting some generators of a pasting diagram

*A self-contained problem. The theories below are defined in full in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r5-2026-11-20.md` (Responses 1–34), `-r8-` (Response 1) and `-r10-` (Responses 1–3); §1 fixes the notation and lists what is proved.*

**What we are asking for.** Let Γ be a finite pasting diagram and M a set of its generators. Form the free algebra on Γ in which the generators of M are made invertible. Which cells of the original free algebra become invertible? A proof assistant decides "this coherence is invertible" by asking exactly this question about one cell over one pasting diagram, with M the set of arguments already known to be invertible. Free algebras on pasting diagrams have no non-identity invertible cells, and the answer is known for single Gray cells; it is not known for an arbitrary cell. The main question asks whether the answer is **decidable**, uniformly in the diagram, the marked set and the cell, for every admissible theory between the least one and the strict Gray quotient, together with a characterization. Without the restriction to pasting diagrams the answer is negative (known result (U) below), so the question is exactly where pasting diagrams sit.

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
- **(M5) Positivity.** Every non-identity cell of F_{V+S}(Γ) has positive conserved weight, so F_{V+S}(Γ) has no non-identity invertible cell. (r5 (K50).)
- **(M6) Decidability.** For every S, Γ and degree, the vertices (cells of F_{V+S}(Γ) of a given dimension with fixed lower faces and weight) form a finite computable set, the generating letters between them are finite and listable, and equality of cells is decidable. (r10 Response 3.)
- **(G1) Gray cells.** For cells x₁, …, xₙ in consecutive homs of hom-dimensions d₁, …, dₙ, the *Gray cell* G(x₁, …, xₙ) is the image under substitution of the top cell of F_{V+S}(ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}) over the top atom of 𝔉, lifted along a planar binary bracketing tree of the factors (each node labelled by the sum of the hom-dimensions below it). For a principal disk tree, G is invertible in every algebra of V + S whenever xᵢ is invertible **iff** no node on the path from leaf i to the root has two children of dimension ≥ 2. The answer is the same in all four settings, and the same when every inner letter is also invertible. In particular the binary cases that propagate are exactly (1, p) and (p, 1), and (2, 2) does not.
- **(G2) Other letters.** An outer cylinder (one positive factor against an edge) with invertible moving input is invertible. An inner interchanger with an invertible left (right) input is invertible exactly when the left split (R) holds. The join h(A, B) is invertible from A exactly when the inner interchanger ῑ₋ of the factorization r̄₁ = h(A, B) · ῑ₋ is, and never from B alone. The letters K and J do not propagate from any positive position; W on composite operands does not.
- **(U) Undecidability off pasting diagrams.** (i) For one fixed finite *matching context* containing group relators (not a pasting diagram) and a computable family of single outer letters ℓ_w = W(ewZ, B), "ℓ_w is invertible whenever its right operand is" holds in every algebra iff w = 1 in a fixed finitely presented group with unsolvable word problem. (ii) For finite marked computads (C, M) in general, the set of pairs ((C, M), t) with t invertible in the free Gray ω-category on C with M inverted is not recursively enumerable, already for one fixed computad with a varying input; the construction simulates a Turing machine with loops in C.
- **(P) The strict ω-categorical level.** In the free strict ω-category ν(λΓ) on a pasting diagram Γ of dimension n, the total cell becomes invertible after inverting M iff every n-dimensional generator is in M (map to the strict ω-category with trivial cells below n and (ℕ, +) in dimension n, sending one unmarked top generator to 1 and every other generator to an identity).

## 2. Definitions

Fix an admissible theory E with V ⊆ E (in the sense of (M1)), a finite pasting diagram Γ, and a set M of positive-dimensional generators of Γ. Optionally fix a set O of objects of Γ.

- **The localization.** F_E(Γ)[M⁻¹] is the algebra presented by F_E(Γ) together with, for each m ∈ M, a new cell m⁻ with the boundary of m reversed and the equations m ∗ m⁻ = 1 and m⁻ ∗ m = 1. Write q : F_E(Γ) → F_E(Γ)[M⁻¹]. Equivalently, a cell c of F_E(Γ) has q(c) invertible iff σ(c) is invertible for every algebra 𝒦 of E and every map σ : F_E(Γ) → 𝒦 sending each generator of M to an invertible cell.
- **With objects.** F_E(Γ)[M⁻¹, O] additionally inverts every letter that π₁ sends to an identity and whose hom lands in an object of O (the inner letters into O).
- **Letterwise.** A cell of F_E(Γ) is a ∗_{d−1}-path of letters. Call c *letterwise invertible* if q of each letter of some path representing c is invertible.

## 3. Questions

**Q1 (main: decidability and characterization).** For every admissible E with V ⊆ E, including V + S for each S ⊆ {left split, R} and the Gray quotient 𝔉: is the set of triples (Γ, M, c), with Γ a finite pasting diagram, M a set of its generators and c a cell of F_E(Γ) such that q(c) is invertible in F_E(Γ)[M⁻¹], decidable? The same with O. A proof for all E in this range, in every dimension, or a counterexample (a pasting diagram on which invertibility is undecidable or not r.e.), is the main result wanted. If the answer depends on E, the dividing line between theories is wanted.

**Q2 (main, the expected route).** Is invertibility letterwise on pasting diagrams: is q(c) invertible iff c is letterwise invertible? And is invertibility of a single letter, applied to generators of Γ and whiskered, decided by a finite criterion on its tag, its operand positions, M, O and S that extends (G1) and (G2) to every native letter of V? If both hold, Q1 follows; please say whether it does. If letterwise invertibility fails, give a cell whose letters are not all invertible but which becomes invertible, and say what replaces the letterwise test.

**Q3 (fallback).** For Γ of dimension at most 4 (so cells of degree at most 5, where every native letter is known to be forced on its arity), decide Q1 and Q2.

## 4. What counts as a solution

A complete answer to Q1 for all E between V and 𝔉, positive or negative, in every dimension; or a complete answer to Q2; or an answer to Q3.

## 5. Literature (searched 2026-11-25)

- Ara–Maltsiniotis, arXiv 1607.00668 (lax Gray tensor); Steiner, *Omega-categories and chain complexes*, HHA 2004; Campion, arXiv 2311.00205.
- Benjamin–Markakis, *Invertible cells in ω-categories*, arXiv 2406.12127 (coherences are invertible; composites of invertible cells are invertible), and Benjamin–Champin–Markakis (inverses in CaTT).
- Fujii–Hoshino–Maehara, *Weakly invertible cells in a weak ω-category*, arXiv 2303.14907 (invertibility is closed under composition and coinductively characterized; no decision procedure).
- Forest–Mimram, arXiv 2109.05369 and 2310.03503 (Gray categories as 3-sesquicategories with invertible interchangers).
- Bourke–Lobbia, arXiv 2610.31448 (sharp coherence for lax interchange).

A search for localizations of free higher categories on pasting diagrams and decidability of invertibility found nothing further. None of these treats localizations of free algebras with directed interchange at inner cuts.
