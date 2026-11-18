# Steiner's ν for loop-free bases, in Agda (ledger A5)

Owner: META. Started 2026-11-18. This note covers the statement, the literature and the formalisation plan.

## 1. Why

Two Agda results stop at the passage from augmented directed complexes to strict ω-categories, and cite it:

- **C8(4)** (`Strict/LaxColimPoint.agda`) computes the lax colimit of the point at the level of complexes. To conclude `laxcolim(const 1) ≅ Free(Γ)` in strict ω-categories it cites three facts:
  - ν(λΓ) is the free strict ω-category on Γ when Γ is loop-free;
  - ν(λΓ ⊗ λD¹) ≅ ν(λΓ) ⊗ D¹;
  - collapsing atoms in ν(K) is computed on their chains.
- **The strict model of L** (`Strict/Soundness.agda` and the support work of E3/G3) works with cells of ν(K) as tables. It never builds ν(K) as a strict ω-category in the sense of `Strict/Omega.agda`, so the general soundness theorem `Strict.OmegaSound.sound-in` cannot be applied to it.

## 2. Statements to formalise

Let K be an augmented directed complex with a basis, as in `Strict/Cell.agda`.

- **(N0) ν(K) is a strict ω-category.** Cells are Steiner's tables. ∂^±_k truncates a table. x #_k y is defined when ∂⁺_k x = ∂⁻_k y, and is x + y − ∂⁺_k x componentwise: the shared entries below k, (x_k^-, y_k^+) at k, and x_j^± + y_j^± above k. The axioms are those of the `ωCat` record. Steiner 2004, Prop. 2.3 / Def. 2.8; Ara–Maltsiniotis 1607.00668 §2.4.
- **(N1) Atom generation.** If the basis is loop-free and unital, every cell of ν(K) is a composite of atoms. Steiner 2004, Thm 5.6, via Props. 5.4 and 5.5 (decomposition index).
- **(N2) Freeness.** Under the same hypotheses, ν(K) is presented by its atoms: a strict functor out of ν(K) is the same as a choice, for each atom ⟨b⟩, of a cell whose boundaries are the images of ∂^±⟨b⟩. Steiner 2004, Thm 5.7 (a morphism from a composition-generated C that is a dimension-preserving bijection on generators is an isomorphism) and Thm 6.1 (presentation by atoms).
- **(N3) Consequences used by C8(4).**
  - For loop-free globular Γ, ν(λΓ) is the free strict ω-category on Γ. This is (N2) with K = λΓ.
  - On strongly loop-free complexes, ⊗ of strict ω-categories is defined by ν(K) ⊗ ν(L) := ν(K ⊗ L), which is Steiner Prop. 7.2 and Thm 7.3, and AM §A.16. So the second cited fact is a definition once (N2) identifies ν(λΓ) with Free(Γ).
  - The chain map q of `LaxColimPoint` induces ν(q). By (N2), maps out of the quotient are atom assignments that kill the end atoms, which is the third cited fact.

## 3. Literature

- R. Steiner, *Omega-categories and chain complexes*, HHA 6 (2004), [math/0403237](https://arxiv.org/abs/math/0403237): Defs. 3.4–3.6, Props. 5.1–5.5, Thms 5.6, 5.7, 5.11, 6.1, Prop. 7.2, Thm 7.3.
- Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*, [1607.00668](https://arxiv.org/abs/1607.00668), §2 and App. A.
- S. Forest, *Unifying notions of pasting diagrams*, HHA 2022, §3.4 (radicality, (F2)).
- A. Campbell, *Parity complexes redux*, [2605.09427](https://arxiv.org/abs/2605.09427), §2.
- R. Steiner, *Opetopes and chain complexes*, [1204.6723](https://arxiv.org/abs/1204.6723), Thm 4.1, a direct proof of radicality.
- The answered prompt `conjectures/answered/steiner-support-formalizable-2026-11-18.md` gives atom-free proofs of radicality, (F2), lifting and "support determines the cell" (via the cut lemma), together with an explicit basis order for tensors of pasting diagrams (`Strict/Order.agda`, PR #110). These are the natural tools for (N1).
- **Formalisations.** A search on 2026-11-18 found no machine-checked proof of (N1) or (N2) in any proof assistant.

## 4. Plan

1. **(N0) Done.**
   - `Strict/Tables.agda`: tables over any commutative monoid satisfy the `ωCat` axioms entry by entry. No cell condition is needed, and composition is x + y − ∂⁺ₙx, with no subtraction.
   - `Strict/Nu.agda`: for an abstract complex (`ADC`: cancellative commutative monoid of chains, additive ∂^±, degree projections, augmentation), Steiner's cells of dimension < L are closed under boundaries and composites. Being a cell is a proposition, so `nu K L : ωCat`.
   - `Strict/FreeADC.agda`: the instance for a finite basis (chains as vectors of naturals, ∂ extended linearly), with the atom of D¹ checked by evaluation.
   - `Strict/Atoms.agda`: the atom ⟨b⟩ of a basis element (Steiner Def. 3.4: ⟨b⟩ₖ⁻ = (∂⟨b⟩ₖ₊₁⁻)₋, ⟨b⟩ₖ⁺ = (∂⟨b⟩ₖ₊₁⁺)₊, with positive and negative parts by pointwise truncated subtraction) is a cell of ν(K) when ∂∂ = 0 holds on chains, ∂ lowers degree by one, the basis element is unital (ε⟨b⟩₀^± = 1), and deg b ≤ L (`atom-cell`).
   - Still to do: bridge the bag/≈ representation of `Strict/Cell.agda` to these tables.
2. **(N1) Done for ordered bases** (`Strict/Generation.agda`, `--safe`, no postulates). `Gen.generation : ∀ x → IsCell K L x → Gen x`, where `Gen` is the closure of the atoms of dimension ≤ L under the composites `compT n` of `nu`.
   - Hypotheses (record `Hyp`): ∂∂ = 0 and degree-lowering of ∂ on chains; ε∂ = 0 on 1-chains; unital basis; and the basis listed in an order with supp ∂⁻bᵢ ⊆ [0, i) and supp ∂⁺bᵢ ⊆ (i, N). The last is the strongly loop-free case (Steiner Def. 3.6 with a linear extension), which covers λΘ, loop-free globular sets and their tensors (the order of `Strict/Order.agda`). Steiner's weaker loop-free hypothesis (Def. 3.5) is not covered.
   - Proof: Steiner's Props. 5.1, 5.2, 5.4, 5.5 and Thm 5.6, with the decomposition index replaced by an induction on the level s.
     - `peel` (Prop. 5.1, binary form): if the rows of a cell above s split as p + q, both satisfying the boundary conditions above s, and (∂p_{s+1})₋ is disjoint from (∂q_{s+1})₊, then the cell is y #ₛ z with y, z cells whose rows above s are p and q.
     - `gen-suc` (Prop. 5.2): rows above s+1 equal to an atom ⟨a⟩ (or zero) give row s+1 = ⟨a⟩_{s+1} + w with w ≥ 0, so the rows above s are those of ⟨a⟩ + Σ_{c ∈ w} ⟨c⟩.
     - `peel-all` (Prop. 5.4): peel the least of these atoms in the basis order, recursing on |w|. The order makes every disjointness condition a support comparison.
     - `gen-0` (Prop. 5.5): at s = 0 unitality forces the cell to be the atom.
   - Equations between chains use a small commutative-monoid solver (`Strict/CMonSolver.agda`).
   - **Instances** (`Strict/BasisCheck.agda`). `mkHyp` builds `Hyp B` from finite checks on the basis elements, each decided by evaluation: ∂∂ = 0, degrees of ∂^±bᵢ, the order, ε∂ = 0 in degree 1, and unitality for i < N. The arrow and the 2-globe are checked, and `gen-D²` applies `generation` to ν(λD²). An earlier version asked unitality for every index i, including i ≥ N, where the "atom" is the zero table; no basis satisfied that. The instances confirm the corrected `Hyp` is satisfiable.
3. **(N2)** Freeness.
   - **Uniqueness: done** (`Gen.uniqueness`). Two strict functors out of `nu K L` (record `Functor`, preserving sources, targets and composites) that agree on the atoms of dimension ≤ L agree everywhere, by induction on `generation`. `gen-cell` shows that composites of atoms are cells.
   - **Existence: open.** It would follow Steiner's Thm 5.7 proof (standard forms, transposing consecutive atoms). The outside prompt asks for a shorter route.
   - **Plan for existence** (internal, in parallel with the outside prompt). Existence reduces to one statement, the word problem for ν(K):
     - **(E1) Expressions: done** (`Strict/Expr.agda`, `Strict/NuWords.agda`). An expression is built from generators, n-composites and boundaries, and `Ev` is its value in any ωCat. `FromWords.functor` builds a strict functor from three inputs: generation, (Def) every expression with a value in ν(K) has one in 𝒟, and (Inv) expressions with equal ν-values have equal 𝒟-values. `NuWords.generated` gives the first input for ν(K). So existence is exactly (Def) + (Inv).
     - **Route (verified outside response, `conjectures/answered/steiner-nu-freeness-2026-11-18.md`).** Unique lifting, specialised to expressions: for composition-only expressions with the same ν-value, the 𝒟-values agree. The stages, for ordered unital bases first, where the index order is a linear extension of every <ᵣ, so `entK-Lo/Hi` and `disj-LH` supply every disjointness:
       - **(L1) Boundary elimination.** Hypothesis (19): each atom b has expressions W_b^± over atoms of lower degree, whose ν-value is ∂^±⟨b⟩ and whose 𝒟-value is ∂^±φ(b). Every expression then rewrites to a composition-only one with the same ν- and 𝒟-values, never raising generator degrees above its dimension. Induction on generator degree.
       - **(L2) Cells are determined by their r-source and their rows above r.** Row r⁺ is forced by Bd and cancellation. This gives the converse of `peel`: in y #ᵣ z = y′ #ᵣ z′ with y ≡ᵣ y′ and z ≡ᵣ z′, the factors agree (fixed-list uniqueness, response §1.2).
       - **(L3) Atom coefficients above r** (§1.1) and the decomposition index δ (computable from the table, matching `GenAt`).
       - **(L4) Standardisation** (§3.1, Steiner Prop. 4.2) on composition-only expressions, by structural induction, keeping both values; and its image (§3.2): the cut of a standardised expression is δ of its ν-value.
       - **(L5) Swap lemma** (§4, Steiner 5.9/5.10), under the induction hypothesis below index r.
       - **(L6) Unique lifting** by induction on δ + 1, with an inner induction on the inversion count of the label list. This gives (Inv); (Def) follows from (Inv) on boundary expressions, by induction on the expression.
       - **L4 status:** done for every strict ω-category (`Strict/StdSem.agda`, `Strict/Std.agda`): `Std.std` with `WFProof.std-wf` (each factor has exactly one generator above the cut r, at most one above r+1 overall, at least two factors) and `SemProof.std-sem` (values preserved). The cut is computed from generator counts, so §3.1's "second-largest degree" bookkeeping becomes `findCut` plus `cut-unique`.
       - **L3 status:** the parts L5/L6 use are done. `Strict/NuRows.agda`: rows of composites add above the composition level, boundaries vanish above it, and an expression with exactly one generator ⟨a⟩ above r has the rows of ⟨a⟩ above r (`Single.single-rows`). `Strict/AtomSum.agda`: a count vector supported on degrees in (r, L] is determined by Σ cᵢ⟨i⟩ on the rows above r (`esum-inj`, §1.1, by descending degree). The decomposition index δ is not needed separately: the cut of a standardised expression is pinned down by these counts.
       - **L5 groundwork:** `Strict/LowerCut.agda`: in y #ₛ₊₁ y′ with y ≡ ⟨b⟩, y′ ≡ ⟨c⟩ above s+1 and c < b, the composite also splits at level s as v #ₛ u with v ≡ ⟨c⟩ and u ≡ ⟨b⟩ above s (`lower-cut`); no such pair exists at level 0 (`no-cut-0`). `StdSem.split′` gives the second interchange form. The expression-level swap and the induction P(s) remain.
       - **Plan for L5/L6 with ordered bases.** No sorting by inversion count is needed. Use an induction shaped like `peel-all`. Statement P(s): for every cell x agreeing above s with an atom or zero, (Ex) some composition-only expression has ν-value x and a 𝒟-value, and (Un) any two such expressions have equal 𝒟-values. In the step at cut r, standardise both expressions; their cut is r (§3.2 + §1.1). Move the factor with the least label to the front by swaps (§4: an adjacent pair (b, c) with c < b satisfies ⟨b⟩ᵣ⁺ ∧ ⟨c⟩ᵣ⁻ = 0 by `entK-Lo/Hi`). Then match the front factor and the rest against the peel decomposition with `Lifting.factors`. The front factor is handled by P(r), the rest by an inner induction on the number of atoms above r, as in `peel-all`. The swap needs a split at level r−1 by an index threshold, a generalisation of the least-atom peel.
