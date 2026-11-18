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

- **(N0) ν(K) is a strict ω-category.** Cells are Steiner's tables. ∂^±_k truncates a table. x #_k y is defined when ∂⁺_k x = ∂⁻_k y, and is given by (x #_k y)_j^± = x_j^± + y_j^± − x_k^+ for j > k (and the shared lower part for j ≤ k). The axioms are those of the `ωCat` record. Steiner 2004, Prop. 2.3 / Def. 2.8; Ara–Maltsiniotis 1607.00668 §2.4.
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

1. **(N0)** Build ν(K) as an `ωCat`. Chains need a canonical form so that cells can be compared with `≡`: sorted lists with multiplicities over a decidable total order on the basis, or tables over a finite basis. The bag/≈ representation of `Strict/Cell.agda` will be bridged to it.
2. **(N1)** Atom generation by Steiner's decomposition index, or by the cut lemma of the answered support prompt if that gives a shorter route.
3. **(N2)** Freeness. Uniqueness of the extension uses (N1). Existence follows Steiner's Thm 5.7 proof (standard forms, transposing consecutive atoms).
4. **(N3)** Discharge the citations of C8(4), and connect the L strict model to `ωCat`.

Steps 2–3 are the bulk. An outside prompt asking for the shortest formalisable route to (N1)–(N2), in the style of the support prompt, is in `conjectures/outbox/steiner-nu-freeness.md`. Internal work proceeds in parallel, starting from (N0).
