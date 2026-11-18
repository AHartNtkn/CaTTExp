# Supports of derivable terms over a single hom (conservativity of two-tier L over CaTT)

## Background

- **Pasting contexts.** A CaTT pasting context Γ (Finster–Mimram, arXiv 1706.02866) is a globular pasting diagram. Its objects are a₀, …, aₙ, and its hom pasting diagrams are Θ₁, …, Θₙ, where Θₖ is the part of Γ between aₖ₋₁ and aₖ, shifted down one dimension. Γ is *single-hom* when n = 1, i.e. Γ = ΣΘ.
- **Tables.** Write λΘ for the Steiner complex of Θ (Steiner 2004; Ara–Maltsiniotis, arXiv 1607.00668, §A). K(Γ) = λΘ₁ ⊗ … ⊗ λΘₙ has as basis the tuples (c₁, …, cₙ) with cₖ a cell of Θₖ. T is the total cell of K(Γ). Its top chain is T_N, with N = Σ dim Θₖ, and its lower chains are T^±_k for k < N.
- **Supports.** For a term t : A over Γ, Gray.Support (`src/CaTTExp/Gray/Support.agda`) defines a set of tuples supp(t : A):
  - The top support of a variable v is {(v)}.
  - A coh Δ with type t′ →_B u′ and argument σ has top support F_σ(T_N(Δ)) in the operation case and ∅ in the coherence case. Here F_σ sends a tuple (w₁, …, wₘ) to the product of the top supports of σ(w₁), …, σ(wₘ).
  - supp(t : A) is the union of the top supports of t and of every term in its type A.
- **Downward closure.** ↓S is the downward closure of S under replacing one entry by its source or target.
- **Two-tier L.** A coh Δ ⊢ t′ →_B u′ is admitted in one of two cases:
  - *Coherence case:* ↓supp(t′) = ↓supp(u′) = ↓Supp(T).
  - *Operation case:* dim B = N, ↓supp(t′) = ↓Supp(∂⁻T) and ↓supp(u′) = ↓Supp(∂⁺T).

## Statement

**Conjecture (term-level conservativity).** Let Γ = ΣΘ be single-hom, and Γ ⊢ t : A be derivable in two-tier L. Then for every non-object variable v of Γ:

  (v) ∈ ↓supp(t : A)  ⟺  v ∈ FV(t) ∪ FV(A).

Consequently, on a single hom, L's side condition is Finster–Mimram's, and L restricted to one hom is CaTT.

## What is known

- **The rule-level half is proved for some diagrams.** For Θ with ≤ 6 edges, ↓Supp(T), ↓Supp(∂^±T) are exactly the non-object variables of Γ and ∂^±Γ. This is checked by evaluation in `Gray/Bounded.agda`.
- **↓Supp(T) is all of K(Δ), for every context Δ.** This is proved in Agda (`Gray/FullSupp.agda`, `full-cover`, 2026-11-18). The proof goes up one hom at a time: a cell that is the s-face of a higher cell is replaced by that cell. Otherwise the cell is already in the s-table.
- **⇒ is proved in Agda, in any number of homs** (`Gray/SuppVars.agda`, `supp-vars`, 2026-11-18). For a derivable t : A over a context whose types are variable towers (every pasting context), every entry of every tuple of ↓supp(t : A) is in FV(t) ∪ FV(A). The proof has two parts. The entries of supports are variables of t : A, which is syntactic. And for derivable t : A, FV(t) ∪ FV(A) is closed under the variables of a variable's type, by induction on the derivation, as in CaTT.
- **⇐ is where the argument stalls.** Take t = coh_Δ(…)[σ] and a variable w of Δ. We need FV(σ(w)) ⊆ ↓supp(t : A). Every w is an entry of a table tuple τ of Δ (by `full-cover`). But F_σ(τ) = ∅ as soon as some other entry α of τ is sent to a coherence-case coh, i.e. an identity-like cell, whose top support is empty.
  - *Example.* Let t be the vertical composite of α : f ⇒ g and β : g ⇒ h, and send α and β to identity-like cells. The middle cell g is an *interior* face: it is in neither ∂⁻T nor ∂⁺T. Its image's variables are reached only through the invariant below, applied to σ(α) and then to σ(β).
  - *Invariant (I).* A derivable cell with empty top support has boundaries with equal closed supports. This follows from strict soundness (`Strict/Soundness.agda`): the interpretation is a Steiner cell, and a cell with zero top chain has x⁺ = x⁻.
  - *What (I) does not give.* (I) moves supports across one interior face. A proof also has to reach every interior face from ∂⁻T or ∂⁺T through a sequence of top tuples whose shared faces are interior. That requires an order on the top tuples with no cycles of interior faces, which is Steiner's *loop-free* condition on the basis of K(Δ). It is known for Gray tensors of pasting diagrams (Steiner 2004, §3; Ara–Maltsiniotis 1607.00668, §A), but not formalized here.
- **Two routes.**
  - **(R1) Atoms.** Every cell of ν(K(Δ)) is a composite of atoms ⟨τ⟩ (Steiner 2004, Thm 3.2, for loop-free unital bases). The strict functor σ̂ preserves composites, and the closed support of a composite is the union of the closed supports of its factors (x⁺ ⊆ ↓∂⁺c ∪ x⁻ from the chain equation). Apply this to the atom of a tuple (c₁, …, w, …, cₘ) whose other entries are 0-dimensional in their homs. Its image's support contains supp(σ(w)), because σ of a hom 0-cell is a 1-cell with nonempty top support.
  - **Available order (2026-11-18).** `conjectures/answered/steiner-support-formalizable-2026-11-18.md` (PR #103) gives an explicit total order on the basis of λΘ₁ ⊗ … ⊗ λΘₘ. Every negative face of b comes before b and every positive face after it. Each factor is in creation order, and tuples are ordered lexicographically, with the comparison reversed after an odd dimension sum. This order is what (R2) needs to cross interior faces without cycles, so (R2) no longer depends on atom theory.
  - **(R2) Chain level.** Prove the ⇐ inclusion by induction on dimension. Use the chain equation of T (hypothesis T-cell of `Strict/Soundness.agda`) to cover the boundary tables, and (I) to cross interior faces in a loop-free order.

## Why it matters

Two-tier L is meant to extend CaTT, the type theory of weak ω-categories, by lax interchange across different homs, without changing anything inside one hom. The conjecture says that on a single hom the new side condition admits exactly the coherences CaTT admits. Without it, L might quietly add or remove coherences even in ordinary one-hom situations.

## What would count as a solution

Any of these:
- A proof of the conjecture, ideally along (R1) or (R2), making explicit which facts about Steiner complexes are used.
- A counterexample: a single-hom derivable term whose closed support misses one of its free variables, or contains a variable that is not free.
- A reference proving the support property for strict functors between free ω-categories on Steiner complexes.

## Literature status

Searched 2026-11-18 (from memory of the sources cited, no new search):
- Steiner, *Omega-categories and chain complexes* (2004): loop-free unital bases, and that atoms generate ν(K).
- Ara–Maltsiniotis, arXiv 1607.00668: Gray tensors of Steiner complexes, and loop-freeness of tensor products.

No statement of the support property for images of cells under strict functors between such ω-categories is known to us.
