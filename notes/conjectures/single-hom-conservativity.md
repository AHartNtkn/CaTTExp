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

**Status: proved in Agda (2026-11-18), for the empty signature.** ⇒ is `Gray/SuppVars.agda` (`supp-vars`), ⇐ is `Strict/SuppFV.agda` (`supp-fv⇐`). See "Proof of ⇐" below.

**Theorem (term-level conservativity, formerly a conjecture).** Let Γ = ΣΘ be single-hom, and Γ ⊢ t : A be derivable in two-tier L. Then for every non-object variable v of Γ:

  (v) ∈ ↓supp(t : A)  ⟺  v ∈ FV(t) ∪ FV(A).

Consequently, on a single hom, L's side condition is Finster–Mimram's, and L restricted to one hom is CaTT.

## What is known

- **The rule-level half is proved for every single-hom diagram** (`Gray/SingleHom.agda`, 2026-11-18). For Θ ⊢ps with dim Θ ≥ 1, ↓Supp(∂^±T) consists exactly of the singletons (v) with v a non-object variable of ∂^±Γ (`rule-bdry⇒`, `rule-bdry⇐`), and ↓Supp(T) of all of them (`rule-full`). The proof goes through a pointwise description of Finster–Mimram's ∂^±, proved for every pasting context (`Gray/BdryChar.agda`). `Gray/Bounded.agda` had checked this by evaluation for Θ with ≤ 6 edges.
- **↓Supp(T) is all of K(Δ), for every context Δ.** This is proved in Agda (`Gray/FullSupp.agda`, `full-cover`, 2026-11-18). The proof goes up one hom at a time: a cell that is the s-face of a higher cell is replaced by that cell. Otherwise the cell is already in the s-table.
- **⇒ is proved in Agda, in any number of homs** (`Gray/SuppVars.agda`, `supp-vars`, 2026-11-18). For a derivable t : A over a context whose types are variable towers (every pasting context), every entry of every tuple of ↓supp(t : A) is in FV(t) ∪ FV(A). The proof has two parts. The entries of supports are variables of t : A, which is syntactic. And for derivable t : A, FV(t) ∪ FV(A) is closed under the variables of a variable's type, by induction on the derivation, as in CaTT.
- **⇐ is proved in Agda** (`Strict/SuppFV.agda`, `supp-fv⇐`, 2026-11-18), for Θ ⊢ps and the empty signature: if Σctx Θ ⊢ t : A and v ∈ FV(t) ∪ FV(A) is not an object, then (v) ∈ ↓supp(t : A). See "Proof of ⇐".
- *The obstacle, for the record.* Take t = coh_Δ(…)[σ] and a variable w of Δ. Every w is an entry of a table tuple τ of Δ (by `full-cover`), but F_σ(τ) = ∅ as soon as another entry of τ goes to a coherence-case coh, whose top support is empty. Example: the vertical composite of α : f ⇒ g and β : g ⇒ h, with α and β sent to identity-like cells; the middle cell g is an interior face, in neither ∂⁻T nor ∂⁺T. Entrywise reasoning cannot reach it. Earlier versions of this note proposed two routes, (R1) atoms and (R2) a loop-free order (`Strict/Order.agda`); the proof below goes through Strict.Recon's cuts instead, which already use that order.

## Proof of ⇐

By induction on the derivation, with Cl(t : A) the set of tuples reached from supp(t : A) by Gray face steps (no bound on the number of steps).

1. **Variables.** (v) ∈ supp(v : A), and the variables of A are in suppTy(A), since types in a pasting context are variable towers.
2. **Coh.** Let t = coh_Δ(t′ →_B u′)[σ] and v ∈ FV(σ(w)). By induction (v) is reached from some s ∈ supp(σ(w) : B_w[σ]). Since B_w is a variable tower, s is in the top support of σ(g) for a variable g of Δ, and since (v) is a singleton so is s = (a). If g is an object, σ(g) is an object variable, which has no faces, so v would be an object. Otherwise:
3. **A tuple through g** (`Gray/Through.agda`). Each hom of Δ contains a 1-cell (`PsFacts.nonE`), so there is τ = (o₁, …, g, …, oₘ) in K(Δ) with 1-cells oᵢ. By `full-cover` it is below a tuple of Supp(T), so by the side condition it is in the closed support of the cell X of ν(K(Δ)) whose σ-image is t (`Strict/Soundness.agda`, `cohX`): T in the operation case, step(t′, u′, 0) in the coherence case.
4. **Images keep the closure** (`Strict/LiftImage.agda`, `image`). Let F = F_σ and let Cl be closed under positive faces and contain every row of F(X). Then every tuple of F(b) is in Cl, for every b in the face closure of X. Proof: Strict.Recon lifts b to the top row of a cell obtained from X by cuts w = u + ∂(c<a) (Strict.Cut). F is a chain map, so F w + ∂⁻F(c<a) = F u + ∂⁺F(c<a) as bags, and every tuple of F w is in F u or a positive face of a tuple of F c. This is where interior faces are crossed.
5. **Single hom** (`Strict/SigmaFacts.agda`). Every cell of ΣΘ goes from object 0 to object 1, so a composable tuple has length ≤ 1, and a strict face is one Gray step. Take Cl = Cl(t : A): it is face-closed, it contains F(X) because F(X) is t's tower (soundness), and its tuples are short (soundness again).
6. **Conclusion.** F(τ) contains w₁ ⋯ (a) ⋯ wₘ, with wᵢ the single tuple of the top support of the 1-cell σ(oᵢ) (augmentation). By 4 it is in Cl, so it is short, so every wᵢ is empty and (a) ∈ Cl. Then (v) ∈ Cl. Paths from a singleton have length ≤ dim Θ, so (v) ∈ ↓supp(t : A).

The facts about Steiner complexes used are those of the strict model: the total cell is a cell (Bridge), support determines cells and cuts (Recon, Cut), and soundness. No atom theory is used.

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
