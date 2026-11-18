# A formalisation-friendly proof that strict ω-categories model CaTT

*This problem is self-contained. It assumes no knowledge of the project that posed it. We are looking for a proof structure suited to a proof assistant, not a new theorem: the result is known.*

## Background

**Strict ω-categories, single-set definition** (Street 1987; Steiner, arXiv math/0403237, Def. 2.1). A strict ω-category is a set C with maps s_n, t_n : C → C for n ∈ ℕ and partial operations x #_n y, defined exactly when t_n x = s_n y. The axioms are:

- **Boundary maps.**
  - s_m s_n x = s_m t_n x = s_m x for m ≤ n.
  - s_m s_n x = s_n x = t_m s_n x for m > n, and likewise for t.
  - Every x has some n with s_n x = x.
- **Units.** s_n x #_n x = x = x #_n t_n x.
- **Boundaries of composites.**
  - s_n(x #_n y) = s_n x and t_n(x #_n y) = t_n y.
  - For m > n: s_m(x #_n y) = s_m x #_n s_m y, and likewise for t_m.
  - For m < n: s_m(x #_n y) = s_m x, and likewise for t_m.
- **Associativity** of each #_n.
- **Interchange.** For m < n: (x #_n y) #_m (z #_n w) = (x #_m z) #_n (y #_m w), whenever both sides are defined.

**CaTT** (Finster–Mimram, LICS 2017). This is a dependent type theory.
- Types are ⋆ and `s →_A u`.
- Terms are variables and `coh Θ (s →_A u) σ`. Here Θ is a *pasting context*, a context presenting a globular pasting diagram, given by the rules
  - ps-start: `x : ⋆ ⊢ps x : ⋆`.
  - ps-extend: from `Γ ⊢ps x : A`, derive `Γ, y : A, f : x →_A y ⊢ps f : x →_A y`.
  - ps-drop: from `Γ ⊢ps f : x →_A y`, derive `Γ ⊢ps y : A`.
  - finish: from `Γ ⊢ps x : ⋆`, conclude that Γ is a pasting context.
- The side condition on s and u is one of two cases.
  - Either both s and u (with A) use all variables of Θ;
  - or s uses exactly the variables of the source boundary ∂⁻Θ, u those of the target boundary ∂⁺Θ, and dim Θ = dim A + 1.
- σ is a substitution into Θ.
- Substitution is strict and syntactic.

**What we have.** We have a full, checked proof of soundness in the strict ω-categories ν(K) of Steiner, for every chain complex K with a basis. It includes the following.
- Every derivable term over a pasting context Θ, evaluated at the generic environment of ν(λΘ), is a cell of ν(λΘ).
- The top chain of a term t : B, at that environment, is the set of variables of t of dimension dim B.
- The coh over Θ in an environment ρ is the image of the coh at the generic environment under the chain map induced by ρ.

## Question

Give a proof, organised for formalisation, of the following theorem.

**Theorem.** Let C be a strict ω-category in the single-set sense.
- Let `Γ ⊢ t : A` be derivable in CaTT.
- Let ρ assign to each variable of Γ a cell of C, compatibly with the boundaries prescribed by Γ.

Then the evident interpretation ⟦t⟧ρ exists. Coherences are interpreted as pasting composites of their substitutions, or as the identity on such composites. When A = s →_B u, the interpretation satisfies s_{dim B} ⟦t⟧ρ = ⟦s⟧ρ and t_{dim B} ⟦t⟧ρ = ⟦u⟧ρ.

Our current plan, with five steps:
1. Labelled Batanin trees with a fold-defined composite.
2. A boundary lemma.
3. A binary pasting lemma: comp(S₁ ⊔_k S₂) = comp S₁ #_k comp S₂.
4. A functor F_λ : ν(λΘ) → C, sending a cell to the composite of its support.
5. Interpretation equals F_λ applied to the ν-interpretation.

Step 4 needs a dictionary between cells of ν(λΘ) and sub-pasting diagrams of Θ. Building that dictionary is a lot of combinatorics.

1. Is there a shorter route that avoids step 4? For instance:
   - a direct induction on CaTT derivations, with a stronger invariant;
   - a definition of the composite of a pasting context directly by recursion on ps-derivations, for which "composite of composites is composite" has a short inductive proof;
   - using only the binary pasting lemma.
2. If step 4 is needed, what is the most economical description of cells of the free strict ω-category on a globular pasting diagram, for the purpose of defining F_λ and proving it preserves #_k?
3. Which interchange instances are actually used? A list of the axioms each step uses would help us size the formalisation.

## What would count as an answer

A sequence of lemmas, each with a proof sketch. Each proof should be by structural induction on trees, ps-derivations or CaTT derivations, with the axioms used named at each step. A reference to a source whose proof has this shape would also do.

## Literature status (searched 2026-11-18)

- Ara's thesis, Ch. 5, §5.1, proves that Θ is a pseudo-coherator for ∞-categories: unique lifts of admissible pairs.
- Ara (arXiv 1212.3085) proves the groupoid case.
- Steiner (arXiv math/0403237) proves Thms 5.6, 5.7 and 6.1: ν(K) is presented by its atoms for loop-free unital bases.
- Leinster (arXiv math/0305049) gives, in App. F and §8.1, the free strict ω-category monad via pasting diagrams.
- Power gives the n-categorical pasting theorem (1991).
- Benjamin–Finster–Mimram (arXiv 2106.04475) show that CaTT models are Grothendieck–Maltsiniotis weak ω-categories.
- None of these is organised as the induction asked for here.
