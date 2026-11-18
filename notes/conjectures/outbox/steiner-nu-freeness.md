# A formalizable proof that ν(K) is free on its atoms, for loop-free unital bases

*A self-contained problem. It assumes no knowledge of the project that posed it. The result is known (Steiner 2004). What is asked for is a proof short and elementary enough to be machine-checked.*

## Background

We use Steiner's augmented directed complexes (R. Steiner, *Omega-categories and chain complexes*, HHA 6 (2004), [math/0403237](https://arxiv.org/abs/math/0403237); Ara–Maltsiniotis, [1607.00668](https://arxiv.org/abs/1607.00668), §2).

**Complexes.** An augmented directed complex K is a chain complex of free abelian groups Kₙ (n ≥ 0), with an augmentation ε : K₀ → ℤ and a distinguished basis Bₙ of each Kₙ. Kₙ* is the monoid of non-negative combinations of Bₙ. For a chain c, supp(c) is its set of basis elements with non-zero coefficient. We write ∂c = (∂c)₊ − (∂c)₋ with (∂c)₊, (∂c)₋ ∈ Kₙ₋₁* of disjoint supports.

**Cells.** An n-cell of ν(K) is a table x = (x₀⁻, x₀⁺, …, xₙ⁻, xₙ⁺) such that:
- xₖ^± ∈ Kₖ*;
- xₙ⁻ = xₙ⁺;
- ∂xₖ^± = xₖ₋₁⁺ − xₖ₋₁⁻ for 1 ≤ k ≤ n;
- ε(x₀^±) = 1.

Boundaries truncate the table. For ∂⁺ₖx = ∂⁻ₖy the composite x #ₖ y has (x #ₖ y)ⱼ^± = xⱼ^± + yⱼ^± − xₖ⁺ for j > k, and the common lower part for j ≤ k. This makes ν(K) a strict ω-category (single-set presentation).

**Atoms.** The atom ⟨b⟩ of b ∈ Bₙ has ⟨b⟩ₙ^± = b, ⟨b⟩ₖ⁻ = (∂⟨b⟩ₖ₊₁⁻)₋ and ⟨b⟩ₖ⁺ = (∂⟨b⟩ₖ₊₁⁺)₊.

**Hypotheses on the basis.**
- *Unital:* ε(⟨b⟩₀⁻) = ε(⟨b⟩₀⁺) = 1 for every b.
- *Loop-free:* for each p ≥ 0, on basis elements of dimension > p, the relation a <ₚ b iff supp⟨a⟩ₚ⁺ and supp⟨b⟩ₚ⁻ meet generates a strict partial order (Steiner Def. 3.5).
- *Strongly loop-free:* the relation a ∈ supp(∂b)₋ or b ∈ supp(∂a)₊ generates a strict partial order on the whole basis (Def. 3.6).

The motivating instances are the complexes λΘ of finite globular pasting diagrams and finite globular sets without loops, and their tensor products, with the Leibniz boundary ∂(a ⊗ b) = ∂a ⊗ b + (−1)^{dim a} a ⊗ ∂b. Their bases are unital and strongly loop-free. In the presentation used by the formalisation, each pasting diagram is built by "start with one 0-cell; at a current cell x of type A, add a new cell y of type A and a new cell f : x → y", and tensor products carry an explicit lexicographic total order with the negative faces before and the positive faces after.

## Statement

Let K have a loop-free unital basis.

- **(N1) Atom generation.** Every cell of ν(K) is an iterated composite of atoms (and of their iterated boundaries/identities).
- **(N2) Freeness.** For every strict ω-category C and every assignment φ sending each atom ⟨b⟩ (dim b = n) to an n-cell φ(b) of C, with ∂^±ₙ₋₁ φ(b) = Φ(∂^±ₙ₋₁⟨b⟩), there is exactly one strict functor Φ : ν(K) → C with Φ⟨b⟩ = φ(b). Here Φ on lower-dimensional cells is defined by induction. Equivalently (Steiner Thms 5.7 and 6.1), ν(K) is presented by its atoms with the relations fixing their boundaries.

## What is known

Steiner proves (N1) as Thm 5.6, through:
- the decomposition index (Prop. 5.4: a cell of index r ≥ 0 splits along #ᵣ into cells of lower index, each congruent to an atom);
- Prop. 5.5 (index −1 means an atom, using unitality).

He proves (N2) as Thm 5.7 by induction on the decomposition index. Uniqueness uses standard forms (Prop. 4.2) and transpositions of consecutive atoms (Props. 5.8, 5.9, Lemma 5.10). Thm 6.1 deduces the presentation.

These proofs are long, and they reason about arbitrary decompositions of a cell into atoms. A formalisation wants a proof by induction on explicit data: chains, an explicit order on the basis, and well-founded measures.

Useful known tools:
- **(Rad)** Every xₖ^± is a sum of distinct basis elements. Forest, HHA 2022, Lemma 3.4.5; Campbell, [2605.09427](https://arxiv.org/abs/2605.09427), Prop. 2.20; Steiner, *Opetopes and chain complexes*, [1204.6723](https://arxiv.org/abs/1204.6723), Thm 4.1, with a direct proof.
- **(F2)** For b ∈ supp(x_{m+1}^±), x_m⁻ is disjoint from (∂b)₊ and x_m⁺ from (∂b)₋. Forest Lemma 3.4.11; Campbell Prop. 2.23.
- **A cut lemma.** For a linear extension of the order, the partial sums of a cell's top chain cut the cell into a composite (an atom-free proof of (Rad), (F2) and "support determines the cell" for the tensor complexes above is known along these lines).

## Questions

**Q1.** Give a proof of (N1) for loop-free unital bases (or strongly loop-free, if easier) that proceeds by explicit induction. A natural candidate: given an n-cell x with top chain c = b₁ + … + b_r listed along a linear extension of the order, show that x = x′ #_{n−1} ⟨b_r⟩-whiskered, where x′ has top chain b₁ + … + b_{r−1}, and recurse on lower dimensions for whiskerings.

**Q2.** Give a proof of the uniqueness half of (N2) that avoids standard forms and transpositions. For example: show that any strict functor out of ν(K) is determined by its values on atoms, by induction on the decomposition used in Q1 together with a lemma saying the result does not depend on the chosen linear extension.

**Q3.** The existence half of (N2): define Φ(x) by the decomposition of Q1 and show it is independent of choices and preserves composition. Or show existence directly from (N1) and an explicit presentation.

**Q4.** If (N2) in general has no short proof, the special cases needed are:
- (Q4a) K = λΓ for a finite loop-free globular set Γ. Here atoms are the generators, and (N2) says ν(λΓ) is the free strict ω-category on Γ.
- (Q4b) K = λΓ ⊗ λD¹ (the Gray cylinder), and the quotient of ν(K) that collapses each end Γ ⊗ {0}, Γ ⊗ {1} to a point is ν of the quotient complex.

## Why it matters

A proof assistant development has proved soundness of a type theory for weak ω-categories in every strict ω-category, and computed a lax colimit at the level of chain complexes. To transfer the chain-level computation to strict ω-categories, and to apply the general soundness theorem to the strict model built from Steiner complexes, it needs (N1) and (N2). Chains in the formalisation are finite multisets of basis elements over a decidable total order, so proofs by induction on lists, extremal elements and counting are the easiest to check.

## What would count as a solution

- An elementary proof of (N1) and (N2), written at the level of chains, with each step checkable.
- Or proofs of Q4a and Q4b.
- Or the shortest known route through the literature, with each lemma stated precisely.

## Literature status (2026-11-18)

- (N1), (N2): Steiner 2004, Thms 5.6, 5.7, 6.1, for loop-free unital bases. Thm 5.11 gives the equivalence with ω-categories with loop-free atomic bases. Prop. 7.2 and Thm 7.3 cover the tensor product.
- Ara–Maltsiniotis 1607.00668, App. A: the tensor on strict ω-categories extending Steiner's.
- Forest 2022 and Campbell 2605.09427: radicality and (F2) for Steiner complexes.
- No machine-checked proof of (N1) or (N2) was found.
