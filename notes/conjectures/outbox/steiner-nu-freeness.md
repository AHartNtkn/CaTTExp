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

Boundaries truncate the table. For ∂⁺ₖx = ∂⁻ₖy the composite x #ₖ y is x + y − ∂⁺ₖx entrywise: the common entries below k, (xₖ⁻, yₖ⁺) at k, and xⱼ^± + yⱼ^± above k. This makes ν(K) a strict ω-category (single-set presentation).

**Atoms.** The atom ⟨b⟩ of b ∈ Bₙ has ⟨b⟩ₙ^± = b, ⟨b⟩ₖ⁻ = (∂⟨b⟩ₖ₊₁⁻)₋ and ⟨b⟩ₖ⁺ = (∂⟨b⟩ₖ₊₁⁺)₊.

**Hypotheses on the basis.**
- *Unital:* ε(⟨b⟩₀⁻) = ε(⟨b⟩₀⁺) = 1 for every b.
- *Loop-free:* for each p ≥ 0, on basis elements of dimension > p, the relation a <ₚ b iff supp⟨a⟩ₚ⁺ and supp⟨b⟩ₚ⁻ meet generates a strict partial order (Steiner Def. 3.5).
- *Strongly loop-free:* the relation a ∈ supp(∂b)₋ or b ∈ supp(∂a)₊ generates a strict partial order on the whole basis (Def. 3.6).

The motivating instances are the complexes λΘ of finite globular pasting diagrams and finite globular sets without loops, and their tensor products, with the Leibniz boundary ∂(a ⊗ b) = ∂a ⊗ b + (−1)^{dim a} a ⊗ ∂b. Their bases are unital and strongly loop-free. In a convenient explicit presentation, each pasting diagram is built by "start with one 0-cell; at a current cell x of type A, add a new cell y of type A and a new cell f : x → y", and tensor products carry an explicit lexicographic total order with the negative faces before and the positive faces after.

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

**A short proof of (N1) in the strongly loop-free case (known, given for reference).** Suppose the basis is listed b₀, …, b_{N−1} so that supp(∂b_i)₋ ⊆ {b_j : j < i} and supp(∂b_i)₊ ⊆ {b_j : j > i}. Then every cell is a composite of atoms, by the following induction on a level s.
- Suppose the rows of x above s+1 are those of an atom ⟨a⟩ (or zero). Then row s+1 is ⟨a⟩_{s+1} + w with w ≥ 0, so the rows above s are those of ⟨a⟩ + Σ_{c ∈ w} ⟨c⟩ (Steiner Prop. 5.2).
- Peel off the least of these atoms in the basis order: x = y #ₛ z. The rows of y above s are those of that one atom, and the rows of z above s are those of the rest (Steiner Prop. 5.1 for two pieces; the order gives the disjointness it needs).
- At s = 0, unitality makes the cell an atom (Prop. 5.5).

Uniqueness in (N2) follows from this: two functors that agree on atoms agree on composites of atoms.

**Q1.** Does (N1) for merely loop-free bases (Def. 3.5) have an equally short proof? Optional; every instance we need is strongly loop-free.

**Q2.** The existence half of (N2) is the main question. Given a strict ω-category C and an assignment φ of atoms as in the statement, define Φ(x) by the peel decomposition above, peeling the least atom first. Then show:
- Φ(x) does not depend on the level used;
- Φ(y #ₖ z) = Φ(y) #ₖ Φ(z) for arbitrary composable cells y, z, not only those produced by peeling;
- Φ commutes with boundaries.

The difficulty is that the decomposition of y #ₖ z is unrelated to the decompositions of y and z. An argument by induction on explicit data is wanted, for example a lemma showing that peeling the least atom commutes with composition up to interchange. Alternatively, give a short proof of Steiner's Thm 5.7 for this case.

**Q3.** Could existence instead come from a presentation? For example: show that ν(K) is isomorphic to the strict ω-category freely generated by the atoms, with the boundary relations, using generation (N1) and a normal form computed from tables.

**Q4.** If (N2) in general has no short proof, the special cases needed are:
- (Q4a) K = λΓ for a finite loop-free globular set Γ. Here atoms are the generators, and (N2) says ν(λΓ) is the free strict ω-category on Γ.
- (Q4b) K = λΓ ⊗ λD¹ (the Gray cylinder), and the quotient of ν(K) that collapses each end Γ ⊗ {0}, Γ ⊗ {1} to a point is ν of the quotient complex.

## Why it matters

Freeness of ν(K) on its atoms is what lets computations made at the level of chain complexes (for example lax colimits, joins and Gray cylinders) be transferred to strict ω-categories, and it is the step that lets general results about strict ω-categories be applied to the models ν(K). A machine-checked version needs a proof by induction on explicit data. Chains there are finite multisets of basis elements over a decidable total order, so proofs by induction on lists, extremal elements and counting are the easiest to check.

## What would count as a solution

- An elementary proof of the existence half of (N2), written at the level of chains, with each step checkable.
- Or proofs of Q4a and Q4b.
- Or the shortest known route through the literature, with each lemma stated precisely.

## Literature status (2026-11-18)

- (N1), (N2): Steiner 2004, Thms 5.6, 5.7, 6.1, for loop-free unital bases. Thm 5.11 gives the equivalence with ω-categories with loop-free atomic bases. Prop. 7.2 and Thm 7.3 cover the tensor product.
- Ara–Maltsiniotis 1607.00668, App. A: the tensor on strict ω-categories extending Steiner's.
- Forest 2022 and Campbell 2605.09427: radicality and (F2) for Steiner complexes.
- No machine-checked proof of (N1) or (N2) was found.
