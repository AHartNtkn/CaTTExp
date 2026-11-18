# Free strict ω-categories with directed interchange at every level

*Self-contained problem statement. No project context needed.*

## Background

**Strict ω-categories.** In a strict ω-category, composites along a k-cell and along an l-cell (k < l) satisfy the interchange law strictly:

```
(a ∗ₗ b) ∗ₖ (c ∗ₗ d)  =  (a ∗ₖ c) ∗ₗ (b ∗ₖ d).
```

**Gray-enriched categories.** A category enriched over strict ω-categories with the (lax) Gray tensor product ⊗ is called Gray-enriched (Ara–Maltsiniotis, arXiv:1607.00668; Gepner–Heine call the ∞-version "oriented categories", arXiv:2510.10504). In such a category the interchange law is replaced, *for composition along 0-cells only*, by a directed (non-invertible) cell. For example, given 2-cells α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z, there is a 3-cell

```
(βf′) ∗₁ (gα)  ⇛  (g′α) ∗₁ (βf)
```

and nothing in the other direction. Composition along k-cells with k ≥ 1 happens inside hom ω-categories and interchanges strictly.

**Free Gray-enriched categories on pasting diagrams.** Let Γ be a globular pasting diagram, decomposed as a wedge of suspensions ΣΘ₁ ∨ … ∨ ΣΘₙ. The free Gray-enriched category on Γ has homs ν(λΘⱼ ⊗ … ⊗ λΘᵢ₊₁), Gray tensors of Steiner complexes (Steiner, HHA 2004). Its cells are therefore computable from chains, and two cells of the same dimension with the same set of generators coincide.

**The obstruction to iterating.** One would like a notion in which the interchange law is replaced by a directed cell for *every* pair k < l of composition dimensions, not just for k = 0. The obvious construction iterates Gray enrichment: categories enriched over categories enriched over …, each with its own Gray-type tensor. This fails beyond dimension 3:
- Crans showed that no monoidal biclosed structure on Gray-categories captures weak transformations;
- Bourke and Lobbia (*A skew approach to enrichment for Gray-categories*, arXiv:2212.12358) replace monoidal by skew monoidal closed structures;
- see also Bourke and Gurski, *A cocategorical obstruction to tensor products of Gray-categories*.

## The problem

Define a notion of **strict lax-interchange ω-category**: a globular set with compositions ∗ₖ, identities, strict associativity and unit laws, in which every interchange law for k < l is replaced by a directed (l+1)-cell, oriented consistently. The interchange cells must themselves satisfy appropriate coherence laws, e.g. with respect to further composition and to each other.

The requirements:

1. **Free objects on globular pasting diagrams.** For every finite globular pasting diagram Γ, the free such structure F(Γ) exists and has an explicit combinatorial description. Ideally this is a "Steiner-like" description: a finite graded set of generators (one for each "iterated tensor" of cells of Γ) with explicit boundaries, so that cells can be computed mechanically.
2. **Support determines cells.** In F(Γ), two cells of the same dimension using the same set of generators are equal.
3. **Directedness.** For every k < l, the interchange cell for two cells side by side along a k-cell exists in F(Γ), and the reverse cell does not exist.
4. **Comparison.** The structure restricts to (or maps to) Gray-enriched categories when all interchange cells for k ≥ 1 are identities, and to strict ω-categories when all interchange cells are identities.
5. **Substitution.** The family Γ ↦ F(Γ) is closed under substitution. A cell of F(Γ) can be substituted for each generator of a pasting diagram Γ′ of matching boundary, giving a map F(Γ′) → F(Γ). Equivalently, the F(Γ) form a globular-operad-like structure.

A negative answer is equally valuable: an argument that no notion satisfies 1–3, or that free objects must be infinite, or that requirement 2 must fail. That would show directed interchange at every level cannot be handled by a generator-support criterion.

## Hints and partial approaches

- **Dimension 3.** Forest and Mimram's "Gray presentations" (*Rewriting in Gray categories with applications to coherence*, MSCS 2022) treat interchange as a 3-generator and work in sesquicategories. That is the k = 0 case in dimension 3. A candidate is to iterate their construction, adding an interchange generator for every pair k < l, and to look for a normal form.
- **Diagrammatic sets.** Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*, arXiv:2404.07273) and Chanavat's Gray products of diagrammatic sets (arXiv:2505.01387) handle pasting by molecules without fixing an interchange law. They may provide the generator sets of requirement 1.
- **Recursive guess.** The generators of F(Γ) between the endpoints of Γ should be tuples (g_n, …, g₁), with each gᵢ a generator of F(Θᵢ) itself. Their boundaries should be given by a Leibniz rule in which "∂gᵢ" is a cell of F(Θᵢ), not a chain. Making this precise requires tensoring a *composite* with a generator. That is where the directed interchange inside F(Θᵢ) enters and the chain-complex calculus stops working.

## What would count as a solution

Either of the following:
- a definition together with a combinatorial description of free objects satisfying requirements 1–5, even if limited to finite dimension;
- an impossibility argument showing that requirements 1–3 cannot hold together.
