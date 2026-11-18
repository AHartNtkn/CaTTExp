# Directed pasting types for Gray-closed structure: which 2-cells between planar proofs?

*A self-contained problem. No knowledge of the project that posed it is assumed. The smallest open case is Question 1.*

## Background

**Unbiased type theories from contractible types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) presents cartesian closed categories without λ-abstraction or application as primitives. Instead:
- a decidable class of **pasting types** is singled out, each having exactly one inhabitant up to βη;
- for every pasting type there is a constant coh_A : A;
- any two terms of a pasting type are equal.

All combinators and all βη-equations arise this way. The style comes from the type theory CaTT for weak ω-categories (Finster–Mimram, LICS 2017). There, "pasting contexts" are contractible, and the coherence rule produces *cells* (not equations) between parallel composites. The hope is that pasting-type theories have higher-dimensional versions in which the equality rule becomes a rule producing higher cells.

**The planar (non-symmetric) 1-dimensional case is settled.** Take formulas built from atoms with ⊗ and the two residuals B\A ("a B on the left gives A") and A/B, with no unit. Sequents Γ ⊢ C have nonempty ordered Γ.
- A sequent is **balanced** if each atom occurs exactly twice, with opposite polarities.
- **Theorem (coherence).** In the free unit-free biclosed monoidal category on the atoms, a balanced sequent has at most one morphism, and exactly one when it is provable in the Lambek calculus with product.
  - This is a non-symmetric analogue of Kelly–Mac Lane, *Coherence in closed categories* (JPAA 1, 1971).
  - Proof idea: factorization lemmas for cut-free derivations, plus connectivity of the axiom-link graph.
- **Consequence:** the theory with coh over balanced provable sequents, closed under type substitution, presents the free biclosed monoidal category.

**The higher target: Gray tensor products.** The lax Gray tensor product ⊗ on (∞,ω)-categories is monoidal biclosed and not symmetric (Campion, arXiv 2311.00205):

```
Map(A ⊗ B, C)  ≃  Map(A, Fun^lax(B, C))     (mapping spaces).
```

The equivalence does **not** hold for mapping (∞,ω)-categories: Gagna–Harpaz–Lanari, arXiv 2006.14495, Rem. 2.20. In the strict setting, the Gray tensor of two arrows D¹ ⊗ D¹ is a square with one non-invertible 2-cell:

```
(f ⊗ b′) ∘ (a ⊗ g)   ⇒   (a′ ⊗ g) ∘ (f ⊗ b)          for f : a → a′, g : b → b′,
```

that is, "right factor first" ⇒ "left factor first" (one of the two conventions). In a Gray-monoidal (biclosed) 2-category, the composites of whiskered 1-cells applied to independent tensor factors are therefore related by **directed** interchange cells, not isomorphisms.

**Why the obvious higher criterion fails.** The proof assistant cccatt implements a directed higher criterion for Mimram's theories (source: github.com/smimram/cccatt, `src/pasting.ml`, commit 69bb11af). For a 2-dimensional goal t → u over a context with no 2-dimensional hypotheses, it accepts every pair of parallel terms of a pasting 1-type. For f, g as above, this accepts both interchange directions, so it presents the *pseudo* (invertible-interchange) structure, not the Gray one.

## Setting for the questions

**Signature.** Fix a set of generating 1-cells fᵢ : Pᵢ → Qᵢ between formulas (in ⊗, \, /, no unit), each to be used exactly once. A **1-term** is a planar multimorphism Γ → C in the free biclosed monoidal category on the atoms and these generators. It is built from:
- structural maps, which are coh's of balanced provable sequents, closed under type substitution;
- the generators.

**Event order.** A 1-term t applies the generators in some order σ(t), its event order. Between consecutive events the structural part is unique, by the coherence theorem.

Two events are **independent** if neither's output is (transitively) an input of the other. Independent events occupy disjoint wire intervals, so planarity gives them a left/right position.

**Subtlety: closures.** When a generator is applied inside a curried argument (a closure passed to a residual hypothesis, or a residual goal), use the following normal form. Curry is strictly natural in the context: Λ(f) ∘ h = Λ(f ∘ (X ⊗ h)). So push every event on a captured wire *inside* the closure. Then treat each closure containing events as one compound event at the outer level, with its own internal event order. This gives a **nested event order**.

**Inversions.** inv(t) is the set of independent pairs (e left of e′, at the same nesting level) with e′ applied before e, collected over all levels.

**Candidate criterion G.** A 2-cell t ⇒ u between 1-terms of the same balanced sequent (and the same generators) is a coherence iff
- the nesting structure agrees; and
- inv(u) ⊆ inv(t).

**What is known about G:**
- It yields the lax naturality cell of evaluation and not its inverse. Take φ : P → C/B and b : X → B. Then t₁ = ev∘(φ⊗B)∘(P⊗b) (b first) and t₂ = ev∘(C/B⊗b)∘(φ⊗X) (φ first). Here inv(t₁) = {(φ, b)} and inv(t₂) = ∅, so G gives t₁ ⇒ t₂ only.
- t ⇒ u and u ⇒ t are both accepted iff σ(t) = σ(u), in which case the cell is invertible.
- For a single nesting level, the event orders are the linear extensions of a 2-dimensional poset: dependency, plus left/right. Inversion-set containment is reachability by oriented adjacent swaps. Those linear extensions form an interval of the weak Bruhat order (Björner–Wachs, *Permutation statistics and linear extensions of posets*, JCTA 58, 1991).

## Questions

1. **(Smallest open case: soundness and completeness in dimension 2, one nesting level.)** Let 𝒢 be the free Gray-monoidal biclosed strict 2-category on a set of objects and a set of generating 1-cells. Interchangers are non-invertible 2-cells, and the closed structure is an isomorphism of hom-categories, strictly natural. Is it true that:
   - for 1-cells t, u with the same source, target and generators, and no closures containing events, there is a 2-cell t ⇒ u in 𝒢 iff inv(u) ⊆ inv(t); and
   - such a 2-cell is then unique?
   Equivalently: is each hom-category of 𝒢 between such 1-cells the weak-Bruhat interval described above?
2. **(Closures.)** Is the nested event order an invariant of 1-cells of 𝒢? Does Question 1's statement hold level by level? In particular, is there an interchanger between an outer event and a compound (closure) event, and is it the only 2-cell relating orders across levels?
3. **(ω-version.)** For n fully independent events, conjecture that the k-cells between event orders are the cells of the hom ω-category of the strict Gray cube ν(D¹ ⊗ … ⊗ D¹) (Steiner complexes) between its bottom and top vertices. Its 1-dimensional part is the weak Bruhat order on Sₙ, and the higher Bruhat orders of Manin–Schechtman (see also Kapranov–Voevodsky, Ziegler) should appear in higher dimensions. Is this right? What is the general (dependent, planar, nested) version?
4. **(Comparison.)** Gepner–Heine (*Oriented category theory*, arXiv 2510.10504, Cor. 4.1.11) describe the morphism object of an oriented category as the presheaf (S, T) ↦ Map(S ⊠ X ⊠ T, Y), recording whether time sits on the left or right. Does criterion G (or its ω-version) present the free bioriented / Gray-closed structure in their sense?

## What counts as a solution

Any of:
- a proof or counterexample for Question 1;
- a precise invariant answering Question 2;
- a statement and proof (or a reference) for Question 3;
- a reference showing that hom-categories of free Gray monoids (or Gray-closed 2-categories) on 1-generators are weak-order intervals.

## Literature (searched 2026-11-18)

- **Pasting types:** Mimram (CSL 2026) for cartesian closed. No published linear, planar or Gray version was found. Mimram lists closed, linear and planar variants as future work.
- **Coherence for Gray monoids and Gray categories:**
  - Gordon–Power–Street, *Coherence for tricategories* (Mem. AMS 1995), where interchangers are invertible;
  - Forest–Mimram, *Coherence of Gray categories via rewriting* (FSCD 2018);
  - Bourke–Lobbia on skew closed structures for lax and pseudo transformations (arXiv 2212.12358).
  None treats the closed (residuated) case with directed interchange.
- **Weak order on linear extensions:** Björner–Wachs (1991); Manin–Schechtman, *Arrangements of hyperplanes, higher braid groups and higher Bruhat orders* (1989); Kapranov–Voevodsky, *Combinatorial-geometric aspects of polycategory theory* (1991).
