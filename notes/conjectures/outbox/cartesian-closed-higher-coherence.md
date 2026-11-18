# Are free cartesian closed (∞,1)-categories 1-categories? Soundness of Mimram's higher pasting criteria

*A self-contained problem. No knowledge of the project that posed it is assumed. The cleanest question is Question 1. Questions 2–3 are the concrete type-theoretic statements it would settle.*

## Background

**Pasting types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) singles out a decidable class of simple types (with →, ×, 1), the **pasting types**, each with exactly one inhabitant up to βη (his Theorem 15).

A type is first normalized by the type isomorphisms of Bruce–Di Cosmo–Longo to A₁ × … × Aₙ with each Aᵢ implicational. Each Aᵢ must then be derivable as Θ \ ∅ | ∅ ⊢ Aᵢ by:

```
Θ \ (Θ′, tgt A) | Γ, A ⊢ B   (tgt A ∉ Θ′)         Θ \ Θ′ | Γ, Δ ⊢ A₁  …  Θ \ Θ′ | Γ, Δ ⊢ Aₙ
────────────────────────────────────────         ───────────────────────────────────────────
Θ \ Θ′ | Γ ⊢ A → B                                Θ \ Θ′ | Γ, (A₁→…→Aₙ→X), Δ ⊢ X
```

Here tgt A is the rightmost variable of A. A type theory with a constant for each pasting type and an equality rule identifying all terms of a pasting type is equivalent to the simply typed λ-calculus with products modulo βη (his Theorems 19 and 21).

**Higher dimensions.** The paper says an "easy variant", with dependent and identity types, should axiomatize cartesian closed ∞-categories, meaning (∞,1). It also says the corresponding criterion is implemented in the tool cccatt but left for future work.

A context may contain:
- objects;
- 1-cells f : A → B between types;
- higher cells α : s → t between parallel terms one dimension down.

A goal is a type of some dimension.

## The two criteria in the tool

Source: github.com/smimram/cccatt, `src/pasting.ml`, commit 69bb11af, 2026-11-15.

**(Rev), for (∞,1).**
1. While possible, pick a hypothesis α of dimension ≥ 2 with a variable endpoint x and other endpoint t, such that:
   - x ∉ FV(t);
   - x occurs in no other hypothesis's type;
   - x has not been rewritten before.

   Delete α and substitute x := t.
2. Then strip the goal's higher layers and require its underlying 1-type to be pasting in the remaining 1-dimensional context.

If this succeeds, every goal of every dimension over these data is accepted, in both directions.

**(Dir), directed.** For a goal of dimension n:
1. The n-dimensional hypotheses must be cells x → y between variables, with:
   - no loops;
   - distinct sources and distinct targets;
   - an acyclic relation.
2. Let the source context be the context without the targets of these cells, and the target context the context without their sources. Check both, recursively, against the goal's (n−1)-type.
3. The goal's source term must avoid targets, and its target term must avoid sources.

There is no fullness condition. With no n-dimensional hypotheses, every parallel pair of terms of a pasting (n−1)-type gets an n-cell in both directions.

## Questions

1. **(Discreteness.)** Let S be a set, or more generally a directed graph. Is the free cartesian closed (∞,1)-category on S equivalent to the free cartesian closed 1-category on S? Equivalently, are its mapping spaces discrete?
   - For comparison, the free symmetric monoidal (∞,1)-category on a set is ⊔ₙ Sⁿ_{hΣₙ}, whose mapping spaces are discrete. So the analogous statement holds there for formal reasons.
   - The analogous statement for weak ω-categories on a graph is also known to hold: the free weak ω-category on a graph is the free category.
   - For cartesian closed structure no formula of that kind is available.
2. **(Soundness of Rev.)** Assuming a positive answer to 1: is every goal accepted by (Rev) uniquely fillable, up to a contractible space, in the free cartesian closed (∞,1)-category on the context?
   - The contraction step adjoins a cell together with its free endpoint, which should be a trivial extension in any (∞,1)-setting. So 2 should reduce to 1 together with Mimram's Theorem 15. Is this reduction correct?
3. **(Soundness of Dir.)** Let 𝒞 be the free cartesian closed (∞,ω)-category, with pseudo exponentials (Map(A × B, C) ≃ Map(A, C^B) as mapping (∞,ω)-categories), on a finite computad of the shape above. Does every goal accepted by (Dir) have a contractible space of fillers, invertible when the goal has no top-dimensional hypotheses?
   - **Smallest open case:** dimension 3 over a graph (no hypotheses of dimension ≥ 2). Are any two parallel 2-cells between βη-equal 1-terms connected by a unique invertible 3-cell? This is coherence for free cartesian closed tricategories.

## What is known

- **Dimension 1:** Mimram, Theorems 15, 19 and 21. His Agda proof postulates Theorem 15.
- **Dimension 2 over a graph:** Fiore–Saville, *Coherence for bicategorical cartesian closed structure* (MSCS 31(7), 2021; LICS 2020). In the free cartesian closed bicategory on a graph there is at most one 2-cell between parallel 1-cells, and every cartesian closed bicategory is biequivalent to a 2-category with 2-categorical cartesian closed structure. This settles (Dir) in dimension 2 without 2-dimensional hypotheses: terms of a pasting 1-type are βη-equal, hence related by a unique invertible 2-cell. See also Saville's thesis (arXiv 2007.00624).
- **No coherence result is known** for cartesian closed tricategories, cartesian closed (∞,1)-categories, or cartesian closed (∞,ω)-categories.

## What counts as a solution

- A proof or a counterexample for Question 1: for instance, a non-trivial loop in a mapping space of the free cartesian closed (∞,1)-category on one object.
- A proof of 2 or 3, or a counterexample: an accepted goal with two inequivalent fillers, or with none.
- A reference proving coherence for cartesian closed tricategories, or the discreteness in 1.
