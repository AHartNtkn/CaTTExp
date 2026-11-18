# Relative coherence for cartesian closed higher categories, round 2: generators of dimension 3

*A self-contained problem. No knowledge of the project that posed it is assumed. Round 1 and its verified answer are archived in `answered/dir-relative-coherence-2026-11-18.md`. The smallest open case is Question 1.*

## Background

**Pasting types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) defines a decidable class of simple types (with →, ×, 1), the **pasting types**. Each has exactly one inhabitant up to βη (his Theorem 15). A type theory with a constant for every pasting type, and an equality rule identifying all terms of a pasting type, presents the free cartesian closed category.

**Higher contexts.** A context may contain:
- objects (type variables);
- 1-cells f : A → B between types;
- higher cells α : s → t between parallel terms one dimension down.

A goal of dimension n is a pair of parallel (n−1)-terms. A filler is an n-cell between them.

**Semantics.** Let 𝒞(Γ) be the free cartesian closed (∞,ω)-category on such a context Γ. Products and exponentials are pseudo: Map(A × B, C) ≃ Map(A, C^B) as mapping (∞,ω)-categories.

**What is known.**
- **Graph contexts** (no hypotheses of dimension ≥ 2). 𝒞(Γ) is the free cartesian closed 1-category: simply typed λ-terms with constants modulo βη, with all higher cells identities up to contractible choice. Sketch of the proof: the free cartesian closed (∞,1)-category on a graph has discrete mapping spaces, by a retract argument onto a set of normal forms. The 1-core functor, which keeps all cells of dimension ≤ 1 and the invertible higher cells, is right adjoint to the inclusion of (∞,1)-categories (Ozornova–Rovelli–Walde, arXiv 2603.11005, Thm 2.20). It preserves cartesian closed structure, so freeness on a graph transfers. In particular, any two parallel 2-cells between βη-equal 1-terms are joined by a contractible space of invertible 3-cells. This includes coherence for cartesian closed tricategories over a graph.
- **Dimension 2 over a graph:** Fiore–Saville, *Coherence for bicategorical cartesian closed structure* (MSCS 2021).
- **Invertible higher hypotheses** that have a free endpoint can be contracted. This is Mimram's reversible criterion; it is sound by the result above.
- **2-dimensional generators (round 1, proved).** Let 𝓕 be the free pseudo cartesian closed (∞,2)-category on atomic types, primitive 1-generators, and 2-generators forming disjoint directed chains f₀ ⇒ f₁ ⇒ ⋯ ⇒ f_r of primitive parallel 1-generators. Then for all u, v : U → V the space of 2-cells u ⇒ v is empty or contractible, and the free (∞,ω) object is 𝓕 with only identities above dimension 2 up to contractible choice. Proof: β-normal η-long forms give a bijection 𝓕₁(U,V) ≅ ∐_ν ∏_{p∈P_ν} X_{σ(p)} natural in relabelling constants (no quotient by permutations); apply it degreewise to X = Δ^r to get a simplicially enriched ccc 𝒦 whose homs are nerves of posets ∐_ν ∏ [r_p]; rectify 𝓕 to a strictly enriched ccc D (Haugseng; enriched injective presheaves); interpret 𝒦 → D degreewise; the retract 𝓕 → 𝒦 → D ≃ 𝓕 makes 2-cell spaces of 𝓕 retracts of poset mapping spaces. In particular duplication creates [1]^m, not ambiguity. So **Dir is sound for every context whose non-invertible generators have dimension ≤ 2**.

## The criterion

**(Dir)**, from Mimram's tool cccatt (`src/pasting.ml`). For a goal of dimension n:
1. The n-dimensional hypotheses must be cells x → y between variables, with:
   - no loops;
   - pairwise distinct sources and pairwise distinct targets;
   - an acyclic relation "x → y".
2. Let the **source context** be the context without the targets of these cells, and the **target context** the context without their sources. Both must, recursively, accept the goal's (n−1)-dimensional type.
3. The goal's source term must avoid targets, and its target term must avoid sources.

There is no fullness condition. With no n-dimensional hypotheses, every parallel pair of terms of a pasting (n−1)-type is accepted, in both directions.

*(Note: the unordered implementation at commit 69bb11af does not enforce distinctness in step 1, because it compares position-carrying terms (filed as smimram/cccatt#15). The question is about the abstract criterion above, not the implementation.)*

## Questions

1. **(Smallest open case.)** Take f, g : A → B, 2-generators α, α′ : f ⇒ g (parallel), and one 3-generator Ξ : α ⇛ α′. (This is Dir-pasting.) In the free cartesian closed (∞,ω)-category 𝒞(Γ), is the space of 3-cells between any two parallel 2-cells empty or contractible? Concretely: with a term using f twice through the diagonal, the 3-cells ⟨Ξ, 1⟩ ∗ ⟨1, Ξ⟩-type composites in the two orders, and the interchange of Ξ with α′ along the two coordinates: are all parallel 3-cells connected by an essentially unique 4-cell?
   - The round-1 method needs a strict model whose hom (∞,1)-categories are nerves of posets. Here the candidate replaces the constant family Δ¹ by the free (∞,2)-category (or a Θ₂-set) on the 2-globe with Ξ: is there a simplicially (or Θ₂-) enriched ccc model built degreewise from long normal forms, with homs that are "free on a poset of addresses", and does the rectification/retract argument go through one dimension up?
2. **(General Dir.)** For every Dir-pasting context (generators in any dimension, Dir's recursive conditions), is every Dir-accepted goal fillable with a contractible filler space?
3. **(Counterexample search.)** If 1 fails, give two parallel 3-cells in 𝒞(Γ) with no 4-cell between them, or with a non-contractible space of 4-cells, ideally detected in a strict cartesian closed 3-category model.

## What counts as a solution

A proof of Question 1 or 2, a counterexample with an explicit model, or a reference proving relative coherence for free cartesian closed higher categories with generators of dimension ≥ 3.

## Literature (searched 2026-11-18)

- Mimram (CSL 2026), and the tool cccatt.
- Fiore–Saville (MSCS 2021), dimension 2 over a graph.
- Hirschowitz, arXiv 1307.6318: free strict cartesian closed 2-category on a 2-signature (Thm 7.11).
- Ozornova–Rovelli–Walde (arXiv 2603.11005): the core adjunctions.
- Haugseng (arXiv 1312.3881): rectification of enriched ∞-categories.
- No relative coherence theorem for cartesian closed structure with generators of dimension ≥ 3 was found.
