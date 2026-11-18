# Gray contexts for all dimensions, and the Steiner Gray tensor

## Background

**CaTT contexts are finite computads** (Benjamin–Markakis–Sarti, [2405.00398](https://arxiv.org/abs/2405.00398)):
- A context lists variables `x : A`, where A is `⋆` or `t →_B u` with t, u terms over earlier variables.
- A context presents the free weak ω-category on the corresponding computad (Dean–Finster–Markakis–Reutter–Vicary, Adv. Math. 2024).

**Mikhail's Gray rules** ([arXiv 2412.13310](https://arxiv.org/abs/2412.13310), §4.2) define, for a context M and each n ≥ 1, a judgment `M₁; …; M_{2n+1} gray M₁`. It is derived by:
- duplicating each variable x of M into layers;
- adding, at layers 2i+1, a connecting cell `p_x : s → t`.

The source and target of `p_x` are fixed only through free-variable conditions:
- **τCond:** `FV(s) = FV(x) ∪ ⋃{FV(p_y) | p_y in the current layer, y ∝ τ(p)…}`.
- **σCond:** the same with x′ and the source.
- Here `y ∝ t` means "y occurs linearly in t at top dimension": unique path through operations and coherences.

The resulting context `M₁, …, M_{2n+1}` is meant to be `M ⊗ Dⁿ`, the Gray tensor with the n-globe. **Mikhail proves existence only for n = 1 (Thm 4.4)**, and the general existence of cones relies on his Conjecture 3.6.

**Steiner's theory**: loop-free augmented directed complexes; Ara–Maltsiniotis, *Joint et tranches* (2020).
- It gives the strict Gray tensor of strict ω-categories.
- Globes have loop-free unital bases.
- The Gray tensor of such complexes is again of that kind, and is the free strict ω-category on a computad.

## Statement

1. **Existence.** For every finite CaTT context M and every n ≥ 1, there are layers `M₁ = M, M₂, …, M_{2n+1}` and connecting cells satisfying Mikhail's rules. Give an explicit formula for the types of the connecting cells in terms of composites of cells of M and of lower layers.
2. **Presentation.** When M is a pasting scheme (more generally, when the free strict ω-category on M is a Steiner complex), the computad presented by `M ⊗ Dⁿ` generates, *as a strict ω-category*, the Steiner Gray tensor `𝒪(M) ⊗ 𝒪(Dⁿ)`.
3. **Weak version** (optional, harder). In (∞,ω)-categories (e.g. Loubaton, [2307.11931](https://arxiv.org/abs/2307.11931), [2406.05425](https://arxiv.org/abs/2406.05425)), the free (∞,ω)-category on `M ⊗ Dⁿ` is the Gray tensor of the free (∞,ω)-categories on M and on Dⁿ.

## What is known

- n = 1 is Mikhail's Thm 4.4. His Remark 4.5 notes that the formula matches one of Ara–Maltsiniotis derived from Steiner complexes.
- Loubaton constructs a Gray tensor on (∞,ω)-categories that preserves colimits in each variable. He also shows that certain pushouts of strict objects are strict (Thm 2.3.3.22). If Free(M) is the iterated pushout of globes along boundary inclusions, then (3) reduces to "globe ⊗ globe is free on its Steiner basis", which is strict input.

## Why it matters

Gray tensors with globes are the shapes of lax transformations and of morphisms between lax cones. A type theory that generates these shapes by syntactic rules needs them to exist in every dimension and to mean what they are supposed to mean.

## What would count as a solution

A proof of (1) and (2), possibly by translating Mikhail's free-variable conditions into Steiner's basis description, or a counterexample context.
