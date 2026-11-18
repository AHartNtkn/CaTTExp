# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** A construction for **all** pairs (and finite families) of pasting diagrams, or a proof that none exists. The question is purely syntactic: whether chosen terms can be made to match their boundaries on the nose, in a theory with no definitional equalities.

## 1. Setting

**CaTT** (Finster–Mimram, LICS 2017, arXiv 1706.02866). Types are `⋆` or `u →_A v`. Terms are variables or `coh_{P, u →_A v}[σ]`, where P is a context presenting a globular pasting diagram, σ is a substitution into P, and either (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`. The type of `coh_{P, u→_A v}[σ]` is `u[σ] →_{A[σ]} v[σ]`. **Definitional equality is syntactic identity.** A context is well formed when, for each variable `x : u →_A v`, the terms u and v have type A syntactically.

**Gray tensors.** For globular pasting diagrams Θ, Δ, let λΘ, λΔ be their Steiner complexes and ν(λΘ ⊗ λΔ) the strict ω-category of the tensor (Steiner, *Omega-categories and chain complexes*, HHA 2004). Its generators are the pairs y ⊗ x of cells, of dimension dim y + dim x, with boundary given by the Leibniz formula. Its cells are molecules (Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273) and are determined by their sets of generators.

**The family context.** Fam(Θ ⊗ Δ) has one variable v_g per generator g, typed `T(∂⁻g) → T(∂⁺g)`, where T(c) is a CaTT term over the earlier variables denoting the cell c.

## 2. Statement

> **Conjecture CT.** For all finite globular pasting diagrams Θ, Δ there is an assignment T from cells c of ν(λΘ ⊗ λΔ) of dimension ≥ 1 to CaTT terms over Fam(Θ ⊗ Δ) such that
> - (a) T(g) = v_g for every generator g;
> - (b) T(c) is built from the variables by coh terms, and its strict interpretation (v_g ↦ g) is c;
> - (c) `T(c) : T(∂⁻c) → T(∂⁺c)` holds **syntactically** for every cell c. In particular Fam(Θ ⊗ Δ) is well formed.

The same question for iterated tensors λΘ₁ ⊗ ⋯ ⊗ λΘ_k.

## 3. What is known

1. **Low dimensions.** For Θ, Δ of dimension ≤ 1, binary composites can be chosen consistently by hand.
2. **D² ⊗ D¹: CT holds.** With binary composites for two-edge paths and whiskering coherences typed `f ∗ h ⇒ g ∗ h`, all boundaries of the layers agree syntactically.
3. **D¹ ⊗ D¹ ⊗ D¹: CT fails for every T built from layerings.** Here "layered" means T(c) is the vertical composite, along a layering of the molecule c, of whiskered generators. The source hexagon of the top cell has a unique layering whose first two layers are a square whiskered on the right and a square whiskered on the left, meeting at a 3-edge path. The first layer's target contains a subterm denoting the 2-edge path bc, and no subterm of the second layer's source denotes bc (in CaTT every term uses exactly the variables of its strict image). So the two sides bracket the 3-edge path differently, and (c) fails.
4. **The weak form holds through dimension 4.** Replace (c) by (c′): T(c) has a type `u → v` with u, v connected to T(∂⁻c), T(∂⁺c) by invertible coherence cells, and the context is made well formed by inserting these coherences into the variables' types. (c′) holds for every generator of dimension ≤ 4: conjugate each layer by associators to a fixed bracketing of paths (dimension ≤ 3), and use that any two parallel 2-terms of any context with equal strict image are connected by a 3-term (dimension 4). In higher dimensions (c′) follows from the analogous statement for parallel (n−2)-terms in loop-free contexts.
5. **Single coherence heads do not avoid the problem directly.** Taking T(c) to be one composition coherence `coh_{P, u→v}[σ]` per cell requires T(∂^±c) to be literally of the form u[σ], v[σ] for terms u, v over P. This fails when the boundary is a composite of lower cells that are not among σ's arguments.
6. **Semantics is settled.** The (∞,ω) Gray tensor of pasting diagrams is the free (∞,ω)-category on the Steiner tensor (Campion, arXiv 2311.00205, Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29). CT is only about syntax.

## 4. Questions

**Q1 (main).** Decide CT for all Θ, Δ. Item 3 rules out layered terms only. A positive answer may use any terms: non-layered composites, single coherence heads over chosen pasting diagrams, terms whose bracketing of each boundary path is chosen globally (for example by a fixed total order on the generators of every molecule that is respected by every boundary), or assignments defined by induction on dimension with all lower choices made simultaneously.

**Q2 (if CT fails).** Prove that no assignment satisfies (a)–(c) for D¹ ⊗ D¹ ⊗ D¹ (or for some other pair), and identify the minimal extra rule that makes the family contexts well formed, for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings. A precise description of which equations are forced is the useful answer.

**Q3 (iterated tensors).** If CT holds for pairs, does it hold for λΘ₁ ⊗ ⋯ ⊗ λΘ_k, compatibly with the associativity of the tensor (the two assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming)?

## 5. What counts as a solution

An explicit construction of T for all Θ, Δ; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18)

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.
