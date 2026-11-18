# Higher coherence for free cartesian closed structure on pasting types

*Self-contained problem statement, 2026-11-18. It asks whether two concrete, decidable criteria for "contractible" higher-dimensional types are sound. Both are implemented in Mimram's proof assistant cccatt, without proofs. No knowledge of the surrounding project is assumed.*

> **Update 2026-11-18.** The (∞,1) questions have an internal proof sketch, `closed-structure.md` C.4, not yet independently reviewed.
> - The free cartesian closed (∞,1)-category on a set or graph has discrete mapping spaces. The proof is normalization by gluing: each hom is a retract of a set of normal forms. Compare Uemura, arXiv 2212.11764.
> - Hence CC-Rev holds.
>
> CC-Dir in (∞,ω) remains open.

## 1. Background

**Simple types and pasting types.** Simple types are built from type variables X, Y, … with → and × (and 1).

Mimram (*An unbiased simply typed combinatory logic*, CSL 2026; tool and source at [github.com/smimram/cccatt](https://github.com/smimram/cccatt)) defines a decidable class of **pasting types**. A type with products is first normalized, by the type isomorphisms of Bruce–Di Cosmo–Longo, to A₁ × … × Aₙ with each Aᵢ implicational. It is pasting iff each Aᵢ is derivable as Θ \ ∅ | ∅ ⊢ Aᵢ in the following system:

```
Θ \ (Θ′, tgt A) | Γ, A ⊢ B                Θ \ Θ′ | Γ, Δ ⊢ A₁   …   Θ \ Θ′ | Γ, Δ ⊢ Aₙ
───────────────────────── (tgt A ∉ Θ′)    ───────────────────────────────────────────────
Θ \ Θ′ | Γ ⊢ A → B                        Θ \ Θ′ | Γ, (A₁ → … → Aₙ → X), Δ ⊢ X
```

Here tgt(A) is the rightmost variable of A.

**Mimram's Theorem 15:** pasting types are contractible, i.e. they have exactly one inhabitant up to βη. A pasting type "in context" Γ ⊢ A means Γ → A is pasting. The resulting theory, with one rule for terms and one for equations, is equivalent to the simply typed λ-calculus with products modulo βη.

**Higher dimensions.** A "context" now contains:
- objects (type variables);
- 1-cells f : A → B between types;
- higher cells α : s → t between parallel terms of the dimension below.

A "goal" is a type of some dimension n: either a 1-type A → B, or an n-type s → t between parallel (n−1)-terms. Terms are built from coh's of accepted goals and substitution, as in Mimram's paper and in CaTT (Finster–Mimram 2017).

## 2. The two criteria

**(Rev), intended for cartesian closed (∞,1)-categories.**
1. Repeatedly pick a hypothesis α of dimension ≥ 2 (a cell between cells of dimension ≥ 1) with a variable endpoint x and other endpoint t such that:
   - x ∉ FV(t);
   - x occurs in the type of no other remaining hypothesis;
   - no rewrite on x was chosen before.

   Delete α and substitute x := t everywhere.
2. When no such hypothesis remains, delete all higher layers of the goal and require the resulting 1-type to be pasting in the remaining 1-dimensional context.

If this succeeds, **every** goal of every dimension with these underlying data is accepted: any two parallel terms are related by a cell, in both directions.

**(Dir), intended for directed higher structure.** Fix a top dimension N; hypotheses above N are contracted as in Rev. For a goal of dimension n:
1. The n-dimensional hypotheses must be cells x → y between *variables*, with:
   - no loops;
   - pairwise distinct sources and pairwise distinct targets;
   - an acyclic relation.
2. The source context Γ⁻ is Γ without the targets of these cells; the target context Γ⁺ is Γ without their sources. Check both, recursively, against the (n−1)-dimensional type of the goal.
3. The goal's source term must not mention targets, and its target term must not mention sources.

There is no "fullness" condition. In particular, with no n-dimensional hypotheses, any two parallel (n−1)-terms of a pasting type get an n-cell in both directions.

## 3. The conjectures

**Conjecture CC-Rev.** Let 𝒞 be the free cartesian closed (∞,1)-category on a set of objects. Equivalently, consider the free one on a finite computad of the kind described in §1, with all cells of dimension ≥ 2 invertible. If a goal is accepted by (Rev), then the space of its fillers in 𝒞 is contractible.
- That is, every two parallel terms over an accepted context are connected by a cell, unique up to a contractible space of higher cells.

**Conjecture CC-Dir.** Let 𝒞 be the free cartesian closed (∞,ω)-category with *pseudo* exponentials on a finite computad. "Pseudo" means Map(A × B, C) ≃ Map(A, C^B) as mapping (∞,ω)-categories, with the cartesian product. Then every goal accepted by (Dir) has a contractible space of fillers. Moreover, the fillers of coherence goals (those with no top-dimensional hypotheses) are invertible.

A weaker form, enough for the intended use: the theory "CaTT with (Dir)-pasting types over the CCC base" has the free cartesian closed (∞,ω)-category as a model.

## 4. Known results (literature status, searched 2026-11-18)

- **Dimension 1:** Mimram, Theorem 15 (pasting ⇒ contractible) and Theorems 19 and 21 (equivalence with STLC and STLC with products modulo βη). Mimram's Agda proof postulates Theorem 15.
- **Dimension 2, over a graph:** Fiore–Saville, *Coherence for bicategorical cartesian closed structure* (MSCS 31(7), 2021; LICS 2020). In the free cartesian closed bicategory on a graph there is at most one 2-cell between any parallel pair of 1-cells, and every cc bicategory is biequivalent to a 2-category with 2-categorical cc structure.
  - So (Dir) with N = 2 and no 2-dimensional hypotheses is sound: two terms of a pasting 1-type are βη-equal, hence related by a unique invertible 2-cell.
  - See also Saville's thesis, [arXiv 2007.00624](https://arxiv.org/abs/2007.00624).
- **Monoidal analogue:** Benjamin (MSCS 2023) gives a type-theoretic definition of monoidal weak ω-categories. Coherence for the planar and symmetric monoidal-closed 1-dimensional cases is classical: Kelly–Mac Lane 1971 for the unit-free symmetric case, and a direct proof for the planar unit-free case is in the project note this file accompanies.
- **No coherence theorem is known** for free cartesian closed (∞,1)- or (∞,ω)-categories, or for cartesian closed tricategories. Mimram's paper states the higher criterion is "left for future work".

## 5. What has been tried

- **Reading the implementation** (commit `69bb11af`, file `src/pasting.ml`) to extract the exact criteria above.
- **The Dir case at dimension 2** reduces to Fiore–Saville as described.
- **Rev** is a based-path contraction. In an (∞,1)-setting, adjoining a cell α : x → t together with its free endpoint x is a trivial extension, i.e. pushout along an anodyne map. So the contraction step preserves the free object up to equivalence. What remains for CC-Rev is the statement for 1-dimensional contexts: the mapping spaces of the free cartesian closed (∞,1)-category, between objects whose hom-type is pasting, are contractible. That is open.

## 6. What would count as a solution

- A proof of CC-Rev, or of CC-Dir (even for N = 3), or a counterexample: an accepted goal with two non-equivalent fillers, or with none.
- A reference proving coherence for free cartesian closed tricategories or (∞,1)-categories.
