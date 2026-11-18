# Problem: composites of molecules in CaTT (Gray contexts), round 2

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Round 1 and its verified answer are archived in `answered/gray-contexts-2026-11-18.md`; this prompt does not re-ask anything answered there.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory for weak ω-categories.

- Types are `⋆` and `u →_A v`. Contexts are lists of typed variables. By Benjamin–Markakis–Sarti ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- The only term former is `coh_{P, u →_A v}[σ]`. It needs:
  - P a **pasting context** (a globular pasting diagram);
  - σ a substitution into P;
  - one of two side conditions:
    - (coherence) `Var(u : A) = Var(P) = Var(v : A)`;
    - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality.
- Every term t of a context Γ has a strict image `π(t)` in the free strict ω-category `F(Γ)`.
- `supp(t)` is the set of variables used by t, closed under dependencies in their types.

### 1.2 Molecules

- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes ([arXiv 2404.07273](https://arxiv.org/abs/2404.07273)). Globes and Gray products of molecules are molecules.
- A **layering** of an n-molecule decomposes it into layers, each one n-dimensional atom pasted with lower-dimensional cells.
- Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) proves:
  - frame-acyclic molecules have layerings, corresponding to linear extensions of a partial order on the top cells (Prop. 2.18);
  - the subdivision poset of a frame-acyclic molecule that is **not an atom** is contractible (Thm 2.52);
  - molecules of dimension ≤ 3, and acyclic molecules, are frame-acyclic.
- *Frame-acyclicity is not Steiner's loop-freeness.* Frame-acyclicity corresponds to Steiner's "split" (Hadzihasanovic, Comment 8.3.5). Example 8.3.12 there is a frame-acyclic 3-atom that is not Steiner loop-free.
- **Presenting a molecule U in CaTT.** Each cell x gets a type `⌈∂⁻x⌉ → ⌈∂⁺x⌉`, whose sides are CaTT terms composing the boundary molecules, by induction on dimension.
- A **U-composite** is a term t with `supp(t) = Var(U)` and `t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉`.

> **Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n presented in CaTT:
> - (existence) U-composites exist;
> - (uniqueness) any two U-composites are connected by a CaTT term `t → t′`.

> **RC(n) for a context Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

Existence in G(n) follows from RC(n−1) for U's (n−1)-skeleton. Uniqueness in G(n) follows from RC(n) for U.

## 2. What is known

1. **RC(2) holds in every CaTT context** (Theorem A).
   - Normalize every 2-term to a vertical composite of whiskered 2-variables.
   - 2-terms without 2-variables pull back to the chain of their path, where the coherence rule applies.
   - Two such composites with the same strict image are related by exchange moves, each a coherence over "chain, 2-disc, chain, 2-disc, chain".
2. **G(2) holds, and existence holds in G(3).** In particular, every Gray generator of dimension ≤ 4 has a CaTT type.
3. **Total support lemma** (a strengthening of Benjamin–Markakis, [arXiv 2406.12127](https://arxiv.org/abs/2406.12127), Lemma 36). If c has no variable of dimension `dim c` in its support, then `supp(c) = supp(src c) = supp(tgt c)`.
4. **Terms without 2-variables.** Parallel n-terms with no 2-variable in their support are connected, for every n. They pull back to the chain of their path, and the coherence rule applies there.
5. **The lax square S.** The context is
   - objects `x⁻, x⁺, y⁻, y⁺ : ⋆`;
   - edges `x↑ : x⁻ → x⁺`, `y↑ : y⁻ → y⁺`, `f⁻ : x⁻ → y⁻`, `f⁺ : x⁺ → y⁺`;
   - one 2-cell `F : p → q`, where `p = f⁻ ∗₀ y↑` and `q = x↑ ∗₀ f⁺`.

   What is known about S:
   - *Strict cells.* The 2-cells of `F(S)` are the identities on the 10 paths, and F. S has no 3-variables, so RC(3) for S asks for a 4-term between **every** pair of parallel 3-terms.
   - *Identity 2-boundary: settled.* If the parallel 3-terms α, β have an identity as strict 2-boundary, then F is not in their support. Item 3 puts α and β over the path context `C_w`, and `coh_{C_w, ᾱ→β̄}[ι_w]` connects them.
   - *2-dimensional arity: reduced.* Let `c = coh_{P,u→v}[σ]` be a coherence 3-term with `dim P = 2` and strict 2-boundary F. Then exactly one 2-variable of P goes to a term with image F. All of P's columns except that one lie over `x⁻` or `y⁺`. A coherence over P's middle column, read as a vertical 2-chain Q, connects c to `coh_{Q,ū→v̄}[τ]`.
   - *One coherence never splits F's boundary.* In any `coh_R[δ]` with F in the support of δ, exactly one 1-column of R has a non-empty path, and that path runs from `x⁻` to `y⁺`. So `f⁻` and `y↑` are never separated into different columns inside a single coherence.
6. **The Gray cube's loops reduce to one hemisphere.** Let U be the Gray cube, X its 3-cell, and `A = ⌈∂⁻U⌉`. By item 3, a 3-term `H : A → A` without X has support in the negative hemisphere `∂⁻U`, which has three faces.

## 3. What remains, and why

In dimension 2, the runs of cells with no top variable live over a single path, and the coherence rule settles them. In dimension 3 they live over a 2-dimensional context, such as S, which is not a pasting context.

Item 5 settles S except in one case. Both parallel 3-terms have strict 2-boundary F, and at least one of them is a composite over a **3-dimensional** arity, or is a coherence whose middle-column 2-terms `τ(ξ_k)` are arbitrary.

The Squier-style route needs one normalization 3-cell `ν_P : P → N(P)` for each 2-term P with image F, chosen once and for all (Theorem A gives one). It must be compatible, up to 4-cells, with every whiskered elementary 3-cell b, i.e. `ν_{src b}` must be connected to `b ∗₂ ν_{tgt b}`. Item 4 settles the part of this inside F-free runs. So the remaining compatibility is with `∗₁`-composition by 2-terms that contain F.

RC(3) fails in general. In `(x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell and the identity are expected not to be connected, since they give a non-zero class in π₃(S²). (This is a sketch, not checked in detail.) So any proof must use some acyclicity of the context, and which notion it needs is part of question 3.

## 4. Questions

Each question asks for explicit CaTT terms, built with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: the F-boundary case of the lax square.** Let `α, β : t → t′` be parallel 3-terms of S with `π(t) = π(t′) = F`. Construct a 4-term `α → β`.
   - *Smaller first step:* take α and β to be coherences over 2-dimensional arities. By item 5, both reduce to coherences over vertical 2-chains Q, Q′ whose middle 2-terms are arbitrary. Connect them.
   - *Equivalent form:* exhibit a choice of `ν_P` for 2-terms P with image F, and prove that `ν_{u ∗₁ W}` is connected to `(ν_u ∗₁ ν_W) ∗₂ (flattening coherence)` whenever W contains F.
2. **The Gray cube.** Let `U = D¹ ⊗ D¹ ⊗ D¹`, presented with hexagon composites. Prove that every X-free 3-term `H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉` is connected to the identity. By item 6, this is RC(3) for 3-loops over the three-face negative hemisphere. This gives uniqueness in G(3) for the cube.
3. **RC(3) for acyclic contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule, or its skeleta. Or prove it for every finite Steiner loop-free computad, and say which hypothesis the proof uses.
4. **G(n) for all n.** Prove RC(n), or the weaker G(n), for such contexts.
   - Chanavat's contractible subdivision poset (Thm 2.52, non-atoms) indexes composites but does not construct them.
   - A proof must give a CaTT composite for each subdivision, comparisons for refinements, and higher comparisons for chains of refinements.
   - It must also show that **arbitrary** CaTT composites are controlled by those comparisons.

## 5. What counts as a solution

Any of the following counts:
- explicit terms for question 1 or 2;
- a proof of RC(3) or RC(n) on acyclic contexts;
- a counterexample: an acyclic context with two parallel terms of equal strict image and no term between them;
- a published reference.

## 6. Literature (searched 2026-11-18)

- No paper treats composites of non-globular molecules inside CaTT or inside Grothendieck–Maltsiniotis weak ω-categories.
- The (∞,n) pasting theorem, the semantic analogue of G:
  - Campion, [arXiv 2311.00200](https://arxiv.org/abs/2311.00200);
  - Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), Thm 3.17 (Thm 3.29 is monoidality for the Gray product).
  - No comparison between CaTT's models and (∞,ω)-categories is known, so these do not transfer directly.
- Di Vittorio, [arXiv 2205.15486](https://arxiv.org/abs/2205.15486): a Gray-categorical pasting theorem. It covers only composites output by its algorithm, and the paper says it is open whether every composite arises that way.
- Hadzihasanovic's diagrammatic sets ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639), [arXiv 2007.14505](https://arxiv.org/abs/2007.14505)) take unique weak composites of round molecules as the definition of a weak higher category.
- Benjamin–Markakis–Sarti ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)) and ICaTT ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)): composites of coherences are invertible.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): 2-cells of free 2-categories as 2-paths modulo exchange, and Squier-style coherence.
