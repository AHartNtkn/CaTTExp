# Conjecture: Gray contexts in CaTT (composites of molecules, and Mikhail's Gray rules)

> **To send to a researcher, use [`outbox/gray-contexts.md`](outbox/gray-contexts.md)**, a clean standalone prompt with the current status (2026-11-18). This file keeps the history, earlier responses and verifications.

*Self-contained problem statement. Familiarity with the type theory CaTT (Finster–Mimram, LICS 2017, arXiv 1706.02866) is assumed, and the relevant parts are recalled in §1. Partial results are in §3. Status: G is open beyond the dimensions listed in §3. In §6 (formerly `gray-contexts-steiner.md`), parts (1)–(2) are open and part (3) is answered (§7).*

## 1. Background

**CaTT in brief.**
- Types are ⋆ and t →_A u.
- Contexts are lists of typed variables. By Benjamin–Markakis–Sarti (arXiv 2405.00398), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- The only term former is coh_{P, t→_A u}[σ]. It requires P to be a **pasting scheme** (a globular pasting diagram) and σ a substitution into P, together with one of two side conditions:
  - **(coherence)** Var(t : A) = Var(P) = Var(u : A);
  - **(composition)** Var(t : A) = Var(∂⁻P) and Var(u : A) = Var(∂⁺P).
- Definitional equality is syntactic.

A variable's type may be a composite. For example, f : x → y, g : y → z, h : x → z, τ : g·f → h is a valid context, even though it is not a pasting scheme.

**Molecules and Gray products.**
- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*). Globes are molecules, and so are Gray products U ⊗ V of molecules. The cells of U ⊗ V are pairs x ⊗ y, with Steiner's boundary formula

  ```
  ∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y)
  ```

  Chanavat (arXiv 2505.01387), Prop. 2.16, gives the boundary formula at all levels.
- A **layering** of an n-molecule U is a decomposition of U as a sequence of n-dimensional atoms, each "whiskered" by lower-dimensional cells and pasted one after another.
- Chanavat, *A strengthened (∞,n)-categorical pasting theorem* (arXiv 2603.22242), gives several relevant results:
  - for **frame-acyclic** molecules, pre-layerings correspond to pre-orderings (Prop. 2.18);
  - the poset of subdivisions is contractible (Thm. 2.52);
  - all molecules of dimension ≤ 3 are frame-acyclic, and so are all acyclic molecules;
  - as a consequence, frame-acyclic molecules have essentially unique composites in (∞,n)-categories.

## 2. Statements

To write a Gray product U ⊗ V as a CaTT context, each generator x ⊗ y needs a type ∂⁻(x⊗y) → ∂⁺(x⊗y). Both sides must be **CaTT terms** that compose the boundary molecules, and the type must be well formed. The two sides must have *syntactically* equal boundaries, since CaTT has no other definitional equality.

**Definition.** For a molecule U that has been presented as a CaTT context, a **U-composite** is a CaTT term t in that context with

```
Var(t) = Var(U)    and    t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉
```

where ⌈−⌉ denotes a chosen U-composite of the lower-dimensional boundary, defined by induction on dimension.

**Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n that is presentable as a CaTT context:
- **(existence)** U-composites exist;
- **(uniqueness)** any two U-composites are related by a CaTT term of type t → t′ that is invertible, i.e. has an inverse up to higher CaTT cells.

**Corollary of G(n) for all n.**
- (a) For pasting schemes P, Q, the Gray product P ⊗ Q is presentable as a CaTT context. Its generators' types are built from U-composites of the boundary molecules, by induction on dimension.
- (b) Extending coh from pasting schemes to frame-acyclic molecules, with the same two side conditions, is a **conservative extension** of CaTT: every new term is equivalent to a CaTT term.

The converse holds as well: (b) implies G(n). So G is exactly the question of whether "molecular coherences" add anything.

## 3. Partial results

### 3.1 G(1) (proof)

1-molecules are paths x₀ → x₁ → … → x_m, which are pasting schemes. Any two composites using all variables are full terms over a pasting scheme, so the coherence side condition gives the comparison cells in both directions.

### 3.2 Existence in G(2), hence Gray generators of dimension ≤ 3 (proof sketch)

Let U be a 2-molecule (dimension ≤ 3 implies frame-acyclic). Choose a layering S₁, …, S_k:
- each Sᵢ is a single 2-cell variable;
- it is whiskered on each side by paths, and the whiskering is a CaTT composite over a pasting scheme in which the 2-cell's boundary has been substituted.

Consecutive layers meet along composites of the same 1-molecule, possibly bracketed differently. Insert the comparison cells of G(1) between them, and at both ends to reach ⌈∂^±U⌉. The resulting vertical composite is a U-composite. ∎

Consequence: **every Gray generator of dimension ≤ 3 has a CaTT type.** The boundary of a dimension-3 generator is a 2-molecule. This covers D¹⊗D¹, D²⊗D¹, D¹⊗D² and the Gray cube D¹⊗D¹⊗D¹. It reproduces and extends Mikhail's construction (arXiv 2412.13310, §4.1), which handles Γ ⊗ D¹ for globular Γ.

### 3.3 Uniqueness in G(2), hence Gray generators of dimension 4 (proof sketch with one gap)

Two U-composites built from layerings L and L′:
- Layerings of a frame-acyclic 2-molecule correspond to linear extensions of a partial order on its 2-cells (Chanavat, Prop. 2.18).
- Any two linear extensions of a finite poset are connected by adjacent transpositions of incomparable elements. This is a standard fact.
- An adjacent transposition swaps two consecutive layers whose 2-cells are incomparable, i.e. side by side. The two composites are then instances, after substituting composite boundaries for 1-cell variables, of the two sides of the **exchange coherence** over the pasting scheme with two horizontally adjacent 2-cells. That coherence is invertible.
- The connecting G(1) cells differ between L and L′, but any two parallel G(1) cells are themselves related by coherences over a pasting scheme.

**Gap.** The cell built from these pieces has to be checked to have exactly the type t → t′ syntactically. That needs a careful bookkeeping argument, which we have not written.

Granting it, G(2) holds, and every Gray generator of dimension 4 (e.g. D²⊗D², D³⊗D¹, D¹⊗D¹⊗D¹⊗D¹) has a CaTT type.

### 3.4 Where the induction stalls

For G(n) with n ≥ 3, two layerings of an n-molecule may differ by moves that are not single swaps of independent atoms. The relevant combinatorics is Chanavat's contractibility of the subdivision poset (Thm. 2.52). The missing step is to **translate a contractible poset of subdivisions into a family of CaTT cells**, with:
- a 1-dimensional CaTT cell for each edge of the poset;
- higher CaTT cells for its higher simplices;
- each realised as a substituted instance of a coherence over a pasting scheme.

This is a syntactic, "algebraic" form of Chanavat's homotopical pasting theorem. Chanavat's result is about (∞,n)-categories; CaTT's models are Grothendieck–Maltsiniotis weak ω-categories, where the pasting theorem has not been proved.

**Question (G-alg).** Does the conclusion of Chanavat's Thm. 2.52, contractibility of the subdivision poset of a frame-acyclic molecule, imply G(n) for CaTT, through an explicit translation of chains of subdivisions into substituted coherences?

## 4. Why it matters

Gray products of globes are the shapes of lax transformations and their higher analogues. A type theory in the CaTT style can name these shapes as contexts only if their generators can be typed by terms of the theory. G also decides whether allowing coherences over arbitrary frame-acyclic molecules, not just globular pasting schemes, adds anything.

## 5. What would count as a solution

Any of the following:
- a proof of G(n) for all n (equivalently, conservativity of molecular coh over CaTT);
- a proof of the bookkeeping step in §3.3 together with a positive answer to G-alg;
- a counterexample: two composites of a frame-acyclic molecule that are not related by any invertible CaTT cell.

*This file merges two earlier problem files: the former `gray-contexts-steiner.md` is now §6. §1–§5 ask the general syntactic question for pasting schemes. §6 asks whether one specific published rule set (Mikhail's) produces Gray contexts `M ⊗ Dⁿ` for every context M and every n. Problem N in `naturality-arbitrary-depth.md` is the case n = 1 for arbitrary contexts, stated as an explicit family of cells. G(n) for all n should imply N (see that file, §8); a verified review found that §8's argument fails as written for composition constructors, so the implication needs re-checking (open-issues D3a).*

## 6. Second form: Mikhail's Gray rules for arbitrary contexts

### 6.1 Background

**CaTT contexts are finite computads** (Benjamin–Markakis–Sarti, [arXiv 2405.00398](https://arxiv.org/abs/2405.00398)).
- A context lists variables `x : A`, where A is `⋆` or `t →_B u`, with t and u terms over earlier variables.
- A context presents the free weak ω-category on the corresponding computad (Dean–Finster–Markakis–Reutter–Vicary, Adv. Math. 2024).

**Mikhail's Gray rules** ([arXiv 2412.13310](https://arxiv.org/abs/2412.13310), §4.2) define, for a context M and each n ≥ 1, a judgment `M₁; …; M_{2n+1} gray M₁`. It is derived in two steps:
- duplicate each variable x of M into layers;
- at the layers 2i+1, add a connecting cell `p_x : s → t`.

The source and target of `p_x` are fixed only through free-variable conditions:
- **τCond:** `FV(s) = FV(x) ∪ ⋃{FV(p_y) | p_y in the current layer, y ∝ τ(p)…}`;
- **σCond:** the same condition, with x′ and the source;
- here `y ∝ t` means "y occurs linearly in t at top dimension", i.e. there is a unique path through operations and coherences.

The resulting context `M₁, …, M_{2n+1}` is meant to be `M ⊗ Dⁿ`. **Mikhail proves existence only for n = 1 (Thm 4.4).** The general existence of cones relies on his Conjecture 3.6.

### 6.2 Statement

1. **Existence.** For every finite CaTT context M and every n ≥ 1, there are layers `M₁ = M, M₂, …, M_{2n+1}` and connecting cells satisfying Mikhail's rules. Give an explicit formula for the types of the connecting cells, as composites of cells of M and of lower layers.
2. **Presentation.** Suppose M is a pasting scheme, or more generally that the free strict ω-category on M is a Steiner complex. Then the computad presented by `M ⊗ Dⁿ` generates, *as a strict ω-category*, the Steiner Gray tensor `𝒪(M) ⊗ 𝒪(Dⁿ)`.
3. **Weak version.** The free (∞,ω)-category on `M ⊗ Dⁿ` is the Gray tensor of the free (∞,ω)-categories on M and on Dⁿ. *Answered for pasting schemes; see §7.*

### 6.2a Caveat: the raw judgment is permissive

Mikhail's side conditions constrain free variables and the linearity of the *new* variable only. An external researcher showed that the analogous cone judgment admits non-canonical cones, which reuse earlier projections; see `lax-colimit-of-point.md`, verified counterexample. The Gray judgment has the same style of side condition, so it presumably admits non-canonical "Gray contexts" too. (1) should therefore ask for *some* derivation, given by an explicit formula. (2) is about that specified construction, not about every context the judgment admits.

### 6.3 Relation to §2

For M a pasting scheme, (1) is the existence half of G applied to the molecules ∂(x ⊗ y) with y a cell of Dⁿ, together with the requirement that the composites satisfy Mikhail's τCond and σCond. For M an arbitrary context, the generators' boundaries are themselves composites. Then (1) needs the naturality cells of `naturality-arbitrary-depth.md` (n = 1), or their analogues for Dⁿ.

### 6.4 What would count as a solution

A proof of (1) and (2), possibly by translating Mikhail's free-variable conditions into Steiner's basis description, or a counterexample context.

## 7. Literature status (searched 2026-11-18)

**G(n) and G-alg: open.** No paper on composites of non-globular molecules inside CaTT, or inside Grothendieck–Maltsiniotis weak ω-categories, was found. Related results:
- **The (∞,n) pasting theorem.** Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), and Campion, [arXiv 2311.00200](https://arxiv.org/abs/2311.00200), prove the semantic analogue of G in (∞,n)-categories. No comparison between CaTT's models and (∞,ω)-categories is known, so this does not transfer.
- **Diagrammatic sets.** Hadzihasanovic, *Representable diagrammatic sets* ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639)) and *Diagrammatic sets and rewriting in weak higher categories* ([arXiv 2007.14505](https://arxiv.org/abs/2007.14505)), take "every round molecule has a weak composite, unique up to equivalence" as the *definition* of a weak higher category. Chanavat–Hadzihasanovic, *Equivalences in diagrammatic sets* ([arXiv 2410.00123](https://arxiv.org/abs/2410.00123)), develop the calculus of equivalences there. So G asks whether CaTT models are "representable" in this sense.
- **Uniqueness only needs connecting cells to exist.** Benjamin–Markakis–Sarti, *Invertible cells in ω-categories* ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)), give a criterion and an algorithm for invertibility in computads, and show that invertible cells are closed under all operations. Benjamin–Champin–Markakis, *A type theory for invertibility in weak ω-categories* ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)), give ICaTT, a conservative extension of CaTT that witnesses invertibility syntactically. Coherence cells (full terms) are invertible, so in G the uniqueness half reduces to constructing *some* connecting cell from substituted coherences.

**§6 (Mikhail's rules).**
- **(1) and the matching half of (2): open.** Mikhail's thesis (*Type Theory for (∞,∞)-Categories, and Decomposition Spaces*, UAB; [record](https://ddd.uab.cat/record/321550)) has no general-n existence result.
- **The strict half of (2) is known.**
  - Ara–Lucas ([arXiv 1909.13564](https://arxiv.org/abs/1909.13564)), Cor. 3.11: the Gray tensor of two cofibrant (that is, free) strict ω-categories is free. The proof of their Prop. 3.7 shows that the tensor of strong Steiner complexes is freely generated by its atoms.
  - Campbell, *Parity complexes redux* ([arXiv 2605.09427](https://arxiv.org/abs/2605.09427)), shows that parity complexes are equivalent to strong Steiner complexes. This may help translate free-variable conditions into a basis description.
- **(3) is answered for pasting schemes M.** Campion ([arXiv 2311.00205](https://arxiv.org/abs/2311.00205)), Example 3.2 and Cor. 3.5: the inclusion of strongly loop-free Steiner complexes into flagged (∞,ω)-categories is strong monoidal for the Gray tensor. Independently: Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)), Thm 3.29. So the free (∞,ω)-category on the Steiner Gray tensor 𝒪(M) ⊗ 𝒪(Dⁿ) is Campion's Gray tensor M ⊗ Dⁿ. See `free-infinity-gray-of-pasting-diagrams.md`.
