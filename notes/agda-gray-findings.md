# Agda milestone: the two-tier L core

*2026-11-18. Code: `src/CaTTExp/TypingWith.agda`, `Subst.agda`, `Gray/`. Everything called "checked" or "proved" below is verified when `src/Everything.agda` type-checks (Agda 2.6.3, `--safe`, no postulates). Companion to `pseudo-vs-gray.md` §3 and §7.1 steps 2–3; ledger rows A1, E1–E3.*

## What is formalized

**One judgment family, two side conditions.**
- `TypingWith 𝕊 side` is the CaTT judgment family with the coh side condition as a parameter: a boolean function of the coh's own (Δ, A, t, u).
- Plain CaTT is `Typing` (Finster–Mimram's `isCoh ∨ isOp`).
- Two-tier L is `Gray.Typing` (`graySide`).
- The certified checker `CheckWith` serves both. Every success returns a derivation; the checker is not proved complete.

**Substitution is admissible, for every side condition** (`Subst.tm[]`, `ty[]`, `sub∘`). The proof never inspects the side condition. That is the formal content of "side conditions are checked only on the coh's own context, so substitution cannot invalidate them" (§3.6). The one hypothesis is that constants have closed types; the empty signature satisfies it. `Gray.Pure.substL` is the L instance.

**The L side condition** (`Gray/Support.agda`).
- A pasting context Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ is decomposed into its homs.
- A basis element of K(Γ) = λΘ₁ ⊗ … ⊗ λΘₙ is a tuple of variables, one per hom; the empty tuple is the unit.
- `topS t` is the support of the top chain of t's strict image. Variables give singletons. A coh gives F_σ of its cell in K(Θ): the total cell T in the operation case, an identity (top chain 0) in the coherence case. F_σ sends a tuple to the product of the supports of the substituted terms. Composition across objects is concatenation of tuples.
- All chains involved are non-negative, so sums and tensors of chains have supports that are unions and products of supports. No integer arithmetic is needed to compute supports.
- T's table is the Steiner/Ara–Maltsiniotis tensor formula (x⊗y)^ε_k = Σ_{i+j=k} x^ε_i ⊗ y^{(−1)^i ε}_j, applied to the tables of the pasting diagrams ⟨Θₖ⟩.
- Decidability is by construction: the side condition is a boolean function.

## Checked results

(`Gray/Examples.agda`, `Gray/Cube.agda`)

1. **Orientation.** Over ΣD¹ ∨ ΣD¹ (α : f ⇒ f′, β : g ⇒ g′), the unfolding computes
   - ∂⁻(α⊗β) = f⊗β + α⊗g′, i.e. (f◁β);(α▷g′), β first;
   - ∂⁺(α⊗β) = α⊗g + f′⊗β, i.e. (α▷g);(f′◁β), α first.

   This matches §3.4.
2. **The interchanger is accepted in one direction only.** coh (f◁β);(α▷g′) ⇛ (α▷g);(f′◁β) is derived; it is the operation case, not the coherence case. For the reverse coh, the side condition evaluates to false. So `no-ich⁻` *proves* that no derivation of the reverse coh exists, in any context, with any substitution or claimed type. Plain CaTT accepts both directions.
   - Read as Example 1 (α a transformation, φ an element arrow), the accepted direction is α_x ; Gφ ⇛ Fφ ; α_y. That is lax naturality as in §3.1, and the term is literally the interchanger.
   - It is also the orientation (u◁φ);(β▷v′) ⇛ (β▷v);(u′◁φ) that the limit rules force (R11).
3. **No horizontal composite across objects.** CaTT's horizontal composite over ΣD¹ ∨ ΣD¹ fails L's side condition, by refl; CaTT accepts it. The two whiskered composites βα and αβ are both derived.
4. **Inside one hom, L is CaTT on the PR #4 examples.** Identity, composite, associator, left unitor and vertical composite are accepted. For the two negative examples, the side condition is false by refl, so no derivation of those cohs exists. Only horizontal composition, which crosses objects, changes.
5. **Suspension.** The suspension of the interchanger (a coh over Σ(ΣD¹ ∨ ΣD¹), i.e. 2-cells inside one hom) is accepted in *both* directions, as a coherence. Two-tier L directs only interchange across objects.
6. **The Gray cube.** Over ΣD¹ ∨ ΣD¹ ∨ ΣD¹ the two hexagons are built from the six whiskered interchangers. The ∂⁻ hexagon uses faces fβγ, αg′γ, αβh; the ∂⁺ hexagon uses αβh′, αgγ, f′βγ. The hexagons are ordinary terms over pasting contexts, with the same boundary, and the 4-cell hex⁻ ⇛ hex⁺ is a single operation-case coh. The reverse 4-cell's side condition is false (`no-cube⁻`).
7. **Vertical composition of transformations** in one hom is the CaTT composite, and its associator is a coherence in both directions.

## Precisions to `pseudo-vs-gray.md` §3

One classification in §3.6 was wrong; it is now corrected there. §3.6 listed "the non-degeneracy argument in 2" among the results proved outright, with no lemma needed. But its last step, "every derivable term is interpreted", is soundness, and soundness uses (B). Non-degeneracy therefore holds under the same hypotheses as Theorem 1. Those hypotheses are now discharged in the literature, so the conclusion stands.

Writing the rule down exactly also fixed three details:

- **Support convention.** supp(t : A) is type-directed: the top support of t together with that of every cell in A, as for Var(t : A). Side conditions compare **downward closures** in K(Γ), as §3.6 says ("the downward-closed set"). That is also the form in which lemma (B) is known: molecules are determined by their closed subsets (Hadzihasanovic).
  - Closures are needed. The table support of the total cell misses the 0-cells f⊗g′ and f′⊗g of D¹ ⊗ D¹, and on a single hom it misses the middle 1-cell g of f ⇒ g ⇒ h. So supp = Var (§3.2 [conj]) is false for table supports and can only hold for closed ones.
  - Checked: the closure of Supp(T) for ΣD¹ ∨ ΣD¹ is all 9 basis elements, and f⊗g′ ∉ Supp(T).
  - An earlier draft of this PR compared table supports. All examples give the same verdicts under both conventions.
- **Dimension in the operation case.** The rule requires dim A = d := Σ dim Θₖ explicitly, i.e. the composite is a (d+1)-cell (§3.3 "the dimension changes"). Given soundness this follows from the support equalities. Without soundness it is an extra, harmless check.
- **The cube's hexagons need associators.** With unbiased ternary composites of 1-cells as boundaries, a hexagon is a vertical composite of whiskered interchangers *and associators* (coherences). The faces are cohs over three-factor contexts with one point factor, e.g. ΣD¹ ∨ ΣD¹ ∨ ΣD⁰. Substituting the two-factor interchanger would produce binary composites of 1-cells, which then need further associators.

## Not yet proved

- **The non-negativity bridge.** Supports are computed on sets: the support of a sum is the union, and the support of a tensor is the product. This is correct only if every chain involved has non-negative coefficients. They do: T's chains are sums of basis elements, and F_σ maps basis elements to supports of top chains of the same kind. But this is argued in `Gray/Support.agda`'s header, not proved in Agda; the integer chains are never built. The side condition as implemented is a precise decidable rule either way. The bridge is needed only to connect it to the strict model, i.e. for Theorem 1 soundness.

- **Conservativity on a single hom.** For Γ = ΣΘ, L's side condition should equal Finster–Mimram's. This splits into two halves.
  - *Rule-level half: checked for all small diagrams.* The closed supports of T, ∂⁻T and ∂⁺T must be exactly the non-object variables of Γ, ∂⁻Γ and ∂⁺Γ, using PR #4's `srcVars`/`tgtVars`. `Gray/Bounded.agda` checks this by evaluation for all 196 pasting diagrams Θ with 1–6 edges, and checks that the test distinguishes ∂⁻ from ∂⁺ on each. It also checks, for every pasting context with 1–5 edges and any number of homs, that ↓Supp(T) is all of K(Γ).
  - *Term-level half: not proved.* For derivable t : A over ΣΘ, ↓supp(t : A) should equal the non-object part of Var(t : A).
  - The inclusion ⊆ (entries of supports are free variables) is syntactic and holds for all terms.
  - The inclusion ⊇ is where a proof gets stuck. F_σ does not commute with downward closure when σ sends a cell to an identity-like term, i.e. a coherence-case coh, whose top support is empty. Then F_σ(α) = ∅ while F_σ(∂α) ≠ ∅. Example: the middle 1-cell g of f ⇒ g ⇒ h lies in the closure of the vertical composite's support but not in its table support.
  - So the induction needs the invariant "a derivable cell with empty top support has boundaries with equal closed supports". That is the support-level shadow of "coherence-case cohs are identities in the strict model", i.e. of Theorem 1 soundness, which needs lemma (B).
  - **Finding:** conservativity (Thm 1(3)) and non-degeneracy (Thm 1(2)) share one missing layer, the strict interpretation with (B). They are not independent proofs, as §3.6 suggests for (3).
- **Non-derivability of the reverse interchanger as any term** (Theorem 1(2)): *now proved, with two explicit hypotheses* (see the next section). The integer-chain layer is avoided: chains are bags (non-negative by construction), and the chain equation is written additively, ∂⁺c + x⁻ = ∂⁻c + x⁺.
- **Validation against the strict model on examples** (chain-level, not just supports): not done. It needs the same integer-chain layer.

## Strict-model soundness (`src/CaTTExp/Strict/`)

*Added 2026-11-18.* The strict interpretation of two-tier L in Steiner's ν(K(Γ)) is formalized.

- `Strict/Cell.agda`: cells of ν(K) for an abstract complex with a basis (Steiner 2004 Def. 2.8), as towers of bags; transport of cells along chain maps.
- `Strict/Complex.agda`: K(Γ) hom by hom, basis = composable tuples of hom cells, boundary by the Leibniz rule.
- `Strict/Subst.agda`: top supports commute with substitution, topS(t[σ]) ≈ F_σ(topS t). This replaces lemma (C) by a proof.
- `Strict/L.agda`: every variable of a pasting context is a cell; a cellular substitution induces a chain map, which sends cells to cells.
- `Strict/Soundness.agda`: `sound-tm`, every derivable term t : A over a pasting context is a cell of ν(K(Γ)) with t's table.
- `Strict/ReverseInterchanger.agda`: `no-reverse-interchanger`, no term of any shape has type (α▷g);(f′◁β) ⇛ (f◁β);(α▷g′) over ΣD¹ ∨ ΣD¹. The proof counts f′⊗β on both sides of the chain equation: |c| + 1 against 0.

The two hypotheses are module parameters, so every use of them is visible in the types:
- **(T-cell)** the total cell built from `chainT` is a cell between the context's first and last object (Ara–Maltsiniotis, arXiv 1607.00668, §A.16, Prop. 4.13);
- **(B-supp)** cells of ν(K(Θ)) of the same dimension with equal downward-closed supports are equal (Hadzihasanovic, arXiv 2404.07273; proved for every Steiner complex in `conjectures/steiner-support-determines-cells.md`).

Both are true statements in the literature; what the formalization takes on trust is that `chainT` and `down` compute the objects those statements are about.
