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
4. **Inside one hom, L is CaTT on the PR #4 examples.** Identity, composite, associator, left unitor and vertical composite are accepted; the two negative examples are still rejected. Only horizontal composition, which crosses objects, changes.
5. **Suspension.** The suspension of the interchanger (a coh over Σ(ΣD¹ ∨ ΣD¹), i.e. 2-cells inside one hom) is accepted in *both* directions, as a coherence. Two-tier L directs only interchange across objects.
6. **The Gray cube.** Over ΣD¹ ∨ ΣD¹ ∨ ΣD¹ the two hexagons are built from the six whiskered interchangers. The ∂⁻ hexagon uses faces fβγ, αg′γ, αβh; the ∂⁺ hexagon uses αβh′, αgγ, f′βγ. The hexagons are ordinary terms over pasting contexts, with the same boundary, and the 4-cell hex⁻ ⇛ hex⁺ is a single operation-case coh. The reverse 4-cell's side condition is false (`no-cube⁻`).
7. **Vertical composition of transformations** in one hom is the CaTT composite, and its associator is a coherence in both directions.

## Precisions to `pseudo-vs-gray.md` §3

None of the note's claims failed. Writing the rule down exactly fixed three details, now recorded in the note.

- **Support convention.** supp(t : A) is type-directed: the top support of t together with that of every cell in A. Under soundness this is the union of the chains of ⟦t⟧'s table, *not* its downward closure.
  - With this convention, the coherence case must compare with Supp(T), the table support of the total cell, not with "all generators of U".
  - Example: in D¹ ⊗ D¹ the 0-cells f⊗g′ and f′⊗g occur only in boundaries of atoms. If the coherence case asked for all generators, it could never fire over ΣD¹ ∨ ΣD¹.
  - Comparing downward closures on both sides would also be consistent. The code uses table supports.
- **Dimension in the operation case.** The rule requires dim A = d := Σ dim Θₖ explicitly, i.e. the composite is a (d+1)-cell (§3.3 "the dimension changes"). Given soundness this follows from the support equalities. Without soundness it is an extra, harmless check.
- **The cube's hexagons need associators.** With unbiased ternary composites of 1-cells as boundaries, a hexagon is a vertical composite of whiskered interchangers *and associators* (coherences). The faces are cohs over three-factor contexts with one point factor, e.g. ΣD¹ ∨ ΣD¹ ∨ ΣD⁰. Substituting the two-factor interchanger would produce binary composites of 1-cells, which then need further associators.

## Not yet proved

- **Conservativity on a single hom, in general.** For Γ = ΣΘ, supp(t : A) ∪ {a₀, a₁} = Var(t : A) for derivable t, and hence L's side condition = CaTT's.
  - Checked on the PR #4 examples only.
  - Proof plan, in progress: (i) top supports commute with substitution, topS(t[σ]) = F_σ(topS t), which holds by construction; (ii) entries(supp) ⊆ Var for all terms; (iii) ⊇ for derivable terms, using that both coh cases have full table support and that 1-cells have non-empty top support.
- **Non-derivability of the reverse interchanger as any term** (Theorem 1(2)). What is proved is that the reverse *coh* has no derivation. Excluding every composite term needs strict-model soundness. That needs integer chain tables, chain maps for substitutions, and lemma (B) "support determines the cell", which is known in the literature (Hadzihasanovic) but not formalized. The plan is soundness as an Agda theorem with (B) as an explicit hypothesis.
- **Validation against the strict model on examples** (chain-level, not just supports): not done. It needs the same integer-chain layer.
