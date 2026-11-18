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

## Invertibility markings (`invertibility-markings.md` §1–2)

`Gray/Marks.agda` encodes the judgments `inv`, `ps` and `ps*` as a decidable function `judge : Nat → Marks → Ctx → Tm → IP` (fuel first; one Bool for each judgment). Marked declarations are a list of (variable, mark) pairs, with marks `inv`, `ps` and `grpd k`. The rules encoded are COH-inv, OP-inv, OP-ps, INV-fac, INV-obj, PS-fac, INV⇒PS, PS* and OBJ-k. PS-fac and OP-ps take ps* premises, as in the revised §1.2. The variant with plain ps premises (Conjecture 2.2′) is not encoded. ps* descends into boundaries, so `judge` takes fuel; the user-facing judgments use fuel = dimension. The factors of a top generator g are read off the tuple g in execution order: each entry gives the dimension of the cell and the judgment of its image under γ. The DES destructors are not encoded.

- **§1.6 examples** (`Gray/MarksExamples.agda`, by evaluation). The unmarked interchanger is neither inv nor ps. It is inv when β is marked ps, or when α is marked inv, but not when only α is marked ps. That one-sidedness is PS-fac in execution order. A vertical composite of ps cells is ps but not inv. The identity 2-cell is inv and ps. Whiskerings of ps cells are ps. Marking an object grpd₁ makes the 2-cells over it inv (grpd₂ does not), and makes the interchanger inv when z is grpd₁. All the expectations in §1.6 hold. Extra (PS*) examples on a 3-cell m : α ⇛ β: m marked ps is ps but not ps*, and becomes ps* once α and β are ps.
- **Substitution preserves marks** (`Gray/MarksSubst.agda`, proved). The judgments take fuel (for the descent into boundaries that ps* needs), and the theorem is fuel-shifted. Say σ respects the marks at fuel N (`Resp N`): for every k, inv variables go to terms that are inv at fuel k + N, ps variables go to terms that are ps at fuel k + N, and grpd_k objects go to variables marked grpd_k' with k' ≤ k. Then for a derivable Γ ⊢ t : A and Δ ⊢ σ : Γ, and each m ∈ {inv, ps, ps*}: if t is m at fuel k, then t[σ] is m at fuel k + N (`inv-[]`, `ps-[]`, `ps*-[]`, for closed signatures). The user-facing judgments `⊢ t inv` etc. use fuel = dim t. Fuel (`Gray/MarksFuel.agda`): every judgment is monotone in the fuel, for all inputs (`fuel-mono`). For a derivable Γ ⊢ t : A, any fuel ≥ dim A gives the same judgments (`fuel-stable`), so `judgeT` is the limit and substitution preserves the user-facing judgments with no shift (`inv-[]ᵀ`, `ps-[]ᵀ`, `ps*-[]ᵀ`: Γ ⊢ t inv ⇒ Δ ⊢ t[σ] inv, and likewise for ps, ps*). These take two hypotheses. (SigOK) constants have well-formed types, which is vacuous for pure L. (DimOK) a derivable coh is at least as high as its pasting context: dim Θ ≤ dim(t →_A u). DimOK is **proved for L** (`Gray/CohDim.agda`, for closed signatures with SigOK), and `StableL` is the stability module with it discharged. The proof: every pasting context satisfies the invariants of `Gray/PsFacts.agda` (types are variable towers, each positive-dimensional cell lies in a hom, every hom is inhabited), so dim Θ ≤ dim K(Θ) + 1 and Supp T has a tuple of rank dim K(Θ). In any context, the support tuples of a derivable t : A have rank ≤ dim A − 1, by induction on the derivation: a coh outside the coh case is in the op case, so its type has dimension dim K(Δ), and F_ρ never raises rank. The op case then gives dim A = dim K(Θ). In the coh case the top tuple of T lies below a support tuple of t, and ranks only go down along the face order. The proof is monotonicity of every rule premise in the judgments of γ. The side conditions are unchanged because the coh's Θ, A, t and u are not touched by σ.
- **A precision.** The objects' requirement has to be "σ sends grpd_k objects to *variables* with a mark at least as strong". If an object went to a general term, OBJ-k could not be read off its marks. Objects in L are variables or signature constants, and constants carry no marks. So the only thing this rules out is sending a grpd object to a constant.

## Fast side condition (E9′)

**Definition change (PR #68).** `Gray/Support.agda` now decides ↓S = ↓R on generators (`sameDown`): every element of S lies below an element of R in the face order, and vice versa. The face order is computed entrywise by `leqL`. Before, both closures were built with `down` and compared (kept as `sameDownClosure`). The two differ in their step budget. `sameDown` allows up to dim K(Γ) face steps *per entry*. `down` allows at most dim K(Γ) single-entry steps *in total*. **Agreement, proved** (`Gray/DownAgree.agda`):
  - `closure⇒same`: the closure-based answer true implies the generator-based answer true, for every Γ, S, R, with no hypotheses.
  - `sameDown≡Closure`: the two are equal when Γ is *graded* (each source and target of a cell has hom-dimension one lower) and every tuple of S and R has *rank* (total hom-dimension) ≤ dim K(Γ). Both hypotheses are needed for the proof, since `down` counts steps over the whole tuple and `leqT` per entry, and the counts match only when each step lowers the rank by one, starting from rank ≤ dim K(Γ). Both are decidable (`gradedB`, `rankB`, with soundness), and `hypSide Θ A t u` checks them for all four comparisons of a coh.
  - Proof: `closeN n` is exactly reachability in ≤ n single-entry steps (`close⇒`/`close⇐`), `leqL`/`leqT` are exactly entrywise bounded paths (`leqL⇒`/`leqL⇐`, `leqT⇒`/`leqT⇐`), entrywise paths compose to tuple paths, and in a graded context a path of length k lowers the rank by exactly k.
  - **The hypotheses hold on every comparison the side condition makes, in every pasting context** (`Gray/Graded.agda`). `graded`: a context whose types are variable towers (every pasting context, `Strict.L.ps-inv`) is graded. `chain-rank`: a tuple of T^±_k has rank exactly k, so every table tuple has rank ≤ dim K. `covers-rank`: in a graded context a tuple below another entrywise has smaller rank, so the comparison ↓supp t A ⊆ ↓(table) itself bounds the rank of supp t A. `PsSide` packages the four comparisons; `Strict/Soundness.agda` uses it, so the side condition adds no hypothesis to strict soundness. Hence on pasting contexts `graySide` is the same predicate under either definition.

**Symbolic supports** (`Gray/Cover.agda`, `Gray/Fast.agda`, proved). A support is described by a sequence of items: a literal set of cells for one hom, a union of sequences, or a *substituted chain* chain(sg, k, homs). The last follows the recursion of the AM tensor table T^sg_k, with every cell already replaced by a symbolic set. The pieces fit together as follows:

- The top support of an operation-case coh is the top chain of K(Θ), with each cell w replaced by the support of ρ(w). The tables of T are the same chains with literal cells. So supports are linear in the size of the term as a tree, and in the number of homs.
- The meaning of a sequence is given by its first-entry decomposition (`nullS`, `heads`).
- The cover check "∀ x ∈ E ∃ y ∈ F, x ≤ y" propagates pairs (residual of E, set of residuals of F) one entry at a time, with duplicates removed. This is an on-the-fly subset construction over a layered automaton.
- `cover-sound` and `cover-complete` prove the check exact for any entry order.
- `fastSide-correct : fastSide Θ A t u ≡ graySide Θ A t u` holds for **all** inputs. There are no well-formedness assumptions and no postulates.

**Benchmark** (n-fold wedge ΣD¹ ∨ … ∨ ΣD¹; the four comparisons ↓∂⁻T = ↓∂⁻T, ↓T = ↓T, ↓∂⁻T ≠ ↓T and ↓∂⁻T ≠ ↓∂⁺T, compiled with the GHC backend):

| n | generator lists (`sameDown`) | symbolic (`fastSame`) |
|---|---|---|
| 6 | 0.03 s | 0.06 s |
| 8 | 0.11 s | 0.21 s |
| 10 | 1.3 s | 0.66 s |
| 11 | 5.0 s | — |
| 12 | — | 1.6 s |
| 16 | — | 7.5 s |
| 20 | — | 27 s |
| 24 | — | 77 s |
| 28 | — | 195 s |

The list version grows by about 3.7× per step, i.e. exponentially. The symbolic version grows polynomially, roughly n⁶ on this family: from n = 20 to 28 the local exponent is 5.6–6.0. On the Gray cube both are instantaneous. The old closure-based checker took 58 s at n = 6 inside the type checker.

- **Caveat on the type checker.** Evaluating the symbolic check *inside the type checker* (a `refl` proof) still grows about 2.2× per step: 0.6 s at n = 1, 50 s at n = 8. The type checker's evaluator does not share the residual sets that later rounds reuse, so they are recomputed. This is a property of Agda's evaluator, not of the algorithm. Large instances should be checked with the compiled checker.
- **What is not proved.** A polynomial bound. The check is exact, so on arbitrary unions of boxes it decides DNF tautology, which is coNP-hard. A polynomial bound for *valid* terms needs the structural statement the markings thread is working on: residuals of a molecule's support are again supports of molecules of the remaining factors. Polynomial behaviour on the wedges is measured, not proved.

## Orientation family L_ε (`closed-structure.md` D.3)

`Gray/Orient.agda` implements L_ε. Here ε says which hom-dimensions are reversed. Supports are computed in ν(Θ₁ ⊗_ε … ⊗_ε Θₙ), with X ⊗_ε Y = D_ε(D_ε X ⊗ D_ε Y). On tables, D_ε swaps the i-dimensional source and target pieces exactly when (i+1)-cells are reversed: (D_ε Θ)^sg_i = Θ^{ε(i+1)·sg}_i. So (T_ε)^sg_k is the AM tensor of the twisted pieces, twisted once more by ε(k+1). Cells, the face order and the top chain do not depend on ε, so only the sides of the tables change.

- **Proved:** `graySideε-const`. For ε constant (no reversal, or total reversal), L_ε = L for every Θ, A, t, u.
- **Proved** (`Gray/OrientRev.agda`): alternating ε gives the factor-reversed tensor on all tables. For ε = odd, every sign, every k and every list of factors, x ∈ (T_ε)^sg_k(Θ₁,…,Θₙ) iff rev x ∈ T^sg_k(Θₙ,…,Θ₁) (`alt-rev⇒`, `alt-rev⇐`). The same holds for Supp(T), Supp(∂^±T) (`full-rev`, `bdry-rev`), and for ε = even, whose tables are literally those of ε = odd (`chainTε-even`). Proof: a tuple in a chain is a path (a dimension iⱼ and a cell per factor, Σ iⱼ = k, with sign flipped by the parity of the prefix sum). Reversing an ⊗_odd path gives an ⊗ path whose signs use suffix sums, and the two agree because prefix + (iⱼ + 1) + (k + 1) ≡ suffix (mod 2).
  - Scope: this is the statement on tables (the supports of the cells of K(Θ)). The side condition compares term supports in the original Θ against these tables, so L_odd's side condition is L's with every table read in reversed factor order. That is what "L_ε = L^rev" means for L, whose rules only use the tables.
- **Checked by evaluation** (`Gray/OrientExamples.agda`):
  - On the interchanger, alternating ε rejects βα ⇛ αβ and accepts αβ ⇛ βα. The nine-wedge table comparison is now a special case of `OrientRev`.
  - Reversing hom-dimension 2 only (the D_{3} image) reverses the interchanger itself, because it is a hom-2 cell.
  - The D.1 example (K = {2} on D¹ ⊗ D³) is confirmed. α⊗s₂ has the codimension-1 chains of ⊗^rev, not of ⊗, and α⊗c₃ has those of ⊗, not of ⊗^rev. On D¹ ⊗ D² ⊗ D¹, this ε is neither L nor L^rev.
- **Proved:** the symbolic checker covers every L_ε. `Gray/Fast.agda` is now parameterised by the orientation (`Oriented o`): each SHom entry lists the twisted pieces, each table starts from the sign flipped by ε(k+1), and `fastSideε-correct : Oriented.fastSide o Θ A t u ≡ graySideε o Θ A t u` for all inputs. L's `fastSide-correct` is the instance o = λ _ → false composed with `graySideε-const`.
- **Not proved:** the "only if" directions ("L_ε = L^rev only if ε alternates", "L_ε = L only if ε is constant"). Both are true at the level of the D_K dualities (`GrayDuality.agda`); here they would need a separating table for each other ε.

## Not yet proved

- **The non-negativity bridge.** *Now done* (2026-11-18): the strict layer keeps chains as bags, so they are non-negative by construction, and `Strict/Subst.topS-sub` proves that the set-level supports of `Gray/Support.agda` are the supports of these chains (see the last section).

- **Conservativity on a single hom.** For Γ = ΣΘ, L's side condition should equal Finster–Mimram's. This splits into two halves.
  - *Rule-level half: **proved for every pasting diagram*** (2026-11-18, `Gray/SingleHom.agda`; it was first checked by evaluation, see below). For Θ ⊢ps with dim Θ ≥ 1 and every variable v of Θ, `rule-bdry⇒`/`rule-bdry⇐` say that (S v) is in ↓Supp(∂^sg T) iff S v ∈ ∂^sg(ΣΘ), and `rule-full` that (S v) is in ↓Supp(T). `tuples-K` says the tuples of K(ΣΘ) are exactly these singletons. The two sides are compared through one pointwise description of Finster–Mimram's boundaries, proved for every pasting context in `Gray/BdryChar.agda` (`bd⇒`, `bd⇐`): v ∈ ∂⁻ᵢΓ iff dim v < i, or dim v = i and v is not the target of an (i+1)-variable, and dually for ∂⁺ᵢ with sources. For ⊇ on the table side, a cell is pushed up through cells it is the sg-face of until it reaches a lower table or dimension N − 1. There it slides along N-cells w : u′ → u from u to u′ (from u to the target for ∂⁺). u′ has the same type, so the same faces, and levels decrease, so the slide stops at a cell of the (N − 1)-table. *Earlier bounded check:* The closed supports of T, ∂⁻T and ∂⁺T must be exactly the non-object variables of Γ, ∂⁻Γ and ∂⁺Γ, using PR #4's `srcVars`/`tgtVars`. `Gray/Bounded.agda` checks this by evaluation for all 196 pasting diagrams Θ with 1–6 edges, and checks that the test distinguishes ∂⁻ from ∂⁺ on each. It also checks, for every pasting context with 1–5 edges and any number of homs, that ↓Supp(T) is all of K(Γ). This last fact is now **proved for every context** (`Gray/FullSupp.agda`, `full-cover`): every tuple of K(Γ) lies entrywise below a tuple of Supp(T). In each hom, a cell that is the s-face of a higher cell is pushed up to that cell, and one that is not is already in ⟨Θ⟩^s_i.
  - *Term-level half: not proved.* For derivable t : A over ΣΘ, ↓supp(t : A) should equal the non-object part of Var(t : A).
  - The inclusion ⊆ (entries of supports are free variables) is **proved** (`Gray/SuppVars.agda`, `supp-vars`): for derivable t : A in any context whose types are variable towers, every entry of ↓supp(t : A) is in Var(t : A).
  - The inclusion ⊇ is where a proof gets stuck. F_σ does not commute with downward closure when σ sends a cell to an identity-like term, i.e. a coherence-case coh, whose top support is empty. Then F_σ(α) = ∅ while F_σ(∂α) ≠ ∅. Example: the middle 1-cell g of f ⇒ g ⇒ h lies in the closure of the vertical composite's support but not in its table support.
  - So the induction needs the invariant "a derivable cell with empty top support has boundaries with equal closed supports". That is the support-level shadow of "coherence-case cohs are identities in the strict model", i.e. of Theorem 1 soundness, which needs lemma (B).
  - **Finding:** conservativity (Thm 1(3)) and non-degeneracy (Thm 1(2)) share one missing layer, the strict interpretation with (B). They are not independent proofs, as §3.6 suggests for (3).
- **Non-derivability of the reverse interchanger as any term** (Theorem 1(2)): *now proved, with one explicit hypothesis, (B-bdry)* (see the next section; (T-cell) and the coherence case are now theorems). The integer-chain layer is avoided: chains are bags (non-negative by construction), and the chain equation is written additively, ∂⁺c + x⁻ = ∂⁻c + x⁺.
- **Validation against the strict model on examples** (chain-level): *now done* for the total cell, by `Strict/CheckCells.agda` on 18 pasting contexts, and in general for every derivable term, given (B-bdry) (last section).

## Strict-model soundness (`src/CaTTExp/Strict/`)

*Added 2026-11-18.* The strict interpretation of two-tier L in Steiner's ν(K(Γ)) is formalized.

- `Strict/Cell.agda`: cells of ν(K) for an abstract complex with a basis (Steiner 2004 Def. 2.8), as towers of bags; transport of cells along chain maps.
- `Strict/Complex.agda`: K(Γ) hom by hom, basis = composable tuples of hom cells, boundary by the Leibniz rule.
- `Strict/Subst.agda`: top supports commute with substitution, topS(t[σ]) ≈ F_σ(topS t). This replaces lemma (C) by a proof.
- `Strict/L.agda`: every variable of a pasting context is a cell; a cellular substitution induces a chain map, which sends cells to cells.
- `Strict/Soundness.agda`: `sound-tm`, every derivable term t : A over a pasting context is a cell of ν(K(Γ)) with t's table.
- `Strict/ReverseInterchanger.agda`: `no-reverse-interchanger`, no term of any shape has type (α▷g);(f′◁β) ⇛ (f◁β);(α▷g′) over ΣD¹ ∨ ΣD¹. The proof counts f′⊗β on both sides of the chain equation: |c| + 1 against 0.

The two facts were first module parameters, so every use of them is visible in the types:
- **(T-cell)** the total cell built from `chainT` is a cell between the context's first and last object (Ara–Maltsiniotis, arXiv 1607.00668, §A.16, Prop. 4.13). **Now a theorem** (`Strict/Bridge.T-cell : TCell`, 2026-11-18), in four steps:
  - `Strict/Tensor.agda`: the Gray tensor of two cell tables is a cell table (`tensor-cell`), from the Leibniz rule and a sign computation; the unit table is a cell.
  - `Strict/TotalCell.agda`: `chainT` of a list of homs is the iterated tensor of the homs' tables (`chainT-cons`), so T is a cell once each hom's table is one (`HomCells → TCell`).
  - `Strict/Pasting.agda`: for every pasting context, the table of each hom, defined by lookups ("cells of the hom of dimension i that are not the target / source of an (i+1)-cell"), is a cell between consecutive objects. By induction on the pasting derivation: each `pse` step changes only the hom of the cursor, where x leaves the + side, y enters it and f enters both sides one dimension up.
  - `Strict/Bridge.agda`: these tables are the ones `Gray/Support`'s `piece`/`homAt`/`homs` compute. The key facts are that a cell is hit only by cells of its own hom, that the hom index read off by `posOf` is the hom between consecutive objects (objects are strictly increasing), and that the hom dimension bounds every cell's.
  `Strict/CheckCells.agda` still checks it by evaluation on 18 pasting contexts.
- **(B-supp)** cells of ν(K(Θ)) of the same dimension in the same hom with equal downward-closed supports are equal (Hadzihasanovic, arXiv 2404.07273; an atom-free proof in `conjectures/answered/steiner-support-formalizable-2026-11-18.md`). Soundness uses it twice, and since 2026-11-18 only one use remains a hypothesis:
  - **Coherence case, now a theorem** (`Strict/CohCase.coh-top`): two cells t, u from the first to the last object whose closed supports both equal Supp(T) have equal top chains. With n their dimension and d = dim K: for n = 0 both are single tuples and the closure argument (ranks, `Gray/DownAgree`, `Gray/Graded`) forces them equal; 0 < n < d is impossible, because T's top table is inhabited (`Gray/Graded.Ranks.top-ne`) and its tuples have rank d; n > d leaves both top chains empty (`Strict/TopCell.deg-bound`); for n = d, ∂ is injective on top-degree chains (`Strict/TopCell.top-inj`). The injectivity proof writes a top tuple as w = p ⊗ α ⊗ r with p of dimension 0 and α the first positive-dimensional entry, counts the face f = p ⊗ t(α) ⊗ r on both sides of the chain equation (f occurs in ∂⁺ only for w, and in ∂⁻ only for tuples p ⊗ β ⊗ r with s(β) = t(α), which come after α in creation order), and inducts on α from the end.
  - **Operation case, still a module parameter** of `Soundness` and `ReverseInterchanger`: **(B-bdry)** (`Strict/Hyp.BBdry`, Q3a of `conjectures/answered/steiner-support-formalizable-2026-11-18.md`): a (d−1)-cell with the closed support of ∂^±T is ∂^±T. `Hyp.bsupp→bbdry` derives it from (B-supp).

(B-bdry) is true in the literature; what the formalization takes on trust is that `down` computes the downward closure it is about. Formalizing the atom-free proof of (B-supp) would remove it; that is in progress (the basis order with LCORE, the cut lemma here; not yet in the library).

An independent review (2026-11-18) checked that the development builds from scratch under `--safe` with no postulates, that `IsCell` is Steiner's Def. 2.8 and `∂T` the Leibniz rule with `chainT`'s sign convention, that `towerOf` reads the whole boundary from the type (so `IsCellTm` is not trivially satisfiable), and that both hypotheses are true as stated.
