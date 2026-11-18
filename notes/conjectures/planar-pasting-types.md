# Planar pasting types: an unbiased theory of biclosed monoidal categories

*Self-contained problem statement with partial results. It adapts Mimram, *An unbiased simply typed combinatory logic* (CSL 2026), from cartesian closed categories to biclosed monoidal categories, which are non-symmetric and have no diagonal. §2 is a theorem with a proof sketch. §3 and §4 are open.*

## 1. Background: Mimram's construction, in brief

- Types are built from type variables (atoms) with →.
- A type is **pasting** if it passes a decidable test (a restricted proof search). Pasting types are **contractible**: they have exactly one inhabitant up to βη.
- The theory has three rules:
  - every pasting type A has a constant coh_A : A;
  - type substitution: coh_A[τ] : A[τ];
  - any two terms of a pasting type are equal.
- No λ or application rule is primitive. Mimram proves this is equivalent to simply typed λ-calculus modulo βη (and to its version with finite products).
- The cartesian case needs pasting types that are "non-negatively duplicated", because cartesian structure duplicates and discards.

## 2. The planar 1-dimensional case

**Types.** Atoms X, Y, … and the two residuals B\A ("expects a B on the left, gives A") and A/B ("expects a B on the right, gives A"). There is no tensor and no unit; see §3 for those.

**Sequents.** Γ ⊢ A, where Γ is an *ordered* list of types. Provability is the product-free Lambek calculus L, which is decidable.

**Definition.**
- A sequent is **balanced** if every atom occurring in it occurs exactly twice, once positively and once negatively. Polarity is computed as usual: the argument of a residual flips polarity, and the context is negative.
- A sequent is **planar-pasting** if it is balanced and provable in L.

**Theory UL** (unbiased Lambek).
- **Terms.** coh_{Γ⊢A}[τ], where Γ ⊢ A is planar-pasting and τ substitutes types for its atoms. Terms are composed by substitution into ordered contexts.
- **Equality.** Any two terms of the same planar-pasting sequent are equal. Equality is closed under substitution and congruence.

**Theorem.** Terms of UL in an ordered context Γ, modulo UL-equality, are in bijection with proofs of Γ ⊢ A in L modulo βη.

**Proof sketch.**

1. **Contractibility.** Erase both residuals to →. This sends L-proofs in η-long normal form to simply typed λ-terms in η-long normal form. The erasure is injective on normal proofs: a normal proof is determined by its term, and the term records every abstraction and application, with the direction fixed by the type. Erasure also preserves balancedness. By the Babaev–Solov'ev coherence theorem (Zap. Nauchn. Sem. LOMI 88, 1979), a balanced implicational type has at most one βη-normal inhabitant. Hence a balanced L-sequent has at most one proof modulo βη, and a planar-pasting sequent has exactly one.
2. **Completeness.** Let t be an η-long normal L-proof of Γ ⊢ A. Its axiom links pair each positive atom occurrence with exactly one negative occurrence, because the proof is linear and η-long. Rename the atom of each link to a fresh atom. The result is a balanced sequent Γ′ ⊢ A′, with a proof t′, and a type substitution τ such that Γ′[τ] = Γ, A′[τ] = A and t′[τ] = t. So Γ′ ⊢ A′ is planar-pasting, and t = coh_{Γ′⊢A′}[τ].
3. **Soundness and faithfulness.**
   - Interpret coh_{Γ⊢A}[τ] as the unique proof of Γ ⊢ A, substituted by τ. The equality rule is sound by step 1.
   - Two UL-terms with the same interpretation have the same link structure. So both are UL-equal to coh of the same generalised sequent from step 2.

∎ (Steps 2–3 are standard but should be written out carefully.)

**Remarks.**
- Unlike Mimram's cartesian case, *type* substitution suffices. Linearity removes the need for term substitution, which repairs Komori's conjecture in the cartesian case.
- **This is the "linearity" principle in exact form.** For non-symmetric closed structure, the contractible shapes are exactly the balanced (linear) and planar ones.

## 3. Open: tensor and unit

**Conjecture PL1.** Add A ⊗ B, with sequent rules non-commutative. Then balanced provable sequents still have at most one proof modulo the usual βη and commuting conversions for ⊗.

This is the non-symmetric analogue of the Kelly–Mac Lane coherence theorem for closed categories (J. Pure Appl. Algebra 1, 1971), which covers constant-free ("proper") shapes in the symmetric case. It may already be known (Lambek; work on proof nets for non-commutative MLL). A literature check comes first.

**Units** are known to break naive coherence in the closed setting (Kelly–Mac Lane). They need a separate criterion, as in Mimram's treatment of 1.

## 4. Open: higher dimensions, and a precise obstruction

The intended application is the **Gray tensor product** on (∞,ω)-categories (Campion, arXiv 2311.00205). It is monoidal biclosed and non-symmetric. A Mimram-style ω-theory would make the coherence rule produce higher cells instead of equalities.

**Obstruction.** The closure of the Gray tensor product holds on mapping *spaces*:

```
Map(A ⊗ B, C)  ≃  Map(A, Fun^lax(B, C))
```

It does **not** extend naively to the mapping (∞,ω)-categories, whose higher cells are cartesian (pseudo). A k-cell of Fun(A ⊗ B, C) is a map (A ⊗ B) × Dᵏ → C. A k-cell of Fun(A, Fun^lax(B, C)) is a map (A × Dᵏ) ⊗ B → C. These do not agree in general: Gagna–Harpaz–Lanari (arXiv 2006.14495, Rem. 2.20) show the corresponding comparison fails for scaled simplicial sets unless one factor is a groupoid.

**Consequence.** A pasting-type theory whose coherence rule makes "currying" an equivalence on all higher cells would be **unsound** for the Gray structure. The higher cells of a closure must remember *where the Dᵏ sits* among the tensor factors.

**Precise form**, using C1 (`gray-vs-cartesian.md`; proved 2026-11-18), which says A × Dᵏ is A ⊗ Dᵏ with the mixed cells inverted:
- k-cells of Fun(A, Fun^lax(B, C)) are maps out of A ⊗ Dᵏ ⊗ B, with only the A–Dᵏ mixed cells inverted;
- k-cells of Fun(A ⊗ B, C) are maps out of A ⊗ B ⊗ Dᵏ, with the (A⊗B)–Dᵏ mixed cells inverted.

**Question PL-ω.** Is there a class of "Gray pasting types" with the following property: the ω-dimensional coherence rule over them generates exactly the cells of the free monoidal biclosed (∞,ω)-category on a set of objects, with each higher cell's "time" direction tracked as a tensor position in this sense? A first test case: is there a pasting-type criterion whose 2-cells are exactly the lax naturality cells of evaluation, Fun^lax(B, C) ⊗ B → C, and which does not also produce their inverses?

## 5. Why it matters

Cartesian closed structure has an unbiased presentation in which all structure maps and laws come from a single contractibility rule (Mimram). The Gray tensor product, which governs lax transformations, is closed but neither symmetric nor cartesian. §2 shows that the 1-dimensional planar analogue works, with linearity built in. The open parts decide whether the same pattern scales to tensors and units, and to higher dimensions, where closure is only an equivalence on mapping spaces.

## 6. What would count as a solution

Any of the following:
- for PL1, a proof, a counterexample, or a reference (non-commutative MLL coherence for balanced sequents);
- for PL-ω, a candidate criterion that passes the evaluation test case, or an argument that no pasting-type criterion can avoid producing inverses.

## 7. Literature status (searched 2026-11-18)

**PL1: very likely true, and assembled from known results. One lemma still needs a precise citation. PL-ω: open, but Gepner–Heine's "bioriented" enrichment is a published framework for exactly the obstruction in §4.**

**PL1.** The argument has three ingredients.
1. **Proof nets are canonical for unit-free non-commutative MLL.** For unit-free multiplicative linear logic, a cut-free proof modulo the usual permutations (βη and commuting conversions for ⊗) is determined by its proof net. The net is the formula trees together with the axiom linking.
   - Symmetric case, categorically: Blute–Cockett–Seely–Trimble, *Natural deduction and coherence for weakly distributive categories* (JPAA 113, 1996).
   - Non-symmetric (planar) case: Schneck, *Natural deduction and coherence for non-symmetric linearly distributive categories* (TAC 6, 1999, [link](https://geodesic.mathdoc.fr/item/TAC_1999_6_a8/)). Coherence holds without units; units need restrictions.
   - A recent self-contained unit-free coherence proof: [arXiv 2605.03113](https://arxiv.org/abs/2605.03113).
   - Lambek-calculus proof nets (Roorda; Lamarche–Retoré, [overview](https://www.lirmm.fr/~retore/ARTICLES/LaReRoma96.pdf)) identify sequent proofs exactly when they give the same net.
2. **In a balanced sequent the axiom linking is forced.** Each atom has exactly one positive and one negative occurrence. So there is at most one proof net, hence at most one proof modulo the equations.
3. **The lemma still to pin down: the intuitionistic (biclosed) fragment.** The free unit-free biclosed monoidal category must map *faithfully* into the free non-symmetric linearly distributive category, so that equality of nets implies equality of biclosed proofs. Faithfulness holds in the symmetric case by Kelly–Mac Lane and BCST. A non-symmetric reference was not located.

Units: Heijltjes–Houston, *No proof nets for MLL with units* (2014), together with Kelly–Mac Lane's counterexamples, confirm that units need a separate criterion, as §3 says.

**PL-ω.** No pasting-type theory for Gray-closed structure was found. Two results bear directly on §4.
- **The currying obstruction is the subject of Gepner–Heine's "bioriented categories".** Gepner–Heine, *Oriented category theory* ([arXiv 2510.10504](https://arxiv.org/abs/2510.10504)), Cor. 4.1.11:
  - the morphism object between X and Y is the presheaf (S, T) ↦ Map(S ⊠ X ⊠ T, Y) on ∞Cat × ∞Cat;
  - that is, a "k-cell" records where its shape sits among the tensor factors, on the left or on the right.
  - This is the "time direction tracked as a tensor position" that PL-ω asks for, at the semantic level. A pasting-type criterion would have to reproduce their left and right morphism objects LMor and RMor.
- **Mimram's own extensions.** Mimram's cartesian construction (CSL 2026) and the earlier slides ([cccatt](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_cccatt_slides_coreact.pdf)) sketch a higher-dimensional "cartesian closed CaTT". No linear or planar version was found.
