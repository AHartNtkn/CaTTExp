# Closed structure via pasting types: PL1, units, dualities, Mimram's higher criteria, Gray tensor, PL-ω

*2026-11-18. Ledger items D7–D12 (`open-issues.md`). Builds on `conjectures/planar-pasting-types.md` (PL1, PL-ω), `internal-hom.md` §5–§6, `pseudo-vs-gray.md` R5 and §3. Machine checks: `scripts/pl1_check.py`, `scripts/duality_check.py`, `src/CaTTExp/GrayDuality.agda`.*

## Summary

| Item | Result | Status |
|---|---|---|
| **D9** PL1 | **Proved.** In the free unit-free biclosed monoidal category, a balanced sequent has at most one morphism (Part A, Theorem A). The proof is a direct sequent-calculus argument: two factorization lemmas plus connectivity. The "faithfulness lemma" the literature route needed is no longer an input; it becomes a corollary (Corollary A3), as does the non-symmetric Kelly–Mac Lane theorem (equal linking ⇒ equal morphism). Steps 2–3 of `planar-pasting-types.md` §2 are written out in full, for the theory with ⊗ (Theorem A4, with the generalization Lemma A5 proved by a sign invariant on unification). | closed |
| **D10** Units | **Balanced is not enough** once a unit is present: the triple-dual endomorphism is a second morphism of a balanced, provable sequent (Part B.1). **A contractible class that does work**: sequents that normalize, under the canonical unit isomorphisms and invertible rules, to a unit-free pasting sequent or to ⊢ I (Theorem B). Completeness of the resulting theory UL_I is proved in outline (B.3). **B.4:** Theorem A extends to empty antecedents, which enlarges the contractible class, and fullness reduces to one lemma about closed terms. | contractibility proved; fullness proved (Theorem B6); faithfulness proved (Theorem B8, D10b closed): the term model of UL_I\* is the free biclosed monoidal multicategory with unit |
| **D8** Dualities under L | **Classified.** A duality D_K on Steiner complexes commutes with ⊗ (canonically) iff K ∈ {∅, all}, and reverses it iff K ∈ {odd, even}. Every other duality turns ⊗ into a *twisted* tensor. For two-tier L: the ambient dualities D_J that are symmetries are exactly J ∈ {∅, {2,3,…}, odd, {1,2,4,6,…}}. Those that swap lax and oplax are J ∈ {{1}, all, even, {3,5,7,…}}. Every other J sends L to a mixed-orientation theory L_ε. The orientation-parameterised kernel is the family L_ε, on which the whole duality group acts transitively, and freely up to the global sign (Part D). Agda: the sign lemma and the classification. | closed (kernel family designed; implementing it is part of E1's checker) |
| **D12** Mimram's higher criterion | The tool (commit `69bb11a`) has **two** higher criteria, read off the source: a *reversible* one, for (∞,1), which contracts higher hypotheses that have a free endpoint; and a *directed*, globular one (Part C). Re-check of `internal-hom.md` §5.7 against the PDF: four corrections. Soundness of the directed criterion in dimension 2 over graphs follows from Fiore–Saville. **New (C.4, sketch):** the free cartesian closed (∞,1)-category on a set or graph has discrete mapping spaces (normalization by gluing, as in Uemura's ∞-type-theory coherence), hence the reversible criterion is sound. The directed (∞,ω) case is posed as a conjecture (`conjectures/cartesian-closed-higher-coherence.md` Q3). | Rev sound (sketch); Dir beyond dim 2 out to researcher |
| **D7** Gray tensor of arbitrary objects | **Partly unblocked.** B ⊗ ⟦Θ⟧ for *arbitrary* B and representable Θ (and ⟦Θ⟧ ⊗ C) can be given by a colimit-free representability rule over the existing lax hom (lhom), sound by Campion's biclosedness. Lax cylinders B ⊗ D¹ of arbitrary objects follow. The universal property is stated precisely, including higher cells (through the pseudo cotensor). A naive rule asserting the bijection on *all* cells is unsound, with an explicit counterexample at B = C = D¹. Both factors arbitrary still needs [C, –]_lax for arbitrary C, which needs either object-indexed limits (F5) or PL-ω. | **done 2026-11-20**: both factors arbitrary via the biclosed rules of F.7.4 (from the verified r3 answer); E.2 is derived from them. Open: Lemma GB-ext check (D7c), Agda (D7d) |
| **D11** PL-ω | **First test passed by a candidate.** Mimram's directed criterion produces the interchanger in *both* directions, so it fails the test. The candidate "Gray criterion" adds an inversion-set condition on the event order. It produces the lax naturality cell of evaluation and never its inverse (Part F). The ω-version is conjectured to be the higher Bruhat orders, recorded in `planar-pasting-types.md` §4. | candidate passes test; general definition and ω-version open |

---

# Part A. PL1: coherence for unit-free biclosed monoidal categories (D9)

## A.0 Setting

**Formulas.** Atoms X, Y, …, and A ⊗ B, B\A ("needs a B on the left"), A/B ("needs a B on the right"). No units.

**Sequents.** Γ ⊢ C with Γ a *nonempty* ordered list. Polarity: the goal is positive, hypotheses are negative, the argument of a residual flips polarity, and ⊗ preserves it.

**Calculus L⊗** (Lambek calculus with product, cut-free, atomic axioms):

```
Ax   X ⊢ X
R⊗   Γ₁ ⊢ C₁   Γ₂ ⊢ C₂  ⟹  Γ₁,Γ₂ ⊢ C₁⊗C₂
L⊗   Θ, A, B, Θ′ ⊢ C     ⟹  Θ, A⊗B, Θ′ ⊢ C
R\   B, Γ ⊢ A            ⟹  Γ ⊢ B\A            (Γ nonempty)
R/   Γ, B ⊢ A            ⟹  Γ ⊢ A/B            (Γ nonempty)
L\   Δ ⊢ B   Θ, A, Θ′ ⊢ C ⟹ Θ, Δ, B\A, Θ′ ⊢ C   (Δ nonempty)
L/   Δ ⊢ B   Θ, A, Θ′ ⊢ C ⟹ Θ, A/B, Δ, Θ′ ⊢ C   (Δ nonempty)
```

**Semantics.** A unit-free biclosed monoidal category is the same as a *biclosed representable multicategory with nonempty sources* (Hermida's correspondence, unit-free form). Write F(Γ; C) for the multimorphisms Γ → C of the free one on the atoms. Rules denote operations:
- R⊗(f₁, f₂) = m ∘ (f₁, f₂), with m : C₁, C₂ → C₁⊗C₂ universal;
- L⊗ is the inverse of precomposition with m;
- R\ is currying Λ;
- L\(h, k) = k ∘_A ev(h, H), where ev : B, B\A → A and ∘_A plugs into the slot A.

Every equation used below is an instance of one of:
- multicategory associativity (sequential, and plugging into different slots);
- naturality of Λ and of the L⊗ bijection, i.e. Λ(g ∘_i e) = Λ(g) ∘_i e for a slot i other than the curried one, which follows from the universal property.

**Cut elimination.** Every element of F(Γ; C) is the denotation of a cut-free L⊗ derivation, and cut-elimination steps preserve denotations (Lambek 1958 for cut elimination; Lambek, *Deductive systems and categories* I–II, 1968–69, for the categorical reading). We use this as standard. The skew analogue is machine-checked by Uustalu–Veltri–Wan ([2204.06727](https://arxiv.org/abs/2204.06727)).

**Balanced.** Every atom occurs exactly twice in the sequent, once positively and once negatively. In a balanced sequent each atom determines a **link** between its two occurrences.

**Link graph.** Its nodes are the formulas of the sequent (hypotheses and goal). It has an edge for each link between occurrences in different nodes. A set of nodes is **link-closed** if no link leaves it. We also use *split* graphs: in the *H-split* graph, a hypothesis H = B\A (or A/B) is replaced by two nodes B and A; in the *goal-split* graph, a goal C₁⊗C₂ is replaced by C₁ and C₂.

## A.1 Two easy lemmas

**Lemma B (balance of premises).** In a provable sequent, each atom has as many positive as negative occurrences (induction on derivations). Hence every premise of a rule instance with provable premises, whose conclusion is balanced, is balanced: the premises partition the occurrences, and each premise is itself provable.

**Lemma C (connectivity).** The link graph of a provable sequent (in L⊗) is connected.
- *Proof.* Induction on the derivation.
- Ax: two nodes and one link.
- R⊗ joins two connected graphs through the new goal node.
- L⊗ merges two nodes.
- R\ merges the nodes B and A into the goal B\A.
- L\ merges the B-node of a connected premise with the A-node of the other connected premise into the single node B\A.
- R/ and L/ are symmetric to R\ and L\. ∎

**Consequence used throughout.** Every sequent has at least two nodes. So in a provable sequent, a link-closed set of nodes that misses some node is empty.

## A.2 The factorization lemmas

**Lemma F\* (factoring through a left rule).** Let S = Γ ⊢ C be balanced, H = B\A ∈ Γ and Γ = Θ, Δ, H, Θ′ with Δ nonempty, such that Δ ∪ {B} is link-closed in the H-split graph. Then for every cut-free derivation π of S,

```
⟦π⟧ = k ∘_A ev(h, H)     for some h ∈ F(Δ; B),  k ∈ F(Θ, A, Θ′; C).
```

The mirror statement holds for H = A/B with Δ on the right.

*No provability hypothesis is needed:* the lemma produces the premises.

*Proof.* Induction on π. Let r be its last rule.
1. **r is L\ at H itself, with split Δ_r.** Its premise Δ_r ⊢ B is balanced and provable, hence connected and link-closed, so Δ_r ∪ {B} is B's component. Δ ∪ {B} is link-closed and contains B, so Δ = Δ_x, Δ_r with Δ_x link-closed on its own.
   - Δ_x lies inside the hypotheses of the other premise Θ_r, A, Θ′ ⊢ C, which is connected and contains C ∉ Δ_x. So Δ_x = ∅ and Δ = Δ_r.
   - Take h, k to be the two sub-derivations.
2. **r is R\ or R/.** The new hypothesis comes from the goal, so it is not linked to Δ ∪ {B}, and Δ stays contiguous and adjacent to H. By the induction hypothesis, the premise is k′ ∘_A ev(h, H). Then ⟦π⟧ = Λ(k′) ∘_A ev(h, H), by naturality of Λ.
3. **r is L⊗ on E⊗E′.**
   - If E⊗E′ ∈ Θ ∪ Θ′, the induction hypothesis on the premise and naturality of L⊗ give the result.
   - If E⊗E′ ∈ Δ, the premise has Δ′ = Δ[E⊗E′ ↦ E, E′], still contiguous and link-closed. The induction hypothesis gives h′ ∈ F(Δ′; B), and ⟦π⟧ = k ∘_A ev(L⊗h′, H).
4. **r is R⊗**, with premises Γᵢ ⊢ Cᵢ. Say H ∈ Γ₁. In the doubly split graph, Δ ∩ Γ₂ = (Δ∪{B}) ∩ (Γ₂∪{C₂}) is link-closed and consists of hypotheses of the connected premise Γ₂ ⊢ C₂. So it is empty, and Δ ⊆ Γ₁.
   - Apply the induction hypothesis to the first premise.
   - Then ⟦π⟧ = m ∘ (k₁ ∘_A ev(h, H), f₂) = (m ∘ (k₁, f₂)) ∘_A ev(h, H).
   - The case H ∈ Γ₂ is symmetric.
5. **r is L\ or L/ at H′ ≠ H**, with premises S₁ = Δ′ ⊢ B′ and S₂ = Θ″, A′, Θ‴ ⊢ C. Work in the graph split at both H and H′. Each of Δ∪{B} (with H′ split if H′ ∈ Δ), Δ′∪{B′}, and the node set of S₂ is link-closed there.
   - **H ∈ S₂, H′ ∉ Δ.** Δ ∩ Δ′ is link-closed, a set of hypotheses of the connected S₁ missing B′. So it is empty, and Δ lies in S₂, still contiguous and adjacent to H. The induction hypothesis on S₂ gives k₂ ∘_A ev(h, H). By associativity, ⟦π⟧ = (k₂ ∘_{A′} ev′(f₁, H′)) ∘_A ev(h, H).
   - **H ∈ S₂, H′ ∈ Δ.** (Δ∩Δ′) ∪ {B′} is link-closed in S₁ and contains B′, so it is all of S₁: Δ′ ⊆ Δ. In S₂, Δ becomes Δ₂ = Δ[Δ′, H′ ↦ A′], which is contiguous, adjacent and link-closed. The induction hypothesis gives h₂ ∈ F(Δ₂; B), and ⟦π⟧ = k ∘_A ev(h₂ ∘_{A′} ev′(f₁, H′), H).
   - **H ∈ S₁, H′ ∉ Δ.** Δ ∩ (Θ″∪Θ‴) is link-closed, a set of hypotheses of the connected S₂ missing C. So it is empty, and Δ ⊆ Δ′. The induction hypothesis on S₁ and associativity finish this case.
   - **H ∈ S₁, H′ ∈ Δ.** (Δ ∩ (Θ″∪Θ‴)) ∪ {A′} is link-closed in S₂, contains A′ and misses C. That contradicts connectivity of S₂, so this case is impossible.
6. **r = Ax** is impossible, since S contains a residual. ∎

**Lemma T\* (factoring through R⊗).** Let S = Γ ⊢ C₁⊗C₂ be balanced and Γ = Γ₁, Γ₂ with Γ₁ ∪ {C₁} link-closed in the goal-split graph (Γᵢ nonempty). Then every ⟦π⟧ = m ∘ (f₁, f₂) with fᵢ ∈ F(Γᵢ; Cᵢ).

*Proof.* Induction on π. R\, R/ and Ax are impossible.
- **r = R⊗:** the split is forced as in F\* case 1.
- **r = L⊗:** the induction hypothesis and naturality of L⊗.
- **r a left rule at H′ ∈ Γ₁:** Δ′ ∩ Γ₂ is a link-closed set of hypotheses of the connected S₁ missing B′, so it is empty. In S₂ the prefix Γ₁[Δ′,H′ ↦ A′] is still link-closed with C₁. Apply the induction hypothesis and associativity.
- **H′ ∈ Γ₂:** symmetric. ∎

## A.3 The theorem and its corollaries

**Theorem A (PL1).** For a balanced sequent S, |F(S)| ≤ 1. If S is also provable, |F(S)| = 1.

*Proof.* Induction on the size of S.
- **An invertible rule applies** (the goal is a residual, or some hypothesis is a tensor). Then F(S) is in bijection with F(S′) for the smaller balanced premise S′.
- **Otherwise,** if F(S) is empty there is nothing to prove. If not, pick a cut-free π₀ (by cut elimination). Its last rule is Ax, R⊗ or a left rule.
  - **Ax:** S = X ⊢ X has only the Ax derivation.
  - **Left rule at H with split Δ:** the premise Δ ⊢ B is balanced, so Δ ∪ {B} is link-closed, and Lemma F\* applies to S, H, Δ.
    - Every π factors as k ∘_A ev(h, H), with h, k in F of two smaller balanced sequents (Lemma B). By induction these have at most one element each.
    - So every ⟦π⟧ equals ⟦π₀⟧.
  - **R⊗:** use Lemma T\* in the same way. ∎

**Corollary A1 (non-symmetric Kelly–Mac Lane, unit-free).** Two morphisms Γ → A of the free unit-free biclosed monoidal category are equal iff their cut-free derivations have the same axiom linking.
- *Proof.* Rename the atoms of each link apart. Both derivations become derivations of the same balanced S′, and the two morphisms are τ_*(f′) and τ_*(g′) for f′, g′ ∈ F(S′). Theorem A gives f′ = g′.
- The linking is an invariant of the morphism. Let G be the Brauer category with loop value 1 on atom-labelled signed points: a morphism is a fixed-point-free involution on leaf occurrences pairing equal atoms of opposite polarity, and composition follows paths and deletes closed loops (Kelly–Mac Lane's category of graphs, *Coherence in closed categories*, 1971). G is compact closed, hence biclosed monoidal, so there is a unique structure-preserving functor F → G that fixes atoms. Rule by rule, it sends a cut-free derivation to its axiom linking: R⊗, L⊗ and R\ juxtapose or regroup leaves, and L\(h, k) = k ∘_A ev(h, H) composes with the straight-through linking of ev, so no loop forms. Two cut-free derivations of the same morphism therefore have the same linking. ∎

**Corollary A2 (the PL1 statement of `planar-pasting-types.md` §3).** Balanced provable sequents of the Lambek calculus with product have exactly one proof modulo βη and the commuting conversions for ⊗.
- Those conversions are exactly the equations of the free biclosed monoidal category.

**Corollary A3 (the faithfulness lemma, now a consequence).** The canonical functor from the free unit-free biclosed monoidal category to the free unit-free non-symmetric linearly distributive (or bilinear) category is faithful.
- *Proof.* That functor preserves axiom linkings, because proof nets record them (Cockett–Seely, TAC 3 (1997), Thm 3.3). Equal images therefore have equal linkings, hence are equal by A1. ∎
- So the literature route of §7 of the conjecture file is no longer needed. Its missing lemma follows from the direct proof.

**Theorem A4 (UL⊗, steps 2–3 of §2 with ⊗).** Let UL⊗ be UL of `planar-pasting-types.md` §2 with formulas extended by ⊗:
- terms are coh_S[τ] for balanced provable S and type substitutions τ, closed under term substitution into ordered contexts;
- equality is the coh-equality rule closed under substitution, congruence and transitivity.

Then UL⊗-terms Γ ⊢ A modulo equality are in bijection with F(Γ; A), compatibly with substitution.

1. **Soundness.** Interpret coh_S[τ] as τ_*(the element of F(S)), where τ_* is the substitution functor of the free category. Composition is multicategory composition. The equality rule holds by Theorem A.
2. **Fullness.** Given f ∈ F(Γ; A), take a cut-free derivation π. Rename each axiom link to a fresh atom. This gives a derivation π′ of a balanced provable S′ and a substitution τ with S′[τ] = (Γ ⊢ A) and τ_*⟦π′⟧ = f. So f = ⟦coh_{S′}[τ]⟧.
3. **Faithfulness.** This step was a sketch until 2026-11-18. It is now written out in full (D9a).

   **Terms.** A UL⊗-term in an ordered context Γ is either:
   - a variable x, in the context x : A, of type A; or
   - coh_S[τ](t₁, …, tₙ), where S = (B₁, …, Bₙ ⊢ B) is balanced and provable, τ is a type substitution, Γ = Γ₁, …, Γₙ, and tᵢ is a term of type Bᵢ[τ] in Γᵢ.

   Type substitution acts on terms by ρ ↦ coh_S[τ;ρ] at every node. Term substitution is grafting.

   **Lemma A5 (generalization).** For every term t : (Γ ⊢ A) there are a balanced sequent S_t, a term t′ : S_t and a substitution σ_t such that S_t[σ_t] = (Γ ⊢ A) and t′[σ_t] = t syntactically.

   *Proof.* Induction on t.
   - **Variable x : A.** Rename the atom occurrences of A apart, one fresh atom per leaf position, giving A′. Then S = (A′ ⊢ A′) is balanced: each fresh atom occurs once in the hypothesis and once in the goal, with opposite polarities. Take t′ = x, and let σ send the fresh atom at leaf position p to the atom of A at p.
   - **t = coh_S[τ](t₁, …, tₙ).** By induction, tᵢ = tᵢ′[σᵢ] with tᵢ′ : Sᵢ = (Γᵢ′ ⊢ Cᵢ) balanced. Rename so that the atoms of S, S₁, …, Sₙ are pairwise disjoint.
     - The unification problem E = {Bᵢ ≐ Cᵢ}ᵢ has the unifier τ ∪ σ₁ ∪ … ∪ σₙ (disjoint domains), since Bᵢ[τ] = Cᵢ[σᵢ].
     - So it has a most general unifier θ (Robinson). Then τ ∪ ⋃σᵢ = θ;π for some π.
     - Put S_t = (Γ₁′, …, Γₙ′ ⊢ B)[θ] and t′ = coh_S[θ](t₁′[θ], …, tₙ′[θ]). This is well-typed, since tᵢ′[θ] has type Cᵢ[θ] = Bᵢ[θ].
     - Take σ_t = π. Then S_t[π] = (Γ ⊢ A) and t′[π] = t.
     - S_t is balanced by the plugging lemma below. ∎

   **Plugging lemma.** In the situation above, (Γ₁′, …, Γₙ′ ⊢ B)[θ] is balanced. This holds for any balanced S, Sᵢ with disjoint atoms; provability and planarity are not used.

   *Proof.* Compute θ by the Martelli–Montanari algorithm. Its state is the sequent (Γ₁′, …, Γₙ′ ⊢ B) together with a set of equations L ≐ R. All its steps preserve the following invariant.

   > **(I)** Count the atom occurrences of the sequent with their polarities, and for each pending equation L ≐ R, count L as an extra hypothesis (negative) and R as an extra goal (positive). Then every atom occurs exactly twice, with opposite signs.

   - **Initially**, orient each equation as Bᵢ ≐ Cᵢ. The counted occurrences are exactly those of S and of the Sᵢ, each balanced, with disjoint atoms. Bᵢ is a hypothesis of S, and Cᵢ is the goal of Sᵢ.
   - **Decompose.**
     - L₁⊗L₂ ≐ R₁⊗R₂ becomes L₁ ≐ R₁ and L₂ ≐ R₂. The signs are unchanged, because ⊗ preserves polarity.
     - L₁\L₂ ≐ R₁\R₂ becomes L₂ ≐ R₂ and R₁ ≐ L₁. Note the swap: the argument of a residual flips polarity, so R₁ now counts negatively and L₁ positively, which are exactly their signs before.
     - The / case is the same as the \ case.
     - A clash between different connectives cannot occur, since E is unifiable.
   - **Delete X ≐ X.** By (I) these are the only two occurrences of X, so X disappears and (I) still holds.
   - **Eliminate X ≐ F**, with F ≠ X; the occurs check passes because E is unifiable. Here X counts negatively, so by (I) X has exactly one other occurrence, which is positive and not inside F. The step substitutes X := F everywhere, i.e. at that single occurrence, and drops the equation.
     - The occurrences of F move from a positive root (the right side of the equation) to a positive position (that occurrence of X). So every moved occurrence keeps its sign.
     - Nothing is copied, and both occurrences of X are gone.
     - F ≐ X is symmetric, with all signs reversed.

   The algorithm terminates with no equations, and the composite of its eliminations is an MGU. At that point (I) says exactly that the sequent is balanced. Any other MGU differs by a renaming, which preserves balance. ∎

   This replaces the earlier appeal to Hirokawa (principal types of BCK-terms). The point is the same: substitutions found by unification move occurrences and never copy them. `scripts/generalization_check.py` tests the plugging lemma on random balanced sequents (no failures).

   **Lemma A6 (linking of an instance).** Let S be balanced, f ∈ F(S) and σ a substitution. The linking of σ_*(f) pairs the leaf (o, p) with (o′, p), where o and o′ are the two occurrences in S of an atom X, and p is a leaf position of σ(X).
   - *Proof.* Apply σ to a cut-free derivation of S, and replace each axiom X ⊢ X by the η-expanded identity on σ(X). Its linking pairs each leaf p of the hypothesis with p of the goal (induction on the formula), and it denotes the identity. The result is a cut-free derivation of S[σ] denoting σ_*(f), with the stated linking. ∎

   **Theorem (faithfulness).** If t, u : (Γ ⊢ A) and ⟦t⟧ = ⟦u⟧, then UL⊗ proves t = u.
   - By A5, t = t′[σ_t] with t′ : S_t balanced and provable. Provability holds because F(S_t) contains ⟦t′⟧, and F(S_t) is nonempty only if S_t is provable, by cut elimination.
   - So t′ and coh_{S_t}(x⃗) are two terms of a pasting type. The equality rule, closed under substitution, gives t = coh_{S_t}[σ_t].
   - Let λ be the linking of ⟦t⟧ = ⟦u⟧ (well-defined by A1). Let S* be Γ ⊢ A with the two leaves of each λ-pair renamed to one fresh atom, and σ* the renaming back. S* is balanced.
   - Define ρ_t(X) as σ_t(X) with the leaf at p renamed to the fresh atom of the λ-pair of (o, p), for an occurrence o of X in S_t. By A6, (o, p) and (o′, p) are λ-paired, so ρ_t is well defined. By construction S_t[ρ_t] = S* and ρ_t;σ* = σ_t.
   - S* is an instance of the provable S_t, so it is a pasting type. The term coh_{S_t}[ρ_t] has type S*, so UL⊗ proves coh_{S_t}[ρ_t] = coh_{S*}.
   - Hence t = coh_{S_t}[ρ_t][σ*] = coh_{S*}[σ*]. The same argument gives u = coh_{S*}[σ*], so t = u. ∎

   Steps 1–3 together prove Theorem A4.

**Machine check.** `scripts/pl1_check.py` enumerates every balanced sequent with at most 4 atoms (8 occurrences) and at most 3 hypotheses: 3 520 753 sequents, 15 458 provable. For each it checks:
- Lemma C;
- Lemma B on every rule instance with provable premises;
- that splits are forced;
- the provability shadow of F\* and T\*: whenever their link-closure hypothesis holds in a provable sequent, both premises are provable.

There were no failures. This tests the combinatorial lemmas, not the semantic equations (those are standard multicategory identities).

---

# Part B. Units (D10)

## B.1 Balanced is not enough with a unit

Let A* := A\I. Take the balanced sequent T ⊢ T with T = (A*)** = (I/(A\I))\I in planar notation (Cockett–Seely, TAC 3, Ex. 3.5; the symmetric version is Kelly–Mac Lane's).

Let k_A : A → A** be the evident map. Two endomorphisms of T are:
- id_T;
- e := k_{A*} ∘ (k_A)* : A*** → A* → A***.

Both have the same axiom linking. But e is only an idempotent; by the triangle identity, (k_A)* ∘ k_{A*} = id_{A*}.

The two are distinct in the free biclosed monoidal category. Interpret in Vect, which is biclosed (symmetric) monoidal, with A infinite-dimensional. There e = id would make k_{A*} surjective, i.e. A* reflexive, which fails.

So Theorem A has no unit-ful analogue for balanced sequents, as the conjecture file anticipated.

## B.2 A contractible class: unit-pasting sequents

**Normalization N.** Rewrite formulas bottom-up with the canonical isomorphisms

```
I⊗A → A    A⊗I → A    I\A → A    A/I → A
```

Then drop hypotheses equal to I, and apply the invertible rules: move goal residuals into the context, and split tensor hypotheses. Empty contexts are allowed during this process. The result N(S) is unique.

**Definition.** S (formulas may contain I, antecedent possibly empty) is **unit-pasting** if
- N(S) is unit-free, has a nonempty antecedent, and is balanced and L⊗-provable (i.e. L-pasting in the sense of Part A); or
- N(S) is ⊢ I.

**Theorem B.** In the free biclosed monoidal category *with* unit, F_I(S) is a singleton for every unit-pasting S.

*Proof.*
1. F_I(S) ≅ F_I(N(S)). Each rewriting step is pre- or post-composition with an isomorphism, using functoriality of ⊗, \ and / in each variable. Dropping an I hypothesis is a unitor. The invertible rules are bijections in any biclosed monoidal category with unit, including at empty contexts.
2. **N(S) = ⊢ I.** A cut-free derivation in the calculus with unit (L* with I, i.e. Lambek with empty antecedents and the unit rules) of ⊢ I must end in R_I, since there is no hypothesis. So F_I(;I) has one element.
3. **N(S) L-pasting (conservativity).** Take a cut-free derivation of N(S) in L* with I.
   - It uses no I-rule, by the subformula property.
   - It has no sequent with empty antecedent. Such a sequent ⊢ B, with B a subformula occurrence of N(S), would be balanced (Lemma B) with all of B's atoms linked inside B.
   - But in an L⊗-derivation of N(S), which exists, that occurrence B appears as a whole formula of some sequent. That sequent is connected (Lemma C) and has at least two nodes, so some atom of B is linked outside B. The linking is forced by balancedness, so this is a contradiction.
   - Hence every cut-free derivation in the calculus with unit is an L⊗-derivation.
   - The proof of Theorem A used only equations valid in every biclosed representable multicategory, including those with nullary maps. So |F_I(N(S))| ≤ 1, and = 1 by provability. ∎

**Examples.**
- Unit-pasting: λ, ρ and their inverses (N gives X ⊢ X); the name of the identity, ⊢ X\X (N gives X ⊢ X); ev at I, i.e. A, A\I ⊢ I (an I-instance of A, A\Y ⊢ Y, see below); id_I (N gives ⊢ I).
- Not unit-pasting: T ⊢ T of B.1, since I stays in the result position of A\I after normalization.

## B.3 The theory UL_I

UL_I has:
- terms coh_S[τ] for S unit-free L-pasting or unit-pasting;
- type substitutions τ that may send atoms to formulas containing I;
- empty contexts allowed.

**Soundness** is Theorem B together with the substitution functor.

**Completeness (proof sketch).** The free biclosed monoidal category with unit is generated, under composition, ⊗ of maps and the functors B\(–) and (–)/B on maps, by:
- the unit-free structure maps, which are coh's of L-pasting sequents;
- λ, ρ and their inverses, which are unit-pasting.

Currying needs no new generator: Λf = (B\f) ∘ η_X, with η_X : X → B\(B⊗X) L-pasting.

Each operation preserves instances: B\(coh_S[τ]) = coh_{B′\S}[τ, B′ ↦ B] for a fresh atom B′, and B′\S is again L- or unit-pasting.

Both id_T and e of B.1 arise this way, as *different* generalized sequents (e = k_{A*} ∘ (k_A)* is a composite of two Y := I instances of L-pasting sequents). So UL_I does not identify them, which is correct.

*Superseded by B.4,* which avoids the generation statement. Original note: *to check* that the generation statement holds for the free biclosed monoidal category with unit, i.e. that nothing beyond these generators and operations is needed. This is a standard presentation, but it has not been verified here.

## B.4 D10a: empty antecedents, a larger contractible class, and fullness reduced to one closed-term lemma

*Added 2026-11-18 (D10a, in progress).*

**Theorem A\* (Theorem A with empty antecedents).** Let S be a balanced sequent with *no occurrence of I*, whose antecedent may be empty. Then |F_I(S)| ≤ 1 in the free biclosed monoidal category with unit, and |F_I(S)| = 1 iff S is provable in L\*, the Lambek calculus with product and empty antecedents.

*Proof.*
- A cut-free derivation of S in L\*_I uses no unit rule, by the subformula property. So it is an L\*-derivation.
- Rerun Part A with empty antecedents allowed: in R\ and R/, in the Δ of L\ and L/, and in the two halves of R⊗.
  - **Lemma C** still holds. The extra base situations only merge nodes: R\ on B ⊢ A gives the one-node sequent ⊢ B\A, and L\ with Δ = ∅ merges the one-node premise ⊢ B into H.
  - What fails is "every sequent has at least two nodes", since ⊢ C has one. But every use of connectivity in A.2 has the form "a link-closed set of hypotheses of a connected premise that misses that premise's goal is empty". That form holds for one-node premises too.
- **Lemma F\*** with Δ possibly empty. Only case 1 needs a new remark. If Δ = ∅, then B is self-linked. If the last rule's split were Δ_r ≠ ∅, the connected premise Δ_r ⊢ B would link B to Δ_r, which is impossible. So Δ_r = ∅ = Δ.
- **Lemma T\*** with Γ₁ or Γ₂ empty: the same argument.
- The semantic equations used are valid in biclosed representable multicategories with nullary maps, as already noted in B.2. ∎

`scripts/pl1star_check.py` reruns `pl1_check.py` with empty antecedents. It checks Lemma C, Lemma B, forced splits and the F\*/T\* shadow. With 6 leaves it covers 35,967 balanced sequents (2,381 provable) with no failures. With 8 leaves it covers 11,460,087 balanced sequents (126,344 provable), again with no failures.

**Consequence: a larger unit-pasting class.** Call S **unit-pasting\*** (UP\*) if N(S) is I-free, balanced and L\*-provable, or N(S) = ⊢ I. Theorem B extends with the same proof, using Theorem A\* in place of step 3. The new class is strictly larger.
- (X\X)\Y ⊢ Y is UP\* but not unit-pasting in the sense of B.2: it is L\*-provable but not L-provable.
- So is ⊢ Y\((W\W)⊗Y), the name of y ↦ j_W ⊗ y.

Below, UL_I\* is UL_I with coh over UP\* sequents.

**Fullness reduces to currying.** Take a cut-free L\*_I-derivation. Every rule except R\, R/ and L⊗ is a grafting into a coh:
- Ax and R_I are the coh's X ⊢ X and ⊢ I.
- R⊗ grafts into m.
- L\ and L/ graft k ∘_A ev(h, H) into ev (h may be closed).
- L_I grafts the I into a neighbouring hypothesis through λ = coh_{I, X ⊢ X} or ρ = coh_{X, I ⊢ X}. If the context is empty, it is λ(u, t) with t the closed premise term. This is I_L(t), because plugging u : ⊢ I into the result gives t back, and plugging u is the bijection that I_L inverts.

L⊗ reduces to currying:
1. Curry Θ from the left and Θ′ from the right.
2. Curry b and a, giving a closed g : ⊢ (E/B)/A.
3. Graft g into the L-pasting coh ((Z/Y)/X, X⊗Y ⊢ Z).
4. Uncurry by grafting into ev coh's.

**So UL_I\* is full iff the denotable morphisms are closed under Λ**, on both sides.

**Currying, by bracket abstraction.** Let t have leftmost free variable x. Define [x]t by induction:
- [x]x = j = coh_{⊢ X\X} (UP\*).
- If x occurs in the first argument, then [x]coh_S[τ](t₁, t₂, …) = coh_K([x]t₁, coh_{S^c}[τ](t₂, …)), where:
  - K = (Y\Z, Z\W ⊢ Y\W) is L-pasting;
  - S^c = (B₂, … ⊢ B₁\C) is S curried, with the same normal form;
  - the equation is naturality of Λ in the remaining variables.
- If closed arguments c₁, …, c_k precede the argument s containing x, first rebracket. With the L-pasting M = (B₁, …, B_k, Y ⊢ B₁⊗…⊗B_k⊗Y) and S⊗ the left-⊗ form of S (pasting iff S is),

  ```
  coh_S[τ](c⃗, s, …) = coh_{S⊗}[τ](coh_M(c⃗, s), …)        (denotationally).
  ```

  Then [x] of the right-hand side is coh_K(coh_K([x]s, ⌜c⃗ ⊗ –⌝), coh_{S⊗^c}[τ](…)), where ⌜c⃗ ⊗ –⌝ := Λ_y coh_M(c⃗, y) : ⊢ Y\(P⊗Y) and P = B₁⊗…⊗B_k[τ].

So **UL_I\* is full iff, for every closed term c : ⊢ P, the closed "left tensoring name" ⌜c ⊗ –⌝ : ⊢ Y\(P⊗Y) is denotable, together with its mirror ⌜– ⊗ c⌝ : ⊢ (Y⊗P)/Y.**

**Proved case.** Generalize c by Lemma A5 to c′ : ⊢ P′. The plugging lemma ignores the constant I. If ⊢ P′ is UP\*, then ⊢ Y\(P′⊗Y) is UP\*:
- its normal form is Y ⊢ N(P′)⊗Y, or Y ⊢ Y when N(P′) = I;
- it is balanced, and L\*-provable by R⊗ with split ∅ | Y.

So ⌜c ⊗ –⌝ = coh_{⊢ Y\(P′⊗Y)}[σ_c]. In particular, UL_I\* is full on every term built only from I-free coh's. More generally it is full whenever the closed subterms met in bracket abstraction have UP\* generalizations.

**The closed-term lemma is false, but fullness does not need it.** *(Updated 2026-11-18.)*

*Counterexample to "every closed term has a UP\* generalization".*
- Take the closed coh c = coh_{⊢ C}, with C = ((Z ⊗ (Z\X)) \ (X ⊗ W)) / W. The sequent ⊢ C is UP\*: it is balanced and I-free, and its normal form Z ⊗ (Z\X), W ⊢ X ⊗ W is L-provable.
- Take the unary UP\* coh S = (((P \ (I ⊗ Q)) / R) ⊢ (P \ Q) / R). Its normal form is an identity sequent.
- Unifying the hypothesis of S with C sends X to I. The closed term coh_S(c) then has generalization ⊢ ((Z ⊗ (Z\I)) \ W) / W, which contains the unremovable Z\I. So it is not UP\*.
- No single UP\* coh denotes this morphism either: any generalization must keep that I.
- `scripts/d10a/cex.py` checks all of this mechanically. `scripts/d10a/closed_tame.py` found no counterexample in 108k random closed trees, so the counterexample is not generic.

**Prop. B5 (tensoring names are always coh composites).** For every closed UL_I\* term c : ⊢ P, the names ⌜c ⊗ –⌝ : ⊢ Y\(P ⊗ Y) and ⌜– ⊗ c⌝ : ⊢ (Y ⊗ P)/Y are denoted by UL_I\* terms.

*Proof.* Induction on c = coh_S[τ](c₁, …, c_k), with S = (B₁, …, B_k ⊢ C) UP\* and every cᵢ closed. Put Bᵢ′ = Bᵢ[τ] and C′ = C[τ].
- **The prefix.** The map y ↦ c₁ ⊗ … ⊗ c_k ⊗ y is a composite of the maps y ↦ cᵢ ⊗ y′. Their names exist by induction, and they compose with the L-pasting coh K = (Y\A, A\B ⊢ Y\B):

  ```
  ⌜c₁ ⊗ c₂ ⊗ –⌝ = coh_K(⌜c₂ ⊗ –⌝, ⌜c₁ ⊗ –⌝[Y := B₂′ ⊗ Y]),
  ```

  and so on for longer prefixes. For k = 0 the prefix is the name of the identity, j_Y.
- **The coh itself.** c ⊗ y = (S[τ] ⊗ Y)(c₁ ⊗ … ⊗ c_k ⊗ y). The name of S ⊗ Y is a single coh, over the sequent

  ```
  T_S = ⊢ (B₁ ⊗ … ⊗ B_k ⊗ Y) \ (C ⊗ Y),   instantiated at τ.
  ```

  T_S is UP\*. Its normal form is nf(B₁), …, nf(B_k), Y ⊢ nf(C) ⊗ Y, or Y ⊢ Y when N(S) = ⊢ I. Since N(S) is I-free, the hypotheses nf(Bᵢ) are I-free and nf(C) is either I-free or I. The normal form is provable by R⊗ with split (hypotheses | Y), from the provability of N(S). It is balanced.
- **Conclusion.** ⌜c ⊗ –⌝ = coh_K(⌜prefix⌝, coh_{T_S}[τ]). The mirror case is symmetric, with T′_S = ⊢ (Y ⊗ C) / (Y ⊗ B₁ ⊗ … ⊗ B_k).
- The argument never uses a generalization of c, so the counterexample above does not affect it. ∎

`scripts/d10a/tens_names.py` checks that T_S and T′_S are UP\* for 3,003 random UP\* coh's, with no failures.

**Theorem B6 (fullness of UL_I\*; D10a).** Every morphism of the free biclosed monoidal category with unit is the denotation of a UL_I\* term.

*Proof.* By the reduction above, fullness follows from closure under Λ. Bracket abstraction gives that closure, given the names ⌜c⃗ ⊗ –⌝ and their mirrors, and Prop. B5 supplies those names. ∎

**What remains (D10b): faithfulness of UL_I\*.** Do equal denotations imply equality in UL_I\*?
- The unit-free proof (A4) went through a single coh per term. With units, a morphism need not be a single coh: the counterexample above is one such morphism, and B.1's e is another. So A4's argument does not apply.

**Prop. B7 (faithfulness is representability of the term model).** *(Added 2026-11-18.)* Let T be the syntactic multicategory of UL_I\*: objects are formulas, T(Γ; A) is the set of terms Γ ⊢ t : A modulo UL_I\* equality, and composition is substitution. Chosen arrows are m = coh_{X,Y ⊢ X⊗Y}, u = coh_{⊢ I}, ev = coh_{Y, Y\Z ⊢ Z} and ev′ = coh_{Z/Y, Y ⊢ Z}, each instantiated by type substitution. Then the following are equivalent:
1. UL_I\* is faithful.
2. T is a biclosed representable multicategory with these chosen arrows. That is, the maps below are bijections in T, not only after interpretation:
   - (R⊗) h ↦ h ∘_i m from T(Γ, A⊗B, Δ; C) to T(Γ, A, B, Δ; C);
   - (R_I) h ↦ h ∘_i u from T(Γ, I, Δ; C) to T(Γ, Δ; C);
   - (R\) k ↦ ev(y, k) from T(Γ; B\C) to T(B, Γ; C), and (R/) its mirror.

*Proof.* (1 ⇒ 2) The interpretation ⟦–⟧ : T → F is full (Theorem B6), and faithful by assumption, so it is an isomorphism of multicategories carrying the chosen arrows of T to the structure maps of F. F has the bijections, so T has them.

(2 ⇒ 1) The free biclosed monoidal category with unit F, viewed as a multicategory with F(Γ; A) = F(⊗Γ, A) and ⊗∅ = I, is the initial biclosed representable multicategory with chosen arrows and a map from the set of atoms. It is the syntactic multicategory of L\*_I with cut, modulo the β/η equations of the universal properties. So:
- There is a unique strict map G : F → T that fixes formulas and sends chosen arrows to chosen arrows.
- ⟦–⟧ : T → F is also strict: ⟦coh_m⟧ = m, and so on. So ⟦G(f)⟧ = f by initiality.
- For a type substitution τ, both G ∘ τ_F and τ_T ∘ G are strict maps F → T that agree on atoms. So they are equal. Here τ_T preserves the chosen arrows because coh's are closed under substitution.

Now show G(⟦t⟧) = t in T by induction on t.
- A variable is sent to itself.
- For t = coh_S[τ](t₁, …, tₙ), multifunctoriality gives G(⟦t⟧) = τ_T(G(⟦coh_S⟧)) ∘ (G⟦t₁⟧, …, G⟦tₙ⟧).
- By induction, G⟦tᵢ⟧ = tᵢ.
- G(⟦coh_S⟧) and coh_S are two terms of the UP\* type S, so the coh-equality rule makes them equal.

Hence ⟦t⟧ = ⟦t′⟧ implies t = G⟦t⟧ = G⟦t′⟧ = t′. ∎

So D10b is now a statement purely about UL_I\* terms: the derived abstraction operations must satisfy β and η *as UL_I\* equations*. Concretely, define [x]t by the bracket abstraction of B.4, and splitting and unit-elimination from it as in the fullness reduction. Then show, by induction on terms:
- **(β)** ev(x, [x]t) = t;
- **(η)** [x]ev(x, k) = k when x ∉ k;
- the mirror equations for /;
- the analogous pair for (R⊗) and (R_I).

Each inductive step needs one equation between coh composites over variables, with the induction hypotheses as holes. Where that equation's generalized sequent is UP\*, the coh rule gives it directly.

**Progress on (R\) (2026-11-18).** Write ≡ for UL_I\* equality. Done naively, each inductive step is one generalized equation, and that equation's type can fail to be UP\* (for instance Y, Y\I, … ⊢ C when the abstracted slot has type I). The failure disappears once each step is split into smaller coh equations, each generalized separately.

*β holds in T: ev(x, [x]t) ≡ t for every term t with leftmost variable x.* Induction on t, following the three clauses of bracket abstraction. Every equation below is the coh rule at a UP\* type, instantiated by type substitution and then by term substitution.
- **[x]x = j.** ev(x, j) ≡ x has type X ⊢ X.
- **x in the first argument.**
  - First, ev(x, coh_K(a, c)) ≡ ev(ev(x, a), c), at type Y, Y\A, A\B ⊢ B with A and B atoms. This is unit-free and L-pasting, and it is applied at A := B₁[τ], which may be I.
  - Then ev(w, coh_{S^c}(b⃗)) ≡ coh_S(w, b⃗), at type S itself.
  - Chaining these with the induction hypothesis ev(x, [x]t₁) ≡ t₁ gives the clause. The single combined equation is not UP\* when B₁ = I, but its two halves are.
- **Closed prefix.** The rebracketing coh_S(c⃗, s, …) ≡ coh_{S⊗}(coh_M(c⃗, s), …) has type S once c⃗ is abstracted to variables.
  - The names of Prop. B5 satisfy ev(y, ⌜c⃗ ⊗ –⌝) ≡ coh_M(c⃗, y), by induction on c⃗. The steps are K-β (as above), ev(coh_M(v⃗, y), coh_{T_S}) ≡ coh_M(coh_S(v⃗), y), whose type is T_S uncurried (UP\*), and associativity of m's.
  - Chaining K-β twice, the names' β, and ev against coh_{S⊗^c} gives the clause.

*η holds syntactically: [y]ev(y, k) ≡ k when y ∉ k.*
- [y]ev(y, k) = coh_K(j, coh_{ev^c}(k)).
- coh_{ev^c} has the identity type Y\Z ⊢ Y\Z, so it is ≡ to the variable.
- coh_K(j, w) ≡ w has type Y\Z ⊢ Y\Z.

So k ↦ ev(y, k) is surjective in T, and [y] is a section of it. It is a bijection as soon as **[x] respects ≡**, a ξ-rule. Then ev(y, k) ≡ ev(y, k′) gives k ≡ [y]ev(y, k) ≡ [y]ev(y, k′) ≡ k′. The mirror (R/) is the same.

*What the ξ-rule needs.* Induct on the derivation of ≡.
- **Coh-rule instance u ≡ v at type S[τ].** [x]u and [x]v both have type S^c[τ], and S^c is UP\* with the same normal form. So they are ≡.
- **Congruence in an argument containing x.** Immediate from the clause.
- **Substitution instances u[σ] ≡ v[σ].** These need a substitution lemma [x](u[s/z, c⃗/w⃗]) ≡ coh_K([x]s, ([z]u)[c⃗/w⃗]), proved by induction on u with the same kind of UP\* steps.
- **Congruence in a closed argument c that bracket abstraction moves into a name ⌜c ⊗ –⌝.** This is the only real case. It needs c ≡ c′ ⇒ ⌜c ⊗ –⌝ ≡ ⌜c′ ⊗ –⌝. Prop. B5 defines the name by recursion on the *syntax* of c, and there is no fixed coh U with ⌜c ⊗ –⌝ = coh_U(c): the would-be type Z ⊢ Y\(Z ⊗ Y) is not planar-provable. Closedness of c is exactly what B5 uses.

**Reduction once (R\) and (R/) hold.** The other two conditions of Prop. B7 follow.
- Any term h equals the uncurrying of its closed name n_h, i.e. a chain of ev's applied to the variables and n_h.
- Abstracting n_h to a variable turns an equation in h into a coh equation over variables. For example, h(u, λ(i, d)) ≡ h(i, d) for (R_I), and h(m(a, b)) ≡ h′ ⇒ … for (R⊗).
- Its type contains I only under the canonical isomorphisms (I\A ↦ A and so on), so it is UP\*.

**Closing the last lemma: generalized names (2026-11-18, proof sketch).** B5's names are defined by recursion on closed syntax. Comparing two of them runs into an interchange of names taken at different instances of Y, which is not a coh equation over variables. The fix is to define names for *open* terms, uniformly in a type variable Y, and to use them in the closed-prefix clause of bracket abstraction.

*Definition.* For a term u : Γ ⊢ C, define a closed term Ť_u : ⊢ (⊗Γ ⊗ Y)\(C ⊗ Y), by recursion on u (⊗∅ ⊗ Y := Y). For B5's closed terms it plays the role of ⌜u ⊗ –⌝.
- Ť_x = coh_{⊢ (X⊗Y)\(X⊗Y)}.
- For u = coh_S[τ](u₁, …, u_k) with uᵢ : Γᵢ ⊢ Bᵢ′, take the K-composite, in this order, of:
  - Ť_{u₁}[Y := Γ₂ ⊗ … ⊗ Γ_k ⊗ Y];
  - L_{B₁′}(Ť_{u₂}[Y := Γ₃ ⊗ … ⊗ Y]);
  - …;
  - L_{B₁′⊗…⊗B_{k−1}′}(Ť_{u_k});
  - coh_{T_S}[τ].

  Here L_B(s) = coh_{Z\W ⊢ (B⊗Z)\(B⊗W)}(s). That type is planar: its normal form is B, Z, Z\W ⊢ B ⊗ W. This is the step that is impossible for an open term on the left of y, as with ⌜u ⊗ –⌝, and it is why Ť_u carries Γ in its domain.

*Lemmas.* Each is proved by induction, and each inductive step is one coh equation at a UP\* type, with the induction hypotheses abstracted as variables.
1. **β:** ev(p, Ť_u) ≡ m(u, y), when p is the tensor of u's variables and y. The steps are K-β, ev against L_B, and ev against T_S, as in the β proof above.
2. **Naturality in Y:** for s : (D⊗Y)\(G⊗Y),
   ```
   K(Ť_u[Y := D⊗Y], L_C(s)) ≡ K(L_{⊗Γ}(s), Ť_u[Y := G⊗Y]).
   ```
   - For Ť_x the step type is Z\W ⊢ (X⊗Z)\(X⊗W).
   - For the T_S piece it is Z\W ⊢ (B₁⊗…⊗B_k⊗Z)\(C⊗W). Its normal form is N(B⃗), Z, Z\W ⊢ N(C) ⊗ W, which is UP\* when S is.
   - For the L_B pieces, functoriality L_B(K(a, b)) ≡ K(L_B a, L_B b) is unit-free L-pasting.
3. **Substitution:** Ť_{u[σ]} ≡ K(Ť_σ, Ť_u), where Ť_σ is the parallel name of σ, built in the same left-to-right order. The inductive step reorders pieces Ť_{u₁}, L(Ť_{σ₂}). That reordering is exactly lemma 2. The remaining steps are K-associativity and unit laws, and L_B functoriality.
4. **Congruence:** u ≡ v implies Ť_u ≡ Ť_v. Induct on the derivation of ≡.
   - **A coh-rule instance at S[τ].** Ť_u and Ť_v both have type T_S[τ], which is UP\*. So the coh rule applies.
   - **Congruence.** Ť is compositional.
   - **Substitution instances.** Use lemma 3.
   - **Refl, sym, trans.** Trivial.

With the closed-prefix clause of bracket abstraction rewritten to use Ť_c (closed c, Γ = ∅) instead of B5's name, the β proof above goes through unchanged, by lemma 1. The ξ-rule's last case is lemma 4. So (R\) and (R/) hold, and Prop. B7 gives:

**Theorem B8 (faithfulness of UL_I\*; D10b), proof sketch.** If two UL_I\* terms have the same denotation in the free biclosed monoidal category with unit, then UL_I\* proves them equal. Together with Theorem B6, the syntactic multicategory of UL_I\* *is* the free biclosed representable multicategory with unit.

*Checks.*
- `scripts/d10a/natural_names.py` checks the only step type that depends on S, the naturality step Z\W ⊢ (B⃗⊗Z)\(C⊗W) and its mirror. It is UP\* for 3,003 random UP\* coh's, with no failures. The checker rejects the non-planar Z ⊢ Y\(Z⊗Y).
- The β-step types depending on S, namely S itself and T_S uncurried, were already checked (`tens_names.py`).
- The remaining step types are fixed unit-free L-pasting sequents.

*Independent check (LIT thread, 2026-11-18).* Lemmas 1–4 were re-derived step by step and are correct at paper level. The check asked for four additions, made here.
1. **Bracketing.** All lists are right-nested: ⊗Γ = Γ₁ ⊗ (Γ₂ ⊗ (… ⊗ Y)), and L_{B₁′⊗…⊗B_{k−1}′} means iterated L, i.e. L_{B₁′}(L_{B₂′}(…)). Otherwise, use L_B(L_{B′}s) ≡ L_{B⊗B′}s, which is unit-free and L-pasting.
2. **Lemma 2 is stated for an arbitrary s : Z\W**, not only for names. The induction uses s′ = L_{Γ_k}(s) with Z′ = Γ_k ⊗ Z.
3. **Lemma 4 uses two facts.**
   - ≡ is closed under type substitution, and Ť_{u[τ]} = Ť_u[τ] syntactically.
   - A coh-rule instance has the form u′[τ] ≡ v′[τ] with u′, v′ : S. A term whose type is S[τ] need not be such an instance; the closed-term counterexample above is one. Ť_{u′} and Ť_{v′} both have type T_S, so they are ≡, and then apply τ.
4. **β for tuples.** ev(p, Ť_σ) ≡ the right-nested tensor of σ's terms with y. It is proved like lemma 1, and is needed for prefixes of several closed terms.

**Lemma D has a gap; the revised abstraction below avoids it.** The LIT thread's check of Lemma D (2026-11-18) found a gap in its prefix case. There, the right-hand side meets names Ť_{[w⃗′]tᵢ} of *curried* closed subterms. Relating these to Ť_{tᵢ} needs a further lemma, and that lemma's inductive step compares T_R with T_{R^c}. The two are not interdefinable by a generic coh: (B₁⊗B₂⊗Y)\(C⊗Y) ⊢ (B₂⊗Y)\((B₁\C)⊗Y) is not planar-provable. The fix is to stop using syntactic bracket abstraction in Prop. B7 at all.

**Revised abstraction.** For t : X, Γ′ ⊢ A, with x the leftmost variable and γ⃗ the rest, set

```
[x]t  :=  coh_F(γ⃗, Ť_t[Y := I]),   F = (Γ′, (X⊗Γ′⊗I)\(A⊗I) ⊢ X\A),
```

with Γ′ generalized to fresh atoms. F is UP\*: its normal form is X, Γ′, (X⊗Γ′)\A ⊢ A. Nothing about t enters except through Ť_t. Then:
- **ξ is immediate.** t ≡ t′ ⇒ Ť_t ≡ Ť_{t′} by lemma 4 ⇒ Ť_t[I] ≡ Ť_{t′}[I] (closure under type substitution) ⇒ [x]t ≡ [x]t′.
- **β.**
  1. ev(x, coh_F(γ⃗, n)) ≡ ρ(ev(m(x, γ⃗, u), n)), where u = coh_{⊢ I} and ρ = coh_{Z⊗I ⊢ Z}. This is one coh equation over x, γ⃗ and n, at the UP\* type X, Γ′, (X⊗Γ′⊗I)\(A⊗I) ⊢ A.
  2. By lemma 1 at Y := I, ev(m(x, γ⃗, u), Ť_t[I]) ≡ m(t, u).
  3. ρ(m(t, u)) ≡ t holds at type A ⊢ A.
- **η.** [y]ev(y, k) ≡ k for y ∉ k.
  1. By lemma 1 at Y := I, k ≡ ρ(ev(m(γ⃗, u), Ť_k[I])).
  2. Ť_{ev(y,k)}[I] is a K-chain of Ť_y, L_Y(Ť_k[I]) and T_ev.
  3. With n := Ť_k[I] abstracted to a variable, both sides of η are coh composites over γ⃗ and n, at the type Γ, (Γ⊗I)\((Y\Z)⊗I) ⊢ Y\Z. Its normal form is Y, Γ, Γ\(Y\Z) ⊢ Z, which is L-pasting, so the type is UP\*.

So k ↦ ev(y, k) is a bijection in T, with inverse [y]: (R\) holds, and (R/) holds by the mirror construction with Ť′. Only lemmas 1 and 4 are used, and those are independently checked. Lemmas A, B and D and the one-step-rewriting argument are no longer needed. `scripts/d10a/abstraction_types.py` checks the types F and U and their mirrors for |Γ′| ≤ 4 (no failures). It rejects a control in which Γ′ and X are in the wrong order.

**(R⊗) and (R_I).** Let n_h := [y₁]…[y_r]h be the closed name of a term h, so that h ≡ ev(y_r, … ev(y₁, n_h)) by β, with the variables in the order the iterated abstraction needs.
- **(R⊗) injectivity.** Suppose h ∘ m ≡ h′ ∘ m.
  - Abstract the variables a, b and the context on both sides. By ξ the results are ≡.
  - [b][a](ev(m(a, b), n)) ≡ Q(n), for the coh Q : (A⊗B)\C ⊢ B\(A\C). Both sides become ≡ after two applications of ev, by a coh equation at A, B, (A⊗B)\C ⊢ C. Then use injectivity of (R\) twice.
  - So Q(n_h) ≡ Q(n_{h′}). Q has a coh inverse, so n_h ≡ n_{h′}, and then h ≡ h′.
- **(R⊗) surjectivity.** h′ := ev(p, Q⁻¹([b][a]h)). Then h′ ∘ m ≡ h by β.
- **(R_I).** The same, with the coh I\C ⊢ C in place of Q.
- **Contexts Γ and Δ.** Abstract them too; the coh's needed are unit-free L-pasting.

**Theorem B8 status: proved at paper level, D10b closed (2026-11-18).** Lemmas 1–4 and the revised abstraction argument were each read independently by the LIT thread, and no gap was found. `scripts/d10a/abstraction_types.py` now checks every step type: F, U and their mirrors, the η type, A, B, (A⊗B)\C ⊢ C, Q, Q⁻¹ and the (R_I) cohs. That is 30 types, with no failures.

The generation statement of B.3 is now no longer needed: the reduction goes through cut-free L\*_I derivations directly.

**Comparison with Mimram.** CCCaTT normalizes products and the terminal type by the Bruce–Di Cosmo–Longo type isomorphisms before checking pasting. B.2 is the monoidal analogue for the unit, with one difference. The monoidal unit is not terminal, so I in a *result* position (A\I, duals) cannot be normalized away. Such I's are reached only by type substitution, never by the pasting check itself.

---

# Part C. Mimram's higher criteria, and the re-check of `internal-hom.md` §5.7 (D12)

## C.1 Re-check of §5.7 against the PDF

The PDF is Mimram, *An unbiased simply typed combinatory logic*. The rules in §5.7 are confirmed. Corrections and additions:

1. **Names.** The implicational system is CCaTT₁ (Mimram's name, "closed clones"). The system with products is CCCaTT₁.
2. **Pasting judgment.** Sequents are Θ \ Θ′ | Γ ⊢ A, where Θ′ records the target variables already introduced.
   - (→ps I) has side condition tgt(A) ∉ Θ′.
   - (→ps E) proves X from Γ, A₁→…→Aₙ→X, Δ, with premises Θ\Θ′ | Γ, Δ ⊢ Aᵢ. The head formula is removed from the context; its target stays in Θ′.
   - **In context:** Θ | Γ ⊢ps A is *defined* as Θ ⊢ps Γ → A, *not* as derivability of Θ\∅ | Γ ⊢ A.
   - Pasting ⊊ deterministic (Remark 16).
3. **Terms carry type *and* term substitutions,** coh_{Θ|Γ⊢A}[τ | σ]. Term substitution is needed: it is what repairs Komori's conjecture in the cartesian case.
   - Equality has reflexivity on variables, (ps=) with equal substitutions, and an explicit transitivity rule. Mimram notes transitivity is not derivable.
   - The planar UL of Part A needs only type substitution for each single coh, while composition is term substitution. This contrast is correct as stated in `planar-pasting-types.md` §2.
4. **"Cartesian closed ∞-categories" means (∞,1):** "weak higher categories in which all cells of dimension strictly above 1 are weakly invertible". The higher criterion is described as implemented in the tool and "left for future work".
   - The main theorem is formalized in Agda *postulating* Theorem 15 (pasting ⇒ contractible).

## C.2 The two higher criteria in the tool

Source: `src/pasting.ml` of [smimram/cccatt](https://github.com/smimram/cccatt) at commit `69bb11af` (2026-11-15). Every mode has a 1-dimensional criterion (`check1`): category, monoidal, symmetric monoidal, SMCC (balanced plus proof search), linear closed, cartesian, CCC (de-product plus Mimram's proof search), and compact closed. On top of these there are two higher-dimensional criteria, selected by the `orientation` setting.

**(Rev) Reversible, for (∞,1).** Given a context of objects, 1-cells and higher cells, and a goal of any dimension:
1. Repeatedly pick a higher hypothesis (an arrow between cells of dimension ≥ 1, or an identity type) with a **variable endpoint** x, other endpoint t, such that:
   - x does not occur in t;
   - x does not occur in the type of another remaining hypothesis ("not a boundary");
   - there is no earlier rule on x.

   Orient it as a rewrite x ↦ t, delete it, and substitute.
2. Strip all higher layers off the goal and check the underlying 1-dimensional type with `check1` in the remaining 1-dimensional context.

If this succeeds, the goal (of any dimension, between any two terms) is a coherence. Reading: this is based-path-space contractibility. A free cell with a free endpoint is a trivial extension in an (∞,1) setting. The code's own TODOs say "check that we are not a coboundary" and "this makes us construct (∞,1)-categories, we should also investigate (∞,∞)".

**(Dir) Directed, globular.** It is the default, but falls back to Rev when "elements" are on. It takes a `dimension` cut-off: cells above it are contracted as in Rev. For a goal of dimension n:
1. The n-dimensional hypotheses must be **directed equations x → y between variables**:
   - no loops;
   - pairwise distinct sources, and pairwise distinct targets;
   - acyclic.
2. Source context = context minus the targets; target context = context minus the sources. Recursively check both against the (n−1)-dimensional goal type.
3. The goal's source term may not use target variables, and its target term may not use source variables.

There is **no fullness condition**. With no n-dimensional hypotheses, *every* parallel pair of (n−1)-terms of a pasting (n−1)-type gets an n-cell in both directions. So all structural cells (β, η, associators, interchangers of independent hypotheses) are invertible, and non-invertible cells come only from hypotheses. This is CaTT's pattern (coherences are invertible; operations come from the pasting shape) with the 1-dimensional base replaced by the mode's pasting types.

## C.3 Soundness status, and what this means here

**Dir in dimension 2, over a graph (no 2-dimensional hypotheses).** Sound for the cartesian closed mode. Fiore–Saville ([MSCS 2021](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/coherence-for-bicategorical-cartesian-closed-structure/9AF32A2CDBDD01A5FB01D9D6DDCD80F0)) prove that in the free cartesian closed bicategory on a graph there is at most one 2-cell between parallel 1-cells. Every bicategory with cc structure is biequivalent to a 2-category with 2-categorical cc structure. And all inhabitants of a pasting type are βη-equal (Mimram, Thm 15), so the 2-cell exists and is invertible.

**Everything beyond.** This covers Dir with 2-dimensional hypotheses, Dir in dimension ≥ 3, and Rev in all dimensions. Soundness needs a coherence theorem for free cartesian closed (∞,1)- or (∞,ω)-categories (with pseudo exponentials) on computads. For (∞,1), and hence Rev, see C.4 (proof sketch). For (∞,ω), none is known. It is posed, self-contained, in [`conjectures/cartesian-closed-higher-coherence.md`](conjectures/cartesian-closed-higher-coherence.md).

**Consequences for the project.**
- *Under P* (pseudo ambient), Dir with the CCC base is a candidate replacement for the λ/⌜⌝ rules of `internal-hom.md` §5.4, as §5.7 suggested. It is now an explicit criterion, not a guess. Its β/η cells are invertible coherences, which is what the pseudo hom needs.
- *Under L / Gray*, Dir is the wrong shape. In monoidal mode, for hypotheses f : a → a′ and g : b → b′, both (f⊗b′)∘(a⊗g) → (a′⊗g)∘(f⊗b) and its reverse are accepted. The source and target contexts are the whole context, and no variable is forbidden. So Dir makes interchangers invertible and fails the PL-ω test (Part F). Part F's candidate is Dir plus one orientation condition.

## C.4 Internal attempt: Rev is sound, via normalization by evaluation (D12, Questions 1–2)

*Added 2026-11-18. Proof sketch; not yet independently reviewed.*

**Theorem C1 (discreteness).** Let Σ be a set of base types together with a set of constants c : A → B between simple types over them; this covers Question 1's "set or directed graph". Let F(Σ) be the free cartesian closed (∞,1)-category on Σ. Then every mapping space of F(Σ) is discrete. Hence F(Σ) is equivalent to the free cartesian closed 1-category on Σ, i.e. simply typed λ-terms with constants modulo βη.

*Proof sketch.* This is the Altenkirch–Hofmann–Streicher / Fiore normalization-by-gluing argument, with every input checked to survive in (∞,1). References: Altenkirch, Hofmann, Streicher, *Categorical reconstruction of a reduction free normalization proof* (CTCS 1995); Fiore, *Semantic analysis of normalisation by evaluation for typed lambda calculus* (PPDP 2002).

1. **Renamings.** Let Ren be the 1-category of contexts (lists of types) and renamings. Let ι : Ren → F(Σ) send a context to the product of its types. The nerve N : F(Σ) → E := PSh(Ren) (presheaves of *spaces*), A ↦ Map(ι–, A), preserves finite products.
2. **Gluing.** Let Gl be the comma ∞-category E ↓ N. Its objects are (P, A, p : P → N A). It is cartesian closed, and the projection Gl → F(Σ) preserves the structure.
   - Products are computed componentwise.
   - (Q, B, q)^(P, A, p) = (R, B^A, r) with R = N(B^A) ×_{(NB)^P} Q^P, a pullback in the ∞-topos E.
   - The mapping-space check is a pasting of pullbacks of mapping spaces, verbatim as in the 1-categorical proof (Mitchell–Scedrov, *Notes on sconing and relators*, 1993). It uses only that E is cartesian closed with pullbacks and that N preserves finite products.
3. **Section.** By the universal property, there is a cartesian closed s : F(Σ) → Gl sending a base type X to (Ne_X, X, emb) and a constant c to its action on neutrals.
   - Here Ne and Nf are the *set-valued*, hence discrete, presheaves of η-long neutral and normal terms.
   - The composite F(Σ) → Gl → F(Σ) is cartesian closed and is the identity on generators. The space of such functors is contractible, so the composite is equivalent to the identity.
4. **Reflect and reify.** By induction on types A, build maps of presheaves of spaces reflect_A : Ne_A → P_A and reify_A : P_A → Nf_A over N A, where s(A) = (P_A, A, p_A). The clauses are the standard ones.
   - For A → B: reify evaluates at the weakening Γ ↪ Γ, a : A and at reflect_A(var a), then applies reify_B and λ-abstracts.
   - Everything here lives in the ∞-topos E: the P_A, the maps p_A, N applied to the structure maps of F(Σ), and the equivalence N(B^A) ≃ (NB)^{+A}, where (–)^{+A} precomposes with context extension. So the clauses can be written as ordinary function definitions in the internal language (HoTT) of E. This is how Uemura avoids externalizing coherence data. The equations emb ∘ reify ≃ p_A and p_A ∘ reflect ≃ emb hold up to homotopy, by η and β in F(Σ) transported through N.
5. **Retract.** For f ∈ Map(ιΓ, A), apply s(f) to the generic element reflect_Γ(vars) ∈ P_Γ(Γ), then apply reify_A. This gives a map of spaces nf : Map(ιΓ, A) → Nf_A(Γ). By the commuting triangles, together with p_Γ(generic) = id and π ∘ s ≃ id, emb ∘ nf is homotopic to the identity up to the self-equivalence induced by π ∘ s ≃ id. So Map(ιΓ, A) is a retract of a set, hence discrete.
6. **Every object.** Every object of F(Σ) is equivalent to a type. The full subcategory of types is cartesian closed and contains Σ, so by the universal property it is everything.
7. **Conclusion.** So F(Σ) is a 1-category. By its universal property among 1-categories, it is the free cartesian closed 1-category. ∎

**Literature.**
- Uemura, *Normalization and coherence for ∞-type theories* ([arXiv 2212.11764](https://arxiv.org/abs/2212.11764)), proves by the same strategy that free models of an ∞-type theory with dependent function types, a natural-number type and constants are 0-truncated. He says the strategy works heuristically for many fragments.
- Uemura also remarks that Fiore–Saville's purely categorical proof "seems to scale to the ∞-dimensional setting". Theorem C1 is that scaling, written out for the simple (cartesian closed) case.
- So Question 1 of the outbox prompt is answered positively, up to checking this sketch.

**Corollary C2 (soundness of Rev; Question 2).** Every goal accepted by (Rev) has a contractible space of fillers in the free cartesian closed (∞,1)-category on its context.

*Proof.*
1. **Contraction is a trivial extension.** Contracting α : x → t, where x is a variable of dimension k − 1 ≥ 1 that is not free in t and occurs in no other type, removes a pushout Γ ⊔_{D^{k−1}} J.
   - Here J is a pair of parallel (k−1)-cells with a k-cell between them, attached along t.
   - In (∞,1), cells of dimension ≥ 2 are invertible, so D^{k−1} → J is an equivalence.
   - The free cartesian closed functor is a left adjoint, so it preserves pushouts. A pushout of an equivalence is an equivalence. So the contracted context presents the same free cartesian closed (∞,1)-category, and goals transport along x := t.
2. **The remaining context is 1-dimensional,** i.e. a Σ as in Theorem C1.
3. **A goal of dimension 1** is a type whose inhabitants form a single βη-class, by Mimram's Theorem 15 (with the context's constants as free variables). By Theorem C1, its space of fillers is that one-point set.
4. **A goal of dimension n ≥ 2** asks for a path, or a higher path, between points of a discrete space whose endpoints are equal, by step 3. That space is contractible, in both directions. ∎

**Researcher response (verified, `conjectures/answered/cartesian-closed-higher-coherence-2026-11-18.md`).**
- Q1 and Q2 are proved by a different route: a strict simplicial model plus a retract. It agrees with C1 and C2, and the verifier found no error in C.4 as a sketch.
- **Q3 is proved over graphs in every dimension.** The 1-core R₁ is right adjoint to the inclusion of (∞,1) into higher categories (Ozornova–Rovelli–Walde, arXiv 2603.11005, Thm 2.20), and it inherits cartesian closed structure. So the free higher cartesian closed category on a graph is the free (∞,1) one, hence the 1-category. In particular this proves coherence for cartesian closed tricategories over a graph.
- **cccatt@69bb11af has one implementation bug.**
  - The unordered Dir duplicate check compares position-carrying terms (`pasting.ml` ll. 597–602). It therefore accepts a 3-goal that has no filler, which is refuted in Cat.
  - It is filed upstream as [smimram/cccatt#15](https://github.com/smimram/cccatt/issues/15), reproduced at master 69bb11a. The fix `var x = var x'` passes cccatt's test suites.
  - *Correction (2026-11-18):* the Rev side condition at l. 474, which tests the hypothesis name, is **not** a bug. `add_rule` rejects every cycle, and any higher hypotheses left over fail `check1`, so no wrong acceptance is possible. It differs only from our paraphrase of Rev in C.2 ("x has not been rewritten before"), which describes the intended behaviour, not that line.

**What remains of D12 (updated).** Abstract Dir with *non-invertible* higher hypotheses. That needs a relative coherence theorem; prompt: `conjectures/answered/dir-relative-coherence-2026-11-18.md`.

**Answer to the follow-up prompt (verified, `conjectures/answered/dir-relative-coherence-2026-11-18.md`): Dir is sound whenever the non-invertible generators have dimension ≤ 2.** Take the free pseudo cartesian closed (∞,2)-category on a graph together with 2-generators forming chains. Every space of 2-cells is empty or contractible. The proof has four steps:
1. Long βη-normal forms, natural in relabelling, with no permutation quotient needed.
2. A degreewise simplicial cartesian closed category 𝒦 whose homs are nerves of posets ∐∏[r].
3. Haugseng rectification to a strict enriched cartesian closed category.
4. A retract 𝓕 → 𝒦 → 𝓕.

*Correction to our expectation:* a generator α need not occur only once in a term. Duplicated uses give cubes [1]^m.

**Still open (D12):** non-invertible generators of dimension ≥ 3. Round-2 prompt, written by the verifying thread: `conjectures/answered/dir-relative-coherence-r2-2026-11-18.md`, answered and verified 2026-11-18: Dir is sound in every dimension, so this is now closed.

*Superseded:* Question 3: Dir in (∞,ω), with directed hypotheses. Its smallest case is dimension 3 over a graph, i.e. coherence for free cartesian closed tricategories. The natural attack is Theorem C1's argument in (∞,ω): glue along a nerve into presheaves of (∞,ω)-categories.
- Fiore–Saville did the bicategorical version.
- The obstacle is step 2. It needs pseudo exponentials in an (∞,ω)-categorical comma object. It also needs a statement that the presheaves of normal forms are discrete as (∞,ω)-categories, i.e. no non-identity cells between normal forms. That is exactly what Dir's directed hypotheses violate, because those hypotheses generate non-invertible cells between neutrals.

---

# Part D. Dualities under L (D8)

## D.1 Dualities and the Gray tensor of Steiner complexes

For K ⊆ {1, 2, …}, the duality D_K reverses cells whose dimension is in K. On a Steiner complex it is
- ∂ ↦ ε∂ on n-dimensional generators, with ε(n) = −1 iff n ∈ K;
- a reversed n-cell swaps its (n−1)-dimensional source and target entries in the table.

So D_K ν(X) ≅ ν(X^ε).

The Gray tensor is ∂(x⊗y) = ∂x⊗y + (−1)^|x| x⊗∂y. Isomorphisms of Steiner complexes preserve bases with sign +1. So the only candidate isomorphisms that respect the generator correspondence (which is what a term-level duality needs) are:
- id: x⊗y ↦ x⊗y;
- sw: x⊗y ↦ y⊗x.

Comparing the coefficients of ∂x⊗y and x⊗∂y for |x| = p, |y| = q:

```
id : D_K(X⊗Y) ≅ D_K X ⊗ D_K Y   iff   ε(p+q) = ε(p)  (p ≥ 1, q ≥ 0)   and   ε(p+q) = ε(q)  (q ≥ 1)
sw : D_K(X⊗Y) ≅ D_K Y ⊗ D_K X   iff   ε(p+q) = (−1)^q ε(p)  (p ≥ 1, q ≥ 0)   and   (−1)^p ε(p+q) = ε(q)  (q ≥ 1)
```

**Proposition D1.** The id condition holds iff ε is constant on dimensions ≥ 1, i.e. K ∈ {∅, all}. The sw condition holds iff ε alternates, i.e. K ∈ {odd, even}.

So:

```
(X⊗Y)^op   ≅ Y^op ⊗ X^op        (odd duality; Chanavat)
(X⊗Y)^co   ≅ Y^co ⊗ X^co        (even duality)       ← the [recall] of internal-hom.md §5.6, now proved
(X⊗Y)^coop ≅ X^coop ⊗ Y^coop    (total duality keeps the order)
```

Every other D_K turns ⊗ into the **twisted tensor**

```
X ⊗_ε Y := D_ε(D_ε X ⊗ D_ε Y),   ∂(x⊗y) = ε(p+q)[ε(p) ∂x⊗y + (−1)^p ε(q) x⊗∂y].
```

The twisted tensor is neither ⊗ nor ⊗^rev. For example, take K = {2} on D¹⊗D³. The 3-generator α⊗s₂ gets the boundary orientation of ⊗^rev, not of ⊗. The 4-generator α⊗c₃ gets the orientation of ⊗, not of ⊗^rev. So no single factor order matches.
- *Checked:*
  - Agda: `GrayDuality.agda`, `IdC↔Const` and `SwapC↔Alt`.
  - Python: `scripts/duality_check.py`, all K ⊆ {1..6} on globes Dᵖ⊗D^q with p, q ≤ 3. The output is exactly {∅, all} and {odd, even}.

## D.2 Which ambient dualities preserve two-tier L

In two-tier L, a wedge ΣΘ₁ ∨ … ∨ ΣΘₙ has hom-shape U = Θ₁ ⊗ … ⊗ Θₙ (execution order, `pseudo-vs-gray.md` §3.1). An ambient duality D_J acts by:
- **on homs,** the shifted duality K = J − 1 = {j − 1 : j ∈ J, j ≥ 2};
- **if 1 ∈ J,** it also reverses the wedge, so the factor order reverses.

Hence D_J maps derivable L-judgments to derivable L-judgments (with the canonical variable correspondence) iff
- 1 ∉ J and id holds for K, or
- 1 ∈ J and sw holds for K.

It maps them to the factor-reversed (oplax) theory iff
- 1 ∉ J and sw holds for K, or
- 1 ∈ J and id holds for K.

**Theorem D2.** Agda (`symmetry-classification`, `to-oplax-classification`) checks the sign arithmetic. The reduction from D_J to the pair (K = J − 1, order reversal iff 1 ∈ J) is the argument just given; in the Agda it is the definition of `Symmetry` and `ToOplax`.

| J | effect on two-tier L |
|---|---|
| ∅, {2,3,4,…}, {1,3,5,…} (odd), {1,2,4,6,…} | **symmetry** (lax ↦ lax) |
| {1}, all, {2,4,6,…} (even), {3,5,7,…} | **lax ↦ oplax** |
| any other J (e.g. {3}, Agda `J₃-not-symmetry`, `J₃-not-oplax`) | **neither**: lands in a mixed theory L_ε |

So 4 of CaTT's 2^ℕ opposites survive as symmetries. Restricted to dimension ≤ 3 (the Gray-category level), this says reversing 1-cells alone swaps lax/oplax, while op (1- and 3-cells) is a symmetry.

## D.3 The orientation-parameterised kernel

Define **L_ε** as two-tier L with supports computed in ν(Θ₁ ⊗_ε … ⊗_ε Θₙ), for ε : {1,2,…} → {±1}.
- L_ε = L iff ε is constant; L_ε = L^rev iff ε alternates.
- Then D_J : L_ε → L_{J·ε} on homs (with the 1 ∈ J reversal), and D_K(X ⊗_ε Y) = D_K X ⊗_{Kε} D_K Y, a one-line computation.
- So the duality group acts on the family freely up to the global sign.

**Practical form.**
1. The kernel implements L_ε. It costs one sign per dimension in the Leibniz formula, and loop-freeness is preserved because duals of Steiner complexes are Steiner.
2. A lemma proved once in L_ε is available in L_{J·ε} for every J by the opposites meta-operation, with no reproof.
3. To use it back in L you need L_{J·ε} = L, which forces J into the symmetry row of D2.

**Worked example.** Prove the lax naturality cell (the operation-case interchanger of `pseudo-vs-gray.md` §3.4) once.
- D_{1}: gives the oplax naturality cell, the same derivation read in L^rev.
- D_{1,3,5,…}: gives a cell of L again; the naturality cell for the opposite transformation.
- D_{3}: gives a cell of L_ε with ε flipping hom-dimension 2. That theory has lax 1-dimensional interchange and oplax interchange between hom-1-cells and hom-3-cells. It is a mixed theory that L does not contain.

Soundness of L_ε is inherited: its models are the D_J-duals of Gray-enriched categories, i.e. categories enriched in ⊗_ε.

**Under uniform L** the analysis is redone in §D.4: the prediction above (every shift J − k must pass the two-tier test) is correct, and it leaves only J = ∅.

## D.4 Dualities of the uniform core V + S (D8, uniform part)

*Setting: spec chapter 2, §2.3. The side condition computes in V + S, S ⊆ {inner law, R}. Agda: `src/CaTTExp/GrayDualityUniform.agda` (no postulates).*

### D.4.1 What a duality does to an interchanger

**The Gray configuration at level n.** Take the context Γ_n = Σⁿ(ΣD¹ ∨ ΣD¹): two (n+2)-cells α (left) and β (right), juxtaposed along an n-cell. For n = 0 these are two 2-cells side by side along an object (spec §2.3 example (a)), and for n = 1 two 2-cells of an object side by side along a 1-cell (example (c)). The two composites of their whiskered parts along (n+1)-cells are "β's part first" and "α's part first". The elementary interchanger is the (n+3)-cell

```
χ_n : (β's part first) ⇛ (α's part first)        (right first ⇛ left first)
```

Its orientation is positional at every level (lax r8 (K9)). It is accepted as `coh_{Γ_n, right first → left first}` in every setting. For n = 0 it is the operation case. For n ≥ 1 its Gray image is an identity on a full-support cell. No admissible theory has its reverse (requirement 3), so `coh_{Γ_n, left first → right first}` is **rejected in every setting**.

**The orientation lemma.** Let D_J reverse the cells whose dimension is in J, and write a_m = 1 if m ∈ J, 0 otherwise. For a configuration of (l+1)-cells juxtaposed along a k-cell, three dimensions decide what D_J does to an interchanger between its two composites:
- **k+1.** If (k+1)-cells are reversed, the k-composition reverses, so α becomes the right operand and β the left one.
- **l+1.** If (l+1)-cells are reversed, the l-composition reverses, so in each composite the other part comes first.
- **l+2.** If (l+2)-cells are reversed, the cell itself is reversed.

Each is a flip of "which operand comes first in the source". So:

**Lemma D3.** D_J sends a cell oriented "right first ⇛ left first" to one with the same orientation in the dual configuration iff

```
row_J(k, l)  :=  a_{k+1} + a_{l+1} + a_{l+2}  ≡  0  (mod 2),
```

and to the reverse orientation iff the row is 1.
- *Agda:* `dual-canonical`, `dual-canonical-iff`, `dual-reversed-iff`. The three flips are the definition `dualIch`. The Agda checks that their composite is governed by the one sign. That the action is these three flips is the argument just given.

**Corollary.** The dual of Γ_n is Γ_n up to renaming. If row_J(n, n+1) = 1, then D_J sends the accepted interchanger χ_n to the rejected type "left first → right first". So **every Gray row must be 0** for D_J to be a symmetry, and **every Gray row must be 1** for D_J to map uniform L to the oplax core.

**The two-tier test is also necessary.** Uniform L ⊂ two-tier L (spec §2.6), so a coherence rejected in two-tier L is rejected in uniform L. The witnesses of §D.2 for failing the two-tier test can be taken over the contexts ΣD¹ ∨ ΣD^q and ΣD^q ∨ ΣD¹: by Proposition D1, failure of IdC and of SwapC is already visible at p = 1. On those contexts uniform L and two-tier L agree, because F_{V+S} has no interchanger along k ≥ 1 there.
- In 𝔉(ΣD¹ ∨ ΣD^q), the hom is λD¹ ⊗ λD^q, with D¹ = (f, f′, α).
- Fix a hom-level j. The generators of dimension ≥ j+2 are f ⊗ e and f′ ⊗ e with |e| ≥ j+2, and α ⊗ e with |e| ≥ j+1. The f-side ones run from f ⊗ e_j⁻ to f ⊗ e_j⁺, the f′-side ones from f′ ⊗ e_j⁻ to f′ ⊗ e_j⁺, and each α ⊗ e spans the whole range from f ⊗ e_j⁻ to f′ ⊗ e_j⁺ (by ∂⁻(α⊗e) = f⊗e + α⊗∂⁺e and ∂⁺(α⊗e) = f′⊗e + α⊗∂⁻e).
- So the only j-routes between the ends are [f ⊗ e, then α ⊗ e_j⁺] and [α ⊗ e_j⁻, then f′ ⊗ e′]. The separating cells α ⊗ e_j^± have dimension j + 1. No two cells of dimension ≥ j+2 are ever ∗_j-adjacent, so there is no interchange position at any level j (for j = 0 this is the factor α ⊗ g_i).
- "No interchange position ⇒ F_{V+S}(Γ) = 𝔉(Γ)" uses the fact that every cell V adds beyond the Gray presentation involves an inner interchanger (as in the (K7)–(K11) constructions). Requirement 4 alone does not say this.
- So a two-tier witness is accepted in uniform L, and its rejected dual is rejected there too.

Acceptance of χ_n for n ≥ 1 above also uses the Gray-projection reading of the side condition (ledger S1, S11). This step is **argued**, not machine-checked.

### D.4.2 Classification

**Theorem D4.** Let J ⊆ {1, 2, …} and let S, S′ be settings.
1. D_J sends every derivable judgment of uniform L in setting S to a derivable judgment in some setting S′ iff **J = ∅**. Then S′ = S.
2. D_J sends uniform L in setting S to the oplax core (every elementary interchanger reversed) iff **J = all**, every dimension ≥ 1. The image is the oplax core in setting mirror(S), which exchanges the inner law and R (§D.4.3).
3. For every other J, some accepted coherence has a rejected dual. The image is the mixed core D_J(V + S), described below.

*Proof.* (1, ⇐) and (2, ⇐) are immediate. For (1, ⇒), §D.4.1 gives two necessary conditions:
- (G) row_J(n, n+1) = 0 for every n;
- (T) J passes the two-tier test, so J ∈ {∅, {2,3,…}, odd, {1,2,4,6,…}} by D2.

Under (T):
- If 1 ∉ J, then J is constant from dimension 2 on. The row (1, 2) is then 3a_2 = a_2, so a_2 = 0 and J = ∅.
- If 1 ∈ J, then J alternates from dimension 2 on. The rows (1, 2) and (2, 3) are then a_2 + 1 and a_2, which cannot both be 0.

(2, ⇒) is the same computation with every row equal to 1. It leaves only J = all. ∎
- *Agda:* `kernel-theorem` (both parts, for c = +1 and c = −1).

**Neither condition suffices alone.**
- (G) alone is solved by the period-3 sets, for example J = {1,2,4,5,7,8,…}, which reverses n iff 3 ∤ n. That set fails (T) (`J124-gray-rows`, `J124-not-two-tier`).
- (T) alone is solved by op (`op-two-tier`), which fails (G) at level 1 (`op-gray-rows`).

So the uniform result is not a level-by-level repetition of the two-tier one. It needs both the Gray interchangers inside objects and the Leibniz data across objects.

**Relation to §D.3's prediction.** §D.3 predicted that J is a symmetry iff every shift of J passes the two-tier test. That is the reading in which each level k carries the full Gray orientation data, with one row (k, l) for every l > k. Arithmetically, this gives the same answer:
- all rows (k, l) equal c ⟺ every shift passes the test ⟺ J ≡ c (`all-rows↔const`, `all-rows↔shifts`, `level0↔Symmetry`, `level0↔ToOplax`);
- of the four two-tier symmetries ∅, {2,3,…}, odd and {1,2,4,6,…}, the shifts are all, even, even and odd, and only ∅ survives.

The proof above does not need the rows with l > k+1, whose geometric meaning inside homs (the tensor-shaped naturality data of lax r8 (K3)) is not pinned down in the notes.

**Worked example: CaTT's op.** op = D_odd is a two-tier symmetry (`op-two-tier`). Take Γ₁ = Σ(ΣD¹ ∨ ΣD¹), the context of spec §2.3 example (c): two 3-cells of 𝒦 (2-cells inside an object) juxtaposed along a 1-cell.
- The interchanger χ₁, a 4-cell from "right first" to "left first", is accepted in every setting.
- op reverses the 3-cells, so their 2-composition reverses. It keeps the 1-composition (2 ∉ odd) and keeps χ₁ (4 ∉ odd).
- So the op-image of χ₁ has type "left first → right first", and it is rejected.
- *Agda:* `op-row-1-2`, `op-reverses-1-2`, `op-gray-rows`.

**The mixed cores.** The orientation of D_J(V + S)'s Gray interchanger at level n is row_J(n, n+1) = a_{n+1} + a_{n+2} + a_{n+3}. For the sets J below, this is lax or oplax according to n alone:

| J | Gray interchanger at level n after D_J |
|---|---|
| ∅ | lax at every n (the identity) |
| all | oplax at every n |
| odd (op) | lax for even n, oplax for odd n |
| even (co) | oplax for even n, lax for odd n |
| {2,3,4,…} | lax at n = 0, oplax for every n ≥ 1 |
| {1,2,4,6,…} | lax for n = 0 and every odd n, oplax for every even n ≥ 2 |

D_J(V) is the least theory satisfying requirements 1–5 transported along D_J. Leastness transfers because D_J is a bijection on cells that preserves generator sets. So D_J(V) is the most general theory with its orientation pattern, and D_J(V + S) adds the duals of the laws in S (§D.4.3).
- **The orbit is free.** D_J D_{J′} = D_{J △ J′}. So D_J(V + S) = D_{J′}(V + S′) forces D_{J △ J′} to be a symmetry, and J = J′ by Theorem D4(1).
- **Checking a mixed core costs nothing.** D_J is an involution on judgments, so SC_{D_J(V+S)}(Γ, A) ⟺ SC_{V+S}(D_J Γ, D_J A). A checker for D_J(V + S) is the V + S checker run on the dualised input. Unlike L_ε of §D.3, nothing has to be implemented.

**Practical consequence.** The two-tier rule "prove a lemma once, get its op-dual free" (§D.3, item 2) does not hold in the uniform core. A uniform-L lemma's D_J-image is a lemma of the core D_J(V + S), which is V + S only for J = ∅. The total dual of a lax lemma is the corresponding oplax lemma, in the oplax core. Within V + S, a dual can still be used whenever the dualised coherence happens to be accepted. But there is no uniform transfer: by Theorem D4 every J ≠ ∅ has an accepted coherence with a rejected dual.

**Restricting to an `ord` fragment.** If every object of the development is marked `ord` (spec chapter 3), the side condition is the two-tier one and §D.2 applies: op and the other three two-tier symmetries come back. In the uniform core, `ord` is what brings the op-symmetry back. Whether the `ord` reduction is exact is ledger E7.

### D.4.3 The switches under duality

The two visible laws are splits of an interchanger whose operand is a composite (`Join/SwitchLaws.agda`, `splitL` and `splitR`):
- the **inner law** (left split): ι(F ⨾ F′, G) = the paste of ι(F, G) and ι(F′, G);
- **R** (right split): ι(F, G ⨾ G′) = the paste of ι(F, G) and ι(F, G′).

Take an interchanger at level k, with its operands juxtaposed along a k-cell. D_J trades its left and right operands iff k+1 ∈ J. The order inside the composite F ⨾ F′ may reverse too, but the dual is still the split of a composite operand. So at level k, D_J sends the left split to the right split, and back, iff k+1 ∈ J. An equation is sent to an equation, and the image of each law needs no orientation.

**Proposition D5.**
- Let mirror(S) swap the two switches. The dual setting at level k is S if k+1 ∉ J, and mirror(S) if k+1 ∈ J. It contains exactly the duals of the laws of S (`dual-has`).
- The total duality mirrors at every level (`total-mirror`). So D_all maps
  - V to V^∘,
  - V + {inner law} to V^∘ + {R},
  - V + {R} to V^∘ + {inner law},
  - T₁₂'s profile to its oplax mirror,

  where V^∘ := D_all(V) is the least oplax-admissible theory (`mirror-iccS`, `mirror-rspS`, `mirror-vS`, `mirror-allS`).
- The dual of one setting is the same at every level iff S is mirror-symmetric (∅ or both switches) or [k+1 ∈ J] does not depend on k (`level-uniform`). For any other pair, the image of a single setting is a level-dependent law set. This only matters for the mixed cores, since J = ∅ and J = all are the only dualities that keep the orientation uniform.

So the four settings of the lax core and the four settings of the oplax core correspond under the total duality, with {inner law} and {R} trading places. A development checked in {inner law} dualises to an oplax development checked in {R}, and conversely.

## D.5 Dualities, ⊗ and the biclosed rules (F.7.4)

*Agda: `src/CaTTExp/Gray/Biclosed/Mirror.agda` (no postulates).*

The biclosed rules involve two dualities, and they must be kept apart.
- **External:** D_J acting on the ambient, as in §D.2–D.4.
- **Internal:** the duality (–)^K acting on objects, X ↦ X^K, a functor of Cat_ω.

Proposition D1 is about the internal one: (X ⊗ Y)^K ≅ X^K ⊗ Y^K iff K ∈ {∅, all}, and ≅ Y^K ⊗ X^K iff K ∈ {odd, even}. D1 is a statement about Gray tensors of Steiner complexes, so it does not depend on the core.

**External dualities with 1 ∈ J do not act on multimaps.** A multimap (X₁, …, Xₙ ▸ Z) is an ambient 1-cell from a tensor of inputs to one output. Reversing it gives a 1-cell from one object to a tensor, which is not a judgment of the system for n ≠ 1. So D_J with 1 ∈ J, including the total duality of Theorem D4(2), sends the biclosed fragment to a "co-closed" system, with left adjoints to ⊗ in place of residuals. That system is not part of the kernel. Only the pure fragment with n = 1 (L itself) carries over.

**Internal dualities: the mirror.** For alternating K, every piece of the biclosed system has a mirror image:
- a multimap X₁ ⊗ … ⊗ Xₙ → Z gives (Xₙ^K, …, X₁^K ▸ Z^K);
- the lax hom A\C goes to the oplax hom C^K/A^K, and C/A goes to A^K\C^K;
- the corollas m, e^ℓ and e^r go to m with swapped arguments, e^r and e^ℓ;
- p_{Δ,Θ} goes to p_{Θ^K, Δ^K}, using D1 for the Gray tensor of contexts;
- a time slot at gap g of an n-ary type goes to gap n − g, so a lax slot (after the data) becomes an oplax slot (before it), matching Cat_ω's (X ⊗ Dᵏ)^K ≅ (Dᵏ)^K ⊗ X^K;
- ⟦Dᵏ⟧^K ≅ ⟦Dᵏ⟧, with source and target swapped iff k ∈ K.

**Proposition D6 (mirror of the rows).** The mirror is an involution on formulas, multimap types and rows. For every row ρ:
- H(ρ*) = H(ρ)* and B(ρ*) = B(ρ)*;
- r_{ρ*}(x*) = r_ρ(x)* for every term x;
- the rows read off M* are exactly the mirrors of the rows read off M. So the candidate templates of the decision procedure (Lemma GB-dec) are mirror-closed.

The pair, probe and unit rows go to rows of the same kind at the mirrored slot, and the left evaluation row goes to the right one and back.
- *Agda:* `mirFm-invol`, `mirM-invol`, `mirRow-invol`, `H-mir`, `B-mir`, `rmap-mir`, `rowsOf-mir`, `rowsOf-mir⁻`.

**What the mirror does to the rest of a template** (paper only):
1. **Directed cuts.** A directed goal d at slot ⟦Dᵏ⟧ inherits its direction from the hypothesis b. In the mirror, b's and d's directions both swap iff k ∈ K. So the mirror of a (GB-dcut) instance is a (GB-dcut) instance, with u⁻ and u⁺ exchanged iff k ∈ K. "No reverse cell" (§8.3 orientation) is preserved.
2. **Collars.** The invertible collars a^± and the comparison cells reverse with their slots. So the mirror of a generic context is a template context only after replacing each reversed collar by its inverse. Inverses of invertible cells are available (chapter 3's `inv` mark), so admissibility is preserved, but not literally on the nose. The Agda therefore stops at the rows.
3. **Probe restrictions.** A restriction along ⟦σ⟧ for an L-substitution σ : Θ′ → Θ mirrors to the restriction along ⟦σ⟧^K = ⟦D_K σ⟧. That is a kernel restriction iff D_K σ is admissible in the core, which holds for all σ iff D_K is a symmetry of the core.

**Consequence.**

| Core | Internal dualities that are symmetries of L + biclosed rules |
|---|---|
| two-tier L | ∅ and the mirror for K = odd (op is a two-tier symmetry, D2). K = even maps to the oplax two-tier core. K = all keeps ⊗'s order but is lax ↦ oplax on the probes. Every other K twists ⊗ (D1) and has no action. |
| uniform L, any setting | **∅ only.** The mirror for K = odd lands in the biclosed system over D_odd(V + S), and for K = even over D_even(V + S), which are mixed cores (§D.4.2). K = all (order-preserving, all slots reversed) lands over the oplax core with mirror(S). |

So in the uniform core the biclosed layer is mirror-symmetric on its own (Proposition D6), but the coupling through the probe restrictions breaks the symmetry. The symmetry-breaking comes entirely from L's side condition, not from ⊗ or the residuals.

**Worked example.** Over two-tier L, the right curry of a lax transformation α : (B, ⟦D¹⟧ ▸ C) is a map B → C/⟦D¹⟧. Its op-mirror is the left curry ⟦D¹⟧^op ⊗ B^op → C^op, an oplax transformation of opposites with the same derivation. Over uniform L the same mirror is still valid on the rows. But if B's diagram involves an interchanger along a 1-cell inside a probe, for example a restriction along the χ₁ of §D.4.2 inside ⟦Θ⟧, then the mirrored restriction is along the reversed interchanger, which uniform L rejects.

---

# Part E. Gray tensor of arbitrary objects (D7)

## E.1 Target universal property, including higher cells

Campion: (Cat_ω, ⊗) is biclosed, Map(B ⊗ C, D) ≃ Map(B, Fun^lax(C, D)) as **mapping spaces**. On mapping ω-categories it fails (GHL Rem. 2.20; `planar-pasting-types.md` §4).

The correct all-levels statement routes higher cells through the **pseudo cotensor** [⟦Dᵏ⟧, D] of `internal-hom.md` §5.4:

```
k-cells of Fun(B ⊗ C, D)  =  maps B ⊗ C → [⟦Dᵏ⟧, D]  ≃  maps B → [C, [⟦Dᵏ⟧, D]]_lax .
```

Only the space-level bijection is asserted. Higher cells come from instantiating D := [⟦Dᵏ⟧, D].

**The naive rule is unsound.** A rule asserting the bijection on cells of all dimensions would identify:
- 2-cells of Fun(B, [C, D]_lax): maps (B × D¹) ⊗ C → D, whose C–time mixed cells may be non-invertible;
- 2-cells of Fun(B ⊗ C, D): maps (B ⊗ C) × D¹ → D, whose C–time mixed cells are inverted. By Theorem (P), X × D¹ is X ⊗ D¹ with the mixed cells inverted.

At B = C = D¹ these are two different localizations of the cube D¹⊗D¹⊗D¹. The first inverts only the B–time faces; the second also the C–time faces. Asserting the bijection forces the lax C–time naturality cells to be invertible.

## E.2 Colimit-free rule for one representable factor

For arbitrary B and representable Θ, [⟦Θ⟧, D]_lax exists for every D, by rule (lhom) of `internal-hom.md` §5.1. So B ⊗ ⟦Θ⟧ can be given as a **representing object**:

```
(⊗Θ-form)  Γ ⊢ B : ⋆  ⟹  Γ ⊢ B ⊗ Θ : ⋆
(⊗Θ-unit)  Γ ⊢ u_B : B → [Θ, B ⊗ Θ]
(⊗Θ-fill)  Γ ⊢ h : B → [Θ, D]  ⟹  Γ ⊢ h♯ : B ⊗ Θ → D,   Γ ⊨ ε_h : [Θ, h♯] ∘ u_B ≅ h
(⊗Θ-uni)   Γ ⊢ g : B ⊗ Θ → D,  Γ ⊨ θ : [Θ, g] ∘ u_B ≅ h  ⟹  Γ ⊨ g ≅ h♯  (with the coherence cell over ε_h, θ)
```

All cells are invertible (written with ⊨). There are no definitional equations, and fillers are unique up to a contractible space. This is CaTT_lim's `uni` pattern, but only at the level of maps into an arbitrary D, per E.1. The higher-cell universal property is the instance D := [⟦Dᵏ⟧, D].

- **Soundness:** Campion's biclosedness, applied with the representable factor.
- **Consistency:** for B = ⟦Δ⟧, B ⊗ Θ and the Gray context ⟦Δ ⊗ Θ⟧ represent the same functor, so they are equivalent. The comparison is *derivable* (E.4, Prop. E2); no extra rule is needed.
- **Mirror:** ⟦Θ⟧ ⊗ C via the oplax hom, which is derivable by `internal-hom.md` §5.6.

**Status 2026-11-20.** This rule is now derived from the biclosed rules of F.7.4, with B ⊗ Θ the formula B ⊗ ⟦Θ⟧ (F.7.4 item 5). It is kept here as the representable case and as the source of E.4.

*Correction 2026-11-21 (ledger S13, `design-decisions.md` §4).* F.7.4 derives this rule with Θ a probe ⟦Θ⟧. Read with Θ a free object (as written above, through (lhom) of `internal-hom.md` §5.1), it is derived only under the proposed rule GB-shape. The consistency clause (B = ⟦Δ⟧) likewise holds within the probe sort.

**Payoff.** Lax transformations between arbitrary functors are maps B ⊗ D¹ → C. That is a cleaner presentation than the fibre definition LaxTr(F, G) of §5.2, and it composes by (⊗Θ-fill).

## E.4 Derived structure of the B ⊗ Θ rule (D7, adjacent)

*Added 2026-11-18.* Everything below is derived from (⊗Θ-form, unit, fill, uni) and the lhom rules of `internal-hom.md` §5.1. All cells are invertible and no definitional equation is added.

**Auxiliary maps.**
- [Θ, F] := Λ(F ∘ id♭) : [Θ, C] → [Θ, D], for F : C → D.
- [τ, C] := Λ(id♭ ∘ (Δ ⊗ τ)) : [Θ, C] → [Θ′, C], for τ : Θ′ → Θ (§5.1).
- From nat-C, β and η: [Θ, G ∘ F] ≅ [Θ, G] ∘ [Θ, F], [Θ, id] ≅ id, and [Θ, F] ∘ Λφ ≅ Λ(F ∘ φ).

**Prop. E1 (functoriality).**
- For F : B → B′, put F ⊗ Θ := (u_{B′} ∘ F)♯ : B ⊗ Θ → B′ ⊗ Θ.
- For τ : Θ′ → Θ, put B ⊗ τ := ([τ, B ⊗ Θ] ∘ u_B)♯ : B ⊗ Θ′ → B ⊗ Θ.
- These preserve composites and identities up to invertible cells, and the two variables interchange: (F ⊗ Θ) ∘ (B ⊗ τ) ≅ (B′ ⊗ τ) ∘ (F ⊗ Θ′).

*Proof.* Each pair of sides g, g′ has [Θ, g] ∘ u ≅ [Θ, g′] ∘ u, by ε, the auxiliary isomorphisms and naturality of u. Then (⊗Θ-uni), applied twice, gives g ≅ (…)♯ ≅ g′. ∎

**Prop. E2 (comparison with Gray contexts).** For B = ⟦Δ⟧, the maps

```
c := (u_B)♭ : ⟦Δ ⊗ Θ⟧ → ⟦Δ⟧ ⊗ Θ      (u_B read as a substitution Δ ⊳ [Θ, ⟦Δ⟧ ⊗ Θ])
d := (Λ id_{Δ⊗Θ})♯ : ⟦Δ⟧ ⊗ Θ → ⟦Δ ⊗ Θ⟧
```

are inverse equivalences.

*Proof.*
- **d ∘ c ≅ id.** We have Λ(d ∘ c) ≅ [Θ, d] ∘ Λ(c) by nat-C. Then [Θ, d] ∘ Λ(c) ≅ [Θ, d] ∘ u_B by η, and [Θ, d] ∘ u_B ≅ Λ id by ε. Applying ♭ and β gives d ∘ c ≅ id.
- **c ∘ d ≅ id.** We have [Θ, c ∘ d] ∘ u_B ≅ [Θ, c] ∘ Λ id. Then [Θ, c] ∘ Λ id ≅ Λ(c) by nat-C, and Λ(c) ≅ u_B by η. Also [Θ, id] ∘ u_B ≅ u_B. So (⊗Θ-uni) identifies both c ∘ d and id with (u_B)♯. ∎

**Prop. E3 (unit).** B ⊗ D⁰ ≃ B, because [D⁰, D] ≃ D by the D⁰ check of §5.1, and representing objects are unique up to equivalence.

**Lax transformations and their algebra.** Let a lax transformation from F to G : B → C be a map α : B ⊗ D¹ → C with cells α ∘ (B ⊗ 0) ≅ F and α ∘ (B ⊗ 1) ≅ G (via E3).
- *Agreement with §5.2.* By (fill) and (uni), these are equivalent, as a space, to maps B → [D¹, C] over (F, G), i.e. to points of LaxTr(F, G).
- *Whiskering.* Postwhiskering by H : C → C′ is H ∘ α. Prewhiskering by K : B′ → B is α ∘ (K ⊗ D¹).
- *Vertical composition.*
  1. [D¹ ∨ D¹, C] ≃ [D¹, C] ×_C [D¹, C], because cotensors turn the wedge (G3) into a pullback (§5.1). So a composable pair (α, β), together with its matching cell, is a map B → [D¹ ∨ D¹, C].
  2. Fill it to B ⊗ (D¹ ∨ D¹) → C.
  3. Precompose with B ⊗ κ, where κ : D¹ → D¹ ∨ D¹ is the composition coherence.

  Unit and associativity hold up to invertible cells, by E1 and the corresponding coherences in Θ.
- *Modifications.* These are maps B ⊗ D² → C. The same construction gives their vertical and horizontal composites through B ⊗ Θ for the relevant pasting shapes Θ.
- *This is the "Payoff" of E.2, made explicit.* The bicategory-level algebra of lax transformations between arbitrary functors comes from substitutions of representables, transported along B ⊗ –.

**What remains of the adjacent item.**
- Implementing (⊗Θ) in the type-checker belongs to whichever thread implements lhom (§5.1).
- On paper, the remaining question is the higher-cell version of E1–E3 at D := [⟦Dᵏ⟧, D]. It is formal once the pseudo cotensor of §5.4 is available, and that is the E.1 reading.

## E.3 What still blocks both factors arbitrary

B ⊗ C with C arbitrary needs [C, –]_lax for arbitrary C as an object. Two routes:
- an end over C's cells, [C, D]_lax ≃ lim_{⟦Θ⟧→C} [Θ, D], which is an object-indexed limit (F5) and connects to C9 (density);
- the PL-ω route (Part F): give ⊗ and [–, –]_lax together as type formers whose structure maps are coherences over Gray pasting types.

The colimit route of `internal-hom.md` §6 (B12) remains a third option. **Status:** partly done. The remainder is blocked on F5, or on D11's general criterion. The adjacent derived structure is done (E.4).

**Checked 2026-11-20.** Neither non-PL-ω route is proved for arbitrary objects. F5 supplies object-indexed colimits, not the limit the end formula needs, and the density step it would rest on (F5b) still lacks a realisation rule, with the universal shape family (F5c) only drafted. The colimit route has no proof that the colimit over cells of B and C has the Gray tensor's universal property. So the step that currently needs PL-ω is forming [C, –]_lax for arbitrary C as an object, with evaluation and currying as coherences; the researcher prompt `conjectures/outbox/gray-biclosed-coherence-r3.md` stays in the outbox for it.

**Update 2026-11-20 (later).** The prompt is answered (`conjectures/answered/gray-biclosed-coherence-r3-2026-11-20.md`, verified). Response 2 gives the PL-ω route in reading (II). The type formers are ⊗, \ and /. The distinguished coherences are pairing, the left and right evaluations, and, at decidable generic sequents, currying c with its comparison ε. The free data model is initial over the lax-grid model. So [C, –]_lax = C\– (and –/C for the oplax side) exists for arbitrary C, and B ⊗ C for two arbitrary factors follows. **Status: done (2026-11-20).** The templates are written into the kernel in **F.7.4**, and E.2/E.4 and (lhom) are derived from them (F.7.4 item 5). What remains is the in-house Lemma GB-ext (D7c, independent check requested) and the Agda module (D7d).

---

# Part F. PL-ω: a candidate criterion that passes the first test (D11)

## F.1 The test, made precise

Work over a signature Σ of generating 1-cells fᵢ : Pᵢ → Qᵢ between formulas, each used exactly once. A 1-term over Σ is a planar multimorphism Γ → C built from:
- structural maps, which are coh's of planar pasting sequents (Part A);
- the generators.

It determines an **event order** σ(t), the order in which the generators are applied. Between consecutive events the structural part is contractible (Theorem A).

Two events are **independent** if neither's output feeds the other's input. Planarity gives independent events a well-defined left/right position (disjoint wire intervals).

**First test:** Σ = {φ : P → C/B, b : X → B}, Γ = P, X, goal C. The two 1-terms are

```
t₁ = ev ∘ (φ ⊗ B) ∘ (P ⊗ b)      b first, then φ
t₂ = ev ∘ (C/B ⊗ b) ∘ (φ ⊗ X)    φ first, then b
```

The lax naturality cell of evaluation at (φ, b) is t₁ ⇒ t₂. This is the orientation of `pseudo-vs-gray.md` §3.4, where ∂⁻(α⊗β) is "right factor first". The test asks for a criterion that yields t₁ ⇒ t₂ and not t₂ ⇒ t₁.

## F.2 Mimram's Dir fails it

By C.2, Dir accepts both t₁ → t₂ and t₂ → t₁. Both are terms of the same 1-pasting type in a context with no 2-dimensional hypotheses.

## F.3 Candidate: the Gray criterion

For a 1-term t, let inv(t) be the set of independent pairs (e, e′) with e left of e′ and e′ before e in σ(t).

**Gray criterion (2-dimensional).** A 2-goal t ⇒ u over a context of objects and 1-cells is a coherence iff:
- t and u are 1-terms of the same planar pasting 1-type (Part A); and
- inv(u) ⊆ inv(t).

**Properties.**
- **Passes the test.** inv(t₁) = {(φ, b)} and inv(t₂) = ∅, so t₁ ⇒ t₂ is accepted and t₂ ⇒ t₁ is not.
- **No inverses of interchangers.** If both t ⇒ u and u ⇒ t are accepted, then inv(t) = inv(u). Together with the dependency order this fixes every pair, so σ(t) = σ(u). The two terms then differ only in contractible structural parts, and the cell between them is an invertible coherence, as in CaTT's coherence case.
- **Every accepted cell is a composite of oriented interchangers and structural coherences.**
  - The event orders are the linear extensions of the dependency order. Together with the left/right order of independent events, that order is a 2-dimensional poset.
  - Its linear extensions form an interval of the weak Bruhat order, and inversion-set containment is reachability by oriented adjacent swaps (Björner–Wachs, *Permutation statistics and linear extensions of posets*, JCTA 1991, two-dimensional case) **[recall: theorem number]**.
- **Relation to L.** With every generator in its own tensor position, inv-containment is exactly the support condition of two-tier L on the cube U = D¹ ⊗ … ⊗ D¹. The Gray criterion is L's side condition, read on the event structure of a planar closed term.
- **Gepner–Heine.** A 2-cell accepted by the criterion records which side of each independent pair moved first. That is a "left versus right placement of time" in the sense of LMor/RMor ([2510.10504](https://arxiv.org/abs/2510.10504), Cor. 4.1.11). The inversion set is the 1-dimensional shadow of that placement.

## F.4 What is open

1. **Event order for terms that cross curried boundaries.** The left/right position of events inside an argument of a residual needs a definition. A candidate is the planar proof net with generator boxes. The test case does not need it.
2. **The ω-version.** The conjecture is that k-cells between event orders are the cells of the hom ω-category of ν(D¹ ⊗ … ⊗ D¹) between its bottom and top vertices. In the fully independent case these are the higher Bruhat orders (Manin–Schechtman; Kapranov–Voevodsky) **[recall]**.
3. **Full soundness and completeness** against the free Gray-monoidal biclosed (∞,ω)-category.

These are recorded in `conjectures/planar-pasting-types.md` §4, which is ready for a researcher.

## F.5 Internal progress on D11 (outbox Question 1, monoidal fragment)

*Added 2026-11-18.*

**Prop. F1 (Gray monoids).** Let 𝒢₀ be the free strict Gray monoid on a set of objects and a set of generating 1-cells. This is a monoid in (2-Cat, ⊗_Gray) with lax interchange and no closed structure. Let t, u be 1-cells of 𝒢₀ with the same source and target and the **same image in the free strict monoidal category**, i.e. the same string diagram. Then:
- there is a 2-cell t ⇒ u iff inv(u) ⊆ inv(t); and
- that 2-cell is unique.

So each hom-category is a poset: a disjoint union of weak-Bruhat-order intervals, one per string diagram.

*Correction (independent review, `reviews/closed-structure-F5-2026-11-18.md`).* The first version assumed only "the same events", which is too weak. For f, g : A → A, the 1-cells f;g and g;f have the same events and inv = ∅, but no 2-cell relates them. In planar form, compare f on the left then g on the right with g on the left then f on the right, on A⊗A. Interchangers preserve the string diagram, so the diagram must be fixed.

*Proof.*
1. **Generators.** 2-cells of 𝒢₀ are composites of whiskered interchangers X_{f,g} for *generating* f, g. An interchanger at composite 1-cells decomposes by the Gray-monoid axioms X_{f, g′∘g} = (X_{f,g′} ∗ g)·(g′ ∗ X_{f,g}) and X_{f, B⊗g} = X_{f⊗B, g} for an object B between f and g, and symmetrically in f. Compare Forest–Mimram's presentation of free Gray categories (FSCD 2018), here without inverses. **[recall: the directed presentation is the same generators and relations, minus the inverse generators]**
2. **Each generator removes one inversion.** A whiskered X_{f,g} swaps two events that are consecutive in time and independent, from "right factor first" to "left factor first". It deletes exactly the pair (f, g) from the inversion set and changes no other pair. So t ⇒ u implies inv(u) ⊆ inv(t). Every 2-path has length |inv(t)| − |inv(u)|.
3. **Existence.** Over a fixed string diagram, the event orders of the 1-cells are the linear extensions of the dependency order. Adding left/right for independent pairs makes it a 2-dimensional poset. Its realizer is the pair of linear orders "precedence, then left first" and "precedence, then right first" (the planar st-graph / dominance fact, **[recall]**). Its linear extensions form an interval of the weak order (Björner–Wachs 1991, Thm 6.8 = Chatel–Pilaud–Pons arXiv 1701.07995, Prop. 26). In the weak order, inv(u) ⊆ inv(t) iff u ≤ t, and then there is a saturated chain of adjacent swaps between them. That chain stays in the interval, so every step is an interchanger.
4. **Uniqueness.**
   - A 2-path from t to u is a maximal chain of [u, t], i.e. a reduced word of the permutation u⁻¹t.
   - By Matsumoto–Tits, any two reduced words are connected by commutation moves s_i s_j = s_j s_i (|i − j| ≥ 2) and braid moves s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}. Each intermediate word is again a chain of [u, t], so it is again a 2-path of 𝒢₀.
   - Commutation moves are the interchange law of the underlying 2-category: the two swaps act on disjoint time slots.
   - Braid moves involve three pairwise independent events. Their two hexagon composites are equal in a Gray monoid, by naturality of X_{f,–} with respect to X_{g,h} together with the decomposition axioms; equivalently, D¹ ⊗ D¹ ⊗ D¹ is a commuting cube in Gray's 2-categorical tensor. In the ω-version this equality becomes the 3-cell of Question 3.
   - Hence any two 2-paths are equal. ∎

**Researcher response (verified, `conjectures/answered/gray-pasting-types-2026-11-18.md`).**
- It proves the corrected Prop. F1 for *any* labeling, using only squares and hexagons and no interval lemma.
- The hom ω-category of ν(I^⊗n) is **not thin**. Two hexagon 2-cells are joined by the 3-cell ***.
- Gray's 2-tensor is its intelligent 2-truncation (Ara–Maltsiniotis A.25, A.31), which is why F1's uniqueness holds.
- The dependent version is νK_P, built from the faces (order ideal J, S ⊆ min(P∖J)). Its truncated hom is the scheduling category S(P).

The researcher findings on the closed part are listed after the next two bullets.

**What the closed structure adds (remaining for Question 1; superseded in part by the findings below).**
- *1-cells.* The underlying 1-category of a Gray-monoidal biclosed 2-category is premonoidal and biclosed. Structural maps are central. Needed: two 1-cells with the same event order and generators are equal. This is a premonoidal version of Theorem A, and should follow by rerunning A.2 with events as non-central generators.
- *2-paths through closures.* A 2-path from t to u may pass through 1-cells with events inside closures, even when t and u have none. Strict naturality of Λ (Λ(f) ∘ h = Λ(f ∘ (X ⊗ h))) and the hom-isomorphism ev ∘ (Λs ⊗ B) = s should push every such intermediate event back out. That reduces the general 2-path to the Prop. F1 situation. This is the content of the nested event order (outbox Question 2).
- Status: Prop. F1 settles the monoidal core.

**Corrections from the response (V3, V5), which restate the two bullets above.**
1. **Pushing events inward is not invariant.** We have h = Λ(ev) ∘ h = Λ(ev ∘ (1 ⊗ h)), and β also changes nesting. So the second bullet needs a *βη-canonical* nesting first, i.e. a specified normal form for closures.
2. **The closed signature must be strictly natural only in the context variable.** Strict naturality of Φ : 𝒢(A⊗B, C) ≅ 𝒢(B, A\C) in the bound variable A forces (f⊗B′)(A⊗g) = (A′⊗g)(f⊗B). Then the two schedules are equal 1-cells. In the bound variable, naturality holds only up to the interchanger.
3. **What remains** is a comparison theorem: for the biclosed Gray structure with signature 2, and 1-cells in βη-canonical nested form, the hom-categories should be products (over nesting levels) of the S(P)'s. Prompt: `conjectures/answered/gray-closed-scheduling-2026-11-18.md`.

**Answer to the follow-up prompt (verified, `conjectures/answered/gray-closed-scheduling-2026-11-18.md`): the comparison theorem cannot be indexed by βη-canonical closure trees.**
- Closure trees are **not** invariants of connected components of hom-categories.
- *Counterexample.* Take a : X → A, f : A⊗B → C and c = Λ_A f. The interchanger gives

  ```
  θ : e ∘ (a⊗U) ∘ (X⊗c)  ⇒  e ∘ (A⊗c) ∘ (a⊗B),
  ```

  and the target is f ∘ (a⊗B) by β.
- In every representative of the source, a generator sits under currying. A Boolean biclosed poset model rules out the structural prefix that would avoid this. So a single 2-cell connects 1-cells with different canonical closure trees.
- A word model gives an invariant W of 1-cells. It separates the first test's two 1-cells: W(t₁) = bφ ≠ φb = W(t₂).

**Still open (D11):**
- the singleton/empty question for the first test;
- a product theorem restricted to an appropriate invariant;
- the correct component invariant (W is a candidate);
- the ω-version. Mapping-space biclosedness is too weak there (GHL Rem. 2.20).

Round-2 prompt answered: `conjectures/answered/gray-closed-scheduling-r2-2026-11-18.md` (verified); round 3 was answered too (`conjectures/answered/gray-closed-scheduling-r3-2026-11-18.md`); round 4 was answered too (`conjectures/answered/gray-closed-scheduling-r4-2026-11-18.md`); round 5 is `conjectures/outbox/gray-closed-scheduling-r5.md` (unsent).

**Round-2 results (verified).**
1. **A weight model.** The integer-weight model 𝓜 is a Gray-monoidal biclosed 2-category.
   - Objects are the integers. Hom-categories are (ℤ, ≤) when the target is at least the source.
   - The weight rules are: w(p⊗u) = w(u) + p·δ(u); left currying subtracts p·δ; an interchanger adds δ(f)·δ(g).
2. **The first test (Q1).** Both reverse homs are empty. The weights are 0 and 1 for t₁ and t₂, and −1 and 0 for the variant s, t. Every forward 2-cell uses exactly one interchange of the two generators.
3. **Undirected components.** The undirected components of the hom-categories are exactly the arrows of the free ordinary biclosed monoidal category, via π₀ and freeness.
4. **The component plus W does not classify 1-cells.**
   - Take f : A → B, g : B → C and paddings L, R, and put m = L⊗gf⊗R.
   - Currying g on the right gives a 2-cell u ⇒ m, and currying on the left gives m ⇒ v. The weights are −1, 0 and 1.
   - So the side on which a generator is curried is data of the 1-cell.

**Still open (D11):**
- forward uniqueness, i.e. coherence of interchangers with a generator-free argument;
- the 1-cells within a component;
- thinness of the hom-categories.

Round 3 (answered): `conjectures/answered/gray-closed-scheduling-r3-2026-11-18.md`; round 4 (answered): `conjectures/answered/gray-closed-scheduling-r4-2026-11-18.md`; round 5 (unsent): `conjectures/outbox/gray-closed-scheduling-r5.md`.

## F.6 Internal notes toward round 3 (D11, closed part)

*Added 2026-11-18.*

**1. Additive models with group-subtraction residuals cannot see generator-free interchangers.** *(Scope narrowed 2026-11-18; see item 4.)*
- Call a model *additive* if 1-cells carry a weight in an ordered abelian group, δ(u) = target − source is additive, and an interchanger adds a bilinear term β(δ(f), δ(g)). The integer model 𝓜 and its matrix version are additive.
- Every structural 1-cell has δ = 0 *when the residual is group subtraction* (p\r = r − p, as in 𝓜), because it is a coh of a balanced sequent. Item 4 drops this assumption, and the conclusion fails.
- So in every additive model, an interchanger χ_{f,g} in which f or g is structural (ev, curried evaluation, associators) has weight 0, and lands in a hom where it is forced to be an identity once the hom is a poset.
- **Consequence for round-3 Q1:** the reduction "only generator-free interchangers remain" cannot be finished with models of this kind. It needs a rewriting or coherence argument, or a model like 𝓟 of item 4.

**2. Structural interchangers are not forced trivial by the stated axioms.**
- Take ev : A⊗(A\C) → C and a generator g : Y → Y′. Compare (ev⊗Y′)∘(A⊗(A\C)⊗g) with (C⊗g)∘(ev⊗Y).
- Apply Φ, currying A on the left, using its strict naturality in the context variable and in the target. The question becomes whether m_{Y′}∘((A\C)⊗g) = (A\C⊗g)∘m_Y, for m_Y := Φ(ev⊗Y).
- That is again an instance of the same question, so Φ only transports it.
- So χ_{ev,g} is a 2-cell between 1-cells that the axioms do not identify. The same holds for χ_{ev,ev′} between two evaluations at independent positions. Structural maps are therefore *non-central events* in 𝒢 unless centrality is imposed, as in Garner–Hirschowitz–Pardon's premonoidal construction.
- **Consequence for round-3 Q2:** a complete invariant of 1-cells will have to schedule structural events as well as generator events. Round 2's item 8 (the curry side is data) is the simplest instance.

**3. A design choice this exposes.** There are two candidate theories for the project's PL-ω:
- (a) the free Gray-monoidal biclosed 2-category 𝒢 as posed, where structural maps are non-central;
- (b) its quotient in which structural 1-cells are central, i.e. every interchanger with a structural argument is an identity.

In (b), the reduction of round-3 Q1 to item 6 of round 2 is immediate: every forward 2-cell between t₁ and t₂ is a single generator interchanger, so 𝒢_b(t₁, t₂) = {α}. Whether (b) is still sound for the Gray tensor of (∞,ω)-categories, i.e. whether ev is central there, is the real question. Campion's biclosedness is only on mapping spaces (GHL Rem. 2.20), which suggests it is not. This is recorded for the round-3 answer to settle.

**4. Evaluation is not central in 𝒢 (proved).** *(Added 2026-11-18.)*

*The polarized model 𝓟.* It is a strict 2-category with codiscrete homs, so every 2-cell equation holds automatically and only the 1-cell structure needs checking.
- **Objects:** pairs (P, N) ∈ ℤ².
- **Tensor and residuals:** A ⊗ B = A + B, and A\C = C/A = C + swap(A), where swap(P, N) = (N, P). So the residual swaps polarity instead of subtracting, unlike 𝓜.
- **1-cells:** a 1-cell X → Y exists iff (P − N)(X) = (P − N)(Y), and is then an integer weight w. Composition adds weights.
- **Grading:** put d(u) = P(source) − P(target).
- **Whiskering:** w(A ⊗ u) = w(u) + P(A)·d(u) and w(u ⊗ B) = w(u).
- **Currying:** left currying is Φ_A(u) = w(u) − P(A)·d(u), and right currying leaves the weight unchanged.

*It is a model of the setting of r3.*
- A⊗– is a functor, ⊗ is strictly associative, and (A⊗v)⊗B = A⊗(v⊗B).
- Φ is a bijection, strictly natural in the context variable and in the target. Naturality in A holds up to the (codiscrete) interchanger.
- The interchanger exists because the homs are codiscrete. It is an identity only when the weights agree, and w(A′⊗g)(f⊗B) − w(f⊗B′)(A⊗g) = (P(A′) − P(A))·d(g) = −d(f)·d(g).
- `scripts/d11/polar_model.py` checks these laws on 20,000 random instances, with no failures.

*Consequence.* Here ev_A = Φ⁻¹(id) has d(ev_A) = P(A) + N(A), which is not 0 in general. Take atoms with A ↦ (1, 0), C ↦ (0, 0), X ↦ (1, 1) and X′ ↦ (0, 0), and a generator g : X → X′. Then the 1-cells (X′ ⊗ ev) ∘ (g ⊗ A ⊗ A\C) and (g ⊗ C) ∘ (X ⊗ ev) have weights 1 and 2. So they are **distinct 1-cells of the free 𝒢**, and χ_{g,ev} is not an identity. The same computation separates the two orders of two evaluations at independent positions, χ_{ev,ev′}, which involves no generator at all.

So:
- **Round-3 Q5, first half: answered, no.** Evaluation is not central in 𝒢, and the quotient 𝒢_c of item 3(b) is a proper quotient.
- **Q1:** structural interchangers really are events between distinct 1-cells. The open part is that any two 2-cells between the same 1-cells built from them are equal, which is a coherence statement and not a triviality.
- **Q2:** confirmed. A complete invariant must schedule structural events too.
- **Item 3's design choice:** it is now a real choice between two different theories. The (∞,ω) half of Q5 still decides which theory matches the Gray tensor.

**5. The r4 obstruction.** *(Added 2026-11-18, after the verified r4 answer, `conjectures/answered/gray-closed-scheduling-r4-2026-11-18.md`.)*
- Take strict ω-categories with the Gray tensor and one orientation of transformations, and let S = J ⊗ J.
- S/J has an arrow v₀ → v₁, but J\S has none, since that arrow would need the reverse of the square γ.
- So in ωCat itself, left closure matches lax transformations and right closure matches oplax ones. The two Φ's are not both isomorphisms of hom-categories of one 2-category with one orientation.

What this means for 𝒢, and the corrected rule set, are in **F.7**. A first version of this item proposed taking Φ_R into the 2-cell-reversed hom 𝒢(B, C/A)^co. **That proposal is withdrawn.** Oplax transformations are maps D¹ ⊗ X → Y, not reversed lax ones (X ⊗ D¹ → Y), so reversing 2-cells does not turn one kind into the other.

*Correction.* r3 known item 11's last bullet said that separation needs non-commuting curryings. That is false. r4's model 𝒟 has strictly equal mixed curryings and still separates H, and left closure alone separates H_L.

## F.7 Orientation of the closed structure: audit and corrected rules (D17)

*Added 2026-11-18.* This section is prompted by r4 §5 (F.6 item 5).

### F.7.1 Two readings of "monoidal biclosed with the Gray tensor"

**(I) Internal.** M is a monoid in (Cat_ω, ⊗_Gray), i.e. a Gray monoid, and its objects are formulas.
- M ⊗ M → M is a functor, so both A ⊗ – and – ⊗ A are ω-functors M → M.
- Biclosed means both have right adjoints as ω-functors. The adjunctions then give isomorphisms of hom ω-categories on *both* sides: M(A⊗B, C) ≅ M(B, A\C) and M(B⊗A, C) ≅ M(B, C/A).
- Interchangers χ_{f,g} of 1-cells are genuine non-identity 2-cells of M.
- This is the structure 𝒢 of F.5 and F.6 and of the r1–r4 prompts, and **its axioms are correct for this reading**.
- r4 §5 shows that ωCat itself, with lax 2-cells, is *not* an instance: there, – ⊗ A is not a 2-functor on lax cells, since it sends X ⊗ D¹ to X ⊗ D¹ ⊗ A.

**(II) Ambient.** This is the project's two-tier L ambient ∞Cat_lax (`conventions.md` §3–4). Objects are ω-categories, 1-cells are functors, and the hom-objects are Fun^lax. The ambient is Gray-gauche enriched.
- ⊗ of functors is strictly functorial in both variables, so 1-cell interchangers are identities (r4 Q5).
- Closure is one-sided at each orientation (`conventions.md` §4, AM):
  ```
  Hom(A⊗B, C) ≅ Hom(B, Hom_lax(A, C)) ≅ Hom(A, Hom_oplax(B, C)).
  ```
  Left currying is an isomorphism of *lax*-cell homs, and right currying of *oplax*-cell homs.
- The Gray content (schedules) lives inside the hom-objects, not in 1-cell interchange.

**The defect.** Several notes say "monoidal biclosed (∞,ω)-category with the Gray tensor" without choosing a reading. They then use (I)'s symmetric hom-isomorphisms while motivating the work by (II)'s type formers.

### F.7.2 Audit

| Item | Uses | Affected? |
|---|---|---|
| PL1 / D9 (Theorem A, A4, UL⊗) | 1-categorical biclosed monoidal category | **No.** Both readings have the same underlying biclosed 1-category; (II)'s hom-*sets* are isomorphic on both sides. |
| D10 (Theorems B, B6, B8, UL_I\*) | same, with unit | **No**, for the same reason. |
| D12 (cartesian closed, Rev/Dir) | symmetric cartesian product, pseudo cells | **No.** No Gray tensor is involved. |
| `conventions.md`, `internal-hom.md` §5, E.2/E.4 (B ⊗ Θ rule, mirror via the oplax hom) | reading (II), one orientation per side | **No.** Already one-sided and correct; these are the reference for the fix. |
| `planar-pasting-types.md` §4 obstruction | mapping spaces | **No**, at mapping-space level. |
| `planar-pasting-types.md` §4 Question PL-ω, §4.1, F.1–F.4 (Gray criterion, first test) | "free monoidal biclosed (∞,ω)-category"; t₁ ⇒ t₂ as a 1-cell interchanger | **Wording.** The test's cell is a 1-cell interchanger, so it is reading (I). In (II) the analogous t₁ and t₂ are equal functors, and the cell appears one level up, in Fun^lax. PL-ω must name its reading. |
| F.5–F.6, the r1–r4 prompts and answers (𝒢) | reading (I) | **No** for (I). These results are about (I). They do **not** transfer to (II) without the rules below. |
| E.3 (D7, both factors arbitrary via PL-ω) | wants (II)'s type formers | **Yes.** It needs the reading-(II) rule set below, not 𝒢. |

### F.7.3 Corrected rule set for reading (II): "Gray-gauche biclosed"

This is a draft. The data:
- **Underlying 1-category.** Objects and 1-cells, with ⊗ strictly associative and strictly functorial in both variables. There are no 1-cell interchangers.
- **Two families of 2-cells on the same 1-cells:**
  - lax cells 𝒢^λ(X, Y), the transformations X ⊗ D¹ → Y;
  - oplax cells 𝒢^ο(X, Y), the transformations D¹ ⊗ X → Y.

  Each family forms a 2-category with these 1-cells. Pseudo cells, those invertible in both, embed in both families.
- **Whiskering by tensoring:**
  - A ⊗ – : 𝒢^λ → 𝒢^λ is a 2-functor, but not on 𝒢^ο;
  - – ⊗ B : 𝒢^ο → 𝒢^ο is a 2-functor, but not on 𝒢^λ;
  - tensoring a lax cell on the right, or an oplax cell on the left, gives a *mixed-shape* cell, which is not a cell of either family. Its type is the Gray cylinder of `gray-cylinders.md`.
- **Left closure:** Φ_L : 𝒢^λ(A⊗B, C) ≅ 𝒢^λ(B, A\C), with A\C = Hom_lax(A, C) in AM's naming.
- **Right closure:** Φ_R : 𝒢^ο(B⊗A, C) ≅ 𝒢^ο(B, C/A), with C/A = Hom_oplax(A, C).
- **Naturality:** both are strictly natural in every variable at the level of 1-cells. There are no interchangers to be lax about.
- **Higher cells:** the lax and oplax cells at dimension k are maps X ⊗ Dᵏ → Y and Dᵏ ⊗ X → Y. Higher cells of mixed shape are the hom-objects of `internal-hom.md` §5, with the lax/oplax duality §5.6 relating the two sides.

**Refinement from the verified round-5 answer** (`conjectures/answered/gray-closed-scheduling-r5-2026-11-18.md`, 2026-11-18). That answer confirms reading (II) and states it more sharply.
- **The full structure is two-sided.** For each pair of objects there is the family ℍ(A, C)(P, Q) = Hom(P ⊗ A ⊗ Q, C), with probes P and Q. This is Gepner–Heine's bienrichment (§1.5, Ex. 3.2.6).
- **The two cell families are its one-sided restrictions.**
  - ℍ_r(A, C) has Q = Dᵏ and P = I, i.e. cells A ⊗ Dᵏ → C. These are the "lax cells" 𝒢^λ above.
  - ℍ_ℓ(A, C) has P = Dᵏ and Q = I, i.e. cells Dᵏ ⊗ A → C. These are the "oplax cells" 𝒢^ο.
  - The answer names them by parameter position to avoid the lax/oplax naming conventions; this note follows it.
  - Cells with both probes non-trivial form the **double hom**: lax and oplax arrows meeting in squares. These are the mixed-shape cells listed above.
- **Currying laws** (r5 eqs. (3), (4)). These agree with Φ_L and Φ_R above:

  ```
  ℍ_r(A⊗B, C) ≅ ℍ_r(B, A\C),        ℍ_ℓ(A⊗B, C) ≅ ℍ_ℓ(A, C/B).
  ```

- **Probe absorption** (r5 eq. (5)). With both probes present, a probe next to a curried variable is absorbed into the residual:

  ```
  Hom(P⊗A⊗B⊗Q, C)  ≅  Hom(B⊗Q, (P⊗A)\C)  ≅  Hom(P⊗A, C/(B⊗Q)).
  ```

  So currying on the "wrong" side is still an isomorphism, but it moves the probe into the residual's argument and does not preserve the probe position. This is the rule for every mixed currying. The rule set includes it as a third clause next to Φ_L and Φ_R.
- **What survives of reading (I)'s phenomena.** In 𝒢′ the round-5 answer proves H = H_L = 1_T. Non-invertible Gray interchange survives, as a modification between schedules of transformations rather than of functors. See "Interchange moves into the homs" below, as corrected by round 6.

**Check of E.2 against these rules (D17 (b), done).**
- E.2 represents B ⊗ Θ by maps B → [Θ, D], with [Θ, D] = Hom_oplax(Θ, D) = D/Θ in AM's naming (`conventions.md` §4). That is right currying of Θ.
- Its higher-cell clause, "the instance D := [Dᵏ, D]", reads Hom(B⊗Θ⊗Dᵏ, D) ≅ Hom(B, D/(Θ⊗Dᵏ)). This is exactly probe absorption with P = I and Q = Dᵏ.
- It is **not** the false one-sided claim ℍ_r(B⊗Θ, D) ≅ ℍ_r(B, D/Θ), and E.2 never states that claim.
- Its "Payoff", lax transformations as B ⊗ D¹ → C, is ℍ_r(B, C) at k = 1.
- The mirror, ⟦Θ⟧ ⊗ C via the oplax hom, is the same check with the sides exchanged.

So E.2 and E.4 are instances of the corrected rule set with one representable factor, and no change is needed.

**Consequences.**
- **Pasting types for (II).** A pasting type for reading (II) must record, for each cell, which side its time direction sits on: X ⊗ Dᵏ versus Dᵏ ⊗ X. This is the "time as a tensor position" of PL-ω, now with a side.
- **Interchange moves into the homs, but not as schedule posets.** *(Corrected 2026-11-18 after the verified round-6 answer, `conjectures/answered/gray-closed-scheduling-r6-2026-11-18.md`.)*
  - For fixed Gray contexts Δ, the cells of Fun^lax(Δ, –) between the extreme vertices of ν(I^⊗n) are still F.5's schedule categories. That part of F.5 transfers.
  - The claim that *transformation-level* homs of 𝒢′ are schedule categories S(P) is **refuted**. Round 6 gives two endo-transformations α and β of 1_A with forward crossings in both directions, and their composite q embeds (ℕ, +) into End(α·β). So these homs are not posets.
  - Round 6 also shows that a non-invertible crossing can be built from structural maps alone.
  - **Round 7** (verified, `conjectures/answered/gray-closed-scheduling-r7-2026-11-18.md`) shows what replaces schedules: crossings of generating endo-transformations of 1_A satisfy exactly the **positive braid relations**.
    - A model with hom Br⁺_S retracts the map F : Br⁺_S → modifications. So End(τⁿ) contains the positive braid monoid B⁺ₙ.
    - No modification changes a word's multiset of letters.
    - Open (r8): whether F is full, i.e. whether End(α·β) ≅ ℕ, and how the choice of probe stock affects this.
  - **2026-11-19** (verified, `conjectures/answered/gray-biclosed-coherence-2026-11-19.md`):
    - The positive-braid description is **not** complete. Generators of probe degree ≥ 2 in the data source (α : J ▷ (J ▷ X) → Y) act as state changes of one event, giving modifications with no braid counterpart. The replacement is a free strict monoidal category with non-invertible braiding, **coupons** (modifications between words of different lengths) and per-event **state categories** K = ⊔(τ₁P_i)^op: End₂(f) ≅ Mon(K), End₂(1_A) ≅ Br⁺(K). Equality is decidable for uniform families and for positive braids with proper coupons (length invariant L(D)). For the endotransformation signature without residuals, the hom is exactly B Br⁺_S (so F is full there).
    - **1-cells of 𝒢 (reading I) have a decidable normal form**: N (context naturality), β, η form a terminating, confluent rewriting system. π ∘ ι = 1 is an instance of the cancellation T_a κ_a(h) ; e_a = h; ι ∘ π and forward uniqueness (2-cells of 𝒢) stay open.
    - The position-rigidity test (distinct endpoints, no endo-transformation generators) does **not** give a product of schedule categories.
    - **Constraint on any PL-ω rule (Q4 no-go):** an endpoint-symmetric coherence rule produces a reverse of the Gray square, and a boundary-lifting rule cannot be exact on Gray cubes if its arities identify the two boundary pastings of some cube (e.g. braid-relation quotients). So the rule must be asymmetric and keep those pastings distinct, as L's two-case rule and the support-based `dcoh_S` rule do.
    - Open: 𝒢′ for arbitrary residual arities, 2-cells of 𝒢, the directed rule in every dimension (`conjectures/answered/gray-biclosed-coherence-r2-2026-11-19.md`).
    - **Internal attempt on ι ∘ π = 1_H (2026-11-19, D11, r2 Q2).** No decision yet. Three facts about the question, all proved:
      1. *Reduction through left currying.* In item 11, u = A ⊗ η with η = Λ_A(1_{A⊗B}) : B → U, and e = ev ⊗ 1. The Gray axiom χ_{A⊗f,g} = A ⊗ χ_{f,g} gives ι = (ev ⊗ Y) ∗ (A ⊗ θ_ι) and π = (ev ⊗ Y) ∗ (A ⊗ θ_π). Here θ_ι = χ_{η,d} ∗ (B ⊗ v) and θ_π = (U ⊗ d) ∗ χ_{η,v} are 2-cells between K′ = (U ⊗ d)(η ⊗ Y′)(B ⊗ v) and η ⊗ Y. Φ_A is a bijection on 2-cells and strictly natural in the context variable. So **E = ι ∘ π is 1_H iff m ∗ (θ_ι ∘ θ_π) = 1, where m = Φ_A(ev ⊗ Y) : U ⊗ Y → A\(A ⊗ B ⊗ Y)**. The left retraction (e, u) disappears: what remains is one structural event η crossing the right retraction (v, d) twice, whiskered by the strength map m. The mirror reduction through right currying is blocked, because χ_{η, ev^R} is not of the form θ ⊗ D.
      2. *Eckmann–Hilton constraint.* In any model where H is sent to the identity 1-cell of T, ι and π become endo-2-cells of an identity 1-cell. Those commute, so E ↦ ι ∘ π = π ∘ ι = 1. Every existing model sends H to 1 or has thin or codiscrete homs: 𝓜, 𝓟, the free-group model, 𝒟, and every strict-monoidal model with identity interchangers. **So none of them can decide the question.** A countermodel needs three things together: H ≠ 1_T as a 1-cell (as in the free-group model), hom-categories with a proper split idempotent (π ∘ ι = 1 ≠ ι ∘ π), and non-invertible structural retractions (item 15).
      3. *Ruled-out families.* Twisted graded models fail. These are strict monoidal categories with objects ℤ and morphisms the elements of a ℤ-graded monoid, where x ⊗ y twists y by σ^{|x|}. So do endofunctor models [C, C] with c an autoequivalence. In both, the interchange law turns the right inverse of a retraction p : c → I into a left inverse as well, so ι ∘ π = 1. A countermodel's split idempotent must therefore sit on a non-invertible object of the hom-category, or use non-shift-invariant tensoring.
      The question stays in r2 Q2 (outbox) and under D11.
    - **Mechanical checks (2026-11-19, in-house, standard 9).**
      - `scripts/d11/nbe_rewrite.py` implements the N/β/η system on typed context-decorated words, with left and right tags and curry bodies. It builds 3,000 random terms from generator seeds by random N-, β- and η-expansions, including inside curry bodies; terms have up to 27 nodes, and 1,326 of them contain at least two redexes.
      - Every expansion and every reduction step type-checks. Every step preserves the weight in the polarized model 𝓟 of F.6 item 4, so the rules are sound in a non-trivial model.
      - Every term has a single normal form: 2,816 terms were checked exhaustively over all reduction orders, and the rest by 8 random strategies each. That normal form equals the seed's.
      - No reduction sequence exceeds C(n,2)+⌊n/2⌋ steps.
      - Control: with rule N disabled, the confluence check fails.
      - `scripts/d11/coupon_invariant.py` runs random walks with the defining equations of positive braids with proper coupons: disjoint interchange, Yang–Baxter, and both coupon naturalities in both directions. That is 2,000 diagrams × 200 steps, including 58,833 naturality steps that change length. L(D) and the labelled coupon data are invariant, the flow law (5) holds, and #crossings ≤ L(D) always. Controls: the plain crossing count changes, and weights r(e)+r(f) in place of r(e)r(f) are not invariant.
      - **Agda proof (D18).** `src/CaTTExp/Gray/NBE/` proves termination (`Termination.sn`) and confluence (`Confluence.confluence`, by local confluence and Newman's lemma) of the N/β/η system. The syntax is untyped and has no X annotation on curries, and it is parametric in formula factors and generator labels. The termination measure is (n, Σ_nodes (n − depth)), lexicographic. N pushes a subtree one level deeper, and β and η delete two nodes. Local confluence follows the seven-row table above, plus the variable cases (a step inside η's body is either a step inside g, or row 7) and the disjoint cases. It uses only list cancellation and associativity, so no typing is needed. `Decide` gives the decision procedure, given decidable equality of factors and labels: normal forms, Church–Rosser for the generated conversion, and `decide`. Its N carries no nonemptiness guard, matching the paper rule. The checker's `nonempty Xn` holds automatically on typed words, so typed steps are exactly the untyped steps between typed words. `Typing` gives a relational typing (generators with sources and targets, e_{a,Z} : T_a(H_a Z) → Z, κ_a(f) : X → H_a Z with X ≠ ∅) and proves subject reduction (`sr`). So every reduction from a typed word stays typed, and confluence and decidability restrict to typed words (`typed-confluence`). D18 is closed.
- **What to keep from F.5–F.6.** Those results are about (I) and keep their value there. The project's own type theory (two-tier L, D7/E.3) needs (II).

**Open (D17).**
- (a) ~~Fix PL-ω's reading in `planar-pasting-types.md` §4~~ done: §4 now names both readings. F.1–F.4 are reading (I). The project's use of PL-ω is the type formers of (II).
- (b) ~~Check E.2~~ done (above): E.2 is probe absorption with Q = Dᵏ.
- (c) Decided: the project's type theory needs only reading (II), and round 5 confirms this. D11's remaining reading-(I) questions (the original 𝒢, ι∘π, forward uniqueness) are research side questions. They stay under D11 and do not block D7 or E.3.

### F.7.4 The biclosed rules of the kernel (D7, from the r3 answer)

*Added 2026-11-20, thread "Add Gray biclosed rules to the core" (GBIC). Source: `conjectures/answered/gray-biclosed-coherence-r3-2026-11-20.md`, Response 2 (verified). This turns the F.7.3 draft into rules. F.7.3's structural statements become derived facts (item 5 below). Agda: `src/CaTTExp/Gray/Biclosed/` (item 7).*

**Reading and names.** Reading (II). Names follow `conventions.md` §3.2:
- A\C = Hom_lax(A, C). Its evaluation takes the argument first, (A, A\C) ▸ C, as in `conventions.md` §4.
- C/A = Hom_oplax(A, C).
- The lax hom [Θ, C] of `internal-hom.md` §5.1 is C/⟦Θ⟧. Maps Δ ⊳ [Θ, C] are maps out of Δ ⊗ Θ, the right residual.

#### 1. Judgements

- **Objects.** Γ ⊢ A : ⋆, as before. There are three new formers: ⊗, \ and /.
- **Multimaps.** The new judgement is Γ ⊢ t : (X₁, …, Xₙ ▸ Z), with n ≥ 0 and every Xᵢ and Z an object. Its meaning is a map X₁ ⊗ … ⊗ Xₙ → Z, and the list is never bracketed.
  - With n = 1 it is an ambient 1-cell.
  - With one representable input it is the diagram judgement: (⟦Δ⟧ ▸ C) is Δ ⊳ C of `internal-hom.md` §5.
- **Time slots.** A *time slot* is an input position holding a representable ⟦Θ⟧. The cells of homs are multimaps with ⟦Dᵏ⟧ in a slot:
  - (B, ⟦Dᵏ⟧ ▸ C) is a lax k-cell between maps B → C, a cell of ℍ_r;
  - (⟦Dᵏ⟧, B ▸ C) is an oplax k-cell, a cell of ℍ_ℓ;
  - a slot between two data inputs gives the mixed cells of the double hom.

  Faces are restrictions along ⟦s⟧, ⟦t⟧ : ⟦Dᵏ⁻¹⟧ → ⟦Dᵏ⟧. With n = 0 and a time slot, Dᵏ ⊳ C is a k-cell of C.
- **Invertible cells.** These are the marked judgement ⊨ (`internal-hom.md` §5.1, `invertibility-markings.md`) at a time slot. Response 2 needs balls Dⁿ of invertible homotopies of operations. Its paragraph "Where to put an invertible parameter" realizes them as cells at an extra time slot all of whose cells are invertible, because by completeness diagrams in the core of a hom are balls. The kernel uses that realization. The slot for an invertible ball is the rightmost gap. For invertible cells the side does not matter, since pseudo cells embed in both families.
- **Substitution and the ambient calculus.** Multimaps substitute into slots planarly, as in a planar multicategory, which extends the pre- and postcomposition of `internal-hom.md` §5. A substitution σ : Θ′ → Θ produced by the L core restricts a time slot along ⟦σ⟧. Composition of cells inside a one-hole hom is therefore L's coh with its side condition in V + S (`design-decisions.md` §1.7). This is the "ambient calculus" that Response 2 takes as its base: the lax-grid calculus, whose model is Keidar–Neuhauser's (arXiv 2606.27574, Thm 4.15 and Cor 4.16).

#### 2. The rules

Every rule has the shape of `coh`: a generic context, a goal, and an admissibility test. Each produces a term with no definitional equation. Universal properties are witnessed by cells (standard 5).

```
(GB-form)   Γ ⊢ A : ⋆    Γ ⊢ B : ⋆   ⟹   Γ ⊢ A ⊗ B : ⋆,   Γ ⊢ A\B : ⋆,   Γ ⊢ B/A : ⋆

(GB-pair)   (U V : ⋆)  ⊢  m_{U,V} : (U, V ▸ U ⊗ V)
(GB-evℓ)    (A C : ⋆)  ⊢  e^ℓ_{A,C} : (A, A\C ▸ C)
(GB-evr)    (A C : ⋆)  ⊢  e^r_{A,C} : (C/A, A ▸ C)
(GB-probe)  ⊢  p_{Δ,Θ} : (⟦Δ⟧, ⟦Θ⟧ ▸ ⟦Δ ⊗ Θ⟧)      for pasting shapes Δ, Θ
(GB-pt)     ⊢  pt : ( ▸ ⟦D⁰⟧)
```

- Δ ⊗ Θ in (GB-probe) is the Gray tensor of contexts (`internal-hom.md` §4), and p is its pair of inclusions. In Response 2 this is "for pure U, V use the identity on their probe product as m_UV".
- (GB-pt) is Response 2's nullary pure operation m₀, with ⟦D⁰⟧ as the probe unit I.

**Rows.** Each row is a restriction r : H → B between multimap types. It sends x to the two-vertex composite of x with the row's distinguished vertex.

| Row | H, the missing vertex | B, the outer operation | r(x) |
|---|---|---|---|
| pair at slot i | (L, U⊗V, R ▸ Z) | (L, U, V, R ▸ Z) | x ∘ᵢ m_{U,V} |
| probe pair at slot i | (L, ⟦Δ⊗Θ⟧, R ▸ Z) | (L, ⟦Δ⟧, ⟦Θ⟧, R ▸ Z) | x ∘ᵢ p_{Δ,Θ} |
| unit at slot i | (L, ⟦D⁰⟧, R ▸ Z) | (L, R ▸ Z) | x ∘ᵢ pt |
| left evaluation | (Φ ▸ A\C) | (A, Φ ▸ C) | e^ℓ ∘ (1_A, x) |
| right evaluation | (Φ ▸ C/A) | (Φ, A ▸ C) | e^r ∘ (x, 1_A) |

- L, R and Φ are lists of objects, and any entry may be a time slot.
- **Sort discipline.** Representables play the probe sort. The output Z or C of a row, and every object variable in an output position, ranges over non-representable formulas (atoms, ⊗, \ and /). Representables may appear in inputs, as time slots, and as bound arguments of residuals (Lemma GB-ext (ii)). Pure profiles (⟦Δ⟧, … ▸ ⟦Θ⟧) are built from L's substitutions, p_{Δ,Θ} and pt. The discipline also covers context variables: a hypothesis whose base profile has a representable output must have only representable inputs. A hypothesis y : (A, … ▸ ⟦Θ⟧) with a data input A is not a well-formed context entry. Without this clause such a y would be a profile with a data input and a pure output, and step 4 below would fail. In Cat_ω a representable is just an object, so this restriction loses no soundness. It keeps the free model's sorts, which conservativity over L uses (§4 step 4). To use ⟦Θ⟧ as a data output, take a data atom interpreted as ⟦Θ⟧.
- A time slot in Φ stays in its gap: the left row's outer input is (A, Φ) and the right row's is (Φ, A). So a cut never moves a directed time past the bound object (Response 2, "Under a cut, use the image of the same gap").
- In the unit row, B is a sub-case of the pair row with nullary m₀.

**(GB-cut_{ρ,n}), for a row ρ and n ≥ 0.** The generic context Ctx(ρ, n) contains:
- a fresh object variable for each formula of the row (U, V, L, R; or A, C and the entries of Φ);
- b, an invertible n-ball of operations of type B;
- u, an (n−1)-sphere of operations of type H, empty when n = 0;
- a, the collar r(u) ⊨ b|_{∂}, empty when n = 0.

Two goals are admissible in Ctx(ρ, n):
- **c_{ρ,n}**: the n-ball of type H with boundary u;
- **ε_{ρ,n}**: the invertible (n+1)-cell of type B from r(c_{ρ,n}) to b with the collar a adjoined.

The source of ε contains c as a term, not as a variable. At n = 0, c is the curry or factorization of b and ε : r(c) ⊨ b. At n = 1 with b constant, the rule connects two lifts of the same b, which is uniqueness.

**(GB-dcut_{ρ,k}), for a row ρ, k ≥ 1, and a time slot ⟦Dᵏ⟧ at a fixed gap of the row's lists.** The generic context contains:
- the object variables of the row;
- u⁻ and u⁺, parallel operations of type H at ⟦Dᵏ⁻¹⟧ in that gap, with their common boundary;
- b, an operation of type B at ⟦Dᵏ⟧ in the same gap;
- a^±, comparisons r(u^±) ⊨ b|_{∂^±} that agree on the common boundary.

The goals are d, of type H at ⟦Dᵏ⟧ with source face u⁻ and target face u⁺, and an invertible comparison r(d) ⊨ b relative to a^±. This is Response 2's template (6). Its exactness is the pushout (6) there.

**Orientation.** The only directed goal is d, and its direction is inherited from the hypothesis b. No template has a directed goal whose orientation is not that of a hypothesis. So the rules admit no reverse cells. The response's specialization argument rules out the reverse of the walking square and both directions of the ν(I^⊗4) pair 212321 / 123212 (r3 item 41).

#### 3. Admissibility and its decidability

A goal is **admissible** iff, up to renaming of context variables, its context and type are one of the templates of §2. The row's formula constructor is read off the goal's type. Admissible goals are then closed under type and term substitution, as for `coh`.

**Lemma GB-dec.** Admissibility is decidable.

*Proof.*
- The templates form finitely many families, indexed by (row, slot, gap, n or k), and the indices are bounded by the size of the goal.
- For each candidate index, matching compares a finite incidence presentation up to a bijection of variables (finitely many) and compares formula expressions syntactically.
- The ε and comparison goals are tested by building the term r(c), which needs no search for an operation.
- Restrictions along ⟦σ⟧ call L's side condition, which is decidable in every switch setting (`design-decisions.md` §1.7, Lemma V-dec and its extension). ∎

Deciding whether an arbitrary sequent has *some* derivation is a different question, and it is undecidable (r3 item 38). The kernel never asks it.

#### 4. Soundness and exactness

- **Soundness.** In Cat_ω, ⊗ is Campion's Gray tensor, \ and / are its two closures (Campion, arXiv 2311.00205), and the probe base is the Gray maps of pasting shapes. Every template is sound there by Response 2's extension lemma, which says that a row is an equivalence iff every relative disk lifts. The combined kernel is sound wherever the L core is sound in Cat_ω, an existing item that this section does not change.
- **Exactness.** Response 2's theorem (3) says that the free data model 𝓕_Σ, built by reflecting at the tree conditions, the grid conditions and the table rows, is initial among data models over the lax-grid model. The two-step attachment identifies naming c and ε with that reflection.

**Lemma GB-ext (in-house, argument level; independent check requested, D7c).** Theorem (3) of Response 2 still holds with three extensions that the kernel needs:
- (i) **element generators**: profiles whose inputs are all probes and whose output is data, including the nullary profile;
- (ii) probes as **bound arguments** of residuals, so that [Θ, C] = C/⟦Θ⟧ is an instance;
- (iii) ~~any probe base generated by the L core in a fixed switch setting V + S~~. *Restated 2026-11-20 after the independent check (D7c):* the probe base is Response 2's own, the Gray maps between grids and globes in Cat_ω, written P. The kernel's probe judgements, which are L in a switch setting V + S, enter only through their interpretation U → P: each L-core substitution σ names the Gray map ⟦σ⟧. The grid tests are the ones over P, which is the reviewer's option of pulling the tests back along U → P. Such an interpretation exists if L is sound in Cat_ω, which is item E11 and is not changed here. The other option, showing that V + S computes the Gray mapping spaces on grids and globes, is not needed and is not claimed.

*Proof sketch.* The argument re-runs Response 2's proof step by step.
1. **Localization.** Allowing more profiles, and the table maps for the new instances (the evaluation rows with Γ pure or empty, and residuals with a probe as the bound argument), still localizes a presentable category at a set of maps. The cellular description (5) is unchanged, because the test objects are still compact.
2. **Grid tests.** The one-hole homs with no data input, G ↦ O(W(G); Z) with W a word of probes, get the same grid Segal and completeness tests. In Cat_ω they hold because O(P, G, Q; Z) = Map(G, P\Z/Q) is represented by an object.
3. **Local objects.** The representability argument goes through unchanged. Its conclusion "unary mixed homs are empty" becomes: probe-to-data homs may be nonempty, and data-to-probe homs are empty. That is the intended Cat_ω picture.
4. **Pure-probe preservation.** The point-extension right adjoint still works: a tree with pure output still has only pure vertices, because no profile has data inputs and pure output. This step uses nothing about the probe base, so semantically the biclosed rules add **no new maps between pasting shapes** beyond those of P.
   - *Syntactic form (the kernel).* The sort discipline of §2 (the output of a data rule is never a representable) means that no derivation of a pure judgement (⟦Δ₁⟧, …, ⟦Δₖ⟧ ▸ ⟦Θ⟧) passes through a data rule. Substitution cannot place a data-output term in an input of a pure-output profile. So no data rule enters a derivation of a pure judgement. The pure fragment is the free planar multicategory on L's substitutions, p_{Δ,Θ} and pt, with no equations between them. It is not L itself: p ∘ (σ, τ) and (σ ⊗ τ) ∘ p are distinct terms, different bracketings of iterated p differ, and p_{Δ,D⁰} ∘ (x, pt) : (⟦Δ⟧ ▸ ⟦Δ ⊗ D⁰⟧) is a unary pure term that is not an L substitution. The conservativity claimed is therefore: the pure judgements of the kernel are those of L + p + pt, in every switch setting, and no biclosed rule adds to them. This needs no comparison between V + S and P. The stronger form, pure judgements exactly L's, would need pure multimaps (⟦Δ₁⟧, …, ⟦Δₖ⟧ ▸ ⟦Θ⟧) to be defined as L substitutions out of Δ₁ ⊗ … ⊗ Δₖ, with ⊗ on substitutions and its unit and associativity laws strict or derivable in L. That is not claimed.
5. **Initiality.** Formula (3) follows from the reflection and the free-corolla property, with Σ now allowed to contain element generators x : (⟦Θ⟧ ▸ T).

What this sketch does not settle: whether step 2's extra tests interact with the table rows when Γ is pure. They should not, since both are locality conditions for one reflection. That is the point the independent check should look at. ∎

#### 5. Reconciliation with E.1, E.2, E.4, F.7.3 and `internal-hom.md` §5.1

Everything in this list is now **derived**. None of it is a primitive any more.

- **(lhom), `internal-hom.md` §5.1.**
  - [Θ, C] := C/⟦Θ⟧.
  - (lhom-Λ) takes φ : (⟦Δ⊗Θ⟧ ▸ C), restricts it by the probe-pair row to (⟦Δ⟧, ⟦Θ⟧ ▸ C), and applies c of the right row at n = 0. (lhom-♭) is the inverse composite of the two r's.
  - β is ε at n = 0.
  - η is c at n = 1, comparing the lifts (ψ, identity) and (Λ(ψ♭), ε).
  - (nat-Δ) and (nat-C) are n = 1 instances: both sides are lifts of the same outer operation.
- **E.2, the B ⊗ Θ rule.** B ⊗ Θ is the formula B ⊗ ⟦Θ⟧.
  - u_B := c_{right,0}(m_{B,⟦Θ⟧}).
  - h♯ := c_{pair,0}(e^r ∘ (h, 1)), and ε_h is built from the two ε's.
  - (⊗Θ-uni) is the n = 1 instance of the pair row.
  - So E.2's four rules are derived, and E.4, which is derived from E.2, is unchanged.
  - E.4 Prop. E2 (⟦Δ⟧ ⊗ Θ ≃ ⟦Δ ⊗ Θ⟧) now also follows directly, because both objects represent the same operation space (pair row against probe-pair row).
- **E.1, the warning.** The rows are equivalences of operation spaces with each time slot fixed in its gap. They are never equivalences of hom (∞,ω)-categories with a time slot moved. So the unsound naive rule of E.1 is not an instance. For example:
  - (B⊗C, ⟦Dᵏ⟧ ▸ D) ≃ (B, C, ⟦Dᵏ⟧ ▸ D) by the pair row;
  - the right row then curries C and the time slot *together*, giving (B ▸ D/(C ⊗ ⟦Dᵏ⟧));
  - that is E.1's "higher cells through [Dᵏ, D]", and it is probe absorption.
- **F.7.3.** All of F.7.3's statements are instances of the rows:
  - Φ_L and Φ_R (pair row, then the left or right row, with Γ = (B, ⟦Dᵏ⟧) or (⟦Dᵏ⟧, A));
  - probe absorption;
  - 2-functoriality of A ⊗ – on lax cells and of – ⊗ B on oplax cells;
  - the canonical but non-literal equivalence (A\C)/B ≃ A\(C/B) (r3 item 17): both sides represent (A, Φ, B ▸ C).
- **Mixed-shape cells.** These are multimaps with an inner time slot, as F.7.3 and `gray-cylinders.md` describe.

#### 6. What changes in the kernel, and what does not

- **New:** the multimap judgement, the formers, five corollas, and the cut and directed-cut templates.
- **Unchanged:**
  - L's coh rule and its side condition in V + S (no biclosed rule enters a pure derivation, by the sort discipline, so pure judgements are those of L + p + pt; §4 step 4);
  - markings, which ⊨ already provides;
  - the pseudo hom of `internal-hom.md` §5.4–§5.5, which is cartesian and independent of these rules.
- **Retired as primitives:** (lhom) and (⊗Θ), which are now derived (item 5). They can stay in the checker as derived rules.
- **No universes, and no definitional equations** beyond CaTT's syntactic substitution. Planar substitution of multimaps is the meta-operation, as substitution is in CaTT.

#### 7. Formalization (standard 9) and open items

- **Agda: `src/CaTTExp/Gray/Biclosed/`** (type-checked locally with Agda 2.6.3, `--safe`, no postulates).
  - `Syntax`: formulas, multimap types, globular cell types with a gap and a mode, and terms. Boolean equality on all of them is proved sound and reflexive.
  - `Typing`: a checker `infer`/`wf`/`wfCtx`. Planar substitution and whiskering move the gap by the number of inputs to its left. The collar term `glue` has a stated typing rule: it stands for an L-core composite, and that composite is not derived from L's coh in Agda.
  - `Templates`: the five rows with their r, the generic contexts of (GB-cut) and (GB-dcut) for every n, the relation `Admissible`, and the decision procedure `admit?`.
    - `admit?-sound` and `admit?-complete` give Lemma GB-dec for the template relation. Renaming is handled by canonical numbering of the generic formulas.
    - `no-reverse` proves that a directed goal and its reverse are never both admissible, so the template relation is not endpoint-symmetric (r3 item 29). This is proved for the template relation on generic contexts. It covers substitution instances only once closure under substitution is formalized.
    - `dir-needs-dir` proves that an admissible directed goal has a directed hypothesis. It too is a statement about the template relation.
  - `Examples` (by evaluation):
    - For nine rows, the derived (lhom) and E.2 unit rows among them, every generated context and both goals are well typed, and both goals are admitted. That covers (GB-cut) at n ≤ 2 (and n = 3 for one row) and (GB-dcut) at k ≤ 2 at every gap.
    - Reversed directed goals are rejected. So are directed goals once b is made invertible.
    - Negative controls: non-generic or misnumbered formulas, n = 0 directed, wrong endpoint types, a dropped collar, and a goal from another row's context.
  - `TemplatesTyped` (D7f, 2026-11-20): `templates-typed` proves for **every** row, gap, mode and n that the generic context is well formed entry by entry and that both goals are well-formed types in it. The proof follows the collar chains through a mixed tower type that moves the levels below j to the H side. The `glue` typing rule is still the stated one.
  - `Subst` and `Instances` (D7e, 2026-11-20). `Subst` defines substitution of formulas and terms, and the judgement Γ ⊢ σ ∶ Δ. Its main result, `sub-infer` / `sub-wf`, says the type checker is stable under well-typed substitution: if x has type A in Δ, then x[σ] has type A[σ] in Γ. This includes the `glue` rule, because a successful glue matches at the one level whose dimension is the collars'. `Instances` defines AdmI Γ A: A is σ applied to a template goal (c or ε) with Γ ⊢ σ ∶ ctx t. It proves four results. `adm→inst`: generic admissibility is the identity instance. `inst-subst`: instances are closed under well-typed substitution, via composition of substitutions. `inst-typed`: every instance is well formed, from D7f. `inst-dir`: for a directed instance, the goal's top cell goes from σ(u⁻) to σ(u⁺), σ(b) is a directed cell from σ(β⁻) to σ(β⁺), and σ(a⁻), σ(a⁺) are invertible collars from r(σ(u±)) to the collared σ(β±). So its direction comes from the instance of b. AdmI does not impose the sort discipline of §2, so it is a superset of the kernel's instances, and `inst-typed` and `inst-dir` hold on it. `SortDisc` (2026-11-20) formalizes the discipline. A context declares its data-sorted object variables S. A substitution is data-sorted from S to S′ (`DSub`) when it sends each variable of S to a non-representable formula whose head variable, if any, lies in S′. The kernel instances `KInst S Γ A` are the AdmI instances whose σ is data-sorted from the template's data variable (the head of its output Z or C) to S. `kinst-subst` proves they are closed under well-typed, data-sorted substitution, via `dsub-⨾`. `adm→kinst` and `kinst→inst` relate them to the generic judgement and to AdmI. `templates-sorted` proves that every entry of every template context satisfies the context-variable clause of §2 for the template's data variable. That clause reads: an entry with non-representable output has its head variable in S, and an entry with representable output has only representable inputs. `sorted-sub` and `sortedCtx-sub` prove that a data-sorted substitution preserves the clause, so the clause carries from template contexts to instances. `no-reverse` and `dir-needs-dir` stay generic-only. Sending b to an identity can make σ(u⁻) = σ(u⁺), so the absence of reverse cells for instances is the semantic r3 argument (the walking square). (Until 2026-11-20 the coherence term was `here A` and inhabited every well-formed type, D7h, witnessed in `HereAmbiguity`; it is now `here t e φs ts`, which records its template and instance and is typed by CaTT's rule for coh(Γ, A)[σ].)
  - Theorem S, generic part (C5b, 2026-11-21, thread "Formalize the strict Gray model in Agda"). `Model` states what a semantics of the kernel needs: a planar multicategory over the formulas up to ≈, with an extrinsic typing judgement, invertible precomposition with the corollas m, p and pt, invertible left and right evaluation rows, and globes with σδ = 1. `ModelFacts` and `RowSem` derive planar composition, whiskering, degeneracies, and r with its inverse and faces for all five rows. `Sem` interprets terms from the values of the context variables, and each cell type as a predicate `Mem`; `SemComp` and `SemHere` prove composition, `glue` and `here` sound. `Soundness.soundness`: in every model, if the values satisfy Γ and `infer Γ t ≡ just A`, then ⟦t⟧ ∈ Mem A. Mode inv is read as flat (source ≈ target). `Poset` and `PosetModel` give a nontrivial model: finite posets and monotone maps, with ⟦Dᵏ⟧ the chain 0 < … < 2k.
  - D7g for the generic contexts (2026-11-21). `DirEnv` values the generic context of a directed template by a tower of cells, in any model; `D7g.d7g` proves, for every row, gap and k, that no term has the reversed goal type, by soundness in the poset model and monotonicity at the interior of the globe.
  - **Not formalized:** the ∞-categorical initiality of §4, which stays on paper (Response 2, verified; Lemma GB-ext, checked at argument level under D7c).
- **Open items:**
  - (D7c, closed 2026-11-20) Lemma GB-ext checked at argument level by an independent reviewer, with (iii) restated over P and conservativity stated as "no biclosed rule enters a pure derivation";
  - (D7e, closed 2026-11-20) closure of admissible goals under substitution, `Subst`, `Instances` and `SortDisc` above, independently reviewed (PR #329);
  - (D7g) no reverse cells for directed instances: proved for the generic contexts in the strict Gray model 𝔖, at argument level (`free-objects-proofs.md` §5.4–§5.5), and in Agda (`D7g`, above, with inv read as flat). The earlier wording "unless σ(b) is invertible" is false for instances; the corrected criterion is there. The instance criterion and the four-cube computation are not yet in Agda (thread "Formalize the strict Gray model in Agda");
  - implementing the new judgement in the type-checker, which belongs to the thread that implements lhom (E.4's note).

---

# Part G. Open items left by this note

| Item | Owner after this thread |
|---|---|
| D10 completeness of UL_I (B.3 generation statement) | CLOSED thread (D10a), in progress |
| ~~A4 generalization lemma written out in full~~ | done (Lemma A5, D9a closed) |
| ~~D7 remainder: both factors arbitrary~~ | done (F.7.4). D7c (independent check of Lemma GB-ext) and D7d (Agda, `src/CaTTExp/Gray/Biclosed/`): GBIC thread |
| D11: event order across residuals; ω-version; soundness/completeness | out to researcher (`conjectures/outbox/gray-pasting-types.md`); internal attempt: CLOSED thread |
| D12: higher coherence for free cartesian closed (∞,1)/(∞,ω)-categories | `conjectures/outbox/cartesian-closed-higher-coherence.md`, ready to send; internal attempt: CLOSED thread |
| ~~D8 for uniform L~~ | done (§D.4–D.5, `GrayDualityUniform.agda`, `Gray/Biclosed/Mirror.agda`) |
| Implement L_ε in the support checker | L-core thread (E1) |
