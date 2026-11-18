# Closed structure via pasting types: PL1, units, dualities, Mimram's higher criteria, Gray tensor, PL-ω

*2026-11-18. Ledger items D7–D12 (`open-issues.md`). Builds on `conjectures/planar-pasting-types.md` (PL1, PL-ω), `internal-hom.md` §5–§6, `pseudo-vs-gray.md` R5 and §3. Machine checks: `scripts/pl1_check.py`, `scripts/duality_check.py`, `src/CaTTExp/GrayDuality.agda`.*

## Summary

| Item | Result | Status |
|---|---|---|
| **D9** PL1 | **Proved.** In the free unit-free biclosed monoidal category, a balanced sequent has at most one morphism (Part A, Theorem A). The proof is a direct sequent-calculus argument: two factorization lemmas plus connectivity. The "faithfulness lemma" the literature route needed is no longer an input; it becomes a corollary (Corollary A3), as does the non-symmetric Kelly–Mac Lane theorem (equal linking ⇒ equal morphism). Steps 2–3 of `planar-pasting-types.md` §2 are written out in full, for the theory with ⊗ (Theorem A4, with the generalization Lemma A5 proved by a sign invariant on unification). | closed |
| **D10** Units | **Balanced is not enough** once a unit is present: the triple-dual endomorphism is a second morphism of a balanced, provable sequent (Part B.1). **A contractible class that does work**: sequents that normalize, under the canonical unit isomorphisms and invertible rules, to a unit-free pasting sequent or to ⊢ I (Theorem B). Completeness of the resulting theory UL_I is proved in outline (B.3). | contractibility proved; completeness proof sketch to check |
| **D8** Dualities under L | **Classified.** A duality D_K on Steiner complexes commutes with ⊗ (canonically) iff K ∈ {∅, all}, and reverses it iff K ∈ {odd, even}. Every other duality turns ⊗ into a *twisted* tensor. For two-tier L: the ambient dualities D_J that are symmetries are exactly J ∈ {∅, {2,3,…}, odd, {1,2,4,6,…}}. Those that swap lax and oplax are J ∈ {{1}, all, even, {3,5,7,…}}. Every other J sends L to a mixed-orientation theory L_ε. The orientation-parameterised kernel is the family L_ε, on which the whole duality group acts transitively, and freely up to the global sign (Part D). Agda: the sign lemma and the classification. | closed (kernel family designed; implementing it is part of E1's checker) |
| **D12** Mimram's higher criterion | The tool (commit `69bb11a`) has **two** higher criteria, read off the source: a *reversible* one, for (∞,1), which contracts higher hypotheses that have a free endpoint; and a *directed*, globular one (Part C). Re-check of `internal-hom.md` §5.7 against the PDF: four corrections. Soundness of the directed criterion in dimension 2 over graphs follows from Fiore–Saville. The general case is posed as a conjecture (`conjectures/cartesian-closed-higher-coherence.md`). | criteria worked out; soundness beyond dim 2 out as a conjecture |
| **D7** Gray tensor of arbitrary objects | **Partly unblocked.** B ⊗ ⟦Θ⟧ for *arbitrary* B and representable Θ (and ⟦Θ⟧ ⊗ C) can be given by a colimit-free representability rule over the existing lax hom (lhom), sound by Campion's biclosedness. Lax cylinders B ⊗ D¹ of arbitrary objects follow. The universal property is stated precisely, including higher cells (through the pseudo cotensor). A naive rule asserting the bijection on *all* cells is unsound, with an explicit counterexample at B = C = D¹. Both factors arbitrary still needs [C, –]_lax for arbitrary C, which needs either object-indexed limits (F5) or PL-ω. | partly done; remainder blocked on F5 or D11 |
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

*To check:* that the generation statement holds for the free biclosed monoidal category with unit, i.e. that nothing beyond these generators and operations is needed. This is a standard presentation, but it has not been verified here.

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

**Everything beyond.** This covers Dir with 2-dimensional hypotheses, Dir in dimension ≥ 3, and Rev in all dimensions. Soundness needs a coherence theorem for free cartesian closed (∞,1)- or (∞,ω)-categories (with pseudo exponentials) on computads. None is known. It is posed, self-contained, in [`conjectures/cartesian-closed-higher-coherence.md`](conjectures/cartesian-closed-higher-coherence.md).

**Consequences for the project.**
- *Under P* (pseudo ambient), Dir with the CCC base is a candidate replacement for the λ/⌜⌝ rules of `internal-hom.md` §5.4, as §5.7 suggested. It is now an explicit criterion, not a guess. Its β/η cells are invertible coherences, which is what the pseudo hom needs.
- *Under L / Gray*, Dir is the wrong shape. In monoidal mode, for hypotheses f : a → a′ and g : b → b′, both (f⊗b′)∘(a⊗g) → (a′⊗g)∘(f⊗b) and its reverse are accepted. The source and target contexts are the whole context, and no variable is forbidden. So Dir makes interchangers invertible and fails the PL-ω test (Part F). Part F's candidate is Dir plus one orientation condition.

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

**Under uniform L** (E6, not yet constructed) the same analysis applies level by level. The symmetries are those J for which every shift J − k passes the test above at every level. This is to be redone once E6's structure exists.

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
- **Consistency:** for B = ⟦Δ⟧, B ⊗ Θ and the Gray context ⟦Δ ⊗ Θ⟧ represent the same functor, so they are equivalent. This needs a comparison cell rule.
- **Mirror:** ⟦Θ⟧ ⊗ C via the oplax hom, which is derivable by `internal-hom.md` §5.6.

**Payoff.** Lax transformations between arbitrary functors are maps B ⊗ D¹ → C. That is a cleaner presentation than the fibre definition LaxTr(F, G) of §5.2, and it composes by (⊗Θ-fill).

## E.3 What still blocks both factors arbitrary

B ⊗ C with C arbitrary needs [C, –]_lax for arbitrary C as an object. Two routes:
- an end over C's cells, [C, D]_lax ≃ lim_{⟦Θ⟧→C} [Θ, D], which is an object-indexed limit (F5) and connects to C9 (density);
- the PL-ω route (Part F): give ⊗ and [–, –]_lax together as type formers whose structure maps are coherences over Gray pasting types.

The colimit route of `internal-hom.md` §6 (B12) remains a third option. **Status:** partly done. The remainder is blocked on F5, or on D11's general criterion. Owner: unowned after this thread.

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

---

# Part G. Open items left by this note

| Item | Owner after this thread |
|---|---|
| D10 completeness of UL_I (B.3 generation statement) | CLOSED thread (D10a), in progress |
| ~~A4 generalization lemma written out in full~~ | done (Lemma A5, D9a closed) |
| D7 remainder: both factors arbitrary (F5 / PL-ω / B12) | blocked; listed under D7. Adjacent E.2 rule work: CLOSED thread |
| D11: event order across residuals; ω-version; soundness/completeness | out to researcher (`conjectures/outbox/gray-pasting-types.md`); internal attempt: CLOSED thread |
| D12: higher coherence for free cartesian closed (∞,1)/(∞,ω)-categories | `conjectures/outbox/cartesian-closed-higher-coherence.md`, ready to send; internal attempt: CLOSED thread |
| D8 for uniform L | blocked on E6 |
| Implement L_ε in the support checker | L-core thread (E1) |
