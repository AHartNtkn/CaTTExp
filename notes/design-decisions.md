# Design decisions: the lax side-condition theory and context checking

*Owner: thread "Choose lax core and context-check designs" (DSGN). Written 2026-11-20. Ledger rows E12 and B25.*

## 0. How these choices are made

These two questions stopped being research questions when the latest answers came back:
- lax interchange: there is no initial theory over P, not even a weakly initial one, and there are infinitely many independent laws (r7, (K54)–(K57));
- context checking: homotopicality of finite polygraphs is undecidable, co-r.e.-complete already on positive 3-polygraphs (HPOL r4).

Neither result picks a design, so the choice is made here, under the project standards:
- every coherent option is described, with worked examples of what it derives and what it rules out;
- the options are compared on decidability of type checking, the CaTT rule aesthetic, no universes and no definitional equalities;
- proved facts decide. Where they leave a tie, the most general option wins (standard 4).
- A claim that is still open is not held against the option that needs it. It gets a proof attempt here, and an outbox question if the attempt stalls.

Each decision ends with what would overturn it.

---

## 1. Lax interchange: which theory the side condition computes in

### 1.1 What the choice actually changes in a CaTT-style kernel

Uniform L keeps CaTT's syntax and changes only the side condition of `coh`. Whether `coh(Γ, u → v)` is derivable over a pasting context Γ is read off the free object F_T(Γ) of a fixed strict theory T (`pseudo-vs-gray.md` §2.5, §7). So:
- **a law of T is never a definitional equality.** If T proves ⟦u⟧ = ⟦v⟧, the kernel gets coherences u → v and v → u, which are cells like any others. Every option below satisfies constraint 5 in the same way.
- **The rule's form does not depend on T.** Only the oracle behind the side condition changes. Every option has the same rule classes as published CaTT variants.
- **Generality is set inclusion.** If T interprets into T′ fixing P, every judgement derivable over T is derivable over T′. Fewer derivable coherences means more models.

### 1.2 Facts that constrain the choice (all proved, see `open-issues.md` E6)

- (K47)–(K50): T₁₂ satisfies requirements 1–5 in every dimension with H ≠ 1. (K52): normal forms in every degree; equality and reachability on F_T₁₂(Γ) are decidable.
- (K44), (K51): the **inner composite-crossing law** (direct crossing of A₁ ∗ A₂ past B = paste of the two crossings) is optional. A tagged model separates the two sides, and the joint theory without the law still satisfies 1–5.
- (K55): on the T₁₂ signature the **right split R** and the **prime left splits L_p** are independent of each other and of T₁₂'s other laws. Any selection of them can be omitted by taking the common laws of T₁₂ and the separating tables (r7 Response 2, "Take the common theory of the primary T coordinate and the tests for just the laws one wants to fail"). (K56): the divisibility laws D_{d,p} give a further infinite family.
- (K54), (K57): no initial and no weakly initial theory exists. In particular, no single theory is sound for every admissible theory's models. Generality can also be inflated without content: duplicating T₁₂'s upper operations gives an admissible theory with an involution (K54).

### 1.3 The options

**L1. Fix T₁₂.** The side condition is reachability in F_T₁₂(Γ).
- Derives: every coherence that T₁₂'s laws give. That includes an invertible cell between the direct inner crossing of a composite and the composite of crossings, and all the splits.
- Rules out: every model in which an inner crossing of a composite differs from the paste of crossings: the tagged model of (K44), the tables M_q of (K55), and U_N of (K56).
- Decidable: yes, by (K50) and (K52).

**L2. Fix the most general known theory J, with the catalogued laws as switches.** J is the common theory of T₁₂ and the separating algebras for each catalogued law:
- the tagged model of (K44)/(K51), which fails the inner composite-crossing law;
- the marked algebra of (K51), which fails R;
- the cyclic marked tables M_q for every prime q, which fail every L_p.

J(S) is J with the laws in S switched back on, which means dropping their separating algebras. J(all) = T₁₂.
- Derives: what holds in every one of these models, which is everything T₁₂ derives except the catalogued laws and their consequences.
- Rules out: nothing that L1 allows. Every T₁₂ model is a J model.
- Decidable: yes (Lemma J-dec, §1.5).
- Developments import upwards: a J(S) development is valid in J(S′) for S ⊆ S′, because the identity-on-letters quotient sends steps to steps (argued in prose) and the abstract lemma that such a map sends paths to paths is machine-checked (`Join/BoundedReach.agda`, `Transport.transport`).

**L3. J plus laws as hypotheses.** Keep J's side condition, and let the user declare a catalogued law as a signature cell over its generic context, marked invertible. All its instances then follow by substitution.
- Derives: the law itself, but not its higher coherences. The side condition does not see a declared cell, so two different uses of it are not related by any coherence.
- Decidable: yes. The cost falls on the user (example (c) below).

**L4. The theory-independent kernel E.** A coherence is derivable iff its type is inhabited in **every** admissible theory.
- Derives: only what all admissible theories share, so it is sound in all of their models. That is the strongest possible reading of "most general".
- Status: nobody knows whether E is the side condition of any admissible theory, or whether it is decidable. (K57) shows that E is not the image of any single weakly initial theory. It does not show that E fails requirement 3 or 4.

### 1.4 Worked examples

(a) **The strip C_{2,1}.** Inside a hom, take two composable inner cells A₁, A₂ and a cell B in interchange position. Let u = W(A₁ ∗ A₂, B) be the direct crossing and v the paste of W(A₁, B) and W(A₂, B). Both have the same Gray image.
- L1: ⟦u⟧ = ⟦v⟧, so `coh` gives an invertible cell u ≅ v.
- L2 (law off): u and v are distinct cells with no cell between them. In the tagged model they really differ.
- L2 with the inner law switched on: same as L1.
- L3: the user declares κ : u ≅ v once, over C_{2,1}.
- L4: unknown. It depends on whether every admissible theory relates u and v by some cell, and (K57)'s U_m suggests that not all do.

(b) **A loop.** In a context with an inner endomorphism A and an adjacent B, compare W(A ∗ A, B) with W(A, B) pasted with W(A, B). Over a pasting context these terms arise only by substituting A₁, A₂ := A into example (a). So in every kernel above, L₂ for this A is decided by the strip law. The independent prime laws only become visible as separate kernel choices if F_T(Γ) of some *pasting* Γ contains an inner endomorphism they act on. F_T₁₂(Γ_{2,2r}) does contain loops (the powers of H, (K45)), so this is possible. Whether it happens is open question Q-vis (§1.6).

(c) **Three-fold composite, L3's cost.** With a declared κ, the crossing of A₁ ∗ A₂ ∗ A₃ past B can be split into single crossings in two ways (κ on the left pair first, or on the right pair first). Under L1 both routes are equal cells, so `coh` relates them. Under L3 the side condition does not know κ, so the two composites of κ instances are unrelated until the user declares a 6-cell, then a 7-cell for the next coherence, and so on. L3 cannot replace switching the law on in the side condition.

(d) **Reductions.** In every option, making inner interchangers identities gives two-tier L, and making all of them identities gives CaTT (requirement 4 for J(S) is part of the r7 Response 2 construction). So markings like `ord` behave the same under every option.

### 1.5 Lemma J-dec (decidability of every switch setting)

**Lemma.** For every finite pasting diagram Γ and every switch set S (finite, or the full prime family), reachability between two cells of F_{J(S)}(Γ) is decidable.

*Proof.*
1. Equality is decidable. A cell of F_{J(S)}(Γ) is a generated tuple (Response 2): a T₁₂ coordinate, which is decidable by (K52), plus the values in the separating algebras. The tagged and marked algebras are finite in each degree. For the whole prime family, Response 2 reduces equality of two given terms to finitely many exceptional primes plus one common answer, a finite linear-algebra computation.
2. Paths have bounded length. J(S) has the T₁₂ signature and a subset of T₁₂'s equations. So the projection to T₁₂ sends a J(S)-path to a T₁₂-path with the same letters, and the positive grading of (K45)/(K50) bounds its length by the gradings of the endpoints.
3. Steps are finite. At fixed boundaries the contextual alphabet is finite (K50).
4. Steps 1–3 make reachability decidable. This abstract step is machine-checked in `src/CaTTExp/Join/BoundedReach.agda` (`Reach.Bounded.reach?`, no postulates). ∎

The cyclic tables for composite N (needed to switch off the D_{d,p} with p | d) need the same linear algebra over ℤ/N. That step is not written out, so those switches are not in the default J yet (§1.6).

### 1.6 Decision (superseded 2026-11-20 by §1.7)

**Original decision: the kernel's side condition computes in J (L2). Each catalogued law is a per-development switch, and T₁₂ is the setting with every switch on.**

Reasons:
1. **L2 against L1.** Both satisfy requirements 1–5, both are decidable, and both have the same rule form. J is strictly more general: the tagged model and the M_q are J models but not T₁₂ models. Standard 4 then picks J unless there is a concrete reason to specialize. No derivation is known yet that needs a catalogued law. The switches keep T₁₂ one setting away, and imports run upwards.
2. **L2 against L3.** Hypotheses do not reach the side condition, so a declared law brings an unbounded tower of coherence declarations (example (c)). Switches put the law into the oracle, where all its coherences come for free.
3. **L2 against L4.** L4 is the right target if it exists, but its admissibility and decidability are unknown. Per standard 1, that is a question to ask, not a reason to drop it: it is now the main question of `conjectures/outbox/lax-interchange-every-dimension-r8.md` (answered 2026-11-20, `conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`: on pasting diagrams a least admissible theory V exists and is decidable; see its Verification section). If it has a positive answer with a decidable side condition, it replaces J.
4. **Stability.** A newly discovered independent law joins the catalogue as a new switch. A development records its switch set, so later additions to the catalogue do not change what it checked against.

**What would overturn this.**
- A positive answer to the least-theory question in r8 (then use that theory).
- A proof that some catalogued law is needed for a core construction, such as cones over composites at inner levels or the directed Eckmann–Hilton of E7 (then that switch defaults to on, with the reason recorded here).
- A failure of the combined J construction under the in-house re-check (then fall back to the largest verified sub-selection).

**Open items (owner DSGN unless stated).**
- (J-chk) Re-check in-house that all separating algebras can be combined at once with exact quotients. Response 2 asserts this ("use (K51)'s argument with all the selected tests at once") and it was verified at construction level.
- (Q-vis) Which catalogued laws are visible on free objects of finite pasting diagrams? A law that is not visible does not change the kernel, so it need not be a switch.
- (ZN) Decidability for the composite-N tables (§1.5), then add the D_{d,p} switches to the default.
- Outbox: the least-theory question, merged into `outbox/lax-interchange-every-dimension-r8.md` as its main question (standard 11); answered 2026-11-20 (`answered/lax-interchange-every-dimension-r8-2026-11-20.md`), follow-up `answered/lax-interchange-every-dimension-r9-2026-11-20.md` (answered 2026-11-20), next follow-up `outbox/lax-interchange-every-dimension-r10.md`.
- LCORE's uniform rule takes the switch set as a parameter (message sent to LCORE).

### 1.7 Revised decision (2026-11-20, after the r8 answers)

The r8 answers (`conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, verified) meet overturn condition 1 in the form the kernel uses.
- **L4 exists.** Let B be the forced base and V = B + the round-5 guarded equations. Then V is admissible, F_V(Γ) = F_B(Γ), and F_V(Γ) maps generator-preservingly to F_E(Γ) for every admissible E. So on every finite pasting diagram, a directed cell or an equality exists in F_V(Γ) iff it exists in every admissible theory.
- **Q-vis.** The right split R and the inner composite-crossing law are visible on pasting diagrams. Every L_p and D_{d,p} is invisible, because every chronological 3-endomorphism in a free object on a pasting diagram is an identity.
- **Q1(a) is negative** (no least or minimal law set on arbitrary algebras). The kernel never sees those algebras, so this does not matter for the decision.

**Decision. The side condition computes in V. The switches are the visible laws: the inner composite-crossing law and R. A setting S means the side condition computes in V + S.**

Reasons:
- V is the most general possible choice, not just the most general known one. Every judgement it derives is derivable in every admissible theory, so a V development is sound in the models of every admissible theory. That is L4, and it removes reason 3 of §1.6.
- The catalogue shrinks to the visible laws. L_p and D_{d,p} do not change the kernel, so they are not switches, and (ZN) is moot.
- (J-chk) leaves the critical path, because J is no longer the default.
- L1 and L3 lose for the same reasons as before.

**Lemma V-dec.** For every finite pasting diagram Γ, equality and reachability in F_V(Γ) are decidable.

*Proof.* The proof follows Lemma J-dec.
1. V has the T₁₂ signature and a subset of T₁₂'s equations. So the identity on letters sends a V-path to a T₁₂-path with the same letters, and the positive gradings of (K45)/(K50) bound its length by the endpoint gradings.
2. At fixed boundaries the contextual alphabet is finite (K50).
3. Equality of two V-terms of the same weight is decidable. A derivation of the equality uses only defining pairs between terms of that same weight, since the gradings are conserved by every equation of V ⊆ T₁₂. So equality is connectivity in the finite graph whose vertices are the terms of that weight at those boundaries and whose edges are one-step applications of V's defining pairs. That graph is finite by step 2.
4. Steps 1–3 satisfy the hypotheses of `Reach.Bounded.reach?` (`src/CaTTExp/Join/BoundedReach.agda`), so reachability is decidable. ∎

**Switch settings V + S.** T₁₂ is admissible and contains both visible laws, so the all-on setting has T₁₂'s pasting profile. Whether V + {R} and V + {inner law} are admissible on their own was asked in r9 and not answered; it is asked again in `outbox/lax-interchange-every-dimension-r10.md` (Q2). Until that is answered, the only settings offered are none (V) and all (T₁₂). Imports still run upwards: F_V(Γ) maps generator-preservingly into F_T₁₂(Γ), and `Transport` applies.

**What would overturn this.**
- A proof that a visible law is needed for a core construction. That law's setting then becomes the default for that construction's development.
- Admissibility answers in r10 that open up the intermediate settings.

**Open items.**
- (FV) An explicit description of F_V(Γ) and of what T₁₂ adds. **Answered 2026-11-20 by r9 (verified):** q : F_V(Γ) → F_T₁₂(Γ) is finite-to-one in every degree, and a V-cell is a T₁₂ normal word with decorated faces and a rank-selected word index (K65). Fibres are unbounded (2^{m−1} on suspended strips) but all those identifications come from R (K66). Visibility of pasting-diagram laws is decidable, so (Q-vis) is decidable for any proposed switch (K67). A closed-form description of the decorations is asked in r10 Q3.
- Whether F_J = F_V on pasting diagrams. This is now only of interest for comparison.
- Admissibility of V + R and of V + inner law separately (r10 Q2).
- LCORE: point the default setting at V (message sent).

---

## 2. Context checking: homotopicality of bases

### 2.1 Where homotopicality entered

The weighted-limit line concluded that "the right hypothesis of the weighted-limit rule is homotopical (Free(Γ) ≃ F_n(Γ))" (`limits-metatheory.md` §9.3). The finite-presentation theorems for totals (B14: `conjectures/outbox/fibration-presentations-characterization-r4.md` items 3–5, 10, 12, 13, 16) assume a homotopical base. The evidence for the hypothesis was item 8: over the bubble σ : 1_x ⇒ 1_x the strict base is F(σ) = B²ℕ, which groupoidifies to K(ℤ,2), so even the terminal weight has no finite presentation.

### 2.2 Facts

- Bubble-free is necessary in every dimension (Theorem N). In dimension 2 it is also sufficient, but **bubble-freeness is itself undecidable for 2-polygraphs** (`answered/homotopy-polygraphs-2026-11-19.md` item 3). So "bubble-free 2-skeleton" is an exact criterion but not a decidable one.
- In dimension 3 bubble-freeness is not sufficient: the positive 3-polygraph A : α₀g ⇛ α₁g, B : gβ₀ ⇛ gβ₁ has a circle fibre.
- Homotopicality is co-r.e.-complete on positive 3-polygraphs (HPOL r4). So **no sound and complete r.e. certificate system for homotopicality exists**. Any witness system certifies a strictly smaller r.e. class, and no extension of it can close the gap.
- Decidable sufficient classes are known: pasting contexts and their Gray tensors; graphs (all 1-polygraphs, loops allowed); positive 2-polygraphs (Chanavat Cor. 3.39); the partition test; positive-to-one polygraphs and their duals; positive 3-polygraphs without matching idle overlaps (RC r6 Response 5); orientals of finite semisimplicial sets (Chanavat Thm 3.35); typing into a fixed finite catalogue of certified templates. All of these except the catalogue are closed under suspension.

### 2.3 The options

**C1. Pasting contexts only.** Decidable and homotopical.
- Rules out: equalizers (the parallel pair x ⇉ y is not a pasting context), pullbacks (the cospan x → z ← y), loops, and every 2-dimensional base that is not a pasting diagram. Too narrow for ordinary mathematics.

**C2. A fixed decidable class.** Take the union of the §2.2 classes.
- Derives: limits over graphs (equalizers, pullbacks, loops), over positive 2-computads such as μ : a·a ⇒ a, and over orientals.
- Rules out: correctly, the bubble and the RC r6 3-polygraph. Wrongly, every homotopical base outside the class. By the co-r.e.-completeness result, no decidable class can avoid this.
- Pitfall: an "exact" test such as bubble-freeness is undecidable in dimension 2 and unsound in dimension 3. The RC r6 polygraph is positive and bubble-free but not homotopical, so a bubble-freeness test would accept it.

**C3. Explicit witnesses.** An inductive judgement Γ ⊢hpol in the style of ⊢ps. Its base rules are the §2.2 classes and its closure rules are proved closure theorems: suspension; adjoining 1-generators in dimension 2; adjoining fresh globes along two vertices (fibration r2, vertex-attachment lemma).
- Checking is decidable when the derivation is given or syntax-directed. The rules fit the CaTT aesthetic.
- Necessarily incomplete (§2.2), but extensible as closure theorems arrive.

**C4. Read bases weakly, and check nothing.** A CaTT diagram over Γ is a context morphism out of Γ, which is a functor out of the free *weak* ω-category Free(Γ), never out of F(Γ). Interpret every base as Free(Γ). Homotopicality is then not a premise of any kernel rule.
- Derives: limits over every finite context, including the bubble and the RC r6 polygraph, with their weak meaning. Over a homotopical base this meaning agrees with the strict one.
- Rules out: nothing a CaTT diagram can express. A functor out of the strict F(σ) = B²ℕ is not expressible in CaTT anyway.
- Decidable: there is no check to decide. Weight presentations still carry their certificates (B14), and those are checked as before.
- Item 8 does not apply: over Free(σ) the total of the terminal weight is Free(σ) itself, presented by σ.

### 2.4 Worked examples

| Base | C1 | C2 | C3 | C4 |
|---|---|---|---|---|
| parallel pair x ⇉ y (equalizers) | rejected | accepted (graph) | accepted (graph axiom) | accepted; fast path |
| μ : a·a ⇒ a on a loop a | rejected | accepted (positive 2-polygraph) | accepted | accepted; fast path |
| bubble σ : 1_x ⇒ 1_x | rejected | rejected | rejected | accepted; weak meaning, over a resolution |
| RC r6: A : α₀g ⇛ α₁g, B : gβ₀ ⇛ gβ₁ | rejected | rejected by the no-matching test (the overlap on g matches); a bubble-freeness test would wrongly accept | rejected unless some closure rule covers it | accepted, over a resolution |
| HPOL r4 semi-Thue family G(T,w,v) | rejected | rejected | homotopical members are accepted only by a lucky closure derivation, and no r.e. system accepts all of them | accepted, over a resolution |

### 2.5 Proposition W (finite presentations over arbitrary bases)

C4 needs the B14 theorems for bases Free(Γ) with Γ arbitrary.

**Proposition W.** Let Γ be any finite n-polygraph, and T : Free(Γ) → ω a coherent weight with values Free(Π_b)[W_b⁻¹], dim Π_b ≤ m. Then ∫T has a finite marked presentation of dimension ≤ n + m.

*Proof attempt.*
1. **Resolution of the base.** Free(Γ) is an iterated homotopy pushout of globes along their boundaries. That holds by definition of Free, not by homotopicality. Run the bounded-model calculus of `answered/fibration-presentations-characterization-r2-2026-11-19.md` §2 on it: homotopy pushouts give dimension max{b, c, a+1}, and globe attachments keep dimension. This gives a finite complicial model K of dimension ≤ n. The conversion L_n (same answer, §2.3) gives a finite polygraph Γ′ that is **homotopical** (oriental of a semisimplicial set, Chanavat Thm 3.35), of dimension ≤ n, and a finite set W′ of its generators with Free(Γ′)[W′⁻¹] ≃ Free(Γ).
2. **Pull back and present.** Let ℓ : F(Γ′) → Free(Γ) be the localisation. Then T∘ℓ is a coherent weight over the homotopical base Γ′. Item 13 (the uniform presentation Ω) gives (Ω′, S′) with Free(Ω′)[S′⁻¹] ≃ ∫(T∘ℓ) and dim Ω′ ≤ n + m.
3. **Localise the total.** Let Ŵ be the cartesian-marked generators z_{w,x} of Ω′ for w ∈ W′ and x a source-fibre vertex. These are the lifts of W′. By Lemma Loc-total below, ∫T ≃ ∫(T∘ℓ)[Ŵ⁻¹] = Free(Ω′)[(S′ ∪ Ŵ)⁻¹]. Localising does not add generators, so the dimension stays ≤ n + m. ∎ (modulo Lemma Loc-total)

**Lemma Loc-total** (remaining step). For B an (∞,ω)-category, S a set of cells, ℓ : B → B[S⁻¹] and T : B[S⁻¹] → ω, the map ∫(T∘ℓ) → ∫T exhibits ∫T as the localisation of ∫(T∘ℓ) at the cartesian lifts of S.

*Attempt.*
- B[S⁻¹] is the pushout of B along marked trivialisations ∐ D_{k+1}^t → ∐ D_k^♭ (Loubaton Def. 3.2.1.6, Prop. 3.2.1.7; (Loc), `limits-metatheory.md` §9.2).
- Pullback along the left cartesian fibration ∫T → B[S⁻¹]^♯ preserves colimits (Loubaton Thm 3.2.3.15, as in item 3). This must be used in its marked form, for the marked trivialisation; that check in Loubaton is still to be done.
- So ∫T is the pushout of ∫(T∘ℓ) along the totals over the trivialisations, and it remains to show that the total over D_{k+1}^t → D_k^♭ is the localisation at the lifts of the top cell.
- Over a globe, the weight is determined by a k-cell of ω whose top part is invertible. Its total over D_{k+1} is a Gray cylinder on the fibre, and inverting the lifted top cell gives the total over D_k^♭ by item 2 (tensor-localisation). Item 2 is stated for X[S⁻¹] ⊗ I. The globe case needs it for D_k ⊗ fibre, which is the same lemma with the factors exchanged.

This last step was posed as Question 3 of the fibration-presentations r4 prompt. **Proved 2026-11-20** (`conjectures/answered/fibration-presentations-characterization-r4-2026-11-20.md`, Response 1, verified). The globe case D_k → D_{k−1} follows from the suspension classification and the tensor-localisation lemma, and the general case from a homotopy pushout of globe trivialisations with Loubaton's pullback–colimit theorem. Steps 1–3 are confirmed, so Proposition W holds unconditionally.

**Effectiveness.** The resolution (Γ′, W′) is found by a terminating search, because a resolution always exists. A finite equivalence certificate (item 15) is checkable. So the kernel can accept any finite base. The certificate becomes trivial (Γ′ = Γ, W′ = ∅) exactly when Γ carries a ⊢hpol derivation. That is C3's role under C4: an optimisation that keeps presentations small, never a gate.

### 2.6 Machine check: what the encoded rules actually require

`src/CaTTExp/Lim/WeakBase.agda` (type-checked locally, Agda 2.6.3, no postulates):
- Mikhail's cone recognition rules, with both the printed and the strict linearity test, **accept the lax cone over the bubble** σ : 1_x ⇒ 1_x. Its projection over σ is p_σ : ρ⁻¹_q ⇛ ρ⁻¹_q ; (q ▷ σ), where ρ⁻¹_q is the cone cell over the coherence 1_x. So the encoded rules accept a cone over a non-homotopical base, and nothing in them requires homotopicality. That is one instance, not a general theorem, and these rules are known to be permissive (Defects D5). An independent reviewer checked that the recognisers reject the reversed orientation and the σ-free cell.
- The **specified** cone construction `coneC` (the repaired rule, `Repaired.agda`) is undefined on the bubble. It is also undefined on the well-formed positive base μ : a·a ⇒ a, which is homotopical by Chanavat Cor. 3.39 (a prose citation, not machine-checked). The reason is that `projTy` (Repaired.agda) only handles generators of dimension ≤ 2 whose boundaries are variables. So the restriction in the encoded repaired rule is "variable boundaries and dimension ≤ 2", not homotopicality. The Agda checks the two instances; the general statement is read off `projTy`.
- Extending `coneC` to term boundaries is the cone-over-coherences problem N^cone (B5, CONE). That problem, not homotopicality, is what the limit rules depend on. It is dimension 1 proved, dimension 2 from RC(2). This finding goes to CONE and LIM-F.

### 2.7 Decision

**Bases are read weakly (C4). No kernel rule checks homotopicality. Homotopicality enters only as the optional certified judgement ⊢hpol (C3, with the decidable §2.2 classes as base rules). Its only effect is to let a weight presentation use the base itself instead of a resolution.**

Reasons:
1. **It removes an unfixable incompleteness.** Every option that checks homotopicality (C1–C3) rejects homotopical bases, and the co-r.e.-completeness result shows that no extension can close that gap. C4 accepts every base.
2. **It matches what CaTT diagrams mean.** Diagrams are maps out of Free(Γ). The strict-base reading behind §9.3 came from the bubble example read through F(σ), which CaTT cannot express.
3. **It is the most general option** (standard 4), it is decidable (nothing to decide), and it adds no rule forms. ⊢hpol is an inductive judgement in the style of ⊢ps, and it sits off the critical path.
4. **What it needs is already owned or posed.** Lemma Loc-total (§2.5) is posed. N^cone (§2.6) is owned by CONE and the RC line.

**What would overturn this.** A counterexample to Proposition W, meaning a weight over a non-homotopical base with no finite presentation. Then the fallback is C3 as a gate for presentation-based weights only, with C4 kept for everything else.

**Open items.**
- ~~Lemma Loc-total.~~ Proved 2026-11-20 (fibration r4 Response 1, verified); Proposition W is unconditional.
- Extend `coneC` to term boundaries (N^cone). Owner CONE/LIM-F, notified.
- Encode ⊢hpol with the §2.2 base classes. Owner DSGN (Loc-total is now proved). **Started 2026-11-20:** `src/CaTTExp/Lim/Hpol.agda` decides the first base rule, positive path 2-polygraphs: objects, 1-cells between objects, and 2-cells between nonempty composites of 1-cell variables. Their homotopicality is cited from Chanavat Cor. 3.39, not formalised. It accepts the parallel pair and μ : a·a ⇒ a, and rejects the bubble. Still to add: pasting contexts, orientals, positive-to-one, the no-matching positive 3-polygraphs, top weight ≤ 2, and closure under suspension. The homotopy-polygraphs r5 answer adds decidable classes: finite strict cells with abelian tests, top weight ≤ 2 in any dimension, and one-resource semaphores.
- B24 (HPOL) is no longer on the critical path of any kernel rule. It remains a research item, and its decidable classes (r5 Q3) feed ⊢hpol.
