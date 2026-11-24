# Completeness of the lax side condition (ledger S30)

Soundness of the lax side condition is established: a yes from SC is a yes in strict Gray models (Agda, `Strict/Soundness.agda`) and in oriented (∞,ω)-categories (`pseudo-vs-gray.md` §3.6, Theorem 2). This note asks the converse: does the kernel derive every coherence that the weak model has?

## 0. Summary

| Result | Status |
|---|---|
| The literal single-head reading ("a type over Δ with a unique inhabitant in the free model, using every variable, is accepted by one coh over Δ") is **false** for two-tier L. Witness: βα → βα₂ over ΣD¹ ∨ ΣD¹, §2. | **[Agda]** `Gray/CohCaseGap.agda` (`gap`, `no-single`) |
| The right reading is **fullness**: every cell of the free model on a pasting context Δ, between images of terms, is the image of a derivable term of that type (§1). For plain CaTT it holds (§3.1). | stated here; P: **[proved]** from RC in strong-Steiner contexts |
| For two-tier L, fullness is **equivalent to EL in pasting contexts** (relative coherence for image equality). The proof of EL in `surface-conservativity.md` Prop. 4.3 does **not** apply to two-tier L as the rule is written: its one step is exactly the coherence that `gap` rejects. | **[Agda]** for the failing step; equivalence **[proved on paper]** |
| **Repair candidate L^V**: keep the operation case; make the coherence case Finster–Mimram's shape plus image equality (`Var(t : A) = Var(Δ)` and ⟦t⟧ = ⟦u⟧). It is strictly more general than two-tier L, and sound: in the strict model the new coherence case is (B) itself; in (∞,ω) models Theorem 2's argument never used full support. | rule and coherence-case soundness lemma **[Agda]** `Gray/CohCaseVar.agda` (`cohV-top`); full strict soundness **[not rebuilt]**; (∞,ω) **[argued]** |
| **Theorem 1 (fullness for L^V)**: every cell of 𝔉(Δ) between term images is the image of a derivable L^V term of exactly that type. So on pasting contexts L^V derives every coherence of the free oriented (∞,ω)-category, and no further generalization of the side condition can add a derivable type. | **[proved on paper]**, modulo cited literature and Lemma 1.3 of `surface-conservativity.md` (argued) |
| The **current** two-tier rule (Gray-full coherence case) is **also complete** (EL and FULL hold in every pasting context), non-constructively: it follows from the verified directed arity lifting of relative-coherence r9 Response 1 (free two-tier algebras on pasting arities are trivial fibrations over 𝔉), re-checked against the §2 shape by the S19 thread on 2026-11-24. So graySide and L^V derive the same types; L^V gives EL by one explicit coherence. | **[verified researcher result]**, §3.3; the in-house attempt of §5 is superseded; the outbox prompt is retired |
| Uniform L relative to oriented (∞,ω) models: **incomplete by design** (inner interchange is directed). Relative to its own free objects F_{V+S}: open, with the same coherence-case issue plus S11. | §6 |

## 1. Statements

Fix a kernel 𝕂 ∈ {P, two-tier L, uniform L in setting S} and its free objects F(Δ) (ν(λΔ), 𝔉(Δ), F_{V+S}(Δ)), with the strict interpretation ⟦−⟧ of `spec/02` §2.1.

**The semantic link.** For a pasting context Δ, the free oriented (∞,ω)-category on Δ has discrete mapping spaces and is 𝔉(Δ). This is hypothesis (D)–(F) of `pseudo-vs-gray.md` Theorem 2, discharged there from Campion (arXiv 2311.00205, Ex. 3.2, Cor. 3.5), Chanavat (arXiv 2603.22242, Thm 3.29) and Gepner–Haugseng (arXiv 1312.3178, §2.5). For P the analogue is that the free (∞,ω)-category on a globular pasting diagram is ν(λΔ). So "a coherence that exists canonically in the weak model" over Δ is a cell of F(Δ), and since the space is discrete every such cell is canonical.

**Definition (single-head completeness, SH).** If 𝔉(Δ) has exactly one cell ⟦t⟧ → ⟦u⟧ and it uses every variable of Δ, then SC(Δ, t →_A u) holds.

**Definition (fullness, FULL).** For every pasting context Δ, every kernel type B = (t →_A u) over Δ and every cell c : ⟦t⟧ → ⟦u⟧ of F(Δ), there is a derivable Δ ⊢ w : B with ⟦w⟧ = c.

**Definition (EL in pasting contexts, `surface-conservativity.md` Def. 2.3).** For parallel kernel terms u, u′ : A over a pasting context Δ with ⟦u⟧ = ⟦u′⟧, there are derivable e : u → u′ and e′ : u′ → u with identity images.

SH is the naive reading of "every canonical weak cell is accepted". FULL is the meaningful one: the kernel can name every cell the model has, at exactly the type it has in the model. In P the two agree up to restriction to a sub-pasting context, because a cell of ν(λΔ) that uses every variable has full Steiner support, so it is τ_Δ or an identity on a full cell (`spec/02` Lemma 2.2.1). In 𝔉 the Steiner basis is tuples of variables, so "uses every variable" and "has full Gray support" come apart, and SH fails (§2).

## 2. The single-head reading fails for two-tier L

Δ = ΣD¹ ∨ ΣD¹ (α : f ⇒ f′ : x → y, β : g ⇒ g′ : y → z). Let

- βα = (f◁β) ; (α▷g′), the source of the interchanger;
- βα₂ = (1_{f;g} ; (f◁β)) ; (α▷g′).

`Gray/CohCaseGap.agda` checks:
1. both are derivable at type f;g → f′;g′;
2. their closed supports are equal and miss the top generator α⊗β;
3. `graySide` rejects coh_{Δ, βα → βα₂} and its reverse (`gap`, `gap⁻`), so `no-single`: no term at all has that head;
4. a composite of coherences of that type is derivable: the unitor λ : L ⇛ 1;L (coherence case over D², one hom) whiskered by R (`e-wf`).

By (B) and item 2 the two images are equal (paper step, not stated in Agda). In 𝔉(Δ) the type βα → βα₂ has exactly one inhabitant, the identity (a strict ω-category of a loop-free Steiner complex has no non-identity endo-cells), and it uses every variable. No pasting sub-context of Δ contains all variables used. So SH fails, while FULL holds for this type by item 4.

There are also operation-like failures of SH: in the cube Δ = (ΣD¹)^{∨3}, the 2-dimensional composite of the whiskered interchangers α⊗β⊗h and f′⊗g′⊗γ is the unique cell between its boundary paths (a second positive 2-chain with the same boundary would differ by a multiple of the boundary sphere of the cube, and is not positive), it uses every variable, and it is not τ_Δ. It is derivable as a composite. **[argued]**, not machine-checked.

## 3. FULL reduces to surjectivity plus EL

### 3.1 The pieces

**Lemma S (surjectivity onto cells, any rule containing two-tier L's operation case and single-hom CaTT).** Every cell of 𝔉(Δ) is ⟦s⟧ for some derivable term s.

*Proof.* Induction on dimension, and inside a dimension on the length of a composite.
- 𝔉(Δ)(aᵢ, aⱼ) = ν(Kᵢⱼ), Kᵢⱼ = λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ, strong Steiner (Ara–Maltsiniotis, Prop. 4.13 for λΘ and closure of strong Steiner complexes under ⊗, AM §A). By Steiner (2004, "Omega-categories and chain complexes", ν(K) is generated by the atoms of a loop-free unital basis) every cell is an iterated composite of atoms and identities.
- *Atoms.* A basis element is b = θᵢ₊₁ ⊗ … ⊗ θⱼ, θₖ a variable of Θₖ of dimension dₖ. Let D_b = ΣD^{dᵢ₊₁} ∨ … ∨ ΣD^{dⱼ} and σ_b : D_b → Δ the variable substitution sending each disc to θₖ (in a globular pasting diagram the boundary of a variable is variables). 𝔉(σ_b) sends τ_{D_b} = ⟨top⟩ ⊗ … ⊗ ⟨top⟩ to ⟨θᵢ₊₁⟩ ⊗ … ⊗ ⟨θⱼ⟩ = ⟨b⟩. By the induction hypothesis on dimension, applied in D_b, and the type lemma below, there are terms s, s′ over D_b of one type with images ∂^∓τ_{D_b}. Then coh_{D_b, s → s′} is in the operation case (supports are those of ∂^∓τ, dimension is dim τ), and coh_{D_b, s → s′}[σ_b] has image ⟨b⟩.
- *Composites.* c₁ #ₖ c₂ inside a hom is composition along (k+1)-cells of 𝔉. Its CaTT head lives over D^{a+1} ∨_{k+1} D^{b+1} = Σ(D^a ∨ₖ D^b), a single hom, where two-tier L's rule is Finster–Mimram's (`Gray/SingleHom.agda`), so the composite head is accepted and its image is c₁ #ₖ c₂. Matching the syntactic boundaries of the two argument terms is done with KC (below) at the lower levels.
- *Identities* are coherence-case cohs over discs.
- *Type lemma.* For a cell c of dimension n there is a well-formed kernel type B with ⟦B⟧ = the boundary of c: build it bottom-up from terms for the iterated boundaries (induction hypothesis), retyped by KC so that each level is typed over the previous one. ∎

**KC (kernel conversion, `surface-conservativity.md` §3.1–3.2).** If Δ ⊢ s : B and B′ is well formed with ⟦B′⟧ = ⟦B⟧, then Δ ⊢ s′ : B′ with ⟦s′⟧ = ⟦s⟧. Theorem B there derives KC in dimension n from EL in dimensions < n, using whiskering heads over linear trees. Those heads are accepted by two-tier L (`Surface/WhiskerGray`), hence by any rule containing it. Theorem B also uses (E) for image equality, Lemma 1.3 there (argued).

**Proposition 3.1.** For any rule 𝕂 containing two-tier L, FULL for 𝕂 ⟺ EL for 𝕂 in pasting contexts.

*Proof.* ⇐: take s from Lemma S with ⟦s⟧ = c; ⟦type of s⟧ = ⟦B⟧ because interpretations respect boundaries (`Strict/Soundness.sound-tm`); KC retypes s to B. ⇒: apply FULL to the type u → u′ and the identity cell, and to u′ → u. ∎

### 3.2 Plain CaTT

EL for P with image equality in ν is RC, which holds in every strong-Steiner context in every dimension (verified researcher answers, `surface-conservativity.md` §4.1), in particular in every pasting context. Lemma S holds for ν with the same proof (no tensors). So FULL holds for P. This is the precise form of "for CaTT, completeness holds".

### 3.3 Two-tier L as written

`surface-conservativity.md` Prop. 4.3 proves EL in a pasting context by one coherence-case coh over Var(u). For two-tier L that coh needs full *Gray* support of the image, which fails whenever the image is a composite such as ∂⁻τ (§2, item 3). So Prop. 4.3's single-head proof does not apply to two-tier L. The pair in §2 is still connected by a composite (item 4), so this was a gap in the proof, not a counterexample.

**Resolved (2026-11-24).** EL, hence FULL, does hold for two-tier L as written. relative-coherence r9 Response 1 (verified 2026-11-20; `conjectures/answered/relative-coherence-all-dimensions-r9-2026-11-20.md`) proves that free two-tier L-algebras on pasting arities are globular trivial fibrations over 𝔉, for the full-Gray-support rule. Lifting the identity between equal images gives EL. The S19 thread re-checked on 2026-11-24 (addendum in that file) that the proof never lifts a single head at a non-total cell such as βα → βα₂: it only lifts generic heads, at total cells and identities on them. The result is **non-constructive** (no explicit connecting terms, no size bound) and rests on the ∞-categorical inputs of Responses 15–16, checked at the level of the stated constructions. Consequence: graySide and L^V derive exactly the same types (L^V ⊇ graySide, and every L^V head's type is inhabited in 𝔉, hence in graySide by FULL). L^V's gain is that EL is witnessed by one explicit coherence (Theorem 1), not a non-constructive lift.

## 4. The repair candidate L^V

**Rule.** Operation case unchanged. Coherence case:

```
cohCaseV(Δ, t →_A u)  :⟺  ⟦t⟧ = ⟦u⟧ in 𝔉(Δ)  and  Var(t : A) = Var(u : A) = Var(Δ)
```

Var is measured as the variables occurring in the closed Gray support, which by Lemma 4.2 below is Finster–Mimram's syntactic Var on derivable terms. Image equality is decided by closed supports (the closure comparison `sameDownClosure`, which is what (B) is stated for, rather than graySide's generator form `sameDown`): by (B) (`Strict/Recon.b-supp`), two cells of one dimension with equal closed supports are equal. The Agda form is `Gray/CohCaseVar.agda`:

```
cohCaseV Θ A t u = endsOK Θ A ∧ sameDownClosure Θ (supp t A) (supp u A)
                              ∧ varFull Θ (supp t A) ∧ varFull Θ (supp u A)
```

Its decision cost is that of the existing closure comparison; on a single hom it is CaTT's coherence case exactly (there Var = support, `pseudo-vs-gray.md` §3.6(3)).

**Comparison with two-tier L as written.**

| | two-tier L (Gray-full coherence case) | L^V (Var-full coherence case) |
|---|---|---|
| shape of the coherence case | "both sides use the whole Gray unfolding" | Finster–Mimram's Var condition, plus equal images |
| on one hom | CaTT | CaTT (identical) |
| contains the other | — | yes [paper]: Gray-full support uses every variable, and full supports are equal |
| βα → βα₂ (§2) | rejected; only a composite of two cohs | one coh |
| directed interchanger, no reverse, no horizontal composite | yes | yes (`CohCaseVar` evaluation checks: the reverse and the horizontal composite are still rejected) |
| strict soundness | Agda (`Strict/Soundness`) | coherence-case step: `cohV-top` (Agda), which is (B) applied to t and u, replaces `coh-top`; the support function `topS` must also dispatch on cohCaseV instead of cohCase (it is defined mutually with graySide's cohCase, so as written it gives βα → βα₂ the operation-case image); the full typing instance is not rebuilt in Agda |
| (∞,ω) soundness | Theorem 2 | same proof: coherence-case cohs go to the invertible cells that (D) provides between parallel cells with equal strict image; full support is not used there |
| EL / FULL in pasting contexts | holds, non-constructively (§3.3) | **proved** (Theorem 1) |
| derivable types | equal to L^V's (FULL holds for both, §3.3) | maximal: by Theorem 1 no further rule on pasting contexts adds a derivable type that is sound in 𝔉 |

**Lemma 4.2 (Var is a pasting sub-context, and is the projected support).** Let u : A be derivable in L^V over a pasting context Δ = ΣΘ₁ ∨ … ∨ ΣΘₙ. Then Var(u : A) equals the set of variables occurring in the closed Gray support of ⟦u⟧ and its boundaries, and it is a pasting sub-context ΣP_{i+1} ∨ … ∨ ΣP_j.

*Proof.* [proved on paper]
- *Projections.* The terminal maps λΘₗ → λD⁰ are strict and the Gray tensor is functorial with unit λD⁰, so for each k there is a strict functor πₖ : ν(Kᵢⱼ) → ν(λΘₖ). It sends ⟨θᵢ₊₁ ⊗ … ⊗ θⱼ⟩ to ⟨θₖ⟩ if every other entry is 0-dimensional and to an identity on a face of ⟨θₖ⟩ otherwise; in both cases its support is ↓θₖ. By functoriality of supports ((C), `pseudo-vs-gray.md` §3.6, from Hadzihasanovic 2404.07273), supp(πₖ x) is the k-th projection of supp(x).
- *Cells of ν(λΘ) have pasting supports.* Induction on Θ = ΣΘ′₁ ∨ … ∨ ΣΘ′ₘ: the hom of ν(λΘ) from the l-th to the r-th object is the product of the ν(λΘ′ₖ), so a cell is a tuple of cells and its support is ΣQₗ₊₁ ∨ … ∨ ΣQᵣ with each Qₖ the support of a cell of ν(λΘ′ₖ) (a point for a 0-cell). So the projected support of a cell of 𝔉(Δ) is a pasting sub-context.
- *Var = projected support,* by induction on u. "⊆ Var" holds because ⟦u⟧ is built from the images of u's variables. "⊇": a variable is its own atom; for coh_{Δ′, s → s′}[σ], the cell c of the head has projected support all of Var(Δ′), in the operation case because τ_{Δ′} contains every variable, and in the coherence case by the varFull clause of the rule. Then (C) and the induction hypothesis on σ give the claim. (For Gray-full two-tier L the same induction works with full support in place of varFull.) ∎

**Theorem 1 (fullness for L^V).** FULL holds for L^V in every pasting context, in every dimension.

*Proof.* By Proposition 3.1 it suffices to prove EL. Let u, u′ : A be parallel L^V terms over Δ with ⟦u⟧ = ⟦u′⟧. By Lemma 4.2, Var(u : A) = Var(u′ : A) =: Δ′ is a pasting sub-context, since both are the projected support of the same cell. Strengthening (variables outside Δ′ do not occur, and side conditions are checked on heads' own contexts) gives ũ, ũ′ over Δ′ with u = ũ[ι], u′ = ũ′[ι]. The inclusion ι induces 𝔉(Δ′) → 𝔉(Δ), injective on cells because K(Δ′) is a sub-complex spanned by a boundary-closed set of basis elements and cells are tables of chains. So ⟦ũ⟧ = ⟦ũ′⟧, and Var(ũ : A) = Var(Δ′). Hence coh_{Δ′, ũ → ũ′} and its reverse pass cohCaseV; their images are identities, and substituting ι gives e and e′. ∎

**What Theorem 1 rests on.** Steiner's generation by atoms and the closure of strong Steiner complexes under ⊗ (literature); (B) and (C) (literature, (B) also Agda); strengthening (standard for CaTT-style systems, not formalized here); Lemma 1.3 of `surface-conservativity.md` for image equality (argued); Theorem B (paper, and Agda over the whiskering interface).

**Consequence for the walkthrough question.** With L^V, the strict free object loses nothing on pasting contexts: every cell of the free oriented (∞,ω)-category on Δ (which is 𝔉(Δ)) is named by a derivable term, at its exact type. The weak reading of general contexts (chapter 4) is a separate matter: there EL already fails at dimension 5 on the suspended scalar (`surface-conservativity.md` §4.3), so no such statement is expected off pasting contexts.

## 5. Is two-tier L as written already complete? (attempt, superseded by §3.3)

By Proposition 3.1 the question is EL for graySide in pasting contexts. A coherence-case coh over Var(u) works whenever ⟦u⟧ has full Gray support in Var(u). Otherwise ⟦u⟧ is a proper composite in a hom of 𝔉, and the connection has to be assembled from smaller cohs, as in §2 item 4.

Route tried: show every term is connected to a canonical one by induction on the term, using (i) congruence of a head in each argument separately (functorialisation in one locally maximal variable: Δ↑{v} is a pasting context and its total cell τ_{Δ↑v} goes from τ_Δ[v] composed with lower functorialised boundary cells to τ_Δ[v′] composed with others, so it is an operation-case coh of two-tier L), with KC to cancel the lower cells, and (ii) an insertion-type step relating coh_H[σ] to a single head over the inserted context when σ(v) is itself a coh. Step (i) goes through on paper for operation-case heads. Step (ii) needs the image of the composite head to have full Gray support in the inserted context, which holds when the inner head is an operation case and fails, again, when the inner head is a coherence case whose image is not Gray-full. So the induction closes only modulo the same obstruction. The prompt written for this (`conjectures/retired/gray-catt-relative-coherence.md`) was retired unsent on 2026-11-24: its Q1 and Q2 are answered by r9 Response 1 (§3.3). A constructive version is part of the open "search-free construction" item of the r9/r10 line.

## 6. Uniform L

- **Against oriented (∞,ω) models: incomplete, by design.** Over Σ(ΣD¹ ∨ ΣD¹) (`spec/02` §2.3 Example (c)) the interchanger inside an object is an identity in 𝔉, so the reverse cell exists canonically in every oriented (∞,ω)-category, and every setting of V + S rejects it. Uniform L targets models whose objects are themselves lax, so this is the intended gap, not a defect. Its completeness has to be measured against F_{V+S}.
- **Against its own free objects.** SH relative to all admissible theories is the leastness of V (`spec/02` §2.3: a cell exists in F_V(Γ) iff it exists in every admissible theory). FULL relative to F_{V+S} needs:
  1. surjectivity: every cell of F_{V+S}(Δ) is the image of a term. The operation case only produces *designated* lifts (`spec/02` §2.2). Other lifts, such as the loop H on Σ[2] ∨ Σ[2], must arise as composites of whiskered elementary interchangers; plausible, not proved;
  2. EL in pasting contexts, which needs Lemma V (ii) of `surface-conservativity.md` (injectivity of F_{V+S}(Δ′) → F_{V+S}(Δ), open) and runs into the same coherence-case issue: the spec's coherence case asks for π-full support, so the Var-shaped repair of §4 would be needed there too;
  3. S11: if two lifts of one head are not connected (E13: H and 1_w are not), FULL still holds as long as both are images of terms; it is the *single* head that cannot name both.
- **Status:** open, owned by this thread (S30).

## 7. Open items

| Item | Owner |
|---|---|
| SPEC: adopt L^V's coherence case for two-tier L (and the Var-shaped analogue for V + S), or keep the Gray-full form. Evidence in §4: strictly more general, CaTT-shaped, sound, and complete on pasting contexts. | **done**: adopted for every row in PR #591 (spec thread) |
| ~~EL for graySide in pasting contexts~~ **holds** (§3.3, r9 Response 1, non-constructive); a constructive version is the r9/r10 search-free construction item | — |
| Full strict-soundness typing instance for graySideV in Agda (parameterise `topS`/`supp` and `Strict/Soundness` by the coherence-case predicate, then use `cohV-top`) | S30 |
| Lemma 4.2 and strengthening in Agda | S30 |
| `surface-conservativity.md` Prop. 4.3 / Corollary 4.4: proof does not apply to two-tier L as written; holds for L^V by Theorem 1 | S19 owner (notified) |
| Uniform L: surjectivity onto F_{V+S}, EL, Var-shaped coherence case | S30 |
