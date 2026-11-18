# Open issues

*The single list of known open items for the project (project standard 10). First compiled 2026-11-18 by a sweep of every file in `notes/`, `notes/conjectures/`, `src/`, and the project-folder survey `catt-survey.md`.*

## How to use this file

- **Every thread that finds an open item adds a row here, and every thread that closes one moves it to "Closed" with a pointer to the result.** Do this in the same PR as the finding.
- **Status** is one of:
  - **in progress**: an active thread has this item on its checklist;
  - **out to researcher**: sent to an external researcher (internal attempts still continue, per standard 2);
  - **unowned**: nobody is working on it. Under standard 0 the coordinator starts a thread for it.
  - **blocked**: cannot advance until another item closes. The blocker is named, and adjacent work is listed.
- **Owner** is a thread, named by title and id. A thread that has finished its task does not own anything: items it left behind are listed as unowned, with the finished thread named as "former area" for context.
- IDs are stable. Do not renumber; retire an ID by moving its row to "Closed".

Thread ids used below:

| Short name | Thread | State at compilation |
|---|---|---|
| LIM-F | "Formalize repaired limit rules in Agda" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbP3GDJGVPBANChSP67cBmyV` | active |
| LCORE | "Formalize the lax-interchange core in Agda" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbC9dAXJgu5wyAG12hYRW5nG` | active |
| LMETA | "Develop limit-rule metatheory and limits over L" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbD4wzRQd7hPxxsf6RGVQJT9` | active (added 2026-11-18) |
| CONE | "Define canonical cone constructions" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbLYSyekUerAT8DpXZFBCtrp` | active (added 2026-11-18) |
| AGDA0 | core Agda / survey thread `cmsg_018pe2CvdFGDdsWgn8Tjn5gbFVBaKE936jSAppjVSszHLX` | idle (awaiting review) |
| IHOM | internal hom and Gray tensor `cmsg_018pe2CvdFGDdsWgn8Tjn5gbEUSN4QBuzbPj9ExdY9DTuF` | done |
| FREE | free ω-categories as objects `cmsg_018pe2CvdFGDdsWgn8Tjn5gb7LiQb6yikB1xjtm14CaXMG` | done |
| LIMN | limits and representables notes `cmsg_018pe2CvdFGDdsWgn8Tjn5gb6zYn9ewLrPvp4YL8AfJHKN` | done |
| PVG | pseudo vs Gray-style core `cmsg_018pe2CvdFGDdsWgn8Tjn5gbKP6yrjEAYBPgxDoAc2gq3F` | done |
| NGC | "Prove naturality and Gray context conjectures" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbS5xgSTBGTmnfCd1k5DprsS` | active |
| LIT | literature / conjecture verification `cmsg_018pe2CvdFGDdsWgn8Tjn5gbKdRdpEiQuvAuEvTAURBqhf` | done |
| MARK | "Design invertibility markings for lax core" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbQhMQC4fsaRjMJypHXq4ZVv` | active |
| FOBJ | "Develop free-object rules" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbUxJhXTzhRJEWFkLNmH5acC` | active |
| CONV | "Clean up recalled claims and conventions" `cmsg_018pe2CvdFGDdsWgn8Tjn5gb1EVjAv52BfW2yu9RrGQaFH` | active (E11) |
| OMATH | "Extend toward ordinary mathematics" `cmsg_018pe2CvdFGDdsWgn8Tjn5gb372mKMHNCxwDtepUMwRs3d` | done (PR #35) |

---

## A. Core CaTT metatheory (Agda)

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| A1 | **Substitution admissibility** for core CaTT: Δ ⊢ σ : Γ and Γ ⊢ t : A give Δ ⊢ t[σ] : A[σ]. The main missing metatheorem; every extension needs it. | `agda-sketch-findings.md` "Not yet done", "Suggested next steps" | **done** (PR #20: `CaTTExp.Subst`, for every side condition, plain CaTT included) | LCORE |
| A2 | **Checker completeness**: the certified checker is sound (returns derivations) but not proved complete. | `agda-sketch-findings.md` | unowned | former area AGDA0 |
| A3 | **Any semantics in Agda**, starting with interpretation in strict ω-categories (or the strict free category on a graph). | `agda-sketch-findings.md` | unowned (needs A1) | former area AGDA0 |
| A4 | **Non-derivability of functoriality of ⟦_⟧** (finding 2) is argued informally. Make it rigorous: soundness of the strict-model interpretation, then the separating model. | `agda-sketch-findings.md` finding 2 | unowned (needs A1, A3) | former area AGDA0 |

## B. Limit rules (CaTT_lim and its repair)

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| B1 | Encode Mikhail's printed Def. 4.15 rules; machine-check the `ctrf` τCond rejection of the intended source of m_f, the `x′ : X` renaming defect, and the non-canonical cone. | `conjectures/catt-lim-pseudo-vs-gray.md` verification 4; `lax-colimit-of-point.md` | in progress | LIM-F |
| B2 | Machine-check the collapse: unchanged `uni` forces cone-morphism cells and ambient 3-cells invertible. | `limits-representables.md` §10.1, §8 item 5 | in progress | LIM-F |
| B3 | Encode the **repaired rules** (specified shapes, certified comparison cells as marked declarations); check the intended examples and that the collapse no longer derives. | `limits-representables.md` §4.1, §10.1 | in progress | LIM-F |
| B4 | **Substitution, composition and soundness** for the marked-declaration version of the repaired rules. | `catt-lim-pseudo-vs-gray.md` open (a); `limits-metatheory.md` §6 | **Substitution admissibility proved.** Composition of transfors over generators of dimension ≤ 1 given explicitly (what B9 and the researcher's step 2 use). Composition over higher generators reduces to B5/C1. Soundness under P reduces to Loubaton (ω is lax complete, Prop. 4.2.3.8; Cor. 4.2.3.18) plus B5 and E11. Remaining parts: in progress | LMETA (higher-generator composition with CONE/C1) |
| B5 | **Specified (canonical) cone, cocone and `ctrf` construction for arbitrary Γ**, checked against the Steiner Gray product. Subsumes Mikhail's Conj. 3.6 (cones over arbitrary contexts) for the cases needed. | `limits-representables.md` §4.1(1), §10.3; `free-objects.md` §7.1 item 3; `gray-contexts-in-catt.md` §6.2a | unowned | former area LIMN |
| B6 | **Free object = lax colimit of the point, syntactically**: for the specified cocone C(Γ), is the constant-diagram instance equivalent to the suspension (c:⋆, Σ_{⊤,c}Γ)? Then Step B (higher cocone morphisms vs transfors). If it holds, R-A's rules become admissible. | `conjectures/lax-colimit-of-point.md` "What remains"; `limits-representables.md` §5.2, §10.3 | unowned (needs B5) | former area LIMN |
| B7 | **Restate the limit rules over the Gray (L) core.** | `limits-metatheory.md` §5; `conjectures/oriented-lax-limits.md` (verified) | **Done as a design.** P and L share the specified shapes and one horn-form filler rule. They differ only in the core and in which transfor comparisons are certified: under P, those over all positive-dimensional diagram generators; under L, only those over *marked* diagram generators (coherent marking, as the verified Problem 3 correction requires). L needs only operation-case cohs over `ΣDᵃ ∨ ΣDᵇ`. Sound in the strict model for every finite computad (Theorem A); the arrow case is sound in ∞Cat (researcher). Remaining: the shapes (B5), the comparison of filler rules with the weighted limit for general Γ in (∞,ω) (B17), and the Agda encoding (B15) | CONE (shapes), LMETA (B17), LIM-F (B15) |
| B14 | **Finite fibration test for weights**: a finite, generator-level criterion on π : Ψ → Γ implying the lifting schema (19). | `conjectures/finite-fibration-test.md`; `limits-metatheory.md` §9 | **Proved for set-valued weights over graphs** (the test is: π is a discrete opfibration of graphs, and it is complete there). The category-valued case is posed with a candidate FT₂ and a localisation lemma (Loc), ready to send to a researcher. In progress | LMETA |
| B15 | Agda: encode the **horn form** of the filler rule (one `uni` over `Horn_n`, shared by P and L, with marks as the switch). Under LCORE's core, check that the forced-invertibility derivation is blocked, i.e. that no inverse of the interchanger is derivable. | `limits-metatheory.md` §5.3, §10 | in progress | LIM-F |
| B16 | Agda: machine-check the all-dimensions collapse (B9) for d = 4 in the **intended** rules (selector and copy fixed); the printed rules cannot run it. | `limits-metatheory.md` §3; `catt-lim-formalization.md` D1/D3 | in progress | LIM-F |
| B17 | **(∞,ω) Theorem A for general Γ**: in ∞Cat as an oriented category, the cell-attachment limit (one Gray-cotensor pullback per generator) represents the cone category presented by the specified shapes. The ingredients (mixed currying and pullback preservation) are verified in the B8 response for the arrow, and general existence holds (Heine Lemma 3.69). What is open is matching the specified syntactic shapes to the weight. | `limits-metatheory.md` §1.5 | in progress | LMETA |

## C. Free objects and representables

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| C1 | **Conjecture N** (naturality of coherences for up-closed variable sets of depth ≥ 2), which gives Γ ⊗ Dᵏ for every context. Settled: every term of dimension ≤ 2, any pasting context, any up-closed Y (NGC, 2026-11-18: Theorem A, relative 2-coherence for every context, plus the reduction N ⇐ RC; extends the verified ladder theorem). Open: dimension ≥ 3, reduced to RC(n) on cylinder contexts; smallest cases a 3-dim coherence over one arrow (RC(3) on the lax square) and the 3-dim unitor over the 2-disc. | `conjectures/naturality-arbitrary-depth.md` §7 and "Verification"; `free-objects.md` §7.1 | out to researcher (prompt: `conjectures/outbox/naturality-arbitrary-depth.md`); internal attempts in progress | NGC |
| C1b | **Run the ladder construction mechanically**: build the associator's naturality 3-cell over a fully selected chain (conjecture file, response §3) in a CaTT checker, to confirm the paper proof's generated terms typecheck. | `naturality-arbitrary-depth.md` "Verification", last bullet | in progress | NGC |
| C2 | Check that iterated N-cylinders coincide with **Mikhail's `gray` contexts**, and that the cone terms p_t obtained from naturality terms satisfy Mikhail's free-variable condition. | `free-objects.md` §7.1 items 2–3 | in progress (Mikhail's printed rules extracted; layer structure matches) | NGC |
| C3 | **Decomposition of diagrams**: Diag((Γ, x : A), C) ≃ Diag(Γ, C) ×_{Diag(∂D, C)} Diag(D, C) at every dimension. **Proved** as an isomorphism onto the strict pullback at every k, given the cylinder contexts (unconditional for globular Γ): `free-objects-proofs.md` Thm 3. Strict ≃ pseudo pullback proved at level 0 (Lemma 4) and in the strict model at all levels. Remaining: (C3a) compatibility with Diag's composition, once D3 fixes it; (C3b) boundary restriction is an ω-equifibration at all levels, syntactically; (C3c) higher-depth cylinders = C1. | `free-objects.md` §3.3, §7.2.1; `free-objects-proofs.md` §2 | in progress (C3a adjacent work, C3b) | FOBJ |
| C4 | **Lifts of invertible cells are invertible** under the LIFT schema. **Proved on paper** (`free-objects-proofs.md` §1, coinduction; rule-level form of FHM 2406.13240 Prop. 3.1.7). Agda proof done (`Free/Reflect.agda`), in independent review. | `free-objects.md` §7.2.2 | in progress (Agda review) | FOBJ |
| C5 | **Conservativity**: cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms. Non-collapse half **proved under P** in the strict cartesian model (`free-objects-proofs.md` Prop. 5). Weak statement **reduced** to BMS + DFMRV (known) and a sound weak interpretation (E11). Remaining: (C5a) weak half, blocked on E11; (C5b) strict half under L, needs the strict Gray model of the L core (adjacent to E2). | `free-objects.md` §2.6, §5, §7.2.3; `free-objects-proofs.md` §5 | C5a blocked on E11; C5b in progress (adjacent work while C5a waits) | FOBJ |
| C7 | Agda: postulate A1 (⟦Γ⟧ + LIFT) and A2 (INIT/ATTACH + LIFT) side by side and derive A1's LIFT₀ from A2; formalise the cylinder contexts Q↑Y and machine-check the depth-2 left-unitor case and the C1 next checks. Paper side of the derivation done (`free-objects-proofs.md` §3), with the finding that it needs naturality terms of Γ's boundary terms already at dimension 0. Done in Agda (in review): cylinder contexts for globular Γ, the depth-2 left-unitor naturality cell. Remaining: A1/A2 side by side with the A2 ⇒ A1 LIFT₀ derivation; the associator case (shared with C1b). | `free-objects.md` §6 | in progress | FOBJ |
| C8 | Agda targets from the limits notes: (1) elements elaboration R-C → §5.1 is well typed; (2) constant substitutions `(c:⋆) ⊢ !_Γ : Γ` exist; (3) cone contexts exist for pasting-scheme diagrams; (4) strict-model check of `laxcolim(const 1) ≅ Free(Γ)` for D¹, D², the loop and the composable pair; (6) formalise the free-on-graph trivial-fibration argument. (Target 5 is B2.) | `limits-representables.md` §8 | (3), (4), (6) in progress; (1), (2) unowned | FOBJ for (3), (4), (6); former area LIMN for (1), (2) |

## D. Gray contexts, internal hom and closed structure

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| D1 | **G(2) uniqueness bookkeeping gap**: check that the cell built from exchange coherences has exactly the type t → t′. Closes Gray generators of dimension 4. | `conjectures/gray-contexts-in-catt.md` §3.3 | closed (proved by Theorem A, NGC 2026-11-18; independently by a researcher, verified 2026-11-18 in `gray-contexts-in-catt.md`) | NGC |
| D2 | **G(n), n ≥ 3, and G-alg**: translate Chanavat's contractible subdivision poset into substituted CaTT coherences (conservativity of molecular coh). Ready to send to a researcher. Researcher response (verified 2026-11-18) confirms G(2) and existence in G(3). It also shows that "(∀n G(n)) ⇒ conservativity" is not established: molecular coherences of dimension above the molecule need a higher filling statement (RC-shaped). | `gray-contexts-in-catt.md` §3.4 and verification §4 | existence in G(3) proved (hence Gray generators of dim ≤ 4 typed); G(n≥3) uniqueness and G-alg reduced to RC(n); out to researcher (prompt: `conjectures/outbox/gray-contexts.md`) | NGC |
| D3 | **Mikhail's Gray rules for every context and every n**: existence with an explicit formula, and presentation of the Steiner Gray tensor. Must be a specified construction, since the raw judgment is permissive. | `gray-contexts-in-catt.md` §6 | in progress (explicit construction via iterated top-layer cylinders for dim Γ ≤ 2, all n) | NGC |
| D3b | **Defects of Mikhail's printed Gray rules** (verified researcher result, 2026-11-18). (i) The source-side selector must use `y ∝ σ(p)`, and copies must be renamed; otherwise the walking arrow has no Gray derivation. This matches LIM-F's machine-checked D3/D4. (ii) New: the linearity predicate `∝` (Def. 3.1, OP case) does not enforce multiplicity one; e.g. ℓ ∝ c(c(ℓ,ℓ),ℓ). Any repaired cone, gray or ctrf rule needs a multiplicity-one linearity test. | `conjectures/gray-contexts-in-catt.md` verification §5; `catt-lim-formalization.md` | (i) done in Agda (LIM-F `fixed` variant); (ii) unowned, natural owner LIM-F (its `Conditions.agda` implements the printed ∝) | LIM-F |
| D3a | **Re-check "G implies N"** (`gray-contexts-in-catt.md` intro, README, `naturality-arbitrary-depth.md` §8). The verified review found §8's whole-cylinder fullness argument false for composition constructors (for c = f ∗₀ g, a_c and b_c miss f↑, g↑). The implication needs a separate argument for composites and a support theorem for the boundary lifts. | `naturality-arbitrary-depth.md` §8 (corrected) and "Verification" | closed by `relative-coherence.md` §4.3: N ⇐ RC proved directly (no G needed); conservativity (statement (b) of the G file) ⇒ N holds for full Y via the support lemma, using the composition side condition for composites | NGC |
| D4 | Side conditions of the Gray tensor of contexts: **G2** functoriality in substitutions (needed for nat-Δ), **G4** associativity up to coherence (may need CaTT_sua), **G5** whether linearity (x ∝ t) is needed. | `internal-hom.md` §4.2 | in progress (G2 for D¹ by structural induction; G5 not needed; G4 reduced to RC) | NGC |
| D5 | Agda targets for Gray contexts: Γ ⊗ D¹ for Γ a pasting scheme as a function on syntax, proved well formed; G3 (wedges); vertical composition of lax transformations as a substitution, recording which non-ps composites are needed; D¹ ⊗ D¹ ⊗ D¹ under both orientations. | `internal-hom.md` §7 | unowned (LCORE's Gray-cube test is the L-side analogue, not this) | former area IHOM |
| D6 | If molecular coh is adopted: re-examine **pruning, insertion and rehydration** for molecules. | `internal-hom.md` §4.3(ii) | unowned (conditional on D2 outcome) | former area IHOM |
| D7 | **Gray tensor of arbitrary objects** B ⊗ C as a colimit of ⟦x ⊗ y⟧, then check the Gray tensor's universal property. Needed for lax currying with both factors arbitrary. | `internal-hom.md` §6; `pseudo-vs-gray.md` §4.3 | blocked on general colimits (B12); adjacent work: state the target universal property | former area IHOM |
| D8 | **Dualities under L**: which reversals stay symmetries and which swap lax/oplax (PR #3 experiment 3), (the duality formulas for ⊗, including the even one, are now verified: AM Props. A.20–A.23, `conventions.md` §3.3; odd and even duals swap lax/oplax, the total dual does not); design an orientation-parameterised kernel so proofs transfer. | `pseudo-vs-gray.md` R5; `internal-hom.md` §5.6 | unowned | former area PVG |
| D9 | **PL1**: pin down the faithfulness lemma (free unit-free biclosed monoidal category → free non-symmetric linearly distributive category); write out steps 2–3 of the 1-dimensional theorem carefully. | `conjectures/planar-pasting-types.md` §2, §7 | unowned | former area IHOM |
| D10 | **Units** for planar pasting types: a separate criterion. | `planar-pasting-types.md` §3 | unowned | former area IHOM |
| D11 | **PL-ω**: a class of Gray pasting types; first test, a criterion whose 2-cells are exactly the lax naturality cells of evaluation Fun^lax(B, C) ⊗ B → C, without inverses; compare Gepner–Heine's LMor/RMor. | `planar-pasting-types.md` §4, §7 | unowned | former area IHOM |
| D12 | **Mimram's CCCaTT**: work out the higher-dimensional cartesian pasting criterion (unpublished), and re-check the rule details against the PDF (they were read via a summary). | `internal-hom.md` §5.7 | unowned | former area IHOM |

## E. Lax-interchange (L) core

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| E1 | Implement Steiner chains and the Gray unfolding; checker with decidability; **supp = Var on a single hom** (conservativity over CaTT). | `pseudo-vs-gray.md` §7.1 step 2, §3.6 Thm 1(3) | side condition + checker done (`Gray/Support.agda`); conservativity checked on PR #4 examples, general proof in progress | LCORE |
| E2 | Two-object cases mechanically: D²∨D² (interchanger one way only), D¹∨D² (whiskering), D²∨D²∨D² (cube 4-cell from ps-terms); validate against the strict AM model. | `pseudo-vs-gray.md` §7.1 step 3, §3.4 | done at support level (`Gray/Examples.agda`, `Gray/Cube.agda`, `agda-gray-findings.md`); chain-level validation against the strict AM model not done | LCORE |
| E3 | Substitution admissibility and **non-derivability of the reverse interchanger** for L. | `pseudo-vs-gray.md` §3.6 Thm 1(2) | substitution done (PR #20); reverse interchanger *coh* proved underivable; reverse *type* uninhabited needs strict-model soundness with (B) as hypothesis, not started | LCORE |
| E4 | **Invertibility markings.** Designed 2026-11-18 in `invertibility-markings.md` §1–2: judgments `inv` and `ps` (pseudo is one-sided in execution order), recursive `ps*` = corrected C1″, marked declarations, propagation rules (INV-fac, INV-obj, PS-fac, OP-inv/ps, OBJ-k for `grpd_k` objects), all **proved sound** in oriented (∞,ω)-categories and the strict model; "interchanger with an invertible factor is invertible" is now proved. Agda encoding done 2026-11-18 (`Gray/Marks*.agda`: rules, §1.6 examples by evaluation, substitution preserves marks proved; see `agda-gray-findings.md`). Remaining: DES destructors in Agda; whether ICaTT's rec is admissible (low priority). Revised 2026-11-18 after G1 check: (PS-fac)/(OP-ps) now take ps* premises, proved from C1′ alone; (OBJ-k) reproved via Campion's τₙ-reflected tensor; top-only pseudo is Conj. 2.2′ (open). | `invertibility-markings.md` | in progress (DES in Agda) | MARK |
| E5 | **Generality ordering.** Semantic half of P ≈ L + "every mixed cell invertible" **proved** (`invertibility-markings.md` Thm 3.1, via n-ary gray-vs-cartesian and a sub-operad argument). Open: syntactic half, Conjecture 3.2 (conservative translation CaTT → L⁺), reduced to a relative coherence lemma; uniform ⊂ two-tier part needs E6. Thm 3.1 step 1 reproved without assuming localisations are stable under ⊗ (uses corrected C1″ and Gepner–Heine 4.1.9). | `invertibility-markings.md` §3 | in progress | MARK |
| E6 | **Uniform L construction**: free structure with directed interchange at every level (requirements 1–5), corrected boundary-adjusted reading. Literal version impossible (verified). New 2026-11-18: no single directed complex, or hom-wise family of them, can present the answer (`invertibility-markings.md` §7, Obs. 7.1); a description must be an iterated tower. Researcher-ready prompt: `conjectures/outbox/directed-interchange-every-level.md` (Q1–Q4). Internal next step: the first genuinely uniform case ΣD² ∨ ΣD² up to dimension 5 (Q2). Q2 worked to 𝒦-dimension 4: exactly two extra generators χ₁, χ₂ beyond the Steiner ones (`invertibility-markings.md` §7); dimension 5 depends on the open coherence choice. | `conjectures/strict-lax-interchange-at-every-level.md`; `conjectures/outbox/directed-interchange-every-level.md`; `invertibility-markings.md` §7 | in progress; prompt ready to send | MARK |
| E7 | Uniform L experiments: re-run E1–E2 for Σ(D¹ ∨ D¹) *inside* an object (directed Eckmann–Hilton); check that the "ordinary ω-category" marking (`ord`, `invertibility-markings.md` §1.5) restores exactly plain CaTT. | `pseudo-vs-gray.md` §7.1 step 7 | blocked on E6; adjacent marking design done (E4 §1.5) | MARK |
| E8 | **Representables and lax homs over L.** Hom rule and R-A restated over L (`invertibility-markings.md` §4); semantics proved from the literature; elimination (reading Gray-shaped components off a native lax cell) derivable. **Finding:** G1 does not disappear under L: introducing a lax cell from components needs a Gray-shaped context. Posed as Conjecture CT, `conjectures/canonical-gray-terms.md`. CT results: strict CT false for D¹⊗D¹⊗D¹ (layered terms), true for D²⊗D¹; CT′ holds through dimension 4 (via RC(2), `relative-coherence.md`); beyond, CT′ ⇔ RC for loop-free contexts. | `invertibility-markings.md` §4; `pseudo-vs-gray.md` §4.2 | in progress (CT open) | MARK |
| E9 | **Cost.** The [conj] is **false for explicit supports** (term of size O(n) with support 3ⁿ; source chains of size C(n,k)). Restated as E9′: is the side condition decidable in time polynomial in shared term size? Open; timing experiment on n-fold wedges asked of LCORE. | `invertibility-markings.md` §5 | in progress | MARK; LCORE for measurement |
| E10 | **Surface defaults**: settled 2026-11-18 by worked counts (`invertibility-markings.md` §6): kernel has no defaults; surface marks only at declarations (M1), derives the rest; default horizontal composite is the ∂⁻-layering. Remaining: the uniform-L `ord` default, which waits on E6/E7. | `invertibility-markings.md` §6 | blocked on E6 for the uniform part only | MARK |
| E11 | **Long-term semantics gaps**, now written out in `semantics-gaps.md`: (S1) a homotopy theory on GM weak ω-categories / CaTT models and a comparison with (∞,ω)-categories (no model structure on weak ω-categories exists yet; Fujii–Hoshino–Maehara 2025 call it future work); (S2) strict-substitution (coherent-choice) models presenting a given (∞,ω)-category or oriented one; (S3) which (∞,ω) notion (inductive, coinductive, flagged) is intended; (S4) whether the cited results hold there; Gray-coherator models of L. **Settled in passing:** strict ω-Cat with lax transformations (AM's ∞-Cat_lax) is a strict model of two-tier L, by Theorem 1 of `pseudo-vs-gray.md` §3.6; P's strict model has only strict 2-cells. | `semantics-gaps.md`; `pseudo-vs-gray.md` §3.6 caveat, §5.4 | in progress | CONV |

## F. Ordinary mathematics and further extensions

Design note: `ordinary-math.md` (added 2026-11-18 by OMATH). Rows F1–F6 are its proposals; the lettered rows are what it leaves open.

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| F1 | **Dependent eliminators.** Families are maps, sections are maps with an invertible cell; dependent elimination is *derived* from non-dependent universal properties (AGS argument). Proved on paper: dependent elimination for shapes ⟦Γ⟧ from R-A (Thm 4.1); induction for N from recursion (Thm 4.3); recursion for N := Hom_{⟦L⟧}(x,x) from two general principles, G (lax colimits are Grothendieck constructions) and DJ (comma objects are free cocartesian fibrations) (Thm 4.4). Three routes compared (§4.5). | `ordinary-math.md` §4 | proposal written (PR #35) | — ; open parts F1a, F1b |
| F1a | Write G and DJ as rules with their `uni`-style higher levels; check the uniqueness step of Thm 4.4 in detail. | `ordinary-math.md` §4.6 | unowned | former area OMATH |
| F1b | Tree-shaped inductive objects, and lists over an arbitrary object, in route III (no ℕ-specific rule). | `ordinary-math.md` §4.7 | unowned | former area OMATH |
| F2 | **Discreteness filler tactic** for graph contexts: proved on paper (Thm 3.1), implemented with certified output and checked examples in `src/CaTTExp/GraphFiller*.agda`. | `ordinary-math.md` §3 | done (paper + certified instances) | — |
| F2a | Agda: totality of the graph filler (every parallel pair with the same path gets a filler). | `ordinary-math.md` §3.4 | blocked on A1; adjacent: more instances | former area OMATH |
| F2b | Filler for **globular** contexts (Thm 3.2, semantic proof done): implement strict normal forms (labelled trees) and the lift. | `ordinary-math.md` §3.3 | unowned | former area OMATH |
| F3 | **h-level discipline**: judgment `C trunc n` with T-fill/T-inv and closure rules; T-lim and T-hom proved (sketch); base rules T-graph and T-loc sound by `free-on-graph.md` and Dwyer–Kan. Gives `N trunc 0`, `ℤ trunc 0`, automatic coherence for set-level algebra. | `ordinary-math.md` §2 | proposal written (PR #35) | — ; open parts F3b, F3c |
| F3b | Non-derivability of T-graph from R-A (argued, Prop. 2.5), or a Hedberg-style derivation of `N trunc 0`. | `ordinary-math.md` §2.3 | unowned | former area OMATH |
| F3c | Full proofs of T-lim and T-hom against the specified `ctrf` construction. | `ordinary-math.md` §2.3 | blocked on B5; adjacent: F3b | former area OMATH |
| F4 | **The integers**: ℤ := Hom(x,x) in ⟦L⟧ localised at s (a finite pushout). ℤ ≃ ℤ_disc proved from Dwyer–Kan 1980 Prop. 2.3 and `free-on-graph.md`. General quotients need a set-truncation rule (proposed, §5.3). | `ordinary-math.md` §5 | done for ℤ; quotients proposed | — ; open parts F4a, F4b |
| F4a | Filler tactic for localised graphs (reduced words). | `ordinary-math.md` §5.1 | unowned | former area OMATH |
| F4b | Effectiveness of quotients under the Trunc rule. | `ordinary-math.md` §5.3 | unowned | former area OMATH |
| F5 | **Object-indexed colimits**: diagrams as cocartesian fibrations; lax colimit = total space, pseudo colimit = finite localisation, left Kan extension = comma + localisation; sequential colimits = pseudo coequaliser of the total family. No new rule. Colimits *inside* an object are declared structure (§6.4). First test case carried over from C9: the Θ-density rule, B as the colimit of its pasting-diagram elements, which gives extensionality of transformations for arbitrary domains (now expressible as an ambient colimit over the cocartesian fibration of elements, §6.1; not yet worked out, F5b). | `ordinary-math.md` §6 | proposal written | — ; open part F5a |
| F5b | Θ-density as an instance of §6.1: write B as the localised Grothendieck construction of its disk elements and derive extensionality of transformations (C9). | `ordinary-math.md` §6.1; `limits-representables.md` §7 | unowned | former area OMATH |
| F5a | Check §6.1–6.3 against the (∞,ω) sources (Gepner–Heine, Loubaton) at statement level, not abstracts. | `ordinary-math.md` §6 | unowned | former area OMATH |
| F6 | **Lax functors**: out of finite loop-free shapes, maps out of the glued orientals P^lax (no new rule); lax-functor variables via a directed refinement-coherence rule. | `ordinary-math.md` §7 | proposal written | — ; open part F6a |
| F6a | `conjectures/lax-functor-refinement.md`: are lax-functor comparison cells decided by Steiner supports of the oriental complex? Ready to send to a researcher. | `conjectures/lax-functor-refinement.md` | unowned (ready to send) | former area OMATH |
| F7 | Write out **ICaTT's and Rice's (CaTT_su/sua) rules in full** from the papers; the survey paraphrased them. Needed by E4, by the walking-equivalence quotients of `limits-representables.md` §6.1, and by ⟦J⟧ in F4 and F5. | `catt-survey.md` "Possible next steps" | unowned | — |
| F8 | **Exponentials of sets** (function sets ℕ → ℕ, sequences for ℝ): an internal hom restricted to `trunc 0` targets, e.g. Mimram's cartesian closed rules (D12) for sets. | `ordinary-math.md` §6.5 | unowned | — |
| F9 | **Formalise the h-level and recursion rules** (standard 9): encode `trunc` and T-fill and check the ring example of §2.5; encode recursion over a parameter context. Needs syntax for operations "over a context applied to a substitution" beyond `coh`. | `ordinary-math.md` §8 | unowned | former area OMATH |

## G. Verification debt

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| G4 | **Re-check the [recall] and abstract-level claims of `ordinary-math.md`** (added after G1 closed): Riehl–Verity's characterisation of cocartesian fibrations and fibrational Yoneda; Lurie HTT 3.3.4.3; Gepner–Haugseng–Nikolaus free fibrations; T-coprod; homs of orientals are Gray cubes; and DK 1980 Prop. 2.3 against a clean copy (read here through an OCR scan). | `ordinary-math.md` | unowned | former area OMATH |

---

## Out to external researchers

**Paste-ready prompts live in `conjectures/outbox/`.** Each is standalone: definitions, what is proved, numbered questions with the smallest open case first.
- `outbox/naturality-arbitrary-depth.md` (C1)
- `outbox/gray-contexts.md` (D2)


**Responses received, awaiting verification:** none. (`naturality-arbitrary-depth.md` and `strict-lax-interchange-at-every-level.md` were verified 2026-11-18.)

**Ready to send** (self-contained, literature-checked): `outbox/lax-functor-refinement.md` (F6a; paste as is). `outbox/finite-fibration-test.md` (B14; paste as is). `outbox/directed-interchange-every-level.md` (E6; paste as is). `canonical-gray-terms.md` (CT, from E8). `gray-contexts-in-catt.md` G and §6 (D1–D3). The remaining open parts of N (C1) and the corrected uniform-L question (E6) are now restated in their files and can be sent again.

## Closed

Kept briefly for orientation; details are in the linked files.

- B9 (collapse in all dimensions ≥ 3): **proved**, `limits-metatheory.md` §3. A d-cell is the top f-component of a (d−2)-transfor over 1_Y, and `uni` at level d−1 inverts it. Only the full-support coherence rule is needed, not BM Prop. 35. Machine check: B16.
- B10 (models of the intended CaTT_lim rules): **classified**, `limits-metatheory.md` §4. They are exactly the (∞,ω)-categories with cells of dimension ≥ 3 invertible that have finite GHL/Loubaton lax limits (e.g. Cat), conditional on B5 and E11.
- B11 (horn judgment): **done as a design**, `limits-metatheory.md` §5.3. Agda encoding: B15.
- B12 (one schema): **done as a design**, `limits-metatheory.md` §8. The alternating variance is a condition on the index (B14), not on the cone schema. Under L, colimit transfors take the diagram index first. Full duality is not a symmetry of L: it reverses the interchanger (passed to D8).
- B13 (Hom_⊖): **identified at the generator level under P**. Loubaton's ⊖ is Gray in the first transfor direction and cartesian above it (Construction 3.1.2.15, Prop. 3.1.2.17), which is the repaired table. Under L the cone categories are the full Gray homs (Theorem A, strict). Full identification of the shapes: B5. See `limits-metatheory.md` §7.
- `free-on-graph.md`: solved (researcher, verified). N ≃ ℕ_disc semantically.
- `weighted-as-partially-lax-omega.md`: solved in Loubaton's model (researcher, verified). Leaves B12–B14.
- `gray-vs-cartesian.md`: C1, C1′ proved; C1″ without "locally full" (researcher, verified). Leaves E4's recursive marking.
- `catt-lim-pseudo-vs-gray.md`: answered (researcher, verified). Leaves B1–B4, B9, B10.
- `lax-colimit-of-point.md`: semantic claim solved; arbitrary-derivation syntactic form refuted. Leaves B5, B6.
- `free-infinity-gray-of-pasting-diagrams.md`: solved in the literature. Discharges (D)–(F) of `pseudo-vs-gray.md` §3.6.
- `steiner-support-determines-cells.md`: solved for the needed case (Hadzihasanovic). Discharges (A)–(C). The general case (G3) was proved 2026-11-18.
- `limits-representables.md` §10.2: marking needs no closure condition.
- **G1** (re-check every [recall] claim): done 2026-11-18 by CONV. All ~35 claims in `internal-hom.md`, `pseudo-vs-gray.md`, `limits-representables.md`, `free-objects.md`, `invertibility-markings.md`, the conjecture files and the project-folder survey are now cited with their place, proved, or corrected. Corrections: Steiner's tensor statement is for *strongly* loop-free bases; Al-Agl–Steiner, not Crans, introduced the ω-Gray tensor, and no "pseudo version" was found; BMOSV's naturality is only for depth ≤ 1, so `internal-hom.md` §4.1's Γ ⊗ D¹ on composite terms depends on Conjecture N (C1); ω-sesquicategories are not Markakis's setting; the dimension-2 lax-limit theory is Cat-weighted, not Gray-weighted; no model structure on weak ω-categories exists to cite (now in E11).
- **G2** (one place for conventions): done 2026-11-18 by CONV, `conventions.md`. L's factor order (execution order, L = AM's ∞-Cat_lax), names checked against AM, JFS, Haugseng, Loubaton and Gepner–Heine (all agree with Bénabou's lax), Mikhail's transformations are Bénabou-oplax, the naming hazard between `internal-hom.md`'s lax hom (AM's Hom_oplax) and L's hom 𝒦(Θ, C) (AM's Hom_lax), and the duality table. Fixed one inconsistent factor order in `invertibility-markings.md` §4.2.
- **G3** (Steiner support lemma for arbitrary Steiner complexes): done 2026-11-18 by CONV. Problems 1–3 of `conjectures/steiner-support-determines-cells.md` hold for every Steiner complex. Problem 1 is Forest Lemma 3.4.5 / Campbell Prop. 2.20. Problem 2 follows from a lifting lemma (an element of the support of x lies in the top chain of some cell parallel to the relevant boundary of x) plus Forest Lemma 3.4.11 / Campbell Prop. 2.23. Problem 3 follows from Supp(x #_k y) = Supp(x) ∪ Supp(y). The convexity step (Conv) is no longer needed.
- C6 (weak model of ATTACH): answered in `free-objects-proofs.md` §4. Strict and (∞,ω) models justified; the algebraic-weak gap is part of E11.
- C9 (density): answered in `free-objects-proofs.md` §6. Disks are not dense, Θ is; the Θ-density rule is recorded under F5.
- B8 (oriented lax limits): answered by a researcher, verified 2026-11-18. Problems 1–2 yes; Problem 3 false as stated, true with coherent marking (full Hom_C(b,a)). The internal R11 re-derivation is done by the response's §1. Leaves B7.
- C1a (verify the response on N): done 2026-11-18. Ladder theorem verified; Lemma 2, §4 case 1, §8, orientation and path-object corrections applied. Leaves C1, C1b, D3a.
- F7 (ICaTT and Rice rules in full): done 2026-11-18, `icatt-and-rice-rules.md`.
- E6a (verify the response on directed interchange): done 2026-11-18. Raw-schema no-go verified; statement corrected; `pseudo-vs-gray.md` §2.5 and §7 updated. Leaves E6.
