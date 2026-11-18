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
| AGDA0 | core Agda / survey thread `cmsg_018pe2CvdFGDdsWgn8Tjn5gbFVBaKE936jSAppjVSszHLX` | idle (awaiting review) |
| IHOM | internal hom and Gray tensor `cmsg_018pe2CvdFGDdsWgn8Tjn5gbEUSN4QBuzbPj9ExdY9DTuF` | done |
| FREE | free ω-categories as objects `cmsg_018pe2CvdFGDdsWgn8Tjn5gb7LiQb6yikB1xjtm14CaXMG` | done |
| LIMN | limits and representables notes `cmsg_018pe2CvdFGDdsWgn8Tjn5gb6zYn9ewLrPvp4YL8AfJHKN` | done |
| PVG | pseudo vs Gray-style core `cmsg_018pe2CvdFGDdsWgn8Tjn5gbKP6yrjEAYBPgxDoAc2gq3F` | done |
| LIT | literature / conjecture verification `cmsg_018pe2CvdFGDdsWgn8Tjn5gbKdRdpEiQuvAuEvTAURBqhf` | done |
| MARK | "Design invertibility markings for lax core" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbQhMQC4fsaRjMJypHXq4ZVv` | active |
| FOBJ | "Develop free-object rules" `cmsg_018pe2CvdFGDdsWgn8Tjn5gbUxJhXTzhRJEWFkLNmH5acC` | active |

---

## A. Core CaTT metatheory (Agda)

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| A1 | **Substitution admissibility** for core CaTT: Δ ⊢ σ : Γ and Γ ⊢ t : A give Δ ⊢ t[σ] : A[σ]. The main missing metatheorem; every extension needs it. | `agda-sketch-findings.md` "Not yet done", "Suggested next steps" | unowned | former area AGDA0. LCORE proves substitution for the L side condition; check whether that proof covers or can be reused for plain CaTT. |
| A2 | **Checker completeness**: the certified checker is sound (returns derivations) but not proved complete. | `agda-sketch-findings.md` | unowned | former area AGDA0 |
| A3 | **Any semantics in Agda**, starting with interpretation in strict ω-categories (or the strict free category on a graph). | `agda-sketch-findings.md` | unowned (needs A1) | former area AGDA0 |
| A4 | **Non-derivability of functoriality of ⟦_⟧** (finding 2) is argued informally. Make it rigorous: soundness of the strict-model interpretation, then the separating model. | `agda-sketch-findings.md` finding 2 | unowned (needs A1, A3) | former area AGDA0 |

## B. Limit rules (CaTT_lim and its repair)

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| B1 | Encode Mikhail's printed Def. 4.15 rules; machine-check the `ctrf` τCond rejection of the intended source of m_f, the `x′ : X` renaming defect, and the non-canonical cone. | `conjectures/catt-lim-pseudo-vs-gray.md` verification 4; `lax-colimit-of-point.md` | in progress | LIM-F |
| B2 | Machine-check the collapse: unchanged `uni` forces cone-morphism cells and ambient 3-cells invertible. | `limits-representables.md` §10.1, §8 item 5 | in progress | LIM-F |
| B3 | Encode the **repaired rules** (specified shapes, certified comparison cells as marked declarations); check the intended examples and that the collapse no longer derives. | `limits-representables.md` §4.1, §10.1 | in progress | LIM-F |
| B4 | Prove **substitution, composition and soundness** for the marked-declaration version of the repaired rules. Includes composition of cone transfors, which the forced-invertibility argument assumes. | `catt-lim-pseudo-vs-gray.md` "Open after this response" (a), verification 2 | unowned (LIM-F encodes the rules; the metatheory proofs are not on its checklist) | former area LIMN |
| B5 | **Specified (canonical) cone, cocone and `ctrf` construction for arbitrary Γ**, checked against the Steiner Gray product. Subsumes Mikhail's Conj. 3.6 (cones over arbitrary contexts) for the cases needed. | `limits-representables.md` §4.1(1), §10.3; `free-objects.md` §7.1 item 3; `gray-contexts-in-catt.md` §6.2a | unowned | former area LIMN |
| B6 | **Free object = lax colimit of the point, syntactically**: for the specified cocone C(Γ), is the constant-diagram instance equivalent to the suspension (c:⋆, Σ_{⊤,c}Γ)? Then Step B (higher cocone morphisms vs transfors). If it holds, R-A's rules become admissible. | `conjectures/lax-colimit-of-point.md` "What remains"; `limits-representables.md` §5.2, §10.3 | unowned (needs B5) | former area LIMN |
| B7 | **Restate the limit rules over the Gray (L) core**, with directed interchangers; check whether `ctrf` shapes become native cells of 𝒦(c, ·) [conj]. "The main open item for L on the limits side." | `limits-representables.md` §4.1(3), §10.1; `pseudo-vs-gray.md` §4.4, R11 | unowned for the paper design (LIM-F lists a two-tier L variant only as an "if feasible" step) | former area LIMN / PVG |
| B8 | **Oriented lax limits**: is the unrestricted lax universal property consistent in oriented categories, do limits exist, and do they give comma and hom objects? Internally: re-derive the R11 argument line by line in L to confirm it fails there. | `conjectures/oriented-lax-limits.md`; `pseudo-vs-gray.md` R11 | out to researcher (2026-11-18); internal attempt unowned | — |
| B9 | Check the extension of the collapse to **all dimensions ≥ 3** line by line (researcher cites Benjamin–Markakis Prop. 35; not checked here). | `catt-lim-pseudo-vs-gray.md` verification 5 | unowned | former area LIT |
| B10 | Classify the models of the **original** CaTT_lim rules beyond "cells of dimension ≥ 3 are invertible". | `catt-lim-pseudo-vs-gray.md` open (b) | unowned (low priority) | former area LIT |
| B11 | Kernel simplification: merge `star`/`pstar`/`uni` bookkeeping into one **horn-filling judgment** `M horn(Γ; c) ⊢ x`. | `limits-representables.md` §4.1 | unowned | former area LIMN |
| B12 | **One limit schema** parameterised by orientation {lim, colim} × {lax, oplax} × marking, with the **marking variance alternating by dimension** (left/right cartesian) as the weighted-limit result requires. | `limits-representables.md` §4.3, §4.4, §10.4 | unowned | former area LIMN |
| B13 | Show the syntactic cone categories present **Loubaton's Hom_⊖** (marked Gray product in higher dimensions), under P (certified marking) and under L (Gray-core `ctrf`). The remaining syntax-to-semantics step for weighted limits. | `limits-representables.md` §10.4 | unowned (needs B3/B7) | former area LIMN |
| B14 | **Finite fibration test for weights**: a finite, generator-level criterion on π : Ψ → Γ that implies the (infinite) lifting schema (19) making π present a left cartesian fibration. | `conjectures/weighted-as-partially-lax-omega.md` §5; `limits-representables.md` §4.2, §10.4 | unowned | former area LIMN |

## C. Free objects and representables

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| C1 | **Conjecture N** (naturality of coherences for up-closed variable sets of depth ≥ 2), which gives Γ ⊗ Dᵏ for every context. Settled (researcher, verified 2026-11-18): every 2-dimensional coherence over a fully selected chain, via the relative ladder theorem. Still open: the 3-dimensional unitor over the 2-disc (§7 case 3); arbitrary up-closed subsets of a chain; arbitrary depth; the proposed induction hypothesis (RC)_{d,r} plus a relative existence statement for composition constructors. | `conjectures/naturality-arbitrary-depth.md` §7 and "Verification"; `free-objects.md` §7.1 | unowned (ready to restate and send to a researcher) | former area FREE |
| C1b | **Run the ladder construction mechanically**: build the associator's naturality 3-cell over a fully selected chain (conjecture file, response §3) in a CaTT checker, to confirm the paper proof's generated terms typecheck. | `naturality-arbitrary-depth.md` "Verification", last bullet | unowned (needs a checker that handles 3-cells over non-pasting contexts by substitution) | former area AGDA0 |
| C2 | Check that iterated N-cylinders coincide with **Mikhail's `gray` contexts**, and that the cone terms p_t obtained from naturality terms satisfy Mikhail's free-variable condition. | `free-objects.md` §7.1 items 2–3 | unowned (needs C1 for general Γ) | former area FREE |
| C3 | **Decomposition of diagrams**: Diag((Γ, x : A), C) ≃ Diag(Γ, C) ×_{Diag(∂D, C)} Diag(D, C) at every dimension. **Proved** as an isomorphism onto the strict pullback at every k, given the cylinder contexts (unconditional for globular Γ): `free-objects-proofs.md` Thm 3. Strict ≃ pseudo pullback proved at level 0 (Lemma 4) and in the strict model at all levels. Remaining: (C3a) compatibility with Diag's composition, once D3 fixes it; (C3b) boundary restriction is an ω-equifibration at all levels, syntactically; (C3c) higher-depth cylinders = C1. | `free-objects.md` §3.3, §7.2.1; `free-objects-proofs.md` §2 | in progress (C3a adjacent work, C3b) | FOBJ |
| C4 | **Lifts of invertible cells are invertible** under the LIFT schema. **Proved on paper** (`free-objects-proofs.md` §1, coinduction; rule-level form of FHM 2406.13240 Prop. 3.1.7). Remaining: Agda proof (`Free/Reflect.agda`). | `free-objects.md` §7.2.2 | in progress (Agda) | FOBJ |
| C5 | **Conservativity**: cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms. Non-collapse half **proved under P** in the strict cartesian model (`free-objects-proofs.md` Prop. 5). Weak statement **reduced** to BMS + DFMRV (known) and a sound weak interpretation (E11). Remaining: (C5a) weak half, blocked on E11; (C5b) strict half under L, needs the strict Gray model of the L core (adjacent to E2). | `free-objects.md` §2.6, §5, §7.2.3; `free-objects-proofs.md` §5 | C5a blocked on E11; C5b in progress (adjacent work while C5a waits) | FOBJ |
| C7 | Agda: postulate A1 (⟦Γ⟧ + LIFT) and A2 (INIT/ATTACH + LIFT) side by side and derive A1's LIFT₀ from A2; formalise the cylinder contexts Q↑Y and machine-check the depth-2 left-unitor case and the C1 next checks. Paper side of the derivation done (`free-objects-proofs.md` §3), with the finding that it needs naturality terms of Γ's boundary terms already at dimension 0. | `free-objects.md` §6 | in progress | FOBJ |
| C8 | Agda targets from the limits notes: (1) elements elaboration R-C → §5.1 is well typed; (2) constant substitutions `(c:⋆) ⊢ !_Γ : Γ` exist; (3) cone contexts exist for pasting-scheme diagrams; (4) strict-model check of `laxcolim(const 1) ≅ Free(Γ)` for D¹, D², the loop and the composable pair; (6) formalise the free-on-graph trivial-fibration argument. (Target 5 is B2.) | `limits-representables.md` §8 | (3), (4), (6) in progress; (1), (2) unowned | FOBJ for (3), (4), (6); former area LIMN for (1), (2) |

## D. Gray contexts, internal hom and closed structure

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| D1 | **G(2) uniqueness bookkeeping gap**: check that the cell built from exchange coherences has exactly the type t → t′. Closes Gray generators of dimension 4. | `conjectures/gray-contexts-in-catt.md` §3.3 | unowned | former area IHOM |
| D2 | **G(n), n ≥ 3, and G-alg**: translate Chanavat's contractible subdivision poset into substituted CaTT coherences (conservativity of molecular coh). Ready to send to a researcher. | `gray-contexts-in-catt.md` §3.4 | unowned | former area IHOM |
| D3 | **Mikhail's Gray rules for every context and every n**: existence with an explicit formula, and presentation of the Steiner Gray tensor. Must be a specified construction, since the raw judgment is permissive. | `gray-contexts-in-catt.md` §6 | unowned (related to C1, B5) | former area IHOM |
| D3a | **Re-check "G implies N"** (`gray-contexts-in-catt.md` intro, README, `naturality-arbitrary-depth.md` §8). The verified review found §8's whole-cylinder fullness argument false for composition constructors (for c = f ∗₀ g, a_c and b_c miss f↑, g↑). The implication needs a separate argument for composites and a support theorem for the boundary lifts. | `naturality-arbitrary-depth.md` §8 (corrected) and "Verification" | unowned | former area IHOM / LIT |
| D4 | Side conditions of the Gray tensor of contexts: **G2** functoriality in substitutions (needed for nat-Δ), **G4** associativity up to coherence (may need CaTT_sua), **G5** whether linearity (x ∝ t) is needed. | `internal-hom.md` §4.2 | unowned | former area IHOM |
| D5 | Agda targets for Gray contexts: Γ ⊗ D¹ for Γ a pasting scheme as a function on syntax, proved well formed; G3 (wedges); vertical composition of lax transformations as a substitution, recording which non-ps composites are needed; D¹ ⊗ D¹ ⊗ D¹ under both orientations. | `internal-hom.md` §7 | unowned (LCORE's Gray-cube test is the L-side analogue, not this) | former area IHOM |
| D6 | If molecular coh is adopted: re-examine **pruning, insertion and rehydration** for molecules. | `internal-hom.md` §4.3(ii) | unowned (conditional on D2 outcome) | former area IHOM |
| D7 | **Gray tensor of arbitrary objects** B ⊗ C as a colimit of ⟦x ⊗ y⟧, then check the Gray tensor's universal property. Needed for lax currying with both factors arbitrary. | `internal-hom.md` §6; `pseudo-vs-gray.md` §4.3 | blocked on general colimits (B12); adjacent work: state the target universal property | former area IHOM |
| D8 | **Dualities under L**: which reversals stay symmetries and which swap lax/oplax (PR #3 experiment 3), including the even-duality formula for ⊗ (marked [recall]); design an orientation-parameterised kernel so proofs transfer. | `pseudo-vs-gray.md` R5; `internal-hom.md` §5.6 | unowned | former area PVG |
| D9 | **PL1**: pin down the faithfulness lemma (free unit-free biclosed monoidal category → free non-symmetric linearly distributive category); write out steps 2–3 of the 1-dimensional theorem carefully. | `conjectures/planar-pasting-types.md` §2, §7 | unowned | former area IHOM |
| D10 | **Units** for planar pasting types: a separate criterion. | `planar-pasting-types.md` §3 | unowned | former area IHOM |
| D11 | **PL-ω**: a class of Gray pasting types; first test, a criterion whose 2-cells are exactly the lax naturality cells of evaluation Fun^lax(B, C) ⊗ B → C, without inverses; compare Gepner–Heine's LMor/RMor. | `planar-pasting-types.md` §4, §7 | unowned | former area IHOM |
| D12 | **Mimram's CCCaTT**: work out the higher-dimensional cartesian pasting criterion (unpublished), and re-check the rule details against the PDF (they were read via a summary). | `internal-hom.md` §5.7 | unowned | former area IHOM |

## E. Lax-interchange (L) core

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| E1 | Implement Steiner chains and the Gray unfolding; checker with decidability; **supp = Var on a single hom** (conservativity over CaTT). | `pseudo-vs-gray.md` §7.1 step 2, §3.6 Thm 1(3) | in progress | LCORE |
| E2 | Two-object cases mechanically: D²∨D² (interchanger one way only), D¹∨D² (whiskering), D²∨D²∨D² (cube 4-cell from ps-terms); validate against the strict AM model. | `pseudo-vs-gray.md` §7.1 step 3, §3.4 | in progress | LCORE |
| E3 | Substitution admissibility and **non-derivability of the reverse interchanger** for L. | `pseudo-vs-gray.md` §3.6 Thm 1(2) | in progress | LCORE |
| E4 | **Invertibility markings.** Designed 2026-11-18 in `invertibility-markings.md` §1–2: judgments `inv` and `ps` (pseudo is one-sided in execution order), recursive `ps*` = corrected C1″, marked declarations, propagation rules (INV-fac, INV-obj, PS-fac, OP-inv/ps, OBJ-k for `grpd_k` objects), all **proved sound** in oriented (∞,ω)-categories and the strict model; "interchanger with an invertible factor is invertible" is now proved. Remaining: Agda encoding (asked of LCORE); whether ICaTT's rec is admissible (low priority). | `invertibility-markings.md` | in progress (Agda encoding) | MARK; LCORE for the encoding |
| E5 | **Generality ordering.** Semantic half of P ≈ L + "every mixed cell invertible" **proved** (`invertibility-markings.md` Thm 3.1, via n-ary gray-vs-cartesian and a sub-operad argument). Open: syntactic half, Conjecture 3.2 (conservative translation CaTT → L⁺), reduced to a relative coherence lemma; uniform ⊂ two-tier part needs E6. | `invertibility-markings.md` §3 | in progress | MARK |
| E6 | **Uniform L construction**: free structure with directed interchange at every level (requirements 1–5), corrected boundary-adjusted reading. Literal version impossible (verified). New 2026-11-18: no single directed complex, or hom-wise family of them, can present the answer (`invertibility-markings.md` §7, Obs. 7.1); a description must be an iterated tower. Researcher-ready prompt: `conjectures/outbox/directed-interchange-every-level.md` (Q1–Q4). Internal next step: the first genuinely uniform case ΣD² ∨ ΣD² up to dimension 5 (Q2). | `conjectures/strict-lax-interchange-at-every-level.md`; `conjectures/outbox/directed-interchange-every-level.md`; `invertibility-markings.md` §7 | in progress; prompt ready to send | MARK |
| E7 | Uniform L experiments: re-run E1–E2 for Σ(D¹ ∨ D¹) *inside* an object (directed Eckmann–Hilton); check that the "ordinary ω-category" marking (`ord`, `invertibility-markings.md` §1.5) restores exactly plain CaTT. | `pseudo-vs-gray.md` §7.1 step 7 | blocked on E6; adjacent marking design done (E4 §1.5) | MARK |
| E8 | **Representables and lax homs over L.** Hom rule and R-A restated over L (`invertibility-markings.md` §4); semantics proved from the literature; elimination (reading Gray-shaped components off a native lax cell) derivable. **Finding:** G1 does not disappear under L: introducing a lax cell from components needs a Gray-shaped context. Posed as Conjecture CT, `conjectures/canonical-gray-terms.md`. | `invertibility-markings.md` §4; `pseudo-vs-gray.md` §4.2 | in progress (CT open) | MARK |
| E9 | **Cost.** The [conj] is **false for explicit supports** (term of size O(n) with support 3ⁿ; source chains of size C(n,k)). Restated as E9′: is the side condition decidable in time polynomial in shared term size? Open; timing experiment on n-fold wedges asked of LCORE. | `invertibility-markings.md` §5 | in progress | MARK; LCORE for measurement |
| E10 | **Surface defaults**: settled 2026-11-18 by worked counts (`invertibility-markings.md` §6): kernel has no defaults; surface marks only at declarations (M1), derives the rest; default horizontal composite is the ∂⁻-layering. Remaining: the uniform-L `ord` default, which waits on E6/E7. | `invertibility-markings.md` §6 | blocked on E6 for the uniform part only | MARK |
| E11 | **Interpreting a dependent type theory in (∞,ω)-categories** (strictification / coherent choice), shared with CaTT; and whether ωCat itself is a model of CaTT (or of L). | `pseudo-vs-gray.md` §3.6 caveat, §5.4 | unowned (long-term) | — |

## F. Ordinary mathematics and further extensions

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| F1 | **Dependent eliminators**: induction/primitive recursion on the ℕ-like object N, directed J. Needs a fibrations story without universes (fibrations as maps plus a (co)cartesian lifting rule, or fibration-shaped contexts). No thread has ever owned fibrations. | `limits-representables.md` §6.4, §7, §10.5; `catt-survey.md` §10, §13 | unowned | — |
| F2 | **Discreteness filler tactic**: an admissible meta-operation that fills any parallel pair of cells of dimension ≥ 2 in a 1-dimensional context by a coherence over the chain pasting scheme (DFMRV Prop. 7.19, 7.32). Gives "N is discrete" inside the theory. | `limits-representables.md` §10.5 | unowned | former area LIMN |
| F3 | **h-level discipline**: stating and proving truncation properties (e.g. a ring object is discrete) inside the theory. Needed under every option. | `pseudo-vs-gray.md` Example 5; `limits-representables.md` §6.4 | unowned | — |
| F4 | **Presentations with equations** via marked colimits (coequaliser/localisation style). Test case: the integers, where cancellation appears. Then vector-space-like objects. | `limits-representables.md` §6.5, §9.3 | unowned (needs colimit rules, B12) | former area LIMN |
| F5 | **Object-indexed colimits** (sequential colimits, Kan extensions along non-shapes): left adjoint to C → [I, C], or localised Grothendieck constructions (AHM Thm F). First test case (from C9): the Θ-density rule, B as the colimit of its pasting-diagram elements, which gives extensionality of transformations for arbitrary domains. | `limits-representables.md` §7, §9.4 | unowned | former area LIMN |
| F6 | **Lax functors** (composition preserved only up to a directed cell): no option provides them; needs a new rule family, e.g. Gray-shaped lax-functor contexts. | `pseudo-vs-gray.md` "What none of the three gives" | unowned | — |

## G. Verification debt

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| G1 | **Re-check every claim marked [recall]** against its source, e.g.: AM Gray tensor biclosedness and its naming; Steiner's "tensors of loop-free complexes are loop-free"; ν(K ⊗ L) ≅ ν(K) ⊗ ν(L); "a lax transformation's naturality cell at an equivalence is invertible"; the even-duality formula for ⊗; Haugseng on lax transformations; Gray 1974; Markakis's generalised signatures. | `internal-hom.md`, `pseudo-vs-gray.md`, `free-objects.md`, `limits-representables.md` (search "[recall]") | unowned | former area LIT |
| G2 | **One place for conventions**: lax vs oplax and factor order. `pseudo-vs-gray.md` §3.1 fixes L's order from the limit rules; `internal-hom.md` §4.1 ("Mikhail's Γ ⊗ Dⁿ is Dⁿ ⊗ Γ in AM orientation") and `limits-representables.md` §1 use their own. Write a single conventions section and make the other notes cite it. | `internal-hom.md` §4.1; `pseudo-vs-gray.md` §3.1, §7.1 step 1 | unowned | former area PVG |
| G3 | **Steiner support lemma for arbitrary Steiner complexes** (beyond acyclic ones). Not needed by any current design; recorded so it is not lost. | `conjectures/steiner-support-determines-cells.md` | unowned (low priority) | — |

---

## Out to external researchers

- `conjectures/oriented-lax-limits.md` (B8), sent 2026-11-18.

**Responses received, awaiting verification:** none. (`naturality-arbitrary-depth.md` and `strict-lax-interchange-at-every-level.md` were verified 2026-11-18.)

**Ready to send** (self-contained, literature-checked): `outbox/directed-interchange-every-level.md` (E6; paste as is). `canonical-gray-terms.md` (CT, from E8). `gray-contexts-in-catt.md` G and §6 (D1–D3). The remaining open parts of N (C1) and the corrected uniform-L question (E6) are now restated in their files and can be sent again.

## Closed

Kept briefly for orientation; details are in the linked files.

- `free-on-graph.md`: solved (researcher, verified). N ≃ ℕ_disc semantically.
- `weighted-as-partially-lax-omega.md`: solved in Loubaton's model (researcher, verified). Leaves B12–B14.
- `gray-vs-cartesian.md`: C1, C1′ proved; C1″ without "locally full" (researcher, verified). Leaves E4's recursive marking.
- `catt-lim-pseudo-vs-gray.md`: answered (researcher, verified). Leaves B1–B4, B9, B10.
- `lax-colimit-of-point.md`: semantic claim solved; arbitrary-derivation syntactic form refuted. Leaves B5, B6.
- `free-infinity-gray-of-pasting-diagrams.md`: solved in the literature. Discharges (D)–(F) of `pseudo-vs-gray.md` §3.6.
- `steiner-support-determines-cells.md`: solved for the needed case (Hadzihasanovic). Discharges (A)–(C). Leaves G3.
- `limits-representables.md` §10.2: marking needs no closure condition.
- C6 (weak model of ATTACH): answered in `free-objects-proofs.md` §4. Strict and (∞,ω) models justified; the algebraic-weak gap is part of E11.
- C9 (density): answered in `free-objects-proofs.md` §6. Disks are not dense, Θ is; the Θ-density rule is recorded under F5.
- C1a (verify the response on N): done 2026-11-18. Ladder theorem verified; Lemma 2, §4 case 1, §8, orientation and path-object corrections applied. Leaves C1, C1b, D3a.
- F7 (ICaTT and Rice rules in full): done 2026-11-18, `icatt-and-rice-rules.md`.
- E6a (verify the response on directed interchange): done 2026-11-18. Raw-schema no-go verified; statement corrected; `pseudo-vs-gray.md` §2.5 and §7 updated. Leaves E6.
