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
| OMATH | "Extend toward ordinary mathematics" `cmsg_018pe2CvdFGDdsWgn8Tjn5gb372mKMHNCxwDtepUMwRs3d` | active (2026-11-18) |

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
| C1 | **Conjecture N** (naturality of coherences for up-closed variable sets of depth ≥ 2), which gives Γ ⊗ Dᵏ for every context. A researcher response (added to main 2026-11-18, *not yet verified*, see C1a) proves the associator and every 2-dimensional coherence over a fully selected chain, via a relative ladder theorem. Still open after it: arbitrary up-closed subsets of a chain; the 3-dimensional unitor over the 2-disc; arbitrary depth; the proposed relative comparison property (RC)_{d,r}; a relative existence statement for composition constructors. | `conjectures/naturality-arbitrary-depth.md` §6–7 and "Researcher Response" §5; `free-objects.md` §7.1 | unowned | former area FREE |
| C1a | **Verify the researcher response on N** and fold it in: the ladder theorem; the corrections to Lemma 2 (induction order) and to the §8 whole-cylinder fullness claim (false for composition constructors); fixing the strict tensor convention (§4.4); then update `free-objects.md` §7.1 and the conjectures README. | `naturality-arbitrary-depth.md` "Researcher Response" | unowned | former area LIT |
| C2 | Check that iterated N-cylinders coincide with **Mikhail's `gray` contexts**, and that the cone terms p_t obtained from naturality terms satisfy Mikhail's free-variable condition. | `free-objects.md` §7.1 items 2–3 | unowned (needs C1 for general Γ) | former area FREE |
| C3 | **Decomposition of diagrams**: Diag((Γ, x : A), C) ≃ Diag(Γ, C) ×_{Diag(∂D, C)} Diag(D, C) at every dimension. The step from A2's rules to A1's universal property. | `free-objects.md` §3.3, §7.2.1 | unowned (higher cells need C1) | former area FREE |
| C4 | **Lifts of invertible cells are invertible** under the LIFT schema. | `free-objects.md` §7.2.2 | unowned | former area FREE |
| C5 | **Conservativity**: cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms. "The key theorem to formalise." | `free-objects.md` §2.6, §5, §7.2.3 | unowned | former area FREE |
| C6 | **Weak model of ATTACH**: identify the model structure on weak ω-categories in which boundary inclusions are cofibrations. | `free-objects.md` §3.6, §7.2.4 | unowned | former area FREE |
| C7 | Agda: postulate A1 (⟦Γ⟧ + LIFT) and A2 (INIT/ATTACH + LIFT) side by side and derive A1's LIFT₀ from A2; formalise the cylinder contexts Q↑Y and machine-check the depth-2 left-unitor case and the C1 next checks. | `free-objects.md` §6 | unowned | former area FREE |
| C8 | Agda targets from the limits notes: (1) elements elaboration R-C → §5.1 is well typed; (2) constant substitutions `(c:⋆) ⊢ !_Γ : Γ` exist; (3) cone contexts exist for pasting-scheme diagrams; (4) strict-model check of `laxcolim(const 1) ≅ Free(Γ)` for D¹, D², the loop and the composable pair; (6) formalise the free-on-graph trivial-fibration argument. (Target 5 is B2.) | `limits-representables.md` §8 | unowned | former area LIMN |
| C9 | **Density / extensionality**: are the disks jointly dense, so that a transformation is determined by components and naturality, for arbitrary (non-representable) domains? | `limits-representables.md` §5.1, §7; `internal-hom.md` §5.5a | unowned (likely needs a colimit principle, F5) | former area IHOM |

## D. Gray contexts, internal hom and closed structure

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| D1 | **G(2) uniqueness bookkeeping gap**: check that the cell built from exchange coherences has exactly the type t → t′. Closes Gray generators of dimension 4. | `conjectures/gray-contexts-in-catt.md` §3.3 | unowned | former area IHOM |
| D2 | **G(n), n ≥ 3, and G-alg**: translate Chanavat's contractible subdivision poset into substituted CaTT coherences (conservativity of molecular coh). Ready to send to a researcher. | `gray-contexts-in-catt.md` §3.4 | unowned | former area IHOM |
| D3 | **Mikhail's Gray rules for every context and every n**: existence with an explicit formula, and presentation of the Steiner Gray tensor. Must be a specified construction, since the raw judgment is permissive. | `gray-contexts-in-catt.md` §6 | unowned (related to C1, B5) | former area IHOM |
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
| E4 | **Invertibility markings**: port ICaTT's judgment; state "pseudo transformation" with the *recursive* marking (every cell in every dimension marked, since the pseudo hom is not locally full); propagation rules ("an interchanger with an invertible factor is invertible" [conj]; "C has only invertible 2-cells" propagating to interchangers into C). | `pseudo-vs-gray.md` §7.1 step 4, §2.4, §3.5, §5.3, Example 5 | unowned | former area PVG |
| E5 | **Generality ordering [conj]**: P ≈ L + "every interchanger, of every dimension, is invertible"; uniform L ⊂ two-tier L ⊂ P; every two-tier model is a uniform model. | `pseudo-vs-gray.md` §0.5, §2.4, §2.5, §3.6 | unowned (last part needs E6) | former area PVG |
| E6 | **Uniform L construction**: free strict structure with directed interchange at every level (requirements 1–5). A researcher response (added to main 2026-11-18, *not yet verified*, see E6a) proves a no-go for the *literal* schema (direct comparisons between raw interchange expressions force lower interchange to be strict, already in dimension 4), but not for the corrected schema whose higher comparisons have lower interchangers composed onto their boundaries. The corrected question is open. Then transfer Thm 1. | `conjectures/strict-lax-interchange-at-every-level.md`; `pseudo-vs-gray.md` §2.5 | unowned | former area PVG |
| E6a | **Verify the researcher response on directed interchange** and fold it in: the dimension-4 no-go for the literal schema; the corrected boundary-adjusted schema; the finiteness condition a finite support set imposes (§4); its reading of Bourke–Lobbia §4.2.6/§4.3 and Bourke–Gurski. Update `pseudo-vs-gray.md` §2.5 and §7 with what it means for uniform L. | `strict-lax-interchange-at-every-level.md` "Researcher Response" | unowned | former area LIT |
| E7 | Uniform L experiments: re-run E1–E2 for Σ(D¹ ∨ D¹) *inside* an object (directed Eckmann–Hilton); check that the "ordinary ω-category" marking restores exactly plain CaTT. | `pseudo-vs-gray.md` §7.1 step 7 | blocked on E6; adjacent: E4 | former area PVG |
| E8 | **Representables and lax homs over L**: restate R-B and the §5.4 hom rule over L; prove [conj] that Δ ⊗ Θ-shaped diagrams are Δ-families of cells of the native hom 𝒦(⟦Θ⟧, C) (Gray contexts derived, G1 gone). | `pseudo-vs-gray.md` §4.2, §7.1 step 6 | unowned | former area PVG |
| E9 | **Cost [conj]**: supports computed symbolically are polynomial in term size. | `pseudo-vs-gray.md` §5.2, §2.5 | unowned (LCORE's implementation is the natural place to measure) | former area PVG |
| E10 | **Surface defaults** (marking defaults for objects and transformations; default layering for horizontal composites). Listed as questions for Anthony; per standard 3, settle them from the E2/E7 experiments with a worked comparison instead. | `pseudo-vs-gray.md` §8 Q2–Q3, §5.3 | unowned | former area PVG |
| E11 | **Interpreting a dependent type theory in (∞,ω)-categories** (strictification / coherent choice), shared with CaTT; and whether ωCat itself is a model of CaTT (or of L). | `pseudo-vs-gray.md` §3.6 caveat, §5.4 | unowned (long-term) | — |

## F. Ordinary mathematics and further extensions

Design note: `ordinary-math.md` (added 2026-11-18 by OMATH). Rows F1–F6 are its proposals; the lettered rows are what it leaves open.

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| F1 | **Dependent eliminators.** Families are maps, sections are maps with an invertible cell; dependent elimination is *derived* from non-dependent universal properties (AGS argument). Proved on paper: dependent elimination for shapes ⟦Γ⟧ from R-A (Thm 4.1); induction for N from recursion (Thm 4.3); recursion for N := Hom_{⟦L⟧}(x,x) from two general principles, G (lax colimits are Grothendieck constructions) and DJ (comma objects are free cocartesian fibrations) (Thm 4.4). Three routes compared (§4.5). | `ordinary-math.md` §4 | proposal written | OMATH (proposal); open parts F1a, F1b |
| F1a | Write G and DJ as rules with their `uni`-style higher levels; check the uniqueness step of Thm 4.4 in detail. | `ordinary-math.md` §4.6 | unowned | former area OMATH |
| F1b | Tree-shaped inductive objects, and lists over an arbitrary object, in route III (no ℕ-specific rule). | `ordinary-math.md` §4.7 | unowned | former area OMATH |
| F2 | **Discreteness filler tactic** for graph contexts: proved on paper (Thm 3.1), implemented with certified output and checked examples in `src/CaTTExp/GraphFiller*.agda`. | `ordinary-math.md` §3 | done (paper + certified instances) | — |
| F2a | Agda: totality of the graph filler (every parallel pair with the same path gets a filler). | `ordinary-math.md` §3.4 | blocked on A1; adjacent: more instances | former area OMATH |
| F2b | Filler for **globular** contexts (Thm 3.2, semantic proof done): implement strict normal forms (labelled trees) and the lift. | `ordinary-math.md` §3.3 | unowned | former area OMATH |
| F3 | **h-level discipline**: judgment `C trunc n` with T-fill/T-inv and closure rules; T-lim and T-hom proved (sketch); base rules T-graph and T-loc sound by `free-on-graph.md` and Dwyer–Kan. Gives `N trunc 0`, `ℤ trunc 0`, automatic coherence for set-level algebra. | `ordinary-math.md` §2 | proposal written | OMATH; open parts F3b, F3c |
| F3b | Non-derivability of T-graph from R-A (argued, Prop. 2.5), or a Hedberg-style derivation of `N trunc 0`. | `ordinary-math.md` §2.3 | unowned | former area OMATH |
| F3c | Full proofs of T-lim and T-hom against the specified `ctrf` construction. | `ordinary-math.md` §2.3 | blocked on B5; adjacent: F3b | former area OMATH |
| F4 | **The integers**: ℤ := Hom(x,x) in ⟦L⟧ localised at s (a finite pushout). ℤ ≃ ℤ_disc proved from Dwyer–Kan 1980 Prop. 2.3 and `free-on-graph.md`. General quotients need a set-truncation rule (proposed, §5.3). | `ordinary-math.md` §5 | done for ℤ; quotients proposed | — ; open parts F4a, F4b |
| F4a | Filler tactic for localised graphs (reduced words). | `ordinary-math.md` §5.1 | unowned | former area OMATH |
| F4b | Effectiveness of quotients under the Trunc rule. | `ordinary-math.md` §5.3 | unowned | former area OMATH |
| F5 | **Object-indexed colimits**: diagrams as cocartesian fibrations; lax colimit = total space, pseudo colimit = finite localisation, left Kan extension = comma + localisation; sequential colimits = pseudo coequaliser of the total family. No new rule. Colimits *inside* an object are declared structure (§6.4). | `ordinary-math.md` §6 | proposal written | — ; open part F5a |
| F5a | Check §6.1–6.3 against the (∞,ω) sources (Gepner–Heine, Loubaton) at statement level, not abstracts. | `ordinary-math.md` §6 | unowned | former area OMATH |
| F6 | **Lax functors**: out of finite loop-free shapes, maps out of the glued orientals P^lax (no new rule); lax-functor variables via a directed refinement-coherence rule. | `ordinary-math.md` §7 | proposal written | — ; open part F6a |
| F6a | `conjectures/lax-functor-refinement.md`: are lax-functor comparison cells decided by Steiner supports of the oriental complex? Ready to send to a researcher. | `conjectures/lax-functor-refinement.md` | unowned (ready to send) | former area OMATH |
| F7 | Write out **ICaTT's and Rice's (CaTT_su/sua) rules in full** from the papers; the survey paraphrased them. Needed by E4, by the walking-equivalence quotients of `limits-representables.md` §6.1, and by ⟦J⟧ in F4 and F5. | `catt-survey.md` "Possible next steps" | unowned | — |
| F8 | **Exponentials of sets** (function sets ℕ → ℕ, sequences for ℝ): an internal hom restricted to `trunc 0` targets, e.g. Mimram's cartesian closed rules (D12) for sets. | `ordinary-math.md` §6.5 | unowned | — |
| F9 | **Formalise the h-level and recursion rules** (standard 9): encode `trunc` and T-fill and check the ring example of §2.5; encode recursion over a parameter context. Needs syntax for operations "over a context applied to a substitution" beyond `coh`. | `ordinary-math.md` §8 | unowned | former area OMATH |

## G. Verification debt

| ID | Item | Source | Status | Owner |
|---|---|---|---|---|
| G1 | **Re-check every claim marked [recall]** against its source (including those in `ordinary-math.md`, and DK 1980 Prop. 2.3 against a clean copy), e.g.: AM Gray tensor biclosedness and its naming; Steiner's "tensors of loop-free complexes are loop-free"; ν(K ⊗ L) ≅ ν(K) ⊗ ν(L); "a lax transformation's naturality cell at an equivalence is invertible"; the even-duality formula for ⊗; Haugseng on lax transformations; Gray 1974; Markakis's generalised signatures. | `internal-hom.md`, `pseudo-vs-gray.md`, `free-objects.md`, `limits-representables.md` (search "[recall]") | unowned | former area LIT |
| G2 | **One place for conventions**: lax vs oplax and factor order. `pseudo-vs-gray.md` §3.1 fixes L's order from the limit rules; `internal-hom.md` §4.1 ("Mikhail's Γ ⊗ Dⁿ is Dⁿ ⊗ Γ in AM orientation") and `limits-representables.md` §1 use their own. Write a single conventions section and make the other notes cite it. | `internal-hom.md` §4.1; `pseudo-vs-gray.md` §3.1, §7.1 step 1 | unowned | former area PVG |
| G3 | **Steiner support lemma for arbitrary Steiner complexes** (beyond acyclic ones). Not needed by any current design; recorded so it is not lost. | `conjectures/steiner-support-determines-cells.md` | unowned (low priority) | — |

---

## Out to external researchers

- `conjectures/oriented-lax-limits.md` (B8), sent 2026-11-18.

**Responses received, awaiting verification:** `naturality-arbitrary-depth.md` (C1a), `strict-lax-interchange-at-every-level.md` (E6a).

**Ready to send** (self-contained, literature-checked): `gray-contexts-in-catt.md` G and §6 (D1–D3); `lax-functor-refinement.md` (F6a). After C1a and E6a are verified, the remaining open parts of N (C1) and of the corrected uniform-L question (E6) can be restated and sent again.

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
