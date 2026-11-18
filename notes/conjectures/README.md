# Conjectures and open problems

**The repository copy (`notes/conjectures/` on `main` of AHartNtkn/CaTTExp) is canonical.** The shared project folder holds a synced copy. Edits made there are folded back into the repository.

This folder holds problem statements written to be **self-contained**: a reader who knows higher category theory but nothing about this project should be able to work on any file here alone.

**Project standard (adopted 2026-11-18).** "Unproved" is a reason to investigate, never a reason to reject a design. When a design note rests on an unproved claim:
1. The note attempts a proof and records how far the attempt got.
2. Where the attempt stalls, the remaining gap is written up here as a well-posed problem.

Each file has the same parts:
- **Background:** the definitions needed, with references.
- **Statement:** precise, with any choices of convention made explicit.
- **What is known:** related results and partial arguments.
- **Why it matters:** one paragraph, with no project jargon.
- **What would count as a solution:** a proof, a counterexample, or a reference.

Literature searches were done on 2026-11-18. Each file ends with a "Literature status" or "Literature search" section, with citations.

## Status at a glance

Owners and status of the follow-up work these problems leave are tracked in `notes/open-issues.md`.


- **Solved:**
  - `free-on-graph.md`: proved by an external researcher, and verified here.
  - `weighted-as-partially-lax-omega.md`: proved by an external researcher in Loubaton's model, and verified here. A finite computad test is still open.
  - `gray-vs-cartesian.md`: proved by an external researcher, who completed the literature sketch, and verified here. C1″ holds without "locally full".
  - `catt-lim-pseudo-vs-gray.md`: answered by an external researcher, and verified here. The intended CaTT_lim forces pseudo cone morphisms, and even all cells of dimension ≥ 3 invertible. The corrected universal property is identified. The printed `ctrf` rules need repair.
  - `free-infinity-gray-of-pasting-diagrams.md`: in the literature (Campion 2311.00205, Cor. 3.5; Chanavat 2603.22242, Thm 3.29).
  - `steiner-support-determines-cells.md`: the main case follows from Hadzihasanovic's book (arXiv 2404.07273), Prop. 8.3.17 and Thm 11.2.18.
- **Partly solved:**
  - `planar-pasting-types.md`: PL1 follows from unit-free proof-net coherence, up to one lemma.
  - `lax-colimit-of-point.md`: the semantic claim is solved (Loubaton, Example 4.2.3.12). The syntactic form is false for arbitrary cone-judgment derivations (verified counterexample); it is open for a specified cocone construction.
  - `gray-contexts-in-catt.md` §6: the (∞,ω) part is answered.
  - `naturality-arbitrary-depth.md`: every 2-dimensional coherence over a fully selected chain (the associator included) is settled by a researcher's relative ladder theorem, verified here. Open: the 3-dimensional unitor over the 2-disc, arbitrary up-closed sets on a chain, and arbitrary depth.
  - `strict-lax-interchange-at-every-level.md`: the literal reading (raw higher interchange cells) is proved impossible by a researcher, verified here; the statement is corrected to boundary-adjusted higher comparisons, which remain open.
- **Open:**
  - `gray-contexts-in-catt.md`: G(n), and Mikhail's rules.

## Index (each distinct problem once)

| File | Problem | Status | Depends on / related to | Origin |
|---|---|---|---|---|
| `gray-contexts-in-catt.md` | **Gray contexts in CaTT.** (G) Do frame-acyclic molecules have CaTT composites, unique up to invertible cells (equivalently, is "molecular coh" conservative over CaTT)? (§6) Do Mikhail's Gray rules give contexts `M ⊗ Dⁿ` for every context M and every n, presenting the Steiner Gray tensor? *Merges the former `gray-contexts-steiner.md`.* | G open (G(1) proved, G(2) up to bookkeeping); §6 (1)–(2) open, with the strict half of (2) known; §6 (3) answered | G should imply `naturality-arbitrary-depth.md` (argument needs repair for composites; open-issues D3a). §6 (3) is `free-infinity-gray-of-pasting-diagrams.md`. Needed for `lax-colimit-of-point.md` Step B. | `internal-hom.md` §4.3; `limits-representables.md` §10.3 |
| `naturality-arbitrary-depth.md` | Does every CaTT coherence over a pasting context have a naturality cell for every up-closed set of variables, of any depth? This gives `Γ ⊗ D¹` for every context Γ. | **Partly solved.** Depth ≤ 1 (BMOSV). Every 2-dimensional coherence over a fully selected chain (researcher, verified). Open: 3-dim unitor over the 2-disc, arbitrary Y on a chain, arbitrary depth. | A special case of G in `gray-contexts-in-catt.md`. It gives §6 (1) there for n = 1. | `free-objects.md` §7.1 |
| `free-infinity-gray-of-pasting-diagrams.md` | Are Gray tensors of globular pasting diagrams free as (∞,n)-categories, and equal to Campion's Gray tensor? | **Solved** (literature) | Answers `gray-contexts-in-catt.md` §6 (3). Used by `pseudo-vs-gray.md` (D)–(F) and `limits-representables.md`. | `pseudo-vs-gray.md` §3.6 |
| `steiner-support-determines-cells.md` | In free strict ω-categories on Steiner complexes (e.g. Gray tensors of pasting diagrams), is a cell determined by its dimension and its set of generators? | **Solved** for Gray tensors of pasting diagrams (literature). Open for arbitrary Steiner complexes. | The k = 0 case of requirement 2 in `strict-lax-interchange-at-every-level.md` | `pseudo-vs-gray.md` §3.6 |
| `strict-lax-interchange-at-every-level.md` | Construct free strict ω-categories in which *every* interchange law is a directed cell, with cells determined by their generators. | **Sharpened.** Raw higher interchange cells are impossible (researcher, verified); open for boundary-adjusted comparisons | Generalises `steiner-support-determines-cells.md` to all levels | `pseudo-vs-gray.md` §2.5, §3.6 |
| `gray-vs-cartesian.md` | Is Dᵏ × Dˡ the Gray product Dᵏ ⊗ Dˡ with mixed cells inverted ("pseudo = lax + marking")? | **Solved** (researcher, verified): C1 and C1′ in (∞,ω) and every finite n. C1″ holds without "locally full". | Assumed by `planar-pasting-types.md` §4. Bears on `catt-lim-pseudo-vs-gray.md`. | `internal-hom.md` §5.5 |
| `planar-pasting-types.md` | An unbiased theory of biclosed monoidal categories via balanced Lambek types (1-dimensional case proved). PL1: tensor. PL-ω: Gray version. | PL1 very likely true (known coherence results, one lemma to cite). PL-ω open. | PL-ω uses `gray-vs-cartesian.md` | `internal-hom.md` §5.7 |
| `catt-lim-pseudo-vs-gray.md` | Does Mikhail's CaTT_lim universal property force cone-morphism cells to be invertible in a CaTT ambient? | **Answered: yes** (researcher, verified). It even forces cells of dimension ≥ 3 invertible. Corrected universal property given; printed `ctrf` rules need repair. Follow-ups open. | Related to `gray-vs-cartesian.md` | `limits-representables.md` §10.1 |
| `oriented-lax-limits.md` | In oriented (Gray-enriched) categories, is the *unrestricted* lax universal property of limits consistent (no forced invertibility), and does it give comma and hom objects? | Open; sent to an external researcher (2026-11-18) | Follows up `catt-lim-pseudo-vs-gray.md`; related to `strict-lax-interchange-at-every-level.md` | `pseudo-vs-gray.md` R11 |
| `lax-colimit-of-point.md` | Is the lax colimit of the constant point diagram over a free (∞,ω)-category the category itself? Syntactically, is the constant cocone context equivalent to the suspension? | Semantic: **solved**. Syntactic: **false** for arbitrary derivations of Mikhail's judgment (counterexample verified); open for a specified cocone construction | Step B uses `gray-contexts-in-catt.md` §6. A special case of `weighted-as-partially-lax-omega.md`. | `limits-representables.md` §10.3 |
| `weighted-as-partially-lax-omega.md` | Are weighted (co)limits in (∞,ω)-categories partially lax (co)limits over the Grothendieck construction of the weight? | **Solved** in Loubaton's model (researcher, verified). Finite computad test open. | Generalises `lax-colimit-of-point.md` | `limits-representables.md` §10.4 |
| `free-on-graph.md` | Is the free weak ω-category on a graph equivalent to the free category? | **Solved: yes** (external researcher, verified) | None | `limits-representables.md` §10.5 |

**Which files to send out.** Paste-ready prompts are in `outbox/`: send `outbox/naturality-arbitrary-depth.md` and `outbox/gray-contexts.md` as they are. The files in this folder keep the history, earlier responses and verifications. Files marked solved need no external work. Their literature sections say exactly which published results to cite. The best candidates for external researchers are G in `gray-contexts-in-catt.md`, `naturality-arbitrary-depth.md` (now §7 case 3, the 3-dimensional unitor over the 2-disc, and the proposed induction hypothesis (RC) in the verification), and the corrected `strict-lax-interchange-at-every-level.md` (dimension-4 boundary formulas, or a finite Γ forcing infinitely many cells). `oriented-lax-limits.md` has been sent to a researcher.
