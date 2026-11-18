# Conjectures and open problems

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

A literature search was done on 2026-11-18. Each file has a "Literature search" subsection. Summary: two problems are partly answered by existing work (the strict Gray tensor of free ω-categories is free; the (∞,1) version of the lax colimit of the point), and none is fully answered.

| File | Problem | Origin |
|---|---|---|
| `catt-lim-pseudo-vs-gray.md` | Does Mikhail's CaTT_lim universal property force cone-morphism cells to be invertible in a CaTT ambient? | `limits-representables.md` §10.1 |
| `gray-contexts-steiner.md` | Do Mikhail's Gray contexts `Γ ⊗ Dⁿ` exist for all n and present the Steiner Gray tensor? | `limits-representables.md` §10.3 |
| `lax-colimit-of-point.md` | Is the lax colimit of the constant point diagram over a free (∞,ω)-category the category itself? | `limits-representables.md` §10.3 |
| `weighted-as-partially-lax-omega.md` | Are weighted (co)limits in (∞,ω)-categories partially lax (co)limits over the Grothendieck construction of the weight? | `limits-representables.md` §10.4 |
| `free-on-graph.md` | Is the free weak ω-category on a graph equivalent to the free category? | `limits-representables.md` §10.5 |
| `steiner-support-determines-cells.md` | In free strict ω-categories on Steiner complexes (e.g. Gray tensors of pasting diagrams), are cells determined by their dimension and set of generators? | `pseudo-vs-gray.md` §3.6, lemmas (A)–(C) |
| `free-infinity-gray-of-pasting-diagrams.md` | Are Gray tensors of globular pasting diagrams free as (∞,n)-categories (scope of Campion's pasting theorem)? | `pseudo-vs-gray.md` §3.6, (D)–(F) |
| `strict-lax-interchange-at-every-level.md` | Construct free strict ω-categories in which *every* interchange law is a directed cell, with cells determined by generators. | `pseudo-vs-gray.md` §2.5, §3.6 |
| `gray-vs-cartesian.md` | Is Dᵏ × Dˡ the Gray product Dᵏ ⊗ Dˡ with mixed cells inverted ("pseudo = lax + marking")? | `internal-hom.md` §5.5 |
| `gray-contexts-in-catt.md` | Do frame-acyclic molecules (e.g. boundaries of Gray generators) have composites in CaTT, unique up to invertible cells? | `internal-hom.md` §4.3 |
| `planar-pasting-types.md` | Unbiased theory of biclosed monoidal categories via balanced Lambek types (1-dim proved); tensor/unit and ω-version open | `internal-hom.md` §5.7 |
| `naturality-arbitrary-depth.md` | Does every CaTT coherence over a pasting context have a naturality cell for every up-closed set of variables, of any depth? (Extends BMOSV beyond depth 1; one depth-2 case settled.) | `free-objects.md` §7.1 |
