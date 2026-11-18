# Lax functors as a directed coherence: are comparison cells decided by supports?

> **Status: open (2026-11-18).** Written by the thread "Extend toward ordinary mathematics" (ledger F6, F6a). Self-contained: no knowledge of the project is assumed.

## Background

**Weak ω-categories and CaTT.** CaTT (Finster–Mimram, LICS 2017) is a dependent type theory whose models are weak ω-categories. Its single term former `coh` produces, for a *pasting context* Θ (a context presenting a globular pasting diagram) and two terms u, v over Θ that are parallel and each use every variable of Θ ("full support"), a cell `u → v`. Every such cell is invertible. Composition operations are the case where u and v use exactly the source and target boundary variables of Θ. In CaTT, "coherence" therefore means: *a cell exists between two parallel composites iff a support (free-variable) condition holds*.

**A directed variant.** One can ask for a directed version of this pattern: a rule producing a cell `u → v` (and not `v → u`) when a *support condition computed on a Steiner complex* holds. For the Gray tensor product of pasting diagrams this is known to be the right picture: in a free strict ω-category on a loop-free Steiner complex, cells are determined by their supports (Steiner 1993; for Gray tensors of pasting diagrams this follows from Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273, Prop. 8.3.17 and Thm 11.2.18), and these Gray tensors are free as (∞,n)-categories (Campion, arXiv 2311.00205, Cor. 3.5).

**Lax functors.** A (normalised) lax functor F : A ⇝ B between 2-categories assigns objects, 1-cells and 2-cells, with comparison 2-cells `F f ; F g → F(f ; g)` (here diagrammatic order) satisfying associativity and unit axioms, and `F 1 = 1`. Oplax functors reverse the comparison. A lax functor out of the terminal category, without normalisation, is a monad (Bénabou).

**Orientals and nerves.** Street's orientals O_n are the free strict ω-categories on the n-simplex (as a Steiner/parity complex). The Street nerve of an ω-category B has as n-simplices the strict ω-functors O_n → B. For a 2-category B, the simplices are exactly the normalised (op)lax functors [n] ⇝ B, where [n] is the ordinal poset (Street; Duskin; see e.g. Gagna below). For a small category A, write `c_∞ N(A)` for the strict ω-category obtained by gluing orientals along the nerve of A (the left adjoint of the Street nerve applied to N(A)).

## Statement

Fix a finite category A whose nerve has finitely many non-degenerate simplices (for instance the free category on a finite directed acyclic graph, or a finite poset). Let Λ(A) be the normalised Steiner chain complex of N(A) (the "oriental complex" of A), so that `c_∞ N(A)` is the free strict ω-category ν Λ(A) on it, when Λ(A) is a Steiner complex.

An **F-image term** over A is a formal composite in the free strict ω-category `c_∞ N(A)` of generators (each non-degenerate simplex of N(A) is a generator); its **support** is the set of generators it uses, recorded with dimensions.

**Conjecture LF.**
1. (*Steiner.*) Λ(A) is a loop-free unital Steiner complex, so `c_∞ N(A) = ν Λ(A)` and its cells are determined by their supports.
2. (*Directed coherence.*) For parallel cells u, v of `c_∞ N(A)` there is a cell u → v iff a decidable support condition holds; when it holds, the cell is unique. For a chain A = [k], in dimension 2 the condition says "the partition of the path 0 → k given by u refines that given by v", and the cells form the Gray cube `(D¹)^{⊗(k−1)}` as `Hom_{O_k}(0, k)`.
3. (*Weak version.*) The same holds in the free *weak* ω-category on the computad presenting `c_∞ N(A)`, up to equivalence: the comparison from weak to strict is an equivalence, and parallel cells are connected by a cell iff they are in the strict model, with contractible choices. (For A = [n] this is Maehara's theorem below.)
4. (*Normalised oplax functors.*) For every weak ω-category B, the ω-category of maps `c_∞ N(A) → B` (weak sense) is equivalent to an ω-category of normalised oplax ω-functors A ⇝ B, for any reasonable definition of the latter that restricts to the known ones in dimensions ≤ 3.

If LF holds, a type theory can have *lax-functor variables* F : A ⇝ B whose comparison cells are produced by a single directed coherence rule with a support side condition, exactly as CaTT's `coh` produces invertible coherences.

## What is known

- **Orientals are Steiner complexes and loop-free** (Steiner 1993, *The algebra of directed complexes*; Street 1987, *The algebra of oriented simplexes*). So part 1 holds for A = [n], and the support statement of part 2 then holds for O_n by Steiner's theory.
- **Homs of orientals** are cubes: `Hom_{O_n}(0, n)` is the (n−1)-dimensional Gray cube **[recall, to be checked]**.
- **Gagna, *On a notion of oplax 3-functor*, arXiv 2004.14220.** Normalised oplax 3-functors between strict 3-categories correspond bijectively to simplicial maps between Street 3-nerves sending certain "constraint" simplices with trivial top cell to such; for a 1-category A without split monomorphisms or split epimorphisms, `c_∞ N(A)` is described and its universal property verified (§5). This is part 4 in dimension ≤ 3, for strict B.
- **Maehara, *Orientals as free weak ω-categories*, arXiv 2102.09736.** The orientals are also free *weak* ω-categories on the same generating data; the proof identifies the Street nerves of orientals as fibrant replacements of simplices in Verity's model structure for complicial sets. This is part 3 for A = [n].
- **Dwyer–Kan-type rigidity for 1-categories** (free categories on graphs have discrete homs as ∞-categories) suggests that gluing orientals along N(A) does not create extra homotopy when A is loop-free, but this is not a proof.
- **Not known to us:** whether Λ(A) is loop-free for every finite A with finitely many non-degenerate simplices (the gluing along faces could create loops); whether part 2's uniqueness survives the gluing; any statement for B weak in all dimensions.

## What has been tried

- For A = [2]: `c_∞ N(A) = O_2` has a single 2-cell `f₀₁ ; f₁₂ → f₀₂`, and the conjecture is immediate.
- For A = [3]: `O_3` has four 2-cells and one 3-cell between the two composites `(f₀₁ ; α₁₂₃) · α₀₁₃` and `(α₀₁₂ ; f₂₃) · α₀₂₃`; the support condition picks out exactly this 3-cell. This is the associativity axiom of a lax functor, now a cell.
- For a non-poset A, e.g. the free category on `x → y → z` together with an extra edge `x → z`, Λ(A) is the union of two copies of O_2 sharing an edge; loop-freeness holds by inspection.

## Why it matters

Lax functors appear throughout higher category theory (monads, lax monoidal functors, lax actions). A type theory for weak ω-categories that only has strict or pseudo functors cannot state them directly. If the comparison cells of a lax functor are governed by a support condition, then a lax functor can be a *variable* in such a type theory, and all its coherence follows from one rule, in the same way that all the coherence of weak ω-categories follows from one rule in CaTT.

## What would count as a solution

A proof of parts 1–3 (part 4 can be taken as a definition), a counterexample (a finite loop-free A with Λ(A) not loop-free, or two parallel cells of `c_∞ N(A)` with the same support that differ), or references.

## Literature status (2026-11-18)

Searched: "lax functors orientals ω-categories Street nerve normal lax functor classifier". Found Gagna (2004.14220) and Maehara (2102.09736), described above; Verity's complicial sets (arXiv 1308.1532, *Complicial structures in the nerves of omega-categories*) for the nerve side. No statement of part 2 for general A was found.
