# Which polygraphs are homotopy polygraphs? From dimension 2 to every dimension

*A self-contained problem. It assumes familiarity with polygraphs (computads), strict ω-categories and (∞,ω)-categories, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general recognition theorem you can prove, valid in every dimension: ideally an exact characterisation of the finite homotopy polygraphs, and failing that the sharpest sufficient condition with a matching counterexample. Isolated low-dimensional examples are of little use to us.

## 1. Setting

- A **polygraph** Γ (computad) is a set of generators of each dimension, each n-generator having a source and a target which are parallel (n−1)-cells of the free strict ω-category on the lower generators. All polygraphs here are finite.
- `F(Γ)` is the free strict ω-category on Γ.
- `Free(Γ)` is the free (∞,ω)-category on Γ: generators are attached one at a time along their boundaries by pushouts of `∂Dⁿ → Dⁿ` in (∞,ω)-categories (Loubaton's Cat_ω, arXiv 2406.05425, or Campion's framework, arXiv 2311.00200). Strict ω-categories are (∞,ω)-categories, so there is a canonical comparison `c_Γ : Free(Γ) → F(Γ)`.
- Γ is a **homotopy polygraph** (or *homotopical*) when c_Γ is an equivalence, i.e. when every strict pushout attaching a generator is also a homotopy pushout.
- A 2-cell `1_x ⇒ 1_x` of F(Γ) other than the identity is a **bubble**.
- Γ is **positive in every dimension** when every generator of dimension n ≥ 2 has a source and a target that are not identity cells. (For n = 2: both boundary paths are nonempty.)
- More generally, a non-identity n-cell `e : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c` (n ≥ 2, source and target both the (n−1)-dimensional iterated identity of a k-cell c, k ≤ n−2) is an **iterated-identity endo-cell**. Γ is **bubble-free in every dimension** when F(Γ) has none. For n = 2, k = 0 these are the bubbles.
- A strict ω-functor p : C → D is a **discrete Conduché functor** when every factorisation of p(x) in D lifts uniquely to a factorisation of x in C.

## 2. Why it matters

Homotopy polygraphs are exactly the computads whose free (∞,ω)-category can be computed strictly. Finite presentations of Grothendieck constructions over a free base, the comparison of weak and strict free objects in type theories for weak ω-categories, and pasting theorems for non-globular shapes all need this hypothesis, and at present each use checks it by hand. Dimension 2 is now settled exactly (item 5 below); everything above dimension 2 is open beyond closure rules.

## 3. What is known

1. **Pasting theorems.** For a strongly loop-free Steiner complex K, ν(K) is the free (∞,ω)-category on its atoms (Campion, *Pasting diagrams in higher categories are free*, arXiv 2311.00200). Chanavat (*A strengthened (∞,n)-categorical pasting theorem*, arXiv 2603.22242) extends this to regular directed complexes with frame-acyclic molecules (Thm 3.17), and deduces that positive 2-polygraphs (Cor. 3.39) and regular 3-polygraphs in Henry's sense (Cor. 3.38) are homotopical. Comment 3.40 there describes the extension to arbitrary regular and positive polygraphs as expected, without proof.
2. **Bubbles obstruct.** If F(Γ) has a bubble q, sending every 2-generator to 1 gives r : F(Γ) → B²ℕ with r(q) = k > 0, and q defines i : B²ℕ → F(Γ) by Eckmann–Hilton; ri = [k] acts by kʲ on H_{2j}(K(ℤ,2); ℚ), so the groupoidification of F(Γ) has nonzero rational homology in every even degree, while that of Free(Γ) is a finite CW complex. Example: (x; σ : 1_x ⇒ 1_x), F(Γ) = B²ℕ ≃ K(ℤ,2) after groupoidification, Free(Γ) ≃ S².
3. **Bubble-freeness is undecidable**, already for one-vertex 2-polygraphs with no generating bubble (reduction from reachability in positive semi-Thue systems via an insertion rule 1 ⇒ L w Z and a deletion rule L v Z ⇒ 1).
4. **Dimension 2, combinatorial core.** For a progressive one-colour string diagram G every component of which meets the boundary, the cell complex K_G whose vertices are the *tier encodings* of G (decompositions into layers of simultaneous generators) and whose faces are products of permutohedra (splitting a layer) has contractible components. Proof: right-exchange runs (which terminate for boundary-connected diagrams, Delpeuch–Vicary arXiv 1804.07832, Cor. 2.16) give a unique maximal cell F(v) with source v; deleting vertices in topological order removes a closed star along its antistar, a ball. Two floating scalars give a circle, so the boundary condition is needed.
5. **Dimension 2, exact answer.** A finite 2-polygraph is homotopical **iff it is bubble-free**. The "if" direction uses item 4 and Heidemann's mesh model of (∞,2)-categories (arXiv 2411.04870): a presheaf X_Γ on meshes with L₂ j*X_Γ ≃ Free(Γ), and an objectwise equivalence j*X_Γ → N₂F(Γ) computed as X_Γ(Q) ≃ B(Q↓t) ≃ ⊔_G BP_G over the diagrams G of shape Q, with each BP_G contractible by item 4 (a bubble-free polygraph has no boundary-disjoint diagram component and no diagram automorphisms). Consequences: homotopicality of finite 2-polygraphs is undecidable (item 3); the finite case of Guetta's conjecture (homologically coherent ⟺ bubble-free, *Homology of strict ω-categories*, arXiv 2104.12662, Conj. 6.6.5) holds; every 2-polygraph whose 2-generators all have non-empty target (or all non-empty source) is homotopical, with any number of vertices.
6. **Suspensions.** Σ^k Γ is homotopical iff Γ is (Hom_{ΣC}(0,1) ≃ C, and suspension preserves and detects the comparison). So for 2-polygraphs, Σ^k Γ is homotopical iff Γ is bubble-free.
7. **Graph assembly, every dimension.** For a finite directed graph Q (loops and parallel edges allowed) and finite polygraphs P_e on its edges, the polygraph B_Q(P_•) with vertices Q₀ and (r+1)-generators ⊔_e (P_e)_r (the free category on Q enriched in the F(P_e)) is homotopical iff every P_e is. In particular **adjoining a 1-generator preserves homotopicality in every dimension**.
8. **Discrete Conduché descent (Theorem A).** If p : Γ → Δ is a polygraph map with F(p) discrete Conduché and Δ homotopical, then Γ is homotopical. Surjectivity on generators alone is not enough ([1] → F(loop)).
9. **Typing into positive templates (Theorem B).** A polygraph map Γ → Δ into a homotopical Δ that is source-positive or target-positive in every dimension makes Γ homotopical (Henry's cartesianness for such polygraphs makes F(p) discrete Conduché).
10. **Mapping cylinders (Theorem C).** Strict double mapping cylinders of finite homotopical presentations along arbitrary strict functors have finite homotopical presentations, with generators Δ_n ⊔ ℰ_n ⊔ Γ_{n−1}; Gray cylinders, cones and suspensions are instances (Loubaton arXiv 2406.05425 Thm 2.3.3.22, Campion's pasting theorem for Dⁿ ⊗ [1]). Items 7–10 give a sound finite-certificate system, but typing into templates from a good class cannot leave that class, so it does not reach all positive polygraphs.
11. **Positivity is not necessary.** (∗; t; η : 1 ⇒ t) is homotopical (Blans–Linskens, arXiv 2605.03150), and so is its suspension, a non-positive 3-polygraph. Regularity is not necessary either: the positive non-regular 3-polygraph x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r is homotopical.
12. **Positivity in the top dimension alone is not enough.** One vertex, b : 1 ⇒ 1, Ω : b ⇛ b: Ω has non-identity boundaries, but b is a bubble.
13. **Strict versus "stricter".** Chanavat (*Homotopy theory of stricter n-categories*, arXiv 2509.26563, Comment 2.67) gives a 4-dimensional regular directed complex whose molecules do not form a polygraph under strict composition. This is **not** a counterexample to the positive case: the extra equations appear in the passage from the free strict category to molecules, not in the free strict category itself.

14. **Higher bubbles obstruct in every dimension.** If a nonidentity n-cell is an endomorphism of an iterated identity on any k-cell, k ≤ n − 2, then the strict n-skeleton has nonzero mod-p cohomology in arbitrarily high degrees for some prime p. The free cellular n-skeleton has cohomological dimension at most n, and homotopicality passes to skeleta. This covers composite bubbles and positive-dimensional bases. [Proof of the higher-bubble obstruction](../answered/higher-bubble-obstruction-2026-11-19.md)

## 4. Questions

**Question 1 (main: the all-dimensional characterisation).** Is a finite polygraph Γ homotopical **iff F(Γ) is bubble-free in every dimension** (no iterated-identity endo-cell, §1)? This is the all-dimensional form of item 5. "Only if" for endo-cells of 1_x^{n−1} at a vertex x should follow by the argument of item 2 (an endo-cell q of 1^{n−1}_x gives Bⁿℕ → F(Γ) → Bⁿℕ with nonzero degree); please prove or refute it for endo-cells of 1^{n−1−k}_c with c of positive dimension k. For "if", the expected route is item 5's method one dimension up: a mesh or Θ-presheaf model of the free (∞,n)-category in which the fibres over each shape are classifying spaces of combinatorial complexes of "encodings" of a pasting diagram, contractible under the bubble-free hypothesis.

**Status, 2026-11-19.** Item 14 settles the “only if” conjecture over every base cell. The open direction is whether bubble-freeness suffices.

**Question 2 (positivity in every dimension).** If Question 1 is out of reach, prove that every finite polygraph that is positive in every dimension (§1) is homotopical — the "positive" half of Chanavat's Comment 3.40, which is a sub-case of Question 1 because positive polygraphs are bubble-free in every dimension. If it fails, give the smallest counterexample with a proof of non-homotopicality.

**Question 3 (dimension 3).** As a fallback, settle Question 1 for finite 3-polygraphs: is a finite 3-polygraph homotopical iff F(Γ) has no bubble and no non-identity 3-cell 1_{1_x} ⇛ 1_{1_x} or 1_f ⇛ 1_f? Item 4's combinatorics suggest the 3-dimensional analogue: contractibility of the complex of "layerings" of a boundary-connected 3-dimensional diagram in which no component is a closed 2-sphere.

## 5. What counts as a solution

A proof of Question 1, 2 or 3; a counterexample with a proof of non-homotopicality (for example by a homology computation as in item 2); or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40) and arXiv 2509.26563.
- Heidemann, arXiv 2411.04870 (mesh model of (∞,n)-categories).
- Delpeuch–Vicary, arXiv 1804.07832.
- Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guetta, arXiv 2104.12662 (Conj. 6.6.5, Thm 6.11); Guetta, *Polygraphs and discrete Conduché ω-functors*, Higher Structures 4(2) (2020).
- Loubaton, arXiv 2406.05425.
- Blans–Linskens, arXiv 2605.03150.
- No published recognition theorem for homotopy polygraphs in dimension ≥ 3 beyond the classes in item 1 was found.
