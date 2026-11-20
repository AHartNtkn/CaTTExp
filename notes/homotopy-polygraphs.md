# Homotopy polygraphs: homotopical iff bubble-free

*Owner: thread "Prove polygraphs homotopical iff bubble-free" (HPOL). Started 2026-11-19. Open-issues row B24.*

**Question.** Let Γ be a finite polygraph and `c_Γ : Free(Γ) → F(Γ)` the comparison from the free (∞,ω)-category to the free strict ω-category. Γ is *homotopical* when c_Γ is an equivalence. Is Γ homotopical iff F(Γ) is **bubble-free in every dimension**, i.e. has no non-identity n-cell `e : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c` (n ≥ 2, c a k-cell, 0 ≤ k ≤ n − 2)? Such an e is an *iterated-identity endo-cell*.

**Status.**

| Direction | Dimension 2 | Every dimension |
|---|---|---|
| homotopical ⟹ bubble-free | proved (researcher, verified) | **proved, all k**: Theorem N (§1, in-house) and independently the researcher (`conjectures/answered/homotopy-polygraphs-r2-2026-11-19.md` Responses 1–2; `conjectures/answered/higher-bubble-obstruction-2026-11-19.md`) |
| bubble-free ⟹ homotopical | proved (researcher, verified; Heidemann inputs on trust) | **false from dimension 3** (§0: positive, bubble-free 3-polygraph with a circle fibre); true for positive-to-one polygraphs and their dimensionwise duals (r2 Response 1 Thm 2) and for positive 3-polygraphs without matching idle overlaps (§0) |

Sources: `conjectures/answered/homotopy-polygraphs-2026-11-19.md` (dimension 2, Theorems A–C); follow-up prompt `conjectures/answered/homotopy-polygraphs-r2-2026-11-19.md`.

---

## 0. Sufficiency fails in dimension 3 (2026-11-20)

**Counterexample** (relative-coherence round, [`conjectures/answered/relative-coherence-all-dimensions-r6-2026-11-20.md`](conjectures/answered/relative-coherence-all-dimensions-r6-2026-11-20.md#researcher-response-3) Response 3, verified 2026-11-20). Objects 0 → 1 → 2 → 3, edges f₀, f₁ : 0 → 1, g : 1 → 2, h₀, h₁ : 2 → 3, 2-generators α₀, α₁ : f₀ ⇒ f₁ and β₀, β₁ : h₀ ⇒ h₁, 3-generators A : α₀g ⇛ α₁g and B : gβ₀ ⇛ gβ₁. Every generator has non-identity source and target, the 1-graph is acyclic, and counting occurrences of f₁, h₁ (resp. α₁, β₁) excludes endo-cells of every kind, so Γ is positive and bubble-free in every dimension. The strict 3-cell α₀gβ₀ ⇛ α₁gβ₁ is unique, but its fibre in Free(Γ) is S¹: the hom (∞,2)-category from 0 to 3 is (D × Q) ⊔_{Q×Q} (Q × D), two squares glued along their perimeter. So Γ is not homotopical, and **"bubble-free in every dimension ⟹ homotopical" is false**, as is "positive in every dimension ⟹ homotopical". Necessity (§1) and the dimension-2 theorem are unaffected; so is Guetta's Conj. 6.6.5, which is a statement about 2-categories.

**What goes wrong, in the terms of §4.** A and B are both whiskered by the idle wire g, so as regions of the 2-diagram they overlap on g and cannot fire in one 3-tier, yet each can fire first. The 3-tier sequences are then A | B and B | A with no common coarsening: Π_G is the braid fan on the cone {h_A ≠ h_B} minus its wall, two points instead of a contractible complex. The two exchange paths between the serial orders (β₀ placed before or after α₀ along g) close up into the circle. This is exactly the "pairwise" step of §4 ("two steps that can each fire first can fire together"), which fails here, and the step-4 caveat of §3 (strict interchange identifies diagrams that are not isotopic). The §4 checker never met it: its 3-steps are vertex regions with no idle boundary wires, so A and B would be the disjoint steps α₀ ⇛ α₁ and β₀ ⇛ β₁.

**What is known about the corrected question** (same file, Responses 4–10, not independently re-checked by HPOL):
- Positive 3-polygraphs in which no idle right suffix of a generating 3-face equals an idle left prefix of a generating 3-face have contractible fibres, hence are homotopical (Response 5). For width-preserving positive 3-polygraphs the matching test is exact (Response 4).
- Every weight-two fibre of a positive 3-polygraph is a point, an interval or a circle, and a circle occurs iff some path is an idle suffix of both faces of one generator and an idle prefix of both faces of another (Response 5).
- Full-support fibres can be spheres S^{k−1} for every k ≥ 2 ("seam rings"), with all weight-two fibres contractible (Response 8), so no finite-weight test suffices.

**Revised B24 question.** Give an exact characterisation of finite homotopical polygraphs in every dimension. Bubble-freeness in every dimension is necessary (Theorem N) and sufficient in dimension 2. From dimension 3 an extra condition on idle overlaps (seam cycles) is needed. The working conjecture is: bubble-free, plus no cycle of idle overlaps in any fibre. Its precise all-dimensional form is open. The follow-up prompt `conjectures/outbox/homotopy-polygraphs-r3.md` asks for it.

## 1. Necessity in every dimension (Theorem N)

**Theorem N.** If F(Γ) has an iterated-identity endo-cell, of any dimension n ≥ 2 and any k ≤ n − 2, then the finite polygraph Γ is not homotopical.

So the "only if" half of the all-dimensional characterisation holds, and the open half is sufficiency.

### Inputs

Write |C| for the ∞-groupoidification (left adjoint of the inclusion of spaces into Cat_ω) of an (∞,ω)-category C, and view strict ω-categories as (∞,ω)-categories.

- **(I1)** For q ≥ 1, |B^q ℕ| ≃ K(ℤ, q), and the generating q-cell represents a generator of H_q. (B^q M is the strict q-category with one cell in each dimension below q and M in dimension q.) Sketch: the inclusion of strict ω-categories preserves homs, so B^q ℕ is the q-fold delooping of the discrete E_∞-monoid ℕ; groupoidification of a delooping is the delooping of the group completion, and ℕ^{gp} = ℤ. The same input with q = 2 is used in the dimension-2 bubble obstruction (prompt item 2). Equivalently, via Ara–Maltsiniotis (*Comparaison des nerfs n-catégoriques*), |C| is the realisation of the Street nerve.
- **(I2)** Strict suspension agrees with (∞,ω) suspension (already used for the suspension theorem), and |ΣC| is the unreduced suspension of |C| (ΣC is the pushout of ∂[1] ← C ⊗ ∂[1] → C ⊗ [1], and |A ⊗ B| ≃ |A| × |B|).
- **(I3)** Γ is homotopical iff every skeleton Γ_{≤n} is (verified, `conjectures/answered/fibration-presentations-all-dimensions-2026-11-19.md`).
- Standard: |Free(Γ_{≤n})| is a finite CW complex, one cell per generator, since |·| preserves colimits and |∂Dⁿ → Dⁿ| = (S^{n−1} → D^n). Steenrod operations commute with the suspension isomorphism, and H*(K(ℤ,2); F_p) = F_p[ι₂].

### Proof

Fix e : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c in F(Γ), non-identity, and put q = n − k ≥ 2. Since n-cells of F(Γ) only involve generators of dimension ≤ n, e lies in F(Γ_{≤n}); by (I3) it suffices to show Γ_{≤n} is not homotopical.

1. **Counting map.** Sending every generator of dimension < n to an identity and every n-generator to 1 respects boundaries, so it defines a strict functor r : F(Γ_{≤n}) → B^n ℕ → B^n ℤ. Let m = r(e). An n-cell of a free n-category with no n-generator occurrence is an identity, so m ≥ 1.
2. **Section.** A strict functor Σ^k B^q ℕ → F(Γ_{≤n}) is a k-cell together with a monoid map from ℕ to the endomorphisms of its (n−1)-fold identity (q ≥ 2, so Eckmann–Hilton makes that monoid commutative, and Σ^k B^q ℕ has no composable pairs along dimensions below k). Take c and 1 ↦ e: this is s.
3. **The composite on cohomology.** By (I1)–(I2), |rs| : S^k K(ℤ,q) → K(ℤ,n), with S^k the unreduced k-fold suspension. Its class in H^n(S^k K(ℤ,q); ℤ) ≅ H^q(K(ℤ,q); ℤ) = ℤ is m: restrict along the q-sphere |Free(x; ω : 1^{q−1}_x ⇒ 1^{q−1}_x)| → |B^q ℕ|, whose k-fold suspension is the n-sphere that rs sends to m times the generating n-cell. Pick a prime p ∤ m.
4. **Infinitely many classes.** Let θ_j = P^{p^{j−1}} ⋯ P^{p} P^{1} (for p = 2, θ_j = Sq^{2^j} ⋯ Sq^4 Sq^2). Then θ_j ι₂ = ι₂^{p^j} ≠ 0 in H*(K(ℤ,2); F_p). For q ≥ 2, the (q−2)-fold cohomology suspension sends θ_j ι_q to θ_j ι₂, so θ_j ι_q ≠ 0. Hence
   (rs)*(θ_j ι_n) = θ_j (m · σ^k ι_q) = m · σ^k(θ_j ι_q) ≠ 0, in a degree that grows with j.
   Since (rs)* = s* r*, the map r* : H*(K(ℤ,n); F_p) → H*(|F(Γ_{≤n})|; F_p) is non-zero in infinitely many degrees.
5. **Conclusion.** If Γ_{≤n} were homotopical, |F(Γ_{≤n})| ≃ |Free(Γ_{≤n})| would be a finite CW complex, with mod-p cohomology in finitely many degrees. Contradiction. ∎

(The degree of θ_j ι_n is n + 2(p^j − 1) for p odd and n + 2^{j+1} − 2 for p = 2; only unboundedness matters.)

### Remarks

- **The rational argument does not extend.** The dimension-2 obstruction used rational homology of K(ℤ,2). For odd q, H*(K(ℤ,q); ℚ) is ℚ in degrees 0 and q only, so a rational retraction argument gives no contradiction. Mod-p cohomology with Steenrod operations works uniformly in q, and the section through Σ^k handles endo-cells over cells c of positive dimension, including loops c : x → x and composite c, where no retraction onto Σ^k B^q ℕ exists. (Example: x; a : x → x; α : a ⇒ 1_x; Ω : 1_a ⇛ 1_a. F has no bubble or vertex-level endo-cell, but Ω is an endo-cell of 1_a, so Γ is not homotopical. No strict functor F(Γ) → Σ B² ℕ sends a to the generating 1-cell, so a retraction argument would fail here; Theorem N only needs the map to B³ℤ.)
- **Finiteness is used** only in step 5.
- **Consequence for Guetta's Conjecture 6.6.5** (homologically coherent ⟺ bubble-free, stated for 2-categories): unchanged; the dimension-2 result already gives the finite case both ways. Theorem N gives the higher-dimensional analogue of the "homotopical ⟹ bubble-free" half.

---

## 2. Relation to the r2 researcher responses

The r2 prompt was sent and answered in parallel with this work (responses appended to `conjectures/answered/homotopy-polygraphs-r2-2026-11-19.md`). Response 1 Theorem 1 and Response 2 prove the same statement as Theorem N. Their route differs only in using the d = n − 2 fold hom, so that the scalar is always 2-dimensional (B² ℕ, ℂP^∞), where Theorem N uses B^{n−k} ℕ and the cohomology suspension down to ι₂. Response 1 also gives:
- **Theorem 2** (sufficiency for positive-to-one polygraphs: every d-generator, d ≥ 2, has a generating (d−1)-cell as target and a non-identity source; plus dimensionwise duals). This covers FTX's priority case (1) only when the 3-generators have generator targets; item 8's ζ : α ▷ r ⇛ β ▷ r has a whiskered target, so it is **not** covered.
- **Groupoidification is not a recognition test from dimension 3**: Π = (x; a : 1_x ⇒ 1_x; ε : a ⇛ 1_{1_x}) has contractible strict and weak groupoidifications but is not homotopical (it has a bubble in its 2-skeleton).
- The open step is contractibility of encoding spaces over a fixed strict cell, the same step §4 isolates.

## 3. Sufficiency: bubble-free ⟹ homotopical (in progress)

Plan, following the dimension-2 proof (Followup 2 of the answered file):

1. **Mesh model in dimension n.** X_Γ = colim over Γ-labelled n-meshes, with L_n j* X_Γ ≃ Free(Γ). The dimension-2 argument (§4 of Followup 2) uses only active/inert factorisation, normal forms, atomic Segal descent and the regularity pushout, each of which Heidemann states for all n. This step is expected to generalise verbatim, with n + 1 atom types (one per generator dimension) plus artificial atoms.
2. **Values on cells.** X_Γ(Q) ≃ ⊔_G B P_G over Γ-labelled n-diagrams G of shape Q, where P_G is the poset of normal marked meshes (*layerings*) of G.
3. **Combinatorial core.** Each component of B P_G is contractible when G has no closed component, and bubble-freeness in every dimension excludes closed components and automorphisms.
4. **π₀ is the strict cell.** Components of ⊔_G B P_G are exactly the n-cells of F(Γ).

Step 3 in dimension 3 is being tested by machine (`tools/layering3_check.py`, §4); the fibre turns out to be an infinite category in dimension 3 (§4). Step 4 is where strictness enters: in dimension ≥ 3 the strict interchange identifies diagrams that are not isotopic as framed diagrams in general, and bubble-freeness has to exclude that.

## 4. Dimension-3 layering complexes (machine check)

`tools/layering3_check.py` builds random marked 3-dimensional diagrams G (a planar diagram D₀ followed by 3-steps g : S_g ⇛ T_g, each replacing a whiskerable block; 3-positive steps, identity sources 1_w ⇛ T and identity targets S ⇛ 1_w; never both, which would be an endo-cell excluded by Theorem N) and enumerates layerings.

**Model K = 0 (the poset P_G).** A layering is a 3-tier sequence T₁ | ⋯ | T_r (sets of steps fired simultaneously), a 2-dimensional tier encoding of every singular slice S_i (L_{i−1} with each S_g, g ∈ T_i, contracted to a point), and **one** 2-dimensional encoding of every regular slice L_i, such that the legs S_i → L_{i−1}, S_i → L_i (expanding points to S_g, resp. T_g) are maps of 2-trusses. Order: refinement of 3-tiers together with the induced 2-truss maps of all slices. The script checks that the relation is a partial order, removes beat points, and computes Z/2 homology of the core.

Controls: with no 3-steps it reproduces the dimension-2 complexes; two floating scalars give a circle; two floating components, one rewritten by a 3-step, give a circle.

Results (2026-11-19):

| batch | diagrams tested | step kinds | non-contractible | poset size (max) |
|---|---|---|---|---|
| seed 4, 3-positive only | 101 | 1–3 positive steps | 0 | 427 |
| seed 3, all kinds | 79 | positive, identity source, identity target, mixed | 0 | 475 |
| seed 11, Quillen fibres | 79 (≥ 2 steps) | all kinds | 0 (Π_G and every upper fibre over a 3-tier sequence contractible) | 300 |
| seed 1, all kinds | 84 | all kinds | 0 (one further diagram with no K = 0 layering, two identity-source steps; see below) | 487 |

So in every case P_G is contractible when it is non-empty, and the forgetful map P_G → Π_G to 3-tier sequences has contractible upper fibres, which suggests the proof route "Quillen's Theorem A over Π_G, plus contractibility of Π_G" (Π_G is the 3-dimensional analogue of the dimension-2 tier complex, with steps in place of vertices).

**Finding: P_G is not the whole fibre.** One generated diagram (seed 5; an identity-source step g₀ that caps a wire and creates a floating vertex, then a positive step g₁ whose source contains a p = 0 vertex) has **no** K = 0 layering at all, although it is a valid strict 3-cell: between g₀ and g₁ the slice must be isotoped (the p = 0 vertex moves past the new cap), and K = 0 allows no isotopy between consecutive 3-tiers. In Heidemann's normal meshes such isotopies are *interchange slices*: artificial singular slices L ← A → L′ with A a common coarsening and not both legs identities. They cannot be normalised away (the two regular slices differ), so the true fibre over the 3-cube is the classifying space of an **infinite** category of layerings (zigzags of any length). Truncating at K interchange slices per gap is not a homotopy-correct approximation: for D₀ = two parallel vertices and no steps, K = 0 gives a point, K = 1 a wedge of two circles, and K = 2 is not even a poset (`meshes_k`, `analyse_k`).

**Consequence for the plan.** (B₃) must be proved for the infinite category. The expected argument: fibre it over 3-tier sequences; between consecutive singular slices the interchange zigzags form path spaces in a regular slice's encoding complex, which is contractible by the dimension-2 theorem whenever that slice is bubble-free, so each gap contributes a contractible factor; what is left is a finite complex built from 3-tier sequences and singular-slice encodings. A first attempt at that finite model (singular encodings only, with an existential condition on the regular slice between split tiers) is not transitive, so the reduction has to be done as a homotopy colimit, not as a poset. **Open (owned):** state and prove that reduction, then rerun the check on the reduced model.

**Model fix (2026-11-19, after the table above).** The singular-slice builder processed the steps of a tier in name order, so an identity-source point on a boundary wire of a positive region in the same tier was rewired before the region was contracted and left a dangling port; such tiers were wrongly rejected. Regions are now contracted first and identity-source points placed afterwards (points stacked on one wire in dependency order). Rerun of the full check, seed 5, 26 diagrams: no non-contractible P_G (one EMPTY of the kind described next).

**Trace structure of Π_G (checked; proof below).** For every tested diagram, the valid 3-tier sequences are exactly the ordered partitions of the step set compatible with one partial order ≺_G (a ≺_G b if a precedes b in every valid sequence), with antichains as blocks: the singleton sequences are the linear extensions of ≺_G, and every antichain is a valid 3-tier at every down-set. Batches: seed 1 all kinds 150, seed 2 all kinds 200, seed 3 3-positive 200 (`trace` test, scratch). Before the model fix, 23 antichains failed, all through the dangling-port artifact.

*Why it holds.* Whether g may fire at stage X depends on S_g being present and convex in D(X); presence is monotone (generated by "h produces a vertex or wire of S_g") and convexity of a fixed block fails only through a path through a vertex produced or consumed by another step, which is again a pairwise relation. Simultaneity of a set T is the conjunction of pairwise disjointness of the regions, and an acyclicity argument shows no third step can obstruct a pair that is individually orderable both ways. So the admissible height functions h : steps → ℝ (generic layerings up to isotopy of heights) form the open polyhedral cone C_G = {h : h_a < h_b whenever a ≺_G b}, and Π_G is the poset of cells of the braid arrangement contained in C_G.

*Π_G is contractible.* C_G is a non-empty open convex cone (a linear extension exists), a union of open cells of the braid fan. If ≺_G is discrete, Π_G has the one-block sequence as an extremal element. Otherwise C_G misses the diagonal line, and Π_G is an upward-closed set of cells of the regular CW decomposition of the sphere S(ℝⁿ/ℝ·𝟙); the order complex of such a set is homotopy equivalent to the union of its open cells, here C_G ∩ S, an open convex subset of a hemisphere, hence contractible. This is the 3-dimensional analogue of the dimension-2 tier complex, with steps in place of vertices. The pairwise-obstruction claim holds for steps without idle boundary wires (all the checker generates). It is false in general (§0): two steps whiskered by a common idle wire can each fire first without being simultaneous, and then Π_G is a cone minus walls. **Open (owned):** write it out, then do the hammock reduction of the fibre to Π_G (previous paragraph).

## 5. Heidemann inputs to the dimension-2 proof

The dimension-2 theorem takes four inputs from Heidemann, *Manifold diagrams for higher categories* (arXiv 2411.04870v1, a thesis), on trust: active/inert factorisation of truss maps, terminal labelled degeneracies (normal forms), atomic Segal descent, and the regularity pushout (5) of the answered file. Owned here (B24(c)): re-derive or machine-check them.

**What the thesis states** (read from the arXiv PDF, 2026-11-19):
- **Lemma 4.1.0.5.** For an open n-truss E, Grid(E) = Ṫn(⊞(−), E) is the free n-uple Segal space with one generator per atom A ↪ E. Proof by induction on n: E is a zigzag R₀ ← S₀ → R₁ ⋯ of (n−1)-trusses, Grid(E) is the free Segal object on the graph ⊔Grid(S_i) ⇉ ⊔Grid(R_i), and atoms of E correspond to atoms of the R_i (if stype_n = 0) or of the S_i (if stype_n = 1).
- **Corollary 4.1.0.6** (atomic covers go to colimits in Seg(Δⁿ)) and **Lemma 4.1.0.12** (Grid(A) ≃ Grid(∂A) ⊔_{Grid(∂□A)} Grid(□A) in Seg(Δⁿ), for every atom A) are immediate from 4.1.0.5: both sides are free on the same generators.
- **Theorem 4.1.0.13**: restriction gives Seg^r(Ṫn) ≃ Seg(Δⁿ) (regular Segal presheaves on trusses = n-uple Segal spaces).
- **§4.4.3**: for every n-diagrammatic computad Σ, a free (∞,n)-category 𝔽(Σ) whose values are spaces of Σ-labelled n-manifold diagrams (Theorem 4.4.2.5, Construction 4.4.3.1), with a right adjoint (Prop. 4.4.3.3).

**How the dimension-2 proof uses them.** Equation (5) of the answered file is Lemma 4.1.0.12 after the localisation L₂ (a left adjoint, so it keeps pushouts) and restriction j* (which keeps colimits). Atomic Segal descent (8) is Corollary 4.1.0.6 mapped into a complete C. So the analytic input reduces to **Lemma 4.1.0.5**, a statement about set-valued presheaves (Grid(E) is discrete), plus the truss combinatorics (active/inert factorisation, normal forms) used in §§4.2–5.3.

**Plan.**
1. Machine-check Lemma 4.1.0.5 for open 2-trusses up to a size bound: enumerate maps from grids [k₁, k₂] into E and compare with the nerve of the free double category on the atoms of E (the free Segal object on a discrete graph is levelwise the set of composable strings). Also machine-check active/inert factorisation and uniqueness of terminal labelled degeneracies on the same trusses.
2. Write the induction of Lemma 4.1.0.5 out in full for n = 2 (it is short).
3. With 1–2, the dimension-2 theorem depends on Heidemann only through standard definitions, and the Guetta Conj. 6.6.5 consequence is unconditional up to these checks.

**Consequence for every dimension.** §4.4.3 gives the all-dimensional analogue of the dimension-2 model directly: 𝔽(Σ_Γ) for the diagrammatic computad Σ_Γ whose atoms are the generators of Γ. Sufficiency in dimension n then reduces to (A_n) 𝔽(Σ_Γ) ≃ Free(Γ) (the cell-attachment property, which follows from Lemma 4.1.0.12 as in dimension 2) and (B_n) on each cell shape X, the evaluation from the space of Σ_Γ-labelled diagrams to the strict cells of F(Γ) has contractible fibres and is a bijection on π₀. (B₃) is what `tools/layering3_check.py` tests.
