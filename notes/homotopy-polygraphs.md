# Homotopy polygraphs: homotopical iff bubble-free

*Owner: thread "Prove polygraphs homotopical iff bubble-free" (HPOL). Started 2026-11-19. Open-issues row B24.*

**Question.** Let Γ be a finite polygraph and `c_Γ : Free(Γ) → F(Γ)` the comparison from the free (∞,ω)-category to the free strict ω-category. Γ is *homotopical* when c_Γ is an equivalence. Is Γ homotopical iff F(Γ) is **bubble-free in every dimension**, i.e. has no non-identity n-cell `e : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c` (n ≥ 2, c a k-cell, 0 ≤ k ≤ n − 2)? Such an e is an *iterated-identity endo-cell*.

**Status.**

| Direction | Dimension 2 | Every dimension |
|---|---|---|
| homotopical ⟹ bubble-free | proved (researcher, verified) | **proved here, Theorem N (§1)**, all k |
| bubble-free ⟹ homotopical | proved (researcher, verified; Heidemann inputs on trust) | open; §3 |

Sources: `conjectures/answered/homotopy-polygraphs-2026-11-19.md` (dimension 2, Theorems A–C); follow-up prompt `conjectures/outbox/homotopy-polygraphs-r2.md`.

---

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

## 2. Bookkeeping: what the prompt asks and what is now known

The r2 prompt's Question 1 asked for the "only if" half for k > 0. Theorem N answers it, so the prompt is revised to state Theorem N under "What is known" and to ask only for sufficiency (most general form), with positivity in every dimension and dimension 3 as fallbacks.

---

## 3. Sufficiency: bubble-free ⟹ homotopical (in progress)

Plan, following the dimension-2 proof (Followup 2 of the answered file):

1. **Mesh model in dimension n.** X_Γ = colim over Γ-labelled n-meshes, with L_n j* X_Γ ≃ Free(Γ). The dimension-2 argument (§4 of Followup 2) uses only active/inert factorisation, normal forms, atomic Segal descent and the regularity pushout, each of which Heidemann states for all n. This step is expected to generalise verbatim, with n + 1 atom types (one per generator dimension) plus artificial atoms.
2. **Values on cells.** X_Γ(Q) ≃ ⊔_G B P_G over Γ-labelled n-diagrams G of shape Q, where P_G is the poset of normal marked meshes (*layerings*) of G.
3. **Combinatorial core.** Each component of B P_G is contractible when G has no closed component, and bubble-freeness in every dimension excludes closed components and automorphisms.
4. **π₀ is the strict cell.** Components of ⊔_G B P_G are exactly the n-cells of F(Γ).

Step 3 in dimension 3 is being tested by machine (`tools/layering3_check.py`, §4). Step 4 is where strictness enters: in dimension ≥ 3 the strict interchange identifies diagrams that are not isotopic as framed diagrams in general, and bubble-freeness has to exclude that.

## 4. Dimension-3 layering complexes (machine check)

*To be filled in with the checker's results.*

## 5. Heidemann inputs to the dimension-2 proof

The dimension-2 theorem takes four inputs from Heidemann (arXiv 2411.04870) on trust: active/inert factorisation, terminal labelled degeneracies (normal forms), atomic Segal descent, and the regularity pushout (5) (Lemma 4.1.0.12). Owned here: re-derive or machine-check them. *Plan and progress to be recorded here.*
