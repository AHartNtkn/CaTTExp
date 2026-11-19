# Extending the CaTT-models comparison: the unit condition beyond torsion-free computads, and a realization of L's coherator in every dimension

*Thread "Extend the models unit condition and L's coherator" (UCL), 2026-11-19. Owns E11-Q1 (unit condition (11) beyond torsion-free computads) and E11-Q4 (L's coherator in every dimension) in `open-issues.md`.*

*Background and notation are those of `conjectures/answered/catt-models-unit-condition-2026-11-19.md` (the prompt's Known (I)–(VI) and the verified response). In brief: A_𝔠 is the free CaTT model on a finite computad 𝔠, F(𝔠) the free strict ω-category, π_𝔠 : A_𝔠 → F(𝔠) the strict-image map, 𝓛_R ⊣ S₀ the realization adjunction between CaTT models and algebraically fibrant complete Segal Θ_ω-spaces 𝒜, η the unit, W the Fujii–Hoshino–Maehara (FHM) ω-weak equivalences, Q coinductive completion, and*

```
(11)_𝔠    η_{A_𝔠} ∈ W.
```

*The verified response shows that (11) for all finite computads implies the homotopy hypothesis for Lanari's coherator 𝕋^bi, so the general case is not the target. Part A extends the torsion-free reduction to every finite computad and isolates exactly what (11) says on the others. Part B gives L's coherator a realization in every dimension.*

---

## Part A. The unit condition for every finite computad

### A.1 Relative coherence with identity image

For a finite computad 𝔠 define

```
RC_id(𝔠)   for every n and all parallel n-cells a, b of A_𝔠 with π a = π b,
           there is an (n+1)-cell u : a → b with π u = 1_{π a}.
```

The response's RC (no condition on π u) is equivalent to RC_id when every endo-(n+1)-cell of F(𝔠) on an n-cell is an identity (𝔾-regularity, which holds for torsion-free complexes). With loops it is strictly weaker: for 𝔠 = (x; f : x → x; α : f ⇒ f), the pair (f, f) is joined by α itself, whose image is not an identity. RC_id is the statement that matters.

### A.2 Lemma (free strict ω-categories on finite polygraphs are gaunt)

**Lemma A.2.** Let 𝔠 be a polygraph with generators in dimensions ≤ N. Every coinductively invertible cell of F(𝔠) is an identity.

*Proof.* For an n-cell w of F(𝔠), n ≥ 1, let c_n(w) ∈ ℕ^{𝔠_n} be the multiset of n-generators occurring in an expression of w. It is well defined: every axiom of strict ω-categories (associativity, units, interchange, and the identity laws 1_x ∗_k 1_y = 1_{x ∗_k y}) preserves the multiset of n-generators of an n-dimensional expression. It is additive, c_n(u ∗_k v) = c_n(u) + c_n(v) for k < n, and c_n(1_x) = 0. A cell with c_n(w) = 0 has an expression built from identity n-cells only, so it is an identity.

Induct downward on dimension. Cells of dimension > N are identities. Suppose every invertible (n+1)-cell is an identity, and let w be an invertible n-cell with inverse w′ and invertible witness e : w ∗_{n−1} w′ → 1. Then e is an identity, so w ∗_{n−1} w′ = 1 strictly. Hence c_n(w) + c_n(w′) = 0 in ℕ^{𝔠_n}, so c_n(w) = 0 and w is an identity. ∎

(c_n is the top component of the canonical ω-functor F(𝔠) → λ(ℤ𝔠) to Steiner's ω-category of the polygraphic chain complex, restricted to non-negative chains; the argument above avoids needing that functor.)

### A.3 Theorem A (the trivial-fibration criterion holds for every finite computad)

**Theorem A.** For every finite computad 𝔠,

```
π_𝔠 ∈ W   ⟺   π_𝔠 is a globular trivial fibration   ⟺   RC_id(𝔠).
```

*Proof.* (RC_id ⇒ trivial fibration.) The boundary-correction lemma and the initial-lift induction of the response (§4.3–4.4 of its Q3 part) use exactly hypothesis (I) there, which is RC_id. They use nothing else about 𝔠: generators lift to generators, identities and composites lift by induction on strict expressions, and whiskering by RC_id witnesses does not change strict images because the witnesses map to identities.

(Trivial fibration ⇒ W.) As in FHM: a globular trivial fibration is essentially surjective with identity comparison cells.

(W ⇒ RC_id.) Let a ∥ b with π a = π b. FHM essential surjectivity with prescribed boundary (a, b), applied to 1_{π a}, gives u : a → b and an invertible cell π u → 1_{π a} in F(𝔠). By Lemma A.2 that cell is an identity, so π u = 1_{π a}. ∎

So the regularity input of the response (Campion's 𝔾-regularity) is not needed. Only gauntness of F(𝔠) is used, and that holds for every finite polygraph.

### A.4 Theorem B (homotopy polygraphs) and Theorem C (the rest)

Let e_𝔠 : 𝓛_R A_𝔠 → N F(𝔠) be the adjunct of π_𝔠 (N F(𝔠) carries its canonical algebraic structure, F(𝔠) being gaunt). The adjunction identity is

```
S₀(e_𝔠) ∘ η_{A_𝔠} = π_𝔠.                                                (∗)
```

Call 𝔠 **Q-homotopical** when Q U(e_𝔠) is an equivalence. Since 𝓛_R turns generator attachments into homotopy pushouts (Known (VI), filtration), 𝓛_R A_𝔠 presents the free (∞,ω)-category on 𝔠 and e_𝔠 is the canonical comparison c_𝔠 : Free(𝔠) → F(𝔠) of `conjectures/outbox/homotopy-polygraphs.md`. So every homotopy polygraph in the sense of that file is Q-homotopical.

**Lemma A.4.** S₀(e_𝔠) ∈ W ⟺ 𝔠 is Q-homotopical.

*Proof.* (⇐) is the reflection statement (A) of the response (part 2, §3.1): Q U f an equivalence ⇒ S₀ f ∈ W. (⇒) is detection, Known (IV). ∎

Two-out-of-three for W (FHM, from 2-out-of-6) applied to (∗) gives:

**Theorem B.** If 𝔠 is Q-homotopical, then (11)_𝔠 ⟺ π_𝔠 ∈ W ⟺ RC_id(𝔠).

**Theorem C.** If 𝔠 is not Q-homotopical, then (11)_𝔠 ⇒ ¬RC_id(𝔠). Equivalently, a non-homotopical finite computad satisfying RC_id is a counterexample to (11).

**Corollary C′.** (11) for all finite computads implies: for every finite computad 𝔠, RC_id(𝔠) ⟹ 𝔠 is Q-homotopical. Together with Theorem B, (11) makes RC_id, a statement about CaTT terms over 𝔠, an exact test for homotopicality on the class where RC_id holds; and on homotopical computads it makes RC_id equivalent to (11)_𝔠.

So, for each finite computad, (11)_𝔠 is equivalent to an RC-type statement exactly when 𝔠 is homotopical; on non-homotopical computads (11)_𝔠 predicts the *failure* of relative coherence.

### A.5 The classes now covered, beyond torsion-free

By Theorem B, (11)_𝔠 ⟺ RC_id(𝔠) for every finite computad in the known homotopical classes (all listed with sources in `conjectures/outbox/homotopy-polygraphs.md` §3):

- strongly loop-free Steiner complexes (Campion), the torsion-free case of the response;
- **positive 2-polygraphs, loops and cycles allowed** (Chanavat, arXiv 2603.22242, Cor. 3.39), e.g. (x; f : x → x; α : f ⇒ f ∗₀ f);
- regular 3-polygraphs in Henry's sense (Chanavat, Cor. 3.38);
- the partition-test class of item 7 (adjoining 1-generators, loops allowed, preserves homotopicality in dimension 2), the operadic class of items 4–5 (e.g. (∗; t; η : 1 ⇒ t)) and its suspensions, item 9's non-regular 3-polygraph, item 10's attachments.

For these the unit condition is now exactly relative coherence with identity image. RC_id is the RC program (C1, D2, B19), whose outbox prompt `relative-coherence-all-dimensions.md` already asks about homotopy polygraphs in its Question 2; the RC_id refinement (identity image is needed once loops are allowed) is passed to its owner (RCX).

Sanity check: for a finite graph G (loops allowed) Known (IV) gives α_G a globular trivial fibration, i.e. RC_id(G); graphs are homotopical (Free(G) ≃ N Path(G)); Theorem B then gives (11)_G, matching Known (IV).

### A.6 The bubble: Theorem C is consistent with (11) on the first non-homotopical computad

𝔠_○ = (x; α : 1_x ⇒ 1_x) is not homotopical (`homotopy-polygraphs.md` item 2: F(𝔠_○) groupoidifies to K(ℤ,2), Free(𝔠_○) to S²). Theorem C says (11)_{𝔠_○} forces RC_id to fail. It does fail, at the first candidate pair, modulo one identification flagged below.

**Proposition D (sketch; one step to check).** Let EH be a CaTT 3-term over the context (x; a, b : 1_x ⇒ 1_x) of type a ∗₁ b ⇛ b ∗₁ a (an Eckmann–Hilton term), and σ := EH[a ↦ α, b ↦ α]. Then σ and 1_{α ∗₁ α} are parallel with the same strict image (F(𝔠_○) has no non-identity 3-cells), and no 4-term σ ⇛ 1_{α ∗₁ α} exists in A_{𝔠_○}.

*Argument.* Take B = super vector spaces over a field of characteristic 0, with its braided monoidal structure, and let Y ∈ 𝒜 present the 3-truncated (∞,3)-category B²B (one object, one 1-cell, objects of B as 2-cells, morphisms as 3-cells; both ∗₀ and ∗₁ of 2-cells realise ⊗). Let m : A_{𝔠_○} → S₀Y send α to the odd line L. A 4-cell Φ : σ ⇛ 1 would give m(Φ), which in a 3-truncated model forces m(σ) = id in End(P), where P = m(α ∗₁ α) ≅ L ⊗ L (source and target of m(σ) are the same cell, so one witness iso conjugates both sides). The claim to check is

```
(EH-odd)   m(σ) corresponds, under P ≅ L ⊗ L, to an odd power of the braiding c_{L,L}.
```

Granted (EH-odd), m(σ) = (−1)^{odd} = −1 ≠ id, so Φ does not exist. (EH-odd) is a strand-permutation statement: over two distinct generators X, Y in the free braided monoidal category, Hom(X⊗Y, Y⊗X) consists of odd braids only, so any term of EH's type realises as an odd braid; what needs care is transporting this along the specialisation X, Y ↦ L, because a braided functor between the generic and specialised models need not be a map in 𝒜 (it need not preserve chosen fillers). A second route avoids the specialisation: interpret A_{𝔠_○} in a CaTT model built from the doubly degenerate Gray-category of a braided strict monoidal category, where all CaTT coherences except interchangers are identities, so that the standard EH term is a single interchanger, i.e. the braiding; this needs the (expected) construction of CaTT models from Gray-categories via Gray coherence. Status: open check, listed in `open-issues.md` under E11.

So the bubble is not a counterexample to (11) by the RC route, and it illustrates Theorem C: the weak free model keeps the braiding that the strict F(𝔠_○) kills.

### A.7 What is left for (11) beyond torsion-free

- On homotopical computads: RC_id, which is the RC program (owner RCX; prompt `relative-coherence-all-dimensions.md`, Question 2 now to be phrased with RC_id).
- On non-homotopical computads: (11)_𝔠 is not an RC statement. The cellular-induction route (pushouts along F_w ∂Dₙ → F_w Dₙ preserve W between cofibrant models, close to (12) and (FEA) of the response) is the only general route known, and it contains the homotopy hypothesis for 𝕋^bi. Not targeted, per the coordinator's brief.
- ~~Proposition D's check (EH-odd).~~ **Closed 2026-11-19:** the relative-coherence r2 researcher response (verified; filed by thread "Process seven round-3 researcher responses") proves ¬RC_id(3) for every context with a bubble in its 2-skeleton, so π ∉ W for the bubble computad. Consistent with (11) by Theorem C; (11) for the bubble stays undecided (asked in the unit-condition r4 prompt).

---

## Part B. L's coherator in every dimension: a realization without enrichment

### B.1 Why the earlier rounds stalled

Rounds 2–6 tried to obtain L's analogue of R through a *Gray-enriched* (or coloured-operadic) cellular presentation of L's coherator, with resolved tensor arities, so that the enriched lifting theorem of round 2 applies. Round 5 proved that a strict cell-representing Gray enrichment of the raw coherator is impossible (it would need c(f, i(y)) = f definitionally), and round 6 repaired one arity (the two-square grid, by attaching a walking 3-equivalence along ρ) but not the general substitution-compatible family. Round 2 had noted the alternative: the arity colimits can also be obtained from "a replacement construction preserving the same arity colimits". Part B supplies that replacement, using a presentation theorem of Gepner–Heine.

### B.2 The semantic input: Gepner–Heine's Θ-presentation of enriched categories

Gepner–Heine, *Oriented category theory*, arXiv 2510.10504v2 (read in the PDF, 2026-11-19):

- §1.4, §1.6 (p. 9–10), Def. 3.2.1: oriented categories are categories **left enriched in ∞Cat with respect to the lax Gray tensor product** (equivalently right enriched in the oplax one). This is the intended two-tier model of L: interchange strict inside a hom, lax across objects. AM's ∞-Cat_lax is the strict case, and `conventions.md` (G2) records that the orientations agree. ∞Cat is the limit of Cat_n along the core functors (§1.2).
- **Theorem 2.4.8** (= Thm 1.6.3). Let 𝒲 be presentably monoidal and V ⊂ 𝒲 a small dense full monoidal subcategory. The full subcategory Θ(V) ⊂ 𝒲-Cat of wedges of suspensions of objects of V (and the point) is dense, and a presheaf on Θ(V) is in the essential image of the nerve iff it satisfies the Segal condition (F(S(A₁) ∨ … ∨ S(A_k)) ≃ F(S(A₁)) ×_{F(∗)} … ×_{F(∗)} F(S(A_k))) and all its morphism presheaves (presheaves on V, Def. 2.4.7) are in the essential image of the 𝒲-nerve.
- **Corollaries 2.2.6, 2.2.8 and Def. 2.2.7.** S(A) has objects {0, 1} and Mor(0, 1) ≃ A, and maps out of it are maps from A into a hom. The wedge is the pushout over the shared object, and for S(A₁) ∨ … ∨ S(A_n) the canonical map ⊗_{k≤ℓ<m} A_{ℓ+1} → Mor(k, m) is an equivalence, with initial reverse homs and trivial endo-homs.
- **Remark 3.1.2, Remark 3.5.4.** ∞Cat ⇄ ∞Cat_strict is a monoidal localisation with fully faithful right adjoint, and it induces localisations of enriched categories whose right adjoints (strict oriented Gray-categories into oriented categories) are fully faithful.
- Thm 1.6.1 / 4.3.1 is the case V = Gray cubes (Θ(□, ⊠)); we use Thm 2.4.8 with a different V.

Take 𝒲 = (∞Cat, lax Gray) and V = W_Θ, the closure of Θ under finite Gray products. W_Θ is small, full, monoidal (unit ∗ ∈ Θ) and dense (it contains Θ). By Campion (arXiv 2311.00205, Cor. 3.5, Thm 3.14, Cor. 3.15; already used for (S4) in `semantics-gaps.md`), its objects are the strict Steiner products ν(λΘ₁ ⊗ … ⊗ λΘ_k), gaunt strict ω-categories. Put

```
Θ^or := Θ(W_Θ),    the finite wedges  S(w₁) ∨ … ∨ S(w_k),  wᵢ ∈ W_Θ.
```

Every pasting context Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ of L is an object of Θ^or, and by Cor. 2.2.8 its hom from a_i to a_j is Θᵢ₊₁ ⊗ … ⊗ Θ_j = U_{ij}(Γ). So, as an oriented category, Γ is the strict Gray-category ν_Gray(Γ) of L's coh rule.

By Remark 3.5.4, mapping spaces between objects of Θ^or (all strict) are the discrete sets of strict oriented functors, so Θ^or is a 1-category. Let 𝓜_or be the left Bousfield localisation of the injective model structure on simplicial presheaves on Θ^or at a set of maps presenting the essential image of the nerve (it is an accessible localisation, being the image of a fully faithful right adjoint between presentable categories). It is combinatorial and left proper, its cofibrations are the monomorphisms, and by Thm 2.4.8 it presents oriented categories. Nikolaus's category 𝒜_or of algebraically fibrant objects exists, with free functor F ⊣ U.

### B.3 Theorem L (a realization of the raw coherator of L in every dimension)

Let 𝕋_L be the raw coherator of L: the colimit of free globular extensions adjoining each admissible head once, admissibility being L's two-tier coh rule with (i, j) = (0, n) (Known (IV) of the unit-condition prompt; generator classification through global dimension 3 in round 4). Its arities are the pasting contexts and its models are the globular-sum-preserving presheaves.

**Inputs** (the first two are statements about Gepner–Heine's theory, independent of L's syntax):

- (H1) For every pasting context Γ, the representable yΓ = N(ν_Gray Γ) is a discrete fibrant object of 𝓜_or. *Proof from B.2:* it is discrete because Θ^or is a 1-category (Remark 3.5.4); discrete presheaves are injective-fibrant (a levelwise trivial cofibration A ↪ B induces π₀A ≅ π₀B, through which maps to a discrete presheaf extend); it is local because representables are nerves (Thm 2.4.8).
- (H2) For every Γ, the spine inclusion Sp(Γ) = colim_{disks of Γ} yD_k → yΓ is a weak equivalence of 𝓜_or, where D_0 = ∗ and D_k = S(D_{k−1}). *Proof from B.2:* for a local presheaf F, the Segal condition splits F(Γ) over the wedge into the F(ΣΘᵢ), and F(ΣΘᵢ) is the morphism presheaf of F evaluated at Θᵢ, fibred over F(∗)²; that morphism presheaf is in the image of the ∞Cat-nerve on W_Θ, so it sends Θᵢ to the limit over its globular spine (Θ's own Segal condition in ∞Cat). Hence Map(yΓ, F) → Map(Sp Γ, F) is an equivalence for every local F.

Both therefore hold, given **(G): Campion's Gray tensor (used to identify W_Θ with the strict Steiner products) is Gepner–Heine's lax Gray tensor ⊠.** This follows from the sources, modulo a matching of conventions:
- Campion (arXiv 2311.00205, Theorem A = Cors. 3.15 and 4.6) proves that for n ∈ ℕ ∪ {ω} there is a **unique** monoidal biclosed structure on Cat_n making the inclusion of the lax Gray cubes strong monoidal; and (Cor. 3.5) for a monoidally suitable site S, for instance strongly loop-free Steiner complexes (Example 2.2), the inclusion S → Cat_ω is strong monoidal for the strict Gray tensor, so Gray products of pasting shapes computed strictly are the (∞,ω) ones.
- Gepner–Heine's ⊠ is the Day convolution of the cube Gray structure □ⁿ ⊠ □ᵐ = □ⁿ⁺ᵐ descended along P(□) → ∞Cat (Cor. 3.1.1), and it is closed (Example 3.5.3 and §3.1). By Campion's uniqueness the two agree.
- Residual convention check: that Gepner–Heine's ∞Cat (limit along cores) is Campion's Cat_ω, and that their oriented cubes and Campion's lax Gray cubes carry the same orientation (Gepner–Heine credit Campion for cube density, Cor. 3.1.1).

- (H3) Strict soundness of L: every head over Γ has a strict filler in ν_Gray(Γ) (operation: the top cell of U_{0n}(Γ); coherence: an identity, since supports determine cells). **This is proved and machine-checked** (`src/CaTTExp/Strict/`, `Soundness.sound-tm`, `Recon`, `Bridge`; `pseudo-vs-gray.md` §3.6).

**Theorem L.** Given (H1)–(H3), hence given (G), there is a functor R_L : 𝕋_L → 𝒜_or sending each pasting context Γ to F(Sp Γ), preserving globular sums, constructed head by head in every dimension at once. Consequently

```
S_L(Y) := 𝒜_or(R_L(−), Y)
```

is an L-model with strict substitution for every algebraically fibrant Y, with S_L(Y)_n = (UY)(D_n)₀, functorial in Y.

*Proof.* Exactly the CaTT construction of Known (I), with Θ_ω replaced by Θ^or.

- *Arities.* F is a left adjoint and Sp Γ is the colimit of the disks, so R_L(Γ) := F(Sp Γ) is the globular sum of the R_L(D_k) in 𝒜_or. No tensor domain needs to be named in the theory: the Gray tensor is computed by the semantics, through (H2).
- *Comparison.* By (H1)–(H2), ε_Γ : F(Sp Γ) → N(ν_Gray Γ) (adjunct of the spine inclusion, target with its canonical algebraic structure) is a weak equivalence onto a discrete fibrant object, hence a trivial fibration in 𝒜_or, by the argument Known (I) uses for F Sp(P) → yP.
- *Heads.* Proceed along the tower of free extensions. Suppose R_L is defined on the stage containing the boundary terms t, u : D_{m−1} → Γ of a head h, with the invariant ε_Γ ∘ R_L(s) = ⟦s⟧ (the strict interpretation) for every term s. Then R_L(t), R_L(u) give F(∂D_m) → F(Sp Γ), and (H3) gives a strict filler ⟦h⟧ : F(D_m) → N(ν_Gray Γ) of the same sphere. F(∂D_m) → F(D_m) is a cofibration (F of a monomorphism) and ε_Γ a trivial fibration, so a lift R_L(h) exists, and it satisfies the invariant. Limit stages are colimits. Substitution is composition in 𝕋_L and is preserved because R_L is a functor on the free extension. ∎

**What this settles.**

- **No enriched or resolved arities are needed.** The two-square case shows the mechanism: the independent whole-grid head G_Γ and the elementary paste E_Γ are two cells of F(Sp Γ) over the same strict cell ρ of ν_Gray(Γ). Because ε_Γ is a trivial fibration, its fibres are contractible, so they are joined semantically, and in 𝕋_L they are already joined by coherence heads (Known (IV)). Round 6's walking-3-equivalence attachment Û_Γ is a strict stand-in for F(Sp Γ); the general substitution-compatible family it asked for is F(Sp −) itself.
- **Round 5's obstruction does not apply.** It concerns a strict Gray enrichment of 𝕋_L; Theorem L enriches nothing. The Gray structure lives in Θ^or, a strict category of strict Gray-categories.
- **Invertibility needs no declaration.** L's coherence heads are symmetric (both directions are admissible), so their inverses are heads, as in CaTT. Interchangers across objects are operation heads in one direction only (`ReverseInterchanger.no-reverse-interchanger`), and the lift stays directed because ⟦h⟧ is.
- **Q4 of the unit-condition prompt is answered at the level of the construction**, conditional only on the convention check in (G) (both papers' Gray tensors agree by Campion's uniqueness theorem). (H1)–(H2) are the oriented analogue of "yP is discrete fibrant and F Sp(P) → yP is a trivial fibration" in Known (I).

### B.4 What is left on the L side

1. **The residual convention check in (G)**: Gepner–Heine's ∞Cat versus Campion's Cat_ω, and the orientation of their cubes. Also to re-read: the localising set for Thm 2.4.8's image (only its existence is used).
2. **The comparison program for L** (posed as Q2 of `conjectures/answered/catt-models-unit-condition-r3-2026-11-19.md`, which now states Theorem L as known, 2026-11-19). With S_L in hand, the CaTT program (𝓛_{R_L} ⊣ S_L, coinductive completion, the derived adjunction, the unit condition) can be repeated for L. Its first missing ingredient is a class of weak equivalences on L-models (an FHM theory for L's directed cells: essential surjectivity with directed comparison cells, and invertibility only where L declares it). The L-analogue of Theorem A then reads: for a Gray loop-free context, π^L : A^L_Γ → ν_Gray(Γ) is a trivial fibration ⟺ L-relative coherence with identity image, and ν_Gray(Γ) is gaunt (Lemma A.2 applies to its hom complexes, which are Steiner).

### B.5 Agda

No rule set changes in this note, so standard 9 does not call for new formalisation. Theorem L uses the strict model of L exactly as already machine-checked ((H3)). Lemma A.2 is elementary and could be checked on the existing free-ω-category encodings if a later step relies on it mechanically.
