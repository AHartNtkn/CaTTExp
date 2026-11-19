# Limit-rule metatheory, and limits over the Gray core (L)

*Design and proof note, 2026-11-18. Owner thread: "Develop limit-rule metatheory and limits over L" (`cmsg_018pe2CvdFGDdsWgn8Tjn5gbD4wzRQd7hPxxsf6RGVQJT9`). Covers ledger items B4, B7, B8 (internal attempt), B9–B14 of `notes/open-issues.md`. Companion to `limits-representables.md` (§4, §10), `pseudo-vs-gray.md` (§3, §4.4, R11), `conjectures/catt-lim-pseudo-vs-gray.md` and the Agda findings in `catt-lim-formalization.md` (PR #22).*

*Markers as in the other notes. **[paper]**: checked against the cited source this session (for Loubaton, arXiv 2406.05425v2, the PDF was read at the cited numbers). **[conj]**: unproved, with an attempt recorded. **Proved** means a complete argument is written here; **proved (strict)** means it is proved in the strict model only.*

---

## 0. Summary

1. **Unrestricted lax limits are consistent over L (B8, internal).** In strict ω-categories, self-enriched over the Ara–Maltsiniotis Gray tensor, every diagram over a finite computad has a lax limit whose universal property is an *isomorphism* between `𝒦(c, lim)` and the ω-category of lax cones with **unrestricted** Gray-shaped transfors (Theorem A, §1). Cone morphisms with non-invertible comparison cells exist and are classified. Comma and hom objects come out as the full hom ω-categories. This is the strict analogue, for every finite computad, of the researcher's answer to `conjectures/oriented-lax-limits.md` (PR #29, verified). That answer proves the arrow case in ∞Cat with the same two ingredients.
2. **R11 re-derived line by line in two-tier L (B8, internal; agrees with the researcher's §1).** Exactly one step of the forced-invertibility and collapse arguments fails in L: the invertibility of `F(w)_g`, the image of a cell under the universal cone, which in L is an operation-case Gray cell. It fails at every level. Every other step (associators, unitors, J2 certificates, the endpoint reduction) goes through unchanged (§2).
3. **The collapse in every dimension ≥ 3 is proved (B9).** A clean induction: a d-cell becomes the top f-component of a (d−2)-transfor over the identity arrow, and `uni` at level d−1 makes it invertible. It needs no appeal to Benjamin–Markakis Prop. 35, only the full-support coherence rule (§3).
4. **Models of the original CaTT_lim are classified (B10).** They are exactly the (∞,ω)-categories whose cells of dimension ≥ 3 are invertible and which have finite lax limits in the sense of Gagna–Harpaz–Lanari and Loubaton. Example: the 2-category Cat (§4). This holds under the shared premises (specified shapes, B5; interpreting CaTT in (∞,ω)-categories, E11).
5. **Limit rules over L, in one schema with P (B7, B11).** P and L use the same specified cone and transfor shapes, and the same filler rule. They differ in two places only: the core, and which transfor comparison cells carry invertibility marks. Under P, the comparisons over all positive-dimensional diagram generators are marked; under L, only those over *marked* diagram generators (the coherent marking that the verified Problem 3 correction requires). The whole `cone`/`ctrf`/`pctrf`/`star`/`pstar`/`⊢uni` apparatus becomes one horn context `Horn_n(Γ, γ; c)` and one term former `uni`. Under L, the only cells the rules need from the core are operation-case cohs over two-factor wedges `ΣDᵃ ∨ ΣDᵇ`, which LCORE's checker already covers (§5).
6. **Metatheory of the marked version (B4).** Substitution admissibility is proved. Composition of transfors over arrows is given explicitly; over higher generators it reduces to the specified-shape problem B5 / naturality C1. Soundness reduces to Loubaton's lax limits in ω (Prop. 4.2.3.8, Cor. 4.2.3.18) plus B5 and E11 (§6).
7. **Hom_⊖ under P is identified at the generator level (B13).** Loubaton's marked enhanced Gray product `I ⊖ a♯` is Gray in the first transfor direction and *cartesian* in all higher ones (Construction 3.1.2.15, Prop. 3.1.2.17). That is exactly the repaired table: arbitrary vertex components and invertible comparisons over positive-dimensional generators. Under L the cone categories are the full Gray homs of Theorem A (§7).
8. **One schema, and where the alternating variance lives (B12).** The alternating variance of the weighted-limit theorem is a condition on the *index* (π, μ), so it belongs to B14, not to the cone schema, which keeps one variance. Under L, **colimit transfors have the opposite Gray factor order** (diagram index first) and need no second interchange direction. **Full duality is not a symmetry of L**: it reverses the interchanger. So colimit rules must come from their own specified shapes, not from dualising derivations (§8).
9. **Finite fibration test (B14).** Proved for set-valued weights over graphs: the test is "π is a discrete opfibration of graphs". The general case, with a candidate generator-level criterion and the localisation lemma it needs, is posed in `conjectures/finite-fibration-test.md` (§9).

---

## 1. Strict model: unrestricted lax limits in strict ωCat with the Gray tensor (B8)

### 1.1 Setting

- **ωCat** is the category of strict ω-categories, and ⊗ is the Ara–Maltsiniotis Gray tensor. It is monoidal and biclosed **[paper: AM Thm A.15, §A.18; G1 check]**. Write `⟦A, –⟧ˡ` for the right adjoint of `A ⊗ –` and `⟦B, –⟧ʳ` for the right adjoint of `– ⊗ B`. In AM's names (`conventions.md` §3.2), ⟦A, C⟧ˡ = Hom_lax(A, C) and ⟦B, C⟧ʳ = Hom_oplax(B, C):

  ```
  ωCat(A ⊗ B, C)  ≅  ωCat(B, ⟦A, C⟧ˡ)  ≅  ωCat(A, ⟦B, C⟧ʳ).
  ```

  Which of these AM call "lax" and which "oplax" is a naming question for G2. Nothing below depends on the names.
- **𝒦** is ωCat enriched over itself with `𝒦(A, B) := ⟦A, B⟧ˡ`. Composition `𝒦(A,B) ⊗ 𝒦(B,C) → 𝒦(A,C)` is adjoint to `A ⊗ 𝒦(A,B) ⊗ 𝒦(B,C) → B ⊗ 𝒦(B,C) → C`, with factors in **execution order**. This is a strict Gray-enriched category: the strict model of two-tier L (`pseudo-vs-gray.md` §3.6, Theorem 1).

### 1.2 Two lemmas

**Lemma 1 (cotensors commute with homs).** For all K, X, c there is an isomorphism, natural in all three:

```
𝒦(c, ⟦K, X⟧ʳ)  ≅  ⟦K, 𝒦(c, X)⟧ʳ.
```

*Proof.* For a test object T:
`ωCat(T, ⟦c, ⟦K,X⟧ʳ⟧ˡ) ≅ ωCat(c ⊗ T, ⟦K,X⟧ʳ) ≅ ωCat((c ⊗ T) ⊗ K, X) ≅ ωCat(c ⊗ (T ⊗ K), X) ≅ ωCat(T ⊗ K, ⟦c,X⟧ˡ) ≅ ωCat(T, ⟦K, ⟦c,X⟧ˡ⟧ʳ)`. The middle step is the associator of ⊗. Conclude by Yoneda. ∎

So `⟦K, X⟧ʳ` is the cotensor of X by K in the Gray-enriched sense. Its n-cells are maps `Dⁿ ⊗ K → X`.

**Lemma 2.** `𝒦(c, –) = ⟦c, –⟧ˡ` preserves all limits, since it is a right adjoint. ∎

### 1.3 Lax limits by cell attachment

Let Γ be a finite computad with generators x₁, …, x_N in an order in which each boundary is built from earlier generators. Let D be a diagram of shape Γ in 𝒦: an assignment of cells of 𝒦 to generators that respects boundaries. Since the free Gray-enriched category on Γ is free, this is the same as a Gray-functor out of it. For a generator x of dimension k ≥ 1, let `b(x)` be the object at its end in execution order.

Define objects `L_j` and universal cones `λ` by induction on j:
- `L₀ := 1`, the terminal ω-category.
- **x_j an object.** `L_j := L_{j−1} × D(x_j)`, and `λ_{x_j}` is the projection.
- **x_j of dimension k ≥ 1.** The cone cell over x_j is a k-cell of the hom `𝒦(c, D b)`, with b = b(x_j), so a (k+1)-cell of 𝒦. Its boundary is fixed by the earlier components, as in Mikhail's σCond and τCond. In the strict model it is a sphere

  ```
  S_j : ∂Dᵏ → 𝒦(L_{j−1}, D b),
  ```

  obtained by composing earlier λ's with D's cells in 𝒦. Composition is strict, so this is well defined. Its transpose is a map `L_{j−1} → ⟦∂Dᵏ, D b⟧ʳ`. Put

  ```
  L_j := L_{j−1} ×_{⟦∂Dᵏ, D b⟧ʳ} ⟦Dᵏ, D b⟧ʳ,
  ```

  and let `λ_{x_j}` be the second projection, transposed.

Define `Cone_Γ(c, D)` by the same formula with `𝒦(c, –)` applied throughout:

```
Cone_{Γ_j}(c) := Cone_{Γ_{j−1}}(c) ×_{⟦∂Dᵏ, H⟧ʳ} ⟦Dᵏ, H⟧ʳ,      H := 𝒦(c, D b).
```

Here the boundary map is S_j precomposed with the earlier cone data. Its 0-cells are exactly lax cones in Mikhail's sense: a k-cell p_x of the hom for each k-generator x, with the prescribed boundary and **no invertibility requirement**.

**Theorem A (strict lax limits, unrestricted).** Postcomposition with λ is an isomorphism of strict ω-categories

```
𝒦(c, L_Γ)  ≅  Cone_Γ(c, D),
```

natural in c, and Gray-natural. **Proved (strict).**

*Proof.* Induction on j. Apply `𝒦(c, –)` to the defining pullback. Lemma 2 keeps it a pullback, and Lemma 1 turns `𝒦(c, ⟦Dᵏ, D b⟧ʳ)` into `⟦Dᵏ, H⟧ʳ`. The boundary map is S_j precomposed with the inductive isomorphism, because composition in 𝒦 is a Gray-functor. ∎

**What the n-cells are.** By the pullback formula, an n-cell of `Cone_Γ(c, D)` gives, at each k-generator x, an n-cell of `⟦Dᵏ, H⟧ʳ`, i.e. a map `Dⁿ ⊗ Dᵏ → H`, compatible on boundaries.
- These are Gray-shaped, with the **transfor index first** and the diagram index second.
- No component is required to be invertible.
- For Γ = (x, y, f : x → y) and n = 1, the data are m_x and m_y (1-cells of H) and the top cell `e₁ ⊗ e₁` of D¹ ⊗ D¹, which is the comparison m_f. It is arbitrary.

**Orientation check.** In L the interchanger is the top cell of U = Θ₁ ⊗ Θ₂ in execution order (`pseudo-vs-gray.md` §3.1). Here, the image under λ of a cell w of 𝒦(c, L) at a generator g is the composition 𝒦(c,L) ⊗ 𝒦(L, D b) → 𝒦(c, D b) applied to w ⊗ λ_g. That is the top cell of `D^{dim w − 1} ⊗ D^{dim g}`, again in execution order (w first, λ_g second). So the strict model and L's operation-case cell agree, and both give the orientation of R11 eq. (2): `(u◁φ);(β▷v′) ⇛ (β▷v);(u′◁φ)`.

### 1.4 Corollaries

**A1. No forced invertibility.** The comparison is an isomorphism, so every cone morphism is `F(β)` for a unique β, including those with non-invertible m_f. Concretely, take the researcher's 2-category C with `C(b, a) = (f →α g)`, `C(a, b) = ∅`, trivial endomorphisms, and the arrow diagram `a : 1 → C`.
- `L = 1 ×_C ⟦D¹, C⟧ʳ`, restricted to the end at a, is the slice whose objects over b are f and g.
- Its arrow f → g is the unique β with `F(β)_f = α`.
- The cartesian obstruction of `catt-lim-pseudo-vs-gray.md` §4 does not arise, because `F(β)_f` is the Gray interchanger of β with the universal evaluation cell, which is not invertible.

**A2. Comma and hom objects (Problem 3, strict).** Take the diagram `x, y, z, f : x → z, g : y → z`, sent to `1, 1, C, a, b`, with g marked. In the strict model, "marked" is taken to mean that p_g is an identity. Because the leg is a fixed point, the pullback then also makes every transfor comparison over g an identity: the marking is respected **coherently**. The verified researcher response shows this is necessary. If p_g is only invertible and the transfor comparison m_g is arbitrary, no limit exists in general (its counterexample is the one-object 2-category with hom-poset [1] and composition max). Then

```
lim = {a} ×_C ⟦D¹, C⟧ʳ ×_C {b},
```

the fibre of the Gray arrow object over a pair of objects. Its n-cells are maps `Dⁿ ⊗ D¹ → C` constant at the ends. Collapsing `Dⁿ ⊗ {0}` and `Dⁿ ⊗ {1}` in `Dⁿ ⊗ D¹` gives `D^{n+1}` **[paper, G1 check: Ara–Maltsiniotis 1607.00668 Cor. B.6.6, ΣC ≅ D⁰ ⊔_C (D¹ ⊗ C) ⊔_C D⁰. That is the D¹ ⊗ C orientation; for Dⁿ ⊗ D¹ apply the even dual (AM Prop. A.22), under which Dⁿ and D¹ are self-dual, so the result is again D^{n+1}]**. So the fibre is the **full hom ω-category** between a and b (in the orientation the convention fixes), with non-invertible arrows. It is the strict counterpart of Gagna–Harpaz–Lanari's `fib(Ar^oplax(C) → C × C) ≃ Hom_C` (eq. (7) of the researcher response), and the opposite of the cartesian answer (eq. (8): the core).

**A3. Cotensors.** `[⟦Γ⟧, C]`, the lax limit of the constant diagram at C over Γ, is a finite iterated pullback of `⟦Dᵏ, C⟧ʳ`'s. Its points are Γ-shaped lax diagrams in C, and its arrows are lax transformations. This is the claim of `limits-representables.md` §6.3 under L, now proved in the strict model.

**Theorem A′ (colimits, strict).** 𝒦 has tensors: `𝒦(X ⊗ K, c) ≅ ⟦K, 𝒦(X, c)⟧ˡ`. *Proof:* `ωCat(T, ⟦X⊗K, c⟧ˡ) ≅ ωCat(X⊗K⊗T, c) ≅ ωCat(K⊗T, ⟦X,c⟧ˡ) ≅ ωCat(T, ⟦K, ⟦X,c⟧ˡ⟧ˡ)`. Also, `𝒦(–, c)` sends pushouts to pullbacks. So the dual cell-attachment construction gives lax colimits with `𝒦(colim, c) ≅ Cocone_Γ(c, D)`. The n-cells of `⟦Dᵏ, H⟧ˡ` are maps `Dᵏ ⊗ Dⁿ → H`: **cocone transfors have the diagram index first.** **Proved (strict).** §8 uses this.

### 1.5 What this does and does not settle

- **Settled (strict).** The unrestricted lax universal property is consistent in a Gray-enriched setting: it has a model in which comparison cells are genuinely non-invertible, and in which comma objects are the full homs. This is the positive half of R11 that the notes predicted, now proved for strict ω-categories. With Theorem 1 of `pseudo-vs-gray.md` (whose lemmas (A)–(C) are discharged by Hadzihasanovic), it gives a **relative consistency result: the unrestricted limit rules over two-tier L have a non-degenerate model.** It depends on one more identification: that the specified syntactic cone and transfor shapes interpret as the cell-attachment formula above. That is B5's job.
- **(∞,ω).** The researcher response to `conjectures/oriented-lax-limits.md` (PR #29, verified) proves the ∞Cat version of Lemma 1 (its mixed currying (4), from Gepner–Heine Notation 3.1.3) and of Lemma 2, and with them the arrow case. Existence for all small diagrams follows from Heine Lemma 3.69. What is still open (ledger B17) is the general-Γ statement that the cell-attachment limit represents the cone category presented by the *specified syntactic shapes*: a comparison between filler rules and the weight, which the response flags too.

---

## 2. R11 line by line in two-tier L (B8, internal attempt)

Each step of the verified argument (`conjectures/catt-lim-pseudo-vs-gray.md`, response §§1–4), re-checked under the two-tier L rule of `pseudo-vs-gray.md` §3.3:

| Step | In CaTT | In two-tier L |
|---|---|---|
| §1 interchange cell `I_{β,φ}` over `ΣD¹ ∨ ΣD¹` | coherence case, invertible | **operation case**: supp S = ∂⁻U, supp T = ∂⁺U. Derivable as S ⇛ T, exactly eq. (2)'s orientation. The reverse is not derivable (Thm 1(2), now unconditional). |
| associators `(uλ_x)f ≅ u(λ_x f)` over `ΣD⁰ ∨ ΣD⁰ ∨ ΣD⁰` | invertible | U is a point, both sides have full support: coherence case, **invertible** |
| naturality of associators in β, over `ΣD¹ ∨ ΣD⁰ ∨ ΣD⁰` | invertible | U = D¹, both sides full: coherence case, **invertible** |
| so `N := F(β)_f` | invertible | invertible **iff** the interchanger is; it is not |
| §2: J2 certifies E_x, E_y, E_f; A, B whiskerings of E_x, E_y | invertible | unchanged: J2 outputs are certified in both designs (§5.3) |
| §2: `R ≅ A;N;B⁻¹`, so R invertible iff N invertible | R invertible | **R ≅ conjugate of a directed interchanger: no conclusion** |
| §2 endpoint reduction (dimension-1 `uni`, composition of transfors) | used | unchanged, and harmless |
| §4 collapse: the unit coherences relating `a` and `P_f;(a▷1_Y)` | invertible | the context is `ΣD¹ ∨ ΣD⁰` with U ≅ D¹, both sides full: **invertible**. So m_f ≅ z still holds. |
| §4: `F(α)_g` for higher α "invertible by BM Prop. 35" | invertible | the top cell of `D^{dim α − 1} ⊗ D^{dim g}`, operation case, **not invertible** (Thm 1(2) covers every y ⊗ x with both dimensions ≥ 1) |

The researcher's response to `oriented-lax-limits.md` (§1, verified) reaches the same conclusion for the cone-morphism step. The table above also covers the collapse argument and the higher levels.

**Conclusion.** The only step that fails in L is the invertibility of `F(w)_g`, and it fails at every level. Everything else, including the unit and associator bookkeeping, survives. So in L the argument proves something true but harmless: **every cone transfor is conjugate, by certified cells, to a directed interchanger.** Theorem A shows this is exactly what happens in the strict model. Together with §1.5, this closes the internal half of B8.

---

## 3. The collapse in every dimension ≥ 3 (B9): proved

**Claim.** In the intended calculus of unchanged CaTT_lim (recognition rules repaired as in PR #22, transfors closed under composition), if `uni` holds at every level, then every ambient d-cell with d ≥ 3 has derivable inverse data.

The premises are those of the researcher's response. Composition of transfors over the arrow diagram is supplied explicitly in §6.2.

**Proof.** Let z : a ⇛ b be a d-cell, d ≥ 3, with a, b parallel (d−1)-cells. All of them lie in a single hom 𝒦(c, Y). Put k := d − 2 ≥ 1. Use the diagram Γ = (x, y, f : x → y) with γ = (Y, Y, 1_Y), and L := lim_Γ[γ].

1. **A k-transfor T with T_f ≅ z.**
   - At every level j < k, take the x- and y-components equal: they are the iterated boundaries of a, which coincide with those of b.
   - At level j < k, take the f-components to be the unit coherences: at level 0, the inverse right unitor `r ⇒ r;1_Y`. In general it is the coherence relating a j-component w to its composite with 1_Y and the lower f-components. Its context is a disk, both sides have full support, so it is an invertible coherence.
   - At level k, put `T_x := a` and `T_y := b`.
   - The required f-component has type `S_a ⇛ S_b`, where S_a (resp. S_b) is a pasted with the lower unit coherences (resp. b with them). The coherences `c_a : a ≅ S_a` and `c_b : b ≅ S_b` are full-support cohs over the disk of a, hence invertible.
   - Put `T_f := c_a⁻¹ ; z ; c_b`. T is a well-typed k-transfor: under PR #22's repaired rules, the shapes are accepted.
2. **Endpoint reduction.** T goes between (k−1)-transfors T⁻ and T⁺. By `uni` at levels ≤ k, there are invertible k-transfors `e : T⁻ ⇛ F(w⁻)` and `d : T⁺ ⇛ F(w⁺)`. Put `T̃ := e⁻¹ ; T ; d` (§6.2). Then T̃_f is T_f whiskered with components of e⁻¹ and d, which are invertible. Whiskering by invertible cells reflects invertibility (Benjamin–Markakis). So T_f is invertible iff T̃_f is.
3. **Comparison at level k+1.** Applied to T̃, `uni` at level k+1 gives, by J1, a (k+1)-cell w of 𝒦(c, L) with boundary (w⁻, w⁺), and, by J2, a certified (k+1)-transfor `E : T̃ ⇛ F(w)`. Its f-component is
   ```
   E_f : T̃_f ; B ⇛ A ; F(w)_f,
   ```
   with A, B whiskerings of the certified E_x, E_y, so A and B are invertible.
4. **`F(w)_f` is invertible in CaTT.** It is the (k+2)-cell over the context `ΣD^k ∨ ΣD¹`: w as a k-cell of the hom 𝒦(c, L), and φ := λ_f as a 1-cell of 𝒦(L, Y), up to associators. It is the cell whose Gray shape is the top cell of `D^k ⊗ D¹`. By the Leibniz formula, its source contains `e_k ⊗ (endpoint)` (the whiskered w) and `∂e_k ⊗ e₁` (lower interchangers, which contain φ). So both source and target use every variable of the context, and in CaTT this is a coherence-case coh, hence invertible. This replaces the appeal to BM Prop. 35.
5. Hence `T̃_f ≅ A ; F(w)_f ; B⁻¹` is invertible, so T_f is, so `z = c_a ; T_f ; c_b⁻¹` is. ∎

Level d−1 of `uni` is used for d-cells, so, as the researcher says, invertibility of all 3-cells alone would not give invertibility of 4-cells. **B9 is closed.** The Agda thread is machine-checking the instance d = 4 in the intended rules (§10, item 3). The printed rules cannot run the collapse at all, so "original rules" in B9–B10 means the intended calculus.

---

## 4. Models of the original rules (B10): classified

**Proposition.** Assume the shared premises: specified shapes (B5), and an interpretation of CaTT-style theories in (∞,ω)-categories (E11). Then a weak ω-category 𝒜 models the original CaTT_lim (intended calculus, unrestricted transfors, `uni` at all levels) **iff**
1. every cell of 𝒜 of dimension ≥ 3 is invertible, so 𝒜 is an (∞,2)-category; and
2. every finite diagram in 𝒜 has a lax limit in the sense of Gagna–Harpaz–Lanari (Cor. 5.1.7) and Loubaton (Def. 4.2.3.3, Cor. 4.2.3.18).

*Proof.*
- (⇒) Condition 1 is §3. Given condition 1, every transfor comparison cell has dimension ≥ 3, so it is invertible. Hence the unrestricted cone categories coincide with the pseudo-morphism ones, which are Loubaton's `hom_{Hom⊖(I,ω)}(cst 1, hom(a, F–))` (§7). So the universal property is the GHL/Loubaton one.
- (⇐) Under condition 1, the same coincidence holds. The GHL/Loubaton universal property then supplies `ucone`, J1 and J2 at every level, the J2 cells being equivalences. ∎

**Examples.**
- The strict 2-category Cat of small categories: strict lax limits exist (they are Cat-weighted limits, and Cat has all of them: Street 1976, Kelly 1989; Lack, *A 2-categories companion*, [math/0702535](https://arxiv.org/abs/math/0702535), §§6.7–6.8 **[paper, G1 check]**), and its cells of dimension ≥ 3 are identities.
- The (∞,2)-category of (∞,1)-categories (Gagna–Harpaz–Lanari, *Fibrations and lax limits of (∞,2)-categories*, [2012.04537](https://arxiv.org/abs/2012.04537), abstract: lax, weighted and pseudo limits via fibrations **[paper, G1 check]**).
- *Non-example:* the researcher's Bicat, which has non-invertible modifications, so fails condition 1.

So the original rules are a reasonable theory of (∞,2)-categories with lax limits, and nothing more. **B10 is closed**, conditional on the two shared premises.

---

## 5. Limit rules over L, and the horn judgment (B7, B11)

### 5.1 Shapes (shared by P and L)

Following the repair of `limits-representables.md` §4.1, shapes are **functions**, not judgments. They are defined by the cone-constructions thread (B5) and checked by PR #22:
- `Cone(Γ; c)`: the cone context over a diagram context Γ (any finite context) with apex variable c.
- `Tr_n(Γ; c)` for n ≥ 1: the context of n-transfors between cones. These are Gray shapes with the **transfor index first** (Theorem A's `Dⁿ ⊗ Dᵏ`), the apex not duplicated, and every cone variable copied with its type renamed (PR #22's repair of `x′ : X`).

### 5.2 The image of a cell under the universal cone

Let `Δ ⊢ γ : Γ` and `L := lim_Γ[γ]`, with universal cone λ (`ucone`). For a cell w of 𝒦(c, L) of 𝒦-dimension n, the transfor `F(w)` has:
- `F(w)_x := w ▷ λ_x` for an object generator x. In L this is the operation case over `ΣD^{n−1} ∨ ΣD⁰`, with U ≅ D^{n−1}. Under P it is the same CaTT whiskering.
- `F(w)_g` for a k-generator g, k ≥ 1: the cell with Gray shape the top cell of `D^{n−1} ⊗ D^k`.
  - **Under L** it is the operation-case coh over `ΣD^{n−1} ∨ ΣD^k`, substituted by (w, λ_g). It is directed.
  - **Under P** it is the coherence-case CaTT coh with the same source and target, and it is invertible.
- Plus the invertible associator and unitor adjustments, which are coherence-case in both designs (§2 table).

**So the only cells L must supply are operation-case cohs over two-factor wedges `ΣDᵃ ∨ ΣDᵇ`.** LCORE's checker (E1–E2) already handles these.

### 5.3 The horn judgment

**Definition.**
- `Horn₀(Γ, γ; c) := Cone(Γ; c)[γ]`.
- For n ≥ 1, `Horn_n(Γ, γ; c)` is the context made of:
  - c;
  - a boundary sphere `∂w = (w⁻, w⁺, …)` of (n−1)-cells of 𝒦(c, L);
  - the variables of `Tr_n(Γ; c)[γ]` that do not lie over its boundary. The boundary variables are *substituted* by `F(∂w)` (§5.2).

  This substitution is what Mikhail's `star`/`pstar` did.

**The one filler rule.** For `Θ ⊢ σ : Horn_n(Γ, γ; c)`:

```
(J1)  Θ ⊢ uni^w_{Γ,n}[σ]     : the n-cell of 𝒦(c, L) with boundary ∂w[σ]
(J2)  Θ ⊨ uni^y_{Γ,n}[σ]     for every component y of the comparison transfor  E : T ⇛ F(uni^w)
```

Here T is the transfor that σ supplies. **All of E's components are certified**: an invertible transfor in a Gray hom must have invertible components *and* invertible comparison cells. **[proved for 2-categories, G1 check; the (∞,ω) version is the same claim as the [conj] in `invertibility-markings.md` Lemma 2.2]** For 2-categories (proof: if β is a vertical inverse of α, the composite's components α_x β_x and naturality cells, the pastings of α_f and β_f, are identities; with α_x invertible, β_f whiskered by α's components is a two-sided inverse of α_f), an equivalence in the 2-category of lax transformations has invertible naturality cells, since the inverse's cells are mates.

**The P/L switch.**

| | Inputs σ | Outputs |
|---|---|---|
| **L** | unrestricted, except that Tr_n's comparison variables over **marked** diagram generators are marked declarations (coherent marking; verified Problem 3 correction) | J2 certified |
| **P** | Tr_n's comparison variables over positive-dimensional diagram generators are **marked declarations**, so σ must certify them (§6.1) | J2 certified |

This is "P = L + marking" (`pseudo-vs-gray.md` §2.4) at the level of the limit rules: one schema, one implementation, and the set of marked comparison variables in Tr_n as the switch.

**What this removes.** `cone`, `ctrf`, `pctrf`, `star`, `pstar`, `⊢uni` and `⊢_{K,Θ}` become two context functions (`Cone`, `Tr`, or the single `Horn`) and one term former. The rule now reads like `coh`: `uni_{Horn_n(Γ,γ;c), y}[σ]`. **B11 is closed as a design.** Its encoding is an Agda follow-up (§10, item 2).

**[conj] Horns are cones.** In the strict model, by Lemma 1, an n-transfor of Γ-cones over D is the same as a cone over the cotensored diagram `⟦Dⁿ, D–⟧ʳ`. Equivalently, it is a cone over `Dⁿ ⊗ Γ` for the diagram pulled back along the collapse `Dⁿ ⊗ Γ → Γ`, up to the unit coherences that the collapse inserts. If this holds syntactically, `Tr_n(Γ) = Cone(Dⁿ ⊗ Γ)[π]` up to unit coherences, and B5 has only one construction to supply. Note the factor order `Dⁿ ⊗ Γ`, not `Γ ⊗ Dⁿ` (§8).

### 5.4 Answers to the earlier [conj]s about L

- **`pseudo-vs-gray.md` §4.4, "ctrf shapes become native cells of 𝒦(c, ·)".**
  - Semantically, yes: Theorem A identifies n-transfors with n-cells of 𝒦(c, L).
  - Syntactically, the shapes are still needed to *state* `uni`. They shrink to `Tr_n`, or to `Cone(Dⁿ ⊗ Γ)` if the [conj] above holds.
- **`limits-representables.md` §6.2–§6.3 under L.** Hom objects and lax cotensors come directly from the limit rules: A2 and A3, strict.
- **`limits-representables.md` §4.1(3), "restating the rules over the Gray core is open".** §5.1–§5.3 is that restatement. What remains is the shape construction (B5) and the encoding (§10).

---

## 6. Metatheory of the marked-declaration version (B4)

### 6.1 The system

- **Marked declarations.** Contexts may contain marked declarations `x :≅ A`.
- **The invertibility judgment `Γ ⊢ t inv`.** This is the ICaTT-style judgment, closed under:
  - marked variables;
  - coherence-case cohs;
  - `inv`, `eta`, `eps` of invertible terms (which are themselves invertible);
  - composites and whiskerings of invertible terms. Explicit inverse data: `inv(t;u) := inv(u);inv(t)`, with eta and eps built from those of t and u and coherences (Benjamin–Markakis Thm 33).
- **Substitutions.** `Δ ⊢ σ : Γ` requires `Δ ⊢ σ(x) inv` for every marked declaration x of Γ, in addition to the usual typing.
- **Limit rules.** As in §5.3, with the comparison variables of `Tr_n` over positive-dimensional diagram generators marked, and the J2 outputs in `inv`.
- **Diagram markings** (`limits-representables.md` §4.2) mark the cone variables p_x for marked diagram generators x, in `Cone(Γ^μ; c)`.

### 6.2 Results

**B4.1 Substitution admissibility. Proved.** If `Δ ⊢ σ : Γ` and Γ ⊢ J, for J a typing or an `inv` judgment, then Δ ⊢ J[σ].

*Proof.* By mutual induction on derivations. The CaTT cases are standard. In both P and L, side conditions are checked on the coh's own context and never on Δ (`pseudo-vs-gray.md` §3.6).
- **Marked variable.** `x[σ] = σ(x)`, and `Δ ⊢ σ(x) inv` is part of σ.
- **`uni` term.** `(uni_{H,y}[τ])[σ] := uni_{H,y}[τ ∘ σ]`. The composite `τ ∘ σ` is a substitution into H: its marked entries `τ(v)[σ]` are `inv` by the induction hypothesis. The side conditions of `uni` concern only the specified context H. This is where the *specified-shape* repair is used: with Mikhail's permissive judgments one would also need the shape derivation to be stable, which holds but is extra work.
- **J2 outputs.** They are in `inv` by rule, and stable by the same equation.
- **Closure rules for `inv`.** Immediate from the induction hypothesis. ∎

Associativity and unit laws for composition of substitutions follow as in CaTT, since certificates are carried along by substitution.

**B4.2 Composition of transfors.**
- **Over generators of dimension ≤ 1: explicit.** For cone morphisms `m : P → Q` and `n : Q → R`, put `(m;n)_x := m_x ; n_x` in the hom, and

  ```
  (m;n)_f :  p_f;((m_x;n_x)▷f)  ⇛  p_f;(m_x▷f);(n_x▷f)  ⇛  m_y;q_f;(n_x▷f)  ⇛  m_y;n_y;r_f,
  ```

  as `(p_f ; δ)`, then `(m_f ; (n_x▷f))`, then `(m_y ; n_f)`, with associators.
  - δ is the whiskering-distributivity coherence over `Σ(D¹ ∨ D¹) ∨ ΣD⁰`. There U ≅ D¹ ∨ D¹ and both sides have full support, so δ is invertible in **both** CaTT and L.
  - If m_f and n_f are certified, so is `(m;n)_f`, by the closure rules.
  - Inverses: `(e⁻¹)_x := inv(e_x)`, and `(e⁻¹)_f` is `inv(e_f)` whiskered by `inv(e_x)` and `inv(e_y)` and corrected by eta/eps. It is certified.
  - Vertical composition of k-transfors over the arrow along their (k−1)-boundary follows the same pattern, one level up. This is what §3 and the researcher's step 2 use.
- **Over generators of dimension ≥ 2: reduces to B5/C1.** The composite `(m;n)_g` must paste m_g and n_g. Its boundary is built from `(m;n)_{∂g}`, while the pasting's boundary is built from m_{∂g} and n_{∂g} separately. Relating the two needs a naturality coherence over a non-pasting context: exactly Conjecture N (C1) and the specified construction B5. All the cells involved lie in the single hom `𝒦(c, D b)`, except interchangers of m_x with D's higher cells, which are coherence-case under P and operation-case under L. So no new kind of term is needed. Status: **open, owned by B5/C1**.

**B4.3 Soundness. Reduced to B5 + E11.**
- **Under P.** Interpret `lim_Γ[γ]` in Loubaton's ω as `laxlim_{Free(Γ)^μ}` of the diagram.
  - ω is lax complete: Prop. 4.2.3.8 with A = 1, since `1̂ = Hom(1ᵗ, ω) = ω` **[paper]**.
  - Its universal property is Cor. 4.2.3.18 **[paper]**: `hom(a, l) ≃ hom_{Hom⊖(I,ω)}(cst 1, hom(a, F–))`.
  - §7 checks that the cells of the right-hand side are exactly the repaired table, so J1 and J2 are interpreted by this equivalence and its inverse.
  - What remains: B5 (the specified shapes present `I ⊖ Dⁿ♯`) and E11 (interpreting a CaTT-style theory in (∞,ω)-categories, shared with CaTT itself).
- **Under L.** Strict soundness is Theorem A plus Theorem 1 of `pseudo-vs-gray.md`, again modulo B5. The (∞,ω) version is B8's open half (`oriented-lax-limits.md`).

---

## 7. Hom_⊖ (B13)

### 7.1 Under P: identified at the generator level

**Loubaton's definitions [paper].**
- Def. 4.1.4.1: `Hom(a, Hom⊖(I, A)) := Hom(I ⊖ a♯, A♯)` for a globular sum a.
- Construction 3.1.2.15: `C ⊖ [b, n]♯` is the pushout of `m_{b♯}(C ⊗ [n]♯)` along the vertices, where `m_C` sends `[a, n]` to `[a × C, n]`. That is, the hom-ω-categories of `C ⊗ [n]` are **multiplied cartesianly** by b.
- Prop. 3.1.2.17 makes this explicit for `[C, 1] ⊖ [b, 1]♯`. Its middle term is `[(C ⊗ [1]♯) × b♯, 1]`.

**Reading off the cells.** Cones are 1-cells of `Hom⊖(I, ω)`, i.e. maps `I ⊗ [1]♯ → ω`, since `C ⊖ K♯ ≅ C ⊗ K♯` for (∞,1)-categories K. A k-transfor between cones is a (k+1)-cell, i.e. a map `I ⊖ [D^{k−1}, 1]♯ → ω`. Take Γ = (x, y, f : x → y) and k = 1. A cone morphism is a 2-cell of `Hom⊖(I, ω)`, so the test shape is `D² = [D¹, 1]` and b = D¹ = [1]:
- The hom of `I ⊗ [1]` from (x,0) to (y,1) is the arrow category `{(f⊗0);(y⊗e) → (x⊗e);(f⊗1)}`. Multiplying it by b = [1] gives a **commutative** square. So the comparison m_f is degenerate (an equivalence), while m_x and m_y, the new 1-cells `(x⊗e) × e` and `(y⊗e) × e`, are arbitrary.
- In general, a component over a generator g of dimension j at transfor level k ≥ 1 is a cell of `(hom of I ⊗ [1]) × b`. It is an arbitrary cell when g is an object (j = 0), and a cell of a cartesian product with a positive-dimensional factor in the hom-of-I direction otherwise, hence an equivalence.
- Diagram marks: `f ⊗ e` is marked when f is (Remark 4.2.3.7).

This is exactly the repaired table (response eq. (6)): **lax in the first transfor direction, cartesian above it**. So "certified comparison cells over positive-dimensional diagram generators" is Hom_⊖, read through Prop. 3.1.2.17. **Verified at the generator level.** The full identification, that `Tr_n(Γ)` presents `Free(Γ) ⊖ Dⁿ♯` as a context, is part of B5.

### 7.2 Under L

The cone categories are the full Gray homs: `⟦Dᵏ, H⟧ʳ` at every generator (Theorem A), with ⊗ in every transfor direction and nothing cartesian. In Loubaton's terms this would be `Hom(I ⊗ a, –)` with the *plain* Gray tensor in place of ⊖ **[conj for (∞,ω); proved strict]**. That is the internal Gray hom, which Loubaton's ω does not use for its *own* homs (they are cartesian). This is why L's semantics needs an oriented ambient.

**B13: done for P at the generator level, and for L in the strict model.** The rest is B5.

---

## 8. One schema, and where the variance alternates (B12)

### 8.1 The alternating variance is a property of the index

The weighted-limit theorem (`conjectures/weighted-as-partially-lax-omega.md`, response §4) alternates the variance of the *marked cells of ∫W*: cocartesian 1-cells, cartesian 2-cells, and so on. The *cone* side does not alternate:
- marking a k-generator makes its (k+1)-dimensional cone cell invertible, uniformly in k (Remark 4.2.3.7, response §6);
- the cone cells all have the lax direction `D(u)λ_j ⇒ λ_j′` (eq. (2)).

So **the limit schema needs no per-dimension variance parameter.** The alternation is part of the condition that `(π : Ψ → Γ, μ)` presents a left cartesian fibration, i.e. B14 (§9). This corrects `limits-representables.md` §10.4, which said the schema must alternate.

### 8.2 The schema

One schema `Shape_ε(Γ; c)`, with ε ∈ {lim, colim} and a diagram marking μ. Other lax/oplax variants come from cotensors with opposite shapes (`limits-representables.md` §10.6).

| ε | Legs | Cone cell over `f : x → y` | Transfor shape (L) | Transfor comparison (L) |
|---|---|---|---|---|
| lim | `p_x : c → D x` | `p_f : p_y ⇒ p_x ; D f` | `Dⁿ ⊗ Dᵏ`: **transfor index first** | `m_f : p_f;(m_x▷f) ⇛ m_y;q_f` |
| colim | `q_x : D x → c` | `q_f : q_x ⇒ D f ; q_y` | `Dᵏ ⊗ Dⁿ`: **diagram index first** | `m_f : m_x;q′_f ⇛ q_f;(Df◁m_y)` |

**Derivation of the colim row.** For w : u ⇒ u′ : colim → c, compute `F(w)_f` with L's single direction: second-factor cell first ⇛ first-factor cell first. Here the first factor is λ_f (along `D x → colim`) and the second is w (along `colim → c`):

```
(λ_x◁w) ; (λ_f▷u′)   ⇛   (λ_f▷u) ; (Df;λ_y ◁ w).
```

That is `m_x;q′_f ⇛ q_f;(Df◁m_y)`. Theorem A′ gives the same shape semantically: `Dᵏ ⊗ Dⁿ`. **Both rows are well typed with L's one interchange direction.** They differ in which cell comes first, so their Gray factor orders are opposite.

Under P both orders give the same thing, since the higher directions are cartesian (§7.1), and Loubaton's colimits use the same ⊖ (Def. 4.2.3.3).

### 8.3 Full duality is not a symmetry of L

Write °, op₁, co for reversing all cells, 1-cells only, and 2-cells only. Transport L's interchanger `S ⇛ T` (with S = `(u◁φ);(β▷v′)` and T = `(β▷v);(u′◁φ)`) through each duality, apply L's rule in the dual ambient, and translate back:

| Duality | What L derives in the dual, read in 𝒦 |
|---|---|
| ° | T ⇛ S |
| op₁ | T ⇛ S |
| co | T ⇛ S |
| op₁ ∘ co | S ⇛ T |

Each of "reverse dimension 1", "reverse dimension 2" and "reverse dimension 3" flips the interchanger. So a duality preserves L's 3-dimensional interchanger iff it reverses an even number of the dimensions {1, 2, 3}. Higher Gray cells add further parity conditions, which is D8's even-duality question.

**Consequence.** Colimit rules under L cannot be obtained by dualising limit derivations, as `limits-representables.md` §4.3 suggested for P. They need the specified diagram-first shapes of §8.2. Under P (CaTT core), full duality *is* a symmetry (Benjamin–Markakis), so `Cocone(Γ; c) = Cone(Γ°; c)°` works there.

This fact is passed to D8.

**B12 is closed as a design.** The open parts are D8 (dualities under L) and B14.

---

## 9. Finite fibration test (B14)

### 9.1 Proved: set-valued weights over graphs

**Proposition.** Let Γ and Ψ be finite 1-dimensional computads (graphs). Let `π : Ψ → Γ` send vertices to vertices and edges to edges, with every edge of Ψ marked. Then `Free(Ψ)^♯ → Free(Γ)^♯` is a left cartesian fibration (condition (19) of the weighted-limit response) **iff** π is a **discrete opfibration of graphs**: for every vertex e of Ψ and every edge u of Γ out of π(e), there is exactly one edge of Ψ over u out of e.

*Proof.*
- **(⇐)**
  - Unique edge lifting gives unique path lifting, so `Free₁(Ψ) → Free₁(Γ)` is a discrete opfibration of 1-categories.
  - By the free-on-graph theorem (`conjectures/free-on-graph.md`), the free weak ω-categories on Ψ and Γ are equivalent to these free categories. Their homs are discrete.
  - Check Thm 3.2.2.24(5)'s three conditions **[paper, as quoted in the response]**:
    1. Unique marked lifts: unique path lifting.
    2. Condition (20) for marked u: unique factorisation in a discrete opfibration.
    3. Hom maps right cartesian: they are maps of discrete spaces, which is trivially so.
- **(⇒)** A lift of the length-1 path u at e must be a single edge, because π sends edges to edges. Condition 1 of Thm 3.2.2.24(5) asks for a unique one. ∎

**Completeness.** Every functor `Free(Γ) → FinSet` is a graph action (one function per edge). Its category of elements is the free category on the covering graph. So **every finite-set-valued weight on a free category on a graph has a finite presentation passing this test.** Weighted limits by such weights include products indexed by finite sets, and the conical limits used in `limits-representables.md` §6.

### 9.2 Category-valued weights over graphs: solved (researcher, verified)

See `conjectures/answered/finite-fibration-test-2026-11-18.md`.
- **(Loc) holds in every positive dimension.** Inverting a set S of marked cells is a pushout of Loubaton's marked trivialisations `D_{k+1}^t → D_k^♭`, hence initial and final (Def. 3.2.1.6, Prop. 3.2.1.7). So the whole cone (∞,ω)-categories over J and J[S⁻¹] agree (Lemmas 4.2.3.15, 4.2.3.23).
- **FT₂ is the test.** Vertical generators are unmarked, μ = horizontals ∪ θ's, one marked horizontal lift per (vertex, base edge), and one marked filler θ_{u,β} per (vertical edge, base edge). Then the localisation is the Grothendieck construction of the transport functor. The test is complete for weights valued in categories free on finite graphs, and a checker may index by the unlocalised computad.
- **Use in the horn rules (§5.3).** By (Loc), a marked index cell that every diagram sends to an equivalence may be inverted in the index without changing the limit. In particular, marked diagram generators of dimension ≥ 1 can be treated as invertible index cells when comparing shapes.

### 9.3 2-dimensional bases (FT₃): solved for positive bases; hypothesis is homotopicality (researcher, verified)

See `conjectures/answered/finite-fibration-test-2d-base-2026-11-18.md` (PR #76).

**The data FT₃ needs for each base 2-generator α : u ⇒ v:**
- vertical paths `a_{α,e}` satisfying finitely many path equalities (naturality on generators);
- marked lifts `λ_{α,e} : τ_{u,e};a_{α,e} ⇒ τ_{v,e}`, with prescribed target;
- a marked 3-generator Ξ_{α,β} for each 3-dimensional naturality relation, inverted together with the θ's.

**Results:**
- **Positive bases.** A 2-computad is *positive* when no 2-generator has an identity in its boundary. For positive bases, Free(Γ) ≃ F₂(Γ) (Chanavat 2603.22242, Cor. 3.39), and FT₃ holds. On the walking 2-cell, the homs are intervals or points. The general positive case follows from Loubaton Thm 3.2.3.15.
- **Some non-positive bases admit no finite presentation.** Take σ : 1_x ⇒ 1_x. The localisation of B²ℕ is K(ℤ,2), but every finite `Free(Ψ)[S⁻¹]` groupoidifies to a finite CW complex. This obstruction belongs to that base, not to non-positivity: round 2 (§9.4) shows that Q = (∗; t; η : 1 ⇒ t) is non-positive with Free(Q) ≃ F₂ = BΔ_+^inj. **So the right hypothesis of the weighted-limit rule is "homotopical" (Free(Γ) ≃ F_n(Γ)), not positivity.** Positivity is one sufficient condition for it (Chanavat).

### 9.4 Higher bases (FT_n): partly solved (researcher, verified modulo cited Loubaton results)

See `conjectures/answered/finite-fibration-test-higher-base-2026-11-18.md` (PR #99).

- **Walking 3-cell base, Cat-valued weights: solved.** The presentation is the FT₃ data plus:
  - 3-generators `ω_e : λ_{α,e} ⇛ λ_{β,e}`, one per fibre vertex;
  - 4-generators `K_{Ω,f}`, one per fibre arrow;
  - localisation at the θ's, Ξ's and K's.

  In general, the generators are the relative Gray-tensor generators `k ⊗ a` of a universal total space. The ω_e alone do not suffice: the Euler-characteristic count is 4 − 6 + 6 − 4 = 0, but B × [1] is contractible.
- **2-category-valued weights over the walking 2-cell: a 4-generator (α ⊗ fibre 2-cell) is necessary.** Sufficiency is open.
- **Regularity is not necessary.** A non-regular 3-computad (x, y, z; p, q : x → y; r : y → z; α, β : p ⇒ q; ζ : α▷r ⇛ β▷r) still has Free ≃ F₃.
- **Pattern for the kernel.** Every case so far is "the Gray-tensor generators of the fibre against the base generator, with the over-identity ones marked and localised". This matches the Gray shapes the limit rules already use (§1, §5), so the weight test should be stated through the same shape construction (B5) rather than as a separate rule.
- **Round 2 (researcher, verified; PR #112):** `conjectures/answered/finite-fibration-test-higher-base-r2-2026-11-18.md`.
  - **2-category-valued weights over the walking 2-cell: solved.** The presentation is a double Gray cylinder: generators u_x, v_x, η^w_f, λ_x, κ^w_ρ, Ξ_f and one 4-generator Ω_ρ per fibre 2-cell, localised at η, κ, Ξ, Ω. Every boundary and the Euler characteristics are checked.
  - **Lemma.** X[S⁻¹] ⊗ I ≃ (X ⊗ I)[s⊗0, s⊗1, s⊗i]⁻¹. "Gray localised at the mixed generators ≃ product" holds for 2-category fibres when all mixed dimensions are included.
  - **Positivity is not necessary.** Q = (∗; t; η : 1 ⇒ t) is non-positive with Free(Q) ≃ F₂ = BΔ_+^inj, and its suspension is a non-positive homotopical 3-computad. The hypothesis is "homotopical" (§9.3).
  - **Open.** General FT_n: gluing totals gives attaching maps only into the localised category, and lifting them to Free(Ψ) is the missing step. Also open: a decidable homotopicality criterion for 2- and 3-computads.
- Round 3 (verified, `conjectures/answered/finite-fibration-test-higher-base-r3-2026-11-18.md`): attaching maps lift along δ_r : I → [r], so FT holds over every homotopical base of dimension ≤ 2 with fibres of any finite dimension; an operadic criterion and an obstruction for homotopical 2-computads; a 3-dimensional attachment rule.
- Round 4: `conjectures/outbox/finite-fibration-test-higher-base-r4.md` (unsent).

### 9.5 Bases of dimension ≥ 4: which auxiliary generators the checker accepts (FTX, 2026-11-19)

**The problem.** The uniform presentation with one relative Gray generator q ⊗ g per (base generator, fibre generator) pair is **false** from base dimension 4. The counterexample is in `conjectures/answered/fibration-presentations-all-dimensions-2026-11-19.md` §1 (Followup). It is machine-checked in `src/CaTTExp/Fibration/PentagonCounterexample.agda`: every positive 3-cell of the relevant hom is enumerated, and the short side R → E → L of P ⊗ x has no positive lift, because it needs the inverse of the mixed generator M = μ ⊗ g. After localisation the boundary exists (V ; M⁻¹ ; V). What fails is only the attaching map in the unlocalised Free(Ψ).

**Options.**

1. **Orientation freedom only.** The checker accepts either orientation of each inverted generator. This is conservative by (Loc): `Free(s : a → b)[s⁻¹] ≃ Free(s′ : b → a)[s′⁻¹]`. It repairs the pentagon: reversing M gives the edge Ee → El, and the short side becomes V ; M′ ; V. It fails as soon as two faces of one base generator need the same mixed generator in opposite directions. Nothing rules that out from base dimension 5.
2. **Inverse data on inverted generators (recommended).** For any generator s : a → b in the inverted set S, the presentation may add:
   - a right inverse `r_s : b → a` with a witness `ρ_s : s · r_s → 1_a`;
   - a left inverse `l_s : b → a` with a witness `λ_s : l_s · s → 1_b`.
   
   All four go into S, and the rule may be iterated (inverse data on a witness). For example, the pentagon uses r_M : c₂;u₀ ⇛ u₀;c₀, whose witness ρ_M is a 4-generator. Each step is conservative: the space of one-sided inverses of an equivalence is contractible, so the localisation does not change. (Quasi-inverse data, one inverse with both witnesses, is *not* contractible, and should not be the rule.) The data is generator-level, has the same rule class as the existing marking/inversion data, and each new boundary is determined syntactically by s.
3. **The complicial route** (§2 of the same answer). This gives finite presentations for every homotopical base and every weak weight with finitely presented values, via anodyne expansions and the L_d conversion. The certificate consists of simplicial-set data and has no n + m bound. It is correct, but it is not generator-level, and it does not match the CaTT rule aesthetic (standard 5).

**What the checker verifies with option 2.** The certificate lists the relative Gray generators g ⊗ c, their inverse data, and for each base generator of dimension k an explicit **attaching map** Φ_k. Φ_k is a computad map from the local block presentation over ∂D_k (R5 item 16, fully explicit) into Free(Ψ_{<k} + inverse data). The checks:

- (a) Φ_k is a computad map, i.e. boundaries agree syntactically;
- (b) it lies over the base attaching map;
- (c) it sends marked generators to marked cells and inverted ones to cells built from S;
- (d) it is the identity on the two end fibres.

**Soundness** is the fibrewise-equivalence argument of `conjectures/fibration-test-nonsuspension.md` §3 step 5. After localisation, Φ_k is a map of left cartesian fibrations over ∂D_k that is the identity on fibres, hence an equivalence. The pushout then presents ∫T by Loubaton Cor. 3.2.3.16.

**Existence** of certificates (completeness of the rule):

- *Sketch.* The localisation Free(Ψ)[S⁻¹] is the sequential colimit of the presentations with n-fold iterated inverse data. The block over ∂D_k is a finite computad, hence compact. So its canonical map into the localisation factors through a finite stage.
- *What is not yet established.*
  - A written-out compactness proof in Loubaton's model.
  - A bound on the iteration depth. For the pentagon, depth 1 suffices.
  - Whether the n + m dimension bound survives. The pentagon stays within it.
- These are tracked under B14.

**Worked example (pentagon).** Base b; a; μ : aa ⇒ a; associator α; pentagon P. Fibre x, g, δ, κ. Weight T(a) = constant at x. The presentation is:

- the generators of (1) in the answer;
- the long-side boundary R →V B_δ →D B_c →V C →V L_r →κ L_l, which is positive;
- the short-side boundary R →V E_early →r_M E_late →V L_l, which uses r_M;
- r_M and ρ_M, both inverted, besides M.

With option 1 alone (M reversed), this example also passes. The Agda file records that M as prescribed has no inverse path, which is what forces one of the two options.

**Update 2026-11-19: the n + m bound and the uniform presentation Ω** (`conjectures/answered/fibration-presentations-characterization-r2-2026-11-19.md`, verified).

This supersedes the "existence" paragraph above, i.e. the compactness sketch, the open bound on inverse-data depth, and the open question whether n + m survives.

- **Every pair has a presentation of dimension ≤ n + m, and n + m is optimal.**
  - *Hypotheses.* Γ is a finite homotopical n-polygraph. T is a coherent weight whose values are Free(Π_b)[W_b⁻¹] with dim Π_b ≤ m.
  - *Conclusion.* There are a finite homotopical Ψ of dimension ≤ n + m and finite sets Q (cartesian marking) and S (localisation) such that `(Free(Ψ), ⟨Q ∪ S⟩)[S⁻¹] ≃ (∫T, Cart)` over the base.
  - *Optimality.* Take base ∂D_{n+1}, fibre ∂D_{m+1} and the constant weight. The total groupoidifies to Sⁿ × S^m, which has H_{n+m} ≠ 0.
  - *The pentagon example* has a presentation of dimension ≤ 7.
- **The uniform presentation Ω.** This is the form the checker should accept in general.
  - The original fibre polygraphs Π_b are literal subpolygraphs.
  - For each base k-generator q and source-fibre j-generator g there is a designated generator z_{q,g} of dimension k + j. Its 0-endpoints are the original fibre vertices. It is cartesian-marked, and it is in S when j > 0.
  - The positive-dimensional faces of z_{q,g} are **auxiliary face copies**. These are related to the required composites by explicitly localised **comparison cylinders**.
  - dim Ω ≤ n + m. Ω itself need not be homotopical.
- **How Ω relates to option 2.**
  - Ω's comparison cylinders are a uniform version of option 2's inverse data. Instead of an inverse of each offending mixed generator, every face gets an auxiliary copy with an inverted comparison to the composite it stands for. Both are conservative for the same reason: inverted data with contractible choice does not change the localisation.
  - Option 2 is cheaper when it applies, since it needs no auxiliary face copies. The pentagon needs only r_M and ρ_M. Ω always applies.
  - **Recommended rule:** accept presentations of Ω's shape, with the §8 certificate of that answer: finite incidence tables, elementary-anodyne steps, the generator and localisation lists, and a check that every localisation generator projects to an identity. Option 2 is the special case where the comparison cylinders are inverse data on existing mixed generators.
  - The certificate's own proof witnesses have unbounded size and dimension. Only the output presentation is bounded by n + m.
- **Still open: recognising the unaugmented presentation.** Is the plain relative-Gray presentation, with Leibniz attaching expressions and no auxiliary generators, correct for a given (Γ, T)? Once attaching terms are supplied, this is only positively semi-decidable (§10 of the answer). A terminating criterion, or an undecidability proof, is the round-3 prompt `conjectures/outbox/fibration-presentations-characterization-r3.md`. The pentagon shows the plain presentation can fail. The Agda file shows it fails *as prescribed*.

---

## 10. Open items, owners and hand-offs

| # | Item | Owner |
|---|---|---|
| 1 | Shapes `Cone`, `Tr_n` (transfor-first) and cocone shapes (diagram-first) as functions, matched to the cell-attachment formula of §1.3; the [conj] `Tr_n(Γ) = Cone(Dⁿ ⊗ Γ)[π]`. Needed by B4.2 (higher generators), B4.3, B7, B13. | B5, "Define canonical cone constructions" (`cmsg_018pe2CvdFGDdsWgn8Tjn5gbLYSyekUerAT8DpXZFBCtrp`) |
| 2 | Agda: encode the horn form (§5.3) for P on top of PR #22. Under LCORE's core (PR #26), encode the L version with `F(w)_g` as operation-case cohs, and machine-check that the forced-invertibility derivation is blocked, i.e. that no inverse of the interchanger is derivable. | ledger B15, LIM-F (accepted 2026-11-18) |
| 3 | Agda: machine-check the B9 induction for d = 4 in the *intended* rules (selector and copy fixed, unrestricted transfors), inside the horn encoding. The printed rules cannot run the collapse at all, since over an arrow they never produce the needed transfors (`catt-lim-formalization.md` D1/D3). | ledger B16, LIM-F (accepted 2026-11-18) |
| 4 | (∞,ω) version of Theorem A for general Γ, matched to the specified shapes. The arrow case is done (researcher, verified). | ledger B17, LMETA |
| 5 | Composition of transfors over higher generators (B4.2). | C1 / B5 |
| 6 | Dualities under L: the parity table of §8.3, extended to higher Gray cells. | D8 |
| 7 | Finite fibration test over higher bases (FT_n). FT₃ is solved for positive bases, and 2-category-valued weights over the walking 2-cell are solved (§9.4). The rule's hypothesis is "homotopical base" (Free ≃ F_n), not positivity; some non-positive bases admit no finite presentation (§9.3). Open: general FT_n lifting step, and a homotopicality criterion. | ledger B14, LMETA; prompt `conjectures/outbox/finite-fibration-test-higher-base-r4.md` ready to send (rounds 1–3 answered; round 3 settles FT over homotopical bases of dimension ≤ 2) |
