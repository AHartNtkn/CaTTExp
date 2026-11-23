# Higher and directed inductive objects from INIT

*Design notes, 2026-11-23. Owner: thread "Develop higher and directed inductive types via INIT" (HIT). Question asked: does the initiality construction (spec §9.3, INIT) cover analogs of higher inductive types (HITs) and of directed HITs? Companion to `spec/09-ordinary-math.md` §9.1–9.4, `notes/universe-free-principles.md` §4 and `notes/homotopy-polygraphs.md`. Open-issues rows F11–F11g.*

*Markers as in `universe-free-principles.md`. **[proved here]**: proof written out in this note. **[sketch]**: proof idea complete, details not written. **[recall]**: background knowledge, not re-checked this session. **[conj]**: unproved. **[paper]**: checked against the cited source at statement level.*

---

## 0. Answer

**Yes, with three qualifications.** INIT's grammar already admits cell constructors of every dimension, invertible or not, and the initial models are what one expects:

| Context (sketch) | μΔ | Reference |
|---|---|---|
| `(X, x, y : ⊤ → X, f : x → y)` | the directed interval ⟦D¹⟧ | Thm A |
| `(X, b : ⊤ → X, l : b → b)` | the **directed circle** BN: the free (∞,ω)-category on a loop, a 1-category | Thm A, T-graph |
| the same with `l inv`, or with `X : grpd` | the **circle** S¹ = BZ, the free ∞-groupoid on a loop | Thm A, Thm B |
| `(X, n, s : ⊤ → X, m : A → Hom_X(n, s))` | the Gray suspension ΣA (Hom(n, s) = A) | Thm A, R-A⁺ |
| the same with `X : grpd` | the homotopy suspension of \|A\| | Thm B |
| `(X : grpd, b, p, q : b → b, t : p;q ⇒ q;p)` | the torus K(ℤ², 1) | Thm B, §7.2 |
| `(X, b, p, q : b → b, t : p;q ⇒ q;p)` | the **directed torus**: the strict free 2-category on that computad, trunc 2 | Thm A, §7.3 |
| `(X, x : ⊤ → X, e : 1_x ⇒ 1_x)` | the directed 2-sphere D²/∂D²; **not** the strict B²ℕ | Thm A, §7.3 |
| `(X : grpd, g : A → X, sq : π₁ ⇒ π₂ : X × X → X)` | the propositional truncation ‖A‖₋₁ (recursive higher constructor) | Thm C |
| the same without `grpd`, A = ⊤ | **not** ⊤: the walking idempotent is a model that ⊤ does not map to | Prop C′ |

1. **Universal properties.** When no source mentions X ("cellular" Δ), maps μΔ → B are the same as models of Δ in B, as ω-categories (Lemma 0); for recursive Δ the universal property is initiality among models, as stated in §9.3. For non-recursive ("cellular") contexts, μΔ is a finite cell complex in Cat_ω, an iterated pushout of A ⊗ ∂Dᵏ → A ⊗ Dᵏ (Theorem A). The groupoidal HIT is its ∞-groupoid reflection (Theorem B), so HoTT's non-recursive HITs are the groupoidifications of directed ones.
2. **Dependent elimination** holds for **every** positive Δ and **every** family p : E → μΔ, by the Awodey–Gambino–Sojakova argument (Theorem D). Over a cocartesian family its data unfold to *directed* paths-over: a cell constructor l : x → y asks for a fibre map l_!(e_x) → e_y, which need not be invertible even over a groupoid base. Families over a cellular μΔ are built by DESC, given the cell-shaped edge cases G_k of §6, which are proved here only as a sketch.
3. **h-levels are not decidable** once cell constructors are allowed (Prop E1), so T-init cannot be extended to a complete clause. What can be said: directed cellular contexts are polygraph presentations, and μΔ is n-truncated when the polygraph is *homotopical* (the HPOL characterisation, B24). Bubbles (e.g. the directed 2-sphere) break this. In the groupoidal case there are decidable sound sufficient conditions (Lyndon; Gersten's weight test), proposed as T-init clauses in §7.

**Two findings about the spec**, independent of HITs:
- **(F11a) Which cotensor `Hom_X` is cut from.** The fibre of the *cartesian* cotensor `[⟦D¹⟧, X] → X × X` over (x, y) has only the *invertible* 2-cells of X as its 1-cells, so it is not Hom_X(x, y). Hom targets must be cut from the **lax** cotensor (§1.3). The same choice decides whether an "external" path constructor with a non-point source builds the suspension or collapses it (§2.3).
- **(F11b) R-U is not a positive context as written.** Its operation `p : X → Θ₀` has a constant target other than ⊤, which §9.3's target condition forbids. It is meant as multi-sorted INIT over the set Θ₀ (as §9.4's path example is), and a general version, **INIT over a base and with several sorts**, is sound by the same argument as INIT. It is also what higher inductive-*inductive* definitions need (§8).

---

## 1. Set-up

### 1.1 Representability (Lemma 0) [proved here]

Let Δ be **cellular** (no source mentions X). Then a map h : A → B carries a model σ on A to a model h_*σ on B (compose each operation S → T(A) with T(h); sources are constant), so `Mod_Δ(–)` is a functor and there is a restriction `η* : Hom(μΔ, B) → Mod_Δ(B)`, h ↦ h_*η. A model morphism μΔ → (B, σ) is a map h with invertible cells h_*η ≅ σ: a point of the fibre of η* over σ. INIT-J1 says the fibre is inhabited, INIT-J2 that any two points are connected, and the higher clause (cells between model morphisms are model morphisms into `[⟦Dᵏ⟧, B]`) says that the fibre is contractible at every level.

**Lemma 0.** For cellular Δ, INIT holds iff `η* : Hom(μΔ, B) → Mod_Δ(B)` is an equivalence of ω-categories, natural in B. The cells of `Mod_Δ(B)` are the pointwise ones, i.e. models in `[⟦Dᵏ⟧, B]`.

*Proof.* Contractible fibres at every level give an equivalence on k-cells for every k. Conversely, an equivalence has contractible fibres. ∎

For recursive Δ (a source mentions X) a map out of A does not transport models, and the universal property is only initiality among models. Theorem A below uses Lemma 0; Theorems C and D use only initiality.

### 1.2 Two kinds of cell constructor

A path constructor can be written in two ways that §9.3 both admits:
- **internal:** `c : A → Hom_X(u, v)`, with u, v : A → X earlier composites; the target is cut from a cotensor of X;
- **external:** `c : u ⇒ v`, a cell variable between the maps u, v : A → X (any dimension k + 1, between parallel k-cells).

For A = ⊤ the two agree: a cell between points ⊤ → X *is* a cell of X. For other sources they can differ (§2.3).

### 1.3 Targets are relative cotensors (Lemma 1) [proved here]

Every target admitted by §9.3 is obtained from X by ⊤, homs of earlier points, cotensors `[K, X]` (cartesian or lax) by fixed K, and finite limits of these. Cotensors turn colimits in K into limits, and iterated cotensors compose (`[K, [K′, X]] = [K ⊠ K′, X]`). Hence:

**Lemma 1.** An operation `c : A → T(X)` of Δ is the same as a map `A ⊠ K → X` that restricts on `A ⊠ K₀` to a map given by earlier operations, for a finite K₀ ↪ K read off T. Here ⊠ is × for a cartesian cotensor and the Gray tensor ⊗ for a lax one. Examples: `T = X` gives (∅ ↪ ⊤); `T = Hom_X(x, y)` gives (∂⟦D¹⟧ ↪ ⟦D¹⟧); a (k+1)-cell variable gives (∂⟦D^{k+1}⟧ ↪ ⟦D^{k+1}⟧).

**Which cotensor gives Hom (F11a).** In the cartesian `[⟦D¹⟧, X]`, a 1-cell between arrows u, u′ : x → y with identity ends is a map ⟦D¹⟧ × ⟦D¹⟧ → X, a square that commutes up to an *invertible* 2-cell. So the fibre over (x, y) has the invertible 2-cells u ≅ u′ as its 1-cells, and it is not Hom_X(x, y) unless X is a (∞, 1)-category. In the lax cotensor, 1-cells are lax squares, so the fibre's 1-cells are all 2-cells u ⇒ u′: this fibre **is** Hom_X(x, y). §9.3's sentence "Hom_X(x_v, x_w) is a pullback of [⟦D¹⟧, X]" must be read with the lax cotensor. That reading is also the one under which R-A⁺'s stated initial model (with the Gray suspension ΣB_e) is correct.

---

## 2. Cellular contexts (Theorem A)

Call Δ **cellular** if no operation's source mentions X (sources are fixed objects A_c; targets as in §9.3).

**Theorem A [proved here].** Let Δ be cellular, with operations c₁, …, c_m in order, c_i given (Lemma 1) by `A_i ⊠ K_{0,i} ↪ A_i ⊠ K_i` with boundary map ∂_i built from c₁, …, c_{i−1}. Then μΔ is the iterated pushout
```
M₀ = ∅,   M_i = M_{i−1} ⊔_{A_i ⊠ K_{0,i}} (A_i ⊠ K_i)      (attaching along ∂_i evaluated in M_{i−1}),
μΔ = M_m.
```
If Δ has a mark `inv` on some c_i, μΔ is the localisation of M_m at those cells. If it has a mark `⋆^{≤n}`, μΔ is ‖M_m‖_n. If it has a mark `grpd`, μΔ is \|M_m\| (Theorem B).

*Proof.* By induction on m, with Lemma 0. `Mod_{Δ, c}(B)` is the ω-category of pairs (σ ∈ Mod_Δ(B), an extension of ∂ σ along A ⊠ K₀ ↪ A ⊠ K): this is Lemma 1, applied pointwise. By induction `Mod_Δ(B) ≃ Hom(M, B)`, so `Mod_{Δ,c}(B) ≃ Hom(M, B) ×_{Hom(A ⊠ K₀, B)} Hom(A ⊠ K, B) = Hom(M ⊔_{A⊠K₀} A ⊠ K, B)`, naturally in B. The pullback is computed pointwise at every level, so the equivalence holds on cells as well, and Yoneda gives μ(Δ, c) ≃ M ⊔ (A ⊠ K). An `inv` mark adds the condition "c is invertible" to models; maps out of the localisation are exactly the maps that invert c. A reflective mark restricts B to the reflective class, and maps out of the reflection are maps out of M into that class. ∎

So **cellular INIT is the cell-complex construction of Cat_ω**, and every finite cell complex arises this way (one cell variable per cell). For A_i = ⊤ throughout, the data are a **polygraph** (computad) Γ_Δ, and μΔ = Free(Γ_Δ), the free (∞,ω)-category on Γ_Δ (`homotopy-polygraphs.md`).

### 2.1 Examples, directed

- `(X, x, y, f : x → y)`: ⊤ ⊔ ⊤ ⊔_{∂D¹} D¹ = ⟦D¹⟧.
- **Directed circle.** `(X, b, l : b → b)`: ⊤ ⊔_{∂D¹} D¹ with both ends at b. This is ⟦L⟧, the free (∞,ω)-category on a loop, which is the 1-category BN (T-graph: trunc 1; Hom(b, b) ≃ ℕ by encode–decode, §9.4). Its universal property: maps BN → B are pairs (object, endomorphism) of B, at every level.
- **Walking isomorphism.** `(X, x, y, f : x → y inv)`: the localisation of ⟦D¹⟧ at f, contractible.
- **Directed spheres.** `(X, x, y, f, g : x → y)` is ∂⟦D²⟧; adding `α : f ⇒ g` gives ⟦D²⟧. Iterating gives the globes ⟦Dᵏ⟧ and their boundaries, as the globular sum construction of chapter 1 expects.
- **Directed 2-sphere** `(X, x, e : 1_x ⇒ 1_x)`: D²/∂D². Not the strict B²ℕ: §7.3.
- **Suspension.** `(X, n, s, m : A → Hom_X(n, s))`, with Hom cut from the lax cotensor: ⊤ ⊔ (A ⊗ ⟦D¹⟧) ⊔ ⊤ along A ⊗ ∂⟦D¹⟧, which is the Gray suspension ΣA, with Hom(n, s) ≃ A. This is R-A⁺ for one edge.

### 2.2 Examples, groupoidal (HoTT's HITs)

Add `X : grpd` (§3), or mark every operation `inv`. Then μΔ = \|M_m\|, and since \|−\| preserves pushouts, \|A ⊠ K\| ≃ \|A\| × \|K\| (Campion's (OBJ-1) for ⊗, sifted-colimit commutation for ×), \|⟦Dᵏ⟧\| ≃ * and \|∂⟦Dᵏ⟧\| ≃ S^{k−1}, the result is the CW complex with one cell \|A_i\| × D^{k_i} per cell variable. That is the standard semantics of non-recursive HITs in spaces (Lumsdaine–Shulman's cell monads, "Semantics of higher inductive types", 2020) **[recall]**:
- circle S¹ = \|BN\| = BZ (the classifying space of the free monoid on one generator is S¹);
- spheres S^k, the torus, suspensions Σ\|A\|, pushouts, finite CW complexes.

So in the system **HoTT's non-recursive HITs are the groupoid reflections of directed ones**, and the directed object is the more general one (standard 4).

### 2.3 Internal vs external constructors under P (F11a) [proved here]

Take the external form of the suspension, `(X, n, s : ⊤ → X, m : n ∘ ! ⇒ s ∘ ! : A → X)`. Under L the cell lives in the lax cotensor and Theorem A attaches A ⊗ ⟦D¹⟧: the same ΣA as the internal form. Under P (cells between maps A → X are pseudo-natural) it attaches A × ⟦D¹⟧, and the result is different:

*Example.* A = ⟦D¹⟧. Then A × ⟦D¹⟧ is the commutative square, and collapsing its ends {0} × A and {1} × A is the localisation at those two edges (collapsing an edge Δ¹ → Δ⁰ is a localisation, and pushouts of localisations are localisations). The commutative square with both horizontal edges inverted is ⟦D¹⟧, so Hom(n, s) ≃ ⊤, not A = ⟦D¹⟧. The arrow of A has been identified away, not turned into a 2-cell.

So a directed path constructor family must be written internally (or externally under L). For groupoid A, or A = ⊤, the forms agree.

---

## 3. Groupoidal marks (Theorem B) [proved here]

∞-groupoids form a reflective and coreflective subcategory of Cat_ω (reflector \|−\|, coreflector the core), closed under all limits and colimits. So `X : grpd` is a mark of the kind §9.3 allows ("restricts X to a reflective class closed under limits and filtered colimits"). The same holds for `grpd_k` ((∞, k−1)-categories, reflector the localisation at all cells of dimension ≥ k).

**Theorem B.** Let R be a mark's reflective class with reflector ρ. If ρ commutes (by the canonical comparison) with every source functor of Δ, then μ(X : R, Δ) ≃ ρ(μΔ).

*Proof.* ρ(μΔ) carries a model (apply ρ to the operations, using ρS(X) ≃ S(ρX) on sources and the unit on targets, which are limit-preserving and so preserve R). For B in R, maps ρ(μΔ) → B are maps μΔ → B, which are models in B by Lemma 0, and a model on an R-object is the same in both contexts. ∎

\|−\| commutes with coproducts, colimits, ⊗ and × with fixed objects. It does not commute with pullbacks or cotensors. Example: `S(X) = X ×_{X×X} X = [S¹, X]` (S¹ = ⊤ ⊔_{⊤⊔⊤} ⊤ = BZ in Cat_ω). For X = ⟦D¹⟧, maps BZ → ⟦D¹⟧ land in the core {0, 1}, so \|S(X)\| is two points, while S(\|X\|) = S(∗) = ∗. So Theorem B covers every cellular context and every recursive context whose sources are built from colimits, products and Gray tensors. For sources with pullbacks, μ(X : grpd, Δ) is still an INIT instance, just not computed by Theorem B.

---

## 4. Recursive higher constructors

### 4.1 Propositional truncation by a squash constructor (Theorem C) [proved here]

Δ_sq(A) := `(X : grpd, g : A → X, sq : π₁ ⇒ π₂)`, with π₁, π₂ : X × X → X (source X × X: positive; target the cotensor [⟦D¹⟧, X]: limit-preserving).

**Theorem C.** μΔ_sq(A) ≃ ‖A‖₋₁.

*Proof.* A model is an ∞-groupoid B with a map A → B and a natural transformation α : π₁ ⇒ π₂. Claim: B carries such an α iff B is empty or contractible, and then α is unique. If B is contractible, the space of transformations is contractible. If x ∈ B, restrict α to {x} × B: a transformation const_x ⇒ id_B, i.e. a section of the path fibration (x ↓ B) → B. That total space is contractible, so id_B factors through a contractible space and B is contractible. So the models are the (−1)-truncated groupoids under A, whose initial object is ‖A‖₋₁ (INIT-J1/J2 for the mark ⋆^{≤−1}). ∎

So the HoTT definition of ‖A‖₋₁ by a recursive path constructor is an INIT instance, and it agrees with the truncation by mark.

### 4.2 The directed squash is not a truncation (Prop C′) [proved here]

Drop `grpd`: Δ⃗_sq := `(X, g : ⊤ → X, sq : π₁ ⇒ π₂)`.

**Prop C′.** ⊤ is not the initial model of Δ⃗_sq.

*Proof.* Let Idem be the 1-category with one object ∗ and endomorphisms {1, e}, e ∘ e = e. Put g = ∗ and sq_{(∗,∗)} = e. Every naturality square (along pairs from {1, e}²) reads `e ∘ e = e ∘ e` or `e = e ∘ e`, so sq is natural: (Idem, ∗, e) is a model (strict naturality is in particular pseudo and lax). A strong model morphism ⊤ → Idem would need an invertible cell h(sq_⊤) ≅ sq_Idem, i.e. 1_∗ ≅ e, and e is not invertible. Since there is a model morphism Idem → ⊤, the initial model maps to Idem, so it is not ⊤. ∎

[conj] The initial model is Idem (as an (∞,1)-category, Lurie's walking idempotent, whose (∞,1)-nerve is the 1-category). The 1-categorical version is immediate: a morphism to (B, b, α) must send e ↦ α_{b,b}, which is idempotent by naturality. The ∞-version needs the coherence of the idempotent built from α. Row F11e.

---

## 5. Dependent elimination (Theorem D) [proved here]

There are no universes, so a family over μΔ is a map p : E → μΔ, and a section is s : μΔ → E with s ; p ≅ 1 (§9.4).

**Theorem D.** Let Δ be positive and p : E → μΔ any map. A **dependent model** over η is a model σ_E of Δ on E with a model-morphism structure on p : (E, σ_E) → (μΔ, η). For every dependent model there is a section s with s ; p ≅ 1 and s ∘ η ≅ σ_E *over* η. Any two such sections are connected by an invertible cell over μΔ, at every level.

*Proof.* (Awodey–Gambino–Sojakova; Sojakova's "HITs as homotopy-initial algebras", arXiv:1402.0761, for W-suspensions in HoTT.) Let s := rec_{σ_E}, a model morphism by INIT-J1. Then p ∘ s and 1 are both model morphisms η → η, and INIT-J2 gives p ∘ s ≅ 1 *as model morphisms*, so the computation cell s ∘ η ≅ σ_E lies over η. Uniqueness: two sections over η are model morphisms into E over μΔ, so INIT-J2 in the slice (equivalently, in the cotensor for the higher clause) connects them. ∎

This needs no condition on Δ (recursive constructors, marks and cells included) and none on p. It is the general dependent eliminator, with propositional computation rules as invertible cells, which is the CaTT style.

**Fibrewise reading.** When p is a cocartesian fibration, a cell of E over a 1-cell constructor l : x → y of the base is the same as a fibre map `l_!(e_x) → e_y` (factor through the cocartesian lift). So the dependent datum for a path constructor is a **directed path-over**. It need not be invertible even when l is: over S¹ with fibres non-groupoidal, the datum is a fibre endomorphism l_!(e) → e, not an automorphism. For groupoid fibres it is HoTT's path-over. For k-cell constructors the datum is a k-cell in E over the constructor, which straightening (Loubaton Thm 4.1.4.2, already cited in §9.2) turns into a cell between transported fibre data. The fibrewise form is a reading of Theorem D, not a separate rule.

---

## 6. Families over cellular μΔ (descent) [sketch]

By Theorem A a cellular μΔ is a finite colimit, so DESC-glue applies, given a description of cocartesian fibrations over each attaching piece A ⊠ ⟦Dᵏ⟧. For k = 1 that is G₁ and G⁺ (§9.4). For k ≥ 2:

**Prop G_k [sketch].** Cocartesian fibrations over ⟦Dᵏ⟧ (and relative to a base A) are glued from data (fibres over the two ends, a pair of parallel transport (k−1)-cells, and a k-cell between them), with uniqueness at every level.

*Sketch.* ⟦Dᵏ⟧ = Σ⟦D^{k−1}⟧ is the pushout of ⊤ ← ⟦D^{k−1}⟧ ⊗ ∂⟦D¹⟧ → ⟦D^{k−1}⟧ ⊗ ⟦D¹⟧ (I2 of `homotopy-polygraphs.md`). DESC-glue over this pushout reduces to the Gray cylinder ⟦D^{k−1}⟧ ⊗ ⟦D¹⟧, which is DESC-or along the cylinder relative to the base ⟦D^{k−1}⟧, exactly as G⁺ is obtained (§9.4). Induct on k. ∎ (Same status as G⁺: paper only. Row F11c.)

*Examples.* Over the directed circle, a cocartesian family is a fibre F with an endofunctor φ : F → F. For F = ℕ, φ = succ, encode–decode gives Hom_{BN}(b, b) ≃ ℕ, i.e. T-graph's computation. Over S¹, a family is F with an automorphism, and F = ℤ, φ = succ gives ΩS¹ ≃ ℤ (§9.5).

Recursive μΔ (§4) are not finite colimits, so DESC does not build families over them directly. Theorem D still eliminates into any given family. Families *defined by induction* over a base need INIT over a base (§8).

---

## 7. h-levels

### 7.1 No complete clause (Prop E1) [proved here]

**Prop E1.** No decidable rule is sound and complete for `μΔ trunc 0` over cellular Δ with a `grpd` mark, already for one point, 1-cells and 2-cells, with mark ⋆^{≤1}.

*Proof.* For a finite presentation ⟨g_1..g_r | w_1..w_s⟩ take `(X : grpd, X : ⋆^{≤1}, b, g_i : b → b, ρ_j : w_j ⇒ 1_b)`. By Theorems A and B, μΔ = ‖P‖₁ = BG with P the presentation complex. BG is trunc 0 iff G is trivial, which is undecidable (Adian–Rabin). ∎

This is why T-init excludes cell variables, and it settles that **no extension of T-init can be complete**. Extensions must be sound sufficient conditions.

### 7.2 Groupoidal: decidable sufficient conditions [paper; recall for the theorems cited]

For one-object 2-dimensional groupoidal Δ (a presentation complex P), P aspherical gives μΔ = K(G, 1), trunc 1. Two decidable sufficient conditions:
- **Lyndon**: one relator, not a proper power ⇒ P aspherical **[recall]**. The torus `⟨p, q | pqp⁻¹q⁻¹⟩` is covered: μ = K(ℤ², 1).
- **Gersten's weight test** (decidable) ⇒ diagrammatically reducible ⇒ aspherical **[recall; see Gersten 1987, and arXiv:1601.00604 for a recent test]**.

Proposed clause **T-init-asph** (row F11d): groupoidal cellular Δ of dimension ≤ 2 whose 2-cells pass the weight test ⇒ μΔ trunc 1. Sound by the cited theorems; decidable.

### 7.3 Directed: the polygraph question (B24) [proved here, relative to HPOL]

For cellular Δ with all sources ⊤ and no marks, μΔ = Free(Γ_Δ). If Γ_Δ is **homotopical** (Free(Γ) → F(Γ), the strict free ω-category, is an equivalence) and has dimension ≤ n, then μΔ is a strict n-category, so trunc n (cells above n are identities, so every parallel pair above n is filled by an identity). Hence:
- **directed torus**: the computad (b; p, q; t : pq ⇒ qp) is 2-dimensional and bubble-free, so homotopical (dimension-2 theorem, `homotopy-polygraphs.md`), and μΔ is the strict free 2-category, trunc 2;
- **directed 2-sphere** (x; e : 1_x ⇒ 1_x): e is a bubble, so Γ is not homotopical (Theorem N), and μΔ ≠ B²ℕ. Its End(1_x) is expected to be the free E₂-monoid on a point (configuration spaces of the plane), so μΔ has non-trivial 3-cells (the Eckmann–Hilton braiding) **[conj]**;
- dimension-1 Γ (graphs) is always homotopical, which is T-graph.

The exact characterisation of homotopical polygraphs in every dimension is open and owned by HPOL (B24); its answer becomes a T-init clause directly. Proposed clause **T-init-pol** (row F11d): cellular, ⊤-sourced, unmarked Δ of dimension ≤ n whose polygraph is positive-to-one (r2 Response 1 Thm 2, a decidable sufficient condition) ⇒ μΔ trunc n.

---

## 8. INIT over a base and with several sorts (F11b) [proposal; soundness sketch]

**The finding.** R-U (`universe-free-principles.md` §4.3; spec §9.7) writes `Δ = (X : ⋆, p : X → Θ₀, a : Φ_p(X) → X over Θ₀)`. The target Θ₀ of p is a constant other than ⊤, which §9.3 forbids, and rightly so for that grammar: the forgetful functor to Cat_ω does not create limits (the product of two models over Θ₀ is a pullback over Θ₀). §9.4's path example uses the same pattern, "read over the finite set V by DESC-grpd".

**Proposal (INIT_B, multi-sorted).** Allow finitely many distinguished variables X₁, …, X_m, each over a fixed base object B_i (B_i = ⊤ by default). Operations are maps over the bases; targets are limit-preserving in the slices `Cat_ω/B_i` (with B_i in place of ⊤); sources are accessible covariant in all X_j.

*Soundness [proved, relative to the verified researcher answer].* The verified INIT answer (`conjectures/answered/universe-free-descent-and-initial-models-2026-11-21.md`, "Maximal uniform target class") proves existence of initial models for any presentable category of carriers, explicitly including a slice. `∏_i Cat_ω/B_i` is presentable (slices and finite products of presentable categories are), and its terminal object is (B_i)_i, so the same argument applies, with the same maximal target class. Adopted into spec §9.3 (2026-11-23).

*What it gives.*
- R-U and §9.4's path family as stated, without the DESC-grpd detour, and over non-discrete bases;
- **inductive families over any base**, e.g. a universal cover over S¹ defined inductively rather than glued;
- **higher inductive-inductive definitions**: a sort R with p : R → X × X (target limit-preserving in (X, R)) declared together with X, as the Cauchy reals and partiality QIITs need.

Row F11b (closed). Not derivable from single-sort INIT in an obvious way; non-derivability is not claimed.

---

## 9. What INIT does not cover

- Constructors with X in a contravariant position (excluded already for ordinary inductive types).
- Final models / coinductive objects (unsound in general, §9.3).
- The directed analogue of a *specific* HoTT recursive HIT need not be its directed truncation (Prop C′): one has to pick the constructor that means what is wanted.

---

## 10. Open items (all rows in `open-issues.md`)

| Row | Item | Owner |
|---|---|---|
| F11 | HITs and directed HITs as INIT instances: this note; spec §9.3 examples | HIT (this thread) |
| F11a | Spec: Hom targets are cut from the lax cotensor; external constructors under P | HIT |
| F11b | INIT over a base and multi-sorted (R-U as written violates §9.3) | HIT; spec change after review |
| F11c | G_k: cocartesian fibrations over ⟦Dᵏ⟧ from DESC-or (needed for families over cellular μΔ) | HIT |
| F11d | T-init-asph and T-init-pol as h-level clauses; directed case waits on B24 (HPOL) | HIT |
| F11e | Directed squash: is the initial model the walking idempotent? | HIT |
| F11f | Agda: Theorem D over an abstract category of models (`CaTTExp.HIT.DependentElim`); Prop C′ and the §2.3 collapse (`CaTTExp.HIT.DirectedSquash`); 1-truncated, written, awaiting honesty review | HIT, coordinated with S26a (binders) |
