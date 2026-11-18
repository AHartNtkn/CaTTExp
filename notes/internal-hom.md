# Internal hom, Gray tensor, and lax vs pseudo

*Design notes, 2026-11-18, revised the same day. Part I states the lax-vs-pseudo problem; the comparison of options is in `notes/pseudo-vs-gray.md`. Part II holds the technical material: literature, rules and side conditions. Builds on `catt-survey.md` (project files). Claims marked **[recall]** come from background knowledge and were not re-checked against the source. Rules are proposals, not results.*

---

# Part I. The choice, in practice

## I.1 What is being decided

The plan is to run CaTT with the ambient being "the ω-category of ω-categories":
- objects (variables of type ⋆) are categories;
- 1-cells are functors;
- 2-cells are transformations between functors;
- and so on up.

The question is **what a 2-cell α : F ⇒ G is**, concretely what its naturality cells look like. For a cell f : x → y of the source category, α has a component α_x : Fx → Gx and a naturality cell comparing Gf ∘ α_x with α_y ∘ Ff.

- **Pseudo** (also called strong): the naturality cell is invertible. The components α_x are still ordinary one-way cells, not isomorphisms.
- **Lax**: the naturality cell goes one way only, and need not be invertible.

Every pseudo transformation is a lax one, so lax is the more general notion. Lax transformations are what show up for lax limits, lax algebras, monad morphisms and twisted constructions.

## I.2 The fact that forces a choice

In CaTT, the following is a theorem, produced by the coh rule.

> Take two 2-cells side by side, α : f ⇒ f′ on the left and β : g ⇒ g′ on the right. Applying α first and then β, or β first and then α, gives two composites. CaTT supplies a cell between them **in both directions**, so they are equivalent. This is the interchange law.

Now read it in the ambient, where α and β are transformations between functors:

- α : F ⇒ G, where F, G : A → B;
- β : H ⇒ K, where H, K : B → C.

The two composites are "do α, then β" and "do β, then α", both going from HF to KG. Evaluated at an object a, they differ by the naturality cell of β at the component α_a. So:

- if β is **pseudo**, that naturality cell is invertible and the interchange law holds. CaTT is sound.
- if β is **lax**, the naturality cell exists in one direction only. CaTT would also give the reverse cell, which does not exist in general. CaTT is **unsound**.

So **if the core rules are CaTT's, the ambient's native 2-cells are pseudo**. The limits notes (PR #2, §3) reach the same conclusion independently.

Your blog post already reflects this. It observes that the naturality square of a transformation comes out as a coherence. Coherences between full composites come in both directions, so the squares produced that way are invertible, i.e. pseudo.

## I.3 The comparison of options

The full comparison of the two responses lives in **`notes/pseudo-vs-gray.md`** (PR #5). It is the single pseudo-vs-lax comparison for the project. Its option names:
- **P** keeps the CaTT core and gets lax transformations as functors into lax arrow objects. P is what earlier versions of these notes called Option A.
- **L** makes the native 2-cells lax, with a directed interchange. L was called Option B here.

These notes previously had their own comparison in this place. It was superseded, and corrected on several points, by that note's "Reconciliation" section.

---

# Part II. Technical material

The section numbers below continue those of the first version of these notes.

**Scope.** §4 and §5 are **Option P material**. They are the rules P needs: the Gray tensor of contexts, the lax hom out of a shape, the pseudo hom, and the marked cylinder. Under L, the kernel does not need Gray-shaped contexts. The Gray shapes would still be useful there for describing Gray-shaped diagrams (e.g. lax cones). Wherever §4 and §5 say "Option A", read "Option P".

## 1. Literature

### 1.1 Strict ω-categories

- **Ara–Maltsiniotis**, *Joint et tranches pour les ∞-catégories strictes* (Mém. SMF 165; [arXiv 1607.00668](https://arxiv.org/abs/1607.00668v4)). They build the Gray tensor product on strict ω-Cat through Steiner's augmented directed complexes. **[recall]** It is monoidal and biclosed but not symmetric:

  ```
  Hom(A ⊗ B, C) ≅ Hom(A, Hom_oplax(B, C)) ≅ Hom(B, Hom_lax(A, C))
  ```

  (lax/oplax naming depends on convention). The tensor of two Steiner-free ω-categories is again Steiner-free, with basis {x⊗y}. They also describe joins and slices, which are the lax cones Mikhail uses.
- **Crans** (thesis, 1995) **[recall]** gave the first Gray tensor of ω-categories, and also a pseudo version. **Al-Agl–Brown–Steiner** **[recall]** handle the cubical side.
- **Steiner's formula** **[recall]** gives the boundary of a product generator by a Leibniz rule: d(x⊗y) = dx⊗y + (−1)^|x| x⊗dy.

### 1.2 Weak (∞,n) and (∞,ω)

- **Campion**, *An (∞,n)-categorical pasting theorem* ([2311.00200](https://arxiv.org/abs/2311.00200v1)). For a class of pasting diagrams, the space of composites assembled from all the generators is contractible in any (∞,n)-category. The class is torsion-free complexes (Forest), which include Θ-cells, orientals, **lax Gray cubes** and regular directed CW complexes. This is the semantic licence for "molecular coh" in §4.3.
- **Campion**, *The Gray tensor product of (∞,n)-categories* ([2311.00205](https://arxiv.org/abs/2311.00205v1)). He builds models as presheaves on categories of computads and defines ⊗ by Day convolution plus reflection, with model-independent universal properties. The idea that "Gray tensor of computads is computed generator-wise" is what §4 copies syntactically.
- **Campion–Kapulkin–Maehara**, *A cubical model for (∞,n)-categories* ([2005.07603](https://arxiv.org/abs/2005.07603)). This is the cubical route to the Gray tensor.
- **Gagna–Harpaz–Lanari**, *Gray tensor products and lax functors of (∞,2)-categories* ([2006.14495](https://arxiv.org/abs/2006.14495)). The edges of Fun^gr and Fun^opgr are lax and oplax transformations. Their Prop. 2.12 says the Gray product, with triangles marked where one edge is invertible, maps by an equivalence to the cartesian product. This is the (∞,2) evidence for "pseudo = lax + marking" (§5.5). Their Remark 2.20 warns that the naive adjunction fails at the level of point-set models, so currying statements must be read ∞-categorically.
- **Loubaton**, *Categorical theory of (∞,ω)-categories* ([2406.05425](https://arxiv.org/abs/2406.05425)). A lax transformation f ⇒ g : A → B is a map A ⊗ [1] → B with the given ends. Gray cylinder, cone and ◦-cone are pushouts of C ⊗ [1]. There is an internal hom whose 1-cells are lax transformations. Mikhail's Gray rules follow Loubaton.
- **Chanavat**, *Gray products of diagrammatic (∞,n)-categories* ([2505.01387](https://arxiv.org/html/2505.01387v1)). On regular directed complexes, P ⊗ Q has underlying poset P × Q. The boundary is given by the formula (Prop. 2.16)

  ```
  ∂ₙ^α(U ⊗ V) = ⋃ₖ ∂ₖ^α U ⊗ ∂ₙ₋ₖ^{(−)ᵏα} V
  ```

  On diagrammatic sets it is defined by Day convolution and is biclosed, with internal homs of lax and oplax transfors. Also (X ⊗ Y)^op ≅ Y^op ⊗ X^op for the odd duality, and tensoring with the walking equivalence is a functorial cylinder.

### 1.3 Lax transformations and their conventions

- **Johnson-Freyd–Scheimbauer**, *(Op)lax natural transformations, twisted QFTs, and "even higher" Morita categories* ([1502.06526](https://arxiv.org/abs/1502.06526)). They build C^↓ (lax), C^→ (oplax) and [Θ⁽¹⁾, C] (strong) from walking i-by-j-morphisms, which are higher analogues of Crans–Gray cells. A lax transformation is a functor B → C^↓. Functors themselves stay strong; only transfors are lax. They follow Bénabou's naming: a lax transformation has G(b)∘η ⇒ η∘F(b). Their motivation for lax: with duals, strong transformations are forced to be invertible, and adjunctibility is classified by lax twists.
- **Haugseng**, *On lax transformations, adjunctions, and monads in (∞,2)-categories* **[recall]**.

### 1.4 The CaTT line

- **Mikhail, CaTT_lim** ([2412.13310](https://arxiv.org/abs/2412.13310), §4.1). This defines the judgments `M₁;…;M₂ₙ₊₁ gray Γ`. Each variable x is duplicated to x′ and a cell pₓ is added. For Γ = (x, y, f, g, α : f → g) and n = 1:

  ```
  pₓ : x → x′     p_y : y → y′
  p_f : f·p_y → pₓ·f′
  p_α : (α ∗ 1_{p_y})·p_g → p_f·(1_{pₓ}·α′)
  ```

  Side conditions are τCond/σCond, in the same style as the cone conditions. Existence is proved only for globular Γ and n = 1, and the n > 1 claim is unproved. Remark 4.5 points to Ara–Maltsiniotis for the strict formula.
- **Benjamin–Markakis–Offord–Sarti–Vicary**, *Naturality for higher-dimensional path types* ([2501.11620](https://arxiv.org/abs/2501.11620)). This is a meta-operation producing naturality fillers along a directed interval, "a local tensor product with a directed interval". **[recall]** It takes a term and a set X of its variables, and produces the filler relating the composite at x⁻ with the composite at x⁺ through cells x⃗.
- **Benjamin–Markakis**, Σ ⊣ Hom, and homs of free are free ([2402.01611](https://arxiv.org/abs/2402.01611)). This is the template for the native internal hom rule in §5.4.

---

## 4. Gray tensor of contexts

### 4.1 Definition

Input: finite CaTT contexts Γ and Δ, viewed as finite computads (Benjamin–Markakis–Sarti). Output: a context Γ ⊗ Δ.

- **Generators.** One variable x⊗y for each x ∈ Γ and y ∈ Δ, with dim(x⊗y) = dim x + dim y. They are ordered by total dimension, then lexicographically, which is compatible with dependency.
- **Typing.** For dim x = m and a sign α ∈ {−, +}:

  ```
  ∂^α(x⊗y)  :=  composite of the molecule  (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^m α} y)
  x⊗y : ∂⁻(x⊗y) → ∂⁺(x⊗y)
  ```

  This is Steiner's Leibniz formula (Chanavat Prop. 2.16 gives all boundary levels).
- **Extension to terms.** Here ∂^α x is a *term* of Γ, usually a composite, so t ⊗ y must be defined for terms t:
  - if dim y = 0, then t ⊗ y is t with each variable x renamed to x⊗y (a substitution Γ → Γ ⊗ Δ);
  - if dim y = 1, then t ⊗ y is the naturality filler of t along y, i.e. the BMOSV meta-operation with X = all variables of t;
  - for higher y, it is the iterated version.

  So **⊗ on contexts is "naturality, iterated and applied generator-wise".**

**Check against Mikhail** (n = 1). Write I = (0, 1, i : 0 → 1). Then I ⊗ Γ is Mikhail's `gray` output with pₓ = i⊗x and x′ = 1⊗x. For a 1-cell f : x → y, dim i = 1 and α = − give

```
∂⁻(i⊗f) = (0⊗f)·(i⊗y) = f·p_y        ∂⁺(i⊗f) = (i⊗x)·(1⊗f) = pₓ·f′
```

This matches p_f. So Mikhail's "Γ ⊗ Dⁿ" is Dⁿ ⊗ Γ in the AM/Steiner orientation. Conventions should be fixed once, in one place.

**Lax vs oplax orientation.** With the convention of §5.3, functors into [D¹, C]ₗₐₓ, where the cells have shape Δ ⊗ D¹, have naturality cells α_b · Gf ⇒ Ff · α_{b′} (diagrammatic order). That is Bénabou/JFS **lax**. The other side, D¹ ⊗ Δ, gives oplax.

### 4.2 Side conditions

| Condition | What it says | Status |
|---|---|---|
| **G1. Well-typedness** | The two composites ∂⁻(x⊗y) and ∂⁺(x⊗y) have *syntactically equal* boundaries, since CaTT has only syntactic definitional equality. | Main burden; see §4.3. Mikhail proves it for Γ globular, Δ = D¹. |
| **G2. Functoriality in substitutions** | A substitution σ : Δ′ → Δ induces Γ ⊗ σ : Γ ⊗ Δ′ → Γ ⊗ Δ, using the same term extension t ⊗ y. Needed for naturality of λ in §5.3. | Follows from G1 if t ⊗ – commutes with substitution. Unproved. |
| **G3. Preservation of wedges** | Γ ⊗ (Δ ∨ Δ′) ≅ (Γ ⊗ Δ) ∨_{Γ⊗pt} (Γ ⊗ Δ′) | Immediate on generators. Needed for composing transformations. |
| **G4. Associativity** | (Γ ⊗ Δ) ⊗ Θ ≅ Γ ⊗ (Δ ⊗ Θ) | Bijective on generators. Agreement of types holds up to coherence, so strict equality may need CaTT_sua. |
| **G5. Linearity** | Mikhail's x ∝ t may be needed when a boundary term uses a variable non-linearly (e.g. after an endo-coherence). | Open. It is unclear whether the naturality meta-operation imposes it. |

### 4.3 Two ways to get the composites

The molecules in ∂^α(x⊗y) are generally **not pasting schemes**. For example, the source of the Gray cube's 3-cell is a hexagon of three lax squares. Plain coh cannot compose them directly. There are two in-style options:

**(i) Layering, with coherence bookkeeping.** Write each molecule as a sequence of whiskered single generators (a *layering*) and compose with ordinary ps-composites, inserting associators and unitors so the boundaries line up.
- This is what Mikhail does by hand, with explicit types and τCond/σCond.
- **Over CaTT_sua the associators and unitors disappear definitionally**, so any layering has the right boundary on the nose. Different layerings still differ by interchange, so a canonical layering must be chosen.
- This suggests that **Gray shapes push strict associativity/units (Rice) earlier** than "end-stage ergonomics". It may be part of the core typing story.
- Existence of layerings is a real condition on molecules ("frame-acyclic" in Hadzihasanovic's terminology **[recall]**). Gray products of globes should satisfy it, but this needs checking.

**(ii) Molecular coh.** Extend the coh rule from pasting schemes to a class 𝓜 of *molecules*, with the same two side conditions:

```
U ∈ 𝓜    U ⊢ t →_A u    Δ ⊢ σ : U
(composition)  Var(t:A) = Var(∂⁻U),  Var(u:A) = Var(∂⁺U)
(coherence)    Var(t:A) = Var(U) = Var(u:A)
──────────────────────────────────────────────
Δ ⊢ coh_{U, t→_A u}[σ] : (t →_A u)[σ]
```

- **Semantic licence:** Campion's pasting theorem. For torsion-free complexes, which include lax Gray cubes, composites exist and the space of them is contractible.
- **The class 𝓜 must be molecules, not arbitrary computads.** For example, the 2-skeleton of the Gray cube (a 2-sphere with no 3-cell) is a computad but not a molecule. Coh over it would *create* the Gray cube's 3-cell as an invertible coherence, collapsing laxness.
- So the shape judgment must certify "molecule", not just "finite computad". A natural candidate is the class generated from globes by ⊗, joins and pasting.
- **Gain:** ∂^α(x⊗y) is a single unbiased term coh_{∂^α(x⊗y)}. G1 becomes a statement about molecules, not about chosen bracketings.
- **Cost:** this answers survey §12 Q3 ("how far may non-ps shapes go?") with "to molecules". Pruning, insertion and rehydration would have to be re-examined for molecules.

**(i) and (ii) are the same question.** Molecular coh (ii) is a conservative extension of CaTT exactly when every molecule's composites exist and are unique up to invertible cells in plain CaTT, which is what (i) needs. This is stated as Conjecture G(n) in [`conjectures/gray-contexts-in-catt.md`](conjectures/gray-contexts-in-catt.md). Status:
- **G(1)** is proved.
- **Existence in G(2)** is proved, using Chanavat's result that all molecules of dimension ≤ 3 are frame-acyclic. So **every Gray generator of dimension ≤ 3 has a plain-CaTT type**, including the Gray cube.
- **Uniqueness in G(2)** has a proof sketch: linear extensions are connected by swaps, and each swap is an exchange coherence. One bookkeeping gap remains. Granting it, every Gray generator of dimension 4 is covered too.
- **G(n) for n ≥ 3** is open. The missing step is translating Chanavat's contractible subdivision poset (arXiv 2603.22242, Thm. 2.52) into CaTT cells. The problem statement there is written for external researchers.

---

## 5. Rules for Option A

The ambient judgment `Γ ⊢ C : ⋆` means C is an ω-category. `Γ ⊢ φ : Δ ⊳ C` means φ is a Δ-shaped diagram in C, i.e. a functor ⟦Δ⟧ → C, equivalently a 1-cell out of a representable. How representables are presented is the other thread's question. These rules only assume:

- diagrams Δ ⊳ C exist;
- they can be precomposed with substitutions σ : Δ′ → Δ (written φ ∘ σ);
- they can be postcomposed with ambient 1-cells F : C → D (written F ∘ φ).

### 5.1 Lax hom out of a representable

```
       Θ ⊢   (finite, closed)      Γ ⊢ C : ⋆
(lhom) ───────────────────────────────────────
               Γ ⊢ [Θ, C] : ⋆

        Γ ⊢ φ : (Δ ⊗ Θ) ⊳ C                     Γ ⊢ ψ : Δ ⊳ [Θ, C]
(lhom-Λ) ─────────────────────           (lhom-♭) ──────────────────────
        Γ ⊢ Λφ : Δ ⊳ [Θ, C]                      Γ ⊢ ψ♭ : (Δ ⊗ Θ) ⊳ C

(β-cell)  Γ ⊨ βφ : (Λφ)♭ → φ            (η-cell)  Γ ⊨ ηψ : ψ → Λ(ψ♭)
(nat-Δ)   Γ ⊨ (Λφ) ∘ σ → Λ(φ ∘ (σ ⊗ Θ))   for σ : Δ′ → Δ    (needs G2)
(nat-C)   Γ ⊨ F ∘ (Λφ) → Λ(F ∘ φ)         for F : C → D
```

**No definitional β or η.** β, η and naturality are *invertible cells*, written in Mikhail's invertibility judgment ⊨ (or as ICaTT invertible cells), not equations. This is the pattern of CaTT_lim's `uni` fillers. The theory keeps only syntactic definitional equality, as in core CaTT.

There are two ways to generate these cells:
- (a) list them as above, with their higher coherences produced by a single filler schema in Mikhail's style;
- (b) use Mimram's approach (§5.7): declare the relevant shapes contractible, so that Λ, ♭ and all their laws are coherences over those shapes.

(b) is more uniform. (a) is closer to existing published rules.

- **Covariance in Θ.** A substitution τ : Θ′ → Θ induces a restriction [τ, C] : [Θ, C] → [Θ′, C], defined by Λ((–)♭ ∘ (Δ ⊗ τ)).
- **Style.** The rule is a shape plus a bijection with no new side conditions beyond G1 and G2. It is the hom-version of Mikhail's cone rule: a representing object for a family of Gray-shaped diagrams.
- **D⁰ check.** Points of [Θ, C], i.e. D⁰ ⊳ [Θ, C], are Θ-diagrams in C, since D⁰ ⊗ Θ ≅ Θ.
- **Correction: the bijection is between maps, not between whole hom-categories.**
  - Native higher cells of the ambient are cartesian. A 2-cell between φ, φ′ : ⟦Δ⟧ → [Θ, C] is a map (⟦Δ⟧ × D¹) ⊗ Θ → C, *not* a 2-cell between the transposes in Fun(⟦Δ⊗Θ⟧, C). Gagna–Harpaz–Lanari (2006.14495), Rem. 2.20, show these differ in general.
  - So (lhom-Λ/♭) must be read as a correspondence of *maps* Δ ⊳ –. Higher cells are reached by letting Δ range over marked cylinders: ⟦Δ⟧ × D¹ ≃ ⟦(Δ ⊗ D¹)^μ⟧, which is Theorem (P) below (formerly Conjecture C1, now proved).
  - The β-, η- and naturality cells are invertible ambient cells, consistent with this reading.
  - See [`conjectures/planar-pasting-types.md`](conjectures/planar-pasting-types.md) §4 for the precise form of the obstruction.
- **Cotensors turn colimits of shapes into limits** (handed over from limits-representables.md §10.6). This is formal from the rule: a map into [Θ, C] is a map out of Δ ⊗ Θ, and ⊗ preserves colimits of contexts in each variable (G3 is the case of a wedge). So [colim Θᵢ, C] ≃ lim [Θᵢ, C], provided the limit exists.
- **Role under P** (limits-representables.md §10.1). Cone-style limits cannot produce lax cotensors or hom objects Hom_C(a, b) under a pseudo ambient. Under P, these come from this rule. In particular, Hom_C(a, b) is the fibre of [D¹, C] → C × C over (a, b).

### 5.2 Lax transformations between arbitrary functors

For F, G : B → C (ambient 1-cells), define

```
LaxTr(F, G)  :=  fibre of  [B, [D¹, C]] → [B, C] × [B, C]  over (F, G)
```

The map is induced by the two endpoint substitutions 0, 1 : D⁰ → D¹. This uses the native hom (§5.4) and a pullback, which belongs to the limits thread. A point of LaxTr(F, G) is a functor α : B → [D¹, C] whose ends are F and G (up to the fibre's identification). Its "naturality square at f : b → b′" is the D¹ ⊗ D¹ generator, which is a lax square.

### 5.3 Composition and interchange are restriction along coherences

- **Vertical composition.** By G3, [D¹ ∨ D¹, C] ≃ [D¹, C] ×_C [D¹, C]. The 1-composite comp : D¹ → D¹ ∨ D¹ is a substitution (a coh term), and composition of lax transformations is the restriction [comp, C]. Every associativity or unit law for lax transformations is then the restriction along a coherence between substitutions of globes. **No new rule is needed.**
- **Whiskering.**
  - On the left: precomposition B′ → B → [D¹, C].
  - On the right: postcomposition with [D¹, H] : [D¹, C] → [D¹, D] (nat-C).
- **The lax interchanger.** For α : B → [D¹, C] and β : C → [D¹, D], the composite [D¹, β] ∘ α : B → [D¹, [D¹, D]] ≃ [D¹ ⊗ D¹, D] (currying plus G4) picks out a Gray square of transformations. Its 2-cell generator *is* the directed interchanger of §I.2. The non-invertible interchange appears as a *generator of a shape*, not as a coherence. This is how Option A avoids the obstruction.

### 5.4 Native (pseudo) internal hom

This makes the ambient's own hom-ω-categories into objects. It is the Benjamin–Markakis adjunction Σ ⊣ Hom, promoted to an object former:

```
        Γ ⊢ B : ⋆    Γ ⊢ C : ⋆
(hom)   ───────────────────────
           Γ ⊢ [B, C] : ⋆

        Γ ⊢ σ : ΣΔ → Γ    σ(N) ≡ B    σ(S) ≡ C               Γ ⊢ φ : Δ ⊳ [B, C]
(hom-⌜⌝) ──────────────────────────────────────    (hom-⌞⌟) ─────────────────────────────
        Γ ⊢ ⌜σ⌝ : Δ ⊳ [B, C]                              Γ ⊢ ⌞φ⌟ : ΣΔ → Γ    (ends B, C)

with invertible cells ⌞⌜σ⌝⌟ → σ and φ → ⌜⌞φ⌟⌝, and naturality in Δ, as in §5.1
(no definitional equations)
```

Here ΣΔ → Γ means a ΣΔ-shaped tuple of terms of the ambient context. So "a Δ-cell of [B, C]" is "a ΣΔ-diagram of functors, transformations, … from B to C".

- **Elements and application.** An element of [B, C] is a 1-cell F : B → C. Application to an element a : D⁰ ⊳ B is composition F ∘ a. So evaluation is ambient composition, and it needs no product. Currying with × waits on products from the limits thread.
- **The CaTT coh rule applies inside [B, C] unchanged.** Its cells are pseudo transfors, so the exchange law is sound.

### 5.5 Pseudo as marking

**Theorem (P)** (was a conjecture; proved 2026-11-18, see [`conjectures/gray-vs-cartesian.md`](conjectures/gray-vs-cartesian.md), C1/C1′). For representable Θ,

```
Δ ⊳ [⟦Θ⟧, C]  ≃  (Δ ⊗ₘ Θ) ⊳ C
```

Here Δ ⊗ₘ Θ is Δ ⊗ Θ with every *mixed* generator x⊗y (dim x, dim y ≥ 1) marked invertible in the sense of ICaTT. Equivalently, ⟦Δ⟧ × ⟦Θ⟧ is the localisation of ⟦Δ ⊗ Θ⟧ at the mixed generators.

- **Status: proved**, in (∞,ω) and for every finite n. The general statement is (A ⊗ B)[mixed⁻¹] ≃ A × B, where the localisation is at the images of mixed generators along all globe maps.
  - The proof is by an external researcher; it was verified by the literature-search thread and merged as PR #14.
  - It completes the earlier sketch with two lemmas: tensoring a localisation with the interval, and generated markings in Loubaton's marked cylinder.
  - It then runs a cube induction and extends to all objects through Campion's cube density, using mapping spaces.
  - Lemma S3 follows.
- **Correction: the marking must reach the boundaries.** The pseudo hom is a sub-object of the lax hom, but it is **not locally full**.
  - An r-cell σ of [Θ, C]ₗₐₓ is pseudo exactly when its adjunct inverts every mixed cell, *including those on its boundary faces*.
  - So a cell between two pseudo cells can still fail to be pseudo. The counterexample is B = D¹, C = D³: a modification between two strong transformations with a non-invertible naturality 3-cell.
  - In the rules, ⊗ₘ marks **all** mixed generators of Δ ⊗ Θ, boundary ones included. That is the correct condition. A rule that marked only the top cell and inherited membership from the endpoints would be wrong.
- **Consequently,** [⟦Θ⟧, C] (pseudo) embeds in [Θ, C]ₗₐₓ as the part whose cells invert all mixed cells, including those on boundaries. The two homs then share one rule schema, [Θ, C]_μ for a marking policy μ ∈ {lax, pseudo}:
  - only the context operation changes (⊗ vs ⊗ₘ);
  - the λ/♭ rules are identical;
  - μ = pseudo needs ICaTT's invertibility judgment (Benjamin–Champin–Markakis) or Mikhail's ⊨ judgment.
- **Payoff:** "lax by default" holds at the level of shapes. Pseudo is an extra marking, never a separate construction.
- **Consistency check:** (P) with Θ = D¹ says the native 2-cells of the ambient (pseudo transformations) are exactly the lax transformations whose naturality cells are invertible.

### 5.5a The marked Gray cylinder rule (from the limits notes)

`notes/limits-representables.md` §5.1 (PR #2) proposes this rule and hands it to these notes:

```
Hom(⟦Γ⟧, D)(u, v)  ≃  Hom(⟦(Γ ⊗ D¹)^μ⟧, D)        (fibre over the ends u, v)
```

This is the case Δ = D¹ of Theorem (P). It says that an ambient (pseudo) 2-cell between Γ-diagrams u, v is the same as a marked Gray cylinder with ends u and v. Here it is stated in this note's notation, for any shape Δ:

```
        Γ ⊢ φ : (Δ ⊗ₘ Θ) ⊳ C                    Γ ⊢ ψ : Δ ⊳ [⟦Θ⟧, C]
(cyl-Λ) ────────────────────────         (cyl-♭) ──────────────────────────
        Γ ⊢ Λₘφ : Δ ⊳ [⟦Θ⟧, C]                  Γ ⊢ ψ♭ₘ : (Δ ⊗ₘ Θ) ⊳ C

β-, η- and naturality cells exactly as in §5.1 (invertible cells, not equations)
```

The cylinder rule is (cyl-Λ/♭) at Δ = D¹, combined with the native hom of §5.4: a D¹-cell of [⟦Θ⟧, C] is an ambient 2-cell between Θ-diagrams.

Points to settle:

- **Which cells are marked.** Only the *mixed* generators x⊗i with dim x ≥ 1 should be marked, i.e. the naturality cells. The components x⊗i for dim x = 0 are the transformation's components, and they must stay unmarked and directed. Otherwise the rule would classify invertible transformations, not pseudo ones. In Mikhail's notation: mark p_f, p_α, …, never pₓ for objects x.
- **Orientation.** The limits note writes Γ ⊗ D¹. With every mixed cell marked, Γ ⊗ₘ D¹ and D¹ ⊗ₘ Γ should be equivalent, since both model Γ × D¹. So the orientation only matters for the unmarked (lax) version, where it decides lax vs oplax (§4.1, §5.6).
- **Status.**
  - Under Option A (option P of the limits notes), this rule is the *definition* of how pseudo cells of the ambient relate to shapes.
  - Its semantic justification is Theorem (P), formerly Conjecture C1, now proved ([`conjectures/gray-vs-cartesian.md`](conjectures/gray-vs-cartesian.md)).
  - It needs ICaTT-style marking (Benjamin–Champin–Markakis), or Mikhail's ⊨ judgment, to state.
- **Density / extensionality.** The limits note defers to this thread the question of whether components plus naturality determine a transformation. For *representable* domains ⟦Θ⟧, (cyl-Λ) is exactly that principle.
  - For arbitrary domains B, the same question becomes whether the disks are jointly dense, i.e. whether a 1-cell B → [D¹, C] is determined by its restrictions along all elements Dⁿ ⊳ B.
  - In style, that would need a colimit principle presenting B from its cells (§6).
  - *Answered 2026-11-18* (`free-objects-proofs.md` §6): the disks are not dense (counterexample over the composable pair), while pasting diagrams Θ are. The extensionality principle for arbitrary B is therefore Θ-density, a colimit rule tracked under F5.
- **Relation to the lax rule.** (lhom) of §5.1 is the same schema with no marking. Both rules are one schema [Θ, C]_μ with μ ∈ {lax, pseudo}, and the marked Gray cylinder is its μ = pseudo instance.

### 5.6 Oplax and other variances

Oplax homs use Θ ⊗ Δ in place of Δ ⊗ Θ. Since (X ⊗ Y)^op ≅ Y^op ⊗ X^op (Chanavat, odd duality),

```
[Θ, C]ₒₚₗₐₓ ≃ ([Θ^op, C^op]ₗₐₓ)^op
```

So oplax is *derivable* from the lax rule and the opposites meta-operation of Benjamin–Markakis. Only one primitive rule is needed. The even and total dualities give the other mixed-variance versions **[recall: exact duality formulas for ⊗ under even duality]**.

---

### 5.7 Alternative: closed structure by contractible types (Mimram's CCCaTT)

Source: Mimram, *An unbiased simply typed combinatory logic* (CSL 2026; [PDF](http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_cccatt.pdf), [Agda](https://github.com/smimram/agda-ccatt/)). Read from the PDF via a summary, so rule details are approximate.

**What it does.** It is the 1-categorical truncation of CaTT for cartesian closed categories.
- **Pasting types replace pasting contexts.** A type is *pasting* if a deterministic proof search derives `Θ \ ∅ | ∅ ⊢ A`. The rules are `→ps I`, with the side condition that tgt(A) is not already a used target, and `→ps E`, which consumes the head hypothesis. This is a decidable subclass of the contractible types (exactly one βη-inhabitant).
- **One rule gives all combinators.** For a pasting type A there is `coh_A : A`. For example, I, K, S and application (`X, Y | f : X → Y, x : X ⊢ Y`) are all coh.
- **One rule gives all equations.** Any two terms of a pasting type are equal (`ps=`), so β and η come out as instances.
- **No λ/app rule.** Abstraction is meta-level only.
- **Results.** Bijections with STLC (Thm. 19) and with STLC with finite products (Thm. 21), both up to βη. The paper says that an unbiased variant axiomatises cartesian closed ∞-categories. That variant is unpublished; its pasting criterion is implemented in the tool but not yet studied.

**Why it matters here.**
- It is the first CaTT-line treatment of an **exponential**, which is not a limit, so Mikhail's CaTT_lim does not cover it.
- It is in exactly the style Anthony asked for: the universal property is *not* a λ/♭ bijection. Instead, a shape class (pasting types) is declared contractible, and every structure map and law is a coherence over it.
- It is a candidate replacement for the λ/⌜⌝ rules of §5.4. Cartesian closure is the *pseudo* hom, which is what the ambient needs under Option A. In the ω-version:
  - `ps=` would become a coherence cell, invertible as usual;
  - β and η would become higher cells, not definitional equalities;
  - so the "limited normalisation" requirement of survey §13 would be respected.
- **Neutral between P and L** (see `pseudo-vs-gray.md`, R9): each option needs both a cartesian version and a planar/linear version.
- It suggests a route to the **lax** hom too. The Gray tensor is biclosed and *non-symmetric*. An unbiased CCCaTT-style theory for it would need pasting types without duplication or exchange, i.e. a Lambek-calculus-like, planar, linear criterion. Mimram lists closed, linear and planar variants as future work.
  - This lines up with the recurring linearity theme (survey §13; Mikhail's x ∝ t).
  - **1-dimensional case proved** ([`conjectures/planar-pasting-types.md`](conjectures/planar-pasting-types.md) §2). Take pasting types to be the balanced, Lambek-provable sequents. They are contractible: erase the residuals to → and apply the Babaev–Solov'ev coherence theorem. They are also complete: rename the atoms of each axiom link. So an unbiased theory built on them is equivalent to the Lambek calculus modulo βη. Only type substitution is needed, not term substitution.
  - **Open:** the tensor and unit (PL1), and the ω-version (PL-ω). The ω-version has a precise obstruction: Gray closure is an equivalence on mapping spaces but not on mapping (∞,ω)-categories. So a pasting-type theory must track where each higher cell's time direction sits among the tensor factors.

**Caveats.**
- CCCaTT works *inside* one cartesian closed category, whereas §5.4 internalises the ambient ωCat's hom. To match, the pasting types must range over ambient object variables B, C : ⋆, with [B, C] a type former of the ambient. This seems direct.
- The higher-dimensional criterion, which the paper says needs dependent types, is unpublished. Working it out for the cartesian case, and the Gray case via PL-ω, is a next step. The rules of §5.1 and §5.4 do not compete with it: they are what a pasting-type theory would have to derive.

## 6. What about ⊗ of arbitrary objects?

Architecture A never forms B ⊗ C for non-representable B and C.

- **What would be lost:** an object-level ⊗ is needed for lax-functor-category currying [B ⊗ C, D] ≃ [B, [C, D]ₗₐₓ] with *both* B and C arbitrary.
- **Why it is hard:** its mapping-out property is a Day-convolution coend, so it is not finitary. In style, it would have to come from a colimit principle (lax colimits of computads, survey §13 Q3) plus "⊗ preserves colimits in each variable".
- **Next step:** once colimits exist, define B ⊗ C as the colimit, over cells of B and C, of ⟦x ⊗ y⟧. Then check that it has the Gray tensor's universal property. The cocontinuity argument of `conjectures/gray-vs-cartesian.md` §3.1 is the template.

---

## 7. Suggested formalisation targets

These are for the Agda thread, smallest first.

1. **Γ ⊗ D¹ for Γ a pasting scheme** (Mikhail n = 1). Implement it as a function on syntax and prove the output is a well-formed context. This is G1 in the simplest case. It is the base of everything else.
2. **G3:** Γ ⊗ (D¹ ∨ D¹) ≅ (Γ ⊗ D¹) ∨ (Γ ⊗ D¹).
3. **Vertical composition of lax transformations** as a substitution Γ ⊗ D¹ → Γ ⊗ (D¹ ∨ D¹). First check, for Γ = D¹ and D², whether plain coh provides every needed term (option (i) of §4.3). Record exactly which non-ps composites are needed. That list is the concrete case for or against molecular coh.
4. **D¹ ⊗ D¹ ⊗ D¹** (the Gray cube) under both orientations, checking G4 syntactically. This is the first place layering choices (§4.3) bite.

---
