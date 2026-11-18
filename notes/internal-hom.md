# Internal hom, Gray tensor, and lax vs pseudo

*Design notes, 2026-11-18, revised the same day. Part I is a plain-language comparison of the options and what each gains and loses in practice. Part II holds the technical material: literature, rules and side conditions. Builds on `catt-survey.md` (project files). Claims marked **[recall]** come from background knowledge and were not re-checked against the source. Rules are proposals, not results.*

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

There are two ways to respond, described next. A third, keeping two kinds of 2-cell side by side ("double" categories), is mentioned in I.5.

## I.3 Option A: keep CaTT; lax transformations are maps into an "arrow object"

**Description.** The core rules stay exactly as in CaTT. The ambient's native 2-cells are pseudo transformations. Lax transformations are added in a different way:

- For a category C, there is an object C^→ (written [D¹, C]_lax in Part II), the **lax arrow category** of C:
  - its objects are the arrows of C;
  - its 1-cells are squares of C with a one-way 2-cell inside (lax squares);
  - its higher cells are the higher-dimensional analogues (lax cubes and so on), all finite shapes.
- A **lax transformation** α : F ⇒ G : B → C is then a *functor* α : B → C^→ whose source and target ends are F and G. This is the standard definition in the literature (Johnson-Freyd–Scheimbauer; Loubaton).
  - Applying α to an object x of B gives an arrow of C, i.e. the component α_x.
  - Applying α to a 1-cell f of B gives a lax square, i.e. the naturality cell at f.

So a lax transformation is a native 1-cell (a functor) into a constructed object. It is not a native 2-cell.

**What a user does, concretely.**
- *Components and naturality of a lax α.* These are α applied to x and to f, so they are ordinary functor application, then reading off the parts of the resulting shape. They are no harder than for a pseudo transformation. The elaborator can show them as α_x and α_f.
- *Composing two lax transformations.* The composite is a functor B → C^→ built from the two given ones. Gluing two arrows end to end is a coherence on the arrow shape (the composite of two arrows), so the composite comes from a coherence applied to shapes, not from a new rule. The associativity and unit laws for composing lax transformations come the same way.
- *Whiskering by functors.* On the source side, precompose: B′ → B → C^→. On the target side, apply a functor H : C → D to every cell of the arrow shape. Both are ordinary composition.
- *Interchange of two lax transformations.* This appears as a lax square inside D^→, i.e. a two-dimensional arrow object. It is one-way, as it should be, and it is a piece of data rather than a coherence.
- *Pseudo transformations.* These are the native 2-cells, so everything in CaTT applies to them directly: interchange, whiskering, functoriality and the post's "naturality as a coherence".

**What is gained.**
- **No change to the core.** Every existing CaTT result carries over unchanged: the GM/BFM models, computads, CaTT_sua and Rice's strictification, ICaTT invertibility, and the meta-operations (suspension, opposites, functorialisation, naturality, inverses).
- **Duality stays complete.** The opposites meta-operations reverse cells in any set of dimensions, and this is where most of the reported proof-size savings came from (survey §2). In A, reversing dimension 2 of the ambient turns pseudo into pseudo, so nothing is lost. The lax/oplax pair is related by duality at the level of the arrow object.
- **Most ordinary mathematics uses pseudo cells.** Natural isomorphisms, units and counits of adjunctions between functors, and equivalences of categories are all pseudo. They get the full CaTT treatment for free.
- **Known semantics.** The intended model is weak ω-categories with the cartesian closed structure. The lax arrow objects are the constructions of JFS, Loubaton and Campion.

**What is lost.**
- **Lax transformations are second-class syntactically.** They are not cells of the ambient, so CaTT's coh rule does not compose them directly. Every operation on them goes through the arrow object: compose by gluing shapes, whisker by composing functors.
  - This is mechanical, and an elaborator can hide it.
  - But the theory has two notions of "transformation" with different bookkeeping, and the user can see the seam whenever lax and pseudo cells interact. For example, whiskering a lax transformation with a pseudo one means converting the pseudo one into a map into the arrow object first.
- **Two function categories.**
  - The pseudo one, [B, C], exists for every B. It just turns the ambient's own homs into objects.
  - The lax one, [Θ, C]_lax, is directly available only when the domain Θ is a finite shape, such as an arrow or a square. Lax functor categories with an arbitrary domain B have to be assembled, e.g. as the functors B → C^→ with prescribed ends. That assembly needs pullbacks, which come from the limits thread.
- **New shape machinery is still needed.** The arrow-object shapes (lax squares, lax cubes, …) are not pasting schemes. Part II §4 explains how they can be generated from CaTT contexts by a "Gray tensor of contexts". Making their boundaries type-check is the main technical cost (Part II §4.3).

## I.4 Option B: make the ambient's native 2-cells lax, and change the core

**Description.** The ambient's native 2-cells are lax transformations. Then CaTT's interchange coherence has to go. The core is replaced by a variant, call it Gray-CaTT, in which:
- interchange is a **one-way cell**, a generator rather than an invertible coherence;
- the coh side condition must be refined so that it never proves a coherence relating two composites that differ by an interchange.

Pseudo transformations are then lax transformations whose naturality cells are marked invertible, using ICaTT-style marking.

**What a user does, concretely.**
- *A lax transformation* is a native 2-cell. Its components and naturality cells come out of whiskering and interchange, exactly as the post describes, but now the naturality cells are one-way. So lax naturality is automatic.
- *Composition and whiskering* of lax transformations are native composition.
- *A pseudo transformation* is a 2-cell together with invertibility witnesses for its naturality cells. To use the interchange law in the reverse direction, the user, or the elaborator, must supply those witnesses.

**What is gained.**
- **One notion of transformation, one function category.** Lax is the default everywhere and all composition is native. There is no arrow object in the user's way, and no seam between lax and pseudo beyond invertibility markings.
- **The post's observation yields lax naturality** directly. This is arguably the most "directed" reading of the original aesthetic.
- **Function categories [B, C] are lax for every B**, so lax functor categories need no assembly.

**What is lost.**
- **The core must be redesigned, and nobody has done it.** No coherence theory for weak "lax-Gray" ω-categories exists in the literature. The strict analogue (Gray-categories) is well understood only in low dimensions. The new side condition must detect the *orientation* of interchange, which is a new kind of side condition, not a free-variable check. Its correctness is the central open problem.
- **Most existing CaTT results need to be redone.** Models, the computad correspondence, CaTT_sua strictification, ICaTT and the meta-operations were all proved for the invertible-interchange core.
- **Half the dualities stop being symmetries.** Reversing dimension-2 cells turns lax into oplax, so the opposites meta-operation no longer maps the theory to itself in that dimension. The proof-size savings from opposites would be partially lost, or the theory would need lax and oplax variants side by side.
- **Ordinary mathematics pays a tax.** Most transformations used in practice are pseudo. In B, each one carries invertibility witnesses, and each use of reverse interchange needs them. This is the same kind of overhead ICaTT already has, but now it is pervasive.
- **Unknown semantics.** The intended model, ω-categories enriched over the Gray tensor, is expected to exist but is not in the literature in a usable form.

## I.5 Option C, briefly: two kinds of 2-cell

The ambient could carry both kinds of 2-cell as two separate directions, a pseudo one and a lax one, with squares between them. This is a "double ω-category", the structure JFS actually build.
- It makes both kinds of transformation native, with no seam and no unsound coherence.
- It doubles the shape language, since every pasting scheme now has two kinds of 2-cell, and it has no CaTT-style precedent.

It is listed for completeness. It looks strictly heavier than A and B.

## I.6 Side-by-side, task by task

| Task | Option A (CaTT core, lax via arrow objects) | Option B (Gray-CaTT core, lax native) |
|---|---|---|
| Use a natural isomorphism, adjunction unit or equivalence | Native 2-cell; all CaTT coherences apply | Native 2-cell plus invertibility witnesses; reverse interchange needs them |
| Use a lax transformation (lax limits, monad morphisms, lax algebras) | A functor into C^→; components and naturality by application | Native 2-cell |
| Compose lax transformations | Glue arrow shapes along a coherence (no new rule) | Native composition |
| Interchange of two transformations | Pseudo: invertible coherence. Lax: one-way cell inside D^→ | One-way generator; invertible only with witnesses |
| Lax functor category [B, C]_lax, arbitrary B | Assembled from C^→ and a pullback | Primitive |
| Opposites / duality meta-operations | All still symmetries | Dimension-2 reversal swaps lax and oplax; fewer symmetries |
| Existing results (models, computads, CaTT_sua, ICaTT, meta-operations, formalisation) | All carry over | Need re-proving for the new core |
| New machinery | Gray tensor of contexts; molecule composites (Part II §4) | A directed-interchange side condition (unknown), plus the same Gray shapes |
| Semantics | Known (cartesian closed (∞,ω)-categories; JFS/Loubaton arrow objects) | Expected, not available |
| Where the cost is felt | Ergonomics: a seam between lax and pseudo, hidden by elaboration | Foundations: the core and its metatheory |

**Summary.** A puts the cost in usability, where elaboration can absorb most of it. B puts the cost in foundations, where it is an open research problem. In B, everything built on a working core then looks cleaner. Both need the same Gray shape machinery of Part II §4, so that work is useful whichever way the choice goes.

## I.7 What would settle it

These are concrete experiments, not preferences:

1. **Write a lax limit, a monad morphism and a lax algebra in A's style** (functors into C^→), and see how much of the seam the user actually sees. If the elaborator can hide it, A's main loss is small.
2. **Try to state B's side condition.** Find a free-variable-style test on a pasting scheme that permits the coherences of CaTT minus interchange, and check whether it can be stated without orientation bookkeeping. If no clean statement exists, B is not in the CaTT aesthetic.
3. **Count dualities.** List the opposites used in the Eckmann–Hilton development (survey §2) and see which would fail under B.
4. **Formalise the Gray tensor of contexts** for an arrow times a pasting scheme (Part II §7, item 1). Both options need it, and it shows how heavy the shape machinery is.

---

# Part II. Technical material

The section numbers below continue those of the first version of these notes.

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

Option (i) is less invasive and fits the "admissible before primitive" principle. Option (ii) is more uniform and makes the user-facing syntax much nicer. A reasonable plan: **use (i) as the kernel and (ii) as the surface syntax, with (i) as the elaboration target.** This mirrors CaTT_sua over CaTT via rehydration.

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

**Conjecture (P).** For representable Θ,

```
Δ ⊳ [⟦Θ⟧, C]  ≃  (Δ ⊗ₘ Θ) ⊳ C
```

Here Δ ⊗ₘ Θ is Δ ⊗ Θ with every *mixed* generator x⊗y (dim x, dim y ≥ 1) marked invertible in the sense of ICaTT. Equivalently, ⟦Δ⟧ × ⟦Θ⟧ is the localisation of ⟦Δ ⊗ Θ⟧ at the mixed generators.

- **Evidence:** GHL Prop. 2.12 in dimension 2, and the strict pseudo-Gray story **[recall]**. It is unverified for weak ω.
- **If (P) holds,** [⟦Θ⟧, C] (pseudo) embeds in [Θ, C]ₗₐₓ as the "mixed-invertible" part. The two homs then share one rule schema, [Θ, C]_μ for a marking policy μ ∈ {lax, pseudo}:
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

This is the case Δ = D¹ of Conjecture (P), read as a rule rather than a conjecture. It says that an ambient (pseudo) 2-cell between Γ-diagrams u, v is the same as a marked Gray cylinder with ends u and v. Here it is stated in this note's notation, for any shape Δ:

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
  - Its semantic justification is the localisation statement in (P): GHL Prop. 2.12 in dimension 2, unverified for weak ω.
  - It needs ICaTT-style marking (Benjamin–Champin–Markakis), or Mikhail's ⊨ judgment, to state.
- **Density / extensionality.** The limits note defers to this thread the question of whether components plus naturality determine a transformation. For *representable* domains ⟦Θ⟧, (cyl-Λ) is exactly that principle.
  - For arbitrary domains B, the same question becomes whether the disks are jointly dense, i.e. whether a 1-cell B → [D¹, C] is determined by its restrictions along all elements Dⁿ ⊳ B.
  - In style, that would need a colimit principle presenting B from its cells (§6). It stays open here.
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
- It suggests a route to the **lax** hom too. The Gray tensor is biclosed and *non-symmetric*. An unbiased CCCaTT-style theory for it would need pasting types without duplication or exchange, i.e. a Lambek-calculus-like, planar, linear criterion. Mimram lists closed, linear and planar variants as future work.
  - This lines up with the recurring linearity theme (survey §13; Mikhail's x ∝ t).
  - The guess "lax closed structure = linear, planar pasting types" is worth testing on small cases: is the type of lax-hom evaluation pasting while the type of a diagonal is not?

**Caveats.**
- CCCaTT works *inside* one cartesian closed category, whereas §5.4 internalises the ambient ωCat's hom. To match, the pasting types must range over ambient object variables B, C : ⋆, with [B, C] a type former of the ambient. This seems direct.
- The higher-dimensional criterion, which the paper says needs dependent types, is the unknown. Until it appears, the rules of §5.1 and §5.4, with β/η as invertible cells, remain the conservative fallback.

## 6. What about ⊗ of arbitrary objects?

Architecture A never forms B ⊗ C for non-representable B and C.

- **What would be lost:** an object-level ⊗ is needed for lax-functor-category currying [B ⊗ C, D] ≃ [B, [C, D]ₗₐₓ] with *both* B and C arbitrary.
- **Why it is hard:** its mapping-out property is a Day-convolution coend, so it is not finitary. In style, it would have to come from a colimit principle (lax colimits of computads, survey §13 Q3) plus "⊗ preserves colimits in each variable".
- **Suggestion:** leave ⊗ as a context operation. Revisit once the colimits thread exists, because B ⊗ C := colim over cells of B and C of ⟦x ⊗ y⟧ is then a definition, not a rule.

---

## 7. Suggested formalisation targets

These are for the Agda thread, smallest first.

1. **Γ ⊗ D¹ for Γ a pasting scheme** (Mikhail n = 1). Implement it as a function on syntax and prove the output is a well-formed context. This is G1 in the simplest case. It is the base of everything else.
2. **G3:** Γ ⊗ (D¹ ∨ D¹) ≅ (Γ ⊗ D¹) ∨ (Γ ⊗ D¹).
3. **Vertical composition of lax transformations** as a substitution Γ ⊗ D¹ → Γ ⊗ (D¹ ∨ D¹). First check, for Γ = D¹ and D², whether plain coh provides every needed term (option (i) of §4.3). Record exactly which non-ps composites are needed. That list is the concrete case for or against molecular coh.
4. **D¹ ⊗ D¹ ⊗ D¹** (the Gray cube) under both orientations, checking G4 syntactically. This is the first place layering choices (§4.3) bite.

---
