# Pseudo ambient (P) vs Gray-style core (L)

*Design notes, 2026-11-18. Answers the decision raised in `notes/limits-representables.md` §3 (PR #2), `notes/internal-hom.md` §2–3 (PR #3) and `notes/agda-sketch-findings.md` finding 4 (PR #4). Background: `catt-survey.md` (project files). Redoing existing results is treated as free, per Anthony; only mathematical and practical upsides and downsides count.*

*Markers. **[paper]**: checked against the source this session. **[recall]**: background knowledge, not re-checked. **[conj]**: my conjecture. **[proposal]**: a design choice being put forward.*

---

## Practical gains and losses

This section answers one question: what can a user write, construct and prove under each option, and how much bookkeeping does each force? The technical comparison starts at §0.

The three options, in one line each:
- **P:** plain CaTT. The ambient's 2-cells are pseudo transformations.
- **Two-tier L:** the ambient's 2-cells are lax transformations. Inside each object, plain CaTT.
- **Uniform L:** like two-tier L, but composition is laxly interchanged inside objects too.

A "mark" below means an annotation the user writes, such as "this cell is pseudo" or "this object is an ordinary ω-category". Under it, coh treats the relevant interchange cells as invertible.

### Example 1: a lax transformation and its naturality cell

Take F, G : B → C, an element x of B (a map ⊤ → B), and an arrow f : x ⇒ y of B.

**P.** A lax transformation is not a cell. The user declares

```
α  : B → [⟦D¹⟧, C]ₗₐₓ
e₀ : ev₀ ∘ α ≅ F        e₁ : ev₁ ∘ α ≅ G          (invertible 2-cells)
```

- **Component at x.** First take (α ∘ x)♭ : ⟦D¹⟧ → C. This is an arrow of C from ev₀(αx) to ev₁(αx). It becomes an arrow F x → G x only after composing with (e₀x)⁻¹ and e₁x.
- **Naturality at f.** First take (α ∘ f)♭ : ⟦D¹ ⊗ D¹⟧ → C, a lax square. Then extract its 2-cell generator and whisker it with e₀ and e₁ at x and y.
- So every use goes through two transport isomorphisms and the Λ/♭ rule.

**Two-tier L and uniform L.**

```
α   : F ⇒ G                                   (a context variable)
α_x := α ∘ x                                  (whiskering coh)
α_f := the interchange coh of α with f        (one term; the reverse direction is rejected)
```

**Verdict:** L is one line, P is about five steps with two isomorphisms carried through. If α is a *pseudo* transformation, P is one line (α is a variable and naturality is a coh in both directions). Two-tier L is then one line plus a "pseudo" mark on α.

### Example 2: composing lax transformations

Take α : F ⇒ G and α′ : G ⇒ G′, both from B to C, and β : H ⇒ K from C to D.

**Vertical composite α′·α.**
- **P.** Four steps:
  1. Pair α and α′ into B → [D¹, C] ×_C [D¹, C]. This is a pullback map, and it needs an isomorphism ev₁α ≅ ev₀α′ built from e₁ and e₀′.
  2. Identify the result with [D¹∨D¹, C].
  3. Restrict along the composite D¹ → D¹∨D¹.
  4. Build the new endpoint isomorphisms.

  Associativity and unit laws are restrictions along coherences, followed by comparing the endpoint data.
- **L.** α′·α is a coh. Associativity and units are coh.

**Horizontal composite of α and β.**
- **P.** Compose [D¹, β] ∘ α : B → [D¹, [D¹, D]]. Curry to [D¹⊗D¹, D], then restrict along one of the two diagonal paths of the square. The interchange between the two choices is restriction along the square's 2-cell. Endpoint isomorphisms for HF and KG are built by whiskering the e's.
- **L.** Write (βG)·(Hα) or (Kα)·(βF), one coh each. The directed interchanger between them is one more coh.
  - The user must pick one of the two. Laws such as middle-four interchange then hold in one direction only.
  - If β or α is marked pseudo, the two choices become interchangeable.

**Verdict:** for lax transformations L turns a multi-step universal-property construction into single coherences, and P never lets coh see these laws. The cost of L is choosing an order for horizontal composites.

### Example 3: comma objects and lax slices

- **All three options.** f ↓ g, the lax slice C//c, and other lax or partially lax limits are the same cone context (Mikhail's rules plus markings). Constructing them, and their 1-dimensional universal property, look the same.
- **Where they differ: the 2-dimensional universal property.**
  - Under P, the cells of Hom(X, f ↓ g) are built from pseudo transformations. The question "what does a *lax* transformation into C//c correspond to?" can be asked only through [D¹, –]ₗₐₓ again.
  - Under L it is a direct statement about native cells.

**Verdict:** for building limits, a wash. L only matters once lax transformations are mapped into them.

### Example 4: adjunctions and monads between ω-categories

The standard notions (adjunction L ⊣ R : A ⇄ B, monad T on C) use pseudo transformations for η, ε, μ.

- **P.** Written exactly as in CaTT, with no annotations. Triangle laws and higher coherences (the swallowtail; associativity of μ at arity 4, which uses μ ⋆ μ) are cohs, and horizontal composites like μ ⋆ μ are canonical.
- **L, unmarked.** η, ε and μ are lax, so the user gets a weaker notion: a "lax adjunction" or "lax-natural monad". All of its theorems also hold for real adjunctions and monads. But some standard theorems need invertible naturality and fail for it, for example the hom-isomorphism Hom(Lx, y) ≅ Hom(x, Ry) being natural in both variables. The higher coherences involve μ ⋆ μ and η ⋆ ε, which have two non-equivalent layerings, so the user must write them in a specific orientation.
- **L, with "pseudo" marks on η, ε, μ.** Behaves like P. The cost is one mark per structure cell, plus a marking-propagation rule that makes every interchanger involving them invertible.
- **Gained by L:** monads and adjunctions whose structure cells are genuinely lax become statable directly. These are rare in practice.

**Verdict:** P wins on the standard notions. L matches it only with marks. L's advantage here is narrow.

### Example 5: a group or ring (ordinary math)

- **Group.** Present BG as an object from a computad with invertible marks, e.g. BZ from (x, s : x → x) with s invertible. Reasoning about elements of BG (composing, inverting, proving equations) happens *inside one object*.
  - P and two-tier L: identical, plain CaTT.
  - Uniform L: horizontal composites inside BG are directed. Every cell of BG is invertible, so with a propagation rule ("an interchanger with an invertible factor is invertible" **[conj]**) nothing changes. Without that rule the user marks BG ordinary.
- **Ring.** R with + and · : R × R → R (products are finite limits) and equation witnesses: invertible 2-cells between maps R³ → R.
  - P: those witnesses must be marked invertible anyway, since ambient 2-cells are directed in P too.
  - Two-tier L: the same marks suffice, given the propagation rule.
  - Neither option proves R discrete; that needs an h-level discipline in all three.

**Verdict:** P and two-tier L cost the same. Uniform L costs nothing extra *if* invertibility propagates automatically, and one mark per object otherwise.

### Example 6: structure inside an object (where uniform L differs)

A monoidal category M as a one-object 2-category BM: f ⊗ g is the horizontal composite of two 2-cells.

- **P and two-tier L.** f ⊗ g is a canonical coh, and Eckmann–Hilton and the braiding argument go through as in CaTT.
- **Uniform L, unmarked.** f ⊗ g has two layerings, (f⊗1)(1⊗g) and (1⊗g)(f⊗1), connected by a directed cell. So BM is a monoidal structure whose ⊗ is only laxly functorial. Ordinary monoidal reasoning needs "BM is ordinary".
- **Gained by uniform L:** objects whose own composition interchanges only laxly are first class. Examples are monoidal-like structures with a non-invertible interchanger, and ωCat_lax itself (or a lax universe) as an object. P and two-tier L can describe such things only through maps out of Gray tensors.

### What none of the three gives

**Lax functors**, meaning maps preserving composition only up to a directed cell. In all three options functors preserve composition up to invertible cells. Lax functors would need yet another rule (e.g. Gray-shaped "lax functor" contexts) in any of them.

### Gains and losses, side by side

| | **P** | **Two-tier L** | **Uniform L** |
|---|---|---|---|
| Lax transformations | 1-cells into [⟦D¹⟧, C]ₗₐₓ plus two endpoint isomorphisms. Every component and naturality cell is unpacked by hand. | context variables; components and naturality are cohs | same as two-tier |
| Composing lax transformations | universal-map constructions (pullback pairing, currying, restriction); laws not checked by coh | cohs; pick an order for horizontal composites | same |
| Standard notions (adjunction, monad, equivalence) | exactly as in CaTT | one "pseudo" mark per structure cell, or you get the weaker lax notion | same |
| Reasoning inside an object (elements, groups, rings) | plain CaTT | plain CaTT | plain CaTT after an "ordinary" mark or automatic propagation; otherwise directed |
| Objects with lax internal composition | not expressible as objects | not expressible as objects | expressible |
| Bookkeeping falls on | lax work (heavy) | pseudo work (one mark each) + layering choices | pseudo work + ordinary objects (one mark each) |

### The practical trade-off

- P is cheapest when most transformations are pseudo, which is the case in standard (∞,n)-category theory and ordinary math. It is clumsy wherever lax transformations are the point: lax naturality, lax colimits and Grothendieck constructions, (op)lax twists, lax slices.
- L reverses this. It moves the annotation cost from lax work to pseudo work.
- **Surface defaults are a lever.** The kernel can be uniform L while the surface syntax assumes "objects are ordinary, transformations are pseudo, unless declared lax". The user then writes P-style code for standard work and opts into laxness where it matters. The kernel cost is the marking and propagation machinery, which P also needs for marked limits.

---

## 0. Summary

1. **The target is not an ω-category.** The ω-category of ω-categories with lax transformations is a category *enriched over ωCat with the lax Gray tensor*, which Gepner–Heine call an **oriented category** ([2510.10504](https://arxiv.org/abs/2510.10504), §1.8, with ∞Cat's hom-objects being Fun^lax(S, T)) **[paper, intro level]**. A CaTT model is enriched over the *cartesian* product. So under P the ambient is a different object (ωCat with pseudo transformations), and the lax one appears only as a family of objects and maps inside it.
2. **Two versions of L.** In ωCat_lax only the outermost composition is Gray, since each hom Fun^lax(B, C) is an ordinary ω-category.
   - **Two-tier L** matches that exactly: plain CaTT inside homs, directed interchange only for composition across objects.
   - **Uniform L** makes interchange directed at every level. Its rule is the same algorithm applied recursively (§2.5).
   - Uniform L is weaker than two-tier L, which is weaker than P. Each stronger theory is the weaker one plus an invertibility marking, so every model of the stronger theory is a model of the weaker one, ωCat_lax included **[conj]**.
   - *Revised 2026-11-18 after Anthony clarified that "lax by default" means "the most general version until there is a concrete reason otherwise". The first version recommended two-tier L.*
3. **The L rule is a small syntactic change.** Contexts stay pasting schemes, and the coh rule keeps its shape. What changes is the side condition: free-variable sets are replaced by **supports in the Gray unfolding** of the pasting scheme. For Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, that unfolding is the hom-level shape Θₙ ⊗ … ⊗ Θ₁. Supports are Steiner chains, so the check is integer linear algebra and decidable (§3).
4. **L absorbs the hardest open item of P.** Under P, lax homs [Θ, C]ₗₐₓ need a Gray *context former* whose generators x⊗y must be typed by composites of non-pasting molecules. PR #3 calls this "the biggest open technical point" (G1). Under L, a lax square in C is just the interchanger of a native 2-cell with an arrow of C, so lax homs are the native hom made into an object and Gray contexts become derivable (§4.2).
5. **L is the weaker theory, and P is recoverable from it.** Every cartesian-enriched model is also Gray-enriched, through the comparison map X ⊗ Y → X × Y. So **P ≈ L + "interchangers are invertible"** **[conj]**. "Pseudo = lax + marking", which PR #3 adopted for shapes, then holds for the ambient as well. Choosing L does not close off P; the reverse is false.
6. **L's real costs.**
   - The horizontal composite of 2-cells across objects no longer exists canonically. Users choose an order, and the laws carry directed interchangers.
   - Ordinary-math reasoning in low dimensions may meet interchangers that are semantically invertible but not syntactically so.
   - The metatheory (computads, models, invertibility, substitution) must be built for the new side condition.
   - Under two-tier L, a future universe object would be pseudo, not lax, so it would not match the ambient (§4.7). Uniform L removes this mismatch.

   None of these makes L ill-defined.
7. **Is there an unambiguous path?**
   - **P:** unambiguous to build, but it is the least general option.
   - **Two-tier L:** a target in the literature (oriented categories; the strict model of Ara–Maltsiniotis), a pinned-down rule change, and a finite list of lemmas.
   - **Uniform L:** the syntax is just as well defined, as the recursive Gray unfolding. What is missing is an established *semantics* of its own: iterated Gray enrichment fails as a construction (Crans; Bourke–Lobbia). That is a risk for the soundness proofs, not a reason the theory is wrong. Its intended models, ωCat_lax among them, are still models.

**Recommendation (revised): uniform L as the kernel**, with "ordinary ω-category" (interchange invertible inside an object) and "pseudo" as markings (§2.5, §7). Two-tier L is its first milestone, since the two differ only in whether the unfolding recurses. Both two-tier L and P remain reachable by marking.

---

## 1. What the question is

Three threads found the same obstruction. CaTT's coherence side condition admits the interchange cell in both directions, so in any CaTT model the naturality cell of a 2-cell at a 1-cell is invertible (Benjamin–Markakis, all coherences are invertible, [2406.12127](https://arxiv.org/abs/2406.12127)). Lax transformations do not have this property.

- **P:** keep CaTT. The ambient's 2-cells are pseudo transformations. Lax ones come from lax function objects [⟦D¹⟧, C]ₗₐₓ, built from Gray-tensored contexts.
- **L:** change the coherence rule so interchange across objects is directed. The ambient's 2-cells are lax transformations.

The comparison should be about which *mathematical object* each theory is the internal language of, and what working in it is like.

---

## 2. Structural facts that decide most of the comparison

### 2.1 ωCat with lax transformations is Gray-enriched

- **Strict.** Strict ω-Cat with the Ara–Maltsiniotis Gray tensor is monoidal biclosed, with Hom(A ⊗ B, C) ≅ Hom(A, Fun_oplax(B, C)) ≅ Hom(B, Fun_lax(A, C)) up to naming conventions ([1607.00668](https://arxiv.org/abs/1607.00668)) **[recall]**. So strict ω-Cat is a category enriched over (ω-Cat, ⊗).
- **(∞,ω).** Campion constructs a unique monoidal biclosed Gray structure on Cat_n for n ∈ ℕ ∪ {ω} (Theorem A of [2311.00205](https://arxiv.org/abs/2311.00205)) **[paper, abstract/intro]**. A closed presentably monoidal ∞-category is enriched over itself (Gepner–Haugseng) **[recall]**. So Cat_ω is Gray-enriched, with hom-objects Fun^lax(A, B).
- **Named notion.** Gepner–Heine, *Oriented category theory* ([2510.10504](https://arxiv.org/abs/2510.10504)), define oriented categories as categories enriched in ∞Cat for the lax Gray tensor. Their compositions "only commute up to a coherent (anti)oriented interchange law". They state that ∞Cat viewed as an oriented category has hom-objects Fun^lax(S, T) **[paper, intro level]**. Their companion paper on oriented colimits is the one PR #2 already cites ([2608.02592](https://arxiv.org/abs/2608.02592)).

So **L's semantic target is an established notion. P's ambient is the cartesian (∞,ω)-category Cat_ω, which is a different object.**

### 2.2 Only composition across objects is Gray

In a Gray-enriched 𝒦:

- For objects a, b, the hom 𝒦(a, b) is an ordinary ω-category. All its internal compositions, which are 𝒦's compositions in dimension ≥ 1, interchange invertibly as usual.
- Composition across objects is 𝒦(b, c) ⊗ 𝒦(a, b) → 𝒦(a, c). On generators it sends a pair (y, x) of cells of dimensions m and k (in the homs) to a cell of dimension m + k. So:
  - an object x (k = 0) whiskers: y ⊗ x has the dimension of y;
  - two 1-cells of homs (2-cells of 𝒦, i.e. transformations α, β) give a **2-cell of the hom, i.e. a 3-cell of 𝒦: the interchanger**, between the two whiskered composites. There is no horizontal composite in dimension 2.

This is the precise content of "lax by default" for ωCat. Inside an object C, cells are an ω-category, and CaTT reasoning in C is plain CaTT. Lax transformations compose vertically by the ordinary laws of Fun^lax(B, C). Directedness lives only where transformations are composed across different objects.

### 2.3 "Directed interchange at every level" is not a settled target

One could try a theory in which *every* pair of compositions interchanges directedly, i.e. Gray structure at every level. The evidence says this is not a well-understood structure:

- Crans showed that no monoidal biclosed structure on Gray-categories captures weak transformations. Bourke–Lobbia ([2212.12358](https://arxiv.org/abs/2212.12358)) recall this and work around it with *skew* monoidal closed structures, one for lax and one for pseudo transformations **[paper, abstract/intro]**. A related obstruction is Bourke–Gurski, *A cocategorical obstruction to tensor products of Gray-categories* **[recall]**.
- Gepner–Heine introduce *bioriented* categories, related to suspension. This is the frontier, not a foundation one can build a kernel against yet **[paper, intro level]**.
- The objects of ωCat are ordinary ω-categories anyway. A uniformly directed theory would describe something *other* than ωCat_lax.

*First-version conclusion, superseded by §2.5:* "L should mean two-tier L." That conclusion assumed the target was ωCat_lax exactly. Under the generality principle it does not hold, and §2.5 replaces it.

### 2.4 Every P-model is an L-model

There is a canonical comparison X ⊗ Y → X × Y, which collapses the mixed generators. It makes the identity a lax monoidal functor (ωCat, ×) → (ωCat, ⊗), and change of base along it turns a cartesian-enriched ω-category into a Gray-enriched one whose interchangers are invertible **[recall for the comparison map; the change of base is standard]**.

Consequences:

- Everything L proves holds in every CaTT model. **L is a weaker theory with more models**, including both ωCat_lax and ωCat_pseudo.
- **[conj]** L plus a rule "every interchanger is invertible" is equivalent to P, in the sense of having the same models, with a conservative translation of P-terms. Horizontal composites become definable by a chosen layering, and the two layerings are related by an invertible cell.
- PR #3's principle "pseudo = lax + marking" (Conjecture P, GHL Prop. 2.12) becomes uniform. It applies to the ambient's own cells, not only to shapes.

### 2.5 Uniform L, and where generality stops

**The rule.** Recurse the Gray unfolding of §3.1 into the hom pieces:

```
U(ΣΘ₁ ∨ … ∨ ΣΘₙ)  :=  U(Θₙ) ⊗ … ⊗ U(Θ₁)          U(point) := point
```

Two-tier L is the case where U(Θᵢ) is replaced by Θᵢ itself.

- Tensors and suspensions of loop-free Steiner complexes are loop-free **[recall]**, so supports are computed exactly as in §3.2 and the check stays decidable.
- The rule (§3.3) is unchanged. Only U changes.

**What it does.**
- Example: inside a single object C, take two 2-cells composable along a 1-cell, i.e. Γ = Σ(D¹ ∨ D¹) in C's own cells. This now gets a directed interchanger one dimension up, just as transformations do in two-tier L.
- So Eckmann–Hilton, horizontal composites and the like are directed everywhere, unless marked.

**Generality ordering [conj].** Uniform L ⊂ two-tier L ⊂ P, in the sense that each is the previous one plus invertibility markings:
- "interchange inside this hom is invertible" gives two-tier;
- "every interchanger is invertible" gives P.

Finer supports map onto coarser ones under the collapse X ⊗ Y → X × Y, so every pair of terms the finer rule accepts, the coarser rule accepts too. Hence every model of the stronger theory is a model of the weaker one, including ωCat_lax and every ordinary ω-category.

**What uniform L gains over two-tier L.**
- Objects need not be ordinary ω-categories. The theory also covers objects whose own compositions interchange directedly, such as Gepner–Heine's oriented categories, which are not ω-categories.
- The ambient and its objects are the same *kind* of structure again. This removes the universe mismatch of §4.7: a universe object can be lax.
- One rule at every level, with no special status for dimension 0. That is closer to the CaTT aesthetic than two-tier L.

**Concrete reasons it could fail (none decisive now).**
1. **No established semantics of its own.** The obvious construction, iterated Gray enrichment, breaks at dimension 4: there is no monoidal biclosed structure on Gray-categories for weak transformations (Crans; Bourke–Lobbia). Gepner–Heine's bioriented categories are the closest current work. This makes S1 (§3.6) harder to *prove*, because there is no ∞-categorical model class to check against. It does not make the theory inconsistent, since its intended models are models.
2. **Usability, unless markings are cheap.** Plain CaTT reasoning inside an object (elements, the post's §Functors) now has directed interchange. The fix is a marking "C is an ordinary ω-category" that restores invertible interchange in C. The marking must be easy enough that ordinary use never notices it.
3. **Cost.** Unfoldings now multiply at every level, not only across objects. Symbolic supports should keep this polynomial **[conj]**, but it is a real constant-factor cost.

**Where generality stops.** One step further is to drop the interchanger entirely (an ω-sesquicategory, the setting of Markakis's generalised signatures **[recall]**). That gives up the *existence* of naturality cells, which every lax transformation has. So there is a concrete reason to stop at directed interchange: it is the most general option that still contains the intended structure.

---

## 3. What the Gray-style coh rule looks like (two-tier L)

### 3.1 Contexts: unchanged

Pasting schemes as in Finster–Mimram. Every pasting scheme decomposes uniquely as a wedge of suspensions

```
Γ  =  ΣΘ₁ ∨ ΣΘ₂ ∨ … ∨ ΣΘₙ          (n ≥ 0; objects a₀, …, aₙ)
```

Here Θᵢ is the pasting scheme of cells in the hom from aᵢ₋₁ to aᵢ.

**Gray unfolding.** Define the hom-level shapes

```
U_{ij}(Γ)  :=  Θⱼ ⊗ … ⊗ Θᵢ₊₁          (i < j)
```

These are tensors of Steiner complexes, computed generator-wise, with generators θⱼ ⊗ … ⊗ θᵢ₊₁, dimension the sum, and boundary given by the Leibniz formula. Mikhail's `gray` judgment and PR #3 §4.1 give the same formula. Steiner complexes of pasting schemes are loop-free, and tensors of loop-free complexes are loop-free (Steiner) **[recall]**. So the free strict ω-category on U_{ij} is well behaved and cells of it are determined by their chains.

The **order of factors** (Θⱼ ⊗ … ⊗ Θᵢ₊₁ vs. the reverse) is the lax/oplax convention. It must be fixed once, as PR #3 §4.1 already notes.

### 3.2 Supports

For a term t : A in context Γ with endpoints aᵢ, aⱼ (dimension ≥ 1), define **supp(t : A)** as the graded set of generators of U_{ij}(Γ) that appear in the image of t and its iterated boundaries under the *strict* interpretation. That is, interpret t in the free strict Gray-enriched ω-category on Γ, which is computable through Steiner chains. For objects and terms of dimension 0 the support is just the variable.

**[proposal]** Read side conditions off the strict model. This is how the free-variable sets of CaTT behave too:

- **[conj]** On a single hom (n = 1), supp coincides with Finster–Mimram's Var. The intuition is that the free strict ω-category on a pasting scheme has no cancellation, so a variable used by a term stays in the support of its strict image.
- This is the same "linearity / no cancellation" principle that the survey (§13) identifies as recurring.

### 3.3 The rule

```
Γ ⊢ps     Γ ⊢ t :A    Γ ⊢ u :A      Δ ⊢ σ : Γ        (t, u with endpoints aᵢ, aⱼ)

(operation)  supp(t:A) = ∂⁻U_{ij}(Γ)   and   supp(u:A) = ∂⁺U_{ij}(Γ)
(coherence)  supp(t:A) = U_{ij}(Γ) = supp(u:A)
──────────────────────────────────────────────────────────────────────
Δ ⊢ coh_{Γ, t →_A u}[σ] : (t →_A u)[σ]
```

- ∂^± are taken in the molecule U_{ij} at dimension dim U_{ij} − 1, with all lower boundaries.
- Composites and coherences relate the endpoints a₀ and aₙ, so in practice (i, j) = (0, n). The general indexing is for sub-terms.
- **The dimension changes.** The operation case over Γ produces a cell of 𝒦-dimension 1 + Σᵢ dim Θᵢ, not dim Γ.

### 3.4 Worked cases

**Whiskering.** Take Γ = ΣD⁰ ∨ ΣD¹, a 1-cell f followed by a 2-cell β : g ⇒ g′. Then U = D¹ ⊗ D⁰ ≅ D¹, and the operation case gives βf. This is the same as in CaTT.

**Horizontal composite: gone.** Take Γ = ΣD¹ ∨ ΣD¹, with α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z.

- U = D¹_β ⊗ D¹_α is the lax square in 𝒦(x, z). It has four vertices gf, gf′, g′f, g′f′, four edges, and one 2-dimensional generator β⊗α.
- No term of 𝒦-dimension 2 has full support, so there is **no coherence-case or operation-case horizontal composite**. The two whiskered composites (βf′)·(gα) and (g′α)·(βf) are both well typed, through ordinary whiskering and vertical cohs, but they are not identified.

**The interchanger: one direction only.** In the same Γ, the Leibniz formula gives

```
∂⁻(β⊗α) = (g⊗α) ∪ (β⊗f′)      i.e.   (βf′)·(gα)
∂⁺(β⊗α) = (g′⊗α) ∪ (β⊗f)      i.e.   (g′α)·(βf)
```

These are in diagrammatic order, with one choice of convention.

- So coh_{Γ, (βf′)·(gα) → (g′α)·(βf)} is an operation-case 3-cell.
- The reverse fails, because the support of its source is ∂⁺U, not ∂⁻U.
- This is exactly the lax naturality cell of β at the component of α.

**The Gray cube.** Take Γ = ΣD¹ ∨ ΣD¹ ∨ ΣD¹. Then U is the 3-cube, and its top generator is a 4-cell of 𝒦 between the two hexagonal composites of interchangers.

- Each hexagon is a vertical composite of whiskered interchangers. Each interchanger is a coh over a two-factor sub-wedge, substituted. So **the source and target are ordinary terms over pasting schemes.**
- No coh over a non-pasting context is needed. The Gray molecules appear only in the side-condition computation.
- This corrects PR #3 §4.3's expectation that a Gray core forces "molecular coh" into the kernel.

**Inside a hom.** Take Γ = ΣΘ. Then U = Θ, and by the [conj] of §3.2 the rule is plain CaTT. Suspension maps L-terms to L-terms, since the image lands in the cartesian tier.

### 3.5 Which cells are invertible

| Cell | Invertible? | Why |
|---|---|---|
| Coherence case (supp t = supp u = U) | yes | The reversed coh satisfies the same condition; Benjamin–Markakis's argument goes through unchanged. |
| Anything inside a single hom | as in CaTT | §3.4, last case |
| Composites (operation case, n = 1) | no, as in CaTT | |
| Interchangers y ⊗ x with dim x, dim y ≥ 1 | **no** | The source and target supports are different halves of ∂U. |
| Interchanger where one factor is invertible | yes **[conj]** | For 2-categories, a lax transformation's naturality cell at an equivalence is invertible **[recall]**. Needs an ICaTT-style invertibility judgment ([2602.16602](https://arxiv.org/abs/2602.16602)) with a propagation rule. |
| Interchangers with a transformation marked *pseudo* | yes, by marking | A pseudo transformation is a 2-cell whose interchangers are all marked invertible. |

### 3.6 Soundness: what has to be proved

- **S1. Coherence case.** In the free Gray-enriched weak ω-category on Γ, any two parallel cells of full support are connected by an invertible coherence. Evidence:
  - in the strict model this holds on the nose (Steiner: cells of a free strict ω-category on a loop-free basis are determined by their chains);
  - Campion's pasting theorem ([2311.00200](https://arxiv.org/abs/2311.00200)) gives contractible spaces of composites for torsion-free complexes, which include Gray cubes **[paper, abstract]**.

  This is **[conj]** for weak ω, and it is the central lemma.
- **S2. Freeness.** The hom 𝒦(a₀, aₙ) of the free Gray-enriched category on Γ is Free(Θₙ) ⊗ … ⊗ Free(Θ₁) ≃ Free(Θₙ ⊗ … ⊗ Θ₁). This holds in the strict case (Ara–Maltsiniotis; Steiner) **[recall]**, and for (∞,ω) via Campion's generator-wise construction **[conj]**.
- **S3. Substitution.** Supports must be computed for substituted terms. A substitution induces a chain map between Gray unfoldings, which is tensor-functorial. This is the L analogue of the substitution-admissibility metatheorem, which PR #4 lists as open for plain CaTT too.

---

## 4. How each option handles the main constructions

### 4.1 Lax and pseudo transformations

| | P | L |
|---|---|---|
| Lax transformation F ⇒ G : B → C | a 1-cell B → [⟦D¹⟧, C]ₗₐₓ over (F, G): an element of a pullback (PR #2 §6.3, PR #3 §5.2) | a native 2-cell |
| Pseudo transformation | a native 2-cell | a native 2-cell with marked (invertible) interchangers |
| Naturality "via coherence" (the post's §Functors) | pseudo naturality | **lax naturality** (§3.4) |
| Composing transformations across objects | maps [C,D]ₗₐₓ ⊗ [B,C]ₗₐₓ → [B,D]ₗₐₓ out of a Gray tensor of objects, or curried. The coherence laws come from universal-property (uni) rules, not from coh. | coh |
| Vertical composition | coh in [⟦D¹⟧, C]ₗₐₓ restricted along cohs (PR #3 §5.3) | coh |

**Why P cannot use the cartesian product here.** A map [C,D]ₗₐₓ × [B,C]ₗₐₓ → [B,D]ₗₐₓ would force (β,1)∘(1,α) = (1,α)∘(β,1) to map to isomorphic composites, i.e. an invertible interchanger. So under P the composition of lax transformations needs the Gray tensor *of objects*, or its curried form. Either way it is a new rule family whose coherences do not come from coh.

### 4.2 Gray shapes and lax homs

- **P.** [Θ, C]ₗₐₓ needs Γ ⊗ Δ as a *context former* (PR #3 §4–5.1). Its generators x⊗y must be typed by composites of molecules such as hexagons, and those composites must have syntactically matching boundaries (condition G1). Two routes are proposed:
  - layering with associator bookkeeping, which pushes CaTT_sua early;
  - molecular coh justified by Campion.

  Both are open.
- **L.** A lax square in C is the interchanger of a native 2-cell α : u ⇒ v (with u, v : ⟦D¹⟧ → C) with the generic arrow of ⟦D¹⟧, read in 𝒦(⊤, C) ≃ C. More generally, **[conj]** Δ ⊗ Θ-shaped diagrams in C are Δ-shaped families of cells of the native hom 𝒦(⟦Θ⟧, C).
  - So [⟦Θ⟧, C]ₗₐₓ is the native hom made into an object, by the same Σ ⊣ Hom-style rule PR #3 §5.4 proposes for P's pseudo hom.
  - Gray contexts become *derived* notation, and G1 disappears.
  - The Gray tensor still appears, but only as an algorithm on chain complexes inside the side condition, which is standard Steiner theory.

This is the largest concrete simplification L offers. It is also the place where the earlier threads underestimated L.

### 4.3 Internal homs

| | P | L |
|---|---|---|
| Native hom made an object | [B, C]: pseudo (PR #3 §5.4) | [B, C]: lax, by the same rule |
| Currying | Hom(A, [B,C]) ≅ Hom(A × B, C), using × from finite limits: all finitary | Hom(A, [B,C]) ≅ Hom(A ⊗ B, C). Needs a Gray tensor of *objects* A ⊗ B, given by a mapping-out rule (adjunction-style β/η). This is finitary as a rule, but it is a new object former. |
| The other hom | [B, C]ₗₐₓ for all B needs Gray tensors of objects as well (§4.1) | [B, C]_pseudo = the sub-hom with marked naturality. Cartesian currying via × from limits. |

So each option makes one hom native and gets the other from an extra rule family. The difference is which one CaTT's coh handles for free.

### 4.4 Limits (CaTT_lim)

- **P.** Mikhail's rules apply as published ([2412.13310](https://arxiv.org/abs/2412.13310)). Lax cones have non-invertible ambient 2-cells p_f, so they are lax limits in ωCat_pseudo. Transfors between cones are Gray-shaped *contexts* (`ctrf`), whose existence is proved only for n = 1.
- **L.** The cone *shapes* are the same: a cone over Γ is the same context. The universal property becomes a Gray-enriched one, quantifying over native lax cells.
  - **[conj]** The `ctrf` shapes (transfors between cones) become native cells of the hom 𝒦(c, ·), so the `ctrf`/`star` machinery may shrink. A cone transfor would be a native cell between cones, with interchangers supplying the Gray squares.
  - Gray-enriched weighted limits are standard in dimension 2 (Street; Lack) **[recall]**.
  - Gepner–Heine's oriented colimits are the matching (∞,ω) notion. PR #2 §2.4 already suspects CaTT_lim's limits are "oriented" in their sense. Under L that becomes the expected reading rather than a mismatch.
- **Markings** (PR #2 §4.2) are needed by both.

### 4.5 Free objects and representables

- **Both.** PR #1's construction (initial object plus one-generator cell attachment) and PR #2's R-B (⟦Γ⟧ := lax colimit of const ⊤) are colimits and work in either ambient.
- **What changes is what Hom(⟦Γ⟧, C) means.**
  - Under P it is pseudo transformations of Γ-diagrams.
  - Under L it is lax ones, which matches Johnson-Freyd–Scheimbauer's lax transformations between diagrams and the "lax by default" decision.
- **Elements** (PR #2 §5.1, PR #4 finding 3): 𝒦(⊤, C) ≃ C holds in both, since 1 ⊗ X ≅ X ≅ 1 × X. Under L, the functor action is whiskering as before, but **the naturality square of α at an element arrow f is a directed interchanger**. The post's elementwise style then yields lax naturality, which is what Anthony's 2026-11-17 answers asked for.

### 4.6 The ω-category of ω-categories itself

- **P.** The ambient is Cat_ω with pseudo transformations, a (large) ω-category, cartesian closed.
  - Lax data is present as objects [B, C]ₗₐₓ and maps between them.
  - The Gray-enriched structure of ωCat_lax is *constructed*: composition maps out of Gray tensors of objects, plus their coherences via uni-style rules.
  - **Users who want to reason in ωCat_lax do so through universal maps, not through coh.**
- **L.** The ambient *is* ωCat_lax, an oriented category. Its compositions and their coherences are CaTT-style cohs. ωCat_pseudo is the marked sub-structure.

### 4.7 Universes (not on the current plan, but they affect the long term)

- **P.** A universe U : ⋆ of small ω-categories is an ω-category whose cells are functors and pseudo transformations. That is the same *kind* as the ambient, so "ωCat : ωCat" is at least kind-correct (modulo size).
- **L.** Objects are ω-categories, but ωCat_lax is an oriented category, not an ω-category. So a universe *object* can only be the pseudo one.
  - Elementwise reasoning inside U would give pseudo naturality while the ambient gives lax: a mismatch.
  - A lax universe would need objects that are themselves oriented categories. That is the uniform/bioriented frontier of §2.3.

PR #1 recommends no universe for now, so this is a long-term cost of two-tier L, not a near-term one. **Uniform L removes it** (§2.5), because its objects may be oriented categories themselves.

---

## 5. Decidability, cost, usability

### 5.1 Decidability

- **P.** Plain CaTT is decidable: the pasting-scheme check is linear and the Var checks are set computations. The CaTT_lim side conditions are syntactic too.
- **L.** Still decidable.
  - Supports are computed in the strict Gray model through Steiner chains, i.e. integer linear algebra.
  - Gray unfoldings of pasting schemes are generated, never recognised, so no molecule recognition is needed.
  - The rule never asks for coh over a molecule (§3.4).

### 5.2 Cost

- U for a row of n horizontally composable 2-cells is the n-cube, with 3ⁿ cells. Computed naively, supports blow up exponentially in the *horizontal width* of a pasting scheme.
- Computed symbolically, as sums of tensors of chains touching only the cells a term uses, the cost should be polynomial in term size **[conj]**.
- In practice horizontal width is small. Plain CaTT has no such cost.

### 5.3 Usability

- **L: no canonical horizontal composite.** A user composing transformations across objects must pick a whiskering order. Laws relating the two orders are directed interchangers, the bookkeeping familiar from Gray categories.
  - This is intrinsic to lax transformations: P's users meet it too, the moment they use lax transformations, and there coh does not help them.
  - L's users meet it even for pseudo transformations, unless they mark them.
  - Mitigation: surface syntax with a default layering, plus automatic invertibility propagation from markings.
- **L: interchangers in low-dimensional math.** For "ordinary math" objects (1-category-like, groupoid-like), interchangers are *semantically* invertible, but L only knows that from markings. A property like "C has only invertible 2-cells" would need to propagate to interchangers with cells into C. Neither option has such a property-propagation rule yet. Under P the question never arises.
- **P: two kinds of cell for one concept.** P's users handle lax transformations as 1-cells into [⟦D¹⟧, C]ₗₐₓ, a different kind of thing from the ambient's 2-cells. Laws for them come from universal properties, and coh does not apply to the outer level. This is a large ergonomic cost if lax transformations are common, and "lax by default" says they are.

### 5.4 Metatheory and semantics

| | P | L |
|---|---|---|
| Models | GM/BFM weak ω-categories; computads (Dean–Finster–Markakis–Reutter–Vicary); Benjamin–Markakis–Sarti contexts-as-computads | to build: "Gray-coherator" models. Target notion exists (Gepner–Heine). Markakis's generalised signatures may cover the computads **[recall]**. |
| Strict test model | strict ω-Cat with the cartesian hom (strictly natural transformations) | strict ω-Cat with the AM Gray tensor. This model is exactly the one used to compute supports, so the side condition and the test model coincide. |
| Is ωCat itself a model? | open (algebraic weak ω-cats vs (∞,ω)) | open, same gap |
| Invertibility, Σ, opposites, naturality meta-operations | done | to redo. Σ is admissible (§3.4). Opposites swap tensor order via (X⊗Y)^op ≅ Y^op ⊗ X^op (Chanavat) **[paper per PR #3]**. The naturality meta-operation (BMOSV) becomes the interchange coh. |
| Biggest open lemma | G1 for Gray contexts (PR #3 §4.3); Conj. (P) "pseudo = marked Gray" for weak ω | S1 (coherence case over Gray unfoldings, §3.6) |

---

## 6. Side-by-side

| | **P: pseudo ambient** | **L: two-tier Gray-CaTT** | **L: uniform** |
|---|---|---|---|
| Internal language of | Cat_ω with pseudo transformations | ωCat_lax, an oriented category (Gepner–Heine) | structures with directed interchange at every level; ωCat_lax is one model |
| Core rule | CaTT, unchanged | CaTT syntax; side conditions on Gray supports | same, with the unfolding applied recursively |
| Lax transformations | constructed (cotensor + pullback) | native | native |
| Pseudo transformations | native | lax + marking | lax + marking |
| Inside one object | plain CaTT | plain CaTT | directed, unless C is marked as an ordinary ω-category |
| Generality | strongest theory | P + nothing; P = it + marking **[conj]** | weakest; both others = it + marking **[conj]** |
| Gray tensor of contexts | primitive context former (G1 open) | algorithm inside the side condition. Gray diagrams are derived **[conj]**. | same |
| Coherence of lax composition | via universal-property rules | via coh | via coh |
| Horizontal composite | canonical | chosen across objects; laws are directed | chosen everywhere unless marked |
| Internal hom with cartesian currying | yes (pseudo) | yes for the marked pseudo hom | yes for the marked pseudo hom |
| Internal hom, lax | needs Gray tensor of objects | native; currying needs Gray tensor of objects | same |
| Limits | CaTT_lim as published | CaTT_lim re-read Gray-enriched; ctrf may simplify **[conj]** | same |
| Free objects, elements | yes | yes; naturality comes out lax | yes |
| Future universe | kind-correct (pseudo) | pseudo only (mismatch) | kind-correct (lax) |
| Established semantics | (∞,ω)-categories | oriented categories | none of its own yet; frontier (bioriented) |
| Decidable | yes | yes; cost grows with horizontal width | yes; cost grows at every level |
| Central open lemma | G1 + Conj. (P) | S1 | S1, without a model class to check against |

---

## 7. Recommendation

**Revised recommendation: uniform L as the kernel**, with two markings:
- "C is an ordinary ω-category": interchange inside C is invertible;
- "this transformation is pseudo".

Two-tier L and P are then fragments obtained by marking. The working rule is "steer toward the most general version until there is a concrete reason otherwise", and §2.5 found no decisive reason against uniform L. The one reason found against going further, dropping interchangers altogether, is concrete: it loses naturality cells that every lax transformation has.

**Order of work: two-tier first.** Two-tier L is the *first milestone* toward uniform L, not a competing choice:
- it has a model class in the literature to check S1 against;
- the only change from two-tier to uniform is letting the unfolding recurse (§2.5).

If the recursive version hits a concrete problem, such as S1 failing for an unfolding inside a hom or marking overhead that makes ordinary CaTT reasoning unusable, that is the concrete reason to stop at two-tier.

The reasons for L over P (first version, still valid):

1. **It is the internal language of the stated target.** "Internal language for the ω-category of ω-categories" with lax transformations names an oriented category, not an ω-category. Under P the target is a derived structure whose coherences coh never sees. With redoing results set aside as a cost, P's remaining advantage is mostly that it works in a different, easier ambient.
2. **It removes P's hardest open item rather than adding one.** P needs Gray contexts as a primitive, with G1 open. L gets lax squares, cubes and lax homs from native interchangers, and keeps the Gray tensor as a chain-complex computation in the side condition.
3. **It is weaker and more general.** Every CaTT model is an L-model, and P is (conjecturally) L plus one marking. So L does not foreclose anything P offers. Choosing P forecloses the lax ambient.
4. **The target and the test are concrete.**
   - The semantics is Gray-enriched (∞,ω)-categories (Campion's monoidal structure; Gepner–Heine's oriented categories).
   - The strict AM model is exactly what the side condition computes in, so every rule can be tested mechanically against it.

*The first version advised against uniform L because "it describes something other than ωCat_lax". Under the generality principle that is not a reason: ωCat_lax remains a model. The dimension-4 literature (Crans; Bourke–Lobbia) is a risk for its semantics (§2.5), not a refutation.*

**Honest residual risks of L:**
- S1 could fail for some endo-coherence in a Gray unfolding. The direct analogue for pasting schemes took real work (Finster–Mimram; Benjamin–Finster–Mimram).
- Usability of directed horizontal composition could be worse than expected in practice.
- The universe mismatch (§4.7) means a later universe story starts from a pseudo universe.

### 7.1 Staged plan, with a fallback

1. **Fix conventions.** Choose lax vs oplax, i.e. the factor order in U, once, consistently with Mikhail and with PR #3 §4.1.
2. **Supports and conservativity (Agda).**
   - Implement Steiner chains for pasting schemes and the Gray unfolding.
   - Prove that on a single hom, supp = Var. Then L restricted to one hom *is* the existing PR #4 checker.
3. **Two-object cases.**
   - Check §3.4 mechanically: D²∨D² (interchanger accepted one way, rejected the other); D¹∨D² (whiskering); D²∨D²∨D² (the cube's 4-cell typed from ps-terms only).
   - Validate against the strict AM model.
4. **Invertibility markings.** Port ICaTT's judgment, add the interchange propagation rule, and state "pseudo transformation".
5. **S3 (substitution) and S1 on paper,** starting from Steiner's strict result and Campion's pasting theorem.
6. **Representables and lax homs.** Restate PR #2's R-B and PR #3's §5.4 hom rule over L. Check the [conj] in §4.2 that Gray-shaped diagrams are derivable.
7. **Go uniform.**
   - Let the unfolding recurse (§2.5) and add the "ordinary ω-category" marking.
   - Re-run steps 2–3 for the case Σ(D¹ ∨ D¹) *inside* an object, i.e. directed Eckmann–Hilton-type interchange.
   - Check that marking an object restores exactly plain CaTT inside it.

**Fallback criteria.** Each fallback adds a marking globally, so under §2.4 and §2.5 work done earlier carries over.
- If the recursive step fails (S1 inside homs, or marking overhead), stay at two-tier.
- If S1 fails already for two-tier, or step 3 shows the support condition admits an interchanger in both directions or rejects a needed whiskering law, fall back to P.

---

## 8. Questions for Anthony

1. *(Answered 2026-11-18: "lax by default" means the most general version until there is a concrete reason otherwise. This note now recommends uniform L, reached through two-tier L.)*
2. **Marking ergonomics.** Under uniform L, plain CaTT reasoning inside an object needs the "ordinary ω-category" marking. Should objects be unmarked by default (most general), with the marking opt-in, as recommended here? Or should the surface syntax assume the marking unless told otherwise?
3. **Horizontal composition.** Is it acceptable that composing transformations across objects has no canonical result, with a surface-syntax default layering, or should the surface hide interchangers more aggressively?
