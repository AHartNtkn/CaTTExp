# Size, universes, and free ω-categories as objects

*Design notes, first pass, 2026-11-18. Companion to `notes/catt-survey.md` (project files). Claims marked **[recall]** are from background knowledge and were not re-checked against the source this session. Claims marked **[conj]** are my own conjectures.*

---

## 0. Summary

The survey records Anthony's position that universes are "probably neither desirable nor needed", and that the goal is to *construct objects that behave like* ordinary structures, not to have a category of all of them. This note takes that seriously and asks what "size" still has to mean.

There are three separate questions that tend to get mixed together:

| Layer | Question | Is it a size problem? |
|---|---|---|
| **A. Presented objects** | Can the free ω-category ⟦Γ⟧ on a CaTT context Γ be an object of the ambient? | **No.** Finite computads give small ω-categories. It is a *representability* question. |
| **B. The ambient** | The theory is the internal language of ωCat. Is ωCat itself an object? | Only if we ask for it. By default the ambient stays *external and schematic*, the way core CaTT has one implicit ambient. |
| **C. Internal universes** | Is there an object U whose maps C → U classify something (functors into ωCat, fibrations, presented objects)? | **Yes.** This is where consistency is at stake. |

**Recommendation.**

1. Build layer A as two rules: an **initial object** and **cell attachment** `C[x : a → b]`. ⟦Γ⟧ is then the iterated attachment ∅[x₁]…[xₙ]. This is CaTT-shaped (shape + side condition + one filler schema), linear, and needs no universe.
2. Keep layer B external: no object for ωCat. "For all categories" is a context variable `C : ⋆`, as in CaTT's own single ambient.
3. For layer C, adopt **no universe** now (option U0). Keep **U_fp**, the object of finitely presented ω-categories, as the candidate if one is ever needed. It is small, contains no copy of itself, and needs no level algebra.
4. Do **not** add `ωCat : ωCat`, and avoid level hierarchies with `max`/`succ`. The second conflicts with the "no algebraic structure in the meta-theory" rule.

The rest of the note gives the literature, the rules, the consistency story, and what the other threads should know.

---

## 1. Literature

### 1.1 Size in category theory

- **Grothendieck universes.** The standard device: fix an inaccessible κ, call κ-small sets small, and ωCat is the large category of small ω-categories. Shulman, *Set theory for category theory* ([arXiv 0810.1279](https://arxiv.org/abs/0810.1279)) surveys this and the alternatives (ZMC, NBG classes, Feferman's reflection-style approaches) **[recall]**.
- **"Cat of all categories."** Lawvere's ETCC treats categories and functors as the primitive objects of a metacategory, with no category of all categories inside it **[recall]**. That is exactly layer B kept external.
- **Higher-categorical size.** Lurie builds Cat_∞ as a large ∞-category using a universe (HTT §3.0) **[recall]**. Every "∞-category of ∞-categories" in the literature is one size up from its objects.

### 1.2 Universes in type theory

- **Girard's paradox.** Martin-Löf's original `Type : Type` is inconsistent. Hurkens' simplification needs impredicative-style quantification over the universe (Π over U landing in U) **[recall]**. The lesson: paradoxes come from *quantifying over the universe inside the universe*, not from the universe existing.
- **Russell vs Tarski.** Russell style (`A : U` means A is a type) vs Tarski style (codes `a : U` plus a decoding `El a`). Tarski style keeps the object and the "large" thing it names separate. It fits CaTT better, since in CaTT `⋆` is a type and cells are terms.
- **Levels.** Agda, Lean and Rocq use level hierarchies with level expressions (`suc`, `⊔`). Kovács, *Generalized universe hierarchies and first-class universe levels* (CSL 2022, [arXiv 2103.00223](https://arxiv.org/abs/2103.00223)) shows levels can be any well-founded order, internal or external. This matters for us because a level algebra is exactly the kind of meta-level algebraic structure Anthony rules out.
- **Hofmann–Streicher universes.** Every presheaf topos has a universe built from a universe in the metatheory **[recall]**. Computads form a presheaf topos (survey §5), so a universe of *computads* (syntax) exists canonically. A universe of *ω-categories* (semantics) is a separate question.

### 1.3 Directed universes

- **Riehl–Shulman simplicial type theory**, and **Gratzer–Weinberger–Buchholtz**, *Directed univalence in simplicial HoTT* ([arXiv 2407.09146](https://arxiv.org/abs/2407.09146)) and *The ∞-category of ∞-categories in simplicial type theory* ([arXiv 2602.02218](https://arxiv.org/abs/2602.02218)). The universe is a universe of covariant families; directed univalence says hom in the universe is the type of functions. This is the (∞,1) benchmark, and the survey already records that Anthony judged the approach aesthetically far from CaTT.
- **Loubaton**, *Theory and models of (∞,ω)-categories* ([arXiv 2307.11931](https://arxiv.org/abs/2307.11931)) and *Categorical theory of (∞,ω)-categories* ([arXiv 2406.05425](https://arxiv.org/abs/2406.05425)). Develops Gray tensor, lax transformations, Yoneda and a Grothendieck construction for (∞,ω)-categories **[recall: exact scope of straightening]**. This is the closest semantic home for a lax "ωCat of ωCats".
- **Inductive vs coinductive (∞,ω).** Henry and Loubaton ([arXiv 2301.11424](https://arxiv.org/abs/2301.11424)) and related work show there are two different (∞,ω) theories, depending on whether equivalences are defined inductively or coinductively **[recall: exact titles and statements]**. GM-style weak ω-categories (the CaTT models) use the coinductive notion. Any internal universe has to pick one, and its "directed univalence" changes meaning with the choice.

### 1.4 CaTT-side facts used below

- **BMS:** CaTT contexts are exactly finite computads, and the syntactic category of CaTT is equivalent to (the opposite of) finite computads with Kleisli maps of the free ω-category monad ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)) **[recall: exact form of the equivalence]**. So "⟦Γ⟧ is an object" amounts to embedding CaTT's own syntactic category into the ambient, contravariantly.
- **Computads as cell attachments.** A computad is built by repeatedly attaching a generator along a boundary sphere. The free ω-category is built the same way. This is why ⟦Γ⟧ can be generated by one attachment rule.
- **Weak ω-categories are algebras of a finitary monad on globular sets** (GM / Batanin–Leinster) **[recall]**. So their category is locally finitely presentable, which gives the size story in §4.3.

---

## 2. Layer A: presented objects without a universe

Notation follows the survey's "CaTT with ambient ωCat" plan.

- `Θ ⊢ C : ⋆` says C is an ω-category (an object of the ambient).
- `Θ ⊢ F : C → D` is a functor, and higher arrows are transfors.
- `Θ ⊢ a :ₙ C` is an n-cell of C, with `a : s → t` for its boundary. Whether this *element judgment* is primitive or defined is the representables thread's question; the rules below work with either reading (see §2.4).

### 2.1 Option A1: ⟦Γ⟧ as a primitive

```
   Γ ⊢            (Γ a CaTT context, i.e. a finite computad)
──────────────    (FREE-FORM)
 Θ ⊢ ⟦Γ⟧ : ⋆

 Γ ⊢    Θ ⊢ C : ⋆    Θ ⊢ σ : Γ ⇒ C     (σ assigns a cell of C to each variable of Γ, respecting boundaries)
──────────────────────────────────────    (FREE-ELIM)
          Θ ⊢ ⟨σ⟩ : ⟦Γ⟧ → C
```

plus generic cells `ηₓ :ₙ ⟦Γ⟧` for each `x : A` in Γ, and a universal-property schema saying that restriction along η is an equivalence between maps `⟦Γ⟧ → C` and substitutions `Γ ⇒ C`, at every dimension. That schema is the same pattern as Mikhail's `uni` rule (survey §9a): a shape judgment, here "transfors between substitutions", plus one filler schema.

- **Side conditions:** Γ is closed (does not mention Θ). There is no free-variable condition because nothing is being *asserted* about Γ; the rule only names its free object.
- **Pro:** directly states the goal. CaTT's coh terms become cells of ⟦Γ⟧ for free: `coh_{Δ,A}[τ]` in Γ is a cell of ⟦Γ⟧.
- **Con:** substitution Γ ⇒ C needs the element judgment first. Functoriality in Γ (a CaTT substitution `σ : Γ → Δ` gives `⟦Δ⟧ → ⟦Γ⟧`) is either a definitional equation, which adds strictness to the ambient's weak composition, or yet another coherence family.

### 2.2 Option A2 (recommended): initial object plus cell attachment

Two rules generate all of A1, and they also work *relative to an arbitrary object*, which A1 cannot do.

```
──────────────    (INIT)
 Θ ⊢ 0 : ⋆

 Θ ⊢ C : ⋆    Θ ⊢ a, b :ₙ C    Θ ⊢ a ∥ b       (a and b parallel: same source and target, or both 0-cells)
──────────────────────────────────────────────    (ATTACH)
 Θ ⊢ C[x : a → b] : ⋆
 Θ ⊢ ι : C → C[x : a → b]
 Θ ⊢ x :ₙ₊₁ C[x : a → b]    with  x : ι a → ι b
```

Universal property, as one schema: for every D, restriction along (ι, x) is an equivalence

```
Hom(C[x : a → b], D)  ≃  Σ (F : C → D) . (F a → F b in D)
```

at every dimension, with the higher cells generated by a transfor-shape judgment, as in Mikhail's construction. For INIT the right-hand side is a point.

- **⟦Γ⟧ is derived:** for `Γ = x₁ : A₁, …, xₙ : Aₙ`, set `⟦Γ⟧ := 0[x₁ : A₁][x₂ : A₂]…[xₙ : Aₙ]`, reading each Aᵢ through the earlier ι maps. FREE-ELIM follows by induction on Γ.
- **Linearity:** each attachment uses its new variable exactly once and never identifies cells, so the "linear generation" principle from the survey (§13) holds. No equations are introduced.
- **Side conditions** stay syntactic: parallelism of a and b is a boundary check of exactly the kind CaTT already uses.
- **Relative presentations come free.** `C[x : a → b]` adjoins a generator to any object. That is the main tool for "objects that behave like" a structure: start from a free object, attach generators, and later (with invertibility, survey §7) attach invertible cells for relations.
- **ℕ-like objects need no size.** `⟦y : ⋆, s : y → y⟧ = 0[y][s : y → y]` is finite. Maps out of it are "an object of D with an endomorphism" **[conj: its endo-hom is a weak version of ℕ]**. Induction or recursion principles are a separate question (colimits thread), but the *object* is already finitely presented.
- **Con:** ATTACH is a pushout, so it is a colimit. In the weak setting it must be the *pseudo* (invertible-cone) pushout, not Mikhail's lax colimit. That means it relies on whatever invertibility judgment the limits thread adopts, or it is taken as primitive. Either way, A2 is really "colimits of a specific shape", and should share machinery with that thread.

### 2.3 Why A2 over A1

A1 is the special case of A2 where the base is 0. A2 costs one more rule and gives relative presentations, which ordinary mathematics needs constantly (adjoin a root, adjoin an element, adjoin a relation). A2 also keeps every rule about a *single generator*, so its side conditions are as small as CaTT's.

### 2.4 Interaction with representables

- If **elements are primitive** (`a :ₙ C`), ATTACH is stated as above.
- If **elements are defined by Yoneda** (`a :ₙ C` means a map `Dⁿ → C`, where `Dⁿ := ⟦disc context⟧`), there is a circularity: Dⁿ is itself built by ATTACH. It is harmless if disks are generated first: `D⁰ := 0[x]` needs no elements, and `Dⁿ⁺¹ := Dⁿ ∪_{Sⁿ} Dⁿ[x : …]` uses only cells of earlier disks. Writing this out is a good early check for the Agda formalisation.

---

## 3. Layer B: keep the ambient external

The theory is the internal language *of* ωCat. That does not require ωCat to be an object *in* it.

- **Rule shape:** no rule concludes `Θ ⊢ ωCat : ⋆`. A statement "for every ω-category C" is a judgment in a context with `C : ⋆`. This is how core CaTT already works: there is one ambient, never named.
- **What this costs:** no internal quantification over all categories. A theorem about every C is schematic (a judgment with a free variable), not an object of the theory. No "category of vector spaces" object. Both match Anthony's stated target.
- **What it keeps:** internal homs `[C, D]`, limits and colimits of finite diagrams, and presented objects are all small constructions on small objects. None of them forces ωCat to be an object.
- **Analogy:** ETCC for categories, and Lean/Agda's "universe of the metatheory" for statements that quantify over all types at the judgment level.

**Recommendation:** fixed. Nothing in the other threads' scope (internal hom, Gray tensor, limits) seems to require breaking it.

---

## 4. Layer C: internal universes, if ever

### 4.1 The options

| Option | Rules | What maps C → U mean | Consistency | Aesthetic fit |
|---|---|---|---|---|
| **U0: none** | none | n/a | trivially fine | best: adds nothing |
| **U_fp: finitely presented objects** | `⊢ U_fp : ⋆`; each closed attachment term P gives a code `⌜P⌝ :₀ U_fp`; directed univalence `Hom_{U_fp}(⌜P⌝, ⌜Q⌝) ≃ [P, Q]` | only "pointwise" names of fp objects; no classification of families | U_fp is small (countably many fp shapes up to iso) and not itself fp, so it never contains itself | good: indexed by *shapes*, no levels |
| **U_i: level hierarchy** | `U_i : ⋆`, `U_i :₀ U_{i+1}`, Tarski decoding, directed univalence, straightening-style classification of families | lax functors C → ωCat_i, i.e. (op)fibrations with small fibres | needs one Grothendieck universe per level in the model; standard | poor: level algebra in the rules, needs straightening for (∞,ω) |
| **U = ωCat, U : U** | one self-containing universe | same as above, unrestricted | **[conj]** dangerous once U is closed under internal hom and *limits indexed by U*; probably consistent with only finite limits, but unproven | elegant to state, risky |

### 4.2 Why `U : U` is risky, and exactly where

Girard-style paradoxes need a way to quantify over U inside U.

- Here that would be a **limit indexed by U** (an end ∫_{X:U}) or an internal hom whose domain is U itself, landing back in U.
- Mikhail's limits (survey §9a) are over **finite** contexts only. If every universal construction is indexed by a finite computad, U is never a diagram shape, and the usual encodings do not go through **[conj]**.
- Lawvere's fixed-point form of Cantor needs a point-surjection `A → [A, B]` and an endomap of B without fixed points. Without a subobject classifier there is no obvious B **[conj]**.

So `U : U` may well be consistent in a finite-limits theory. But it would be a fragile invariant: every future universal-property rule would need a "not indexed by U" side condition, and that side condition is not syntactic in the CaTT sense. That is the main argument against it.

### 4.3 Why U_fp is the right fallback

- Weak ω-categories are algebras of a finitary monad, so ωCat is locally finitely presentable **[recall]**. Every object is a filtered colimit of finitely presented ones, and the finitely presented ones form an essentially small category.
- So **U_fp is a small object**, and it is the "universe" that the theory already implicitly ranges over: each object built by INIT and ATTACH is fp. U_fp internalises the syntactic category of presentations, which BMS already identify with CaTT's syntactic category.
- **No self-membership:** U_fp has infinitely many objects, so it is not finitely presented, so `⌜U_fp⌝` is not a code. The stratification comes from the shape language, not from a level index.
- **What it does not give:** families. A map C → U_fp is not a fibration with fp fibres in general, since fp objects are not closed under the relevant limits. So U_fp is a catalogue, not a classifier. If dependent families are needed, the survey's suggestion (families as fibration-shaped contexts, or lax limits over a base) is still the route.
- **Use case:** internalising meta-operations. For example, a functor `Σ : U_fp → U_fp` for suspension, or quantifying over shapes inside the theory. This is speculative, and is the only reason I can see to want U_fp at all.

---

## 5. What "consistent" means here

CaTT has no empty type and no negation, so "inconsistent" cannot mean "proves ⊥". Three properties are the useful substitutes, from weakest to strongest:

1. **Non-triviality.** There is a model in which the interpretation is not the terminal ω-category everywhere.
   - Cheap check: the **strict model**. Interpret the ambient in strict ω-categories with the lax Gray structure (Crans; Ara–Maltsiniotis **[recall]**), ⟦Γ⟧ as the free strict ω-category on Γ (a polygraph), and ATTACH as the strict pushout. Every rule in §2 holds there, and the model is clearly non-trivial.
   - Caveat: strict ω-categories with *lax* transformations form a Gray-enriched structure, not a strict ω-category, so the ambient is modelled weakly even here.
2. **Conservativity over CaTT.** The new rules prove no new cells between CaTT terms of ⟦Γ⟧. For A2 this should follow from the universal property: cells of ⟦Γ⟧ between CaTT terms are cells of the free weak ω-category on Γ, and these are exactly CaTT terms by BMS **[conj: this is the key theorem to formalise]**. It is also what rules out `U : U`-style collapse in practice.
3. **Decidable checking.** ATTACH and INIT add only new term formers and no definitional equations (the universal property gives cells, not rewrites), so they cannot break CaTT's syntactic equality. A definitional β-rule for FREE-ELIM (`⟨σ⟩ ∘ η_x ≡ σ(x)`) would be the only rewrite and is clearly terminating. Universes with directed univalence as a *definitional* rule would be the first real threat here.

---

## 6. Notes for the other threads

- **Agda formalisation.** For the postulated sketch of free-ω-category-as-object, I suggest postulating INIT and ATTACH (with ι, x and the 1-dimensional part of the universal property) rather than ⟦Γ⟧ directly, then *defining* ⟦Γ⟧ by recursion on contexts. That makes the BMS-style conservativity statement (§5.2) something you can state, and keeps the postulates per-generator.
- **Limits and representables.** ATTACH is a pseudo pushout along a sphere inclusion. If that thread adopts an invertibility judgment and pseudo colimits, ATTACH should be an instance of it. If it adopts disks as primitive objects, §2.4 shows the bootstrapping order.
- **Internal hom and Gray tensor.** Nothing here needs `[C, D]`. If it exists, U_i-style directed univalence becomes statable, but U0 and U_fp do not depend on it.

---

## 7. Open questions for Anthony

1. **A1 or A2?** Is "free object on a whole context" the primitive you want, or is "attach one generator to any object" (A2) closer to the aesthetic? A2 is smaller per rule and gives relative presentations.
2. **Is the ambient allowed to stay external** (layer B), with "for all C" only at the judgment level?
3. **U0 for now, U_fp later?** Or should even U_fp be off the table?
4. **Definitional β for FREE-ELIM?** Accept `⟨σ⟩ ∘ η_x ≡ σ(x)` as a definitional rule, or keep everything weak and get it from the universal-property schema?
5. **Inductive or coinductive invertibility** for the pseudo pushout in ATTACH. CaTT models are coinductive; this should match whatever ICaTT-style judgment the project adopts.
