# Free ω-categories as objects

*Design notes, second pass, 2026-11-18. Companion to `notes/catt-survey.md` (project files). Claims marked **[recall]** are from background knowledge and were not re-checked against the source. Claims marked **[conj]** are conjectures.*

This note started as "universes and size". After review, the universe question is closed (§0), and what remains is the problem of making free and presented ω-categories into objects of the ambient. The note sets out two ways to do that, A1 and A2, in full, and compares them.

---

## 0. Decisions already made

These come from Anthony's review of the first pass.

1. **The ambient stays external.** ωCat is never an object of the theory. Quantifying over all categories happens at the meta-level, through context variables `C : ⋆`, as in core CaTT.
   - Particular objects that support it may still have **Lawvere-style internal quantifiers**, given as adjoints to reindexing. Those are universal properties of those objects, not the mechanism for meta-level quantification.
2. **No universes, ever.** There is no object classifying ω-categories, families, or presented objects. This includes the "object of finitely presented ω-categories" floated in the first pass.
3. **No definitional β-rules for universal properties.** A universal property produces *cells*: a lifted map together with an invertible cell relating it to the data it was built from. It never produces a definitional equation.
4. **Invertibility means invertibility in CaTT's models**, the coinductive notion that ICaTT internalises. It is not a parameter of the design.

Size is therefore no longer a live problem for this thread. Every object built by the rules below is finitely presented, hence small, and is interpreted in the ω-category of small ω-categories (§5).

---

## 1. The common setting

Both options are stated against the same background, so this section fixes it once.

### 1.1 Ambient judgments

The ambient reads `⋆` as "ω-category".

- `Θ ⊢ C : ⋆` says C is an object, meaning an ω-category.
- `Θ ⊢ F : C → D` is a functor.
- `Θ ⊢ α : F → G` is a 2-cell between functors, and so on upward.

Whether those 2-cells are pseudo or lax is the P/L choice compared in `notes/pseudo-vs-gray.md`. If the ambient's core rule is CaTT's, its 2-cells are forced to be pseudo (`limits-representables.md` §3.1).

- **Under P**, lax transformations are not 2-cells. They are maps out of Gray cylinders, so lax cells of diagrams (D3 below) are built from the Gray shapes `Γ ⊗ Dᵏ`.
- **Under L**, lax transformations are the native 2-cells, and L's coherence rule computes its side condition on the Gray unfolding of a pasting scheme.

Everything below holds under either option. Composition of functors, whiskering and their coherences are the ambient's own coherences, and nothing below adds to them.

### 1.2 Diagrams

Both options need to talk about "a Γ-shaped family of cells in C", for a closed CaTT context Γ. Write this

```
Θ ⊢ σ : Γ ⇒ C
```

and call σ a **Γ-diagram in C**. It assigns to each variable `x : A` of Γ a cell σ(x) of C of type A[σ]. The options need four things from it.

- **(D1) Evaluation.** A CaTT term `Γ ⊢ t : A` gives a cell t[σ] of C. This holds because C is an ω-category, so CaTT's operations are available inside it.
- **(D2) Functor action.** `F : C → D` and `σ : Γ ⇒ C` give `F∘σ : Γ ⇒ D`.
- **(D3) Higher cells of diagrams.** Γ-diagrams in C form an ω-category `Diag(Γ, C)`. A 1-cell `σ → σ'` is a lax transformation of diagrams: a cell `σ(x) → σ'(x)` for each object-variable x, plus lax naturality cells for the higher variables. Its shape is Mikhail's Gray context Γ ⊗ D¹ (`catt-survey.md` §9a, project files), and a k-cell has shape Γ ⊗ Dᵏ.
- **(D4) Transfor action.** A k-cell between functors `C → D` acts on a diagram `σ : Γ ⇒ C` to give a k-cell of `Diag(Γ, D)`.

How diagrams are defined belongs to the representables work. There are two candidates.

- **Primitive elements.** There is a judgment for cells of C, and σ is a list of such cells. Boundaries hold by typing, so σ(f) for `f : x → y` has source exactly σ(x).
- **Yoneda.** An n-cell of C is a map from a disc object `Dⁿ → C`. Then the source of σ(f) agrees with σ(x) only up to a cell, and a diagram becomes a homotopy-coherent family. This is workable but heavier.

The rest of this note works with either. It only uses (D1)–(D4).

### 1.3 How a universal property is stated

Both options state their universal property in the same way: some restriction functor `R : X → Y` between ω-categories is an **equivalence**. In CaTT style, this is one rule per dimension, all of the same form.

```
 y an object of Y
──────────────────────────────────────────────    (LIFT₀)
 an object x of X,  and an invertible cell  R x ≅ y  in Y

 u, u' parallel k-cells of X,   θ : R u → R u'  in Y
──────────────────────────────────────────────    (LIFTₖ₊₁)
 a cell v : u → u' of X,  and an invertible cell  R v ≅ θ  in Y
```

This is the coinductive definition of equivalence (essentially surjective on objects, and on every hom), written as filler rules. It is the same pattern as Mikhail's `uni` rule for limits. There are no side conditions beyond well-typedness, and no equations.

The two options differ in what X, Y and R are.

---

## 2. Option A1: one object for each CaTT context

### 2.1 Idea

For every closed CaTT context Γ there is an object ⟦Γ⟧, the free ω-category on Γ. Maps out of ⟦Γ⟧ are the same as Γ-diagrams. The object is indexed by CaTT syntax, the same way `coh_{Γ,A}` is indexed by a pasting scheme.

### 2.2 Rules

```
 Γ ⊢          (Γ a closed CaTT context)
───────────────    (FREE)
 Θ ⊢ ⟦Γ⟧ : ⋆

 Γ ⊢
──────────────────────    (GEN)
 Θ ⊢ η_Γ : Γ ⇒ ⟦Γ⟧
```

η_Γ is the **generic diagram**: η_Γ(x) is the generator x, seen as a cell of ⟦Γ⟧.

**Universal property.** Restriction along η_Γ,

```
R : Hom(⟦Γ⟧, C) → Diag(Γ, C),    F ↦ F ∘ η_Γ,
```

is an equivalence, stated by the LIFT schema of §1.3. Concretely, at dimension 0 this reads:

```
 Θ ⊢ σ : Γ ⇒ C
─────────────────────────────────────────────    (LIFT₀)
 Θ ⊢ ⟨σ⟩ : ⟦Γ⟧ → C
 Θ ⊢ β_σ : ⟨σ⟩ ∘ η_Γ ≅ σ      (invertible 1-cell of Diag(Γ, C))
```

At dimension 1 it says: given two functors `F, G : ⟦Γ⟧ → C` and a lax transformation of diagrams `θ : F∘η_Γ → G∘η_Γ`, there is a transformation `⟨θ⟩ : F → G` with an invertible cell `⟨θ⟩∘η_Γ ≅ θ`. Higher dimensions follow the same pattern.

**Side conditions.** Γ is closed and well formed. There is no free-variable condition, because the rule asserts nothing about Γ; it only names its free object.

### 2.3 What is derived

- **Maps from CaTT substitutions.** A CaTT substitution `Δ ⊢ τ : Γ` sends each variable of Γ to a term over Δ. Evaluating those terms at the generic diagram of Δ (D1) gives a diagram `τ[η_Δ] : Γ ⇒ ⟦Δ⟧`. Define

  ```
  ⟦τ⟧ := ⟨τ[η_Δ]⟩ : ⟦Γ⟧ → ⟦Δ⟧.
  ```

  The direction reverses, as expected. For composable substitutions, `⟦τ'⟧ ∘ ⟦τ⟧` and `⟦τ ∘ τ'⟧` are related by an invertible cell obtained from LIFT₁, not by an equation.
- **Discs and spheres.** `Dⁿ := ⟦disc context of dimension n⟧`. Its source and target maps `Dⁿ⁻¹ → Dⁿ` are ⟦τ⟧ for the two substitutions that pick out the source and target sub-discs.
- **Operations of C as precomposition.** Every CaTT operation becomes a map between free objects, and applying it to cells of C is precomposition (example below).

### 2.4 Worked example

Let `A = (x : ⋆, y : ⋆, f : x → y)` and `P = (x, y, z : ⋆, f : x → y, g : y → z)`. ⟦A⟧ is the walking arrow, and ⟦P⟧ is the walking composable pair.

1. In P, CaTT gives the term `comp(f, g) : x → z`. So `(x, z, comp(f, g))` is a substitution from A into P, and it gives a functor `⟦comp⟧ : ⟦A⟧ → ⟦P⟧`.
2. A composable pair `f' : a → b`, `g' : b → c` in C is a diagram `σ : P ⇒ C`. LIFT₀ gives `⟨σ⟩ : ⟦P⟧ → C`.
3. The functor `⟨σ⟩ ∘ ⟦comp⟧ : ⟦A⟧ → C` is "the composite of f' and g'". Restricting it along η_A gives `comp(f', g')` up to the β-cell.
4. Let Q be the context of three composable arrows. The associator coherence of CaTT relates the two composites in Q. By LIFT₁, it becomes a transformation between the two functors `⟦A⟧ → ⟦Q⟧` built from the two bracketings.

### 2.5 What A1 needs from elsewhere

- Diagrams `Γ ⇒ C` and their higher cells `Diag(Γ, C)` **for every finite context Γ**. That needs the Gray shapes `Γ ⊗ Dᵏ` for arbitrary Γ. Mikhail constructs these generally only conditionally: cones over arbitrary contexts rest on his Conjecture 3.6, and existence of Gray shapes is proved only for n = 1 (`catt-survey.md` §9a). §7.1 reduces the general case to one conjecture and records progress on it.
- Transfor action on arbitrary diagrams (D4).

### 2.6 Semantics

- **Strict model:** ⟦Γ⟧ is the free strict ω-category on Γ, read as a polygraph. The universal property holds strictly, which is stronger than required.
- **Weak model:** ⟦Γ⟧ is the free Grothendieck–Maltsiniotis weak ω-category on the computad Γ, using BMS's identification of CaTT contexts with finite computads.
- **Conservativity.** Cells of ⟦Γ⟧ between CaTT terms should be exactly CaTT terms, by the same identification **[conj: this is the key theorem to formalise]**.

---

## 3. Option A2: the initial object and one-cell attachment

### 3.1 Idea

There are two primitives: the empty ω-category, and the operation of **attaching one new cell** to any object along a chosen boundary. Free objects on contexts are built by attaching their generators one at a time. This mirrors how CaTT contexts are themselves built, one variable at a time, so A2 internalises *context extension* rather than *contexts*.

### 3.2 Rules

A **sphere of dimension n** in C is a pair of parallel (n−1)-cells `(a, b)` of C. For n = 0 the sphere is empty. Write it as a diagram `(a, b) : ∂Dⁿ ⇒ C`.

```
───────────────    (INIT)
 Θ ⊢ 0 : ⋆

 Θ ⊢ C : ⋆      Θ ⊢ (a, b) : ∂Dⁿ ⇒ C
──────────────────────────────────────────    (ATTACH)
 Θ ⊢ C[x : a → b] : ⋆
 Θ ⊢ ι : C → C[x : a → b]
 Θ ⊢ x : ι a → ι b    (a cell of C[x : a → b])
```

For n = 0, the result is written `C[x : ⋆]`, and x is a new object.

**Universal property of 0.** Hom(0, D) is contractible. There is a map `! : 0 → D`, and any two parallel k-cells of Hom(0, D) are related by an invertible (k+1)-cell. This is the LIFT schema with Y the terminal ω-category.

**Universal property of attachment.** A map out of `C[x : a → b]` is the same as a map F out of C together with a cell `F a → F b`. Precisely, the restriction

```
R : Hom(C[x : a → b], D)  →  Hom(C, D) ×_{Diag(∂Dⁿ, D)} Diag(Dⁿ, D),
    G  ↦  (G ∘ ι,  G x)
```

is an equivalence, stated by the LIFT schema. The right-hand side is a pseudo-pullback, so its cells carry invertible cells relating the two boundaries. At dimension 0 this reads:

```
 Θ ⊢ F : C → D      Θ ⊢ y : F a → F b    (a cell of D)
──────────────────────────────────────────────────    (LIFT₀)
 Θ ⊢ ⟨F, y⟩ : C[x : a → b] → D
 Θ ⊢ β : ⟨F, y⟩ ∘ ι ≅ F
 Θ ⊢ β_x : a cell relating ⟨F, y⟩ x to y, over the components of β at a and b
```

At dimension 1 it says: given `G, G' : C[x : a → b] → D`, a transformation `α : G∘ι → G'∘ι`, and a lax cylinder relating `G x` to `G' x` over α's action on a and b (a cell of shape `Dⁿ ⊗ D¹`), there is a transformation `G → G'` restricting to both, up to invertible cells.

**Side conditions.** a and b are parallel. This is a boundary check of exactly the kind CaTT already uses. Nothing else.

### 3.3 What is derived

- **Free objects on contexts, as notation:**

  ```
  ⟦x₁ : A₁, …, xₙ : Aₙ⟧  :=  0[x₁ : A₁][x₂ : A₂] … [xₙ : Aₙ]
  ```

  Each type Aᵢ mentions earlier generators. It is read in the current stage by pushing those generators forward along the ι maps (D2). This is a definition by recursion on the context, not an equation between terms.
- **The generic diagram** η_Γ: each attached generator, pushed forward along the later ι maps.
- **A1's universal property, as a theorem.** By induction on Γ, chain the attachment universal properties:

  ```
  Hom(⟦Γ, x : A⟧, C)  ≃  Hom(⟦Γ⟧, C) ×_{Diag(∂D, C)} Diag(D, C)
                      ≃  Diag(Γ, C)  ×_{Diag(∂D, C)} Diag(D, C)
                      ≃  Diag((Γ, x : A), C)
  ```

  The last step is a decomposition property of diagrams: a diagram on an extended context is a diagram on Γ plus one more cell. Under primitive elements this is immediate for 0-cells of Diag. For higher cells it is a statement about how the Gray shape `(Γ, x) ⊗ Dᵏ` decomposes **[conj for k ≥ 2]**.

  *Update:* the decomposition holds as an isomorphism onto the strict pullback at every k, given the cylinder contexts (`free-objects-proofs.md` Theorem 3). The step from the first line to the second, written out at dimension 0, also needs the action of the inductive β on the boundary terms of A, i.e. naturality terms (`free-objects-proofs.md` §3).
- **Maps from CaTT substitutions:** exactly as in A1 §2.3, once the universal property of ⟦Γ⟧ is available.
- **Attaching to objects that are not free.** For example:
  - `C[e : a → a]` adjoins a free endomorphism of an object a of C. Maps out of it are a functor F on C together with an endomorphism of `F a`.
  - `[C, D][γ : F → G]` adjoins a free transformation to an internal hom, if internal homs exist.

### 3.4 Worked example

1. `⟦P⟧ = 0[x : ⋆][y : ⋆][z : ⋆][f : x → y][g : y → z]`, the walking composable pair.
2. The disc objects bootstrap the same way: `D⁰ = 0[x : ⋆]` and `D¹ = 0[x : ⋆][y : ⋆][f : x → y]`. Each stage uses only cells of earlier stages, so if elements are later *defined* by Yoneda through discs, there is no circularity.
3. Composition as precomposition then works exactly as in §2.4, using the derived universal property of ⟦P⟧.

### 3.5 What A2 needs from elsewhere

- Diagrams only on **discs and spheres**: `Diag(Dⁿ, C)`, `Diag(∂Dⁿ, C)`, and their higher cells of shape `Dⁿ ⊗ Dᵏ`. These are cylinders on globes, the case that the naturality paper (2501.11620) and Mikhail's Gray rules already handle.
- Pseudo-pullbacks of hom ω-categories. These appear only *inside* the statement of the universal property, as the source of the cells to be lifted. They are not a new object former.
- Transfor action on cells (D4), for spheres only.

### 3.6 Semantics

- **Strict model:** `C[x : a → b]` is the strict pushout of C along the boundary inclusion `∂Dⁿ → Dⁿ`. This is the standard "add one generator" step for polygraphs.
- **Weak model:** the homotopy pushout along the boundary inclusion. Boundary inclusions are the generating cofibrations in the known model structures on ω-categories, so this pushout is well behaved **[recall: for the weak (GM) case, which model structure to cite]**.

---

## 4. Comparison

### 4.1 How each option relates to the other

- **A2 gives A1 with no further rules.** ⟦Γ⟧ is defined by iterated attachment, and its universal property is a theorem (§3.3), given the decomposition property of diagrams.
- **A1 gives A2 only together with pushouts.** `C[x : a → b]` would be the pushout of `C ← ⟦∂Dⁿ⟧ → ⟦Dⁿ⟧`, where the left map is `⟨(a, b)⟩`. Without pushouts, A1 cannot adjoin a cell to an object that is not free.

So **A2 = A1 + pushouts along boundary inclusions**, and nothing more. If the colimits work supplies general pseudo pushouts anyway, the two options become interderivable, and the remaining difference is which object is the primitive seed.

### 4.2 Table

| | A1 | A2 |
|---|---|---|
| New object formers | ⟦Γ⟧ for each closed CaTT context | 0, and `C[x : a → b]` |
| Indexed by | CaTT syntax, like `coh` | a sphere in an arbitrary object |
| Side condition | Γ closed and well formed | a, b parallel |
| Universal property compares Hom with | `Diag(Γ, C)`, for any finite Γ | `Hom(C, D) ×_{Diag(∂Dⁿ, D)} Diag(Dⁿ, D)` |
| Gray shapes used in the rules | `Γ ⊗ Dᵏ` for every finite Γ | `Dⁿ ⊗ Dᵏ` only |
| Gray shapes used to get ⟦Γ⟧'s universal property | `Γ ⊗ Dᵏ` (in the rule itself) | `Γ ⊗ Dᵏ` (in the decomposition theorem) |
| Status of `Γ ⊗ Dᵏ` for general Γ | reduces to Conjecture N (§7); being investigated | same conjecture |
| ⟦Γ⟧ | primitive | defined by recursion on Γ |
| Universal property of ⟦Γ⟧ | primitive | theorem, needing the decomposition of Diag |
| Adjoining a cell to a non-free object | needs pushouts | direct |
| Maps from CaTT substitutions | derived from LIFT₀ | derived the same way |
| Definitional equations | none | none |
| Strict model | free strict ω-category on a polygraph | strict pushout along a boundary inclusion |
| Weak model | free GM ω-category on a computad | homotopy pushout along a boundary inclusion |
| Conservativity over CaTT | stated directly for ⟦Γ⟧ | same statement, for the derived ⟦Γ⟧ |

### 4.3 Discussion

**Fit with the existing rules.** Both are CaTT-shaped: each is a judgment with a syntactic side condition plus one filler schema, and neither adds equations or breaks linearity. A1 is indexed by contexts, which matches how `coh_{Γ,A}` is indexed by pasting schemes. A2 is indexed by one generator at a time, which matches how contexts themselves are formed. Neither is obviously closer to the aesthetic. The difference is whether the object language sees whole contexts or context extension.

**Dependence on the Gray shapes.** Both options need the Gray shapes `Γ ⊗ Dᵏ` for arbitrary Γ, in different places.

- A1's universal property quantifies over lax transformations between Γ-diagrams for every finite Γ, so the shapes appear in the rule itself.
- A2's rules only mention cylinders on globes. But deriving the universal property of ⟦Γ⟧ from them needs the decomposition of `Diag((Γ, x), C)`, whose higher cells are again shaped like `Γ ⊗ Dᵏ`.

So this is not a difference in what the two options ultimately rest on. It is a difference in whether the shapes enter as part of a rule or as part of a theorem. §7 reduces the existence of these shapes to a single conjecture, now under investigation.

**Expressivity.** On its own, A2 is strictly stronger, because it adjoins cells to arbitrary objects. Constructing "an object that behaves like" a structure constantly adjoins to objects that are not free: a cell to an internal hom, a cell to a limit, a relation to a presented object. Without pushouts, A1 can only build free objects from nothing.

**Cost of A2.** A2's universal property is heavier to state, because even at dimension 0 the lift comes with two coherence cells (β and β_x). A2 also produces many intermediate objects: every prefix of a context is an object. And the universal property of ⟦Γ⟧, which is what most users would use, becomes a theorem rather than a rule.

**When the difference disappears.** If general pseudo pushouts are added for other reasons, A1 + pushouts and A2 + pushouts are the same theory. A1 then has the smaller statement for the common case.

### 4.4 Status

Both options remain open. What separates them is structural, not evidential:

1. **General pushouts.** If the theory has general pseudo pushouts, A1 is the smaller addition and ATTACH is redundant. If it does not, A1 cannot adjoin a cell to a non-free object, while A2 can.
2. **Where the Gray shapes enter.** A1 uses `Γ ⊗ Dᵏ` inside a rule; A2 uses it inside a theorem. Both need it to give ⟦Γ⟧ its universal property.

The next step is not to choose but to settle the shared dependency: the existence of `Γ ⊗ Dᵏ` for arbitrary Γ. §7 records what has been proved and the precise conjecture that remains.

### 4.5 Relation to `limits-representables.md` §5

The limits and representables note compares two kernel options for the same goal. Both are relevant here.

- **Its R-A is A1.** That note states the same object former and the same universal property, with the same "no definitional β" convention.
- **Its R-B defines ⟦Γ⟧ as the lax colimit of the constant point diagram over Γ.** It adds no rule beyond general lax colimits, and rests on the conjecture `laxcolim(const ⊤) ≃ Free(Γ)`.
- **Its §5.1 supplies the diagram notion of §1.2 here.** Elements of C are maps `⊤ → C`, and a Γ-diagram is a Γ-family of such maps. With that reading, ATTACH's input `(a, b)` is a pair of parallel ambient cells `⊤ → C`.

How A2 sits next to R-A and R-B:

1. **Dependence on general Gray shapes.** All three need them. R-A needs them in its rule (§4.3). R-B needs them because a lax cocone over an arbitrary context Γ is built from Mikhail's cone machinery, including his Conjecture 3.6. A2 needs them in the decomposition theorem. §7 shows that Conjecture 3.6 and the Gray shapes reduce to the same conjecture.
2. **Lax or pseudo.** R-B uses *lax* colimits, which Mikhail's framework already provides. ATTACH is a *pseudo* pushout: the cell relating `G ∘ ι` to F must be invertible. A lax pushout of the span `C ← ⟦∂Dⁿ⟧ → ⟦Dⁿ⟧` would instead add non-invertible cells between the two copies of the boundary. So under R-B, adjoining a cell to a non-free object needs either pseudo colimits or lax colimits with marked (invertible) legs. Which of these is available depends on the pseudo-versus-lax choice for the ambient (`notes/pseudo-vs-gray.md`).
3. **Staging.** If R-B's conjecture is proved and pseudo colimits are available, both A1 and A2 become derived rules.

---

## 5. Size and consistency

**Size.** Every object built from 0, ATTACH and ⟦Γ⟧ is finitely presented, so small. The rules are interpreted in the ω-category of small ω-categories. The universe of the meta-theory is used once, externally, to say what "small" means, and never appears in the rules.

**Consistency.** CaTT has no empty type and no negation, so "inconsistent" cannot mean "proves ⊥". Three properties replace it.

1. **Non-triviality.** The strict model of §2.6 and §3.6 is non-trivial and validates every rule. One caveat: strict ω-categories with *lax* transformations form a Gray-enriched structure rather than a strict ω-category, so the ambient is modelled weakly even there.
2. **Conservativity over CaTT.** Cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms **[conj]**. This is the theorem that guarantees the new rules do not collapse anything.
3. **Decidable checking.** Neither option adds definitional equations, so neither can affect CaTT's syntactic equality or the termination of any future strictification rewrites.

---

## 6. Notes for the other threads

- **Agda formalisation.** Both options can be postulated side by side: ⟦Γ⟧ with A1's LIFT, and INIT/ATTACH with A2's LIFT. Deriving A1's LIFT₀ from A2's rules (§3.3) is then a concrete statement to prove, and the conservativity statement of §5 can be stated for either. The cylinder contexts `Q↑Y` of §7.1 are syntactic and could be formalised directly, which would let the depth-2 cases be machine-checked.
- **Limits and representables.** Both options need the diagram judgment of §1.2. Primitive elements make strict boundaries automatic. The Yoneda reading needs homotopy fibers. ATTACH is a pseudo pushout along a boundary inclusion: if general pseudo colimits are adopted there, ATTACH becomes an instance of them (§4.4).
- **Internal hom and Gray tensor.** Neither option needs `[C, D]`. If internal homs exist, attaching to them gives free transformations and free modifications.

---

## 7. Open technical problems

### 7.1 The shared dependency: Gray shapes for arbitrary contexts

The Gray shapes `Γ ⊗ Dᵏ` that A1, A2 (via its decomposition theorem) and R-B all need reduce to one conjecture, written up for external analysis in [`conjectures/naturality-arbitrary-depth.md`](conjectures/naturality-arbitrary-depth.md).

**The conjecture (N).** For every pasting context Q, every full type B over Q, and every up-closed set Y of variables of Q, the coherence `coh_{Q,B}` has a naturality cell in the cylinder context `Q↑Y`. This extends BMOSV's naturality construction (arXiv 2501.11620), which is proved only when Y has depth at most 1. "Depth" means how many dimensions below the coherence the duplicated variables sit.

**What has been established** (proof sketches in the conjecture file):

1. **Reduction to pasting contexts.** Given N, cylinder contexts `Γ↑X` and naturality terms exist for *every* CaTT context Γ, by recursion through substitutions. The general type of a cylinder cell is the nested-whiskering formula of the conjecture file, §2.2, which agrees with BMOSV at depth ≤ 1 and with Mikhail's cone formula after collapsing one end.
2. **Gray shapes for all k.** Applying N to `Γ↑X` with the up-closed set of cylinder variables gives `Γ ⊗ D²`, and iterating gives `Γ ⊗ Dᵏ`. *To check:* that these coincide with the contexts generated by Mikhail's `gray` judgment.
3. **Mikhail's Conjecture 3.6 (cones).** A cone over Γ is the cylinder `Γ↑Var(Γ)` with its source end collapsed to the apex. The cone terms `p_t` are obtained from the naturality terms by substituting `x⁻ ↦` identities on the apex and correcting with unitor coherences. *To check:* Mikhail's free-variable condition on `p_t`.
4. **First case beyond the literature.** The left unitor over a single arrow, with all variables duplicated (depth 2), is proved by a "sliding" argument. It uses only coherences over pasting contexts and BMOSV's depth-0 case.
5. **Every 2-dimensional coherence over a fully selected chain** (researcher response, verified 2026-11-18). A *relative ladder theorem* compares any two parallel 2-terms in the cylinder of a chain whose boundaries cross the ladder at the two ends. This settles the associator over three arrows and subsumes item 4. The proof uses only coherences over pasting contexts, then substitution.
6. **Corrections from the same review.** The recursion for naturality terms needs structural induction within each dimension (a composite's arity variables are sent to terms of the same dimension). The whole-cylinder fullness argument in the conjecture file's §8 holds at best for coherence constructors, not composites. With Steiner's sign convention the cylinder formula presents `I ⊗ Γ`, not `Γ ⊗ I`. A directed cylinder alone is not a path object.

**Under P and under L.** Under P, lax cells of diagrams are maps out of `Γ ⊗ Dᵏ`, so these contexts are needed as written. Under L, the naturality cells would instead come from L's native lax interchange coherences, whose correctness is lemma S1 of `pseudo-vs-gray.md`. N is the CaTT-side instance of the same claim: a coherence is laxly natural in its variables.

**Related problem statements.** One other file in `conjectures/` overlaps with this one, in two places.

- **`gray-contexts-in-catt.md` (G(n)).** It asks whether coherences over frame-acyclic molecules are conservative over CaTT. Conjecture N with all variables duplicated is a special case of that, for the molecules `P ⊗ D¹` (conjecture file §8). The left-unitor proof uses the same layering idea as G's §3.2.
- **`gray-contexts-in-catt.md` §6 (1)** (formerly `gray-contexts-steiner.md`). It asks for Mikhail's Gray contexts in all dimensions. Items 1 and 2 above give an explicit candidate, conditional on N.

**What remains.** The general depth-≥2 case. The next concrete checks are the 3-dimensional unitor over the 2-disc (the first 2-dimensional Q), and arbitrary up-closed sets on a chain. The ladder theorem is the dimension-2 instance of a proposed induction hypothesis, the relative comparison property (RC) recorded in the conjecture file's verification section; RC in general is open.

### 7.2 Other open problems

*Progress on all four items, and on density, is in [`free-objects-proofs.md`](free-objects-proofs.md) (2026-11-18): item 2 is proved, item 4 is answered for the strict and (∞,ω) models, item 1 holds strictly at every dimension given the cylinders, and item 3 is proved in its strict half under P and reduced to E11 otherwise. That file also shows that deriving A1's LIFT₀ from A2 already needs the naturality terms of the boundary terms of Γ's types (§3 there), not only (Dec) at higher dimensions. Owners and remaining pieces are in `open-issues.md` (C3–C7, C9).*

1. **Decomposition of diagrams.** Prove `Diag((Γ, x : A), C) ≃ Diag(Γ, C) ×_{Diag(∂D, C)} Diag(D, C)` at every dimension. This is the one step between A2's rules and A1's universal property. Its higher cells are shaped like `Γ ⊗ Dᵏ`, so it depends on §7.1.
2. **Lifts of invertible cells are invertible.** The LIFT schema should imply that the lift of an invertible cell is invertible, so that maps out of ⟦Γ⟧ agreeing on generators are related by an invertible cell. This is expected from the coinductive definition of equivalence, but it needs a proof in the rule system.
3. **Conservativity.** Prove that the cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms.
4. **Weak model of ATTACH.** Identify the model structure on weak ω-categories in which boundary inclusions are cofibrations, so that the homotopy pushout of §3.6 is justified.

---

## References

- Finster & Mimram, *A type-theoretical definition of weak ω-categories*, LICS 2017 ([arXiv 1706.02866](https://arxiv.org/abs/1706.02866)).
- Benjamin, Markakis & Sarti, *CaTT contexts are finite computads* ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)).
- Mikhail, *A type-theoretic definition of lax (∞,∞)-limits* ([arXiv 2412.13310](https://arxiv.org/abs/2412.13310)).
- Benjamin, Markakis, Offord, Sarti & Vicary, *Naturality for higher-dimensional path types* ([arXiv 2501.11620](https://arxiv.org/abs/2501.11620)).
- Benjamin, Champin & Markakis, *A type theory for invertibility in weak ω-categories* ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)).
- Loubaton, *Theory and models of (∞,ω)-categories* ([arXiv 2307.11931](https://arxiv.org/abs/2307.11931)) and *Categorical theory of (∞,ω)-categories* ([arXiv 2406.05425](https://arxiv.org/abs/2406.05425)). Semantic background for the lax ambient.
- Shulman, *Set theory for category theory* ([arXiv 0810.1279](https://arxiv.org/abs/0810.1279)). Background for the external treatment of size in §5.
