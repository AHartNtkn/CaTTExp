# Chapter 6. Limits and representables

The limit rules extend the kernel by **two context functions and one term former**. The context functions are the specified shapes of chapter 5 (Cone, Tr_n, combined into Horn_n). The term former is `uni`, the universal filler. Limits of every finite diagram, lax, pseudo or partially lax, come from this one schema. Colimits are a second instance of the same schema with their own shapes. Elements, hom objects, comma objects and cotensors are derived.

The rules are Mikhail's CaTT_lim (arXiv 2412.13310) with three repairs, restated over the lax core.

## 6.1 The limit object and its universal cone

**Rule.**
```
Γ ⊢    Δ ⊢ γ : Γ                                   Γ ⊢    Δ ⊢ γ : Γ
───────────────────── (lim)                       ─────────────────────────────── (ucone)
Δ ⊢ lim_Γ[γ] : ⋆                                  Δ ⊢ λ : Cone(Γ; lim_Γ[γ])[γ]
```
Γ is any finite context, the base of the diagram (chapter 4: read weakly, no homotopicality check). The universal cone λ is a substitution into the specified cone shape (chapter 5, §5.4), with apex the limit. A diagram context may **mark** some of its positive-dimensional variables (`(x : A)^{inv}` in the sense of chapter 3); marked variables get invertible cone cells.

**Side condition and decision procedure.** Γ ⊢ and the substitution's well-typedness (chapter 1). The cone shape is computed, not checked: it is a function of Γ.

**Example.** Γ = (x, y : ⋆, f : x → y) with γ = (A, B, F). lim_Γ[γ] is the lax limit of the arrow F, Fun^oplax([1], B) ×_B A in ∞Cat. With f marked, it is the pseudo limit, A itself up to equivalence.

**Semantics.** In strict ω-Cat with the Gray tensor, every diagram over a finite computad has a lax limit whose universal property is an isomorphism between 𝒦(c, lim) and the ω-category of lax cones with unrestricted Gray-shaped transfors (Theorem A of `notes/limits-metatheory.md` §1). In ∞Cat as an oriented category, the arrow case holds with non-invertible comparison cells in every dimension (verified researcher answer, `notes/conjectures/oriented-lax-limits.md`). Partially lax limits must respect their marked legs coherently: m_b invertible in every dimension.

**Status.** Strict soundness for every finite computad: **proved** (Theorem A). (∞,ω) for the arrow: **proved**; for general Γ: open (B17, LMETA). Shapes: chapter 5 (B5). **Source:** `notes/limits-representables.md` §4.1–4.2; `notes/limits-metatheory.md` §1, §5.

## 6.2 The universal filler (horn form)

**Rule.** For a diagram Δ ⊢ γ : Γ with L := lim_Γ[γ], define
- Horn₀(Γ, γ; c) := Cone(Γ; c)[γ];
- for n ≥ 1, Horn_n(Γ, γ; c): the apex c, a boundary sphere ∂w of (n−1)-cells of 𝒦(c, L), and the variables of Tr_n(Γ; c)[γ] not over its boundary. The boundary variables are substituted by F(∂w), the image of ∂w under the universal cone.

Then, for Θ ⊢ σ : Horn_n(Γ, γ; c):
```
(J1)  Θ ⊢ uni^w_{Γ,n}[σ] : the n-cell of 𝒦(c, L) with boundary ∂w[σ]
(J2)  Θ ⊢ uni^y_{Γ,n}[σ] inv     for every component y of the comparison transfor E : T ⇛ F(uni^w)
```
where T is the transfor σ supplies.

**The image of a cell under the universal cone.** For w a cell of 𝒦(c, L):
- F(w)_x := w ▷ λ_x for an object generator x (an operation-case coherence over ΣD^{n−1} ∨ ΣD⁰);
- F(w)_g for a k-generator g, k ≥ 1: the operation-case coherence over ΣD^{n−1} ∨ ΣD^k substituted by (w, λ_g). Under L it is directed.

So the only cells the limit rules need from the core are operation-case coherences over two-factor wedges ΣDᵃ ∨ ΣDᵇ, which every setting of chapter 2 accepts.

**Side condition and decision procedure.** The transfor comparison variables of Tr_n over **marked** diagram generators are marked declarations (chapter 3), so σ must supply `inv` derivations for them. Over unmarked generators they are unrestricted. Everything else is a substitution check.

**Example (cone morphisms are lax).** Γ the arrow f : x → y, unmarked. A cone morphism (n = 1) from a cone T to F(w) may have a non-invertible comparison m_f. With f marked, m_f must be certified, and the collapse instance (an arbitrary 3-cell over 1_Y) is rejected unless certified.

**Semantics.** As §6.1. J2's certification: an invertible transfor in a Gray hom has invertible components and invertible comparison cells (proved for 2-categories; the (∞,ω) form is the claim behind Lemma 2.2 of chapter 3).

**Why the repair.** Mikhail's unchanged rules force every cone-morphism comparison cell, and with `uni` at every level every ambient cell of dimension ≥ 3, to be invertible (proved; `notes/limits-metatheory.md` §3). Their models are exactly the (∞,ω)-categories whose cells of dimension ≥ 3 are invertible and which have finite lax limits (§4 there). Under L, exactly one step of that argument fails: the image F(w)_g is a directed operation-case cell, not an invertible coherence.

**Status.** Design: **done** (ledger B7, B11). Agda: the horn form for n ≤ 1 over the arrow in both cores (`Lim/Horn.agda`, B15); the P/L switch on the cone-morphism shapes, with the collapse instance accepted unrestricted under L and rejected under P or when f is marked (`Lim/OverL.agda`, O1–O3); general n and Γ open (B15, LIM-F, former). **Source:** `notes/limits-metatheory.md` §2–§5; `notes/catt-lim-formalization.md`.

## 6.3 Colimits

**Rule.** A second instance of §6.1–6.2: (colim), (ucocone), and `couni` over the specified cocone and cocone-transfor shapes. In dimension 1 the cocone cell reverses the leg: for f : x → y, q_f : q_x → f ∗ q_y.

**Why a separate instance.** Full duality is not a symmetry of L: it reverses the interchanger. So colimit rules are not obtained by dualising derivations. Colimit transfors have the opposite Gray factor order (diagram index first) and need no second interchange direction.

**Status.** **Proved** consistent as a design (`notes/limits-metatheory.md` §8); shapes chapter 5, §5.4.3. **Source:** `notes/limits-representables.md` §4.3.

## 6.4 Weighted limits

**Rule (derived).** A weight is a **display**: a substitution π : Ψ → Γ with a marking of Ψ (the Grothendieck construction of the weight). Then
```
lim^{(Ψ,π)} γ := lim_{Ψ^μ}[γ ∘ π]
```

**Side condition.** None in the kernel: any π gives some partially lax limit. That π is a (co)cartesian display is needed only for the comparison theorem with weighted limits, and it is checked by the finite fibration test where one exists (B14; chapter 4 for bases).

**Example.** A comma object f ↓ g is the cospan with one leg marked. A hom object Hom_C(b, a) is the comma of ⊤ →a C ←b ⊤ with the coherent marking, and it is the full hom.

**Semantics.** Weighted limits are marked lax limits in every dimension, with the marking variance alternating by dimension (verified, `notes/limits-representables.md` §10.4). The alternation is a condition on the index (π, μ), not on the cone schema.

**Status.** **Proved** in Loubaton's model. Finite fibration test: set-valued weights over graphs **proved**; FT with one generator per pair **false** from base dimension 4 (pentagon counterexample, Agda-checked, `Fibration/PentagonCounterexample.agda`); finite presentations with auxiliary generators exist over every base (chapter 4, Proposition W). **Source:** `notes/limits-representables.md` §4.2; `notes/limits-metatheory.md` §8–9; ledger B14.

## 6.5 Derived objects

| Object | Construction | Under L |
|---|---|---|
| terminal ⊤ | lim over the empty context | — |
| product A × B | lim over two points (marking irrelevant) | — |
| pullback, equalizer | all-marked lim over the cospan, the parallel pair | — |
| comma f ↓ g | cospan, one leg marked | arrows are all cells, not only invertible ones |
| hom object Hom_C(b, a) | comma of two elements | the full hom (`notes/limits-metatheory.md` §5.4) |
| lax cotensor [⟦Θ⟧, C] | lim over Θ of the constant diagram | directly from the limit rules |
| ℕ-like object Hom_{⟦x, s : x → x⟧}(x, x) | hom object in a free object | discrete (proved) |

## 6.6 Elements and representables

**Rule (no new rule).** With ⊤ := lim_ε, an element of C is a 1-cell ⊤ → C, an arrow between elements is a 2-cell between them, and so on. Composition of elements is the ambient's composition in the hom 𝒦(⊤, C), which is reached by suspension. A functor acts on elements by whiskering, F x := x ; F, and its functoriality cells are ambient coherences. Components of α : F ⇒ G are α_x := x ▷ α.

**Example.** Example (a) of chapter 3, §3.3: the naturality cell of α at an element arrow f is the Gray cell of f ⊗ α, directed unless α is pseudo.

**Semantics.** Hom(1, C) ≃ C in ωCat. Disks are not dense; pasting diagrams Θ are, so extensionality principles must be indexed by Θ (`notes/free-objects-proofs.md` §6; chapter 9, §9.5).

**Chapter 8's points.** A point of C in chapter 8 is a nullary multimap ( ▸ C). Rule GB-shape (chapter 8, §8.8) makes it the same as an element ⊤ → C. Without GB-shape the two are unrelated (`notes/ordinary-math.md` Theorem 6.4 (a)). Likewise, GB-shape makes the lax cotensor of §6.5, defined here as a limit, equivalent to chapter 8's C/⟦Θ⟧.

**Status.** Elements elaborate to well-typed kernel terms: **Agda-checked** (`CaTTExp.Suspension`, `elements-at`; ledger C8(1)). **Source:** `notes/limits-representables.md` §5.1.

## 6.7 Open surface questions

**Q6.1. Element notation.** Same as Q0.2: `x : ⊤ → C` (kernel) or `x : C` (elaborated). The choice decides whether lax naturality at elements is visible in the notation.

**Q6.2. How diagrams are given to `lim`.**
- *Option A: a base context and a substitution,* as in the kernel. Uniform; the user writes the base context once per diagram shape and reuses it.
- *Option B: named shapes* (`pullback f g`, `equalizer f g`, `comma f g`) elaborated to bases with markings. Familiar; each name hides a marking choice, so the reader must know that `comma` marks one leg.

**Q6.3. Whether lax is the default marking.** The kernel has no default: an unmarked variable is lax.
- *Option A: lax unless marked* (kernel reading). Most general; every ordinary pullback must mark both legs.
- *Option B: pseudo unless written `lax`.* Ordinary limits need no marks; forgetting `lax` silently computes the pseudo limit, a different object. Parallel to Q3.1's M2.
