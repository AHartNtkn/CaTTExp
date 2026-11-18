# Free objects: proofs and reductions for the open items of `free-objects.md`

*2026-11-18. Works the open items C3–C6, C9 and the paper side of C7 from `notes/open-issues.md` (all from `free-objects.md` §6–§7.2 and `limits-representables.md` §5.1). Each section states what is proved, under which hypotheses, and what is left. Machine-checked parts are in `src/CaTTExp/Free/` and are listed in §7.*

Notation is that of `free-objects.md`: the ambient judgments of §1.1, Γ-diagrams `σ : Γ ⇒ C` with (D1)–(D4) of §1.2, the LIFT schema of §1.3, A1 (§2) and A2 (§3). "Invertible" is the coinductive notion (`free-objects.md` §0.4). A cell `c` is **connected** to `c'`, written `c ~ c'`, when there is an invertible cell `c → c'`.

---

## 1. Lifts of invertible cells are invertible (C4): proved

### 1.1 Statement

**Theorem 1 (reflection).** Let `R : X → Y` satisfy the LIFT schema of `free-objects.md` §1.3 (LIFT₀ and LIFTₖ₊₁ at every dimension). If `v : u → u'` is a cell of X and `R v` is invertible, then `v` is invertible.

**Corollaries.** For A1 (R = restriction along η_Γ) and for A2 (R = restriction to `(G ∘ ι, G x)`):

1. *Lifts of invertibles are invertible.* If θ is invertible then the lift `⟨θ⟩` given by LIFTₖ₊₁ is invertible: `R⟨θ⟩ ~ θ`, so `R⟨θ⟩` is invertible (Lemma I3 below), so `⟨θ⟩` is invertible by Theorem 1.
2. *Agreement on generators.* If `F, G : ⟦Γ⟧ → C` and `α : F ∘ η_Γ → G ∘ η_Γ` is an invertible cell of `Diag(Γ, C)`, then F and G are related by an invertible cell (the lift of α).
3. *Essential uniqueness of the LIFT₀ filler.* If `F : ⟦Γ⟧ → C` comes with an invertible `β' : F ∘ η_Γ ≅ σ`, then `F ~ ⟨σ⟩`: apply 2 to `β_σ⁻¹ ∘ β'`.

### 1.2 What the proof uses

The theorem is about one restriction functor R, so the proof only needs closure properties of invertible cells, all of which are known for CaTT's models:

- **(I1)** Invertible cells are closed under composition. (Fujii–Hoshino–Maehara, *Weakly invertible cells in a weak ω-category*, arXiv 2303.14907, Thm 3.3.7, for all pastings; Benjamin–Markakis, arXiv 2406.12127, in CaTT syntax.)
- **(I2)** Whiskering an invertible cell by any cell gives an invertible cell (a special case of I1 with an identity, FHM Prop. 3.2.3–3.2.4).
- **(I3)** If `c ~ c'` and `c'` is invertible then `c` is invertible (I1: `c = c' ∘ (c'⁻¹ ∘ c)` up to an invertible cell, then invariance of invertibility under `~`, FHM §3).
- **(I4)** R preserves composition and identities up to invertible cells. Here R is precomposition with η_Γ (A1) or with `(ι, x)` (A2), that is, whiskering in the ambient; the comparison cells are CaTT coherences, which are invertible (Benjamin–Markakis 2406.12127).
- **(I5)** R preserves invertible cells (whiskering, I2).

### 1.3 Proof

By coinduction. Let `W` be the class of cells `v` of X (in any hom, at any dimension) such that `R v` is invertible. Invertibility is the greatest post-fixed point of the operator Φ that sends a class S to the cells having an inverse with both witnesses in S (FHM Remark 3.1.2). So it suffices to show `W ⊆ Φ(W)`.

Let `v : u → u'` with `R v` invertible: an inverse `w' : R u' → R u` and invertible witnesses `p' : R v ∘ w' → id`, `q' : w' ∘ R v → id`.

1. LIFTₖ₊₁ applied to `u', u` and `w'` gives `w : u' → u` and an invertible `θ : R w → w'`.
2. In Y, compose the invertible cells
   `R(v ∘ w) → R v ∘ R w` (I4), then `R v ∘ θ : R v ∘ R w → R v ∘ w'` (I2), then `p'`, then `id_{R u} → R(id_u)` (I4). By I1 this is an invertible cell `c : R(v ∘ w) → R(id_u)`. (We write composites in diagrammatic order where the side does not matter.)
3. LIFTₖ₊₂ applied to the parallel pair `v ∘ w, id` of X and `c` gives `p : v ∘ w → id` and an invertible cell `R p → c`. By I3, `R p` is invertible, so `p ∈ W`.
4. Symmetrically, `q : w ∘ v → id` with `q ∈ W`.

So v has an inverse w whose witnesses p, q lie in W, i.e. `v ∈ Φ(W)`. ∎

This is the rule-level form of FHM, *ω-weak equivalences between weak ω-categories* (arXiv 2406.13240), Prop. 3.1.7 ("ω-weak equivalences reflect invertible cells"), whose definition of ω-weak equivalence (essential surjectivity on every hom) is exactly the LIFT schema.

**Machine check (§7).** `src/CaTTExp/Free/Reflect.agda` proves Theorem 1 and Corollary 1 by guarded corecursion, for an abstract tower of hom-sets with composition, identities and whiskering, and with I1, I2 and I4 taken as record arguments; I3 is derived from them and I5 is not needed (no postulates). See §7.

---

## 2. Decomposition of diagrams (C3)

The statement is

```
Diag((Γ, x : A), C)  ≃  Diag(Γ, C) ×_{Diag(∂Dⁿ, C)} Diag(Dⁿ, C)        (Dec)
```

where `n = dim A + 1`, the right map is restriction to the boundary, and the left map is `τ_A^* : Diag(Γ, C) → Diag(∂Dⁿ, C)`, evaluation of the sphere `A = (a →_B b)` (D1). There are two halves: a **strict** decomposition (an isomorphism onto the strict pullback) and the comparison **strict pullback ≃ pseudo pullback**.

### 2.1 The strict decomposition holds at every dimension, given the cylinders

Take primitive elements (`free-objects.md` §1.2), so a k-cell of `Diag(Γ, C)` is a Γ ⊗ Dᵏ-family of cells of C, that is, a substitution into the context `Γ ⊗ Dᵏ`. Take `Γ ⊗ D¹ := Γ↑Var(Γ)` as built in `conjectures/naturality-arbitrary-depth.md` §3 ("Consequence (any context)"), and `Γ ⊗ Dᵏ⁺¹ := (Γ ⊗ Dᵏ)↑(cylinder variables)` (`free-objects.md` §7.1 item 2).

**Lemma 2 (cylinders commute with extension).** For every context Γ and type `Γ ⊢ A` of dimension n − 1, with `τ_A : Γ → ∂Dⁿ` the substitution classifying A,

```
(Γ, x : A)↑  =  Γ↑ , x⁻ : A⁻[τ_A↑] , x⁺ : A⁺[τ_A↑] , x↑ : (a_d → b_d)[τ_A↑, x⁻, x⁺]
```

as an equality of contexts, where `d` is the top variable of Dⁿ, `A^± = (∂Dⁿ-sphere)[in^±]`, and `τ_A↑ : Γ↑ → (∂Dⁿ)↑` is the cylinder of τ_A (`naturality-arbitrary-depth.md` Lemma 2). In words: `(Γ, x : A)↑` is the pushout of `Γ↑ ← (∂Dⁿ)↑ → (Dⁿ)↑` along `τ_A↑`, in the syntactic category.

*Proof.* By the definition of `Γ↑X` by recursion on the length of Γ, the types of x⁻, x⁺, x↑ are `A[in⁻]`, `A[in⁺]` and `a_x → b_x`. The factors of `a_x`, `b_x` are `w↑` for the iterated boundaries w of x, which are the boundary terms of A, i.e. `s[τ_A]` for the sphere variables s of ∂Dⁿ. By the definition of `γ↑` (`s↑ ↦ (s[τ_A])↑`), `(s[τ_A])↑ = s↑[τ_A↑]`; and binary composites commute with substitution. So `a_x = a_d[τ_A↑, x⁻, x⁺]` and likewise for b. Omitted factors agree because `Var(s) ∩ Y = ∅` iff `Var(s[τ_A]) ∩ Y = ∅` when Y is all variables (both are always non-empty). ∎

**Theorem 3 (strict decomposition).** For every k, substitutions `Δ ⊢ ρ : (Γ, x : A) ⊗ Dᵏ` are in bijection with pairs `(ρ_Γ, ρ_D)` of substitutions into `Γ ⊗ Dᵏ` and `Dⁿ ⊗ Dᵏ` that agree on `∂Dⁿ ⊗ Dᵏ` (ρ_D restricted to ∂Dⁿ ⊗ Dᵏ equals `(τ_A ⊗ Dᵏ) ∘ ρ_Γ`). The bijection commutes with sources and targets, so (Dec) holds as an isomorphism of globular sets onto the strict pullback.

*Proof.* Lemma 2, iterated k times (each iteration of ↑ is again the recursion of Lemma 2, applied to `Γ ⊗ Dʲ` with the cylinder variables of the new generators), shows `(Γ, x) ⊗ Dᵏ` is `Γ ⊗ Dᵏ` extended by the generators `x ⊗ e` (e ranging over the cells of Dᵏ) with types pulled back along `τ_A ⊗ Dᵏ` from those of `d ⊗ e` in `Dⁿ ⊗ Dᵏ`. A substitution into a context extension is a substitution into the base plus one term per new variable of the substituted type (inversion of the substitution rule). Sources and targets of k-cells of Diag are restrictions along the end inclusions `Γ ⊗ Dᵏ⁻¹ ⇉ Γ ⊗ Dᵏ`, which are defined by the same recursion and so commute with the decomposition. ∎

**Status of the hypothesis.** The only input is the existence of the cylinder contexts, i.e. Conjecture N (C1) for the coherences occurring in the boundary terms of Γ's types. In particular Theorem 3 is **unconditional** for:

- contexts whose variables all have variable boundaries (globular contexts, the computads of globular sets, including all pasting contexts and the loop): there a_x and b_x use only variable cylinders and binary composites, so no K is needed;
- every k ≤ 1 context whose boundary terms have depth ≤ 1 in the BMOSV sense (arXiv 2501.11620, Thm 3.1).

**Machine check (§7).** `src/CaTTExp/Free/Cylinder.agda` defines `Γ↑` for globular contexts as a function on syntax, checks the resulting contexts (lax square, cylinder on the 2-disc, the loop, the 2-loop, the composable pair) with the certified checker, and checks Lemma 2 on instances (the full three-variable extension) by `refl`; the general statement is the paper proof above.

**What Theorem 3 does not cover.** It is a statement about cells of Diag and their boundaries. The *composition* of Diag (vertical composition of lax transformations, and their higher analogues) is not yet defined in the notes (it belongs to D3 of `free-objects.md` §1.2). Whatever it is, if it is given by co-operations between cylinder contexts built by the same recursion (as for Mikhail's `gray` rules), it commutes with (Dec) by the same argument. This is recorded as part of C3's remaining work.

### 2.2 Strict pullback versus pseudo pullback

`free-objects.md` §3.2 states ATTACH with the pseudo pullback. The strict pullback includes into it. The inclusion is an equivalence when the boundary restriction `r : Diag(Dⁿ, C) → Diag(∂Dⁿ, C)` is an **ω-equifibration** (Fujii–Hoshino–Maehara, arXiv 2511.09849: lifting of invertible cells along r, at every level).

**Lemma 4 (transport, level 0).** Given a cell `y : a' → b'` of C and an invertible cylinder `φ : (a, b) ⇒ (a', b')` between spheres (a 1-cell of `Diag(∂Dⁿ, C)` all of whose components and naturality cells are invertible), there is `y_φ : a → b` and a cylinder relating y_φ to y over φ.

*Proof.* Induction on n. For n = 1, `y_φ := φ_a ∗₀ y ∗₀ φ_b⁻¹`, and the cylinder cell is a unitor/associator composite with the witness `φ_b⁻¹ ∗₀ φ_b → id`. For n > 1, the top components of φ are invertible n-cells with whiskered boundaries; compose `y` on both sides with them and their inverses, transported first to the correct boundary by the induction hypothesis one dimension down. ∎

So the comparison holds at level 0 of `Diag` (objects), which is all that A2's LIFT₀ uses. At higher levels it needs Lemma 4 for `Dⁿ ⊗ Dᵏ`-cylinders; this is the statement "r is an ω-equifibration", open in the weak setting (FHM 2511.09849 prove that `X → 1` is an ω-equifibration for every X, but not this case). It holds in the strict model (§4.1).

### 2.3 Remaining for C3

- (C3a) Composition of Diag and its compatibility with (Dec): blocked on D3 (`free-objects.md` §1.2) being fixed; adjacent work: the vertical composite of two lax squares as a substitution, for the globular case.
- (C3b) Lemma 4 at all levels (r is an ω-equifibration), syntactically.
- (C3c) Higher-depth cylinders: C1.

---

## 3. From A2's rules to A1's universal property (paper side of C7)

`free-objects.md` §3.3 derives A1's universal property by chaining equivalences. At dimension 0 the chain can be written as an explicit construction, and doing so exposes one extra ingredient.

**Construction (A1's LIFT₀ from A2).** By induction on Γ. For `Γ = ∅`, `⟦∅⟧ = 0`, and LIFT₀ for 0 gives `! : 0 → C`. For `(Γ, x : A)`, a diagram is `(σ, y)` with `σ : Γ ⇒ C` and `y : A[σ]`.

1. By induction, `F := ⟨σ⟩ : ⟦Γ⟧ → C` and an invertible `β : F ∘ η_Γ ≅ σ` in `Diag(Γ, C)`.
2. The sphere of ATTACH is `(a, b) := A[η_Γ]`, a sphere of `⟦Γ⟧`. We need `y' : F a → F b`.
3. Evaluate β on the boundary terms of A: `β_A : A[F ∘ η_Γ] ⇒ A[σ]`, an invertible cylinder between spheres. **This is the action of a 1-cell of Diag on terms, i.e. the naturality terms `t↑` of the boundary terms t of A.** For variable boundaries it is a component of β; for composite boundaries it is the naturality construction of `naturality-arbitrary-depth.md` §3.
4. Also `F a ~ a[F ∘ η_Γ]`: F is an ambient functor, so it preserves CaTT operations up to an invertible coherence (D2).
5. Transport `y` along the composite invertible cylinder `(F a, F b) ⇒ A[σ]` (Lemma 4) to get `y' : F a → F b`.
6. ATTACH's LIFT₀ gives `⟨F, y'⟩ : ⟦Γ, x : A⟧ → C`, with `β' : ⟨F, y'⟩ ∘ ι ≅ F` and `β'_x` relating `⟨F, y'⟩ x` to y'.
7. The new β is `(β ∘ (β' η_Γ), β'_x ∘ (transport cylinder of step 5))`. It is invertible by I1.

**All dimensions, as a chain of equivalences.** `src/CaTTExp/Free/A2toA1.agda` proves, by induction on the context, that the chain of `free-objects.md` §3.3 gives A1's LIFT schema at every dimension, from three explicit hypotheses: A2's LIFT (for 0 and for each ATTACH), the decomposition map being an equivalence (C3), and pullback stability (an equivalence `R_Γ` induces an equivalence on the pullbacks; this is where the boundary restriction must be an ω-equifibration, C3b). The content proved is that LIFT-equivalences compose (coinductively) and that the induction goes through. Pullback stability remains the open hypothesis.

**Finding.** Even dimension 0 of the derivation needs step 3, the action of β on the boundary terms of A. So "A2 gives A1's LIFT₀" depends on Conjecture N for the coherences in Γ's types, not just on (Dec) at higher dimensions as `free-objects.md` §3.3 suggests. It is unconditional for globular Γ (step 3 is then a list of components) and, at each depth, wherever N is known.

---

## 4. Weak model of ATTACH (C6): answered, with one gap recorded

### 4.1 Strict model: fully justified

- The folk model structure on strict ω-categories (Lafont–Métayer–Worytkiewicz 2010) has generating cofibrations the boundary inclusions `∂Dⁿ → Dⁿ`, and every object is fibrant.
- It is monoidal for the (lax) Gray tensor product (Ara–Lucas, *The folk model category structure on strict ω-categories is monoidal*, arXiv 1909.13564): the pushout-product of cofibrations is a cofibration, trivial if either factor is.
- By adjunction, for a cofibration `i : A → B` and any D, `[B, D]_lax → [A, D]_lax` is a fibration, trivial if i is.

So `C[x : a → b]`, the strict pushout along `∂Dⁿ → Dⁿ`, is a homotopy pushout, and `[C[x], D] → [C, D] ×_{[∂Dⁿ, D]} [Dⁿ, D]` is an *isomorphism* onto a strict pullback along a fibration, hence a homotopy pullback. This validates ATTACH's universal property in the strict model, at every dimension, under both P (cartesian homs: the folk structure is also cartesian monoidal) and L (Gray homs). It also proves §2.2's equifibration statement in the strict model.

### 4.2 (∞,ω)-categorical model: justified

In Loubaton's (∞,ω)-categories (arXiv 2307.11931, 2406.05425), a presentable ∞-category, pushouts exist and are homotopy-invariant by construction; ATTACH is the pushout along `∂Dⁿ → Dⁿ`. In a model-categorical presentation by complicial sets (Verity; Ozornova–Rovelli, arXiv 2207.08504), cofibrations are monomorphisms, so every object is cofibrant, the model structure is left proper, and the strict pushout along the boundary inclusion is already a homotopy pushout. The universal property is then the statement that `Fun(−, D)` sends pushouts to pullbacks, which holds for the Gray-enriched internal homs (Campion, arXiv 2311.00205; Loubaton) as they are right adjoints.

### 4.3 Grothendieck–Maltsiniotis / algebraic weak ω-categories: no model structure in the literature

The literature search (2026-11-18) found **no** model structure on algebraic weak ω-categories with boundary inclusions as cofibrations. The closest results are:

- Fujii–Hoshino–Maehara, arXiv 2406.13240: ω-weak equivalences between weak ω-categories, with 2-out-of-3 and 2-out-of-6; no model structure.
- Fujii–Hoshino–Maehara, arXiv 2511.09849: ω-equifibrations, characterised by a right lifting property against an explicit set J; for strict ω-categories they are the folk fibrations; every weak ω-category is fibrant. The paper describes a weak analogue of the folk model structure as future work.
- BMOSV (arXiv 2501.11620) note that a path-object construction (which Conjecture N would provide) is the long-sought missing piece of such a model structure.

What *is* available in the algebraic setting is enough for the free case: for C free on a computad, the pushout `C[x : a → b]` is the free weak ω-category on the extended computad (Dean–Finster–Markakis–Reutter–Vicary, *Computads for weak ω-categories as an inductive type*), which is what ⟦Γ⟧ uses. For non-free C, the homotopy pushout is defined by first resolving C by a computad.

**Conclusion.** ATTACH has a fully justified semantics in the strict model and in (∞,ω)-categories. In algebraic weak ω-categories it is justified on free objects; for arbitrary objects, it needs the weak folk model structure, which is open (and to which C1 contributes the path object). C6 is closed as a question ("which model structure"); the algebraic-weak gap is folded into E11 (interpreting the ambient in weak ω-categories), where it belongs.

---

## 5. Conservativity (C5): strict half proved under P, full statement reduced

### 5.1 Statement

For a closed CaTT context Γ, and closed derivations (in the empty ambient context, so no hypothesis mentions cells of ⟦Γ⟧):

- **(C5-ess)** every closed k-cell e of ⟦Γ⟧ satisfies `e ~ t[η_Γ]` for some CaTT term `Γ ⊢ t`;
- **(C5-full)** for parallel CaTT terms t, u over Γ, there is a closed cell `t[η_Γ] → u[η_Γ]` iff there is a CaTT term `Γ ⊢ w : t → u` (up to `~`).

The "if" direction of C5-full is immediate: `w[η_Γ]`.

### 5.2 The weak statement reduces to two known results and E11

Suppose the ambient theory with FREE/LIFT has a sound interpretation `⟦−⟧_M` in algebraic weak ω-categories in which ⟦Γ⟧ is the free weak ω-category `F(Γ)` on the computad Γ and η_Γ the generic diagram. Then:

- cells of `F(Γ)` are exactly CaTT terms over Γ: Benjamin–Markakis–Sarti (arXiv 2405.00398) identify CaTT contexts with finite computads, and Dean–Finster–Markakis–Reutter–Vicary give the cells of the free weak ω-category on a computad as syntactic terms;
- soundness sends a closed cell `c : t[η] → u[η]` to a cell of F(Γ) from t to u, hence to a CaTT term.

This gives C5-full, and C5-ess similarly. The hypothesis is exactly **E11** (interpreting the ambient type theory in weak ω-categories) plus checking that LIFT holds there for free objects. So the weak half of C5 is blocked on E11.

### 5.3 Strict half: proved under P

Under P (pseudo ambient), interpret the ambient in the strict ω-category of strict ω-categories with **cartesian** internal homs (strict ω-Cat is cartesian closed, hence self-enriched, hence a strict (ω+1)-category). This is a model of CaTT. Interpret ⟦Γ⟧ as the free strict ω-category `F_s(Γ)` on the polygraph Γ. Under P, k-cells of `Diag(Γ, C)` are maps out of the marked cylinders `(Γ ⊗ Dᵏ)^μ`, which present `Γ × Dᵏ` (Theorem (P), `conjectures/gray-vs-cartesian.md`), so `Diag(Γ, C) ≅ [F_s(Γ), C]_cart` and LIFT holds as an isomorphism. Soundness gives:

**Proposition 5.** Under P, if a closed cell `t[η] → u[η]` is derivable, then t and u are equal in `F_s(Γ)`.

This is the non-collapse half: for instance, no closed cell relates two distinct parallel generators. It does not give C5-full (strict equality in `F_s(Γ)` is coarser than connection by CaTT cells). Under L, the corresponding strict model is Gray-enriched rather than a strict ω-category; LCORE's strict AM-model validation (E2) is the natural place to add ⟦Γ⟧.

### 5.4 Remaining for C5

- (C5a) Weak half: blocked on E11.
- (C5b) Strict half under L: needs the strict Gray model of the L core (E2 adjacent).

---

## 6. Density (C9): answered negatively for disks; Θ is the right index

**Question** (`limits-representables.md` §5.1, `internal-hom.md` §5.5): is a transformation `F ⇒ G : B → C` determined by its components and naturality cells at the disks `Dⁿ → B`, for arbitrary B?

**Answer.**

1. **Uniqueness holds strictly.** In the strict model, `B ⊗ D¹` is generated as an ω-category by `x ⊗ 0`, `x ⊗ 1`, `x ⊗ I` for cells x of B (Steiner / Ara–Maltsiniotis description of the Gray tensor by elementary tensors), so a lax transformation is determined by its values at disks.
2. **Existence fails: the disks are not dense.** Counterexample, already 2-categorical: B = the walking composable pair `0 →f 1 →g 2` (with its composite `gf`), C any 2-category with a non-trivial 2-cell. Disk-indexed data assigns components α₀, α₁, α₂ and naturality cells α_f, α_g, α_{gf} independently. A lax transformation also requires `α_{gf}` to equal the pasting of α_f and α_g. Choosing α_{gf} different from that pasting gives disk-indexed data that is not a transformation. So the restriction map from transformations to disk-indexed data is injective but not surjective: the disks are not dense. The missing conditions are indexed by the pasting diagram `[2]`, not a disk.
3. **Pasting diagrams are dense.** Θ (Joyal's category of pasting diagrams, i.e. the ⟦P⟧ for P a pasting context) is dense in strict ω-categories (Berger's nerve theorem), and in (∞,ω)-categories by construction (Loubaton defines them as Θ-presheaves satisfying Segal and completeness conditions; for finite n, Rezk's Θₙ-spaces).

**Consequence for the design.** The right extensionality principle is: *a transformation `B → [D¹, C]` is the same as a coherent family of transformations out of the pasting-diagram elements `⟦P⟧ → B`*, i.e. B is the colimit of its Θ-elements. For representable `B = ⟦Θ⟧` this is the cylinder rule (cyl-Λ) of `internal-hom.md` §5.5a, already in the design. For arbitrary B it is an object-indexed colimit principle, which is F5. So the question C9 is closed; the remaining work (stating the Θ-density rule) moves to F5 as a test case.

---

## 6a. The limits-notes Agda targets C8 (3), (4), (6)

**C8(3): cone contexts over pasting-scheme diagrams.** Done by B5: `src/CaTTExp/Cones.agda` builds the specified cone `cone Γ` as a total function for every globular Γ (pasting schemes included) and `ConesExamples.agda` certifies it on D⁰–D⁴, loops, parallel pairs, the cospan and the composable pair (`specified-cones.md` §7). Over an arrow it gives `p_f : p_y → p_x ∗ f` up to a unit, which is Mikhail's Thm 3.3 orientation (`conventions.md` §5). It agrees with the collapsed cylinder: the cylinder `Γ↑Var(Γ)` of `Free/Cylinder.agda` with every x⁻ sent to the iterated identity on c.

**C8(4): orientation of `laxcolim(const 1)`.** Settled by Loubaton, Example 4.2.3.12 (already verified, `limits-representables.md` §10.3): `laxcolim_{A♭} 1 ≃ A` with no opposite, for every (∞,ω)-category A. The strict computation agrees: with the Leibniz formula of `conventions.md` §2, a generator a ⊗ i of A ⊗ D¹ has `∂^α(a ⊗ i) = (∂^α a ⊗ i) ∪ (a ⊗ ∂^{±α} i)`; in a lax cocone over the constant diagram at 1 the cells `a ⊗ 0` go to identities, so the cocone cell of a runs from the cocone cells of `∂⁻a` to those of `∂⁺a`, in every dimension. A strict check on examples would add nothing, so this target is closed by the literature and this computation.

**C8(6): cells over a graph are determined by their path.** This is F2: the canonical lift to the chain Θ_k (placing each edge occurrence at its position along the path, so repeated edges are handled) is proved on paper in `ordinary-math.md` §3 and implemented as a certified tactic in `src/CaTTExp/GraphFiller.agda`, with examples (loops traversed several times, cells in dimensions 2–4, a two-object graph, negative checks) in `GraphFillerExamples.agda`. An independent implementation in this thread agreed on overlapping examples (loop three times, path f·g·f) and was dropped as a duplicate. What remains is totality in Agda, which is F2a.

## 7. Machine-checked parts

Under `src/CaTTExp/Free/`, typechecked locally with Agda 2.6.3 (`--safe`, plus `--guardedness` for `Reflect`); no postulates. *Status:* `Reflect`, `Builders`, `Cylinder`, `LeftUnitorDepth2` reviewed and merged (PR #28). `A2toA1` and `AssociatorDepth2` submitted for review.

- `Reflect.agda` (C4): Theorem 1 (`reflect`) and Corollary 1 (`lift-inv`) of §1, by guarded corecursion, for an abstract tower of hom-sets with composition, identities and whiskering. The hypotheses I1, I2 and I4 are record arguments; I3 is derived (`conn-inv`). A terminal-tower instance shows the hypotheses are jointly satisfiable.
- `Builders.agda`: unbiased composites over Batanin trees, binary composites and whiskerings `u ∗ₖ v` of any dimensions, identities, and `certify`, which turns a successful run of the certified checker into a typing derivation at typechecking time.
- `Cylinder.agda` (C3, C7): `cyl Γ = Γ↑Var(Γ)` for globular contexts, as a function on syntax. Certified well formed for D⁰, D¹ (the lax square), D², the composable pair, the loop and a 2-loop. Lemma 2 checked by `refl` on the loop, the 2-loop and the composable pair, comparing the whole extension (x⁻, x⁺, x↑) with the disc cylinder's pulled back along τ_A↑; the general statement is proved on paper in §2.1 only.
- `LeftUnitorDepth2.agda` (C7, C1): the depth-2 naturality 3-cell of the left unitor (`naturality-arbitrary-depth.md` §6), built by the sliding argument and certified: `K-λ-wf : Sq ⊢tm K-λ ∶ L → R`. Also certified: the depth-1 naturality term `K_comp` for binary composition, and ι for identities. Negative checks show the cell has the claimed direction and is not a single coherence over the lax square.
- `A2toA1.agda` (C7): LIFT-equivalences compose (`Equiv-∘`, guarded corecursion, with "functors preserve invertibles" as a record argument); A1's LIFT for every context from A2's, by induction (`A1-lift`), under the hypotheses listed in §3.
- `AssociatorDepth2.agda` (C7, C1/C1b): the depth-2 naturality 3-cell of the associator over three arrows with every variable selected, built by the sliding argument (distribute; slide f↑, g↑, h↑ by naturality of the associator in its top argument; compare four segments along single paths of the ladder, the last being the pentagon). Every coherence it uses is certified at typecheck time in its own pasting context. The assembled cell has about 3.6·10⁵ syntax nodes, which exhausts Agda's typecheck-time normaliser, so it is certified by running the same checker compiled (`tools/run/RunAssoc.agda`, with a negative and a consistency control); this trusts the MAlonzo/GHC compilation in addition to Agda.

## References

- Ara, Lucas, *The folk model category structure on strict ω-categories is monoidal*, arXiv 1909.13564.
- Benjamin, Markakis, *Invertible cells in ω-categories*, arXiv 2406.12127.
- Benjamin, Markakis, Sarti, *CaTT contexts are finite computads*, arXiv 2405.00398.
- Benjamin, Markakis, Offord, Sarti, Vicary, *Naturality for higher-dimensional path types*, arXiv 2501.11620.
- Berger, *A cellular nerve for higher categories*, Adv. Math. 2002.
- Campion, *The Gray tensor product of (∞,n)-categories*, arXiv 2311.00205.
- Dean, Finster, Markakis, Reutter, Vicary, *Computads for weak ω-categories as an inductive type*, Adv. Math. 2024.
- Fujii, Hoshino, Maehara, *Weakly invertible cells in a weak ω-category*, arXiv 2303.14907.
- Fujii, Hoshino, Maehara, *ω-weak equivalences between weak ω-categories*, arXiv 2406.13240.
- Fujii, Hoshino, Maehara, *ω-equifibrations between strict and weak ω-categories*, arXiv 2511.09849.
- Lafont, Métayer, Worytkiewicz, *A folk model structure on omega-cat*, Adv. Math. 2010.
- Loubaton, arXiv 2307.11931 and 2406.05425.
- Ozornova, Rovelli, *The complicial model of (∞,ω)-categories*, arXiv 2207.08504.
