# Chapter 3. Invertibility markings

The lax core makes every interchanger directed. Pseudo transformations, ordinary ω-categories and groupoids are recovered by **marks**. For ordinary ω-categories the mark is `ord`, which makes inner letters trivial and acts through the side condition (rule (COH-ord)). With every object marked `ord`, uniform L derives exactly two-tier L (§3.6; ledger S16(b)). Marks are proof-irrelevant judgments on terms and object variables, propagated by syntax-directed rules. Marks add no new definitional equalities. They add only the inverse term formers that ICaTT has, without its equations.

**Pseudo = L + marks.** P (plain CaTT with pseudo transformations) has exactly the models of L in which every mixed cell of every dimension is invertible (Theorem 3.5.1). So the kernel does not need a separate pseudo core.

The rules below are stated over the **two-tier** unfolding U(Γ) = Θ₁ ⊗ … ⊗ Θₙ of chapter 2, §2.5, which is where they are proved and machine-checked. Their restatement over F_{V+S}(Γ), read through the Gray projection, is §3.6.

## 3.1 Notation

- For a term t whose iterated 0-source and 0-target are objects a and b, **hd(t) := dim t − 1** is its dimension in the hom 𝒦(a, b).
- A generator of U(Γ) is g = x₁ ⊗ … ⊗ xₙ with xᵢ a cell of Θᵢ of dimension dᵢ. It is **mixed** if at least two dᵢ ≥ 1.
- For a substitution γ out of Γ, the **Gray cell** g[γ] is the operation-case coherence over ΣD^{d₁} ∨ … ∨ ΣD^{dₙ} with its canonical ∂⁻ → ∂⁺ type, substituted by (x₁[γ], …, xₙ[γ]). For one positive factor it is a whiskering; for a mixed g it is an interchanger.
- "Before" means earlier in execution order: in g, xᵢ is before xⱼ when i < j.

## 3.2 Judgments and marked declarations

**Rule.**
```
Γ ⊢ t inv        t is invertible
Γ ⊢ t ps         t is pseudo: for every cell y with hd(y) ≥ 1 composed before t, the Gray cell y ⊗ t is invertible
Γ ⊢ t ps*        t is recursively pseudo: hd(t) = 0, or t ps and (hd(t) ≥ 2 ⇒ both boundaries ps*)
Γ ⊢ C grpd_k     the object variable C has only invertible cells from hom-dimension k up (k ≥ 1)
```

Declarations may carry marks: `(x : A)^inv`, `(x : A)^ps`, `(x : A)^{ps*}` (the ps mark on x with ps* on the boundary terms of A), and for object variables `(C : ⋆)^{grpd_k}`. A marked variable has its mark:

```
(x : A)^m ∈ Γ
────────────── (mark)
  Γ ⊢ x m
```

A substitution Δ ⊢ γ : Γ must preserve marks: Δ ⊢ x[γ] m for every marked x. A `grpd_k` variable must go to an object **variable** marked `grpd_k′` with k′ ≤ k, because (OBJ-k) reads the mark off the object variable and constants carry no marks.

**Side condition and decision procedure.** All judgments are decided by the syntax-directed rules of §3.3: the generators of U(Γ) are finite and marks are finite data.

**Status.** **Agda-checked**: the rules (`Gray/Marks.agda`), substitution preserves marks (`Gray/MarksSubst.agda`), fuel monotone and stable above dim t given "a derivable coh is at least as high as its pasting context" (`Gray/MarksFuel.agda`), the latter proved for L (`Gray/CohDim.agda`). **Source:** `notes/invertibility-markings.md` §1.2–1.3; ledger E4.

## 3.3 Rules

### Destructors (ICaTT's, without equations)

```
Γ ⊢ t inv    Γ ⊢ t : u → v
──────────────────────────────────────────────────────── (DES)
Γ ⊢ t⁻ˡ : v → u      Γ ⊢ t⁻ʳ : v → u
Γ ⊢ λ_t : t⁻ˡ ; t → id_v      Γ ⊢ ρ_t : t ; t⁻ʳ → id_u
Γ ⊢ λ_t inv      Γ ⊢ ρ_t inv
Γ ⊢ t⁻ˡ inv      Γ ⊢ t⁻ʳ inv                                              (DES-inv)
```

There is no β or η, so ICaTT's `can`/`rec` equations have nothing to say. Since `inv` is a judgment, the destructors depend on t only.

(DES-inv) was missing until 2026-11-22: without it no rule makes an inverse invertible, so composites involving t⁻ˡ were not derivably inv (`notes/marking-alternatives.md` §3.2). It is sound (t⁻ˡ has inverse t) and syntax-directed. Agda: with the destructors, ledger E4.

### Propagation

Below, `coh_{Γ,A}[γ]` is an L-coherence and g ranges over the generators of U(Γ) of top dimension D = dim U(Γ).

```
(COH-inv)   coherence case                                         ⇒  coh_{Γ,A}[γ] inv
(OP-inv)    operation case, g[γ] inv for every top g                ⇒  coh_{Γ,A}[γ] inv
(OP-ps)     operation case, and for every top g:
              g[γ] inv, or some xⱼ in g has dⱼ ≥ 1 and xⱼ[γ] ps*     ⇒  coh_{Γ,A}[γ] ps
(INV-fac)   some dᵢ ≥ 1 with xᵢ[γ] inv                               ⇒  g[γ] inv
(INV-obj)   all dᵢ = 0 and every xᵢ[γ] inv                           ⇒  g[γ] inv
(PS-fac)    some dⱼ ≥ 1 with xⱼ[γ] ps*, and some i < j with dᵢ ≥ 1    ⇒  g[γ] inv
(INV⇒PS)    t inv and hd(t) ≥ 1                                      ⇒  t ps
(OBJ-k)     the 0-target of t is C, C grpd_k, hd(t) ≥ k              ⇒  t inv
```

Pseudo is **one-sided**: (PS-fac) needs the *later* factor to be pseudo. (INV-fac) and (INV-obj) are symmetric.

**Example (a): naturality of a pseudo transformation.** α : F ⇒ G : B → C and an element arrow f : x → y of B, f before α. The naturality cell is the Gray cell of f ⊗ α, from α_x ; Gf to Ff ; α_y.
- α unmarked: no rule applies. The cell is directed, and no term has the reverse type (chapter 2, §2.4).
- α marked ps: (PS-fac) with j = α, i = f. The cell is inv, so `(f ⊗ α)⁻ˡ` is a term. That is pseudo naturality, with one mark.
- f marked inv, α unmarked: (INV-fac). The lax naturality cell at an invertible arrow is invertible.

**Example (b): one-sidedness.** α : F ⇒ G : B → C marked ps and β : H ⇒ K : C → D unmarked. The interchanger of α (earlier) with β (later) is not derivably invertible, because (PS-fac) needs β pseudo. This is correct: with B = ⊤, α ⊗ β is β's naturality cell at the arrow α of C, which is not invertible for a lax β.

**Example (c): composites stay pseudo.** For α, α′ marked ps in 𝒦(B, C): the vertical composite α ; α′ is ps by (OP-ps); the identity on F is ps by (COH-inv) and (INV⇒PS); whiskerings on either side are ps by (OP-ps). So pseudo transformations are closed under every composition, with marks only on the declared ones.

**Example (d): a ring object.** R with + and ·, and its equation witnesses as 2-cells between maps R³ → R. Declaring `(R : ⋆)^{grpd_1}` makes every equation witness, every naturality cell landing in a hom 𝒦(X, R) and every higher cell into R invertible by (OBJ-k), with no per-witness marks.

**Semantics.** The models are oriented (∞,ω)-categories with a choice of invertibility data for each invertible cell (to interpret the destructors), and morphisms preserving the choices. `t inv` means ⟦t⟧ is invertible; `t ps` means ⟦y⟧ ⊗ ⟦t⟧ is invertible for every positive-dimensional y composed before t; `C grpd_k` means every cell of hom-dimension ≥ k of every 𝒦(X, C) is invertible, i.e. C lies in Cat_{k−1}.

- Lemma 2.1 (invertible factor), via Dᵐ ⊗ Eᵏ ≃ Dᵐ ⊗ Dᵏ⁻¹, gives (INV-fac), (INV-obj) and (INV⇒PS).
- Lemma 2.2 (pseudo factor), via C1′ of the gray-vs-cartesian theorem, gives (PS-fac).
- Lemma 2.3 (pasting composites of invertible cells are invertible) gives (OP-inv) and (OP-ps).
- (OBJ-k): Campion's Gray tensor on Cat_n is the reflection τ_n of the one on Cat_ω.
- The strict model (strict ω-Cat with the Ara–Maltsiniotis tensor and strict inverses) is covered by the same arguments with functoriality in place of localisation.

**Non-collapse.** No rule makes an unmarked interchanger invertible: every derivation of `inv` ends in (COH-inv), a mark, or a rule with a marked premise. So L with marks is still strictly more general than P.

**Status.** Soundness of every rule: **proved** (`notes/invertibility-markings.md` §2, Lemmas 2.1–2.3). The rules and the §1.6 examples: **Agda-checked** by evaluation (`Gray/MarksExamples.agda`). The destructors (DES) are **not yet in Agda** (ledger E4, owner MARK). Which (∞,ω) notion makes Eᵏ ≃ Dᵏ⁻¹ hold is `notes/semantics-gaps.md` (S3)–(S4), ledger E11. **Source:** `notes/invertibility-markings.md` §1–2.

## 3.4 Recursive pseudo

ps* is the right notion of "pseudo" in the sense of P. An r-cell of Fun^lax(B, C) is strong iff its adjunct Dʳ ⊗ B → C inverts **all** mixed cells, including those on boundary faces (C1″, verified). A pseudo mark on a 2-cell (hd 1) is already ps*. For modifications and higher, the mark is needed on every cell: there is a modification between two strong transformations that is not strong (B = D¹, C = D³), so ps* on the boundary does not give ps on the cell.

(PS-fac) and (OP-ps) take ps* premises. The version with top-only ps premises would need Conjecture 2.2′ (a cell of Fun^lax(X, D) is invertible iff its adjunct inverts the cells x ⊗ top), which is open and used by no rule.

**Status.** C1″ **proved** (verified researcher answer, `notes/conjectures/gray-vs-cartesian.md`). Conjecture 2.2′ **open** (not on any critical path). **Source:** `notes/invertibility-markings.md` §1.3, §2.

## 3.5 Pseudo = L + marks

**Theorem 3.5.1 (semantic half).** The ∞-category of oriented (∞,ω)-categories whose composition maps invert all mixed cells is equivalent to the ∞-category of Cat_ω-enriched ∞-categories, by change of base along the comparison A ⊗ B → A × B.

*Proof outline.* Precomposition with A₁ ⊗ … ⊗ Aₙ → A₁ × … × Aₙ is a monomorphism on mapping spaces whose image is the maps inverting all mixed cells (induction with Gray and cartesian currying, and Fun → Fun^lax an inclusion, Gepner–Heine Thm 4.1.9). So the cartesian ∞-operad is a sub-∞-operad of the Gray one, and enriched categories are algebras (Gepner–Haugseng).

**Conjecture 3.5.2 (syntactic half).** There is a translation of CaTT terms into L⁺ (L with every variable of hom-dimension ≥ 1 marked ps) that preserves types, commutes with substitution up to an invertible cell, and is essentially surjective up to invertible cells. Composites translate to the ∂⁻-layering, and CaTT's interchanger to the inverse of L's (available by (PS-fac)). The missing step is a relative coherence lemma: two parallel L⁺ terms whose strict images agree after collapsing U(Γ) → Θ₁ × … × Θₙ are connected by an invertible L⁺ term.

**Status.** Theorem 3.5.1 **proved**. Conjecture 3.5.2 **open**: composites and the interchanger done, the general coherence case reduced to relative coherence (ledger E5). **Source:** `notes/invertibility-markings.md` §3.

## 3.6 Marks over the uniform core

The rules of §3.3 are stated over U(Γ). Over V + S (chapter 2, §2.3) they are restated by reading the **designated lift** c of a coherence (§2.2) through the Gray projection π. Every letter of c is **outer** (π sends it to a whiskered Gray generator) or **inner** (π sends it to an identity). The cases are:
- the **Gray operation case**, π(c) = τ_Γ;
- the **Gray coherence case**, π(c) an identity, which is either the coherence case (⟦t⟧ = ⟦u⟧ in F_{V+S}(Γ)) or an **inner coherence** (⟦t⟧ ≠ ⟦u⟧, as for an inner interchanger).

TopGray(Γ) is the set of top generators of U(Γ). inner-top(Γ, A) holds iff some lift of the head has an inner letter of top dimension; both are computed by the procedure of §2.3. ord-tgt means that γ(aₙ) is an object variable marked `ord`.

**Rule.**
```
(C : ⋆)^ord        every inner letter whose hom lands in a hom 𝒦(X, C) is trivial
                   (an identity in strict models; so in particular invertible)
(COH-ord)    Γ^ord ⊢ps (every object of Γ marked ord), SC_𝔉(Γ, t → u),
             γ sends every object of Γ to an ord variable    ⊢  coh^ord_{Γ, t → u}[γ];
             its marks are the two-tier rules of §3.3

(COH-inv)    coherence case                                                   ⇒  inv
(OP-inv_S′)  Gray operation case, designated lift c; every outer top letter ℓ
             of c has generators of Γ as operands and is one of
               (i)   a whiskered Gray cell G(x₁, …, xₙ), with g[γ] inv,
               (ii)  an outer cylinder whose moving input x has x[γ] inv,
               (iii) h(A, B) with A[γ] inv and (ord-tgt, or the split on
                     the side of the A-cylinder in ῑ₋ is in S);
             and (inner-top(Γ, A) ⇒ ord-tgt)                                   ⇒  inv
(OP-ps_S′)   as (OP-inv_S′), except that in case (i) "g[γ] inv" may be
             replaced by "some xⱼ with dⱼ ≥ 1 has xⱼ[γ] ps*"                    ⇒  ps
(ORD)        inner coherence, ord-tgt                                          ⇒  inv
(INN-fac_S)  inner coherence whose head is the elementary inner interchanger,
             with (inner law ∈ S and its left input inv) or (R ∈ S and its right input inv)
                                                                               ⇒  inv
```
The Gray cells g[γ] are the operation-case coherences over wedges of disks, as in §3.1. (INV-fac), (INV-obj), (PS-fac), (INV⇒PS), (PS*), (OBJ-k), (DES) and the mark rule are unchanged. A `ord` mark, like `grpd_k`, may only be sent by a substitution to an object variable marked `ord`.

**Side condition and decision procedure.** Finite, given the side-condition procedure of §2.3. That procedure is not yet implemented (ledger S3), so the Agda encoding takes its output as a parameter.

**Example (a): directed Eckmann–Hilton inside an object.** The inner interchanger head over Σ(ΣD¹ ∨ ΣD¹), substituted with identity 1-cells and 2-cells a, b : 1_x ⇒ 1_x of the hom 𝒦(X, C), gives EH₁ : b ∗ a ⇛ a ∗ b; swapping a and b gives EH₂ : a ∗ b ⇛ b ∗ a. These are two directed cells, not inverse to each other. With `(C : ⋆)^ord` both are invertible by (ORD). With the inner law on and a marked `inv`, or with R on and b marked `inv`, (INN-fac_S) makes them invertible without `ord`. In setting ∅, with no marks, nothing makes them invertible. In two-tier L the same head is one coherence in the coherence case, and EH is invertible with no marks.

**Example (b): why `ord` is needed in the Gray operation case.** For hom-1 cells α, β of 𝒦(X, C) composable along a hom-0 cell, the strict composite is the Gray operation case, but a lift from one layering to the other has the inner interchanger ι(α, β) as a top letter. So a composite of invertible cells inside an object is invertible only when C is `ord` (or (INN-fac_S) applies).

**Semantics.** The intended models are algebras of admissible theories satisfying S (§2.3), with strict inverses. `C ord` quantifies over all inner letters, not only elementary interchangers.
- **Sound in every model:** (COH-inv), (ORD), (INN-fac_S), and (INV-fac)/(INV-obj) for Gray cells with one positive factor (from the outer unary subdivisions of V's base B). (INN-fac_S) uses the switched split law together with the unit law ι(1, G) = 1.
- **Also sound in every model:** (OP-inv_S′) (`notes/uniform-marks.md` Theorem 8.1). Each top letter of the lift is invertible: in case (i) by closure under substitution, in case (ii) by the cylinder result, in case (iii) by r̄₁ = h(A, B) · ῑ₋, and inner top letters by `ord`.
- **Sound only in the model class 𝓜_S:** the ps* branch of (OP-ps_S′), and the factor rules for Gray cells with several positive factors. 𝓜_S is cut out by the hypothesis (IL): an outer letter is invertible whenever the Gray cell of its Gray image is. 𝓜_S contains every strict Gray-enriched category and every strict ω-category, but **no free algebra of V + S**.
- **Why the rule was repaired.** The first version, (OP-inv_S), read its premise on the Gray generator g[γ]. The researcher answer of 2026-11-21 shows that (IL) is false on free algebras, in every setting. The letter E(Z, b), with Z an inner square composed with a generator x, has Gray cell G(x, b). A substitution contracting x makes that Gray cell an identity, while the letter becomes E(I, b), which is not invertible. Requiring the operands of the letter to be generators of Γ removes the gap.
- **Both switch conditions are exact.** An inner interchanger with an invertible input need not be invertible without the matching split. Invertible elementary inner interchangers do not make the other inner letters invertible. So `ord` has to quantify over all inner letters, and (INN-fac_S) is as strong as possible.

**`ord` everywhere is two-tier L** (`notes/ord-recovers-two-tier.md`, ledger S16(b)). With every object variable marked `ord`, (COH-ord) accepts exactly the two-tier heads, and the uniform rule set derives exactly two-tier L's terms, types and marks (there, Corollary 3.2, **proved on paper**). **Agda-checked** (`Uniform/OrdCoh.agda`, `recovers`, `conservative`): only the Boolean form of the acceptance rule, on abstract side conditions, assuming the inclusion SC_{V+S} ⇒ SC_𝔉 of S2. S2 is closed under the S1 reading of the side condition. (COH-ord) is sound in every strict model whose `ord` objects have trivial inner letters: such a model kills every inner letter of the head, so its map out of F_{V+S}(Γ) factors through the quotient 𝔉(Γ) (requirement 4). The path-level form of that factorization is **Agda-checked** (`OrdCoh.Erase.factor`); the algebra-level step is proved on paper. With no `ord` marks, nothing changes.

**Why `ord` must change the side condition.** The first reading of `ord` only made inner letters invertible. Under that reading, `ord` everywhere does **not** give two-tier L's coherences, **in any setting**. Under the uniform rules, the uniform rule set derives `inv` and `ps` only for designated lifts whose outer top letters have generator operands and are of kinds (i)–(iii).
- **The loop.** The loop H : w ⇛ w on Σ[2] ∨ Σ[2] (a whiskered inner interchanger) and 1_w have the same Gray image. In a V + S algebra in which every inner letter is invertible they still differ, and no higher cell joins them. Inverting the inner letters therefore creates no cell H ⇛ 1_w.
- **The outer strip.** The outer W-strip on C_{2,1} is a second witness, and it survives both switches.
- **The inner strip.** It is equal exactly when the inner law holds. Without the inner law it stays unconnected after localization.

So invertibility alone does not make an object an ordinary ω-category up to coherence. Any mark that recovers two-tier coherences must force inner letters to be trivial, and therefore has to act through the side condition, because the kernel has no definitional equality. Whether to keep the invertible-only reading as a second, weaker mark is an open design choice. Nothing in the spec needs it. Source: `notes/uniform-marks.md` §8; `notes/conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`.

**Status.**
- Rules: **stated here**, following `notes/uniform-marks.md` §3.
- (ORD) and (COH-inv): **proved** (§4.3 there).
- (INN-fac_S): **Agda-checked** (`Uniform/InnerInv.agda`, `left-inv`, `right-inv`, from the sesquicategory axioms, the unit law and the split, as record fields).
- Outer cylinders: **proved**.
- (OP-inv_S′): **proved** in every model (`notes/uniform-marks.md` Theorem 8.1). The ps* branch of (OP-ps_S′) and the factor rules for several positive factors: **proved** for 𝓜_S only, which excludes the free algebras. Whether they hold in every model is open (ledger E14).
- **Agda-checked** (`Uniform/Marks.agda`, which encodes the first version (OP-inv_S); re-encoding (OP-inv_S′) is ledger E14): the decision procedure on head data, uniform ⇒ two-tier, ord-covers-two-tier, setting monotonicity, non-collapse, soundness from the per-rule statements, and Example (a) by evaluation. These statements are about the encoded rules on abstract head data. The encoded two-tier rules (`invT`, `psT`) share only `grayInv` and `grayPs` with `Gray/Marks.agda`. The identification of two-tier's coherence case with `coherenceC ∨ innerC` on the projected head is a paper step (§3.6 Semantics), as is the head classification itself until S3. `innFac-sem` takes the unit and split laws as hypotheses on the model. That they hold as 3-cell equations in the intended models is proved on paper only (`notes/uniform-marks.md` §4.4).
- Ledger S4, E7 and E13 are done. What remains is ledger E14.

**Source.** `notes/uniform-marks.md`; `notes/invertibility-markings.md` §1.5.

## 3.7 The form of the marks, and saturation

The marks are proof-irrelevant judgments. This form was compared against an equation-free invertibility type (ICaTT without equations), marked arrow types, complicial thinness and modes in `notes/marking-alternatives.md` (ledger S17).
- **What was forced.** Pseudo is a property of lax cells (Theorem 3.5.1), so marks rather than a second sort of cell. `ps*` is forced by C1″. `ord` must act through the side condition (E13), so `ord` and `grpd_k` are modes on objects in any form.
- **What was not forced.** Proof-irrelevant judgments rather than evidence terms. That was a choice.
- **Its cost.** `inv` is not *saturated*: it is not closed under ICaTT's inv-intro. In Γ₁ = (x : a → b)(y : b → a)(l : y;x ⇛ 1)^inv(r : x;y ⇛ 1)^inv, x is invertible in every model, but no 1-cell a → b is derivably inv. One dimension up, the naturality cell of a lax transformation at such an x is invertible in every model and not derivably so. **Agda-checked** (`Gray/MarksSaturation.agda`).
- **Theorem (saturation vs decidability).** No sound judgment on raw terms that is closed under inv-intro, (OP-inv), (DES) and (DES-inv) is decidable, uniformly in Γ, already for one object, 1-cells and inv-marked 2-cells. **Proved** (`notes/marking-alternatives.md` Theorem 3.3), by reduction of the unit problem of finitely presented monoids (Narendran–Ó'Dúnlaing–Otto 1991).

**Proposed evidence layer [proposal].**
```
e ::= !                                   the judgment itself (ICaTT's evidence erased)
    | inv(t; s, s′, l, r; e_l, e_r)        inv-intro: l : s ; t → 1, r : t ; s′ → 1
    | can(coh[γ]; {i ↦ e_i})               arguments upgraded by evidence, fed to §3.3/§3.6
Γ ⊢ t inv by e
```
Evidence `!` is exactly the judgment. Evidence is checked structurally, so the layer is decidable and conservative over §3.3. It is used where a judgment needs a cell that is invertible by data: substitution into a marked variable (the "equivalence certificates" of CaTT_lim) and the premises of the propagation rules. Destructors on evidence follow ICaTT without equations. The judgment's own t⁻ˡ is linv(!).
- **Agda-checked**: the checker for cells of dimensions 1 and 2, conservativity, and the two examples (`Gray/MarksSaturation.agda`). General dimensions are not encoded.
- **Proved on paper**: soundness.
- **Open**:
  - pseudo by data, which needs a binder over a generic earlier cell (ledger S19);
  - whether finite certificates suffice in L (ledger S20, `notes/conjectures/outbox/invertibility-certificates.md`). In P they do (`notes/marking-alternatives.md` §6.1).

**Rejected forms.** Marked arrow types need subtyping, or they duplicate every coh by its annotation. Complicial thinness replaces `coh` rather than marking it, and its saturated form is undecidable by the theorem above. Modes cannot carry cell-level marks: two lax transformations between the same functors can differ in being pseudo.

## 3.8 Open surface questions

**Q3.1. Where marks are written.** The kernel has no defaults: every mark a derivation needs is a declared mark or derived by §3.3.
- *Option M0: the user writes every mark the rules need,* including `inv` on derived cells. Nothing is inferred; far more annotation (≥ 6 marks for an adjunction).
- *Option M1: marks only on declarations* (`ps`, `inv`, `grpd_k`, `ord`), everything else derived by §3.3. One mark per pseudo structure cell. Forgetting a mark makes a proof fail to check, which is visible.
- *Option M2: pseudo by default.* Every declared 2-cell is ps* unless written `lax`. Saves one mark per pseudo structure cell and costs one per lax cell. Forgetting `lax` silently proves a weaker theorem, about pseudo transformations only.
- *Counts from `notes/invertibility-markings.md` §6.1* (annotations written by the user):

| Example | P | M0 | M1 | M2 |
|---|---|---|---|---|
| Lax transformation and naturality | ~5 steps | 0 | 0 | 1 |
| Pseudo transformation and naturality | 0 | ≥ 2 | 1 | 0 |
| Composite of 3 pseudo transformations | 0 | ≥ 5 | 3 | 0 |
| Adjunction (η, ε, two triangles) | 2 | ≥ 6 | 4 | 2 |
| Monad (η, μ, three coherences) | 3 | ≥ 8 | 5 | 3 |
| Ring object (+, ·, ~8 witnesses) | 8 | 8+ | 1 | 1 |
| Lax colimit / Grothendieck construction | heavy | 0 | 0 | one per transformation |

The note proposed M1; the choice is left open here.

**Q3.2. Whether `ps` and `ps*` are both visible.** The kernel has both.
- *Option A: expose only `ps*`, written "pseudo".* Matches the meaning in P; every pseudo modification must have pseudo boundaries anyway.
- *Option B: expose both.* `ps` alone is the more general building block, but no rule currently uses it as a premise, so it would be a mark the user can write and nothing can consume.

**Q3.3. How `ord` is scoped.** Under uniform L, inner interchange is directed in every object unless marked. (Whatever the scope, with (COH-ord) an `ord` object is ordinary in the full two-tier sense, in every switch setting, because SC_𝔉 does not depend on S, §3.6. Heads that mix `ord` and non-`ord` objects use the uniform rule until ledger E15 is settled.)
- *Option A: per object declaration* (`(C : ⋆)^ord`). Precise; most objects in ordinary use need the mark.
- *Option B: a per-file default "all objects ord" with an opt-out.* Ordinary mathematics needs no annotation; a development that forgets the opt-out silently proves a statement only about ordinary ω-categories.
- *Option C: a per-development setting, like the switch setting of chapter 2.* Uniform with Q2.1; coarse.
