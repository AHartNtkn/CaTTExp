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

(DES-inv) is needed because no other rule makes an inverse invertible: without it, composites involving t⁻ˡ would not be derivably inv (`notes/marking-alternatives.md` §3.2). It is sound (t⁻ˡ has inverse t) and syntax-directed. Agda: with the destructors, ledger E4.

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

The rules of §3.3 are stated over U(Γ). Over V + S(Γ) (chapter 2, §2.3; S(Γ) is the set of splits marked on every object a₁, …, aₙ of Γ) they are restated by reading the **designated lift** c of a coherence (§2.2) through the Gray projection π. Every letter of c is **outer** (π sends it to a whiskered Gray generator) or **inner** (π sends it to an identity). The cases are:
- the **Gray operation case**, π(c) = τ_Γ;
- the **Gray coherence case**, π(c) an identity, which is either the coherence case (⟦t⟧ = ⟦u⟧ in F_{V+S}(Γ)) or an **inner coherence** (⟦t⟧ ≠ ⟦u⟧, as for an inner interchanger).

TopGray(Γ) is the set of top generators of U(Γ). inner-top(Γ, A) holds iff some lift of the head has an inner letter of top dimension; both are computed by the procedure of §2.3. ord-tgt means that γ(aₙ) is an object variable marked `iord` or `ord`.

**Rule.**
```
(C : ⋆)^iord       every inner letter whose hom lands in a hom 𝒦(X, C) is invertible
(C : ⋆)^ord        every inner letter whose hom lands in a hom 𝒦(X, C) is trivial
                   (an identity in strict models; so in particular invertible)
(C : ⋆)^lsplit     every inner crossing in a hom 𝒦(X, C) satisfies the left split
(C : ⋆)^rsplit     every inner crossing in a hom 𝒦(X, C) satisfies the right split R
                   (ord implies lsplit and rsplit; chapter 2, §2.3)
(COH-ord)    Γ^ord ⊢ps (objects a₁, …, aₙ of Γ marked ord), SC_𝔉(Γ, t → u),
             γ sends a₁, …, aₙ to ord variables              ⊢  coh^ord_{Γ, t → u}[γ];
             (a₀ is the target of no hom of Γ, so its mark is irrelevant)
             its marks are the two-tier rules of §3.3

(COH-inv)    coherence case                                                   ⇒  inv
(OP-inv_S′)  Gray operation case, designated lift c; every outer top letter ℓ
             of c has generators of Γ as operands and is one of
               (i)   a whiskered Gray cell G(x₁, …, xₙ), with g[γ] inv,
               (ii)  an outer cylinder whose moving input x has x[γ] inv,
               (iii) h(A, B) with A[γ] inv and (ord-tgt, or the split on
                     the side of the A-cylinder in ῑ₋ is in S(Γ));
             and (inner-top(Γ, A) ⇒ ord-tgt)                                   ⇒  inv
(OP-ps_S′)   as (OP-inv_S′), except that in case (i) "g[γ] inv" may be
             replaced by "some xⱼ with dⱼ ≥ 1 has xⱼ[γ] ps*"                    ⇒  ps
(ORD)        inner coherence, ord-tgt                                          ⇒  inv
(INN-fac_S)  inner coherence whose head is the elementary inner interchanger,
             with (left split ∈ S(Γ) and its left input inv) or (R ∈ S(Γ) and its right input inv)
                                                                               ⇒  inv
```
The Gray cells g[γ] are the operation-case coherences over wedges of disks, as in §3.1. (INV-fac), (INV-obj), (PS-fac), (INV⇒PS), (PS*), (OBJ-k), (DES) and the mark rule are unchanged. A `ord` mark, like `grpd_k`, may only be sent by a substitution to an object variable marked `ord`; an `lsplit` (`rsplit`) mark only to one marked `lsplit` (`rsplit`) or `ord`.

**Side condition and decision procedure.** Finite, given the side-condition procedure of §2.3. That procedure is not yet implemented (ledger S3), so the Agda encoding takes its output as a parameter.

**Example (a): directed Eckmann–Hilton inside an object.** The inner interchanger head over Σ(ΣD¹ ∨ ΣD¹), substituted with identity 1-cells and 2-cells a, b : 1_x ⇒ 1_x of the hom 𝒦(X, C), gives EH₁ : b ∗ a ⇛ a ∗ b; swapping a and b gives EH₂ : a ∗ b ⇛ b ∗ a. These are two directed cells, not inverse to each other. With `(C : ⋆)^ord` both are invertible by (ORD). With `(C : ⋆)^lsplit` and a marked `inv`, or with `(C : ⋆)^rsplit` and b marked `inv`, (INN-fac_S) makes them invertible without `ord` (`Uniform/SplitMarks.agda`, `eh-lsplit`, `eh-rsplit`; the wrong-side cases are rejected, `eh-*-wrong-side`). With no marks, nothing makes them invertible. In two-tier L the same head is one coherence in the coherence case, and EH is invertible with no marks.

**Example (b): why `ord` is needed in the Gray operation case.** For hom-1 cells α, β of 𝒦(X, C) composable along a hom-0 cell, the strict composite is the Gray operation case, but a lift from one layering to the other has the inner interchanger ι(α, β) as a top letter. So a composite of invertible cells inside an object is invertible only when C is `ord` (or (INN-fac_S) applies).

**Semantics.** Soundness is checked in algebras of admissible theories in which each marked object satisfies its split marks (§2.3), with strict inverses. `C ord` quantifies over all inner letters, not only elementary interchangers.
- **Sound in every model:** (COH-inv), (ORD), (INN-fac_S), and (INV-fac)/(INV-obj) for Gray cells with one positive factor (from the outer unary subdivisions of V's base B). (INN-fac_S) uses the marked split law together with the unit law ι(1, G) = 1.
- **Also sound in every model:** (OP-inv_S′) (`notes/uniform-marks.md` Theorem 8.1). Each top letter of the lift is invertible: in case (i) by closure under substitution, in case (ii) by the cylinder result, in case (iii) by r̄₁ = h(A, B) · ῑ₋, and inner top letters by `ord`.
- **Sound only in the model class 𝓜_S** (whether in every model is open, ledger E14): the ps* branch of (OP-ps_S′), and the factor rules for Gray cells with several positive factors. 𝓜_S is cut out by the hypothesis (IL): an outer letter is invertible whenever the Gray cell of its Gray image is. 𝓜_S contains every strict Gray-enriched category and every strict ω-category, but **no free algebra of V + S**.
- **Why the operands must be generators of Γ.** A premise read only on the Gray generator g[γ] would not be sound, because (IL) is false on free algebras, with any split marks. The letter E(Z, b), with Z an inner square composed with a generator x, has Gray cell G(x, b). A substitution contracting x makes that Gray cell an identity, while the letter becomes E(I, b), which is not invertible. Requiring the operands of the letter to be generators of Γ removes the gap.
- **Both split conditions are exact.** An inner interchanger with an invertible input need not be invertible without the matching split. Invertible elementary inner interchangers do not make the other inner letters invertible. So `ord` has to quantify over all inner letters, and (INN-fac_S) is as strong as possible.

**`ord` everywhere is two-tier L** (`notes/ord-recovers-two-tier.md`, ledger S16(b)). With every object variable marked `ord`, (COH-ord) accepts exactly the two-tier heads, and the uniform rule set derives exactly two-tier L's terms, types and marks (there, Corollary 3.2, **proved on paper**). **Agda-checked** (`Uniform/OrdCoh.agda`, `recovers`, `conservative`): only the Boolean form of the acceptance rule, on abstract side conditions, assuming the inclusion SC_{V+S} ⇒ SC_𝔉 of S2. S2 is closed under the S1 reading of the side condition. (COH-ord) is sound in every strict model whose `ord` objects have trivial inner letters: such a model kills every inner letter of the head, so its map out of F_{V+S}(Γ) factors through the quotient 𝔉(Γ) (requirement 4). The path-level form of that factorization is **Agda-checked** (`OrdCoh.Erase.factor`); the algebra-level step is proved on paper. With no `ord` marks, nothing changes.

**Why `ord` must change the side condition.** A mark that only made inner letters invertible would not give two-tier L's coherences, **with any split marks**. With such a mark on every object, the uniform rule set would derive `inv` and `ps` only for designated lifts whose outer top letters have generator operands and are of kinds (i)–(iii).
- **The loop.** The loop H : w ⇛ w on Σ[2] ∨ Σ[2] (a whiskered inner interchanger) and 1_w have the same Gray image. In a V + S algebra in which every inner letter is invertible they still differ, and no higher cell joins them. Inverting the inner letters therefore creates no cell H ⇛ 1_w.
- **The outer strip.** The outer W-strip on C_{2,1} is a second witness, and it survives both split marks.
- **The inner strip.** It is equal exactly when the left split holds. Without it it stays unconnected after localization.

So invertibility alone does not make an object an ordinary ω-category up to coherence. Any mark that recovers two-tier coherences must force inner letters to be trivial, and therefore has to act through the side condition, because the kernel has no definitional equality. **Both readings are kept** (decided 2026-11-23, `notes/ord-recovers-two-tier.md` §6):
- `iord` (inner letters invertible) is enough for (ORD) and (OP-inv_S′). It is sound in strictly more strict models, for example the E13 loop model, where the inner letters are invertible but not identities.
- `ord` (inner letters trivial) adds (COH-ord) and gives two-tier L.

This is the lax / pseudo / strict pattern of §0.4 applied to interchange inside an object: unmarked, `iord`, `ord`. `ord` implies `iord`. An `iord` variable may be sent to an `iord` or `ord` variable, and an `ord` variable only to an `ord` variable. Source: `notes/uniform-marks.md` §8; `notes/conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`.

**Status.**
- Rules: **stated here**, following `notes/uniform-marks.md` §3.
- (ORD) and (COH-inv): **proved** (§4.3 there).
- (INN-fac_S): **Agda-checked** (`Uniform/InnerInv.agda`, `left-inv`, `right-inv`, from the sesquicategory axioms, the unit law and the split, as record fields).
- Outer cylinders: **proved**.
- (OP-inv_S′): **proved** in every model (`notes/uniform-marks.md` Theorem 8.1). The ps* branch of (OP-ps_S′) and the factor rules for several positive factors: **proved** for 𝓜_S only, which excludes the free algebras. Whether they hold in every model is open (ledger E14).
- **Agda-checked, repaired rules** (`Uniform/MarksRepaired.agda`): (OP-inv_S′)/(OP-ps_S′) per top letter, `iord`/`ord`, (COH-ord). The first version accepts the E13 shape and the repaired rule rejects it (`old-accepts`, `new-rejects`, by evaluation). Also checked: uniform ⇒ two-tier given the projection data as a hypothesis; `iord` suffices for (ORD); all-`ord` heads use the two-tier rules; setting monotonicity (with split marks: `Uniform/SplitMarks.agda`, `invM-mono`). `sound′` reduces soundness to the paper theorems given as fields of `Sem′` (4.3, 4.4, 8.1, 2.2/2.3, and `compose` = decomposition of the coherence image into the letters of its lift plus Lemma 4.1); `iso-path` and `join-iso` are proved separately. In the operation case `sound-op` connects `iso-path`: invertibility is IsIso of the path composite, and two inputs remain unchecked: (1) that the coherence's image is `pcomp p` for the lift's letter images (`p` is a free field, not tied to `liftTops h`, so `OpModel` can be inhabited with `p = nil`), and (2) `letters`, the per-letter step. None of those fields is (IL).
- **Agda-checked, first version** (`Uniform/Marks.agda`, superseded; its premise is read on g[γ] rather than on the letter's operands): the decision procedure on head data, uniform ⇒ two-tier, ord-covers-two-tier, setting monotonicity, non-collapse, soundness from the per-rule statements, and Example (a) by evaluation. These statements are about the encoded rules on abstract head data. The encoded two-tier rules (`invT`, `psT`) share only `grayInv` and `grayPs` with `Gray/Marks.agda`. The identification of two-tier's coherence case with `coherenceC ∨ innerC` on the projected head is a paper step (§3.6 Semantics), as is the head classification itself until S3. `innFac-sem` takes the unit and split laws as hypotheses on the model. That they hold as 3-cell equations in the intended models is proved on paper only (`notes/uniform-marks.md` §4.4).
- Ledger S4, E7 and E13 are done. What remains is ledger E14.

**Source.** `notes/uniform-marks.md`; `notes/invertibility-markings.md` §1.5.

## 3.7 The form of the marks, and saturation

The marks are proof-irrelevant judgments. This form was compared against an equation-free invertibility type (ICaTT without equations), marked arrow types, complicial thinness and modes in `notes/marking-alternatives.md` (ledger S17).
- **What was forced.** Pseudo is a property of lax cells (Theorem 3.5.1), so marks rather than a second sort of cell. `ps*` is forced by C1″. `ord` must act through the side condition (E13), so `ord` and `grpd_k` are modes on objects in any form.
- **What was not forced.** Proof-irrelevant judgments rather than evidence terms. That was a choice.
- **Its cost.** `inv` is not *saturated*: it is not closed under ICaTT's inv-intro. In Γ₁ = (x : a → b)(y : b → a)(l : y;x ⇛ 1)^inv(r : x;y ⇛ 1)^inv, x is invertible in every model, but x is not derivably inv (**Agda-checked**, `Gray/MarksSaturation.agda`). In fact no 1-cell a → b is derivably inv (**proved** on paper). One dimension up, the naturality cell of a lax transformation at such an x is invertible in every model and not derivably so (**Agda-checked**).
- **Theorem (saturation vs decidability).** No sound judgment on raw terms is decidable, uniformly in Γ, if it contains the marked variables and the coherence-case cohs and is closed under inv-intro, (OP-inv), (INV-fac), (DES) and (DES-inv). This holds already for one object, 1-cells and inv-marked 2-cells. **Proved** (`notes/marking-alternatives.md` Theorem 3.3), by reduction of the unit problem of finitely presented monoids (Narendran–Ó'Dúnlaing–Otto 1991).

**Proposed evidence layer [proposal].**
```
e ::= !                                   the judgment itself (ICaTT's evidence erased)
    | inv(t; s, s′, l, r; e_l, e_r)        inv-intro: l : s ; t → 1, r : t ; s′ → 1
    | can(coh[γ]; {i ↦ e_i})               arguments upgraded by evidence, fed to §3.3/§3.6
    | clock(u, v, f; e_1..e_4; W, σ, {e_w})  (INV-clock), for the cell w_0·f
Γ ⊢ t inv by e
```
(INV-clock) takes cells u : s ⇒ t and v : t ⇒ s with evidence e_1..e_4 for u;v, (tu);(tv), (tv);(tu) and t·f. It also takes a finite list W of prefix 1-cells with a successor map σ on W, and for each w ∈ W evidence e_w for a comparison w ⇒ σ(w)·s. It concludes that w_0·f is invertible, where w_0 is the first word. It is sound in every model (the clock criterion: following σ gives an infinite chain of comparisons, and each copy of s pays for one level of the reversal tower). It covers the known pattern that needs an infinite tower: two directed cylinders whose composite is invertible.
Evidence `!` is the judgment, by definition. Evidence is checked structurally, and the new terms it introduces are type-checked, so the layer is decidable. It only adds derivations, so everything §3.3 derives is kept. It is used where a judgment needs a cell that is invertible by data: substitution into a marked variable (the "equivalence certificates" of CaTT_lim) and the premises of the propagation rules. Destructors on evidence follow ICaTT without equations. The judgment's own t⁻ˡ is linv(!).
- **Agda-checked**: the checker for cells of dimensions 1 and 2, and the two examples (`Gray/MarksSaturation.agda`). General dimensions are not encoded.
- **Proved on paper**: soundness, for well-typed evidence (the Agda checker type-checks the evidence terms). For (INV-clock), soundness is the clock criterion of the verified r3 answer. It is proved for strict Gray ω-categories, and for the weak case by coinductive completion of the ordinary homs (citations checked against the sources).
- **Open**:
  - **No complete certificate language exists in L** (verified researcher answers, `notes/conjectures/answered/invertibility-certificates-r2-2026-11-23.md` and `-r3-2026-11-23.md`; `notes/marking-alternatives.md` §§9–10). A finite marked computad has an invertible 3-cell that no finite certificate reaches. More strongly, invertibility in free L-models is not recursively enumerable. Nonhalting reduces to it, even for one fixed computad. So no decidably checked evidence language is complete, and no maximal one exists. `inv` and the evidence layer are decidable sufficient criteria, permanently incomplete in L, as principle 0.6 allows; in P they are complete. A development that needs a cell outside them declares it `inv` as a hypothesis.
  - (INV-clock) in Agda: ledger S21.

**`ps` is declared, never certified from data.** Freely attaching a generic cell y before t makes y ⊗ t invertible iff t is invertible (Ara–Maltsiniotis B.6.5–6; verified researcher answer, `notes/conjectures/answered/invertibility-certificates-2026-11-23.md`). So in a context without `ps`, `grpd_k` or `ord` marks, a term that is pseudo in every model is invertible in every model (`notes/marking-alternatives.md` Prop. 8.2). The evidence layer therefore has no Ps-intro rule: pseudo-ness enters only through declared marks and (PS-fac)/(OP-ps). **Proved**, from the verified answer.

**Rejected forms.** Marked arrow types need subtyping, or they duplicate every coh by its annotation. Complicial thinness replaces `coh` rather than marking it, and its saturated form is undecidable by the theorem above. Modes on objects or 1-cells cannot carry cell-level marks: two lax transformations between the same functors can differ in being pseudo. A mode on the hom amounts to a marked arrow type or a second kind of 2-cell.

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

**Q3.3. How `ord` is scoped.** Under uniform L, inner interchange is directed in every object unless marked. The same question applies to `iord`, `lsplit` and `rsplit`. Whatever the surface does, the kernel context it produces carries every mark on its variable, so a mark is always a hypothesis of the statement proved. No option is a file-level choice of the models a development is about (chapter 0, §0.1). (Whatever the scope, with (COH-ord) an `ord` object is ordinary in the full two-tier sense, whatever the split marks of other objects, because SC_𝔉 does not depend on S, §3.6. Heads that mix `ord` and non-`ord` objects use the uniform rule until ledger E15 is settled.)
- *Option A: per object declaration* (`(C : ⋆)^ord`). Precise; most objects in ordinary use need the mark.
- *Option B: notation that writes `ord` on every object variable a declaration introduces, with a per-variable opt-out.* Ordinary mathematics needs little annotation. The marks still appear in each elaborated context, but a reader of the surface text does not see them. A statement that forgot an opt-out is stated only for ordinary objects; it can't be applied to an unmarked object, which is visible at the use site.
- *Option C: the surface infers the weakest marks a proof needs* (§0.5 allows inferring marks). It writes each inferred mark into the elaborated context, and the user can ask to see it. Nothing is assumed that the proof does not use. Inference has to be decidable and proved conservative like every surface layer, and an error appears only when a needed mark contradicts a declared one.
- *Worked example.* A lemma about a composite of invertible 2-cells inside an object C needs C `ord` or (INN-fac) (§3.6 Example (b)). Under A, the author writes `(C : ⋆)^ord`. Under B, nothing is written. Under C, the surface infers `ord`, or the weaker `iord` if (ORD) alone suffices, and shows it in the lemma's elaborated statement.
