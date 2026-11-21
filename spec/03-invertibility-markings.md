# Chapter 3. Invertibility markings

The lax core makes every interchanger directed. Pseudo transformations, ordinary ω-categories and groupoids are recovered by **marks**: proof-irrelevant judgments on terms and object variables, propagated by syntax-directed rules. Marks add no new definitional equalities. They add only the inverse term formers that ICaTT has, without its equations.

**Pseudo = L + marks.** P (plain CaTT with pseudo transformations) has exactly the models of L in which every mixed cell of every dimension is invertible (Theorem 3.5.1). So the kernel does not need a separate pseudo core.

The rules below are stated over the **two-tier** unfolding U(Γ) = Θ₁ ⊗ … ⊗ Θₙ of chapter 2, §2.5, which is where they are proved and machine-checked. Their restatement over the generators of F_{V+S}(Γ) is §3.6.

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
```

There is no β or η, so ICaTT's `can`/`rec` equations have nothing to say. Since `inv` is a judgment, the destructors depend on t only.

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

**Rule (stated here).** Over V + S, the generators of F_{V+S}(Γ) include, beyond the Gray tensor tuples of §3.1, the inner interchangers and their naturality cells. The marks of §3.2 keep their meaning, and two additions are needed:

```
(C : ⋆)^ord      C is an ordinary ω-category: every inner interchanger of every hom 𝒦(X, C) is invertible

(ORD)       an inner interchanger whose cells land in a hom 𝒦(X, C), with C ord   ⇒  inv
```

together with the (INV-fac)-style rule for inner generators: an inner interchanger with an invertible positive-dimensional factor is invertible.

**Intended meaning.** Marking every object `ord` should give exactly two-tier L up to invertible cells: under `ord`, the coherences accepted in setting S over 𝒦(X, C) coincide with two-tier L's, up to invertible cells. Marking everything `ord` and every variable ps should give P.

**Example.** Example (c) of chapter 2, §2.3: in an object C, the directed interchanger of two 2-cells composable along a 1-cell is not invertible; with `(C : ⋆)^ord` it is, and directed Eckmann–Hilton becomes the ordinary invertible one.

**Status.** **Stated here** following `notes/invertibility-markings.md` §1.5. The notes record this as blocked on the uniform construction, which now exists (V, chapter 2), so it is no longer blocked: the restatement of (INV-fac), (PS-fac) and (OP-ps) over F_{V+S}(Γ), the soundness of (ORD), and the check "ord restores two-tier L" are ledger E7 and S4.

## 3.7 Open surface questions

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

**Q3.3. How `ord` is scoped.** Under uniform L, inner interchange is directed in every object unless marked.
- *Option A: per object declaration* (`(C : ⋆)^ord`). Precise; most objects in ordinary use need the mark.
- *Option B: a per-file default "all objects ord" with an opt-out.* Ordinary mathematics needs no annotation; a development that forgets the opt-out silently proves a statement only about ordinary ω-categories.
- *Option C: a per-development setting, like the switch setting of chapter 2.* Uniform with Q2.1; coarse.
