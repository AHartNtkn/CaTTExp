# Invertibility and pseudo markings for the lax core (L)

*Design notes, 2026-11-18. Ledger items E4, E5, E8, E9, E10 (and an attempt on E6). Builds on `pseudo-vs-gray.md` (§2.4, §3, §3.5), the proved result in `conjectures/gray-vs-cartesian.md`, and the ICaTT rules written out in `icatt-and-rice-rules.md`.*

*Markers as elsewhere: **[paper]** checked against the source; **[recall]** background, not re-checked; **[conj]**; **[proposal]**; **[proved]** proved here, with the proof given.*

## 0. Summary

1. **Two judgments, not one.** L needs an *invertibility* judgment `Γ ⊢ t inv` (ICaTT's, minus its equations) and a separate *pseudo* judgment `Γ ⊢ t ps`, "every Gray cell with t as its later factor is invertible". Pseudo is one-sided in execution order: a pseudo transformation has invertible naturality cells against cells *before* it, not after (§1.2, Example 1.6c). "Recursively pseudo" is ps on the cell and on every boundary cell of hom-dimension ≥ 1, which is the corrected C1″ (§1.3).
2. **Propagation rules, all proved sound** in oriented (∞,ω)-categories and in the strict Gray model (§2):
   - (INV-fac) a Gray generator with an invertible positive-dimensional factor is invertible. This proves the old [conj] "an interchanger with an invertible factor is invertible";
   - (PS-fac) a Gray generator whose factor xⱼ is pseudo, with a positive-dimensional factor somewhere before it, is invertible;
   - (can-L) the L analogue of ICaTT's `can`: an operation-case coh is invertible (resp. pseudo) when each top generator of its Gray unfolding is; coherence-case cohs are always invertible;
   - (OBJ-k) an object C marked `grpd_k` makes every cell of hom-dimension ≥ k in any hom 𝒦(X, C) invertible. This is the "C has only invertible k-cells" propagation asked for in `pseudo-vs-gray.md` §5.3.
3. **P ≈ L + marking, semantic half: proved** (§3). Oriented (∞,ω)-categories whose composition inverts all mixed cells are exactly Cat_ω-enriched ∞-categories. The proof: by the n-ary form of the gray-vs-cartesian theorem, the cartesian multimorphisms form a sub-∞-operad of the Gray ones, so algebras over the first are algebras over the second whose operations land in it. The **syntactic** half (a conservative translation of CaTT into L + "everything is ps") is proved for the interchange case and reduced to one lemma in general; it is open.
4. **Representables and lax homs over L** (§4). Restating the hom rule and R-A over L is straightforward. The claim that "G1 disappears" under L is **half right**: *using* a lax cell (reading off its Gray-shaped components) needs no Gray context, but *introducing* a lax cell from component data does, and then the syntactic-matching problem behind G1 comes back. It is posed as Conjecture CT (canonical Gray terms) in `conjectures/canonical-gray-terms.md`.
5. **Cost** (§5). The [conj] "supports computed symbolically are polynomial in term size" is **false for explicit supports**: the term T over the n-fold wedge of 2-cells has size O(n) and support of size 3ⁿ, and the chains of its iterated source have size C(n, k). A restated question (decide the side condition in time polynomial in the *shared* term size) is open and passed to the Agda thread to measure.
6. **Surface defaults** (§6), settled by worked counts, not by asking: the kernel has no defaults; the surface marks only at declaration sites (`pseudo`, `grpd_k`), derives everything else by §1's rules, and uses the **∂⁻-layering** as the default horizontal composite, because every directed interchanger then leaves the default.
7. **E6 (uniform L construction): attempted, not solved** (§7). One obstruction is made precise: no free uniform structure can be the Steiner realisation ν(K) of a single complex, or of a hom-wise family of Steiner complexes; its homs must themselves be presented hom-wise, recursively, and the missing piece is a Gray tensor of such towers on free objects. The marking design of §1 is stated so that uniform L only adds one more judgment (`ord`, §1.5).

---

## 1. The rules [proposal]

### 1.1 Setting and notation

L as in `pseudo-vs-gray.md` §3: contexts, and coh over pasting schemes Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with supports in the Gray unfolding U(Γ) = Θ₁ ⊗ … ⊗ Θₙ (execution order).

- For a term t whose iterated 0-source and 0-target are objects a, b, write **hd(t) := dim t − 1**, its dimension *in the hom* 𝒦(a, b). Objects have no hom-dimension; 1-cells of 𝒦 have hd = 0.
- A generator of U(Γ) is g = x₁ ⊗ … ⊗ xₙ with xᵢ a cell of Θᵢ (a variable of ΣΘᵢ other than its two objects), dᵢ := dim xᵢ in Θᵢ. Its dimension is Σ dᵢ. It is **mixed** if at least two dᵢ ≥ 1.
- For a substitution γ out of Γ, write g[γ] for the **Gray cell of g at γ**: the op-case coh over the wedge ΣD^{d₁} ∨ … ∨ ΣD^{dₙ} with its canonical ∂⁻ → ∂⁺ type, substituted with (x₁[γ], …, xₙ[γ]). For n = 1 this is x₁[γ] itself (up to the unary-composite coherence); for one positive factor it is a whiskering; for mixed g it is an interchanger.

### 1.2 Judgments and rules

Two new judgments, both proof-irrelevant (no new terms):

```
Γ ⊢ t inv        t is invertible
Γ ⊢ t ps         t is pseudo: for every positive-dimensional cell y composed *before* t,
                 the Gray cell y ⊗ t is invertible
```

plus ICaTT's destructors as **term formers without equations**:

```
Γ ⊢ t inv    Γ ⊢ t : u → v
──────────────────────────────────────────────────────────────
Γ ⊢ t⁻ˡ : v → u     Γ ⊢ t⁻ʳ : v → u
Γ ⊢ λₜ : t⁻ˡ ∗ t → id v     Γ ⊢ ρₜ : t ∗ t⁻ʳ → id u
Γ ⊢ λₜ inv     Γ ⊢ ρₜ inv
```

(The names t⁻ˡ etc. are ICaTT's linv(e), …, with the evidence e erased: since inv is a judgment, the destructors depend on t only. There is no β or η, so there is nothing for ICaTT's can/rec equations to say.)

**Marked declarations.** A context may declare a variable with marks: `(x : A)^inv`, `(x : A)^ps`, and for objects `(C : ★)^{grpd_k}` (k ≥ 1). Rules: `(x:A)^m ∈ Γ ⇒ Γ ⊢ x m`. A substitution `Δ ⊢ γ : Γ` must send every marked variable to a term with the same mark: `Δ ⊢ x[γ] m`. This is the marked-computad style of Benjamin–Champin–Markakis (`icatt-and-rice-rules.md` §3).

**Propagation rules.** Below, `Δ ⊢ coh_{Γ,A}[γ] : A[γ]` is an L-coh (operation or coherence case), and g ranges over the generators of U(Γ) of the top dimension D := dim U(Γ) (in the op-case, hd of the coh is D; in the coherence case it is D + 1).

```
(COH-inv)    coherence case                                  ⇒  Δ ⊢ coh_{Γ,A}[γ] inv
(OP-inv)     operation case, and Δ ⊢ g[γ] inv for every top g  ⇒  Δ ⊢ coh_{Γ,A}[γ] inv
(OP-ps)      operation case, and for every top g:
               Δ ⊢ g[γ] inv  or  some xⱼ in g has dⱼ ≥ 1 and Δ ⊢ xⱼ[γ] ps
                                                             ⇒  Δ ⊢ coh_{Γ,A}[γ] ps

(INV-fac)    some i with dᵢ ≥ 1 and Δ ⊢ xᵢ[γ] inv             ⇒  Δ ⊢ g[γ] inv
(INV-obj)    all dᵢ = 0 and Δ ⊢ xᵢ[γ] inv for every i          ⇒  Δ ⊢ g[γ] inv
(PS-fac)     some j with dⱼ ≥ 1, Δ ⊢ xⱼ[γ] ps, and some i < j with dᵢ ≥ 1
                                                             ⇒  Δ ⊢ g[γ] inv

(INV⇒PS)     Δ ⊢ t inv, hd(t) ≥ 1                             ⇒  Δ ⊢ t ps
(DES)        the destructors and their units are inv (above)
(OBJ-k)      Δ ⊢ t : A, the 0-target of t is C, Δ ⊢ C grpd_k, hd(t) ≥ k
                                                             ⇒  Δ ⊢ t inv
```

Remarks.
- (COH-inv) and (OP-inv) for n = 1 are exactly ICaTT's can-intro with Var_{dim A+1}(Γ) as the set of top generators (Thm 3.8). In the coherence case, D < hd(coh), so the condition is vacuous, as in ICaTT.
- In (PS-fac) the order matters: "before" is execution order, i < j. (INV-fac) and (INV-obj) are symmetric.
- (OP-ps) also covers the identity transformation and whiskerings of pseudo cells (Example 1.6b).
- Everything is decidable: the rules are syntax-directed on coh, the generators of U(Γ) are finite, and the marks are finite data.

### 1.3 Recursive pseudo

Define `Γ ⊢ t ps*` ("strong") by: hd(t) = 0, or (`Γ ⊢ t ps` and, if hd(t) ≥ 2, `Γ ⊢ s ps*` and `Γ ⊢ u ps*` for t : s → u). For hd(t) = 1, ps* = ps.

This is the corrected C1″ of `gray-vs-cartesian.md` (verified): an r-cell of Fun^lax(B, C) is strong iff its adjunct Dʳ ⊗ B → C inverts **all** mixed cells, including those on boundary faces. The mixed cells on the boundary faces are the ps conditions of the boundary cells. So **ps* is "pseudo" in the sense of P**, and ps alone is the most general building block (standard 4): it is what (PS-fac) needs (Lemma 2.2 uses only the top condition).

A declaration `(x : A)^{ps*}` abbreviates the ps mark on x together with the requirement that the boundary terms in A are ps*. The verified counterexample (B = D¹, C = D³: a modification between two strong transformations that is not strong) shows that ps* on the boundary does **not** give ps on the cell, so the mark on every higher cell is genuinely needed.

### 1.4 Do we need ICaTT's rec?

ICaTT's rec builds invertibility of the image of a cell under an arbitrary construction (a term over the walking equivalence). In L the constructions are cohs and substitutions, and invertibility of the images is given directly by (OP-inv), (INV-fac), (INV-obj), and closure of inv under substitution. A case that these do not cover would be a construction that is not a single coh, e.g. a term over Eⁿ⁺¹ that applies a destructor and then composes. Such terms are cohs applied to destructor terms, which are inv by (DES), so (OP-inv) handles them. **[conj]** rec is admissible in this system: every term over Eⁿ⁺¹ of the form t[μ] (factoring through the underlying disk) whose top generator is invertible is derivably inv. Not needed for anything below; recorded so the question is not lost.

### 1.5 Uniform L (adjacent work while E6 is open)

Uniform L adds directed interchange *inside* objects. The same shape of rule handles it, with one more object mark:

```
(C : ★)^{ord}     C is an ordinary ω-category: inner interchangers of every hom 𝒦(X, C) are invertible
```

with an (INV-fac)-style rule for the inner Gray generators of the uniform unfolding, once that unfolding exists (§7). The check "marking C ord restores plain CaTT inside C" (E7) is then the statement that, under `ord`, the uniform rule's accepted terms in 𝒦(X, C) coincide with two-tier L's up to invertible cells. It stays blocked on E6.

### 1.6 Worked examples

**(a) Example 1 of `pseudo-vs-gray.md`.** α : F ⇒ G : B → C (hd 1 in 𝒦(B, C)), and f : x → y an element arrow of B (hd 1 in 𝒦(⊤, B)). The naturality cell is the Gray cell of f ⊗ α (f first in execution order), from α_x ; Gf to Ff ; α_y.
- α unmarked: no rule applies; the cell is directed, and the reverse is not derivable (Theorem 1(2) of `pseudo-vs-gray.md` §3.6).
- α marked ps: (PS-fac) with j = 2 (α), i = 1 (f, d₁ = 1). The cell is inv, so its inverse α_f⁻ˡ is a term: pseudo naturality, one mark.
- f marked inv, α unmarked: (INV-fac). The lax naturality cell at an invertible arrow is invertible. This is the former [conj] of `pseudo-vs-gray.md` §3.5, now a sound rule (Lemma 2.1).

**(b) Composites of pseudo transformations.** α : F ⇒ G, α′ : G ⇒ H, both ps, in 𝒦(B, C).
- Vertical α ; α′: coh over Σ(D¹ ∨ D¹), a single hom; top generators α, α′ are ps; (OP-ps) gives ps.
- Identity on F: coherence case, inv by (COH-inv), so ps by (INV⇒PS).
- Whiskering α ▷ K (K : C → D after α): one generator α ⊗ K, d = (1, 0), α ps: (OP-ps) gives ps. Whiskering K ; α (K : A → B before α): generator K ⊗ α, α ps: ps.
- So **pseudo transformations are closed under all composition**, with marks only on the declared ones.

**(c) The one-sidedness of ps.** α : F ⇒ G : B → C and β : H ⇒ K : C → D, with α ps, β unmarked. The interchanger of α with β is the Gray cell of α ⊗ β (α first). (PS-fac) needs the *later* factor β to be ps. So it does **not** follow that this cell is invertible. This is correct semantically: take B = ⊤. Every transformation out of ⊤ is strong (D¹ ⊗ ⊤ has no mixed cells), and α ⊗ β is then β's naturality cell at the arrow α of C, which is not invertible for a general lax β. With β ps instead, the cell is invertible.

**(d) Adjunction.** η : 1 ⇒ RL, ε : LR ⇒ 1 marked ps; the triangle modifications marked inv (they are invertible in P too). By (INV⇒PS) the modifications are ps, and their boundaries are composites of η, ε, identities and whiskerings, which are ps by (b). So all structure cells are ps*: one extra mark per structure 2-cell compared with P, and nothing else.

**(e) A ring object.** R with + and ·, equation witnesses as 2-cells between maps R³ → R (hd 1 in 𝒦(R³, R)). Declare `(R : ★)^{grpd_1}`. Then by (OBJ-k) every equation witness, every naturality cell landing in a hom 𝒦(X, R), and every higher cell into R is invertible, with no per-witness marks. This answers `pseudo-vs-gray.md` §5.3's "C has only invertible 2-cells" question for the two-tier theory.

---

## 2. Soundness of the rules [proved]

The intended models are oriented (∞,ω)-categories 𝒦 (Gepner–Heine), with an L-interpretation as in `pseudo-vs-gray.md` §3.6, Theorem 2, plus a choice of invertibility data for each invertible cell (to interpret the destructors). Morphisms of models preserve the choices; this is the usual algebraic reading, and it is what makes destructors stable under substitution. The strict test model (strict ω-Cat with the Ara–Maltsiniotis Gray tensor, strict inverses) is covered by the same arguments, with "localisation" replaced by functoriality (noted at each step).

Interpretation of the judgments: `t inv` means ⟦t⟧ is invertible; `t ps` means that for every object X and every cell y of 𝒦(X, a) with hd(y) ≥ 1 (a the 0-source of t), the composite of y and ⟦t⟧ along the Gray composition, i.e. the image of y ⊗ ⟦t⟧ under 𝒦(X, a) ⊗ 𝒦(a, b) → 𝒦(X, b), is invertible; `C grpd_k` means every cell of hom-dimension ≥ k of every 𝒦(X, C) is invertible.

Write Eᵏ := Dᵏ[top⁻¹] for the walking invertible k-cell. In Cat_ω, Eᵏ ≃ Dᵏ⁻¹ by the collapse, and a k-cell e : Dᵏ → B is invertible iff it factors through Dᵏ → Eᵏ **[recall: standard; Loubaton's and Campion's conventions agree, both use coinductive invertibility in Cat_ω]**.

**Lemma 2.1 (invertible factor).** Let A, B be (∞,ω)-categories, y : Dᵐ → A any cell (m ≥ 0) and e : Dᵏ → B an invertible cell, k ≥ 1. Then the image of the top generator of Dᵐ ⊗ Dᵏ under y ⊗ e : Dᵐ ⊗ Dᵏ → A ⊗ B is invertible. Same with the factors swapped.

*Proof.* e factors through Eᵏ, so y ⊗ e factors through Dᵐ ⊗ Eᵏ. Since ⊗ preserves colimits in each variable and Eᵏ is a pushout of Dᵏ, Dᵐ ⊗ Eᵏ ≃ Dᵐ ⊗ Dᵏ⁻¹ through the map induced by the collapse. Dᵐ ⊗ Dᵏ⁻¹ has dimension m + k − 1, so the image of the (m + k)-dimensional top generator there is an identity, hence invertible. Equivalences reflect invertibility and functors preserve it. ∎

*Strict model.* If e has a strict inverse e′, then by strict functoriality of ⊗ in the second variable, y ⊗ (e ∗ e′) = y ⊗ id is an identity, and the whiskered composite of y ⊗ e and y ⊗ e′ equals it. So y ⊗ e is strictly invertible.

**Corollary (INV-fac, INV-obj).** For g = x₁ ⊗ … ⊗ xₙ with dᵢ ≥ 1 and xᵢ[γ] invertible, write the n-fold composite as a composite of binary ones, (x₁ ⊗ … ⊗ x_{i−1}) ⊗ xᵢ ⊗ (rest), using associativity of the Gray composition. Lemma 2.1 makes the image of block ⊗ xᵢ invertible (the block may have dimension 0), and then the image of that ⊗ (rest) invertible, by Lemma 2.1 again if the rest has positive dimension and because whiskering preserves invertibility otherwise. For INV-obj: a composite of equivalences (1-cells of 𝒦) is an equivalence, using only whiskering. ∎

**Lemma 2.2 (pseudo factor).** Let β be a cell of 𝒦(C, D) with hd(β) = r ≥ 1 that is ps in the semantic sense, and y a cell of 𝒦(X, C) with hd(y) = m ≥ 1. Then y ⊗ β is invertible in 𝒦(X, D).

*Proof.* In ωCat_lax (and, by Yoneda on 𝒦's representables, in any oriented 𝒦) the cell y ⊗ β of Fun^lax(X, D) is invertible iff its adjunct D^{m+r} ⊗ X → D sends every generator of the form top ⊗ x (x any cell of X, including objects) to an invertible cell **[recall: invertibility of a cell of a lax functor category is checked on its components and all its naturality cells; this is the content of Fun^lax(X, D) ≃ Hom(X, ...) with E^{m+r} ⊗ X the localisation of D^{m+r} ⊗ X at top ⊗ X]**. That generator's image is the image of β's adjunct Dʳ ⊗ C → D on the cell top_r ⊗ y(top_m ⊗ x), whose second factor has dimension m + dim x ≥ 1. This is a mixed cell of Dʳ ⊗ C, inverted because β is ps. ∎

For X = ⊤ this is the definition of ps on elements; the lemma shows ps on elements implies ps against every generalised element. Only β's top condition is used, which is why ps (not ps*) is the right premise of (PS-fac).

**Corollary (PS-fac).** For g with xⱼ ps, dⱼ ≥ 1, and some i < j with dᵢ ≥ 1: the block x₁ ⊗ … ⊗ x_{j−1} has positive dimension, so (block) ⊗ xⱼ is invertible by Lemma 2.2, and then ⊗ (rest) stays invertible as in the previous corollary. ∎

**Lemma 2.3 (composites, OP-inv and OP-ps).** In the model, the op-case coh over Γ at γ is interpreted as a lift of the total cell T of U(Γ), a pasting composite in the ω-category 𝒦(a₀, aₙ) of the images of the generators of U(Γ). A pasting composite whose top-dimensional constituents are invertible is invertible (invertible cells are closed under composition and whiskering: Benjamin–Markakis, Hoshino et al.; in (∞,ω) standard). This gives (OP-inv). For (OP-ps): y ⊗ T is a pasting composite of the cells y ⊗ g over the generators g of U(Γ), with top constituents y ⊗ g for top g. Each is invertible: if g[γ] is invertible, by Lemma 2.1 (first factor y); if some xⱼ is ps with dⱼ ≥ 1, by Lemma 2.2 applied to the block (y ⊗ x₁ ⊗ … ⊗ x_{j−1}), which has positive dimension because y does. ∎

**(COH-inv)**: the coherence-case coh is interpreted as an invertible cell by Theorem 2 of `pseudo-vs-gray.md` §3.6 (the cells (D) provides between parallel cells with equal strict image are invertible). **(INV⇒PS)** is Lemma 2.1. **(OBJ-k)**: an r-cell σ of 𝒦(X, C) = Fun^lax(X, C) with r ≥ k has an adjunct Dʳ ⊗ X → C whose generators top ⊗ x have dimension r + dim x ≥ k, so they land on invertible cells of C, and σ is invertible by the criterion used in Lemma 2.2. **Substitution** preserves every judgment because marks are preserved by substitutions by definition and all side conditions are on the coh's own Γ.

**Non-collapse.** None of the rules makes an unmarked interchanger invertible: in the free model on an unmarked context, every derivation of `inv` ends in (COH-inv), a mark, or a rule whose premises include a mark; Theorem 1(2) of `pseudo-vs-gray.md` §3.6 shows the unmarked interchanger has no inverse. So two-tier L with markings is still strictly more general than P.

---

## 3. P ≈ L + marking (E5)

### 3.1 Semantic half [proved]

**Theorem 3.1.** The ∞-category of oriented (∞,ω)-categories whose composition maps invert all mixed cells is equivalent to the ∞-category of Cat_ω-enriched ∞-categories (with the cartesian product), via change of base along the comparison c : A ⊗ B → A × B.

*Proof.*
1. **n-ary localisation.** For all A₁, …, Aₙ, the comparison cₙ : A₁ ⊗ … ⊗ Aₙ → A₁ × … × Aₙ is the localisation at the images of the mixed generators (generators with ≥ 2 positive-dimensional factors, along all globe maps). Induction on n: A₁ ⊗ (A₂ ⊗ … ⊗ Aₙ) → A₁ ⊗ Π_{≥2} is A₁ ⊗ (a localisation), which is a localisation because ⊗ preserves colimits in each variable (a localisation is a pushout along ∐ Dᵏ → ∐ Eᵏ); it inverts the images of x ⊗ m with m mixed in the last n − 1 factors, which are mixed. Then A₁ ⊗ Π_{≥2} → A₁ × Π_{≥2} is a localisation at mixed cells by the binary theorem (C1′, `gray-vs-cartesian.md`, verified). A composite of localisations is a localisation at the union of the (preimages of the) inverted sets, and every cell in that union is mixed in the n-fold sense.
2. **Sub-operad.** Let Cat^⊗ and Cat^× be the monoidal ∞-categories, viewed as ∞-operads with multimorphism spaces Map(A₁ ⊗ … ⊗ Aₙ, B) and Map(A₁ × … × Aₙ, B). The comparisons make the identity a lax monoidal functor Cat^× → Cat^⊗, i.e. a map of ∞-operads. On multimorphism spaces it is precomposition with cₙ, which by step 1 is a monomorphism (precomposition with a localisation is an inclusion of components) onto the maps inverting mixed cells. A map of ∞-operads that is an equivalence on objects and a monomorphism on multimorphism spaces exhibits Cat^× as a sub-∞-operad of Cat^⊗.
3. **Algebras.** Enriched ∞-categories with object space S are algebras for the generalised ∞-operad Δ^op_S (Gepner–Haugseng) **[recall]**. Maps of generalised ∞-operads into a sub-∞-operad are the maps into the ambient one whose images of active morphisms lie in the sub-object (a monomorphism of ∞-categories is a subcategory inclusion). Every active morphism of Δ^op_S is sent to an n-ary composition, which is a composite of binary compositions and units, and those invert mixed cells by hypothesis; mixed cells of the n-fold tensor are sent by an iterated binary composite to images of mixed cells of binary tensors (or of their whiskerings), so n-ary compositions invert them too. ∎

**Remarks.**
- This is the precise form of `pseudo-vs-gray.md` §2.4's [conj] at the level of models: "L + every interchanger of every dimension invertible" has exactly the models of P. It needs the *recursive* condition only in the sense that "mixed cells" includes all dimensions; a condition on dimension-3 interchangers only would not do (the C1″ counterexample).
- *Strict analogue.* For strict Gray-enriched categories with strictly invertible interchangers the same statement is not literally true (strict A × B is a quotient, not a strict localisation, of A ⊗ B). Not needed: the strict model is only a test model for L.

### 3.2 Syntactic half [conj, partial proof]

**Conjecture 3.2.** Let L⁺ be L with every variable of hom-dimension ≥ 1 implicitly marked ps (equivalently: (PS-fac) and (INV-fac) are replaced by "every mixed Gray cell is inv"). There is a translation tr from CaTT-terms over a context Γ to L⁺-terms over Γ such that (i) tr(t) has the translated type of t; (ii) tr commutes with substitution up to an invertible L⁺ cell; (iii) every L⁺-term over a CaTT context is connected by an invertible cell to the translation of a CaTT term.

*What is proved.*
- **Composites.** A CaTT operation-case coh over Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ has dimension 1 + max dim Θᵢ, while L's op-case over Γ has hd Σ dim Θᵢ. Define tr on such a coh as the **∂⁻-layering** (§6): in the hom 𝒦(a₀, aₙ), the vertical composite, at each dimension, of the whiskerings of the composites ⟨Θᵢ⟩, in the order given by ∂⁻T. Each whiskering is an L op-case over ΣΘᵢ ∨ (objects) substituted; the vertical composites are op-cases on a single hom. So tr(composite) is an L-term, and its strict image is the cartesian composite under the collapse U(Γ) → ×. (This is the standard layering of a horizontal composite in a Gray-category.)
- **The interchanger.** The CaTT coherence (α ▷ g) ; (f′ ◁ β) → (f ◁ β) ; (α ▷ g′) over ΣD¹ ∨ ΣD¹ translates to the inverse of the L op-case T (which goes the other way), available in L⁺ by (PS-fac).
- **Coherences with equal supports.** If both sides of a CaTT coherence translate to L-terms with the same support S ⊆ U(Γ), and S is the support of a single-hom pasting scheme after substitution, the L coherence case over that scheme gives the cell.

*What is missing.* The general coherence case: tr(t) and tr(u) can have different supports in U(Γ) (e.g. different layerings), and they must be connected through mixed generators and their inverses. The missing lemma is a relative version of the coherence case: **any two parallel L⁺-terms over Γ whose strict images agree after collapsing U(Γ) → Θ₁ × … × Θₙ are connected by an invertible L⁺-term.** In the strict model this is the statement that the Gray tensor with mixed cells inverted is (Steiner-)contractible relative to the product, which is C1 at the strict level for pasting diagrams. A syntactic proof would follow the plan of Benjamin–Markakis's invertibility of coherences, with the mixed generators as additional invertible "variables". Owner: this thread; it is listed as E5 in the ledger.

### 3.3 The generality ordering

- **Two-tier L ⊂ P** (in the sense "P = two-tier L + markings"): semantic half by Theorem 3.1; syntactic half is Conjecture 3.2.
- **Every P-model is a two-tier L-model**: proved (change of base along c, §3.1).
- **Uniform L ⊂ two-tier L**, and "every two-tier model is a uniform model": blocked on E6 (there is no uniform side condition yet to compare).

---

## 4. Representables and lax homs over L (E8)

### 4.1 The hom rule over L [proposal]

`internal-hom.md` §5.4's rule carries over verbatim, with ΣΔ read in L (suspension maps L-terms to L-terms, `pseudo-vs-gray.md` §3.4):

```
(hom)    Γ ⊢ B : ★,  Γ ⊢ C : ★   ⇒   Γ ⊢ [B, C] : ★
(hom-⌜⌝) Γ ⊢ σ : ΣΔ → Γ with ends B, C   ⇒   Γ ⊢ ⌜σ⌝ : Δ ⊳ [B, C]
(hom-⌞⌟) Γ ⊢ φ : Δ ⊳ [B, C]             ⇒   Γ ⊢ ⌞φ⌟ : ΣΔ → Γ
with invertible cells ⌞⌜σ⌝⌟ → σ and φ → ⌜⌞φ⌟⌝ (no equations)
```

Under L the cells of [B, C] are **lax** transformations, modifications, and so on: the lax hom of `pseudo-vs-gray.md` §4.2–4.3, now as an object. The pseudo hom is its ps*-marked part:

```
[B, C]_ps*  :  cells φ of Δ ⊳ [B, C] such that ⌞φ⌟ sends every variable of hd ≥ 1 to a ps* term
```

By Theorem 3.1 and C1″ this is Fun(B, C) inside Fun^lax(B, C). It is not a full sub-hom (C1″ counterexample), so it is a *marking on cells*, not a new object former.

### 4.2 Shapes over L (R-A) [proposal]

R-A of `limits-representables.md` §5.2, restated over L: ⟦Θ⟧ for a pasting scheme Θ, with generic elements ιᵧ (one per cell y of Θ, hd(ιᵧ) = dim y in 𝒦(⊤, ⟦Θ⟧)), and a **restriction** operation:

```
for ψ : Δ ⊳ [⟦Θ⟧, C], the (Θ ⊗ Δ)-family  res(ψ) := { (y ⊗ x)[ιᵧ, ψ(x)] }_{y ∈ Θ, x ∈ Δ}
```

where (y ⊗ x)[ιᵧ, ψ(x)] is the Gray cell of §1.1 over ΣD^{dim y} ∨ ΣD^{dim x}: element y first, then the transformation-level cell ψ(x). Its boundary is, by construction, a composite of the cells of res(ψ) on the faces of y ⊗ x, so res(ψ) is a well-typed family **with the types it inherits from the L-terms**. Its strict image is the generator y ⊗ x of λΘ ⊗ λΔ by Theorem 1 of `pseudo-vs-gray.md` §3.6.

**Semantics [proved, given the literature].** In ωCat_lax, cells Δ ⊳ Fun^lax(⟦Θ⟧, C) correspond to maps ⟦Δ⟧ ⊗ ⟦Θ⟧ → C (Gray closedness, Campion Thm A) and ⟦Δ⟧ ⊗ ⟦Θ⟧ ≃ the free (∞,ω)-category on λΔ ⊗ λΘ (Campion Ex. 3.2, Cor. 3.5; `free-infinity-gray-of-pasting-diagrams.md`, (D)–(E)). Under this correspondence res is restriction to generators. (The factor order Θ ⊗ Δ in execution order is the lax convention fixed in `pseudo-vs-gray.md` §3.1.)

### 4.3 Where G1 goes [finding]

`pseudo-vs-gray.md` §4.2 says that under L "Gray contexts become derived notation, and G1 disappears". Splitting the universal property in two:

- **Elimination (using a lax cell): no Gray context needed. [proved by construction above]** Every Gray-shaped component of a native lax cell is an L-term, and their boundaries match because they are defined as the boundaries of those terms.
- **Introduction (building a lax cell from components): a Gray-shaped context is needed.** The universal property of ⟦Θ⟧ must say that every (Θ ⊗ Δ)-family in C is res(ψ) for some ψ, up to invertible cells. Its input is a family of *variables* indexed by the generators of Θ ⊗ Δ, typed by composites of lower ones along Gray molecules. Writing that context requires choosing, for every generator, source and target terms whose own types match **syntactically**. That is exactly G1.

So L moves G1 but does not remove it. Two things improve:
1. In L the needed boundary terms always exist (they are the L-terms of res in the generic case, with the generic cells replaced by variables), so the question is only whether the choices can be made *consistently*: Conjecture CT below.
2. Only the introduction rule needs it. All derived constructions that start from existing lax cells (composition, whiskering, naturality, the limit rules' comparison cells) are unaffected.

**Conjecture CT (canonical Gray terms)**, posed self-contained in `conjectures/canonical-gray-terms.md`: for pasting diagrams Θ and Δ there is an assignment of a term to every cell of the free strict Gray tensor ν(λΘ ⊗ λΔ) (more generally of ν(U(Γ))) that (a) sends generators to variables, (b) is built only from composition operations over globular pasting diagrams, and (c) gives the canonical term of a cell the type "canonical term of its source → canonical term of its target" **syntactically**. CT implies that the family context Fam(Θ ⊗ Δ) is a well-formed CaTT context, which is G1 for both P and L. A weaker form suffices for L: (c′) the two sides may differ by a single-hom CaTT coherence. (c′) is implied by the coherence case of L on one hom if the mismatched terms have equal support in a pasting scheme; it is open in general because Gray molecules are not globular pasting diagrams.

### 4.4 Lax homs of arbitrary domain

[B, C] for arbitrary B is the (hom) rule, so lax homs of arbitrary domain are native under L. What still needs a new rule is currying, which needs the Gray tensor of objects (D7, unchanged).

---

## 5. Cost of supports (E9)

**The conjecture as stated is false for explicit supports.** Take Γₙ = ΣD¹ ∨ … ∨ ΣD¹ (n factors). U(Γₙ) = (D¹)^⊗n, the oriented n-cube, with 3ⁿ cells. The op-case coh T over Γₙ is a term of size O(n) (one coh, a substitution of 2n + 1 + n terms) whose support is all 3ⁿ cells. The chains in its table also blow up: the k-dimensional source of the oriented n-cube has C(n, k) cells of dimension k **[checked for k = 0, 1, n − 1, n; the general count is the standard one for orientals/cubes, recall]**, so the table of T has total size Σ_k C(n, k) ≈ 2ⁿ. Any decision procedure that materialises supports or full chain tables is exponential in the horizontal width n.

**What can still be polynomial.** Two observations:
1. Equality of cells of ν(K) is equality of top chains plus equality of sources and targets (definition of the table). The type of a term already carries its source and target as terms, so a checker can compare *top chains* at each level and recurse into the type, with memoisation over shared subterms.
2. Top chains of the cells that occur are small in the examples: the top chain of ∂⁻T is n generators; of T, one.

**Restated question (E9′) [conj].** Is the L side condition decidable in time polynomial in the DAG size (with sharing) of the term and its type? The recursion of observation 1 visits the iterated sources of the type, and those have top chains of size up to C(n, n/2). So the procedure is polynomial if and only if terms of polynomial DAG size cannot have types whose iterated sources have exponentially large top chains, which needs a lower bound on the size of terms denoting the k-source of the n-cube. Open; the natural experiment (time the checker on Γₙ for n = 1…8) is passed to the L-core Agda thread.

---

## 6. Surface defaults (E10), settled by counts

The questions were `pseudo-vs-gray.md` §8 Q2–Q3: marking defaults for objects and transformations, and the default layering of horizontal composites. Per project standard 3, these are settled by a worked comparison.

### 6.1 Marking defaults

Three candidate policies:
- **(M0) kernel only.** No defaults; the user writes every mark the rules need.
- **(M1) declaration marks + derivation.** Marks are written only on declared variables (`pseudo`, `inv`, `grpd_k`); everything else is derived by §1.2.
- **(M2) pseudo by default.** Every declared 2-cell is ps* unless written `lax`.

Counts on the worked examples (number of annotations the user writes):

| Example | P | M0 | M1 | M2 |
|---|---|---|---|---|
| Lax transformation and naturality (`pseudo-vs-gray.md` Ex. 1) | ~5 steps | 0 | 0 | 1 (`lax`) |
| Pseudo transformation and naturality | 0 | ps on α, plus inv on each naturality cell used | 1 (ps on α) | 0 |
| Composite of 3 pseudo transformations | 0 | 3 + one per composite | 3 | 0 |
| Adjunction (η, ε, two triangle modifications) | 2 (inv on modifications) | ≥ 6 | 4 (ps on η, ε; inv on modifications) | 2 |
| Monad (η, μ, three coherence modifications) | 3 | ≥ 8 | 5 | 3 |
| Ring object R (+, ·, ~8 equation witnesses) | 8 (inv) | 8+ | 1 (`grpd_1` on R) | 1 |
| Lax colimit / Grothendieck construction | heavy (lax homs) | 0 | 0 | one `lax` per transformation |

Reading:
- M0 is dominated by M1 everywhere; M1's derivation is what §1's rules exist for.
- M1 vs M2: M2 saves one mark per pseudo structure cell and costs one per lax cell. Standard 4 (most general by default) picks the default that does not silently strengthen hypotheses: under M2, forgetting `lax` silently proves a weaker theorem (one about pseudo transformations only); under M1, forgetting `pseudo` makes the proof fail to check, which is visible.
- **Decision: M1.** The kernel has no defaults (it is the most general system); the surface writes marks only at declarations, and a missing mark shows up as a type error, not as a silently weaker statement. M2 can be offered as a per-file pragma later, since it is purely an elaboration of M1.

### 6.2 Default layering

For a composite of two cells across objects, the two layerings are ∂⁻ and ∂⁺ of the Gray generator (`pseudo-vs-gray.md` §3.4). For f (element arrow, first) and α (transformation, later): ∂⁻(f ⊗ α) = α_x ; Gf and ∂⁺(f ⊗ α) = Ff ; α_y.

**Decision: the default horizontal composite is the ∂⁻-layering.** Reason, checked on the examples: the op-case interchanger always goes ∂⁻ → ∂⁺, so from the default every other layering is reachable by a derivable cell, while from the ∂⁺ default nothing is reachable without a ps mark. In Example 1 the default is α_x ; Gf and the naturality cell goes from it, matching the Bénabou/JFS lax convention fixed in §3.1 there. With ps marks, the inverse makes the choice irrelevant, as in P.

---

## 7. E6: an attempt on the uniform construction

*Problem: `conjectures/strict-lax-interchange-at-every-level.md`, corrected (boundary-adjusted) reading. Out to a researcher as well.*

**Observation 7.1 (no single-complex presentation) [proved].** Let K be any augmented directed complex with basis containing 2-cells α : f ⇒ f′ and β : g ⇒ g′ with f, f′ : x → y and g, g′ : y → z. In ν(K), the cells (α ▷ g) ; (f′ ◁ β) and (f ◁ β) ; (α ▷ g′) have the same table: top chain α + β, 1-chains f + g and f′ + g′, 0-chains x and z. So they are equal, and interchange along 0-cells is strict in ν(K).

So a structure with directed interchange along 0-cells can never be ν of a complex; two-tier L escapes this by applying ν **hom-wise** (to U(Γ) = Θ₁ ⊗ … ⊗ Θₙ, where the expanded basis α ⊗ g vs α ⊗ g′ separates the two layerings; this is the researcher's §3 point). The same argument one level up shows that the homs of a uniform free structure cannot be ν of complexes either: within the hom, composition along hom-0-cells would again interchange strictly. Hence:

**Consequence.** A uniform free structure F(Γ) with a Steiner-like description must be a *tower*: objects; for each pair of objects a hom presented again as objects and homs; and so on, with ν used only at the bottom of each branch, if at all. For Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ the hom over [aᵢ, aⱼ] should be a "Gray tensor" F(Θᵢ₊₁) ⊠ … ⊠ F(Θⱼ) of such towers, with generators the tuples of generators of the F(Θ)'s (the recursive guess), and the hom of a tensor of towers is again a tensor of towers.

**Where it stalls.** The hom of A ⊠ B between two objects is not the tensor of homs of A and B: in the Gray tensor of 2-categories the hom between (a, b) and (a′, b′) is generated by paths alternating A- and B-steps. So ⊠ of towers must be defined by a recursion that builds those path homs, and each path hom is itself a "Gray tensor of sequences of homs". This is the same recursion that defines Gray tensors of Gray-categories, where Crans and Bourke–Gurski found that no monoidal biclosed structure exists. The difference here is that only *free towers on pasting diagrams* are needed, and closure under substitution (requirement 5) only for those, so the obstruction does not apply directly, but no definition is in hand.

**A testable first case.** Γ = Σ(ΣD¹ ∨ ΣD¹) ∨ ΣD⁰ ... is still a suspension of the two-tier case and gives nothing new. The first genuinely uniform case is two 3-cells A, B side by side along a 0-cell, Γ = ΣD² ∨ ΣD², where the hom U = D² ⊗ D² (two-tier) contains pairs of hom-cells side by side along hom-0-cells (e.g. the whiskered faces of the 4-dimensional generator), whose interchange uniform L must direct. Computing the extra generators this forces in dimension 5, and checking them against the boundary-adjusted comparison (4) of the researcher response, is the concrete next step. It is a finite computation and is listed under E6 in the ledger.

**Status.** E6 stays open (in progress here, and out to the researcher). E7 stays blocked on it. §1.5 is the adjacent marking design, ready for when the construction exists.

---

## 8. Open items from this note

| Item | Status | Owner |
|---|---|---|
| Conjecture 3.2 (syntactic P ≈ L⁺), via the relative coherence lemma | open | this thread (E5) |
| Conjecture CT (canonical Gray terms), the L form of G1 | open; self-contained statement in `conjectures/canonical-gray-terms.md` | this thread (E8) |
| E9′ (polynomial side-condition check with sharing) | open; experiment handed to LCORE | this thread + LCORE |
| §1.4: rec admissible | open, low priority | this thread |
| E6 first uniform case (ΣD² ∨ ΣD², dimension 5) | in progress | this thread |
| Agda: encode inv/ps judgments, the propagation rules, and the Example 1.6 checks | to start | LCORE (asked) |
