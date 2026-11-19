# Fibration test over non-suspension bases, and whether bubble-freeness suffices

*Working note for ledger item B14 (thread "Prove fibration test over non-suspension bases", started 2026-11-18). It continues `answered/finite-fibration-test-higher-base-r4-2026-11-18.md` and answers Question 1 of the unsent round-5 prompt (`outbox/finite-fibration-test-higher-base-r5.md`) internally. Item numbers "(R5 item n)" refer to §2 of that prompt. Composition is diagrammatic (`notes/conventions.md` §1): `;` for 1-cells, `·` for vertical composition of 2-cells, `∗` for whiskering.*

Status summary:

- **§1–§3, proved here; confirmed independently.** Round 5 (`answered/finite-fibration-test-higher-base-r5-2026-11-18.md` §1, §2.3, verified 2026-11-18) gives an explicit unlocalised attaching map for ζ by outer-cylinder subdivision, which needs only R a = R b. It also proves Cat fibres over every 3-computad base whose 2-skeleton is homotopical and whose 3-cell attachment is a homotopy pushout, which contains Theorem A. FT₃ holds over **every** finite 3-computad base Γ such that Γ and its 2-skeleton are homotopical, for weights valued in categories free on finite graphs. In particular it holds over the non-suspension base ζ of R5 item 8. The new ingredient is an unlocalised lift of the FT₃ data along **right whiskering**, which uses the naturality cells η^r on the paths a_e. The presentation has one generator `g ⊗ c` per base k-generator g (k ≥ 1) and generator c of the source fibre, in dimension k + dim c. Dimension ≤ 4.
- **§4, sketched.** The same argument gives FT_n over every homotopical n-computad base (all skeleta homotopical) with Cat-valued free fibres, using item 16's suspension blocks for the globes D_k and ∂D_k. Fibres of dimension ≥ 2 remain open (R5 Question 2).
- **§5, open.** Bubble-free ⇒ homotopical is a strengthening of Guetta's open Conjecture 6.6.5. The bubble obstruction already proved (R5 item 17) settles the "only if" half of Guetta's conjecture. The note also gives a reformulation as a collapse problem over a **positive** computad, and proposes a decidable subclass, the *one-sided* 2-computads, that contains the positive ones, both operadic classes and Q, and is automatically bubble-free.

---

## 1. Conventions for the FT₃ data

Fix the orientation of R5 items 9 and 12. For a base 1-cell w : b → b′ with W = T(w), a fibre vertex e and a fibre arrow f : e → e′ of T(b):

- `w_e : (b, e) → (b′, We)`, marked (cocartesian lift);
- `η^w_f : w_e ; Wf ⇒ f ; w_{e′}`, inverted;
- for a base 2-cell α : u ⇒ v with a = T(α) : U ⇒ V, `λ_{α,e} : u_e ; a_e ⇒ v_e`, marked (prescribed target);
- `Ξ_{α,f} : (λ_{α,e} ∗ Vf) · η^v_f ⇛ (η^u_f ∗ a_{e′}) · (f ∗ λ_{α,e′})`, inverted. The source of both sides is `u_e ; Uf ; a_{e′} = u_e ; a_e ; Vf`, by strict naturality of a in the free category T(b′).

R5 item 3 orients θ the other way. Reversing an inverted generator does not change the localisation (`Free(s : a → b)[s⁻¹] ≃ Free(s′ : b → a)[s′⁻¹]`), so the choice is free. The orientation above is the one for which right whiskering needs no inverse (§2.2).

**Paths.** For a fibre path g = g₁ ; … ; g_n in T(b), put `η^w_g := (η^w_{g₁} ∗ W(g₂…g_n)) · (g₁ ∗ η^w_{g₂…g_n})`, and the identity when n = 0. This is R5 item 12's path rule. Then `η^w_{g;h} ≃ (η^w_g ∗ Wh) · (g ∗ η^w_h)` up to the coherence equivalences of Free(Ψ). For a base path w₁ ; w₂ put `(w₁;w₂)_e := w₁_e ; w₂_{W₁e}` and `η^{w₁;w₂}_f := (w₁_e ∗ η^{w₂}_{W₁f}) · (η^{w₁}_f ∗ w₂_{W₁e′})`, again as in R5 item 12.

## 2. Lifting the FT₃ data to every 2-cell of the base, without inverses

Let Γ₂ be a finite 2-computad and Ψ₂ the unlocalised presentation of R5 item 12 for T restricted to F₂(Γ₂). Every 2-cell of F₂(Γ₂) is an identity or a vertical composite of whiskered generators `w₁ ∗ g ∗ w₂`. So it suffices to lift λ and Ξ along identities, vertical composites, left whiskering and right whiskering. "Lift" means a cell of **Free(Ψ₂)**, not of its localisation, with the boundary required by §1.

### 2.1 Identities, vertical composites, left whiskering

- **Identity** 1_u : a_e = 1, so `λ_{1_u,e} := 1_{u_e}` and `Ξ_{1_u,f} := 1`.
- **Vertical composite** δ = β · γ : R5 item 15, `λ_{δ,e} = (λ_{β,e} ∗ c_e) · λ_{γ,e}`, with Ξ_δ pasted from Ξ_β and Ξ_γ.
- **Left whiskering** by w : b″ → b (fibre map W), for α : u ⇒ v out of b:
  - `λ_{w▷α,e} := w_e ∗ λ_{α,We}`;
  - `Ξ_{w▷α,f} := (w_e ∗ Ξ_{α,Wf}) · (η^w_f ∗ v_{We′})`, up to interchangers, where `Ξ_{α,Wf}` is Ξ pasted along the path Wf. The boundary check is the mirror image of §2.2 and uses only η^w_f in the forward direction.

### 2.2 Right whiskering (the new case)

Base: α : p ⇒ q : x → y, r : y → z. Fibres A = T(x), B = T(y), C = T(z), with P, Q : A → B, R : B → C and a = T(α) : P ⇒ Q. Then T(α ▷ r) = a ∗ R has components R(a_e).

**Lift of λ.**
```
λ_{α▷r,e} := (p_e ∗ η^r_{a_e}) · (λ_{α,e} ∗ r_{Qe})
          :  p_e ; r_{Pe} ; R(a_e)  ⇒  p_e ; a_e ; r_{Qe}  ⇒  q_e ; r_{Qe}.
```
Its source is `(p;r)_e ; R(a_e)` and its target is `(q;r)_e`, as §1 requires. Only η^r is used, in its forward direction.

**Lift of Ξ.** The required boundary is
```
(λ_{α▷r,e} ∗ RQf) · η^{q;r}_f   ⇛   (η^{p;r}_f ∗ R a_{e′}) · (f ∗ λ_{α▷r,e′}).
```
Expanding with §1 and applying one interchanger on each side:

- **Left side.** `(p_e ∗ η^r_{a_e} ∗ RQf) · (λ_{α,e} ∗ r ∗ RQf) · (q_e ∗ η^r_{Qf}) · (η^q_f ∗ r)`. The middle two factors interchange to `((p_e;a_e) ∗ η^r_{Qf}) · (λ_{α,e} ∗ Qf ∗ r)`. Hence the left side is `(p_e ∗ η^r_{a_e;Qf}) · (LHS(Ξ_{α,f}) ∗ r_{Qe′})`.
- **Right side.** `(p_e ∗ η^r_{Pf} ∗ Ra_{e′}) · (η^p_f ∗ r ∗ Ra_{e′}) · (f ∗ p_{e′} ∗ η^r_{a_{e′}}) · (f ∗ λ_{α,e′} ∗ r)`. The middle two factors interchange to `((p_e;Pf) ∗ η^r_{a_{e′}}) · (η^p_f ∗ a_{e′} ∗ r)`. Hence the right side is `(p_e ∗ η^r_{Pf;a_{e′}}) · (RHS(Ξ_{α,f}) ∗ r_{Qe′})`.

In the free category B, `a_e ; Qf = Pf ; a_{e′}` is an equality of **words**, so `η^r_{a_e;Qf}` and `η^r_{Pf;a_{e′}}` are the same pasting. Therefore
```
Ξ_{α▷r,f} := ι′ · ( 1_{p_e ∗ η^r_{a_e;Qf}} · (Ξ_{α,f} ∗ r_{Qe′}) ) · ι
```
has the required boundary, where ι and ι′ are the interchange equivalences. Interchangers are invertible cells of the (∞,ω)-category Free(Ψ₂) itself. They are not marked generators, so no localisation is involved.

**Why the orientation matters.** With θ oriented as in R5 item 3 (`a ; r ⇒ r ; Ra`), λ_{α▷r} would need θ⁻¹. This is the same phenomenon as R5 item 11, and the orientation of §1 avoids it.

### 2.3 Marking

The lifts must land in the marking of ∫T, the cartesian cells, after localisation. The η's and Ξ's become invertible, hence marked. For λ: in the strict Grothendieck construction a 2-cell over α from (u, m) to (v, n) is a fibre morphism `m ⇒ a_e ; n`, and it is cartesian exactly when that morphism is an identity. This property is preserved by vertical composition and by whiskering with any 1-cell on either side: right whiskering applies the functor R, which preserves identities, and left whiskering precomposes. So every λ lift above is cartesian.

## 3. FT₃ over homotopical 3-computad bases

**Theorem A.** Let Γ be a finite 3-computad such that `Free(Γ) ≃ F₃(Γ)` and `Free(Γ₂) ≃ F₂(Γ₂)`, and let `T : F₃(Γ) → Cat` take values in categories free on finite graphs. Then ∫T is presented by the finite marked computad Ψ with the following generators:

- the generators of the fibres T(x), for x a vertex of Γ;
- the R5 item 12 data over Γ₂: w_e, η^w_f, λ_{α,e}, Ξ_{α,f};
- for each 3-generator Ω : s ⇛ t of Γ, with s, t : u ⇒ v 2-cells of F₂(Γ₂) out of the vertex x:
  - a marked 3-generator `ω_{Ω,e} : λ_{s,e} ⇛ λ_{t,e}` for each vertex e of T(x);
  - a 4-generator `K_{Ω,f} : Ξ_{s,f} · L_{ω,f} ⇛ R_{ω,f} · Ξ_{t,f}` for each arrow f of T(x), with L, R as in R5 item 6.

  Here λ_s, λ_t, Ξ_s and Ξ_t are the §2 lifts.

Localise at all η, Ξ and K. The parallelism needed for ω is `T(s) = T(t)`, which holds because T(Ω) is an identity in the 2-category Cat.

**Generator count.** For every base k-generator g (k ≥ 1) with source vertex x, there is one generator `g ⊗ c` of dimension k + dim c for each generator c of T(x). It is marked when c is a vertex and inverted when c is an arrow. These are the relative Gray-tensor generators, as in R5 items 6 and 16.

**Proof.**

1. **Base pushout.** Free(Γ) is by definition `Free(Γ₂) ∐_{∐ ∂D₃} ∐ D₃`, one D₃ per 3-generator. By hypothesis this is F₃(Γ), and its 2-skeleton is F₂(Γ₂).
2. **Totals over the pieces.** By Loubaton Cor. 3.2.3.16 (pullback along a left cartesian fibration preserves colimits),
   ```
   ∫T ≃ ∫_{F₂(Γ₂)} T  ∐_{∐ ∫_{∂D₃} T_Ω}  ∐ ∫_{D₃} T_Ω,
   ```
   where T_Ω is T pulled back along the map D₃ → F₃(Γ) classifying Ω.
3. **The pieces are presented.**
   - ∫_{F₂(Γ₂)}T is presented by Ψ₂ (R5 item 12).
   - ∫_{D₃}T_Ω is the walking-3-cell weight with fibres T(x) and T(x′), U = T(u), V = T(v) and a = T(s) = T(t), so it is presented by Ψ_{D₃} (R5 item 6).
   - ∫_{∂D₃}T_Ω is presented by the sub-computad Ψ_∂ ⊂ Ψ_{D₃} obtained by deleting ω and K. This is R5 item 12 for the positive 2-computad ∂D₃.
4. **The attaching map exists before localisation.** Define `φ : Ψ_∂ → Free(Ψ₂)` on generators:
   - `u_e ↦ (u)_e` and `η^u_f ↦ η^u_f`, the path lifts of §1 (similarly for v);
   - `λ_{α,e} ↦ λ_{s,e}` and `Ξ_{α,f} ↦ Ξ_{s,f}`, the §2 lifts (similarly for β ↦ t).
   
   The image of each generator lies over the correct base cell, and φ is the identity on the fibres T(x) and T(x′).
5. **φ is the right map.**
   - After localisation, φ is a map of marked (∞,ω)-categories over ∂D₃ into the pullback `∫_{F₂(Γ₂)}T ×_{F₂(Γ₂)} ∂D₃ = ∫_{∂D₃}T_Ω`. It preserves marked cells by §2.3.
   - Both sides are left cartesian fibrations over (∂D₃)^♯, and φ is the identity on fibres over the two vertices.
   - Under straightening (Loubaton Thm 4.1.4.2), φ is therefore a natural transformation T_Ω|_{∂D₃} ⇒ T_Ω|_{∂D₃} whose components are equivalences, so φ is an equivalence.
   
   Any choice of representatives for the composites in §2 works, because only this fibrewise property is used.
6. **Assemble.** Ψ = Ψ₂ ∐_{Ψ_∂} ∐ Ψ_{D₃}, i.e. Ψ₂ plus the generators ω and K attached along φ. Free sends this pushout of computads to a pushout of (∞,ω)-categories, and localisation commutes with colimits (it is a pushout along `∐ D_n^t → ∐ (inverted)`). Hence `Free(Ψ)[S⁻¹]` is the pushout in step 2, which is ∫T. ∎

### 3.1 The base ζ of R5 item 8

Base Γ: vertices x, y, z; arrows p, q : x → y and r : y → z; 2-cells α, β : p ⇒ q; 3-cell `ζ : α ▷ r ⇛ β ▷ r`. Γ is homotopical by R5 item 8, and Γ₂ is positive, hence homotopical by Chanavat Cor. 3.39. With A, B, C, P, Q, R as in §2.2, a = T(α) and b = T(β), we have R(a_e) = R(b_e), since T(ζ) is an identity. Note that a_e ≠ b_e is allowed: the lifts λ_{α▷r,e} and λ_{β▷r,e} use the different pastings η^r_{a_e} and η^r_{b_e}, and they are still parallel.

The presentation consists of:

- the vertices and arrows of A, B and C;
- marked `p_e, q_e` (e ∈ A) and marked `r_d` (d ∈ B);
- inverted `η^p_f, η^q_f` (f in A) and `η^r_g` (g in B);
- marked `λ_{α,e}, λ_{β,e}` and inverted `Ξ_{α,f}, Ξ_{β,f}`;
- marked `ω_e : (p_e ∗ η^r_{a_e}) · (λ_{α,e} ∗ r_{Qe})  ⇛  (p_e ∗ η^r_{b_e}) · (λ_{β,e} ∗ r_{Qe})`, one per vertex e of A;
- inverted 4-generators `K_f : Ξ_{α▷r,f} · L_{ω,f} ⇛ R_{ω,f} · Ξ_{β▷r,f}`, one per arrow f of A.

The total dimension is ≤ 4.

### 3.2 Checks

- **Terminal weight** (A = B = C = 1). The presentation is Γ itself: the λ lifts reduce to λ_α ∗ r, since η^r of the empty path is an identity. ✓
- **Product weight** (A = B = C = [1], identity functors, identity transformations). The generator counts are (6, 9, 7, 4, 1), so χ = 1 = χ(Γ) · χ([1]). ✓
- **A weight with a_e ≠ b_e**:
  - Setup: A = C = 1, B free on two parallel arrows m, n : s → t, P(∗) = s, Q(∗) = t, a = m, b = n, and R constant.
  - Cells: 4 vertices; arrows m, n, p_∗, q_∗, r_s, r_t; 2-cells η^r_m, η^r_n, λ_α, λ_β; one 3-cell ω.
  - The 2-skeleton has π₁ = 1 and H₂ ≅ ℤ, generated by the cycle `η_m + λ_α − η_n − λ_β`. That cycle is exactly the boundary of ω, so the presentation groupoidifies to a point.
  - This agrees with Thomason's hocolim of (pt, S¹, pt) over this base, which is contractible: the S¹ = |B| is filled by the two λ's and the two η's, and ω kills the resulting 2-sphere. ✓

## 4. FT_n with Cat-valued fibres (sketch)

**Theorem A′ (sketch; for n ≥ 4 only a conjecture, see §6 item 6).** Let Γ be a finite n-computad with every skeleton homotopical (`Free(Γ_k) ≃ F_k(Γ_k)` for k ≤ n), and T : F_n(Γ) → Cat with values free on finite graphs. Then ∫T is presented by the fibre generators and one generator `g ⊗ c` per base k-generator g (k ≥ 1) and generator c of its source fibre. These are marked for c a vertex and inverted for c an arrow, with dimension ≤ n + 1. The proof is the induction of §3, with these inputs:

- **Local blocks.** Over D_k, use R5 item 16 with Q = D_{k−1}. Over ∂D_k = Σ∂D_{k−1}, use item 16 with Q = ∂D_{k−1}. Both are homotopical: Σ commutes with Free, since it preserves colimits of bipointed objects, and Σ F_m(Λ) = F_{m+1}(ΣΛ).
- **Lifts of composites.** For k ≥ 3, T of every k-cell is an identity, so the k-dimensional lifts of composites are built from the lower ones exactly as in §2. ∗_j-composites for j ≥ 1 are composites of lifts. Right whiskering by r uses `p_e ∗ η^r_{a_e}`, and the lower faces are parallel because a_e is the same on both sides.
- **Marking.** For k ≥ 3 the marking check is automatic: the fibres are 1-categories, so the iterated hom fibrations of ∫T have discrete fibres in dimension ≥ 3, and every cell there is cartesian.

This closes the Cat-fibre part of R5 Question 2. Fibres of dimension ≥ 2, which need the double-cylinder blocks of R5 item 9 at every level, remain open.

## 5. Is bubble-freeness sufficient? (R5 Question 3)

### 5.1 Literature

- Guetta, *Homology of strict ω-categories* (PhD thesis, 2021, [arXiv 2104.12662](https://arxiv.org/abs/2104.12662)), §6.6 defines bubbles (Def. 6.6.1) and states **Conjecture 6.6.5**: *a free 2-category is homologically coherent iff it is bubble-free*. 6.6.6 says the author has "no real hint towards a proof".
- Homotopicality (`Free(Γ) ≃ F₂(Γ)`) implies homological coherence: the groupoidification of Free(Γ) is the CW complex whose cellular chains are the polygraphic chains. So **bubble-free ⇒ homotopical implies the "if" half of Guetta's conjecture**, and is at least as hard.
- Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) covers positive 2-polygraphs (Cor. 3.39) via frame-acyclic directed complexes. Non-positive generators such as η : 1 ⇒ t are not regular, so Thm 3.17 does not apply to them.
- No later result on Conjecture 6.6.5 was found (searches 2026-11-18).

### 5.2 The "only if" half of Guetta's Conjecture 6.6.5 follows from R5 item 17

Let P be any free 2-category, finite or not, with a bubble q. The R5 item 17 argument gives:

- strict 2-functors i : B²ℕ → P and r : P → B²ℕ with r ∘ i = [k], k ≥ 1;
- since |B²ℕ| ≃ K(ℤ,2) (Ara, Quillen B, Ex. 4.10), H^Sing_{2j}(P; ℚ) ≠ 0 for every j ≥ 1.

Polygraphic homology of a free 2-category vanishes above degree 2. So P is not homologically coherent. Guetta states the conjecture as an equivalence and proves this direction only for examples, so this half appears to be new. Before claiming it outside the project, it should be checked against Guetta's later papers.

### 5.3 Reformulation over a positive computad

Given a finite 2-computad Γ, let Γ⁺ add a 1-generator e_x : x → x for each vertex x, and replace every empty boundary path at x by e_x:

- a creator 1_x ⇒ w becomes e_x ⇒ w;
- an annihilator w ⇒ 1_x becomes w ⇒ e_x;
- a generating bubble becomes e_x ⇒ e_x.

Γ⁺ is positive, hence homotopical (Chanavat Cor. 3.39). Collapsing each e_x to 1_x is a pushout of computads, so by cocontinuity of Free:
```
Free(Γ) ≃ Free(Γ⁺) ∐_{∐ C_x} ∐ {x},        C_x = the free category on one loop.
```
The strict analogue `F₂(Γ) = F₂(Γ⁺) ∐^{strict}_{∐ C_x} ∐ {x}` also holds. Hence:

> **Lemma B.** Γ is homotopical iff the strict collapse of the loops e_x in F₂(Γ⁺) is a homotopy pushout in (∞,2)-categories.

This turns R5 Question 3 into a question about collapsing endo-1-cells in a **positive** free 2-category. A bubble of Γ is a nonidentity 2-cell of F₂(Γ⁺) between words in the e_x alone. Example: for σ : 1 ⇒ 1, Γ⁺ = (x; e; σ⁺ : e ⇒ e) is homotopical, but the collapse produces B²ℕ.

### 5.4 A decidable subclass: one-sided 2-computads

Call Γ **target-nonempty** if every 2-generator has a nonempty target path, and **source-nonempty** dually. Call it **one-sided** if it is either.

- **One-sided ⇒ bubble-free.** Write a putative bubble as a vertical composite of whiskered generators. Its last factor has target `w₁ ; t(g) ; w₂ = 1_x`, so t(g) is empty, which a target-nonempty Γ forbids. Dually for source-nonempty.
- **The class is decidable and contains all known homotopical 2-computads:**
  - positive ones;
  - both operadic classes of R5 item 13 (single generating arrow as target, respectively as source);
  - Q = (∗; t; η : 1 ⇒ t).
- **It excludes both known non-homotopical examples:** σ : 1 ⇒ 1 (both sides empty) and R = (η : 1 ⇒ t, ε : t ⇒ 1) (mixed).

**Conjecture C.** Every finite one-sided 2-computad is homotopical.

Conjecture C is exactly the "decidable sufficient condition covering positivity, the operadic criterion and Q" asked for in R5 Question 3. In the language of Lemma B, for target-nonempty Γ the loop e_x occurs in Γ⁺ only in sources. So in F₂(Γ⁺) every e_x is consumed and never produced, which is the situation where the collapse should be computable by a cofinality argument on "where the e_x are inserted".

### 5.5 Heuristic for the general statement

Under a weak Joyal–Street principle, hom-spaces of Free(Γ) are moduli spaces of progressive plane diagrams, and each strict 2-cell is an isotopy class. Homotopicality then says each isotopy class has contractible moduli.

- **Bubble case.** A closed component (a bubble) floats in a 2-dimensional face. n bubbles give configuration spaces of the plane, which is the K(ℤ,2) phenomenon.
- **Bubble-free case.** Every component of the diagram meets the boundary of the disk, so every complementary face is simply connected. The height function on a simply connected face has a tree as Reeb graph, so the space of monotone positions of a creator or annihilator in its face looks contractible.

So bubble-freeness is exactly the hypothesis this picture needs. Making it a proof needs (i) the weak Joyal–Street identification and (ii) contractibility of moduli of boundary-connected progressive diagrams. Neither is in the literature as far as the 2026-11-18 search found.

## 6. Open items left by this note

1. ~~Independent check of Theorem A~~: done by round 5 §1 and §2.3.
2. Theorem A′ (§4) for n ≥ 4 in its unaugmented form (no auxiliary generators) is an instance of the open recognition question. That question is posed in `outbox/fibration-presentations-characterization-r3.md`. Presentations of dimension ≤ n + m *with* auxiliary generators exist for every pair (`answered/fibration-presentations-characterization-r2-2026-11-19.md`), so A′ is no longer needed for existence.
3. ~~FT_n with fibres of dimension ≥ 2~~: settled by the same r2 answer (dimension ≤ n + m, optimal).
4. ~~Conjecture C and bubble-free ⇒ homotopical~~: `answered/homotopy-polygraphs-2026-11-19.md` proves that a finite 2-polygraph is homotopical iff it is bubble-free (Heidemann inputs taken on trust). Since one-sided implies bubble-free (§5.4), Conjecture C follows. Since homotopical implies homologically coherent, and §5.2 gives the converse half, this settles Guetta's Conjecture 6.6.5 for finite 2-polygraphs, modulo the same trusted inputs.
5. Check §5.2, and the consequence for Guetta's conjecture in item 4, against the post-2021 literature before citing either outside the project.
6. (2026-11-19) The uniform relative-Gray presentation fails from base dimension 4 (pentagon counterexample, `answered/fibration-presentations-all-dimensions-2026-11-19.md` §1). It is machine-checked in `src/CaTTExp/Fibration/PentagonCounterexample.agda`. The checker policy for bases of dimension ≥ 4 is in `limits-metatheory.md` §9.5. The counterexample's fibre is 3-dimensional, so it does not refute Theorem A′ (§4, Cat-valued fibres). But A′'s "lifts of composites" step for n ≥ 4 makes the same kind of unchecked assumption, namely that positive lifts exist. A′ is therefore only a conjecture for n ≥ 4. With one-sided inverse data allowed (§9.5), the existence part goes through by the compactness sketch there.
