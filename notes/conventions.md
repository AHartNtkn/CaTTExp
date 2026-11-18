# Conventions: composition order, Gray tensor, lax and oplax

*The single place where the project fixes its orientation conventions (ledger item G2, closed 2026-11-18). Every other note cites this file instead of stating its own. Each claim is marked **[paper]** (checked against the cited source, with the exact place) or **[computed]** (checked here by a short calculation that is written out).*

If a note disagrees with this file, this file wins and the note is a bug.

---

## 1. Composition order

- `f ; g` and `f · g` mean **diagrammatic order**: first f, then g. CaTT terms, Mikhail's rules and the L-core notes use this.
- `g ∘ f` means **classical order**: also first f, then g.
- "Execution order" for a list of factors means first-executed factor first, i.e. diagrammatic order.

## 2. The Gray tensor

We use the Ara–Maltsiniotis / Steiner orientation throughout.

- **Augmented directed complexes.** For basis elements x, y of dimensions p, q,
  ```
  ∂(x ⊗ y) = ∂x ⊗ y + (−1)^p x ⊗ ∂y
  ```
  **[paper]** Steiner, *Omega-categories and chain complexes*, HHA 2004 ([math/0403237](https://arxiv.org/abs/math/0403237)), Example 3.10.
- **Boundaries of a product generator.** With dim x = m and a sign α ∈ {−, +},
  ```
  ∂^α(x ⊗ y) = composite of (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^m α} y)
  ```
  This is the Leibniz formula read off on positive and negative parts. It is the form used in `internal-hom.md` §4.1.
- **Strict ω-categories.** The Gray tensor ⊗ on strict ω-Cat is the unique monoidal structure that extends the tensor of strong Steiner complexes along ν and is cocontinuous in each variable. It is **biclosed and not symmetric**, with unit D⁰ **[paper]** (Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*, [1607.00668](https://arxiv.org/abs/1607.00668), Thm A.15, §A.16). It agrees with the tensor of Al-Agl–Steiner and Crans (Remark A.17 there).
- **ν is compatible with ⊗.** ν(K) ⊗ ν(L) ≅ ν(K ⊗ L) for strong Steiner complexes K, L **[paper]** (AM §A.16). λ(S) is a strong Steiner complex for every pasting diagram S ∈ Θ **[paper]** (AM Prop. 4.13). Tensors of strongly loop-free unital bases are strongly loop-free **[paper]** (Steiner, Example 3.10).
- **(∞,ω).** Campion's Gray tensor on Cat_n (n ∈ ℕ ∪ {ω}) is the unique monoidal biclosed structure for which the functor from Gray cubes is strong monoidal ([2311.00205](https://arxiv.org/abs/2311.00205), Thm A), and it agrees with the strict one on Gray tensors of pasting diagrams (see `conjectures/free-infinity-gray-of-pasting-diagrams.md`, "Literature status").

## 3. Lax and oplax transformations

### 3.1 Names, by the direction of the naturality cell

For functors F, G : X → Y, a transformation α : F ⇒ G, and a 1-cell f : x → y of X:

| Name | Naturality cell at f (classical order) | Same, execution order | Classifying map |
|---|---|---|---|
| **lax** | Gf ∘ α_x ⇒ α_y ∘ Ff | α_x ; Gf ⇒ Ff ; α_y | X ⊗ D¹ → Y |
| **oplax** | α_y ∘ Ff ⇒ Gf ∘ α_x | Ff ; α_y ⇒ α_x ; Gf | D¹ ⊗ X → Y |

- **The names** are Bénabou's, as used by Johnson-Freyd–Scheimbauer **[paper]** ([1502.06526](https://arxiv.org/abs/1502.06526), §1, before Remark 1.2). They note that this is the majority convention, and that Johnstone's *Elephant* uses the reverse names.
- **The classifying maps** are Ara–Maltsiniotis's **[paper]**: oplax transformations are maps D¹ ⊗ C → D (AM Remark 1.10, Cor. B.2.6), lax ones are maps C ⊗ D¹ → D (AM Remark 1.13, Cor. B.2.7). AM's oplax naturality cell at a 1-cell x is α_{t(x)} ∗₀ u(x) → v(x) ∗₀ α_{s(x)} (AM §1.9, with ∗₀ in classical order), i.e. the "oplax" row above. So **AM's names and Bénabou's names agree**.
- **[computed]** The Leibniz formula gives the same rows. For X ⊗ D¹ with f : b → b′ in X and i : 0 → 1, the generator f ⊗ i has ∂⁻ = (b⊗i) ; (f⊗1) = α_b ; Gf and ∂⁺ = (f⊗0) ; (b′⊗i) = Ff ; α_{b′}. That is the lax row.
- **Other names in the literature.** Haugseng ([2002.01037](https://arxiv.org/abs/2002.01037), Def. 3.9 and footnote 4) says **colax** for oplax. Loubaton ([2406.05425](https://arxiv.org/abs/2406.05425), Intro, Ch. 4) defines a lax transformation as a map A ⊗ [1] → B, matching the table.

### 3.2 Internal homs, and a naming hazard

AM's two internal homs satisfy **[paper]** (AM §A.18)

```
Hom(A ⊗ B, C)  ≅  Hom(A, Hom_oplax(B, C))  ≅  Hom(B, Hom_lax(A, C))
Hom_oplax(A, B)_i = Hom(Dⁱ ⊗ A, B)            Hom_lax(A, B)_i = Hom(A ⊗ Dⁱ, B)
```

So the 1-cells of Hom_lax(A, B) are lax transformations, and those of Hom_oplax(A, B) are oplax ones.

**Hazard.** A *map into* a hom classifies the other variance:
- maps Δ → Hom_oplax(D¹, C) are maps Δ ⊗ D¹ → C, i.e. **lax** transformations between Δ-diagrams;
- maps Δ → Hom_lax(D¹, C) are **oplax** transformations (AM Remark 1.10).

`internal-hom.md` §5.1 calls `[Θ, C]` (defined by Δ ⊳ [Θ, C] ↔ (Δ ⊗ Θ) ⊳ C) the "lax hom", because maps into [D¹, C] are lax transformations. In AM's naming it is **Hom_oplax(Θ, C)**: its own 1-cells are oplax transformations between Θ-diagrams. Notes keep the name "lax hom [Θ, C]" for the rule of `internal-hom.md` §5.1 and write Hom_lax / Hom_oplax only in AM's sense.

### 3.3 Dualities

Write D_J for the dual reversing the cells of every dimension in J ⊆ {1, 2, …}. AM write C^op for J = odd dimensions, C^co for J = even dimensions, and C° for J = all dimensions (AM §1.8). Benjamin–Markakis's opposites op_J ([2402.01611](https://arxiv.org/abs/2402.01611)) are the same operations on CaTT syntax.

**[paper]** (AM Prop. A.20 for Steiner complexes, Prop. A.22 for ω-categories, Prop. A.23 for homs):

```
(A ⊗ B)^op ≅ B^op ⊗ A^op        Hom_oplax(A, B)^op ≅ Hom_lax(A^op, B^op)
(A ⊗ B)^co ≅ B^co ⊗ A^co        Hom_oplax(A, B)^co ≅ Hom_lax(A^co, B^co)
(A ⊗ B)°   ≅ A° ⊗ B°            Hom_oplax(A, B)°   ≅ Hom_oplax(A°, B°)
```

So the odd and the even duals both swap lax and oplax, and the total dual keeps them. AM Remark A.21: apart from the trivial dual, these are the only dualities with isomorphisms of this kind.

**[computed]** The same, directly from the Leibniz formula. D_J multiplies ∂ in degree n by σ(n) = −1 if n ∈ J and +1 otherwise. The swap x ⊗ y ↦ y ⊗ x commutes with the differentials iff σ(p+q) = (−1)^q σ(p) and σ(p+q)(−1)^p = σ(q) for all p, q ≥ 1. This holds for σ(n) = (−1)^n (odd) and σ(n) = −(−1)^n (even). The identity map commutes with them iff σ is constant on positive degrees, which is the total dual.

## 4. The ambient of the L core

The lax ambient 𝒦 of `pseudo-vs-gray.md` (option L) is fixed as follows. This is the convention that §3.1 there derived from the limit rules (R11).

- **Composition across objects is 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c), factors in execution order.** For a pasting scheme Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ the Gray unfolding is U_{ij} = Θᵢ₊₁ ⊗ … ⊗ Θⱼ.
- **The interchanger.** For 1-cells β : u ⇒ u′ in 𝒦(c, L) and φ : v ⇒ v′ in 𝒦(L, y), the generator β ⊗ φ is
  ```
  (u◁φ) ; (β▷v′)  ⇛  (β▷v) ; (u′◁φ)
  ```
  **[computed]** ∂(β⊗φ) = u′⊗φ − u⊗φ − β⊗v′ + β⊗v. The negative part {u⊗φ, β⊗v′} is the source path, the positive part {β⊗v, u′⊗φ} the target. This is the direction Mikhail's universal cone needs (`conjectures/catt-lim-pseudo-vs-gray.md`, eq. (2)).
- **2-cells of 𝒦 are lax transformations.** Taking elements x, y : 1 → X, f : x → y, and α ∈ 𝒦(X, Y)(F, G), the generator f ⊗ α ∈ 𝒦(1, X) ⊗ 𝒦(X, Y) gives α_x ; Gf ⇛ Ff ; α_y **[computed]**, the lax row of §3.1.
- **Semantics.** This is AM's ∞-Cat_lax, the "Gray-gauche" ∞-category of strict ω-categories, with hom-objects Hom_lax(A, B) **[paper]** (AM Ex. C.18; a Gray-gauche category is enriched in (X, Y) ↦ Y ⊗ X, §C.16, and AM write composition as Hom(y, z) ⊗ Hom(x, y) → Hom(x, z), §C.4, so in execution order this is ⊗). Equivalently, the evaluation map X ⊗ Hom_lax(X, Y) → Y puts elements first. AM's ∞-Cat_oplax is the other orientation. In the (∞,ω) setting, Gepner–Heine's oriented categories have hom-objects Fun^lax(S, T) ([2510.10504](https://arxiv.org/abs/2510.10504), intro).

## 5. Mikhail's conventions, translated

Mikhail ([2412.13310](https://arxiv.org/abs/2412.13310)) uses his own names. The notes keep his names for his rules, with this translation.

- **His transformations are Bénabou-oplax.** In his Example 4.1, a transformation p from Γ to its copy Γ′ has p_f : f · p_y → p_x · f′ (diagrammatic) **[paper]**. With F = (unprimed) and G = (primed) this is Ff ; α_y ⇒ α_x ; Gf, the oplax row of §3.1.
- **His "Γ ⊗ Dⁿ" is Dⁿ ⊗ Γ in the AM orientation** **[computed]**, `internal-hom.md` §4.1: for I = (0, 1, i : 0 → 1) and f : x → y, ∂⁻(i⊗f) = f · p_y and ∂⁺(i⊗f) = p_x · f′.
- **His "lax cones" are oplax transformations Δc ⇒ d in Bénabou's names.** The cone cell is p_f : p_y → p_x ∗ f (diagrammatic), `limits-representables.md` §2.1. "Lax limit" in the notes means Mikhail's notion unless stated otherwise. He notes that the other orientations come from reversing s and t or from opposites (start of §3 there).
- These are statements about Gray-shaped *contexts* (families of ambient cells). They do not conflict with §4, which is about the composition of the ambient itself. The orientation that §4 fixes is the one the universal cone forces.

## 6. Where each note uses these

| Note | Place | Uses |
|---|---|---|
| `pseudo-vs-gray.md` | §2.2, §3.1, R5, R11 | §4 (L's factor order), §3.3 (dualities) |
| `internal-hom.md` | §1.1, §1.3, §4.1, §5.1, §5.5a, §5.6 | §2, §3.2 (hazard), §3.3, §5 |
| `limits-representables.md` | §1, §4.4 | §5 (Mikhail) |
| `conjectures/catt-lim-pseudo-vs-gray.md` | eq. (2) | §4 |
