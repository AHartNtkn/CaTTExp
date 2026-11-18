# Problem: composites of molecules in CaTT (Gray contexts), round 5

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Rounds 1–4 and their verified answers are archived in `answered/gray-contexts-2026-11-18.md`, `answered/gray-contexts-round2-2026-11-18.md`, `answered/gray-contexts-r3-2026-11-18.md` and `answered/gray-contexts-r4-2026-11-18.md`; this prompt does not re-ask anything answered there.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory for weak ω-categories.

- Types are `⋆` and `u →_A v`. Contexts are lists of typed variables. By Benjamin–Markakis–Sarti ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- The only term former is `coh_{P, u →_A v}[σ]`. It needs:
  - P a **pasting context** (a globular pasting diagram);
  - σ a substitution into P;
  - one of two side conditions:
    - (coherence) `Var(u : A) = Var(P) = Var(v : A)`;
    - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality.
- Every term t of a context Γ has a strict image `π(t)` in the free strict ω-category `F(Γ)`.
- `supp(t)` is the set of variables used by t, closed under dependencies in their types.

### 1.2 Molecules

- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes ([arXiv 2404.07273](https://arxiv.org/abs/2404.07273)). Globes and Gray products of molecules are molecules.
- A **layering** of an n-molecule decomposes it into layers, each one n-dimensional atom pasted with lower-dimensional cells.
- Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) proves:
  - frame-acyclic molecules have layerings, corresponding to linear extensions of a partial order on the top cells (Prop. 2.18);
  - the subdivision poset of a frame-acyclic molecule that is **not an atom** is contractible (Thm 2.52);
  - molecules of dimension ≤ 3, and acyclic molecules, are frame-acyclic.
- *Frame-acyclicity is not Steiner's loop-freeness.* Frame-acyclicity corresponds to Steiner's "split" (Hadzihasanovic, Comment 8.3.5). Example 8.3.12 there is a frame-acyclic 3-atom that is not Steiner loop-free.
- **Presenting a molecule U in CaTT.** Each cell x gets a type `⌈∂⁻x⌉ → ⌈∂⁺x⌉`, whose sides are CaTT terms composing the boundary molecules, by induction on dimension.
- A **U-composite** is a term t with `supp(t) = Var(U)` and `t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉`.

> **Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n presented in CaTT:
> - (existence) U-composites exist;
> - (uniqueness) any two U-composites are connected by a CaTT term `t → t′`.

> **RC(n) for a context Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

Existence in G(n) follows from RC(n−1) for U's (n−1)-skeleton. Uniqueness in G(n) follows from RC(n) for U.

## 2. What is known

1. **RC(2) holds in every CaTT context** (Theorem A).
   - Normalize every 2-term to a vertical composite of whiskered 2-variables.
   - 2-terms without 2-variables pull back to the chain of their path, where the coherence rule applies.
   - Two such composites with the same strict image are related by exchange moves, each a coherence over "chain, 2-disc, chain, 2-disc, chain".
2. **G(2) holds, and existence holds in G(3).** In particular, every Gray generator of dimension ≤ 4 has a CaTT type.
3. **Total support lemma** (a strengthening of Benjamin–Markakis, [arXiv 2406.12127](https://arxiv.org/abs/2406.12127), Lemma 36). If c has no variable of dimension `dim c` in its support, then `supp(c) = supp(src c) = supp(tgt c)`.
4. **Terms without 2-variables.** Parallel n-terms with no 2-variable in their support are connected, for every n. They pull back to the chain of their path, and the coherence rule applies there.
5. **The lax square S.** The context is
   - objects `x⁻, x⁺, y⁻, y⁺ : ⋆`;
   - edges `x↑ : x⁻ → x⁺`, `y↑ : y⁻ → y⁺`, `f⁻ : x⁻ → y⁻`, `f⁺ : x⁺ → y⁺`;
   - one 2-cell `F : p → q`, where `p = f⁻ ∗₀ y↑` and `q = x↑ ∗₀ f⁺`.

   What is known about S:
   - *Strict cells.* The 2-cells of `F(S)` are the identities on the 10 paths, and F. S has no 3-variables, so RC(3) for S asks for a 4-term between **every** pair of parallel 3-terms.
   - *Identity 2-boundary: settled.* If the parallel 3-terms α, β have an identity as strict 2-boundary, then F is not in their support. Item 3 puts α and β over the path context `C_w`, and `coh_{C_w, ᾱ→β̄}[ι_w]` connects them.
   - *2-dimensional arity: reduced.* Let `c = coh_{P,u→v}[σ]` be a coherence 3-term with `dim P = 2` and strict 2-boundary F. Then exactly one 2-variable of P goes to a term with image F. All of P's columns except that one lie over `x⁻` or `y⁺`. A coherence over P's middle column, read as a vertical 2-chain Q, connects c to `coh_{Q,ū→v̄}[τ]`.
   - *One coherence never splits F's boundary.* In any `coh_R[δ]` with F in the support of δ, exactly one 1-column of R has a non-empty path, and that path runs from `x⁻` to `y⁺`. So `f⁻` and `y↑` are never separated into different columns inside a single coherence.
6. **The Gray cube's loops reduce to one hemisphere.** Let U be the Gray cube, X its 3-cell, and `A = ⌈∂⁻U⌉`. By item 3, a 3-term `H : A → A` without X has support in the negative hemisphere `∂⁻U`, which has three faces.
7. **Suspended coherences over vertical chains (round 2, proved).** Let Γ be any context and α = coh_{ΣC,ΣA}[τ], β = coh_{ΣC′,ΣA′}[τ′] parallel 3-terms with 0-boundary (a, b), where C, C′ are 1-dimensional path contexts and both the arity **and the type** are literal syntactic suspensions; the substituted 2-terms are arbitrary. Then there is a 4-term α → β. Proof: by Benjamin–Markakis, the hom H = Hom(a, b) is free on its indecomposable cells and decomposable hom cells are exactly coh_{ΣP,ΣB}[σ]; so α, β desuspend to hom 2-terms over a finite graph of hom generators, which lift to full-support 2-terms α̂, β̂ over a path context C_w (item 4 in the hom), and `coh_{ΣC_w, Σα̂ → Σβ̂}[δ_w]` is the required term.
8. **The hom shortcut fails in general (round 2, proved).** Over D₂ = (x, y, f, g, A : f → g) put W(A) = (λ_f⁻¹ ∗₁ (1_{1_x} ∗₀ A)) ∗₁ λ_g, r = coh_{D₂, A → W(A)}, ℓ = coh_{D₂, W(A) → A}, κ = r ∗₂ ℓ. Then r, ℓ are indecomposable hom 2-generators (their types contain ∗₀, so are not suspensions), κ ≠ 1_A in the strictification of the hom computad, yet coh_{D₂, κ → 1_A} exists globally; substituting into S gives the same in the lax square. So "equal global strict image ⇒ equal hom strict image" is false, and item 7 does not by itself settle the F-boundary case.
9. **Literature on normalisers.** Rice's thesis (arXiv 2502.17068) proves rehydration of semistrict CaTT over pasting contexts (Thm 4.5.3); §4.5.2 explains that extending it to arbitrary contexts needs normalisers that are not single coherences and comparisons between normalisation choices, and leaves this open. The BMOSV naturality construction (arXiv 2501.11620) covers depth ≤ 1 only.
10. **RC(3) for the lax square S, all cases (proved on paper, 2026-11-18).** Any two parallel 3-terms of S are connected by a 4-term. Method: for a 2-term with strict image F, exactly one 0-column of its arity carries F and spans x⁻ → y⁺, while every other column sits at the point x⁻ or y⁺ and factors literally through a point context; this factorisation through a vertical chain is stable under substitution, and normalisers ν_T : T → (κ(σT, p) · F) · κ(q, τT) built from it are compatible with every 3-term by induction on syntax. The step that uses the square: x⁻ is the unique source and y⁺ the unique sink, so the discarded columns are point-supported.
11. **Suspended chain coherences are not a normal form (round 3, proved).** Let 𝓔 be the class of 3-terms generated from literally suspended coherences over 1-dimensional path contexts and identities by the ordinary compositions and whiskerings (and inverses). Let L(t) be the length of the hom-1 word of a 2-term t under the intrinsic strictification of the Benjamin–Markakis hom computad. Every γ ∈ 𝓔 has L(s₂γ) = L(t₂γ), because ∗₀-composites of 2-terms are indecomposable hom 1-cells of length 1. But L(F) = 1 and L(W(F)) ≥ 3, so no γ ∈ 𝓔 has boundary F → W(F), already over D₂. Any normalisation proof of RC(3) must use boundary-adjusting 3-terms, as item 10's normalisers do.
12. **The hom-level reformulation is not a route (round 3, proved).** For every 3-term α : u → v in every context, coh_{D₃, z → (z ∗₂ 1_v) ∗₂ 1_v} gives α → (α ∗₂ 1_v) ∗₂ 1_v, a composite of decomposable hom cells. So "connected to a composite of decomposable hom cells" is trivially true, while the recursive reading (no indecomposable hom 2-generator anywhere) is false by item 11.

13. **RC(3) on the cylinder of a composable pair (proved on paper, 2026-11-18).** For Q = (x → y → z) and the cylinder Q↑Var(Q) (two lax squares F, G glued along the middle edge), any two parallel 3-terms are connected. The method extends item 10: a column carrying F or G that does not span the unique source and sink factors literally through `C_n ∗₀ D¹(h)` or `D¹(h) ∗₀ C_n`, with h sent to a fixed edge variable; the composite case H = (f⁻ ∗₀ G) ∗₁ (F ∗₀ g⁺) is point-supported with a forced order. Source: `answered/naturality-arbitrary-depth-r3-2026-11-18.md`.
14. **Literal inactive-column factorisation (round 4, proved).** Let Γ have dimension ≤ 2 and an acyclic directed graph of generating 1-cells, and let σ : Γ ⊢ P with P a pasting context of dimension ≤ 3, P = Q₁ ∨₀ … ∨₀ Q_k in 0-columns. Call Q_j *inactive* if no image of its 2-variables contains a 2-variable of Γ.
    - All 1-variables of an inactive column have images with one strict path w_j. All its assigned terms use only the vertices and edges of w_j (total support lemma). The path labelling ι_j : C_{w_j} → Γ is injective by acyclicity, so the column lifts literally: σ|_{Q_j} = θ_j[ι_j].
    - Replacing every inactive column by its path context gives a pasting context R_σ (a horizontal word of retained active columns and linear paths) and σ = κ_σ[δ_σ] syntactically, with ⋃ supp κ_σ(x) = Var(R_σ).
    - **Comparison.** χ_σ = coh_{R_σ, p_σ → r_σ}[id][δ_σ] : coh_{P,A}[σ] → coh_{R_σ, A[κ_σ]}[δ_σ], where p_σ = coh_{P,A}[κ_σ] and r_σ = coh_{R_σ, A[κ_σ]}[id] (a 3-term for 2-dimensional heads, a 4-term for 3-dimensional ones).
    - **Stability.** For ρ : Γ′ ⊢ Γ (Γ′ also acyclic of dimension ≤ 2) there is λ_{σ,ρ} : R_{σ[ρ]} ⊢ R_σ with δ_σ[ρ] = λ[δ_{σ[ρ]}], κ_{σ[ρ]} = κ_σ[λ], λ_{σ,id} = id and λ_{σ,ρ[τ]} = λ_{σ,ρ}[λ_{σ[ρ],τ}]. Coherences ζ_{σ,ρ} (old reduced head transported vs new one) and Θ_{σ,ρ} (the triangle of comparisons) exist.
    - On the Gray cube's negative hemisphere, height i + j + k shows that every arity has at most one active 0-column, so reduced 2-dimensional arities are V, D¹ ∨₀ V or V ∨₀ D¹ with V a vertical 2-chain.
    - Source: `answered/gray-contexts-r4-2026-11-18.md`.
15. **Whiskering distributes over vertical composites, coherently (round 4, proved).** Over P_m = V_m ∨₀ D¹ (V_m a vertical chain of m 2-cells, D¹ an edge e) there is a coherence D_m : W_e(C_m(α_i)) → C_m(W_e(α_i)). Over P_m↑ = (D³ ∨₁ … ∨₁ D³) ∨₀ D¹ (3-cells η_i : α_i⁻ ⇛ α_i⁺) there is a coherence 4-term Ω_m : W³(C³(η)) ∗₂ D_m⁺ → D_m⁻ ∗₂ C³(W³(η)). It can be substituted with arbitrary terms, and the left-whiskering version is symmetric. No acyclicity is needed.

## 3. What remains

Item 14 removes inactive columns literally and stably in every acyclic context of dimension ≤ 2. What is missing is the treatment of **active** columns: the 2-terms substituted into the retained vertical chain V are arbitrary composites of 2-generators and edge whiskers. A normaliser for such a column must be compared with the composite of the normalisers of its inputs ("evaluation fusion"). Replacing a 2-variable of V by a whiskered 2-term gives declarations with composite 1-boundaries, which are not a pasting context, so no single coherence performs this comparison. Item 15 handles one such interaction (a fixed whisker across a vertical composite). RC(3) fails for loopy contexts such as (x, a : 1_x → 1_x), so a proof must use acyclicity.

## 4. Questions

1. **The Gray cube (smallest open case).** Let U = D¹ ⊗ D¹ ⊗ D¹, presented with hexagon composites. Prove that every X-free 3-term H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉ is connected to the identity. By item 14 every arity has at most one active column; the remaining task is the active column.
2. **Evaluation fusion for active columns.** In an acyclic context of dimension ≤ 2, define normalisers ν_T : T → N(T) for 2-terms T (for instance, a fixed vertical composite of whiskered 2-generators, built from item 14's reduced heads and item 10's square normalisers), and construct for every coherence head c = coh_{V,A}[σ] over a vertical chain a 4-term relating ν_c to the composite of the ν_{σ(z)}. How should the non-globular declarations (2-variables replaced by whiskered terms) be handled: by refining V with item 14 applied to each input, by cells of the shape of item 15 for every head, or otherwise?
3. **RC(3) for acyclic contexts of dimension ≤ 2.** With items 14 and 15, prove RC(3) for every finite context of dimension ≤ 2 with acyclic generating 1-graph (or every finite Steiner loop-free 2-computad), or give a counterexample. The cylinders of 1-dimensional pasting contexts are the main examples.
4. **Contexts with 3-variables.** Extend item 14 to contexts of dimension 3, such as the cylinder of the 2-disc or the join context c ⋆ D², where an inactive 3-term no longer has the support of its 2-source.
5. **RC(n) or G(n).** Prove RC(n) for acyclic contexts, or the weaker G(n) for frame-acyclic molecules.

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) on acyclic contexts; a counterexample (an acyclic context with two parallel terms of equal strict image and no term between them); or a published reference.

## 6. Literature (searched 2026-11-18)

- No paper treats composites of non-globular molecules inside CaTT or inside Grothendieck–Maltsiniotis weak ω-categories.
- The (∞,n) pasting theorem, the semantic analogue of G:
  - Campion, [arXiv 2311.00200](https://arxiv.org/abs/2311.00200);
  - Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), Thm 3.17 (Thm 3.29 is monoidality for the Gray product).
  - No comparison between CaTT's models and (∞,ω)-categories is known, so these do not transfer directly.
- Di Vittorio, [arXiv 2205.15486](https://arxiv.org/abs/2205.15486): a Gray-categorical pasting theorem. It covers only composites output by its algorithm, and the paper says it is open whether every composite arises that way.
- Hadzihasanovic's diagrammatic sets ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639), [arXiv 2007.14505](https://arxiv.org/abs/2007.14505)) take unique weak composites of round molecules as the definition of a weak higher category.
- Benjamin–Markakis–Sarti ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)) and ICaTT ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)): composites of coherences are invertible.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): 2-cells of free 2-categories as 2-paths modulo exchange, and Squier-style coherence.
