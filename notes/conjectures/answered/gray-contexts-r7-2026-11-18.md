# Problem: composites of molecules in CaTT (Gray contexts), round 7

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Everything under "What is known" is proved and is not re-asked. Questions are in §4, smallest first.*

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
7. **Suspended coherences over vertical chains.** Let Γ be any context and α = coh_{ΣC,ΣA}[τ], β = coh_{ΣC′,ΣA′}[τ′] parallel 3-terms with 0-boundary (a, b), where C, C′ are 1-dimensional path contexts and both the arity **and the type** are literal syntactic suspensions; the substituted 2-terms are arbitrary. Then there is a 4-term α → β. Proof: by Benjamin–Markakis, the hom H = Hom(a, b) is free on its indecomposable cells and decomposable hom cells are exactly coh_{ΣP,ΣB}[σ]; so α, β desuspend to hom 2-terms over a finite graph of hom generators, which lift to full-support 2-terms α̂, β̂ over a path context C_w (item 4 in the hom), and `coh_{ΣC_w, Σα̂ → Σβ̂}[δ_w]` is the required term.
8. **The hom shortcut fails in general.** Over D₂ = (x, y, f, g, A : f → g) put W(A) = (λ_f⁻¹ ∗₁ (1_{1_x} ∗₀ A)) ∗₁ λ_g, r = coh_{D₂, A → W(A)}, ℓ = coh_{D₂, W(A) → A}, κ = r ∗₂ ℓ. Then r, ℓ are indecomposable hom 2-generators (their types contain ∗₀, so are not suspensions), κ ≠ 1_A in the strictification of the hom computad, yet coh_{D₂, κ → 1_A} exists globally; substituting into S gives the same in the lax square. So "equal global strict image ⇒ equal hom strict image" is false, and item 7 does not by itself settle the F-boundary case.
9. **Literature on normalisers.** Rice's thesis (arXiv 2502.17068) proves rehydration of semistrict CaTT over pasting contexts (Thm 4.5.3); §4.5.2 explains that extending it to arbitrary contexts needs normalisers that are not single coherences and comparisons between normalisation choices, and leaves this open. The BMOSV naturality construction (arXiv 2501.11620) covers depth ≤ 1 only.
10. **RC(3) for the lax square S, all cases (proved).** Any two parallel 3-terms of S are connected by a 4-term. Method: for a 2-term with strict image F, exactly one 0-column of its arity carries F and spans x⁻ → y⁺, while every other column sits at the point x⁻ or y⁺ and factors literally through a point context; this factorisation through a vertical chain is stable under substitution, and normalisers ν_T : T → (κ(σT, p) · F) · κ(q, τT) built from it are compatible with every 3-term by induction on syntax. The step that uses the square: x⁻ is the unique source and y⁺ the unique sink, so the discarded columns are point-supported.
11. **Suspended chain coherences are not a normal form.** Let 𝓔 be the class of 3-terms generated from literally suspended coherences over 1-dimensional path contexts and identities by the ordinary compositions and whiskerings (and inverses). Let L(t) be the length of the hom-1 word of a 2-term t under the intrinsic strictification of the Benjamin–Markakis hom computad. Every γ ∈ 𝓔 has L(s₂γ) = L(t₂γ), because ∗₀-composites of 2-terms are indecomposable hom 1-cells of length 1. But L(F) = 1 and L(W(F)) ≥ 3, so no γ ∈ 𝓔 has boundary F → W(F), already over D₂. Any normalisation proof of RC(3) must use boundary-adjusting 3-terms, as item 10's normalisers do.
12. **The hom-level reformulation is not a route.** For every 3-term α : u → v in every context, coh_{D₃, z → (z ∗₂ 1_v) ∗₂ 1_v} gives α → (α ∗₂ 1_v) ∗₂ 1_v, a composite of decomposable hom cells. So "connected to a composite of decomposable hom cells" is trivially true, while the recursive reading (no indecomposable hom 2-generator anywhere) is false by item 11.

13. **RC(3) on the cylinder of a composable pair (proved).** For Q = (x → y → z) and the cylinder Q↑Var(Q) (two lax squares F, G glued along the middle edge), any two parallel 3-terms are connected. The method extends item 10: a column carrying F or G that does not span the unique source and sink factors literally through `C_n ∗₀ D¹(h)` or `D¹(h) ∗₀ C_n`, with h sent to a fixed edge variable; the composite case H = (f⁻ ∗₀ G) ∗₁ (F ∗₀ g⁺) is point-supported with a forced order.
14. **Literal inactive-column factorisation.** Let Γ have dimension ≤ 2 and an acyclic directed graph of generating 1-cells, and let σ : Γ ⊢ P with P a pasting context of dimension ≤ 3, P = Q₁ ∨₀ … ∨₀ Q_k in 0-columns. Call Q_j *inactive* if no image of its 2-variables contains a 2-variable of Γ.
    - All 1-variables of an inactive column have images with one strict path w_j. All its assigned terms use only the vertices and edges of w_j (total support lemma). The path labelling ι_j : C_{w_j} → Γ is injective by acyclicity, so the column lifts literally: σ|_{Q_j} = θ_j[ι_j].
    - Replacing every inactive column by its path context gives a pasting context R_σ (a horizontal word of retained active columns and linear paths) and σ = κ_σ[δ_σ] syntactically, with ⋃ supp κ_σ(x) = Var(R_σ).
    - **Comparison.** χ_σ = coh_{R_σ, p_σ → r_σ}[id][δ_σ] : coh_{P,A}[σ] → coh_{R_σ, A[κ_σ]}[δ_σ], where p_σ = coh_{P,A}[κ_σ] and r_σ = coh_{R_σ, A[κ_σ]}[id] (a 3-term for 2-dimensional heads, a 4-term for 3-dimensional ones).
    - **Stability.** For ρ : Γ′ ⊢ Γ (Γ′ also acyclic of dimension ≤ 2) there is λ_{σ,ρ} : R_{σ[ρ]} ⊢ R_σ with δ_σ[ρ] = λ[δ_{σ[ρ]}], κ_{σ[ρ]} = κ_σ[λ], λ_{σ,id} = id and λ_{σ,ρ[τ]} = λ_{σ,ρ}[λ_{σ[ρ],τ}]. Coherences ζ_{σ,ρ} (old reduced head transported vs new one) and Θ_{σ,ρ} (the triangle of comparisons) exist.
    - On the Gray cube's negative hemisphere, height i + j + k shows that every arity has at most one active 0-column, so reduced 2-dimensional arities are V, D¹ ∨₀ V or V ∨₀ D¹ with V a vertical 2-chain.
    -
15. **Whiskering distributes over vertical composites, coherently.** Over P_m = V_m ∨₀ D¹ (V_m a vertical chain of m 2-cells, D¹ an edge e) there is a coherence D_m : W_e(C_m(α_i)) → C_m(W_e(α_i)). Over P_m↑ = (D³ ∨₁ … ∨₁ D³) ∨₀ D¹ (3-cells η_i : α_i⁻ ⇛ α_i⁺) there is a coherence 4-term Ω_m : W³(C³(η)) ∗₂ D_m⁺ → D_m⁻ ∗₂ C³(W³(η)). It can be substituted with arbitrary terms, and the left-whiskering version is symmetric. No acyclicity is needed.
16. **The support lemma (proved).** In every CaTT context Γ, the generators used by the strict image of a term are exactly its dependency-closed support: `supp(π t) = supp(t)`. So a term whose strict image lies in a dependency-closed sub-context is literally a term of that sub-context.
17. **The Gray cube's X-free loops are contractible.** Every X-free 3-term H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉ is connected to the identity.
    - *Hemisphere.* Its paths 000 → 111 are 321, 231, 213 and 123, with rewrites E₁, E₂, E₃ in a line. So the strict 2-cells between them are the intervals of E₁E₂E₃.
    - *Proper intervals.* The pairs of adjacent faces are two-square cylinders (one with item 13's orientation, one 2-opposite). Single whiskered faces are literal retracts of them. So every proper interval satisfies RC(3).
    - *Normal forms.* N(T) = C(γ_r, E_{i+1}, …, E_j, γ̄_s), with fixed bracketing and path corrections γ. For a full-word T, the reduced head is one vertical chain V_m. Then ν_T is the generic comparison b : T̃ → K(T̃) over V_m (one coherence, both sides full), followed by the input normalisers and a gap flattening Φ.
    - *Relative evaluation fusion.* For a full 2-term u over a formal V_m and δ into the hemisphere, there is a 4-term ν_{u[δ]} → b_u[δ] ∗₂ f_{u,δ}. The 2-variables of V_m stay formal, and only the chosen normal forms N(δ(α_i)) are expanded. The tools are the coherences A_a = coh_{V_m↑, a[−] → a[+]} and Ω_χ : χ[−] ∗₂ A_b → A_a ∗₂ χ[+] over V_m↑ = D³ ∨₁ ⋯ ∨₁ D³, and one coherence over a formal gap context for path-only gaps.
    - *Compatibility.* For every 3-term H : u → v there is I_H : ν_u → H ∗₂ ν_v. It is built from one coherence Ξ_P over H's reduced 3-arity, plus relative fusion at both ends.
    -
18. **Item 14 extends to some contexts with 3-variables.** Let dim Γ ≤ 3 and suppose every 3-variable z has a 2-generator in the support of its 2-source. Then a 3-term whose 2-source has no 2-generator in its support has no 2- or 3-generator in its support. So item 14's inactive-column test, path lift, comparisons and stability hold unchanged in acyclic such Γ.
    - The cylinder of D² (squares F, G and Z : (A⁻ ∗₀ k) ∗₁ G → F ∗₁ (h ∗₀ A⁺)) satisfies the hypothesis, and so does the join c ⋆ D² (Z : β_g → β_f ∗₁ (p ∗₀ A)).
    - The hypothesis is needed. In (x, y, f, Z : 1_f → 1_f), a column assigning 1_f to both 2-variables and Z to the 3-variable is inactive by the old test but carries Z.
19. **An acyclic generating 1-graph is not enough.** The context (x, a : 1_x → 1_x) has no 1-generators, so its 1-graph is acyclic, and RC(3) fails there. Adjoining y and f : x → y gives a connected example that retracts onto it, so RC(3) fails there too. The obstruction is a 2-generator whose source and target are both identities.

20. **A one-generator extension lemma (proved).** Let Λ be a context of dimension ≤ 2 with an acyclic generating 1-graph in which RC(3) holds, and let Γ = (Λ, z : A → B) be such that the only nonidentity 3-cell of F(Γ) is z. Then RC(3) holds in Γ.
    - *Head expansion.* A 3-term whose arity P has dimension 3 is in the composition case. One coherence Ω_P over P compares it with a boundary-corrected binary composite K_P of P's 3-variables. The z-count is additive, so exactly one substituted 3-argument uses z and the recursion follows one branch.
    - *Whiskers.* Since z is the only nonidentity strict 3-cell, ∗₁-whiskers of the z-factor are path-supported and ∗₀-whiskers are point-supported. Explicit 4-coherences over D³, D² ∨₁ D³ ∨₁ D² ∨₁ D² and D²(f) ∨₁ D³(z) ∨₁ D³(e) remove them.
    - *Assembly.* This gives H ⇛ (L ∗₂ z_rs) ∗₂ R with z-free L, R, which RC(3) in Λ compares with chosen normalisers ν_u : u → A_rs (from RC(2)).
21. **The whole Gray cube (proved).** RC(3) holds for the Gray cube U, including its 3-variable X. So any two U-composites ⌈∂⁻U⌉ → ⌈∂⁺U⌉ are connected: uniqueness in G(3) holds for the cube. Proof: the paths 000 → 111 form a hexagon with two directed routes, and the second hemisphere (321 → 312 → 132 → 123) is handled exactly as item 17 handles the first. X has no nontrivial strict whiskerings and π(A) ≠ π(B), so item 20 applies.
22. **A line-word criterion (proof sketch).** Let w = E₁ ⋯ E_r be a strict 2-cell in a 2-dimensional context with acyclic generating 1-graph. Suppose (i) w has a unique ordered word of whiskered generating 2-cells, (ii) every proper contiguous subword, including the empty ones, satisfies RC(3), and (iii) some event uses a generating 2-cell whose own 0-source and 0-target are the external endpoints of w. Then the fibre of w satisfies RC(3). The construction of item 17 is used for words of any length: the full-span generator forces all other 0-columns to be point-supported, so item 14 leaves one vertical column.
23. **The cylinder of D² and the join c ⋆ D² (proved).** Both satisfy RC(3). For the cylinder, the strict 2-cells x⁻ → y⁺ have event words a, b, c, d, ab, cd; a and d are pasting fibres, b and c are lax squares (item 10), and ab, cd satisfy item 22 with full-span generators G and F. Z has no strict whiskerings and its two 2-boundaries differ, so item 20 applies. The join is handled the same way.
24. **The exchange has a local 4-dimensional law (proved).** Over P = D²(a) ∨₀ D²(b) (a : f₀ → f₁, b : g₀ → g₁) put L = (a ∗₀ g₀) ∗₁ (f₁ ∗₀ b), R = (f₀ ∗₀ b) ∗₁ (a ∗₀ g₁) and χ = coh_{P, L → R}[id]. Over P↑ = D³ ∨₀ D³ with composition terms A_L : L⁻ → L⁺ and A_R : R⁻ → R⁺,
    coh_{P↑, (χ⁻ ∗₂ A_R) → (A_L ∗₂ χ⁺)}[id]
    is a valid 4-term, and it may be substituted with arbitrary input normalisers. Backtrack cancellation for χ and its reverse is one 4-coherence over P. This is a local law only: it does not compare an arbitrary 3-head whose value involves an exchange with a chosen combination of exchanges.
25. **Two independent letters with a cut vertex (proved).** In the context a, b, c, d; X : a → b, f⁻ : a → c, f⁺ : b → c, g⁻, g⁺ : c → d; F : f⁻ ⇒ X ∗₀ f⁺, G : g⁻ ⇒ g⁺, the letters F and G act on the two sides of the cut vertex c and commute up to exchange, and RC(3) holds.
    - The normal form of the diagonal 2-cell uses the horizontal composite F ∗₀ G, keeping horizontal identity factors for one-letter transitions.
    - Vertical composition of normal forms is a matrix-style multiplication I ; (m^F ∗₀ m^G), with I : (α ∗₀ β) · (α′ ∗₀ β′) ⇛ (α · α′) ∗₀ (β · β′) over C₂ ∗₀ C₂.
    - Fusion uses a horizontal fold over C₃ ∗₀ C₃ and a horizontal–vertical 4-cell built over C₆ ∗₀ C₆. A separate clause absorbs a column that becomes point-supported under substitution.
    - The cut vertex is essential to this argument: every 0-cut of a head must go to one of the common vertices a, c, d of the two boundary paths, so heads are horizontal composites of at most two vertical chains.
26. **On question 3's hypothesis.** In an acyclic generating 1-graph, a 2-generator with an identity source has a closed path, hence an identity, as target. So "acyclic, and no 2-generator has an identity as both source and target" is the same as "acyclic, and every 2-generator has nonempty source and target paths". Forest–Mimram ([arXiv 2109.05369](https://arxiv.org/abs/2109.05369)) prove coherence for the free Gray category on a positive Gray presentation (termination of interchanger rewriting plus confluence of critical branchings); this is the strict-Gray analogue, not a relative normalisation of CaTT terms.

## 3. What remains

Items 20–23 reduce RC(3) for contexts whose 3-generators are isolated (no strict whiskering, no strict composite) to RC(3) for their 2-skeleta, and settle the 2-skeleta in which every strict 2-cell has a unique event word. Item 25 settles one case with two commuting letters, using a cut vertex to split heads horizontally. The step that remains open is a 2-skeleton where two 2-generators commute up to exchange **without** a cut vertex separating them, so that a strict 2-cell has several event words related by exchange, and a single 0-column of a head can carry both letters.

## 4. Questions

1. **The 2 × 2 grid.** Prove RC(3) for the Gray product of two paths of length 2 (four lax squares; the path h v h v admits two independent face rewrites, and there is no cut vertex separating them). The missing step is a comparison taking every 3-head whose value involves an exchange to a chosen normal form, for instance a Squier-style normal form of the exchange class with item 24 as the local law. Any normal form and fusion is acceptable.
2. **Exchange in general, dimension 2.** Prove RC(3) for every finite context of dimension ≤ 2 whose generating 1-graph is acyclic and in which every 2-generator has nonempty source and target paths. Or give a counterexample. If the general statement is out of reach, prove it for finite Steiner loop-free 2-computads, which include the cylinders of 1-dimensional pasting contexts and the Gray products of two such contexts.
3. **Several 3-generators.** Extend item 20 to several 3-generators, or to a 3-generator with nontrivial strict whiskerings or composites. The smallest cases are the Gray product of a 2-disc with an edge whose 3-generators compose along a 2-cell, and a 3-cell z : A → B where some 2-cell can be whiskered onto z nontrivially.
4. **RC(4) and G(4).** Prove RC(4) for the 4-dimensional Gray cube (or for the cylinder of D³), or explain what new compatibility is needed. A 4-dimensional analogue of the head expansion in item 20 needs a 5-dimensional comparison between chosen 3-normalisers.
5. **RC(n) or G(n).** Prove RC(n) under the hypothesis of question 2 (suitably extended to higher generators), or the weaker G(n) for frame-acyclic molecules.

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) under a stated hypothesis; a counterexample (a context satisfying the hypothesis of question 3 with two parallel terms of equal strict image and no term between them); or a published reference.

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


# Researcher Response

**The \(2\times2\) grid satisfies \(\mathrm{RC}(3)\).** The missing comparison can be constructed by extending the relative-fusion argument of item 17.

The essential point is to separate two operations:

1. Move input normalisers through a generic head while their \(2\)-sources remain formal variables.
2. Expand only the resulting chosen normal forms. At that stage, every exchange is between the same two adjacent faces \(F,G\). Reassociate to isolate those faces together with the intervening path terms, and apply \(\mathrm{RC}(3)\) in their cut-vertex subcontext.

The cut-vertex result must first be extended from item 25’s triangle and globe to two squares. I give that extension explicitly below. I also give extensions of item 20 to vertically composable \(3\)-generators and to a cube with a nontrivial edge whisker.

## 1. The grid and its strict \(2\)-cells

Orient each face as \(hv\Rightarrow vh\). Name the six paths from \((0,0)\) to \((2,2)\) as follows.

| Name | Path |
|---|---|
| \(p_0\) | \(hhvv\) |
| \(p_1\) | \(hvhv\) |
| \(p_2\) | \(vhhv\) |
| \(p_3\) | \(hvvh\) |
| \(p_4\) | \(vhvh\) |
| \(p_5\) | \(vvhh\) |

Put
\[
D=e_{10},\qquad F=e_{00},\qquad G=e_{11},\qquad E=e_{01}.
\]
With the required edge whiskers, the elementary rewrites are
\[
p_0\xrightarrow{D}p_1,
\]
\[
p_1\xrightarrow{F}p_2\xrightarrow{G}p_4,
\qquad
p_1\xrightarrow{G}p_3\xrightarrow{F}p_4,
\]
\[
p_4\xrightarrow{E}p_5.
\tag{1}
\]

This list follows by applying \(hv\mapsto vh\) at each adjacent \(hv\) in each of the six paths. The only pair of independent events is \(F,G\). Thus the nonunique event words are exactly
\[
FG=GF,\qquad
DFG=DGF,\qquad
FGE=GFE,\qquad
DFGE=DGFE.
\tag{2}
\]

The two-event cells other than \(FG\) are
\[
DF,\quad DG,\quad GE,\quad FE.
\tag{3}
\]
Each is a two-square strip with one unchanged outer edge.

The three remaining cells to prove coherent are therefore
\[
DFG,\qquad FGE,\qquad DFGE.
\tag{4}
\]

Their boundary paths have no common interior vertex:
\[
\begin{aligned}
\operatorname{Vert}(p_0)\cap\operatorname{Vert}(p_4)
&=\{(0,0),(2,2)\},\\
\operatorname{Vert}(p_1)\cap\operatorname{Vert}(p_5)
&=\{(0,0),(2,2)\},\\
\operatorname{Vert}(p_0)\cap\operatorname{Vert}(p_5)
&=\{(0,0),(2,2)\}.
\end{aligned}
\tag{5}
\]

Consequently, a head evaluating to any cell in (4) has precisely one nonconstant \(0\)-column. Indeed, every \(0\)-cut of its arity maps to a vertex of both boundary paths. By (5), it maps to an external endpoint. Acyclicity then makes all other columns point-supported.

After item 14, a \(2\)-head has arity \(V_m\), a vertical chain of \(2\)-discs; a \(3\)-head has one \(0\)-column, possibly with several vertical chains of \(3\)-variables.

This reduction concerns **every head**, independently of how its substituted \(2\)-terms were constructed.

## 2. Proper fibers: fixed paths and the two-square cut

Write
\[
V_n=D^2\vee_1\cdots\vee_1D^2,
\qquad
V_n^\uparrow=D^3\vee_1\cdots\vee_1D^3.
\]
Let \(\mathsf C\) denote a fixed bracketing of vertical \(2\)-composition.

For full parallel \(3\)-terms \(a,b\) over a pasting context \(P\), abbreviate
\[
[a,b]_P
=
\operatorname{coh}_{P,a\to b}[\operatorname{id}_P].
\]
This abbreviation always denotes a particular \(4\)-term.

### 2.1 Adding fixed prefix and suffix paths

The line-word constructions already established for squares, strips, and cube hemispheres extend to fixed outer paths. The additional terms are the following.

Let
\[
R=V_n\vee_0C_w,
\]
where \(C_w\) is a nonempty linear path context, and let \(q\) be its chosen composite. If \(a_1,\ldots,a_n\) are the \(2\)-variables of \(V_n\), put
\[
a_\Sigma=\mathsf C(a_1,\ldots,a_n).
\]
Define
\[
\mathsf F_{n,w}:
\mathsf C(a_1*_01_q,\ldots,a_n*_01_q)
\longrightarrow
a_\Sigma*_01_q
\tag{6}
\]
by one full-support \(3\)-coherence over \(R\).

Its naturality under arbitrary \(3\)-comparisons of the \(a_i\) is a \(4\)-coherence over
\[
R^\uparrow=V_n^\uparrow\vee_0C_w.
\]
Writing \(A_{\mathrm{exp}}\) and \(A_{\mathrm{fold}}\) for the two composition actions, its type is
\[
A_{\mathrm{exp}}*_2\mathsf F_{n,w}^{+}
\longrightarrow
\mathsf F_{n,w}^{-}*_2A_{\mathrm{fold}}.
\tag{7}
\]
Both sides use every formal \(3\)-input and every edge of \(C_w\).

There is also a comparison with the matrix fold used in item 25. Over
\[
Q_n=V_n^L\vee_0V_n^R,
\]
define
\[
I_n:
\mathsf C(a_i*_0b_i)
\longrightarrow
\mathsf C(a_i)*_0\mathsf C(b_i)
\tag{8}
\]
by a full-support \(3\)-coherence.

Let \(\theta:R\vdash Q_n\) send every right-hand \(1\)-variable to \(q\), and every right-hand \(2\)-variable to \(1_q\). Choose the path-supported comparison
\[
\epsilon_q:\mathsf C(1_q,\ldots,1_q)\longrightarrow1_q.
\]
Then the following two \(3\)-terms have exactly the same \(2\)-boundary:
\[
\mathsf F_{n,w},
\qquad
I_n[\theta]*_2(1_{a_\Sigma}*_0\epsilon_q).
\]
Both have full \(R\)-support. Therefore
\[
\boxed{
K_{n,w}
=
\left[
\mathsf F_{n,w},
I_n[\theta]*_2(1_{a_\Sigma}*_0\epsilon_q)
\right]_R
}
\tag{9}
\]
is a \(4\)-term.

There are left-hand and two-sided versions over
\[
C_u\vee_0V_n\vee_0C_w.
\tag{10}
\]
Different orders of folding the outer paths are compared by full-support \(4\)-coherences over (10). Empty paths use the point-column clause already present in item 25.

Here is the resulting induction. Include, in the family being normalised, every event subword of the original line word with every admissible fixed prefix and suffix path. This is necessary because an active column can extend through part of an unchanged outer path. A reduced \(2\)-head has the form (10). Apply the generic head comparison, normalise its \(2\)-inputs, flatten the path gaps, and apply (6). An input with fewer events belongs to an earlier case; an input with the same events is a proper syntactic subterm.

Relative fusion uses the same induction, with:

- item 17’s comparisons for the vertical column;
- (7) to move input normalisers through the path folds;
- (9) to compare path folding with matrix folding;
- item 14’s \(\lambda,\zeta,\Theta\);
- path coherence and the point-column clause.

For a \(3\)-head, retain its actual reduced \(3\)-arity and use its generic \(\Xi\)-comparison, as in item 17. In particular, one does not replace an arbitrary \(3\)-arity by \(V_n^\uparrow\).

Only the **\(3\)-operations** are varied using \(4\)-dimensional naturality. After those variations have been moved, the \(4\)-cells such as \(K_{n,w}\) are simply substituted with the resulting \(2\)-normal forms. No naturality of a \(4\)-cell is required.

This proves \(\mathrm{RC}(3)\) for the one-face fibers with fixed paths and the four strip fibers in (3).

### 2.2 Two squares meeting at one vertex

Let \(\Lambda_{FG}\) be the dependency-closed subcontext consisting of the two squares \(F,G\). Write
\[
F:f_0\to f_1\quad(a\to c),
\qquad
G:g_0\to g_1\quad(c\to d),
\]
where each \(f_i,g_i\) is a two-edge path.

Choose the middle path bracketings so that
\[
p_1=f_0*_0g_0,\quad
p_2=f_1*_0g_0,\quad
p_3=f_0*_0g_1,\quad
p_4=f_1*_0g_1.
\tag{11}
\]

The common vertices of \(p_1,p_4\) are exactly \(a,c,d\). A head with strict value \(FG\) consequently has, after item 14, either:

- one active column from \(a\) to \(d\); or
- two active columns, from \(a\) to \(c\) and from \(c\) to \(d\).

All other columns are point columns. In particular, the one-column case using both faces is included.

Use \(F*_0G\) as the diagonal normal form. A sequence of normalised inputs is a sequence of rows
\[
\alpha_i*_0\beta_i,
\]
where the left column uses \(F\) once in total and the right column uses \(G\) once in total; the other factors are the corresponding horizontal identities. Its multiplication is
\[
I_n*_2(m_F*_0m_G),
\tag{12}
\]
where \(m_F,m_G\) are the selected one-square normalisation comparisons.

The construction of item 25 now applies with the following substitutions of proof data.

| Required comparison | Construction here |
|---|---|
| Factorwise multiplication, unit and associativity comparisons | \(\mathrm{RC}(3)\) of the appropriate square, or the path case |
| Horizontal fold fusion | The same generic terms over \(V_3\vee_0V_3\) |
| Horizontal–vertical fusion | The same generic terms over \(V_6\vee_0V_6\) |
| Moving arbitrary input \(3\)-normalisers through a \(3\)-operation | Its \(4\)-coherence over the lifted genuine pasting arity |
| An inactive factor represented by a longer path | (9) |
| A column becoming point-supported | Item 25’s point-column clause |

The triangular boundary of item 25’s first generator and the globular boundary of its second generator are not used by these generic matrix terms. Their formal \(1\)-variables may be assigned the two-edge paths \(f_i,g_i\). The factorwise comparisons are now supplied by the square theorem.

For a one-column head, normalise its inputs into rows and use (12). For a two-column head, normalise the columns separately. The generic horizontal–vertical fusion compares those prescriptions. The two cases and the point-collapse case exhaust the possible images of the \(0\)-cut \(c\), so the same relative-fusion and \(3\)-head inductions prove
\[
\boxed{\mathrm{RC}(3)\text{ in the }FG\text{ fiber of }\Lambda_{FG}.}
\tag{13}
\]

We may subsequently use the vertical normal form
\[
L=(F*_01_{g_0})*_1(1_{f_1}*_0G)
\tag{14}
\]
instead of \(F*_0G\). The comparison between them is one \(3\)-coherence over \(D^2\vee_0D^2\), followed by substitution. Compatibility with any chosen normalisers is supplied by the now-proved (13).

Thus **every grid fiber with at most two faces satisfies \(\mathrm{RC}(3)\)**.

## 3. Chosen normal forms for the remaining fibers

Fix literal \(1\)-terms for all the paths \(p_i\), using (11) for the middle four paths.

Each elementary rewrite in (1) is represented by its face with the indicated edge whiskers. Insert path-supported \(2\)-coherences at its source and target when necessary to obtain exactly the chosen path bracketings. This fixes the elementary \(2\)-terms once and for all.

Always order \(F\) before \(G\). Hence the selected words for (4) are
\[
D,F,G;\qquad F,G,E;\qquad D,F,G,E.
\]

For \(T:r\to s\) with strict image \(w:p_i\to p_j\), put
\[
N(T)=
\mathsf C\bigl(
\kappa(r,p_i),\,
E(w),\,
\kappa(p_j,s)
\bigr),
\tag{15}
\]
where \(E(w)\) is the selected word and \(\kappa\) denotes a selected path-supported \(2\)-coherence.

A singleton composite is itself. An empty event list is an identity. A correction factor is omitted when its two arguments are literally identical.

For proper fibers, choose normalisers
\[
\nu_T:T\longrightarrow N(T)
\]
using \(\mathrm{RC}(2)\). Their compatibility with \(3\)-terms follows from the \(\mathrm{RC}(3)\) results of §2.

For a full fiber in (4), define \(\nu_T\) recursively.

After item 14, write the \(2\)-head as
\[
\widetilde T[\delta],
\]
where \(\widetilde T\) is full over \(V_m\), with formal \(2\)-variables \(\alpha_1,\ldots,\alpha_m\).

Let \(K(\widetilde T)\) be the framed vertical composite of these variables, with exactly the literal \(1\)-boundaries of \(\widetilde T\). Then
\[
b_{\widetilde T}
=
\operatorname{coh}_{V_m,\,
\widetilde T\to K(\widetilde T)}
[\operatorname{id}]
\tag{16}
\]
is a valid \(3\)-term.

Define \(\nu_T\) by:

1. \(b_{\widetilde T}[\delta]\);
2. the input normalisers \(\nu_{\delta\alpha_i}\), applied to the framed vertical composite;
3. a specified flattening \(\Phi\).

The flattening \(\Phi\) does the following:

- expands the chosen \(N(\delta\alpha_i)\);
- combines adjacent path-only factors and normalises them;
- removes the resulting internal identity factors;
- if the expanded event order is \(GF\), applies the fixed reverse of the exchange in item 24;
- puts the result into the bracketing of (15).

There is at most one such exchange. The faces are each used once, and \(D\), when present, precedes both \(F,G\), while \(E\), when present, follows both.

This recursion is well founded: a substituted \(2\)-input with the same strict face set is a proper syntactic subterm.

The remaining issue is coherence of this recursion under evaluation. That is addressed next.

## 4. The flattening comparison with exchange

The following comparison replaces the path-only gap comparison used in item 17.

### Flattening lemma

Take a vertical expression formed from chosen event normal forms, with strict value one of
\[
DFG,\quad FGE,\quad DFGE.
\]
Any two hierarchical applications of the specified flattening \(\Phi\), with the same literal source and target, are connected by a \(4\)-term.

Here a hierarchical application means that some consecutive input groups are first flattened, and their results are then flattened together.

### Construction

First use vertical associators and their \(4\)-dimensional comparisons to expose the individual fixed event terms and the intervening path-only factors. These comparisons are formed over vertical pasting contexts before substitution.

Every change of event order is between \(F,G\). They are adjacent events after the optional initial \(D\) and before the optional final \(E\). Reassociate so that the following factors form one \(2\)-subexpression:

- \(F,G\), in either order;
- every path-only factor between them;
- their endpoint corrections on the middle paths \(p_1,p_4\).

When \(D\) or \(E\) is absent, include the corresponding outer correction in this same subexpression.

Every path used by those corrections is one of
\[
p_1,\ p_2,\ p_3,\ p_4.
\]
Its vertices and edges belong to \(\Lambda_{FG}\). Thus the isolated \(2\)-subexpression has strict image \(FG\) and is literally a term over \(\Lambda_{FG}\).

After the reassociations, each candidate flattening gives a \(3\)-term between the same two literal \(2\)-terms in this \(FG\) fiber. By (13), these \(3\)-terms have a \(4\)-comparison. Whisker that comparison by the fixed outer \(D,E\) terms.

The path-only operations outside this \(FG\) subexpression are compared using item 4. Their changes of position relative to other factors use full-support \(4\)-coherences over vertical strings of \(3\)-discs and \(2\)-discs.

This construction does **not** assert that a path-gap comparison between \(F\) and \(G\) is independent of the exchange. Such a comparison belongs to the isolated \(FG\) subexpression and is handled by (13).

There are also no assumptions about the syntax of the original input normalisers. Those remain formal \(3\)-inputs until generic naturality has moved them. Only their selected target \(2\)-normal forms are expanded.

This proves the lemma.

## 5. Relative evaluation fusion

Here is the induction that makes the preceding lemma apply to arbitrary heads.

Let \(u\) be a full \(2\)-term over \(V_m\), and let \(\delta\) be a substitution into the grid. Choose the generic comparison
\[
b_u:u\longrightarrow K(u)
\]
as in (16), taking \(b_u=1_u\) in the variable case.

Let
\[
f_{u,\delta}:K(u)[\delta]\longrightarrow N(u[\delta])
\]
be the application of the input normalisers followed by the specified \(\Phi\).

We construct
\[
\boxed{
\mathcal E(u,\delta):
\nu_{u[\delta]}
\longrightarrow
b_u[\delta]*_2f_{u,\delta}.
}
\tag{17}
\]

If the strict image is a proper fiber already settled, use its \(\mathrm{RC}(3)\). The variable case is a \(4\)-unitor.

For the remaining case, induct on the syntax of \(u\).

Since \(u\) is over a formal vertical chain, its head has one nonconstant \(0\)-column. Its other columns are point-supported. After applying \(\delta\), those columns remain point-supported, and the active column cannot disappear because the resulting strict cell is nonidentity. Thus the reduction used in defining \(\nu_{u[\delta]}\) is the substitution of the generic reduction used for \(u\).

Let \(u_i\) be the \(2\)-inputs of that reduced head. Their generic strict images are contiguous subchains of \(V_m\). Apply the induction hypothesis on those supporting subchains. For an input whose actual strict image is proper, its established \(\mathrm{RC}(3)\) supplies the same comparison.

It remains to compare the two flattenings. The following gives the precise \(4\)-dimensional calculation.

Write
\[
\eta_j=\nu_{\delta\alpha_j},
\]
and let \(\delta^+\) agree with \(\delta\) on \(0\)- and \(1\)-variables and send
\[
\alpha_j\longmapsto N(\delta\alpha_j).
\]
This is a well-typed substitution: each normaliser preserves the literal \(1\)-boundary.

Let \(a_0\) be the generic outer composite of the \(K(u_i)\). Choose
\[
\chi_{\mathrm{gen}}:a_0\longrightarrow K(u)
\]
by the specified generic gap-flattening route over \(V_m\).

For a full \(2\)-term \(a\), write \(A_a(\eta)\) for its action on the \(3\)-inputs \(\eta\), formed over \(V_m^\uparrow\). Each
\[
f_i=f_{u_i,\delta}
\]
has the form
\[
A_{K(u_i)}(\eta)*_2\Phi_i.
\]

Up to the explicitly inserted associativity comparisons, the needed calculation is
\[
\begin{aligned}
\mathsf C^3(f_i)*_2\Phi_{\mathrm{head}}
&\Longrightarrow_4
A_{a_0}(\eta)
 *_2\mathsf C^3(\Phi_i)
 *_2\Phi_{\mathrm{head}}\\
&\Longrightarrow_4
A_{a_0}(\eta)
 *_2\chi_{\mathrm{gen}}[\delta^+]
 *_2\Phi_u\\
&\Longrightarrow_4
\chi_{\mathrm{gen}}[\delta]
 *_2A_{K(u)}(\eta)
 *_2\Phi_u.
\end{aligned}
\tag{18}
\]

The justifications are:

1. The first comparison is the generic action/composition comparison over the appropriate vertical strings of \(3\)-discs.
2. The second is the flattening lemma of §4.
3. The third is the reverse of
   \[
   \Omega_{\chi_{\mathrm{gen}}}:
   \chi_{\mathrm{gen}}[\delta]*_2A_{K(u)}(\eta)
   \longrightarrow
   A_{a_0}(\eta)*_2\chi_{\mathrm{gen}}[\delta^+],
   \]
   formed over \(V_m^\uparrow\).

Before substitution, the generic head comparison, the input comparisons \(b_{u_i}\), and \(\chi_{\mathrm{gen}}\) assemble into a \(3\)-term
\[
b_{\mathrm{eval}}:u\longrightarrow K(u).
\]
Both \(b_{\mathrm{eval}}\) and \(b_u\) have full \(V_m\)-support. Consequently
\[
[b_{\mathrm{eval}},b_u]_{V_m}
\tag{19}
\]
is the final \(4\)-term needed for (17).

This is the point at which an arbitrary generic coherence is handled. It is compared **over its formal pasting context**, and its naturality is used before any chosen input normal form is expanded. No global assertion that arbitrary \(3\)-terms are exchange words has been assumed.

## 6. Compatibility with every \(3\)-term

We now construct, for every grid \(3\)-term \(H:T\to T'\),
\[
\boxed{
I_H:\nu_T\longrightarrow H*_2\nu_{T'}.
}
\tag{20}
\]

For a proper strict fiber, this follows from its already-established \(\mathrm{RC}(3)\). For the three fibers in (4), induct on \(H\).

Apply item 14 to its head. The reduced arity \(P\) has one \(0\)-column. When \(\dim P=3\), its \(1\)-columns are chains
\[
\alpha_{j,0}
\xrightarrow{\xi_{j,1}}
\cdots
\xrightarrow{\xi_{j,r_j}}
\alpha_{j,r_j}.
\]
Let
\[
D_j=\xi_{j,1}*_2\cdots *_2\xi_{j,r_j},
\]
using an identity when \(r_j=0\), and let \(D\) be their framed \(*_1\)-composite.

Write the generic head as
\[
h:u\longrightarrow v.
\]
The generic comparisons \(b_u,b_v\) and \(D\) have types
\[
b_u:u\to K^-,
\qquad
D:K^-\to K^+,
\qquad
b_v:v\to K^+.
\]
Hence
\[
\boxed{
\Xi_P=
[b_u*_2D,\ h*_2b_v]_P
}
\tag{21}
\]
is a valid \(4\)-coherence. The first endpoint uses every \(3\)-variable through \(D\); the second uses them through \(h\). Identities retain all maximal lower-dimensional declarations.

For a \(2\)-dimensional arity, take \(D=1_K\).

After substitution:

- apply the induction hypothesis to the images of the \(\xi_{j,k}\);
- compose those comparisons within each chain and then along \(*_1\);
- apply relative fusion (17) at the two boundary \(2\)-terms.

The normal forms at the two ends of a fixed \(j\)-chain are literally identical. Their strict \(2\)-images agree, and their literal \(1\)-boundaries are the same substitution entries. Therefore, after the input normalisations, the same literal \(2\)-expression appears on both sides. Use **the identical chosen \(\Phi\)** on those two expressions.

This gives
\[
f_{u,\delta}\longrightarrow D[\delta]*_2f_{v,\delta}.
\]
Together with (17) and (21), the resulting route is
\[
\begin{aligned}
\nu_{u[\delta]}
&\Longrightarrow_4 b_u[\delta]*_2f_{u,\delta}\\
&\Longrightarrow_4
(b_u[\delta]*_2D[\delta])*_2f_{v,\delta}\\
&\Longrightarrow_4
h[\delta]*_2(b_v[\delta]*_2f_{v,\delta})\\
&\Longrightarrow_4
h[\delta]*_2\nu_{v[\delta]}.
\end{aligned}
\tag{22}
\]
The comparison from the original head to the reduced head, supplied by item 14, transfers this to (20).

Every recursive call concerns an original substituted \(3\)-argument. Thus this induction covers arbitrary \(3\)-dimensional heads as well as \(2\)-dimensional coherence heads.

### The requested \(4\)-term

For parallel
\[
\alpha,\beta:T\longrightarrow T',
\]
put \(\nu=\nu_{T'}\), and choose its inverse \(\bar\nu\) and cancellation witness. These are constructive CaTT operations on composites of coherences. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

Let
\[
c_\alpha:(\alpha*_2\nu)*_2\bar\nu\longrightarrow\alpha,
\qquad
c_\beta:(\beta*_2\nu)*_2\bar\nu\longrightarrow\beta
\]
be the resulting cancellation routes, including associators and unitors.

Then
\[
\boxed{
c_\alpha^\dagger
 *_3
\bigl((I_\alpha^\dagger*_3I_\beta)*_21_{\bar\nu}\bigr)
 *_3
c_\beta
:
\alpha\longrightarrow\beta
}
\tag{23}
\]
is the required term.

All smaller \(0\)-boundary rectangles in the grid have at most two faces and are covered by §2. Equations (17)–(23) handle the remaining three fibers. Therefore
\[
\boxed{\mathrm{RC}(3)\text{ holds for the entire }2\times2\text{ grid}.}
\]

## 7. Several vertically composable \(3\)-generators

There is also a direct extension of item 20.

### Proposition

Let
\[
\Gamma=(\Lambda,z_i:A_i\to B_i\mid i\in I),
\]
where \(\Lambda\) has dimension at most \(2\), its generating \(1\)-graph is acyclic, and \(\mathrm{RC}(3)\) holds in \(\Lambda\). Assume:

1. Nonidentity strict \(3\)-cells are uniquely represented by nonempty composable vertical words in the \(z_i\).
2. Every defined \(*_0\)- or \(*_1\)-composition involving a nonidentity strict \(3\)-cell has exactly one nonidentity operand and returns that operand.
3. \(\pi A_i\ne\pi B_i\) for every \(i\).

Then \(\mathrm{RC}(3)\) holds in \(\Gamma\).

### Construction

Head expansion works recursively on all original \(3\)-arguments. To distribute lower compositions over vertical strings, use the direct \(4\)-coherences
\[
(U*_2V)*_kE
\longrightarrow
(U*_k1_{s_2E})*_2(V*_kE),
\qquad k=0,1,
\tag{24}
\]
over
\[
(D^3\vee_2D^3)\vee_kD^3,
\]
and the left-hand versions over
\[
D^3\vee_k(D^3\vee_2D^3).
\]

Both sides of (24) use all three formal \(3\)-variables and have the same literal \(2\)-boundary.

Assumption 2 ensures that the other operand of a lower composition has an identity strict image and therefore restricts to \(\Lambda\). Repeatedly apply (24), then absorb the \(\Lambda\)-factors into adjacent nonempty factors. This constructs
\[
e_H:H\longrightarrow F_1*_2\cdots *_2F_m,
\qquad
\pi F_j=z_{i_j},
\tag{25}
\]
where \(i_1\cdots i_m\) is the strict word of \(H\).

For each \(i\), the restricted context \((\Lambda,z_i)\) has exactly one nonidentity strict \(3\)-cell: a longer word using only \(z_i\) cannot compose, by assumption 3. Item 20 therefore applies to that restricted context.

Now factor parallel \(H,H'\) with the same strict word:
\[
F_j:u_{j-1}\to u_j,
\qquad
F'_j:u'_{j-1}\to u'_j.
\]
All intermediate \(2\)-terms have the same literal \(1\)-boundary frame. Choose, using \(\mathrm{RC}(2)\) in \(\Lambda\),
\[
\nu_j:u'_j\to u_j,
\qquad
\bar\nu_j:u_j\to u'_j,
\]
taking endpoint identities.

The two terms
\[
F'_j,
\qquad
(\nu_{j-1}*_2F_j)*_2\bar\nu_j
\]
are parallel and have strict image \(z_{i_j}\). Support agreement places both in \((\Lambda,z_{i_j})\), so item 20 supplies their \(4\)-comparison.

Compose these comparisons. The resulting intermediate factors are
\[
\bar\nu_j*_2\nu_j.
\]
They are \(\Lambda\)-terms, so \(\mathrm{RC}(3)\) in \(\Lambda\) compares them with the appropriate identities. Cancelling them gives a \(4\)-term from \(H'\) to the same product \(F_1*_2\cdots *_2F_m\) reached by \(H\). This proves the proposition.

No comparison between the chosen \(4\)-fillers is used.

For example, it applies to
\[
x,y;\quad f,g:x\to y;\quad a,b:f\to g;
\quad z:a\to b,\quad w:b\to a.
\tag{26}
\]
The strict \(3\)-cells are the alternating words
\[
z,\ w,\ zw,\ wz,\ zwz,\ wzw,\ldots.
\]
Their lower compositions are units because \(x\ne y\) and \(f\ne g\). The \(2\)-dimensional base satisfies \(\mathrm{RC}(3)\): support restricts each pair to a \(2\)-globe, a \(1\)-globe, or a point, where one full-support coherence gives the comparison.

Thus (26), which is not a pasting context, satisfies \(\mathrm{RC}(3)\), including arbitrary repeated vertical words.

## 8. A nontrivial strict whisker

A concrete extension in the other direction is the Gray cube with one new outgoing edge
\[
e:111\longrightarrow c.
\tag{27}
\]
This context also satisfies \(\mathrm{RC}(3)\).

Its nonidentity strict \(3\)-cells are exactly
\[
X,\qquad X_e=X*_01^3_{1^2_e}.
\tag{28}
\]
Indeed, freely adjoining the new terminal vertex and edge copies each old hom \(C(u,111)\) into \(C(u,c)\), by right whiskering with \(e\). It creates no other composites. Its new strict \(2\)-cells are likewise exactly the fixed-suffix whiskers of old ones.

The \(2\)-skeleton therefore satisfies \(\mathrm{RC}(3)\) by the fixed-path extension in §2.1 applied to the two cube hemispheres and their proper intervals.

The new local comparison is formed over
\[
P=D^3_z\vee_0D^1_e.
\]
Write
\[
z:a\to b,\qquad a,b:f\to g,
\]
and let
\[
\beta:c_2\to d_2,\qquad c_2,d_2:r\to s
\]
be a \(3\)-term over \(D^1_e\), with strict image \(1^3_{1^2_e}\).

Choose path-supported \(2\)-terms
\[
\kappa_f:f*_0r\to f*_0e,
\qquad
\lambda_g:g*_0e\to g*_0s.
\]
Over \(D^2_a\vee_0D^1_e\), define
\[
L:a*_0c_2\longrightarrow
C^2(\kappa_f,a*_01^2_e,\lambda_g),
\]
and define \(R\) analogously over \(D^2_b\vee_0D^1_e\). Both are full-support \(3\)-coherences.

With \(I_e=1^3_{1^2_e}\), the new \(4\)-term is
\[
\boxed{
\operatorname{coh}_{P,\,
(z*_0\beta)\to
L*_2C^3(\kappa_f,z*_0I_e,\lambda_g)*_2R^\dagger}
[\operatorname{id}].
}
\tag{29}
\]
Its endpoints have exactly the same \(2\)-source and \(2\)-target and full \(P\)-support.

To move an existing \(2\)-frame past \(e\), use item 15 over
\[
(D^2_p\vee_1D^3_z\vee_1D^2_q)\vee_0D^1_e.
\]
Writing \(W(-)=(-)*_0I_e\) in dimension \(3\), the comparison has the form
\[
W(C^3(p,z,q))*_2D_b
\longrightarrow
D_a*_2C^3(Wp,Wz,Wq).
\tag{30}
\]
Append \(D_b^\dagger\) and cancel \(D_b*_2D_b^\dagger\), using the established \(\mathrm{RC}(3)\) of the \(2\)-skeleton.

Now perform item 20’s head expansion. The strict \(X\)-case restricts to the original cube. For the strict \(X_e\)-case, the only new binary case is a term of strict image \(X\) composed along \(*_0\) with a term of strict image \(1^3_{1^2_e}\). Apply (29), then (30). The remaining path and point adjustments are exactly the generic templates of item 20, with their formal \(3\)-variable assigned \(X_e\).

The remaining \(X\)-free \(3\)-factors are compared in the \(2\)-skeleton. This gives a common normal form for all terms with strict image \(X_e\), proving the claim.

## 9. Scope and the next-dimensional obligation

The argument proves:

- \(\mathrm{RC}(3)\) for the \(2\times2\) grid;
- the vertical-word extension in §7;
- a case with a nontrivial strict whisker, namely (27).

It does not establish Question 2 for all positive acyclic \(2\)-contexts.

For Question 4, one precise new obligation is already visible in the grid proof. In §4, cut-fiber coherence supplies a \(4\)-term
\[
C(k,k'):k\longrightarrow k'
\]
between parallel \(3\)-terms. A dimension-higher proof must compare choices and composites of these fillers. For example, it needs \(5\)-terms
\[
C(k_0,k_1)*_3C(k_1,k_2)
\longrightarrow
C(k_0,k_2).
\tag{31}
\]
The current proof never requires (31).

Equivalently, after choosing \(4\)-normalisers
\[
\eta_H:H\longrightarrow N(H)
\]
for \(3\)-terms, compatibility with a \(4\)-term \(K:H\to H'\) requires
\[
\eta_H
\longrightarrow
K*_3\eta_{H'}
\tag{32}
\]
in dimension \(5\). The generic pasting-context instances of (32) are available from the coherence rule; the missing step is relative fusion after the chosen \(3\)-normalisers have been substituted and expanded.

I have not constructed that \(5\)-dimensional fusion for the \(4\)-cube or the cylinder of \(D^3\), nor proved the general \(\mathrm{RC}(n)\) or \(G(n)\) statements.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level.**
- **Settled:** Question 1. RC(3) holds for the 2 × 2 grid.
- **Two extensions toward Question 3:**
  - several 3-generators forming unique vertical words, with unit lower compositions (§7);
  - the Gray cube with an outgoing edge, a 3-generator with a nontrivial strict whisker (§8).
- **Open:** Question 2 (general exchange in dimension 2), Question 4 (RC(4)), Question 5.
- **New precise obligation for RC(4):** the 5-dimensional fusion (31)/(32).

Checked step by step:

1. **Strict 2-cells, §1.** With faces oriented hv ⇒ vh, the rewrites (1) are right. I enumerated adjacent hv pairs in the six paths: F and G are the only independent pair. The fibres needing work are DFG, FGE and DFGE (4). Their boundary paths meet only at the corners (5), so every head has a single nonconstant 0-column and item 14 reduces it to a vertical chain.
2. **Two-square cut fibre, §2.2.** The cut vertex c and the bracketings (11) make item 25's matrix argument apply with the two-edge paths f_i, g_i in place of single edges.
   - The generic matrix terms over V₃ ∨₀ V₃ and V₆ ∨₀ V₆ do not depend on the triangular or globular boundary of item 25's generators, so this substitution is legitimate.
   - The factorwise comparisons are RC(3) of single squares (item 10).
   - Result: RC(3) for every grid fibre with at most two faces, including FG.
3. **Normal forms, §3.** The rules are: F before G, D first, E last, and at most one exchange (the fixed reverse of item 24). The recursion for ν_T is well founded because a substituted input with the same face set is a proper subterm.
4. **Flattening lemma, §4.** This is the key new idea.
   - Every exchange is between F and G, which are adjacent after D and before E.
   - Reassociating isolates F, G, the path factors between them and the corrections on p₁ … p₄ into one literal 2-subterm of the subcontext Λ_FG.
   - Two flattenings then differ by a 3-term in the FG fibre, and (13) compares them.
   - I checked that the paths involved lie in Λ_FG: p₁ … p₄ use only vertices of the two squares.
5. **Relative fusion and compatibility, §5–6.**
   - The 4-step calculation (18) uses the generic action/composition comparison over V_m↑, the flattening lemma and Ω_χ, which matches item 17's pattern.
   - The final comparison (19) is a full coherence over V_m.
   - Ξ_P (21) is a valid coherence: both endpoints use every 3-variable.
   - The induction in (22) recurses only on original 3-arguments.
   - As in earlier rounds, not every 4-cell is written out.
6. **Vertical words, §7.**
   - The distribution coherences (24) over (D³ ∨₂ D³) ∨_k D³ are full on both sides.
   - Assumption 2 makes the other operand of a lower composition a Λ-term.
   - Each factor F_j lies in (Λ, z_{i_j}), where item 20 applies because assumption 3 prevents words in one letter.
   - Example (26) is right: x ≠ y and f ≠ g make the lower compositions units.
7. **Cube plus an edge, §8.** The new strict 3-cells are X and X ∗₀ e (28), because adjoining a terminal edge only copies homs into c. The 4-coherence (29) over D³ ∨₀ D¹ has full support with equal 2-boundaries. Moving frames uses item 15.

**Relation to other results.** The cone-over-coherences round-5 extension theorem (`cone-over-coherences-r5-2026-11-18.md` §1–6) proves RC(3)(Λ + any 3-generators) ⇔ RC(3)(Λ) for dim Λ ≤ 2 with an acyclic 1-graph. That subsumes §7 and §8 and answers Question 3 in full. Question 2 is therefore the whole remaining RC(3) problem. The grid is its first case without a cut vertex.

Follow-up prompt: `outbox/gray-contexts-r8.md` (round 8, unsent).
