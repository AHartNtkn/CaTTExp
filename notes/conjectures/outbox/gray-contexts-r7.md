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

