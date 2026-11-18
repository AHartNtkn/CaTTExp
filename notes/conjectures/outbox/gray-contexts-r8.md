# Problem: composites of molecules in CaTT (Gray contexts), round 8

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
26. **On question 1's hypothesis.** In an acyclic generating 1-graph, a 2-generator with an identity source has a closed path, hence an identity, as target. So "acyclic, and no 2-generator has an identity as both source and target" is the same as "acyclic, and every 2-generator has nonempty source and target paths". Forest–Mimram ([arXiv 2109.05369](https://arxiv.org/abs/2109.05369)) prove coherence for the free Gray category on a positive Gray presentation (termination of interchanger rewriting plus confluence of critical branchings); this is the strict-Gray analogue, not a relative normalisation of CaTT terms.

27. **The 2 × 2 grid (proved).** RC(3) holds for the Gray product of two paths of length 2. Orient each face hv ⇒ vh, and name the faces D = e₁₀, F = e₀₀, G = e₁₁, E = e₀₁. The six paths are p₀ = hhvv, p₁ = hvhv, p₂ = vhhv, p₃ = hvvh, p₄ = vhvh, p₅ = vvhh, with rewrites p₀ →D p₁, p₁ →F p₂ →G p₄, p₁ →G p₃ →F p₄, p₄ →E p₅. Only F and G are independent, so the fibres that need work are DFG, FGE and DFGE.
    - *One active column.* The boundary paths of those three fibres meet only at the corners, so every head has one nonconstant 0-column and item 14 reduces it to a vertical chain V_m.
    - *The FG cut fibre.* F and G meet at the cut vertex c = (1,1). With the bracketings p₁ = f₀ ∗₀ g₀, p₂ = f₁ ∗₀ g₀, p₃ = f₀ ∗₀ g₁, p₄ = f₁ ∗₀ g₁ (two-edge paths), item 25's matrix argument applies verbatim, with item 10 supplying the factorwise comparisons. So every grid fibre with at most two faces satisfies RC(3).
    - *Normal forms.* N(T) = C(κ(r, pᵢ), E(w), κ(pⱼ, s)), where E(w) is the event word with F before G, D first and E last. ν_T is defined by the generic comparison over V_m, the input normalisers and a flattening Φ that expands chosen normal forms, merges path factors and applies the fixed reverse of item 24 at most once.
    - *Flattening lemma.* Every exchange is between F and G, which are adjacent in every word. Reassociating isolates F, G, the path factors between them and their corrections into one literal 2-subterm of the two-square subcontext, so any two flattenings differ by a 3-term in the FG fibre, where RC(3) holds.
    - *Fusion and compatibility.* Relative evaluation fusion ν_{u[δ]} → b_u[δ] ∗₂ f_{u,δ} is proved by induction on u, keeping input normalisers formal until they have been moved through the head by generic naturality over V_m↑. Compatibility I_H : ν_T → H ∗₂ ν_{T′} uses one coherence Ξ_P = [b_u ∗₂ D, h ∗₂ b_v]_P over the reduced 3-arity.
28. **Vertically composable 3-generators (proved).** If dim Λ ≤ 2, Λ has an acyclic 1-graph and RC(3), and Γ = (Λ, z_i : A_i → B_i) is such that nonidentity strict 3-cells are unique vertical words in the z_i, every lower composition with a nonidentity 3-cell has one nonidentity operand, and π(A_i) ≠ π(B_i), then RC(3)(Γ). Example: x, y; f, g : x → y; a, b : f → g; z : a → b, w : b → a.
29. **A nontrivial strict whisker (proved).** The Gray cube with an outgoing edge e : 111 → c satisfies RC(3). Its nonidentity strict 3-cells are X and X ∗₀ e, and the new local comparison is one 4-coherence over D³ ∨₀ D¹.
30. **The 3-generator extension theorem (proved).** Let Λ have dimension ≤ 2 and an acyclic generating 1-graph, and let Γ = (Λ, z_1 : A_1 → B_1, …, z_k : A_k → B_k) with A_i, B_i parallel 2-terms of Λ. Then RC(3)(Γ) ⇔ RC(3)(Λ), with no restriction on the number, order, whiskering or composability of the z_i. This supersedes items 20, 28 and 29.
    - *Quotient category.* For literal parallel 1-terms p, q, 3-terms between 2-terms p → q modulo "joined by a 4-term" form a category (4-terms of Γ and 3-terms of Λ are invertible, by the Benjamin–Markakis–Sarti criterion). Normalise each 3-term U : A → B to r_A⁻¹ ; U ; r_B, with r_A : A → (chosen representative of πA) from RC(2). RC(3)(Λ) makes every normalised Λ-3-term an identity.
    - *Comparison lemma.* For 2-terms F(X), G(X) over (Λ, X) with X a fresh 2-variable and πF(X) = πG(X) with X formal, RC(2) gives J(X) : F(X) → G(X). Depth-1 naturality of J in X (Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620, Thm 3.1) shows F and G whisker every 3-term U to the same normalised arrow.
    - *Strict presentation.* Strict 3-cells are composites of elementary steps C[z_i], and equality is generated by replacement and adjacent exchange (Polygraphs book, App. D, Props. D.3.9 and D.3.12). Both moves preserve normalised evaluation, so it is well defined on strict 3-cells, and sequentialisation shows every 3-term evaluates to its strict image.
    - *Consequence.* RC(3) for every 3-dimensional context with an acyclic dimension-≤2 part reduces to its 2-skeleton.
31. **The next-dimensional obligation.** In item 27, cut-fibre coherence supplies 4-terms C(k, k′) : k → k′ between parallel 3-terms, and no comparison between them is needed. For RC(4), after choosing 4-normalisers η_H : H → N(H) for 3-terms, compatibility with a 4-term K : H → H′ needs a 5-term η_H → K ∗₃ η_{H′}, equivalently 5-terms C(k₀,k₁) ∗₃ C(k₁,k₂) → C(k₀,k₂). The generic pasting-context instances exist by the coherence rule. The missing step is relative fusion after the chosen 3-normalisers have been substituted and expanded.

## 3. What remains

By item 30, RC(3) for every context of dimension ≤ 3 whose dimension-≤2 part has an acyclic generating 1-graph reduces to RC(3) of that 2-dimensional part. Items 10, 13, 17, 22, 23, 25 and 27 settle 2-dimensional cases with at most one pair of independent letters. In each, either a cut vertex splits heads horizontally, or the independent letters are adjacent in every event word, so one exchange can be isolated in a smaller fibre. The open step is a 2-dimensional context in which a strict 2-cell has event words related by several exchanges, or by exchanges between letters that are not adjacent in every word. In dimension 4 the open step is item 31.

## 4. Questions

1. **General exchange in dimension 2.** Prove RC(3) for every finite context of dimension ≤ 2 whose generating 1-graph is acyclic and in which every 2-generator has nonempty source and target paths (item 26). Or give a counterexample. Smallest open cases:
   - the Gray product of paths of lengths 2 and 3 (six squares; a strict 2-cell can need several exchanges, and independent letters need not be adjacent);
   - the 3 × 3 grid;
   - finite Steiner loop-free 2-computads, which include all cylinders of 1-dimensional pasting contexts and all Gray products of two such contexts.
   A Squier-style argument would suffice: a normal form for event words modulo exchange (for example a fixed orientation of exchanges that terminates and whose critical branchings close), together with relative fusion as in item 27 that isolates each exchange step in a smaller fibre.
2. **RC(4).** Construct the 5-dimensional compatibility of item 31, or show it fails. Smallest cases:
   - the triangle context (x, y, z; f : x → y, g : y → z, h : x → z; α : f ∗₀ g ⇒ h), where RC(3) holds and RC(4) is open;
   - the lax square S of item 5;
   - the 4-dimensional Gray cube, or the cylinder of D³.
3. **A 4-dimensional extension theorem.** Is there an analogue of item 30 one dimension up: for Λ of dimension ≤ 3 with RC(4), does adjoining 4-generators preserve RC(4)? The quotient-category argument needs 5-terms between 4-terms and invertibility of 5-terms.
4. **RC(n) or G(n).** Prove RC(n) under the hypothesis of question 1, suitably extended to higher generators, or the weaker G(n) for frame-acyclic molecules.

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) under a stated hypothesis; a counterexample (a context satisfying the hypothesis of question 1 with two parallel terms of equal strict image and no term between them); or a published reference.

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

There are two results.

1. **RC(3) holds for the \(2\times3\) grid.** The additional comparisons are a comparison between block exchange and individual exchanges, and one 4-cell filling the square in the graph of event orders.
2. **Adjoining 4-generators preserves RC(4) if the base also satisfies RC(3)** and has an acyclic generating 1-graph. This does not establish the extension theorem from RC(4) alone.

I give the constructions below. The general positive-computad statement, the \(3\times3\) grid, and RC(4) for the triangle and lax square are not proved here.

# I. RC(3) for the \(2\times3\) grid

Write
\[
V_m=D^2\vee_1\cdots\vee_1D^2
\]
for a vertical chain of \(m\) formal 2-cells. All composites below have fixed bracketings.

For parallel full-support terms \(a,b\) over a pasting context \(P\), use the notation
\[
[a,b]_P:=\operatorname{coh}_{P,a\to b}[\mathrm{id}].
\]
Thus, when \(a,b\) are 3-terms, \([a,b]_P\) is a 4-term.

Inverses below are the constructed weak inverses, with their cancellation cells. They are available for the 3-terms used here because the grid has no 3-generators. The invertibility criterion supplies the inverse and cancellation data without assuming RC(3). 

## 1. The event orders and the required proper fibres

Use vertices \((i,j)\), with \(0\le i\le2\), \(0\le j\le3\), and orient every square \(hv\Rightarrow vh\). Label the faces
\[
a=e_{10},\quad b=e_{11},\quad c=e_{12},\qquad
d=e_{00},\quad e=e_{01},\quad f=e_{02}.
\]

The order constraints on the six events are
\[
a<b<c<f,\qquad a<d<e<f,\qquad b<e.
\]
Consequently the full composite has exactly five event words:
\[
\begin{aligned}
w_0&=abcdef,&
w_1&=abdcef,&
w_2&=abdecf,\\
w_3&=adbcef,&
w_4&=adbecf.
\end{aligned}
\]

Orient exchanges towards alphabetical order. The complete reduction graph is:

| Word | Reductions |
|---|---|
| \(adbecf\) | \(abdecf\), by \(db\mapsto bd\); \(adbcef\), by \(ec\mapsto ce\) |
| \(abdecf\) | \(abdcef\), by \(ec\mapsto ce\) |
| \(adbcef\) | \(abdcef\), by \(db\mapsto bd\) |
| \(abdcef\) | \(abcdef\), by \(dc\mapsto cd\) |
| \(abcdef\) | None |

There is one square and one additional edge.

Here is also the required classification of proper fibres. A frontier path determines an ideal of the event poset. For ideals \(I\subseteq J\), the events between their frontiers are
\[
R=J\setminus I
\]
with the induced order. Fixing words on \(I\) and on its complementary final segment embeds the event-order graph of \(R\) into the five-word graph above. The regions with at least three faces are precisely:

| Event set | Treatment |
|---|---|
| \(abc,def\) | Three-square strips |
| \(abd,bce,bde,cef\) | Established \(2\times2\) fibres, with fixed paths |
| \(bcd,cde\) | A square beside a two-square strip |
| \(abcd,cdef\) | New fibres with a three-vertex exchange graph |
| \(abde,bcef\) | Established \(2\times2\) fibres |
| \(bcde\) | New four-face fibre |
| \(abcde,bcdef\) | New five-face fibres |
| \(abcdef\) | Full six-face fibre |

The new fibres in the last four rows have boundary paths meeting only at their external endpoints. Thus every reduced head for any of those fibres has one nonconstant 0-column. A reduced 2-head has arity \(V_m\); a reduced 3-head retains its actual one-column 3-dimensional pasting arity.

The three-square strips also have this property after removing their fixed exterior paths: their extreme paths are \(hvvv\) and \(vvvh\). They have a unique event word, and their proper intervals are two-square strips or single faces. Item 17’s construction therefore applies: its geometric requirements are one retained column, a unique event word, and RC(3) for proper intervals. No full-span face is needed once the one-column assertion has been established directly.

We next handle the two cut fibres \(bcd,cde\), and then construct the new exchange comparisons.

## 2. The two cut fibres

The persistent cuts are
\[
bcd=d\ast_0(bc)\quad\text{at }(1,1),
\qquad
cde=(de)\ast_0c\quad\text{at }(1,2).
\]

The factor fibres are single squares and two-square strips. Their RC(3) results, including their subfibres, are already available.

For a literal intermediate 1-term \(q\), let \(q_L,q_R\) be the chosen path terms on the two sides of the cut, and choose a path coherence
\[
\kappa_q:q\longrightarrow q_L\ast_0q_R.
\]
For a 2-term \(T_i:q_{i-1}\to q_i\), whose strict factors are \(l_i,r_i\), use the row normal form
\[
\kappa_{q_{i-1}}
\ast_1
\bigl(K_L(l_i)\ast_0K_R(r_i)\bigr)
\ast_1
\kappa_{q_i}^{\dagger}.
\tag{1}
\]
Rows with an identity factor are retained.

For a vertical sequence of such rows:

1. Cancel the internal \(\kappa_{q_i}^{\dagger}\ast_1\kappa_{q_i}\) using path-context comparisons.
2. Apply
   \[
   I_m:
   C(A_1\ast_0B_1,\ldots,A_m\ast_0B_m)
   \longrightarrow
   C(A_1,\ldots,A_m)\ast_0 C(B_1,\ldots,B_m).
   \tag{2}
   \]
3. Normalize the two factor composites.

The term \(I_m\) is the full-support coherence on \(V_m\vee_0V_m\).

A head with one retained column uses this row construction. A head with two retained columns is split at the persistent cut and normalized factorwise. The comparisons between these constructions are exactly the matrix fusion comparisons on \(V_3\vee_0V_3\) and \(V_6\vee_0V_6\) from item 25, together with factorwise RC(3) and the path comparisons. Their formal entries may be arbitrary 2-terms; replacing one square factor by a two-square strip changes none of their arities.

If one input row has all three events, its normalizer is defined recursively on that input’s smaller 2-term derivation. Its own RC(3) is not used.

The same construction gives the needed fixed-path variants. A path factor has only identity strict 2-cells, so its comparisons come from item 4. The generic folds have arities
\[
C_u\vee_0V_m\vee_0C_v,
\]
and their naturality comparisons have the corresponding arities with \(V_m\) replaced by \(V_m^\uparrow\). Item 14 handles the literal path lifts, and the point-collapse clause handles empty paths.

For later use, choose explicit serializations of the two product normal forms:

- From \(K_d\ast_0K_{bc}\), use the inverse of (2) with rows
  \[
  (1,b),\quad(1,c),\quad(d,1).
  \]
  This gives the order \(bcd\).
- From \(K_{de}\ast_0K_c\), use rows
  \[
  (1,c),\quad(d,1),\quad(e,1).
  \]
  This gives \(cde\).

Insert the fixed factor unitors, path transports and reassociations. These serializations are specified composites, not arbitrary applications of RC(2).

This proves RC(3) for \(bcd,cde\) by the same relative-fusion and actual-3-arity argument as item 25.

## 3. A block exchange is compared with its individual exchanges

This is a useful generic term beyond this particular grid.

On
\[
P_{m,n}=V_m\vee_0V_n,
\]
write the formal variables as
\[
\alpha_i:f_{i-1}\to f_i,\qquad
\beta_j:g_{j-1}\to g_j,
\]
and put
\[
A=C(\alpha_1,\ldots,\alpha_m),\qquad
B=C(\beta_1,\ldots,\beta_n).
\]

Define
\[
\begin{aligned}
L&=(A\ast_0 1_{g_0})\ast_1(1_{f_m}\ast_0 B),\\
R&=(1_{f_0}\ast_0 B)\ast_1(A\ast_0 1_{g_n}),
\end{aligned}
\]
and take the block exchange
\[
\chi_{m,n}=[L,R]_{P_{m,n}}.
\]

Let
\[
d_L:L\to E_L,\qquad d_R:R\to E_R
\]
be the specified distributors and reassociations expanding \(A,B\) into their individual 2-variables. Define
\[
G_{m,n}:E_L\to E_R
\]
by moving \(\beta_1\) left across \(\alpha_m,\ldots,\alpha_1\), then moving \(\beta_2\) across the same list, and so on. Every step is an explicitly framed instance of the two-variable exchange.

Both
\[
\chi_{m,n}
\quad\text{and}\quad
d_L\ast_2G_{m,n}\ast_2d_R^\dagger
\]
are 3-terms with literal source \(L\), literal target \(R\), and full support \(P_{m,n}\). Therefore
\[
\boxed{
B_{m,n}
=
\bigl[
\chi_{m,n},
d_L\ast_2G_{m,n}\ast_2d_R^\dagger
\bigr]_{P_{m,n}}
}
\tag{3}
\]
is a valid 4-term.

A fixed path between the factors uses
\[
V_m\vee_0C_w\vee_0V_n
\]
instead. The same construction and support check apply. Empty event lists are handled by the path/unit cases.

Formula (3) matters because it reduces a horizontal serialization comparison to individual exchanges **before substitution**. After substitution of chosen event terms, each individual exchange is syntactically a framed two-face exchange. No locality assertion is inferred from the support of an entire six-face 3-term.

## 4. Choose literal evaluations of event words

Fix:

- a literal 1-term \(\ell_p\) for each frontier path \(p\);
- a 2-term
  \[
  t_{p,x}:\ell_p\to\ell_{px}
  \]
  for each enabled face \(x\), obtained from that face by its fixed edge whiskers and path-boundary corrections;
- a local 3-term
  \[
  \epsilon_{p,x,y}:
  t_{p,x}\ast_1t_{px,y}
  \longrightarrow
  t_{p,y}\ast_1t_{py,x}
  \tag{4}
  \]
  for each enabled independent pair.

The local context for (4) includes all its fixed path segments.

There are three independent pairs:

- \(b,d\), with a fixed final vertical edge;
- \(c,e\), with a fixed initial vertical edge;
- \(c,d\), with the intervening edge
  \[
  v_{(1,1)}:(1,1)\to(1,2).
  \]

For the last pair, the physical path order is
\[
d,\quad v_{(1,1)},\quad c.
\]
Its two-face domain has source and target paths
\[
(hv)\,v_{(1,1)}\,(hv),
\qquad
(vh)\,v_{(1,1)}\,(vh).
\]
The fixed-path cut construction above applies to this domain.

Write \(\operatorname{ev}(w)\) for the chosen composite of the \(t_{p,x}\) along \(w\). A graph edge is **defined** as the corresponding \(\epsilon\), framed by the specified earlier and later event terms and the fixed reassociations.

Consequently:

- alternative implementations of a bare exchange can be compared in its two-face context;
- the resulting 4-term can then be framed;
- an arbitrary 3-term between two whole-word evaluations is not presumed to have this form.

That last class will be handled by relative fusion.

## 5. The square in the exchange graph has a direct 4-cell

The relevant frontiers are
\[
p_1=hvhvv,\qquad p_3=vhvhv,\qquad p_5=vvhvh.
\]
Put
\[
\begin{aligned}
X_0&=\operatorname{ev}(bd):\ell_{p_1}\to\ell_{p_3},&
X_1&=\operatorname{ev}(db):\ell_{p_1}\to\ell_{p_3},\\
Y_0&=\operatorname{ev}(ce):\ell_{p_3}\to\ell_{p_5},&
Y_1&=\operatorname{ev}(ec):\ell_{p_3}\to\ell_{p_5}.
\end{aligned}
\]

Choose the sorting-oriented instances of (4):
\[
\alpha:X_1\to X_0,\qquad
\beta:Y_1\to Y_0.
\]

Bracket the four middle events of each cycle vertex as \(X_i\ast_1Y_j\), with optional outer \(a,f\). Thus the four vertices have these literal expressions.

On
\[
P_\square=D^3\vee_1D^3
\]
form
\[
\begin{aligned}
L_\square
&=
(\alpha\ast_1 1_{Y_1})
\ast_2
(1_{X_0}\ast_1\beta),\\
R_\square
&=
(1_{X_1}\ast_1\beta)
\ast_2
(\alpha\ast_1 1_{Y_0}).
\end{aligned}
\]
Both are 3-terms
\[
X_1\ast_1Y_1\longrightarrow X_0\ast_1Y_0
\]
of full support. Hence
\[
\boxed{
S_\square=[L_\square,R_\square]_{P_\square}
}
\tag{5}
\]
is a 4-term.

After substitution and optional framing by \(a,f\), it compares
\[
w_4\to w_2\to w_1
\qquad\text{with}\qquad
w_4\to w_3\to w_1.
\]

For a formula whose boundaries are already the complete framed composites, use the full-support coherence on
\[
D^2\vee_1(D^3\vee_1D^3)\vee_1D^2,
\]
omitting either exterior \(D^2\) when absent.

Choose the sorting paths
\[
\begin{aligned}
\phi_{w_0}&=1,\\
\phi_{w_1}&=(w_1\to w_0),\\
\phi_{w_2}&=(w_2\to w_1)\ast_2\phi_{w_1},\\
\phi_{w_3}&=(w_3\to w_1)\ast_2\phi_{w_1},\\
\phi_{w_4}&=(w_4\to w_2)\ast_2\phi_{w_2}.
\end{aligned}
\]
For every graph edge \(e:v\to w\), there is now a 4-term
\[
e\ast_2\phi_w\longrightarrow\phi_v.
\tag{6}
\]
For the four chosen tree edges this uses associators, unitors and cancellation. The remaining edge uses (5). Reversed edges use the chosen inverse data.

Induction on a graph path gives the corresponding comparison for every evaluated path. The same argument applies to proper-region graphs: they are trees or have this same square, with the appropriate optional exterior events removed.

No general Squier theorem is required for this finite graph.

## 6. The flattening comparison

For a strict fibre \(R\) without an interior cut, choose
\[
K_R=\operatorname{ev}(w_R),
\]
where \(w_R\) is the alphabetically ordered event word. Its serialization is the identity. For the cut fibres, use the explicit serializations from §2.

Define a selected flattening by the following operations, in this order:

1. Expand the **chosen normal forms** of its inputs.
2. Apply the specified product serializations.
3. Merge boundary-path factors and reassociate.
4. Apply the selected sorting path in the event-order graph.

The comparison between two hierarchical applications of this construction is assembled as follows.

| Comparison required | 4-term used |
|---|---|
| Moving an input normalizer through a generic 3-operation | Its \(\Omega\)-term on the lifted pasting arity |
| Reassociation or another generic head route | Full-support coherence on the stated generic pasting arity |
| Merging or cancelling path factors | Item 4, with item 14’s substitution comparisons |
| Regrouping matrix rows, including identity rows | Item 25’s matrix fusion |
| Replacing block exchange by individual exchanges | \(B_{m,n}\) from (3) |
| Replacing a bare individual exchange by the selected \(\epsilon\) | RC(3) of its two-face context |
| Comparing evaluated exchange paths | \(S_\square\), (6), and backtrack cancellation |

This list is exhaustive for the selected flattenings: their constructors are path transports, vertical reassociations, the matrix folds, distributors, and the explicitly chosen exchanges.

There are two distinct uses of support here.

First, a residual 3-term belonging to a proper input can be strengthened to that **entire proper fibre**, including its fixed exterior paths, and compared there by the induction hypothesis.

Second, a whole-word graph edge is local only because it was defined as a framed \(\epsilon\). Exact support alone would not provide that factorization.

Thus the flattening comparison never invokes RC(3) of the fibre currently being proved.

## 7. Relative fusion, with explicit decreasing inductions

For a 2-term \(T:r\to s\), of strict image \(w:p\Rightarrow q\), set
\[
N(T)=
C\bigl(
\kappa(r,\ell_p),
K_w,
\kappa(\ell_q,s)
\bigr).
\tag{7}
\]

For each event count, define
\[
\nu_T:T\to N(T)
\]
by induction on the **actual 2-term derivation**. On already settled proper fibres one may use the established normalizers and comparisons.

For a new full-fibre head, apply item 14. Its reduced 2-arity is \(V_m\). For the resulting full formal 2-term \(u\), let \(K(u)\) be the boundary-corrected vertical composite of the formal variables, and take
\[
b_u=[u,K(u)]_{V_m}.
\]
After substitution, follow \(b_u\) by the input normalizers and the flattening of §6. Recursive calls to \(\nu\) concern only the 2-images in the displayed outer substitution of \(T\).

The required relative-fusion term is
\[
\boxed{
E(u,\delta):
\nu_{u[\delta]}
\longrightarrow
b_u[\delta]\ast_2 f_{u,\delta},
}
\tag{8}
\]
where \(f_{u,\delta}\) is input normalization followed by the selected flattening.

Prove (8) by induction on the **original generic derivation of \(u\)**:

- For a variable \(u=x\), leave \(\nu_{\delta x}\) unchanged; the comparison is a unitor.
- For a coherence, apply the induction hypothesis only to its original substitution-image terms \(u_i\).
- A manufactured expression resulting from head reduction or path folding is handled by its generic comparison, not by a recursive call.

In particular, \(u_i[\delta]\) may have the entire event set. This is harmless: \(u_i\) is a smaller generic derivation, and its normalizer is attached to an actual input derivation of \(u[\delta]\).

Here is the central comparison in this induction. Put
\[
\eta_j=\nu_{\delta(\alpha_j)},\qquad
\delta^+(\alpha_j)=N(\delta(\alpha_j)),
\]
leaving the 0- and 1-assignments unchanged. After applying the input induction hypotheses, the remaining expression has the form
\[
C^3(f_i)\ast_2\Phi_{\mathrm{head}}.
\]
Let \(a_0\) be the generic expression assembled from the \(K(u_i)\), and let
\[
\chi:a_0\to K(u)
\]
be the specified generic vertical reassociation and path-gap flattening. Then the comparison is
\[
\begin{aligned}
C^3(f_i)\ast_2\Phi_{\mathrm{head}}
&\;\Longrightarrow_4\;
A_{a_0}(\eta)
 \ast_2 C^3(\Phi_i)
 \ast_2\Phi_{\mathrm{head}}\\
&\;\Longrightarrow_4\;
A_{a_0}(\eta)
 \ast_2\chi[\delta^+]
 \ast_2\Phi_u\\
&\;\Longrightarrow_4\;
\chi[\delta]
 \ast_2A_{K(u)}(\eta)
 \ast_2\Phi_u.
\end{aligned}
\tag{9}
\]

The first arrow is the generic comparison for composing actions on the inputs. The second is §6’s flattening comparison. The third is the reverse of \(\Omega_\chi\) on \(V_m^\uparrow\).

The remaining generic 3-term \(b_{\mathrm{eval}}:u\to K(u)\) is compared with \(b_u\) by
\[
[b_{\mathrm{eval}},b_u]_{V_m}.
\]
Substituting \(\delta\) completes (8).

The formal input variables have therefore stayed formal until the input normalizers have been moved through the generic operations. Only their selected normal-form targets were expanded.

## 8. Arbitrary 3-heads

After constructing \(\nu\) and (8), induct on the 3-term derivation to construct
\[
I_H:\nu_T\longrightarrow H\ast_2\nu_{T'}
\qquad(H:T\to T').
\tag{10}
\]

For a reduced coherence head \(h:u\to v\), retain its actual reduced 3-arity \(P\). Let \(D\) be the boundary-corrected composite of its formal 3-variables, with identities on the remaining maximal 2-declarations. The generic comparison is
\[
\boxed{
\Xi_P=
[b_u\ast_2D,\;h\ast_2b_v]_P.
}
\tag{11}
\]
Its two boundaries are literally parallel and have full support \(P\).

After substitution, use the induction hypothesis on the proper 3-inputs. Since the grid has no 3-generators, their two 2-boundaries have the same strict image. Their selected normal forms are therefore literally the same terms. This gives
\[
f_u\Longrightarrow_4D[\delta]\ast_2f_v.
\]
Together with (8) at both ends and (11), it gives
\[
\begin{aligned}
\nu_{u[\delta]}
&\Longrightarrow_4 b_u[\delta]\ast_2f_u\\
&\Longrightarrow_4
(b_u[\delta]\ast_2D[\delta])\ast_2f_v\\
&\Longrightarrow_4
h[\delta]\ast_2(b_v[\delta]\ast_2f_v)\\
&\Longrightarrow_4
h[\delta]\ast_2\nu_{v[\delta]}.
\end{aligned}
\]
Item 14’s 4-dimensional head comparison transfers this to the original head.

This is the step covering arbitrary 3-terms. They have not been assumed to be composites of exchanges.

Finally, for parallel \(\alpha,\beta:T\to T'\), put \(\nu=\nu_{T'}\), choose its inverse \(\bar\nu\), and let
\[
c_\alpha:(\alpha\ast_2\nu)\ast_2\bar\nu\to\alpha
\]
be the constructed cancellation 4-term; define \(c_\beta\) similarly. A required filler is
\[
\boxed{
c_\alpha^\dagger
\ast_3
\Bigl(
(I_\alpha^\dagger\ast_3I_\beta)
\ast_2 1_{\bar\nu}
\Bigr)
\ast_3 c_\beta.
}
\tag{12}
\]

The event-count induction follows the table in §1: first the three-event cases, then the new four-event fibres, then the five-event fibres, and finally \(abcdef\). Therefore
\[
\boxed{\mathrm{RC}(3)(\Gamma_{2,3}).}
\]

By item 30, the same holds after adjoining any finite family of 3-generators to this grid.

# II. A conditional 4-dimensional extension theorem

The following is the dimension-four analogue of item 30 with an explicit lower-coherence hypothesis.

> **Theorem.** Let \(\dim\Lambda\le3\), let its generating 1-graph be acyclic, and assume \(\mathrm{RC}(3)(\Lambda)\). For any well-typed extension by 4-generators
> \[
> \Gamma=(\Lambda,z_i:A_i\to B_i)_{i\in I},
> \]
> one has
> \[
> \boxed{
> \mathrm{RC}(4)(\Gamma)
> \iff
> \mathrm{RC}(4)(\Lambda).
> }
> \]
> There are no restrictions on the whiskering, composability or order of the \(z_i\).

## 1. Fresh formal 3-variables are controlled

Put \(\Delta=\Lambda_{\le2}\).

Exact support shows that RC(3) for \(\Lambda\) implies RC(3) for \(\Delta\). Indeed, a 4-term between 3-terms of \(\Delta\) has strict image an identity on a 3-cell supported in \(\Delta\), so it cannot use a 3-generator of \(\Lambda\).

Every 3-generator of \(\Lambda\), and every fresh formal 3-variable \(X\), has its declaration type over \(\Delta\). Item 30 therefore gives
\[
\boxed{\mathrm{RC}(3)(\Lambda,X).}
\tag{13}
\]
The same applies to finitely many fresh 3-variables.

This formal-variable conclusion is needed below; RC(3) for \(\Lambda\) alone is not applied directly to a term depending on \(X\).

## 2. Normalize in a quotient category

Fix literal parallel 2-terms \(S,T\). Form the category whose:

- objects are 3-terms \(A:S\to T\);
- arrows are 4-terms, modulo existence of a 5-term;
- composition is induced by \(\ast_3\).

Every 5-term in \(\Gamma\) is invertible, and every 4-term over \(\Lambda\) is invertible, by the empty-top-support criterion. The generic 5-dimensional associators and unitors make this quotient a category.

For each strict 3-cell \(q:\pi S\to\pi T\), choose a lift
\[
\widehat q:S\to T.
\]
Such lifts are obtained by evaluating a strict composite and aligning its literal boundaries: path 2-cells align its 1-boundaries, and RC(2) supplies 3-cells aligning its 2-boundaries.

By RC(3), choose
\[
r_A:A\to\widehat{\pi A}.
\]
For \(U:A\to B\), define its normalized arrow
\[
\mathcal N(U)
=
[\,r_A^\dagger\ast_3U\ast_3r_B\,].
\tag{14}
\]

Assume RC(4) for \(\Lambda\). If \(U\) is a 4-term over \(\Lambda\), its strict image is an identity. Hence
\[
\boxed{\mathcal N(U)=1.}
\tag{15}
\]
The inverse data for \(r_B\) also gives
\[
\mathcal N(U\ast_3V)=\mathcal N(U)\mathcal N(V).
\]

## 3. The exact context-replacement 5-term

Suppose
\[
\Lambda,X\vdash F(X),G(X):S\to T,
\qquad
\pi F(X)=\pi G(X)
\]
with \(X\) retained as a formal 3-generator.

By (13), choose
\[
J(X):F(X)\to G(X).
\]
Here \(\dim J=4\), and \(X\) has depth one in \(J\).

For a 4-term \(U:A\to B\), depth-zero naturality defines \(F(U),G(U)\). Depth-one naturality of \(J\) then gives
\[
\boxed{
N_J(U):
J(A)\ast_3G(U)
\longrightarrow
F(U)\ast_3J(B).
}
\tag{16}
\]
Both boundaries are literally 4-terms \(F(A)\to G(B)\).

This is an application of Theorem 3.1 of Benjamin–Markakis–Offord–Sarti–Vicary with an upward-closed singleton consisting of a 3-variable. Their substitution lemma also supplies compatibility of the context action with substitution. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

Both \(J(A)\) and \(J(B)\) are over \(\Lambda\). Applying (15) to (16) gives
\[
\boxed{\mathcal N(F(U))=\mathcal N(G(U)).}
\tag{17}
\]
Thus normalized evaluation is independent of the chosen weak lift of a strict 3-context.

Only depth-one naturality is used here.

## 4. Adjacent exchange has a generic 5-cell

Let
\[
U:A\to B,\qquad V:C\to D
\]
be \(k\)-composable 4-terms, \(0\le k<3\). On the generic pasting context
\[
P_{4,k}=D^4\vee_kD^4
\]
form
\[
\begin{aligned}
L&=(U\ast_k1_C)\ast_3(1_B\ast_kV),\\
R&=(1_A\ast_kV)\ast_3(U\ast_k1_D).
\end{aligned}
\]
Both are full-support 4-terms
\[
A\ast_kC\longrightarrow B\ast_kD.
\]
Consequently
\[
\boxed{[L,R]_{P_{4,k}}}
\tag{18}
\]
is the required 5-term.

The same full-support rule compares \(U\ast_kV\) with either sequential expression. Thus (18) supplies both exchange and sequentialization. Further contexts act on these 5-terms by iterated depth-zero naturality.

## 5. Arbitrary 4-heads can be expanded before substitution

Let
\[
H=\operatorname{coh}_{P,u\to v}[\mathrm{id}],
\qquad \dim P=4.
\]

Choose the fixed binary composite \(B_P\) of the 4-discs of the globular tree of \(P\), inserting identities on its lower-dimensional maximal declarations.

Its boundaries need not initially equal those of \(H\) syntactically. Correct them in this order:

1. **Align 1-boundaries.** Use 2-coherences on the relevant 1-boundary pasting contexts, and whisker \(B_P\) by their depth-zero actions.
2. **Align 2-boundaries.** Use 3-coherences on the relevant 2-boundary pasting contexts, again applying their depth-zero actions.
3. **Align 3-boundaries.** The resulting source \(a\) is now literally parallel to \(u\), and its target \(b\) to \(v\). Choose
   \[
   \ell:u\to a,\qquad r:b\to v
   \]
   by full-support coherences on \(\partial^-_3P,\partial^+_3P\).

The corrected term
\[
K_P=\ell\ast_3 B'_P\ast_3r
\]
has literally the same type as \(H\), and both terms have full support \(P\). Hence
\[
\boxed{
E_P=[H,K_P]_P:H\to K_P
}
\tag{19}
\]
is a 5-term.

After a substitution into \(\Gamma\), every padding term in this construction is a 4-term over \(\Lambda\): its defining arity has dimension at most three. Equation (15) removes these padding terms in normalized evaluation.

Apply (18) repeatedly to sequentialize the remaining binary composite. Induction on the original substituted 4-inputs reduces it to a sequence of contextual applications of the \(z_i\).

If \(\dim P\le3\), the entire 4-head already belongs to \(\Lambda\), so (15) applies directly.

This proves head expansion without assuming RC(4) in a context with fresh 4-generators.

## 6. Evaluation respects the strict presentation

For a strict elementary 4-cell \(C[z_i]\), choose a weak formal 3-context \(F(X)\) lifting \(C\), with its literal boundaries aligned, and define
\[
\mathcal E(C[z_i])=\mathcal N(F(z_i)).
\tag{20}
\]

Equation (17) makes this independent of the lift.

The strict presentation required here is the one in *Polygraphs*, Appendix D: expressions sequentialize into elementary steps; equality of elementary steps reduces to equality of their labels and lower-dimensional contexts; equality of sequential expressions is generated by replacement and adjacent exchange. These are Propositions D.3.6, D.3.9 and D.3.12. [arxiv.org](https://arxiv.org/pdf/2312.00429?utm_source=chatgpt.com)

Replacement is respected by (17), and adjacent exchange by (18). Therefore (20) extends to a well-defined evaluation of strict 4-cells.

Induction on term syntax, using (19), proves
\[
\mathcal N(U)=\mathcal E(\pi U).
\]
Thus, if \(U,V:A\to B\) satisfy \(\pi U=\pi V\), then
\[
\mathcal N(U)=\mathcal N(V).
\]
Undoing the \(r_A,r_B\) normalization yields a 5-term \(U\to V\).

Every equality used in this quotient proof has a specified 5-term witness: (16), (18), (19), an RC(4) comparison in \(\Lambda\), or a composition/whiskering of those terms. Consequently the proof supplies a CaTT filler, rather than only a semantic equality.

For the converse, a 5-term in \(\Gamma\) between 4-terms over \(\Lambda\) has no 4-generator in its strict support. Exact support strengthens it to \(\Lambda\).

This proves the theorem.

For example,
\[
\mathrm{RC}(4)\bigl(D^3+\text{arbitrary 4-generators}\bigr)
\]
follows. RC(3) and RC(4) for \(D^3\) follow directly from support: the support of a term with a fixed strict image is one of its subglobes, and parallel terms lift to full-support terms on that subglobe.

## What the extension proof does not establish

The additional RC(3) assumption is used twice:

- to choose \(r_A:A\to\widehat{\pi A}\);
- to construct \(J(X)\) between equal strict formal 3-contexts.

Choosing representatives separately in existing 4-cell connected classes does not supply the second comparison. Therefore this argument neither proves the extension from RC(4) alone nor proves that the additional assumption is necessary.

It also does not supply the missing RC(4) fusion for the triangle or square. Moving 3-inputs of a 4-term is covered by depth-one naturality; moving its 2-inputs through the chosen 3-normalizers is the additional compatibility still required.
