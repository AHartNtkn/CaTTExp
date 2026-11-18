# Problem: composites of molecules in CaTT (Gray contexts), round 6

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Rounds 1–5 and their verified answers are archived in `answered/gray-contexts-2026-11-18.md`, `answered/gray-contexts-round2-2026-11-18.md`, `answered/gray-contexts-r3-2026-11-18.md`, `answered/gray-contexts-r4-2026-11-18.md` and `answered/gray-contexts-r5-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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
16. **The support lemma (proved, cone-over-coherences round 3).** In every CaTT context Γ, the generators used by the strict image of a term are exactly its dependency-closed support: `supp(π t) = supp(t)`. So a term whose strict image lies in a dependency-closed sub-context is literally a term of that sub-context.
17. **The Gray cube's X-free loops are contractible (round 5, proved on paper).** Every X-free 3-term H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉ is connected to the identity.
    - *Hemisphere.* Its paths 000 → 111 are 321, 231, 213 and 123, with rewrites E₁, E₂, E₃ in a line. So the strict 2-cells between them are the intervals of E₁E₂E₃.
    - *Proper intervals.* The pairs of adjacent faces are two-square cylinders (one with item 13's orientation, one 2-opposite). Single whiskered faces are literal retracts of them. So every proper interval satisfies RC(3).
    - *Normal forms.* N(T) = C(γ_r, E_{i+1}, …, E_j, γ̄_s), with fixed bracketing and path corrections γ. For a full-word T, the reduced head is one vertical chain V_m. Then ν_T is the generic comparison b : T̃ → K(T̃) over V_m (one coherence, both sides full), followed by the input normalisers and a gap flattening Φ.
    - *Relative evaluation fusion.* For a full 2-term u over a formal V_m and δ into the hemisphere, there is a 4-term ν_{u[δ]} → b_u[δ] ∗₂ f_{u,δ}. The 2-variables of V_m stay formal, and only the chosen normal forms N(δ(α_i)) are expanded. The tools are the coherences A_a = coh_{V_m↑, a[−] → a[+]} and Ω_χ : χ[−] ∗₂ A_b → A_a ∗₂ χ[+] over V_m↑ = D³ ∨₁ ⋯ ∨₁ D³, and one coherence over a formal gap context for path-only gaps.
    - *Compatibility.* For every 3-term H : u → v there is I_H : ν_u → H ∗₂ ν_v. It is built from one coherence Ξ_P over H's reduced 3-arity, plus relative fusion at both ends.
    - Source: `answered/gray-contexts-r5-2026-11-18.md`.
18. **Item 14 extends to some contexts with 3-variables (round 5, proved).** Let dim Γ ≤ 3 and suppose every 3-variable z has a 2-generator in the support of its 2-source. Then a 3-term whose 2-source has no 2-generator in its support has no 2- or 3-generator in its support. So item 14's inactive-column test, path lift, comparisons and stability hold unchanged in acyclic such Γ.
    - The cylinder of D² (squares F, G and Z : (A⁻ ∗₀ k) ∗₁ G → F ∗₁ (h ∗₀ A⁺)) satisfies the hypothesis, and so does the join c ⋆ D² (Z : β_g → β_f ∗₁ (p ∗₀ A)).
    - The hypothesis is needed. In (x, y, f, Z : 1_f → 1_f), a column assigning 1_f to both 2-variables and Z to the 3-variable is inactive by the old test but carries Z.
19. **An acyclic generating 1-graph is not enough (round 5).** The context (x, a : 1_x → 1_x) has no 1-generators, so its 1-graph is acyclic, and RC(3) fails there. Adjoining y and f : x → y gives a connected example that retracts onto it, so RC(3) fails there too. The obstruction is a 2-generator whose source and target are both identities.

## 3. What remains

Item 17 settles the cube's X-free loops. Its fusion argument relies on three features of the hemisphere: the events form a line (no exchange between two events), every full-word head reduces to a single vertical chain, and proper intervals live in two-square cylinders, which are already settled. In a general 2-dimensional context, two 2-generators can be exchanged, the strict 2-cells between two paths form a poset of exchange classes rather than a line, and an active column can sit beside other non-point columns. The cube itself still has 3-terms that use X.

## 4. Questions

1. **All of the Gray cube.** Prove RC(3) for U, the context of the Gray cube including its 3-variable X. Equivalently, show that any two parallel 3-terms of U with the same strict image are connected. In particular, any two U-composites ⌈∂⁻U⌉ → ⌈∂⁺U⌉ are connected (uniqueness in G(3) for the cube). The new step is a normal form for 3-terms that use X, with whiskers removed as in item 17.
2. **Fusion with exchange.** Extend item 17's normal forms and relative fusion to a 2-dimensional context where two 2-generators commute up to exchange. The smallest case is the 2 × 2 grid of lax squares, the Gray product of two paths of length 2. There the path h v h v admits two independent face rewrites. (A strip of squares, the cylinder of a path, has no such pair, since each path crosses it with a single vertical edge.) Normal forms could be Squier-style normal forms of exchange classes, with an exchange coherence as the comparison between two orderings.
3. **RC(3) in dimension 2, corrected hypothesis.** Prove RC(3) for every finite context of dimension ≤ 2 whose generating 1-graph is acyclic and in which no 2-generator has an identity as both source and target. Or give a counterexample. If the general statement is out of reach, prove it for finite Steiner loop-free 2-computads, which include the cylinders of 1-dimensional pasting contexts and the Gray products of two such contexts.
4. **Contexts with 3-variables.** Prove RC(3) for the cylinder of D² or for the join c ⋆ D², using item 18 for the inactive columns.
5. **RC(n) or G(n).** Prove RC(n) under the hypothesis of question 3 (suitably extended to higher generators), or the weaker G(n) for frame-acyclic molecules.

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

# Research Response

**Questions 1 and 4 have positive answers, using the results stated in the prompt.** The new step is a normalisation lemma for adjoining a single \(3\)-generator whose strict image admits no nontrivial whiskering or iteration.

I first give the lemma and its CaTT constructions. I then apply it to the cube, the cylinder of \(D^2\), and \(c\star D^2\). The general exchange-fusion problem in Questions 2 and 3 remains unresolved by this argument.

## 1. A one-generator extension lemma

Let \(\Lambda\) be a context of dimension at most \(2\), and put
\[
\Gamma=(\Lambda,z:A\to B).
\]
Assume:

1. The generating \(1\)-graph of \(\Lambda\) is acyclic.
2. \(\mathrm{RC}(3)\) holds in \(\Lambda\).
3. The only nonidentity \(3\)-cell of \(F(\Gamma)\) is the generating cell \(z\).

Then **\(\mathrm{RC}(3)\) holds in \(\Gamma\)**.

Condition 3 is strong. In particular, it excludes nontrivial strict whiskerings of \(z\), and excludes a strict composite using \(z\) twice. These are exactly the restrictions satisfied by the three contexts considered below.

### Notation and available operations

For parallel \(3\)-terms \(a,b\) with full support in a pasting context \(P\), write
\[
[a,b]_P
=
\operatorname{coh}_{P,a\to b}[\operatorname{id}_P].
\]
Thus \([a,b]_P\) denotes a specified \(4\)-term, not an assertion that a comparison exists.

Write
\[
C(f,a,g)=(f*_1a)*_1g,
\qquad
C^3(f,H,g)=(1_f*_1H)*_1 1_g.
\]
Here \(f,g\) are \(2\)-terms, \(H:a\to b\) is a \(3\)-term, and the identities in \(C^3\) are \(3\)-dimensional. Its boundary is
\[
C^3(f,H,g):C(f,a,g)\longrightarrow C(f,b,g).
\]

Products are left associated unless parentheses specify otherwise. Reassociations of \(3\)-products are implemented by \(4\)-coherences over strings of \(3\)-discs. No reassociation below is a definitional equality.

A \(3\)-term over \(\Lambda\) has a chosen inverse and \(4\)-dimensional cancellation witnesses. The same holds for every \(4\)-term over \(\Gamma\). These are instances of the constructive invertibility criterion: a cell with no generator of its own dimension in its support is invertible. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

### The selected normal form

Write the literal \(1\)-boundaries of \(A,B\) as
\[
A,B:p_0\longrightarrow q_0.
\]

For every \(1\)-term \(r\) with \(\pi r=\pi p_0\), choose a path-supported \(2\)-coherence
\[
\gamma_r:r\longrightarrow p_0.
\]
Similarly choose
\[
\bar\gamma_s:q_0\longrightarrow s
\qquad
(\pi s=\pi q_0).
\]
Take \(\gamma_{p_0}=1_{p_0}\) and \(\bar\gamma_{q_0}=1_{q_0}\).

Define
\[
\begin{aligned}
A_{rs}&=C(\gamma_r,A,\bar\gamma_s),\\
B_{rs}&=C(\gamma_r,B,\bar\gamma_s),\\
z_{rs}&=C^3(\gamma_r,z,\bar\gamma_s).
\end{aligned}
\]
These have literal boundaries
\[
A_{rs},B_{rs}:r\longrightarrow s,
\qquad
z_{rs}:A_{rs}\longrightarrow B_{rs}.
\]

Using \(\mathrm{RC}(2)\), choose, once for each relevant \(2\)-term,
\[
\nu_u:u\longrightarrow A_{rs}
\quad\text{if }\pi u=\pi A,
\]
and
\[
\nu_v:v\longrightarrow B_{rs}
\quad\text{if }\pi v=\pi B.
\]
Choose these in \(\Lambda\). For \(u=A\) and \(v=B\), take the ordinary unit-insertion coherences over their formal \(2\)-discs.

For a \(3\)-term \(H:u\to v\) with \(\pi H=z\), the selected normal form is
\[
\boxed{
N(u,v)=
(\nu_u*_2z_{rs})*_2\nu_v^\dagger.
}
\tag{1}
\]
It depends only on the literal boundary \(u,v\), not on \(H\).

The rest of the proof constructs
\[
R_H:H\longrightarrow N(u,v).
\tag{2}
\]

## 2. Expanding a \(3\)-dimensional coherence head

This step works over an arbitrary \(3\)-dimensional pasting context.

Let
\[
h_P=\operatorname{coh}_{P,u\to v}[\operatorname{id}_P],
\qquad \dim P=3.
\]

Construct a binary \(3\)-composite \(K_P^0\) by the ordered globular-sum decomposition of \(P\):

- compose the strings of \(3\)-variables by \(*_2\);
- combine the resulting \(1\)-columns by \(*_1\);
- combine the \(0\)-columns by \(*_0\);
- use iterated identities on maximal declarations of dimension below \(3\).

The last clause ensures
\[
\operatorname{supp}(K_P^0)=\operatorname{Var}(P).
\]
Every \(3\)-variable of \(P\) is used exactly once.

The raw \(K_P^0\) need not have the same literal \(1\)-boundaries as \(u,v\). Suppose its \(1\)-boundaries are \(p',q'\), whereas those of \(u,v\) are \(p,q\). Their respective strict paths agree. Choose \(2\)-coherences on the linear boundary pastings
\[
a:p\longrightarrow p',
\qquad
b:q'\longrightarrow q,
\]
and set
\[
K_P=C^3(a,K_P^0,b).
\]

Now the following are literal types:
\[
b_-:u\longrightarrow s_2K_P,
\qquad
b_+:t_2K_P\longrightarrow v.
\]
Define \(b_-\) by one coherence over \(\partial^-P\), and \(b_+\) by one coherence over \(\partial^+P\). Their respective endpoints have full support in those boundary pastings.

Consequently,
\[
\boxed{
\Omega_P=
\left[
h_P,\,
(b_-*_2K_P)*_2b_+
\right]_P
}
\tag{3}
\]
is a valid \(4\)-term. Both endpoints are parallel and have full \(P\)-support.

For
\[
H=\operatorname{coh}_{P,u\to v}[\sigma],
\]
substitute \(\sigma\) into (3).

The added \(3\)-terms \(b_-[\sigma]\) and \(b_+[\sigma]\) use only images of variables of dimension at most \(2\); they are therefore \(z\)-free.

### Why this expansion terminates along one branch

A \(3\)-head using \(z\) must have a \(3\)-dimensional arity: an arity of dimension at most \(2\) has no substitution entry that can use \(z\).

Use the additive count of \(z\) in the free strict \(3\)-category:
\[
\#_z(\xi*_k\eta)=\#_z(\xi)+\#_z(\eta),
\qquad
\#_z(1)=0,
\qquad
\#_z(z)=1.
\]
This count is preserved by strict interchange.

Since \(\pi H=z\), and \(K_P^0\) uses each formal \(3\)-variable once, exactly one substituted \(3\)-variable has an image using \(z\). Recursively expand that original substitution subterm. Its syntactic size decreases.

The result is a binary \(3\)-expression with:

- exactly one leaf labelled \(z\);
- all other \(3\)-leaves \(z\)-free;
- explicit \(4\)-terms comparing it with \(H\).

This argument uses the additive count, not merely support equality.

## 3. The universal comparisons needed for whiskers

For \(k=0,1\), there is a direct \(4\)-coherence over \(D^3\vee_kD^3\):
\[
H*_kK
\longrightarrow
(H*_k1_{s_2K})*_2(1_{t_2H}*_kK).
\tag{4}
\]
Its two endpoints have the same literal \(2\)-boundary and use both formal \(3\)-variables.

Distribution of a vertical string through such a composition is obtained in the same way. For example, the relevant arity for a three-factor string is
\[
(D^3\vee_2D^3\vee_2D^3)\vee_kD^3.
\tag{5}
\]

These comparisons separate the factor using \(z\) from \(z\)-free \(3\)-factors. Condition 3 of the lemma then has two consequences:

- every \(2\)-term used to \(*_1\)-whisker the factor using \(z\) has a strict identity image;
- every \(3\)-term composed beside it by \(*_0\) has a strict image supported at a single vertex.

By support agreement, the first kind is path-supported and the second factors literally through a point context.

The following two constructions remove them.

### 3.1 Point-supported factors

Work over the formal \(3\)-disc
\[
D^3=(x,y,f,g,a,b,z),
\qquad
a,b:f\to g,\quad z:a\to b.
\]

Let \(\beta'(y)\) be a fixed \(3\)-term over the point \(y\), with
\[
\beta':c\longrightarrow d,
\qquad
c,d:r\longrightarrow s,
\qquad
r,s:y\longrightarrow y.
\]

The term \(z*_0\beta'(y)\) has \(1\)-boundaries
\[
f*_0r,\qquad g*_0s.
\]
Over the corresponding formal \(1\)-discs, define
\[
\kappa_f:f*_0r\longrightarrow f,
\qquad
\bar\kappa_g:g\longrightarrow g*_0s
\]
by \(2\)-coherences.

Over \(D^2(a)\), the terms
\[
a*_0c,\qquad C(\kappa_f,a,\bar\kappa_g)
\]
are literally parallel and both have full support. Thus define
\[
\ell:
a*_0c\longrightarrow C(\kappa_f,a,\bar\kappa_g)
\]
by one \(3\)-coherence over \(D^2(a)\).

Likewise define, over \(D^2(b)\),
\[
r_b:
b*_0d\longrightarrow C(\kappa_f,b,\bar\kappa_g).
\]

Now
\[
\boxed{
\left[
z*_0\beta'(y),\,
\bigl(\ell*_2C^3(\kappa_f,z,\bar\kappa_g)\bigr)*_2r_b^\dagger
\right]_{D^3}
}
\tag{6}
\]
is a valid \(4\)-term.

Its endpoints are literally parallel, and both have full \(D^3\)-support. Substituting an actual \(3\)-term for the formal \(z\) replaces its point-supported factor by:

- two path-supported \(2\)-whiskers;
- two \(z\)-free \(3\)-terms.

For a point-supported factor on the left, use \(\beta'(x)*_0z\), with
\[
\kappa_f:r*_0f\to f,
\qquad
\bar\kappa_g:g\to s*_0g,
\]
and the same displayed construction.

### 3.2 Path-supported \(2\)-whiskers

Consider a right whisker
\[
w:s\longrightarrow t,
\qquad
\pi w=1_{\pi q_0}.
\]
Its support consists of vertices and edges of that path.

The two \(2\)-terms
\[
\bar\gamma_s*_1w,\qquad \bar\gamma_t
\]
are literally parallel and path-supported. Item 4 therefore supplies an explicit path-context coherence
\[
d:(\bar\gamma_s*_1w)\longrightarrow\bar\gamma_t.
\tag{7}
\]

Let \(\mathsf a_3\) denote the ordinary \(3\)-associator for \(*_1\)-composition of \(2\)-terms. Define
\[
\begin{aligned}
\rho_A={}&
\mathsf a_3(\gamma_r*_1A,\bar\gamma_s,w)
*_2
(1_{\gamma_r*_1A}*_1d),\\
\rho_B={}&
\mathsf a_3(\gamma_r*_1B,\bar\gamma_s,w)
*_2
(1_{\gamma_r*_1B}*_1d).
\end{aligned}
\tag{8}
\]
Their types are
\[
\rho_A:A_{rs}*_1w\longrightarrow A_{rt},
\qquad
\rho_B:B_{rs}*_1w\longrightarrow B_{rt}.
\]

There is a \(4\)-term
\[
\boxed{
(z_{rs}*_11_w)*_2\rho_B
\longrightarrow
\rho_A*_2z_{rt}.
}
\tag{9}
\]

Here is its construction, including the arities.

**First, reassociate around the formal \(3\)-variable.** Use a direct \(4\)-coherence over
\[
D^2\vee_1D^3\vee_1D^2\vee_1D^2,
\tag{10}
\]
substituting respectively \(\gamma_r,z,\bar\gamma_s,w\). It compares
\[
(z_{rs}*_11_w)
*_2
\mathsf a_3(\gamma_r*_1B,\bar\gamma_s,w)
\]
with
\[
\mathsf a_3(\gamma_r*_1A,\bar\gamma_s,w)
*_2
\bigl((1_{\gamma_r}*_1z)*_11_{\bar\gamma_s*_1w}\bigr).
\]

**Second, interchange with \(d\).** Over the formal pasting
\[
P_I=D^2(f)\vee_1D^3(z)\vee_1D^3(e),
\]
write
\[
z:a\to b,\qquad e:c\to c'.
\]
Take the direct \(4\)-coherence between
\[
\bigl((1_f*_1z)*_11_c\bigr)
*_2
(1_{f*_1b}*_1e)
\]
and
\[
(1_{f*_1a}*_1e)
*_2
\bigl((1_f*_1z)*_11_{c'}\bigr).
\tag{11}
\]
Substitute
\[
f\mapsto\gamma_r,\qquad
z\mapsto z,\qquad
c\mapsto\bar\gamma_s*_1w,\qquad
c'\mapsto\bar\gamma_t,\qquad
e\mapsto d.
\]

In particular, \(c\) is a **formal \(2\)-variable** in \(P_I\). Its assigned value is the composite \(\bar\gamma_s*_1w\). We do not declare a \(3\)-generator with that composite source in the purported pasting context.

Composing these two comparisons, with vertical associativity comparisons, gives (9). Appending \(\rho_B^\dagger\) and using its cancellation witness gives
\[
\boxed{
z_{rs}*_11_w
\longrightarrow
(\rho_A*_2z_{rt})*_2\rho_B^\dagger.
}
\tag{12}
\]

For completeness, left padding has the same construction. If
\[
w:t\to r,\qquad
d:(w*_1\gamma_r)\to\gamma_t,
\]
put
\[
\begin{aligned}
\rho_A^\ell={}&
\mathsf a_3(w,\gamma_r*_1A,\bar\gamma_s)^\dagger\\
&*_2
\bigl(\mathsf a_3(w,\gamma_r,A)^\dagger*_11_{\bar\gamma_s}\bigr)\\
&*_2
\bigl((d*_11_A)*_11_{\bar\gamma_s}\bigr),
\end{aligned}
\tag{13}
\]
and define \(\rho_B^\ell\) similarly. The associativity comparisons live over
\[
D^2(w)\vee_1D^2(\gamma_r)\vee_1D^3(z)\vee_1D^2(\bar\gamma_s),
\]
and the interchange comparison over
\[
D^3(d)\vee_1D^3(z)\vee_1D^2(\bar\gamma_s).
\]
They give
\[
(1_w*_1z_{rs})*_2\rho_B^\ell
\longrightarrow
\rho_A^\ell*_2z_{ts},
\]
and hence the left version of (12).

Thus both kinds of whisker are removed by explicit \(4\)-coherences over globular pastings.

## 4. Completing the normalisation

Apply the head expansion of §2. Normalise the resulting binary expression by induction on its syntax, following the unique leaf labelled \(z\).

- At a \(*_2\)-node, the other factor is \(z\)-free and is added to the preceding or following \(3\)-product.
- At a \(*_1\)-node, use (4) and (5) to separate the \(z\)-free \(3\)-factor. Then use (12) or its left version to remove the remaining path-supported \(2\)-whisker.
- At a \(*_0\)-node, the other factor is point-supported. Apply (6), then the already established path-whisker constructions.
- At the leaf \(z\), the comparison with its framed version is a direct \(4\)-coherence over \(D^3\), using the selected unit-insertion choices of \(\nu_A,\nu_B\).

This yields a \(4\)-term
\[
H\longrightarrow (L*_2z_{rs})*_2R,
\tag{14}
\]
where
\[
L:u\longrightarrow A_{rs},
\qquad
R:B_{rs}\longrightarrow v,
\]
and \(L,R\) are \(z\)-free.

The recursion is finite. Head expansion recurses only into original substitution subterms. Whisker removal operates on the resulting finite binary expression; its newly constructed coherence terms are not recursively expanded.

Now use \(\mathrm{RC}(3)\) in \(\Lambda\):
\[
L\longrightarrow\nu_u,
\qquad
R\longrightarrow\nu_v^\dagger.
\tag{15}
\]
These pairs are literally parallel. Their strict images agree because \(\Lambda\) has no \(3\)-generators.

Whiskering (15) into (14) constructs the required
\[
R_H:H\longrightarrow N(u,v).
\]

For parallel \(H,H'\) with strict image \(z\), the target normal forms are syntactically identical. Therefore
\[
\boxed{
R_H*_3R_{H'}^\dagger:H\longrightarrow H'
}
\tag{16}
\]
is the requested \(4\)-term.

Finally, suppose their common strict image is an identity \(3\)-cell. Item 16 implies that neither term uses \(z\), so both are literally terms of \(\Lambda\). Apply \(\mathrm{RC}(3)\) there.

This proves the extension lemma.

## 5. Application to the entire Gray cube

Let \(\Lambda=U_{\leq2}\), and let
\[
U=(\Lambda,X:A\to B).
\]

### The \(X\)-free cases

For the full \(0\)-boundary \(000\to111\), the strict path-rewrite graph consists of the two chains
\[
321\longrightarrow231\longrightarrow213\longrightarrow123
\]
and
\[
321\longrightarrow312\longrightarrow132\longrightarrow123.
\tag{17}
\]

A strict \(2\)-cell is a directed subpath of one of these chains. The two length-three paths are distinct strict \(2\)-cells, namely \(\pi A\) and \(\pi B\).

The first chain is covered by item 17. The second satisfies the same hypotheses of that construction:

- its three events have a forced order;
- its proper intervals are the corresponding two-square cylinders and single whiskered faces;
- a full-word head reduces to one vertical column.

Thus the same construction gives \(\mathrm{RC}(3)\) on the second hemisphere.

For smaller \(0\)-boundaries, the relevant strict \(2\)-cells are identities or faces, with possible edge whiskers. They are among the proper-interval cases. By support agreement, any \(3\)-term with a specified strict \(2\)-boundary strengthens to the corresponding subcontext.

Consequently,
\[
\mathrm{RC}(3)\text{ holds in }\Lambda.
\tag{18}
\]

### The strict \(3\)-cells

The cell \(X\) has \(0\)-boundary \(000\to111\). There is no nonempty path into \(000\), or out of \(111\), so it has no nontrivial strict \(0\)-whiskering.

Its \(1\)-source path is \(321\), the initial vertex of the rewrite graph (17), and its \(1\)-target path is \(123\), the terminal vertex. Hence it has no nontrivial strict \(1\)-whiskering.

Finally, \(\pi A\neq\pi B\), so \(X\) cannot be vertically composed with itself. There are no other \(3\)-generators.

Therefore the only nonidentity strict \(3\)-cell is \(X\). All hypotheses of the extension lemma hold.

\[
\boxed{\mathrm{RC}(3)\text{ holds for the whole Gray-cube context }U.}
\]

In particular, if \(H:A\to B\) is any \(U\)-composite, its strict image is \(X\). Applying the construction to \(H\) and to \(X\) gives the explicit term
\[
\boxed{
R_H*_3R_X^\dagger:H\longrightarrow X.
}
\tag{19}
\]
This proves uniqueness in \(G(3)\) for the cube.

## 6. Application to the cylinder and join on \(D^2\)

The extension lemma also settles Question 4. The additional work is to verify \(\mathrm{RC}(3)\) in their \(2\)-skeleta.

### A consequence of the line-word argument in item 17

The construction in item 17 applies to an event word of any finite length, provided its three geometric requirements hold.

A useful sufficient criterion is the following. Fix a strict \(2\)-cell
\[
w=E_1\cdots E_r
\]
in a \(2\)-dimensional context with acyclic generating \(1\)-graph. Suppose:

1. \(w\) has a unique ordered word of whiskered generating \(2\)-cells.
2. Every proper contiguous subword, including empty subwords, satisfies \(\mathrm{RC}(3)\).
3. At least one event uses a generating \(2\)-cell whose own \(0\)-source and \(0\)-target are the external endpoints of \(w\).

Then the fiber of \(w\) satisfies \(\mathrm{RC}(3)\).

Here is why the existing construction applies. In any head evaluating to \(w\), the generator in condition 3 is assigned through a \(0\)-column whose image spans both external endpoints. Acyclicity forces all preceding and following \(0\)-columns to be point-supported. Item 14 therefore leaves one vertical column.

The images of its successive \(2\)-variables are contiguous subwords of the unique event word. Proper subwords use condition 2; a full-word input is handled by induction on the original term syntax. The relative-fusion construction uses precisely the same \(A_a\), \(\Omega_\chi\), and path-gap comparisons as item 17. None depends on the event list having length three. Its generic \(\Xi_P\) comparison then gives compatibility with arbitrary \(3\)-heads.

The case \(r=1\) is included. It proves the one-face polygon case from the path cases.

For a full strict composite of a globular pasting context, the required proper-subword case is even simpler: both parallel \(3\)-terms have full support, so their comparison is one coherence over that pasting context.

### 6.1 Cylinder of \(D^2\)

Use the notation from item 18:
\[
Z:(A^-*_0k)*_1G
\longrightarrow
F*_1(h*_0A^+).
\]

Its four full-boundary \(1\)-paths are
\[
p_0=f^-k,\qquad
p_1=g^-k,\qquad
p_2=hf^+,\qquad
p_3=hg^+.
\]
The elementary rewrites are
\[
p_0\xrightarrow{\,a=A^-*_0k\,}p_1
\xrightarrow{\,b=G\,}p_3,
\]
and
\[
p_0\xrightarrow{\,c=F\,}p_2
\xrightarrow{\,d=h*_0A^+\,}p_3.
\tag{20}
\]

Thus the nonempty strict event words are exactly
\[
a,\ b,\ c,\ d,\ ab,\ cd.
\]
In particular, \(ab\) and \(cd\) are distinct strict \(2\)-cells.

Their fibers are covered as follows.

| Strict word | Construction of its \(\mathrm{RC}(3)\) comparisons |
|---|---|
| Empty | Path-context coherence |
| \(a\) | Pasting context \(D^2\vee_0D^1\) |
| \(d\) | Pasting context \(D^1\vee_0D^2\) |
| \(b,c\) | Lax-square result |
| \(ab\) | Line-word criterion, using the full-span generator \(G\) |
| \(cd\) | Line-word criterion, using the full-span generator \(F\) |

The other \(0\)-boundaries contribute only path cases and the unwhiskered globes \(A^\pm\). Support agreement justifies restriction to the indicated subcontexts. Hence the entire \(2\)-skeleton satisfies \(\mathrm{RC}(3)\).

The source \(p_0\) and target \(p_3\) of (20) are respectively initial and terminal in this rewrite graph. The external vertices are also source and sink in the generating \(1\)-graph. Therefore \(Z\) has no nontrivial strict whiskerings. Its two strict \(2\)-boundaries are distinct, so it cannot be iterated.

The extension lemma gives
\[
\boxed{\mathrm{RC}(3)\text{ for the cylinder of }D^2.}
\tag{21}
\]

### 6.2 The join \(c\star D^2\)

Write its \(2\)-generators as
\[
A:f\to g,\qquad
\beta_f:q\to p*_0f,\qquad
\beta_g:q\to p*_0g,
\]
and its \(3\)-generator as
\[
Z:\beta_g\longrightarrow\beta_f*_1(p*_0A).
\]

The full-boundary rewrite graph is
\[
q\xrightarrow{\beta_f}pf\xrightarrow{p*_0A}pg,
\qquad
q\xrightarrow{\beta_g}pg.
\tag{22}
\]

The relevant nonempty event words are
\[
\beta_f,\qquad p*_0A,\qquad
\beta_g,\qquad \beta_f;(p*_0A).
\]

- The word \(p*_0A\) is covered by the pasting context \(D^1\vee_0D^2\).
- Each singleton \(\beta_f,\beta_g\) satisfies the one-face polygon case of the criterion.
- The two-event word satisfies the criterion because \(\beta_f\) spans its external \(0\)-boundary.

Together with the path cases and the globe \(A\), these prove \(\mathrm{RC}(3)\) for the \(2\)-skeleton.

Again, the external vertices are source and sink, \(q\) is initial in (22), and \(pg\) is terminal. The two strict \(2\)-boundaries of \(Z\) are distinct. Thus \(Z\) is the only nonidentity strict \(3\)-cell.

Applying the same explicit normalisation gives
\[
\boxed{\mathrm{RC}(3)\text{ for }c\star D^2.}
\tag{23}
\]

## 7. What remains for exchange and the corrected general hypothesis

The proof above leaves \(z\)-free \(3\)-terms to an already established \(\mathrm{RC}(3)\) theorem for the \(2\)-skeleton. It therefore does not establish that theorem for the \(2\times2\) grid or for arbitrary contexts in Question 3.

The elementary exchange does have the required local fourth-dimensional compatibility. Over
\[
P=D^2(a)\vee_0D^2(b),
\]
put
\[
\begin{aligned}
L&=(a*_0g_0)*_1(f_1*_0b),\\
R&=(f_0*_0b)*_1(a*_0g_1),\\
\chi&=\operatorname{coh}_{P,L\to R}[\operatorname{id}].
\end{aligned}
\]
Replacing the two formal \(2\)-variables by formal \(3\)-discs gives
\[
P^\uparrow=D^3\vee_0D^3.
\]
Define the composition terms
\[
A_L:L^-\to L^+,\qquad A_R:R^-\to R^+.
\]
Then
\[
\boxed{
\operatorname{coh}_{P^\uparrow,\,
(\chi^-*_2A_R)\to(A_L*_2\chi^+)}
[\operatorname{id}]
}
\tag{24}
\]
is a valid \(4\)-term, and may be substituted with arbitrary input normalisers. Backtrack cancellation for \(\chi\) and its reverse is likewise one \(4\)-coherence over \(P\).

What is still needed for Question 2 is a comparison taking **every arbitrary grid \(3\)-head** to the chosen combination of these exchanges and structural comparisons. Formula (24) alone does not provide that comparison.

There is also a relevant published semistrict result. Under Question 3’s hypothesis, both strict boundaries of every \(2\)-generator are nonempty: in an acyclic generating graph, an identity boundary would force both boundaries to be identities. Forest–Mimram prove termination of interchanger rewriting for positive Gray presentations, show that two interchangers produce no remaining critical branching, and derive coherence from termination and critical confluence. Applied to the presentation with only structural interchangers, these results establish the corresponding free Gray-category statement. They do not supply the missing relative normalisation of arbitrary CaTT \(3\)-heads. [arxiv.org](https://arxiv.org/pdf/2109.05369?utm_source=chatgpt.com)

Thus the constructions above settle **all of the Gray cube**, **the cylinder of \(D^2\)**, and **the join \(c\star D^2\)**. General exchange fusion, the full statement of Question 3, and the higher-dimensional assertions in Question 5 are not proved here.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level.**
- **Settled:** Question 1 (RC(3) for the whole Gray cube U, hence uniqueness in G(3) for the cube, with the explicit term (19)) and Question 4 (RC(3) for the cylinder of D² and for c ⋆ D²).
- **New, general tool:** the one-generator extension lemma (§1–4). If Λ has dimension ≤ 2, an acyclic generating 1-graph and RC(3), and Γ = (Λ, z : A → B) has z as its only nonidentity strict 3-cell, then RC(3) holds in Γ. Its proof needs no fusion: the z-free parts are compared by RC(3) in Λ.
- **New sufficient criterion (sketch, §6):** the "line-word criterion" for RC(3) on the fibre of a strict 2-cell with a unique event word, a full-span event and RC(3) on proper subwords. It reuses round 5's construction for words of any length; I checked its hypotheses on the cases used, not a separate full proof.
- **Open:** Questions 2, 3 and 5. One local ingredient for Question 2 is given: the 4-term (24) relating the exchange coherence to 3-cells substituted into its two 2-variables.

Checked step by step:

1. **Normal form (1).** ν_u : u → A_rs exists by RC(2) (u and A_rs are parallel 2-terms with the same strict image), and lies in Λ because 2-terms cannot use z. N(u, v) depends only on the literal boundary.
2. **Head expansion (§2).** A 3-term whose arity P has dimension 3 is in the composition case (in the coherence case its 2-boundaries would have to use the 3-variables of P, which 2-terms cannot). So u has support Var(∂⁻P) and v has support Var(∂⁺P), and b_∓ are legal coherences over ∂^∓P. Both sides of Ω_P are 3-terms with full support in P, so (3) is a legal 4-coherence. The z-count is additive and preserved by the strict axioms; since π H = z and K_P⁰ uses each 3-variable once, exactly one substituted 3-argument has z-count 1, and by the support lemma the others are z-free. Arities of dimension ≤ 2 cannot reach z. Recursion is on proper subterms.
3. **Whisker separation (§3).** (4) is a coherence over D³ ∨_k D³ with both sides full. Since z is the only nonidentity strict 3-cell, z ∗₁ π(w) = z forces π(w) to be an identity (the 2-source A ∗₁ π w must equal A), and a ∗₀ partner must be point-supported. The support lemma then makes these path-supported or point-factoring.
4. **Point factors (6).** z ∗₀ β′(y) has 1-boundaries f ∗₀ r and g ∗₀ s; ℓ and r_b are 3-coherences over D²(a), D²(b) with full, parallel endpoints; both endpoints of (6) are full in D³ (β′ uses only y). Legal.
5. **Path whiskers (9)–(13).** d exists by item 4 of the prompt. The reassociation is a coherence over D² ∨₁ D³ ∨₁ D² ∨₁ D² and the interchange (11) a coherence over D²(f) ∨₁ D³(z) ∨₁ D³(e), which is a pasting context; c is a formal 2-variable assigned the composite γ̄_s ∗₁ w, which substitution allows. The left version is symmetric.
6. **Assembly (§4).** The recursion follows the unique z-leaf and is finite. The z-free prefix L : u → A_rs and suffix R : B_rs → v are compared with ν_u and ν_v^† by RC(3) in Λ (Λ has no 3-generators, so all its 3-cells have identity strict image). 4-terms of Γ are invertible (no 4-generators), so R_H ∗₃ R_{H′}^† is legal. The identity-image case reduces to Λ by the support lemma.
7. **The cube (§5).** The 2-skeleton's paths 000 → 111 form a hexagon with two directed routes, so strict 2-cells are directed subpaths of either chain. The first chain is round 5's. For the second (321 → 312 → 132 → 123), I checked that its two adjacent pairs of faces are again one two-square cylinder of each orientation (321 → 312 → 132 moves the coordinate-1 edge from the end of the path to the front; 312 → 132 → 123 moves the coordinate-3 edge from the front to the end), as in the first hemisphere, and that the height argument of round 4 gives one active column. So round 5's construction applies to it. X has no nontrivial strict whiskerings (000 has no incoming edges, 111 no outgoing ones, 321 is initial and 123 terminal in the rewrite graph) and π A ≠ π B, so X is the only nonidentity strict 3-cell and the lemma applies.
8. **Cylinder of D² (§6.1).** The four paths x⁻ → y⁺ and the rewrite graph (20) are right; the words are a, b, c, d, ab, cd, with ab ≠ cd. Fibres a and d are pasting contexts, b and c are lax squares (prompt item 10), and ab, cd satisfy the line-word criterion with the full-span generators G and F. Z has no strict whiskerings and its two 2-boundaries differ.
9. **c ⋆ D² (§6.2).** This is Cone(D²; c), whose RC(3) was proved in cone-over-coherences round 3; the lemma gives a second, shorter proof.
10. **Exchange 4-term (24).** Both sides go from L⁻ to R⁺ over D³ ∨₀ D³ and are full; legal. As the response says, this is a local law, not the missing fusion statement.
11. **Literature remark.** Forest–Mimram's coherence result for positive Gray presentations is about the free Gray category on a presentation, not about relative normalisation of CaTT terms; the response states this correctly.

**Consequence for the project.** The extension lemma reduces RC(3) for 3-dimensional contexts with "isolated" 3-generators to RC(3) for their 2-skeleta. The 2-skeleton step with exchange (Question 2, the 2 × 2 grid) is now the single open step shared by this problem, the naturality problem (round 6, D² ∗₀ D²) and the cone problem (round 4, D² ∨ D²).

Follow-up prompt: `outbox/gray-contexts-r7.md` (round 7, unsent).
