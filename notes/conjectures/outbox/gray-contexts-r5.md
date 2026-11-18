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

# Researcher Response

**Question 1 follows from the two-square result in item 13.** The missing evaluation-fusion argument can be carried out relative to a formal vertical chain: its \(2\)-variables remain variables during the proof, and their substituted terms are treated as fixed inputs. No whiskered term’s arity is inserted into that chain.

I give the construction below. It proves RC(3) for the negative hemisphere, hence gives the requested \(4\)-term \(H\to1_A\). I then give an extension of item 14 that applies to both examples in Question 4.

The generating-\(1\)-graph hypothesis in Question 3 needs correction: the stated counterexample \((x:\star,a:1_x\to1_x)\) already has an acyclic generating \(1\)-graph.

# 1. The hemisphere and its proper intervals

Write \(\mathcal H\) for the negative hemisphere. Label the coordinate directions so that its paths from \(000\) to \(111\) are
\[
321,\qquad231,\qquad213,\qquad123,
\]
and its generating rewrites, with their necessary edge whiskers, are
\[
321\xRightarrow{E_1}231
\xRightarrow{E_2}213
\xRightarrow{E_3}123.
\tag{1}
\]

These are all the paths and all the elementary rewrites between them: the missing cube vertex excludes the other two permutations. Consequently, a strict \(2\)-cell between these endpoints is an interval of the word \(E_1E_2E_3\), including an empty interval.

Fix literal bracketed \(1\)-terms \(p_0,p_1,p_2,p_3\) for these four paths, and literal terms
\[
E_i:p_{i-1}\to p_i.
\]
For example, choose left-associated paths. Then \(E_1,E_3\) are the right-whiskered faces, and \(E_2\) is the left-whiskered middle face preceded and followed by the required path associators.

## Proper intervals satisfy RC(3)

The unions of the first two faces and of the last two faces are rectangular two-square contexts. One has the cylinder orientation of item 13; the other has its \(2\)-opposite. Reversing dimension \(2\) transfers RC(3), using the opposite construction on computads and their cells. [arxiv.org](https://arxiv.org/html/2402.01611v2?utm_source=chatgpt.com)

A single face with its external edge whisker is a retract of an adjacent rectangle. Here are the substitutions explicitly. Write a two-square cylinder as
\[
F:f^-e_1\to e_0f^+,\qquad
G:g^-e_2\to e_1g^+.
\]

For the subcontext consisting of \(F\) and \(g^+\), fix its variables and send
\[
c^-\mapsto b^-,
\qquad
g^-\mapsto1_{b^-},
\qquad
e_2\mapsto e_1g^+,
\]
and send \(G\) to
\[
\lambda_{e_1g^+}:1_{b^-}(e_1g^+)\to e_1g^+.
\]
This is a literal retraction.

For the subcontext consisting of \(f^-\) and \(G\), fix its variables and send
\[
a^+\mapsto a^-,
\qquad
e_0\mapsto1_{a^-},
\qquad
f^+\mapsto f^-e_1,
\]
and send \(F\) to the reverse left unitor
\[
f^-e_1\to1_{a^-}(f^-e_1).
\]

Thus the proper nonempty intervals of (1), including their necessary whiskers, satisfy RC(3). Empty intervals are covered by item 4.

The support restriction used here follows from the supplied support lemma and positivity of free strict \(2\)-composition. In a \(2\)-term, each generating \(2\)-cell contributes positively to its strict image: composition adds these contributions and exchange preserves them. Hence a term with a proper interval as strict image uses only that interval’s faces. Its remaining support consists of their boundary paths and the required external whisker. A \(3\)-term has the same support as its \(2\)-source by item 3.

# 2. Two universal constructions

The proof needs two families of \(4\)-terms. Both are constructed over globular pasting contexts.

## 2.1 Varying the \(2\)-inputs of a vertical context

Let
\[
V_m=
\bigl(x,y;\ f_0,\ldots,f_m:x\to y;\
\alpha_i:f_{i-1}\to f_i\bigr).
\]
Replace each \(\alpha_i\) by
\[
\alpha_i^-,\alpha_i^+:f_{i-1}\to f_i,
\qquad
\eta_i:\alpha_i^-\to\alpha_i^+.
\]
The resulting context is
\[
V_m^\uparrow=D^3\vee_1\cdots\vee_1D^3.
\]

For any full \(2\)-term \(a\) over \(V_m\), define
\[
\mathsf A_a
=
\operatorname{coh}_{V_m^\uparrow,\ a[-]\to a[+]}[\mathrm{id}].
\tag{2}
\]
The composition condition holds: \(a[-]\) uses exactly the negative \(2\)-boundary, and \(a[+]\) exactly the positive one.

If \(\chi:a\to b\) is a \(3\)-term over \(V_m\), with \(a,b\) full, define
\[
\boxed{
\Omega_\chi=
\operatorname{coh}_{V_m^\uparrow,\,
(\chi[-]*_2\mathsf A_b)
\to
(\mathsf A_a*_2\chi[+])}
[\mathrm{id}].
}
\tag{3}
\]
Both boundary \(3\)-terms have the literal type \(a[-]\to b[+]\). Each uses every \(\eta_i\), and therefore every variable of \(V_m^\uparrow\). This is a valid \(4\)-coherence.

The \(\eta_i\) may be substituted by arbitrary \(3\)-terms. In particular, they may be the normalizers of arbitrary whiskered \(2\)-terms. Their \(1\)-boundaries remain fixed.

We also need the following operations, constructed by the same rule.

* **Action on \(4\)-cells:** replace each \(\eta_i\) by two parallel \(3\)-variables and a \(4\)-variable between them. The arity is a sequence of \(4\)-discs glued along dimension \(1\); the composition rule gives the action.
* **Compatibility with composition of \(3\)-inputs:** use
  \[
  (D^3\vee_2D^3)\vee_1\cdots\vee_1(D^3\vee_2D^3).
  \]
  A full-support \(4\)-coherence compares
  \[
  \mathsf A_a(\eta*_2\theta)
  \quad\text{and}\quad
  \mathsf A_a(\eta)*_2\mathsf A_a(\theta).
  \]
* **Compatibility with substitution of \(2\)-expressions:** if \(\tau\) assigns \(2\)-terms over \(V_m\), then
  \[
  \mathsf A_{a[\tau]}
  \quad\text{and}\quad
  \mathsf A_a[\tau^\uparrow]
  \]
  are parallel \(3\)-terms over \(V_m^\uparrow\). When \(a[\tau]\) is full, both are full, so a coherence over \(V_m^\uparrow\) compares them.

These supply the action, composition, and substitution comparisons below. They do not require naturality in a \(1\)-input.

## 2.2 Coherent normalization of path-only gaps

Fix a parenthesization convention for vertical composites, denoted \(C\). A singleton composite is its term.

Consider an expression assembled from fixed event terms and path-only \(2\)-terms. Associate it into the form
\[
C(G_0,E_1,G_1,E_2,G_2,E_3,G_3),
\tag{4}
\]
omitting absent events. Each \(G_i\) uses only the edges of the single path \(p_i\). An internal \(G_i\) has type \(p_i\to p_i\).

Choose \(3\)-normalizations
\[
h_i:G_i\to H_i,
\]
where an internal \(H_i\) is \(1_{p_i}\), and an outside \(H_i\) is the prescribed endpoint correction. Item 4 constructs these terms over individual path contexts.

Normalize the gaps in left-to-right order, remove the resulting internal identities, and associate the remaining factors to the fixed convention. Call this \(3\)-term \(\Phi\).

There is a specified \(4\)-comparison between a nested application of this procedure and a single application to the expanded expression.

Here is its construction.

1. Use associativity comparisons to fix the literal source expression for each \(G_i\). Moving these associators past a gap \(3\)-term uses (3).
2. Compose all operations on a given gap into one \(3\)-term \(G_i\to H_i\). Any two such terms are compared by item 4 over that path.
3. Compare the orders of the resulting gap operations over
   \[
   P_{\mathrm{gap}}
   =
   D^3(h_0)\vee_1D^2(E_1)\vee_1D^3(h_1)
   \vee_1D^2(E_2)\vee_1D^3(h_2)
   \vee_1D^2(E_3)\vee_1D^3(h_3).
   \]
   If several successive operations on one gap have not yet been composed, use a chain of \(3\)-discs there instead.

   The two formal \(3\)-terms \(L,R\) apply the same gap operations in different orders. Choose their source and target parenthesizations identically. Both use every displayed generator, so
   \[
   \boxed{\operatorname{coh}_{P_{\mathrm{gap}},\,L\to R}[\mathrm{id}]}
   \tag{5}
   \]
   is a \(4\)-term.
4. After substitution, the internal targets \(H_i\) are identity \(2\)-terms. Comparisons between their removal and the final reassociations are coherences over the vertical context of the remaining event and endpoint factors.

Thus (5) does not identify a formal \(2\)-variable with an identity. Identity removal is performed after substitution and compared over the appropriate smaller vertical arity.

This construction compares only path-gap operations and vertical associativity operations. It never requires commuting \(4\)-fillers obtained from the two overlapping rectangles.

# 3. Choose normal forms and normalizers

For every \(1\)-term \(r\) whose strict path is \(p_i\), choose
\[
\gamma_r:r\to p_i,
\qquad
\bar\gamma_r:p_i\to r
\]
by lifting to the path context. When \(r=p_i\) literally, omit that endpoint factor.

If \(T:r\to s\) has strict event word
\[
w=E_{i+1}\cdots E_j,
\]
put
\[
N(T)=C(\gamma_r,E_{i+1},\ldots,E_j,\bar\gamma_s).
\tag{6}
\]
An empty list denotes the appropriate identity. This convention fixes all bracketings.

For proper intervals, choose
\[
\nu_T:T\to N(T)
\]
using RC(2). Any required comparison between such normalizers is supplied by the proper-interval RC(3) established in §1.

For the full word, define \(\nu_T\) recursively.

Write \(T=\operatorname{coh}_{Q,B}[\sigma]\). Item 14 gives
\[
\sigma=\kappa[\delta].
\]
Because \(T\) uses all three faces, the unique active column spans \(000\to111\). Every other column is point-supported. Therefore its reduced arity is a pure vertical context \(V_m\).

In \(V_m\), write
\[
\widetilde T=\operatorname{coh}_{Q,B}[\kappa].
\]
Its strict \(2\)-image is the entire vertical chain. If its exact \(1\)-boundaries are \(r,s\), define
\[
K(\widetilde T)
=
C(\gamma_r^{V_m},\alpha_1,\ldots,\alpha_m,\bar\gamma_s^{V_m}),
\]
where the superscript means that the path corrections are formed in \(V_m\). Here the canonical paths are the individual formal \(1\)-variables \(f_i\).

Both terms are full, so take
\[
b_{\widetilde T}
=
\operatorname{coh}_{V_m,\,
\widetilde T\to K(\widetilde T)}[\mathrm{id}].
\tag{7}
\]

Let \(T_i=\delta(\alpha_i)\). Define \(\nu_T\) by the composite
\[
\boxed{
T
\xrightarrow{\,b_{\widetilde T}[\delta]\,}
K(\widetilde T)[\delta]
\xrightarrow{\,C^3(\nu_{T_i})\text{ with the fixed framing}\,}
C(\gamma_r^{V_m}[\delta],N(T_i),\bar\gamma_s^{V_m}[\delta])
\xrightarrow{\,\Phi\,}
N(T).
}
\tag{8}
\]
The middle arrow uses ordinary vertical composition of the \(3\)-normalizers, with identity \(3\)-terms on the framing factors.

This recursion is well founded: every full-word \(T_i\) is a proper syntactic subterm of \(T\); the other \(T_i\) already have chosen normalizers.

The flattening \(\Phi\) includes the endpoint comparisons
\[
\gamma_r^{V_m}[\delta]*_1\gamma_{\delta(f_0)}
\longrightarrow \gamma_{r[\delta]},
\tag{9}
\]
and
\[
\bar\gamma_{\delta(f_m)}*_1\bar\gamma_s^{V_m}[\delta]
\longrightarrow\bar\gamma_{s[\delta]}.
\]
Both sides of each comparison are path-only \(2\)-terms with identical boundaries, so item 4 supplies the \(3\)-term. They are not identified definitionally.

# 4. Relative evaluation fusion

This is the central lemma.

> **Relative fusion lemma.** Let \(u\) be a full \(2\)-term over a formal vertical context \(V_m\), and let
> \[
> \mathcal H\vdash\delta:V_m
> \]
> send its endpoints to \(000,111\).
> Choose the generic comparison
> \[
> b_u:u\to K(u)
> \]
> as in (7), using the identity when \(u\) is a variable. Let
> \[
> f_{u,\delta}:K(u)[\delta]\to N(u[\delta])
> \]
> first apply the normalizers \(\nu_{\delta(\alpha_i)}\), then apply the fixed flattening \(\Phi\).
> There is a constructible \(4\)-term
> \[
> \boxed{
> E(u,\delta):
> \nu_{u[\delta]}
> \longrightarrow
> b_u[\delta]*_2 f_{u,\delta}.
> }
> \tag{10}
> \]

## Proof

Induct on the syntax of \(u\). The substituted terms \(\delta(\alpha_i)\) remain fixed inputs throughout this induction.

If \(u[\delta]\) has a proper event interval, the two sides of (10) are parallel \(3\)-terms over the corresponding proper-interval context. Its RC(3) supplies (10).

If \(u=\alpha_i\), both sides use the same \(\nu_{\delta(\alpha_i)}\). The comparison is the appropriate \(4\)-unitor. No arity of \(\delta(\alpha_i)\) is expanded.

Now suppose
\[
u=\operatorname{coh}_{Q,A}[\tau]
\]
and \(u[\delta]\) has the full word.

### The head reduction is stable

In the formal context \(V_m\), a nonidentity strict \(2\)-term uses a consecutive subchain of the \(\alpha_i\). Its \(0\)-boundary is the pair of formal endpoints \(x,y\).

Therefore the head of \(u\), evaluated into \(V_m\), has one active \(0\)-column spanning \(x\to y\); all other columns are point-supported. After substituting \(\delta\), that column remains active, since otherwise \(u[\delta]\) would have no \(2\)-generator in its support.

Consequently the reduced head arity is unchanged. With fixed positional names, the refinement \(\lambda\) of item 14 is the identity here. Alternatively, its supplied refinement comparison gives the same result.

Thus the initial head comparison in the recursive definition of \(\nu_{u[\delta]}\) is precisely the substitution of the corresponding generic head comparison.

### Replace the input normalizers

Let \(u_i\) be the generic \(2\)-inputs of that reduced head, restricted to their supporting vertical subchains. Write
\[
b_i:u_i\to K(u_i).
\]
The induction gives
\[
\nu_{u_i[\delta]}
\longrightarrow b_i[\delta]*_2 f_{u_i,\delta}.
\tag{11}
\]
For a proper image, this is instead the proper-interval filler.

Transport (11) through the head’s composition operation using the action on \(4\)-cells from §2.1. Use its composition comparison to separate the \(b_i[\delta]\) from the \(f_{u_i,\delta}\).

### Compare the generic evaluations

Let \(h\) be the generic reduced-head comparison. Let \(\mathcal C\) denote the framed vertical-composition expression at this head.

Over \(V_m\), define
\[
a_0=\mathcal C(K(u_i)).
\]
Let
\[
\chi_{\mathrm{gen}}:a_0\to K(u)
\]
be the explicit generic gap flattening of §2.2, formed in \(V_m\).

Then
\[
b_{\mathrm{eval}}
=
h*_2\mathcal C^3(b_i)*_2\chi_{\mathrm{gen}}
\]
has the same type as \(b_u\). Both are full in \(V_m\): their source is the full term \(u\). Hence
\[
\operatorname{coh}_{V_m,\,b_{\mathrm{eval}}\to b_u}[\mathrm{id}]
\tag{12}
\]
is a valid \(4\)-term.

### The actual fusion calculation

Put
\[
\eta_j=\nu_{\delta(\alpha_j)},
\qquad
\delta^+(\alpha_j)=N(\delta(\alpha_j)),
\]
leaving the \(0\)- and \(1\)-assignments unchanged.

By definition, each \(f_{u_i,\delta}\) is the action on the relevant \(\eta_j\), followed by its gap flattening \(\Phi_i\). Let \(\Phi_{\mathrm{head}}\) be the outer flattening, and let \(\Phi_u\) be the flattening used in \(f_{u,\delta}\).

The gap lemma gives
\[
\mathcal C^3(\Phi_i)*_2\Phi_{\mathrm{head}}
\longrightarrow
\chi_{\mathrm{gen}}[\delta^+]*_2\Phi_u.
\tag{13}
\]
Indeed, after replacing each base input by \(N(\delta(\alpha_j))\), every event factor is one of the fixed \(E_i\). All remaining factors are path-only. Both sides of (13) are therefore nested or flat normalizations of the same expanded expression.

Now perform the following \(4\)-dimensional calculation:
\[
\begin{aligned}
\mathcal C^3(f_{u_i,\delta})*_2\Phi_{\mathrm{head}}
&\Longrightarrow
\mathsf A_{a_0}(\eta)*_2
\mathcal C^3(\Phi_i)*_2\Phi_{\mathrm{head}}\\
&\Longrightarrow
\mathsf A_{a_0}(\eta)*_2
\chi_{\mathrm{gen}}[\delta^+]*_2\Phi_u\\
&\Longrightarrow
\chi_{\mathrm{gen}}[\delta]*_2
\mathsf A_{K(u)}(\eta)*_2\Phi_u\\
&=
\chi_{\mathrm{gen}}[\delta]*_2 f_{u,\delta}.
\end{aligned}
\tag{14}
\]
The first arrow uses the composition and substitution comparisons of §2.1. The second is (13). The third is the reverse of (3), applied to \(\chi_{\mathrm{gen}}\).

When the expression is a framed vertical composite, its explicit action by ordinary compositions and the action (2) are compared by a full-support \(4\)-coherence on \(V_m^\uparrow\). Thus the use of \(\mathsf A\) in (14) agrees with the middle arrow chosen in (8), up to a specified \(4\)-term.

Combining (11), (14), and (12), with the fixed associators, constructs (10). This completes the induction.

The proof expands the **chosen normal forms** \(N(\delta(\alpha_i))\) into their vertical words. It never expands the original arities of the arbitrary terms \(\delta(\alpha_i)\).

# 5. Compatibility with every \(3\)-term

We now construct, for every \(3\)-term \(H:u\to v\) in the hemisphere,
\[
\boxed{
I_H:\nu_u\longrightarrow H*_2\nu_v.
}
\tag{15}
\]
Since the hemisphere has no \(3\)-variables, \(u,v\) have the same strict \(2\)-image. Their exact \(1\)-boundaries agree, so \(N(u)=N(v)\) literally.

If their event word is proper, (15) is supplied by proper-interval RC(3).

For the full word, induct on the syntax of \(H\). Apply item 14 to its head. Its reduced arity is one suspended column, with every other column point-supported. The supplied \(4\)-comparison transfers (15) between the original and reduced heads.

Write the reduced formal head as
\[
\mathfrak h=\operatorname{coh}_{P,u_0\to v_0}[\mathrm{id}],
\qquad
H=\mathfrak h[\delta].
\]

## 5.1 A comparison over the formal \(3\)-arity

Suppose first that \(\dim P=3\). The context \(P\) has \(1\)-variables \(f_0,\ldots,f_m\); for each \(j\), its \(2\)- and \(3\)-variables form a chain
\[
\alpha_{j,0}
\xrightarrow{\xi_{j,1}}
\alpha_{j,1}
\longrightarrow\cdots
\xrightarrow{\xi_{j,r_j}}
\alpha_{j,r_j},
\]
where every \(\alpha_{j,k}\) has type \(f_{j-1}\to f_j\).

Let
\[
D_j=\xi_{j,1}*_2\cdots *_2\xi_{j,r_j},
\]
using \(1_{\alpha_{j,0}}\) when \(r_j=0\). Compose the \(D_j\) along dimension \(1\), and add the same endpoint framing as in the generic normal forms. This gives an explicit \(3\)-term
\[
D:K^-\to K^+.
\]
Here \(K^-\) and \(K^+\) are the framed composites of the negative and positive \(2\)-boundary rows.

Choose
\[
b_{u_0}:u_0\to K^-,
\qquad
b_{v_0}:v_0\to K^+
\]
over the corresponding vertical \(2\)-boundary contexts.

Both
\[
b_{u_0}*_2D,
\qquad
\mathfrak h*_2b_{v_0}
\]
have the exact type \(u_0\to K^+\), and both are full in \(P\). For the first, every \(\xi_{j,k}\) is used by \(D\); an empty chain retains its \(\alpha_{j,0}\) through its identity term. The second is full because \(\mathfrak h\) is full.

Therefore
\[
\boxed{
\Xi_P=
\operatorname{coh}_{P,\,
(b_{u_0}*_2D)\to
(\mathfrak h*_2b_{v_0})}[\mathrm{id}]
}
\tag{16}
\]
is legal.

If \(\dim P=2\), use \(K^-=K^+=K\) and \(D=1_K\). The same formula is legal.

## 5.2 Normalize the substituted \(3\)-inputs

For fixed \(j\), all terms \(\alpha_{j,k}[\delta]\) have the same exact \(1\)-boundaries and the same strict event word. Thus their normal form is one literal term \(N_j\).

The inductive comparisons for the proper subterms \(\xi_{j,k}[\delta]\) compose to
\[
\nu_{\alpha_{j,0}[\delta]}
\longrightarrow
D_j[\delta]*_2\nu_{\alpha_{j,r_j}[\delta]}.
\tag{17}
\]
Include the \(4\)-associators for the chosen bracketing of \(D_j\). For an empty chain, (17) is the inverse \(4\)-unitor.

Compose (17) along dimension \(1\), using the ordinary \(4\)-dimensional interchange coherence. Its arity consists of two successive \(3\)-cells in each position, with those positions glued along dimension \(1\). This is a globular pasting context.

We obtain
\[
G^-\longrightarrow D[\delta]*_2G^+,
\tag{18}
\]
where
\[
G^-:K^-[\delta]\to L,\qquad
G^+:K^+[\delta]\to L,
\]
and
\[
L=C(\gamma_s[\delta],N_1,\ldots,N_m,\bar\gamma_t[\delta]).
\]
The terms \(s,t\) are common to \(u_0,v_0\), so \(L\) is literally the same on both sides.

Choose one flattening
\[
\Phi:L\to N(u_0[\delta])=N(v_0[\delta]).
\]
Appending it to (18) gives
\[
f_u\longrightarrow D[\delta]*_2 f_v,
\qquad
f_u=G^-*_2\Phi,\quad f_v=G^+*_2\Phi.
\tag{19}
\]

## 5.3 Assemble the compatibility term

Apply relative fusion to the two boundary terms. Then compose
\[
\begin{aligned}
\nu_{u_0[\delta]}
&\xRightarrow{E_u}
b_{u_0}[\delta]*_2f_u\\
&\Longrightarrow
b_{u_0}[\delta]*_2(D[\delta]*_2f_v)\\
&\Longrightarrow
(b_{u_0}[\delta]*_2D[\delta])*_2f_v\\
&\xRightarrow{\Xi_P[\delta]}
(\mathfrak h[\delta]*_2b_{v_0}[\delta])*_2f_v\\
&\Longrightarrow
\mathfrak h[\delta]*_2(b_{v_0}[\delta]*_2f_v)\\
&\xRightarrow{E_v^\dagger}
\mathfrak h[\delta]*_2\nu_{v_0[\delta]}.
\end{aligned}
\tag{20}
\]
The unlabelled arrows are (19), whiskered as required, and \(4\)-associators. The superscript \(\dagger\) means the reverse-directed construction; no \(5\)-dimensional inverse equation is needed.

This proves (15) for the reduced head. The head comparison from item 14 proves it for the original head and completes the induction.

# 6. The requested cube contraction

Now let
\[
H:A\to A
\]
be \(X\)-free. Item 6 places it literally in the hemisphere context. Equation (15) gives
\[
I_H:\nu_A\longrightarrow H*_2\nu_A.
\]

Choose the inverse normalizer and its cancellation witness
\[
\bar\nu_A:N(A)\to A,
\qquad
\varepsilon:\nu_A*_2\bar\nu_A\to1_A.
\]
These are constructed by reversing the primitive full-support coherences in \(\nu_A\), taking their cancellation coherences over the same arities, and composing the witnesses using the ordinary associators and interchange terms.

The following composite is the required \(4\)-term:
\[
\boxed{
\begin{aligned}
H
&\longrightarrow H*_2 1_A\\
&\longrightarrow H*_2(\nu_A*_2\bar\nu_A)\\
&\longrightarrow (H*_2\nu_A)*_2\bar\nu_A\\
&\xrightarrow{\,I_H^\dagger\text{ whiskered by }\bar\nu_A\,}
\nu_A*_2\bar\nu_A\\
&\xrightarrow{\varepsilon}1_A.
\end{aligned}}
\tag{21}
\]
The first three arrows are the inverse unitor, the whiskering of \(\varepsilon^\dagger\), and the associator.

This is a recursive construction from the syntax of \(H\), using the supplied proper-interval RC(3) terms and the displayed coherence constructors.

# 7. Extension to contexts with \(3\)-variables

There is also a sufficient condition for retaining item 14’s original inactivity test.

Write
\[
\operatorname{supp}_k(t)=\operatorname{supp}(t)\cap\operatorname{Var}_k(\Gamma).
\]
Assume \(\dim\Gamma\leq3\) and
\[
\boxed{
\operatorname{supp}_2(s_2z)\ne\varnothing
\quad\text{for every \(3\)-variable }z\text{ of }\Gamma.
}
\tag{22}
\]

Then
\[
\boxed{
\operatorname{supp}_2(s_2t)=\varnothing
\quad\Longrightarrow\quad
\operatorname{supp}_{\geq2}(t)=\varnothing
}
\tag{23}
\]
for every \(3\)-term \(t\).

## Proof of the boundary-support assertion

Induct on \(t\).

For a variable, the premise contradicts (22).

For \(t=\operatorname{coh}_{P,u\to v}[\sigma]\) with \(\dim P\leq2\), the coherence condition makes \(u\) full in \(P\). Thus
\[
\operatorname{supp}(u[\sigma])
=
\bigcup_{a\in\operatorname{Var}(P)}
\operatorname{supp}(\sigma(a)).
\]
If its \(2\)-support is empty, every assignment is \(2\)-generator-free. Those assignments have dimension at most \(2\), so they also use no \(3\)-generator.

For \(\dim P=3\), the constructor uses the composition condition. The images of all \(2\)-variables in \(\partial^-_2P\) therefore have empty \(2\)-support.

The graph whose vertices are the \(2\)-variables of \(P\) and whose edges are its \(3\)-variables is a disjoint union of directed chains, allowing isolated vertices. Its initial vertices are precisely the \(2\)-variables of \(\partial^-_2P\). This follows from the globular pasting construction: composition along dimension \(2\) concatenates these chains, while composition along lower dimensions places chains alongside one another.

Proceed along each chain. If \(z:a\to b\) is a formal \(3\)-variable and \(\sigma(a)\) has empty \(2\)-support, the induction hypothesis applies to the proper subterm \(\sigma(z)\). It has support only in dimensions \(0,1\). Its target \(\sigma(b)\) consequently has empty \(2\)-support as well.

This proves (23) for all assignments and hence for \(t\).

Condition (22) is also necessary for this particular one-sided assertion: apply (23) to a \(3\)-variable.

## Consequence for factorization

Suppose additionally that the generating \(1\)-graph of \(\Gamma\) is acyclic. In an inactive column, every assigned \(2\)-term is \(2\)-generator-free. For each assigned \(3\)-term, its \(2\)-source is one of those assignments, so (23) places the entire \(3\)-term on the \(1\)-skeleton.

The literal path lift from item 14 therefore applies unchanged. Its constructions
\[
R_\sigma,\quad\kappa_\sigma,\quad\delta_\sigma,\quad
\chi_\sigma,\quad\lambda_{\sigma,\rho},\quad
\zeta_{\sigma,\rho},\quad\Theta_{\sigma,\rho}
\]
remain valid. For stability, require both ambient contexts to satisfy (22). An old inactive column stays path-supported; a column that becomes inactive is handled by (23) in the new context.

### Cylinder of \(D^2\)

Use \(A^\pm:f^\pm\to g^\pm\), vertical edges \(h,k\), and squares
\[
F:f^-k\to hf^+,\qquad G:g^-k\to hg^+.
\]
Its \(3\)-generator is
\[
Z:(A^-*_0k)*_1G
\longrightarrow
F*_1(h*_0A^+).
\]
Its source \(2\)-support is \(\{A^-,G\}\), and its target \(2\)-support is \(\{F,A^+\}\). This is the cylinder presentation in BMOSV, Figure 18. Its generating \(1\)-graph is a directed square with parallel horizontal arrows, hence acyclic. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

### The join \(c\star D^2\)

Write
\[
f,g:x\to y,\qquad A:f\to g,\qquad
p:c\to x,\qquad q:c\to y,
\]
with
\[
\beta_f:q\to p*_0f,\qquad
\beta_g:q\to p*_0g,
\]
and
\[
Z:\beta_g\longrightarrow\beta_f*_1(p*_0A).
\]
This orientation follows from the join differential
\[
d(c\star A)=A-(c\star g)+(c\star f).
\]
Thus the source \(2\)-support is \(\{\beta_g\}\); the target \(2\)-support is \(\{\beta_f,A\}\). The generating \(1\)-graph increases along \(c<x<y\). [arxiv.org](https://arxiv.org/pdf/1607.00668?utm_source=chatgpt.com)

Both examples satisfy both the source and target versions of (22).

Without a condition of this kind, the old test fails. In
\[
(x,y,\ f:x\to y,\ Z:1_f\to1_f),
\]
map the two \(2\)-boundary variables of \(D^3\) to \(1_f\) and its top variable to \(Z\). The sole column is inactive according to the old test, but no literal factorization through the path context of \(f\) can produce the variable \(Z\).

# 8. Scope of the result

The proof establishes the cube case and evaluation fusion for its active vertical columns. It uses the forced three-event order, the proper-interval cylinder results, and the fact that a full-word head reduces to one pure vertical column.

It does not prove general RC(3) from acyclicity of the generating \(1\)-graph. That hypothesis is already refuted by the counterexample supplied in §3:
\[
(x:\star,\ a:1_x\to1_x)
\]
has one vertex and no generating \(1\)-edges. If a nonempty connected graph is required, adjoin \(y\) and \(f:x\to y\); the substitution \(y\mapsto x,\ f\mapsto1_x\) retracts it to the same counterexample.

The Steiner loop-free alternative and the general \(RC(n)\)/\(G(n)\) statements are not established by this argument.
