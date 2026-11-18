# Problem: composites of molecules in CaTT (Gray contexts), round 4

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Rounds 1–3 and their verified answers are archived in `answered/gray-contexts-2026-11-18.md`, `answered/gray-contexts-round2-2026-11-18.md` and `answered/gray-contexts-r3-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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

## 3. What remains

RC(3) for the lax square is settled (item 10). In larger acyclic contexts, the columns of an arity that do not carry the active 2-generator may carry nonidentity paths, so item 10's point-support step fails. RC(3) fails for loopy contexts such as (x, a : 1_x → 1_x) (π₃(S²) = ℤ: the weak free object groupoidifies to S², the strict one to K(ℤ,2)), so a proof must use some acyclicity.

## 4. Questions

1. **The Gray cube (smallest open case).** Let U = D¹ ⊗ D¹ ⊗ D¹, presented with hexagon composites. Prove that every X-free 3-term H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉ is connected to the identity (RC(3) for 3-loops over the three-face negative hemisphere). Here the three faces are lax squares glued along edges, so item 10 applies to each face separately but not to composites that whisker one face by edges of another.
2. **Beyond point-supported columns.** Generalise item 10's active-column factorisation to contexts where the inactive columns carry nonidentity paths, e.g. two lax squares glued along an edge (the cylinder of x → y → z). Is there a substitution-stable factorisation through a "horizontal word of vertical chains"?
3. **RC(3) and RC(n) for acyclic contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule (or every finite Steiner loop-free computad), and say which hypothesis the proof uses; then RC(n), or the weaker G(n).

## 5. What counts as a solution

Explicit terms for question 1, 2 or 3; a proof of RC(3) or RC(n) on acyclic contexts; a counterexample (an acyclic context with two parallel terms of equal strict image and no term between them); or a published reference.

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

**The factorization asked for in Question 2 exists when the directed graph of generating \(1\)-cells is acyclic.** It is literal at the level of substitutions and has explicit comparison terms compatible with further substitution.

This gives a reduction of inactive columns to paths. It does **not** yet contract an arbitrary cube loop: active columns retain their substituted \(2\)-terms. I give the factorization, its coherence terms, and a \(4\)-cell for distributing a fixed whisker across a vertical composite.

## 1. Literal factorization of inactive columns

Let \(\Gamma\) be a finite context of dimension at most \(2\), and suppose its directed graph of generating \(1\)-cells is acyclic. Let
\[
\Gamma\vdash \sigma:P
\]
be a substitution into a globular pasting context of dimension at most \(3\).

Use the convention that \(\Delta\vdash\theta:P\) assigns a term of \(\Delta\) to each variable of \(P\); thus \(\theta[\eta]\) denotes substitution into those assigned terms.

Write the decomposition of \(P\) into \(0\)-columns as
\[
P=Q_1\vee_0\cdots\vee_0Q_k,
\qquad Q_j=\Sigma B_j.
\]
This is the suspension-and-wedge description of globular pasting diagrams. If \(\dim P\leq2\), each \(Q_j\) is a vertical \(2\)-chain, allowing the chain with no \(2\)-variables, namely \(D^1\). [arxiv.org](https://arxiv.org/html/2402.01611v2?utm_source=chatgpt.com)

Call \(Q_j\) **inactive for \(\sigma\)** if, for every \(2\)-variable \(z\) of \(Q_j\),
\[
\operatorname{supp}(\sigma(z))\cap\operatorname{Var}_2(\Gamma)=\varnothing.
\]
Otherwise call it active. A column with no \(2\)-variables is inactive.

### The literal lift of an inactive column

All \(1\)-variables of an inactive \(Q_j\) have images with the same strict path, say \(w_j\). Indeed, the image of each \(2\)-variable is a term over the \(1\)-skeleton, so its strict image is an identity. Its two \(1\)-boundaries therefore have equal strict paths. These equalities connect all the \(1\)-variables of the column.

Moreover, every assigned term from this column uses only the vertices and edges of \(w_j\):

- For an assigned \(1\)-term, its support is precisely the vertices and edges of its strict path. This follows by induction on its syntax: a composition concatenates the paths of its inputs, and a coherence of dimension \(1\) over a point contributes only that point.
- For an assigned \(2\)-term, the total support lemma, §2(3) of the question, identifies its support with that of its \(1\)-source.
- For an assigned \(3\)-term, the same lemma applies because \(\Gamma\) has no \(3\)-variables; its support equals that of its assigned \(2\)-source.

Let \(C_{w_j}\) be the linear path context of \(w_j\), and let
\[
\Gamma\vdash\iota_j:C_{w_j}
\]
send its vertices and edges to the corresponding generators of \(\Gamma\). For an empty path, \(C_{w_j}\) is a point.

Acyclicity implies that \(w_j\) has no repeated vertices. Consequently, \(\iota_j\) is an **injective variable renaming**, and substitution along \(\iota_j\) reflects syntactic equality.

Every term assigned by \(\sigma|_{Q_j}\) therefore has a unique literal lift along \(\iota_j\). These lifts form a substitution
\[
C_{w_j}\vdash\theta_j:Q_j
\]
such that
\[
\boxed{\sigma|_{Q_j}=\theta_j[\iota_j].}
\tag{1}
\]
The lift preserves every coherence constructor and every bracketing. It changes only variable names.

### Assemble the factorization

Define
\[
R_\sigma=R_1\vee_0\cdots\vee_0R_k,
\qquad
R_j=
\begin{cases}
Q_j,&Q_j\text{ active},\\
C_{w_j},&Q_j\text{ inactive}.
\end{cases}
\tag{2}
\]
This is a globular pasting context. Empty paths are point factors and disappear under the wedge.

There are substitutions
\[
R_\sigma\vdash\kappa_\sigma:P,
\qquad
\Gamma\vdash\delta_\sigma:R_\sigma
\]
defined as follows:

| Column | \(\kappa_\sigma\) | \(\delta_\sigma\) |
|---|---|---|
| Active | Structural inclusion of the retained \(Q_j\) | Original assignments \(\sigma|_{Q_j}\) |
| Inactive | Literal lift \(\theta_j\) | Path labeling \(\iota_j\) |

Their endpoint assignments agree at each gluing vertex. Equation (1) gives
\[
\boxed{\sigma=\kappa_\sigma[\delta_\sigma]}
\tag{3}
\]
as a syntactic equality.

For \(\dim P\leq2\), \(R_\sigma\) is exactly a horizontal word of vertical \(2\)-chains and linear paths. Consecutive path factors concatenate, so each maximal inactive stretch becomes one linear path.

For \(\dim P=3\), the same construction works, but an active \(Q_j\) remains its original suspended \(3\)-dimensional pasting context.

For \(P\) a point, take \(R_\sigma=P\), \(\kappa_\sigma=\mathrm{id}\), and \(\delta_\sigma=\sigma\).

## 2. Explicit comparison with the reduced coherence head

Consider a legal \(d\)-term
\[
c=\operatorname{coh}_{P,A}[\sigma],
\qquad d\in\{2,3\}.
\]

First, the factorization has the support property
\[
\bigcup_{x\in\operatorname{Var}(P)}
\operatorname{supp}\bigl(\kappa_\sigma(x)\bigr)
=
\operatorname{Var}(R_\sigma).
\tag{4}
\]
For an active column this follows from retaining all its variables. For an inactive column, the lift of any of its \(1\)-variable images traverses the whole path \(C_{w_j}\), hence uses every edge and vertex of that path. For an empty path it uses its point.

We must also check that \(A[\kappa_\sigma]\) is admissible over \(R_\sigma\).

If \(A\) satisfies the coherence side condition over \(P\), both endpoints use all variables of \(P\). Equation (4) makes both substituted endpoints full in \(R_\sigma\).

If \(A\) satisfies the composition side condition, then \(\dim P=d\). Column by column, \(\kappa_\sigma\) sends the support of each \((d-1)\)-boundary of \(P\) onto the corresponding boundary support of \(R_\sigma\):

- An active column is retained.
- Each boundary of an inactive column maps to terms using its entire replacement path.

Thus the composition side condition holds when \(\dim R_\sigma=d\). If \(\dim R_\sigma<d\), both substituted boundary supports are all of \(R_\sigma\), so the coherence side condition applies instead.

Define, in \(R_\sigma\),
\[
p_\sigma=\operatorname{coh}_{P,A}[\kappa_\sigma],
\qquad
r_\sigma=
\operatorname{coh}_{R_\sigma,A[\kappa_\sigma]}[\mathrm{id}].
\]
They have literally the same type, and both have support \(\operatorname{Var}(R_\sigma)\). Hence
\[
\overline\chi_\sigma
=
\operatorname{coh}_{R_\sigma,\,
p_\sigma\to_{A[\kappa_\sigma]}r_\sigma}
[\mathrm{id}]
\]
is legal. Substitution gives the requested comparison:
\[
\boxed{
\chi_\sigma=\overline\chi_\sigma[\delta_\sigma]:
\operatorname{coh}_{P,A}[\sigma]
\longrightarrow
\operatorname{coh}_{R_\sigma,A[\kappa_\sigma]}[\delta_\sigma].
}
\tag{5}
\]

This is a \(3\)-term when \(d=2\), and a **\(4\)-term when \(d=3\)**. Its boundaries retain their exact original syntax.

## 3. Stability under substitution

Let
\[
\Gamma'\vdash\rho:\Gamma,
\]
where \(\Gamma'\) also has dimension at most \(2\) and an acyclic generating \(1\)-graph.

Recompute the construction for \(\sigma[\rho]\). There is a canonical substitution
\[
R_{\sigma[\rho]}\vdash
\lambda_{\sigma,\rho}:R_\sigma
\]
satisfying
\[
\boxed{
\begin{aligned}
\delta_\sigma[\rho]
&=\lambda_{\sigma,\rho}[\delta_{\sigma[\rho]}],\\
\kappa_{\sigma[\rho]}
&=\kappa_\sigma[\lambda_{\sigma,\rho}].
\end{aligned}}
\tag{6}
\]

Here is its complete definition. Retain the original column cuts when identifying the restrictions of the substitutions.

An inactive column remains inactive after \(\rho\), because substituting for variables of dimensions \(0\) and \(1\) cannot introduce a \(2\)-variable. There are therefore three cases:

| Status for \(\sigma\) | Status for \(\sigma[\rho]\) | Restriction of \(\lambda_{\sigma,\rho}\) |
|---|---|---|
| Active | Active | Structural renaming of the retained original column |
| Active | Inactive | The new literal lift \(\theta_j\) |
| Inactive | Inactive | Exact path lifts of the substituted old path edges |

For the last case, write the old path as
\[
w=e_1\cdots e_m,
\qquad
\pi(e_i[\rho])=w_i.
\]
The new path is \(w_1\cdots w_m\). Send the old vertex at position \(i\) to the new vertex at position
\[
|w_1|+\cdots+|w_i|.
\]
Send the old formal edge labeled by \(e_i\) to the exact lift of the term \(e_i[\rho]\) along the interval corresponding to \(w_i\). Empty \(w_i\) are allowed.

The first equation in (6) follows immediately from these assignments.

For the second equation, active new columns give equality directly. On an inactive new column, both sides are substitutions into the new path context. Their substitutions along its injective path labeling are equal, by the first equation and (3). That labeling reflects syntactic equality, so the substitutions themselves are equal. **Injectivity is used only on this path context; \(\delta_{\sigma[\rho]}\) need not be injective globally.**

Fixing positional names for paths and the glued contexts makes these literal equations. The same argument gives
\[
\boxed{
\begin{aligned}
\lambda_{\sigma,\mathrm{id}}&=\mathrm{id},\\
\lambda_{\sigma,\rho[\tau]}
&=
\lambda_{\sigma,\rho}
\bigl[\lambda_{\sigma[\rho],\tau}\bigr].
\end{aligned}}
\tag{7}
\]
For the composition equation, a column remains active throughout, or becomes inactive at one stage and remains inactive. In the latter case, equality is reflected by the final injective path labeling.

### Coherence of the head comparisons

The construction also gives
\[
\bigcup_{x\in\operatorname{Var}(R_\sigma)}
\operatorname{supp}\bigl(\lambda_{\sigma,\rho}(x)\bigr)
=
\operatorname{Var}(R_{\sigma[\rho]}).
\tag{8}
\]
The active cases follow as before. In the inactive-to-inactive case, the paths of the substituted old edges concatenate to the entire new path.

Write
\[
R'=R_{\sigma[\rho]},\qquad \lambda=\lambda_{\sigma,\rho}.
\]
In \(R'\), put
\[
p=p_{\sigma[\rho]},\qquad
q=r_\sigma[\lambda],\qquad
r=r_{\sigma[\rho]}.
\]
Equation (6) gives \(p_\sigma[\lambda]=p\). The terms \(p,q,r\) have the same type and full support in \(R'\). Consequently,
\[
\zeta_{\sigma,\rho}
=
\operatorname{coh}_{R',\,q\to r}[\mathrm{id}]
\tag{9}
\]
compares the old reduced head, transported to \(R'\), with the newly reduced head.

The two reduction paths
\[
\overline\chi_\sigma[\lambda]*_d\zeta_{\sigma,\rho},
\qquad
\overline\chi_{\sigma[\rho]}
\]
are parallel and full in \(R'\). Therefore
\[
\boxed{
\Theta_{\sigma,\rho}
=
\operatorname{coh}_{R',\,
\bigl(\overline\chi_\sigma[\lambda]*_d\zeta_{\sigma,\rho}\bigr)
\to\overline\chi_{\sigma[\rho]}}
[\mathrm{id}]
}
\tag{10}
\]
is legal.

For a \(3\)-dimensional head, (9) is a \(4\)-cell and (10) is a \(5\)-cell. Substituting \(\delta_{\sigma[\rho]}\) gives their versions in \(\Gamma'\).

Further comparisons between parallel iterated reduction terms are obtained by the same rule over the final refined pasting context: equations (7) identify their substituted boundaries, and (8) preserves full support. This concerns the reductions constructed above; it makes no assertion about arbitrary ambient \(3\)-terms.

## 4. A \(4\)-cell for a nonidentity whisker and vertical composition

There is also an explicit compatibility term for arbitrary \(3\)-cells in a vertical sequence. This construction does not require acyclicity.

Let
\[
V_m=
\bigl(
a,b;\ f_0,\ldots,f_m:a\to b;\
\alpha_i:f_{i-1}\Rightarrow f_i
\bigr),
\qquad m\geq1,
\]
and append an edge \(e:b\to c\). Set
\[
P_m=V_m\vee_0D^1.
\]

Choose the vertical composite by
\[
C_m^2(\alpha_1,\ldots,\alpha_m)
=
\operatorname{coh}_{V_m,\,f_0\to f_m}[\mathrm{id}].
\]
Choose right whiskering \(W_e^2(\alpha)=\alpha*_0e\) by the composition rule over \(D^2\vee_0D^1\), with exact \(1\)-boundaries \(f*_0e\) and \(g*_0e\).

The two terms
\[
W_e^2\bigl(C_m^2(\alpha_i)\bigr),
\qquad
C_m^2\bigl(W_e^2(\alpha_i)\bigr)
\]
are parallel and full in \(P_m\). Define
\[
D_m=
\operatorname{coh}_{P_m,\,
W_e^2(C_m^2(\alpha_i))
\to C_m^2(W_e^2(\alpha_i))}
[\mathrm{id}].
\tag{11}
\]

Now replace each \(\alpha_i\) by
\[
\alpha_i^-,\alpha_i^+:f_{i-1}\Rightarrow f_i,
\qquad
\eta_i:\alpha_i^-\Rrightarrow\alpha_i^+.
\]
The resulting context
\[
P_m^\uparrow
=
\bigl(D^3\vee_1\cdots\vee_1D^3\bigr)\vee_0D^1
\]
is a globular pasting context.

Define \(C_m^3(\eta_i)\) by the composition rule over the displayed sum of \(3\)-discs, with exact boundary
\[
C_m^2(\alpha_i^-)\Rrightarrow C_m^2(\alpha_i^+).
\]
Similarly, define \(W_e^3(\eta)\) by the composition rule over \(D^3\vee_0D^1\), with boundary
\[
W_e^2(s_2\eta)\Rrightarrow W_e^2(t_2\eta).
\]

Let \(D_m^\pm\) denote (11) with \(\alpha_i\) replaced by \(\alpha_i^\pm\). The terms
\[
\begin{aligned}
L_m
&=
W_e^3\bigl(C_m^3(\eta_i)\bigr)
*_2D_m^+,\\
R_m
&=
D_m^-*_2C_m^3\bigl(W_e^3(\eta_i)\bigr)
\end{aligned}
\]
are literally parallel. Their common source and target are
\[
W_e^2(C_m^2(\alpha_i^-)),
\qquad
C_m^2(W_e^2(\alpha_i^+)).
\]
Both use every \(\eta_i\) and \(e\), and hence every variable of \(P_m^\uparrow\). Thus
\[
\boxed{
\Omega_m=
\operatorname{coh}_{P_m^\uparrow,\,L_m\to R_m}[\mathrm{id}]
}
\tag{12}
\]
is a \(4\)-term.

One may substitute arbitrary parallel \(2\)-terms for \(\alpha_i^\pm\), arbitrary \(3\)-terms for \(\eta_i\), and any \(1\)-term for \(e\). In particular, the \(\eta_i\) may be the square normalizers from §2(10).

Left whiskering uses
\[
D^1\vee_0V_m,\qquad
D^1\vee_0(D^3\vee_1\cdots\vee_1D^3),
\qquad
W_e^k(t)=e*_0t,
\]
with the same formulas (11)–(12). Thus the comparison is available for nonidentity paths on either side.

## 5. Consequences and the remaining cube step

The factorization applies to the two-square cylinder: its generating \(1\)-graph is acyclic. It replaces every inactive column by its actual path, with the exact refinement equations (6)–(7) and the comparisons (5), (9), and (10).

For the cube hemisphere, a more specific restriction follows. Give a vertex \((i,j,k)\) height
\[
h(i,j,k)=i+j+k.
\]
Every edge increases height by \(1\), while each face generator has \(0\)-boundary of height difference \(2\). Hence any active column has endpoint height difference at least \(2\). The endpoint differences of successive columns add, and the whole cube has height difference at most \(3\). Therefore an arity substituted into the hemisphere has **at most one active \(0\)-column**.

For a \(2\)-dimensional arity, after removing point factors, the reduced arity consequently has one of the forms
\[
V,\qquad D^1\vee_0V,\qquad V\vee_0D^1,
\]
where \(V\) is a vertical \(2\)-chain. If the substitution uses all three hemisphere faces, its active column must span height \(0\) to height \(3\), so all other columns are point-supported.

This still leaves the essential problem: the terms assigned to the \(2\)-variables of \(V\) may themselves be arbitrary composites involving the three faces and their edge whiskers. Equations (6)–(10) preserve those active assignments; they do not normalize them.

To prove the cube contraction, one must additionally compare the fixed normalizer of a substituted \(2\)-term with the normalizer obtained by first normalizing its \(2\)-inputs and then composing. Formula (12) handles one interaction in that comparison. It does not handle every active-column coherence head. In particular, replacing a \(2\)-variable in a vertical chain by a whiskered \(2\)-term replaces its primitive \(1\)-boundaries by composite \(1\)-terms; the resulting declarations need not form a globular pasting context, so a direct coherence over those declarations is unavailable.

Thus the construction proves the substitution-stable inactive-column factorization in Question 2 and its explicit coherence terms. **The contraction of arbitrary cube loops and the RC statements in Question 3 remain unproved here.**
