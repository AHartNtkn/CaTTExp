# Problem: composites of molecules in CaTT (Gray contexts), round 3

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Rounds 1 and 2 and their verified answers are archived in `answered/gray-contexts-2026-11-18.md` and `answered/gray-contexts-round2-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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

## 3. What remains

RC(3) for the lax square is settled (item 10). In larger acyclic contexts, the columns of an arity that do not carry the active 2-generator may carry nonidentity paths, so item 10's point-support step fails. RC(3) fails for loopy contexts such as (x, a : 1_x → 1_x) (π₃(S²) = ℤ: the weak free object groupoidifies to S², the strict one to K(ℤ,2)), so a proof must use some acyclicity.

## 4. Questions

1. **The Gray cube (smallest open case).** Let U = D¹ ⊗ D¹ ⊗ D¹, presented with hexagon composites. Prove that every X-free 3-term H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉ is connected to the identity (RC(3) for 3-loops over the three-face negative hemisphere). Here the three faces are lax squares glued along edges, so item 10 applies to each face separately but not to composites that whisker one face by edges of another.
2. **Beyond point-supported columns.** Generalise item 10's active-column factorisation to contexts where the inactive columns carry nonidentity paths, e.g. two lax squares glued along an edge (the cylinder of x → y → z). Is there a substitution-stable factorisation through a "horizontal word of vertical chains"?
3. **RC(3) and RC(n) for acyclic contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule (or every finite Steiner loop-free computad), and say which hypothesis the proof uses; then RC(n), or the weaker G(n).
4. **The hom-level question.** Is every indecomposable hom 2-generator of a loop-free context whose strict image is an identity connected, by a global 4-term, to a composite of decomposable hom cells (item 8 gives such generators)?

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

**The reduction in Q1 is false for its first instance \(r[F]:F\to W(F)\).** No literally suspended coherence over a vertical chain, nor any composite of such using ordinary CaTT compositions and whiskerings, has that boundary.

The obstruction already occurs over \(D_2\), so it is independent of acyclicity. It does **not** refute RC(3): it shows that the proposed class of normal forms is too restrictive.

Q2 needs a distinction. With Benjamin–Markakis’s literal meaning of “decomposable,” it has an explicit positive answer in every context. If it means recursively eliminating all hom \(2\)-generators, it fails for the same reason as Q1.

## 1. An invariant of the proposed normal forms

Write \(\mathcal W(\Gamma)\) for the free weak \(\omega\)-category of CaTT terms. For each pair of \(0\)-cells \(a,b\), Benjamin–Markakis identify
\[
H_{a,b}=\operatorname{Hom}_{\mathcal W(\Gamma)}(a,b)
\]
as free on a computad \(D_{a,b}\) whose generators are its indecomposable cells. Their proof identifies decomposable hom cells with global terms
\[
\operatorname{coh}_{\Sigma P,\Sigma B}[\sigma],
\]
where **both the arity and the type are literal suspensions**. This is Definition 9 and Proposition 10 of the arXiv version of *Hom \(\omega\)-categories of a computad are free*. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

Consider the intrinsic strictification
\[
\rho_{a,b}:H_{a,b}\longrightarrow F_{\mathrm{str}}(D_{a,b}).
\]
This is different from your global strictification \(\pi\).

For a global \(2\)-term \(t\) with \(0\)-boundary \((a,b)\), let
\[
w(t)=\rho_{a,b}(t)
\]
at hom dimension \(1\). Thus \(w(t)\) is a path in the free category on the \(1\)-generators of \(D_{a,b}\). Define
\[
L(t)=|w(t)|.
\]

These are ordinary directed paths, with no cancellation of generators. In particular:

- An indecomposable hom \(1\)-cell has length \(1\).
- A hom identity \(1\)-cell has length \(0\).
- Global vertical composition satisfies
  \[
  L(u*_1v)=L(u)+L(v).
  \]

An arbitrary hom \(2\)-generator can connect different words. We are not interpreting all of \(H_{a,b}\) in a locally discrete category.

### Suspended chain coherences preserve the word

Suppose
\[
\theta=\operatorname{coh}_{\Sigma C,\Sigma A}[\tau]
\]
is one of the proposed \(3\)-dimensional normal forms, with \(C\) a \(1\)-dimensional path context.

It desuspends to a hom \(2\)-coherence over \(C\). Its substitution supplies only hom \(0\)- and \(1\)-cells: there are no hom \(2\)-variables in \(C\). In the free strict \(\omega\)-category on that path, this coherence is an identity \(2\)-cell. Substituting the words of the supplied hom \(1\)-cells therefore gives
\[
w(s_2\theta)=w(t_2\theta).
\tag{1}
\]
Consequently,
\[
L(s_2\theta)=L(t_2\theta).
\tag{2}
\]

### Ordinary compositions and whiskerings preserve equality of lengths

Let \(\mathcal E\) be the class generated by these suspended chain coherences and identity \(3\)-cells, using ordinary binary compositions and whiskerings by lower-dimensional terms. Then
\[
\boxed{\gamma\in\mathcal E
\quad\Longrightarrow\quad
L(s_2\gamma)=L(t_2\gamma).}
\tag{3}
\]

Here “ordinary” refers to the CaTT binary operations with recursively specified boundaries, as in Benjamin–Markakis §3.1. For example,
\[
s_2(\gamma*_k\delta)=s_2\gamma*_k s_2\delta
\qquad(k<2),
\]
and likewise for targets. Their mixed-dimensional operations have the corresponding whiskering boundary formulas. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

To prove (3), proceed by induction on the expression defining \(\gamma\).

- **Suspended chain coherence:** use (1).
- **Identity:** its two \(2\)-boundaries are equal.
- **Composition along \(2\):** equality of lengths passes through the common intermediate \(2\)-boundary.
- **Composition along \(1\):** lengths add on both boundaries.
- **Composition along \(0\):** both boundaries are ordinary horizontal composites of \(2\)-terms. Each such composite is an indecomposable hom \(1\)-cell, hence has length \(1\).

For the last assertion, the outer coherence of a horizontal binary composite has arity \(D_2\vee D_2\), with three \(0\)-variables. That arity is not a suspension. Substitution does not change the arity recorded in the coherence constructor, even when some arguments are identities. Thus the resulting term cannot be a suspended hom operation.

Mixed-dimensional whiskerings obey the same argument: whiskering along \(1\) adds the same length to each boundary, while whiskering along \(0\) gives length \(1\) on each boundary. Allowing inverses of the resulting \(3\)-cells also preserves (3), since inversion swaps the boundaries.

Notice that equality of the whole words need not survive ambient \(0\)-composition. Equality of their lengths does, which is sufficient here.

## 2. Apply the invariant to \(r[F]\)

Put \(a=x^-\), and write
\[
h(F)=1_{1_a}*_0F.
\]
Your term is
\[
W(F)=\bigl(\lambda_p^{-1}*_1h(F)\bigr)*_1\lambda_q.
\]

First, \(F\) is a global variable, so it is an indecomposable hom \(1\)-cell:
\[
L(F)=1.
\tag{4}
\]

Second, \(h(F)\) is an ordinary horizontal composite. By the preceding argument,
\[
L(h(F))=1.
\tag{5}
\]

Finally,
\[
\lambda_p^{-1}:p\longrightarrow 1_a*_0p,
\qquad
\lambda_q:1_a*_0q\longrightarrow q.
\]
Their respective endpoints are **syntactically distinct** global \(1\)-terms. These are distinct hom \(0\)-cells, and intrinsic hom strictification does not identify hom \(0\)-cells. Therefore neither corresponding path can be empty:
\[
L(\lambda_p^{-1})\geq1,
\qquad
L(\lambda_q)\geq1.
\tag{6}
\]

Using additivity,
\[
\begin{aligned}
L(W(F))
&=L(\lambda_p^{-1})+L(h(F))+L(\lambda_q)\\
&\geq3.
\end{aligned}
\tag{7}
\]

Equations (4) and (7) contradict the necessary condition (3) for any proposed normal form with boundary \(F\to W(F)\). Hence
\[
\boxed{\text{There is no }\alpha'\in\mathcal E
       \text{ with }\alpha':F\to W(F).}
\]

In particular, there can be no \(4\)-term \(r[F]\to\alpha'\) of the requested kind: the required target term does not exist.

The argument applies verbatim to
\[
r:A\to W(A)
\]
over \(D_2\), replacing \(p,q,F\) by \(f,g,A\). Thus even a globular pasting context does not satisfy this elimination property.

This is compatible with coherence over \(D_2\). For every term \(r':A\to W(A)\) over \(D_2\), the typed supports of \(r\) and \(r'\) are all of \(D_2\), so
\[
\operatorname{coh}_{D_2,\;r\to r'}[\mathrm{id}]
\]
exists. The failure is the absence of a representative in the proposed restricted class, not the absence of comparisons between existing representatives.

Allowing arbitrary additional coherences with nonsuspended types would escape the invariant, but would also admit the hom \(2\)-generators that the proposed reduction is meant to eliminate.

## 3. Literal Q2 has an explicit answer in every context

“Decomposable hom cell” is a condition on the outer constructor. It does not say that the substitution arguments recursively avoid indecomposable hom cells.

For any global \(3\)-term
\[
\alpha:u\to v,
\]
define
\[
J(\alpha)=\alpha*_2 1_v,
\qquad
B(\alpha)=J(\alpha)*_2 1_v.
\tag{8}
\]

Both factors in the displayed expression for \(B(\alpha)\) are decomposable hom \(2\)-cells:

- \(J(\alpha)\) is a hom \(2\)-composition, hence has a suspended outer coherence;
- \(1_v\) is a hom identity \(2\)-cell, also a suspended coherence.

There is an explicit global \(4\)-term
\[
E_\alpha:\alpha\to B(\alpha).
\]

To construct it, take the standard pasting context
\[
D_3=
\bigl(
x,y:\star,\;
f,g:x\to y,\;
u,v:f\to g,\;
z:u\to v
\bigr)
\]
and form
\[
B(z)=(z*_2 1_v)*_2 1_v.
\]
The terms \(z\) and \(B(z)\) are parallel and satisfy
\[
\operatorname{supp}(z:u\to v)
=
\operatorname{supp}(B(z):u\to v)
=
\operatorname{Var}(D_3).
\]
The coherence rule therefore gives
\[
\boxed{
E_\alpha=
\operatorname{coh}_{D_3,\;z\to_{u\to v}B(z)}
[\sigma_\alpha]
:\alpha\to B(\alpha),
}
\tag{9}
\]
where the disk substitution is
\[
\begin{aligned}
\sigma_\alpha(x)&=s_0\alpha,&
\sigma_\alpha(y)&=t_0\alpha,\\
\sigma_\alpha(f)&=s_1\alpha,&
\sigma_\alpha(g)&=t_1\alpha,\\
\sigma_\alpha(u)&=s_2\alpha,&
\sigma_\alpha(v)&=t_2\alpha,\\
\sigma_\alpha(z)&=\alpha.
\end{aligned}
\]

This uses only a coherence over a pasting context and substitution. It requires neither acyclicity nor any assumption on \(\pi(\alpha)\).

It does not eliminate \(\alpha\). If \(\alpha\) is an indecomposable hom \(2\)-generator, it remains a substitution argument in \(J(\alpha)\) and \(B(\alpha)\). Indeed, intrinsic hom strictification gives
\[
\rho_2(B(\alpha))=\rho_2(\alpha),
\]
by strict unitality.

The dimension distinction explains why this does not supply Q1’s normal form:

- A suspended chain coherence has arity \(\Sigma C\) with \(\dim C=1\). Its substitution supplies no hom \(2\)-cell.
- The composition defining \(J(\alpha)\) has arity \(\Sigma P\) with \(\dim P=2\). Its substitution supplies \(\alpha\) itself as a hom \(2\)-cell.

Thus the literal Q2 is true by (9), while its intended recursive elimination reading is false by the boundary obstruction.

## 4. Consequences for the remaining questions

The claimed equivalence between Q1 and Q2 does not hold. Neither formulation, as written, gives the missing RC(3) argument:

- Recursive elimination into suspended chain coherences can fail because no term in that class has the required boundary.
- Making the outer constructor decomposable always works, but retains the original hom \(2\)-generator as an argument.

A normalization argument for RC(3) must therefore allow boundary-adjusting \(3\)-terms such as \(r[F]\) among its normalizing data. It cannot require every representative to be built solely from suspended chain coherences.

Q3 and Q4 remain unresolved here. The invariant above does not obstruct the cube’s \(3\)-loops, whose source and target are already the same \(2\)-term, and it supplies no counterexample to RC(3) or \(G(n)\).


# Verification of the researcher response (2026-11-18)

**Verdict: correct, but it answers the earlier draft of this prompt.** The response's "Q1" and "Q2" are the questions of the version of `gray-contexts-r3.md` committed before 17:39 UTC (commit 34b8575): Q1 = "replace every F-boundary 3-term of S by a literally suspended coherence over a vertical chain, starting with r[F]", Q2 = "the hom-level formulation". The file was then revised (commit 790d18c) after RC(3) for the lax square was settled by another route (known item 10), and the revised file above asks Q1 = Gray cube, Q2 = beyond point-supported columns, Q3 = RC(3)/RC(n), Q4 = the hom-level question. So the response settles the old Q1 (negatively) and the current Q4 (literal reading yes, recursive reading no); **the current Q1–Q3 are unanswered** and go to round 4.

Step by step.

1. **The length invariant (§1).** Correct. By Benjamin–Markakis the hom H_{a,b} is free on a computad D_{a,b}; ρ : H_{a,b} → F_str(D_{a,b}) is a strict functor, and at hom-dimension 1 it gives paths of hom 1-generators, so L(t) = |ρ(t)| is additive under ∗₁ and is 0 exactly on hom identities. Hom 0-cells are global 1-terms and are generators, so ρ is injective on them.
   - A suspended chain coherence desuspends to a hom 2-coherence over a 1-dimensional path context C. Its image under the strict functor ρ is a coherence 2-cell over C in a strict ω-category, hence an identity, so its two 2-boundaries have equal words.
   - Under ∗₂ the length passes through the shared middle; under ∗₁ it adds on both sides.
   - Under ∗₀ both 2-boundaries are coherences over D₂ ∨ D₂ (three 0-variables, not a suspension), hence indecomposable hom 1-cells of length 1. The arity recorded in a coh term does not change under substitution, so this holds even when arguments are identities.
   - Whiskerings and inverses are handled the same way.
   
   So every γ in the class 𝓔 has L(s₂γ) = L(t₂γ).

2. **r[F] has no representative in 𝓔 (§2).** Correct:
   - L(F) = 1, since F is a variable and so a generator.
   - L(1_{1_a} ∗₀ F) = 1.
   - λ_p⁻¹ and λ_q run between syntactically distinct global 1-terms (p versus 1_a ∗₀ p, and 1_a ∗₀ q versus q), so they are non-identity hom 1-cells of length ≥ 1.
   - Hence L(W(F)) ≥ 3 ≠ 1.
   
   The same holds over D₂ for r : A → W(A). This settles the old Q1 negatively. The response notes that this is not a failure of RC(3), and I agree: coh_{D₂, r → r′} connects any two such terms. It is consistent with known item 10: the normalisers used there, ν_T : T → (κ(σT, p) · F) · κ(q, τT), already contain boundary-adjusting coherences κ that are not suspended chain coherences.

3. **The literal hom-level question (§3; current Q4).** Correct, and trivial in hindsight.
   - Over D₃ the terms z and B(z) = (z ∗₂ 1_v) ∗₂ 1_v are parallel and full, so E_α = coh_{D₃, z → B(z)}[σ_α] : α → B(α) exists for every 3-term α in every context.
   - B(α) is a ∗₂-composite, whose arity is the suspension Σ(D₂ ∨₁ D₂), so it is a decomposable hom 2-cell. Its factors α ∗₂ 1_v and 1_v are also decomposable.
   - So "connected to a composite of decomposable hom cells" holds for every context, with no acyclicity needed.
   - On the recursive reading, where no indecomposable hom 2-generator may occur anywhere, the answer is no by item 2: ρ₂(B(α)) = ρ₂(α).
   
   Either way, the hom-level question is not a route to RC(3), and round 4 drops it.

4. **What is not addressed.** The Gray cube (current Q1), factorisation beyond point-supported columns (current Q2) and RC(3)/RC(n) for acyclic contexts (current Q3). The response says explicitly that it does not settle Q3/Q4 and gives no counterexample to RC(3) or G(n).

**Consequences for D2.** Two new facts:
- The suspended-chain normal form is impossible: no class built from suspended chain coherences by ordinary compositions reaches F → W(F).
- The hom-level reformulation is either trivially true or false.

Neither affects RC(3) for the lax square, which item 10 proves with boundary-adjusting normalisers. Any normalisation proof of RC(3) on larger contexts must likewise include boundary-adjusting 3-terms. Follow-up prompt: `gray-contexts-r4-2026-11-18.md` (round 4, answered). It re-asks the current Q1–Q3 with these facts as known items.
