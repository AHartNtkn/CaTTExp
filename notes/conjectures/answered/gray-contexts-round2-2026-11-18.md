# Problem: composites of molecules in CaTT (Gray contexts), round 2

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first. Round 1 and its verified answer are archived in `answered/gray-contexts-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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

## 3. What remains, and why

In dimension 2, the runs of cells with no top variable live over a single path, and the coherence rule settles them. In dimension 3 they live over a 2-dimensional context, such as S, which is not a pasting context.

Item 5 settles S except in one case. Both parallel 3-terms have strict 2-boundary F, and at least one of them is a composite over a **3-dimensional** arity, or is a coherence whose middle-column 2-terms `τ(ξ_k)` are arbitrary.

The Squier-style route needs one normalization 3-cell `ν_P : P → N(P)` for each 2-term P with image F, chosen once and for all (Theorem A gives one). It must be compatible, up to 4-cells, with every whiskered elementary 3-cell b, i.e. `ν_{src b}` must be connected to `b ∗₂ ν_{tgt b}`. Item 4 settles the part of this inside F-free runs. So the remaining compatibility is with `∗₁`-composition by 2-terms that contain F.

RC(3) fails in general. In `(x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell and the identity are expected not to be connected, since they give a non-zero class in π₃(S²). (This is a sketch, not checked in detail.) So any proof must use some acyclicity of the context, and which notion it needs is part of question 3.

## 4. Questions

Each question asks for explicit CaTT terms, built with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: the F-boundary case of the lax square.** Let `α, β : t → t′` be parallel 3-terms of S with `π(t) = π(t′) = F`. Construct a 4-term `α → β`.
   - *Smaller first step:* take α and β to be coherences over 2-dimensional arities. By item 5, both reduce to coherences over vertical 2-chains Q, Q′ whose middle 2-terms are arbitrary. Connect them.
   - *Equivalent form:* exhibit a choice of `ν_P` for 2-terms P with image F, and prove that `ν_{u ∗₁ W}` is connected to `(ν_u ∗₁ ν_W) ∗₂ (flattening coherence)` whenever W contains F.
2. **The Gray cube.** Let `U = D¹ ⊗ D¹ ⊗ D¹`, presented with hexagon composites. Prove that every X-free 3-term `H : ⌈∂⁻U⌉ → ⌈∂⁻U⌉` is connected to the identity. By item 6, this is RC(3) for 3-loops over the three-face negative hemisphere. This gives uniqueness in G(3) for the cube.
3. **RC(3) for acyclic contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule, or its skeleta. Or prove it for every finite Steiner loop-free computad, and say which hypothesis the proof uses.
4. **G(n) for all n.** Prove RC(n), or the weaker G(n), for such contexts.
   - Chanavat's contractible subdivision poset (Thm 2.52, non-atoms) indexes composites but does not construct them.
   - A proof must give a CaTT composite for each subdivision, comparisons for refinements, and higher comparisons for chains of refinements.
   - It must also show that **arbitrary** CaTT composites are controlled by those comparisons.

## 5. What counts as a solution

Any of the following counts:
- explicit terms for question 1 or 2;
- a proof of RC(3) or RC(n) on acyclic contexts;
- a counterexample: an acyclic context with two parallel terms of equal strict image and no term between them;
- a published reference.

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

**I have a partial construction for Question 1, with arbitrary substituted 2-terms, but it requires an additional syntactic hypothesis: both the arity and the coherence type must be literal suspensions.** A suspended arity alone is insufficient.

I do not obtain the unrestricted first step, the full F-boundary case, or Questions 2–4. The construction below identifies a subclass that is settled and gives an explicit example explaining why the hom-category argument does not settle the rest.

## 1. A restricted version of Question 1

Write \(\Sigma\) for **syntactic suspension**, acting on contexts, types and terms.

### Proposition

Let \(\Gamma\) be any CaTT context, and fix \(a,b:\star\) in \(\Gamma\). Suppose
\[
\alpha=\operatorname{coh}_{\Sigma C,\Sigma A}[\tau],
\qquad
\beta=\operatorname{coh}_{\Sigma C',\Sigma A'}[\tau']
\]
are parallel \(3\)-terms with \(0\)-source \(a\) and \(0\)-target \(b\), where \(C,C'\) are \(1\)-dimensional path contexts. The one-vertex path context is also allowed.

Here the hypothesis concerns the displayed syntax:

- the arities are \(\Sigma C,\Sigma C'\);
- the coherence types, including their boundary terms, are \(\Sigma A,\Sigma A'\).

The substituted \(2\)-terms \(\tau(\xi)\) and \(\tau'(\xi')\) are arbitrary.

Then one can construct a CaTT \(4\)-term
\[
\chi_{\alpha,\beta}:\alpha\longrightarrow\beta.
\]

This applies to the square \(S\), but requires no acyclicity assumption on \(\Gamma\).

### Construction

Let
\[
H=\operatorname{Hom}_{F_{\mathrm w}(\Gamma)}(a,b).
\]
Benjamin–Markakis prove that \(H\) is free on a computad of indecomposable cells. Their construction sends a hom coherence to a global coherence with both its arity and its type suspended. This is Theorem 4.5 and the calculation in its proof. [api.repository.cam.ac.uk](https://api.repository.cam.ac.uk/server/api/core/bitstreams/bca694d1-41be-4afb-b058-ba7369bdca83/content?utm_source=chatgpt.com)

Consequently, the displayed terms desuspend to hom \(2\)-terms
\[
\bar\alpha=\operatorname{coh}_{C,A}[\bar\tau],
\qquad
\bar\beta=\operatorname{coh}_{C',A'}[\bar\tau'].
\]

**Step 1: reduce to a finite graph of hom generators.**

Every value of \(\bar\tau\) and \(\bar\tau'\) has dimension at most \(1\). Decompose these finitely many cells into terms of the hom computad. Only finitely many generators of dimensions \(0\) and \(1\) are used.

Let \(K\) be the finite graph consisting of those generators and their endpoints. Then \(\bar\alpha,\bar\beta\) are terms over \(K\). In particular, **neither uses a hom \(2\)-variable**.

There is no restriction here on the original substituted \(2\)-terms: they become arbitrary hom \(1\)-terms, whose decompositions can use hom \(1\)-generators.

**Step 2: unfold their common path.**

Let \(\bar t\) be their common source, a hom \(1\)-term, and let
\[
w=e_1\cdots e_r
\]
be its image in the free category on \(K\).

Both hom \(2\)-terms have strict image \(1_w\). Apply the path-chain lifting result from your §2(4), now in the hom computad. It gives:

- the path context \(C_w\);
- a substitution \(\eta\) assigning its edge variables to \(e_1,\ldots,e_r\);
- parallel, full-support \(2\)-terms
  \[
  \widehat\alpha,\widehat\beta:B_w
  \]
  over \(C_w\), satisfying
  \[
  \widehat\alpha[\eta]=\bar\alpha,
  \qquad
  \widehat\beta[\eta]=\bar\beta.
  \]

The lifts use the same chosen lifts of the common source and target. Thus their parallelism holds syntactically before substitution.

If a generator appears more than once in \(w\), the corresponding positions of \(C_w\) are distinct variables with equal substitution images. If \(w\) is empty, \(C_w\) has one vertex.

**Step 3: suspend the lifted comparison.**

Define the substitution
\[
\Gamma\vdash\delta_w:\Sigma C_w
\]
as follows:

- its two \(0\)-variables map to \(a,b\);
- its \(1\)-variables map to the global \(1\)-terms labeling the vertices of \(w\);
- its \(2\)-variables map to the global \(2\)-terms labeling the edges of \(w\).

The required term is
\[
\boxed{
\chi_{\alpha,\beta}
=
\operatorname{coh}_{
 \Sigma C_w,\,
 \Sigma\widehat\alpha
 \;\to_{\Sigma B_w}\;
 \Sigma\widehat\beta
}[\delta_w].
}
\]

This is well-typed because:

1. \(\Sigma C_w\) is a pasting context;
2. \(\Sigma\widehat\alpha\) and \(\Sigma\widehat\beta\) are parallel;
3. both have full support in \(\Sigma C_w\);
4. the hom-operation formula gives the syntactic equalities
   \[
   (\Sigma\widehat\alpha)[\delta_w]=\alpha,
   \qquad
   (\Sigma\widehat\beta)[\delta_w]=\beta.
   \]

Therefore
\[
\Gamma\vdash\chi_{\alpha,\beta}:\alpha\to\beta.
\]

The argument uses the hom computad’s own path decomposition. It does **not** identify its strictification with the hom of the global strictification.

## 2. Why a vertical-chain arity is insufficient

The extra hypothesis on the coherence type cannot be inferred from the arity. The following explicit example also shows why applying \(\mathrm{RC}(2)\) to the hom computad does not prove general \(\mathrm{RC}(3)\).

Work first over the \(2\)-disk
\[
D_2=
(x,y:\star,\ f,g:x\to y,\ A:f\to g).
\]

For a \(1\)-term \(h:x\to y\), choose the two disk coherences
\[
\lambda_h:(1_x*_0h)\to h,
\qquad
\lambda_h^{-1}:h\to(1_x*_0h).
\]
The superscript here denotes the chosen reverse coherence; no definitional inverse equation is being asserted.

Define
\[
W(A)=
\bigl(\lambda_f^{-1}*_1(1_{1_x}*_0A)\bigr)
*_1\lambda_g
:
f\to g.
\]

Both \(W(A)\) and \(A\) use every variable of \(D_2\). Hence the following are valid \(3\)-terms:
\[
r=\operatorname{coh}_{D_2,\ A\to W(A)}[\mathrm{id}],
\qquad
\ell=\operatorname{coh}_{D_2,\ W(A)\to A}[\mathrm{id}].
\]
Put
\[
\kappa=r*_2\ell:A\to A.
\]

### The arities suspend, but the types do not

We have
\[
D_2=\Sigma D_1.
\]
Nevertheless, the types \(A\to W(A)\) and \(W(A)\to A\) are not literal suspensions. The expression \(W(A)\) uses a \(0\)-composition operation, and syntactic suspension increases every composition direction by one.

In the Benjamin–Markakis hom structure, a decomposable cell has the syntax
\[
\operatorname{coh}_{\Sigma P,\Sigma B}[\sigma].
\]
Both the arity and the type are suspended. Injectivity of the coherence constructor therefore prevents \(r\) and \(\ell\) from being hom coherences. They are indecomposable hom \(2\)-generators. [api.repository.cam.ac.uk](https://api.repository.cam.ac.uk/server/api/core/bitstreams/bca694d1-41be-4afb-b058-ba7369bdca83/content?utm_source=chatgpt.com)

Let
\[
\lambda:H\longrightarrow F_{\mathrm{str}}(\Omega D_2)
\]
denote the hom computad’s own strictification. Then
\[
\lambda(\kappa)\neq\lambda(1_A).
\]
Indeed, the former uses the two generating hom \(2\)-cells corresponding to \(r,\ell\), while the latter is an identity. Counting generating \(2\)-cells distinguishes them in the free strict category.

### Yet the global \(4\)-filler exists

Directly in CaTT,
\[
\boxed{
\operatorname{coh}_{D_2,\ \kappa\to1_A}[\mathrm{id}]
:
\kappa\to1_A
}
\]
is valid: its two boundary terms are parallel and have full \(D_2\)-support.

Substitute
\[
x\mapsto x^-,
\quad
y\mapsto y^+,
\quad
f\mapsto p,
\quad
g\mapsto q,
\quad
A\mapsto F.
\]
This gives the same example in the lax square, with both \(3\)-terms having the literal boundary \(F\to F\).

Thus:

- the global strict images agree;
- a global \(4\)-term connects them;
- their images under the hom computad’s strictification differ.

This is **not** a counterexample to Question 1. It is a counterexample to the proposed shortcut
\[
\text{equal global strict images}
\ \Longrightarrow\
\text{equal strict images in the free hom computad}.
\]

It also shows that the additional restriction in §1 is substantive, even when the arity is a single \(2\)-disk.

## 3. A reference locating the remaining normalization problem

A relevant source absent from the supplied list is Alexander Rice’s thesis, [*A type-theoretic approach to semistrict higher categories*](https://arxiv.org/abs/2502.17068).

Theorem 4.5.3 proves rehydration over pasting contexts. Section 4.5.2, “Towards generalised rehydration,” explicitly discusses extending it to arbitrary contexts. It identifies the missing normalizers and the need to compare different normalization choices by higher cells; it also proposes contractibility of the family of rehydrations. The section does not prove that extension. [arxiv.org](https://arxiv.org/pdf/2502.17068?utm_source=chatgpt.com)

Consequently, normalizing a term in semistrict CaTT and then appealing to a general rehydration theorem is not an established way to complete the present argument.

Similarly, the published BMOSV naturality construction covers depth at most \(1\). A proposed reduction that changes \(1\)-dimensional arguments of a \(3\)-coherence has depth \(2\), so that particular step needs an additional construction. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

The unresolved step for the approach above is therefore precise: construct boundary-preserving \(4\)-comparisons that replace arbitrary F-bearing \(3\)-terms by terms whose hom expressions use no hom \(2\)-generators. The restricted proposition supplies the final comparison once that has been done, but neither vertical-chain arities nor equal global strict images establish the required reduction.

---

## Verification of the researcher response (2026-11-18)

**Verdict: correct; partial.** It settles a restricted subclass of the F-boundary case (Question 1), shows that the "hom-computad RC(2)" shortcut cannot settle the rest, and leaves Questions 1 (unrestricted), 2, 3, 4 open. Checked step by step:

- **V1. Proposition (§1), shape of the hypothesis.** α = coh_{ΣC,ΣA}[τ] with C a 1-dimensional path context: ΣC is a vertical 2-chain, and A a type over C whose desuspension ᾱ = coh_{C,A}[τ̄] is a hom 2-term. Dimensions check (ΣA is a 3-type because A is a 2-type over C). **Confirmed.**
- **V2. Desuspension.** Relies on the Benjamin–Markakis hom theorem (cited as Thm 4.5 of a Cambridge repository document): the hom of a free weak ω-category on a computad is free on its indecomposable cells, and a decomposable hom cell is literally coh_{ΣP,ΣB}[σ]. **Not re-read** (the cited document is not on arXiv under that title; the statement matches what the project already uses from BM in `free-objects.md`). Everything below is conditional on it at statement level.
- **V3. Step 1.** Values of τ̄ have dimension ≤ 1, so they use only finitely many hom generators of dimension ≤ 1; ᾱ, β̄ are terms over a finite graph K. **Confirmed** (support of an n-cell in a free computad has dimension ≤ n).
- **V4. Step 2.** Uses known item 4 (terms without 2-variables pull back to the chain C_w of their path, with chosen common lifts of source and target). Repeated generators handled by distinct variables with equal images. **Confirmed** as an application of item 4.
- **V5. Step 3.** coh_{ΣC_w, Σα̂ → Σβ̂}[δ_w] is well-typed: ΣC_w is a pasting context; suspension preserves parallelism and full support; (Σα̂)[δ_w] = α is the BM hom-operation formula (V2). **Confirmed, conditional on V2.**
- **V6. §2 example.** W(A) = (λ_f⁻¹ ∗₁ (1_{1_x} ∗₀ A)) ∗₁ λ_g : f → g has full support in D₂; r, ℓ are valid coherences; κ = r ∗₂ ℓ : A → A. The types contain a ∗₀-composite, so they are not literal suspensions, and injectivity of `coh` makes r, ℓ indecomposable hom generators; κ ≠ 1_A in the hom strictification (count r-generators). coh_{D₂, κ → 1_A}[id] is a valid global 4-term, and the substitution x ↦ x⁻, y ↦ y⁺, f ↦ p, g ↦ q, A ↦ F transports it to S. **Confirmed.** So "equal global strict image ⇒ equal hom strict image" is false, and the restriction in §1 is substantive.
- **V7. §3 references.** Rice, arXiv 2502.17068: Thm 4.5.3 (rehydration over ps-contexts) and §4.5.2 "Towards generalised rehydration" (open; identifies the missing normalisers, with the scalar example α ∗₀ id(x)) read and **confirmed**. BMOSV, arXiv 2501.11620: the construction requires depth ≤ 1, higher depth "beyond our present work". **Confirmed.**

**Consequences.** RC(3) for S now holds for parallel 3-terms that are both literally suspended coherences over vertical chains (any Γ, no acyclicity). The remaining step is precise: boundary-preserving 4-comparisons replacing an arbitrary F-bearing 3-term by one whose hom expression uses no hom 2-generators. Global coherences such as r, ℓ (types with ∗₀-whiskers) are exactly what such a reduction must absorb; for those, global full-support coherences over D₂ still exist, so the example is not an obstruction. Follow-up prompt: `answered/gray-contexts-r3-2026-11-18.md` (round 3).
