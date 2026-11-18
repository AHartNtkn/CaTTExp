# Free strict ω-categories with directed interchange at every level

*Self-contained problem statement. No project context needed.*

## Background

**Strict ω-categories.** In a strict ω-category, composites along a k-cell and along an l-cell (k < l) satisfy the interchange law strictly:

```
(a ∗ₗ b) ∗ₖ (c ∗ₗ d)  =  (a ∗ₖ c) ∗ₗ (b ∗ₖ d).
```

**Gray-enriched categories.** A category enriched over strict ω-categories with the (lax) Gray tensor product ⊗ is called Gray-enriched (Ara–Maltsiniotis, arXiv:1607.00668; Gepner–Heine call the ∞-version "oriented categories", arXiv:2510.10504). In such a category the interchange law is replaced, *for composition along 0-cells only*, by a directed (non-invertible) cell. For example, given 2-cells α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z, there is a 3-cell

```
(βf′) ∗₁ (gα)  ⇛  (g′α) ∗₁ (βf)
```

and nothing in the other direction. Composition along k-cells with k ≥ 1 happens inside hom ω-categories and interchanges strictly.

**Free Gray-enriched categories on pasting diagrams.** Let Γ be a globular pasting diagram, decomposed as a wedge of suspensions ΣΘ₁ ∨ … ∨ ΣΘₙ. The free Gray-enriched category on Γ has homs ν(λΘⱼ ⊗ … ⊗ λΘᵢ₊₁), Gray tensors of Steiner complexes (Steiner, HHA 2004). Its cells are therefore computable from chains, and two cells of the same dimension with the same set of generators coincide.

**The obstruction to iterating.** One would like a notion in which the interchange law is replaced by a directed cell for *every* pair k < l of composition dimensions, not just for k = 0. The obvious construction iterates Gray enrichment: categories enriched over categories enriched over …, each with its own Gray-type tensor. This fails beyond dimension 3:
- Crans showed that no monoidal biclosed structure on Gray-categories captures weak transformations;
- Bourke and Lobbia (*A skew approach to enrichment for Gray-categories*, arXiv:2212.12358) replace monoidal by skew monoidal closed structures;
- see also Bourke and Gurski, *A cocategorical obstruction to tensor products of Gray-categories*.

## The problem

Define a notion of **strict lax-interchange ω-category**: a globular set with compositions ∗ₖ, identities, strict associativity and unit laws, in which every interchange law for k < l is replaced by a directed cell, oriented consistently. The interchange cells must themselves satisfy appropriate coherence laws, e.g. with respect to further composition and to each other.

*Precise reading (corrected 2026-11-18, see the verified researcher response at the end).* The **elementary** interchanger is for (l+1)-cells a, b, c, d: an (l+2)-cell between the two composites. (An earlier version said "(l+1)-cell", which is off by one: in the Gray example, k = 0, l = 1 and the interchanger is a 3-cell.) For cells of higher dimension n > l+1, the interchanger must **not** be a raw (n+1)-cell `(a ∗ₗ b) ∗ₖ (c ∗ₗ d) → (a ∗ₖ c) ∗ₗ (b ∗ₖ d)`: such cells force every interchange law two dimensions down to hold strictly, which contradicts requirement 3. The higher instances are instead naturality comparisons whose boundaries have the lower interchangers composed on, e.g. for 3-cells A, B, C, D a 4-cell `L_A ∗₂ χ_{a′} ⇛ χ_a ∗₂ R_A`. Choosing these boundary formulas is part of the problem.

The requirements:

1. **Free objects on globular pasting diagrams.** For every finite globular pasting diagram Γ, the free such structure F(Γ) exists and has an explicit combinatorial description. Ideally this is a "Steiner-like" description: a finite graded set of generators (one for each "iterated tensor" of cells of Γ) with explicit boundaries, so that cells can be computed mechanically.
2. **Support determines cells.** In F(Γ), two cells of the same dimension using the same set of generators are equal.
3. **Directedness.** For every k < l, the interchange cell for two cells side by side along a k-cell exists in F(Γ), and the reverse cell does not exist.
4. **Comparison.** The structure restricts to (or maps to) Gray-enriched categories when all interchange cells for k ≥ 1 are identities, and to strict ω-categories when all interchange cells are identities.
5. **Substitution.** The family Γ ↦ F(Γ) is closed under substitution. A cell of F(Γ) can be substituted for each generator of a pasting diagram Γ′ of matching boundary, giving a map F(Γ′) → F(Γ). Equivalently, the F(Γ) form a globular-operad-like structure.

A negative answer is equally valuable: an argument that no notion satisfies 1–3, or that free objects must be infinite, or that requirement 2 must fail. That would show directed interchange at every level cannot be handled by a generator-support criterion.

## Hints and partial approaches

- **Dimension 3.** Forest and Mimram's "Gray presentations" (*Rewriting in Gray categories with applications to coherence*, MSCS 2022) treat interchange as a 3-generator and work in sesquicategories. That is the k = 0 case in dimension 3. A candidate is to iterate their construction, adding an interchange generator for every pair k < l, and to look for a normal form.
- **Diagrammatic sets.** Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*, arXiv:2404.07273) and Chanavat's Gray products of diagrammatic sets (arXiv:2505.01387) handle pasting by molecules without fixing an interchange law. They may provide the generator sets of requirement 1.
- **Recursive guess.** The generators of F(Γ) between the endpoints of Γ should be tuples (g_n, …, g₁), with each gᵢ a generator of F(Θᵢ) itself. Their boundaries should be given by a Leibniz rule in which "∂gᵢ" is a cell of F(Θᵢ), not a chain. Making this precise requires tensoring a *composite* with a generator. That is where the directed interchange inside F(Θᵢ) enters and the chain-complex calculus stops working.

## What would count as a solution

Either of the following:
- a definition together with a combinatorial description of free objects satisfying requirements 1–5, even if limited to finite dimension;
- an impossibility argument showing that requirements 1–3 cannot hold together.

## Literature status (searched 2026-11-18)

**Status (updated 2026-11-18 after a verified researcher response): open, with the problem sharpened. The literal reading (a raw higher cell between the two composites in every dimension) is impossible; this is proved below. The corrected reading, with boundary-adjusted higher comparisons, is open. Two necessary conditions are now known: supports must be taken in the expanded basis, and one finite generator set with injective support forces finitely many non-identity cells in total.** The literature search found: no construction that satisfies requirements 1–5, and no impossibility result either. The closest work handles either "no interchange at all" in every dimension, or directed interchange in dimension ≤ 4 only.**

- **No interchange at all, every dimension.** Interchange as a *generator* rather than a law is handled by these:
  - n-sesquicategories: Araújo, *Simple string diagrams and n-sesquicategories* ([arXiv 2202.09293](https://arxiv.org/abs/2202.09293)), and *Computads and string diagrams for n-sesquicategories* ([arXiv 2210.07704](https://arxiv.org/abs/2210.07704)). Computads for them form a presheaf category, and there is a string-diagram normal form.
  - Precategories: Forest–Mimram, *Free precategories as presheaf categories* ([arXiv 2211.16099](https://arxiv.org/abs/2211.16099)), and Forest–Mimram, *Rewriting in Gray categories with applications to coherence* (MSCS 2022).
  - A strict lax-interchange ω-category would be an n-sesquicategory with directed interchange generators and coherence relations among them. Araújo's computads are the natural setting for requirement 1. Neither paper adds directed interchangers in all dimensions.
- **Directed interchange up to dimension 4.**
  - Crans's teisi.
  - Bourke–Lobbia, *Semi-strict 4-categories as enriched categories* ([arXiv 2610.31448](https://arxiv.org/abs/2610.31448)). This defines several flavours of semi-strict 4-category through skew-monoidal enrichment over Gray-categories, and identifies Crans's 4-teisi among them. It also shows that Gray-categories and their higher transformations form a "left-sharp 4-category". This is the most recent dimension-4 answer to "iterate Gray enrichment". It does not address free objects or a support criterion.
- **Weak alternatives without a fixed interchange.**
  - Associative n-categories: Dorn, [arXiv 1812.10586](https://arxiv.org/abs/1812.10586), with normal forms in Heidemann–Reutter–Vicary, [arXiv 2205.08952](https://arxiv.org/abs/2205.08952). These are strictly associative and unital; interchangers are homotopies, so invertible, not directed.
  - Diagrammatic sets: Hadzihasanovic.
  - Both decide equality of diagrams combinatorially, which is related to requirement 2, but neither has directed interchange.
- **Evidence for requirement 2 in the k = 0 case.** See the literature status of `steiner-support-determines-cells.md`, which settles it for Gray tensors of pasting diagrams.

**Recommended next step:** take Araújo's n-sesquicategorical computads as the ambient. Add an interchange generator for each pair k < l, as in Forest–Mimram's Gray presentations, and test requirement 2 in dimension 4 against Bourke–Lobbia's semi-strict 4-categories.

# Researcher Response

**There is a no-go theorem for the literal replacement of every interchange equation by a higher globular cell. It appears already in dimension 4 and does not depend on the support requirement.** However, it does **not** rule out the interpretation in which higher comparisons have lower interchangers composed onto their boundaries. For that corrected interpretation, I do not have a construction satisfying 1–5 or a proof of impossibility.

The distinction matters here: the literal schema forces interchange to become strict, whereas your recursive guess could avoid that schema.

## 1. Direct comparisons between the raw interchange expressions force strict interchange

Write \(n\) for the dimension of \(a,b,c,d\), and let \(k<\ell<n\). Define

\[
\begin{aligned}
L^n_{k,\ell}(a,b,c,d)
  &=(a\ast_\ell b)\ast_k(c\ast_\ell d),\\
R^n_{k,\ell}(a,b,c,d)
  &=(a\ast_k c)\ast_\ell(b\ast_k d).
\end{aligned}
\]

A direct comparison between these expressions would be an **\((n+1)\)-cell**. Thus the literal all-dimensional schema is

\[
\chi^n_{k,\ell}(a,b,c,d):
L^n_{k,\ell}(a,b,c,d)
\longrightarrow
R^n_{k,\ell}(a,b,c,d).
\tag{1}
\]

Assume that the compositions have the usual globular boundaries. In particular, for \((m+1)\)-cells \(u,v\) and \(j<m\),

\[
s(u\ast_jv)=s(u)\ast_j s(v).
\tag{2}
\]

### Proposition

If (1) exists for every admissible dimension and composable quadruple, then every ordinary interchange equation holds strictly.

### Proof

Fix composable \(m\)-cells \(a,b,c,d\) and \(k<\ell<m\). Consider their identity \((m+1)\)-cells

\[
1_a,\qquad 1_b,\qquad 1_c,\qquad 1_d.
\]

Applying (1) one dimension higher gives an \((m+2)\)-cell

\[
\chi^{m+1}_{k,\ell}(1_a,1_b,1_c,1_d):
\widetilde L\longrightarrow\widetilde R,
\]

where

\[
\begin{aligned}
\widetilde L
  &=(1_a\ast_\ell1_b)\ast_k(1_c\ast_\ell1_d),\\
\widetilde R
  &=(1_a\ast_k1_c)\ast_\ell(1_b\ast_k1_d).
\end{aligned}
\]

The source and target of a globular cell must be parallel. Consequently,

\[
s(\widetilde L)=s(\widetilde R).
\tag{3}
\]

Since \(k,\ell<m\), equation (2) applies to every composition displayed above. Using \(s(1_a)=a\), and similarly for the other identities, equation (3) becomes

\[
(a\ast_\ell b)\ast_k(c\ast_\ell d)
=
(a\ast_k c)\ast_\ell(b\ast_k d).
\]

This is strict interchange. ∎

The proof does not use associativity, support, freeness, or coherence equations. It does not even require

\[
1_u\ast_j1_v=1_{u\ast_jv};
\]

the source equations suffice.

**Finite-dimensional consequence.** In an \(N\)-dimensional structure satisfying the raw schema, all interchange equations in dimensions \(m\leq N-2\) are forced to hold strictly. In particular, a raw four-dimensional theory already forces strict interchange of 2-cells.

### A finite pasting diagram witnessing the conflict with directedness

Use chronological composition in this example: \(u\ast_kv\) means first \(u\), then \(v\).

Take the finite globular pasting diagram with

\[
f_0,f_1,f_2:x\to y,
\qquad
g_0,g_1,g_2:y\to z,
\]

and generating 2-cells

\[
a:f_0\Rightarrow f_1,\quad
b:f_1\Rightarrow f_2,\quad
c:g_0\Rightarrow g_1,\quad
d:g_1\Rightarrow g_2.
\]

Set

\[
p=(a\ast_1b)\ast_0(c\ast_1d),
\qquad
q=(a\ast_0c)\ast_1(b\ast_0d).
\]

The requested directed interchange supplies a 3-cell \(p\to q\). The raw four-dimensional schema applied to \(1_a,1_b,1_c,1_d\) forces \(p=q\). Hence \(1_p\) is also a 3-cell \(q\to p\), contradicting the requirement that no reverse cell exist.

This is not merely the observation that an exchange of identity inputs can be degenerate: identity inputs **one dimension higher force the exchange of the original nonidentity generators to have equal endpoints**.

One can also avoid identity inputs to the higher exchange. Take four generating 3-cells

\[
A:a\Rightarrow a',\quad B:b\Rightarrow b',
\quad C:c\Rightarrow c',\quad D:d\Rightarrow d',
\]

arranged in the finite pasting shape

\[
(D^3\ast_1D^3)\ast_0(D^3\ast_1D^3).
\]

A raw 4-cell between \(L^3_{0,1}(A,B,C,D)\) and \(R^3_{0,1}(A,B,C,D)\) again forces \(p=q\), by taking their 2-sources.

Thus **the literal raw schema cannot satisfy the intended nontrivial directedness condition**, independently of requirements 1 and 2.

## 2. The correctly typed higher comparison escapes this theorem

Suppose

\[
A:a\Rightarrow a',\quad B:b\Rightarrow b',
\quad C:c\Rightarrow c',\quad D:d\Rightarrow d'
\]

are 3-cells. Abbreviate their two composite 3-cells by

\[
L_A:L_a\Rightarrow L_{a'},
\qquad
R_A:R_a\Rightarrow R_{a'},
\]

where, for example,

\[
L_a=L^2_{0,1}(a,b,c,d).
\]

The lower interchangers are

\[
\chi_a:L_a\Rightarrow R_a,
\qquad
\chi_{a'}:L_{a'}\Rightarrow R_{a'}.
\]

The expressions \(L_A\) and \(R_A\) generally are **not parallel**. But the following expressions are parallel:

\[
L_A\ast_2\chi_{a'}
\quad\text{and}\quad
\chi_a\ast_2R_A.
\]

Both are 3-cells

\[
L_a\longrightarrow R_{a'}.
\]

Consequently, a possible directed naturality comparison has the well-typed boundary

\[
\boxed{
L_A\ast_2\chi_{a'}
\;\Longrightarrow\;
\chi_a\ast_2R_A.
}
\tag{4}
\]

Here \(\ast_2\) is again chronological composition. The opposite orientation is another possible choice; its compatibility with the remaining axioms would need to be established.

When \(A,B,C,D\) are identities, the two boundaries in (4) reduce to \(\chi_a\). They do **not** force \(L_a=R_a\).

This distinction is also present in established Gray-category calculations: Di Vittorio–Lobbia’s generalized interchange result compares 3-cell composites after accounting for the isomorphism between their boundary composites. It does not assert interchange between arbitrary unadjusted expressions. [arxiv.org](https://arxiv.org/abs/2310.03503?utm_source=chatgpt.com)

Therefore:

- If “every interchange law is replaced by a directed cell” means (1) at every dimension, the proposition gives a negative answer.
- If it means elementary exchanges together with recursively adjusted comparisons such as (4), the proposition does not give a negative answer.

Your recursive guess is compatible with the second interpretation. The missing higher boundary formulas are substantive mathematical data.

## 3. A support obstruction exists under an additional hypothesis—but that hypothesis excludes your Gray example

There is a second elementary obstruction worth isolating.

Suppose a support function satisfies

\[
\operatorname{supp}(u\ast_jv)
=
\operatorname{supp}(u)\cup\operatorname{supp}(v)
\tag{5}
\]

for **every** composition dimension \(j\), with values in the subsets of one fixed generating set.

Then

\[
\begin{aligned}
\operatorname{supp}(L^n_{k,\ell}(a,b,c,d))
&=
\operatorname{supp}(a)\cup\operatorname{supp}(b)
 \cup\operatorname{supp}(c)\cup\operatorname{supp}(d)\\
&=
\operatorname{supp}(R^n_{k,\ell}(a,b,c,d)).
\end{aligned}
\]

Support injectivity therefore forces strict interchange immediately.

So a nontrivial theory satisfying requirement 2 **cannot also have a support function satisfying (5) for every composition**.

However, this does not refute your proposed tensor support. In the Gray-enriched construction, composition along dimension \(0\) changes the tensor factors indexing the relevant generators. Its effect on support is not the union operation in (5).

For example, take adjacent generating 2-cells

\[
\alpha:f_0\Rightarrow f_1:x\to y,
\qquad
\beta:g_0\Rightarrow g_1:y\to z.
\]

In the tensor hom from \(x\) to \(z\), the two paths have respective one-dimensional tensor-basis supports

\[
\{\,g_0\otimes\alpha,\ \beta\otimes f_1\,\}
\]

and

\[
\{\,\beta\otimes f_0,\ g_1\otimes\alpha\,\}.
\]

These sets differ. Identifying both with the original-label set \(\{\alpha,\beta\}\) discards the endpoint indices that distinguish the tensor generators.

Steiner’s subset description concerns the basis of the directed complex: Theorem 6.2 establishes the relevant coefficient-\(0/1\) property for loop-free unital bases. It is not a theorem that arbitrary original-label support is injective after forgetting tensor indices. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Thus a support-based impossibility argument must address **the expanded basis itself**. Counting only the original generators of \(\Gamma\) is insufficient.

## 4. A finite support set imposes a stronger finiteness condition than finite generation

There is another necessary consequence of your proposed finite-basis version.

### Proposition

Let \(C\) be a reflexive globular set. Suppose one finite set \(B\) admits injective functions

\[
\operatorname{supp}_n:C_n\hookrightarrow\mathcal P(B)
\]

for every \(n\). Then \(C\) has only finitely many nonidentity cells in total. In particular, all sufficiently high-dimensional cells are identities.

### Proof

Put

\[
c_n=|C_n|,
\qquad M=2^{|B|}.
\]

Support injectivity gives \(c_n\leq M\). The identity map

\[
i_n:C_n\longrightarrow C_{n+1}
\]

is injective because \(s\,i_n=\mathrm{id}\). Hence

\[
c_n\leq c_{n+1}\leq M.
\]

Let

\[
N_{n+1}=C_{n+1}\setminus i_n(C_n)
\]

be the set of nonidentity \((n+1)\)-cells. Then

\[
|N_{n+1}|=c_{n+1}-c_n.
\]

For every \(r\),

\[
\sum_{n=0}^{r-1}|N_{n+1}|
=c_r-c_0
\leq M-c_0.
\]

The total number of positive-dimensional nonidentity cells is therefore at most \(M-c_0\). Only finitely many dimensions can have any such cells. ∎

No compatibility between support and identities was assumed.

This gives a precise route to the negative result you proposed:

> Find one finite pasting diagram \(\Gamma\) for which the required directed exchanges and coherences force infinitely many nonidentity cells. That would contradict a globally finite support set together with requirement 2.

I have not established such a diagram. The proposition also does not apply if the generating set is merely finite in each degree, rather than finite altogether.

## 5. What the cited constructions establish

Three details delimit the remaining problem.

**Araújo supplies the ambient composition syntax, not the required completion.** His basic operations are top-dimensional composition and mixed-dimensional whiskering,

\[
C_i\times_{C_{\min(i,j)-1}}C_j\longrightarrow C_{\max(i,j)}.
\]

The subsequent computad paper proves its normal-form and presheaf results, while explicitly separating them from the addition of coherent weak interchange. Consequently, adjoining higher generators requires checking their parallel boundaries; it cannot mean simply adjoining (1) in every degree. [arxiv.org](https://arxiv.org/html/2202.09293v4?utm_source=chatgpt.com)

**Bourke–Lobbia’s 2026 paper goes further on existence than your status note indicates, but does not meet directedness at every level.** Section 4.2.6 explicitly defines lax variants: their designated 3-cell interchangers need not be equivalences, and certain 4-cell comparisons need not be invertible. Their homs nevertheless remain ordinary Gray-categories, so the interchangers supplied by those homs are invertible. Thus these definitions do not meet requirement 3 at every composition level. Section 4.3 also states that their flavours are monadic over 4-dimensional globular sets, which gives abstract free structures; this is distinct from the requested finite combinatorial description and support theorem. [arxiv.org](https://arxiv.org/html/2610.31448v2?utm_source=chatgpt.com)

**The cocategorical obstruction has additional hypotheses.** Bourke–Gurski constrain cocontinuous tensor bifunctors on Gray-categories and derive obstructions to the desired biclosed and model-compatible tensor structures. Those hypotheses are not consequences of requirements 1–5. Their result therefore cannot establish nonexistence of every algebraic theory contemplated here. [arxiv.org](https://arxiv.org/pdf/1412.1320?utm_source=chatgpt.com)

The proved obstruction is consequently specific: **direct higher comparisons of the raw rectangular composites force lower interchange to be strict.** Once higher boundaries are adjusted as in (4), the unresolved question is whether one can choose all those comparisons and coherence equations so that free structures admit a finite expanded basis, injective support, and substitution. None of the arguments above settles that corrected question.

---

## Verification of the researcher response (2026-11-18)

**Verdict: correct. The no-go theorem for raw higher interchangers is right and elementary. The boundary-adjusted alternative (4) is well typed. The support and finiteness propositions are right. The citations check out. The corrected problem remains open, and the statement above has been updated.**

**§1, no-go for raw interchangers.** If a raw (m+2)-cell `χ^{m+1}(1_a, 1_b, 1_c, 1_d) : L̃ → R̃` exists, its source and target are parallel, so `s(L̃) = s(R̃)`. Because k, l < m, the source of a composite along a dimension below m is the composite of the sources, and `s(1_a) = a`. So `s(L̃) = (a ∗ₗ b) ∗ₖ (c ∗ₗ d)` and `s(R̃) = (a ∗ₖ c) ∗ₗ (b ∗ₖ d)`, and strict interchange holds for m-cells. The proof uses only globularity and the boundary formula (2). Correct.
- The finite witness is correct. With 2-cells a, b, c, d in a 2-dimensional pasting diagram, the elementary 3-cell `p → q` exists by requirement 3. The raw 4-dimensional schema forces `p = q`, so `1_p : q → p` is a reverse cell.
- The variant with four generating 3-cells is also correct: taking 2-sources of the two sides of a raw 4-cell gives `p = q` again.
- This was an error in the problem statement's wording, not in the intended construction: Gray-categories already handle interchange of 3-cells along 0-cells through naturality of the interchanger, not through a raw cell. The statement above now says so.

**§2, the corrected comparison.** For 3-cells `A : a ⇛ a′` etc., `L_A : L_a ⇛ L_{a′}` and `χ_{a′} : L_{a′} ⇛ R_{a′}`, so `L_A ∗₂ χ_{a′} : L_a ⇛ R_{a′}`. Likewise `χ_a ∗₂ R_A : L_a ⇛ R_{a′}`. The two are parallel, and for identity inputs both reduce to `χ_a`, which forces nothing. Correct. Di Vittorio–Lobbia (arXiv 2310.03503) is cited for the same pattern in Gray-categories: their abstract states generalized interchange of 3-cells "modulo the unique isomorphism" between boundary composites. Confirmed.

**§3, union support.** If support of every composite is the union of supports, then L and R always have the same support, and requirement 2 makes interchange strict. Correct and immediate. The tensor example is right: the two whiskered paths for adjacent 2-cells α, β use different basis elements (`g₀ ⊗ α, β ⊗ f₁` versus `β ⊗ f₀, g₁ ⊗ α`). So requirement 2 must be stated for the expanded basis, as `pseudo-vs-gray.md` already does for k = 0.

**§4, finiteness.** Injective `C_n → 𝒫(B)` gives `|C_n| ≤ 2^{|B|}`. Identities `C_n → C_{n+1}` are injective since `s ∘ i = id`. So `|C_n|` is non-decreasing and bounded, and the numbers of new non-identity cells sum to at most `2^{|B|} − |C_0|`. Correct. The consequence: if every F(Γ) has one finite generator set with injective support (as Steiner complexes of pasting diagrams do), then F(Γ) has only finitely many non-identity cells, so the tower of higher interchange comparisons must stop in each F(Γ). A finite Γ that forces infinitely many would refute the finite-basis version. Neither is established.

**§5, citations.**
- Bourke–Lobbia, arXiv 2610.31448v2, §4.2.6: "lax 4-categories", in which the 3-cell interchanger is not an adjoint equivalence and certain 4-cells need not be invertible. They are enriched in Gray-categories, so interchange inside homs stays invertible. Confirmed. §4.3 says their flavours are monadic over 4-globular sets (via Griffiths' presentations). Confirmed. So they give existence of free objects abstractly in dimension 4, directed only at the outer level. This sharpens the "dimension 4" entry of the literature status above.
- Araújo and Bourke–Gurski: the qualifications are fair. They supply ambient syntax and an obstruction under extra hypotheses respectively, not a construction or a no-go for requirements 1–5.

**What this settles, and what it opens.**
- Settled: the literal reading is impossible. The problem statement is corrected.
- Settled: supports must be computed in the expanded basis.
- Settled: a finite basis with injective support forces finitely many non-identity cells.
- Open: the corrected problem. The concrete next steps are (a) write the boundary formulas for the higher comparisons in dimension 4 and check them against Bourke–Lobbia's lax 4-categories, and (b) search for a finite Γ forcing infinitely many non-identity cells, which would refute the finite-basis version.
- Consequence for uniform L in `pseudo-vs-gray.md`: its side condition must compute supports in a structure whose higher interchangers are boundary-adjusted, never raw.
