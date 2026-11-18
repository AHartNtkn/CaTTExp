# Problem: composites of molecules in CaTT (Gray contexts)

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory for weak ω-categories.

- Types are `⋆` and `u →_A v`. Contexts are lists of typed variables. By Benjamin–Markakis–Sarti ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- A variable's type may be a composite: `f : x → y, g : y → z, h : x → z, τ : g·f → h` is a context, though not a pasting diagram.
- The only term former is `coh_{P, u →_A v}[σ]`. It needs P to be a **pasting context** (a globular pasting diagram), σ a substitution into P, and one side condition:
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality.
- Every CaTT term t of a context Γ has a strict image `π(t)` in the free strict ω-category `F(Γ)` on the computad Γ, since strict ω-categories are models of CaTT.

### 1.2 Molecules and their presentations

- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*, [arXiv 2404.07273](https://arxiv.org/abs/2404.07273)). Globes are molecules, and so are Gray products `U ⊗ V` of molecules. Their cells satisfy Steiner's boundary formula `∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y)`.
- A **layering** of an n-molecule is a decomposition into a sequence of layers, each a single n-dimensional atom pasted with lower-dimensional cells. Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) proves: frame-acyclic molecules have layerings, and their layerings correspond to linear orders compatible with a partial order on the top cells (Prop. 2.18); the poset of subdivisions is contractible (Thm 2.52); every molecule of dimension ≤ 3, and every acyclic molecule, is frame-acyclic.
- **Presenting a molecule in CaTT.** To present a molecule U as a CaTT context, each cell x needs a type `⌈∂⁻x⌉ → ⌈∂⁺x⌉` whose two sides are CaTT terms composing the boundary molecules, by induction on dimension. A **U-composite** is a term t with `Var(t) = Var(U)` and `t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉`.

> **Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n presented in CaTT: (existence) U-composites exist; (uniqueness) any two U-composites are connected by a CaTT term `t → t′` (which is then invertible, being built from coherences).

A related statement is **conservativity**: extending the coherence rule from pasting contexts to frame-acyclic molecules, with the same two side conditions, adds no new cells up to invertible CaTT cells. Conservativity implies G(n) for all n. The converse is *not* known: molecular coherences over an m-molecule include cells of every dimension above m, which needs RC (§2) above the top dimension and not only G.

## 2. What is known

Write RC(n) for the property:

> **RC(n) for a context Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

1. **G(1)**: 1-molecules are paths, which are pasting contexts.
2. **Theorem A (proved): RC(2) holds for every CaTT context.** (An external referee independently proved the special case of 2-molecules by the same route: normalize to atomic generators, show each face is used once via injectivity of ∂₂, then apply adjacent swaps.) Proof sketch:
   - Two 1-terms with the same flattened path w are full parallel terms over the chain context of w, so the coherence rule connects them. Any 2-term with no 2-variable pulls back to that chain and is connected to the comparison cell with the same boundary.
   - Every 2-term is connected to a vertical composite of whiskered 2-variables and 2-terms without 2-variables (coherences over its arity and over small pasting contexts).
   - Each whiskered 2-variable x, with whisker paths λ and ρ, is connected to a fixed normal form built from one composition coherence over the pasting context "chain, 2-disc, chain", with the disc sent to x and all comparisons made over the expanded paths.
   - Two 2-paths of whiskered generators give the same strict 2-cell iff they are related by exchange moves. Each exchange move is a coherence over "chain, 2-disc, chain, 2-disc, chain", substituted and normalised. ∎
3. **G(2) (proved).** In a 2-molecule, every 2-path from `∂⁻U` to `∂⁺U` uses each 2-cell exactly once (the 2-cycles of a molecule are zero), and two such paths are related by exchange moves (linear extensions are connected by adjacent swaps, and two incomparable consecutive 2-cells sit side by side). So any two U-composites have the same strict image, and Theorem A connects them. Existence is by a layering, with Theorem A's 1-dimensional comparison cells between layers.
4. **Existence in G(3) (proved; also proved independently by a referee, by padding with fixed binary composites).** Take a layering of the 3-molecule. Realise each layer as a 3-term `U₁ ∗₁ (a ∗₀ X ∗₀ b) ∗₁ U₂` (X the layer's 3-cell, whiskers chosen with the right strict images, boundaries adjusted by 2-dimensional comparison cells). Consecutive layers meet at 2-terms with equal strict images, so Theorem A connects them. Hence **every Gray generator of dimension ≤ 4** (e.g. of `D²⊗D²`, `D³⊗D¹`, `D¹⊗D¹⊗D¹⊗D¹`) has a CaTT type.
5. **General pattern.** The same argument shows: existence in G(n) follows from RC(n−1) for the (n−1)-skeleton of U, and uniqueness in G(n) follows from RC(n) for U.

## 3. Why dimension 3 is different

RC(3) is false for arbitrary contexts. In `Γ = (x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell `a ∗₀ a → a ∗₀ a` and the identity have equal strict images but are expected not to be connected (in the fundamental weak ω-groupoid of S², with a a generator of π₂, the Eckmann–Hilton cell is non-zero in π₃(S²); *sketch, not checked in detail*). So a proof must use **loop-freeness**. Molecules are loop-free, and Campion ([arXiv 2311.00205](https://arxiv.org/abs/2311.00205), Cor. 3.5) and Chanavat (Thm 3.29) show that their free strict ω-categories are also their free (∞,ω)-categories, so RC holds for them in (∞,ω)-semantics.

The dimension-2 argument fails at one step. Between two consecutive 3-generators, a 3-dimensional proof has runs of 3-cells with no 3-variable, between 2-terms with equal strict image. In dimension 2 the analogous runs live over a single path, where the coherence rule settles everything. In dimension 3 they live over a 2-dimensional context that is not a pasting context, such as the lax square `f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺` or the boundary 2-sphere of the Gray cube. A Squier-style argument (critical branchings of elementary 3-cells close up to 4-cells) is the natural attack. The hard branchings pair a move of a 2-generator with a reassociation that splits that generator's boundary composite; no pasting context contains both.

## 4. Questions

Each question asks for explicit CaTT terms, built with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: RC(3) for the lax square.** Let S be the context `x⁻, x⁺, y⁻, y⁺ : ⋆; x↑ : x⁻ → x⁺; y↑ : y⁻ → y⁺; f⁻ : x⁻ → y⁻; f⁺ : x⁺ → y⁺; F : f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺`. Are any two parallel 3-terms of S connected by a 4-term?
2. **Uniqueness in G(3) for the Gray cube.** For `U = D¹ ⊗ D¹ ⊗ D¹`, presented with hexagon composites as the boundary of its 3-cell X, show that any two U-composites are connected. The essential case: a 3-term from `⌈∂⁻U⌉` to itself built from coherences only (no X) is connected to the identity. This is RC(3) for the boundary 2-sphere of the cube.
3. **RC(3) for loop-free contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule (or its skeleta), or for every finite loop-free computad. Equivalently for molecules: uniqueness in G(3), and hence existence in G(4).
4. **G(n) for all n.** Prove RC(n) for loop-free contexts for all n, or the weaker G(n). In particular: does Chanavat's contractibility of the subdivision poset (Thm 2.52) translate into CaTT cells, with a 1-cell for each edge of the poset and higher cells for its higher simplices, each a substituted coherence over a pasting context?

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) on loop-free contexts; or a counterexample: a frame-acyclic molecule with two U-composites (or a loop-free context with two parallel terms of equal strict image) not connected by any CaTT term. A published reference also counts.

## 6. Literature (searched 2026-11-18)

- No paper treats composites of non-globular molecules inside CaTT or inside Grothendieck–Maltsiniotis weak ω-categories.
- Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) and Campion ([arXiv 2311.00200](https://arxiv.org/abs/2311.00200)) prove the (∞,n) pasting theorem, the semantic analogue of G. No comparison between CaTT's models and (∞,ω)-categories is known, so it does not transfer directly.
- Hadzihasanovic's diagrammatic sets ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639), [arXiv 2007.14505](https://arxiv.org/abs/2007.14505)) take "every round molecule has a weak composite, unique up to equivalence" as the definition of a weak higher category. G asks whether CaTT's models satisfy it.
- Benjamin–Markakis–Sarti ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)) and ICaTT ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)): composites of coherences are invertible, so uniqueness only needs some connecting cell.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): 2-cells of free 2-categories as 2-paths modulo exchange; Squier-style coherence.
- Ara–Lucas ([arXiv 1909.13564](https://arxiv.org/abs/1909.13564)), Cor. 3.11, and Steiner (HHA 6, 2004): Gray tensors of free strict ω-categories are free on their atoms.

# Researcher Response

**I have not obtained a solution meeting §5.** The unresolved case already includes arbitrary parallel 3-terms of the lax square whose strict 2-boundary is \(F\). I did not find a published theorem that supplies those CaTT fillers.

There are, however, two explicit partial constructions and a support restriction that sharpens the cube problem. I give their proofs below, including the point where the square argument stops.

## 1. A support restriction

Write \(\operatorname{supp}(t)\) for the variables used by \(t\), closed recursively under dependencies in their declared types, and \(\operatorname{supp}_d(t)\) for its dimension-\(d\) subset.

Benjamin–Markakis, Lemma 36, proves equality of the \((d-1)\)-supports below. The same induction gives the following stronger, total-support statement:
\[
\boxed{
\operatorname{supp}_d(c)=\varnothing
\quad\Longrightarrow\quad
\operatorname{supp}(c)
=\operatorname{supp}(s c)
=\operatorname{supp}(t c).
}
\tag{1}
\]
This strengthening is a deduction, not the literal statement of their lemma. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

**Proof.** Induct structurally on \(c\). A variable is excluded. Write
\[
c=\operatorname{coh}_{P,a\to b}[\sigma],
\qquad
\operatorname{supp}(c)=
\bigcup_{z\in\operatorname{Var}(P)}
\operatorname{supp}(\sigma z).
\]

If \(\dim P<d\), fullness of \(a,b\) gives the result by substitution.

If \(\dim P=d\), every arity variable below dimension \(d-1\) belongs to the source boundary. Every remaining \((d-1)\)-variable is reached from that boundary by a vertical string of \(d\)-variables. Each substituted \(d\)-variable has empty \(d\)-support. Induction identifies its total support with both endpoint supports. Consequently, all supports in the displayed union already belong to \(\operatorname{supp}(a[\sigma])\). The reverse inclusion follows from substitution. The target argument is identical. ∎

The dependency closure matters: (1) is not a statement about a convention under which the support of a variable is just that variable.

## 2. Explicit 4-fillers for the identity-path cases of the lax square

Let
\[
p=f^-*_0y^\uparrow,
\qquad
q=x^\uparrow *_0f^+,
\]
so \(F:p\Rightarrow q\).

### Strict classification

The generating graph has ten paths: four empty paths, four edges, and \(p,q\). Its free strict 2-category has precisely
\[
1_w\quad\text{for those ten paths }w,
\qquad\text{and}\qquad F:p\Rightarrow q.
\tag{2}
\]

Indeed, two copies of \(F\) cannot compose vertically because \(p\ne q\). No nonempty path precedes \(F\), since no edge enters \(x^-\); no nonempty path follows \(F\), since no edge leaves \(y^+\). Thus adjoining identities produces no additional nonidentity 2-cells.

Consider parallel 3-terms
\[
\alpha,\beta:t\longrightarrow t'.
\]
Their common strict 2-boundary is therefore either \(1_w\) or \(F\). Since \(S\) has no 3-generators, their strict 3-images agree automatically.

### Construction when \(\pi(t)=1_w\)

First, \(t\) cannot use \(F\). To see this syntactically, count \(F\) in strict 2-cell expressions. The count is additive under composition and preserved by associativity, units and exchange. Induction on a CaTT 2-term shows that its strict count is positive exactly when its support includes \(F\): a composition uses every top-dimensional input of its pasting arity, and a coherence over an arity of dimension at most one has no 2-dimensional input. Hence strict count zero implies absence of \(F\).

Applying (1), first in dimension three and then in dimension two, gives
\[
\operatorname{supp}(\alpha)
=\operatorname{supp}(\beta)
=\operatorname{supp}(t)
=\operatorname{supp}(s t).
\tag{3}
\]
The 1-term \(s t\) flattens to \(w\). Induction on 1-terms identifies its support with the vertices and edges of \(w\): concatenation has no cancellation.

Let \(C_w\) be the standard path context for \(w\), and let
\[
S\vdash \iota_w:C_w
\]
send each path variable to the corresponding variable of \(S\). By (3), restricting and renaming \(\alpha,\beta\) gives full parallel terms \(\bar\alpha,\bar\beta\) over \(C_w\), with
\[
\bar\alpha[\iota_w]=\alpha,
\qquad
\bar\beta[\iota_w]=\beta.
\]
Therefore the required 4-term is
\[
\boxed{
K(\alpha,\beta)
=
\operatorname{coh}_{C_w,\,
\bar\alpha\to\bar\beta}[\iota_w].
}
\tag{4}
\]

This is a single legal application of the original coherence rule. It settles all cases in (2) except the case with common strict 2-boundary \(F\).

## 3. An explicit reduction for elementary coherences with strict boundary \(F\)

There is also a reduction for a 3-term
\[
c=\operatorname{coh}_{P,u\to v}[\sigma]
\tag{5}
\]
when \(\dim P=2\) and
\[
\pi(u[\sigma])=\pi(v[\sigma])=F.
\]
It reduces the arity to a vertical 2-chain.

### The substitutions

Decompose the globular 2-pasting context \(P\) into horizontal columns. Write its 0-variables as \(z_0,\ldots,z_m\). Column \(j\) has parallel 1-variables and a vertical chain:
\[
g_{j,0},\ldots,g_{j,n_j}:z_{j-1}\to z_j,
\qquad
\theta_{j,k}:g_{j,k-1}\Rightarrow g_{j,k}.
\]
A column with \(n_j=0\) consists of one 1-variable.

Because \(u,v\) have full support, their strict 2-images use every \(\theta_{j,k}\) once. This follows directly from the column description: vertical composition traverses a subchain, and full support forces traversal of every step in every column.

After applying \(\sigma\), exactly one \(\theta_{j,k}\) has strict image \(F\). Let \(j_0\) be its column. That column spans \(x^-\to y^+\). The absence of nonempty paths entering \(x^-\) or leaving \(y^+\) forces:

- Every column before \(j_0\) to be assigned terms over the single vertex \(x^-\).
- Every column after \(j_0\) to be assigned terms over the single vertex \(y^+\).

Here the assertion about terms, rather than just their strict images, follows from the identity-path support argument in §2, in dimensions one and two.

Let \(n=n_{j_0}\), and let \(Q\) be the vertical 2-chain with variables
\[
x,y:*,
\qquad h_k:x\to y\quad(0\le k\le n),
\qquad
\xi_k:h_{k-1}\Rightarrow h_k\quad(1\le k\le n),
\]
declared in the pasting-context order
\[
x,y,h_0,h_1,\xi_1,h_2,\xi_2,\ldots,h_n,\xi_n.
\]

Define \(Q\vdash\lambda:P\) by:

- Sending \(z_i\) to \(x\) for \(i<j_0\), and to \(y\) for \(i\ge j_0\).
- Sending \(g_{j_0,k}\) to \(h_k\), and \(\theta_{j_0,k}\) to \(\xi_k\).
- For every variable in another column, taking its \(\sigma\)-image and renaming its sole supporting vertex \(x^-\) to \(x\), or \(y^+\) to \(y\), respectively.

Define \(S\vdash\tau:Q\) by
\[
x\mapsto x^-,
\quad y\mapsto y^+,
\quad h_k\mapsto\sigma(g_{j_0,k}),
\quad \xi_k\mapsto\sigma(\theta_{j_0,k}).
\]
These substitutions satisfy the syntactic equality
\[
\lambda[\tau]=\sigma.
\tag{6}
\]

### The 4-term

Put
\[
\bar c=\operatorname{coh}_{P,u\to v}[\lambda],
\qquad
\bar u=u[\lambda],
\qquad
\bar v=v[\lambda],
\]
and define
\[
d=\operatorname{coh}_{Q,\bar u\to\bar v}[\operatorname{id}_Q].
\]
Both \(\bar u,\bar v\) have full support \(Q\), since every central-column variable is retained by \(\lambda\). Thus \(d\) is legal. Likewise, \(\bar c,d\) are full parallel 3-terms over \(Q\). Hence
\[
\boxed{
R(c)=
\operatorname{coh}_{Q,\bar c\to d}[\tau]
:
c\longrightarrow
\operatorname{coh}_{Q,\bar u\to\bar v}[\tau].
}
\tag{7}
\]
The source is exactly \(c\), by (6).

### Why this does not finish question 1

The terms \(\tau(\xi_k)\) remain arbitrary 2-terms of \(S\). Exactly one has strict image \(F\); the others have identity strict images. In particular, the term assigned to that one \(\xi_k\) need not be the variable \(F\).

Your \(RC(2)\) supplies comparisons between parallel choices for these 2-terms. It does not supply the 4-cells making those comparisons compatible with every 3-term. Moreover, an arbitrary 3-term can have a three-dimensional composition arity, whereas (7) treats a two-dimensional coherence arity.

Thus (7) is an explicit arity reduction, but it does not yield a common normal form for arbitrary parallel 3-terms. Using it as such would leave precisely the missing coherence argument unproved.

## 4. The cube’s specified loop already lies over one hemisphere

Let
\[
A=\left\lceil\partial^-U\right\rceil,
\qquad
H:A\longrightarrow A
\]
be a 3-term with no \(X\).

Equation (1) gives
\[
\boxed{\operatorname{supp}(H)=\operatorname{supp}(A).}
\tag{8}
\]
Therefore \(H\) cannot use any positive-hemisphere face generator absent from \(A\). Since support includes type dependencies, it cannot introduce additional edge or vertex generators either.

Consequently, \(H\) is obtained by weakening a term over the context presenting the **negative three-face 2-molecule**. The specified nullhomotopy problem can be studied entirely over that hemisphere; it does not require all six face generators of the boundary sphere.

This is a restriction on possible terms, not a construction of
\[
H\longrightarrow 1_A.
\]
I have not established the required \(RC(3)\) for that three-face context.

## 5. What subdivision contractibility does and does not supply

Chanavat’s Theorem 2.52 states that \(\mathrm{Sd}\,U\) is contractible for a frame-acyclic molecule **that is not an atom**. For an atom, this subdivision poset is empty. The semantic freeness statement is Theorem 3.17; Theorem 3.29 concerns compatibility with the Gray product under its acyclic-atom hypothesis. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

To derive the requested CaTT result from subdivision contractibility, one must additionally construct:

1. A CaTT composite for each chosen subdivision.
2. A comparison term for each refinement.
3. Higher comparison terms satisfying the boundaries prescribed by chains of refinements.
4. A proof that arbitrary CaTT composites and comparison terms are controlled by this construction.

Contractibility of the indexing poset does not construct these terms. Even a coherent assignment on its nerve would only compare the assigned terms unless the fourth requirement were proved. For \(RC(3)\), that requirement includes control of arbitrary syntactic 3-loops.

The Gray-categorical pasting theorem does not remove this issue as stated. Di Vittorio explicitly restricts the theorem to composites produced by the specified pasting algorithm and leaves the identification with all composites of the free Gray-category outside that paper’s proof. A further translation to arbitrary CaTT terms would still be needed. [arxiv.org](https://arxiv.org/pdf/2205.15486?utm_source=chatgpt.com)

There is also a hypothesis distinction in §3 of the problem: **frame-acyclicity should not be identified with Steiner loop-freeness**. Hadzihasanovic’s Comment 8.3.5 relates Steiner loop-freeness to strong dimension-wise acyclicity, whereas Example 8.3.12 gives a frame-acyclic 3-atom that is not even dimension-wise acyclic. Thus a theorem for Steiner’s loop-free class would not, by that hypothesis alone, cover every frame-acyclic molecule. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

The explicit constructions established here are (4) and (7). The arbitrary \(F\)-boundary case of question 1, the hemisphere nullhomotopy required by question 2, and the general assertions in questions 3–4 remain unresolved by these arguments.

## Verification of the researcher response (2026-11-18)

Checked step by step, with the cited sources read in the arXiv PDFs (Benjamin–Markakis 2406.12127; Chanavat 2603.22242v2; Di Vittorio 2205.15486; Hadzihasanovic 2404.07273v2; Campion 2311.00200 and 2311.00205).

**Verdict.** No question of §4 is solved, as the response says. Every claim it does make is correct. It gives two explicit families of 4-terms for question 1, a reduction for question 2, and four corrections to this prompt, two of which also correct our own notes.

### V1. The support lemma (1): correct

- *Citation.* Benjamin–Markakis, *Invertible cells in ω-categories*, Lemma 36 (p. 35), states exactly `supp_d(c) = ∅ ⇒ supp_{d−1}(src c) = supp_{d−1}(tgt c) = supp_{d−1}(c)`. The response says, correctly, that (1) is a strengthening it deduces, not the lemma.
- *Proof.* Rechecked case by case. A d-term `coh_{P,a→b}[σ]` with `dim P < d` is a coherence (a composition over P has dimension `dim P`), so a and b cover `Var(P)` and the supports agree after substitution. With `dim P = d` it is a composition. Every variable of P of dimension < d−1 lies in `∂⁻P`. Every (d−1)-variable not in `∂⁻P` is the target of a d-variable, and following sources reaches `∂⁻P`. Each substituted d-variable has empty d-support, so by induction its total support equals that of its source. Hence every summand of `supp(c)` lies in `supp(a[σ])`. This is the same induction as BM's proof, carried for total support.
- *Small gap, closable.* The proof uses without comment that a composition over P has dimension `dim P`. In Finster–Mimram's formulation that is a consequence, not a rule. It follows from (1) one dimension down, or by taking the BMS form of the rule. This does not affect the result.
- The dependency-closed support (Var of a term together with its type) is the convention of the CaTT side conditions, so (1) applies to them directly.

### V2. Strict classification (2): correct

- The paths of the lax square are 4 vertices, 4 edges, and the two composites `p = f⁻ ∗₀ y↑` and `q = x↑ ∗₀ f⁺`: 10 in all. There are no paths of length 3.
- `F : p ⇒ q` starts at `x⁻`, which has no incoming edge, and ends at `y⁺`, which has no outgoing edge, so F has only trivial whiskers. `F ∘ F` is undefined since `p ≠ q`. So the free strict 2-category has exactly the identities `1_w` and F as 2-cells.
- S has no 3-variables, so parallel 3-terms have equal strict images automatically. Question 1 therefore really is: every pair of parallel 3-terms.

### V3. The identity-boundary filler (4): correct

- *F-count.* The F-count is a functor from the free strict 2-category to ℕ. A 2-term is F itself, a composition over a 2-dimensional arity (count = sum over all 2-variables of the arity), or a coherence over an arity of dimension ≤ 1 (no 2-inputs, count 0). So by induction, count 0 ⇔ F ∉ supp. Rechecked.
- *(3).* Applying (1) to α (no 3-variables exist), and then to t (no F), gives `supp α = supp β = supp t = supp t′ = supp(s t)`. The support of a 1-term is the vertices and edges of its flattened path; in S paths have no repeated vertex, so `ι_w` is an injective renaming onto a sub-context closed under dependencies.
- *Legality.* ᾱ and β̄ (types included) live over `C_w` and are full, and `C_w` is a pasting context. So `coh_{C_w, ᾱ→β̄}[ι_w]` is one instance of the coherence rule, with source α and target β. This includes the empty path, where `C_w` is a point.
- **So question 1 is settled for every pair of parallel 3-terms whose 2-boundary is an identity.** Open: the F-boundary case.

### V4. The arity reduction (7): correct

- A 3-term over a 2-dimensional P is a coherence, and a 2-dimensional pasting context is a sequence of columns, each a vertical chain. That is the standard decomposition.
- *Each θ is used once.* This is not "directly from the column description": it uses the count argument of V3 for each θ separately (full support ⇒ count ≥ 1), together with "count ≤ 1" in the free 2-category on P. With that line added, it holds.
- *Exactly one θ goes to F.* The F-counts add up to 1, and every 2-cell of S is `1_w` or F. Correct. 0-terms are variables, so `σ(z_{j₀−1}) = x⁻` and `σ(z_{j₀}) = y⁺` hold syntactically. Then the side columns are forced over the single vertices `x⁻` and `y⁺`, at the level of terms, by V3 in dimensions 1 and 2.
- *λ and τ.* I typechecked both on every variable. `λ[τ] = σ` holds syntactically: in the side columns τ renames x and y back to `x⁻` and `y⁺`.
- *Legality.* ū and v̄ contain every central-column variable, so they are full over Q, and d is a coherence. c̄ and d are parallel and full over Q. So `R(c) = coh_{Q, c̄→d}[τ]` is legal, with source `c̄[τ] = coh_{P,u→v}[λ[τ]] = c`.
- *The response's own assessment is right.* (7) only reduces the arity. It does not touch 3-terms whose arity is 3-dimensional, and it leaves `τ(ξ_k)` as arbitrary 2-terms.

### V5. The hemisphere reduction (8): correct

- H has no 3-variable, since X is the only one. So by (1), `supp H = supp A = Var(∂⁻U)`, and H is a weakening of a term over the 2-molecule `∂⁻U` (three faces).
- More generally: **RC(3) for 3-loops with no 3-variables reduces to the support of the base 2-term.** This applies to any context, not only the cube.

### V6. Corrections to the prompt: all confirmed

1. **Chanavat Thm 2.52** reads "Let U be a frame-acyclic n-molecule which is not an atom. Then Sd U is contractible." The prompt omitted "not an atom".
2. **Semantic freeness** is Chanavat **Thm 3.17** (Mol/X is a polygraph and a homotopy polygraph, for X with frame-acyclic molecules). **Thm 3.29** is the monoidality of `ι_s Mol/−` for the Gray product on complexes with acyclic atoms. The prompt §3 cited 3.29.
   - *Not noticed by the response:* prompt §3 also cites "Campion arXiv 2311.00205, Cor. 3.5". 2311.00205 is Campion's *Gray tensor product of (∞,n)-categories*, and its Cor. 3.5 is the strong monoidality of `S → Cat^f_ω` for a monoidally suitable site, which is what Chanavat uses to prove 3.29. The freeness statement is Campion's pasting theorem, arXiv **2311.00200** (cited correctly in §6).
3. **Frame-acyclic ≠ Steiner loop-free.** Hadzihasanovic, Comment 8.3.5: acyclicity and strong dimension-wise acyclicity correspond to Steiner's total loop-freeness and loop-freeness. Frame-acyclicity corresponds to Steiner's "split". Example 8.3.12 is a 3-atom that is frame-acyclic but not dimension-wise acyclic, so by Prop. 8.3.6 it is not Steiner loop-free. The prompt's "molecules are loop-free" (§3) and the two classes in question 3 should be kept apart. §3's motivation is not affected: the Eckmann–Hilton context needs a cell `a : id_x → id_x` with degenerate boundary, which no regular directed complex has. Which form of loop-freeness a proof of RC(3) can use for all frame-acyclic molecules is part of question 3.
4. **Di Vittorio**, p. 3: the theorem covers only composites output by the pasting algorithm. "Every possible composite in the free Gray-category … arises in this way" is said to be beyond the scope of the paper, and the relation is called an open problem. Confirmed.

The response's analysis of what Sd-contractibility does not give (items 1–4 of its §5) is also correct. Contractibility of the indexing poset only compares the chosen composites. Requirement 4 (control of arbitrary terms) is RC itself.

### V7. Consequences for the project

- **Question 1 now reduces to the F-boundary case**, and within it, coherence 3-terms over 2-dimensional arities reduce by (7) to coherences over a vertical chain Q. What is left: 3-terms with 3-dimensional composition arities, and compatibility of RC(2) comparisons for the 2-terms `τ(ξ_k)`.
- **Question 2 reduces to RC(3) for X-free 3-loops over the negative hemisphere** (three faces).
- **(1) is a general tool.** It is the total-support form of BM Lemma 36, usable for "N ⇐ RC" and wherever a filler must be built over the support of its boundary (`relative-coherence.md`, D3a).
- **Corrections that also apply to our notes.** `gray-contexts-in-catt.md` and `relative-coherence.md` should cite Chanavat Thm 2.52 with "not an atom", Thm 3.17 for freeness, and Campion 2311.00200 for the pasting theorem. Their hypotheses should keep frame-acyclic and Steiner loop-free apart.
- **Updated prompt.** It should start from the F-boundary case of the lax square, state V3–V5 as known, and make the citation fixes. It is owed by the owner of D2 (NGC).
