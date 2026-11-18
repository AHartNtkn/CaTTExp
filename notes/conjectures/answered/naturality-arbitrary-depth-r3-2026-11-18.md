# Problem: naturality of CaTT coherences at depth ≥ 2, round 3

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first. Rounds 1 and 2 and their verified answers are archived in `answered/naturality-arbitrary-depth-2026-11-18.md` and `answered/naturality-arbitrary-depth-r2-2026-11-18.md`; this prompt does not re-ask anything answered there.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory whose models are weak ω-categories. We use the syntax of Benjamin–Markakis–Offord–Sarti–Vicary (BMOSV, [arXiv 2501.11620](https://arxiv.org/abs/2501.11620), §2).

```
Types          A ::= ⋆ | u →_A v
Terms          t ::= x | coh_{P, A}[γ]
Contexts       Γ ::= ∅ | Γ, x : A
Substitutions  γ ::= ⟨⟩ | ⟨γ, x ↦ t⟩
```

- `dim ⋆ = −1`, `dim(u →_A v) = dim A + 1`; a term of type A has dimension `dim A + 1`. For `t : u → v` write `σt = u`, `τt = v`, and `σᵏ, τᵏ` for iterates.
- `Var(t : A)` is the set of free variables of t and A.
- A **pasting context** `P ⊢ps` is a context presenting a globular pasting diagram (Finster–Mimram's rules). It has source and target boundaries `∂⁻P`, `∂⁺P`, again pasting contexts.
- **Coherence rule.** If `P ⊢ps`, `P ⊢ u →_A v` and `Δ ⊢ γ : P`, then `Δ ⊢ coh_{P, u→_A v}[γ] : (u →_A v)[γ]`, provided either
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality. There is nothing else.
- Binary composites `u ∗_k v` (including whiskerings, when the dimensions differ) are coherences over the pasting context of two discs glued along a k-disc. Their boundaries are computed componentwise, syntactically.

### 1.2 Strict interpretation

Every CaTT context Γ is a finite computad (polygraph); write `F(Γ)` for the free *strict* ω-category on it. Strict ω-categories are models of CaTT, so every term t of Γ has a strict image `π(t)` in `F(Γ)`: a coherence is sent to the unique strict composite of its arity. (In a strict ω-category, any two full parallel terms over a pasting context are equal.)

### 1.3 The cylinder context Q↑Y

Let P be a pasting context and `Y ⊆ Var(P)` **up-closed**: if `y ∈ Y` occurs in the type of x, then `x ∈ Y`. The **depth** of Y in a term `t : A` is `max { dim t − dim y : y ∈ Var(t : A) ∩ Y }`.

Suppose that every term w of dimension `< n` with `Var(w) ∩ Y ≠ ∅` already has a "cylinder" `w↑`, and two copies `w⁻`, `w⁺`. If `Var(w) ∩ Y = ∅`, put `w⁻ = w⁺ = w`, and **omit** every factor `w↑` below (literal deletion of that binary composite). For a term t of dimension `n ≥ 1` define

```
a_t := ( … ((t⁻ ∗₀ (τⁿt)↑) ∗₁ (τⁿ⁻¹t)↑) … ) ∗_{n−1} (τt)↑
b_t := (σt)↑ ∗_{n−1} ( … ((σⁿ⁻¹t)↑ ∗₁ ((σⁿt)↑ ∗₀ t⁺)) … )
```

and `a_t := t⁻`, `b_t := t⁺` for n = 0. For n = 1 this is the lax square `t⁻ ∗₀ (τt)↑ → (σt)↑ ∗₀ t⁺`.

**Lemma 1.** If each lower `w↑` has type `a_w → b_w`, then `a_t, b_t : a_{σt} → b_{τt}` are well typed. (Uses that terms disjoint from Y have boundaries disjoint from Y.)

The context `P↑Y` keeps each `x ∉ Y` and replaces each `x ∈ Y` by `x⁻, x⁺` (copies, with Y-variables in their types renamed to the same sign) and `x↑ : a_x → b_x`. By Lemma 1 it is well formed. It is not a pasting context in general. For `Y = Var(P)` it presents the strict Gray cylinder: with Steiner's sign convention the formulas give `I ⊗ P`.

**Example (the lax square).** `P = (x, y, f : x → y)`, `Y = Var(P)`:

```
x⁻, x⁺, x↑ : x⁻ → x⁺,   y⁻, y⁺, y↑ : y⁻ → y⁺,
f⁻ : x⁻ → y⁻,   f⁺ : x⁺ → y⁺,   f↑ : f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺.
```

### 1.4 Naturality terms and Conjecture N

Naturality terms are defined by recursion: `x↑` is the variable for `x ∈ Y`, and

```
(coh_{Q,B}[γ])↑ := K(Q, B, γ⁻¹Y)[γ↑]
```

where `γ⁻¹Y = { q : Var(q[γ]) ∩ Y ≠ ∅ }` (up-closed in Q) and `γ↑` sends `q^± ↦ (q[γ])^±`, `q↑ ↦ (q[γ])↑`, and `q ↦ q[γ]` for q outside `γ⁻¹Y`. The recursion runs by dimension, and within a dimension by structural induction on the term (a composite's top arity variables are sent to terms of the same dimension, which are proper subterms). Its only non-syntactic ingredient is the family K:

> **Conjecture N.** For every pasting context Q, every type B full in Q, and every non-empty up-closed `Y ⊆ Var(Q)`, the type `a_c → b_c`, where `c = coh_{Q,B}[id]`, is inhabited in `Q↑Y`.

Given N, every CaTT context Γ (not only pasting ones) gets cylinder contexts `Γ↑X` and naturality terms `t↑ : a_t → b_t` for every term t, by substitution. For `X = Var(Γ)` this is the context `Γ ⊗ D¹` (lax transformations out of Γ), and iterating on the top layer gives `Γ ⊗ Dⁿ`.

## 2. What is known

Write RC(n) for the property:

> **RC(n) for a context Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

1. **Depth ≤ 1.** BMOSV, Theorem 3.1.
2. **RC(2) holds in every CaTT context** (Theorem A).
   - Normalize every 2-term to a vertical composite of whiskered 2-variables.
   - 2-terms without 2-variables pull back to the chain of their path.
   - Two such composites with the same strict image are related by exchange moves, each a coherence over a pasting context.
3. **N follows from RC.** Under the strict collapse `F(I ⊗ Q) → F(Q↑Y)`, the cell `e ⊗ π(c)` goes `π(a_c) → π(b_c)`.
   - If c is a coherence, then `π(a_c) = π(b_c)`, and RC(n) for `Q↑Y` gives K.
   - If c is a composition, realise each whiskered top generator of the strict cell as a layer, and connect consecutive layers by RC(n).
   - So **RC(n) on the cylinders `Q↑Y` implies N for coherences of dimension n.**
4. **N holds for every term of dimension ≤ 2**, for every Q and every up-closed Y. This gives `Γ ⊗ D¹` for every Γ of dimension ≤ 3, and `Γ ⊗ Dⁿ` for every n when `dim Γ ≤ 2`.
5. **Explicit 3-dimensional instances** (round 1).
   - Fix the lower lifts universally: the lift `C(A, B)` of a vertical composite, and the lift `J` of an identity 2-cell. Then the 3-dimensional unitor `α ∗₁ id_g → α` over the 2-disc has an explicit K.
   - One explicit non-endomorphism 3-dimensional instance over the single arrow `(x, y, f)` is also known.
   - The 3-dimensional associator naturality over the fully selected 3-chain has been built and machine-checked.
6. **Endomorphism coherences, every dimension.** For `c : u → u` with u full in Q, N holds for any choice of lower lifts. The coherence rule gives `c → 1_u`, and unit absorption finishes.
7. **Partial RC(3) for the lax square S** (the §1.3 example, with `F := f↑`).
   - Every 2-cell of `F(S)` is either an identity on a path or F.
   - **Identity 2-boundary: settled.** Parallel 3-terms whose strict 2-boundary is an identity do not use F. By the total-support form of Benjamin–Markakis Lemma 36, they live over the path context `C_w`, and one coherence there connects them.
   - **F-boundary, 2-dimensional coherence arity: reduced.** Such a coherence is connected to a coherence over a vertical 2-chain, but the 2-terms substituted into that chain are arbitrary.
   - **Terms without 2-variables:** connected in every dimension, in any context.
   - In any coherence touching F, F's boundary `f⁻ ∗₀ y↑` is never split across columns.
8. **RC(3) for the lax square S, all cases (round 2, proved on paper).** Any two parallel 3-terms of S are connected by a 4-term, so K(Q, B, Var Q) exists for every 3-dimensional coherence over the single arrow. The method:
   - *Active-column factorisation.* For a 2-term T = coh_{P,A}[γ] with π(T) = F, exactly one 0-column of the arity P carries F, and it spans x⁻ → y⁺; every other column sits at the point x⁻ or y⁺ (S has no directed loops there), so it factors literally through a point context. Hence γ = δ[η] with δ landing in a vertical chain C_k, and the factorised constructor H = coh_{P,A}[δ] is literally unchanged by any substitution C_n → S sending the full word to F.
   - *Normalisers* ν_T : T → N_F(σT, τT) = (κ_p(σT, p) · F) · κ_q(q, τT), defined by the factorisation and a fixed vertical fold, with associativity/unit/mixed 4-laws given by coherences on path contexts and small vertical pasting contexts (e.g. V(1,0,1) for the interchange of two path contractions around F).
   - *Evaluation fusion:* ν_{u[σ]} is 4-connected to (relative normaliser of u)[σ] followed by the fold; then every 3-term G with F-boundary gets Λ_G : G ; ν_{T′} → ν_T by induction on its syntax (2- and 3-dimensional arities, the latter via the 3-chains of the retained column V(k₁,…,k_m)), and right cancellation of the invertible ν gives the filler.
   - *Where it uses the square:* x⁻ is the unique source and y⁺ the unique sink, so discarded columns are point-supported. In a general cylinder Q↑Y, discarded columns can carry nonidentity paths, and literal stability fails.
9. **Dimension of the global-choice question.** A K for an n-dimensional coherence is an (n+1)-cell; comparing two choices of K is an (n+2)-cell.

## 3. What remains, and why

RC(3) fails for loopy contexts such as (x : ⋆, a : id_x → id_x): the weak free object groupoidifies to S² and the strict one to K(ℤ,2), and π₃(S²) = ℤ. So a proof must use acyclicity. For the lax square (item 8) the proof used that the F-carrying column always spans the unique source and the unique sink. The next cylinders do not have this: in the cylinder of the composable pair (x → y → z), a 2-term whose strict image is the lax square of the first arrow can be followed horizontally by a nonidentity path, so the discarded columns are no longer point-supported.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: RC(3) on the cylinder of a composable pair.** Let Q = (x, y, z, f : x → y, g : y → z) and Y = Var(Q), so Q↑Y is two lax squares F_f, F_g glued along y↑. Prove that any two parallel 3-terms of Q↑Y with equal strict image are connected by a 4-term. The new feature: a 2-term with image F_f ∗₀ g⁺ (or whiskered by paths on either side) has active columns that are not at the extreme vertices. Does a factorisation through a "horizontal word of vertical chains", stable under substitution, replace item 8's point-support step?
   - *Alternative smallest case:* the cylinder of the 2-disc Q = (x, y, f, g : x → y, A : f ⇒ g) with Y = Var(Q), which has a 3-variable A↑.
2. **Global choice of K in dimension 3 (corrected).** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with Y = Var(Q), compatible with substitution. Two choices of K for the same (Q, B, Y) are 4-cells; the minimal requirement is a **5-cell** between them (item 9).
3. **RC(3) on all cylinders.** Prove RC(3) for every cylinder Q↑Y, or for every finite Steiner loop-free context. Or give a loop-free counterexample.
4. **All dimensions.** Prove RC(n) for all n on the cylinders Q↑Y. By §2 item 3, this proves Conjecture N at every depth.

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) for the cylinders or for loop-free contexts; a counterexample (a cylinder Q↑Y, or a loop-free context, with two parallel n-terms of equal strict image and no term between them); or a published reference.

## 6. Literature (searched 2026-11-18)

- BMOSV, *Naturality for higher-dimensional path types*, [arXiv 2501.11620](https://arxiv.org/abs/2501.11620): depth ≤ 1. Its v3 says higher-depth cases are beyond the paper.
- Benjamin–Markakis–Sarti, *Invertible cells in ω-categories*, [arXiv 2406.12127](https://arxiv.org/abs/2406.12127), including Lemma 36, the support lemma. ICaTT, [arXiv 2602.16602](https://arxiv.org/abs/2602.16602): composites of coherences are invertible.
- Mikhail, *A type-theoretic definition of lax (∞,∞)-limits*, [arXiv 2412.13310](https://arxiv.org/abs/2412.13310), Thm 4.4: the contexts `Γ ⊗ D¹` for globular Γ, without the terms K.
- The (∞,ω) analogue:
  - Campion's pasting theorem, [arXiv 2311.00200](https://arxiv.org/abs/2311.00200);
  - Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), Thm 3.17.
  - No comparison with CaTT's models is known.
- Steiner, *Omega-categories and chain complexes*, HHA 6 (2004): loop-free bases and Gray tensors.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): Squier-style coherence.

# Researcher Response

**Question 1 has a positive answer for the cylinder of the composable pair, using the round-2 construction stated in §2.8.** The additional ingredient is a relative normalizer for a square with one fixed incoming or outgoing edge.

The required retained pasting contexts are
\[
C_n,\qquad C_n*_0D^1(h),\qquad D^1(h)*_0C_n,
\]
and their 3-dimensional versions. In the second and third families, the substitution sends \(h\) to the corresponding edge variable **literally**. That restriction supplies the substitution stability that was missing.

Below is a term-building proof. It proves RC(3) for the composable-pair cylinder and hence gives \(K\) for every 3-dimensional coherence over that pair. It does not settle the alternative 2-disc case or Questions 2–4.

## 1. Strict 2-cells and the exact middle boundary

Write
\[
X=x^\uparrow,\qquad Y=y^\uparrow,\qquad Z=z^\uparrow,
\]
and
\[
F:f^-*_0Y\longrightarrow X*_0f^+,\qquad
G:g^-*_0Z\longrightarrow Y*_0g^+.
\]

Define the actual CaTT 2-terms
\[
L=f^-*_0G,\qquad R=F*_0g^+.
\]

Use juxtaposition below only for **flattened strict 1-paths**, and put
\[
w_2=f^-g^-Z,\qquad
w_1=f^-Yg^+,\qquad
w_0=Xf^+g^+.
\]

The nonidentity strict 2-cells are exactly:

| Strict 2-cell | Flattened source | Flattened target |
|---|---|---|
| \(\pi F\) | \(f^-Y\) | \(Xf^+\) |
| \(\pi G\) | \(g^-Z\) | \(Yg^+\) |
| \(\pi L\) | \(w_2\) | \(w_1\) |
| \(\pi R\) | \(w_1\) | \(w_0\) |
| \(H=\pi L*_1\pi R\) | \(w_2\) | \(w_0\) |

Indeed, every directed 1-path crosses from the minus layer to the plus layer at most once. Applying \(G\), then \(F\), moves that crossing successively to the left:
\[
w_2\longrightarrow w_1\longrightarrow w_0.
\]
There is no other rewrite sequence. Two nonidentity 2-cells cannot be horizontally composable: each has a minus vertex as 0-source and a plus vertex as 0-target.

The strict product defining \(H\) is **not** yet a CaTT composite. Its middle boundaries are
\[
\tau L=f^-*_0(Y*_0g^+),\qquad
\sigma R=(f^-*_0Y)*_0g^+.
\]
Let
\[
s=\kappa_{w_1}(\tau L,\sigma R):\tau L\longrightarrow\sigma R,
\]
where \(\kappa_w(A,B)\) is the path-context coherence between 1-terms with flattened path \(w\). Fix
\[
C=(L*_1s)*_1R.
\tag{1}
\]
Then \(\pi C=H\), with literal matching of all composition boundaries.

We also need the following support reductions.

- A 2-term with strict image \(F\), respectively \(G\), is a term of its square.
- A 2-term with strict image \(R\) is a term of the first square together with \(g^+\).
- A 2-term with strict image \(L\) is a term of \(f^-\) together with the second square.
- The same reductions hold for 3-terms with these strict 2-boundaries.

For 2-terms, this follows by induction through the arity substitutions: generator multiplicities in the strict 2-image are nonnegative, so a term with image \(R\) cannot use \(G\); its remaining 1-variables belong to the paths used by \(F\) and \(g^+\). For 3-terms, the absence of 3-generators gives equality of their 2-support with the 2-support of either boundary, by Lemma 36. The remaining path-support argument is the one used in round 2. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

Thus the new cases are \(R\), \(L\), and \(H\).

## 2. The fixed-edge extension lemma

We first prove:

> **Fixed-edge extension lemma.** Let \(S\) be the lax square with 2-generator \(F:p\to q\). Adjoin a fresh edge
> \[
> h:b\longrightarrow c
> \]
> at its terminal vertex \(b\). Then RC(3) holds in the resulting context. The corresponding assertion holds for a fresh edge adjoined at the initial vertex.

The only new nonidentity strict 2-cell is
\[
E=F*_0h.
\]

### 2.1 The retained arities

Let \(C_n\) be the vertical 2-chain with parallel 1-variables
\[
u_0,\ldots,u_n:a\to b
\]
and 2-variables
\[
A_i:u_{i-1}\to u_i,\qquad 1\leq i\leq n.
\]
Set
\[
D_n=C_n*_0D^1(h).
\]

For 3-arities, write \(V(k_1,\ldots,k_n)\) for the vertical pasting context with
\[
A_{i,0},\ldots,A_{i,k_i}:u_{i-1}\to u_i,
\]
and
\[
M_{i,j}:A_{i,j-1}\to A_{i,j}.
\]
When every \(k_i=0\), this is \(C_n\).

All of
\[
C_n,\quad D_n,\quad V(\mathbf k),\quad V(\mathbf k)*_0D^1(h)
\tag{2}
\]
are pasting contexts.

Consider a constructor
\[
T=\operatorname{coh}_{P,B}[\gamma]
\]
whose strict 2-image is \(E\). Each 0-variable of \(P\) maps to a common vertex of the source and target paths of \(E\). Those common vertices are precisely \(a,b,c\).

There is one 0-column with nonidentity 2-image, and it has one of two endpoint pairs.

1. **Endpoints \(a,c\).** Every other column is point-supported. Retaining this column gives an exact factorization through \(C_k\).

2. **Endpoints \(a,b\).** Columns to its left are point-supported. The nonconstant part to its right is supported on the single edge \(h\). Lift those terms literally to \(D^1(h)\), and retain the active column. This gives an exact factorization through \(D_k\).

Thus
\[
\gamma=\delta[\eta],\qquad
T=H[\eta],\qquad
H=\operatorname{coh}_{P,B}[\delta].
\tag{3}
\]
This is equality of substitutions and terms, not a comparison cell.

The factorization retains **every vertical position** of the selected column, including positions whose assigned 2-term has identity strict image.

The same argument for a 3-constructor retains either
\[
V(\mathbf k)
\quad\text{or}\quad
V(\mathbf k)*_0D^1(h).
\]
An inactive column’s 3-arguments have identity strict 2-boundaries. They are therefore path-supported and lift literally to the appropriate point or edge context.

### 2.2 Exact stability

For evaluations of \(D_n\), require:

- its three 0-variables map to the three indicated, distinct vertices;
- \(h\mapsto h\) literally;
- the vertical word maps to \(F\).

For evaluations of \(C_n\), its endpoints map to \(a,c\), and its vertical word maps to \(E\).

Under these evaluations, the factorized head \(H\) in (3) is unchanged:

- point-supported terms retain their syntax under the fixed renaming;
- edge-supported terms retain their syntax because \(h\) is fixed;
- the retained vertical arguments are still represented by the same fresh variables.

An internal constructor on \(D_n\) can itself retain either a \(D_k\)-frame or a whole-span \(C_k\)-frame. In the former case, its new edge maps to the old \(h\) literally. Thus this family is closed under the factorizations used by the recursion.

This proves the required stability without asking for stability under arbitrary substitutions for a 1-argument.

## 3. The additional 3- and 4-cell constructors

Write
\[
U\cdot V=U*_1V,\qquad M;N=M*_2N,\qquad W_h(U)=U*_0h.
\]
Every displayed comparison between 3-terms below is a 4-term. Changes of parentheses in a sequence of 3-cells use the 4-associator.

### 3.1 Fixed whiskering

Choose
\[
d_h(U,V):
W_hU\cdot W_hV\longrightarrow W_h(U\cdot V)
\tag{4}
\]
as the direct 3-coherence on \(C_2*_0D^1(h)\), and
\[
t_h(A):W_h(1_A)\longrightarrow1_{W_hA}
\tag{5}
\]
as a 3-coherence on the two-edge path \((A,h)\).

Here are the required 4-comparisons and their arities.

| Comparison | Pasting arity |
|---|---|
| Naturality of \(d_h\) in two 3-arguments | \(V(1,1)*_0D^1(h)\) |
| Associativity of \(d_h\) | \(C_3*_0D^1(h)\) |
| Left and right unit laws for \(d_h,t_h\) | \(D^2*_0D^1(h)\) |
| \(W_h(M;N)\to W_hM;W_hN\) | \(V(2)*_0D^1(h)\) |

For example, with \(M:U_0\to U_1\) and \(N:V_0\to V_1\), the naturality comparison is
\[
\begin{aligned}
&(W_hM\cdot W_hV_0);
 (W_hU_1\cdot W_hN);
 d_h(U_1,V_1)
\\
&\hspace{12mm}\longrightarrow
d_h(U_0,V_0);
W_h\bigl((M\cdot V_0);(U_1\cdot N)\bigr).
\end{aligned}
\tag{6}
\]

Writing \(a\) for the 3-associator of \(\cdot\), the associativity comparison is
\[
\begin{aligned}
&(d_h(U,V)\cdot W_hT);
 d_h(U\cdot V,T);
 W_h a(U,V,T)
\\
&\hspace{8mm}\longrightarrow
a(W_hU,W_hV,W_hT);
(W_hU\cdot d_h(V,T));
d_h(U,V\cdot T).
\end{aligned}
\tag{7}
\]

The unit comparisons are
\[
d_h(1_A,U);W_h\ell_U
\longrightarrow
(t_h(A)\cdot W_hU);\ell_{W_hU},
\tag{8}
\]
and
\[
d_h(U,1_B);W_h\rho_U
\longrightarrow
(W_hU\cdot t_h(B));\rho_{W_hU}.
\tag{9}
\]

Each pair consists of parallel full 3-terms on the stated pasting context. Its comparison is therefore one application of the coherence rule there. These definitions allow arbitrary substitution for the 2- and 3-arguments.

### 3.2 Path comparisons after whiskering

For 1-terms \(A,B\) with common flattened path \(w\), choose
\[
r^h_{AB}:
W_h\kappa_w(A,B)
\longrightarrow
\kappa_{wh}(A*_0h,B*_0h)
\tag{10}
\]
as a 3-coherence on the **expanded path context** \(C_{wh}\).

Let
\[
m^w_{ABC}:
\kappa_w(A,B)\cdot\kappa_w(B,C)
\longrightarrow\kappa_w(A,C).
\]
The comparison
\[
\begin{aligned}
&d_h(\kappa_w(A,B),\kappa_w(B,C));
 W_hm^w_{ABC};
 r^h_{AC}
\\
&\hspace{8mm}\longrightarrow
\operatorname{Map}_{\cdot}(r^h_{AB},r^h_{BC});
m^{wh}_{Ah,Bh,Ch}
\end{aligned}
\tag{11}
\]
is a direct 4-coherence on \(C_{wh}\). Here \(Ah\) abbreviates the actual term \(A*_0h\), and
\[
\operatorname{Map}_{\cdot}(M,N)
=(M\cdot V_0);(U_1\cdot N).
\]

The analogous unit comparison is also a direct path coherence.

In particular, when \(w=p=f^-Y\), the arity in (10)–(11) is the actual three-edge path \(f^-,Y,h\).

### 3.3 Whiskering a normal form

Use the square normal form
\[
N_F(A,B)
=
\bigl(\kappa_p(A,p)\cdot F\bigr)\cdot\kappa_q(q,B),
\]
and the corresponding new normal form
\[
N_E(A',B')
=
\bigl(\kappa_{ph}(A',p*_0h)\cdot E\bigr)
 \cdot\kappa_{qh}(q*_0h,B').
\]

There is an explicit 3-term
\[
\phi^h_{AB}:W_hN_F(A,B)\longrightarrow N_E(Ah,Bh).
\tag{12}
\]

Put \(l=\kappa_p(A,p)\), \(r=\kappa_q(q,B)\). Its four successive steps are
\[
\begin{aligned}
&W_h((l\cdot F)\cdot r)
\\
&\xrightarrow{d_h^{-}(l\cdot F,r)}
 W_h(l\cdot F)\cdot W_hr
\\
&\xrightarrow{d_h^{-}(l,F)\cdot W_hr}
 (W_hl\cdot E)\cdot W_hr
\\
&\xrightarrow{(r^h_{A,p}\cdot E)\cdot W_hr}
 \bigl(\kappa_{ph}(Ah,ph)\cdot E\bigr)\cdot W_hr
\\
&\xrightarrow{(\kappa_{ph}(Ah,ph)\cdot E)\cdot r^h_{q,B}}
 N_E(Ah,Bh).
\end{aligned}
\]
The superscript \({}^{-}\) denotes a chosen reverse coherence, not a strict inverse equation.

For an identity-valued normal form, define \(\phi^h\) to be (10).

### 3.4 Compatibility with the vertical fold

Let \(\mu\) be the round-2 multiplication of normal forms. Its nontrivial cases are:

- identity followed by identity: \(m^w\);
- identity followed by \(F\): reassociate, then contract the two initial \(p\)-path comparisons;
- \(F\) followed by identity: reassociate, then contract the two final \(q\)-path comparisons.

Use the same definitions for \(\mu^h\), with \(E\) and the expanded paths.

The required compatibility is the 4-term
\[
\boxed{
d_h(N_U,N_V);
W_h\mu_{U,V};
\phi^h_{UV}
\longrightarrow
\operatorname{Map}_{\cdot}(\phi^h_U,\phi^h_V);
\mu^h_{U,V}.
}
\tag{13}
\]

Here is an explicit construction of the case identity/\(F\), which is the case where the split boundary matters.

Write
\[
a=\kappa_p(A,B),\quad b=\kappa_p(B,p),\quad
c=\kappa_q(q,C),\quad
a'=\kappa_p(A,p),
\]
and \(m:a\cdot b\to a'\). Define
\[
\operatorname{Exp}(U,V,T)
=
d_h^{-}(U\cdot V,T);
\bigl(d_h^{-}(U,V)\cdot W_hT\bigr),
\]
and
\[
j(a,b;F,c)
=
a^{-}_{a,b\cdot F,c};
\bigl(a^{-}_{a,b,F}\cdot c\bigr).
\]
Thus
\[
j(a,b;F,c):
a\cdot((b\cdot F)\cdot c)
\longrightarrow
((a\cdot b)\cdot F)\cdot c.
\]

Construct (13) in this order.

1. **Move expansion before the path multiplication.** Take the direct 4-coherence on
   \[
   V(1,0,0)*_0D^1(h)
   \]
   comparing
   \[
   W_h((M\cdot F)\cdot c);
   \operatorname{Exp}(L_1,F,c)
   \]
   with
   \[
   \operatorname{Exp}(L_0,F,c);
   ((W_hM\cdot W_hF)\cdot W_hc).
   \]
   Substitute \(L_0=a\cdot b\), \(L_1=a'\), \(M=m\).

2. **Collect the distributors before the contractions.** Put
   \[
   E_0=
   \bigl(W_ha\cdot\operatorname{Exp}(b,F,c)\bigr);
   j(W_ha,W_hb;W_hF,W_hc).
   \]
   On \(C_4(a,b,F,c)*_0D^1(h)\), take the direct 4-coherence between
   \[
   d_h(a,(b\cdot F)\cdot c);
   W_hj(a,b;F,c);
   \operatorname{Exp}(a\cdot b,F,c)
   \]
   and
   \[
   E_0;((d_h(a,b)\cdot W_hF)\cdot W_hc).
   \]

3. **Apply the path comparison (11).** The remaining initial-path expression is
   \[
   d_h(a,b);W_hm;r^h_{A,p}.
   \]
   Replace it using (11), formed on \(C_{ph}\), and whisker that 4-cell by \(E\) and the final path factor.

4. **Put the two routes in the same order.** Use vertical 4-interchange and associator naturality to commute the final \(r^h_{q,C}\) past the initial-path comparison. These are direct coherences on vertical pasting contexts, with the entire intervening 2-term substituted for a 2-variable.

Both routes now have the same expression. The \(F\)/identity case uses the corresponding construction on \(C_{qh}\). The identity/identity case is (11).

This construction treats the targets \(\kappa_{wh}\) as actual path terms. It never requires them to be syntactically whiskered \(\kappa_w\)-terms.

## 4. Normalizers and evaluation fusion for the fixed-edge extension

The new comparisons above suffice to extend the round-2 recursion.

### 4.1 Relative normal forms

For a 2-term \(u\) on \(D_n\) with strict word
\[
(A_{i+1}\cdots A_j)*_0h,
\]
define its relative normal form by
\[
B(u)=
\Bigl(
\kappa_{u_i h}(\sigma u,u_i*_0h)
\cdot
\bigl(\operatorname{word}(A_{i+1},\ldots,A_j)*_0h\bigr)
\Bigr)
\cdot
\kappa_{u_jh}(u_j*_0h,\tau u).
\tag{14}
\]
Fix left-associated brackets for \(\operatorname{word}\).

On \(C_n\), omit the final whisker and use the round-2 formula. For an identity strict word, use the single path comparison
\[
B(u)=\kappa_w(\sigma u,\tau u).
\]

Each construction uses its indicated consecutive subframe and is then weakened to the ambient frame.

For a factorized head \(H\) on \(R=C_k\) or \(D_k\), choose
\[
v_H=\operatorname{coh}_{R,H\to B(H)}[\mathrm{id}_R].
\tag{15}
\]
Both 2-terms are full in \(R\). In particular, (15) absorbs every path-supported argument of the discarded columns.

### 4.2 The evaluation fold is a separate operation

Define an evaluator \(D\) on expressions built from:

- substituted 2-letters;
- path-only 2-factors;
- vertical products;
- the fixed whiskering \(W_h\).

Its clauses are:

\[
\begin{aligned}
D_{\text{letter }A}&=\nu_{A[\sigma]},\\
D_{\text{path factor}}&=\text{its path-context normalizer},\\
D_{U\cdot V}&=
\operatorname{Map}_{\cdot}(D_U,D_V);\mu,\\
D_{W_hU}&=W_hD_U;\phi^h.
\end{aligned}
\tag{16}
\]

In particular, \(D_{B,\sigma}\) is **not defined to be**
\(\nu_{B[\sigma]}\).

For an actual \(E\)-valued 2-constructor \(T=H[\eta]\), define
\[
\nu_T=v_H[\eta];D_{B(H),\eta}.
\tag{17}
\]
In the \(C_k\)-case, the letter normalizers in (16) concern proper \(E\)-valued subterms. In the \(D_k\)-case, they concern square-valued subterms, whose normalizers are already available. Thus (17) is well founded.

Define relative normalizers
\[
\lambda_u:u\longrightarrow B(u)
\]
by the same head recursion on the generic frames. Their folds use vertical associators and unitors, path contractions, and \(d_h^{\pm},t_h^{\pm}\). At a generic 2-variable, use the padding coherence on its 2-disc.

### 4.3 The new fold-evaluation case

The new elementary fold step is \(d_h(U,V)\). Its compatibility with (16) is the following composite of 4-cells:
\[
\begin{aligned}
d_h(U,V);D_{W_h(U\cdot V)}
&\Longrightarrow
\operatorname{Map}_{\cdot}(W_hD_U,W_hD_V);
d_h(N_U,N_V);
W_h\mu;
\phi^h
\\
&\Longrightarrow
\operatorname{Map}_{\cdot}(W_hD_U,W_hD_V);
\operatorname{Map}_{\cdot}(\phi^h_U,\phi^h_V);
\mu^h
\\
&\Longrightarrow
D_{W_hU\cdot W_hV}.
\end{aligned}
\tag{18}
\]
The first step uses (6) and preservation of 3-composition by \(W_h\). The second is (13). The third is functoriality of the vertical word action, supplied by coherences on vertical 3-pastings.

The \(t_h\)-case has path-only boundaries and is a direct path 4-coherence. All other fold steps are the vertical and path steps from round 2.

Consequently, structural induction on a generic 2-term gives
\[
\boxed{
\mathcal E_{u,\sigma}:
\nu_{u[\sigma]}
\longrightarrow
\lambda_u[\sigma];D_{B(u),\sigma}.
}
\tag{19}
\]

The induction has four cases.

- If the evaluated term is path-only, both routes are compared on its actual path context.
- Square-valued terms use the round-2 construction.
- At a variable, naturality of the padding coherence on a 3-disc, followed by the fold’s unit comparisons, gives (19). The padding is not identified with an identity.
- At a new constructor, exact stability makes the leading \(v_H\) on the two routes literally the same. Apply the induction hypotheses to its proper arguments, then use the fold comparisons, including (18).

This establishes the needed fusion statement for both retained frame families.

## 5. The 3-term induction and cancellation

For every 3-term \(G:T\to T'\) with strict 2-boundary \(E\), construct
\[
\Lambda_G:G;\nu_{T'}\longrightarrow\nu_T.
\tag{20}
\]

There are two retained-arity cases.

### 5.1 Retained arity of dimension 2

Suppose the head factors through \(R=C_n\) or \(D_n\), and write
\[
H:U\longrightarrow V
\]
for the factorized head.

Since \(U,V\) are parallel and full, their relative normal forms are literally equal:
\[
B(U)=B(V).
\]
Take
\[
\Xi_H=
\operatorname{coh}_{R,\,
(H;\lambda_V)\to\lambda_U}
[\mathrm{id}_R].
\tag{21}
\]
Both endpoints are full 3-terms on the pasting context \(R\).

Substitute the actual arguments, append the common evaluation fold, and use (19). This gives (20).

### 5.2 Retained arity of dimension 3

Now let
\[
R=V(\mathbf k)
\quad\text{or}\quad
V(\mathbf k)*_0D^1(h).
\]
Let \(W\) be the action of all retained 3-chains on the central 2-word, with the identical outer path pads. In the second case, whisker the central action by \(h\).

The direct 4-coherence on \(R\) is
\[
\Xi_H:
H;\lambda_V
\longrightarrow
\lambda_U;W.
\tag{22}
\]
Both routes use every retained 3-variable and every fixed 2-position, so fullness holds.

Each actual term substituted for a retained 3-variable is a proper subterm of the original 3-constructor. Its induction hypothesis supplies (20). Applying these hypotheses through the word action, and using preservation of 3-composition by fixed whiskering, gives
\[
W[\sigma];D_{B(V),\sigma}
\longrightarrow
D_{B(U),\sigma}.
\tag{23}
\]
Equations (19), (22), and (23) compose to give \(\Lambda_G\).

If every \(k_i=0\), the retained context has dimension 2. Use (21); no 3-dimensional composition side condition is applied to that case.

### 5.3 The resulting filler

For parallel \(\alpha,\beta:T\to T'\), put
\[
r=\nu_{T'},\qquad s=\nu_T.
\]
Then
\[
\Theta=
\Lambda_\alpha *_3\overline{\Lambda_\beta}
:
\alpha;r\longrightarrow\beta;r.
\]

Choose a reverse \(\bar r\) and a cancellation 4-cell
\[
\epsilon:r;\bar r\longrightarrow1_{T'}.
\]
These are available syntactically: reverse the elementary coherence steps of \(r\), and combine their cancellation cells using the generic vertical composition coherences. Equivalently, the normalizers have empty 3-support and the constructive invertibility criterion applies. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

The required 4-term is the following fixed composite:
\[
\begin{aligned}
\alpha
&\longrightarrow \alpha;1_{T'}
\longrightarrow \alpha;(r;\bar r)
\longrightarrow(\alpha;r);\bar r
\\
&\xrightarrow{\Theta*_2\bar r}
(\beta;r);\bar r
\longrightarrow\beta;(r;\bar r)
\longrightarrow\beta;1_{T'}
\longrightarrow\beta.
\end{aligned}
\tag{24}
\]
The unnamed arrows are the indicated inverse unitor, whiskered inverse cancellation, associators, whiskered cancellation, and unitor.

This proves the outgoing fixed-edge lemma. Replacing \(W_h(U)=U*_0h\) by \(W_h(U)=h*_0U\), and replacing the retained arities by
\[
D^1(h)*_0C_n,\qquad D^1(h)*_0V(\mathbf k),
\]
gives the incoming version by the same construction.

Therefore the \(R\)- and \(L\)-cases of the pair cylinder are settled.

## 6. The remaining two-generator case

It remains to treat strict 2-value \(H\).

Use the fixed actual term \(C\) from (1), and define
\[
N_H(A,B)=
\bigl(\kappa_{w_2}(A,\sigma L)\cdot C\bigr)
\cdot\kappa_{w_0}(\tau R,B).
\tag{25}
\]

### 6.1 The factorization is point-supported again

The source and target paths of \(H\), namely \(w_2,w_0\), have only \(x^-\) and \(z^+\) as common vertices.

Hence every arity 0-variable of an \(H\)-valued constructor maps to one of those two vertices. Exactly one column spans them; all other columns are point-supported.

Thus the exact, substitution-stable factorization is through
\[
C_n\quad\text{or}\quad V(\mathbf k),
\]
precisely as in the square proof. No fixed-edge frame is needed for this case.

### 6.2 The vertical fold has one additional multiplication case

At these endpoints, the possible strict 2-values are identities, \(L\), \(R\), and \(H\). The only composable pair of nonidentity values is \(L\) followed by \(R\).

Use the fixed-edge normal forms
\[
N_L(A,B)=
\bigl(\kappa_{w_2}(A,\sigma L)\cdot L\bigr)
\cdot\kappa_{w_1}(\tau L,B),
\]
and
\[
N_R(B,D)=
\bigl(\kappa_{w_1}(B,\sigma R)\cdot R\bigr)
\cdot\kappa_{w_0}(\tau R,D).
\]

To multiply them, reassociate and apply
\[
m^{w_1}_{\tau L,B,\sigma R}:
\kappa_{w_1}(\tau L,B)\cdot
\kappa_{w_1}(B,\sigma R)
\longrightarrow s.
\tag{26}
\]
Reassociate to the brackets in (25).

All fold comparisons now have the following exhaustive description:

- overlapping path contractions lie on one of \(w_2,w_1,w_0\), and are compared there;
- contractions in different gaps commute by vertical 4-interchange, with \(L\), \(R\), or their intervening composite substituted for fixed 2-positions;
- changes of brackets and inserted units use the vertical associativity and unit comparisons.

For example, simultaneous contractions in the three gaps can be compared on
\[
V(1,0,1,0,1).
\]
There is no exchange between \(L\) and \(R\): their order is forced.

This supplies the two-letter version of the round-2 vertical fold.

### 6.3 Fusion and the 3-term induction

Define the \(H\)-normalizers by the stable-head formula (17), now using (25) and the fold just specified.

For fusion, a proper evaluated subterm has one of four kinds of strict value:

- identity: use a path 4-coherence;
- \(L\) or \(R\): use the fixed-edge theorem already proved;
- \(H\): use the structural induction hypothesis.

In the \(L\)- and \(R\)-cases, both 3-routes in the desired fusion comparison strengthen to the corresponding fixed-edge context. Its established RC(3) therefore compares them, regardless of their chosen normalizers. This introduces no circularity.

For an \(H\)-valued constructor, exact point-supported factorization gives the same leading \(v_H\) before and after evaluation. The proper-subterm comparisons and the two-letter fold give fusion.

The 3-term induction then uses exactly (21)–(23), with retained arities \(C_n\) and \(V(\mathbf k)\). Formula (24) supplies the final filler.

Every strict 2-value in the pair cylinder has now been covered. Therefore:

\[
\boxed{
\text{Any two parallel 3-terms of }Q\uparrow\operatorname{Var}(Q)
\text{ are connected by a 4-term.}
}
\]

Since this context has no 3-generators, equality of the strict images of parallel 3-terms is automatic.

## 7. Consequence for naturality

For a 3-dimensional coherence \(c\) over the composable pair, retain the already fixed lower lifts and form its actual terms \(a_c,b_c\). Define
\[
\boxed{
K(Q,B,\operatorname{Var}Q)
=
\operatorname{Fill}_{Q\uparrow\operatorname{Var}Q}(a_c,b_c),
}
\]
where \(\operatorname{Fill}\) is the construction (17)–(24), with the additional \(H\)-fold (26).

The construction works for any fixed lower lifts: the normalizers used in this proof are auxiliary and do not replace those lifts.

The extension established here depends on three precise facts: the two fixed-edge factorizations are literal, the two-generator case has point-supported discarded columns, and its nonidentity 2-generators have a forced order. The proof does not establish these conditions for arbitrary cylinders, nor does it construct the 5-cells required to compare global choices of \(K\).

**Verification scope:** the displayed distributor and expansion boundary schemas were checked symbolically without associativity or unit identifications. The complete recursive construction above is a proof on paper, not a CaTT-kernel verification.


# Verification of the researcher response (2026-11-18)

**Verdict: correct as a paper proof, at the same standard as round 2.** Question 1 is answered: RC(3) holds on the cylinder of the composable pair, so K exists for every 3-dimensional coherence over that pair. The alternative smallest case (the 2-disc cylinder), Question 2 (global K, 5-cells), Question 3 (all cylinders) and Question 4 (RC(n)) remain open.

Step by step.

1. **Strict 2-cells (§1).**
   - The strict 2-cells of F(Q↑Y) for the composable pair are the identities on paths and the cells F = F_f, G = F_g, L = f⁻ ∗₀ G, R = F ∗₀ g⁺ and H = L ∗₁ R.
   - These are exactly the non-identity 2-cells of the strict Gray cylinder I ⊗ (x → y → z): the two generating squares, their whiskerings by the remaining edge, and their vertical composite.
   - The middle boundary of H is C = (L ∗₁ s) ∗₁ R, where s is the identity on the shared middle path. It is computed correctly. ✓

2. **The fixed-edge extension lemma (§2).**
   - The 0-columns of an arity carrying F_f (or F_g) span common vertices a, b, c.
   - A column (a, c) factors through a vertical chain C_k.
   - A column (a, b) factors through D_k = C_k ∗₀ D¹(h), with h sent literally to the edge variable (y↑ in one case, g⁺ or f⁻ in the others). It does not go through a path context.
   - **Stability (§2.2).** Every substitution C_n → Q↑Y that sends the full word to the given 2-cell also sends h to the same edge variable. So the factorised constructor is unchanged, which is exactly the property round 2 got from point support. ✓

3. **The new 3- and 4-cell constructors (§3).**
   - The typing of the fixed whiskering d_h in (6) is correct.
   - The associativity comparison (7) is correct.
   - The fold-compatibility cell φ^h in (12) has matching source and target.
   - Each is a coherence over a pasting context of the shape C_n ∗₀ D¹(h) or its 3-dimensional version, so each is valid. ✓

4. **Normalisers and evaluation fusion (§4).**
   - The relative normal forms are defined over the retained arities.
   - The evaluation fold is kept separate from the vertical fold, as it must be.
   - The new fold-evaluation case is handled by φ^h. ✓

5. **The 3-term induction (§5).**
   - Retained arities of dimension 2 and 3 are treated as in round 2, with the fixed edge carried along.
   - The filler (24) uses right cancellation by the invertible normalisers, which are composites of coherences and so invertible (ICaTT). ✓

6. **The two-generator case H (§6).**
   - In a term with strict image H, the discarded columns are point-supported again, because H spans the unique source x⁻ and the unique sink z⁺.
   - L and R occur in a forced order (L before R), so the vertical fold needs only one more multiplication case, the fold (26). ✓

7. **Consequence (§7).**
   - K(Q, B, Var Q) = Fill(a_c, b_c) for every 3-dimensional coherence c over the pair, for any fixed lower lifts. ✓
   - The researcher checked the distributor and expansion boundary schemas symbolically. The full construction is a paper proof, not a kernel check.

**What the proof uses, and where it stops.**
- It uses three specific facts:
  - the two fixed-edge factorisations are literal;
  - the H case has point-supported discarded columns;
  - the 2-generators of H have a forced order.
- None of these is established for a general cylinder. For example:
  - a longer chain x → y → z → w has columns with a fixed edge on both sides;
  - Q↑Y with Y proper has unlifted edges.
- **The natural generalisation** is factorisation through "horizontal words" D¹(h₁) ∗₀ … ∗₀ C_n ∗₀ … ∗₀ D¹(h_k), with each hᵢ sent literally to an edge variable.
- **A second tool now exists.** The cone round-2 answer (`answered/cone-over-coherences-r2-2026-11-18.md`, §2) gives a syntactic dimension-lowering translation D, with RC(r+1) on a suspended context implying RC(r). An analogue for cylinders, from RC on (ΣQ)↑Y′ to RC on Q↑Y, would reduce the fixed-dimension part of Question 4.

Follow-up prompt: `answered/naturality-arbitrary-depth-r4-2026-11-18.md` (round 4, answered).
