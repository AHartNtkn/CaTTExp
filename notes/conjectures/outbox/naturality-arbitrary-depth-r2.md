# Problem: naturality of CaTT coherences at depth ≥ 2, round 2

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first. Round 1 and its verified answer are archived in `answered/naturality-arbitrary-depth-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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

## 3. What remains, and why

RC(3) fails for arbitrary contexts. In `(x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell and the identity are expected not to be connected, since they give a non-zero class in π₃(S²). (This is a sketch, not checked in detail.) So a proof must use acyclicity of the context. The cylinders `Q↑Y` present Steiner complexes with loop-free bases.

In dimension 3, runs of 3-cells without 3-variables live over a 2-dimensional context such as S, where no single pasting context covers them. For S, everything except the F-boundary case is settled (item 7). What is left is the compatibility of a chosen normalization `ν_P : P → N(P)`, for 2-terms P with image F, with `∗₁`-composition by 2-terms containing F.

Separately, N as stated lets K be chosen for each (Q, B, Y). It is not known whether one family of choices, with the lower lifts fixed universally as in item 5, works for all instances at once.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: the F-boundary case of RC(3) for the lax square S.** Let `α, β : t → t′` be parallel 3-terms of S with `π(t) = π(t′) = F`. Construct a 4-term `α → β`. This gives N for every 3-dimensional coherence over the single arrow `(x, y, f)` with `Y = Var(Q)`.
   - *Smaller first step:* take α and β to be coherences over 2-dimensional arities. They reduce to coherences over vertical 2-chains whose middle 2-terms are arbitrary. Connect those.
2. **Global choice of K in dimension 3.** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with `Y = Var(Q)`, such that the naturality terms `t↑` it defines are compatible with substitution. The minimal requirement: two choices for the same `(Q, B, Y)` are connected by a 4-term.
3. **RC(3) on the cylinders.** Prove RC(3) for every cylinder `Q↑Y`, or for every finite Steiner loop-free context. Or give a loop-free counterexample.
4. **All dimensions.** Prove RC(n) for all n on the cylinders `Q↑Y`. By item 3 of §2, this proves Conjecture N at every depth.

## 5. What counts as a solution

Any of the following counts:
- explicit terms for question 1 or 2;
- a proof of RC(3) or RC(n) for the cylinders, or for loop-free contexts;
- a counterexample: a cylinder `Q↑Y`, or a loop-free context, with two parallel n-terms of equal strict image and no term between them;
- a published reference.

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

**Question 1 admits a construction using a new choice of the 2-cell normalizers.** The key is an exact factorization through a vertical pasting context that is stable under the substitutions needed in the proof.

The construction below establishes:

> **Theorem.** In the lax square \(S\), any two parallel 3-terms are connected by a 4-term. In particular, the \(F\)-boundary case of \(\mathrm{RC}(3)\) holds.
>
> Consequently, \(K(Q,B,\operatorname{Var}(Q))\) can be constructed for every 3-dimensional coherence over the single-arrow context \(Q=(x,y,f)\).

The proof does not establish Questions 2–4. Its essential restriction is that \(F\) spans the initial and terminal vertices of the square, so every horizontal factor before or after an expression with strict image \(F\) is supported at one endpoint.

I use the path-support and path-filling results stated in §2.7 of your prompt as established inputs. The support argument is the one underlying Benjamin–Markakis’s Lemma 36. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

## 1. Conventions and elementary constructions

Write
\[
p=f^-*_0y^\uparrow,\qquad q=x^\uparrow*_0f^+,\qquad F:p\Rightarrow q.
\]

For readability, write
\[
U\cdot V:=U*_1V,\qquad r;s:=r*_2s.
\]
Thus \(\cdot\) also denotes dimension-1 whiskering when the dimensions differ. Products displayed without parentheses are left-associated.

The notation
\[
r\simeq_4 s
\]
will mean a **constructed 4-cell** \(r\to s\), with a constructed reverse. It never means definitional equality.

Every reassociation of a product of 3-cells below uses the 4-coherence on the corresponding vertical 3-chain.

### Path comparisons

If \(A,B\) are 1-terms with the same flattened path \(w\), let
\[
\kappa_w(A,B):A\Rightarrow B
\]
be the coherence on the path context \(C_w\), followed by its substitution into the ambient context.

Choose
\[
m^w_{ABC}:
\kappa_w(A,B)\cdot\kappa_w(B,C)
\longrightarrow
\kappa_w(A,C)
\tag{1}
\]
and
\[
\eta^w_A:1_A\longrightarrow\kappa_w(A,A)
\tag{2}
\]
as 3-coherences on \(C_w\).

These choices have all the required path-only 4-comparisons directly on \(C_w\). For example, the two routes
\[
\begin{aligned}
&(\kappa(A,B)\cdot\kappa(B,C))\cdot\kappa(C,D)
   \longrightarrow \kappa(A,D)
\end{aligned}
\]
obtained using \(m^w\) and the vertical associator are parallel full 3-terms on \(C_w\). Their comparison is the coherence on \(C_w\) between those exact terms.

No identification of \(\kappa_w(A,A)\) with \(1_A\) is made.

### Vertical pasting contexts

Let
\[
C_n=
\bigl(
x,y,h_0:x\to y,\;
h_i:x\to y,\ A_i:h_{i-1}\Rightarrow h_i
\ (1\leq i\leq n)
\bigr)
\]
be the vertical 2-chain.

More generally, write
\[
V(k_1,\ldots,k_n)
\]
for the pasting context with
\[
z_{i,j}:h_{i-1}\Rightarrow h_i
\quad(0\leq j\leq k_i),
\qquad
M_{i,j}:z_{i,j-1}\longrightarrow z_{i,j}
\quad(1\leq j\leq k_i).
\]
Its declaration order is
\[
x,y,h_0,\quad
h_i,z_{i,0},z_{i,1},M_{i,1},\ldots,z_{i,k_i},M_{i,k_i}
\quad(i=1,\ldots,n).
\]
After each block, descend to \(h_i\) before introducing the next block. This is a derivation by the pasting-context rules.

For a fixed vertical 2-expression \(w(A_1,\ldots,A_n)\), let
\[
\operatorname{Map}_w(r_1,\ldots,r_n)
\]
be its 3-cell action: change the arguments in increasing index order, whiskering each \(r_i\) through the binary expression \(w\), and compose the resulting 3-cells.

The following 4-cells are obtained directly by the coherence rule:

\[
\operatorname{Map}_w(r_i;s_i)
\simeq_4
\operatorname{Map}_w(r_i);
\operatorname{Map}_w(s_i),
\tag{3}
\]
on \(V(2,\ldots,2)\), and, for a fixed full 3-term \(b:u\to v\) on \(C_n\),
\[
b[A_i^-];\operatorname{Map}_v(r_i)
\simeq_4
\operatorname{Map}_u(r_i);b[A_i^+],
\tag{4}
\]
on \(V(1,\ldots,1)\).

In every application below, \(u,v,w\) are vertical expressions using each displayed 2-position. Consequently, both 3-boundaries in (3) or (4) use every displayed 3-generator and have full support.

These constructions supply the required functoriality of vertical words and the naturality of their associators, unitors, and padding maps.

## 2. Coherent folding of vertical words

Define the canonical 2-terms
\[
N_{\mathrm{id}_w}(A,B)=\kappa_w(A,B)
\tag{5}
\]
and
\[
N_F(A,B)=
\bigl(\kappa_p(A,p)\cdot F\bigr)\cdot\kappa_q(q,B).
\tag{6}
\]

A composable vertical list in \(S\) whose strict composite is \(F\) has exactly one \(F\)-valued entry. All earlier entries have strict image \(1_p\), and all later entries have strict image \(1_q\).

There are therefore only three binary multiplication cases for the normal forms:
\[
\mathrm{id}/\mathrm{id},\qquad
\mathrm{id}/F,\qquad
F/\mathrm{id}.
\]

The first uses (1). Here are explicit choices for the other two.

Put
\[
P_{AB}=\kappa_p(A,B),\qquad Q_{AB}=\kappa_q(A,B).
\]
For a fixed \(q\)-word \(C\), set
\[
W_C(U)=(U\cdot F)\cdot Q_{qC}.
\]
Let
\[
a(U,V,T):(U\cdot V)\cdot T\longrightarrow U\cdot(V\cdot T)
\]
be the vertical associator, and let \(a^{-}\) be the reverse coherence on the same arity. Define
\[
\lambda_C(U,V)
=
a^{-}(U,V\cdot F,Q_{qC});
\bigl(a^{-}(U,V,F)\cdot Q_{qC}\bigr).
\tag{7}
\]
Its exact type is
\[
U\cdot W_C(V)\longrightarrow W_C(U\cdot V).
\]

Choose
\[
\mu_L(A,B;C)
=
\lambda_C(P_{AB},P_{Bp});
W_C(m^p_{ABp}),
\tag{8}
\]
and
\[
\mu_R(A;B,C)
=
a(P_{Ap}\cdot F,Q_{qB},Q_{BC});
\bigl((P_{Ap}\cdot F)\cdot m^q_{qBC}\bigr).
\tag{9}
\]

These have the respective types
\[
P_{AB}\cdot N_F(B,C)\longrightarrow N_F(A,C)
\]
and
\[
N_F(A,B)\cdot Q_{BC}\longrightarrow N_F(A,C).
\]

### The 4-dimensional folding laws

The multiplication maps just defined have associativity and unit 4-cells. The following describes their construction, including the comparisons that involve \(F\).

**Three path-valued factors.** Both multiplication routes are terms on one path context. Use its direct 4-coherence.

**Two path factors before \(F\).** After applying (4) to the associators in (7), the two routes reduce to
\[
\lambda_C(a\cdot b,c);W_C(\ell)
\quad\text{and}\quad
\lambda_C(a\cdot b,c);W_C(r),
\]
where, on the \(p\)-path,
\[
\ell=(m^p_{ABC}\cdot P_{Cp});m^p_{ACp},
\]
and
\[
r=
a(P_{AB},P_{BC},P_{Cp});
(P_{AB}\cdot m^p_{BCp});
m^p_{ABp}.
\]
The comparison \(\ell\simeq_4 r\) is a direct coherence on \(C_p\).

The reassociation needed for this reduction is itself the direct 4-coherence on the vertical 2-chain \((a,b,c,F,Q_{qC})\) between
\[
\begin{aligned}
&a(a,b,W_C(c));
(a\cdot\lambda_C(b,c));
\lambda_C(a,b\cdot c),\\
&\lambda_C(a\cdot b,c);
W_C(a(a,b,c)).
\end{aligned}
\tag{10}
\]
Both routes have the same exact boundaries and use all five 2-positions.

**Two path factors after \(F\).** Use the corresponding construction on \(C_q\), with the factors in the reverse order.

**One path contraction on each side of \(F\).** Use the following explicit pasting:
\[
\begin{aligned}
R=\bigl(
&x,y,a:x\to y,\ b:x\to y,\\
&L_0,L_1:a\Rightarrow b,\ M:L_0\to L_1,\\
&c:x\to y,\ Z:b\Rightarrow c,\\
&d:x\to y,\ R_0,R_1:c\Rightarrow d,\ N:R_0\to R_1
\bigr).
\end{aligned}
\]
The two 3-terms
\[
\begin{aligned}
r_{LR}
&=((M\cdot Z)\cdot R_0);
  ((L_1\cdot Z)\cdot N),\\
r_{RL}
&=((L_0\cdot Z)\cdot N);
  ((M\cdot Z)\cdot R_1)
\end{aligned}
\]
both run
\[
(L_0\cdot Z)\cdot R_0
\longrightarrow
(L_1\cdot Z)\cdot R_1.
\]
They are full in \(R\), so take
\[
\Omega_R=
\operatorname{coh}_{R,r_{LR}\to r_{RL}}[\mathrm{id}].
\tag{11}
\]
Substitute \(Z\mapsto F\), and substitute the two path multiplication 3-cells for \(M,N\). This gives the mixed multiplication law, after the reassociations supplied by (4) and (10).

**Units.** For the left unit, write \(P=P_{Ap}\), \(J=P_{AA}\), and use \(\eta_A:1_A\to J\). Naturality (4) changes the unit route into
\[
\lambda_C(1_A,P);
W_C\bigl((\eta_A\cdot P);m^p_{AAp}\bigr).
\]
On \(C_p\), compare
\[
(\eta_A\cdot P);m^p_{AAp}
\quad\text{with}\quad
\ell_P.
\]
Then use the direct 4-coherence on \((P,F,Q_{qC})\) between
\[
\lambda_C(1_A,P);W_C(\ell_P)
\quad\text{and}\quad
\ell_{W_C(P)}.
\tag{12}
\]
The right unit uses the analogous \(q\)-path comparison and the direct coherence between
\[
a(L,Q,1_B);(L\cdot\rho_Q)
\quad\text{and}\quad
\rho_{L\cdot Q}.
\]

Thus all the folding laws use path contexts or the displayed vertical pasting contexts.

### Restricted folding lemma

Fix a folding procedure as follows:

1. reassociate a vertical expression into a left-associated word;
2. replace path-only factors by the chosen \(\kappa\)-terms;
3. combine adjacent path factors using (1), (8), and (9);
4. use (2) and unitors for identity factors;
5. retain the two outer pads in (6).

Then:

> **Folding lemma.** For a vertical expression with at most one \(F\)-valued entry, normalizing its entries and folding is compatible, through constructed 4-cells, with reassociation, unit insertion or removal, and replacement of a path-only factor by a parallel path-only 2-term along a 3-cell.

For reassociation and units, first use (4) to move the argument normalizers through the structural 3-cell, then use the multiplication laws above.

For a path-only replacement \(b:T\to T'\), the comparison
\[
b;\nu_{T'}\simeq_4\nu_T
\]
is a direct path coherence. Whisker it into the vertical word.

Compatibility with successive normalization of the entries uses (3). Compatibility with different folding orders follows by binary-tree rotations, the associativity laws above, and the mixed comparison (11). This supplies a finite construction for every comparison in the lemma; it makes no assertion about arbitrary 3-coherences on \(S\).

## 3. Exact active-column factorization

This is the additional fact that makes the normalization compatible with substitution.

Let
\[
T=\operatorname{coh}_{P,A}[\gamma]
\]
be a 2-term of \(S\) with \(\pi(T)=F\). Its arity \(P\) is 2-dimensional.

A 2-dimensional pasting context is a horizontal sequence of vertical 2-chains. Exactly one of those columns contributes \(F\) under \(\gamma\). That column has substituted 0-source \(x^-\) and 0-target \(y^+\).

Every earlier column has both substituted 0-endpoints \(x^-\); every later column has both endpoints \(y^+\). Otherwise the strict result would have a nonempty horizontal factor before or after \(F\).

The substituted terms in these other columns factor **literally** through the corresponding point context. There is no nonempty directed path from \(x^-\) to itself or from \(y^+\) to itself, and the support result excludes hidden uses of \(F\).

Retain the contributing column as a fresh \(C_k\). Define
\[
C_k\vdash\delta:P,\qquad S\vdash\eta:C_k
\]
by:

- sending the retained 1- and 2-variables to the corresponding variables of \(C_k\);
- sending preceding and following 0-variables to \(x\) and \(y\);
- lifting every other substituted term literally from \(D^0(x^-)\) or \(D^0(y^+)\) to \(D^0(x)\) or \(D^0(y)\);
- letting \(\eta\) assign the actual retained arguments.

Then
\[
\boxed{\gamma=\delta[\eta]}
\tag{13}
\]
is a syntactic equality.

Put
\[
H=\operatorname{coh}_{P,A}[\delta].
\]
This is a full 2-term on \(C_k\). Its source \(S_H\) is a term on the 1-disc \(h_0\); its target \(T_H\) is a term on the 1-disc \(h_k\). With a fixed bracketing, set
\[
E_H=
\bigl(
\kappa_{h_0}(S_H,h_0)\cdot
\operatorname{word}(A_1,\ldots,A_k)
\bigr)\cdot
\kappa_{h_k}(h_k,T_H).
\]
Both \(H\) and \(E_H\) are full on \(C_k\), with exactly the same 1-boundaries. Hence
\[
\boxed{
v_H=
\operatorname{coh}_{C_k,H\to E_H}[\mathrm{id}]
}
\tag{14}
\]
is a 3-cell.

### Stability

Suppose the constructor is first considered over a vertical chain \(C_n\), and then substituted into \(S\), with
\[
x\mapsto x^- ,\qquad y\mapsto y^+.
\]

Along a subterm whose substituted strict image is \(F\):

- the retained column is unchanged;
- every discarded argument is still the same point-supported term;
- only the retained arguments change.

Using fixed indexed names for the fresh variables, the term \(H\) in (14) is therefore **literally the same before and after substitution**.

This is stronger than pointwise verticalization. It is also where the square hypothesis is used.

## 4. Define new normalizers

The proof must define its normalizers by the stable construction above. An arbitrary earlier choice of \(\nu_T\) cannot be substituted here without another comparison proof.

### Normalizers in \(S\)

For a path-only 2-term \(T:A\Rightarrow B\), define
\[
\nu_T:T\longrightarrow\kappa_w(A,B)
\tag{15}
\]
by the direct 3-coherence on \(C_w\).

For \(F\), use inverse unitors to obtain
\[
F\longrightarrow (1_p\cdot F)\cdot1_q,
\]
then whisker \(\eta^p_p\) and \(\eta^q_q\). This gives
\[
\nu_F:F\longrightarrow N_F(p,q).
\tag{16}
\]

For a constructor \(T\) with strict image \(F\):

1. use (13) and apply \(v_H[\eta]\);
2. normalize the retained 2-arguments;
3. normalize the two unary path pads;
4. apply the fixed fold of §2.

Exactly one retained argument has strict image \(F\), and it is a proper subterm of \(T\). All other retained arguments are path-only. This recursion terminates and defines
\[
\boxed{\nu_T:T\longrightarrow N_F(\sigma T,\tau T).}
\tag{17}
\]

### Relative normalizers on \(C_n\)

A nonidentity strict 2-cell on \(C_n\) is a consecutive block
\[
A_{i+1}\cdots A_j.
\]
For a 2-term \(u\) with that strict image, define
\[
B(u)=
\bigl(
\kappa_{h_i}(\sigma u,h_i)\cdot
\operatorname{word}(A_{i+1},\ldots,A_j)
\bigr)\cdot
\kappa_{h_j}(h_j,\tau u).
\tag{18}
\]
For an identity block, use
\[
B(u)=\kappa_{h_i}(\sigma u,\tau u).
\]

Define
\[
\lambda_u:u\longrightarrow B(u)
\tag{19}
\]
by the same constructor recursion:

1. the comparison \(v_H\);
2. the relative normalizers of its retained arguments;
3. an **explicit vertical fold**.

The last fold uses only reassociation, path comparisons on the relevant \(h_i\), and unitors. It concatenates the consecutive blocks, combines adjacent unary pads, removes internal identity pads, and retains the two outer pads.

In particular, this fold is not chosen as an arbitrary coherence on \(C_n\).

For a variable \(A_i\), \(\lambda_{A_i}\) is the padding 3-cell obtained from inverse unitors. It is not an identity.

## 5. Evaluation fusion

Let
\[
S\vdash\sigma:C_n
\]
send the full strict word \(A_1\cdots A_n\) to \(F\).

For the explicit vertical expression \(B(u)[\sigma]\), define
\[
D_{B(u),\sigma}:
B(u)[\sigma]\longrightarrow N_{\pi(u[\sigma])}
      (\sigma(u[\sigma]),\tau(u[\sigma]))
\tag{20}
\]
by normalizing its substituted letters and unary pads, then applying the fixed fold.

The notation on the right means (5) or (6), as appropriate.

> **Evaluation lemma.** There is a constructed 4-cell
> \[
> \boxed{
> E_{u,\sigma}:
> \nu_{u[\sigma]}
> \longrightarrow
> \lambda_u[\sigma];D_{B(u),\sigma}.
> }
> \tag{21}
> \]

The proof is by induction on the **generic 2-term \(u\)**.

### Case 1: \(u[\sigma]\) is path-only

Both sides of (21) are parallel 3-terms over the same actual path context. Use its direct 4-coherence.

This also handles a generic nonempty block all of whose letters become identity-valued after substitution.

### Case 2: \(u=A_i\)

The right side first pads \(\sigma A_i\), then normalizes and folds it. Apply (4) to the padding 3-cell and the given
\[
\nu_{\sigma A_i}:\sigma A_i\to N(\sigma A_i).
\]
Follow it by the left and right unit laws of §2.

This gives (21). The argument treats \(\nu_{\sigma A_i}\) as a given 3-cell, so no induction on the size of \(\sigma A_i\) is involved.

### Case 3: \(u\) is a constructor and \(u[\sigma]\) has strict image \(F\)

By stability of (13), both recursive constructions start with exactly
\[
v_H[\eta[\sigma]].
\]

Apply the induction hypotheses to the retained arguments. Use (3) to separate their relative normalizers from their evaluation normalizers.

After the common prefix \(v_H[\eta[\sigma]]\) and the relative argument normalizers, the two remaining routes differ only in the order of vertical folding and evaluation. The folding lemma supplies their 4-comparison:

- associators use (4) and the multiplication associativity laws;
- unary path comparisons use a 4-coherence on the actual \(p\)- or \(q\)-path;
- unitors use (4) and the multiplication unit laws.

Compose these 4-cells.

This proves (21) without assuming compatibility for an arbitrary 3-coherence.

## 6. The smaller first step: coherences over 2-dimensional arities

First consider **any** 3-term
\[
C_n\vdash H:u\longrightarrow v
\]
whose 2-boundaries are full on \(C_n\).

Because \(u,v\) are parallel and full, their strict blocks are both \(A_1\cdots A_n\), and their exact 1-source and 1-target terms agree. Consequently,
\[
\boxed{B(u)=B(v)}
\tag{22}
\]
as terms.

Write this common term as \(B\). The two 3-terms
\[
H;\lambda_v
\quad\text{and}\quad
\lambda_u
\]
are parallel and full on \(C_n\). Therefore form
\[
\boxed{
\Xi_H=
\operatorname{coh}_{C_n,\,
 (H;\lambda_v)\to\lambda_u}
[\mathrm{id}].
}
\tag{23}
\]

After substitution and postcomposition with \(D_{B,\sigma}\), use (21):
\[
\begin{aligned}
H[\sigma];\nu_{v[\sigma]}
&\simeq_4
H[\sigma];\lambda_v[\sigma];D_{B,\sigma}\\
&\simeq_4
\lambda_u[\sigma];D_{B,\sigma}\\
&\simeq_4
\nu_{u[\sigma]}.
\end{aligned}
\tag{24}
\]

The middle comparison is \(\Xi_H[\sigma]\), whiskered with \(D_{B,\sigma}\).

Now let the original 3-coherence have a 2-dimensional arity \(P\) and \(F\)-valued 2-boundaries. Factor its substitution by (13). It becomes a 3-term \(H\) on a vertical \(C_n\), with full boundaries. Thus (24) applies.

This settles the smaller first step, including arbitrary substituted middle 2-terms.

## 7. Extension to every 3-term of \(S\)

We construct, for every 3-term \(G:T\to T'\) with \(F\)-valued 2-boundary, a 4-cell
\[
\boxed{
\Lambda_G:
G;\nu_{T'}\longrightarrow\nu_T.
}
\tag{25}
\]

Induct on the actual syntax of \(G\).

There are no 3-variables in \(S\). A coherence constructor producing a 3-term has arity of dimension at most 3.

Arity of dimension at most 1 cannot produce an \(F\)-boundary. Arity of dimension 2 is handled by §6. It remains to handle an arity of dimension 3.

### Retaining the contributing 0-column

The same exact factorization applies, now retaining the entire contributing column, including its 3-variables. Every other substituted term is point-supported, including the substituted 3-terms.

The retained context has the form
\[
R=V(k_1,\ldots,k_m).
\]
Let the factorized constructor be
\[
R\vdash H:U\longrightarrow V.
\]

Its source 2-boundary is the vertical chain in \(z_{i,0}\); its target boundary is the vertical chain in \(z_{i,k_i}\).

The relative normalizers give
\[
\lambda_U:U\to B_U,\qquad
\lambda_V:V\to B_V.
\]
Since \(U,V\) are parallel, the two outer unary pads in \(B_U,B_V\) are literally identical.

Let
\[
W:B_U\longrightarrow B_V
\tag{26}
\]
be the vertical-word action of the 3-chains
\[
M_{i,1};\cdots;M_{i,k_i}.
\]
Use increasing \(i\), and increasing \(j\) within each position. Positions with \(k_i=0\) remain fixed.

Both
\[
H;\lambda_V
\quad\text{and}\quad
\lambda_U;W
\]
are parallel full 3-terms on \(R\): the first uses every \(M_{i,j}\) through \(H\), and the second uses them through \(W\). Thus form
\[
\boxed{
\Xi_H=
\operatorname{coh}_{R,\,
 (H;\lambda_V)\to(\lambda_U;W)}
[\mathrm{id}].
}
\tag{27}
\]

### Applying the induction hypotheses

Write \(S\vdash\sigma:R\) for the retained argument substitution.

At each fixed position \(i\), the terms
\[
z_{i,0}[\sigma],\ldots,z_{i,k_i}[\sigma]
\]
have the same exact 1-boundaries and the same strict 2-value. Their normal forms are therefore literally equal.

Each \(M_{i,j}[\sigma]\) is a proper 3-subterm of the original constructor. Its induction hypothesis gives
\[
M_{i,j}[\sigma];\nu_{z_{i,j}[\sigma]}
\simeq_4
\nu_{z_{i,j-1}[\sigma]}.
\]
For an identity-valued position, this comparison is also available directly on its path context.

Compose these comparisons along each 3-chain. Word functoriality (3), followed by whiskering the resulting 4-cells, gives
\[
\boxed{
W[\sigma];D_{B_V,\sigma}
\simeq_4
D_{B_U,\sigma}.
}
\tag{28}
\]
The final fold on both sides is the same fold: after argument normalization, the 2-term at each position is literally the same.

Combining (21), (27), and (28),
\[
\begin{aligned}
H[\sigma];\nu_{V[\sigma]}
&\simeq_4
H[\sigma];\lambda_V[\sigma];D_{B_V,\sigma}\\
&\simeq_4
\lambda_U[\sigma];W[\sigma];D_{B_V,\sigma}\\
&\simeq_4
\lambda_U[\sigma];D_{B_U,\sigma}\\
&\simeq_4
\nu_{U[\sigma]}.
\end{aligned}
\tag{29}
\]
This is (25).

There is one harmless dimension drop: all \(k_i\) may be zero because the original arity’s 3-variables were in discarded point-supported columns. Then \(R=C_m\), and §6 applies directly. Equivalently, take \(W=1_B\) and use the 4-unitor.

The induction is well founded: only the proper 3-subterms \(M_{i,j}[\sigma]\) use (25). Evaluation fusion was established separately by induction on generic 2-terms.

## 8. The requested 4-term

Let
\[
\alpha,\beta:T\longrightarrow T'
\]
have \(F\)-valued 2-boundary. Set
\[
r=\nu_{T'},\qquad s=\nu_T.
\]
The construction above gives
\[
\Lambda_\alpha:\alpha;r\to s,
\qquad
\Lambda_\beta:\beta;r\to s.
\]
Hence
\[
\Theta=
\Lambda_\alpha *_3\overline{\Lambda_\beta}
:
\alpha;r\longrightarrow\beta;r.
\tag{30}
\]

The normalizer \(r\) is a composite of coherence 3-cells and their whiskerings. Its reverse \(\bar r\) and a cancellation 4-cell
\[
\epsilon_r:r;\bar r\longrightarrow1_{T'}
\]
are constructed by reversing those coherences and using their cancellation coherences on the same pasting arities.

Right-cancel \(r\) in (30). Explicitly, compose the following 4-cells:
\[
\begin{aligned}
\alpha
&\longrightarrow \alpha;1_{T'}\\
&\longrightarrow \alpha;(r;\bar r)\\
&\longrightarrow (\alpha;r);\bar r\\
&\xrightarrow{\ \Theta*_2\bar r\ }(\beta;r);\bar r\\
&\longrightarrow \beta;(r;\bar r)\\
&\longrightarrow \beta;1_{T'}\\
&\longrightarrow \beta.
\end{aligned}
\tag{31}
\]
The first and last arrows are 4-unitors; the second uses \(\overline{\epsilon_r}\); the third and fifth are 4-associators; the sixth uses \(\epsilon_r\).

Their \(*_3\)-composite is the required term
\[
\boxed{\operatorname{Fill}_S(\alpha,\beta):\alpha\longrightarrow\beta.}
\]

For identity-valued 2-boundaries, use the path-context filler already established in your §2.7. These two cases exhaust the strict 2-cells of \(S\), proving the theorem.

For a 3-dimensional coherence \(c\) over the fully selected single arrow, the promised rule is therefore
\[
\boxed{
K(Q,B,\operatorname{Var}(Q))
=
\operatorname{Fill}_S(a_c,b_c).
}
\tag{32}
\]

The lower lifts may remain fixed as in the problem: the auxiliary normalizers constructed here are used to compare the resulting 3-terms and do not replace those lower lifts.

## Scope

This resolves Question 1, including the comparison of arbitrary 3-terms with \(F\)-boundary. The crucial additional lemma is the **exact, substitution-stable active-column factorization**, followed by evaluation fusion for a normalizer defined using that factorization.

The argument does not establish RC(3) for general cylinders or loop-free contexts. In those contexts, the discarded horizontal columns need not be supported at points, so the literal stability used in (21) is unavailable.

For Question 2, there is also a dimension correction: a \(K\) for a 3-dimensional coherence is a **4-cell**, so a comparison between two choices of \(K\) is a **5-cell**. The RC(3) construction above does not supply that uniqueness statement.

This is a metatheoretic construction with specified pasting arities and substitutions; it has not been run through a CaTT implementation.
