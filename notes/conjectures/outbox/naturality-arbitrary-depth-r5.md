# Problem: naturality of CaTT coherences at depth ≥ 2, round 5

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first. Rounds 1–4 and their verified answers are archived in `answered/naturality-arbitrary-depth-2026-11-18.md` and `answered/naturality-arbitrary-depth-r2-2026-11-18.md` through `-r4-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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
10. **RC(3) on the cylinder of a composable pair (round 3, proved on paper).** Q = (x, y, z, f : x → y, g : y → z), Y = Var(Q). The strict 2-cells are the identities on paths, F = F_f, G = F_g, L = f⁻ ∗₀ G, R = F ∗₀ g⁺ and H = L ∗₁ R. The method:
    - *Fixed-edge extension.* A column carrying F (or G) that does not span the unique source and sink factors literally through a retained pasting context `C_n ∗₀ D¹(h)` or `D¹(h) ∗₀ C_n` (and their 3-dimensional versions), where every substitution sending the full word to the 2-cell sends h to the **same edge variable**. This replaces point support.
    - *New constructors.* Fixed whiskering d_h, its associativity, path comparisons after whiskering, whiskering of normal forms, and a compatibility cell φ^h with the vertical fold, all coherences over pasting contexts.
    - *Normalisers and fusion* as in item 8, with the evaluation fold kept separate from the vertical fold.
    - *The two-generator case H.* Discarded columns are point-supported again (H spans x⁻ → z⁺), and L and R occur in a forced order, so the vertical fold needs one additional multiplication case.
    - So K(Q, B, Var Q) exists for every 3-dimensional coherence over the pair, for any fixed lower lifts.
    - It uses three facts that are not known for general cylinders: the fixed-edge factorisations are literal, the H case is point-supported, and the 2-generators of H have a forced order.
11. **A dimension-lowering translation (from the cone problem).** For join contexts `Cone(Q; c)` (Q a pasting context, with an apex c and cone cells p_q), there is a syntactic *cut translation* D: colour the 0-variables 0/1, nondecreasing along generating 1-cells; D deletes same-side variables and lowers each crossing term by one dimension, decoding a coherence over its unique crossing root branch. It satisfies D(Σt) ≡ t, D(u ∗_k v) ≡ D(u) ∗_{k−1} D(v), D(e ∗₀ u) ≡ D(u) and D(t[θ]) ≡ D(t)[D(θ)], and with a raising substitution it gives `RC(r+1, Cone(ΣQ; d)) ⇒ RC(r, Cone(Q; c))`. Details: `answered/cone-over-coherences-r2-2026-11-18.md`, §2.
12. **Literal inactive-column factorisation (from the Gray-contexts problem).** In every context Γ of dimension ≤ 2 with an acyclic graph of generating 1-cells (for example Q↑Y for 1-dimensional Q), an arity column none of whose 2-variables receives a term containing a 2-variable lifts literally to the path context of its common strict path (the path labelling is injective by acyclicity). Replacing such columns gives a reduced pasting context R_σ with σ = κ_σ[δ_σ], comparison terms coh_{P,A}[σ] → coh_{R_σ,A[κ_σ]}[δ_σ], and refinement substitutions λ_{σ,ρ} that are functorial under further substitution, with coherence cells between iterated reductions. A coherence 4-term also distributes a fixed whisker across a vertical composite of 3-cells. Details: `answered/gray-contexts-r4-2026-11-18.md`. The open part is the treatment of active columns, whose 2-variables carry arbitrary composites.

13. **RC(3) on the cylinder of the 2-disc (round 4, proved on paper).** Q = (x, y, f, g : x → y, A : f ⇒ g), Y = Var(Q).
    - Write X = x↑, Y = y↑, F = f↑, G = g↑, c = A⁻ ∗₀ Y, d = X ∗₀ A⁺, L = c ∗₁ G and R = F ∗₁ d, so that U = A↑ : L → R.
    - *Strict cells.* The strict 2-cells are a, b, c, d, F, G, L, R and identities. The only nonidentity strict 3-cell is πU, and every term with that image uses U exactly once.
    - *RC(3) on the 2-skeleton Γ₀.* Restrict by value. The values a, b, c, d are direct coherences, F and G are squares, and L and R use the round-3 two-letter construction (point-supported, forced order).
    - *Sequentialization.* Any 3-head over a 3-dimensional arity is 4-connected to a binary composite B_H with RC(2)-bridges in P_{≤2}. Interchange with identities then extracts every term of image πU to I₀ ; ω(U) ; I₁, where I₀ and I₁ are structural and ω is a whiskering by terms of dimension ≤ 2.
    - *Whiskering normalization.* ω is normalized by three local constructions: path coefficients (the interchanger on D³ ∗₁ D³), point-supported 2-coefficients (D²(a) ∗₀ D³(U)), and point-supported 1-loops l : x⁻ → x⁻ (D²(κ) ∗₀ D³(U) with unitors).
    - So K exists for every 3-dimensional coherence over the 2-disc, for any lower lifts.
14. **Suspension descent (round 4, proved on paper).** With ΣY selected and the poles N, S unselected, (ΣQ)↑ΣY = Σ(Q↑Y). The cut decoder of item 11 handles arbitrary coloured contexts, with a dimension-1 clause D coh[γ] = D(γ(e)) and with full-endpoint decoding when the cut column has dimension ≤ d − 2. It satisfies D(Σt) = t. Hence
    ```
    RC(r+1, (ΣQ)↑ΣY)  ⇒  RC(r, Q↑Y).
    ```
    So RC(n) on all cylinders, **including partial selections**, gives Conjecture N through dimension n.
15. **Chains (round 4).**
    - *Full chain cylinders.* With vᵢ = xᵢ↑ and Fᵢ : aᵢ⁻vᵢ → vᵢ₋₁aᵢ⁺, the strict 1-paths x_a⁻ → x_b⁺ are P_j = a⁻ … a_j⁻ v_j a⁺_{j+1} …, and Fᵢ sends P_i to P_{i−1}. So every nonidentity strict 2-cell has the forced word F_r … F_{s+1}, and arities factor literally through frames P_left ∗₀ C_n ∗₀ P_right or P_left ∗₀ V(k) ∗₀ P_right.
    - *Proper selections.* A one-chain frame is not enough. For Y = {a₁, a₂} on x₀ → x₁ → x₂, the cylinder is D² ∗₀ D² with two independent 2-generators.

## 3. What remains, and why

RC(3) fails for loopy contexts such as (x : ⋆, a : id_x → id_x), so any proof must use acyclicity. The cylinders done so far are the square, the composable pair, and the 2-disc. In each of them every column carrying a nonidentity cell either spans the unique source and sink, or has one fixed edge on one side.

Three things change in larger cases:
- Longer full chains produce forced words of length ≥ 3, whose letters sit in different vertical chains.
- Proper selections produce several independent chains, as in item 15.
- 2-dimensional Q with more than one 2-cell produce several 3-variables. Their strict 3-cells can then compose and interchange, so the "exactly one U" count of item 13 fails.

Item 14 reduces the whole conjecture to RC(n) on all cylinders.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Forced words of length 3.** Q = (x₀ → x₁ → x₂ → x₃), Y = Var(Q). Using the frames of item 15, give normalisers and evaluation fusion for 2-terms whose strict image is F₃F₂F₁, or any forced word of length ≥ 3. Item 10's H case is the length-2 instance. Conclude RC(3) for this cylinder.
2. **Proper selections.** Give RC(3) for the cylinder of a 1-dimensional pasting context with Y proper, where several vertical chains must be retained. Start with the smallest case that is not a pasting context: x → y → z with Y = {z, g}, or Y = {y, z, f, g}. The frames retain several chains, and the fusion must handle the exchange between them.
3. **Two 3-variables.** RC(3) on the full cylinder of
   - Q = D² ∗₀ D² (two 2-cells side by side), and
   - Q = D² ∗₁ D² (two 2-cells composed vertically).

   Here the cylinder has two 3-variables, and their strict images can be composed (∗₂ for the vertical case) or interchanged (∗₀ for the horizontal case). The 2-disc proof of item 13 then needs a normal form for several uses of 3-variables.
4. **RC(3) on all cylinders.** Prove RC(3) for every Q↑Y, or for every finite Steiner loop-free context. Or give a loop-free counterexample.
5. **All dimensions.** Prove RC(n) on all cylinders Q↑Y, including partial selections. By item 14, this proves Conjecture N at every depth. A first target is RC(4) on the cylinder of the 3-disc, or on (ΣD²)↑ΣY.
6. **Global choice of K in dimension 3.** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with Y = Var(Q), compatible with substitution. Two choices of K for the same (Q, B, Y) are 4-cells; the minimal requirement is a **5-cell** between them (item 9).

## 5. What counts as a solution

Any of the following:
- explicit terms for question 1, 2, 3 or 6;
- a proof of RC(3) or RC(n) for the cylinders or for loop-free contexts;
- a counterexample: a cylinder Q↑Y, or a loop-free context, with two parallel n-terms of equal strict image and no term between them;
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

**The finite-word construction extends to arbitrary finite length.** Using the factorization and refinement results accepted in §2.12 and §2.15, it gives:

1. **RC(3) for the full cylinder of every finite chain**, including the three-arrow chain in question 1.
2. **RC(3) for both proposed proper selections**, \(Y=\{z,g\}\) and \(Y=\{y,z,f,g\}\).
3. **RC(3) for the full cylinder of \(D^2*_1D^2\)**, the vertical case of question 3.

The construction remains restricted to one active \(0\)-column. It does not establish the independent-column exchange cases, including the horizontal case of question 3.

The essential extension is a finite-word fold with explicit path comparisons, together with its \(4\)-dimensional compatibility with evaluation. I give that construction first.

## 1. Conventions and the pasting arities

Write
\[
\cdot=*_{1},\qquad ;=*_{2}.
\]
Thus \(\cdot\) composes \(2\)-cells vertically, and \(;\) composes \(3\)-cells vertically. Parentheses below denote actual syntax.

For a pasting context \(P\) and parallel full terms \(s,t\), write
\[
\mathsf C_P(s,t):=\operatorname{coh}_{P,s\to t}[\mathrm{id}].
\]
Every use of \(\mathsf C\) below specifies a genuine pasting context and checks fullness there, before substitution. This is the full-support alternative of the CaTT coherence rule. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

Let
\[
C_n=
\bigl(
a,b;\;
u_0,\ldots,u_n:a\to b;\;
z_i:u_{i-1}\Rightarrow u_i
\bigr)
\]
be the vertical chain of \(n\) \(2\)-discs.

Let \(V_n(k_1,\ldots,k_n)\) replace its \(i\)-th \(2\)-disc by
\[
z_i^0,\ldots,z_i^{k_i}:u_{i-1}\Rightarrow u_i,
\qquad
h_i^j:z_i^{j-1}\Rightarrow z_i^j.
\]
When \(k_i=0\), that position is just a \(2\)-disc.

The universal arities needed are
\[
P_\ell*_0C_n*_0P_r,
\qquad
P_\ell*_0V_n(\mathbf k)*_0P_r,
\tag{1}
\]
their boundary pastings, and literal \(1\)-path contexts. Empty exterior paths are omitted.

For a literal path \(w\), use the fixed path comparison
\[
\kappa_w(A,B):A\Rightarrow B
\]
from the accepted path construction. In particular,
\[
\kappa_w(A,A)
\]
is retained as a term; it is not identified with \(1_A\).

All the constructions below are finite recipes for terms. A direct comparison is \(\mathsf C_P\); insertion into a larger expression uses mixed composition and substitution.

## 2. Normal forms for finite forced words

Fix the full cylinder of
\[
x_0\xrightarrow{a_1}x_1\longrightarrow\cdots
\xrightarrow{a_k}x_k.
\]

For fixed outer endpoints \(x_a^-,x_b^+\), choose the following raw \(2\)-terms:
\[
E_i^{a,b}
=
L_i^-*_0(F_i*_0R_i^+),
\tag{2}
\]
where \(L_i^-\) is the chosen bracketed minus-prefix from \(x_a^-\) to \(x_{i-1}^-\), and \(R_i^+\) is the chosen bracketed plus-suffix from \(x_i^+\) to \(x_b^+\). Omit an empty whisker.

Put
\[
S_i=\sigma E_i^{a,b},\qquad T_i=\tau E_i^{a,b}.
\]

The strict paths are
\[
P_j^{a,b}
=
a_{a+1}^-\cdots a_j^-\,v_j\,
a_{j+1}^+\cdots a_b^+.
\]
The strict image of \(E_i^{a,b}\) goes from \(P_i^{a,b}\) to \(P_{i-1}^{a,b}\).

For a nonempty forced word
\[
w=(r,r-1,\ldots,s+1),
\]
define
\[
\begin{aligned}
N_w(A,B)=\operatorname{LF}\bigl[
&\kappa_{P_r}(A,S_r),\,E_r,\,
\kappa_{P_{r-1}}(T_r,S_{r-1}),\,E_{r-1},\,\ldots,\\
&E_{s+1},\,\kappa_{P_s}(T_{s+1},B)
\bigr],
\end{aligned}
\tag{3}
\]
where \(\operatorname{LF}\) is the literal left-associated product.

For an empty word on \(P_j\), put
\[
N_\varnothing(A,B)=\kappa_{P_j}(A,B).
\tag{4}
\]

These definitions retain a path comparison between every two raw letters, even when their endpoints happen to be syntactically equal.

For the requested three-letter word, the normal form is therefore exactly
\[
\boxed{
\operatorname{LF}\bigl[
\kappa_{P_3}(A,S_3),E_3,
\kappa_{P_2}(T_3,S_2),E_2,
\kappa_{P_1}(T_2,S_1),E_1,
\kappa_{P_0}(T_1,B)
\bigr].
}
\tag{5}
\]

In particular, none of the differently bracketed \(1\)-boundaries of \(E_3,E_2,E_1\) has been identified.

### 2.1 The multiplication term

On an actual path \(p\), define
\[
m_p(A,B,C):
\kappa_p(A,B)\cdot\kappa_p(B,C)
\Longrightarrow
\kappa_p(A,C)
\tag{6}
\]
by direct \(3\)-coherence on that path.

For composable words \(u,v\), construct
\[
\mu_{u,v}:
N_u(A,B)\cdot N_v(B,C)
\Longrightarrow
N_{uv}(A,C)
\tag{7}
\]
as follows.

1. Concatenate the two lists defining the normal forms.
2. Reassociate to make the two path comparisons at the join a binary subexpression.
3. Apply \(m\) there.
4. Return to the prescribed left association.

The reassociation is a direct \(3\)-coherence on \(C_N\), with each list entry substituted for a distinct \(2\)-variable. The contraction is inserted by mixed composition.

There is exactly one pair to contract:

| Words | Pair at the join |
|---|---|
| Both nonempty | \(\kappa(T_u,B)\cdot\kappa(B,S_v)\) |
| \(u\) empty | \(\kappa(A,B)\cdot\kappa(B,S_v)\) |
| \(v\) empty | \(\kappa(T_u,B)\cdot\kappa(B,C)\) |
| Both empty | \(\kappa(A,B)\cdot\kappa(B,C)\) |

Thus (7) includes every empty-word case.

When another operation introduces a longer sequence of adjacent path comparisons, contract its leftmost adjacent pair and repeat. Each contraction reduces the number of list entries.

### 2.2 The \(4\)-cells for the fold

The comparison between two contraction orders has three cases.

**The same first pair.** Compare the reassociation routes by direct \(4\)-coherence on \(C_N\), then continue with the shorter list.

**Disjoint first pairs.** First group each pair as one \(2\)-subexpression. The two contraction \(3\)-cells then occupy distinct positions in a vertical pasting \(V_n(\mathbf k)\). Their interchange is a direct \(4\)-coherence there. Continue after both contractions.

**Overlapping first pairs.** The overlap is
\[
\kappa(A,B),\quad\kappa(B,C),\quad\kappa(C,D)
\]
on one actual path. The two contraction routes are parallel full \(3\)-terms on that path. Use their direct \(4\)-coherence.

Pure reassociation comparisons are taken on \(C_N\); reassociation naturality is taken on the corresponding \(V_n(\mathbf k)\).

This constructs the associativity comparison for \(\mu\), including its empty-word cases. It also constructs the padding-unit comparisons. It is an induction on the number of list entries, not an appeal to an unspecified coherence theorem.

No step exchanges two \(F_i\)'s.

## 3. Fixed path whiskering

This is the part needed to evaluate a retained frame after its marked \(2\)-variables are assigned longer words.

Let \(W\) be fixed left or right whiskering by a specified bracketed \(1\)-path. There is a direct \(3\)-coherence
\[
d_W(U,V):
WU\cdot WV\Longrightarrow W(U\cdot V)
\tag{8}
\]
on \(P*_0C_2\) or \(C_2*_0P\), respectively.

Its associativity and naturality \(4\)-cells are direct coherences on the corresponding framed \(C_3\) and \(V_n(\mathbf k)\).

There is also an actual-path comparison
\[
\rho_W(A,B):
W\kappa_p(A,B)
\Longrightarrow
\kappa_{Wp}(WA,WB).
\tag{9}
\]
The right side is the chosen comparison on the expanded literal path. It is generally not the substitution image of the original \(\kappa_p\).

### 3.1 Comparing two bracketings of a whiskered letter

Let
\[
Q=P_\ell*_0D^2(z)*_0P_r.
\]
Suppose \(S(z)\) and \(T(z)\) are two expressions obtained by whiskering the same marked \(2\)-variable with the full exterior paths.

On \(Q\), form
\[
\operatorname{Pad}_Q(T;\sigma S,\tau S)
=
\bigl(
\kappa(\sigma S,\sigma T)\cdot T
\bigr)\cdot
\kappa(\tau T,\tau S),
\]
using the source and target path contexts of \(Q\). Then define
\[
e^Q_{S,T}
=
\mathsf C_Q
\bigl(S,\operatorname{Pad}_Q(T;\sigma S,\tau S)\bigr).
\tag{10}
\]

After a substitution \(\eta\), repair the two evaluated path comparisons to the chosen comparisons on the actual expanded paths:
\[
\delta_s:
\kappa(\sigma S,\sigma T)[\eta]
\Longrightarrow
\kappa_{\mathrm{actual}}
(\sigma S[\eta],\sigma T[\eta]),
\]
and similarly \(\delta_t\).

Both repairs are direct \(3\)-coherences on paths. Define
\[
\epsilon_{S,T;\eta}
=
e^Q_{S,T}[\eta]\ ;
\operatorname{Map}(\delta_s,1_{T[\eta]},\delta_t).
\tag{11}
\]

This is the required conversion from one raw whiskering expression to the other, padded by the actual-path comparisons.

The compatibility of successive conversions is obtained in two stages:

- before evaluation, compare the two full \(3\)-routes by direct \(4\)-coherence on \(Q\);
- after evaluation, compare path repairs on their actual paths and move them past the marked \(2\)-term using \(V_3(1,0,1)\).

Naturality in a \(3\)-variable \(h:z\Rightarrow z'\) is formed on
\[
P_\ell*_0D^3(h)*_0P_r.
\tag{12}
\]

If the two raw expressions have differently associated boundaries, (10) supplies the necessary boundary comparisons. There is no unpadded comparison between nonparallel terms.

### 3.2 The finite-word whiskering term

Construct
\[
\phi_{W,w}:
W N_w(A,B)
\Longrightarrow
N_{Ww}(WA,WB)
\tag{13}
\]
by the following fixed procedure:

1. Distribute \(W\) over the left-associated list using the reverse of (8).
2. Convert each whiskered path comparison using (9).
3. Convert each whiskered raw letter to the chosen raw letter in the enlarged interval using (11).
4. Flatten the resulting list.
5. Contract adjacent path comparisons by the leftmost-first rule of §2.

For an empty word, (13) is just (9).

For two-sided whiskering, perform the right whisker first and the left whisker second, matching convention (2).

The required multiplicativity \(4\)-cell compares
\[
W\mu_{u,v}\ ;\phi_{W,uv}
\]
with
\[
d_W^{-1}\ ;
(\phi_{W,u}\cdot\phi_{W,v})\ ;
\mu_{Wu,Wv}.
\tag{14}
\]
Both start at \(W(N_u\cdot N_v)\) and end at the same literal normal form.

To construct it, move both routes to the same sequence: distribute, convert individual list entries, then contract path comparisons. The local comparisons are:

| Operation being compared | Pasting arity for the \(4\)-cell |
|---|---|
| Two distribution orders | Framed \(C_3\) |
| Distribution naturality | Framed \(V_n(\mathbf k)\) |
| Reassociation naturality | \(V_n(\mathbf k)\) |
| \(\rho_W\) versus \(m\) | The actual expanded path |
| Successive raw-letter conversions | \(P_\ell*_0D^2*_0P_r\) |
| Raw-letter conversion naturality | \(P_\ell*_0D^3*_0P_r\) |
| Two path-contraction orders | The three cases of §2.2 |

Each comparison is then inserted into the surrounding expression by mixed composition.

### 3.3 Evaluating a marked letter at a long word

One further distinction is necessary for fusion.

Suppose the marked \(z\) in (10) is assigned a long normal form. To compare the conversion applied to the whole word with the conversions applied to individual entries:

1. Replace **every** entry of that word, including its path comparisons, by a distinct \(2\)-variable of \(C_N\).
2. Form the comparison on
   \[
   P_\ell*_0C_N*_0P_r.
   \]
   At this stage every entry is treated as an independent variable.
3. Evaluate.
4. Only now replace conversions of path-only entries by their actual-path routes.
5. Apply the contraction comparisons of §2.2.

Before evaluation, both routes have every marked \(2\)-variable in their free-variable sets. After evaluation, the path-only comparisons are made on actual paths.

This supplies the word-substitution law for \(\epsilon\). It avoids treating an independent variable of \(C_N\) as if it were already a path coherence.

## 4. Recursive normalizers and evaluation fusion

### 4.1 Normalizers

For a \(2\)-term with empty strict word, use its literal lift to the actual path context and a direct \(3\)-coherence to (4).

For a \(2\)-variable, use the generic unit-insertion \(3\)-coherence on its \(2\)-disc, followed by path repairs to the two comparisons in (3).

Now let
\[
T=\operatorname{coh}_{P,A}[\gamma]
\]
have nonempty strict word. Use the accepted factorization to obtain an exact presentation
\[
T=H[\eta]
\]
on a retained frame
\[
R=P_\ell*_0C_n*_0P_r.
\]

**Retain every \(2\)-slot of the active original column**, including slots assigned terms with empty strict word.

Let \(B_H\) be its formal reference word: fixed whiskerings of all the marked \(2\)-variables, in their vertical order, with the prescribed path comparisons. It has exactly the same boundary as \(H\). Both are full in \(R\), so put
\[
v_H=\mathsf C_R(H,B_H).
\tag{15}
\]

Define a separate evaluator \(D\) on reference expressions:

\[
\begin{array}{c|l}
\text{Expression} & \text{Evaluation comparison}\\ \hline
z & \nu_{\eta z}\\
K\text{ a path term} & \text{direct actual-path normalizer}\\
B_1\cdot B_2
& \operatorname{Map}(D_{B_1},D_{B_2});\mu\\
WB & W(D_B);\phi_W .
\end{array}
\tag{16}
\]

Then define
\[
\boxed{\nu_T=v_H[\eta];D_{B_H,\eta}.}
\tag{17}
\]

The recursive calls in (16) are to the actual \(2\)-arguments assigned to the retained original slots. They are proper subterms of \(T\).

In particular, evaluating a newly assembled reference word does **not** call \(\nu\) on that composite. It applies the finite fold (16).

### 4.2 The restricted presentation comparison

For fusion, the needed comparison is between presentations of the **same original coherence head** before and after substitution.

If the evaluated total word remains nonempty, its active original \(0\)-column remains active:

- an inactive column has no marked \(2\)-variable in its assigned terms;
- substitution of its \(0\)- and \(1\)-data cannot introduce one;
- losing the sole active column would make the total word empty.

Both presentations therefore retain the same list of original \(2\)-slots, and, for \(3\)-heads, the same \(3\)-links. Slots that become empty are still retained.

The common refinement supplied by §2.12 changes only the inactive exterior paths. It introduces no additional marked \(2\)-slots. Consequently:

- both head-normalizing routes have the same marked higher variables in their free-variable sets;
- every added exterior edge belongs to the support of the relevant endpoint path.

The head comparison on that refinement is therefore full.

Its reference-word folds agree up to \(4\)-cells by (6)–(14): path comparison, fixed whiskering, raw-letter conversion, reassociation, and contraction. This is a finite-expression induction.

If the total evaluated word is empty, both complete routes are path-only and are compared directly on their actual common path.

This is the restricted presentation comparison needed here. No arbitrary refinement invariance is being asserted.

### 4.3 Fusion

On retained frames, define the relative normalizer \(\lambda_u\) by the same recursive construction and the same elementary fold.

There is a \(4\)-term
\[
\boxed{
\mathcal F_{u,\sigma}:
\nu_{u[\sigma]}
\Longrightarrow
\lambda_u[\sigma]\ ;D_{B_u,\sigma}.
}
\tag{18}
\]

Construct it by induction on the relative term \(u\).

For a nonvariable head, apply the induction hypotheses to its proper \(2\)-arguments. The remaining expression is built using the four clauses of (16):

- path positions use actual-path \(4\)-coherences;
- vertical products use the finite-list comparisons of §2.2;
- fixed whiskers use (14);
- raw-letter conversions evaluated at words use §3.3.

Finally use the restricted presentation comparison above.

The variable case deserves a separate description. Put \(Z=z[\sigma]\). Use the generic naturality \(4\)-coherence on
\[
D^3(h:Z\Rightarrow N_Z),
\qquad h\mapsto\nu_Z,
\]
to move the generic padding insertion across \(\nu_Z\). The remaining padding-unit calculation is made first on \(C_N\), with every entry of \(N_Z\) marked. After evaluation, the first and last path contractions are compared on their actual paths. If \(N_Z\) is an empty-word normal form, the whole remaining comparison is on one path.

This uses the already constructed \(\nu_Z\). It does not invoke \(\nu\) on \(N_Z\), so the induction is well founded.

## 5. The \(3\)-term induction and RC(3)

For every \(3\)-term \(G:T\Rightarrow T'\) in the full chain cylinder, construct
\[
\boxed{
\Lambda_G:G;\nu_{T'}\Longrightarrow\nu_T.
}
\tag{19}
\]

The path-only case is already settled.

### A head over a retained \(2\)-pasting

Let its relative form be \(H:U\Rightarrow V\). Since \(U,V\) are parallel full \(2\)-terms on that pasting, their formal normal words are literally the same.

Hence
\[
\Xi_H=
\mathsf C_R(H;\lambda_V,\lambda_U)
\tag{20}
\]
is a legal \(4\)-term.

Evaluate (20), and attach the fusion comparisons (18) at its two ends.

### A head over a retained \(3\)-pasting

Its arity has the form
\[
R=P_\ell*_0V_n(\mathbf k)*_0P_r.
\]

Define \(\mathcal W_R\) on the formal normal word by updating each slot along
\[
h_i^1,\ldots,h_i^{k_i},
\]
in a fixed order of slots and links. Whisker each update by the exterior paths and insert it into the corresponding position of the normal word.

The path comparisons are unchanged: the \(2\)-boundaries of each \(h_i^j\) have literally equal \(1\)-boundaries.

Every retained \(3\)-link is used, including those later evaluated at structural terms. Thus
\[
\Xi_H=
\mathsf C_R
\bigl(H;\lambda_V,\lambda_U;\mathcal W_R\bigr)
\tag{21}
\]
is full.

After evaluation, construct
\[
\mathcal W_R[\eta]\ ;D_{B_V,\eta}
\Longrightarrow
D_{B_U,\eta}.
\tag{22}
\]
Move the fold backwards through the slot updates using the laws of §§2–3. At an updated slot, apply the proper-argument induction hypothesis
\[
h[\eta];\nu_{\tau(h[\eta])}
\Longrightarrow
\nu_{\sigma(h[\eta])}.
\]
Process a chain of links from its last link backwards. Changes of slot order needed to move independent normalization operations use the corresponding \(V_n(\mathbf k)\) \(4\)-coherences.

Combining (18), (21), and (22) gives
\[
\begin{aligned}
G;\nu_{T'}
&\Longrightarrow
G;\lambda_V[\eta];D_{B_V,\eta}\\
&\Longrightarrow
\lambda_U[\eta];\mathcal W_R[\eta];D_{B_V,\eta}\\
&\Longrightarrow
\lambda_U[\eta];D_{B_U,\eta}\\
&\Longrightarrow\nu_T.
\end{aligned}
\]
This is (19). The recursion uses only proper \(3\)-arguments of the original head.

### Cancellation

The normalizers are composites of invertible \(3\)-coherences. For a primitive full coherence, reverse its endpoints and construct its cancellation \(4\)-cells on the same pasting arity; extend through composition and whiskering. This is also covered by the syntactic invertibility construction for terms with empty top-dimensional support. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

For parallel \(3\)-terms \(\alpha,\beta:T\Rightarrow T'\), compose
\[
\Lambda_\alpha
\quad\text{with the reverse of}\quad
\Lambda_\beta
\]
to obtain
\[
\alpha;\nu_{T'}\Longrightarrow\beta;\nu_{T'}.
\]
Right cancellation of \(\nu_{T'}\) gives
\[
\boxed{\alpha\Longrightarrow_4\beta.}
\tag{23}
\]

This proves **RC(3) for every finite full chain cylinder**.

The argument permits arbitrarily many retained slots, including slots evaluated at empty words. The number of nonidentity letters need not equal the number of retained slots.

By the reduction in §2.3 of the question, it also gives \(K\) for every \(3\)-dimensional coherence over a fully selected finite chain, for any fixed lower lifts.

## 6. The two proposed proper selections

Neither proposed example requires exchange between independent active columns.

### 6.1 \(Y=\{z,g\}\)

The nontrivial declarations are
\[
f:x\to y,\qquad
g^-:y\to z^-,\qquad
Z:z^-\to z^+,\qquad
g^+:y\to z^+,
\]
\[
G:g^-*_0Z\Rightarrow g^+.
\]

The source and target paths of \(G\) have only \(y,z^+\) as common vertices. Thus the one-letter transition has one active column.

Its local normal form is
\[
N_G(A,B)
=
\bigl(\kappa_{g^-Z}(A,g^-*_0Z)\cdot G\bigr)
\cdot\kappa_{g^+}(g^+,B).
\]

The only nontrivial exterior extension is the fixed prefix \(f\), with raw letter
\[
E=f*_0G.
\]
It uses the literal retained frame \(D^1(f)*_0C_n\).

The construction above applies to the words \(G\) and \(fG\), with the empty-word cases handled on paths. Therefore this cylinder has RC(3).

### 6.2 \(Y=\{y,z,f,g\}\)

Here
\[
F:f^-*_0Y\Rightarrow f^+,
\qquad
G:g^-*_0Z\Rightarrow Y*_0g^+.
\]

The full transition has forced order \(G\), then \(F\):
\[
f^-g^-Z\;\longrightarrow\;f^-Yg^+
\;\longrightarrow\;f^+g^+.
\]
The first step creates the subpath required by the second.

Choose
\[
E_G=f^-*_0G,\qquad E_F=F*_0g^+.
\]
Their actual endpoints include
\[
\tau E_G=f^-*_0(Y*_0g^+),
\qquad
\sigma E_F=(f^-*_0Y)*_0g^+.
\]

Consequently the normal form is
\[
\boxed{
\operatorname{LF}\bigl[
\kappa_{f^-g^-Z}(A,\sigma E_G),E_G,
\kappa_{f^-Yg^+}(\tau E_G,\sigma E_F),E_F,
\kappa_{f^+g^+}(\tau E_F,B)
\bigr].
}
\tag{24}
\]

The middle comparison in (24) is essential.

The full two-letter transition has only its outer vertices in common between source and target paths. Its one-letter subtransitions have just the fixed prefix \(f^-\) or suffix \(g^+\). These are exactly the retained frames used above.

Hence this cylinder also has RC(3).

For comparison, \(Y=\{x,f,g\}\) gives
\[
F:f^-\Rightarrow X*_0f^+,\qquad
G:g^-\Rightarrow g^+,
\]
and both orders \(FG\) and \(GF\) exist. That case requires the additional two-column exchange/fusion construction.

## 7. Two vertically composed \(2\)-discs

Now take
\[
Q=(x,y,f,g,h,\ A:f\Rightarrow g,\ B:g\Rightarrow h)
\]
with full selection. Write
\[
r_0=f,\quad r_1=g,\quad r_2=h,
\]
and put
\[
p_i=r_i^-*_0Y,\qquad q_i=X*_0r_i^+,
\]
\[
c_0=A^-*_0Y,\quad c_1=B^-*_0Y,\qquad
d_0=X*_0A^+,\quad d_1=X*_0B^+.
\]

The generating \(3\)-cells are
\[
U_A:(c_0\cdot F_1)\Longrightarrow(F_0\cdot d_0),
\]
\[
U_B:(c_1\cdot F_2)\Longrightarrow(F_1\cdot d_1).
\tag{25}
\]

Let \(\Gamma_0\) be the context with \(U_A,U_B\) omitted.

### 7.1 RC(3) for \(\Gamma_0\)

Every mixed strict \(2\)-cell \(p_i\Rightarrow q_j\) has the unique word
\[
C(i,k,j)=
c_i\cdots c_{k-1}\,F_k\,d_k\cdots d_{j-1},
\qquad i\le k\le j.
\tag{26}
\]

Indeed, before the \(F_k\)-step only the \(c\)-chain is available; after it only the \(d\)-chain is available.

Different \(k\)'s give different strict \(2\)-cells. Normal forms must therefore be indexed by the whole word (26), not just by \(p_i,q_j\).

The new length-three words are
\[
c_0c_1F_2,\qquad c_0F_1d_1,\qquad F_0d_0d_1.
\tag{27}
\]

For a mixed value, its source path \(r_i^-Y\) and target path \(Xr_j^+\) have exactly \(x^-,y^+\) as common vertices. Thus its retained arity has one active original \(0\)-column and point-supported exterior columns.

The pure-side values use the genuine pastings
\[
C_m,\qquad C_m*_0D^1(Y),\qquad D^1(X)*_0C_m.
\tag{28}
\]
All remaining values are path-only.

The finite-word proof of §§2–5 applies with the raw-letter dictionary
\[
c_0,c_1,F_0,F_1,F_2,d_0,d_1
\]
and the typing restrictions (26). Its proof uses the prescribed word order, not the numerical labels of the \(F_i\)'s.

When \(c_i,d_i\) are formal entries of \(C_n\), they remain independent variables until evaluation. Their internal whiskerings are exposed only using their own marked-disc frames
\[
D^2(A_i^-)*_0D^1(Y),
\qquad
D^1(X)*_0D^2(A_i^+).
\]
This is precisely the distinction enforced in §3.3.

Therefore
\[
\boxed{\mathrm{RC}(3)_{\Gamma_0}.}
\tag{29}
\]

### 7.2 Strict \(3\)-values

The action of \(U_A\) decreases the crossing index \(1\to0\); \(U_B\) decreases it \(2\to1\).

Two nonidentity strict \(3\)-cells cannot compose in dimension \(0\): each has outer endpoints \(x^-,y^+\). They cannot compose in dimension \(1\), because that would require a path \(q_j\) to equal a path \(p_i\).

Thus there are exactly five nonidentity strict \(3\)-values:
\[
\pi U_A,\quad \pi U_B,\quad
\pi W_A,\quad \pi W_B,\quad
(\pi W_B)*_2(\pi W_A),
\tag{30}
\]
where
\[
W_A=U_A*_1d_1,\qquad W_B=c_0*_1U_B.
\]

The only two-generator order is \(U_B\), then \(U_A\).

### 7.3 Extracting the generating steps

Use the accepted head-sequentialization construction from §2.13 of the question.

The extension from one generator to several uses the direct \(4\)-coherence
\[
r*_ks
\Longrightarrow
\bigl(r*_k1_{\sigma s}\bigr);
\bigl(1_{\tau r}*_ks\bigr),
\qquad k=0,1,
\tag{31}
\]
on \(D^3*_kD^3\), together with distribution of whiskering over \(;\). Mixed-dimensional versions use \(D^3*_kD^2\) and its reflection.

This transforms any \(3\)-term into a vertical program of structural \(3\)-terms and individually whiskered copies of \(U_A,U_B\).

An entry with identity strict \(3\)-image belongs to \(\Gamma_0\). To verify this, assign weight \(1\) to each generating \(U_A,U_B\). Strict compositions add weights; units have weight \(0\); the strict relations preserve weight. Induction on CaTT \(3\)-terms shows that a term with either \(U_A\) or \(U_B\) in its top-dimensional support has positive weight.

By (30), the extracted program has at most two nonstructural entries.

### 7.4 Normalizing \(2\)-coefficients

After the point-supported \(0\)-whiskers are normalized as in the accepted \(2\)-disc proof, an active entry has the form
\[
(L*_1U)*_1R.
\]

Suppose its actual \(1\)-boundaries are \(A,B\). Choose the following exact targets for its coefficients:

| Strict entry | Target for \(L\) | Target for \(R\) |
|---|---|---|
| \(U_A\) | \(\kappa_{p_0}(A,p_0)\) | \(\kappa_{q_1}(q_1,B)\) |
| \(U_B\) | \(\kappa_{p_1}(A,p_1)\) | \(\kappa_{q_2}(q_2,B)\) |
| \(W_A\) | \(\kappa_{p_0}(A,p_0)\) | \(d_1\cdot\kappa_{q_2}(q_2,B)\) |
| \(W_B\) | \(\kappa_{p_0}(A,p_0)\cdot c_0\) | \(\kappa_{q_2}(q_2,B)\) |

Each target is parallel to the original coefficient and has the same strict image. RC(2) supplies the coefficient \(3\)-comparisons in \(\Gamma_0\).

For a left coefficient comparison \(\kappa:L\Rightarrow L_0\), and \(U:S\Rightarrow T\), use the direct \(4\)-coherence on
\[
D^3(\kappa)*_1D^3(U)
\]
between
\[
(\kappa*_1S);(L_0*_1U)
\quad\text{and}\quad
(L*_1U);(\kappa*_1T).
\tag{32}
\]
Both have source \(L\cdot S\) and target \(L_0\cdot T\).

The reflected construction treats the right coefficient. RC(3) in \(\Gamma_0\) supplies cancellation for the coefficient comparisons.

Regrouping the resulting expression uses associator-padded \(4\)-coherences. For example, compare
\[
((K\cdot c_0)*_1U_B);a_T
\]
with
\[
a_S;\bigl(K*_1(c_0*_1U_B)\bigr)
\]
on
\[
D^2(K)*_1D^2(c_0)*_1D^3(U_B).
\tag{33}
\]
The boundary associators in (33) are required.

Hence each active entry is \(4\)-comparable to a fixed \(W\in\{U_A,U_B,W_A,W_B\}\), with path padding and structural \(3\)-terms before and after it.

### 7.5 Exact anchors and the two-generator normal form

All anchors must retain the actual \(1\)-boundaries.

For each strict \(2\)-word \(C\), use the normal form \(N_C(A,B)\) constructed above. For \(z:A\Rightarrow B\), write
\[
\nu_z:z\Rightarrow N_{\pi z}(A,B),
\qquad
\bar\nu_z:N_{\pi z}(A,B)\Rightarrow z.
\]

For a fixed raw \(W\) with \(1\)-boundaries \(p,q\), first define
\[
W^{A,B}
=
\bigl(\kappa_p(A,p)*_1W\bigr)*_1\kappa_q(q,B).
\]
Then set
\[
E_W^{A,B}
=
\bar\nu_{\sigma(W^{A,B})};
W^{A,B};
\nu_{\tau(W^{A,B})}.
\tag{34}
\]

For the long interval, put
\[
C_2=c_0c_1F_2,\qquad
C_1=c_0F_1d_1,\qquad
C_0=F_0d_0d_1.
\]
Equation (34) gives
\[
E_B^{A,B}:N_{C_2}(A,B)\Rightarrow N_{C_1}(A,B),
\]
\[
E_A^{A,B}:N_{C_1}(A,B)\Rightarrow N_{C_0}(A,B).
\tag{35}
\]
These are literally composable.

The raw terms are not:
\[
\tau W_B=c_0\cdot(F_1\cdot d_1),
\qquad
\sigma W_A=(c_0\cdot F_1)\cdot d_1.
\tag{36}
\]

An extracted two-generator program has a structural run between those boundaries. After path padding, RC(3) in \(\Gamma_0\) compares that run with
\[
\nu_{\tau(W_B^{A,B})};
\bar\nu_{\sigma(W_A^{A,B})}.
\tag{37}
\]
This supplies the exact middle seam in (35).

Consequently, for \(\alpha:s\Rightarrow t\), where \(s,t:A\Rightarrow B\), the normal \(3\)-term is:

- for identity strict image,
  \[
  \nu_s;\bar\nu_t;
  \]
- for strict image \(\pi W\),
  \[
  \nu_s;E_W^{A,B};\bar\nu_t;
  \]
- for strict image \((\pi W_B)*_2(\pi W_A)\),
  \[
  \boxed{
  \nu_s;
  \bigl(E_B^{A,B};E_A^{A,B}\bigr);
  \bar\nu_t.
  }
  \tag{38}
  \]

The preceding constructions give a \(4\)-term from \(\alpha\) to the corresponding expression. Two parallel \(3\)-terms with equal strict image select the same expression. Reverse one comparison and compose.

Therefore
\[
\boxed{
\mathrm{RC}(3)_{\,(D^2*_1D^2)\uparrow\mathrm{Var}(D^2*_1D^2)}.
}
\tag{39}
\]

No comparison of \(4\)-cell choices is used in this proof.

## 8. Scope

The new results are RC(3) for arbitrary finite full chain cylinders, the two specified proper selections, and the full vertical two-disc cylinder. They give the corresponding \(K\)'s in dimension \(3\) for arbitrary fixed lower lifts.

The following remain unresolved by this construction:

- proper selections with independent active columns;
- the full cylinder of \(D^2*_0D^2\), whose \(2\)-skeleton already requires two-column comparisons;
- RC(3) on all cylinders;
- RC(4) and the all-dimensional conjecture;
- the \(5\)-cell comparison required for global uniqueness of dimension-\(3\) choices of \(K\).

The indispensable distinction throughout is between **forming a coherence on a retained pasting with every marked variable present**, and **repairing its evaluated path comparisons on actual literal paths**. That distinction is what makes the arbitrary-length fusion construction type correctly.

