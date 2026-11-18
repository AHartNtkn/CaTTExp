# Problem: naturality of CaTT coherences at depth ≥ 2, round 4

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first. Rounds 1–3 and their verified answers are archived in `answered/naturality-arbitrary-depth-2026-11-18.md`, `answered/naturality-arbitrary-depth-r2-2026-11-18.md` and `answered/naturality-arbitrary-depth-r3-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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

## 3. What remains, and why

RC(3) fails for loopy contexts such as (x : ⋆, a : id_x → id_x), so a proof must use acyclicity. Rounds 2 and 3 handle cylinders in which every column carrying a 2-generator either spans the unique source and sink (point-supported discarded columns) or has exactly one fixed edge on one side. In longer cylinders a column can have nonidentity paths on both sides, several 2-generators can occur in more than one order, and for Q of dimension 2 the cylinder has 3-variables (e.g. A↑ for A : f ⇒ g), so parallel 3-terms need not have equal strict images automatically.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: RC(3) on the cylinder of the 2-disc.** Q = (x, y, f, g : x → y, A : f ⇒ g), Y = Var(Q). Q↑Y has the 2-variables f↑, g↑ and the 3-variable A↑. Prove that any two parallel 3-terms of Q↑Y with equal strict image are connected by a 4-term. (This gives K for every 3-dimensional coherence over the 2-disc, for instance the unitor `A ∗₁ id_g → A`, now for arbitrary lower lifts.)
2. **Longer cylinders.** For the cylinder of a chain x₀ → x₁ → … → x_k (k ≥ 3), or of any 1-dimensional pasting context with Y a proper up-closed subset, item 12 removes inactive columns literally. Complete item 10's construction for the active columns: normalisers for vertical chains whose 2-variables carry arbitrary composites, compatible with evaluation ("fusion"), including several 2-generators in more than one order.
3. **RC(3) on all cylinders.** Prove RC(3) for every cylinder Q↑Y, or for every finite Steiner loop-free context. Or give a loop-free counterexample.
4. **Fixed dimension for cylinders.** Is there an analogue of item 11 for cylinders, giving `RC(r+1, (ΣQ)↑Y′) ⇒ RC(r, Q↑Y)` for a suitable Y′? Combined with item 3 of §2, this would reduce Conjecture N through dimension n to RC(n) on cylinders.
5. **All dimensions.** Prove RC(n) for all n on the cylinders Q↑Y. By §2 item 3, this proves Conjecture N at every depth.
6. **Global choice of K in dimension 3.** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with Y = Var(Q), compatible with substitution. Two choices of K for the same (Q, B, Y) are 4-cells; the minimal requirement is a **5-cell** between them (item 9).

## 5. What counts as a solution

Explicit terms for question 1, 2 or 6; a proof of RC(3) or RC(n) for the cylinders or for loop-free contexts; a proof of the descent in question 4; a counterexample (a cylinder Q↑Y, or a loop-free context, with two parallel n-terms of equal strict image and no term between them); or a published reference.

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

**Questions 1 and 4 have positive answers.** For the 2-disc cylinder, the construction reduces every 3-term with nonidentity strict image to one use of \(A^\uparrow\), with explicitly controlled whiskering. For descent, take
\[
Y'=\Sigma Y
\]
and leave the two new suspension objects unselected.

I also establish the literal factorization asked for in Question 2 for full chain cylinders. For proper \(Y\), the proposed frame with only one retained vertical chain can fail: several vertical chains may need to be retained.

The arguments below use the results accepted in §2, particularly RC(2), the square construction, and the two-letter construction from round 3.

# 1. RC(3) for the cylinder of the 2-disc

Let \(\Gamma\) be that cylinder, and let \(\Gamma_0\) be the context obtained by deleting its 3-variable. Write
\[
X=x^\uparrow,\qquad Y=y^\uparrow,\qquad
a=A^-,\qquad b=A^+,\qquad
F=f^\uparrow,\qquad G=g^\uparrow.
\]

Introduce the following actual CaTT terms:
\[
\begin{aligned}
p&=f^-*_0Y,&q&=g^-*_0Y,\\
r&=X*_0f^+,&s&=X*_0g^+,\\
c&=a*_0Y,&d&=X*_0b,\\
L&=c*_1G,&R&=F*_1d.
\end{aligned}
\]
Their boundaries match literally. The remaining variable is
\[
U=A^\uparrow:L\longrightarrow R.
\]

Throughout this section, write
\[
u\cdot v=u*_1v,\qquad M;N=M*_2N.
\]
Thus \(\cdot\) composes 2-cells, including the corresponding higher whiskerings, while \(;\) composes 3-cells.

## 1.1 The strict calculation

The nonidentity strict 2-cells of \(\Gamma_0\) are exactly the images of the following eight terms.

| Term | Source | Target |
|---|---|---|
| \(a\) | \(f^-\) | \(g^-\) |
| \(b\) | \(f^+\) | \(g^+\) |
| \(c=a*_0Y\) | \(p\) | \(q\) |
| \(d=X*_0b\) | \(r\) | \(s\) |
| \(F\) | \(p\) | \(r\) |
| \(G\) | \(q\) | \(s\) |
| \(L=c\cdot G\) | \(p\) | \(s\) |
| \(R=F\cdot d\) | \(p\) | \(s\) |

In particular,
\[
\pi L\ne\pi R.
\]

To verify completeness, inspect the generating rewrites on 1-paths. At the outer endpoints \(x^-\to y^+\), they are
\[
p\xrightarrow{c}q\xrightarrow{G}s,
\qquad
p\xrightarrow{F}r\xrightarrow{d}s.
\]
There is no nonidentity 2-cell into \(p\) or out of \(s\). The unwhiskered rewrites \(a,b\) give the other two entries.

It follows that the only nonidentity strict 3-cell of \(\Gamma\) is \(\pi U\):

- it cannot be composed with another copy of itself along dimension \(2\), since \(\pi L\ne\pi R\);
- it cannot receive a nonidentity 2-whisker along dimension \(1\), since there is no nonidentity 2-cell into \(p\) or out of \(s\);
- it cannot receive a nonidentity 1-whisker along dimension \(0\), since \(x^-\) is initial and \(y^+\) is terminal in the generating directed graph.

The number of uses of \(U\) in the strict image of a 3-term is additive under composition. Consequently:

1. a 3-term with identity strict image is a term of \(\Gamma_0\);
2. a 3-term with strict image \(\pi U\) uses \(U\) exactly once when expanded into binary composition and structural 3-terms.

Here a **structural 3-term** means a term of \(\Gamma_0\).

## 1.2 RC(3) for the 2-skeleton \(\Gamma_0\)

This is the first input to the construction involving \(U\).

Terms with identity strict 2-boundary are handled by the path result. For the other strict 2-values:

| Strict 2-value | Context to which the terms restrict | Available construction |
|---|---|---|
| \(a,b\) | A 2-disc | Direct 4-coherence |
| \(c\) | \(D^2(a)*_0D^1(Y)\) | Direct 4-coherence |
| \(d\) | \(D^1(X)*_0D^2(b)\) | Direct 4-coherence |
| \(F,G\) | The corresponding lax square | Round 2 |
| \(L,R\) | A two-letter case described below | Round-3 construction |

These restrictions concern the entire typed support of the 3-term. Positivity of the strict 2-image gives the restriction for 2-terms. For 3-terms, the absence of 3-generators in \(\Gamma_0\) identifies their 2-support with that of either boundary; the path classification then restricts their 1-support. This is the support argument used in the accepted square proof, based on Lemma 36. The resulting terms lift by renaming to the indicated pasting contexts. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

For \(L\), its outer 1-paths \(p=f^-Y\) and \(s=Xg^+\) have only \(x^-,y^+\) as common vertices. Therefore every constructor with strict 2-value \(L\) has the exact point-supported factorization through
\[
C_n\quad\text{or}\quad V(k_1,\ldots,k_m)
\]
from round 3. The active 2-arguments have nonidentity values only among
\[
c,\quad G,\quad L.
\]
The order of the two distinguished letters is forced: \(c\), then \(G\).

Thus the round-3 two-letter construction applies with these letters. Its smaller cases are already available: the \(c\)-case is supported on a pasting context, and the \(G\)-case is a square. Proper arguments of value \(L\) are handled by structural induction, as in round 3.

One can retain the normal-form seam
\[
c\cdot\kappa_q(q,q)\cdot G.
\]
The comparison with the literal term \(L=c\cdot G\) uses the path 3-cell
\[
1_q\longrightarrow\kappa_q(q,q),
\]
together with vertical unitors and associators. No equality
\(\kappa_q(q,q)\equiv1_q\) is imposed.

The \(R\)-case is identical, with distinguished letters \(F,d\) and middle path \(r\).

This proves
\[
\boxed{\operatorname{RC}(3,\Gamma_0).}
\tag{1}
\]

The dependency order matters: first construct the normalizers and fusion for \(L,R\) by the accepted two-letter induction; only after obtaining (1) may arbitrary structural normalizers be substituted for those choices.

## 1.3 Fix the target normal form for 3-terms

For a 1-term \(e\) with strict path \(p\), and a 1-term \(h\) with strict path \(s\), fix path coherences
\[
k_e=\kappa_p(e,p),\qquad j_h=\kappa_s(s,h).
\]

Put
\[
L_{e,h}=(k_e\cdot L)\cdot j_h,\qquad
R_{e,h}=(k_e\cdot R)\cdot j_h,
\]
and define the 3-term
\[
U_{e,h}=(k_e*_1U)*_1j_h:
L_{e,h}\longrightarrow R_{e,h}.
\tag{2}
\]
These are mixed-dimensional whiskerings with the displayed brackets.

For every 2-term \(t:e\to h\) with \(\pi t=\pi L\), choose, using RC(2),
\[
\nu_t:t\longrightarrow L_{e,h}.
\]
For \(\pi t=\pi R\), choose
\[
\nu_t:t\longrightarrow R_{e,h}.
\]
All these terms belong to \(\Gamma_0\).

Choose reverse 3-terms \(\bar\nu_t\) using RC(2). Their two cancellation 4-cells are supplied by (1). No choice-coherence condition on the family \(\nu\) is needed: (1) compares any two parallel structural 3-routes.

For \(v:t\to t'\) with strict image \(\pi U\), the target normal form will be
\[
\mathcal N(t,t')
=
(\nu_t;U_{e,h});\bar\nu_{t'}.
\tag{3}
\]
It depends only on the literal boundary terms \(t,t'\), the fixed path comparisons, and the fixed choices of \(\nu\).

We next construct a 4-term
\[
v\longrightarrow\mathcal N(t,t').
\tag{4}
\]

## 1.4 Sequentialize arbitrary 3-constructors first

This removes the need for a new arbitrary-head fusion theorem.

Consider a 3-head
\[
H=\operatorname{coh}_{P,u\to v}[\mathrm{id}_P].
\]

If \(\dim P\leq2\), every substitution instance of this head is structural. Suppose \(\dim P=3\).

A binary strict composite of \(P\) uses every maximal generator, with identities on maxima of lower dimension. Realize that expression weakly as follows.

- At a dimension-0 composition, the 0-boundary already matches literally.
- At a dimension-1 composition, insert a path 2-comparison if the matching 1-terms differ syntactically.
- At a dimension-2 composition, first align the literal 1-boundaries by path comparisons, then insert an RC(2) 3-bridge between the matching 2-terms.

All added 3-bridges are constructed in \(P_{\leq2}\). This context need not be a pasting context: universal RC(2) applies to it.

Call the result \(C_P\). It retains every maximal generator and has the required strict 3-image. Pad its 1-boundaries to those of \(H\), obtaining
\[
C'_P:S'\longrightarrow T'.
\]
RC(2) in \(P_{\leq2}\) gives
\[
a:u\longrightarrow S',\qquad
b:T'\longrightarrow v.
\]
Hence
\[
B_H=(a;C'_P);b
\]
is parallel to \(H\) and full in \(P\). Define
\[
\operatorname{coh}_{P,H\to B_H}[\mathrm{id}_P].
\tag{5}
\]
This is a legal 4-coherence.

After substitution, all the inserted 3-bridges remain structural: their arguments have dimension at most \(2\), so cannot use \(U\). Recursively apply (5) to the proper substituted 3-arguments.

We have therefore reduced to binary 3-composition. For \(k<2\), the comparison
\[
u*_kv
\longrightarrow
(u*_k1_{\sigma v});(1_{\tau u}*_kv)
\tag{6}
\]
is a direct 4-coherence on \(D^3*_kD^3\). Also use
\[
(M;N)*_kc
\longrightarrow
(M*_kc);(N*_kc)
\tag{7}
\]
on \((D^3*_2D^3)*_kD^2\), and the corresponding left-whiskering formula. These have literal matching boundaries by the componentwise boundary equations.

Equations (6)–(7), associativity, and the direct comparison between an identity-lifted 2-coefficient and mixed-dimensional whiskering extract every term of strict image \(\pi U\) into
\[
I_0;\omega(U);I_1,
\tag{8}
\]
with fixed brackets, where:

- \(I_0,I_1\) are structural 3-terms;
- \(\omega\) is obtained by binary whiskering by terms of dimension at most \(2\);
- dimension-1 coefficients have identity strict 2-image on \(p\) or \(s\);
- dimension-0 coefficients are supported at \(x^-\) or \(y^+\).

Every comparison used in this extraction is a coherence on a pasting context, followed by substitution.

## 1.5 Normalize the whiskering around \(U\)

The required statement is:

> For every \(\omega\) in (8), with literal 1-boundaries \(e,h\), there are structural 3-terms
> \[
> \delta_L:\omega(L)\to L_{e,h},\qquad
> \delta_R:\omega(R)\to R_{e,h},
> \]
> and a 4-term
> \[
> \omega(U);\delta_R
> \longrightarrow
> \delta_L;U_{e,h}.
> \tag{9}
> \]

Here are the constructors for an induction on \(\omega\).

### A. Vertical path coefficients

A 2-coefficient with identity strict image is a path term. Normalize it to the chosen \(\kappa\) using a path 3-coherence.

Its passage past \(U\) is the 4-interchanger on
\[
D^3*_1D^3.
\]
For example, for \(m:a\to a'\), the comparison
\[
(a*_1U);(m*_1R)
\longrightarrow
(m*_1L);(a' *_1U)
\tag{10}
\]
is a direct 4-coherence on that pasting.

Concatenated path coefficients are folded by path multiplication 3-cells and vertical associators. Their naturality in the distinguished 3-cell is obtained from:

- associator naturality on vertical 3-pastings;
- (10) for each path multiplication or cancellation;
- the unitor 4-law on \(D^3\).

This also handles the base case of \(\omega\): inserting the two pads in (2) is not treated as an identity operation.

### B. A dimension-0 coefficient of dimension 2

Let \(a:l_0\to l_1\) be point-supported, and let \(T:p\to s\) be a 2-cell. Define
\[
\theta_T:
(l_0*_0T)\cdot(a*_0s)
\longrightarrow
a*_0T
\tag{11}
\]
by direct 3-coherence on \(D^2(a)*_0D^2(T)\).

Its naturality through \(U:L\to R\) is the direct 4-coherence
\[
\begin{aligned}
&\bigl((l_0*_0U)*_1(a*_0s)\bigr);\theta_R
\\
&\hspace{12mm}\longrightarrow
\theta_L;(a*_0U)
\end{aligned}
\tag{12}
\]
on \(D^2(a)*_0D^3(U)\).

Using reverse coherences and their cancellation cells, (12) reduces the 2-coefficient to:

1. the point-supported 1-coefficient \(l_0\);
2. the dimension-1 path coefficient \(a*_0s\).

The second is handled by A. The right-hand version uses
\(D^3(U)*_0D^2(a)\).

### C. A point-supported 1-coefficient

This is the substantive local calculation.

Let \(l:x^-\to x^-\). Choose a point-context 2-cell
\[
\kappa:l\longrightarrow1_{x^-}.
\]

For a 2-cell \(T:p\to s\), first construct the inverse-free interchanger
\[
J_{\kappa,T}:
(l*_0T)\cdot(\kappa*_0s)
\longrightarrow
(\kappa*_0p)\cdot(1_{x^-}*_0T).
\tag{13}
\]
It is a direct coherence on \(D^2(\kappa)*_0D^2(T)\), with the point identification made only by substitution.

Its naturality is a direct 4-coherence on
\[
D^2(\kappa)*_0D^3(U):
\]
\[
\begin{aligned}
&\bigl((l*_0U)*_1(\kappa*_0s)\bigr);J_{\kappa,R}
\\
&\hspace{8mm}\longrightarrow
J_{\kappa,L};
\bigl((\kappa*_0p)*_1(1_{x^-}*_0U)\bigr).
\end{aligned}
\tag{14}
\]

Let \(\ell_p,\ell_s\) be the 2-unitors
\[
1_{x^-}*_0p\to p,\qquad1_{x^-}*_0s\to s.
\]
The 3-term
\[
\ell_T:
(1_{x^-}*_0T)\cdot\ell_s
\longrightarrow
\ell_p\cdot T
\tag{15}
\]
is a direct coherence on \(D^2(T)\); its naturality in \(U\) is a direct 4-coherence on \(D^3(U)\).

Put
\[
u=(\kappa*_0p)\cdot\ell_p,\qquad
d=(\kappa*_0s)\cdot\ell_s.
\]
Using associators, (13), and (15), form
\[
\chi_T:(l*_0T)\cdot d\longrightarrow u\cdot T.
\tag{16}
\]
Explicitly, if \(\mathfrak a\) is the vertical 3-associator, the five steps are
\[
\begin{aligned}
\chi_T={}&
\mathfrak a^{-}_{lT,\kappa s,\ell_s};
(J_{\kappa,T}\cdot\ell_s);
\mathfrak a_{\kappa p,1T,\ell_s};
\\
&((\kappa p)\cdot\ell_T);
\mathfrak a^{-}_{\kappa p,\ell_p,T}.
\end{aligned}
\]
Here only the abbreviations \(lT=l*_0T\), \(\kappa p=\kappa*_0p\), and similarly for the other dimension-0 composites have been used.

Choose a reverse path 2-cell
\[
\bar d:s\longrightarrow l*_0s
\]
and a path 3-cell
\[
\bar\epsilon_d:1_{l*_0s}\longrightarrow d\cdot\bar d.
\]
Then the following is a structural 3-term:
\[
\begin{aligned}
l*_0T
&\longrightarrow(l*_0T)\cdot1_{l*_0s}\\
&\longrightarrow(l*_0T)\cdot(d\cdot\bar d)\\
&\longrightarrow((l*_0T)\cdot d)\cdot\bar d\\
&\xrightarrow{\chi_T\cdot\bar d}
(u\cdot T)\cdot\bar d.
\end{aligned}
\tag{17}
\]

The first arrow is the inverse right unitor. The next two arrows are the whiskered \(\bar\epsilon_d\) and inverse associator.

All cancellation data in (17) depend only on \(p,s,l,\kappa\). They remain fixed when \(T\) changes through \(U\). Consequently its naturality follows by composing:

- (14);
- the naturality of (15);
- vertical associator naturality;
- the 4-interchanger (10) for \(\bar\epsilon_d\).

Finally, normalize \(u,\bar d\) to the chosen path comparisons. Their naturality is again (10). This yields the required comparison for the point 1-whisker.

The right-hand calculation replaces \(\kappa*_0p\) by \(p*_0\kappa\), uses right unitors, and has arity \(D^3(U)*_0D^2(\kappa)\).

Cases A–C exhaust the whiskering operations in \(\omega\), proving (9). All changes to parentheses are explicit associators; all inverse and cancellation terms are obtained on the stated pasting or path contexts.

## 1.6 Finish the normalization

Start with (8). Using (9) and the cancellation data for \(\delta_R\), compare it to
\[
(I_0;\delta_L);U_{e,h};(\bar\delta_R;I_1).
\tag{18}
\]
Both exterior 3-terms are structural.

By RC(3) in \(\Gamma_0\),
\[
I_0;\delta_L\longrightarrow\nu_t,
\qquad
\bar\delta_R;I_1\longrightarrow\bar\nu_{t'}
\]
have 4-fillers. Whiskering these fillers gives (4).

For parallel \(v,w:t\to t'\) with strict image \(\pi U\), their target normal form (3) is literally the same. Compose
\[
v\longrightarrow\mathcal N(t,t')
\]
with the reversed normalization of \(w\). Reversing these 4-comparisons does not reverse \(U\): reverse the coherence steps above \(U\), keeping \(U\) as their fixed 3-dimensional argument.

If the common strict image is an identity, both terms belong to \(\Gamma_0\), so (1) applies directly.

Therefore
\[
\boxed{\operatorname{RC}(3,\Gamma).}
\tag{19}
\]

For any 3-dimensional coherence \(c\) over the 2-disc, with any fixed lower lifts, define
\[
K(Q,B,\operatorname{Var}Q)
=
\operatorname{Fill}_\Gamma(a_c,b_c)
\]
using this construction. Their strict images agree by the reduction stated in §2.3 of the question.

This settles Question 1, including the unitor for arbitrary lower lifts.

# 2. Suspension descent for cylinders

The descent works for arbitrary CaTT contexts, not only pasting contexts. The only pasting-context requirement occurs at the arity of each coherence.

## 2.1 Suspension and the selected variables

Use the usual syntactic suspension:
\[
\Sigma\star=N\to S,\qquad
\Sigma(u\to_Av)=\Sigma u\to_{\Sigma A}\Sigma v,
\]
\[
\Sigma x=x,\qquad
\Sigma\operatorname{coh}_{P,B}[\gamma]
=
\operatorname{coh}_{\Sigma P,\Sigma B}[\Sigma\gamma].
\]
Contexts acquire the two new objects \(N,S\), and every old variable increases in dimension by one. This is the suspension meta-operation underlying the computadic suspension construction. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

Take
\[
Y'=\{\Sigma y:y\in Y\}.
\tag{20}
\]
The poles \(N,S\) are unselected. This set is up-closed.

For each original variable \(x\), the possible dimension-0 whiskering factor in \(a_{\Sigma x}\) or \(b_{\Sigma x}\) comes from a pole. It is therefore literally omitted. All remaining factors are the suspended original factors. With the standard suspension-compatible binary composites,
\[
a_{\Sigma x}=\Sigma a_x,\qquad
b_{\Sigma x}=\Sigma b_x.
\]
Hence, up to the fixed naming of variables,
\[
\boxed{
(\Sigma Q)\uparrow\Sigma Y
=
\Sigma(Q\uparrow Y).
}
\tag{21}
\]

It remains to decode arbitrary fillers in a suspended context.

## 2.2 Cut a coloured pasting context

Colour the 0-variables of a context by \(0,1\), nondecreasing along each generating 1-cell. A positive-dimensional term is **crossing** when its 0-source has colour \(0\) and its 0-target has colour \(1\).

Every positive-dimensional pasting context has a root decomposition
\[
P=\Sigma P_1\vee_0\cdots\vee_0\Sigma P_k.
\tag{22}
\]
Its 0-vertices form an ordered list. For a nonconstant nondecreasing colouring, exactly one adjacent pair changes from \(0\) to \(1\).

Let that pair belong to \(\Sigma P_j\). Define
\[
\operatorname{Cut}(P)=P_j.
\]
Thus the cut is a pasting context because it is the desuspension of one root column. It is not an arbitrary deletion of variables.

For dimension-specific boundaries, with \(\partial_m^\epsilon R=R\) when \(m\geq\dim R\),
\[
\operatorname{Cut}(\partial_m^\epsilon P)
=
\partial_{m-1}^\epsilon\operatorname{Cut}(P),
\qquad m\geq1.
\tag{23}
\]
This follows directly from (22), since taking such a boundary truncates every suspended root column at the corresponding dimension.

We also need locality:

> If both 0-boundaries of a typed term have colour \(i\), every variable in its typed support has colour pair \((i,i)\), or is a 0-variable of colour \(i\).

Prove this simultaneously with monotonicity of term boundaries by induction on dimension and syntax. In a coherence case, pull the colouring back along its substitution. Full endpoint support forces all relevant arity vertices to have the endpoint colour. For a boundary-full constructor of dimension at least \(2\), its top boundary includes every 0-variable of the arity. For a 1-dimensional composition, monotonicity along its path gives the same conclusion.

In particular, a term with equal endpoint colours cannot use a crossing variable.

## 2.3 The decoder, including dimension 1

For a coloured context \(\Delta\), define \(D\Delta\) by retaining precisely its crossing variables and lowering their dimensions by one.

On crossing types, set
\[
D(u\to_\star v)=\star
\]
when \(u,v\) are 0-terms, and otherwise set
\[
D(u\to_Av)=Du\to_{DA}Dv.
\tag{24}
\]
For a crossing variable, put \(Dx=x\).

Now let
\[
t=\operatorname{coh}_{P,B}[\gamma]
\]
be crossing. Colour \(P\) by pulling back the colouring along \(\gamma\), and write
\[
R=\operatorname{Cut}(P).
\]
The substitution \(D\gamma\) keeps the crossing arity variables and sends each one to the decoded argument.

There are two constructor clauses.

**If \(\dim t=1\):** \(P\) is a 1-pasting path with a unique crossing edge \(e\). Define
\[
\boxed{
D\operatorname{coh}_{P,B}[\gamma]
=
D(\gamma(e)).
}
\tag{25}
\]
A crossing 1-dimensional full-endpoint coherence over a point is impossible. Thus (25) covers every crossing 1-dimensional coherence.

**If \(\dim t\geq2\):** define
\[
\boxed{
D\operatorname{coh}_{P,B}[\gamma]
=
\operatorname{coh}_{R,DB}[D\gamma].
}
\tag{26}
\]

Clause (25) is necessary: replacing it by (26) would attempt to construct a coherence of type \(\star\).

## 2.4 Typing and fullness of the decoded coherence

Let \(X\) be the set of crossing variables of the ambient context. Simultaneous induction gives
\[
\operatorname{Var}(Dt:DA)
=
\operatorname{Var}(t:A)\cap X.
\tag{27}
\]

For a coherence, the decoded substitution retains exactly the crossing arity arguments. Every discarded argument has equal endpoint colours, so locality says that its support has empty intersection with \(X\). Taking unions of supports proves (27). In dimension 1, the retained arity has just the edge \(e\), so the same calculation proves the claim for (25).

Suppose the original constructor has dimension \(d\geq2\).

- If its endpoints are full in \(P\), equation (27) makes the decoded endpoints full in \(R\).
- If it is a composition, then \(\dim P=d\). Equations (23) and (27) identify the decoded endpoint supports with
  \[
  \operatorname{Var}(\partial_{d-2}^-R),
  \qquad
  \operatorname{Var}(\partial_{d-2}^+R).
  \]

There are two possibilities in the second case.

1. If \(\dim R=d-1\), this is the boundary-full condition for the decoded composition.
2. If \(\dim R\leq d-2\), both displayed boundaries equal \(R\). The decoded constructor instead satisfies the full-endpoint coherence condition.

The second possibility is essential: a deleted root column may have been higher-dimensional than the crossing column.

Thus (26) is always legal. This also proves that \(D\Delta\) is a well-formed context, including when the original declarations have composite boundaries.

## 2.5 Substitution and the retraction

For a colour-preserving substitution \(\theta\), induction gives literal equalities
\[
D(t[\theta])=(Dt)[D\theta],
\qquad
D(A[\theta])=(DA)[D\theta].
\tag{28}
\]
The pulled-back colouring of an arity is the same on both sides. In (25), both sides therefore select the same edge \(e\).

Colour the poles of \(\Sigma\Delta\) by \(0,1\). Every suspended variable is crossing, and \(\Sigma P\) has exactly one root column. Consequently,
\[
\boxed{
D(\Sigma\Delta)=\Delta,\qquad
D(\Sigma A)=A,\qquad
D(\Sigma t)=t.
}
\tag{29}
\]
These are syntactic equalities after fixing compatible names. A suspended coherence has dimension at least \(2\), so (26) reconstructs its original constructor exactly.

One should distinguish (29) from a stronger claim about arbitrary weak 0-whiskering. This decoder need not literally erase such a whisker: it may produce a unary disc coherence. That does not affect descent.

For strict images, define the corresponding strict cut by shifting positive composition indices down by one and retaining the unique crossing factor of a dimension-0 composite. Associativity, units, and interchange preserve this operation. Induction on terms gives
\[
\pi(Dt)=D_{\mathrm{str}}(\pi t),
\qquad
\pi(\Sigma t)=\Sigma_{\mathrm{str}}(\pi t).
\tag{30}
\]
Thus suspension and decoding preserve equal strict images.

## 2.6 Apply the decoder to an arbitrary filler

Put \(\Delta=Q\uparrow Y\). Given parallel \(r\)-terms \(t,t':A\) with
\[
\pi t=\pi t',
\]
their suspensions are parallel \((r+1)\)-terms with equal strict images.

Assume
\[
\operatorname{RC}(r+1,(\Sigma Q)\uparrow\Sigma Y).
\]
By (21), this supplies a term
\[
H:\Sigma t\longrightarrow_{\Sigma A}\Sigma t'
\]
in \(\Sigma\Delta\).

Its type is crossing, so the decoder applies regardless of its syntax. By (29),
\[
DH:t\longrightarrow_A t'.
\]

Therefore
\[
\boxed{
\operatorname{RC}(r+1,(\Sigma Q)\uparrow\Sigma Y)
\Longrightarrow
\operatorname{RC}(r,Q\uparrow Y).
}
\tag{31}
\]

Iterating,
\[
\operatorname{RC}(n,(\Sigma^{n-r}Q)\uparrow\Sigma^{n-r}Y)
\Longrightarrow
\operatorname{RC}(r,Q\uparrow Y).
\]
Hence RC(\(n\)) on **all** cylinders, including partial selections, implies RC(\(r\)) on all cylinders for every \(r\leq n\). Combined with the reduction in §2.3 of the question, it proves Conjecture N through dimension \(n\).

The unselected suspension poles are part of the statement. This argument does not replace the hypothesis by RC(\(n\)) only on fully selected cylinders.

# 3. What the horizontal factorization does establish

There is a useful correction to the possible ordering obstruction in Question 2: **a full chain cylinder has no independent orders of nonidentity 2-generators.**

Write its generators as
\[
v_i:x_i^-\to x_i^+,\qquad
a_i^\pm:x_{i-1}^\pm\to x_i^\pm,
\]
\[
F_i:a_i^-v_i\longrightarrow v_{i-1}a_i^+.
\]

For endpoints \(x_a^-\to x_b^+\), every strict 1-path is
\[
P_j^{a,b}
=
a_{a+1}^-\cdots a_j^-\,v_j\,
a_{j+1}^+\cdots a_b^+,
\qquad a\leq j\leq b.
\]
A generating rewrite changes \(P_i^{a,b}\) to \(P_{i-1}^{a,b}\). Therefore a nonidentity strict 2-cell has a forced word
\[
F_r,F_{r-1},\ldots,F_{s+1}.
\tag{32}
\]
Longer full chains produce longer forced words.

For an arity substitution with such a strict value, exactly one 0-column has nonidentity 2-image. Preceding columns are supported on a minus-row path; following columns are supported on a plus-row path. Retain those literal paths and the entire active column. This gives the exact frames
\[
P_{\mathrm{left}}*_0C_n*_0P_{\mathrm{right}},
\]
or
\[
P_{\mathrm{left}}*_0V(\mathbf k)*_0P_{\mathrm{right}}.
\tag{33}
\]

An assigned term spanning several exterior edges is lifted **as a whole** by renaming those edges. For example,
\[
b(h_1,h_2,h_3)
\]
is sent to the same expression \(b(\widehat h_1,\widehat h_2,\widehat h_3)\) in the retained path. The original arity variable is not split into three variables.

This factorization is literal and stable for the required evaluations that:

- preserve the distinct frame vertices;
- send every retained exterior edge to the same literal edge variable.

It is not a claim of invariance under arbitrary substitutions replacing those edges by composite paths.

For proper \(Y\), a frame with only one vertical chain can be insufficient. Take a two-edge chain and select only its arrows:
\[
Y=\{a_1,a_2\}.
\]
The cylinder is the pasting context \(D^2*_0D^2\), with independent 2-generators
\[
A_1:a_1^-\to a_1^+,\qquad
A_2:a_2^-\to a_2^+.
\]
The two routes
\[
(A_1*_0a_2^-)\cdot(a_1^+*_0A_2),
\]
and
\[
(a_1^-*_0A_2)\cdot(A_1*_0a_2^+)
\]
have the same strict image.

A factorization of this diagram through one \(C_n\) with only fixed 1-paths outside it cannot retain both independent 2-generators: whichever side is replaced by a 1-path would have to express one of \(A_1,A_2\) using only 1-variables. Its strict 2-image would then be an identity. Here both vertical chains must be retained.

This is a limitation of the proposed one-chain frame, not a counterexample to RC(3). The exchange itself is the direct 3-coherence over \(D^2*_0D^2\). A general normalization theorem for proper selections still needs the exchange/fusion argument.

## Scope

The constructions above establish:

- **Question 1:** RC(3) for the full 2-disc cylinder, and its 3-dimensional naturality instances for arbitrary fixed lower lifts.
- **Question 4:** suspension descent with \(Y'=\Sigma Y\), leaving the new poles unselected.
- **The literal factorization part of Question 2:** for full chain cylinders, with the precise fixed-edge substitution condition; also the failure of the single-chain frame for arbitrary proper selections.

They do not establish RC(3) on all cylinders, RC in all dimensions, or the 5-dimensional comparison required in Question 6.

The strict 2-cell classification and the displayed local interchanger, unit, and point-whisker boundary formulas were checked symbolically without associativity or unit identifications. The complete constructions are proofs on paper, not CaTT-kernel verifications.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level. It settles Q1 and Q4 and part of Q2.** RC(3) holds on the cylinder of the 2-disc, so K exists for every 3-dimensional coherence over the 2-disc for arbitrary lower lifts. Suspension descent RC(r+1, (ΣQ)↑ΣY) ⇒ RC(r, Q↑Y) holds with the poles unselected. Full chain cylinders have forced 2-words and literal frames. Q3, Q5, Q6 and the normaliser/fusion part of Q2 stay open.

Checked step by step.

**§1, the 2-disc cylinder.**
1. **Setup.** From §1.3 of the prompt, a_A = (A⁻ ∗₀ y↑) ∗₁ g↑ = c·G = L and b_A = f↑ ∗₁ (x↑ ∗₀ A⁺) = F·d = R, so U = A↑ : L → R as stated.
2. **§1.1, strict cells.** The 1-paths x⁻ → y⁺ are p, q, r, s, and the generating rewrites are c : p→q, F : p→r, G : q→s, d : r→s. With a and b, this gives exactly the eight nonidentity strict 2-cells. πL ≠ πR in the free strict ω-category.
3. **The only strict 3-cell is πU.** U can't be composed with itself, and it can't take a nonidentity whisker: nothing enters p, nothing leaves s, x⁻ is initial and y⁺ is terminal.
4. **U-count.** A 3-dimensional coherence over a 3-dimensional arity is always a composition, because its 2-dimensional endpoints can't be full. So each syntactic leaf contributes to the strict image without cancellation, and a term of image πU uses U exactly once.
5. **§1.2, RC(3, Γ₀).** The value-by-value restriction is the round-2 support argument (Lemma 36). The cases a, b, c and d are direct coherences, and F and G are squares.

   For L and R, the outer paths meet only at x⁻ and y⁺, so discarded columns are point-supported. The round-3 two-letter construction then applies with the letters c, G (respectively F, d) in forced order.

   I checked this transfer at the level of its inputs (point support, forced order, smaller cases available). I did not re-derive the round-3 induction for these letters.
6. **§1.4, sequentialization.** Both H and B_H are full in P and parallel, so (5) is a legal 4-coherence. The inserted 3-bridges live in P_{≤2} and cannot contain U after substitution. (6) and (7) are direct coherences on D³ ∗_k D³ and (D³ ∗₂ D³) ∗_k D². This yields the form I₀;ω(U);I₁ of (8).
7. **§1.5, whiskering normalization.**
   - Case A ((10)) is the interchanger on D³ ∗₁ D³.
   - Case B ((11), (12)) uses direct coherences on D²(a) ∗₀ D²(T) and D²(a) ∗₀ D³(U).
   - Case C: any 1-term into x⁻ is a point-supported loop l : x⁻ → x⁻, since no generator enters x⁻. I typed the five steps of χ_T in (16) one by one: inverse associator, J·ℓ_s, associator, (κp)·ℓ_T, inverse associator. They compose (l∗₀T)·d to u·T.
   - The cancellation data in (17) depend only on p, s, l and κ, so naturality follows from (14), the naturality of (15), and (10).
   - Whiskers by 3-terms are removed by (6). Since x⁻ is initial and y⁺ terminal, cases A–C exhaust ω.
8. **§1.6.** Combining (9) with RC(3, Γ₀) gives v → 𝒩(t, t′). The target normal form depends only on t and t′. Reversing the normaliser of w reverses only coherence steps, each of which has a reverse coherence or an RC(3, Γ₀) filler, and keeps U as a fixed argument. So RC(3, Γ) follows.

**§2, descent.**
1. **(21).** For x of dimension n in Q, the dimension-0 factor of a_{Σx} is the pole S↑ (respectively N↑ in b_{Σx}). The pole is unselected, so the factor is omitted. The remaining factors are the suspended factors of a_x, with ∗_k replaced by ∗_{k+1}, by induction on (Σw)↑ = Σ(w↑).

   For a selected 0-variable x, this gives (Σx)↑ : (Σx)⁻ → (Σx)⁺ = Σ(x↑ : x⁻ → x⁺). So (ΣQ)↑ΣY = Σ(Q↑Y).
2. **The decoder D (§2.2–2.5).** This is the cut translation already verified in `answered/cone-over-coherences-r2-2026-11-18.md` §2, now stated for arbitrary coloured contexts. Two points are new and both correct:
   - the dimension-1 clause (25), needed because (26) would produce a coherence of type ⋆;
   - the case dim R ≤ d − 2 in §2.4, where a decoded composition becomes a full-endpoint coherence.

   In ΣΔ the only 0-variables are the poles, so every non-crossing subterm is a point-supported loop at N or S and uses no crossing variable. D(Σt) = t holds because ΣP has a single root column.
3. **(31).** H : Σt → Σt′ has a crossing type, so DH : t → t′. Strict images are preserved by (30).

   The useful consequence: RC(n) on **all** cylinders, including partial selections with unselected poles, gives RC(r) on all cylinders for r ≤ n, hence Conjecture N through dimension n. RC(n) on fully selected cylinders alone is not enough.

**§3, chains.**
1. The strict 1-paths x_a⁻ → x_b⁺ are the P_j, and F_i sends P_i to P_{i−1}. So every nonidentity strict 2-cell has the forced word F_r … F_{s+1}, and the frames (33) are literal under the stated fixed-edge condition.
2. The proper selection Y = {a₁, a₂} is up-closed. Its cylinder is D² ∗₀ D² with A_i : a_i⁻ ⇒ a_i⁺, so a one-chain frame cannot hold both generators.

   This is not a counterexample to RC(3): the exchange is one direct coherence. It does show that Q2 for proper Y needs frames with several retained chains.

Follow-up prompt: `outbox/naturality-arbitrary-depth-r5.md` (round 5, unsent).
