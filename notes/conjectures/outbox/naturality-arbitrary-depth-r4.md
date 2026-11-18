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

## 3. What remains, and why

RC(3) fails for loopy contexts such as (x : ⋆, a : id_x → id_x), so a proof must use acyclicity. Rounds 2 and 3 handle cylinders in which every column carrying a 2-generator either spans the unique source and sink (point-supported discarded columns) or has exactly one fixed edge on one side. In longer cylinders a column can have nonidentity paths on both sides, several 2-generators can occur in more than one order, and for Q of dimension 2 the cylinder has 3-variables (e.g. A↑ for A : f ⇒ g), so parallel 3-terms need not have equal strict images automatically.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: RC(3) on the cylinder of the 2-disc.** Q = (x, y, f, g : x → y, A : f ⇒ g), Y = Var(Q). Q↑Y has the 2-variables f↑, g↑ and the 3-variable A↑. Prove that any two parallel 3-terms of Q↑Y with equal strict image are connected by a 4-term. (This gives K for every 3-dimensional coherence over the 2-disc, for instance the unitor `A ∗₁ id_g → A`, now for arbitrary lower lifts.)
2. **Horizontal words.** For the cylinder of a chain x₀ → x₁ → … → x_k (k ≥ 3), or of any 1-dimensional pasting context with Y a proper up-closed subset, does a column carrying a 2-generator factor literally through a retained pasting context `D¹(h₁) ∗₀ … ∗₀ D¹(h_i) ∗₀ C_n ∗₀ D¹(h_{i+1}) ∗₀ … ∗₀ D¹(h_j)` with each h sent to a fixed edge variable, stably under substitution? Does item 10's construction extend, including the case of several 2-generators in more than one order?
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
