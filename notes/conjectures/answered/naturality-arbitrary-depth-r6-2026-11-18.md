# Problem: naturality of CaTT coherences at depth ≥ 2, round 6

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first. Rounds 1–5 and their verified answers are archived in `answered/naturality-arbitrary-depth-2026-11-18.md` and `answered/naturality-arbitrary-depth-r2-2026-11-18.md` through `-r5-2026-11-18.md`; this prompt does not re-ask anything answered there.*

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
16. **The support lemma (from the cone problem, proved).** In every context, the generators used by the strict image of a term are exactly its dependency-closed support: `supp(π t) = supp(t)`. So a term whose strict image lies in a dependency-closed sub-context is literally a term of that sub-context. Source: `answered/cone-over-coherences-r3-2026-11-18.md`.
17. **RC(3) on every finite full chain cylinder (round 5, proved on paper).** Q = (x₀ → ⋯ → x_k), Y = Var(Q).
    - *Normal forms.* For a forced word F_r ⋯ F_{s+1} between 1-terms A and B, N_w(A, B) is the left-associated list κ(A, S_r), E_r, κ(T_r, S_{r−1}), E_{r−1}, …, E_{s+1}, κ(T_{s+1}, B). Here E_i = L_i⁻ ∗₀ (F_i ∗₀ R_i⁺) is a fixed raw letter, and κ is the fixed path comparison. A comparison is kept between every two letters, even when its endpoints are syntactically equal.
    - *Fold.* Multiplication μ contracts the one pair of path comparisons at the join. The 4-cells comparing contraction orders have three cases (same pair, disjoint pairs, overlapping pairs on one path), each a single coherence.
    - *Fixed whiskering.* d_W : WU · WV ⇒ W(U · V) and ρ_W : Wκ_p ⇒ κ_{Wp}. Raw-letter conversions are padded with path comparisons on P_ℓ ∗₀ D²(z) ∗₀ P_r and repaired on actual paths after substitution. When a marked letter is evaluated at a long word, every entry of the word is first made a separate variable of C_N.
    - *Normalisers and fusion.* ν_T = v_H[η] ; D_{B_H, η}, where v_H is one coherence on the retained frame and D is a finite fold. Fusion is by induction on the relative term. For every 3-term G : T ⇒ T′ there is Λ_G : G ; ν_{T′} ⇒ ν_T, using one full coherence Ξ_H per head. Right cancellation gives RC(3).
    - Source: `answered/naturality-arbitrary-depth-r5-2026-11-18.md`.
18. **Two proper selections with forced order (round 5, proved on paper).** On x → y → z, RC(3) holds for Y = {z, g} (G : g⁻ ∗₀ Z ⇒ g⁺) and for Y = {y, z, f, g} (G : g⁻ ∗₀ Z ⇒ Y ∗₀ g⁺ and then F : f⁻ ∗₀ Y ⇒ f⁺, with a path comparison kept between them). For Y = {x, f, g}, instead, F : f⁻ ⇒ X ∗₀ f⁺ and G : g⁻ ⇒ g⁺ act on disjoint parts of f⁻g⁻, and both orders occur.
19. **RC(3) on the cylinder of D² ∗₁ D² (round 5, proved on paper).** With U_A : c₀ · F₁ ⇛ F₀ · d₀ and U_B : c₁ · F₂ ⇛ F₁ · d₁:
    - The mixed strict 2-cells are the unique words c_i ⋯ c_{k−1} F_k d_k ⋯ d_{j−1}, and item 17 gives RC(3) on the 2-skeleton.
    - The nonidentity strict 3-cells are U_A, U_B, W_A = U_A ∗₁ d₁, W_B = c₀ ∗₁ U_B and W_B ∗₂ W_A, so a 3-term uses at most two generators, in a forced order.
    - Coefficients are normalised by RC(2) and interchange coherences on D³ ∗₁ D³. Anchors E_W = ν̄ ; W ; ν then compose literally, and the seam between W_B and W_A is an RC(3) comparison on the 2-skeleton.
20. **The same step is open in the Gray-contexts problem.** That problem proved RC(3) for the Gray cube's X-free loops using the same relative-fusion device. Its open step is also fusion when two 2-generators can be exchanged, with the 2 × 2 grid of lax squares as the smallest case. An acyclic generating 1-graph alone is not enough for RC(3): (x, a : 1_x → 1_x) is acyclic and fails. Cylinders Q↑Y are not affected, since they have no 2-generator from an identity to an identity.

## 3. What remains, and why

Every case settled so far has a forced order: each strict 2-cell between two given paths has one word, each word has one active column, and the strict 3-cells compose in at most one order. The next cases break this.

- In a proper selection such as Y = {x, f, g} on x → y → z, two letters act on disjoint parts of a path. A 2-term can carry them in two different columns, and two words related by exchange have the same strict image.
- In the full cylinder of D² ∗₀ D², the same happens already in the 2-skeleton. The two 3-generators can also be interchanged.
- 3-dimensional Q needs RC(4).

Item 14 reduces Conjecture N to RC(n) on all cylinders.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **Two independent letters (smallest exchange case).** Prove RC(3) for the cylinder of x → y → z with Y = {x, f, g}, where F : f⁻ ⇒ X ∗₀ f⁺ and G : g⁻ ⇒ g⁺ can be applied in either order. The new step is a normal form for an exchange class (for example, a fixed order of independent letters), an exchange coherence comparing the two orders, and fusion for 2-terms whose arity has two active columns.
2. **The horizontal two-disc.** Prove RC(3) on the full cylinder of Q = D² ∗₀ D². This combines question 1 in the 2-skeleton with two 3-generators that interchange.
3. **RC(3) on all cylinders.** Prove RC(3) for every Q↑Y with Q a pasting context of dimension ≤ 2, or for every finite Steiner loop-free context. Or give a counterexample.
4. **All dimensions.** Prove RC(n) on all cylinders Q↑Y, including partial selections. By item 14, this proves Conjecture N at every depth. A first target is RC(4) on the cylinder of the 3-disc, or on (ΣD²)↑ΣY.
5. **Global choice of K in dimension 3.** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with Y = Var(Q), compatible with substitution. Two choices of K for the same (Q, B, Y) are 4-cells; the minimal requirement is a **5-cell** between them (item 9).

## 5. What counts as a solution

Any of the following:
- explicit terms for question 1, 2 or 5;
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

**Question 1 admits a construction using \(F*_0G\) as the normal representative of the two-letter strict cell.** The two evaluation orders then become two ways of multiplying matrices of \(2\)-cells. Their comparison is built on ordinary pasting contexts.

The new ingredients are:

- a uniform normal form that retains horizontal identity \(2\)-factors;
- a path comparison that separates two displayed horizontal factors;
- a horizontal fold on \(C_3*_0C_3\);
- its compatibility with vertical folding, formed first on \(C_6*_0C_6\);
- a separate clause for a column that becomes point-supported under substitution.

Together with the results accepted in §2, these give RC(3) for the requested cylinder. I also give an explicit \(4\)-cell for the basic two-generator interchange in question 2, without claiming the full RC(3) statement there.

## 1. The strict values and the only new case

Write
\[
a=x^-,\qquad b=x^+,\qquad c=y,\qquad d=z.
\]
The generating \(1\)-cells are
\[
X:a\to b,\quad f^-:a\to c,\quad f^+:b\to c,\quad
g^-,g^+:c\to d,
\]
with
\[
F:f^-\Rightarrow X*_0f^+,\qquad
G:g^-\Rightarrow g^+.
\]

Set, as actual bracketed \(1\)-terms,
\[
f_0=f^-,
\qquad f_1=X*_0f^+,
\qquad g_0=g^-,
\qquad g_1=g^+,
\]
and
\[
p_{ij}=f_i*_0g_j.
\tag{1}
\]

The strict \(1\)-paths from \(a\) to \(d\) are exactly \(\pi p_{ij}\). A strict \(2\)-cell between them exists exactly when
\[
(i,j)\le(i',j')
\quad\Longleftrightarrow\quad
i\le i',\ j\le j',
\]
and is unique.

Indeed, \(F\) changes the first coordinate from \(0\) to \(1\), and \(G\) changes the second. Neither change can be repeated. The two orders for changing both coordinates are identified by strict interchange.

Denote the diagonal strict \(2\)-cell by
\[
H:\pi p_{00}\Rightarrow\pi p_{11}.
\]

The other nonidentity strict \(2\)-values are
\[
F,\quad G,\quad f^+*_0G,
\]
and
\[
F*_0g_0,\quad F*_0g_1,\quad f_0*_0G,\quad f_1*_0G.
\tag{2}
\]

Every value in (2) uses at most one of \(F,G\). By the support lemma in §2.16, terms with those values restrict literally to the corresponding one-generator subcontexts.

For the triangle \(F\), its two boundary paths \(f^-\) and \(Xf^+\) have only their endpoints in common. Thus the one-column construction applies exactly as in the square case. Its fixed-path extensions are covered by the finite-path construction. The \(G\)-subcontexts are genuine pastings, possibly with fixed path prefixes.

Consequently, **only the \(H\)-case needs a new proof**. A comparison whose strict \(2\)-boundary is not \(H\) can use the established one-column RC(3).

## 2. Uniform normal forms

Write
\[
\cdot=*_{1},\qquad ;=*_{2}.
\]
For parallel full terms on a pasting context \(P\), put
\[
\mathsf C_P(s,t)=\operatorname{coh}_{P,s\to t}[\mathrm{id}].
\]

Write \(\kappa(A,B)\) for the fixed path \(2\)-comparison on the common literal edge word of \(A,B\).

Define local raw \(2\)-terms
\[
a_{00}=1_{f_0},\qquad a_{11}=1_{f_1},\qquad a_{01}=F,
\]
\[
b_{00}=1_{g_0},\qquad b_{11}=1_{g_1},\qquad b_{01}=G.
\tag{3}
\]

For a transition
\[
\delta:(i,j)\longrightarrow(i',j'),
\]
define
\[
E_\delta=a_{ii'}*_0b_{jj'}.
\tag{4}
\]

In particular,
\[
E_H=F*_0G.
\]
For a one-letter transition, (4) retains an identity \(2\)-factor. For an identity transition,
\[
E_{\mathrm{id}_{ij}}=1_{f_i}*_01_{g_j}.
\]
These are not identified definitionally with mixed whiskerings or identities.

For actual \(1\)-terms \(A,B\) with the appropriate strict paths, put
\[
\boxed{
N_\delta(A,B)
=
\bigl(\kappa(A,p_{ij})\cdot E_\delta\bigr)
\cdot\kappa(p_{i'j'},B).
}
\tag{5}
\]

Use the corresponding local normal forms
\[
N^F_{ii'}(A,A')
=
\bigl(\kappa(A,f_i)\cdot a_{ii'}\bigr)
\cdot\kappa(f_{i'},A'),
\tag{6}
\]
and similarly \(N^G\).

For an empty transition these normal forms are path-only. Hence the old empty-word normal form \(\kappa(A,B)\) can be changed to (5) or (6) by a direct path \(3\)-coherence; comparisons between those changes are direct path \(4\)-coherences.

### The raw exchange

Let \(P=D^2(u)*_0D^2(v)\), with
\[
u:r_0\Rightarrow r_1,\qquad v:s_0\Rightarrow s_1.
\]
The two terms
\[
R_{GF}=(r_0*_0v)\cdot(u*_0s_1),
\]
\[
R_{FG}=(u*_0s_0)\cdot(r_1*_0v)
\]
are literally parallel and full in \(P\). Thus
\[
\chi=\mathsf C_P(R_{GF},R_{FG})
\tag{7}
\]
is the exchange \(3\)-cell.

Substitute
\[
r_0\mapsto f_0,\quad r_1\mapsto f_1,\quad
s_0\mapsto g_0,\quad s_1\mapsto g_1,\quad
u\mapsto F,\quad v\mapsto G.
\]
The whole composite \(X*_0f^+\) is assigned to \(r_1\).

Both orders also have direct \(3\)-comparisons
\[
\theta_{GF}:R_{GF}\Rightarrow u*_0v,
\qquad
\theta_{FG}:R_{FG}\Rightarrow u*_0v
\]
on \(P\). Their compatibility with exchange is the explicit \(4\)-term
\[
\mathsf C_P(\chi;\theta_{FG},\theta_{GF}).
\tag{8}
\]

The remaining issue is extending this comparison through arbitrary substituted arguments. The following folds do that.

## 3. Raw multiplication and the vertical fold

For \(i\le j\le k\), choose
\[
m^F_{ijk}:a_{ij}\cdot a_{jk}\Longrightarrow a_{ik}.
\tag{9}
\]
If \(F\) is present, this is a coherence on \(D^2(F)\). Otherwise it is a coherence on \(D^1(f_i)\). Define \(m^G\) similarly.

Let
\[
I_{\alpha,\alpha';\beta,\beta'}:
(\alpha*_0\beta)\cdot(\alpha' *_0\beta')
\Longrightarrow
(\alpha\cdot\alpha')*_0(\beta\cdot\beta')
\tag{10}
\]
be the direct \(3\)-coherence on \(C_2*_0C_2\).

For composable transitions \(\delta,\epsilon\), define
\[
\boxed{
M_{\delta,\epsilon}
=
I;\bigl(m^F*_0m^G\bigr):
E_\delta\cdot E_\epsilon
\Longrightarrow E_{\delta\epsilon}.
}
\tag{11}
\]

Here and below, juxtaposition of transition indices denotes diagrammatic composition.

### Raw \(4\)-laws

The associative comparison for (11), with the required associator inserted, is a direct \(4\)-coherence on the following minimal arity:

| Total transition | Arity |
|---|---|
| \(H\) | \(D^2(F)*_0D^2(G)\) |
| Only \(F\) | \(D^2(F)*_0D^1(g_j)\) |
| Only \(G\) | \(D^1(f_i)*_0D^2(G)\) |
| Identity | \(D^1(f_i)*_0D^1(g_j)\) |

For example, compare
\[
(M_{\delta,\epsilon}*_1E_\eta);
M_{\delta\epsilon,\eta}
\]
with
\[
\mathfrak a;
(E_\delta*_1M_{\epsilon,\eta});
M_{\delta,\epsilon\eta},
\tag{12}
\]
where
\[
\mathfrak a:
(E_\delta\cdot E_\epsilon)\cdot E_\eta
\Longrightarrow
E_\delta\cdot(E_\epsilon\cdot E_\eta).
\]

Both routes have the same literal source and target. If the total transition is \(H\), both are full on \(D^2(F)*_0D^2(G)\). The other rows are identical support checks.

These comparisons are formed with \(f_i,g_j\) as formal \(1\)-variables. Only afterward is \(f_1\) assigned \(X*_0f^+\).

### Multiplication of padded normal forms

Construct
\[
\mu_{\delta,\epsilon}:
N_\delta(A,B)\cdot N_\epsilon(B,C)
\Longrightarrow
N_{\delta\epsilon}(A,C)
\tag{13}
\]
by this fixed procedure:

1. Reassociate the two three-entry lists.
2. Contract the middle pair
   \[
   \kappa(p,B)\cdot\kappa(B,p)
   \Longrightarrow\kappa(p,p)
   \]
   by the path multiplication.
3. Use a path \(3\)-coherence
   \[
   \kappa(p,p)\Longrightarrow1_p.
   \]
4. Remove that identity by specified unit \(3\)-coherences.
5. Apply \(M_{\delta,\epsilon}\) to the two central raw terms.
6. Restore the association in (5).

The \(4\)-laws for (13) use the already established path-contraction comparisons, unit and reassociation naturality on vertical pastings, and the raw comparisons (12).

An arbitrary intermediate \(1\)-term \(B\) is removed by path multiplication. It is never assumed to split at \(y\).

## 4. Separating path comparisons at a displayed cut

For actual paths \(u,v\), suppose
\[
a,a'\text{ have path }u,\qquad b,b'\text{ have path }v.
\]
Define
\[
\boxed{
\zeta:
\kappa(a*_0b,a' *_0b')
\Longrightarrow
\kappa(a,a')*_0\kappa(b,b').
}
\tag{14}
\]
This is a direct \(3\)-coherence on the actual concatenated path \(uv\).

The endpoints in (14) must have the displayed binary form. The construction does not split an arbitrary \(1\)-term.

The essential \(4\)-compatibility compares
\[
(\zeta^{-1}_{01}\cdot\zeta^{-1}_{12});m_{uv}
\tag{15}
\]
with
\[
I;(m_u*_0m_v);\zeta^{-1}_{02}.
\tag{16}
\]
Their common source is
\[
\bigl(\kappa(a_0,a_1)*_0\kappa(b_0,b_1)\bigr)
\cdot
\bigl(\kappa(a_1,a_2)*_0\kappa(b_1,b_2)\bigr),
\]
and their common target is
\[
\kappa(a_0*_0b_0,a_2*_0b_2).
\]

All terms in (15)–(16) are path-only. Their comparison is therefore one direct \(4\)-coherence on the actual path \(uv\). The unit variants, including comparison of \(1_a*_01_b\) with \(1_{a*_0b}\), are formed on that path as well.

## 5. The new horizontal fold

For two composable three-entry lists
\[
L=\operatorname{LF}[L_1,L_2,L_3],
\qquad
R=\operatorname{LF}[R_1,R_2,R_3],
\]
let
\[
Z_3:
L*_0R
\Longrightarrow
\operatorname{LF}
[L_1*_0R_1,L_2*_0R_2,L_3*_0R_3]
\tag{17}
\]
be the direct \(3\)-coherence on \(C_3*_0C_3\).

Evaluate its columns at the local normal forms (6). The middle pair is exactly \(E_\delta\). Apply \(\zeta^{-1}\) to the first and last pairs. This defines
\[
\boxed{
\psi:
N^F_{ii'}(A,A')*_0N^G_{jj'}(B,B')
\Longrightarrow
N_\delta(A*_0B,A' *_0B').
}
\tag{18}
\]

The six entries are independent \(2\)-variables when (17) is formed. Their path-only status is used only after evaluation.

Identity \(2\)-factors remain explicit, so (18) includes one-letter and empty transitions.

### 5.1 The horizontal–vertical \(4\)-cell

Let \(L_1,L_2\) be composable local left normal forms and \(R_1,R_2\) composable local right normal forms. The required comparison is
\[
\boxed{
(\psi_1*_1\psi_2);\mu
\Longrightarrow_4
I(L_1,L_2;R_1,R_2);
(\mu^F*_0\mu^G);
\psi.
}
\tag{19}
\]

Both routes start at
\[
(L_1*_0R_1)\cdot(L_2*_0R_2)
\]
and end at the same literal normal form.

Here is a construction of (19).

#### First: align the pure interchange recipes

Write the concatenated columns as six independent entries
\[
l_1,\ldots,l_6,\qquad r_1,\ldots,r_6.
\]

On \(C_6*_0C_6\), compare these two \(3\)-routes:

- apply \(Z_3\) to each three-entry block and reassociate the resulting two lists;
- apply \(I\) to the two blocks, reassociate each column to six entries, and apply \(Z_6\).

Both end at
\[
\operatorname{LF}[l_1*_0r_1,\ldots,l_6*_0r_6].
\]
Both have every marked \(2\)-variable in their free-variable sets. Their comparison is
\[
\mathsf C_{C_6*_0C_6}(\text{first route},\text{second route}).
\tag{20}
\]

#### Second: group the middle path pairs

After evaluation, the middle pair in each column consists of its outgoing and incoming path comparisons. Group each such pair as one \(2\)-argument.

Moving its \(3\)-contraction through the zip uses top-argument naturality on
\[
V_5(0,0,1,0,0)*_0V_5(0,0,1,0,0).
\tag{21}
\]

These are naturalities in top-dimensional \(2\)-arguments of \(3\)-terms, hence within the already established depth-\(\le1\) case. For the explicit word recipes, they can equivalently be formed as direct \(4\)-coherences on these duplicated pastings. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

Grouping precedes the substitution into (21). Thus a composite path comparison is assigned as a whole \(2\)-argument.

#### Third: compare the middle path operations

The global route contracts
\[
\kappa(p,B_L*_0B_R)\cdot\kappa(B_L*_0B_R,p)
\]
to \(1_p\).

The columnwise route first interchanges the two pairs, contracts them separately, and then compares
\[
1_{f_i}*_01_{g_j}
\]
with \(1_p\).

These are precisely the path-only routes (15)–(16), followed by their unit comparisons. Use their direct actual-path \(4\)-coherence.

The middle term here is literally \(B_L*_0B_R\), because it was produced by (18). No arbitrary \(1\)-term is being split.

#### Fourth: compare the raw multiplication

After the path operations, the central comparison is between raw unit/interchange recipes for
\[
E_\delta\cdot E_\epsilon\Longrightarrow E_{\delta\epsilon}.
\]
Use the appropriate minimal pasting from the table in §3.

Finally, move the two exterior path repairs past these central operations using vertical pastings such as
\[
V_5(1,0,1,0,1).
\]

This completes (19).

In this construction, \(\zeta\) is kept as a whole path-only comparison. It is not treated as a generic \(3\)-variable while simultaneously exposing its horizontal target factors. Only componentwise repairs are moved through the horizontal interchanger; the remaining comparisons are made on actual paths.

### 5.2 Arbitrarily long retained columns

Although the actual state set has only two coordinates taking values \(0,1\), a retained arity may have arbitrarily many slots.

On a reference frame \(C_m*_0C_n\), use
\[
a_{ii'}=\operatorname{LF}[z_{i+1},\ldots,z_{i'}],
\qquad
b_{jj'}=\operatorname{LF}[w_{j+1},\ldots,w_{j'}],
\tag{22}
\]
with identities for empty intervals.

Local multiplication is the fixed concatenation/reassociation \(3\)-term on the corresponding vertical chain. Equations (10), (11), (17), and (19) apply with these whole column words as arguments.

Comparing two block decompositions is done on the expanded genuine pasting
\[
C_M*_0C_N,
\]
before evaluation. Every expanded slot is retained.

After evaluation, the required comparisons are exactly:

- vertical-fold associativity and units;
- (19);
- top-argument naturality;
- the actual-path laws (15)–(16).

This includes a marked slot assigned a long word. It does not require normalizing a newly assembled composite recursively.

## 6. Retained heads and the necessary degeneration clause

For the strict value \(H\), the two boundary paths are
\[
f^-g^-,
\qquad Xf^+g^+.
\]
Their common vertices are exactly
\[
a,\ c,\ d.
\tag{23}
\]

Every original \(0\)-cut of an evaluated pasting must be assigned a common vertex of its two boundary paths. Hence a head with value \(H\) has one of these retained forms:

\[
C_n
\qquad\text{or}\qquad
C_m*_0C_n,
\tag{24}
\]
and in dimension \(3\),
\[
V_n(\mathbf k)
\qquad\text{or}\qquad
V_m(\mathbf k)*_0V_n(\mathbf l).
\tag{25}
\]

In the two-column case the nondegenerate cut is \(c=y\). The left column has value \(F\), the right column value \(G\). Other columns are point-supported.

The literal factorization follows from §2.12 and §2.16:

- copy every variable in each active original column;
- replace an inactive column by the literal lift of its assigned terms to their path context;
- retain every slot in a surviving active column, even if that individual slot evaluates to a path-only term.

This gives a literal equality of substitutions
\[
\gamma=\kappa[\eta].
\tag{26}
\]

There is no literal refinement that splits an arbitrary merged slot of value \(H\) into an \(F\)-slot and a \(G\)-slot. Such a slot is left intact until its recursive normalizer has been applied.

### 6.1 A column may disappear

Unlike the one-column case, one active column can become inactive while the total value remains nonempty.

If the resulting value is not \(H\), the support lemma restricts the comparison to an already settled one-generator subcontext.

If the result remains \(H\), the cut in (24) can be assigned only \(a,c,d\):

- at \(c\), both columns remain active and (18)–(19) apply;
- at \(a\) or \(d\), one column is point-supported.

The point-supported column must be partially evaluated literally before forming the common reduced-frame comparison. A direct coherence on the unreduced frame would have the wrong support if one route had already omitted that column.

### 6.2 Explicit absorption of a point-supported column

This case does not require RC(3) for \(H\).

Suppose
\[
q:\ell_0\Rightarrow\ell_1
\]
is a \(2\)-term supported at the source point of a marked \(2\)-variable
\[
z:s\Rightarrow t.
\]
On \(D^2(z)\), form
\[
\boxed{
B_q(z):
q*_0z
\Longrightarrow
\bigl(\kappa(\ell_0*_0s,s)\cdot z\bigr)
\cdot\kappa(t,\ell_1*_0t).
}
\tag{27}
\]

Here \(q,\ell_0,\ell_1\) are literal terms on the source point. Therefore both endpoints of (27) are terms on \(D^2(z)\), and both are full there. Take their direct \(3\)-coherence.

After assigning \(z\) an actual term, repair the two evaluated path comparisons to the fixed comparisons on the expanded actual paths. The right-point version is analogous. A point-supported \(1\)-whisker is handled by the same construction with its mixed composite.

The required laws are formed before evaluating \(z\):

- naturality in \(z\) on \(D^3\);
- comparison with a vertical word on \(C_N\), with every word entry kept independent;
- comparisons between point-supported coefficients on that point, then inserted beside the marked word.

Only afterward are the actual-path repairs applied.

In particular, if \(z\) is assigned a whole \(H\)-term, it remains one marked argument during this comparison. There is no appeal to RC(3) for its evaluated value.

Allow \(C_0=D^1\) in the relative frames. A zero-slot column assigned a point-supported \(1\)-loop is covered by this same clause.

## 7. Normalizers and fusion

For values other than \(H\), use the established one-column normalizers, transported to conventions (5)–(6).

For a \(2\)-term \(T\) of value \(H\), use (26) to write it exactly as
\[
T=H_0[\eta]
\]
on one of the retained pastings (24).

Choose its reference expression \(B_{H_0}\):

- for \(C_n\), the vertical word in all retained \(2\)-variables;
- for \(C_m*_0C_n\), the horizontal product of the two vertical words;
- in both cases, outer path comparisons matching the exact \(1\)-boundaries of \(H_0\).

Both \(H_0\) and \(B_{H_0}\) are full in the retained pasting. Define
\[
v_{H_0}=\mathsf C_R(H_0,B_{H_0}).
\]

The evaluator has these clauses:

\[
\begin{array}{c|l}
\text{Reference expression} & \text{Evaluation comparison}\\ \hline
z & \nu_{\eta z}\\
K\text{ path-only} & \text{direct actual-path normalizer}\\
U\cdot V & (D_U*_1D_V);\mu\\
U*_0V\text{ at the nondegenerate cut} & (D_U*_0D_V);\psi\\
\text{point-supported column} & \text{the construction }B_q\text{ and its path repairs}\\
\text{fixed path whiskering} & \text{the established fixed-path comparison}.
\end{array}
\tag{28}
\]

Put
\[
\boxed{
\nu_T=v_{H_0}[\eta];D_{B_{H_0},\eta}.
}
\tag{29}
\]

The only recursive normalizer calls in (28) are on the proper original \(2\)-arguments assigned to the retained slots. Evaluation of a reference word is a finite fold.

### Fusion

Define relative normalizers on the retained pastings using the arbitrary finite reference grids (22). Then construct
\[
\boxed{
\mathcal F_{u,\sigma}:
\nu_{u[\sigma]}
\Longrightarrow_4
\lambda_u[\sigma];D_{B_u,\sigma}.
}
\tag{30}
\]

The induction is on the relative term \(u\).

For a nonvariable head, apply the induction hypotheses to its proper arguments. The remaining comparisons are exhausted by the expression grammar (28):

- repeated vertical folds use the laws of \(\mu\);
- horizontal folding followed by vertical folding uses (19);
- changes in marked \(2\)-arguments use top-argument naturality;
- path comparisons use (15)–(16);
- fixed paths use the established laws;
- a vanished column uses the explicit point-absorption construction (27).

If the evaluated value is a one-letter value, the established RC(3) in its support subcontext also supplies the comparison directly.

When a column disappears but the total value remains \(H\), partially evaluate that point column first. Compare the resulting head recipes on the surviving \(C_n\), with all surviving marked slots still independent. The reference-word change is the explicit point-absorption recipe, not an arbitrary new \(3\)-coherence whose fusion would remain to be proved.

For the variable case, a relative variable may be assigned an arbitrary \(H\)-term \(Z\). Use the generic padded-disc naturality on
\[
D^3(h:Z\Rightarrow N_H),
\qquad h\mapsto\nu_Z.
\]
Move the padding insertion across \(\nu_Z\), then use the three-entry word-unit calculation. This uses the already constructed \(\nu_Z\); it does not call the normalizer on \(N_H\).

Thus (30) is well founded.

## 8. The \(3\)-term induction

For every \(3\)-term \(J:T\Rightarrow T'\) with strict \(2\)-boundary \(H\), construct
\[
\Lambda_J:
J;\nu_{T'}\Longrightarrow_4\nu_T.
\tag{31}
\]

For a head on a retained \(2\)-pasting \(R\), the relative boundary normalizers end at the same reference normal form. Hence
\[
\mathsf C_R
\bigl(H_0;\lambda_{\tau H_0},\lambda_{\sigma H_0}\bigr)
\tag{32}
\]
is a full \(4\)-coherence.

For a head on a retained \(3\)-pasting from (25), let \(\mathcal W\) update every retained \(3\)-link in the reference expression. In two columns, form the two column actions and then their horizontal composite. Slots without a \(3\)-link contribute their identity \(3\)-terms.

Every retained \(3\)-variable belongs to the support of \(\mathcal W\). Therefore
\[
\mathsf C_R
\bigl(
H_0;\lambda_{\tau H_0},
\lambda_{\sigma H_0};\mathcal W
\bigr)
\tag{33}
\]
is full.

After evaluation, move the final fold backward through \(\mathcal W\):

- vertical positions use the \(\mu\)-laws;
- horizontal positions use (19) and top-argument naturality of \(\psi\);
- collapsed columns use (27);
- each marked \(3\)-argument uses its proper-argument \(\Lambda\).

Every proper argument of a split head at \(y\) is in an already settled one-letter case. A proper argument of a merged head can have value \(H\), but is smaller in the syntax.

Together with (30), this constructs (31) for every \(3\)-term.

### The requested \(4\)-term

Let
\[
\alpha,\beta:T\Rightarrow T'
\]
be parallel \(3\)-terms. In the \(H\)-case, form
\[
\Lambda_\alpha *_3\overline{\Lambda_\beta}:
\alpha;\nu_{T'}
\Longrightarrow
\beta;\nu_{T'}.
\]
Right-cancel the invertible normalizer \(\nu_{T'}\), using the same explicit cancellation construction as in the earlier rounds.

Thus
\[
\boxed{
\operatorname{Fill}(\alpha,\beta)
=
\operatorname{Cancel}_{\nu_{T'}}
\bigl(\Lambda_\alpha *_3\overline{\Lambda_\beta}\bigr)
:
\alpha\Longrightarrow\beta.
}
\tag{34}
\]

The other strict \(2\)-boundary cases were settled in §1. Hence
\[
\boxed{
\mathrm{RC}(3)_{\,
(x\to y\to z)\uparrow\{x,f,g\}}.
}
\]

In this \(2\)-dimensional context, every strict \(3\)-cell is an identity, so the construction connects every pair of parallel \(3\)-terms.

For a \(3\)-dimensional coherence \(c\) over this chain and selection, the requested naturality term is the instance
\[
K(Q,B,Y)=\operatorname{Fill}(a_c,b_c),
\]
for any fixed lower lifts.

## 9. An explicit interchange \(4\)-cell for question 2

The horizontal two-disc cylinder has one useful new comparison that can be constructed independently of its full RC(3) theorem.

Use
\[
A:f_0\Rightarrow f_1,\qquad B:g_0\Rightarrow g_1,
\]
and their cylinder generators \(U_A,U_B\). Set
\[
V=f_0^-*_0U_B,
\qquad
U=U_A*_0g_1^+.
\]

Their \(1\)-boundaries at the intended interface are
\[
\partial_1^+V=f_0^-*_0(Y*_0g_1^+),
\]
\[
\partial_1^-U=(f_0^-*_0Y)*_0g_1^+.
\]
Choose the path \(2\)-coherence
\[
K:
f_0^-*_0(Y*_0g_1^+)
\Rightarrow
(f_0^-*_0Y)*_0g_1^+.
\tag{35}
\]

On the genuine pasting
\[
P=D^3(v)*_1D^2(k)*_1D^3(u),
\]
define
\[
R_1=
\bigl((v*_1k)*_1\sigma u\bigr);
\bigl((\tau v*_1k)*_1u\bigr),
\]
\[
R_2=
\bigl((\sigma v*_1k)*_1u\bigr);
\bigl((v*_1k)*_1\tau u\bigr).
\]
Both have exact source
\[
(\sigma v\cdot k)\cdot\sigma u
\]
and exact target
\[
(\tau v\cdot k)\cdot\tau u.
\]
Both are full in \(P\). Therefore
\[
\boxed{
\mathsf C_P(R_1,R_2)
[v\mapsto V,\ k\mapsto K,\ u\mapsto U]
}
\tag{36}
\]
compares the \(U_B\)-then-\(U_A\) and \(U_A\)-then-\(U_B\) routes.

The seam \(K\) is part of the term. Omitting it would make the raw composition ill typed.

Equation (36) supplies this particular generator-interchange comparison. Full RC(3) for the horizontal two-disc cylinder still requires normalization and fusion for all exchange classes in its \(2\)-skeleton.

## What this settles

- **Question 1 is settled:** RC(3) holds for the specified proper-selection cylinder.
- The new two-column construction is the combination of \(M\), \(\zeta\), \(\psi\), the \(4\)-cell (19), and the point-column clause (27).
- Equation (36) supplies a concrete \(4\)-term needed for question 2.
- Questions 2–5 in their full generality are not proved here. In particular, the construction does not supply the \(5\)-cell comparison between choices of \(K\).

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level, with the same caveat as rounds 3–5 (the fusion case list was checked, not every 4-cell written out).**
- **Settled:** Question 1. RC(3) holds for the cylinder (x → y → z)↑{x, f, g}. So K(Q, B, Y) exists for every 3-dimensional coherence over x → y → z with Y = {x, f, g}, for any lower lifts. This is the first case with two independent letters (exchange).
- **New ingredient:** the normal form uses the horizontal composite E_H = F ∗₀ G of the two letters, keeping horizontal identity factors, so the two evaluation orders become two multiplications of a 2 × 2 "matrix" of 2-cells. The new constructors are M (11), ζ (14), the horizontal fold ψ (18), the horizontal–vertical 4-cell (19) and the point-column clause B_q (27).
- **Partial for Question 2:** an explicit 4-term (36) comparing the two orders of the cylinder generators U_A, U_B on the horizontal two-disc, with the seam K.
- **Open:** Questions 2 (full RC(3) for D² ∗₀ D²), 3, 4, 5.

Checked step by step:

1. **The cylinder.** Y = {x, f, g} is up-closed (f's type contains x). By §1.3 of the prompt, τf = y is unselected, so a_f = f⁻ and F : f⁻ ⇒ X ∗₀ f⁺; g's endpoints are unselected, so G : g⁻ ⇒ g⁺. This matches §1.
2. **Strict cells.** The paths a → d are p_ij = f_i g_j; F changes the first index, G the second, neither can repeat, and the two orders of doing both are equal by strict interchange. So the strict 2-cells between them form the product order on {0,1}², and the remaining values (2) each use at most one of F, G.
3. **One-letter values.** By the support lemma these restrict to one-generator subcontexts. The F-triangle (a, b, c, X, f⁻, f⁺, F) has a unique source a and sink c and the two boundary paths share only endpoints, so the lax-square method applies; with a fixed edge g_j after it, the round-3 fixed-edge factorisation applies. The G-subcontexts with a fixed prefix f_0 or f_1 = X f⁺ are pasting contexts, so parallel full terms are joined by one coherence.
4. **Raw exchange (7)–(8).** R_GF and R_FG are full and parallel in D²(u) ∗₀ D²(v); θ_GF, θ_FG and the compatibility (8) are coherences there. The substitution assigns the composite X ∗₀ f⁺ to r_1, which is allowed.
5. **Multiplication and its laws (§3).** I is a coherence over C_2 ∗₀ C_2; M = I ; (m^F ∗₀ m^G) has the stated type for all transitions, including those with identity factors. The 4-laws are taken over the minimal arities of the table with f_i, g_j formal before substitution; I checked the support claim for each row. μ never splits an arbitrary intermediate 1-term at y; it contracts through path multiplication.
6. **ζ and (15)–(16).** ζ is a path-only coherence on the concatenated path, and its endpoints have the displayed binary form, so no arbitrary 1-term is split. (15) and (16) share source and target and are path-only, so one coherence on the actual path compares them.
7. **Horizontal fold and (19).** Z₃ is a coherence over C_3 ∗₀ C_3 with six independent 2-variables. The four steps of (19) are, in order, a full coherence over C_6 ∗₀ C_6, top-argument naturality in 2-arguments of 3-terms (depth 1), the path-only comparison (15)–(16), and a raw comparison over the table's minimal arity. Each step uses only constructions that are coherences over pasting contexts or depth-1 naturality.
8. **Retained heads (§6).** The common vertices of f⁻g⁻ and X f⁺ g⁺ are a, c, d, and every 0-cut of a head with value H must go to a common vertex, so the retained forms are C_n or C_m ∗₀ C_n (and V_n(k), V_m(k) ∗₀ V_n(l) in dimension 3). The degeneration clause is necessary and correctly handled: when one column becomes point-supported at a or d, (27) absorbs it by a coherence over D²(z) formed before z is evaluated, so no appeal to RC(3) for H is made.
9. **Fusion and the 3-term induction (§7–8).** The recursion in (28)–(30) calls normalisers only on proper original 2-arguments, and the variable case uses padded-disc naturality on D³ with the already constructed ν_Z. (32) and (33) are full coherences over the retained pasting (in (33) every retained 3-variable is in the support of 𝒲). Cancellation of the invertible ν_{T′} gives (34).
10. **(36).** P = D³(v) ∗₁ D²(k) ∗₁ D³(u) is a pasting context; R_1, R_2 are full with the stated source and target. With v ↦ f₀⁻ ∗₀ U_B and u ↦ U_A ∗₀ g₁⁺, the 1-boundaries are f₀⁻ ∗₀ (Y ∗₀ g₁⁺) and (f₀⁻ ∗₀ Y) ∗₀ g₁⁺, so the seam K is needed and has the right type.

**Relation to the internal attempt.** The project's internal sketch for this case (`relative-coherence.md` §7.6, cut vertex y, horizontal normal forms N₁ ∗₀ N₂, machine-checked constructors in `WedgeRC3`) used the same horizontal normal form. The response supplies the missing fusion, the degeneration clause, and the compatibility (19).

Follow-up prompt: `outbox/naturality-arbitrary-depth-r7.md` (round 7, unsent).
