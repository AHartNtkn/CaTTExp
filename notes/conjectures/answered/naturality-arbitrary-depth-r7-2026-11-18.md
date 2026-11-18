# Problem: naturality of CaTT coherences at depth ≥ 2, round 7

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Everything under "What is known" is proved and is not re-asked. Questions are in §4, smallest first.*

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
5. **Explicit 3-dimensional instances**.
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
8. **RC(3) for the lax square S, all cases.** Any two parallel 3-terms of S are connected by a 4-term, so K(Q, B, Var Q) exists for every 3-dimensional coherence over the single arrow. The method:
   - *Active-column factorisation.* For a 2-term T = coh_{P,A}[γ] with π(T) = F, exactly one 0-column of the arity P carries F, and it spans x⁻ → y⁺; every other column sits at the point x⁻ or y⁺ (S has no directed loops there), so it factors literally through a point context. Hence γ = δ[η] with δ landing in a vertical chain C_k, and the factorised constructor H = coh_{P,A}[δ] is literally unchanged by any substitution C_n → S sending the full word to F.
   - *Normalisers* ν_T : T → N_F(σT, τT) = (κ_p(σT, p) · F) · κ_q(q, τT), defined by the factorisation and a fixed vertical fold, with associativity/unit/mixed 4-laws given by coherences on path contexts and small vertical pasting contexts (e.g. V(1,0,1) for the interchange of two path contractions around F).
   - *Evaluation fusion:* ν_{u[σ]} is 4-connected to (relative normaliser of u)[σ] followed by the fold; then every 3-term G with F-boundary gets Λ_G : G ; ν_{T′} → ν_T by induction on its syntax (2- and 3-dimensional arities, the latter via the 3-chains of the retained column V(k₁,…,k_m)), and right cancellation of the invertible ν gives the filler.
   - *Where it uses the square:* x⁻ is the unique source and y⁺ the unique sink, so discarded columns are point-supported. In a general cylinder Q↑Y, discarded columns can carry nonidentity paths, and literal stability fails.
9. **Dimension of the global-choice question.** A K for an n-dimensional coherence is an (n+1)-cell; comparing two choices of K is an (n+2)-cell.
10. **RC(3) on the cylinder of a composable pair.** Q = (x, y, z, f : x → y, g : y → z), Y = Var(Q). The strict 2-cells are the identities on paths, F = F_f, G = F_g, L = f⁻ ∗₀ G, R = F ∗₀ g⁺ and H = L ∗₁ R. The method:
    - *Fixed-edge extension.* A column carrying F (or G) that does not span the unique source and sink factors literally through a retained pasting context `C_n ∗₀ D¹(h)` or `D¹(h) ∗₀ C_n` (and their 3-dimensional versions), where every substitution sending the full word to the 2-cell sends h to the **same edge variable**. This replaces point support.
    - *New constructors.* Fixed whiskering d_h, its associativity, path comparisons after whiskering, whiskering of normal forms, and a compatibility cell φ^h with the vertical fold, all coherences over pasting contexts.
    - *Normalisers and fusion* as in item 8, with the evaluation fold kept separate from the vertical fold.
    - *The two-generator case H.* Discarded columns are point-supported again (H spans x⁻ → z⁺), and L and R occur in a forced order, so the vertical fold needs one additional multiplication case.
    - So K(Q, B, Var Q) exists for every 3-dimensional coherence over the pair, for any fixed lower lifts.
    - It uses three facts that are not known for general cylinders: the fixed-edge factorisations are literal, the H case is point-supported, and the 2-generators of H have a forced order.
11. **A dimension-lowering translation.** For join contexts `Cone(Q; c)` (Q a pasting context, with an apex c and cone cells p_q), there is a syntactic *cut translation* D: colour the 0-variables 0/1, nondecreasing along generating 1-cells; D deletes same-side variables and lowers each crossing term by one dimension, decoding a coherence over its unique crossing root branch. It satisfies D(Σt) ≡ t, D(u ∗_k v) ≡ D(u) ∗_{k−1} D(v), D(e ∗₀ u) ≡ D(u) and D(t[θ]) ≡ D(t)[D(θ)], and with a raising substitution it gives `RC(r+1, Cone(ΣQ; d)) ⇒ RC(r, Cone(Q; c))`.
12. **Literal inactive-column factorisation.** In every context Γ of dimension ≤ 2 with an acyclic graph of generating 1-cells (for example Q↑Y for 1-dimensional Q), an arity column none of whose 2-variables receives a term containing a 2-variable lifts literally to the path context of its common strict path (the path labelling is injective by acyclicity). Replacing such columns gives a reduced pasting context R_σ with σ = κ_σ[δ_σ], comparison terms coh_{P,A}[σ] → coh_{R_σ,A[κ_σ]}[δ_σ], and refinement substitutions λ_{σ,ρ} that are functorial under further substitution, with coherence cells between iterated reductions. A coherence 4-term also distributes a fixed whisker across a vertical composite of 3-cells. The open part is the treatment of active columns, whose 2-variables carry arbitrary composites.

13. **RC(3) on the cylinder of the 2-disc.** Q = (x, y, f, g : x → y, A : f ⇒ g), Y = Var(Q).
    - Write X = x↑, Y = y↑, F = f↑, G = g↑, c = A⁻ ∗₀ Y, d = X ∗₀ A⁺, L = c ∗₁ G and R = F ∗₁ d, so that U = A↑ : L → R.
    - *Strict cells.* The strict 2-cells are a, b, c, d, F, G, L, R and identities. The only nonidentity strict 3-cell is πU, and every term with that image uses U exactly once.
    - *RC(3) on the 2-skeleton Γ₀.* Restrict by value. The values a, b, c, d are direct coherences, F and G are squares, and L and R use the two-letter construction of item 10 (point-supported, forced order).
    - *Sequentialization.* Any 3-head over a 3-dimensional arity is 4-connected to a binary composite B_H with RC(2)-bridges in P_{≤2}. Interchange with identities then extracts every term of image πU to I₀ ; ω(U) ; I₁, where I₀ and I₁ are structural and ω is a whiskering by terms of dimension ≤ 2.
    - *Whiskering normalization.* ω is normalized by three local constructions: path coefficients (the interchanger on D³ ∗₁ D³), point-supported 2-coefficients (D²(a) ∗₀ D³(U)), and point-supported 1-loops l : x⁻ → x⁻ (D²(κ) ∗₀ D³(U) with unitors).
    - So K exists for every 3-dimensional coherence over the 2-disc, for any lower lifts.
14. **Suspension descent.** With ΣY selected and the poles N, S unselected, (ΣQ)↑ΣY = Σ(Q↑Y). The cut decoder of item 11 handles arbitrary coloured contexts, with a dimension-1 clause D coh[γ] = D(γ(e)) and with full-endpoint decoding when the cut column has dimension ≤ d − 2. It satisfies D(Σt) = t. Hence
    ```
    RC(r+1, (ΣQ)↑ΣY)  ⇒  RC(r, Q↑Y).
    ```
    So RC(n) on all cylinders, **including partial selections**, gives Conjecture N through dimension n.
15. **Chains.**
    - *Full chain cylinders.* With vᵢ = xᵢ↑ and Fᵢ : aᵢ⁻vᵢ → vᵢ₋₁aᵢ⁺, the strict 1-paths x_a⁻ → x_b⁺ are P_j = a⁻ … a_j⁻ v_j a⁺_{j+1} …, and Fᵢ sends P_i to P_{i−1}. So every nonidentity strict 2-cell has the forced word F_r … F_{s+1}, and arities factor literally through frames P_left ∗₀ C_n ∗₀ P_right or P_left ∗₀ V(k) ∗₀ P_right.
    - *Proper selections.* A one-chain frame is not enough. For Y = {a₁, a₂} on x₀ → x₁ → x₂, the cylinder is D² ∗₀ D² with two independent 2-generators.
16. **The support lemma (proved).** In every context, the generators used by the strict image of a term are exactly its dependency-closed support: `supp(π t) = supp(t)`. So a term whose strict image lies in a dependency-closed sub-context is literally a term of that sub-context.
17. **RC(3) on every finite full chain cylinder.** Q = (x₀ → ⋯ → x_k), Y = Var(Q).
    - *Normal forms.* For a forced word F_r ⋯ F_{s+1} between 1-terms A and B, N_w(A, B) is the left-associated list κ(A, S_r), E_r, κ(T_r, S_{r−1}), E_{r−1}, …, E_{s+1}, κ(T_{s+1}, B). Here E_i = L_i⁻ ∗₀ (F_i ∗₀ R_i⁺) is a fixed raw letter, and κ is the fixed path comparison. A comparison is kept between every two letters, even when its endpoints are syntactically equal.
    - *Fold.* Multiplication μ contracts the one pair of path comparisons at the join. The 4-cells comparing contraction orders have three cases (same pair, disjoint pairs, overlapping pairs on one path), each a single coherence.
    - *Fixed whiskering.* d_W : WU · WV ⇒ W(U · V) and ρ_W : Wκ_p ⇒ κ_{Wp}. Raw-letter conversions are padded with path comparisons on P_ℓ ∗₀ D²(z) ∗₀ P_r and repaired on actual paths after substitution. When a marked letter is evaluated at a long word, every entry of the word is first made a separate variable of C_N.
    - *Normalisers and fusion.* ν_T = v_H[η] ; D_{B_H, η}, where v_H is one coherence on the retained frame and D is a finite fold. Fusion is by induction on the relative term. For every 3-term G : T ⇒ T′ there is Λ_G : G ; ν_{T′} ⇒ ν_T, using one full coherence Ξ_H per head. Right cancellation gives RC(3).
    -
18. **Two proper selections with forced order.** On x → y → z, RC(3) holds for Y = {z, g} (G : g⁻ ∗₀ Z ⇒ g⁺) and for Y = {y, z, f, g} (G : g⁻ ∗₀ Z ⇒ Y ∗₀ g⁺ and then F : f⁻ ∗₀ Y ⇒ f⁺, with a path comparison kept between them). For Y = {x, f, g}, instead, F : f⁻ ⇒ X ∗₀ f⁺ and G : g⁻ ⇒ g⁺ act on disjoint parts of f⁻g⁻, and both orders occur.
19. **RC(3) on the cylinder of D² ∗₁ D².** With U_A : c₀ · F₁ ⇛ F₀ · d₀ and U_B : c₁ · F₂ ⇛ F₁ · d₁:
    - The mixed strict 2-cells are the unique words c_i ⋯ c_{k−1} F_k d_k ⋯ d_{j−1}, and item 17 gives RC(3) on the 2-skeleton.
    - The nonidentity strict 3-cells are U_A, U_B, W_A = U_A ∗₁ d₁, W_B = c₀ ∗₁ U_B and W_B ∗₂ W_A, so a 3-term uses at most two generators, in a forced order.
    - Coefficients are normalised by RC(2) and interchange coherences on D³ ∗₁ D³. Anchors E_W = ν̄ ; W ; ν then compose literally, and the seam between W_B and W_A is an RC(3) comparison on the 2-skeleton.
20. **Two independent letters (proved).** RC(3) holds for the cylinder of x → y → z with Y = {x, f, g}, where F : f⁻ ⇒ X ∗₀ f⁺ and G : g⁻ ⇒ g⁺. So K(Q, B, Y) exists for every 3-dimensional coherence over x → y → z with this Y, for any lower lifts.
    - *Strict cells.* The paths a → d are p_ij = f_i g_j; F changes the first index and G the second, so the strict 2-cells between them form the product order on {0,1}².
    - *Normal form.* The diagonal 2-cell is normalised through the horizontal composite E_H = F ∗₀ G, keeping horizontal identity factors for one-letter transitions. The two evaluation orders become two multiplications of a 2 × 2 "matrix" of 2-cells. Raw exchange coherences θ_GF, θ_FG over D²(u) ∗₀ D²(v) compare the two orders.
    - *Multiplication.* M = I ; (m^F ∗₀ m^G), with I : (α ∗₀ β) · (α′ ∗₀ β′) ⇛ (α · α′) ∗₀ (β · β′) a coherence over C₂ ∗₀ C₂, and its 4-laws over the minimal arities. A path-only coherence ζ reassociates the concatenated path without splitting any arbitrary 1-term at y.
    - *Fusion.* A horizontal fold ψ over C₃ ∗₀ C₃ and a horizontal–vertical 4-cell built from a coherence over C₆ ∗₀ C₆, depth-1 naturality and path-only comparisons give fusion.
    - *Retained heads.* The common vertices of the two boundary paths are a, c, d, and every 0-cut of a head must go to one of them, so retained heads are C_n or C_m ∗₀ C_n. A separate clause absorbs a column that becomes point-supported at a or d under substitution, by a coherence over D²(z) formed before z is evaluated.
21. **The interchange of the two generators on D² ∗₀ D² (proved).** On the full cylinder of Q = D² ∗₀ D², with cylinder generators U_A, U_B, let P = D³(v) ∗₁ D²(k) ∗₁ D³(u) and
    R₁ = ((v ∗₁ k) ∗₁ σu) ; ((τv ∗₁ k) ∗₁ u),  R₂ = ((σv ∗₁ k) ∗₁ u) ; ((v ∗₁ k) ∗₁ τu).
    Both are full in P with source (σv · k) · σu and target (τv · k) · τu. Then coh_{P, R₁ → R₂}[v ↦ f₀⁻ ∗₀ U_B, k ↦ K, u ↦ U_A ∗₀ g₁⁺] compares the U_B-then-U_A and U_A-then-U_B routes. The seam K : f₀⁻ ∗₀ (Y ∗₀ g₁⁺) ⇒ (f₀⁻ ∗₀ Y) ∗₀ g₁⁺ is needed for the composite to be well typed.
22. **Related results for other contexts (proved).**
    - *One-generator extension lemma.* Let Λ have dimension ≤ 2, an acyclic generating 1-graph and RC(3), and let Γ = (Λ, z : A → B) have z as the only nonidentity strict 3-cell. Then RC(3) holds in Γ. The proof compares a 3-head with a binary composite of its 3-variables by one coherence, follows the unique z-carrying argument, removes its whiskers by explicit 4-coherences, and compares the z-free remainders by RC(3) in Λ.
    - *Line-word criterion (sketch).* If a strict 2-cell w has a unique event word, every proper contiguous subword satisfies RC(3), and some event uses a 2-generator spanning w's endpoints, then the fibre of w satisfies RC(3).
    - These give RC(3) for the whole Gray cube, for the full cylinder of D² (a second proof of item 13), and for the join c ⋆ D².
    - *Local exchange law.* Over P = D²(a) ∨₀ D²(b), with χ = coh_{P, L → R} the exchange between L = (a ∗₀ g₀) ∗₁ (f₁ ∗₀ b) and R = (f₀ ∗₀ b) ∗₁ (a ∗₀ g₁), the term coh_{D³ ∨₀ D³, (χ⁻ ∗₂ A_R) → (A_L ∗₂ χ⁺)} is a valid 4-term. It is a local law, not a comparison of arbitrary 3-heads.
    - The open step there is the 2 × 2 grid of lax squares: two 2-generators exchange without a cut vertex separating them.
23. **Cones over vertical chains (proved).** For every vertical chain Q_m of 2-discs, RC(3) holds for the join context Cone(Q_m; c). The case Cone(D² ∨ D²; c), with two apex edges under non-point columns, is open for the same reason as question 1 below.

## 3. What remains, and why

Item 20 settles exchange of two letters when a cut vertex splits every head into at most two horizontal columns. Item 21 gives the 4-term that interchanges the two 3-generators of the cylinder of D² ∗₀ D². What is missing for that cylinder is RC(3) on its 2-skeleton, where the exchanges are not separated by a cut vertex, and fusion of the U_A/U_B interchange with that normal form. 3-dimensional Q needs RC(4), which needs a 5-dimensional compatibility between chosen 3-normalisers.

Item 14 reduces Conjecture N to RC(n) on all cylinders.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **The horizontal two-disc.** Prove RC(3) on the full cylinder of Q = D² ∗₀ D². Two steps are needed: RC(3) on its 2-skeleton, where several exchanges between letters are not separated by a cut vertex; and fusion of item 21's interchange with the normal form for 3-terms using U_A and U_B in either order. A solution of the first step alone is useful.
2. **RC(3) on all cylinders.** Prove RC(3) for every Q↑Y with Q a pasting context of dimension ≤ 2 and Y up-closed, or for every finite Steiner loop-free context. Or give a counterexample.
3. **The 3-disc.** Prove RC(4) on the cylinder of the 3-disc, or on (ΣD²)↑ΣY. State what 5-dimensional compatibility of chosen 3-normalisers the proof needs and how it is built.
4. **All dimensions.** Prove RC(n) on all cylinders Q↑Y, including partial selections. By item 14, this proves Conjecture N at every depth.
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

**Question 1 has an affirmative answer, using the results in §2 as premises.** The construction below proves both
\[
\mathrm{RC}(3)(\Gamma_0)
\qquad\text{and}\qquad
\mathrm{RC}(3)(\Gamma),
\]
where
\[
\Gamma=(D^2*_0D^2)\uparrow\operatorname{Var}(D^2*_0D^2)
\]
and \(\Gamma_0\) is obtained from \(\Gamma\) by deleting \(U_A,U_B\).

The new ingredient for \(\Gamma_0\) is a choice of exchange orientation that agrees with serialization at both possible nontrivial cuts. It has exactly one branching, involving two disjoint swaps. The extension from \(\Gamma_0\) to \(\Gamma\) then uses normal forms whose four relevant edges are precisely the edges of the interchange square in §2 item 21.

I use
\[
\alpha\cdot\beta:=\alpha*_1\beta,\qquad
H;K:=H*_2K.
\]
Parentheses displayed below are part of the syntax. For parallel full terms \(s,t\) on a genuine pasting context \(P\), write
\[
[s,t]_P:=\operatorname{coh}_{P,s\to t}[\mathrm{id}].
\]
All uses of this notation below specify such a \(P\).

## 1. The strict 2-cells and the choice of exchange orientation

Write the original two 2-discs as
\[
A:f_0\Rightarrow f_1:x\to y,
\qquad
B:g_0\Rightarrow g_1:y\to z.
\]
In \(\Gamma_0\), put
\[
a=A^-,\quad a'=A^+,\quad b=B^-,\quad b'=B^+.
\]
The other 2-generators are
\[
F_i:f_i^-*_0Y\Rightarrow X*_0f_i^+,
\qquad
G_j:g_j^-*_0Z\Rightarrow Y*_0g_j^+.
\]

For the strict calculation only, suppress parentheses and write the paths \(x^-\to z^+\) as
\[
p_{ij}=f_i^-g_j^-Z,\qquad
q_{ij}=f_i^-Yg_j^+,\qquad
r_{ij}=Xf_i^+g_j^+.
\]

Use \(A,B,F,G\) as **event labels**, distinct from the individual CaTT generators:

- \(A\) increases \(i\); it uses \(a\) before \(F\), and \(a'\) after \(F\).
- \(B\) increases \(j\); it uses \(b\) before \(G\), and \(b'\) after \(G\).
- \(G\) changes a \(p\)-path to a \(q\)-path.
- \(F\) changes a \(q\)-path to an \(r\)-path.

Each event can be used at most once, and \(G\) precedes \(F\) when both are used. The independent pairs are exactly
\[
(A,B),\qquad(A,G),\qquad(F,B).
\]

Orient their exchanges by
\[
AB\longrightarrow BA,\qquad
AG\longrightarrow GA,\qquad
FB\longrightarrow BF. \tag{1}
\]

For an admissible event word \(w\), define
\[
m(w)=
[A\text{ precedes }B]+
[A\text{ precedes }G]+
[F\text{ precedes }B],
\]
with a summand equal to zero when one of its letters is absent. Each reduction decreases \(m\) by one.

Two reductions cannot overlap: every left side of (1) starts in \(\{A,F\}\) and ends in \(\{B,G\}\). Two disjoint reductions require all four events. The only admissible branching is
\[
\begin{aligned}
AGFB&\longrightarrow GAFB\longrightarrow GABF,\\
AGFB&\longrightarrow AGBF\longrightarrow GABF.
\end{aligned} \tag{2}
\]
Both routes then continue to \(GBAF\).

Thus every strict 2-cell has a unique normal event word. For the four strict 2-cells using every event, these words are:

| Order of the dependent pairs | Normal word |
|---|---|
| \(A<F,\ B<G\) | \(BGAF\) |
| \(F<A,\ B<G\) | \(BGFA\) |
| \(A<F,\ G<B\) | \(GBAF\) |
| \(F<A,\ G<B\) | \(GBFA\) |

The orientation matters because it agrees with **right-column-first serialization at every nonpoint cut**:

| Strict 2-cell sector | Possible nonpoint cut | Left-column events | Right-column events |
|---|---|---|---|
| \(p\to q\) | \(y^-\) | \(A\) | a subword of \(BG\) or \(GB\) |
| \(q\to r\) | \(y^+\) | a subword of \(AF\) or \(FA\) | \(B\) |
| \(p\to r\) | none | — | — |

For the last row, the source and target paths have common vertices only \(x^-,z^+\). Consequently every head with a \(p\to r\) value has one retained nonpoint \(0\)-column.

The remaining sectors are covered by the same-cut cases \(p\to p,q\to q,r\to r\), by the local disc cylinders \(x^-\to y^+\) and \(y^-\to z^+\), or by genuine pasting contexts with fixed path factors. In particular, the \(q\to q\) frame can be
\[
C_m*_0D^1(Y)*_0C_n.
\]
The fixed middle edge must be retained.

## 2. The serialization comparison and its 4-dimensional laws

The combinatorial calculation above needs a compatibility with evaluation. Here is the additional term construction.

### 2.1 Serialization of two columns

On
\[
P=D^2(u)*_0D^2(v),
\]
write
\[
u:s_0\Rightarrow s_1,\qquad v:t_0\Rightarrow t_1.
\]
Define
\[
\begin{aligned}
R(u,v)&=(1_{s_0}*_0v)\cdot(u*_01_{t_1}),\\
L(u,v)&=(u*_01_{t_0})\cdot(1_{s_1}*_0v).
\end{aligned}
\]
Both have literal source \(s_0*_0t_0\) and target \(s_1*_0t_1\). Choose
\[
\rho_{u,v}=[u*_0v,R(u,v)]_P,
\qquad
\chi_{u,v}=[L(u,v),R(u,v)]_P. \tag{3}
\]

The identity 2-factors in these expressions are retained.

For \(AG\) and \(FB\), the arities of the exchange are respectively
\[
D^2(a)*_0D^2(G_j),
\qquad
D^2(F_i)*_0D^2(b').
\]
For \(AB\), retain the appropriate fixed path:
\[
\begin{array}{c|c}
p\text{-sector}&D^2(a)*_0D^2(b)*_0D^1(Z),\\
q\text{-sector}&D^2(a)*_0D^1(Y)*_0D^2(b'),\\
r\text{-sector}&D^1(X)*_0D^2(a')*_0D^2(b').
\end{array} \tag{4}
\]
The two descriptions of the \(q\)-sector exchange, obtained by placing \(Y\) with either adjacent column, are compared by a full 4-coherence on the middle arity in (4).

After substituting the actual generators, the path corrections from §2 items 17 and 20 convert these terms to exchanges between the chosen padded word forms. No arbitrary 1-term is split at \(y^\pm\).

### 2.2 Serialization versus multiplication

Work on the genuine pasting context
\[
C_2(u,u')*_0C_2(v,v'),
\]
with
\[
u:s_0\Rightarrow s_1,\quad u':s_1\Rightarrow s_2,
\qquad
v:t_0\Rightarrow t_1,\quad v':t_1\Rightarrow t_2.
\]

Let
\[
I:(u*_0v)\cdot(u' *_0v')
\Rightarrow
(u\cdot u')*_0(v\cdot v')
\]
be the usual interchange coherence.

Define
\[
J:R(u,v)\cdot R(u',v')
\Rightarrow R(u\cdot u',v\cdot v') \tag{5}
\]
by this finite recipe:

1. Reassociate the four factors to isolate
   \[
   (u*_01_{t_1})\cdot(1_{s_1}*_0v').
   \]
2. Apply \(\chi_{u,v'}\).
3. Reassociate to group the two right-column factors and the two left-column factors.
4. Apply the column folds
   \[
   \begin{aligned}
   &(1_{s_0}*_0v)\cdot(1_{s_0}*_0v')
   \Rightarrow1_{s_0}*_0(v\cdot v'),\\
   &(u*_01_{t_2})\cdot(u' *_01_{t_2})
   \Rightarrow(u\cdot u')*_01_{t_2}.
   \end{aligned}
   \]

Now the two 3-terms
\[
I;\rho_{u\cdot u',\,v\cdot v'}
\quad\text{and}\quad
(\rho_{u,v}*_1\rho_{u',v'});J \tag{6}
\]
have the same literal source and target. Each uses all four 2-variables and their boundaries. Therefore
\[
\left[
I;\rho,\,
(\rho*_1\rho);J
\right]_{C_2*_0C_2} \tag{7}
\]
is the required 4-cell.

When the column representatives use their own multiplication \(m^L,m^R\), append those folds and their naturality comparisons to (6). This gives the same law for
\[
M=I;(m^L*_0m^R).
\]

For longer column words, make every entry a separate variable of
\[
C_M*_0C_N.
\]
Both subdivision routes are then explicit full 3-terms on this genuine pasting context, so their comparison is a 4-coherence there. **This comparison is formed before the marked variables are evaluated.**

Updating one marked 2-variable by a 3-cell uses
\[
V_M(0,\ldots,1,\ldots,0)*_0C_N
\quad\text{or}\quad
C_M*_0V_N(0,\ldots,1,\ldots,0).
\]
These are precisely top-2-argument naturality instances: depth \(0\) in the context and depth \(1\) in the 3-term. They are within BMOSV Theorem 3.1. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

This establishes the serialization interface for arbitrary retained column lengths, including a column whose evaluated value is a composite.

## 3. Sorting padded words

Use the padded word convention of §2 item 17. For an enabled event \(e\), let \(E_e\) be its generator with the fixed raw whiskers, and write
\[
S_e=\sigma E_e,\qquad T_e=\tau E_e.
\]
For \(w=e_1\cdots e_k\), put
\[
\begin{aligned}
\langle w\rangle_{U,V}
=\operatorname{LF}\bigl[
&\kappa(U,S_{e_1}),E_{e_1},
\kappa(T_{e_1},S_{e_2}),E_{e_2},\ldots,\\
&E_{e_k},\kappa(T_{e_k},V)
\bigr],
\end{aligned} \tag{8}
\]
where \(\operatorname{LF}\) denotes the fixed left-associated vertical composite.

The empty-word form is the fixed path form. Comparisons \(\kappa(W,W)\) are retained until an explicit path fold removes them.

For a strict value \(\delta\), define
\[
N_\delta(U,V)=\langle n(\delta)\rangle_{U,V}, \tag{9}
\]
where \(n(\delta)\) is its normal event word.

Let \(\operatorname{sort}_w\) be the 3-term that applies the **leftmost** available reduction in (1), using (3)–(4) and the fixed padding conversions, until the word is normal.

For composable values define multiplication by
\[
\mu_{\delta,\epsilon}
=
\mu^{\mathrm{flat}}_{\delta,\epsilon};
\operatorname{sort}_{\,n(\delta)n(\epsilon)}. \tag{10}
\]
Here \(\mu^{\mathrm{flat}}\) is the previously constructed word fold: it contracts the path comparisons at the join and produces the single padded concatenation.

### The one new sorting diamond

Retain the seam between the two exchanged blocks. On
\[
P=D^3(s)*_1D^2(k)*_1D^3(t),
\]
write
\[
s:S_0\Rightarrow S_1,\qquad
t:T_0\Rightarrow T_1.
\]
The terms
\[
\begin{aligned}
D_1&=((s*_1k)*_1T_0);
       ((S_1*_1k)*_1t),\\
D_2&=((S_0*_1k)*_1t);
       ((s*_1k)*_1T_1)
\end{aligned} \tag{11}
\]
have literal 2-source
\[
(S_0\cdot k)\cdot T_0
\]
and literal 2-target
\[
(S_1\cdot k)\cdot T_1.
\]
Both are full in \(P\). Thus
\[
[D_1,D_2]_P \tag{12}
\]
evaluated at the \(AG\) and \(FB\) exchanges fills (2).

The surrounding padded word is handled by the established vertical fold laws. A swap is kept as a whole 3-variable in contexts such as
\[
D^2(\text{prefix})*_1D^3(s)*_1D^2(\text{suffix}),
\]
with separate seam discs when required.

This gives a finite comparison between any two sorting routes. If their first reductions agree, continue with their suffixes. If they differ, use (12), then continue. The measure \(m\) makes this recursion terminate.

Consequently, the associativity 4-cell for (10) is constructed by:

1. applying the old flat-word and path-fold laws to put both routes over the same padded concatenation;
2. moving swaps through those folds using (7) and the whole-3-variable vertical comparisons;
3. comparing the resulting sorting routes by (12).

The unit and subdivision laws use the same construction. There is no overlapping exchange branching.

## 4. Evaluation fusion on the 2-skeleton

This is the step needed to pass from the finite event calculation to arbitrary CaTT terms.

### 4.1 Loss of a cut

Suppose a two-column reference frame evaluates to a value using both \(G\) and \(F\). Its cut must map to \(x^-\) or \(z^+\). One column is therefore point-supported.

By the support lemma, its complete contribution is literally a term
\[
q:\ell_0\Rightarrow\ell_1
\]
over that point. Leave the other 2-variable \(z:s\Rightarrow t\) unevaluated. Use
\[
B_q(z):
q*_0z
\Rightarrow
\bigl(\kappa(\ell_0*_0s,s)\cdot z\bigr)
\cdot\kappa(t,\ell_1*_0t). \tag{13}
\]
This is a full 3-coherence on \(D^2(z)\): \(q,\ell_0,\ell_1\) are terms over its source object, and both endpoints use \(z\).

For \(h:z\Rightarrow z'\), the two routes
\[
(q*_0h);B_q(z')
\]
and
\[
B_q(z);
\bigl((\kappa(\ell_0*_0s,s)*_1h)
       *_1\kappa(t,\ell_1*_0t)\bigr)
\]
are full parallel 3-terms on \(D^3(h)\). Their comparison gives the slot-update law for (13).

The comparison between matrix evaluation and this point absorption is also formed before evaluating \(z\), on \(D^2(z)\), or on \(C_N\) when the other column is a reference word. Thus \(z\) may subsequently be assigned an arbitrary term with the whole global value.

An inactive nonpoint column uses the literal path factorization and the path comparison \(\zeta\) from §2 items 12 and 20.

### 4.2 Normalizers

For a 2-head \(T\), perform the literal factorization
\[
T=H[\eta]
\]
through its retained genuine frame \(R\). Keep every active 2-slot. Choose the fixed reference word or grid \(B_H\), with the same literal 1-boundaries as \(H\), and put
\[
v_H=[H,B_H]_R.
\]

Define
\[
\nu_T=v_H[\eta];D_{B_H,\eta}, \tag{14}
\]
where the evaluator \(D\) has these clauses:

| Reference expression | Evaluation |
|---|---|
| Marked 2-slot | Its proper-child normalizer |
| Path comparison or identity | The established path evaluator |
| Vertical product | Child evaluations followed by (10) |
| Two active horizontal columns | The matrix evaluator followed by \(\rho\) and the fixed padding conversions |
| Inactive nonpoint column | Literal path factorization and \(\zeta\) |
| Point column | (13), formed with the other slot unevaluated, followed by that slot’s evaluation |

The two-active-column clause is applicable to the \(p\to q\) and \(q\to r\) sectors because the column words are forced. Right-first serialization agrees with (1). Longer reference columns are handled by (7) before evaluation.

For a relative 2-term \(u\), let
\[
\lambda_u:u\Rightarrow B_u
\]
be the recursive relative normalizer using these same operations. The fusion cell is
\[
\mathcal F_{u,\sigma}:
\nu_{u[\sigma]}
\Longrightarrow
\lambda_u[\sigma];D_{B_u,\sigma}. \tag{15}
\]

Its construction is by induction on the syntax of \(u\):

- **Slot:** substitute \(h=\nu_{\sigma z}\) into the generic \(D^3(h)\) insertion-transport law.
- **Path:** use path fusion.
- **Vertical product:** use the child fusion cells, flat-fold naturality, and the associativity/subdivision comparisons for (10).
- **Horizontal product:** use matrix fusion, then (7) and its marked-slot naturality. If a column is lost, apply the path clause or (13).
- **Head:** retain the first step \(v_H\) in (14), and apply the preceding finite-fold comparisons. When a retained column becomes point-supported, factor its terms literally through the point before forming the comparison on the surviving \(C_n\).

The slot clause permits \(\sigma z\) to have the entire global value: it uses the already defined \(\nu_{\sigma z}\) as the value of a 3-variable. It does not recursively normalize an assembled expression.

### 4.3 Arbitrary 3-heads

A retained active \(0\)-column of a 3-head is
\[
V_n(k_1,\ldots,k_n),
\]
with arbitrary \(k_i\geq0\). Every original 3-link is retained. Two active columns give the horizontal product of two such frames, with the fixed path factors retained.

For a relative head
\[
H:S\Rightarrow T
\]
on a retained frame \(R\), form \(\lambda_S,\lambda_T\). Let
\[
W:B_S\Rightarrow B_T
\]
update every retained 3-link in the selected reference expression. A slot with \(k_i=0\) contributes an identity 3-cell.

Then
\[
H;\lambda_T
\quad\text{and}\quad
\lambda_S;W
\]
are parallel and full in \(R\). The first uses every retained variable through \(H\); the second uses every 3-link through \(W\) and every remaining 2-slot through the reference expression. Hence
\[
\Xi_H=[H;\lambda_T,\lambda_S;W]_R \tag{16}
\]
is a valid 4-coherence.

Evaluate (16), apply (15), and use the finite-fold naturality laws. Structural induction on a 3-term \(h:S\Rightarrow T\) gives
\[
\Lambda_h:h;\nu_T\Longrightarrow\nu_S. \tag{17}
\]

Every primitive in \(\nu_T\) is a coherence between full 2-terms on a genuine pasting context. Reverse coherences and their 4-dimensional cancellation comparisons are available on the same contexts. Therefore, for parallel \(h,k:S\Rightarrow T\), compose
\[
h;\nu_T
\xRightarrow{\Lambda_h}
\nu_S
\xRightarrow{\overline{\Lambda_k}}
k;\nu_T
\]
and cancel \(\nu_T\).

This constructs
\[
\operatorname{Fill}_{\Gamma_0}(h,k):h\longrightarrow k.
\]

Thus
\[
\boxed{\mathrm{RC}(3)(\Gamma_0).} \tag{18}
\]

## 5. Restoring \(U_A,U_B\): fixed representatives

The generating 3-cells are
\[
\begin{aligned}
U_A&:(a*_0Y)\cdot F_1
 \Rightarrow F_0\cdot(X*_0a'),\\
U_B&:(b*_0Z)\cdot G_1
 \Rightarrow G_0\cdot(Y*_0b').
\end{aligned}
\]

Define actual weak terms
\[
\begin{aligned}
u_j&=U_A*_0g_j^+,& u&=u_1,\\
v_i&=f_i^-*_0U_B,& v&=v_0,\\
e_j&=f_0^-*_0G_j,& d_i&=F_i*_0g_1^+,\\
c&=(f_0^-*_0Y)*_0b',&
a_R&=(a*_0Y)*_0g_1^+.
\end{aligned}
\]

Choose the path associators
\[
\begin{aligned}
K_j &: f_0^-*_0(Y*_0g_j^+)
      \Rightarrow(f_0^-*_0Y)*_0g_j^+,\\
K^i &: f_i^-*_0(Y*_0g_1^+)
      \Rightarrow(f_i^-*_0Y)*_0g_1^+,
\end{aligned}
\]
with \(K_1=K^0=K\) literally.

The following are well-typed representatives of all sixteen single-generator strict 3-values:

| \(i\) | \(A_i\), using \(U_A\) | \(B_i\), using \(U_B\) |
|---|---|---|
| 1 | \(U_A\) | \(U_B\) |
| 2 | \(u_0\) | \(v_0\) |
| 3 | \(u_1\) | \(v_1\) |
| 4 | \((e_0\cdot K_0)*_1u_0\) | \((v_0*_1K^0)*_1d_0\) |
| 5 | \((e_1\cdot K_1)*_1u_1\) | \((v_1*_1K^1)*_1d_1\) |
| 6 | \(c*_1u\) | \((v*_1K)*_1a_R\) |
| 7 | \((\tau v\cdot K)*_1u\) | \((v*_1K)*_1\sigma u\) |
| 8 | \((\sigma v\cdot K)*_1u\) | \((v*_1K)*_1\tau u\) |

Here \(\sigma u,\tau u,\sigma v,\tau v\) are 2-terms of \(\Gamma_0\). In particular, the displayed \(A_i\) do not use \(U_B\), and the \(B_i\) do not use \(U_A\).

The list is exhaustive. For a single \(U_A\), its right 1-whisker is an identity, \(g_0^+\), or \(g_1^+\); its left 1-whisker is point-supported. After moving a possible \(b'\)-suffix to the prefix, the numbers of possible prefix values are respectively \(1,2,5\). They are represented by the eight \(A_i\).

For \(U_B\), the corresponding left 1-whiskers are an identity, \(f_0^-\), or \(f_1^-\). Move a possible \(a\)-prefix to the suffix. The numbers of possible suffix values are \(1,5,2\), represented by the \(B_i\).

These restrictions follow from monotonicity of the indices and of the position of the vertical edge. For example, a prefix ending at \((f_0^-Y)g_j^+\) cannot use \(A\) or \(F\): neither change can subsequently be reversed.

Each strict 3-cell uses each of \(U_A,U_B\) at most once. The only two-step routes using both are
\[
B_7;A_7,\qquad A_8;B_8. \tag{19}
\]
They represent the same strict 3-cell.

## 6. Normalizing a single use of a 3-generator

Two elementary 4-constructions suffice beyond the established sequentialization.

### 6.1 Transporting a 2-cell coefficient

Let
\[
h:c\Rightarrow d,\qquad z:\alpha\Rightarrow\beta
\]
be generic 3-variables. For \(k=0,1\), work on
\[
P_k=D^3(h)*_kD^3(z).
\]
The routes
\[
\begin{aligned}
L_k&=(h*_k\alpha);(d*_kz),\\
R_k&=(c*_kz);(h*_k\beta)
\end{aligned}
\]
are parallel and full. Thus
\[
[L_k,R_k]_{P_k} \tag{20}
\]
transports a coefficient comparison supplied by RC(2) past the distinguished 3-cell.

When a 1-dimensional seam needs correction, retain its 2-disc:
\[
D^3(h)*_1D^2(k)*_1D^3(z).
\]

### 6.2 Distributing a horizontal 2-cell coefficient

Take
\[
z:\alpha\Rightarrow\beta,\qquad
\alpha,\beta:p\Rightarrow q,
\qquad c:r\Rightarrow s.
\]
Work on
\[
P=D^3(z)*_0D^2(c).
\]

On the source boundary choose
\[
\delta_\alpha:
\alpha*_0c
\Rightarrow
(\alpha*_0r)\cdot(q*_0c),
\]
using \(D^2(\alpha)*_0D^2(c)\). Choose the reverse-oriented target comparison \(\overline{\delta_\beta}\).

Then
\[
z*_0c
\quad\text{and}\quad
\delta_\alpha;
\bigl((z*_0r)*_1(q*_0c)\bigr);
\overline{\delta_\beta} \tag{21}
\]
are parallel full 3-terms on \(P\). Their 4-comparison is \([\,\cdot,\cdot\,]_P\).

The other order uses
\[
\alpha*_0c
\Rightarrow
(p*_0c)\cdot(\alpha*_0s).
\]
The left-coefficient version uses \(D^2(c)*_0D^3(z)\).

These coherences are formed with the source and target of \(z\) as whole 2-variables. Only afterward is \(z\) replaced by \(U_A\) or \(U_B\).

### 6.3 The unary normalization procedure

Sequentialization reduces a 3-term with one nonidentity strict generator to structural 3-pads and a term obtained by whiskering that generator.

Apply (21) until only 1-whiskers and 2-cell prefixes/suffixes remain. Normalize the 1-whiskers on their actual path contexts; the relevant universal arities are
\[
P_{\mathrm{left}}*_0D^3(z)*_0P_{\mathrm{right}}.
\]
Normalize the 2-cell coefficients by RC(2), and transport those comparisons using (20).

Finally:

- for \(U_A\), move the possible \(b'\)-suffix to the prefix;
- for \(U_B\), move the possible \(a\)-prefix to the suffix.

The result has one of the sixteen strict values above. A further coefficient normalization targets the corresponding displayed \(A_i\) or \(B_i\). For example, the prefix of \(A_7\) is chosen to be the actual term \(\tau v\cdot K\); it is not identified syntactically with another presentation of its strict value.

All structural 3-pads produced in this process lie in \(\Gamma_0\).

## 7. Actual-boundary normal forms and the double-generator case

Fix a representative \(W_h\) for each strict 3-value \(h\), using the preceding table and
\[
W_{AB}=B_7;A_7
\]
for the value using both generators.

First give representatives with the same strict 1-boundaries a common choice of actual 1-boundaries \(\bar p,\bar q\), using path comparisons. Use the same framing for all four edges in (19).

For a particular problem
\[
T,T':s\Rightarrow t,
\]
let the actual common 1-boundaries be \(p,q\). Choose
\[
L:p\Rightarrow\bar p,\qquad
R:\bar q\Rightarrow q,
\]
and put
\[
W_h^{p,q}=(1_L*_1W_h)*_11_R.
\]
Its 2-source and 2-target are literally
\[
S_h^{p,q}=(L\cdot\sigma W_h)\cdot R,
\qquad
T_h^{p,q}=(L\cdot\tau W_h)\cdot R.
\]

RC(2) now applies to genuinely parallel 2-terms. Fix
\[
\kappa_s:s\Rightarrow S_h^{p,q},
\qquad
\kappa_t:T_h^{p,q}\Rightarrow t,
\]
and define the 3-normal form
\[
\mathcal N_h(s,t)
=(\kappa_s;W_h^{p,q});\kappa_t. \tag{22}
\]

The result of unary normalization differs from (22) only in its structural 3-pads. By (18), any such left pad is 4-connected to \(\kappa_s\), and any such right pad is 4-connected to \(\kappa_t\). Whiskering these comparisons by \(W_h^{p,q}\) gives the required 4-cell to (22).

### The four exact corners

Put
\[
v^{(0)}=\sigma v,\quad v^{(1)}=\tau v,
\qquad
u^{(0)}=\sigma u,\quad u^{(1)}=\tau u,
\]
and define
\[
S_{ij}=(v^{(i)}\cdot K)\cdot u^{(j)}.
\]
The four selected edges have literal boundaries
\[
\begin{array}{c|c}
A_8&S_{00}\to S_{01},\\
A_7&S_{10}\to S_{11},\\
B_7&S_{00}\to S_{10},\\
B_8&S_{01}\to S_{11}.
\end{array}
\]

Thus the two paths in (19) are exactly
\[
\begin{aligned}
B_7;A_7
&=((v*_1K)*_1\sigma u);
  ((\tau v*_1K)*_1u),\\
A_8;B_8
&=((\sigma v*_1K)*_1u);
  ((v*_1K)*_1\tau u).
\end{aligned} \tag{23}
\]
The 4-cell of §2 item 21 applies directly to (23).

For an arbitrary 3-term using both generators, sequentialization produces two unary terms separated by structural 3-pads. Normalize the unary terms as above. The middle pad then becomes a 3-term from one framed \(S_{ij}\) to itself. RC(3) in \(\Gamma_0\) compares it with the identity 3-cell. Replace the outer pads by the fixed ones in (22).

The resulting route is one of (23). Apply the supplied interchange when necessary.

Outer framing is compatible with this step by coherences on
\[
D^2(L)*_1D^3(v)*_1D^2(K)*_1D^3(u)*_1D^2(R).
\]
This is a genuine pasting context.

## 8. The resulting filler and scope

The construction gives, for every 3-term \(T:s\Rightarrow t\), a 4-term
\[
\eta_T:T\longrightarrow\mathcal N_{\pi T}(s,t).
\]
Each elementary comparison is available in the reverse direction as well: reverse the endpoints of its genuine-pasting coherence, or apply RC(3) in \(\Gamma_0\) with reversed arguments.

For parallel \(T,T'\) with equal strict image, the required explicit recursive filler is therefore
\[
\boxed{
\operatorname{Fill}_{\Gamma}(T,T')
=
\eta_T*_3\overline{\eta_{T'}}:
T\longrightarrow T'.
} \tag{24}
\]

This proves
\[
\boxed{
\mathrm{RC}(3)\bigl((D^2*_0D^2)\uparrow
\operatorname{Var}(D^2*_0D^2)\bigr).
}
\]

By §2 item 3, it supplies
\[
K(Q,B,\operatorname{Var}Q)
=
\operatorname{Fill}_{\Gamma}(a_c,b_c)
\]
for every 3-dimensional coherence over the horizontal two-disc, with the lower lifts fixed arbitrarily.

The finite checks performed for this construction verified the event-word branching calculation, the literal boundaries and full support of the serialization-multiplication and disjoint-swap schemes, and the literal types of the sixteen unary representatives and four corner edges. They are symbolic checks of these schemes, not a complete CaTT formalization.

This settles question 1. The construction does not establish RC(3) for all cylinders, RC(4) for the 3-disc cylinder, or the 5-cell comparison required by question 5.

# Verification of the researcher response (2026-11-18)

**Verdict: correct at paper level.**
- **Settled:** Question 1. RC(3) holds on the full cylinder Γ = (D² ∗₀ D²)↑Var, and on its 2-skeleton Γ₀.
- **Consequence:** K(Q, B, Var Q) = Fill_Γ(a_c, b_c) for every 3-dimensional coherence over the horizontal two-disc.
- **Open:** Question 2 (all cylinders), Question 3 (RC(4) for the 3-disc), Question 4 (all dimensions), Question 5 (global K, a 5-cell between choices).

Checked step by step:

1. **Events and orientation, §1.**
   - The 2-skeleton has events A, B, F, G.
   - The chosen exchange orientations are AB → BA, AG → GA and FB → BF.
   - These agree with serialization at both nontrivial cuts.
   - The measure m decreases along each oriented exchange, so rewriting terminates.
   - I rechecked the critical pairs. The only branching is AGFB, with two disjoint swaps, and it closes by the disjoint-swap diamond.
2. **Serialization, §2.** ρ and χ are full coherences over genuine pasting contexts. Their 4-dimensional laws (serialization versus multiplication) are full on both sides with equal 2-boundaries. The finite check reported in §8 agrees.
3. **Sorting padded words, §3.** The one new sorting diamond is the AGFB branching above. The other diamonds are disjoint or come from item 24's local law.
4. **Fusion on the 2-skeleton, §4.**
   - Where a cut is lost, the head has one active column and reduces to a vertical chain, as in the grid argument.
   - Normalisers are built from RC(2), then sorting.
   - Arbitrary 3-heads are handled by the Ξ_P pattern (one coherence over the reduced 3-arity, plus fusion at both ends).
5. **U_A and U_B, §5–7.**
   - The sixteen unary representatives and the corners S_ij have the literal boundaries stated in (23).
   - The two routes of (23) are exactly the boundary of the §2 item-21 interchange 4-cell.
   - The middle pad between two unary terms is an endo-3-term of a framed S_ij, so RC(3)(Γ₀) removes it.
   - This part also follows from the cone-over-coherences round-5 extension theorem (RC(3)(Γ) ⇔ RC(3)(Γ₀), since Γ₀ has dimension 2 and an acyclic 1-graph). That gives an independent check.

**Consequences.**
- By the extension theorem, RC(3) for every cylinder Q↑Y with dim Q ≤ 2 reduces to RC(3) on its 2-skeleton.
- Those 2-skeleta are acyclic 2-dimensional contexts with exchange, which is exactly gray-contexts' general Question 2.
- So the depth-2 part of Conjecture N in dimension 3 is now that one 2-dimensional problem.
- Question 5 needs a 5-cell, the same kind of obligation as gray-contexts' (31)/(32).

Follow-up prompt: `outbox/naturality-arbitrary-depth-r8.md` (round 8, unsent).
