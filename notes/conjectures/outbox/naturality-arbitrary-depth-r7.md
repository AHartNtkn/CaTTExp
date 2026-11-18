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
11. **A dimension-lowering translation (from the cone problem).** For join contexts `Cone(Q; c)` (Q a pasting context, with an apex c and cone cells p_q), there is a syntactic *cut translation* D: colour the 0-variables 0/1, nondecreasing along generating 1-cells; D deletes same-side variables and lowers each crossing term by one dimension, decoding a coherence over its unique crossing root branch. It satisfies D(Σt) ≡ t, D(u ∗_k v) ≡ D(u) ∗_{k−1} D(v), D(e ∗₀ u) ≡ D(u) and D(t[θ]) ≡ D(t)[D(θ)], and with a raising substitution it gives `RC(r+1, Cone(ΣQ; d)) ⇒ RC(r, Cone(Q; c))`.
12. **Literal inactive-column factorisation (from the Gray-contexts problem).** In every context Γ of dimension ≤ 2 with an acyclic graph of generating 1-cells (for example Q↑Y for 1-dimensional Q), an arity column none of whose 2-variables receives a term containing a 2-variable lifts literally to the path context of its common strict path (the path labelling is injective by acyclicity). Replacing such columns gives a reduced pasting context R_σ with σ = κ_σ[δ_σ], comparison terms coh_{P,A}[σ] → coh_{R_σ,A[κ_σ]}[δ_σ], and refinement substitutions λ_{σ,ρ} that are functorial under further substitution, with coherence cells between iterated reductions. A coherence 4-term also distributes a fixed whisker across a vertical composite of 3-cells. The open part is the treatment of active columns, whose 2-variables carry arbitrary composites.

13. **RC(3) on the cylinder of the 2-disc.** Q = (x, y, f, g : x → y, A : f ⇒ g), Y = Var(Q).
    - Write X = x↑, Y = y↑, F = f↑, G = g↑, c = A⁻ ∗₀ Y, d = X ∗₀ A⁺, L = c ∗₁ G and R = F ∗₁ d, so that U = A↑ : L → R.
    - *Strict cells.* The strict 2-cells are a, b, c, d, F, G, L, R and identities. The only nonidentity strict 3-cell is πU, and every term with that image uses U exactly once.
    - *RC(3) on the 2-skeleton Γ₀.* Restrict by value. The values a, b, c, d are direct coherences, F and G are squares, and L and R use the round-3 two-letter construction (point-supported, forced order).
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
16. **The support lemma (from the cone problem, proved).** In every context, the generators used by the strict image of a term are exactly its dependency-closed support: `supp(π t) = supp(t)`. So a term whose strict image lies in a dependency-closed sub-context is literally a term of that sub-context.
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
22. **Related results in the Gray-contexts problem (proved).**
    - *One-generator extension lemma.* Let Λ have dimension ≤ 2, an acyclic generating 1-graph and RC(3), and let Γ = (Λ, z : A → B) have z as the only nonidentity strict 3-cell. Then RC(3) holds in Γ. The proof compares a 3-head with a binary composite of its 3-variables by one coherence, follows the unique z-carrying argument, removes its whiskers by explicit 4-coherences, and compares the z-free remainders by RC(3) in Λ.
    - *Line-word criterion (sketch).* If a strict 2-cell w has a unique event word, every proper contiguous subword satisfies RC(3), and some event uses a 2-generator spanning w's endpoints, then the fibre of w satisfies RC(3).
    - These give RC(3) for the whole Gray cube, for the full cylinder of D² (a second proof of item 13), and for the join c ⋆ D².
    - *Local exchange law.* Over P = D²(a) ∨₀ D²(b), with χ = coh_{P, L → R} the exchange between L = (a ∗₀ g₀) ∗₁ (f₁ ∗₀ b) and R = (f₀ ∗₀ b) ∗₁ (a ∗₀ g₁), the term coh_{D³ ∨₀ D³, (χ⁻ ∗₂ A_R) → (A_L ∗₂ χ⁺)} is a valid 4-term. It is a local law, not a comparison of arbitrary 3-heads.
    - The open step there is the 2 × 2 grid of lax squares: two 2-generators exchange without a cut vertex separating them.
23. **Cones over vertical chains (proved, in the cone problem).** For every vertical chain Q_m of 2-discs, RC(3) holds for the join context Cone(Q_m; c). The case Cone(D² ∨ D²; c), with two apex edges under non-point columns, is open for the same reason as question 1 below.

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

