# Problem: naturality of CaTT coherences at depth ≥ 2, round 8

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
    - The 2 × 2 grid of lax squares, where two 2-generators exchange without a cut vertex separating them, is settled in item 26.
23. **Cones over vertical chains (proved).** For every vertical chain Q_m of 2-discs, RC(3) holds for the join context Cone(Q_m; c). The case Cone(D² ∨ D²; c) is open; by item 25 it reduces to a context with four 2-generators.

24. **RC(3) on the full cylinder of D² ∗₀ D² (proved).** Let Γ = (D² ∗₀ D²)↑Var and Γ₀ its 2-skeleton (Γ without U_A, U_B). Then RC(3)(Γ₀) and RC(3)(Γ) hold, so K(Q, B, Var Q) = Fill_Γ(a_c, b_c) exists for every 3-dimensional coherence over the horizontal two-disc.
    - *Events.* The strict 2-cells x⁻ → z⁺ of Γ₀ are words in four events: A (uses a before F and a′ after), B (uses b before G and b′ after), G (p-paths f⁻g⁻Z to q-paths f⁻Yg⁺) and F (q-paths to r-paths Xf⁺g⁺), each used at most once, with G before F. The independent pairs are (A,B), (A,G) and (F,B).
    - *Orientation.* Orient the exchanges AB → BA, AG → GA and FB → BF. The measure m = [A before B] + [A before G] + [F before B] drops by one at each step. Left sides start in {A, F} and end in {B, G}, so they never overlap, and the only branching is AGFB, which closes with two disjoint swaps. This orientation agrees with right-column-first serialization at both nontrivial cuts y⁻ and y⁺. Sectors p → r have only the corners in common and hence one active column.
    - *Serialization and sorting.* Serialization comparisons ρ, χ and their 4-dimensional laws against multiplication are full coherences over genuine pasting contexts. Padded words are sorted, and the one new sorting diamond is the disjoint-swap diamond.
    - *U_A and U_B.* Normalising a single use of a generator gives sixteen unary representatives with fixed framings. A 3-term using both generators sequentialises into two unary terms with a middle pad, an endo-3-term of a framed corner S_ij = (v^{(i)} · K) · u^{(j)}, which RC(3)(Γ₀) removes. The two remaining routes B₇ ; A₇ and A₈ ; B₈ are exactly the boundary of item 21's interchange 4-cell.
25. **The 3-generator extension theorem (proved).** Let Λ have dimension ≤ 2 and an acyclic generating 1-graph, and let Γ = (Λ, z_1 : A_1 → B_1, …, z_k : A_k → B_k) with A_i, B_i parallel 2-terms of Λ. Then RC(3)(Γ) ⇔ RC(3)(Λ), with no restriction on number, order, whiskering or composability of the z_i.
    - *Method.* 3-terms modulo 4-terms form a category (4-terms of Γ and 3-terms of Λ are invertible, by the Benjamin–Markakis–Sarti criterion). Normalise each 3-term by RC(2) comparisons at both ends. For 2-terms F(X), G(X) in a fresh 2-variable X with equal strict image with X formal, RC(2) gives J(X), and depth-1 naturality of J in X (item 1) shows F and G whisker every 3-term to the same normalised arrow. Strict 3-cells are composites of elementary steps C[z_i] modulo replacement and adjacent exchange (Ara et al., *Polygraphs*, arXiv 2312.00429, App. D, Props. D.3.9 and D.3.12). Both moves preserve normalised evaluation.
    - *Consequence for cylinders.* For every pasting context Q of dimension ≤ 2 and every up-closed Y, Q↑Y has dimension ≤ 3 and an acyclic 1-graph, so RC(3)(Q↑Y) ⇔ RC(3) of its 2-skeleton. Items 19, 21 and 24's treatment of U_A, U_B are instances. For join contexts, RC(3)(Cone(Q; c)) ⇔ RC(3) of its 2-skeleton, and the horizontal cone Cone(D² ∨ D²; c) reduces to the context with vertices c, x, y, z, edges p_x, p_y, p_z, f, f′, g, g′ and 2-generators α, β, p_f, p_g.
26. **RC(3) for the 2 × 2 grid (proved).** In the Gray product of two paths of length 2 (faces oriented hv ⇒ vh), only two faces F, G are independent, and they are adjacent in every event word. Reassociating isolates F, G and the path factors between them in the two-square subcontext, which has a cut vertex where item 20's matrix normal form applies. This settles every fibre.
27. **The next-dimensional obligation.** For RC(4), after choosing 4-normalisers η_H : H → N(H) for 3-terms, compatibility with a 4-term K : H → H′ needs a 5-term η_H → K ∗₃ η_{H′}. Equivalently, the 4-fillers C(k,k′) supplied by RC(3) need 5-terms C(k₀,k₁) ∗₃ C(k₁,k₂) → C(k₀,k₂). The generic pasting-context instances exist by the coherence rule. The missing step is relative fusion after the chosen 3-normalisers have been substituted and expanded.

## 3. What remains, and why

By item 25, RC(3) on every cylinder Q↑Y with dim Q ≤ 2 is equivalent to RC(3) on its 2-skeleton, an acyclic 2-dimensional context. Items 10, 13, 17, 18, 20, 24 and 26 settle the 2-skeleta in which exchanges are separated by a cut vertex or can be isolated one at a time. The general case, with several exchanges between letters that are not adjacent in every event word, is open. 3-dimensional Q needs RC(4), which needs item 27's 5-dimensional compatibility.

Item 14 reduces Conjecture N to RC(n) on all cylinders.

## 4. Questions

Each question asks for explicit CaTT terms, built only with the coherence rule over pasting contexts and substitution.

1. **RC(3) on all 2-dimensional cylinder skeleta.** Prove RC(3) for the 2-skeleton of every Q↑Y with Q a pasting context of dimension ≤ 2 and Y up-closed, or give a counterexample. By item 25 this gives RC(3) on all these cylinders, hence Conjecture N for every 3-dimensional coherence. Natural next cases:
   - the full cylinder of D² ∗₀ D² ∗₀ D² (three horizontally composable discs);
   - the full cylinder of (D² ∗₁ D²) ∗₀ D²;
   - partial selections Y on D² ∗₀ D².
   A uniform route would be an orientation of exchanges that terminates, has closing critical branchings and agrees with serialization at every cut (as in item 24), together with relative fusion.
2. **The 3-disc.** Prove RC(4) on the cylinder of the 3-disc, or on (ΣD²)↑ΣY. Construct item 27's 5-dimensional compatibility, or show it fails.
3. **A 4-dimensional extension theorem.** Is there an analogue of item 25 one dimension up: for Λ of dimension ≤ 3 with RC(4), does adjoining 4-generators preserve RC(4)?
4. **All dimensions.** Prove RC(n) on all cylinders Q↑Y, including partial selections. By item 14, this proves Conjecture N at every depth.
5. **Global choice of K in dimension 3.** With the universal lower lifts of item 5, give one rule that picks K for every 3-dimensional coherence over every 2-dimensional pasting context Q, with Y = Var(Q), compatible with substitution. Two choices of K for the same (Q, B, Y) are 4-cells, and the minimal requirement is a **5-cell** between them (item 9).

## 5. What counts as a solution

Any of the following:
- explicit terms for question 1 or 5;
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

**Question 1 has a uniform affirmative answer.** Using the proved results in §2, in particular the 3-generator extension theorem, one obtains
\[
\boxed{\mathrm{RC}(3)(Q\uparrow Y)}
\]
for every pasting context \(Q\) and every up-closed \(Y\). The argument first proves RC(3) for the 2-skeleton. Its ordering rule works for arbitrary partial selections.

Consequently, **Conjecture N holds through dimension \(3\)**. This does not supply the 5-dimensional comparison required for RC(4) or for uniqueness of the choices of \(K\).

The priority is the **physical column number**. Within one physical column, the exact sequence of generator labels is retained. The new critical comparison is the braid for three independent events. The substitution argument requires an additional distinction: an internal sorting 3-cell is transported as a whole before a cross-column exchange is expanded into individual swaps.

I give the construction below, followed by a conditional answer to question 3.

## 1. The 2-skeleton of a partial cylinder

First suppose \(\dim Q\leq2\). Write \(Q\) as a horizontal sequence of vertical chains:
\[
Q=C_{m_1}*_0\cdots *_0C_{m_n}.
\]
Its variables are
\[
x_0,\ldots,x_n,
\]
\[
e_{i,j}:x_{i-1}\to x_i
\quad(0\leq j\leq m_i),
\]
and
\[
\alpha_{i,j}:e_{i,j-1}\Rightarrow e_{i,j}
\quad(1\leq j\leq m_i).
\]
The case \(m_i=0\) is allowed. Call \(i\) the *physical column* of these generators.

Put
\[
\Lambda=\operatorname{sk}_2(Q\uparrow Y).
\]

For unselected variables, superscripts \(+\) and \(-\) denote the same retained variable. For selected variables, they denote distinct copies. Write \(v_i:x_i^-\to x_i^+\) when \(x_i\in Y\).

The 2-generators of \(\Lambda\) are exactly:

1. The retained \(\alpha_{i,j}\), when \(\alpha_{i,j}\notin Y\).
2. The distinct copies
   \[
   \alpha_{i,j}^{\pm}:
   e_{i,j-1}^{\pm}\Rightarrow e_{i,j}^{\pm},
   \]
   when \(\alpha_{i,j}\in Y\).
3. For every selected \(e_{i,j}\), its cylinder generator
   \[
   r_{i,j}:e_{i,j}^-d_i\Rightarrow d_{i-1}e_{i,j}^+,
   \tag{1}
   \]
   where \(d_i=v_i\) if \(x_i\) is selected, and otherwise \(d_i\) is the empty path.

Formula (1) describes boundary **words**. An empty \(d_i\) means literal omission of that factor in the CaTT type.

All these 2-generators have physical column \(i\). Each has exactly one horizontal 1-generator of column \(i\) in each 1-boundary.

The copies \(\alpha^-_{i,j},\alpha^+_{i,j}\) remain distinct labels even when their boundaries are identical. Selecting a 2-variable without selecting either boundary edge therefore introduces two alternatives, not an equation between them.

## 2. Rank, exchanges, and normal words

Assign ranks
\[
\operatorname{rk}(x_i)
=\operatorname{rk}(x_i^-)
=\operatorname{rk}(x_i^+)=i.
\]

Horizontal edges increase rank by one. Vertex connectors \(v_i\) preserve rank. Thus every strict 1-path traverses a physical column at most once.

An elementary 2-event is an application of one generating 2-cell to a contiguous factor of the current strict 1-path.

### 2.1 Every legal ascending pair exchanges

Consider consecutive events
\[
A_iB_j,\qquad i<j,
\tag{2}
\]
where subscripts indicate physical columns.

If \(j\geq i+2\), their rewritten factors are disjoint. If \(j=i+1\) and at least one event is an \(\alpha\)-event, the factors are again disjoint: an \(\alpha\)-event changes only its horizontal edge.

The remaining possibility consists of two adjacent cylinder events.

If \(x_i\notin Y\), there is no \(v_i\), so their factors are disjoint.

If \(x_i\in Y\), the order (2) is impossible. The left cylinder event requires a source factor
\[
e_{i,a}^-v_i.
\]
The horizontal edge immediately following this factor starts at \(x_i^+\), so it is a plus copy. Applying the left event does not change that edge. The right cylinder event, however, requires a minus copy starting at \(x_i^-\). Up-closure makes these copies distinct.

Therefore:

> **Adjacent inversion lemma.** Every legal consecutive pair with strictly increasing physical-column indices is an independent exchange.

The interacting order of adjacent cylinder events is right before left, which already has decreasing column order.

This argument allows multiple cylinder events at different heights in one physical column. Partial selections can permit that; their existing order is preserved.

### 2.2 Stable column sorting

Orient exchanges by
\[
A_iB_j\longrightarrow B_jA_i
\qquad(i<j).
\tag{3}
\]
The measure
\[
I(w)=\#\{(p,q):p<q,\ \operatorname{col}(w_p)<\operatorname{col}(w_q)\}
\]
decreases by one at every step.

The terminal word is
\[
n(w)=w_nw_{n-1}\cdots w_1,
\tag{4}
\]
where \(w_i\) is the original subsequence of labels in physical column \(i\).

There are exactly two kinds of local branching:

- two disjoint swaps;
- overlapping swaps on
  \[
  A_iB_jC_k,\qquad i<j<k.
  \]

In the second case the outer events are in nonadjacent columns. All three applications are simultaneously disjoint, giving the usual two routes
\[
ABC\to BAC\to BCA\to CBA,
\]
\[
ABC\to ACB\to CAB\to CBA.
\tag{5}
\]

No equal-column exchange is possible: every event in column \(i\) uses the unique horizontal position \(i\) in the current path.

Consequently, **the strict 1-source path together with the ordered column subsequences classifies a strict 2-cell**. The source path is necessary: empty words on different paths are different identity cells. Once the source path is fixed, each generator label has at most one application position, so the sorted word determines all its strict whiskering factors.

### 2.3 Cuts preserve the ordering

Suppose a substituted horizontal factorization has successive 0-boundaries
\[
z_0,z_1,\ldots,z_s,
\qquad b_a=\operatorname{rk}(z_a).
\]
Every event assigned to its \(a\)-th factor has physical column in
\[
(b_{a-1},b_a].
\tag{6}
\]

Indeed, its horizontal edge is a factor of a path from \(z_{a-1}\) to \(z_a\), and rank is nondecreasing along that path.

These half-open intervals are disjoint and ordered. Thus:

- events assigned to distinct reference columns cannot interleave their physical columns;
- serializing reference columns right to left agrees with physical-column sorting;
- a repeated rank contributes no 2-events.

A repeated-rank factor need not be a point. It can be the path \(v_i:x_i^-\to x_i^+\). This case uses inactive **path** factorization, separately from point absorption.

This is the substitution property needed below.

## 3. CaTT terms for the new critical diagrams

Write
\[
a\cdot b=a*_1b,\qquad H;K=H*_2K.
\]
For parallel full terms on a genuine pasting context \(P\), write
\[
[s,t]_P=\operatorname{coh}_{P,s\to t}[\mathrm{id}].
\]

Use the padded word convention of §2 item 17, retaining every prescribed \(\kappa\), including \(\kappa(U,U)\).

### 3.1 The three-event braid

Take
\[
P=D^2(u)*_0D^2(v)*_0D^2(w),
\]
with
\[
u:a_0\Rightarrow a_1,\quad
v:b_0\Rightarrow b_1,\quad
w:c_0\Rightarrow c_1.
\]

Fix the literal 1-source and target
\[
(a_0*_0b_0)*_0c_0,
\qquad
(a_1*_0b_1)*_0c_1.
\]

For each permutation \(\pi\), form the serialized 2-term \(S_\pi\) by applying its three events in that order. At state \((i,j,k)\), the three possible raw factors are
\[
(u*_0b_j)*_0c_k,\qquad
(a_i*_0v)*_0c_k,\qquad
(a_i*_0b_j)*_0w.
\]
Their boundaries are the corresponding left-associated 1-paths. Insert the fixed path comparisons required by the padded-word convention.

Use the binary exchange construction to obtain the two three-swap paths
\[
\begin{aligned}
L:\quad
S_{uvw}&\longrightarrow S_{vuw}
\longrightarrow S_{vwu}
\longrightarrow S_{wvu},\\
R:\quad
S_{uvw}&\longrightarrow S_{uwv}
\longrightarrow S_{wuv}
\longrightarrow S_{wvu}.
\end{aligned}
\]
They are literally parallel 3-terms. Each uses \(u,v,w\) and their boundaries. Hence
\[
\boxed{\beta_{u,v,w}=[L,R]_P}
\tag{7}
\]
is a 4-term.

If the actual three events have intervening path factors, retain those factors between the three discs. The same full-support argument applies. Substitute the actual events only after constructing (7).

### 3.2 Disjoint swaps

Retain the intervening 2-word as a formal argument \(k\). On
\[
P=D^3(s)*_1D^2(k)*_1D^3(t),
\]
with \(s:S_0\Rightarrow S_1\) and \(t:T_0\Rightarrow T_1\), compare
\[
\begin{aligned}
D_1&=((s*_1k)*_1T_0);
      ((S_1*_1k)*_1t),\\
D_2&=((S_0*_1k)*_1t);
      ((s*_1k)*_1T_1).
\end{aligned}
\]
Their common 2-source and target are
\[
(S_0\cdot k)\cdot T_0,
\qquad
(S_1\cdot k)\cdot T_1.
\]
Thus
\[
[D_1,D_2]_P
\tag{8}
\]
gives the disjoint-swap square, including the case where \(k\) is subsequently assigned an identity.

Equations (7) and (8) give a constructive comparison between any two sorting paths: compare their first reductions by the appropriate local diagram, then recurse on the smaller inversion number. No comparison between the resulting 4-cells is required.

## 4. Serialization for arbitrarily many reference columns

Two further comparisons extend the binary evaluator to arbitrary products.

### 4.1 Transport a whole internal sort

On \(D^2(U)*_0D^2(V)\), use the right-first serialization
\[
R(U,V)
=(1_{\sigma U}*_0V)\cdot(U*_01_{\tau V}),
\]
and its full coherence
\[
\rho_{U,V}:U*_0V\Rightarrow R(U,V).
\]

For a generic 3-cell \(h:U\Rightarrow U'\), work on
\[
D^3(h)*_0D^2(V).
\]
Let
\[
R(h,V)
=(1_{\sigma U}*_0V)*_1(h*_01_{\tau V}).
\]
Then
\[
(h*_0V);\rho_{U',V}
\quad\text{and}\quad
\rho_{U,V};R(h,V)
\]
are full parallel 3-terms. Their comparison is therefore a 4-coherence on that genuine pasting context:
\[
\boxed{
\mathsf{Nat}_\rho(h,V):
(h*_0V);\rho_{U',V}
\Longrightarrow
\rho_{U,V};R(h,V).
}
\tag{9}
\]
There is a corresponding comparison for the right argument.

In (9), substitute the **entire** internal normalization or sorting 3-cell for \(h\). The comparison does not require that its individual swaps be expressible on a formal vertical chain.

This is a depth-1 naturality instance, also covered by BMOSV Theorem 3.1. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

### 4.2 Product parenthesization, with actual boundary framing

Let
\[
P=C_M*_0C_N*_0C_L,
\]
and let \(A,B,C\) be the selected full column words.

The terms
\[
H_\ell=(A*_0B)*_0C,
\qquad
H_r=A*_0(B*_0C)
\]
need not be parallel as 2-terms. Choose the path associator at the source and the reverse associator at the target:
\[
\alpha_s:\sigma H_\ell\Rightarrow\sigma H_r,
\qquad
\bar\alpha_t:\tau H_r\Rightarrow\tau H_\ell.
\]
Set
\[
H_r^{\mathrm{fr}}
=(\alpha_s\cdot H_r)\cdot\bar\alpha_t,
\qquad
a=[H_\ell,H_r^{\mathrm{fr}}]_P.
\tag{10}
\]

Fix one padded right-first 2-word \(S\), with the literal 1-boundaries of \(H_\ell\).

Construct:

- \(L_\rho:H_\ell\Rightarrow S\), using the left binary serialization recipe;
- \(R_\rho:H_\ell\Rightarrow S\), using \(a\), the framed right binary recipe, and the full 3-coherence from its resulting padded word to \(S\).

Both are explicit 3-terms formed from the binary recipes and path comparisons. Both use every marked variable of \(P\). Hence
\[
\boxed{\Omega_{M,N,L}=[L_\rho,R_\rho]_P}
\tag{11}
\]
is the required 4-cell.

The same construction compares multiplication recipes after their source and target have been framed identically. For finitely many columns, fix a sequence of adjacent parenthesis rotations and apply (11) at each rotation. This constructs a particular 4-comparison; it does not require a 5-dimensional coherence between rotation sequences.

### 4.3 Refinement of a block exchange

Suppose two normalized blocks have serial entries
\[
U=u_1\cdots u_M,\qquad
V=v_1\cdots v_N.
\]
After whole internal sorts have been moved using (9), regard these entries as independent marked variables of
\[
C_M*_0C_N.
\]

The whole-block exchange and the sequence of its \(MN\) elementary crossings are parallel full 3-terms on that genuine pasting context. Their comparison is a 4-coherence there, formed before evaluation.

Every evaluated crossing is legal: by (6), every physical column used by the left block lies left of every physical column used by the right block.

The order of this construction is essential:

1. Normalize a child as a whole.
2. Move its whole normalization 3-cell through the outer operation by (9).
3. Expand the resulting serial word into marked variables.
4. Refine cross-block exchanges.
5. Compare any remaining sorting routes using (7) and (8).

An internal physical-column permutation is never asserted to be a permutation of the slots of a formal \(C_M\).

## 5. Normalizers and evaluation fusion

For a strict 2-cell \(\delta\), its normal data consists of its strict 1-source and its exact column words. Let \(n(\delta)\) be the decreasing-column serialization.

For a word \(w=e_1\cdots e_k\), use
\[
\begin{aligned}
\langle w\rangle_{A,B}
=\operatorname{LF}\bigl[
&\kappa(A,S_{e_1}),E_{e_1},
\kappa(T_{e_1},S_{e_2}),E_{e_2},\ldots,\\
&E_{e_k},\kappa(T_{e_k},B)
\bigr],
\end{aligned}
\tag{12}
\]
where \(E_e\) is the fixed raw whiskered generator, and
\(S_e=\sigma E_e,\ T_e=\tau E_e\).
The empty word uses the fixed path normal form.

Define
\[
N_\delta(A,B)=\langle n(\delta)\rangle_{A,B}.
\]

Vertical multiplication is
\[
\mu_{\delta,\epsilon}
=
\mu^{\mathrm{flat}}_{\delta,\epsilon};
\operatorname{sort}_{n(\delta)n(\epsilon)}.
\tag{13}
\]
The flat fold is the construction already proved in §2 item 17.

The associativity 4-cell for (13) is constructed as follows:

1. Use flat-fold associativity and the path-fold comparisons to put both routes over the same padded concatenation.
2. Move whole internal sorting cells past the outer operations using (9) and the corresponding vertical whole-slot laws.
3. Compare the resulting sorting paths using (7)–(8).

The same procedure supplies unit and subdivision comparisons.

### 5.1 Retained heads

Every \(0\)-column of a pasting context of dimension at most three has the form
\[
C_m
\quad\text{or}\quad
V_m(k_1,\ldots,k_m).
\]
Here \(V_m(\mathbf k)\) retains all parallel 2-variables in each slot and every intervening 3-link; the \(k_i\) are arbitrary nonnegative integers.

For a head substitution:

- copy every active original column completely;
- replace each inactive column by its literal actual path context, using §2 items 12 and 16.

This gives a genuine pasting context \(R\) and a literal factorization
\[
\gamma=\kappa[\eta].
\tag{14}
\]

Activity is determined by the assigned strict 2-values. In a 3-head, a retained column keeps all its 3-links even though those links evaluate to identity strict 3-cells in \(\Lambda\).

For a 2-head put
\[
H=\operatorname{coh}_{P,A}[\kappa].
\]
Choose the fixed reference expression \(B_H\), using all retained marked variables and having the same literal 1-boundaries as \(H\). Then
\[
v_H=[H,B_H]_R,
\qquad
\nu_T=v_H[\eta];D_{B_H,\eta}.
\tag{15}
\]

### 5.2 The evaluator

The evaluator has the following finite clauses.

| Reference expression | Evaluation |
|---|---|
| Marked 2-variable | Its proper-child normalizer |
| Path comparison or identity | The proved path evaluator |
| Vertical product | Child evaluations followed by (13) |
| Horizontal product | Child evaluations, right-first serialization, and the framed product comparisons |
| Inactive nonpoint column | Literal path factorization and the path comparison \(\zeta\) |
| Point column | Point absorption before the surviving marked argument is evaluated |

For the last clause, with \(q:\ell_0\Rightarrow\ell_1\) a term over a point, use
\[
B_q(z):
q*_0z
\Rightarrow
\bigl(\kappa(\ell_0*_0s,s)\cdot z\bigr)
\cdot\kappa(t,\ell_1*_0t),
\qquad z:s\Rightarrow t.
\tag{16}
\]
This is a full coherence on \(D^2(z)\). Its naturality is formed on \(D^3(h)\). Thus \(z\) can later be assigned a term using an arbitrarily large part of the cylinder.

If a column has equal endpoint ranks but evaluates to \(v_i\), use the inactive nonpoint-path clause, not (16).

### 5.3 Fusion

For a relative 2-term \(u\), let
\[
\lambda_u:u\Rightarrow B_u
\]
be the recursive relative normalizer. The required comparison is
\[
\Phi_{u,\sigma}:
\nu_{u[\sigma]}
\Longrightarrow
\lambda_u[\sigma];D_{B_u,\sigma}.
\tag{17}
\]

Construct it by induction on the syntax of \(u\).

**Variable.** Use the insertion and unit 4-cell on \(D^3(h)\), with
\[
h=\nu_{\sigma z}.
\]
Even when \(B_z=z\), the comparison with \(1_z;\nu_{\sigma z}\) is a unit 4-cell, not syntactic equality.

**Path expression.** Use literal path fusion.

**Vertical product.** Apply child fusion, whole-slot naturality, the multiplication comparison for (13), and the sorting-path comparison.

**Horizontal product.** Apply child fusion and (9). Refine the cross-block shuffles only afterward. Equation (6) guarantees that their order agrees with global physical-column order. Use (11) for different parenthesizations.

**Coherence head.** Use the literal factorization (14). Move child normalizers through the generic head comparison while their arguments remain whole. Expand their resulting serial words into genuine products of marked vertical chains. Compare the structural recipes there by full coherences, and compare their actual sorting continuations by (7)–(8).

If a column becomes inactive under further substitution, first reflect it literally into its path context. If it becomes point-supported, apply (16) before evaluating the surviving arguments. The resulting head comparison is on the surviving genuine product of chains and paths.

These are all cases. The rank intervals in (6) are what make the horizontal induction valid for an arbitrary number of reference columns.

## 6. From fusion to RC(3) of the 2-skeleton

For a retained 3-head
\[
H:S\Rightarrow T
\]
on a genuine frame \(R\), form
\[
\lambda_S:S\Rightarrow B_S,
\qquad
\lambda_T:T\Rightarrow B_T.
\]
Let
\[
W:B_S\Rightarrow B_T
\]
update every retained formal 3-link. Slots with no 3-link contribute identity 3-terms.

Then
\[
H;\lambda_T
\quad\text{and}\quad
\lambda_S;W
\]
are parallel and full in \(R\). The first uses every retained variable through \(H\); the second uses every retained 3-link through \(W\), as well as all remaining marked slots. Hence
\[
\Xi_H=[H;\lambda_T,\lambda_S;W]_R
\tag{18}
\]
is an admissible 4-term.

Evaluate (18), apply fusion (17), and use the comparisons for the proper 3-arguments. Structural induction gives
\[
\Lambda_G:
G;\nu_T\Longrightarrow\nu_S
\tag{19}
\]
for every 3-term \(G:S\Rightarrow T\) of \(\Lambda\).

The normalizers \(\nu_T\) have reverse terms and 4-dimensional cancellation comparisons. Each primitive is a coherence between full 2-terms on a genuine pasting context; reverse it there, and form the cancellation comparison there before substitution.

For parallel \(G,G':S\Rightarrow T\), compose
\[
G;\nu_T
\xRightarrow{\Lambda_G}
\nu_S
\xRightarrow{\overline{\Lambda_{G'}}}
G';\nu_T
\]
and cancel \(\nu_T\). This defines the recursive term
\[
\boxed{\operatorname{Fill}_{\Lambda}(G,G'):G\longrightarrow G'.}
\tag{20}
\]

Thus
\[
\boxed{\mathrm{RC}(3)\bigl(\operatorname{sk}_2(Q\uparrow Y)\bigr)}
\]
holds uniformly for every \(Q\) of dimension at most two and every up-closed \(Y\).

The construction applies to all three proposed next cases: three horizontal discs, a vertical pair followed horizontally by a disc, and arbitrary partial selections on the horizontal two-disc.

## 7. Arbitrary arities and Conjecture N through dimension 3

The argument also allows several distinct parallel generators
\[
\alpha_{i,j,\ell}:e_{i,j-1}\Rightarrow e_{i,j}
\]
at a vertical step. They simply give distinct labels in the preserved column word.

This describes the 2-truncation of an arbitrary-dimensional pasting context. Induction on the pasting rules gives:

- extending a focused 1-variable creates the next 1-level and a 2-generator to that level;
- extending a focused 2-variable adds a parallel 2-variable with the same adjacent 1-boundaries;
- higher extensions add no variables of dimension at most two;
- descending the focus does not return to an earlier 1-level.

Therefore the rank and sorting proof applies to
\[
\operatorname{sk}_2(Q\uparrow Y)
\]
for arbitrary-dimensional \(Q\).

Its generating 1-graph is acyclic. For example, grade \(x_i^-\) by \(2i\), \(x_i^+\) by \(2i+1\), and an unselected \(x_i\) by \(2i\). Every generating 1-cell increases grade.

Apply the proved 3-generator extension theorem to obtain
\[
\mathrm{RC}(3)\bigl(\operatorname{sk}_3(Q\uparrow Y)\bigr).
\]
A 3-term uses no generators above dimension three, and adjoining higher generators does not change equality of strict 3-cells. The same fillers therefore give
\[
\boxed{\mathrm{RC}(3)(Q\uparrow Y)}
\tag{21}
\]
for every pasting \(Q\) and up-closed \(Y\).

Now apply §2 item 3.

For a 3-dimensional **coherence** constructor,
\[
K(Q,B,Y)=\operatorname{Fill}_{Q\uparrow Y}(a_c,b_c).
\]
For a 3-dimensional **composition** constructor, use the specified realization of the strict cylinder as layers, and use (20) to connect consecutive 3-boundaries and the two endpoints.

Hence
\[
\boxed{\text{Conjecture N holds in dimensions }0,1,2,3.}
\]

Fixing the bracketing conventions, path comparisons, leftmost-inversion sorting, and the displayed generic coherences gives one rule for these choices. The substitution compatibility of the resulting naturality operation is the recursive compatibility in §1.4 and the fusion construction above. A 5-cell between different choices remains a separate requirement.

## 8. A conditional 4-dimensional extension theorem

For question 3, the same extension argument gives the following precise result:

> Let \(\dim\Lambda\leq3\), with acyclic generating 1-graph. If both \(\mathrm{RC}(3)(\Lambda)\) and \(\mathrm{RC}(4)(\Lambda)\) hold, then adjoining arbitrary 4-generators preserves RC(4).

Here is the construction.

First, use RC(2) for lower-boundary transports and RC(3) to choose 4-normalizers for old 3-terms. Work with 4-terms modulo 5-terms. After transport to these normal representatives, every old 4-term becomes an identity by RC(4) of \(\Lambda\).

For a fresh 3-variable \(X\), item 25 implies
\[
\mathrm{RC}(3)(\Lambda,X:s\to t):
\]
both contexts are 3-generator extensions of their common 2-skeleton.

Consequently, if two elementary 3-contexts satisfy
\[
\pi F(X)=\pi G(X),
\]
choose
\[
J(X):F(X)\longrightarrow G(X)
\]
in dimension four. Depth-1 naturality of \(J\) in the top-dimensional variable \(X\) gives a 5-term. Substitute
\[
X^-=A_i,\qquad X^+=B_i,\qquad X^\uparrow=z_i.
\]
This compares the two elementary actions on the adjoined 4-generator \(z_i\). The boundary factors \(J(A_i),J(B_i)\) are old 4-terms, so RC(4) of \(\Lambda\) removes them after transport.

Adjacent independent 4-generators are handled by the generic interchange 5-term. Replacement of equal elementary contexts and exchange of adjacent independent atoms generate strict equality: this is the molecular presentation in *Polygraphs*, Appendix D, Propositions D.3.9 and D.3.12. [arxiv.org](https://arxiv.org/pdf/2312.00429?utm_source=chatgpt.com)

This proves the stated conditional theorem.

It does **not** prove the assertion from RC(4) alone. That assumption compares existing parallel 4-terms; it does not supply the 4-terms \(J(X)\) between 3-contexts or the endpoint normalizers used above.

## 9. Verification and remaining scope

The generic term checks verified literal boundaries and full support for:

- the three-event braid;
- the framed three-column product comparison;
- serialization naturality in a whole 3-argument.

Finite rewriting checks also covered every up-closed selection in the three proposed small shapes: 40 selections for the horizontal two-disc, 208 for three horizontal discs, and 88 for a vertical pair followed by a disc. All legal ascending event pairs exchanged, and all tested ascending critical triples admitted the six execution orders with the same result. These are checks of the construction, not a complete CaTT implementation.

The result establishes question 1 and Conjecture N through dimension three. It does not establish RC(4) for the 3-disc cylinder, preservation under adjoining 4-generators from RC(4) alone, or the 5-dimensional comparison between arbitrary choices of \(K\).
