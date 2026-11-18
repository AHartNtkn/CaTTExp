# Relative coherence in CaTT: dimension 2, and what it gives for Gray contexts and naturality

*Thread "Prove naturality and Gray context conjectures", 2026-11-18. Paper proofs, not yet independently checked. They extend the verified relative ladder theorem (`conjectures/naturality-arbitrary-depth.md`, researcher response and verification) and reuse its steps wherever they apply unchanged. The open remainder is stated for researchers in `conjectures/outbox/naturality-arbitrary-depth.md` and `conjectures/outbox/gray-contexts.md`.*

Ledger items addressed: D1 (closed), D2 (existence in G(3); rest reduced), C1 (dimension ≤ 2 closed; rest reduced), D3, D3a, D4, C2 (progress).

## 0. Summary

| Result | Status |
|---|---|
| **Theorem A.** RC(2) holds in every CaTT context: parallel 2-terms with equal strict image are connected by a 3-term (both directions). | proved here (§2); the 2-molecule case was proved independently by a referee, verified (`conjectures/gray-contexts-in-catt.md`) |
| G(2), existence and uniqueness, for every 2-molecule (D1) | proved (§3.1) |
| Existence in G(3), hence every Gray generator of dimension ≤ 4 has a CaTT type | proved (§3.2); also by the referee, by padding |
| Existence in G(n) ⇐ RC(n−1); uniqueness in G(n) ⇐ RC(n) | proved (§3.3) |
| **Reduction.** N for coherences of dimension n ⇐ RC(n) on the cylinder contexts `Q↑Y` | proved (§4.1) |
| N for every term of dimension ≤ 2, every pasting context Q, every up-closed Y (includes arbitrary up-closed Y on a chain) | proved (§4.2) |
| `Γ ⊗ D¹` for every context of dimension ≤ 3; `Γ ⊗ Dⁿ` for all n when dim Γ ≤ 2, by iterated top-layer cylinders | proved, given BMOSV (§5) |
| Support lemma; "G implies N" repaired for full Y (D3a) | proved (§4.3) |
| G2 for the D¹ factor (lifts commute with substitution) | proved (§6) |
| G5: linearity is not needed | answered (§6) |
| G4: associativity up to invertible cells | reduced to RC (§6) |
| RC(3) fails for non-loop-free contexts (Eckmann–Hilton) | sketch (§7) |
| RC(n), n ≥ 3, for loop-free contexts | **open**, sent out |

## 1. Notation

CaTT as in `conjectures/naturality-arbitrary-depth.md` §1. For a context Γ, `F(Γ)` is the free strict ω-category on Γ read as a polygraph, and `π(t)` is the strict image of a term t. Strict ω-categories model CaTT, and in a strict ω-category any two full parallel terms over a pasting context are equal, so π is well defined and every coherence cell has an identity as strict image.

> **RC(n) for Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

"Connected" always means: a term built from substituted coherences. Such terms are invertible (Benjamin–Markakis–Sarti, arXiv 2406.12127), so RC is symmetric.

RC(1) holds in every context. A 1-term's strict image is its flattened path (a word in 1-variables; identities flatten to the empty word). Two 1-terms with the same endpoints and the same path w are full parallel terms over the chain context `C(w)`, pulled back along the evident substitution `ι_w : C(w) → Γ`, so the coherence rule gives `κ_w(a, b) : a → b`. This is §2.1 of the researcher response, with no assumption on Γ.

## 2. Theorem A: RC(2) in every context

**Theorem A.** For every CaTT context Γ and parallel 2-terms `T, T′ : A ⇒ B` with `π(T) = π(T′)`, there are 3-terms `T ⇛ T′` and `T′ ⇛ T`.

The proof follows the ladder theorem's proof. Two things change. Kind (I) factors are handled uniformly by Lemma P, and the forced order of generators is replaced by exchange moves (Step 5).

### Step 1. Pulling back terms without 2-variables

**Lemma P.** Let Φ be a 2-term of Γ with no 2-variable in `Var(Φ)`, and let w be the flattened path of `σΦ`. Then:
- `π(σΦ) = π(τΦ)`, so `τΦ` also has path w;
- `Φ = Φ̃[ι_w]` for a 2-term `Φ̃` over `C(w)` whose type is full in `C(w)`.

Hence the coherence rule over `C(w)` connects Φ, in both directions, to any other such term with the same boundary, in particular to `κ^{(2)}_w := coh_{C(w), …}[ι_w]` and, when `σΦ ≡ τΦ`, to `id_{σΦ}`.

*Proof.* `π(Φ)` is a strict 2-cell with no 2-generator, hence an identity, which gives the first claim. For the second, induct on Φ. If `Φ = coh_{P,B}[γ]`, every 1-variable of P is sent by γ to a 1-term whose strict image is a segment of w. The position of that segment is fixed by the pasting structure of P: columns follow each other along w, and cells in one column all map to the same segment, since their strict images are equal. Every 2-variable of P is sent to a 2-term without 2-variables, which pulls back by induction. Assembling gives `γ̃ : C(w) → P`-shaped data, i.e. `Φ̃ := coh_{P,B}[γ̃]` over `C(w)`, with `Φ = Φ̃[ι_w]`. Its type is `σ̃Φ → τ̃Φ`, and both sides are 1-terms that traverse all of w, so the type is full. Repeated vertices or edges in w cause no problem: positions are indices along w, not vertices of Γ. ∎

### Step 2. Sequentialization

This is §2.2 of the response, which uses nothing about the context. Every 2-term T is connected, in both directions, to a vertical composite `T_seq` whose factors are of two kinds:
- **(G)** an iterated whiskering of a single 2-variable x by 1-terms;
- **(I)** a 2-term with no 2-variable.

`π(T_seq) = π(T)`, since the connecting cells are coherences. By Lemma P, every maximal run of consecutive (I)-factors from a to b is connected to `κ^{(2)}_w(a, b)`. When a and b are syntactically equal, it is connected to `id_a`, and that identity is then removed with a 3-dimensional unitor over a 2-disc.

### Step 3. Normal form of a whiskered generator

Fix, for each path w, one bracketed 1-term `B_w` with path w: say right-nested binary composites, and `id_v` for the empty path at v. A **whiskered generator** is a triple `g = (λ, x, ρ)` with λ, ρ paths and x a 2-variable. Its source path is `λ·⌊σx⌋·ρ` and its target path is `λ·⌊τx⌋·ρ`.

Let `P_g` be the pasting context made of a chain with |λ| edges, a 2-disc `Z : z⁻ ⇒ z⁺`, and a chain with |ρ| edges. Let `N_g(z)` be the right-nested composite of the 1-dimensional context `D_g` (prefix, z, suffix), and let `H_g := coh_{P_g, N_g(z⁻) → N_g(z⁺)}[id]`. This is a composition coherence, since each side is full in the corresponding boundary. Let `θ_g` send the chains to the edges of λ and ρ, `z^± ↦ σx, τx`, and `Z ↦ x`. Define

```
e_g := κ(B_{λ⌊σx⌋ρ}, N_g(σx)) ∗₁ H_g[θ_g] ∗₁ κ(N_g(τx), B_{λ⌊τx⌋ρ})  :  B_{λ⌊σx⌋ρ} ⇒ B_{λ⌊τx⌋ρ}
```

where each κ is the 2-cell of Lemma P over the expanded path.

**Lemma G.** Every 2-term W of either of the following forms, whose generator data is g and whose boundary is `a ⇒ b`, is connected in both directions to `κ(a, B) ∗₁ e_g ∗₁ κ(B′, b)`:
- (i) an iterated whiskering of x by 1-terms;
- (ii) `coh_{P′}[θ′]` with P′ a column pasting context (chain, one 2-disc, chain), `θ′(Z) = x`, and the chains sent to 1-terms.

*Proof.*
- (i) This is §2.5 of the response, verbatim. Abstract x to Z and σx, τx to z^±; compare over `P_g`; compare the outer factors over the expanded paths.
- (ii) Let `ς : P_g → P′` send each prefix edge of `P_g` to the corresponding edge of the pull-back of the 1-term `θ′(prefix edge)` along `ι` (Step 1), and similarly for the suffix, with `z^±, Z` fixed. Then `W = (coh_{P′}[ς])[θ_g]`. Both `coh_{P′}[ς]` and `κ ∗ H_g ∗ κ` (taken over `P_g`, before substitution) are 2-terms over the pasting context `P_g`. Their only 2-variable is Z, and their types are full in `P_g`. After adjusting endpoints by κ's over `D_g[z^±]`, the coherence rule over `P_g` connects them. Substitute `θ_g`. ∎

Applying Lemma G to every (G)-factor of `T_seq`, and Step 2 to the runs between them, gives

```
T  ⇄  𝒩(T) := κ(A, B_{w₀}) ∗₁ e_{g₁} ∗₁ e_{g₂} ∗₁ ⋯ ∗₁ e_{g_k} ∗₁ κ(B_{w_k}, B)
```

with one fixed vertical bracketing. Here `g₁ … g_k` is the **2-path** of `T_seq`: its sequence of whiskered generators, with whisker paths read off from strict images. For k = 0, `𝒩(T) = κ(A, B)`.

### Step 4. Exchange

**Fact (free 2-categories on 2-polygraphs).** Two 2-paths of whiskered generators represent the same 2-cell of the free 2-category iff they are related by a finite sequence of **exchange moves**

```
(λ, x, μ⌊σy⌋ρ) · (λ⌊τx⌋μ, y, ρ)   ~   (λ⌊σx⌋μ, y, ρ) · (λ, x, μ⌊τy⌋ρ).
```

The free 2-category is the free sesquicategory, whose 2-cells are exactly the 2-paths, quotiented by the interchange law. Interchange for composite 2-cells follows from interchange for whiskered generators. See Ara–Burroni–Guiraud–Lafont–Métayer, *Polygraphs*, arXiv 2312.00429, §4.1.5–4.1.8 (Lemma 4.1.6: a 2-polygraph induces a sesquicategory of 2-paths; Prop. 4.1.7: a 2-category is a sesquicategory satisfying exchange; the free 2-category is the quotient (4.7) of the free sesquicategory by exchange) **[paper, G1 check]**. `π(T)` is the class of the 2-path of `T_seq`.

**Lemma E.** For each exchange move there are 3-cells in both directions between `e_{g₁} ∗₁ e_{g₂}` and `e_{g₂′} ∗₁ e_{g₁′}`, where g₁, g₂ and g₂′, g₁′ are the two sides of the move.

*Proof.* Let E be the pasting context made of a chain |λ|, a 2-disc `Z₁ : z₁⁻ ⇒ z₁⁺`, a chain |μ|, a 2-disc `Z₂`, and a chain |ρ|. Over E, let `L` be the composite "column coherence on `Z₁`, then column coherence on `Z₂`", with κ-adjustments over E's 1-dimensional boundaries, and let `R` be the same with `Z₂` first. These are parallel, after the same outer κ's, and both are full in E, so the coherence rule gives `L ⇄ R` over E. Substitute `θ_E` (`z₁^± ↦ σx, τx`, `Z₁ ↦ x`, and likewise for y). The factors of `L[θ_E]` are of kind (ii) of Lemma G (for x and for y) or of kind (I), so Lemma G and Step 2 connect `L[θ_E]` to `κ ∗ e_{g₁} ∗ e_{g₂} ∗ κ`, and similarly for R. The outer κ's are 2-cells between syntactically equal 1-terms, so Lemma P removes them. ∎

### Step 5. Assembly

Since `π(T) = π(T′)`, the 2-paths of `T_seq` and `T′_seq` are related by exchange moves. So

```
T ⇄ 𝒩(T) ⇄ ⋯ ⇄ 𝒩(T′) ⇄ T′
```

where each middle step whiskers a cell of Lemma E by the rest of the normal form (a 3-cell whiskered by 2-cells via ∗₁) and reassociates with 3-dimensional associators over vertical chains of 2-discs. ∎

**Remarks.**
- No hypothesis on Γ is used. The ladder theorem (a cylinder of a chain, `Y = Var(Q)`) is the special case where every exchange class has one element.
- Eckmann–Hilton in dimension 2 is consistent with this. In `(x, a, b : id_x ⇒ id_x)`, `a ∗₀ b` and `b ∗₀ a` have equal strict images, and the Eckmann–Hilton 3-cell connects them. Theorem A reconstructs such a cell from one exchange move, where both whiskers are empty paths at x.

## 3. Gray contexts: G(2), existence in G(3), the general pattern

The definitions are those of `conjectures/gray-contexts-in-catt.md` §1–§2.

### 3.1 G(2) (closes D1)

Let U be a 2-molecule presented in CaTT.
- **Uniqueness.** Let t be a U-composite. Its strict image is a strict 2-cell `∂⁻U ⇒ ∂⁺U` of `F(U)`, represented by a 2-path. That 2-path uses each 2-cell of U exactly once. Its 2-chain c (counting uses) satisfies `∂c = [∂⁺U] − [∂⁻U]`, and the 2-cycles of a molecule are 0: molecules are contractible, so `Z₂ = H₂ = 0` for a 2-dimensional regular complex (no general citation located; for regular 2-molecules this is proved directly by the verified referee argument in `conjectures/gray-contexts-in-catt.md`, verification §2.4: `∂₂` is injective, by taking a flow-minimal face with non-zero coefficient and one of its input edges). So c is the sum of all 2-cells.
  - A 2-path that uses each 2-cell once is a layering. Layerings of a frame-acyclic molecule correspond to linear extensions of a partial order (Chanavat, arXiv 2603.22242, Prop. 2.18).
  - Any two linear extensions are connected by adjacent transpositions of incomparable elements.
  - Two incomparable consecutive 2-cells in a 2-dimensional layering sit side by side, so the transposition is an exchange move.
  - Hence any two U-composites t, t′ have `π(t) = π(t′)`, and Theorem A gives `t ⇄ t′`.
- **Existence.** Choose a layering. Realise each layer as a whiskered 2-variable, and connect consecutive layers, and the two ends to `⌈∂^±U⌉`, by RC(1). (This is §3.2 of the G file.)

### 3.2 Existence in G(3)

Let U be a 3-molecule presented in CaTT. It is frame-acyclic, since every molecule of dimension ≤ 3 is (Chanavat), so it has a layering `L₁, …, L_k`, where layer i is a whiskered 3-cell `Xᵢ`.

1. **Each layer as a 3-term.** In a strict 3-category, a whiskered generator can be written `u₁ ∗₁ (a ∗₀ X ∗₀ b) ∗₁ u₂`, with a, b 1-cells and u₁, u₂ 2-cells (rewrite the whiskers with exchange). Pick CaTT terms for a, b, u₁, u₂ with these strict images: every cell of `F(U)` is a composite of whiskered generators, so it is the strict image of some term. Adjust their boundaries syntactically by κ-cells of RC(1) so that the binary composites typecheck. Call the result `Wᵢ`. Then `π(σWᵢ) = ∂⁻Lᵢ` and `π(τWᵢ) = ∂⁺Lᵢ`, as strict 2-cells.
2. **Gluing.** `∂⁺Lᵢ = ∂⁻L_{i+1}`, so `π(τWᵢ) = π(σW_{i+1})`. Theorem A gives a connecting 3-cell `cᵢ`. Likewise `c₀ : ⌈∂⁻U⌉ ⇛ σW₁` and `c_k : τW_k ⇛ ⌈∂⁺U⌉`. These need the strict images of `⌈∂^±U⌉` to be the boundary 2-cells of U, which holds by §3.1.
3. `c₀ ∗₂ W₁ ∗₂ c₁ ∗₂ ⋯ ∗₂ W_k ∗₂ c_k` is a U-composite. It has the right type, and its support is all of U: every 3-cell is used, every cell in the boundary of a 3-cell lies in the type of that 3-cell's variable, and the remaining cells lie in `∂^±U`. ∎

**Consequence.** Every Gray generator of dimension 4 has a CaTT type, since its boundary molecules are 3-molecules. This covers `D²⊗D²`, `D³⊗D¹`, `D¹⊗D³` and `D¹⊗D¹⊗D¹⊗D¹`. Before this, the G file claimed this conditionally on the D1 gap and on an unstated existence step.

### 3.3 The general pattern

The same proofs give, for frame-acyclic molecules:
- existence in G(n) ⇐ RC(n−1) for the (n−1)-skeleton of U, together with existence in G(n−1);
- uniqueness in G(n) ⇐ RC(n) for U, as soon as U-composites have equal strict images. This holds when U's chain complex has a loop-free unital basis, since cells of the free strict ω-category on such a complex are determined by their chains (Steiner 2004), and the n-chain of a U-composite is the sum of the n-cells, by contractibility.

So G for all n follows from RC on loop-free contexts. G-alg (does Chanavat's contractibility give CaTT cells?) becomes the question of proving RC(n) with Chanavat's combinatorics.

## 4. Naturality (C1, D3a)

The definitions are those of `conjectures/naturality-arbitrary-depth.md` §2–§3, with the corrected induction order of its Lemma 2.

### 4.1 The reduction N ⇐ RC

**Strict naturality.** For full Y, `F(Q↑Y)` is the free strict ω-category on `I ⊗ Q` (Steiner's convention). Write e for the generator of I. For partial Y there is a strict **collapse** functor `F(I ⊗ Q) → F(Q↑Y)` defined on generators:
- `0⊗x, 1⊗x ↦ x` and `e⊗x ↦ id_x` for `x ∉ Y`;
- `0⊗x ↦ x⁻`, `1⊗x ↦ x⁺` and `e⊗x ↦ x↑` for `x ∈ Y`.

It respects boundaries, because the complement of Y is down-closed and the omitted factors of `a_x, b_x` are exactly the generators sent to identities.

**Invariant.** `π(t↑) = collapse(e ⊗ π(t))` for every term t. It holds for variables by definition. For `t = coh[γ]` it follows by substitution, provided every filler K satisfies `π(K) = collapse(e ⊗ π(c))`. Fillers built as in Proposition R do:
- For a **coherence** c of dimension n, the arity has dimension ≤ n−1, so `Q↑Y` has dimension ≤ n while K is an (n+1)-cell. Strict cells above the dimension of the computad are identities, so `π(K)` is an identity. So is `e ⊗ π(c) = e ⊗ id = id`.
- For a **composition** c, `π(K)` is the composite of the layers, because the connecting cells are coherences with identity strict image, and that composite is `collapse(e ⊗ π(c))` by construction.

The lower-dimensional instances of the invariant are what make `π(a_c)` and `π(b_c)` computable. (This was left implicit in the first version; the independent check asked for it to be stated.) Hence, for `c = coh_{Q,B}[id]` of dimension n, the strict cell `collapse(e ⊗ π(c))` goes from `π(a_c)` to `π(b_c)`.

**Proposition R.** Suppose RC(n) holds for `Q↑Y`. Then N holds for c, i.e. `a_c → b_c` is inhabited, and the filler K can be chosen with `π(K) = collapse(e ⊗ π(c))`.

*Proof.*
- **Coherence c.** `π(c)` is an identity, `e ⊗ id = id`, so `π(a_c) = π(b_c)`, and RC(n) gives K.
- **Composition c** (Q of dimension n). `e ⊗ π(c)` is the composite of the (n+1)-cells `e ⊗ q`, for q the top cells of Q, in some layered order. After collapse, the layers with `q ∉ Y` become identities and are dropped. Realise each remaining layer as `U₁ ∗ (a ∗₀ q↑ ∗₀ b) ∗ U₂`, as in §3.2, with whiskers of the right strict images adjusted by RC(1). Connect consecutive layers, and connect the ends to `a_c` and `b_c`, by RC(n): all of these are n-terms with equal strict images. The composite is K. ∎

### 4.2 N for every term of dimension ≤ 2

RC(1) and RC(2) hold in every context (§1, Theorem A). Hence:

**Theorem N≤2.** For every pasting context Q, every full type B over Q with `dim c ≤ 2`, and every up-closed `Y ⊆ Var(Q)`, `a_c → b_c` is inhabited in `Q↑Y`.

This settles the open items "arbitrary up-closed subsets of a chain" and "every 2-dimensional coherence over any 1-dimensional Q". It also gives every 2-dimensional composite over a 2-dimensional Q at any depth, e.g. vertical composition `α ∗₁ β` with all variables selected (depth 2). For dimension-1 terms it reproves BMOSV's case, with no depth restriction.

**Direct check for chains with partial Y** (independent of Steiner, as a sanity check). For Q a chain, `Q↑Y` splits at the vertices outside Y into blocks: pinched ladders, bigons and plain edges. Every 2-path from `π(σa_c)` to `π(τb_c)` flips each square of each block exactly once. Within a block the order is forced, as in the ladder theorem's §2.3. Squares in different blocks commute by exchange. So all such 2-paths represent the same strict 2-cell, and `π(a_c) = π(b_c)` for 2-dimensional coherences c.

### 4.3 Support lemma, and "G implies N" (D3a)

**Lemma S (support).** For every term t of a pasting context Q and every up-closed Y, with fillers chosen as in Proposition R,

```
Var(t↑ : a_t → b_t) = { q⁻, q⁺ : q ∈ Var(t : A) ∩ Y } ∪ { q : q ∈ Var(t : A) ∖ Y } ∪ { q↑ : q ∈ Var(t : A) ∩ Y }.
```

*Proof.* By induction. For a variable x, `a_x` and `b_x` contain `x^±` and the lifts of all iterated boundaries, which by induction cover the cylinder of `Var(x : A)`. For `t = coh_{Q,B}[γ]`, `t↑ = K[γ↑]`.
- If c is a **coherence**, then K's type `a_c → b_c` already contains `c⁻`, `c⁺` (full in Q) and the lifts of its boundary terms, which are also full in Q. So `Var(K : …) = Var(Q↑γ⁻¹Y)`.
- If c is a **composition**, K uses every top `q↑` and its type covers the rest.

Applying `γ↑` gives the claim. ∎

**Repair of "G implies N"** (full Y). Here G must be taken in the form of statement (b) of the G file, i.e. molecular coherences are conservative. G(n) for all n is not known to imply (b), since (b) also needs higher filling, which is RC. Let `U = I ⊗ Q`, a molecule presented by `Q↑Var(Q)`.
- **Coherence c.** By Lemma S, `a_c` and `b_c` are full in U. The molecular coherence rule (coherence side condition) gives a cell `a_c → b_c`, and conservativity gives a CaTT cell. The earlier §8 argument was right for this case, but needed Lemma S.
- **Composition c.** Here §8 was wrong, as the verified review found. The correct side condition is the *composition* one. By Steiner's formula, `∂⁻U = (0⊗Q) ∪ (e ⊗ ∂⁺Q)` and `∂⁺U = (1⊗Q) ∪ (e ⊗ ∂⁻Q)`. By Lemma S, `Var(a_c) = Var(c⁻) ∪ {cylinders of ∂⁺-boundary terms}`, which is `Var(∂⁻U)`, and dually `Var(b_c) = Var(∂⁺U)`. So the molecular composition rule applies.

So G (in form (b)) implies N for full Y, with Lemma S as the missing ingredient. For partial Y, use Proposition R instead. Proposition R does not need G at all, only RC on cylinders, which is the formulation sent out.

## 5. Gray contexts of every context (D3, C2)

**Construction.** Define `Γ ⊗ D¹ := Γ↑Var(Γ)` and, for n ≥ 2,

```
Γ ⊗ Dⁿ := (Γ ⊗ Dⁿ⁻¹) ↑ Yₙ₋₁ ,     Yₙ₋₁ := the variables of the newest layer.
```

The layers are `Γ, Γ′`, then `P, P′, M` for n = 2, and in general 2n+1 layers. Each new variable of the newest layer has type `a_q → b_q`, the nested-whiskering formula. For n = 2 and `f : x → y`, the new variable over `p_f : f ∗ p_y → p_x ∗ f′` has type `p_f ∗₁ (m_x ∗₀ f′) → (f ∗₀ m_y) ∗₁ p′_f`, the modification axiom. This matches Mikhail's Example 4.2 up to his identity-padded composites (arXiv 2412.13310, §4.1).

**When it is defined.** Building the newest layer needs lifts of the boundary terms of variables q in `Yₙ₋₁`. For `n ≥ 2` these terms have depth ≤ `dim Γ − 1` in Yₙ₋₁ (the variables of Yₙ₋₁ have dimension ≥ n−1), and their arities have context depth ≤ `dim Γ − 1` too. So:
- `Γ ⊗ D¹` exists for every context with dim Γ ≤ 3, since it needs lifts of terms of dimension ≤ 2 (Theorem N≤2);
- `Γ ⊗ Dⁿ` exists for every n when dim Γ ≤ 2: the base case is above, and each later step has depth ≤ 1, which is BMOSV Thm 3.1, applied to the pasting arities through the recursion of the N file;
- in general, the construction exists wherever N does.

**Comparison with Mikhail's `gray` rules** (printed rules read from arXiv 2412.13310, §4.1, pp. 22–24):
- **Layer structure.** It matches: 2n+1 layers, and each pair of a variable and its duplicate gets one connecting cell.
- **Boundary formulas.** For globular Γ and n = 1, Mikhail's Thm 4.4 gives `σ(p_x) = x ∗₀ 1^{d−1}_{p_{τᵈx}} ∗₁ ⋯ ∗_{d−1} p_{τx}` and `τ(p_x) = p_{σx} ∗_{d−1} ⋯ ∗₀ x′`. This is the same pasting as our `a_x`, `b_x`, written with identity-padded binary composites instead of whiskerings.
  - The two versions are different terms with equal strict images. For generators of dimension ≤ 3 they are connected by RC(2). In higher dimensions this needs RC(d).
  - So our contexts and Mikhail's T(Γ) agree up to transport along invertible cells for dim Γ ≤ 2. Syntactic equality would require adopting his composite convention.
- **Free-variable conditions.** Mikhail's printed conditions are defective, as found by LIM-F (machine-checked, `catt-lim-formalization.md` D3/D4) and by a verified researcher response (`conjectures/gray-contexts-in-catt.md`, verification §5; ledger D3b):
  - the source-side selector must read `y ∝ σ(p)`, and copies must be renamed;
  - the linearity predicate ∝ does not enforce multiplicity one.
  
  Under the repaired selector, `a_x` and `b_x` satisfy the conditions. Their free variables are x (resp. x′), plus the cylinders of the iterated boundaries and their types, which are exactly the connectors selected by the repaired rule. `x ∝ a_x` and `x′ ∝ b_x` hold with multiplicity one, since x occurs once at top dimension. So the iterated-cylinder construction is a specified derivation of the *repaired* Gray rules for every case in which it is defined. *This is an informal check against the repaired rules; LIM-F's encoding is where it can be machine-checked.*
- **Strict presentation (§6.2(2) of the G file).** Strictly, the partial cylinder of `I ⊗ M` along its top layer is `I ⊗ (I ⊗ M)` collapsed along `I ⊗ (∂I ⊗ M)`. That is `(I⊗I collapsed at two opposite sides) ⊗ M = D² ⊗ M`, because the strict Gray tensor preserves colimits in each variable (Ara–Maltsiniotis). By induction, the iterated construction presents `Dⁿ ⊗ M` under Steiner's convention. The generators are Steiner's atoms, so for Steiner M this is the free strict ω-category on `𝒪(Dⁿ) ⊗ 𝒪(M)` (Ara–Lucas Cor. 3.11). *[sketch]*

## 6. Side conditions of the Gray tensor of contexts (D4)

**G2 (functoriality in substitutions, D¹ factor): holds syntactically.**
- *Claim.* For `Δ ⊢ σ : Γ` and every term t of Γ, `(t[σ])↑ ≡ t↑[σ↑]`, where `σ↑ : Δ↑X′ → Γ↑X` sends `q^± ↦ (qσ)^±`, `q↑ ↦ (qσ)↑`, and `X′ = σ⁻¹X`.
- *Proof.* Induct on t.
  - For a variable, both sides are `(qσ)↑`, by definition.
  - For `t = coh_{Q,B}[γ]`, `t[σ] = coh_{Q,B}[γσ]` and `(γσ)⁻¹X = γ⁻¹(σ⁻¹X)`, so both sides are `K(Q,B,γ⁻¹σ⁻¹X)` substituted along maps that agree on each `q↑` by the induction hypothesis. On `q^±` they agree because renaming commutes with substitution.
- So `Γ ⊗ σ` is a well-typed substitution whenever the lifts are defined, as needed for nat-Δ in `internal-hom.md` §5.1. This is automatic because fillers are chosen once per `(Q, B, Y)` and moved around only by substitution. A construction that chose fillers per term would lose it.

**G5 (linearity): not needed.** The cylinder construction is defined for every term, including non-linear ones. For example, for a loop `f : x → x`, `(f ∗₀ f)↑` uses f↑ twice. Mikhail's linearity condition `x ∝ t` serves his recognition judgment, to pin down which occurrence carries the projection. It plays no role in the naturality-based construction.

**G4 (associativity): reduced to RC.**
- In `(Γ ⊗ Δ) ⊗ Θ` and `Γ ⊗ (Δ ⊗ Θ)` the generators correspond, and the two types of a generator are composites of the same boundary molecule, so they have equal strict images. For generators of dimension ≤ 3, Theorem A connects the two types (e.g. the Gray cube's hexagons).
- In general this needs RC(dim − 1).
- Promoting "types connected by invertible cells" to an equivalence of contexts needs coherent transport of dependent generators along those cells. That is again RC in higher dimensions, and is not written out here.
- Strict equality would need strictly associative composites (CaTT_su/sua).

## 7. Dimension 3: why loop-freeness enters

**RC(3) fails without loop-freeness (sketch; checked in outline by the literature thread).** In `Γ = (x : ⋆, a : id_x ⇒ id_x)`, the Eckmann–Hilton 3-cell `a ∗₀ a ⇛ a ∗₀ a` and the identity are parallel with equal strict images (both identities). Interpret Γ in the fundamental weak ω-groupoid of S², sending a to a generator of π₂(S²). The Eckmann–Hilton cell then represents the self-braiding at that generator, a non-zero element of π₃(S²) ≅ ℤ **[conj, G1 check]**. The candidates are η and the Whitehead square `[ι₂, ι₂] = ±2η`; both are non-zero, and the argument needs only that. A 4-cell would make that class null. *Two claims still need citations before the "sketch" label can go: (a) the fundamental ω-groupoid of S² is a model of CaTT (Grothendieck–Maltsiniotis; Ara); (b) which of the two classes the Eckmann–Hilton term represents.*

So the conjecture must assume a loop-free context. The cylinders `Q↑Y` and the molecules are loop-free, and for them RC holds in (∞,ω)-categorical semantics (Campion arXiv 2311.00205, Cor. 3.5; Chanavat arXiv 2603.22242, Thm 3.29). Dimension 2 is special because exchange is the only relation and it is realised by one pasting context.

**Where the proof of Theorem A stops in dimension 3.**
- Sequentialization extends: every arity is a pasting context, which can be layered.
- Normal forms of whiskered 3-generators extend: whiskers are compared by Theorem A, and moving a whisker comparison past a generator is an interchange over a pasting context.
- Exchange of 3-generators extends: exchange moves are coherences over pasting contexts with two 3-discs.
- What fails is the analogue of Lemma P: runs of 3-cells with no 3-variable, between 2-terms with equal strict image, in a 2-dimensional context that is not a pasting context. Such runs need not pull back to any pasting context. The natural attack is a Squier-style critical branching analysis. The hard branchings pair a 3-cell that moves a 2-generator F with a reassociation that splits F's boundary composite (e.g. `f⁻ ∗₀ y↑` in the lax square), and no pasting context contains both.
- Smallest instance: RC(3) for the lax square, question 1 of both outbox prompts.

### 7.1 A reduction of RC(3) to coherent normalization (progress, 2026-11-18)

Fix a loop-free 2-dimensional context Γ, such as the lax square S. Theorem A gives, for every 2-term P, a normal form `N(P)` and a 3-cell `ν_P : P ⇛ N(P)` built from coherences. Its inverse `ν_P⁻¹` exists, with cancellation 4-cells, because coherence cells are invertible (Benjamin–Markakis–Sarti). Call a 3-cell **basic** if it is `coh_{R, u → u′}[δ]` with R a pasting context of dimension ≤ 2 (so u, u′ are full parallel 2-terms over R). A **whiskered basic cell** is a basic cell composed with 2-terms by `∗₁` and with 1-terms by `∗₀`.

**Proposition (reduction).** RC(3) holds for Γ provided:

> **(CN) coherent normalization.** For every whiskered basic cell `b : P₁ ⇛ P₂` in Γ, the 3-terms `ν_{P₁}` and `b ∗₂ ν_{P₂}` (both `P₁ ⇛ N`) are connected by a 4-term.

*Proof.*
- Sequentialization works in dimension 3 exactly as in Step 2 of Theorem A. Every arity is a pasting context and can be layered, and binary composites are flattened by interchange coherences over pasting contexts. So every 3-term `T : P ⇛ Q` is connected by 4-cells to a vertical composite `b₁ ∗₂ ⋯ ∗₂ b_k` of whiskered basic cells. Γ has no 3-variables, so no other factor occurs.
- By (CN), each `bᵢ` is connected to `ν_{P_{i−1}} ∗₂ ν_{P_i}⁻¹`.
- Telescoping with the cancellation 4-cells gives `T ⇛ ν_P ∗₂ ν_Q⁻¹`.
- So any two parallel 3-terms are connected. ∎

**Where (CN) is hard.** Suppose the cells of `δ` avoid the 2-generators of Γ, or contain them only as whole arguments, i.e. a 2-variable of R is sent to a normal form. Then both 3-terms of (CN) are obtained by substitution from 3-terms over one pasting context, built from R by subdividing the 1-variables along the paths of their images. The coherence rule there gives the 4-cell. *(Sketch; not yet written as a general lemma.)* The remaining case is a basic cell whose arity separates the composite boundary of a 2-generator. In S, an example is an associator moving `v_y` relative to `f⁻` inside the source `f⁻ ∗₀ v_y` of F, whiskered next to a column that contains F. There, `ν` treats `f⁻ ∗₀ v_y` as one abstracted edge `z⁻`, while b splits it, and no pasting context contains both. This is the Squier-style critical branching described above, now isolated as the single family that must be closed.

## 8. Follow-ups and owners

- RC(n), n ≥ 3 (C1 and D2): out to researcher; internal attempts continue in this thread (NGC).
- C1b, mechanical check in the Agda checker (now including Theorem A's exchange step on a small instance): NGC.
- Mikhail's printed-rule defects: ledger D3b, owned by LIM-F.
- Agda for Gray contexts (D5) is unchanged.

## 9. Machine checks (C1b)

`tools/` contains a Python implementation of Theorem A as a term generator (`rc2.py`), for contexts with an acyclic 1-skeleton. It covers sequentialization, Lemma G, Lemma P, and exchange (Lemma E). It emits Agda modules that ask the certified checker `CaTTExp.Check` to infer each generated term's type, and assert by `refl` that the inferred type is the stated one. The Python side is untrusted. See `tools/README.md`.

| Generated module | Checks | Result |
|---|---|---|
| `UnitorNaturality` | the left unitor's naturality 3-cell at depth 2 over the lax square (§6 "partial progress" case of the N file), via Theorem A | typechecks (~50 s) |
| `ExchangeTwoBigons` | Theorem A with one exchange move (two side-by-side bigons) | typechecks (~3 min) |
| `AssociatorNaturality` | the associator's naturality 3-cell over the fully selected 3-chain: the ladder theorem's example, C1b | ASSOC_RESULT |

There is one negative control. In `UnitorNaturality`, swapping source and target in the expected type makes Agda reject the module.

The generator does not implement positional pull-back for 1-skeleta with cycles, so Eckmann–Hilton is not generated. The proof covers that case.
