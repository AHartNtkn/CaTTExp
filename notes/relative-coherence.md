# Relative coherence in CaTT: dimension 2, and what it gives for Gray contexts and naturality

*Thread "Prove naturality and Gray context conjectures", 2026-11-18. Paper proofs, not yet independently checked. They extend the verified relative ladder theorem (`conjectures/naturality-arbitrary-depth.md`, researcher response and verification) and reuse its steps wherever they apply unchanged. The open remainder is stated for researchers in `conjectures/answered/naturality-arbitrary-depth-2026-11-18.md` and `conjectures/outbox/gray-contexts-r6.md`.*

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
| **RC(3) for the lax square S**, every pair of parallel 3-terms; hence N for every 3-dimensional coherence over one arrow | proved by a researcher, verified as a paper construction (§7.4) |
| **RC(3) for the cylinder of a composable pair** x → y → z; hence N for every 3-dimensional coherence over that pair | proved by a researcher at the round-2 standard (fixed-edge extension lemma), verified (`conjectures/answered/naturality-arbitrary-depth-r3-2026-11-18.md`); generalised factorisations machine-checked (§7.5) |
| **RC(3) for the 2-disc cylinder** (the only strict 3-cell is πU); hence N for every 3-dimensional coherence over the 2-disc | proved by a researcher, verified at paper level (`conjectures/answered/naturality-arbitrary-depth-r4-2026-11-18.md`) |
| Suspension descent: RC(r+1) on `(ΣQ)↑ΣY` ⇒ RC(r) on `Q↑Y`, so RC(n) on all cylinders gives N through dimension n | proved by a researcher, verified at paper level (same file) |
| **RC(3) on every finite full chain cylinder**, on the partial selections Y={z,g} and Y={y,z,f,g} over x→y→z, and on the cylinder of D²∗₁D² | proved by a researcher, verified at paper level (`conjectures/answered/naturality-arbitrary-depth-r5-2026-11-18.md`); constructors and fold machine-checked on x₀→⋯→x₃ (§7.7) |
| Gray cube: X-free 3-loops contractible; the factorisation of inactive columns extends to 3-dim contexts whose 3-generators have 2-supported 2-sources (incl. the D² cylinder and c⋆D²) | proved by a researcher, verified at paper level (`conjectures/answered/gray-contexts-r5-2026-11-18.md`) |
| An acyclic 1-graph is **not** enough for RC(3): (x, a : 1_x→1_x) is acyclic and RC(3) fails | counterexample (same file); the open condition is now "no 2-generator from an identity to an identity" |
| Fusion when two generator letters can be exchanged: Y={x,f,g} | proof sketch here (§7.6): y is a cut vertex, so horizontal normal forms remove the exchange; key constructors machine-checked. Not verified |
| Fusion when two generator letters can be exchanged: the 2×2 grid (no cut vertex) | **RC(3) proved by a researcher, verified** (`conjectures/answered/gray-contexts-r7-2026-11-18.md`: matrix normal form, flattening lemma). An independent internal proof (§7.8: path lattice ⊥ ⊕ {0,1}² ⊕ ⊤, all exchange at the cut (1,1)) has its constructors machine-checked (`GridRC3`) |
| RC(3) on the full cylinder of D² ∗₀ D² | **proved by a researcher, verified** (`conjectures/answered/naturality-arbitrary-depth-r7-2026-11-18.md`: orientations AB→BA, AG→GA, FB→BF; U_A/U_B via the interchange 4-cell). An independent internal sketch of the 2-skeleton (§7.9: unique factorisation, a single exchange χ_M) has its normal forms and all multiplications machine-checked (`TwoDiscCylinderRC3`) |
| D14: the Gray cube's two bracketings are inverse up to 4-cells | sketch (§6.1) |
| General exchange in dimension 2 (acyclic, nonempty boundaries) | strict side **proved** (§7.11): exchange classes are linear extensions of event posets, and squares and hexagons are a homotopy basis (machine-checked on grids up to 3 × 3); both are single coherences over pasting contexts (`ExchangeLaws`). RC(3) reduced to two forced-order statements (K), (F): sketch |
| RC(n), n ≥ 3, for general loop-free contexts and cylinders `Q↑Y` | **open**, sent out |

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

### 6.1 D14: the Gray cube's two bracketings are inverse up to 4-cells (sketch, 2026-11-18)

**Setting.** `GrayCtx/Cube.agda` (PR #55) checks two substitutions:
- `CubeR ⊢ toL : CubeL`;
- `CubeL ⊢ toR : CubeR`.

Each is the renaming on the 26 lower generators. It sends the other cube cell X to `K₁ ∗₂ (W ∗₁ X ∗₁ W′) ∗₂ K₂`, where:
- `W, W′` are associator 2-cells (`a`, `b`, or `A1`, `B3`);
- `K₁, K₂` are X-free 3-cells built from three kinds of step: regroupings of vertical chains (`regroup`), unitors on whiskered squares, and a cancellation `Φ` of an associator pair inserted by `stepAt`.

**Claim.** Both composites `toR ∘ toL` and `toL ∘ toR` send the cube cell to a cell connected to it by a 4-term. So the two bracketings of `D¹ ⊗ D¹ ⊗ D¹` are equivalent contexts, with this explicit pair of substitutions. Both composites are the identity on the lower generators.

**Atoms and column cells.** Every 2-term met here is a vertical composite of *atoms*. An atom is either a whiskered square (P▹, ◃Q, …), which contains a 2-variable, or an associator 2-cell, which contains none. A **column ps** Π is the pasting context made of a 1-cell column and a vertical chain of 2-discs, one per atom. The 3-cells of `K₁` and `K₂` are of two kinds:
- (i) **column coherences.** These are substitutions of 3-terms over a column ps, with atoms sent to its discs. Regroupings and unitors on squares are of this kind, and so is any whiskering of a column coherence.
- (ii) **segment rewrites.** These are column 3-terms with one 3-disc slot, filled with a 3-cell between two 2-terms with no 2-variable. The cancellations `Φ : a ∗₁ A1 ⇛ id` and their inverses are of this kind.

**Column-loop lemma (any context).** A 3-loop made of steps of kinds (i) and (ii) is connected to the identity by a 4-term.

*Proof sketch.*
1. *Flat words and segments.* The **flat word** of a column word lists its atoms with identities dropped.
   - Kind (i) steps leave the flat word unchanged, because column coherences cannot reorder atoms.
   - Kind (ii) steps change only atoms without 2-variables.
   - So the 2-variable atoms of the flat word, and their order, are fixed along the loop. They cut the flat word into **segments** with no 2-variable.
2. *Normalization.* Define `ν(word) := R(word) ∗₂ N(flat word)`, where:
   - R is the column coherence to the right-nested flat word;
   - N normalizes each segment u to `κ²(σu, τu)`, by the 3-cell between 2-terms without 2-variables given by Proposition P∞ (§7.2), whiskered into the column.
3. *(CN) for each step b, i.e. `ν(src b) ⇛ b ∗₂ ν(tgt b)`.*
   - **Kind (i).** `R(src b)` and `b ∗₂ R(tgt b)` are full parallel 3-terms over the same column ps, so the coherence rule there connects them. The N-parts are equal.
   - **Kind (ii)**, with b rewriting a subword u. First factor `R(src)` through the column ps in which u is one disc; the coherence rule over the finer ps allows this. Then slide b through R, by the naturality of R in that disc: a coherence over the column ps with the disc promoted to a 3-disc. Finally, `N(seg) ⇛ b ∗₂ N(seg′)` compares two parallel 3-cells between 2-terms without 2-variables. Proposition P∞ connects them, and the resulting 4-cell is whiskered into the column through a 4-disc slot.
4. *Telescoping.* Telescope with the cancellation 4-cells for the inverses of coherence-built cells (Benjamin–Markakis–Sarti). ∎

The key point is that no step ever needs a pasting context in which a square's composite 1-boundary is split. Squares are always whole discs. Associator arithmetic happens only inside segments with no 2-variables, over chains.

**Proof of the claim.** Take `toR ∘ toL` on `X_R`. The other composite is symmetric.
1. Distribute the outer whiskering `A1 ∗₁ (−) ∗₁ B3` over `∗₂`. This is a coherence over a column ps with a stack of 3-discs.
2. Collect `A1 ∗₁ (a ∗₁ X_R ∗₁ b) ∗₁ B3` into `W ∗₁ X_R ∗₁ W′`, with `W = A1;a` and `W′ = b;B3`. This is a regrouping over a column ps with X_R as a 3-disc. The result is `K₁ ∗₂ (W ∗₁ X_R ∗₁ W′) ∗₂ K₂`, with K₁ and K₂ made of steps of kinds (i) and (ii).
3. Let `ι_Z : Z ⇛ W ∗₁ Z ∗₁ W′` be the uniform insertion cell: inverse unitors, then `Φ⁻¹` whiskered next to Z. Each factor is a coherence over a ps with Z as a 2-disc and `Φ⁻¹` substituted wholesale into a 3-disc. So ι is natural in Z. Promoting Z's disc to a 3-disc X gives coherences over D³, or over `D³ ∗₁ D³` for the exchange with the `Φ` slot. Hence `ι_S ∗₂ (W ∗₁ X_R ∗₁ W′) ⇛ X_R ∗₂ ι_T`.
4. `K₁ ∗₂ ι_S⁻¹` and `ι_T ∗₂ K₂` are 3-loops of kinds (i) and (ii), so the column-loop lemma sends both to identities.
5. Altogether, `K₁ ∗₂ (W ∗₁ X_R ∗₁ W′) ∗₂ K₂ ⇛ ι_S ∗₂ (W ∗₁ X_R ∗₁ W′) ∗₂ ι_T⁻¹ ⇛ X_R ∗₂ ι_T ∗₂ ι_T⁻¹ ⇛ X_R`. ∎

**Status.** This is a sketch on paper; the 4-terms have not been generated. Two things in it are not yet written out in full: the positional pull-back in Proposition P∞ (for the cube, the 1-skeleton is acyclic, so the round-1 support argument, answered/gray-contexts-2026-11-18.md §2, covers it), and the factorization of R through coarser column ps's. A mechanical check needs the GrayCtx elaborator plus the `tools/` generator. For the general RC(3) question, the column-loop lemma covers every X-free loop that keeps its 2-variable atoms as fixed syntactic pieces. What it does not cover is a loop whose steps re-parse the same 2-term into different atoms, for example a coherence `coh_Q[τ]` whose middle 2-terms `τ(ξ_k)` are big composites containing F, compared with a step that splits them. This is exactly the remaining F-boundary case for the lax square.

## 7. Dimension 3: why loop-freeness enters

**RC(3) fails without loop-freeness (sketch; checked in outline by the literature thread).** In `Γ = (x : ⋆, a : id_x ⇒ id_x)`, the Eckmann–Hilton 3-cell `a ∗₀ a ⇛ a ∗₀ a` and the identity are parallel with equal strict images (both identities). Interpret Γ in the fundamental weak ω-groupoid of S², sending a to a generator of π₂(S²). The Eckmann–Hilton cell then represents the self-braiding at that generator, a non-zero element of π₃(S²) ≅ ℤ **[conj, G1 check]**. The candidates are η and the Whitehead square `[ι₂, ι₂] = ±2η`; both are non-zero, and the argument needs only that. A 4-cell would make that class null. *Two claims still need citations before the "sketch" label can go: (a) the fundamental ω-groupoid of S² is a model of CaTT (Grothendieck–Maltsiniotis; Ara); (b) which of the two classes the Eckmann–Hilton term represents.*

*Supporting evidence (2026-11-18, verified FT₃ answer, `conjectures/answered/finite-fibration-test-2d-base-2026-11-18.md` §5 and V5).* Consider this same context Γ.
- The groupoidification of the *strict* free object `B²ℕ` is `K(ℤ,2)`, by Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9 and Ex. 4.10.
- The groupoidification of the *weak* (cellular) free object is `S²`.

So the weak free object has 3-dimensional structure, `π₃(S²) = ℤ`, that the strict image π cannot see. That is exactly what RC(3) would forbid. This does not by itself show that the Eckmann–Hilton term is non-zero, which is still claim (b). It does show that **some** pair of parallel 3-cells of Γ with equal strict image is not connected: otherwise `π₃` of the groupoidification would vanish. That needs the step from "RC(3) in CaTT" to "trivial `π₃` after groupoidification". The step is standard but not written out here: CaTT terms present the cellular free object (Benjamin–Markakis–Sarti), and RC(n) for all n together with `π₃(K(ℤ,2)) = 0` would make the comparison map 3-connected.

So the conjecture must assume some acyclicity of the context. The cylinders `Q↑Y` are Steiner loop-free, and frame-acyclic molecules have essentially unique composites. For both, RC holds in (∞,ω)-categorical semantics: see Campion's pasting theorem (arXiv 2311.00200) and Chanavat (arXiv 2603.22242), Thm 3.17. Thm 3.29 there is Gray monoidality, and Campion's arXiv 2311.00205 Cor. 3.5 is strong monoidality. Frame-acyclicity is *not* Steiner loop-freeness (Hadzihasanovic arXiv 2404.07273, Comment 8.3.5 and Ex. 8.3.12), so a proof for one class does not automatically cover the other. Dimension 2 is special because exchange is the only relation and it is realised by one pasting context.

**Where the proof of Theorem A stops in dimension 3.**
- Sequentialization extends: every arity is a pasting context, which can be layered.
- Normal forms of whiskered 3-generators extend: whiskers are compared by Theorem A, and moving a whisker comparison past a generator is an interchange over a pasting context.
- Exchange of 3-generators extends: exchange moves are coherences over pasting contexts with two 3-discs.
- What fails is the analogue of Lemma P: runs of 3-cells with no 3-variable, between 2-terms with equal strict image, in a 2-dimensional context that is not a pasting context. Such runs need not pull back to any pasting context. The natural attack is a Squier-style critical branching analysis. The hard branchings pair a 3-cell that moves a 2-generator F with a reassociation that splits F's boundary composite (e.g. `f⁻ ∗₀ y↑` in the lax square), and no pasting context contains both.
- Smallest instance: RC(3) for the lax square, question 1 of both outbox prompts. Round 1 (`conjectures/answered/gray-contexts-2026-11-18.md`) settled its identity-boundary case and reduced 2-dimensional coherence arities to vertical 2-chains. The round-2 prompts (`conjectures/answered/gray-contexts-round2-2026-11-18.md`, `conjectures/answered/naturality-arbitrary-depth-r2-2026-11-18.md`, which settles it) ask for the F-boundary case.

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

### 7.2 Two partial results toward RC(3) for the lax square (2026-11-18)

**Proposition P∞ (RC in every dimension without 2-variables).** Let Γ be any context, with cycles allowed. Let T, T′ be parallel n-terms of Γ, n ≥ 1, with no variable of dimension ≥ 2 in their support. Then T and T′ are connected by an (n+1)-term. In particular, **RC(n) holds for every n in every 1-dimensional context.** This does not contradict §7: the Eckmann–Hilton cell needs a 2-variable.

(For the lax square this is also proved in round 1, `conjectures/answered/gray-contexts-2026-11-18.md` §2, by a total-support form of Benjamin–Markakis Lemma 36.)

*Proof sketch.* Lemma P (Step 1) works in every dimension.
- Let w be the flattened path of the 1-dimensional boundary.
- Induct on terms. In `coh_{R}[γ]`, each column of R is sent to a segment of w, at a position fixed by the pasting structure. Each variable of R of dimension ≥ 1 is sent to a term with no 2-variables, which pulls back to that segment by induction.
- A pull-back at a given position is unique. The 0-variables of `C(w)` are distinct, so each entry of the assembled substitution has a prescribed type, and the induction determines the entry from that type.
- So T and T′ pull back to parallel terms over the chain `C(w)`, with the same pulled-back boundary. Their types traverse all of w, so they are full, and the coherence rule over `C(w)` connects them. ∎

**Column lemma for S.** Every 0-path in S that passes through `y⁻` or `x⁺` runs from `x⁻` to `y⁺`. Let `coh_R[δ]` be a term of S, R a pasting context, with F in the support of δ. Then all of R's 1-columns except one are sent to empty paths, that is, to identities at `x⁻` or `y⁺`. The remaining column carries all of the F-occurrence, and its two ends are sent to `x⁻` and `y⁺`. Hence a coherence that touches F never separates `f⁻` from `y↑`, or `x↑` from `f⁺`, into different columns.

*Proof.* A variable of R sent to a term containing F has a 1-dimensional boundary path of length 2, from `x⁻` to `y⁺`. It sits over one column of R, so that column covers the whole of `x⁻ → y⁺`. Nothing composes before `x⁻` or after `y⁺` except identities. ∎

**Consequence for (CN).** The critical branching of §7.1 in S can only take one shape: a whiskered basic cell `b ∗₁ W`, where b is F-free and splits `f⁻ ∗₀ y↑`, and W is a 2-term containing F. By the column lemma, it cannot be a cell set beside F's column. Now compare b with the part of `ν` that absorbs b's source run into `κ`. These are parallel F-free 3-cells between F-free 2-terms, so Proposition P∞ connects them. (CN) for S therefore reduces to one compatibility: **ν commutes with `∗₁`-composition by F-containing 2-terms**, i.e. `ν_{u ∗₁ W}` is connected to `(ν_u ∗₁ ν_W) ∗₂ (flattening of N(u) ∗₁ N(W))`. The flattening is a coherence over a pasting context.

Two routes to that compatibility looked natural, and each runs back into an RC(3) or N(3) statement:
- *Define ν by structural recursion on terms, using naturality lifts of `coh_R`.* For 2-dimensional R this uses N for terms of dimension ≤ 2, which is proved. But (CN) then asks for the lift of the 3-cell b, which is N for 3-terms over a pasting context of dimension ≤ 2.
- *Use the retraction S → D².* Let φ : D² → S send `s, t, Φ` to `f⁻∗₀y↑`, `x↑∗₀f⁺`, F. Let ψ : S → D² send `y⁻, x⁺ ↦ b`, `f⁻ ↦ s`, `x↑ ↦ t`, `y↑, f⁺ ↦ id_b`, and F to F conjugated by unitors. There is a transformation `id_S ⇒ φψ`. Its endpoint components are identities, its 1-components are `y↑` and `f⁺`, and its higher components are coherences. RC in D² (a pasting context, so the coherence rule applies directly) then gives RC(3) for the F-touching terms of S, *provided* every 3-term of S has a naturality lift along this transformation. That is N for 3-terms with Y = all of S.

Status: open. The remaining gap is the single compatibility stated above.

### 7.3 Round 2 researcher response on the F-boundary case (verified 2026-11-18)

Source: `conjectures/answered/gray-contexts-round2-2026-11-18.md`. Partial answer, correct.
- **Proved (any context, no acyclicity):** parallel 3-terms that are both *literally suspended* coherences `coh_{ΣC,ΣA}[τ]` over vertical chains ΣC are connected by a 4-term. The proof desuspends to the hom computad, using Benjamin–Markakis hom freeness (relied on at statement level, not re-read), lifts to the path chain `C_w` by item 4 / Proposition P∞, and re-suspends.
- **Refuted shortcut:** "equal global strict image ⇒ equal hom strict image". Over D₂, take `W(A) = (λ_f⁻¹ ∗₁ (1_{1_x} ∗₀ A)) ∗₁ λ_g`, `r = coh(A → W(A))`, `ℓ = coh(W(A) → A)` and `κ = r ∗₂ ℓ`. Then κ is not `1_A` in the hom strictification, yet `coh(κ → 1_A)` exists globally. The same example transports to the lax square S.
- **Consistency with §6.1.** The steps r and ℓ re-parse the atom A into a whiskered expression `W(A)`. This is exactly the step the column-loop lemma excludes, because there atoms stay fixed syntactic pieces. So the column-loop lemma and D14 are unaffected, and the remaining gap is the same in both accounts.
- **What remains:** boundary-preserving 4-comparisons that replace an arbitrary F-bearing 3-term by a suspended one. Equivalently, these are the normalisers that Rice (arXiv 2502.17068, §4.5.2) leaves open. The round-3 answer (`conjectures/answered/gray-contexts-r3-2026-11-18.md`) shows this replacement is impossible in general (a hom-word length invariant), so normalisers must keep boundary-adjusting terms, as in §7.4; rounds 4 and 5 are answered (`conjectures/answered/gray-contexts-r4-2026-11-18.md`, `conjectures/answered/gray-contexts-r5-2026-11-18.md`: the Gray cube's X-free loops are contractible), and round 6 is `conjectures/outbox/gray-contexts-r6.md`.

### 7.4 RC(3) for the lax square: settled (C1 round 2, verified 2026-11-18)

Source: `conjectures/answered/naturality-arbitrary-depth-r2-2026-11-18.md`. A paper construction, verified step by step and not run through an implementation. **Every pair of parallel 3-terms of S is connected by a 4-term.** Hence K(Q, B, Var Q) exists for every 3-dimensional coherence over the single arrow `(x, y, f)`.

The proof has four steps.
1. **Active-column factorisation.** This is the column lemma of §7.2, strengthened. Take a 2-term with image F. Exactly one column of its arity carries F and spans `x⁻ → y⁺`. The other columns sit over a point, because `x⁻` is the unique source and `y⁺` the unique sink. So the term factors literally through a full 2-term on a path context, and the factorisation is stable under substitution.
2. **Normalisers.** Define `ν_T : T → (κ(σT,p)·F)·κ(q,τT)`. Folding 4-laws are given by coherences on path contexts, on vertical chains with F substituted, and on the mixed context `V(1,0,1)`.
3. **Evaluation fusion.** A connecting cell `Λ_G : G ∗₂ ν_{T′} → ν_T` is built by induction on the syntax of the 3-term G, through 2- and 3-dimensional arities.
4. **Right cancellation.** This uses the invertibility of coherence composites.

This is exactly the (CN) programme of §7.1. The researcher's choice of ν, whose normal form folds F with path comparisons, satisfies the compatibility that §7.2 isolated. The method needs the discarded columns to be point-supported. That is why general cylinders `Q↑Y` remain open, for example a composable pair, where inactive columns carry paths, and the 2-disc. They were asked in the round-3 prompt (`conjectures/answered/naturality-arbitrary-depth-r3-2026-11-18.md`, answered: composable pair settled); round 4 answered: `conjectures/answered/naturality-arbitrary-depth-r4-2026-11-18.md` (2-disc cylinder settled, suspension descent); round 5 answered: `conjectures/answered/naturality-arbitrary-depth-r5-2026-11-18.md` (all finite full chains, two forced-order proper selections, D² ∗₁ D²); the rest is in `conjectures/outbox/naturality-arbitrary-depth-r6.md` (unsent). Comparing two choices of K is a 5-cell, not a 4-cell; this corrects round 2's question 2.

### 7.5 Machine checks of the lax-square proof, and the cylinder of a composable pair (2026-11-18)

**Machine checks** (`tools/rc3_square.py`, `tools/rc3_pair.py`, `src/CaTTExp/Generated/LaxSquareRC3.agda`; the certified checker plus `refl`):
- *Active-column factorisation (13).* 43 generated terms of S with strict image F are checked: 40 random 2-terms (random vertical words of path cells and F, random bracketings, random point whiskers) and 3 terms over 3-dimensional arities. For each one:
  - T is a term of S;
  - `H = coh_{P,A}[δ]` is a term of the retained one-column context R;
  - `H[η] ≡ T` holds by `refl`.

  - η is a well-typed substitution `R → S`. The generated module does not call `CheckWith.checkSub`; instead it witnesses this by the coherence `coh_{R, u → u}[η]`, where u is the unbiased composite of R. u is full, and the certified checker accepts the coherence only if every entry of η has the type R requires.

  That each generated term has strict image F is guaranteed by the generator, not checked by Agda. Agda checks only the typing and the syntactic equalities above. Stability is checked in Python on two instances: for u over `C_2` and σ into S, the H of `u[σ]` is literally the H of u.
- *The crux exchange.* Let α and β be the parallel 3-terms `(b ∗₁ F) ∗₂ c` and `c′ ∗₂ ((b′ ∗₁ F) ∗₁ 1_q)`. Here b and b′ are two different path 3-cells, which split `f⁻ | y↑` inside the chain `C(f⁻, y↑)`, and c, c′ are the right unitor of the vertical word, in which F is a whole 2-disc. The 4-term `α ⇛ β` is built as naturality (4), a coherence over `V(1,0)` with b substituted as a whole into the 3-disc, followed by the path 4-cell `b ⇛ b′` (Proposition P∞), whiskered into the column. The certified checker gives it exactly the type `α → β`. With the two sides swapped, it is rejected.
- *The mixed law (11).* `Ω_R` is instantiated in S with `Z ↦ F` and with path 3-cells for M and N. It typechecks.
- *Not checked:* the full recursive construction (normalisers ν, folding laws, evaluation fusion, `Λ_G`, cancellation) on arbitrary pairs. The checks cover its key lemma and its basic 4-cells on generated instances.

**The cylinder of a composable pair.** *Status:* the sketch below was settled by the round-3 answer (`conjectures/answered/naturality-arbitrary-depth-r3-2026-11-18.md`), whose fixed-edge extension lemma replaces observation 2 by a literal factorisation through `C_n ∗₀ D¹(h)` or `D¹(h) ∗₀ C_n`, and whose two-generator case `H = L ∗₁ R` is point-supported with a forced order. The general-chain statement below is still open (longer cylinders, ledger C1). Let `Q = (x, y, z, f, g)` and `Y = Var(Q)`. Q↑Y is two lax squares pasted along `y↑`, with generators `f↑ : f⁻y↑ ⇒ x↑f⁺` and `g↑ : g⁻z↑ ⇒ y↑g⁺`. The lax-square proof uses that inactive columns are point-supported. Here they can carry paths, for example the f⁻ column of `f⁻ ∗₀ g↑`. Two observations remove that obstacle.
1. *At most one active column.* Two 2-generators are never `∗₀`-composable after whiskering. That would need a path from the target vertex of one to the source vertex of the other, and here those are `y⁺ → y⁻`, which does not exist. So in every term, all 2-variable-bearing entries of the arity lie in one column, because columns are horizontally disjoint. The same holds for `Q↑Var(Q)` with Q any chain: edges go `⁻→⁻`, `⁺→⁺` and `⁻→⁺`, never `⁺→⁻`.
2. *Generalised factorisation.* Retain the active column as it is. Pull back each inactive column positionally to the chain of its path, which is possible because the 1-skeleton is acyclic. The retained R is a pasting context: a horizontal concatenation of single-edge columns and the active column. η sends R's chain edges to edges of Γ.

   This is **stable** where the evaluation lemma needs it. Let u be a term over R with an active column, and σ = η. Then u's inactive columns lie over R's chain edges, which σ sends injectively to edges. So the pull-backs before and after σ agree, and the retained H is literally the same. If u has no active column, then `u[σ]` is path-only, and Case 1 of the evaluation lemma applies without stability. **Checked:** 19 generated terms of the composable-pair cylinder, with `γ = δ[η]` by `refl` and H typed in Agda, and 12 stability instances in Python.

With these two changes, the rest of the lax-square proof goes through as far as I can see, with one generalisation. Normal forms are now Theorem A's `κ · e_{g₁} · κ · ⋯ · e_{g_k} · κ`, with several generator letters in one column and no exchange. The folding laws gain a "generator / generator" multiplication case. It is handled like (10) and (11), on vertical chains and on the context R with several Z discs, because each generator letter `e_g`, including its own internal κ's over expanded paths, is always substituted as a whole. So the expected statement is: **RC(3) holds for `Q↑Var(Q)` for every chain Q**. More generally, it should hold for every 2-dimensional context with acyclic 1-skeleton in which no two 2-generators are `∗₀`-composable after whiskering.

*Status: sketch.* The generalised folding laws have not been written out in full. The 2-disc cylinder (question 1 of round 3) is different again: it has a 3-generator α↑, so 3-terms can contain a 3-variable, and that needs a dimension-3 analogue of Theorem A's sequentialization and exchange.

### 7.6 Exchangeable letters: the cylinder with Y = {x, f, g} (attempt, 2026-11-18)

This is question 1 of `conjectures/outbox/naturality-arbitrary-depth-r6.md`, the smallest case where two generator letters can be applied in either order. I attacked it while the prompt is out. **Outcome:** the exchange problem disappears in this case, because the unselected vertex y is a cut vertex. Normal forms can be *horizontal*, `N₁ ∗₀ N₂`, instead of a chosen vertical order. The remaining work is the forced-order machinery of rounds 2 and 5, applied on each side of y, plus one interchange coherence. What follows is a proof sketch. Status is at the end.

**The context.** `W = (x⁻, x⁺, X : x⁻ → x⁺, y, z, f⁻ : x⁻ → y, f⁺ : x⁺ → y, F : f⁻ ⇒ X ∗₀ f⁺, g⁻, g⁺ : y → z, G : g⁻ ⇒ g⁺)`. This is §1.3 of the prompt, with the factors `y↑` and `z↑` omitted. Every directed path from `{x⁻, x⁺}` to z passes through y, and there is no edge out of z or into x⁻. So `W = W₁ ∨_y W₂`, where
- `W₁ = (x⁻, x⁺, X, y, f⁻, f⁺, F)` is a single-letter context, and
- `W₂ = (y, z, g⁻, g⁺, G) = D²`.

**Lemma W0 (the summands).**
- (a) A term of W whose 0-boundary lies in W₁ is literally a term of W₁. This follows from the support lemma (§4.3), because hom-sets of the free strict ω-category on a wedge between objects of W₁ use only generators of W₁. The same holds for W₂.
- (b) RC(n) holds in W₂ = D² for every n. The support of a term of D² is one of D⁰, D¹ (either edge) or D², because no strict cell has support `{y, z}` or `{y, z, g⁻, g⁺}`. Each of these is a pasting context, so two parallel terms with the same strict image are full in the same pasting context and are joined by one coherence there.
- (c) RC(3) holds in W₁ by the round-2 method (§7.4). x⁻ is the unique source and y the unique sink, and every 2-term containing F spans x⁻ → y. So inactive columns are point-supported, exactly as in the lax square, and W₁ is the lax square with `y↑` collapsed. *(Same method; not re-derived line by line.)*

**Lemma W1 (cut-vertex column lemma).** Let `t = coh_{P,A}[γ]` be a term of any dimension whose 0-boundary runs from `{x⁻, x⁺}` to z. Rank the 0-variables x⁻ < x⁺ < y < z. Then:
- the images `γ(v₀), …, γ(v_m)` of P's 0-vertices are non-decreasing, because each column contains a 1-variable and 1-terms only go forward;
- either some `γ(v_j) = y` (a *split*), or exactly one column crosses y;
- in a split, `P = P₁ ∨ P₂` with `γ = γ₁ ∨ γ₂`, where γ₁ lands in W₁ and γ₂ in W₂ by W0(a). Each side has at most one active column (one whose entries contain a 2-variable). On the left it spans x⁻ → y, on the right y → z, and all other columns are point or path columns;
- with a crossing column, every other column is inactive.

*Proof.* Monotonicity is as stated. If no vertex goes to y, the rank jumps from ≤ 1 to 3 at exactly one column. A term containing F has, by the support lemma, a strict image containing F, so it spans x⁻ → y; likewise G spans y → z. ∎

So **two active columns occur only in a split, one on each side of y**. That is the "two letters in different columns" configuration of the r6 prompt, and it is always a horizontal composite at the level of the arity.

**Normal forms.** Let A be a crossing 1-term with `π(A) = l · r`, where l ∈ {f⁻, X f⁺} and r ∈ {g⁻, g⁺}. Its canonical split is `Â := l̂ ∗₀ r̂`, with `l̂ ∈ {f⁻, X ∗₀ f⁺}` and `r̂ ∈ {g⁻, g⁺}` fixed literal terms; Â depends only on π(A). A crossing 2-term with `π = α ∗₀ β` (α ∈ {id, F}, β ∈ {id, G}) gets

```
N(A, B) := κ(A, Â) · ( N₁(α) ∗₀ N₂(β) ) · κ(B̂, B)
```

where N₁ is the round-2 normal form of W₁ between l̂ and l̂′, and N₂(G) = G, N₂(id_r) = κ(r̂, r̂). Both exchange orders have the same strict image F ∗₀ G, so they get the same normal form. Nothing chooses an order. The two orders are joined to the horizontal composite by the exchange coherences, which are single coherences over `D² ∗₀ D²`:

```
χ_L : (F ∗₀ g⁻) · ((X ∗₀ f⁺) ∗₀ G) ⇛ F ∗₀ G,      χ_R : (f⁻ ∗₀ G) · (F ∗₀ g⁺) ⇛ F ∗₀ G.
```

**Normalisers** `ν_T : T ⇛ N(σT, τT)`, for a crossing 2-term T, are built by induction on T, on the round-5 pattern `ν_T = v_H[η] ; D`.
- *No 2-variables.* Proposition P∞: one coherence over the path context.
- *Split.* Factor literally, `T = H[η]`, through a frame `R = R_L ∗₀ R_R` with at most one retained column on each side; point and path columns are pulled back as in §7.5. Then `v_H : H ⇛ κ · (LF(z₁, …) ∗₀ LF(w₁, …)) · κ` is one coherence over the pasting context R. After evaluation, the left entries `η(zᵢ)` are W₁-terms, normalised and folded by the W₁ theory; the right entries are W₂-terms, normalised by W0(b). The outer κ's are merged by the fixed-whiskering cells ρ and the multiplication μ of round 5.
- *Crossing column.* `T = H[η]` through `R = (path) ∗₀ C_n`, `v_H : H ⇛ κ · LF(z) · κ`, and each `η(zᵢ)` is a crossing 2-term, normalised by induction. The vertical product of horizontal normal forms is folded in three steps.
  1. Contract the κ's at each join (μ). The inner comparison is `κ(Ŝ, Ŝ)` with literally equal endpoints, because canonical splits depend only on the strict path.
  2. Apply the **horizontal fold** `μ^h : (z₁ ∗₀ w₁) · (z₂ ∗₀ w₂) ⇛ (z₁ · z₂) ∗₀ (w₁ · w₂)`, one coherence over `C₂ ∗₀ C₂`.
  3. Fold each side.

**3-terms and fusion.** W1 holds for arities of every dimension. For a 3-term `G : T ⇛ T′`, build `Λ_G : G ; ν_{T′} ⇛ ν_T` by induction on G, as in round 5.
- *A split head* is a ∗₀-composite, at the level of its frame, of a W₁ 3-column and a W₂ 3-column. Its Λ is the W₁ Λ (round 2) and the W₂ Λ (one coherence), joined by the 4-coherence that relates μ^h to 3-cells in each factor. That is a coherence over `V(k₁, …) ∗₀ V(k′₁, …)`, which is a pasting context.
- *A crossing head* has crossing 3-term entries. Their Λ's exist by induction, and the vertical fold needs μ^h to be natural in 3-cells. That is again a 4-coherence over `V(𝐤) ∗₀ V(𝐤′)`.

Right cancellation of the invertible ν then gives RC(3), exactly as in §7.4.

**What is new, and what is not written out.**
- *New, and complete on paper:*
  - Lemma W1;
  - the horizontal normal form, which makes exchange classes a non-issue here;
  - χ_L, χ_R and μ^h, all explicit coherences over pasting contexts.
- *Written as a sketch:*
  - the evaluation-fusion cells `E_{u,σ}` for split frames (the 4-cells comparing the normaliser of `u[σ]` with the evaluated relative normaliser);
  - the 4-laws for μ^h.

  Each needed cell is a full coherence over a pasting context of the form `V(𝐤) ∗₀ V(𝐤′)` or `C_n ∗₀ C_m`. I have not checked that the induction closes with no hidden cell of another shape, which is the step the round-5 verification checked line by line. So the status is **proof sketch, at the round-3 standard; not verified.**

**Scope.**
- *Chains.* The argument uses only that y is a cut vertex. On a chain, an unselected vertex x_i is always a cut vertex of `Q↑Y`, so every selection on a chain splits as a wedge of segments, each a forced-order piece in the sense of round 5. So I expect **RC(3) for every up-closed selection on every finite chain**, given the wedge fusion above and forced-order RC(3) for segments with unselected ends.
- *The 2 × 2 grid* (question 2 of the r6 prompt, and the Gray-contexts case) has no cut vertex: y is selected, so `y⁻ ≠ y⁺`. Exchange there is not removed by this device and stays open.

**Machine checks** (`tools/rc3_wedge.py`, `src/CaTTExp/Generated/WedgeRC3.agda`, 381 checks, about 13 s):
- *Python:* Lemma W1 on 688 crossing subterms of generated 2-, 3- and 4-terms (380 splits, 308 crossing columns), and frame stability on 15 instances.
- *Agda:*
  - 56 literal factorisations `γ = δ[η]` through one- or two-column frames, with H typed and η a well-typed substitution;
  - 50 frame normalisers `v_H`, typed over R, and their instances in W;
  - χ_L, χ_R, the two 3-terms relating the exchange orders, and a 4-term between them;
  - μ^h over `C₂ ∗₀ C₂`, and its instance on the layers of `(F ∗₀ g⁻) · ((X ∗₀ f⁺) ∗₀ G)`.
- *Negative control:* a swapped type on the exchange 3-term is rejected.

### 7.7 Machine checks of the chain-cylinder construction (round 5, 2026-11-18)

`tools/rc3_chain.py` and `src/CaTTExp/Generated/ChainCylinderRC3.agda` (172 checks, about 36 s) instantiate §§1–2 of the round-5 answer on the full cylinder of `x₀ → x₁ → x₂ → x₃`. The Agda checker accepts:
- the raw letters `E_i^{a,b} = L_i⁻ ∗₀ (F_i ∗₀ R_i⁺)`, and 22 normal forms N_w (3), for every forced word on the endpoint pairs (0,3), (1,3) and (0,2). This includes the boxed three-letter form (5), with its seven list entries;
- the multiplication `μ_{u,v} : N_u(A,B) · N_v(B,C) ⇛ N_{uv}(A,C)` (7), for all 20 splits of all words on (0,3), including the empty-word cases. Each is the reassociation coherence on `C_N`, followed by the contraction `m_p` inserted as a composition coherence on `V_N(0,…,1,…,0)`. Each has exactly the stated type;
- the two fold 4-cells of §2.2: overlapping pairs (a direct 4-coherence on the path `P₃`) and disjoint pairs (interchange on `V(1,1)`);
- 42 literal frame factorisations of generated 2-terms, each with exactly one active column (asserted), H typed over the frame `P_ℓ ∗₀ C_n ∗₀ P_r`, and η well typed.

Negative control: a swapped type on a μ is rejected. These checks cover the constructors and the fold (§2 of the answer). The normalisers, fusion and the 3-term induction (§§4–5) are not generated.

### 7.8 RC(3) for the 2 × 2 grid (internal proof, thread RCX, 2026-11-18)

This is question 1 of `conjectures/outbox/gray-contexts-r7.md`: the smallest Gray context with two generator letters that commute and no cut vertex of the whole context between them. **Outcome:** RC(3) holds. The path lattice is an ordinal sum `{⊥} ⊕ {0,1}² ⊕ {⊤}`. All exchange happens inside the middle block, and every cell in that block has the centre vertex (1,1) as a cut vertex. So the proof is the round-5 forced-chain construction (§7.7) at the two ends, glued to the round-6 two-letter construction (`conjectures/answered/naturality-arbitrary-depth-r6-2026-11-18.md`) in the middle. The only new ingredient is the multiplication table that mixes the two, and its 4-laws turn out to be laws of kinds already used in rounds 5 and 6. Status is at the end of the subsection.

**The context.** `G₂₂` has vertices `(i, j)`, `0 ≤ i, j ≤ 2`, edges `h_ij : (i,j) → (i+1,j)` and `v_ij : (i,j) → (i,j+1)`, and four lax squares

```
S_ij : h_ij ∗₀ v_{i+1,j}  ⇒  v_ij ∗₀ h_{i,j+1}          (i, j ∈ {0, 1}).
```

This is the strict Gray product of two paths of length 2, and its full sub-squares have the orientation of the lax square (§7.4) with `f = h`, `↑ = v`.

**Lemma G1 (paths and strict cells).** Put `l₀ = h₀₀v₁₀`, `l₁ = v₀₀h₀₁` (the paths (0,0) → (1,1)) and `r₀ = h₁₁v₂₁`, `r₁ = v₁₁h₁₂` (the paths (1,1) → (2,2)). The six paths (0,0) → (2,2) are

```
⊥ = hhvv,   (i, j) := l_i r_j  for i, j ∈ {0, 1},   ⊤ = vvhh,
```

ordered as the lattice `L = {⊥} ⊕ {0,1}² ⊕ {⊤}`. The covers are `⊥ → (0,0)` by S₁₀, `(0,j) → (1,j)` by S₀₀, `(i,0) → (i,1)` by S₁₁, and `(1,1) → ⊤` by S₀₁. Between two paths p, q there is exactly one strict 2-cell if p ≤ q, and none otherwise.

*Proof.* The 2-cells of the free strict 2-category are 2-paths of whiskered generators modulo exchange moves (§2, Step 4). A whiskered generator adds one box to the Young diagram of the path, so a 2-path from p to q is a saturated chain of `[p, q]`. Two saturated chains differ only inside the square `[(0,0), (1,1)]`. There, S₀₀ acts on positions 1–2 of the path and S₁₁ on positions 3–4, so the two chains are related by one exchange move. ∎ *Machine-checked by enumerating all 2-paths and their exchange classes: 20 strict cells, one class each.*

**Sub-context transfer.** If RC(n) holds in Γ, it holds in every dependency-closed sub-context Γ′ ⊆ Γ, and in every context isomorphic to one. *Proof.* Take parallel n-terms T, T′ of Γ′ with `π T = π T′`. RC(n) in Γ gives an (n+1)-term Θ : T → T′ of Γ. Its strict image is the identity on `π T`, which uses only generators of Γ′. By the support lemma (`supp(π Θ) = supp Θ`), Θ uses only variables of Γ′, so it is a term of Γ′. ∎ RC is also invariant under the opposite meta-operations of Benjamin–Markakis (arXiv 2402.01611), which preserve typing and send strict images to opposite strict images. Here this is used for the reversal of 2-cells.

**The fibres.** A 2-term whose 0-boundary is not (0,0) → (2,2) lives, by the support lemma, in a proper sub-rectangle. That sub-rectangle is a path, a lax square, a cylinder of a composable pair, or the 2-opposite of one. RC(3) holds there by Proposition P∞, §7.4 and round 3. So only 3-terms between 2-terms over (0,0) → (2,2) remain. By Lemma G1 their strict 2-boundaries are the intervals `[p, q]` of L.

| Interval [p, q] | Letters | Status |
|---|---|---|
| p = q | none | Proposition P∞ |
| the six covers | one square, with fixed path pieces | sub-context of a full chain cylinder or its 2-opposite: round 5 and transfer |
| `[⊥,(1,0)]`, `[⊥,(0,1)]`, `[(1,0),⊤]`, `[(0,1),⊤]` | two squares in a forced order | a 2 × 1 or 1 × 2 grid with one pendant edge: a sub-context of the full cylinder of x₀ → x₁ → x₂ → x₃ or of its 2-opposite (for example `[⊥,(1,0)]`: S₁₀ = F₁, S₀₀ = F₂, pendant v₂₁ = a₃⁺): round 5 and transfer |
| `[(0,0),(1,1)]` | S₀₀ and S₁₁ in either order | two lax squares wedged at (1,1): the round-6 construction with both letters squares (below) |
| `[⊥,(1,1)]`, `[(0,0),⊤]`, `[⊥,⊤]` | the block exchange plus one or two forced end letters | **new** (below) |

`[(0,0), ⊤]` is the image of `[⊥, (1,1)]` under the (1,2)-opposite with `(i,j) ↦ (2−i, 2−j)`. That opposite is an automorphism of G₂₂ with `S_ij ↦ S_{1−i,1−j}`. The construction below is uniform in any case.

**Lemma G2 (head shapes).** Let `T = coh_{P,A}[γ]` be a term of dimension 2 or 3 whose 0-boundary is (0,0) → (2,2), and let p, q be the paths of its 1-boundaries.
1. Every 0-vertex of P is sent to a vertex on both p and q.
2. If `p ≠ q` and p, q share only their endpoints, then exactly one 0-column of P is active (has an entry containing a 2-variable). All the others are point-supported at (0,0) or (2,2). This happens exactly for the three new intervals.
3. Two active columns are always separated at (1,1). The interval then lies in the block, the left column's value is `1` or S₀₀, and the right column's value is `1` or S₁₁.

*Proof.* (1) The source and target 1-terms of T traverse the images of all 0-vertices of P. (2) (0,0) is the unique source and (2,2) the unique sink, so a column over a single endpoint has an empty path, as in §7.4. (3) An inner common vertex other than (1,1) is (1,0), (2,1), (0,1), (1,2), (2,0) or (0,2). At the first four, one side of the cut is a single shared edge, whose strict value is an identity. The last two lie only on ⊥ or only on ⊤, so the value is an identity there. ∎ *Machine-checked on 1064 subterms of generated 2-, 3- and 4-terms: 67 prime one-column heads, 44 heads split at (1,1).*

So **two active columns occur only in the block, split at the centre**. In the prime fibres every head is one vertical column, with point-supported columns at the unique source and sink. That is the round-2/round-5 situation, with entries whose values are arbitrary intervals of L.

**Normal forms.** Fix the representatives `l̂₀ = h₀₀ ∗₀ v₁₀`, `l̂₁ = v₀₀ ∗₀ h₀₁`, `r̂₀`, `r̂₁` likewise, `p̂_{ij} = l̂_i ∗₀ r̂_j`, and right-nested `⊥̂`, `⊤̂`. The raw letters are:
- *Chain letters*, as in round 5 (2): `E_up = h₀₀ ∗₀ (S₁₀ ∗₀ v₂₁)` and `E_dn = v₀₀ ∗₀ (S₀₁ ∗₀ h₁₂)`.
- *Block letters*, as in round 6 (3)–(4): for `δ = (i,j) → (i′,j′)` in `{0,1}²`, `E_δ = a_{ii′} ∗₀ b_{jj′}`, where `a₀₁ = S₀₀`, `a_ii = 1_{l̂_i}`, `b₀₁ = S₁₁`, `b_jj = 1_{r̂_j}`. Identity factors are kept.

The word of `[p, q]` (p < q) is: `E_up` if p = ⊥; then `E_{p′→q′}` if `p′ ≠ q′`, where `p′ = (0,0)` if p = ⊥ (else p) and `q′ = (1,1)` if q = ⊤ (else q); then `E_dn` if q = ⊤. So a word has at most one block letter. The normal form is the round-5 list

```
N_{p,q}(A, B) = LF[ κ(A, S₁), E₁, κ(T₁, S₂), E₂, …, E_k, κ(T_k, B) ],        N_{p,p}(A, B) = κ(A, B),
```

with `S_m`, `T_m` the literal boundaries of the letters. A comparison is kept between any two letters.

**Multiplication.** `μ_{p,q,r} : N_{p,q}(A,B) · N_{q,r}(B,C) ⇛ N_{p,r}(A,C)` is built in this order:
1. reassociate the concatenated list (a coherence on `C_N`);
2. contract the junction pair `κ(T, B) · κ(B, S) ⇛ κ(T, S)` by path multiplication, inserted on `V_N(0,…,1,…,0)`, as in round 5 (7);
3. *if the letters on both sides of the junction are block letters*, round 6 (13) steps 3–5: `κ(q̂, q̂) ⇛ 1_{q̂}` on the actual path, then unit removal on C₂, then `M_{δ,ε} = I ; (m^F ∗₀ m^G)`, with I the interchange on `C₂ ∗₀ C₂`.

The concatenated word, with the two block letters merged at a block/block junction, is the word of `[p, r]`. So μ has the stated type. *Machine-checked: all 50 composable pairs, 8 of them with a block merge, typed by the certified checker.*

**The 4-laws of μ.** We need the two bracketings of `N₁ · N₂ · N₃` to be joined. Classify the two junctions as *sep* (step 2 only) or *mer* (steps 2–3).
- *sep/sep*: round 5 §2.2. Disjoint pairs use the interchange on `V(1,1)`. When the middle word is empty, the overlapping pairs use one path 4-coherence.
- *mer/mer*: block chains have length ≤ 2, so this needs an empty middle word. It is then round 6's laws: path contraction, unit and reassociation naturality, and the raw law (12) on `D²(F) ∗₀ D²(G)`.
- *sep/mer* with a non-empty middle word: the merge and the contraction act at disjoint slots. The comparison is the interchange coherence on `V(1,1)`, with the whole merge 3-cell and the contraction 3-cell as its two 3-arguments, plus reassociations.
- *sep/mer* with an empty middle word: both routes do the same contractions in a different order and then the same merge. That is round 5's overlapping-pair 4-cell, whiskered by the merge.

So **no new kind of 4-law appears**. The table only combines round-5 and round-6 laws.

**Normalisers and fusion.** For a 2-term T with value `[p, q]`:
- *Settled fibres (rows 1–3 of the table).* Use the established normalisers (rounds 2, 3 and 5, through the sub-context embedding). Transport them to the present letters by fixed raw-letter conversions. For example, `S₀₀ ∗₀ 1_{r̂₀}` versus the round-5 whiskered letter `S₀₀ ∗₀ r̂₀` is one coherence over `D²(S₀₀) ∨₀ C₂`. Round 6 does the same in its §7 ("transported to conventions (5)–(6)"). The conversions commute with the laws by naturality in the letter, with formal letters, before substitution.
- *Block fibre.* Use round 6 §§5–7 verbatim, with both local theories lax squares (rows 2–3) instead of a triangle and a disc. Heads are `C_n` or `C_m ∗₀ C_n` split at (1,1) (Lemma G2). The horizontal fold ψ (18), the horizontal–vertical 4-cell (19) and the point-column clause (27) are unchanged. The local normal forms are the lax-square ones, `κ · S · κ`.
- *Prime fibres.* By Lemma G2 the head factors literally through one column `C_n`, or `V_n(𝐤)` in dimension 3. Put `ν_T = v_H[η] ; D_{B_H,η}`, where `v_H` is the one coherence on the column and D is the vertical fold of the entries' normalisers by μ. The entries are proper subterms of any value, normalised by recursion.

Fusion `F_{u,σ}` (round 6 (30)) is by induction on the relative term u, with the evaluator grammar of round 6 (28): variable, path-only, `U · V` (μ), `U ∗₀ V` at (1,1) (ψ), point column (`B_q`), fixed path whiskering. Its 4-cells are the μ-laws above, round 6's (19), top-argument naturality (depth 1), and the actual-path laws (15)–(16). The 3-term induction `Λ_J` (round 6 (31)–(33)) and right cancellation (34) are unchanged. Hence

```
RC(3) for G₂₂.
```

This is the 2 × 2 case of question 1 of the gray-contexts r7 prompt: RC(3) in a 2-dimensional Gray context where two letters commute and no cut vertex of the whole context separates them. It is the 2-skeleton step for RC(3), hence uniqueness in G(3), of 3-dimensional Gray contexts that contain a 2 × 2 grid. The grid is not a cylinder `Q↑Y` of a pasting context, so it gives no new instance of N directly. Its method is what the D² ∗₀ D² cylinder needs (§7.9).

**What is new, and the status.**
- *New:*
  - the lattice decomposition and Lemma G2, which together locate every exchange at a cut vertex of the cells it occurs in;
  - the mixed normal form, with at most one block letter between forced chain letters;
  - the μ table and the case analysis of its laws.
- *Status: internal proof at the round-5/6 standard.* The case lists are complete and checked. The new constructors and a representative of every new kind of 4-cell are machine-checked. The fusion 4-cells are not all written out, and that is the step the external verifications checked line by line. **Not externally verified.** **Superseded as the reference result** by the verified researcher proof of the same statement (`conjectures/answered/gray-contexts-r7-2026-11-18.md`); this subsection is kept as an independent route whose constructors are machine-checked.

**Why this works, and what it does not reach.** In the grid, the trace poset of every strict cell is series-parallel: S₁₀ ; (S₀₀ ∥ S₁₁) ; S₀₁. A series-parallel poset has a canonical normal form, a vertical list of horizontal products, with no choices. That is why the round-5 and round-6 pieces glue with no new law. The 2-skeleton of the D² ∗₀ D² cylinder (§7.9) contains the N-shaped poset, which is not series-parallel, so a choice is needed there.

**Machine checks** (`tools/rc3_grid.py`, `src/CaTTExp/Generated/GridRC3.agda`, 261 checks, about 3 min):
- *Python:* the classification of Lemma G1; Lemma G2 on 1064 subterms; frame stability.
- *Agda:*
  - the 20 normal forms;
  - the 50 multiplications, each with exactly its stated type;
  - the exchange χ at `(0,0) → (1,1)` and its compatibility 4-term (round 6 (8));
  - the raw law (12) in the block, formed with formal letters on `D²(F) ∗₀ D²(G)` and substituted;
  - `Z₃` on `C₃ ∗₀ C₃` and ζ;
  - the core interchange 4-cell of a sep/mer law (a block merge and a separator contraction at disjoint slots, on `V(1,1)`);
  - 61 literal frame factorisations, with H typed over R and η a well-typed substitution.
- *Negative control:* μ_{⊥,(1,0),⊤} with source and target swapped is rejected.

### 7.9 The 2-skeleton of the D² ∗₀ D² cylinder (proof sketch, thread RCX, 2026-11-18)

This is the 2-dimensional part of question 2 of `conjectures/outbox/naturality-arbitrary-depth-r7.md`.

**The context.** Let `Q = (x, y, z, f₀, f₁ : x → y, A : f₀ ⇒ f₁, g₀, g₁ : y → z, B : g₀ ⇒ g₁)`, and let W₂ be the 2-skeleton of `Q↑Var(Q)`. Its variables are:
- vertices `x^±, y^±, z^±` and cylinder edges `X, Y, Z`;
- edges `f_i^±`, `g_j^±`;
- 2-cells `A^±`, `B^±`, `F_i : f_i⁻ ∗₀ Y ⇒ X ∗₀ f_i⁺` and `G_j : g_j⁻ ∗₀ Z ⇒ Y ∗₀ g_j⁺`.

The 3-generators `U_A`, `U_B` are omitted. The paths x⁻ → z⁺ are `(i, j, c)`, with c the crossing position: `R = f_i⁻ g_j⁻ Z`, `M = f_i⁻ Y g_j⁺`, `L = X f_i⁺ g_j⁺`. The paths in R ∪ M pass through y⁻, and those in M ∪ L pass through y⁺.

**Independence.** Two letters can be adjacent and act on disjoint segments exactly when one is a *left* letter (A⁻, A⁺, F_i) and the other a *right* letter (B⁻, B⁺, G_j), and they are not the pair (G, F). G must precede F, because F needs the edge Y that G produces. Every independent pair is separated by y⁻ or by y⁺. No three letters are pairwise independent.

**Lemma D1 (factorisation).** Every strict 2-cell w between paths x⁻ → z⁺ factors uniquely as

```
w = w₁ · w₂,     w₁ ∈ ⟨A⁻, B⁻, G_j⟩ (a product at the cut y⁻),     w₂ ∈ ⟨F_i, A⁺, B⁺⟩ (a product at the cut y⁺).
```

*Proof.* Call A⁻, B⁻, G_j block-1 letters and F_i, A⁺, B⁺ block-2 letters. Take a block-2 letter immediately followed by a block-1 letter in a 2-path. After F or A⁺ the path is in L, where no block-1 letter applies. After B⁺ the path is in M or L, and B⁻ and G need R. So the only possible pair is B⁺ then A⁻ in M, and those two commute: they act on g⁺ and f⁻ on either side of Y. Bubble-sorting therefore moves every 2-path to block-1 letters followed by block-2 letters, by exchange moves. The block-1 part lives in R ∪ M, so it is a cell of `D²(A⁻) ∨_{y⁻} C_R`, where C_R is the right D²-cylinder's paths from y⁻. There the class is determined by the left and right words, which are forced (round 4). The same holds for block 2 on `C_L ∨_{y⁺} D²(B⁺)`. ∎ *Machine-checked: all 2-paths from all 12 source paths enumerated; 67 strict cells; each exchange class has a block-sorted representative, and distinct classes have distinct factorisations.*

**Why a choice is needed here.** Take the cell `f₀⁻g₀⁻Z ⇒ X f₁⁺ g₁⁺` through A⁻, G₀, F₁, B⁺. Its trace poset is `A⁻ < F₁ > G₀ < B⁺`, the N-shaped poset, which is not series-parallel. The cell has no canonical vertical list of horizontal products. Lemma D1 makes the choice: A⁻ early, B⁺ late.

**Normal forms.** For the block-1 representatives, write paths in R ∪ M as `f_i⁻ ∗₀ (g_j⁻ ∗₀ Z)` or `f_i⁻ ∗₀ (Y ∗₀ g_j⁺)`; the inner factors are literally the boundaries of G_j. For block 2, write paths in M ∪ L as `(f_i⁻ ∗₀ Y) ∗₀ g_j⁺` or `(X ∗₀ f_i⁺) ∗₀ g_j⁺`; the outer factors are the boundaries of F_i. The raw letters are:
- `E¹(w₁) = a ∗₀ b`, where a is `A⁻` or an identity, and b is a local raw word of C_R: `B⁻ ∗₀ Z`, `G_j`, `(B⁻ ∗₀ Z) · κ · G₁`, or an identity;
- `E²(w₂) = a′ ∗₀ b′`, where a′ is a local word of C_L (`F_i`, `X ∗₀ A⁺`, `F₀ · κ · (X ∗₀ A⁺)`, or an identity), and b′ is `B⁺` or an identity.

Then

```
N(w) = LF[ κ, E¹(w₁), κ, E²(w₂), κ ]          (absent letters omitted; N(1) = κ).
```

**Lemma D2 (the only exchange in μ).** Concatenate `N(u) · N(v)`. If `u₂ ≠ 1` and `v₁ ≠ 1`, then `u₂ = B⁺` and `v₁ = A⁻`, both in phase M. *Proof.* As in D1: after F or A⁺ no block-1 letter applies, and from M the only block-1 letter is A⁻. ∎

So μ has three non-trivial cases:
- a block-1 merge (`u₂ = 1`): round 6 M at y⁻, with local multiplications in `D²(A⁻)` and in C_R. The latter are round-5 list multiplications, for example `(B⁻ ∗₀ Z) · G₁ ⇛ LF[B⁻ ∗₀ Z, κ, G₁]`;
- a block-2 merge (`v₁ = 1`): the same at y⁺;
- the exchange case: apply

  ```
  χ_M : LF[ E²(B⁺)_{f₀}, κ, E¹(A⁻)_{g₁} ]  ⇛  LF[ κ, E¹(A⁻)_{g₀}, κ, E²(B⁺)_{f₁}, κ ],
  ```

  then contract the κ pairs on both sides and merge with the neighbours. χ_M is **one coherence over `D²(a) ∨₀ D¹(e) ∨₀ D²(b)`**. All the 1-cells involved (f_i⁻, Y, g_j⁺) are single edges, so the κ's of the instance are literally the substituted formal κ's.

*Machine-checked:* all 203 composable pairs (27 block-1 merges, 27 block-2 merges, 4 exchanges, 145 separators) have exactly the type `N(u) · N(v) ⇛ N(uv)`.

**4-laws of μ.** In a triple `N₁ · N₂ · N₃`, A⁻ and B⁺ occur at most once. So each route applies χ_M at most once, and the two routes apply the same multiset of operations: χ_M, merges at y⁻, merges at y⁺, and contractions. They differ in order and association only. The laws are therefore:
- round-5 and round-6 laws inside a block;
- interchanges of operations at disjoint slots;
- round-5 overlapping-pair path laws where χ_M's boundary κ's meet the neighbouring ones.

**Heads.** Lemma G2 holds verbatim with these changes. Prime values are those containing both G and F; their heads are one column, with point columns at the unique source x⁻ and sink z⁺. Otherwise active columns are separated only at y⁻ and/or y⁺. *Machine-checked on 390 subterms.*

**Fusion, and what is new.** The evaluator grammar of §7.8 gains three clauses:
- a horizontal fold ψ¹ at y⁻ and ψ² at y⁺ (round 6 (18), with local theories D²(A⁻) and C_R, or C_L and D²(B⁺));
- a three-column fold ψ_M for heads split at both y⁻ and y⁺ in phase M. It is the zip `Z` on `C ∗₀ D¹(Y) ∗₀ C`, followed by un-merging `A⁻ ∗₀ Y ∗₀ B⁺` into the two block letters;
- the **transfers** `τ_A, τ_B` between block-1 and block-2 coordinates of a phase-M letter. For example, `1_{f⁻} ∗₀ (Y ∗₀ B⁺) ⇛ κ · (1_{f⁻ ∗₀ Y} ∗₀ B⁺) · κ`, one coherence over `D¹ ∨₀ D¹ ∨₀ D²`. They are needed because ψ¹ produces B⁺ in block-1 coordinates while N puts it in block 2.

The new 4-law families are:
- (19)-type horizontal–vertical laws for ψ¹, ψ² and ψ_M, the last over `C₆ ∗₀ D¹ ∗₀ C₆`;
- the compatibility of τ with merges and with χ_M. These are formal coherences over `D²(a) ∨₀ D¹(e) ∨₀ D²(b)`, again because the letters' boundary 1-cells are single edges.

Each of these is a direct coherence over the named pasting context after the round-6 four-step reduction (pure recipes, top-argument naturality, actual-path laws, raw comparison).

**Status: proof sketch at the round-3 standard.**
- Lemma D1, Lemma D2, the normal forms, all multiplications, χ_M and the transfers are complete and machine-checked.
- The fusion laws for ψ_M and τ are named with their arities but not written out. **Not verified.**
- If the sketch is right, RC(3) holds for W₂. Combined with a two-generator extension lemma, which is still open (U_A and U_B interchange through (36), so item 20 of the gray-contexts prompt does not apply), it would give RC(3) for the full cylinder of D² ∗₀ D². **Both are now settled** by the verified naturality round-7 answer (`conjectures/answered/naturality-arbitrary-depth-r7-2026-11-18.md`), which proves RC(3) on the full cylinder; the cone round-5 extension theorem (`conjectures/answered/cone-over-coherences-r5-2026-11-18.md`) reduces any cylinder of a 2-dimensional Q to its 2-skeleton. This subsection is kept as an independent route.

**Machine checks** (`tools/rc3_d2d2.py`, `src/CaTTExp/Generated/TwoDiscCylinderRC3.agda`, 468 checks):
- the 67 normal forms;
- all 203 multiplications at their exact types;
- χ_M and four transfers;
- 64 frame factorisations;
- the generator interchange 4-term (36) of round 6 on the full cylinder, including U_A and U_B.

*Negative control:* χ_M with source and target swapped is rejected.

### 7.10 Machine checks of constructions from three verified answers (thread RCX, 2026-11-18)

`tools/rc3_r6.py` and `src/CaTTExp/Generated/RoundSixChecks.agda`. The certified checker accepts the following.
- **Cone, round 4** (`conjectures/answered/cone-over-coherences-r4-2026-11-18.md`), in `Cone(D² ∗₁ D²; c)`:
  - `S₁²` (2), with its target associator;
  - the 4-cell (14), formed over `D³ ∗₁ D³` with `M₁` and the right-frame comparison δ substituted. Its type is checked in Agda against the displayed type, built independently from M₁, R, δ and the frame cells (check `cone-e14-ty`).

  (15) is a composite of (14), unitor naturality and the associator. It is not assembled.
- **Gray contexts, round 6** (`conjectures/answered/gray-contexts-r6-2026-11-18.md`):
  - `Ω_P` (3) on `V(1,0,1)`, where `b₋` and `b₊` are non-trivial, and on `D³ ∨₀ D³`;
  - the point-support 4-term (6) over D³, with β′(y) the identity on a unitor 2-cell at y;
  - the interchange 4-coherence (11) over `D² ∨₁ D³ ∨₁ D³`, formally and substituted in the D² ∗₀ D² cylinder with `z ↦ U_A ∗₀ g₀⁺` and e a path-contraction 3-cell;
  - the local exchange law (24) over `D³ ∨₀ D³`.
- **Naturality, round 6** (`conjectures/answered/naturality-arbitrary-depth-r6-2026-11-18.md`), in `(x→y→z)↑{x,f,g}`:
  - the block multiplication M (11) for both orders;
  - ζ (14);
  - three instances of the horizontal fold ψ (18);
  - the first step (20) of the horizontal–vertical 4-cell, a coherence over `C₆ ∗₀ C₆`;
  - the two routes `(ψ₁ ∗₁ ψ₂) ; μ` and `I ; (μ^F ∗₀ μ^G) ; ψ` of (19). They are checked to be parallel, with the same type. The 4-cell (19) itself is a composite through depth-1 naturality and is not assembled.
  - (36) is in `TwoDiscCylinderRC3` (§7.9).

*Negative control:* (24) with source and target swapped is rejected.

### 7.11 General exchange in dimension 2: the strict homotopy basis and a reduction (thread RCX, 2026-11-18)

This is question 1 of `conjectures/outbox/gray-contexts-r8.md`. **Hypothesis (H):** Γ is finite and of dimension ≤ 2, its generating 1-graph is acyclic, and every 2-generator has nonempty source and target paths. **Outcome:** the combinatorics of exchange are settled in general. For each strict 2-cell, the exchange moves between its 2-paths have an explicit homotopy basis made of squares and hexagons, and both are single coherences over pasting contexts. What is left for RC(3) is two forced-order statements, (K) and (F) below. Neither involves exchanging two letters. Both are of the kind proved case by case in rounds 5–7. They are a proof sketch here.

**Lemma E1 (event posets).** Assume (H) and let c : p ⇒ q be a strict 2-cell of F(Γ). Then the 2-paths representing c are exactly the linear extensions of a poset (E_c, <), and an exchange move is exactly a swap of two adjacent incomparable events.

*Proof.* By ABGLM (arXiv 2312.00429), 2-cells of the free 2-category are 2-paths of whiskered generators modulo exchange moves.
- Give each edge occurrence of a path an *instance* name. A letter consumes the instances of its source segment and produces fresh instances for its target segment.
- Order the events (letter occurrences) of a word w by "e′ consumes an instance that e produced", transitively closed. This gives a poset E_w.
- An exchange move swaps two adjacent letters acting on disjoint segments. Neither consumes what the other produced, so it preserves events, instances and E_w.
- Conversely, let e, e′ be adjacent in w with e′ not consuming any instance that e produced. Then e′'s consumed segment and e's produced block are contiguous and disjoint. Both are nonempty by (H), so one lies strictly to the left of the other, and the two letters can be exchanged.
- Bubble sort reaches every linear extension of E_w from w through adjacent incomparable swaps. So the exchange class of w is Lin(E_w). ∎

With an empty boundary, this proof fails at the "strictly to the left" step: for a : 1_x → 1_x the letter has no position. That is the Eckmann–Hilton obstruction of §7.

**Lemma E2 (Squier basis).** Let X_c be the 2-complex with:
- vertices Lin(E_c);
- edges the exchange moves;
- one 2-cell for each *square*: two swaps at disjoint positions, in either order;
- one 2-cell for each *hexagon*: three consecutive pairwise incomparable events abc, with the two reduced routes abc → bac → bca → cba and abc → acb → cab → cba.

Then X_c is simply connected.

*Proof.* Fix L₀ ∈ Lin(E_c), and orient each exchange so that it removes an inversion relative to L₀. This rewriting terminates. Its only normal form is L₀: a linear extension L ≠ L₀ has an adjacent pair that L₀ orders the other way, and two events that two linear extensions order differently are incomparable.

Now take two descents at positions k < l.
- If l > k + 1, they commute: a square.
- If l = k + 1, the three events are pairwise inverted relative to L₀, so they are pairwise incomparable. Both routes to their reversal are descents: a hexagon.

So the rewriting is convergent, and squares and hexagons close all its local branchings. By Squier's homotopy lemma (ABGLM, Polygraphs, the homotopy-basis theorem for convergent 1-polygraphs), they generate all loops of the exchange graph. ∎

*Machine-checked* (`tools/rc3_exch.py`). For each context below and every pair of parallel paths, the script enumerates all 2-paths and checks:
- that exchange classes are exactly the sets of linear extensions (E1);
- that exchanges are exactly the adjacent incomparable swaps;
- that the descent rewriting is stuck only at L₀;
- that every local branching is a square or a hexagon (E2).

| context | strict 2-cells | 2-paths | largest class | square branchings | hexagon branchings | cells with three pairwise independent events |
|---|---|---|---|---|---|---|
| 1 × 1 grid (lax square) | 7 | 7 | 1 | 0 | 0 | 0 |
| 2 × 2 grid | 74 | 78 | 2 | 0 | 0 | 0 |
| 2 × 3 grid | 200 | 241 | 5 | 4 | 0 | 0 |
| 3 × 3 grid | 662 | 1419 | 42 | 402 | 49 | 25 |
| three bigons side by side | 54 | 67 | 6 | 0 | 1 | 1 |
| four bigons side by side | 174 | 286 | 24 | 6 | 18 | 11 |
| D² ∗₀ D² cylinder, 2-skeleton | 120 | 149 | 5 | 1 | 0 | 0 |
| two triangles and a bigon | 77 | 91 | 6 | 0 | 1 | 1 |

So the 2 × 3 grid (since proved, `conjectures/answered/gray-contexts-r8-2026-11-18.md`) needs only squares, while the 3 × 3 grid is the smallest grid that needs hexagons. A path in an m × n grid has at most min(m, n) corners of the form hv, and three pairwise independent faces need three of them.

**Lemma E3 (block-form laws).** Let a, b, c, d be the 2-variables of `D² ∨₀ D² ∨₀ D²` or of `D² ∨₀ D² ∨₀ D² ∨₀ D²`. The *block word* of an order of the letters is the vertical composite of the letters, each whiskered by the current source or target edges of the others. For two orders, the *block exchange* is the full coherence between their block words.
- The two hexagon routes are parallel full 3-terms, so one coherence 4-term connects them.
- The two orders of two disjoint exchanges are likewise connected by one coherence 4-term.

Both are substitution instances of a single coherence, with any 2-terms for the letters and any 1-terms for the edges. *Checked in Agda:* `Generated/ExchangeLaws.agda`, 2 checks, with a negative control (swapped hexagon type) rejected.

**The reduction.** In Γ fix the following data.
- Path representatives p̂.
- Pure-path connectors κ(s, t) : s → t between 1-terms with the same path. By Proposition P∞ these are coherent in every dimension, because acyclicity makes path labellings injective.
- For each strict 2-cell c and each w ∈ Lin(E_c), the word term T_w = κ₀ · L₁ · κ₁ · … · L_k · κ_k. Here L_i is the i-th letter whiskered by representatives.

Then:
- An *exchange in context* X_{w,i} : T_w → T_{w′} is the block exchange of Lemma E3, conjugated by a *block normaliser*. The block normaliser is a 3-term that splits κ_i into whisker-side pieces with Proposition P∞, and slides those pieces past L_i and L_{i+1}. Each slide is the item-24 coherence over `D²(α) ∨₀ D²(κ)`, with α's boundary edges sent to its declared boundary 1-terms. A square or hexagon of E2 in context is then the E3 coherence, up to a comparison of block normalisers.

RC(3) for Γ then follows from two statements.
- **(K) Rigid coherence.** Take two 3-terms between the same two 2-terms, each a composite of pure-path 3-terms inserted between letters and slides of pure-path 2-cells past letters, never exchanging two letters. Then the two are connected.
  - *Sketch.* Slides past one letter compose: a coherence over `D²(α) ∨₀ (D² ∨₁ D²)`. Slides past different letters interchange: a coherence over `V(1,1)`. Slides are natural in pure-path 3-cells: a coherence over `D²(α) ∨₀ D³`. With these, each such 3-term is connected to one canonical slide per letter, fixed by the change of that letter's whiskers, followed by pure-path parts that Proposition P∞ compares.
- **(F) Fusion.** Define normalisers by recursion on syntax: for u = coh_{Q, s→t}[τ] with Q of dimension ≤ 2,

  ```
  ν_u = ν^Q[τ] ; Φ_τ ; ξ.
  ```

  Here:
  - ν^Q : coh_Q[id] → T^Q is the coherence onto Q's block word;
  - Φ_τ flattens T^Q[τ] using ν_{τ(α)} for the 2-variables α of Q, item 15's D_m and Ω_m, and P∞;
  - ξ is the descent path of E2 to the chosen linear extension.

  Then ν_{a[σ]} is connected to ν_a[σ] ; Φ_σ ; ξ′, for every 2-term a over a context Δ and every σ : Γ ⊢ Δ.
  - *Sketch.* By induction on a. a[σ] = coh_Q[τσ] and ν^Q[τσ] = ν^Q[τ][σ] syntactically. The flattenings compare by the induction hypothesis on the τ(α), item 15's Ω_m, and (K). Any two descent paths with the same ends are connected by E2 and E3.

*Assembly.* Let H = coh_{P, a→b}[σ] : u → v be a 3-term. In P, RC(3) for pasting contexts writes coh_P[id] as ν^P_a, then exchanges of P's letters, then whiskered 3-variables of P, then (ν^P_b)⁻¹.
- Substitute σ.
- Expand each substituted P-exchange into elementary exchanges. This is the block-shuffle coherence over `C ∨₀ V_m ∨₀ C ∨₀ V_n ∨₀ C`, which is natural in the slots.
- Apply (F) to ν^P_a[σ] and ν^P_b[σ], and induction to σ of the 3-variables.

This shows ν_u⁻¹ ; H ; ν_v is connected to an exchange path. By E2 and E3, two exchange paths with the same ends are connected. So any two parallel 3-terms with the same strict image are connected.

**Status.**
- E1 and E2 are proved and machine-checked on the contexts in the table. E3 is checked in Agda.
- (K), (F) and the assembly are a proof sketch at the round-3 standard, with the 4-terms not generated. **Not verified.**
- If (K) and (F) hold, RC(3) holds under (H). With the cone round-5 extension theorem, RC(3) then holds for every 3-dimensional context whose 2-skeleton satisfies (H).
- The point of the reduction is that exchange stops being the obstacle. All of it is handled by E2 and two coherences over pasting contexts. What remains is a uniform statement of the relative fusion that rounds 5–7 proved case by case for the lax square, the chain cylinders, the cube hemispheres and the 2 × 2 grid.
- *Superseded (2026-11-20).* The verified RC round-7 answer (`conjectures/answered/relative-coherence-all-dimensions-r7-2026-11-20.md`, Response 87) proves RC_id(n) for every n on every finite positive 2-computad. Hypothesis (H) is a special case, so RC(3) under (H) and every higher RC_id(n) hold, and (K), (F) and the wedge lemma below are no longer needed for that result. The triangle context (α : f ∗₀ g ⇒ h) is positive, so RC(4) for it also holds, which settles the E11 triangle link. E1–E3 stay as an independent description of the exchange combinatorics.
- *Update after the RC r1–r4 answers (2026-11-19).* The 3 × 3 grid is positive, so by the polyplex reduction (`conjectures/answered/relative-coherence-all-dimensions-2026-11-19.md`; item 11 of the r4 prompt), RC(n) over a strict cell c is equivalent to RC(n) in c's generic polyplex P_c. For c = S₀₀ ∗₀ S₁₁ ∗₀ S₂₂ (the hexagon triple), P_c is the wedge of three lax squares at the cut vertices (1,1) and (2,2). So the hexagon instance of (K) in the grid is exactly RC(3) for that wedge. The same holds in general: by E1, an antichain of the event poset whose letters are adjacent in a word spans, in its polyplex, a wedge of single-generator contexts. Hence:
  - (K) restricted to an antichain block is the **wedge lemma**: RC(3) for A₁ ∨₀ ⋯ ∨₀ A_k at cut vertices, given RC(3) for each A_i. For k = 2 this is the matrix argument for two independent letters with a cut vertex (item 25 of the prompt in `conjectures/answered/gray-contexts-r8-2026-11-18.md`).
  - What remains of (K) is the forced-order part: letters joined by connectors that cross their boundary blocks. Its fibres have one linear extension, which is the line-word situation (item 22 of the same prompt).
  So the in-house target for the hexagon is the k-fold matrix argument for the wedge of three lax squares, replacing I with the three-factor interchange `(α ∗₀ β ∗₀ γ) · (α′ ∗₀ β′ ∗₀ γ′) ⇛ (α·α′) ∗₀ (β·β′) ∗₀ (γ·γ′)` over C₂ ∗₀ C₂ ∗₀ C₂. Generating Agda checks for the hexagon in the grid before that is proved would only check single coherences, so it is deferred.

### 7.12 Second-identity calls: a height measure that avoids the shift (thread RCX, 2026-11-20, sketch)

This addresses r10 item 64 / Question 1. Notation follows `conjectures/answered/relative-coherence-all-dimensions-r9-2026-11-20.md`, Responses 3–4.

**The cycle there.** Response 4 reduces first-identity calls at height m to second-identity calls at height m − 1. A second-identity call is then handled by:
1. the identity-tower shift (whisker by a fresh globe), which raises the height by one and lowers the identity level by one;
2. a four-link fold, which lowers the height by one and raises the level by one.

The net effect can be zero, so there is no well-founded measure.

**Proposal: no shift, localize at every identity level.** Write C(h, k) for the call: compare two parallel raw (h + k)-terms of value 1^k_d, where d is an intrinsic strict h-cell, in a strong-Steiner context of height h. (C(h, 1) is Response 3's first-identity call; C(h − 1, 2) is Response 4's second-identity call.)

1. **Higher localization.** The events of d are its top h-atoms. Fix the canonical linear extension L₀. The faces of the permutohedron whose vertices are all linear extensions form a complex. Its cells are the ordered set partitions of the events into antichain blocks, consistent with the order. A k-cell is a product of permutohedra on blocks of total excess k, so every block has at most k + 1 events. This complex is contractible: it is the cell complex of a T-convex set of topes of the braid arrangement (Björner–Las Vergnas–Sturmfels–White–Ziegler, *Oriented Matroids*, §4.2; Edelman). The descent-by-inversions matching gives an explicit collapse toward L₀, so it needs no search.
   - Running Response 4's serial-resolution steps 1–4 one level higher therefore localizes C(h, k) to blocks of at most k + 2 events.
   - k = 1 recovers Response 4's three events: squares and the braid hexagon. k = 2 adds the 3-cells: cubes, hexagonal prisms and the 4-event permutohedron.
2. **(k + 3)-link subdivision.** Subdivide each top h-generator into k + 3 links with fresh knots. The strong-Steiner check is Response 4's, with more knots. A block of at most k + 2 links never contains a whole subdivided generator, so every used segment has a free fresh end.
3. **Folds.** Fold each free end x with its unique link v, using Response 4's two fold formulas. The varying set {x, v} has lowest rank h − 1 under terms of rank h + k, so the fold uses **depth-(k + 1) naturality**. After all folds the context has height h − 1, and the inputs have value 1^{k+1}_{d′}. That is a call C(h − 1, k + 1).
4. **Measure.** Order calls lexicographically by input rank n = h + k and then by height h. Steps 1–3 keep n and strictly lower h. Every other call (lifts, old caps, inverse data) has smaller input rank. The base case C(0, k) is a single head on the point.

So the recursion is well-founded, with **no shift**. When d is itself an identity, Response 3's shift is still used, but only once at entry, at a fixed level, and it is never repeated.

**What this costs.** A call C(h, 1) unfolds to C(h − 1, 2), …, C(0, h + 1). It uses fold naturality of depths 2, …, h + 1.
- Depths 2 and 3 are search-free (Responses 3–4).
- Depth n ≥ 4 is r10 Question 1(c), restricted to *fold selections*: a free knot x and its single link v, with x↑ = v and v↑ a unitor.

Hence **Q1(a) reduces to Q1(c) for fold selections, given the higher localization lemma**. Conversely, Q1(c) is a special case of Q1(a). The two questions are equivalent up to that lemma.

**Where the circularity moves.** In Responses 3–4, depth-n naturality comes from comparisons in partial cylinders with about n nonglobular top ranks. Through this reduction, those comparisons again need fold naturality of depth up to n + 1. So with the known inputs this does not close unconditionally. It closes if fold naturality of every depth is built directly. That may be possible because a fold selection is special: (x, v) is a free face pair. Γ is the pushout of Γ′ along ∂⁻Dʰ ↪ Dʰ, and the fold is the retraction collapsing that elementary expansion. The local model is the partial cylinder Dʰ↑{x, v}, a lax triangle in dimension h (the triangle context for h = 1). This is the next thing to try.

**Status: sketch, not verified.**
- The contractibility input is standard. Its search-free collapse and the level-k version of Response 4's steps 1–4 are not written out in detail.
- No machine check yet.
- New compared with Response 4: replacing the shift by localization at every identity level, which makes height a well-founded measure. That isolates the remaining obligation as fold naturality of all depths.

## 8. Follow-ups and owners

- RC(n), n ≥ 3 (C1 and D2): out to researcher; internal attempts continue in this thread (NGC).
- C1b, mechanical check in the Agda checker (now including Theorem A's exchange step on a small instance): NGC.
- Mikhail's printed-rule defects: ledger D3b, owned by LIM-F.
- Agda for Gray contexts (D5) is unchanged.
- RC exchange step (thread RCX, 2026-11-18): §7.8 (2 × 2 grid, internal proof), §7.9 (D² ∗₀ D² 2-skeleton, sketch) and §7.10 (checks of round-6 constructions). The grid and the full D² ∗₀ D² cylinder are now settled by verified researcher answers (gray-contexts r7, naturality r7), and the several-3-generator question by the cone r5 extension theorem, so the RC(3) frontier is general exchange in dimension 2 (asked in `conjectures/outbox/gray-contexts-r8.md`). §7.11 settles its strict side (event posets; squares and hexagons are a homotopy basis; both are pasting-context coherences) and reduces RC(3) to two forced-order statements. Open, owned by RCX: proving (K) and (F) of §7.11 and generating them for the 3 × 3 grid's hexagon; RC(4) for the triangle context, which is RC(4) of a 2-dimensional context (E11 link, asked in gray-contexts r8); machine checks of the r5/r7 comparison lemma and grid flattening step.

## 9. Machine checks (C1b)

`tools/` contains a Python implementation of Theorem A as a term generator (`rc2.py`), for contexts with an acyclic 1-skeleton. It covers sequentialization, Lemma G, Lemma P, and exchange (Lemma E). It emits Agda modules that ask the certified checker `CaTTExp.Check` to infer each generated term's type, and assert by `refl` that the inferred type is the stated one. The Python side is untrusted. See `tools/README.md`.

| Generated module | Checks | Result |
|---|---|---|
| `UnitorNaturality` | the left unitor's naturality 3-cell at depth 2 over the lax square (§6 "partial progress" case of the N file), via Theorem A | typechecks (~50 s) |
| `ExchangeTwoBigons` | Theorem A with one exchange move (two side-by-side bigons) | typechecks (~3 min) |
| `AssociatorNaturality` | the associator's naturality 3-cell over the fully selected 3-chain: the ladder theorem's example, C1b | typechecks (5121 definitions, about 1 MB; 17 min and about 10 GB with `+RTS -M12G`) |
| `LaxSquareRC3` | Checks toward RC(3) for the lax square (§7.4–7.5): 43 active-column factorisations `γ = δ[η]` (2- and 3-dimensional arities, refl) with H typed over the retained column and η a well-typed substitution `R → S` (witnessed by the coherence `coh_{R, u→u}[η]`, u the unbiased composite of R); an exchange 4-term between a path 3-cell and a column coherence carrying F; the mixed law Ω_R (11) instantiated in S; 19 generalised factorisations for the composable-pair cylinder | typechecks (~11 s); negative control (swapped fill type) rejected |
| `WedgeRC3` | Checks toward RC(3) for Y={x,f,g} on x→y→z (§7.6): 56 factorisations through one- and two-column frames, 50 frame normalisers, the exchange coherences and a 4-term between the two exchange routes, the horizontal fold μ^h | typechecks (~13 s); negative control rejected |
| `ChainCylinderRC3` | Round-5 constructors on the cylinder of x₀→x₁→x₂→x₃ (§7.7): letters, 22 normal forms incl. (5), μ for all 20 splits, the fold 4-cells, 42 one-active-column frame factorisations | typechecks (~36 s); negative control rejected |
| `GridRC3` | RC(3) for the 2 × 2 grid (§7.8): 20 normal forms, 50 multiplications (8 with a block merge), the exchange and its compatibility 4-term, the raw law (12), Z₃, ζ, a sep/mer interchange 4-cell, 61 frame factorisations | typechecks (~3 min); negative control rejected |
| `TwoDiscCylinderRC3` | The D² ∗₀ D² cylinder (§7.9): 67 normal forms, 203 multiplications (incl. 4 through χ_M), χ_M, transfers, 64 frames; (36) on the full cylinder | ~10 min (local Agda 2.6.3); negative control rejected |
| `ExchangeLaws` | Block-form hexagon and square 4-coherences for general exchange (§7.11, `rc3_exch.py`, which also checks Lemmas E1 and E2 combinatorially) | typechecks (~4 s, 2 checks); negative control rejected |
| `RoundSixChecks` | Cone r4 (2), (14); gray-contexts r6 (3) ×2, (6), (11) formal and instance, (24); naturality r6 (11), (14), (18), (20), the two routes of (19) parallel (§7.10) | typechecks (~21 s, 20 checks); negative control rejected |

There is one negative control. In `UnitorNaturality`, swapping source and target in the expected type makes Agda reject the module.

The generator does not implement positional pull-back for 1-skeleta with cycles, so Eckmann–Hilton is not generated. The proof covers that case.
