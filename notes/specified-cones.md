# Specified cones, cocones and transfor shapes; the free object as a lax colimit of the point

*Design and proof note, 2026-11-18. Thread "Define canonical cone constructions" (`cmsg_018pe2CvdFGDdsWgn8Tjn5gbLYSyekUerAT8DpXZFBCtrp`). Ledger items **B5** and **B6** of `open-issues.md`. Agda: `src/CaTTExp/Cones.agda` (constructions) and `src/CaTTExp/ConesExamples.agda` (machine checks).*

*Markers. **Proved**: a complete paper argument is written here. **Machine-checked**: the certified checker of `CaTTExp.Check` returns a typing derivation at Agda typechecking time. **[cited]**: taken from a cited source and not re-proved. **[recall]**: from background knowledge, not re-checked against the source (listed for G1). **[conj]**: open, with the attempt recorded.*

---

## 0. Summary

The printed CaTT_lim cone judgment admits non-canonical cones (`conjectures/lax-colimit-of-point.md`), and its `ctrf` rules reject the intended cone morphisms (`catt-lim-formalization.md`). `limits-representables.md` §4.1(1) therefore asks for shapes given by **functions** of the diagram context. This note supplies them.

| Result | Scope | Status |
|---|---|---|
| **Specified cone** `Cone(Γ; c)` (Def. 2.1): a total function, Mikhail's Thm 3.3 formula | every **globular** Γ (each variable's boundary is a variable: all pasting contexts, loops, parallel cells) | **proved** (Lemma 2.2); machine-checked on 12 shapes up to dimension 4 |
| It is one of the cones Mikhail's printed (KE) admits | globular Γ | **proved** (Prop. 2.3); machine-checked by our (KE) checker; the CaTT_lim thread also reports its `cone?` accepts all 12 (run on its side, not a test in this repository) |
| Its strict free ω-category is the Ara–Maltsiniotis join `c ⋆ Γ` | globular Γ with a Steiner (loop-free) basis | **proved**, modulo the join's sign convention [recall] (Prop. 2.5) |
| **Specified cocone** `Cocone(Γ; c) := O(Cone(OΓ; c))`, O reversing odd dimensions | globular Γ | **proved**; the closed formula (Def. 3.1) equals the dual syntactically (machine-checked by `refl`) |
| **Transfor shapes** `Tr_k(Γ; c)`: iterated cylinder of the cone in the projection direction (transfor index first, `Dᵏ ⊗ Dᵐ`); cocone transfors by duality (diagram index first) | globular Γ, dim Γ ≤ 1: all k | **proved** with plain CaTT coherences only (Thm 4.3); machine-checked k = 1, 2, 3 |
| | globular Γ, dim Γ = 2 | k = 1: **proved** from an interchange and associators over pasting contexts, machine-checked (cone and cocone) on 3 shapes. k ≥ 2: sketched by the same method (§4.3) |
| | globular Γ, dim Γ ≥ 3 | needs Conjecture N at depth dim Γ − 1, for nested whiskerings only [conj] |
| **Cones over non-globular Γ**: recursion through substitutions, one family of universal cells `Π(Q, B)` | Γ whose non-variable boundary terms are 1-dimensional | **proved** (Prop. 5.2); machine-checked on `τ : f ∗₀ g ⇒ h` |
| | arbitrary Γ | equivalent to the cone form of N, `N^cone`, posed in `conjectures/cone-over-coherences.md`. Dimension ≤ 2 **proved** (researcher, verified: `conjectures/answered/cone-over-coherences-2026-11-18.md`). Dimension n follows from RC(n) alone on the join contexts `Cone(Q; c)` (round 2, verified: `conjectures/answered/cone-over-coherences-r2-2026-11-18.md`, via a cut translation lowering RC one dimension). The dimension-3 unitor case over D² has an explicit 4-term. General RC(3) on `Cone(D²; c)` is open [conj] |
| **B6, level 0**: a Γ-family of elements gives a cocone over the constant point diagram (`φ`) | every globular Γ, every dimension | **proved** (Prop. 6.2); machine-checked on all 12 shapes |
| **B6, equivalence**: `φ`, `ψ` and invertible homotopies `ψφ ≃ id`, `φψ ≃ id` | globular Γ of dimension ≤ 1 (graphs) | **proved** (Thm 6.3); machine-checked on 6 graphs |
| | dimension 2 | ψ and `ψφ ≃ id`: **proved**, machine-checked on 9 shapes (§6.4). `φψ ≃ id`: **proved on paper** using BMOSV depth 1 [cited] (Prop. 6.5); its cylinder is machine-checked, its top component is not |
| | dimension ≥ 3 | reduced to transport along unit coherences (§6.4) [conj] |
| B6 Step B (cocone morphisms vs family morphisms) | graphs, level 1 | φ↑ and ψ↑ constructed on paper from coherences over pasting contexts (§6.5); homotopies open |

**What "machine-checked" means here.** Each construction is an Agda function producing CaTT syntax. For each listed shape the certified checker returns a typing derivation. The general statements (for every Γ in the class) are paper proofs. They reduce to the checked generic cases by *locality* (§7): every construction is assembled from its value on disks Dᵐ by substitution. So the checks on D⁰–D⁴ plus substitution admissibility (A1, proved in Agda in `CaTTExp.Subst`, PR #20) cover all globular Γ of dimension ≤ 4. The step from disks to Γ is a paper argument; it is not itself formalised (S5).

---

## 1. Setting

- **CaTT** as in `conjectures/naturality-arbitrary-depth.md` §1, with de Bruijn levels as in `src/CaTTExp/Syntax.agda`. Composition order is diagrammatic (`conventions.md` §1).
- **Binary composites.** For an n-cell u and an m-cell w with `∂⁺_k u = ∂⁻_k w`, `u ∗_k w` is the composition coherence over the pasting context of an n-disk and an m-disk glued along a k-disk. Its boundary is computed componentwise: for `j > k`, `∂^α_j(u ∗_k w) = ∂^α_j u ∗_k ∂^α_j w`, where a factor of dimension ≤ j is left unchanged; and `∂⁻_k(u ∗_k w) = ∂⁻_k u`, `∂⁺_k(u ∗_k w) = ∂⁺_k w`. These hold syntactically (BMOSV §2; in Agda, `binC` computes the coherence's type by exactly this rule, and the checker confirms it).
- **Globular context.** Every variable has type `⋆` or `a →_A b` with a, b *variables*. All pasting contexts are globular, and so are contexts with loops (`f : x → x`) and parallel cells.
- **Diagram = context.** As in `limits-representables.md` §1, a diagram of shape Γ is a substitution into Γ; the cone over the generic diagram is a context extending Γ.
- **Layout** (shared with `Lim/Repaired.agda`, checked equal there): Γ's variables, then the apex c, then one projection per variable of Γ, in Γ's order.

---

## 2. The specified cone

### 2.1 Definition

**Definition 2.1.** For globular Γ, `Cone(Γ; c)` extends Γ by `c : ⋆` and, for each variable t of Γ in order, a variable p_t:

```
p_x : c → x                                                   (dim x = 0)
p_t : p_{τt}  →  p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} ( … (p_{σᵐt} ∗₀ t)))      (dim t = m ≥ 1)
```

Write `S_t := p_{τt}` and `T_t` for the right-hand side; for an object x put `S_x := c`, `T_x := x`. Examples:

```
f : x → y      p_f : p_y ⇒ p_x ∗₀ f
α : f ⇒ g      p_α : p_g ⇛ p_f ∗₁ (p_x ∗₀ α)
θ : α ⇛ β      p_θ : p_β → p_α ∗₂ (p_f ∗₁ (p_x ∗₀ θ))
```

This is the cone of Mikhail's Thm 3.3, lax at the vertices (`limits-representables.md` §1 orientation). It is a function of Γ: no choices are left.

### 2.2 Well-typedness

**Lemma 2.2.** For globular Γ, `Cone(Γ; c)` is a well-formed context. Moreover `S_t, T_t : S_{σt} → T_{τt}` for every t of dimension ≥ 1.

*Proof.* Induction on the position of t. For `1 ≤ j ≤ m+1` put

```
V⁽ʲ⁾_t := p_{σʲt} ∗_{m−j} ( p_{σʲ⁺¹t} ∗_{m−j−1} ( … (p_{σᵐt} ∗₀ t)))      V⁽ᵐ⁺¹⁾_t := t,
```

so `T_t = V⁽¹⁾_t`. Each V⁽ʲ⁾_t is an m-cell.

*Claim: for 2 ≤ j ≤ m+1, `V⁽ʲ⁾_t : V⁽ʲ⁻¹⁾_{σt} → V⁽ʲ⁻¹⁾_{τt}`, and the composite defining V⁽ʲ⁾_t is well formed.* Downward induction on j. For j = m+1 this is `t : σt → τt`. For j ≤ m, the factor `p_{σʲt}` has dimension `m−j+1 ≤ m−1`, so by the boundary rule `∂^α V⁽ʲ⁾_t = p_{σʲt} ∗_{m−j} ∂^α V⁽ʲ⁺¹⁾_t = p_{σʲ⁻¹(σt)} ∗_{(m−1)−(j−1)} V⁽ʲ⁾_{σt} = V⁽ʲ⁻¹⁾_{σt}` for α = −, and likewise for α = + using `σʲt = σʲ⁻¹(τt)` (globularity, j ≥ 2). Composability: iterating the claim, the (m−j)-dimensional source of `V⁽ʲ⁺¹⁾_t` is `V⁽¹⁾_{σʲt} = T_{σʲt}`, which is the target of `p_{σʲt}` by the induction hypothesis on earlier variables.

For j = 1 both factors of `T_t = p_{σt} ∗_{m−1} V⁽²⁾_t` have dimension m = (m−1)+1, so `T_t : ∂⁻p_{σt} → ∂⁺V⁽²⁾_t = S_{σt} → V⁽¹⁾_{τt} = S_{σt} → T_{τt}`. Finally `S_t = p_{τt} : S_{τt} → T_{τt}`, and `S_{τt} = S_{σt}` (both are `p_{σ²t} = p_{στt}` when m ≥ 2, and both are c when m = 1). So `S_t` and `T_t` are parallel and the type of p_t is well formed. ∎

**Machine check.** `ok (ConeOf.cone Γ)` for DiskEx 0–4, the loop with a 2-cell, the loop with a 3-cell, two parallel 2-cells, cospan, parallel pair, endo-arrow, composable pair.

### 2.3 It is one of Mikhail's cones

**Proposition 2.3.** For globular Γ, every projection of `Cone(Γ; c)` satisfies the printed (KE) conditions of Mikhail Def. 3.x (`limits-representables.md` §2.1): τCond on the source, σCond on the target, and `t ∝ T_t`.

*Proof.* For an object x: `FV(c) = {c}`, `FV(x) = {x}`, x ∝ x, and the unions are empty. Let dim t = m ≥ 1 and write `cl(u)` for the downward closure of a variable.
- *Selected projections.* For a variable y of Γ, `y ∝ τ(p) = T_z` forces dim z = dim y and y to occur in T_z at top dimension; the only Γ-variable of dimension dim z in T_z is z. So y selects exactly p_y.
- *Source.* The variables of `τt : ∂X` are `cl(τt)`, so `U_τ = ⋃_{y ∈ cl(τt)} FV(p_y : T_{p_y}) = cl(p_{τt})`, since the type of p_u mentions p_{τu} and p_{σu}. And `FV(S_t : A) = FV(p_{τt} : A) = cl(p_{τt}) ∋ c`. Equal.
- *Target.* Likewise `U_σ = cl(p_{σt})`, and `FV(T_t : A) = cl(t) ∪ {p_{σᵏt}}_k ∪ their closures = cl(t) ∪ cl(p_{σt})`. Equal.
- *Linearity.* t occurs once in T_t, in the innermost composite, at top dimension, and every enclosing composite has exactly one argument (the inner composite, of dimension m) containing it. ∎

**Machine checks.** `KE.okConeAll` (ours) holds for every shape. Independently, the CaTT_lim formalisation thread reports that it ran its certified recogniser `cone? printedLin`, and the strict multiplicity-one variant, on all 12 shapes: all accepted, and where its own `coneC` applies (dimension ≤ 2) the two cones are syntactically equal. That cross-check was run in that thread's workspace; it is not a test in this repository.

**Non-vacuity.** Our checker rejects a cone whose `p_f` forgets f, and *accepts* the researcher's non-canonical cone over the loop (`ConesExamples` §6): that is exactly why a construction, not the judgment, is needed.

### 2.4 Locality

**Remark 2.4.** For a variable t of dimension m, let `χ_t : Γ ⊢ χ_t : Dᵐ` classify t. Then `Cone(χ_t) : Cone(Γ; c) ⊢ Cone(Dᵐ; c)`, sending c ↦ c, the disk variables to their χ-images, and `p_u ↦ p_{χ_t(u)}`, is a substitution, and the type of p_t is the type of p_top in `Cone(Dᵐ; c)` pushed along it. So `Cone(Γ; c)` is well formed as soon as every `Cone(Dᵐ; c)` with m ≤ dim Γ is, by substitution admissibility. The machine check on D⁰–D⁴ thus covers every globular Γ of dimension ≤ 4, by A1 (`CaTTExp.Subst`).

### 2.5 Steiner check

**Proposition 2.5.** Let Γ be globular whose free strict ω-category is generated by a strongly loop-free Steiner basis (e.g. a pasting context). Then the computad `Cone(Γ; c)` presents `ν(c ⋆ λΓ)`, the Ara–Maltsiniotis join of the point with Γ, with p_t ↦ `c ⋆ t`.

*Proof.* In chains, a binary composite contributes the sum of its top-dimensional factors, and whiskering by lower-dimensional cells contributes nothing in top degree. So `[T_t] = t + p_{σt}` and `[S_t] = p_{τt}`, giving

```
d(p_t) = t + p_{σt} − p_{τt} = t − p_{dt},       d(p_x) = x − c.
```

This is the join differential `d(c ⋆ y) = y − c ⋆ dy` (with `d(c ⋆ y) = y − c` in degree 0) **[recall: AM, *Joint et tranches*, §6, sign convention]**. The join of strongly loop-free bases is strongly loop-free **[recall: AM, same]**, so by Steiner's theorem `ν(c ⋆ λΓ)` is freely generated by its atoms, and each atom ⟨c ⋆ t⟩ has as source and target the unique cells with the chain data above (support determines cells: `conjectures/steiner-support-determines-cells.md`, solved for this case). S_t and T_t are cells of the free strict ω-category on the computad with exactly these chain data, so the generators match the atoms with matching boundaries. ∎

---

## 3. The specified cocone

**Definition 3.1.** Let O reverse the cells of every odd dimension. On the syntax used here O is structural: a type of n-cells has source and target swapped when n is odd, and a composite `u ∗_k w` has its factors swapped when k+1 is odd (Benjamin–Markakis, arXiv 2402.01611). Put

```
Cocone(Γ; c) := O(Cone(OΓ; c)).
```

Unfolding, with `u₀ = t` and `u_{k+1}` the source of u_k if dim u_k is even and its target if odd:

```
q_x : x → c
q_t : q_{σt} → E_t          (dim t odd)          E_t = X_{m−1},  X₀ = t ∗₀ q_{u_m},
q_t : E_t → q_{τt}          (dim t even ≥ 2)     X_j = X_{j−1} ∗_j q_{u_{m−j}} (j even),  q_{u_{m−j}} ∗_j X_{j−1} (j odd)

f : x → y      q_f : q_x ⇒ f ∗₀ q_y
α : f ⇒ g      q_α : q_f ∗₁ (α ∗₀ q_y) ⇛ q_g
θ : α ⇛ β      q_θ : q_α → (q_f ∗₁ (θ ∗₀ q_y)) ∗₂ q_β
```

The closed formula (`CoconeOf.cocone`) and the dual (`dualCtx (ConeOf.cone (dualCtx Γ))`) are **syntactically equal** on every shape (machine-checked by `refl`). Well-formedness follows from Lemma 2.2, since O preserves well-typedness of these expressions.

**Why the odd dimensions.** Every cocone cell must run from its σ-side to its τ-side, so that the constant instance is the suspension with *no* opposites (§6). A cell of dimension n+1 over an n-cell runs σ → τ in `O_J(Cone(O_JΓ))` exactly when one of n, n+1 lies in J. That holds for all n iff J alternates, and `q_x : x → c` needs 1 ∈ J. Mikhail's suggestion (reverse 1-cells only, J = {1}) gives a cocone whose constant instance is Σ of Γ with **every dimension ≥ 2 reversed**.

**Agreement with the limit-metatheory table** (`limits-metatheory.md` §8.2, colim row): `q_f : q_x ⇒ D f ; q_y`. Matches.

---

## 4. Transfor shapes

### 4.1 Cylinders

For a context K and an up-closed set Y of its variables, `K↑Y` keeps each variable outside Y and replaces each x ∈ Y by `x⁻, x⁺, x↑ : a_x → b_x`, with Lemma 1 of `conjectures/naturality-arbitrary-depth.md`:

```
a_x = ( … ((x⁻ ∗₀ (τⁿx)↑) ∗₁ (τⁿ⁻¹x)↑) … ) ∗_{n−1} (τx)↑
b_x = (σx)↑ ∗_{n−1} ( … ((σⁿ⁻¹x)↑ ∗₁ ((σⁿx)↑ ∗₀ x⁺)) … )
```

with unaffected factors omitted, and `x↑ : x⁻ → x⁺` for objects. For an arrow, `f↑ : f⁻ ∗₀ y↑ ⇒ x↑ ∗₀ f⁺`, which is `Ff ; α_y ⇒ α_x ; Gf`: the D¹ ⊗ (−) orientation of `conventions.md` §3.1 (transfor index first). When K's boundary terms are composites, their lifts `w↑` are needed. Here only the **depth-0 rule** is used: if every affected variable of `u ∗_k w` has the composite's own dimension, then `(u ∗_k w)↑ = u' ∗_k w'`, where `u' = u↑` if u is affected and `u⁻` otherwise (likewise w'). This is the coherence over the pasting context `Q↑Y` (Q the glued disks), which is again a pasting context (a raised disk), so no conjecture is involved.

For globular K and all of Y, `K↑Y` is the Gray cylinder `D¹ ⊗ K`. Machine-checked on all 12 shapes.

### 4.2 Transfors

**Definition 4.1.** `Tr₁(Γ; c) := Cone(Γ; c)↑{p_t}` (the diagram and the apex are fixed). `Tr_{k+1}(Γ; c) := Tr_k(Γ; c)↑{newest variables}`. Each `Tr_k` has one top variable per variable of Γ.

Over `f : x → y`:

```
Tr₁:  m_x : p⁻_x ⇒ p⁺_x,   m_f : p⁻_f ∗₁ (m_x ∗₀ f)  ⇛  m_y ∗₁ p⁺_f
Tr₂:  μ_x : m⁻_x ⇛ m⁺_x,   μ_f : m⁻_f ∗₂ (p⁻_f ∗₁ (μ_x ∗₀ f))  →  (μ_y ∗₁ p⁺_f) ∗₂ m⁺_f
```

These are the `Dᵏ ⊗ Dᵐ` shapes of `limits-metatheory.md` Theorem A (transfor index first), with apex not duplicated and each cone variable copied with its type renamed.

**Definition 4.2 (marking).** `marked(Tr_k)` is the set of all comparison variables over positive-dimensional variables of Γ, at every level (for Tr₂ over an arrow: m⁻_f, m⁺_f, μ_f). The cone projections themselves stay unmarked. This is the P set of the repaired rules (`limits-representables.md` §4.1(2)). Under L only those over *marked* diagram generators are marked (`limits-metatheory.md` §5.3); that is a filter on the same list.

**Cocone transfors.** `coTr_k(Γ; c) := O(Tr_k(OΓ; c))`. Over an arrow this gives

```
m_f : m_x ∗₁ q⁺_f  ⇛  q⁻_f ∗₁ (f ∗₀ m_y),
```

which is exactly the **diagram-index-first** colimit row of `limits-metatheory.md` §8.2 (`m_x;q′_f ⇛ q_f;(Df◁m_y)`). So the two Gray orders that L needs come out of one construction plus a duality *of shapes*. (Duality of *derivations* is not a symmetry of L, §8.3 there; dualising a context is harmless.)

### 4.3 Which shapes exist unconditionally

**Theorem 4.3.** For every globular Γ of dimension ≤ 1 and every k ≥ 1, `Tr_k(Γ; c)` and `coTr_k(Γ; c)` are well formed, using only the depth-0 rule.

*Proof.* The boundary terms of the cone variables are variables and `p_x ∗₀ f`. At level 1, Y = {p}: the only composite, `p_x ∗₀ f`, has affected factor p_x of its own dimension 1, so its lift is `m_x ∗₀ f`. Inductively, the types at level k contain only variables and binary composites in which the level-k variables (the new Y) occur as factors of the composite's own dimension (`m_x ∗₀ f`, `p⁻_f ∗₁ (m_x ∗₀ f)`, `m_y ∗₁ p⁺_f`, …). For Γ of dimension ≤ 1, the level-k variable over an object has dimension k and the composites in level-k types have dimension k too, so the depth is always 0. Lemma 1 (with the support fact (7) of the researcher response) gives well-formedness. ∎ Machine-checked for k = 1, 2, 3 (cone and cocone) on point, arrow, cospan, parallel pair, endo-arrow, composable pair.

**Dimension 2 (B18).** Over a 2-dimensional Γ, Tr₁ needs two lifts that the depth-0 rule does not give. Both are built from coherences over pasting contexts, so no conjecture is needed.

- *Whisker.* For `t = p_x ∗₀ α` with `α : f ⇒ g : x → y`, the required type is `(p⁻_x ∗₀ α) ∗₁ (m_x ∗₀ g) ⇛ (m_x ∗₀ f) ∗₁ (p⁺_x ∗₀ α)`. Its support `(c, x, p⁻_x, p⁺_x, m_x, y, f, g, α)` is the pasting context `D² ∨₀ D²`, and both sides are full, so the interchange coherence `xc(m_x, α)` inhabits it.
- *Paste.* For `t = u ∗₁ w` with u, w affected 2-cells (here `u = p_f`, `w = p_x ∗₀ α`), write `a_u = u⁻ ∗₁ L(τu)`, `b_u = L(σu) ∗₁ u⁺` and likewise for w, where L is the lift and `τu = σw`. Then

  ```
  t↑ := asL(u⁻, w⁻, L τw) ∗₂ (u⁻ ∗₁ w↑) ∗₂ asR(u⁻, L σw, w⁺) ∗₂ (u↑ ∗₁ w⁺) ∗₂ asL(L σu, u⁺, w⁺)
  ```

  runs from `(u⁻ ∗₁ w⁻) ∗₁ L(τw)` to `L(σu) ∗₁ (u⁺ ∗₁ w⁺)`, which are exactly `a_t` and `b_t`. Here asL and asR are the associator of three 2-cells and its reverse.

**Machine-checked:** `ctrf 1` and `coctrf 1` on D², the loop with a 2-cell, and two parallel 2-cells. The cocone case uses the O_odd duals: the dual of `xc(u, w)` is `xc(w′, u′)` and the dual of asL is asR. This replaces the earlier negative test.

*Higher levels over dimension 2 (sketch, not machine-checked).* At level k ≥ 2 the new up-closed set is the previous level's top variables. In the coherences xc, asL and asR they only occur as *maximal* arguments, meaning cells of the coherence's pasting context that lie in no other cell's boundary. Raising a maximal cell of a pasting context to a disk one dimension up gives a pasting context again. So the naturality of xc and of the associators is again a coherence over a pasting context, and composites are pasted through associators one dimension up as in the paste rule. I expect Tr_k over 2-dimensional Γ to exist for every k from coherences over pasting contexts alone. The Agda lift currently returns `nothing` on the coherence constructors (a recorded test: `ctrf 2 (DiskEx 2)` is undefined). Generalising the lifts is B18's remainder.

**Dimension ≥ 3** needs Conjecture N at depth `dim Γ − 1`, for **nested whiskerings only** (composition constructors). This is a much narrower instance than general N. It is recorded under C1 (`conjectures/outbox/naturality-arbitrary-depth-r4.md`).

### 4.4 "Horns are cones" (`limits-metatheory.md` §5.3): an orientation finding

That note conjectures `Tr_n(Γ) = Cone(Dⁿ ⊗ Γ)[π]` up to unit coherences. Already for Γ a point and n = 1, the cone over `D¹ ⊗ x = (x⁻ —x↑→ x⁺)` has `p_{x↑} : p_{x⁺} ⇒ p_{x⁻} ∗₀ x↑`, which collapses to `p_{x⁺} ⇒ p_{x⁻} ∗₀ id_x`. That is a transfor from the **+** cone to the **−** cone, the reverse of Tr₁'s `m_x : p⁻ ⇒ p⁺`. The reason is that lax cone cells over a 1-cell run from the target's projection to the source's. So the statement needs `(D¹)^op`, or the reversed transfor direction, in the first factor. Since `D¹ ⊗ Γ` for 1-dimensional Γ has composite boundaries of dimension 1 only, its cone exists by Prop. 5.2. A full syntactic comparison for graphs is therefore within reach; it is follow-up S4.

**The arrow, worked out (B23).** Let `J = (+ —j→ −)` and let `J ⊗ Γ` have, for each variable t of Γ, copies t⁺, t⁻ and a cell t↑ = j ⊗ t. With the Steiner sign `∂(j ⊗ f) = ∂j ⊗ f − j ⊗ ∂f` (`conventions.md` §2, Steiner Example 3.10; so `∂⁺(j ⊗ f) = (∂⁺j ⊗ f) ∪ (j ⊗ ∂⁻f)`), for `f : x → y` this gives

```
x↑ : x⁺ → x⁻        f↑ : f⁺ ∗₀ y↑ ⇒ x↑ ∗₀ f⁻.
```

The cone over this context exists by Prop. 5.2: its only composite boundaries are 1-dimensional. Its cells are

```
p_{x↑} : p_{x⁻} ⇒ p_{x⁺} ∗₀ x↑
p_{f↑} : P(x↑ ∗₀ f⁻) ⇛ P(f⁺ ∗₀ y↑) ∗₁ (p_{x⁺} ∗₀ f↑),
```

with `P(a ∗₀ b) = (p_b ∗₁ (p_a ∗₀ b)) ∗₁ κ`. Now substitute π: `t^± ↦ t`, `x↑ ↦ id_x`, and `f↑ ↦` the unit coherence `f ∗₀ id_y ⇒ id_x ∗₀ f`. Up to unitors and the κ's:

- `p_{x↑}` becomes `p⁻_x ⇒ p⁺_x ∗₀ id_x ≅ p⁺_x`, matching `m_x : p⁻_x ⇒ p⁺_x`;
- `p_{f↑}` becomes `p⁻_f ∗₁ (m_x ∗₀ f) ⇛ m_y ∗₁ p⁺_f`, matching `m_f`.

With the other orientation of f↑ (that is, `D¹ ⊗ Γ`), the 2-cell runs the other way. So the corrected statement is `Tr₁(Γ) ≃ Cone(J ⊗ Γ; c)[π]` with J pointing from the + end to the − end, which is `(D¹)^op ⊗ Γ`. For graphs the generators correspond one to one, and their types agree up to the unitors and κ's. Turning this into an equivalence of contexts needs comparison 3-cells between parallel 2-terms with equal strict images. Theorem A of `relative-coherence.md` (RC(2) in every context) supplies those. The two-sided homotopies are not written out; that is B23's remainder.

---

## 5. Cones over arbitrary contexts

### 5.1 The recursion

For non-globular Γ, the type of p_t mentions `P(u)`, the cone cell over the *term* u, for u among the boundaries of t. Extend p to all terms by recursion on terms, with the induction order corrected by the researcher (`naturality-arbitrary-depth.md`, response §4.2: lower-dimensional lifts first, then the filler, then same-dimension structural recursion):

```
P(x)              := p_x
P(coh_{Q,B}[γ])   := Π(Q, B)[Cone(γ)]
```

- `Cone(γ) : Cone(Γ; c) ⊢ Cone(Q; c)` sends q ↦ γ(q), c ↦ c, p_q ↦ P(γ(q)). It is well typed because `T_q[Cone(γ)] = T_{γ(q)}` (binary composites and boundaries commute with substitution).
- `Π(Q, B)` is a cell of `Cone(Q; c)` (Q a pasting context, hence globular, so this cone is Def. 2.1) of type `P(τc₀) → T_{c₀}`, where `c₀ = coh_{Q,B}[id]` and T is the nested whiskering of Def. 2.1 with P in place of p. Lemma 2.2's computation shows that this type is well formed once P is defined on the boundary of c₀.

So **cones over arbitrary Γ exist iff every `Π(Q, B)` exists**. This is the cone form of Conjecture N, posed as `N^cone` in `conjectures/cone-over-coherences.md`. It is Mikhail's Conjecture 3.6 made precise.

### 5.2 The 1-dimensional case

**Proposition 5.2.** `Π(Q, B)` exists for every 1-dimensional coherence. Hence `Cone(Γ; c)` exists for every Γ whose non-variable boundary terms are all 1-dimensional (e.g. `τ : f ∗₀ g ⇒ h`, and `D¹ ⊗ Γ` for any graph Γ).

*Proof.* A 1-dimensional coherence is either an identity (coherence case over a point) or the composite of a chain `x₀ → … → x_m` (composition case). For the identity, `Π : p_x ⇒ p_x ∗₀ id_x` is the full coherence over `(c, x, p_x)`. For a chain, put

```
Π := p_{f_m} ∗₁ ((p_{f_{m−1}} ∗₀ f_m) ∗₁ ( … ∗₁ (((p_{f_1} ∗₀ f_2) ∗₀ …) ∗₀ f_m))) ∗₁ κ,
```

where step i whiskers `p_{f_i}` by `f_{i+1}, …, f_m` (left-nested). Consecutive steps compose, and the last ends at `(…(p_{x₀} ∗₀ f₁) …) ∗₀ f_m`. κ is the full coherence over the chain `c → x₀ → … → x_m` from that left-nested composite to `p_{x₀} ∗₀ comp(f)`: both sides use every variable of the chain. ∎

**Machine check.** `ConesExamples` §9 builds the cone over `x, y, z, f, g, h, τ : f ∗₀ g ⇒ h` with `P(f ∗₀ g) = (p_g ∗₁ (p_f ∗₀ g)) ∗₁ κ`. The checker accepts it, and so does (KE).

**Dimension 2.** For a full 2-dimensional coherence `c : a ⇒ b` over a chain, `P(b)` and `P(a) ∗₁ (p_{x₀} ∗₀ c)` are parallel 2-terms of the cone with the same strict image, so RC(2) (`relative-coherence.md` Theorem A) gives `Π`. For the composition case, the researcher response (`conjectures/answered/cone-over-coherences-2026-11-18.md`, verified) settles dimension 2 completely. The vertical composite is the elementary chain of the conjecture file. The horizontal composite `α ∗₀ β` has an explicit RC-free chain of eight 3-cells: `p_β`, then `p_α ∗₀ g′`, three coherences over pasting contexts, and reassociations. Its strict image is `c ⋆ (α ∗₀ β)`. In general, RC(1..n) on all join contexts `Cone(Q; c)` implies N^cone through dimension n, composition case included. The proof is a strict lift followed by face-by-face transport, and its key lemma is that every RC witness in `c ⋆ Q` strictifies to an identity. **Dimension 3** therefore reduces to RC(3) on join contexts. The smallest case is `Cone(D²; c)`, the unitor case (round 2 answered, with an explicit unitor 4-term: `conjectures/answered/cone-over-coherences-r2-2026-11-18.md`; round-3 prompt `conjectures/outbox/cone-over-coherences-r3.md`).

**Round 2** (`conjectures/answered/cone-over-coherences-r2-2026-11-18.md`, verified). The unitor `α ⇛ α ∗₁ 1_g` over D² has an explicit 4-term, built from generic schemes for `P(1_f)` and `P(α ∗₁ β)` plus six auxiliary coherences. Its strict image is `1_{p_α}`. A cut translation gives `RC(r+1, Cone(ΣQ; d)) ⇒ RC(r, Cone(Q; c))`, so RC(n) on join contexts alone gives N^cone through dimension n. Correction to round 1: `c ⋆ Q` has a unique 0-sink, the last vertex of Q. The real obstruction is a discarded column carrying `p_x`, as in `p_x ∗₀ α`. Open: general RC(3) on `Cone(D²; c)`. The round-3 prompt is `conjectures/outbox/cone-over-coherences-r3.md`.

---

## 6. B6: the free object is the lax colimit of the point

### 6.1 Setting

Let ⊤ and c be objects. The **constant cocone** `𝒦(Γ)` is `Cocone(Γ; c)` with the diagram substituted by the constant diagram `x ↦ ⊤`, `t ↦ id^{dim t}_⊤` (well typed for globular Γ):

```
q_x : ⊤ → c,     q_f : q_x ⇒ id_⊤ ∗₀ q_y,     q_α : q_f ∗₁ (id²_⊤ ∗₀ q_y) ⇛ q_g,  …
```

The **family context** is the suspension `ΣΓ = (⊤, c, s_x : ⊤ → c, s_f : s_x ⇒ s_y, s_α : s_f ⇛ s_g, …)`. Its substitutions are Γ-families of elements of c (`limits-representables.md` §5.1). The question (`lax-colimit-of-point.md`, "What remains") is whether `𝒦(Γ) ≃ ΣΓ`. Here ≃ means substitutions both ways and cylinder homotopies (§4.1, with ⊤ and c fixed) from each composite to the identity, all of whose components are invertible.

### 6.2 A family is a cocone, in every dimension

**Proposition 6.2.** For every globular Γ there is `φ : ΣΓ ⊢ φ : 𝒦(Γ)` with `φ(q_x) = s_x` and, for dim t = m ≥ 1,

```
φ(q_t) := coh_{D^{m+1}, A → B}[χ_t],
```

where `A → B` is the type of q_t pushed along φ (already defined below t), computed generically in `D^{m+1} = ΣDᵐ`, and χ_t classifies s_t.

*Proof.* `coh_{D^{m+1}, A→B}` is a valid **operation** (composition-case coherence) if `Var(A) = ∂⁻D^{m+1}` and `Var(B) = ∂⁺D^{m+1}`. By induction, φ(q_u) uses exactly `cl(s_u)`. The source side of q_t's type is built from `q_{σt}` (or `q_{σt}` composed with W_t) and the target side from `q_{τt}` (or W_t composed with it). W_t involves only q's of iterated boundaries of dimension ≤ m−2 and identities on ⊤, all in both `cl(s_{σt})` and `cl(s_{τt})`. So each side uses exactly the closure of s_{σt}, respectively s_{τt}. ∎

For example `φ(q_f) = U(s_f)` with `U : a ⇒ id_⊤ ∗₀ b` the unary operation over D². No unitor is needed. **Machine-checked** (`PhiAll.okφ`) on all 12 shapes, up to the 4-disk and the loop with a 3-cell.

### 6.3 Graphs: the full equivalence

**Theorem 6.3.** For every globular Γ of dimension ≤ 1, `𝒦(Γ) ≃ ΣΓ`. Explicitly:

- `ψ : 𝒦(Γ) ⊢ ψ : ΣΓ`: `s_x ↦ q_x`, `s_f ↦ q_f ∗₁ λ_{q_y}`, with `λ_w : id_⊤ ∗₀ w ⇒ w` the unitor (full coherence over D¹).
- `H : ΣΓ ⊢ H : ΣΓ↑Y` with `H⁻ = ψφ`, `H⁺ = id`: `H(s_x↑) = id_{s_x}` (note `ψφ(s_x) = s_x`), and `H(s_f↑) : (U(s_f) ∗₁ λ) ∗₁ id_{s_y} ⇛ id_{s_x} ∗₁ s_f`, the full coherence over the disk of s_f.
- `H′ : 𝒦 ⊢ H′ : 𝒦↑Y` with `H′⁻ = φψ`, `H′⁺ = id`: `H′(q_x↑) = id_{q_x}`, and `H′(q_f↑) = c₁ ∗₂ c₂ ∗₂ (q_f ∗₁ c₃) ∗₂ c₄`:

  ```
  c₁ : U(q_f ∗₁ λ) ∗₁ (id_⊤ ∗₀ id_{q_y})  ⇛  (q_f ∗₁ λ) ∗₁ λ⁻¹        full coherence over D², u ↦ q_f ∗₁ λ
  c₂ : (q_f ∗₁ λ) ∗₁ λ⁻¹  ⇛  q_f ∗₁ (λ ∗₁ λ⁻¹)                          associator over three vertical 2-cells
  c₃ : λ ∗₁ λ⁻¹  ⇛  id_{id_⊤ ∗₀ q_y}                                     full coherence over D¹, whiskered by q_f
  c₄ : q_f ∗₁ id  ⇛  id_{q_x} ∗₁ q_f                                     full coherence over D², u ↦ q_f
  ```

Every component is an identity, a coherence, or a vertical composite of whiskered coherences, hence invertible (Benjamin–Markakis–Sarti, arXiv 2406.12127: coherences are invertible, and invertibles are closed under composition and whiskering [cited]).

*Proof.* The point needing care is that `𝒦` is not a pasting context: q_f's target is the composite `id_⊤ ∗₀ q_y`, so no single coherence over a pasting context can compare `φψ(q_f)` with `q_f`. Every pasting context mapping into 𝒦 sees that target as a variable. The proof isolates q_f by inserting `λ ∗₁ λ⁻¹`. Each of c₁–c₄ is a coherence over a genuine pasting context (D², three vertical 2-cells, D¹) whose substitution sends the relevant variable to `id_⊤ ∗₀ q_y` as a whole. The lifts in `𝒦↑Y`, namely `(id_⊤ ∗₀ q_y)↑ = id_⊤ ∗₀ q_y↑`, are depth 0. Typing is then a computation, carried out once for Γ = D¹. For a general graph Γ, every component over f is the D¹-component substituted along the map classifying f (locality, §7). ∎

**Machine-checked** (`ConstPoint.okφ/okψ/okH/okH′`) on point, arrow, cospan, parallel pair, endo-arrow and composable pair. A non-vacuity check: the naive identification `q ↦ s` is *not* a substitution `ΣΓ → 𝒦`.

**Consequence for R-B.** For graphs, "maps out of the lax colimit of the point are Γ-families" holds at level 0: families give cocones (φ), cocones give families (ψ), and the round trips are invertibly homotopic to the identity. Together with the colimit rule's J1/J2, this derives R-A's level-0 rule for graphs: the map `⟦Γ⟧ → C` from a family, and the invertible cells saying it restricts to the family.

### 6.4 Dimension 2: ψ and H (B20)

**Proposition 6.4.** For every globular Γ of dimension ≤ 2, ψ extends to `ψ : 𝒦(Γ) ⊢ ψ : ΣΓ`, and there is a homotopy `H : ψφ ≃ id` on ΣΓ with invertible components.

- For a 2-cell `α : f ⇒ g` over `x → y`, the constant cocone has `q_α : q_f ∗₁ (id²_⊤ ∗₀ q_y) ⇛ q_g`, and ψ(s_α) must run from `q_f ∗₁ λ` to `q_g ∗₁ λ` (λ = λ_{q_y}). Put

  ```
  ψ(s_α) := (q_f ∗₁ κ′) ∗₂ asR(q_f, id²_⊤ ∗₀ q_y, λ) ∗₂ (q_α ∗₁ λ),
  κ′ : λ_w ⇛ (id_{id_⊤} ∗₀ w) ∗₁ λ_w      (full coherence over D¹, at w = q_y).
  ```

  The trick is the one from Theorem 6.3: q_f's target is a composite, so q_f is isolated by whiskering, and every coherence used lives over a pasting context (D¹, or three vertical 2-cells).
- `H(s_α↑) : (ψφ(s_α) ∗₁ id_{s_y}) ∗₂ H_g ⇛ H_f ∗₂ (id_{s_x} ∗₁ s_α)` is the full coherence over the disk around s_α. That disk is ΣD² = D³, a pasting context, and both sides use all of its variables. This is the same argument as for H_f, one dimension up. The argument does not depend on the dimension, so H exists in every dimension once ψ does.

**Machine-checked** (`ConstD2.okψ`, `ConstD2.okH`) on D², the loop with a 2-cell, two parallel 2-cells, and the six graphs.

**The cocone-side homotopy H′.** The cylinder `𝒦↑Y` is built and well typed for these shapes (machine-checked). The lift of `id²_⊤ ∗₀ q_y` is the reversed interchange, and the lift of `q_f ∗₁ W` (W := `id²_⊤ ∗₀ q_y`) uses the paste rule of §4.3. The remaining component is a 4-cell

```
H′(q_α↑) : (φψ(q_α) ∗₁ E) ∗₂ H′_g  ⇛  Paste[H′] ∗₂ (id_{q_x} ∗₁ q_α),        E := id_⊤ ∗₀ id_{q_y},
```

between parallel 3-terms of 𝒦. Here `Paste[H′]` is the paste-rule lift of `q_f ∗₁ W` with H′ substituted: three associators, `H′_f`, and the reversed interchange at `id_{q_y}`.

**Proposition 6.5 (paper; uses BMOSV depth 1 [cited]).** H′(q_α↑) exists, so `𝒦(Γ) ≃ ΣΓ` for every globular Γ of dimension 2.

*Proof.* Write `A = ψ(s_f)`, `B = ψ(s_g)`, `Θ = ψ(s_α) : A ⇛ B`. Then `φψ(q_α) = U₃(Θ)`, where U₃ is the operation over D³ from Prop. 6.2. Also `H′_g = c₁(B) ∗₂ c₂(g) ∗₂ (q_g ∗₁ c₃) ∗₂ c₄(g)`, as in Theorem 6.3.

*Step 1: move q_α to the right.* Five 4-cells, each a coherence over a pasting context, applied by substitution and whiskered:
1. `(U₃(Θ) ∗₁ E) ∗₂ c₁(B) ⇛ c₁′(A) ∗₂ (Θ ∗₁ λ⁻¹)`. Both sides are full 3-terms over D³ (Θ a 3-disk), and `c₁′ : (U(a) ∗₁ W) ∗₁ E ⇛ a ∗₁ λ⁻¹` is a full coherence over D².
2. Distribute `− ∗₁ λ⁻¹` over the three ∗₂-factors of Θ. This is a coherence over three 3-disks glued along 2-disks, with a 2-disk attached along a 1-disk.
3. Naturality of the associator in its first argument: `((q_α ∗₁ λ) ∗₁ λ⁻¹) ∗₂ c₂(g) ⇛ asL(q_f ∗₁ W, λ, λ⁻¹) ∗₂ (q_α ∗₁ (λ ∗₁ λ⁻¹))`. This is a coherence over a 3-disk with two 2-disks attached. The source 2-cell of the 3-disk is sent to the composite `q_f ∗₁ W` as a whole.
4. Interchange of the 3-cells q_α and c₃ along a 1-cell, over `D³ ∨₁ D³`.
5. Naturality of c₄ in its 2-cell argument, over D³.

This gives `LHS ⇛ X ∗₂ (id_{q_x} ∗₁ q_α)`, where X is a 3-term in which q_α does not occur. Its ingredients are c₁′(A), `(q_f ∗₁ κ′) ∗₁ λ⁻¹`, `asR(q_f, W, λ) ∗₁ λ⁻¹`, `asL(q_f ∗₁ W, λ, λ⁻¹)`, `(q_f ∗₁ W) ∗₁ c₃`, `c₄(q_f ∗₁ W)` and the distributivity cell.

*Step 2: compare X with Paste[H′].* X and `P := Paste[H′]` are parallel 3-terms of the sub-context `𝒦(D¹) = (⊤, c, q_x, q_y, q_f)`. That context is equivalent to `ΣD¹ = D²` by Theorem 6.3, via (φ, ψ, H, H′). Pushed along φ, `X[φ]` and `P[φ]` are parallel 3-terms of the pasting context D², and both are full, since `q_f ↦ U(s_f)` uses every variable. So a coherence `Z : X[φ] ⇛ P[φ]` exists, and `Z[ψ] : X[φψ] ⇛ P[φψ]` lives in 𝒦(D¹). It remains to connect T with `T[φψ]` for `T = X, P`. The 3-terms X and P have depth-1 naturality cells `T↑` in `𝒦(D¹)↑Y`: they are built from 2-dimensional variables in 3-dimensional coherences. These exist by BMOSV's depth-1 theorem [cited], carried to arbitrary contexts by substitution (`conjectures/naturality-arbitrary-depth.md` §3, "Consequence", with Lemma 2 as corrected in the researcher response). Substituting the graph homotopy H′ gives `T↑[H′] : (T[φψ] ∗ boundary lifts) ⇛ (boundary lifts ∗ T)`. Since `∂X = ∂P`, the boundary lifts are the same for both. So `X ⇛ X[φψ] ⇛ P[φψ] ⇛ P` after whiskering by the common invertible boundary lifts, using that coherences, H′ and the lifts are invertible (Benjamin–Markakis–Sarti [cited]). Whiskering by `id_{q_x} ∗₁ q_α` and composing with Step 1 gives H′(q_α↑). ∎

**Status.** Step 1 consists of explicit coherences. Step 2 uses BMOSV depth 1 [cited] in a non-pasting context. Neither step is machine-checked: H′ in dimension 2 is not in the Agda. Dimension ≥ 3 needs ψ by transport along invertible spheres (`lax-colimit-of-point.md`, "What is known"), then the same two steps with depth `dim Γ − 1` lifts, which is Conjecture N.

### 6.5 Step B (B21): the maps at level 1, for graphs

Step B compares higher cocone morphisms over the constant diagram with family morphisms. At level 1, the constant instance of `coTr₁(Γ)` is the cylinder of 𝒦 in the direction of the q's. Because cocone transfors put the diagram index first (§4.2), its top cells run `m_x ∗₁ q′_f ⇛ q_f ∗₁ (id_⊤ ∗₀ m_y)`. That is the cylinder `𝒦↑Y` of §4.1 with its new top cells reversed. The family side is the cylinder `ΣΓ↑Y` with the same orientation. An equivalence at level 1 needs `φ↑`, `ψ↑` and homotopies between the cylinders. All the constructions below work for either orientation, by reversing the invertible cells used.

**φ↑ and ψ↑ for graphs (paper).** Both extensions need one new naturality cell each, and neither needs a conjecture:

- **ψ↑ over f** needs the lift of `q_f ∗₁ λ_{q_y}`. This is the paste rule of §4.3, applied to `q_f↑` and `λ↑`. Here `λ↑ : λ⁻ ∗₁ (id_⊤ ∗₀ w↑) ⇛ w↑ ∗₁ λ⁺` lives in the context `(⊤, c, w⁻, w⁺, w↑)`, which is the pasting context D², and both sides are full. So λ↑ is a coherence.
- **φ↑ over f** needs the lift of `U(s_f)`, where U is the unary operation `a ⇒ id_⊤ ∗₀ b` over D². Its variables a and b are 1-dimensional inside a 2-dimensional operation, which is depth 1. Lift it by **transport along an invertible cell**. Let `κ : U(u) ⇛ u ∗₁ λ⁻¹_b` be the full coherence over D², and write `v = u ∗₁ λ⁻¹_b`. Then
  ```
  U↑ := (κ⁻ ∗₁ (id_⊤ ∗₀ b↑)) ∗₂ v↑ ∗₂ (a↑ ∗₁ (κ⁺)⁻¹)
  ```
  runs from `U(u)⁻ ∗₁ (id_⊤ ∗₀ b↑)` to `a↑ ∗₁ U(u)⁺`, which are exactly a_U and b_U. Here `v↑` is the paste-rule lift of `u ∗₁ λ⁻¹`, using `λ⁻¹↑`, a coherence over D². κ⁻ and κ⁺ are κ at the minus and plus copies, and (κ⁺)⁻¹ is the reverse coherence. Every factor is a coherence over a pasting context or a cylinder variable. So U's depth-1 naturality is elementary, and BMOSV is not needed here.

**What remains for Step B at level 1:** the homotopies `ψ↑φ↑ ≃ id` and `φ↑ψ↑ ≃ id` on the cylinders. Their components over objects and arrows are lifts of H and H′ (Theorem 6.3). Those are 3-cells comparing the composites above, and they should follow by the same two-step method as Prop. 6.5. Levels k ≥ 2 iterate. None of this is machine-checked: φ↑ and ψ↑ need U and λ as constructors of the Agda expression language, which they are not yet.

## 7. What the Agda checks cover

- `Cones.agda` builds everything as CaTT syntax through one primitive, `binC k u w` (a coh over the glued-disk tree, with its type computed by the boundary rule of §1), plus two named coherences on 2-cells for the depth-1 lifts (`xchC`, the interchange, and `assocC`, the associator; §4.3). The constructions are **total functions**: `cone`, `cocone`, `susp`, `constCocone`, `CylOf.cyl`, `ctrf`, `coctrf`, `dualCtx`, `PhiAll.φ`, `ConstPoint.{φ,ψ,H,H′}`.
- `ConesExamples.agda` runs the certified checker on: 12 globular shapes (D⁰–D⁴, loop + 2-cell, loop + 3-cell, two parallel 2-cells, cospan, parallel pair, endo-arrow, composable pair); cones, (KE), cocones, suspensions, constant cocones, Gray cylinders, φ on all 12; ctrf and coctrf k ≤ 3 and the B6 equivalence on the six graphs; ctrf and coctrf k = 1 on the three 2-dimensional shapes (D², loop + 2-cell, two parallel 2-cells); the non-globular cone. It also has negative tests: an ill-typed context, a (KE)-violating cone, the depth boundaries (`ctrf 2` over D² and `ctrf 1` over D³ are undefined), and the naive identification.
- **Locality** (Remark 2.4, and the same argument for the cylinder, the cocone, φ and the B6 components) reduces each general statement to its generic case on disks Dᵐ, by substitution. So, for the classes stated, the checks are proofs modulo substitution admissibility. A1 is proved in Agda (`CaTTExp.Subst`); the reduction itself and the general (all-dimension) statements are the paper proofs above.
- **Not formalised:** a general Agda proof of Lemma 2.2 for all m (it needs typing lemmas for `binC` over arbitrary glued trees). This is follow-up S5.

---

## 8. Open items from this note

Ledger IDs in `open-issues.md`: S1 = B20, S2 = B21, S3 = B18, S4 = B23, S5 = B22; N^cone = B19.

| ID | Item | Owner |
|---|---|---|
| S1 | B6 in dimension ≥ 2. Dimension 2: proved (ψ, H machine-checked; H′ on paper, Prop. 6.5). Remaining: H′(q_α↑) in Agda (needs depth-1 lifts of 3-terms in a non-pasting context), and dimension ≥ 3 (ψ by transport, then N at depth dim Γ − 1). | this thread |
| S2 | B6 Step B for graphs. φ↑ and ψ↑ at level 1 constructed on paper (§6.5). Remaining: the level-1 homotopies, levels k ≥ 2, and an Agda check (needs U and λ in the expression language). | this thread |
| S3 | Depth-1 lifts in `CylOf`. Tr₁ over 2-dimensional Γ is done (§4.3). Remaining: lifts of the coherence constructors (naturality in maximal arguments) and the paste rule one dimension up, for Tr_k with k ≥ 2, plus a written proof of the k ≥ 2 sketch. | this thread |
| S4 | "Horns are cones" for graphs: compare `Tr₁(Γ)` with `Cone((D¹)^op ⊗ Γ)[π]` up to units, using Prop. 5.2. | this thread |
| S5 | General Agda proof of Lemma 2.2 (typing of `binC` on glued trees), removing the dependence on per-shape checks. | this thread |
| — | N^cone in dimension ≥ 3, reduced to RC(n) on join contexts (smallest case `Cone(D²; c)`; round 2 answered, `conjectures/answered/cone-over-coherences-r2-2026-11-18.md`; round-3 prompt `conjectures/outbox/cone-over-coherences-r3.md`), and N at depth ≥ 2 for nested whiskerings (part of C1). | C1 owner (naturality thread); this thread keeps attempting |
