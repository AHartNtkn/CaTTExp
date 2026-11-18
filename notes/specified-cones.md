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
| | globular Γ, dim Γ = 2 | reduces to naturality of terms of dimension ≤ 2 (`relative-coherence.md` §4.2, paper, unchecked) and BMOSV depth 1 [cited] |
| | globular Γ, dim Γ ≥ 3 | needs Conjecture N at depth dim Γ − 1, for nested whiskerings only [conj] |
| **Cones over non-globular Γ**: recursion through substitutions, one family of universal cells `Π(Q, B)` | Γ whose non-variable boundary terms are 1-dimensional | **proved** (Prop. 5.2); machine-checked on `τ : f ∗₀ g ⇒ h` |
| | arbitrary Γ | equivalent to the cone form of N, `N^cone`, posed in `conjectures/cone-over-coherences.md` [conj]; dimension 2 follows from RC(2) |
| **B6, level 0**: a Γ-family of elements gives a cocone over the constant point diagram (`φ`) | every globular Γ, every dimension | **proved** (Prop. 6.2); machine-checked on all 12 shapes |
| **B6, equivalence**: `φ`, `ψ` and invertible homotopies `ψφ ≃ id`, `φψ ≃ id` | globular Γ of dimension ≤ 1 (graphs) | **proved** (Thm 6.3); machine-checked on 6 graphs |
| | dimension ≥ 2 | reduced to transport along unit coherences (§6.4) [conj] |
| B6 Step B (cocone morphisms vs family morphisms) | | reduced to depth-1 naturality of two named cells (§6.5) [conj] |

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

**Dimension 2.** Over a 2-dimensional Γ, Tr₁ needs the lift of `p_x ∗₀ α` (depth 1) and of `p_f ∗₁ (p_x ∗₀ α)` (depth 1, all 1-cells affected). These are terms of dimension 2, so `relative-coherence.md` §4.2 (N for every term of dimension ≤ 2, any up-closed Y; paper, not yet independently checked) supplies them, and BMOSV Thm 3.1 [cited] covers depth 1 in general. In general the depth of the projection variables in the level-k types is `dim Γ − 1`, independent of k. The Agda construction does not detect this itself: `ctrf 1 (DiskEx 2)` returns a context, and the certified checker rejects it (a recorded test). Implementing depth-1 lifts is follow-up item S3 (§8).

**Dimension ≥ 3** needs Conjecture N at depth `dim Γ − 1`, for **nested whiskerings only** (composition constructors). This is a much narrower instance than general N. It is recorded under C1 (`conjectures/outbox/naturality-arbitrary-depth.md`).

### 4.4 "Horns are cones" (`limits-metatheory.md` §5.3): an orientation finding

That note conjectures `Tr_n(Γ) = Cone(Dⁿ ⊗ Γ)[π]` up to unit coherences. Already for Γ a point and n = 1, the cone over `D¹ ⊗ x = (x⁻ —x↑→ x⁺)` has `p_{x↑} : p_{x⁺} ⇒ p_{x⁻} ∗₀ x↑`, which collapses to `p_{x⁺} ⇒ p_{x⁻} ∗₀ id_x`. That is a transfor from the **+** cone to the **−** cone, the reverse of Tr₁'s `m_x : p⁻ ⇒ p⁺`. The reason is that lax cone cells over a 1-cell run from the target's projection to the source's. So the statement needs `(D¹)^op`, or the reversed transfor direction, in the first factor. Since `D¹ ⊗ Γ` for 1-dimensional Γ has composite boundaries of dimension 1 only, its cone exists by Prop. 5.2. A full syntactic comparison for graphs is therefore within reach; it is follow-up S4.

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

**Dimension 2.** For a full 2-dimensional coherence `c : a ⇒ b` over a chain, `P(b)` and `P(a) ∗₁ (p_{x₀} ∗₀ c)` are parallel 2-terms of the cone, with the same strict image (the strict cone over the path). So RC(2) (`relative-coherence.md` Theorem A; paper, unchecked) gives `Π`. Composition coherences of dimension 2 need *existence* of a composite with prescribed boundary, by layering. This is the analogue of "existence in G(n) ⇐ RC(n−1)" there. Details are in the conjecture file.

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

### 6.4 Dimension ≥ 2 (open)

φ exists in all dimensions (Prop. 6.2). What is missing is ψ and the two homotopies:
- **ψ** needs, for each t, a cell `ψ(s_{σt}) → ψ(s_{τt})` built from q_t. q_t's boundary differs from the desired one by unit coherences *in every dimension below*. So ψ(s_t) is q_t transported along an invertible boundary comparison. In dimension 2 the transport is explicit: `ψ(s_α) := κ ∗₂ (q_α ∗₁ λ)` with κ assembled as in c₁–c₄. The general transport is the "transport along an invertible sphere" operation of `lax-colimit-of-point.md` ("What is known").
- **The homotopies** need cylinders on 𝒦 at depth `dim Γ − 1`.

Both are follow-up S1 (§8). Since every comparison involved has equal strict images, RC(n) would supply them.

### 6.5 Step B (open)

Higher cocone morphisms against family morphisms: φ and ψ must extend to cylinders, `φ↑ : ΣΓ↑ → 𝒦↑` and back. For graphs this needs exactly two depth-1 naturality cells: of the unary operation U over D² in all its variables (a suspended lax square), and of λ_w in w. The latter's `Q↑Y` is the pasting context D², so it is a plain coherence. The former is within BMOSV's depth-1 theorem and `relative-coherence.md` §4.2. Follow-up S2.

---

## 7. What the Agda checks cover

- `Cones.agda` builds everything as CaTT syntax through one primitive, `binC k u w` (a coh over the glued-disk tree, with its type computed by the boundary rule of §1). The constructions are **total functions**: `cone`, `cocone`, `susp`, `constCocone`, `CylOf.cyl`, `ctrf`, `coctrf`, `dualCtx`, `PhiAll.φ`, `ConstPoint.{φ,ψ,H,H′}`.
- `ConesExamples.agda` runs the certified checker on: 12 globular shapes (D⁰–D⁴, loop + 2-cell, loop + 3-cell, two parallel 2-cells, cospan, parallel pair, endo-arrow, composable pair); cones, (KE), cocones, suspensions, constant cocones, Gray cylinders, φ on all 12; ctrf and coctrf k ≤ 3 and the B6 equivalence on the six graphs; the non-globular cone. It also has negative tests: an ill-typed context, a (KE)-violating cone, the depth boundary, and the naive identification.
- **Locality** (Remark 2.4, and the same argument for the cylinder, the cocone, φ and the B6 components) reduces each general statement to its generic case on disks Dᵐ, by substitution. So, for the classes stated, the checks are proofs modulo substitution admissibility. A1 is proved in Agda (`CaTTExp.Subst`); the reduction itself and the general (all-dimension) statements are the paper proofs above.
- **Not formalised:** a general Agda proof of Lemma 2.2 for all m (it needs typing lemmas for `binC` over arbitrary glued trees). This is follow-up S5.

---

## 8. Open items from this note

Ledger IDs in `open-issues.md`: S1 = B20, S2 = B21, S3 = B18, S4 = B23, S5 = B22; N^cone = B19.

| ID | Item | Owner |
|---|---|---|
| S1 | B6 in dimension ≥ 2: ψ by transport along invertible spheres, and the cylinder homotopies; check via RC(n). Explicit dimension-2 case first. | this thread |
| S2 | B6 Step B for graphs: depth-1 naturality of U and λ, giving φ↑ and ψ↑. | this thread |
| S3 | Depth-1 lifts in `CylOf` (BMOSV / `relative-coherence.md` §4.2), giving Tr_k over 2-dimensional Γ in Agda. Coordinate with the Gray-contexts Agda thread, whose `GrayCtx` cylinder supports binary 1-composites. | this thread |
| S4 | "Horns are cones" for graphs: compare `Tr₁(Γ)` with `Cone((D¹)^op ⊗ Γ)[π]` up to units, using Prop. 5.2. | this thread |
| S5 | General Agda proof of Lemma 2.2 (typing of `binC` on glued trees), removing the dependence on per-shape checks. | this thread |
| — | N^cone in dimension ≥ 3 (`conjectures/cone-over-coherences.md`), and N at depth ≥ 2 for nested whiskerings (part of C1). | C1 owner (naturality thread); this thread keeps attempting |
