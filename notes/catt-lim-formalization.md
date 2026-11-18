# CaTT_lim's printed rules and their repair, machine-checked

*Agda formalization notes, 2026-11-18. Code: `src/CaTTExp/Lim/`. Companion to `limits-representables.md` §4.1, §10.1 and `conjectures/catt-lim-pseudo-vs-gray.md`. The results labelled D1–D5 and R1–R2 are checked by Agda 2.8.0 under `--safe` (no postulates). Two supporting facts are cited, not checked: the non-equivalence in D5 and "Z is invertible iff z is" in R2. The scope of each statement is given with it.*

## 1. What is encoded

- **Printed rules** (Mikhail, [arXiv 2412.13310v2](https://arxiv.org/abs/2412.13310), Def. 4.15), over named contexts so that blocks can grow in the middle exactly as the paper writes them (`Named.agda`, `Rules.agda`):
  - linearity `x ∝ t` (Def. 3.1), the selector `⋃{FV(p:T_p) | y ∈ FV(δ(x):∂X), y ∝ τ(p)}`, δCond and δCond‾ (`Conditions.agda`);
  - the cone judgment (EK), (KE);
  - the gray judgment and the ctrf judgment, instance n = 1 (natural transformations and cone morphisms).
- The gray/ctrf rules take a `Variant` with two switches: how the duplicate `x′` is typed (printed: `X` verbatim; repaired: `X` with the block renamed to its copy) and which boundary of earlier connecting cells the source condition tests (printed: `τ(p)`; repaired: `σ(p)`). `printed`, `copyFixed` (copy only) and `fixed` (both) are the three instances.
- **Repaired rules** (`Repaired.agda`): a specified cone construction (Thm 3.3, globular diagrams of dimension ≤ 2), a specified cone-morphism construction (diagrams of dimension ≤ 1) whose comparison cells over positive-dimensional diagram variables are marked, and a certified-substitution judgment: substituting into a marked variable requires a syntactic invertibility certificate (marked variables, full coherences, and operations whose top-dimensional arguments are certified).

## 2. Findings

**D1. The printed ctrf rule admits no intended cone morphism over an arrow.** For the diagram `f : x → y` and the canonical cone, no derivation of the cone-morphism judgment has a comparison cell `m_f` whose boundary type mentions `q_x`, whatever its source and target terms and whatever type the duplicate `q_f` has (`Defects.D1-printed`, `D1-copyFixed`). The intended `m_f : p_f ; (m_x ◁ f) ⇛ m_y ; q_f` has boundary type `p_y ⇒ q_x f`, so it is rejected. Repairing only the copy does not help; the cause is the selector: the source condition reaches earlier connecting cells only through `τ(p)`, and `m_x` is reachable only through `σ(m_x) = p_x`.

**D2. The printed copy `x′ : X` does not produce a second cone.** No printed ctrf derivation over the arrow has a duplicate block equal to the cone `Q` (`q_f : q_y ⇒ q_x f`), whatever the comparison block is (`Defects.D2`). This is a defect of the literal text, and is almost certainly notational shorthand: Thm 4.4 also writes `Γ′ = (xᵢ′ : Aᵢ)`, while the examples rename (`f′ : x′ → y′`). It carries less weight than the selector defect in D1 and D3, which is mathematical.

**D3. The same selector defect is in the printed gray rule, and it rejects the paper's own Example 4.1.** Mikhail's natural-transformation component `p_f : f · p_y ⇒ p_x · f′` is not derivable, nor is any component over an arrow whose type mentions `y′` (`Defects.D3-printed`, `D3-ex41`). Since Thm 4.4's construction has this form, the printed gray judgment does not recognise the shapes Thm 4.4 builds. This is new relative to the researcher response, which reported the defect for ctrf only.

**D4. What the printed rules do accept over an arrow is degenerate.** The printed gray rule accepts `p_f : f ⇒ f′` with `f′ : x → y` a parallel copy, and the printed ctrf rule accepts `m_f : p_f ⇛ q_f` with `q_f` a parallel copy of `p_f` (`Defects.degenerate-gray`, `degenerate-ctrf`). So as printed, the 2-dimensional universal property over an arrow diagram quantifies only over these degenerate shapes.

**D5. The cone judgment admits a non-canonical cone** over `(x, f : x → x, α : f ⇒ f)`, with α-projection `r ; (r ◁ f) ⇛ (r ; (r ◁ f)) ; (qf ▷ α)`, alongside the canonical one (`Defects.D5-*`). That their constant-diagram instances are not equivalent is the verified researcher result in `conjectures/lax-colimit-of-point.md`; it is cited, not re-proved.

**R1. With both repairs, the intended shapes are recognised.** The fixed rules accept the intended cone morphism over the arrow, Mikhail's Example 4.1, and the specified cone morphism over a composable pair (`Defects.intended-fixed`, `ex41-fixed`, `Repaired.morPair-recognised`). The specified cone construction reproduces the canonical cones and passes (KE) on the examples, including the 2-dimensional diagram of Example 4.1. The non-canonical cone of D5 is not the specified one, so the repaired cone judgment rejects it.

**R2. The collapse instance is rejected by the repaired rule.** Over the diagram `1_Y`, an arbitrary ambient 3-cell `z : a ⇛ b` gives the comparison cell `Z = (naturality of ρ⁻¹ at a) ; (z ◁₁ ρ⁻¹_s)`. The resulting substitution into the cone-morphism context is well typed (`Repaired.collapse-instance-typed`), so the unrestricted universal property applies to it. With `m_f` marked, it is rejected when `z` is an ordinary variable (`collapse-instance-rejected`) and accepted when `z` is certified (`collapse-instance-if-z-certified`).

A consequence of D1, D3 and D4 together: the researcher's collapse argument is a theorem about the *intended* calculus. The printed rules cannot run it, because over an arrow they never produce the cone morphisms it uses. Once the selector and copy are fixed, the argument applies, and the certified marking is what blocks it.

**D3b. The printed linearity test does not enforce multiplicity one** (`Linearity.agda`, open issue D3b, first found by the gray-contexts researcher).
- In Def. 3.1's OP case only the number of *linear* arguments is counted, so for a loop `ℓ`, `ℓ ∝ (ℓ·ℓ)·ℓ` holds (L1).
- Consequently the printed (KE) accepts the projection `p_ℓ : p_x ⇒ (p_x·(ℓ·ℓ))·ℓ` over the loop (L2).
- The repair is a strict test (`linear₁`): exactly one argument is linear in x, *and* x occurs in exactly one argument. The strict cone rule rejects that projection.
- All the intended examples still pass with the copy, selector and linearity repairs together (`fixedStrict`; L4).
- Strict linearity does not remove the D5 cone, whose repeated `r` sits in the source, which carries no linearity condition (L3). So the specified construction is still needed.

**O. The limit rules over two-tier L (B7, first slice; `OverL.agda`).** The shared schema of `limits-metatheory.md` §5.3 differs between P and L only in which transfor comparison variables are marked:
- **The switch.** Under P, the comparisons over every positive-dimensional diagram generator are marked. Under L, only those over *marked* generators are. Here the switch is implemented on the cone-morphism shapes.
- **O1.** The collapse instance is also a well-typed substitution in the L core.
- **O2.** Under L with f unmarked, the instance is admitted with nothing to certify (`CertSubL`, whose typing is the L core's). These are the unrestricted lax transfors.
- **O3.** Under L with f marked, the instance is rejected unless z is certified, as under P.
- **O4. Why the collapse argument does not go through over L.** The reverse interchanger `N⁻¹` cannot be formed as a coh in L, in any context and for any substitution (the L core's `no-ich⁻`). Cited from `limits-metatheory.md` §5.2 and not formalized: the image comparison `F(β)_f` is the interchanger over `ΣD¹ ∨ ΣD¹` at `(β, λ_f)`. So the inverse `R⁻¹ = B ; N⁻¹ ; A⁻¹` used by the collapse is not available by coherence. That no term of L inverts `F(β)_f` at all is Thm 1(2), still open (§3).

This is the syntactic side of `limits-metatheory.md` §1, which gives the semantic counterpart: strict ωCat with the Gray tensor has unrestricted lax limits and non-invertible `m_f`.

**H. The horn form of the filler rule (B15, first slice; `Horn.agda`).** This encodes `limits-metatheory.md` §5.3 over the arrow x → y for n = 0 and n = 1, on the specified shapes of `Cones`. Everything lives over the universal cone `(x, y, f, L, λ_x, λ_y, λ_f)`. For a cell w of 𝒦(c, L), its image transfor is F(w):
- `F(u)_f = (u ∗₀ λ_f) ∗₁ assoc` for a 1-cell u.
- `F(U)_f` is a pasting of associativity coherences with the forward interchanger of `U` and `λ_f`, for a 2-cell U.

A generic `inst` substitutes the boundary variables of a shape (`Cone`, `Tr₁`, `Tr₂`) by given terms and keeps the rest as new variables. This builds `Horn₀`, `Horn₁` and the rule's conclusions: J1 is the cell `uni^w`, and J2 is the new top variables of `Tr_{n+1}`, from T to `F(uni^w)`.
- **H1.** `Horn₀`, `Horn₁` and both rules' conclusion contexts are well formed in the CaTT core and in the L core.
- **H2.** For every `σ : Θ → Horn_n`, the conclusions are well typed in Θ. This follows from admissibility of substitution in each core and is not restated.
- **H3. The switch.** `Tr₁` marks its comparison over f, and `inst` sends it to `m_f` of `Horn₁`. That is a marked declaration under P, and under L exactly when f is marked. `Horn₀` has no comparison variables. Under L the marks are computed per generator, so marking an object x also marks its comparison `m_x`, which P never marks. This is intended: coherent marking marks the comparison over every marked generator, of any dimension, and P is the case where exactly the positive-dimensional generators are marked, with object comparisons left lax as in Mikhail's rules.
- **H4.** Under L, `F(U)_f` needs only the forward interchanger. Its canonical inverse pasting, with every step reversed, is a CaTT term but not an L term. The failing step is the reverse interchanger at `(U, λ_f)`; the other coherences it pastes are L terms. This rules out that pasting, not every inverse term, which is Thm 1(2) and still open.

**C. The d = 4 collapse instance on the specified shapes (B16, first slice; `Collapse4.agda`).** This is step 1 of the B9 proof (`limits-metatheory.md` §3) for k = 2, run on `Cones.ctrf 2` over the arrow, the shape the cone-constructions thread specifies:
- **C1.** Let `z : a ⇛ b` be an arbitrary 4-cell, so Ω₄ = D⁴. The diagram is substituted by `(Y, Y, 1_Y)`. The x- and y-components are the boundaries of a and b. The lower f-components are coherences: the inverse right unitor `ρ` and its naturality `N`. The top f-component is `μ_f = C_a ;₃ G(z)`, where `C_a` is a full-support coherence over D³ and `G(u) = (ρ_r ∗₁ (u ∗₀ 1_Y)) ∗₂ N_{α₁}`. This is a well-typed substitution `Ω₄ → Tr₂` in the CaTT core. So with unrestricted transfors the instance is admitted, and the rest of the argument applies to it.
- **Relation to §3's labels.** §3 puts `T_x := a`, `T_y := b`, `T_f := c_a⁻¹ ; z ; c_b`. Under the cylinder orientation of `Cones` the consistent assignment is the swap `μ_x = b`, `μ_y = a` (C2 shows `μ_x` must be b), and the single coherence `C_a` stands in for `c_a⁻¹` with `c_b` absorbed into `G`. So it is the same step up to labelling and invertible coherences.
- **C2.** The check is not vacuous: putting `a` for `b` at `μ_x` is rejected.
- **C3.** Under P, and under L with f marked, `μ_f` is marked (the shape marks `m⁻_f`, `m⁺_f`, `μ_f`). Its image has no certificate unless z is certified, so the repaired rule refuses the instance. The other marked images, the coherences `N`, are certified.


## 3. What is not formalized

- **The collapse derivation itself.** Building `z⁻¹` and its cancellation 4-cells from the `uni`/`⊨` output needs the star and `⊢uni` judgments and sizeable pasting terms. R2 (d = 3) and C1 (d = 4, on the specified `Tr₂`) check the input to that argument, step 1 of the B9 proof, not its algebra. Steps 2–5 (`uni`, the endpoint reduction, and `F(w)_f` being a coherence-case coh) are not formalized.
- **Non-derivability in the repaired theory.** R2 shows the repaired rule refuses the specific instance. That *no* derivation makes uncertified 3-cells invertible is a soundness statement and needs a model (open item (a) of `conjectures/catt-lim-pseudo-vs-gray.md`).
- **Generality.** The constructions cover cones over globular diagrams of dimension ≤ 2 and cone morphisms over diagrams of dimension ≤ 1. The judgments are the n = 1 instance of Mikhail's schema. That the specified construction passes the fixed rules for every globular diagram (the analogue of Thm 3.3/4.4) is checked on examples only.
- **Certificates.** `cert` is sound on the strength of Benjamin–Markakis ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)): coherences are invertible, and composites and whiskerings of invertible cells are invertible. That is cited.
- **Over L,** only the marking switch, the collapse instance and the absence of the reverse interchanger as a coh are checked. That no term of L inverts the image comparison `F(β)_f` is Thm 1(2) of `limits-metatheory.md`, still open: it needs strict soundness of L with (B). The identification of `F(β)_f` with the interchanger is cited from §5.2. The horn-form filler rule (B15) is encoded for n ≤ 1 over the arrow only (H). General n and general Γ need F(w) for higher w, which is the interchanger family of §5.2, and the shapes over 2-dimensional Γ (B18).
- **Orientation.** The literature thread notes that the cylinder formula `a_x → b_x` presents `I ⊗ Γ` under Steiner's convention. Mikhail's gray components `p_x : x → x′` have that form. Settled in `conventions.md` §5: Mikhail's "Γ ⊗ Dⁿ" is Dⁿ ⊗ Γ in the Steiner/Ara–Maltsiniotis orientation (so `I ⊗ Γ`), checked on the generator i ⊗ f, and his transformations are Bénabou-oplax.
