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

## 3. What is not formalized

- **The collapse derivation itself.** Building `z⁻¹` and its cancellation 4-cells from the `uni`/`⊨` output needs the star and `⊢uni` judgments and sizeable pasting terms. R2 checks the input to that argument, not its algebra.
- **Non-derivability in the repaired theory.** R2 shows the repaired rule refuses the specific instance. That *no* derivation makes uncertified 3-cells invertible is a soundness statement and needs a model (open item (a) of `conjectures/catt-lim-pseudo-vs-gray.md`).
- **Generality.** The constructions cover cones over globular diagrams of dimension ≤ 2 and cone morphisms over diagrams of dimension ≤ 1. The judgments are the n = 1 instance of Mikhail's schema. That the specified construction passes the fixed rules for every globular diagram (the analogue of Thm 3.3/4.4) is checked on examples only.
- **Certificates.** `cert` is sound on the strength of Benjamin–Markakis ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)): coherences are invertible, and composites and whiskerings of invertible cells are invertible. That is cited.
- **The two-tier L variant** (`pseudo-vs-gray.md` R11) is not attempted here. It needs the Gray core being built in a separate thread (`CaTTExp.TypingWith` with the L side condition).
- **Orientation.** The literature thread notes that the cylinder formula `a_x → b_x` presents `I ⊗ Γ` under Steiner's convention. Mikhail's gray components `p_x : x → x′` have that form; matching the orientation to `Γ ⊗ I` is unchecked here.
