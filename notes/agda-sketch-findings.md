# Agda milestone 1: core CaTT and a first "representables" sketch

*2026-11-18. Accompanies `src/`. Everything stated as "checked" below is
verified by the certified checker when `src/Everything.agda` is typechecked.*

## What is formalized

**Core CaTT** (`CaTTExp.Syntax`, `Typing`, `PastingTrees`, `Check`)

- Raw syntax with de Bruijn *levels*, so extending a context never renames.
- Substitution on raw syntax.
- The four judgments `Γ ⊢ctx`, `Γ ⊢ty A`, `Γ ⊢tm t ∶ A` and `Γ ⊢sub σ ∶ Δ`.
- Finster–Mimram's pasting judgments `Γ ⊢ps x ∶ A` (pss, pse, psd) and `Γ ⊢ps`.
- Source and target ∂⁻ and ∂⁺.
- The single `coh` rule with its two side conditions (full coherence, or operation).

The theory is parameterised by a **signature of closed constants** (`CaTTExp.Signature`). Pure CaTT is the empty signature (`CaTTExp.Pure`). This is the extension point the sketch uses.

**Deviations from the paper.** All of these are standard and believed equivalent:

- The operation side condition types `t : A` in Γ and asks Var(t:A) = Var(∂⁻Γ). The paper types it in the sub-context ∂⁻Γ. These agree because boundaries are downward closed.
- Side conditions are booleans lifted to propositions, so they are decidable by construction.

**Pasting contexts from trees.**
- `psOf : Tree → Σ Ctx _⊢ps` builds a context and its pasting derivation from a Batanin tree.
- The checker decides `Γ ⊢ps` by parsing Γ to a tree and comparing contexts.

**Certified checker.** Every success returns a derivation, so a successful run is a proof. It is also proved complete (`CaTTExp.Completeness`, using the deterministic pasting checker `CaTTExp.PastingCheck`), so it decides all four judgments.

**Checked examples** (`CaTTExp.Examples`)

Accepted:
- identity
- binary composition
- the ∂⁻ and ∂⁺ computations
- the associator
- the left unitor
- vertical and horizontal 2-cell composition

Rejected:
- a coh over the non-pasting sphere
- a "composite" that forgets variables
- an "inverse" of an arrow

**Metatheory added since milestone 1** (all checked with `--safe`, no postulates):

- Substitution admissibility, `CaTTExp.Subst` (PR #20); pure instance in `CaTTExp.PureMetatheory`.
- Checker completeness and decidability of the four judgments, `CaTTExp.Completeness`. The pasting judgment is decided by `CaTTExp.PastingCheck` (read left to right, descend with psd to the dimension of the next object). Hypotheses: the equality test on constants is reflexive and `valid?` is complete; both hold for pure CaTT.
- Constant substitutions `(c : ⋆) ⊢ !_Γ ∶ Γ`, `CaTTExp.ConstSub`, for constant-free Γ in any signature, hence for every pure Γ. Some hypothesis is needed (argued, not formalised): Γ = (x : c₀ → c₁) with two unrelated constants should have no such substitution, since nothing has type c₀ → c₁.
- Weakening and context extension along a substitution, `CaTTExp.Weakening`.
- Suspension, `CaTTExp.Suspension`: Σ preserves all four judgments for constant-free syntax (all syntax in pure CaTT), including both side conditions and the pasting judgment. `elements-at` puts any derivation over Θ in the context ΣΘ[a, b] (`limits-representables.md` §8 target 1).
- Soundness for the one-object, locally discrete strict models B G (G a group, constants allowed), `CaTTExp.GroupModel`. General strict ω-categories are ledger item A3a.

## The sketch (`CaTTExp.Sketch.Representables`)

**Setup.** Read CaTT with ambient ωCat, so ⋆-terms are ω-categories, 1-cells functors, and 2-cells transformations. Add closed constants:

- `⟦Γ⟧ : ⋆` for every well-formed *pure* context Γ (the free ω-category on Γ);
- `⟦σ⟧ : ⟦Γ⟧ → ⟦Δ⟧` for every pure substitution Δ ⊢ σ : Γ.

Validity of a constant is a pure CaTT judgment, decided by the pure checker.

### Findings

**1. Shapes are stratified.**
- ⟦_⟧ accepts only constant-free contexts.
- This is natural rather than a restriction: a shape is a computad, whose generators' types are built from other generators, never from named objects.
- It is not a universe either. ⟦Γ⟧ is a particular finitely presented object, not a code for one.

**2. Functoriality of ⟦_⟧ is not derivable.** *Machine-checked* in `CaTTExp.Sketch.NonDerivable` (2026-11-18). The separating model is B(ℤ/2): every ⟦Γ⟧ goes to the one object and every ⟦σ⟧ to the non-identity element. By soundness for group models, no term has type ⟦s⟧ ; ⟦id⟧ ⇒ ⟦s⟧, ⟦id_Γ⟧ ⇒ id, or ⟦σ ∘ τ⟧ ⇒ ⟦σ⟧ ; ⟦τ⟧, nor the reverse of any of them, in the empty context or any context with a valid ℤ/2 environment. The original informal argument follows.
- Nothing relates ⟦σ ∘ τ⟧ to ⟦τ⟧ ; ⟦σ⟧, or ⟦id⟧ to the ambient identity.
- `coh` only proves laws for *arbitrary* cells (variables). It never proves laws about named constants.
- Argument for non-derivability:
  - Interpret the ambient theory in a strict ω-category: the free category on the graph whose vertices are the ⟦Γ⟧ and whose edges are the ⟦σ⟧, with only identity cells above dimension 1.
  - Strict ω-categories model CaTT, so every derivable term is interpreted.
  - A cell ⟦s⟧ ; ⟦id_{D₁}⟧ ⇒ ⟦s⟧ would become an identity between two distinct paths, which is impossible.
  - The formal proof uses B(ℤ/2) instead of the free category on the graph, since it only needs to separate the two sides.
- Any law about a new object must come from a new rule. There are three options:
  - (a) definitional equalities, which pull in CaTT_su/sua-style strictness early, against the plan;
  - (b) invertible comparison cells, which need an invertibility judgment or type from the start (as in Mikhail's `⊨` or ICaTT);
  - (c) state ⟦_⟧ by a *universal property* (Yoneda-style) whose generic filler rule produces these cells, as Mikhail's `uni` rules do for limits. Option (c) matches the "every higher cell from generic rules" principle.

**3. Elements need only one representable, by dimension shift** (checked).
- Objects of C are maps x : ⟦D₀⟧ → C, and arrows of C are ambient 2-cells f : x ⇒ y.
- For lax or pseudo transformations out of the one-point category, Hom(⟦D₀⟧, C) is C again.
- Then:
  - the cell types of C are dependent for free, since "f : x → y" is just an ambient hom-type;
  - composition in C is ambient vertical composition;
  - F(f) is right whiskering, and F(g∘f) ≅ F(g)∘F(f) is a plain coherence;
  - the naturality square of α : F ⇒ G at f is the interchange coherence.
- This reproduces the "Functors" section of *Omega-Categories Made Easy* mechanically.
- The alternative, arrows as maps ⟦D₁⟧ → C, loses the dependent typing. Composing two such elements needs gluing along t(a) = s(b). That is an equation CaTT cannot state, or else a lax colimit (Mikhail's construction with the orientation reversed), which glues along a *connecting* cell and so yields a three-cell shape, not Comp₂.
- So the higher ⟦Γ⟧ matter for *diagram shapes*, such as functors ⟦Γ⟧ → C as Γ-diagrams and limits indexed by Γ, not for elements.

**4. Tension: plain CaTT forces pseudo, not lax** (checked).
- The naturality coherence typechecks in *both* orientations, `naturality` and `naturality⁻¹`. In fact coherences are invertible (Benjamin–Markakis).
- So reading the ambient as a plain CaTT model makes every transformation pseudo-natural.
- Lax transformations have one-way naturality cells. Strict and weak ω-categories with lax transformations are enriched over the *lax Gray tensor*, not the cartesian product. Horizontal composition of lax transformations is only functorial up to a non-invertible interchanger (Gray, for 2-Cat).
- So **"ambient = ωCat with lax transformations" and "ambient = a CaTT model" are incompatible.** The options:
  - (a) the ambient is pseudo, ωCat with pseudo-natural transformations. Laxness lives *inside* via lax limits and colimits, which Mikhail shows is expressible in plain CaTT;
  - (b) develop a **Gray-CaTT**: the coh rule's full-coherence case splits, so interchange-type coherences get a fixed orientation. Mikhail's Gray-shape judgments and the naturality construction of Benjamin–Markakis–Offord–Sarti–Vicary already compute these orientations. This is more expressive and more novel, and is the natural home of the internal-hom/Gray-tensor work;
  - (c) both: a Gray-CaTT whose invertible fragment is CaTT.

## Questions this raises

1. Given finding 4, is the lax default about the *ambient* (requiring a Gray-CaTT) or about what is *expressible* (lax limits, lax transformations as internal constructions over a pseudo ambient)?
2. Is option 2(c), ⟦_⟧ by a universal property, the right home for functoriality? If so, what exactly is the property? Two candidates:
   - maps ⟦Γ⟧ → C correspond to Γ-shaped data in C, via dimension shift;
   - ⟦Γ⟧ is a (non-lax) colimit of disks.
3. With dimension shift, is ⟦D₀⟧ (the terminal or unit object) the only representable needed early on? Higher ⟦Γ⟧ could then wait until diagram-indexed limits come up.

## Suggested next steps

- ~~Prove substitution admissibility for the core.~~ Done (PR #20).
- Prototype a minimal Gray-CaTT side condition: orient the full-coherence case using Mikhail's gray judgments. Check that the naturality cell then typechecks in only one direction.
- State Mikhail's lax limits over the signature mechanism, with cone and transfor judgments, and check his examples.
