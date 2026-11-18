# Lax limits in oriented categories: is the unrestricted universal property consistent?

*Self-contained problem statement. No project context needed.*

## Background

**Oriented categories.** Gepner and Heine (*Oriented category theory*, arXiv:2510.10504) define an *oriented category* to be a category enriched in ∞Cat, the ∞-category of (∞,∞)-categories, with respect to the lax Gray tensor product (Campion, arXiv:2311.00205; Loubaton, arXiv:2406.05425).
- The main example is ∞Cat itself, whose hom-objects are Fun^lax(S, T).
- In an oriented category, the two ways of composing 2-cells β : u ⇒ u′ : c → L and φ : v ⇒ v′ : L → y are related by a *directed* interchange cell, not an invertible one. In execution order, its direction is

  ```
  (u◁φ) ; (β▷v′)  ⇛  (β▷v) ; (u′◁φ).
  ```

- Gepner–Heine's companion paper *Colimits in oriented category theory* (arXiv:2608.02592) studies oriented (co)limits.

**Lax cones.** For a finite diagram given by a computad Γ (e.g. a single arrow f : x → y), a lax cone with apex c consists of:
- projections p_x : c → x for each object x;
- for each arrow f : x → y, a cell p_f : p_y ⇒ p_x ; f;
- for each higher cell, the corresponding higher cells.

None of these is required to be invertible.

**Morphisms of lax cones (lax transfors).** A morphism m : P → Q of lax cones consists of:
- cells m_x : p_x ⇒ q_x;
- for each arrow f, a comparison cell m_f : p_f ; (m_x ▷ f) ⇛ m_y ; q_f;
- and so on, with Gray-tensor shapes.

In the *unrestricted* version, m_f is arbitrary. In the *pseudo* version, m_f must be invertible for every positive-dimensional diagram variable.

**What is known.** In an ordinary (cartesian-enriched) (∞,ω)-category, the unrestricted version cannot be the universal property of any limit object. A universal cone λ forces every m_f to be invertible, because ucone_*(β) has the invertible interchanger as its comparison cell. With the universal property imposed in all dimensions, every cell of dimension ≥ 3 is forced to be invertible as well. The pseudo version is the correct property there. (This is a verified result in the companion file `catt-lim-pseudo-vs-gray.md` of this folder.)

## The problems

Let 𝒦 be an oriented category, e.g. ∞Cat with lax transformations, and Γ a finite computad, starting with the single arrow x → y.

**Problem 1 (no collapse).** Show that the forced-invertibility argument does not go through in 𝒦. Concretely:
- define the lax limit L of a Γ-diagram in 𝒦 by the unrestricted universal property: an equivalence, natural in c, between 𝒦(c, L) and the (∞,ω)-category of lax cones with apex c and unrestricted lax transfors;
- show that this does *not* force the m_f, or any higher cells, to be invertible;
- ideally, exhibit an oriented category, such as ∞Cat, together with a diagram whose lax limit has a cone morphism with non-invertible m_f.

**Problem 2 (existence).** Does every finite diagram in ∞Cat, viewed as an oriented category, have a lax limit in the unrestricted sense? Is it Gepner–Heine's oriented limit? For the arrow diagram, is it the oriented comma/arrow construction, e.g. built from Fun^lax([1], –)?

**Problem 3 (comma and hom objects).** For the partially lax limit of ⊤ →a C ←b ⊤, with the b-comparison invertible and m unrestricted, is the result the full hom-object Hom_C(b, a), with non-invertible arrows? Compare the cartesian case, where the analogous construction gives only the maximal sub-∞-groupoid (Gagna–Harpaz–Lanari, arXiv:2012.04537).

## Why it matters

A type theory for higher categories needs limits whose universal property is stated by generic filler rules. The verified negative result shows that in an ordinary (cartesian) setting, lax cone morphisms must be restricted to pseudo ones, and that hom-objects then cannot be built as limits. This problem asks whether moving to oriented categories, where the relevant interchange is directed, restores the unrestricted lax universal property. If it does, comma and hom objects become limits again.

## What would count as a solution

Any of the following:
- a proof of Problem 1, or a counterexample showing that some other mechanism still forces invertibility in oriented categories;
- references settling Problems 2–3, e.g. from Gepner–Heine's oriented (co)limits;
- partial answers in the (∞,2) case, using Gray-enriched 2-categories and lax limits in the sense of Street and Lack.
