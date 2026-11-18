# Weighted (co)limits as partially lax (co)limits in (∞,ω)-categories

## Background

Abellán–Haugseng–Martini ([2602.07604](https://arxiv.org/abs/2602.07604), Thm F and surrounding results) prove, for (∞,2)-categories:
- The I-lax colimit of `F : A → Cat_{(∞,2)}` is the total space of the classifying fibration, with the cartesian 2-morphisms and the cocartesian 1-morphisms over a marked class I inverted.
- **Weighted (co)limits can be expressed as partially lax (co)limits over the fibration classified by the weight, and conversely.**

Loubaton ([2406.05425](https://arxiv.org/abs/2406.05425)) proves:
- a lax Grothendieck construction for (∞,ω)-categories (Thm 4.1.4.2), in which "the extent of laxness is adjustable";
- results on marked (∞,ω)-categories and cartesian fibrations (Ch. 3).

## Statement

Let 𝒞 be an (∞,ω)-category. Let `W : I → (∞,ω)Cat` be a weight and `F : I → 𝒞` a diagram. Let `p : ∫W → I` be the (lax) Grothendieck construction of W, with its (co)cartesian cells marked.

**Show that the W-weighted limit of F, when it exists, is the partially lax limit of `F ∘ p` over `∫W`.** Here "partially lax" means: the cone cells over marked cells are invertible, and the cone cells over unmarked cells may be non-invertible. Show the converse as well. State the variance conventions precisely.

**Syntactic corollary (for finite I).** Suppose I is presented by a finite computad Γ and W by a finite computad Ψ with a map `π : Ψ → Γ` and a marking μ of Ψ. Then the marked lax limit `lim_{Ψ^μ}(γ ∘ π)` is the weighted limit. This needs:
- a condition on π making it present a (co)cartesian fibration;
- the dimension in which "partially lax" applies.

## What is known

- Dimension 2: AHM.
- Dimension ω: Loubaton's lax Grothendieck construction appears to be the main ingredient. The question is whether his partial-laxness parameter matches marked cones.
- **Side result, settled in the design note.** For marked cones, no closure condition on the marking is needed. Cone cells over composites of marked generators, over identities and over coherences are composites of invertible cells, hence invertible.

### Literature search (2026-11-18)
- **Known in dimension 2:** Abellán–Haugseng–Martini, as above.
- *The higher algebra of weighted colimits* ([arXiv 2406.08925](https://arxiv.org/abs/2406.08925)) treats (op)lax colimits of (∞,n)-categories, for all n, as weighted colimits (its Cor. 1.4). That is the easy direction. It does not express general weighted colimits as partially lax ones.
- **Open for n > 2 and for ω:** the converse (weighted ⇒ partially lax over the Grothendieck construction). Nothing found.

## Why it matters

If true, a type theory with lax limits and a per-variable "this cell must be invertible" flag gets all weighted limits with no further rule.

## What would count as a solution

A proof or reference in a model of (∞,ω)-categories, together with a computad-level characterisation of the π's that present fibrations.
