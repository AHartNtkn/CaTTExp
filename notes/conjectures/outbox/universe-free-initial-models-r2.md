# Which initial algebras follow from finite limits, finite colimits and descent?

## Setting

Let 𝓔 be an (∞,1)-category with finite limits and finite colimits. Consider the following hypotheses, each a "universe-free" axiom (no object classifies other objects):

- **(D) descent:** every finite colimit in 𝓔 is van Kampen for all maps (universal and effective), as in an ∞-topos (Lurie, HTT §6.1.3).
- **(D_c) restricted descent:** 𝓔 carries a class of maps 𝓒 (in the intended example, cocartesian fibrations in the (∞,1)-category of (∞,ω)-categories) containing all maps between objects that are groupoids, closed under base change and composition, such that every finite colimit is van Kampen for 𝓒, and colimits indexed by finite groupoids are van Kampen for all maps.
- **(L) local cartesian closure**, and **(Ω) a subobject classifier**.
- **(T) truncation:** n-truncations exist and families with n-truncated fibres over a groupoid Y descend uniquely along `Y → τ_{≤n+1} Y`.

A **positive signature** over a presentable 𝓔 is a finite list of operations `S(X) → T(X)` (and cells between composites of operations), where each source S is an accessible functor and each target T is an accessible limit-preserving functor; models are taken with strong homomorphisms. In a presentable 𝓔 every positive signature has an initial model (adjoint functor theorem plus presentability of categories of algebras; Kerodon 9.4.9, 9.5.1–9.5.2), and limit-preserving targets are the largest class that can be paired with every source. The question is what survives when 𝓔 is only finitely complete and cocomplete.

Known:
- Rasekh (*Every elementary higher topos has a natural number object*, TAC 37 (2021), arXiv:1809.01734) proves that a finitely bicomplete locally cartesian closed (∞,1)-category with a subobject classifier and descent (HTT 6.1.3) has a natural number object, built from the loop space ΩS¹ of the circle `S¹ = * ⊔_{*⊔*} *`. No universe is used for this; universes enter only in his §5.
- In 1-category theory the analogue fails: the topos of finite sets has no natural number object, and finite colimits in a 1-topos are not effective for non-free group actions.
- In the univalent setting, the integers are the initial pointed type with an equivalence (Altenkirch–Scoccola, arXiv:2007.00167, with bi-invertible data; the quasi-inverse presentation gives a non-set, Basold–Geuvers–van der Weide 2017).

## Questions

**1 (main).** Under (D) + finite limits and colimits (without (L) or (Ω)), does every positive signature whose sources are built from finite limits, finite colimits and products with fixed objects, and whose targets are X, ⊤, finite limits and cotensors by finite objects, have an initial model? If not, give the largest such class and a model of (D) in which a signature just outside it fails. In particular: does (D) alone give a natural number object (is Rasekh's use of (L) and (Ω) necessary)? Does (D) + (L) + (Ω) give initial algebras for all finitary polynomial endofunctors, i.e. finitary W-types, and free monoids?

**2.** The same with (D_c) + (T) in place of (D), for an (∞,1)-category that is the underlying (∞,1)-category of an (∞,2)-category with cotensors by [1] (so that cocartesian fibrations are defined by the usual adjoint condition). The intended model is the (∞,1)-category of (∞,ω)-categories, where (D_c) and (T) hold.

**3.** Non-derivability: is there a model of finite limits, finite colimits, (D) (or (D_c) + (T)), with some positive signature in the class of Question 1 having no initial model? A non-presentable example is required, since every presentable model has all initial models.

## Why it matters

A type theory without a universe must state the consequences of a universe as rules. If finite colimits with descent already produce natural numbers and inductive objects, as Rasekh's theorem suggests, then an "initial model" rule could be replaced, wholly or partly, by descent; if not, a model separating them shows that both rules are needed.

## What would count as a solution

For Question 1 and 2, a proof for a stated class with a countermodel just outside it; for Question 3, an explicit model. A reference with the exact statement counts.
