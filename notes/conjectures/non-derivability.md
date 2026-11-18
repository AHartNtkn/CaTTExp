# Three non-derivability questions for a coherence-style theory of ω-categories with limits

> **Status: answered (researcher, verified 2026-11-18).** All three are **not derivable**. Q1 (recursion): categories with an auxiliary equivalence relation, where N is the discrete ℕ but every map N → Bool is constant. Q2 (discreteness): the comma (H₁(–)[1] ↓ id_{D(ℤ)}), where N has a K(ℤ,1) of self-maps from a test object; this needs R-A in its hom-wise form, which is the project's. Q3 (effectiveness): posets with discrete homs. Prompt, response and verification: `answered/non-derivability-2026-11-18.md`.

*A self-contained problem. No knowledge of the project that posed it is assumed. The three questions are independent. The smallest one is Question 3 (effectiveness of quotients), which is a question about 1-categories of sets inside a higher setting.*

## Background

**The base theory.** Fix a dependent type theory 𝕋 for weak ω-categories in the style of CaTT (Finster–Mimram, LICS 2017): contexts of typed variables (objects, and cells between cells), and one term former `coh` producing cells between parallel composites over pasting contexts. Add to it, as rules stated by universal properties witnessed by cells (never by definitional equalities, and with no universe):
- **finite limits** in the ambient (∞,ω)-category of ω-categories: a terminal object ⊤, pullbacks, and *cotensors* `[⟦D⟧, C]` by finite shapes D;
- **finite colimits**: pushouts, coequalisers, coproducts, and lax colimits of finite diagrams;
- **R-A (free objects on finite computads):** for each finite context Γ, an object ⟦Γ⟧ such that maps `⟦Γ⟧ → C` correspond to substitutions Γ → C (up to cells at every level). In particular, for the loop `L = (x : ⋆, s : x → x)`, maps `⟦L⟧ → C` correspond to an object of C with an endo-1-cell.

Write `Hom_C(a, b)` for the pullback of `[⟦D¹⟧, C] → C × C` along `(a, b)`. Put `N := Hom_{⟦L⟧}(x, x)`, with `zero := 1_x` and `succ := – ; s`. Semantically (in the (∞,ω)-category of (∞,ω)-categories), ⟦L⟧ is the free category on one loop and N is the discrete set ℕ (the free weak ω-category on a graph is the free category on it).

**Truncation levels.** An object C is *n-truncated* (C trunc n) when parallel cells into C of level ≥ n + 1 are connected and cells of level n + 1 are invertible. Sets are the 0-truncated objects. A *truncation rule* `Trunc_n` gives for each X a reflection `|–| : X → ‖X‖_n` onto n-truncated objects (existence of extensions, and of cells between extensions agreeing on X).

**Derivability.** A rule is *derivable* if every instance of its conclusion is a term of 𝕋 (with the stated additional rules). Non-derivability can be shown by a model of the rules in which the conclusion fails, or by a normal-form argument on the syntax.

## Statement

**Question 1 (recursion on a hom object).** In 𝕋 (finite limits, finite colimits, R-A), is the recursion principle for N derivable? That is: for every object A, point `a : ⊤ → A` and map `f : A → A`, is there a map `r : N → A` with invertible cells `r ∘ zero ≅ a` and `r ∘ succ ≅ f ∘ r`?

**Question 2 (discreteness of N).** In 𝕋 together with any rules that make Bool := ⊤ ⊔ ⊤ a set (coproducts of sets are sets and disjoint), is `N trunc 0` derivable? More generally: is "⟦Γ⟧ is 1-truncated for every finite graph Γ" derivable?

**Question 3 (effective quotients).** In 𝕋 + Trunc₀, for a set X and an equivalence relation `R ↪ X × X` (R a set, with reflexivity, symmetry and transitivity maps), let `X/R := ‖coeq(R ⇉ X)‖₀` (pseudo coequaliser, then set-truncation). Is the canonical map `R → X ×_{X/R} X` an equivalence (derivably)?

The expected answer to all three is **no**. A "no" should come with a model (or a syntactic argument) showing it; a "yes" with a derivation.

## What is known

- **Semantically all three conclusions hold** in the intended model (ω-categories, or (∞,ω)-categories): N is ℕ, free categories on graphs are 1-categories (Dwyer–Kan-type rigidity; the free weak ω-category on a graph is the free category on it), and sets are ordinary sets, whose quotients are effective.
- **Where the obvious derivations stop.**
  - *Q1.* R-A produces maps *out of* ⟦L⟧ from endo-1-cells of an object C; functoriality then gives `N → Hom_C(c, c)`. To land in an arbitrary A with action f, one needs a C whose endo-hom at some c is A with composition-by-s acting as f. The lax colimit T of the diagram (A, f) over L is the natural candidate, but colimit rules describe maps *out of* T, not the homs of T. With a rule identifying lax colimits with Grothendieck constructions plus a "directed J" rule (comma objects `a ↓ C` are free cocartesian fibrations), recursion and induction *are* derivable (the posing project has a proof). The question is whether those rules can be avoided.
  - *Q2.* A Hedberg-style derivation (as in homotopy type theory's proof that ℕ is a set) goes through with the directed J rule up to one step: from `eq(m, n) = true` produce an invertible arrow m → n. The standard proof inducts on m for all n at once, which needs a function object Π over N (exponentials), or an induction principle whose parameter changes along the step. Without exponentials the derivation stalls there.
  - *Q3.* In homotopy type theory effectiveness is proved by encode–decode against a family `X/R → Prop`, which uses a universe of propositions (univalence). The theory here has no universe. Effectiveness is a statement about maps *into* a pullback over X/R, and no colimit or truncation rule describes those.
- **1-categorical analogues.** Finite sets have finite limits and colimits but no natural numbers object, so a primitive NNO is independent of finite limits and colimits; but here N is already given by R-A, so this does not settle Q1. Regular categories with coequalisers of equivalence relations need not be exact (e.g. torsion-free abelian groups, or topological spaces), which is the 1-categorical shadow of Q3; the question is whether such a failure can occur for the 0-truncated objects of a model of 𝕋 + Trunc₀.

## What has been tried

- For Q1, candidate countermodels where *cell-iteration* (needed by R-A for every object C) is available but *map-iteration* (recursion into an arbitrary A) is not: internal ω-categories in a base with restricted function classes (e.g. elementary or primitive recursive maps). The difficulty is that R-A for internal categories already seems to require a parametrised natural numbers object in the base, which gives recursion. Not resolved.
- For Q2, the term model: with a variable `c`, two variables `u, u' : c → ⟦L⟧` and parallel `α, β : u → u'`, no rule of 𝕋 obviously produces a cell α → β, since `coh` needs α and β in one pasting context and no rule introduces cells between variables whose target is a constant. Turning this into a proof needs a normal-form theorem for 𝕋, which is not available.
- For Q3, nothing beyond the observation above.

## Why it matters

A type theory for weak ω-categories that adds only universal properties (limits, colimits, free objects) is very economical. These questions decide whether it already contains basic arithmetic (recursion on ℕ), whether ℕ is provably a set, and whether quotient sets behave correctly, or whether each needs its own rule. A "no" justifies adding the rule; a "yes" removes a rule from the design.

## What would count as a solution

For each question: a model of the stated rules in which the conclusion fails (or a syntactic argument), or a derivation, or references.

## Literature status (2026-11-18)

Searched: "natural numbers object not derivable from free category on a graph finite limits colimits recursion"; "effective quotients exact category not implied by regular category with coequalizers counterexample". Found: Rijke, *An elementary approach to truncations* (arXiv 1812.10527), constructing truncations in homotopy type theory from non-recursive higher inductive types (it works in a univalent setting, so does not bear on Q3 without a universe); the nLab pages on natural numbers objects and on exact categories (standard 1-categorical facts quoted above). No result on derivability of recursion, discreteness or effectiveness in a CaTT-style theory with limits was found.
