**Status: unsent** (written 2026-11-18; follows `answered/non-derivability-2026-11-18.md`, Question 2).

# Is ℕ provably a set in a coherence-style theory of ω-categories with limits and exponentials by shapes?

*A self-contained problem. No knowledge of the project that posed it is assumed. It is the one question left open by an earlier answer; §"What is known" says exactly what that answer proved.*

## Background

**The base theory.** Fix a dependent type theory 𝕋 for weak ω-categories in the style of CaTT (Finster–Mimram, LICS 2017): contexts of typed variables (objects, and cells between cells), and one term former `coh` producing cells between parallel composites over pasting contexts. Add to it, as rules stated by universal properties witnessed by cells (never by definitional equalities, and with no universe):
- **finite limits** in the ambient (∞,ω)-category of ω-categories: a terminal object ⊤, pullbacks, and *cotensors* `[⟦D⟧, C]` by finite shapes D;
- **finite colimits**: pushouts, coequalisers, coproducts, and lax colimits of finite diagrams;
- **R-A (free objects on finite computads):** for each finite context Γ, an object ⟦Γ⟧ such that maps `⟦Γ⟧ → C` correspond to substitutions Γ → C (up to cells at every level). In particular, for the loop `L = (x : ⋆, s : x → x)`, maps `⟦L⟧ → C` correspond to an object of C with an endo-1-cell.

Write `Hom_C(a, b)` for the pullback of `[⟦D¹⟧, C] → C × C` along `(a, b)`. Put `N := Hom_{⟦L⟧}(x, x)`, with `zero := 1_x` and `succ := – ; s`. Semantically (in the (∞,ω)-category of (∞,ω)-categories), ⟦L⟧ is the free category on one loop and N is the discrete set ℕ (the free weak ω-category on a graph is the free category on it).

**Truncation levels.** An object C is *n-truncated* (C trunc n) when parallel cells into C of level ≥ n + 1 are connected and cells of level n + 1 are invertible. Sets are the 0-truncated objects. A *truncation rule* `Trunc_n` gives for each X a reflection `|–| : X → ‖X‖_n` onto n-truncated objects (existence of extensions, and of cells between extensions agreeing on X).

**Derivability.** A rule is *derivable* if every instance of its conclusion is a term of 𝕋 (with the stated additional rules). Non-derivability can be shown by a model of the rules in which the conclusion fails, or by a normal-form argument on the syntax.

**The strengthened rules (the reading intended here).**
- **(E) Cotensors are cartesian exponentials by the realized shapes:** maps `A → [⟦D⟧, C]` correspond to maps `A × ⟦D⟧ → C`, for every object A, naturally and at every level.
- **Parameterised R-A:** for every object A, maps `A × ⟦Γ⟧ → C` correspond to substitutions of Γ into the hom ω-category of maps A → C.
- **Universal disjoint coproducts of sets:** Bool := ⊤ ⊔ ⊤ is a set, coproduct injections of sets are disjoint monos, and coproducts of sets are stable under pullback along any map.

## Statement

In 𝕋 + (E) + parameterised R-A + universal disjoint coproducts of sets (optionally + Trunc₀), is `N trunc 0` derivable? More generally, is "⟦Γ⟧ is 1-truncated for every finite graph Γ" derivable?

The expected answer is **no**. A "no" should come with a model in which (E), parameterised R-A and universal coproducts hold and N is not a set; a "yes" with a derivation.

## What is known

- **Semantically** the conclusion holds: in (∞,ω)-categories the free category on a graph is a 1-category and N is the discrete set ℕ.
- **Without (E) the answer is no (proved).** Let 𝒦 = (F ↓ id) for F : Spaces → D(ℤ), F(X) = H₁(X; ℤ)[1], regarded as locally groupoidal. Objects are (X, A, α : F(X) → A). It has all limits and colimits, enriched cotensors `Map(T, C^D) ≃ Map(|D|, Map(T, C))`, and R-A with ⟦Γ⟧ = (|Γ|, F|Γ|, id). There N ≃ (ℤ, ℤ[0], 0), and for E = (∅, ℤ[−1], 0), Map(E, N) ≃ K(ℤ,1), so N is not a set; Map(E, ⟦L⟧) ≃ K(ℤ,2). Sets are the (S, 0, 0) with S discrete; Bool is a set with disjoint injections. But (E) fails: with E₂ = (∅, ℤ/2[0], 0) and the two-point shape T(2) = (2, 0, 0), E₂ × T(2) ≃ E₂, so Map(E₂ × T(2), E₂) has 2 points while Sub(2, Map(E₂, E₂)) has 4.
- **Recursion and effectiveness are independent even with (E) (proved).** Recursion on N fails in categories with an auxiliary equivalence relation on objects (N is discrete ℕ with the total relation, so every map N → Bool is constant). Effectiveness of quotients fails in Pos with discrete homs. Both models satisfy (E). In both, N is a set, so neither bears on this question.
- **Where the obvious derivation stops.** A Hedberg-style proof (decidable equality N × N → Bool, then "eq(m,n) = true gives an invertible m → n") needs induction on m for all n at once, i.e. exponentials over N or induction with a varying parameter. The theory has exponentials only by shapes ⟦D⟧, and recursion on N is itself not derivable.
- **Observation.** In the comma model, R-A cannot detect the failure: maps from realized shapes into ⟦L⟧ form 1-types; the failure is seen only by the "phantom" objects E with empty underlying space. (E) and universal coproducts force products with shapes to behave like copowers, which kills that particular model.

## Candidate approaches

- Modify the comma construction so that products with realized shapes are copowers: e.g. glue along a functor F that is product-preserving in a suitable sense, or replace D(ℤ) by a cartesian closed target with a non-truncated "phantom" part.
- A syntactic normal-form argument: in context `c : ⋆`, `u, u' : c → ⟦L⟧`, `α, β : u → u'`, show no term `α → β` exists. Under (E), maps c × ⟦D¹⟧ → ⟦L⟧ are available, which is exactly what the earlier normal-form attempt did not account for.

## What would count as a solution

A model of the stated rules in which N (or some ⟦Γ⟧ for a finite graph Γ) is not appropriately truncated; or a derivation; or references.
