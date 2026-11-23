# Final coalgebras of dependent polynomials without disjoint coproducts

## Setting

Let 𝒱 be a category, or more generally an (∞,1)-category, with:

**(a) Finite limits and finite colimits.** No compatibility between them is assumed. In particular, finite coproducts need not be disjoint, and colimits need not be stable under pullback.

**(b) A biclosed monoidal structure (⊗, I) whose unit is the terminal object 1.** There are internal homs A\C and C/A with
  Hom(A ⊗ B, C) ≃ Hom(B, A\C) ≃ Hom(A, C/B),
natural in all variables. The cartesian closed case (⊗ = ×) is the main example. The Gray tensor on (∞,ω)-categories is the motivating non-cartesian example.

**(c) Initial algebras of positive signatures.** A *positive signature* in one sort X consists of:
- a finite list of operations o_i : S_i(X) → T_i(X), where
  - each *source* S_i is built from X and fixed objects by finite limits, finite colimits, and ⊗ or × with fixed objects;
  - each *target* T_i is X, 1, an internal hom K\X or X/K with K fixed, or a finite limit of these (so T_i preserves limits);
- finitely many equations between parallel composites of the operations.

An algebra is an object X with maps o_i satisfying the equations, and a morphism of algebras is a map commuting with the operations. In the (∞,1) case, morphisms are coherent (strong) homomorphisms, and the equations are specified homotopies. Axiom (c): every positive signature has an initial algebra. Examples are the natural numbers μX.(1 + X) and lists μX.(1 + X ⊗ E).

**Dialgebras.** For a map p : E → A, a *p-dialgebra* is a triple (C, h : C → A, t : C ×_A E → C), where C ×_A E is the pullback of p along h. A morphism (C, h, t) → (C′, h′, t′) is a map g : C → C′ with h′g = h and t′ ∘ (g ×_A E) = g ∘ t, coherently in the (∞,1) case.

When pullback along p has a right adjoint Π_p, a p-dialgebra is the same as a coalgebra of the polynomial endofunctor P_p(X) = Σ_A Π_p(p*X) on 𝒱/A, composed to 𝒱. A terminal p-dialgebra is then the M-type (object of non-wellfounded trees) of p. The dialgebra formulation needs only pullbacks, so it makes sense in every 𝒱 of the setting.

## What is known

1. **Constant arities hold in every 𝒱 satisfying (a)–(c).** For objects A and E, let L := μX.(1 + X ⊗ E) be the initial algebra of (n : 1 → X, c : X ⊗ E → X). Coalgebras (C, h : C → A, t : E ⊗ C → C) then have a terminal object, namely L\A. The proof transposes a coalgebra morphism g : C → L\A to a map L ⊗ C → A, and then to an algebra morphism L → A/C for the algebra (A/C, h̄, curry(ev ∘ (1 ⊗ t))), which is unique by initiality. In the cartesian case this is the terminal p-dialgebra for the projection p : A × E → A. Streams (E = 1) are the special case νX. A × X = ℕ\A.
2. **The literature constructions all use extensivity.**
   - Abbott–Altenkirch–Ghani, *Containers: constructing strictly positive types* (TCS 342, 2005), Prop. 4.1: M-types exist in every Martin-Löf category (an LCCC with disjoint coproducts and W-types). The proof uses disjointness of coproducts.
   - van den Berg–De Marchi, *Non-well-founded trees in categories* (APAL 146, 2007; arXiv:math/0409158): M-types exist in every locally cartesian closed pretopos with W-types (Cor. 2.5). Prop. 2.9 uses only an NNO when A has decidable equality, but still works inside a pretopos.
   - Ahrens–Capriotti–Spadotti, *Non-wellfounded trees in homotopy type theory* (TLCA 2015; arXiv:1504.02949): the construction is the terminal chain Pⁿ(1), defined as a family ℕ → U by recursion into a universe. It uses funext; univalence is used only to show that finality is a proposition.
3. **Why disjointness enters.** Every construction known to us does one of two things:
   - it splits E × C into C ×_A E and its complement (to extend t to all addresses), which needs decidable equality on A and disjoint, universal coproducts; or
   - it computes the fibres of a family over ℕ defined by initiality (the terminal chain), which needs pullback-stability and disjointness of the coproduct 1 + ℕ.
4. **Case analysis on coproduct inputs is free.** Because ⊗ is biclosed, X ⊗ – and – ⊗ X preserve finite coproducts. For a polynomial with finitely many constructors, P(X) = ∐_{j∈J} A_j × (E_j\X), a coalgebra c : C → P(C) has a candidate final object: the equaliser, inside L\((∐_j A_j) + 1), of the consistent label functions on addresses L = μX.(1 + X ⊗ ∐_j E_j). Existence and uniqueness of maps into it follow by transposition and initiality, as in item 1. The one step that seems to need more is the structure map M → P(M). It requires splitting M along its root-label map M → ∐_j A_j + 1, that is, **universality** of finite coproducts (stability under pullback). Disjointness does not appear to be needed for that step.
5. **Locally presentable models are no counterexample.** If 𝒱 is locally presentable, every accessible endofunctor has a terminal coalgebra: the coalgebra category is accessible, and its forgetful functor creates colimits. So in every locally presentable 𝒱 satisfying (a)–(c), the coalgebra-form M-types of finitary polynomials exist. For dialgebras, the same argument works when pullback along p preserves colimits.
6. **Universality is not forced.** Let T : Set → {0 < 1} send X to "X is inhabited", and let Gl(T) be its Artin gluing: sets X with a flag y, where y = 1 only if X is inhabited, and maps that do not lower the flag. Gl(T) is locally presentable and cartesian closed, with coproducts (X ⊔ X′, y ∨ y′). For z : (1, 1) → (1, 0) + (1, 1) hitting the first summand, the pullbacks of the two injections are (1, 0) and (∅, 0), whose sum (1, 0) is not (1, 1). So Gl(T) satisfies (a)–(c) with ⊗ = ×, its finite coproducts are disjoint but not universal, and it still has all coalgebra-form M-types by item 5.
7. **Conatural numbers without universality (in-house; machine-checked in Agda for a 1-category with strict equations).** In any cartesian closed category with finite limits, finite coproducts and an NNO, the decreasing sequences M ↪ 2^ℕ are the terminal coalgebra of X ↦ 1 + X. The structure map is (! + 1) ∘ δ ∘ ⟨ev₀, – ∘ s⟩, where δ : 2 × M ≅ M + M is distributivity. Uniqueness follows by post-composing with 1 + M → 2 and with [0, 1] : 1 + M → M, then using initiality of ℕ. No universality or disjointness is used. The same idea, where an inconsistent branch "stays at the current node", appears to handle finitely many constructors over a cartesian base. It uses the diagonal, so it does not transfer to a non-cartesian ⊗ in general. It does transfer when ⊗ agrees with × on maps into the label objects (for example when maps A ⊗ W → B and A × W → B correspond for every set B), because every target of the construction is such a label object.
8. **Internal arities in coalgebra form (in-house, sketch).** For P(X) = List X = μY.(1 + X × Y), the coalgebra form of p : Fin → ℕ, the same pattern gives the terminal coalgebra over a cartesian base. Its carrier is the label functions List ℕ → ℕ satisfying equations of maps into 2. The corecursion never needs 1 + C as a target. What remains is the dialgebra form. Extending t : C ×_ℕ Fin → C to a total step needs the subobject {i < h x} ↪ C × ℕ to be complemented, that is, universality of 1 + 1 along lt : C × ℕ → 2.

## Questions

**Question 1 (main).** Determine the class of maps p : E → A for which **every** 𝒱 satisfying (a)–(c) has a terminal p-dialgebra. Either:
- give a construction of the terminal p-dialgebra from (a)–(c), uniform in 𝒱 (as in Known 1), for a class of p that includes at least all maps between finite coproducts of 1 and, if possible, all maps between objects that are initial algebras of positive signatures (such as ℕ, lists, finitary W-types); or
- give a 𝒱 satisfying (a)–(c) and a map p between finite coproducts of 1 (or between such initial algebras) with no terminal p-dialgebra, and identify which extra axiom restores existence. Candidates for that axiom are disjointness of finite coproducts, universality of finite coproducts, and decidable equality of A.

**Question 1′ (internal shapes and non-cartesian tensors).** Known 7 leaves two cases open. Treat them together:
- (i) p : E → A with A an arbitrary object, not a finite coproduct of 1. For example A = ℕ with E → ℕ the family of finite ordinals. By Known 8 the coalgebra form is available, so the question is the dialgebra form: is there a terminal p-dialgebra without universality, or a 𝒱 in which coalgebras of List exist and are terminal but p-dialgebras have no terminal object?
- (ii) ⊗ not cartesian, where the diagonal used by Known 7 is unavailable.

In either case, give a construction from (a)–(c), or a 𝒱 satisfying (a)–(c), necessarily not locally presentable by Known 5, without the terminal coalgebra.

**Question 2 (directed case).** Take 𝒱 = Cat_(∞,ω) with the Gray tensor, or 𝒱 = Cat_(∞,1) with ×. For which maps p : E → A does the category of p-dialgebras have a terminal object?
- Is exponentiability of p (for example, p a cocartesian or cartesian fibration) sufficient? Is it necessary?
- In particular, what happens for the inclusion {0 < 2} → [2]?

If Question 1 is answered by a uniform construction, the most useful form also says whether the construction is natural in p (stable under pullback of p along maps A′ → A).

Fallback, only if the general questions resist: the case A = 1 + 1, E = 1 → A the first injection (the polynomial X ↦ 1 + X, whose final coalgebra is the conatural numbers), in a 𝒱 satisfying (a)–(c) in which 1 + 1 is not disjoint.

## Why it matters

The axioms (a)–(c) give inductive types without any universe or descent principle. Constant-arity coinductive types follow from them. The question is whether non-wellfounded trees with label-dependent branching, already including the conatural numbers, also follow, or whether some form of extensivity (descent for coproducts) is the price of dependent coinduction.

## What would count as a solution

A proof (a uniform construction) for an explicit class of p, a countermodel for a map between finite discrete objects, or a reference to either.

## Literature search (2026-11-23)

The searches covered M-types from W-types (Abbott–Altenkirch–Ghani; van den Berg–De Marchi; Ahrens–Capriotti–Spadotti) and final coalgebras of accessible functors on locally presentable categories (Adámek, Worrell). Every positive construction found assumes a locally cartesian closed category with disjoint coproducts, or a universe. No result was found on dependent M-types in non-extensive settings, and no counterexample was found. van den Berg–De Marchi note that it is open whether there are interesting coinductive pretoposes that are not predicative toposes.
