------------------------------------------------------------------------
-- Examples for the total 1-dimensional filler (CaTTExp.GraphFillerTotal).
--
-- Here the 2-cells come from the theorem `total`, applied to typing
-- derivations of the two 1-cells and a proof that their paths agree,
-- not from running a checker on the output. The comparisons with
-- CaTTExp.GraphFiller check that the structural filler produces the
-- same term as the fuel-based tactic on its examples.
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotalExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal
import CaTTExp.GraphFiller as GF
open import CaTTExp.GraphFillerExamples
  using (comp; L; x; s; _⨾_; [ss]s; s[ss]; hom; id; long₁; long₂; G; fg-f; f-gf)

-- A typing derivation found by the certified checker, at its own type.
typed : (Γ : Ctx) (t : Tm) → {ok : T (is-just (infer Γ t))} →
        Γ ⊢tm t ∶ fst (from-just (infer Γ t) {ok})
typed Γ t {ok} = snd (from-just (infer Γ t) {ok})

-- Associativity on the loop, from the theorem.
assoc₃ : L ⊢tm fill₁ L [ss]s s[ss] hom ∶ arr hom [ss]s s[ss]
assoc₃ = total (typed L [ss]s) (typed L s[ss]) refl

-- It is the term the fuel-based tactic finds.
_ : fill₁ L [ss]s s[ss] hom ≡ fst (from-just (GF.fill L [ss]s s[ss] hom))
_ = refl

unit-swap : L ⊢tm fill₁ L (s ⨾ id x) (id x ⨾ s) hom ∶ arr hom (s ⨾ id x) (id x ⨾ s)
unit-swap = total (typed L (s ⨾ id x)) (typed L (id x ⨾ s)) refl

zero-zero : L ⊢tm fill₁ L (id x ⨾ id x) (id x) hom ∶ arr hom (id x ⨾ id x) (id x)
zero-zero = total (typed L (id x ⨾ id x)) (typed L (id x)) refl

long : L ⊢tm fill₁ L long₁ long₂ hom ∶ arr hom long₁ long₂
long = total (typed L long₁) (typed L long₂) refl

_ : fill₁ L long₁ long₂ hom ≡ fst (from-just (GF.fill L long₁ long₂ hom))
_ = refl

graph-assoc : G ⊢tm fill₁ G fg-f f-gf (arr ⋆ (var 0) (var 1)) ∶ arr (arr ⋆ (var 0) (var 1)) fg-f f-gf
graph-assoc = total (typed G fg-f) (typed G f-gf) refl

-- A context that is not a graph: a 2-cell α : f ⇒ g between parallel
-- edges. The theorem is about 1-cells, so it applies all the same.
-- Levels: x0 y1 f2 g3 α4.
H : Ctx
H = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1) ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)

i⨾f : Tm
i⨾f = comp (var 0) (var 0) (id (var 0)) (var 1) (var 2)

idf-f : H ⊢tm fill₁ H i⨾f (var 2) (arr ⋆ (var 0) (var 1)) ∶ arr (arr ⋆ (var 0) (var 1)) i⨾f (var 2)
idf-f = total (typed H i⨾f) (typed H (var 2)) refl
