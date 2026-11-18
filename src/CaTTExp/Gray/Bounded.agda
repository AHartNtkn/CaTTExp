------------------------------------------------------------------------
-- Bounded machine checks of the rule-level half of conservativity.
--
-- For a single hom Γ = ΣΘ, two-tier L's side condition is plain
-- CaTT's provided (i) the closed supports of T, ∂⁻T, ∂⁺T are exactly
-- the non-object variables of Γ, ∂⁻Γ, ∂⁺Γ (Finster–Mimram's
-- boundaries), and (ii) supp(t : A) = Var(t : A) for derivable terms
-- (the term-level half, not checked here). This file checks (i) for
-- every pasting diagram Θ with at most 6 edges (197 contexts), by
-- evaluation.
------------------------------------------------------------------------
module CaTTExp.Gray.Bounded where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure

-- All forests whose trees have e edges in total (a tree with k inner
-- edges contributes k + 1), with fuel.
forestsF : Nat → Nat → List (List Tree)
forestsF _          zero    = [] ∷ []
forestsF zero       (suc _) = []
forestsF (suc fuel) (suc e) =
  concatMap (λ k → concatMap (λ t → map (t ∷_) (forestsF fuel (e ∸ k)))
                              (map node (forestsF fuel k)))
            (filter (λ k → k <ℕ suc e) (upto e))

-- Pasting diagrams Θ with exactly e edges.
treesE : Nat → List Tree
treesE e = map node (forestsF e e)

-- The check for one Θ, on Γ = ΣΘ.
nonObj : Ctx → List Nat → TSet
nonObj Γ vs = map (_∷ []) (filter (λ i → not (elem i (objs Γ))) vs)

check : Tree → Bool
check θ =
  let Γ  = ctxOf (node (θ ∷ []))
      hs = homs Γ
  in ≈T (down Γ (bdryT false hs)) (nonObj Γ (∂⁻ Γ))
   ∧ ≈T (down Γ (bdryT true hs))  (nonObj Γ (∂⁺ Γ))
   ∧ ≈T (down Γ (fullT hs))       (nonObj Γ (varsCtx Γ))

lengthL : ∀ {a} {A : Set a} → List A → Nat
lengthL []       = 0
lengthL (_ ∷ xs) = suc (lengthL xs)

-- 1 + 2 + 5 + 14 + 42 + 132 = 196 diagrams with 1 to 6 edges.
diagrams : List Tree
diagrams = concatMap treesE (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [])

_ : lengthL diagrams ≡ 196
_ = refl

single-hom-boundaries : all check diagrams ≡ true
single-hom-boundaries = refl

-- The check is not vacuous: ∂⁻ and ∂⁺ are distinguished on every one
-- of these diagrams.
distinguishes : Tree → Bool
distinguishes θ =
  let Γ = ctxOf (node (θ ∷ [])) in
  not (≈T (down Γ (bdryT false (homs Γ))) (nonObj Γ (∂⁺ Γ)))

_ : all distinguishes diagrams ≡ true
_ = refl

-- For every pasting context Γ with 1 to 5 edges (any number of homs),
-- the closed support of the total cell is all of K(Γ): the coherence
-- case asks for full support in the note's sense.
allTuples : List Hom → TSet
allTuples []       = [] ∷ []
allTuples (h ∷ hs) = prod1 (map lvl (hcs h)) (allTuples hs)

fullIsAll : Tree → Bool
fullIsAll γ = let Γ = ctxOf γ in ≈T (down Γ (fullT (homs Γ))) (allTuples (homs Γ))

_ : all fullIsAll (concatMap treesE (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) ≡ true
_ = refl
