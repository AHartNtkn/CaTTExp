------------------------------------------------------------------------
-- The degenerate obstruction: no source-joining completion is natural
-- under maps that send a seed to an identity but keep an inner arrow
-- into its target.
--
-- If F α = 1 and F R is a nonempty inner path, the image of a
-- generator j with j ; R = α would be an H with H ; F R = 1. In the
-- cospan completion (and so in r7's, which it contains) there is none
-- (no-unit-division): equations keep seed lists, so H is inner, and
-- an inner word is normal.
--
-- So requirement 5 for substitutions that degenerate a seed needs the
-- substitution to degenerate the inner arrows into that seed's target
-- too; whether CaTT's degeneracies do is the remaining check.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
import CaTTExp.Join.Cospan as Cospan

module CaTTExp.Join.Degenerate {V : Set} (E P : V → V → Set) where

open Cospan E P

private
  innW-nf : ∀ {a b} (p : IPath a b) → Normal (innW p)
  innW-nf (e ∷ p) _ (skip _ s) = innW-nf p _ s

  seeds-++ : ∀ {a b c} (w : Word a b) (r : Word b c) →
             seeds (w ++ᵖ r) ≡ seeds w ++ seeds r
  seeds-++ []             r = refl
  seeds-++ (inn e ∷ w)    r = seeds-++ w r
  seeds-++ (jn α I R ∷ w) r = cong (seed α ∷_) (seeds-++ w r)

  all-inner : ∀ {a b} (w : Word a b) → seeds w ≡ [] → Σ (IPath a b) λ p → w ≡ innW p
  all-inner []             _  = [] , refl
  all-inner (inn e ∷ w)    eq with all-inner w eq
  ... | p , refl = e ∷ p , refl
  all-inner (jn α I R ∷ w) ()

  -- seeds (H ++ innW R) ≡ seeds H ++ [].
  seeds-H : ∀ {a u} (H : Word a u) (R : IPath u a) → seeds (H ++ᵖ innW R) ≡ [] →
            seeds H ≡ []
  seeds-H H R eq with trans (sym (seeds-++ H (innW R))) eq
  ... | eq′ = lemma (seeds H) _ eq′
    where
    lemma : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ []
    lemma []       ys _  = refl
    lemma (x ∷ xs) ys ()

no-unit-division : ∀ {a u v} (r : E u v) (R : IPath v a) →
                   ¬ (Σ (Word a u) λ H → H ++ᵖ innW (r ∷ R) ~ [])
no-unit-division {a} {u} r R (H , eqn) with all-inner H (seeds-H H (r ∷ R) (seeds-~ eqn))
... | p , refl with nf-unique (subst Normal (innW-++ p (r ∷ R)) (innW-nf (p ++ᵖ (r ∷ R))))
                             (λ _ ()) eqn
... | eq = absurd p eq
  where
  absurd : (p : IPath a u) → innW p ++ᵖ innW (r ∷ R) ≡ [] → ⊥
  absurd []      ()
  absurd (e ∷ p) ()
