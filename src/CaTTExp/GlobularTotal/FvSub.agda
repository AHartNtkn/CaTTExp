------------------------------------------------------------------------
-- F2c toward (1′), L6 (first half): free variables under substitution.
--
--   fv-tm : memL z (fvTm (t [ σ ]tm)) ≡ anyL (λ y → memL z (fvTm (lookupₛ σ y))) (fvTm t)
--
-- i.e. the support of t[σ] is the union, over the variables y of t,
-- of the supports of σ's images of y. This is the syntactic side of
-- "labels of nf t = support of t" in the coh case of (1′), where
-- Labels.flat⊆/flat⊇ give the same union on the tree side.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FvSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularTotal.Uniq using (memL)
open import CaTTExp.GlobularTotal.Labels using (anyL)

private
  ∨-false : ∀ a → a ≡ (a ∨ false)
  ∨-false true  = refl
  ∨-false false = refl

  ∨-assoc : ∀ a b c → ((a ∨ b) ∨ c) ≡ (a ∨ (b ∨ c))
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

  ∨-cong : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → (a ∨ b) ≡ (a' ∨ b')
  ∨-cong refl refl = refl

memL-++ : ∀ z xs ys → memL z (xs ++ ys) ≡ (memL z xs ∨ memL z ys)
memL-++ z []       ys = refl
memL-++ z (x ∷ xs) ys =
  trans (cong ((z ==ℕ x) ∨_) (memL-++ z xs ys)) (sym (∨-assoc (z ==ℕ x) (memL z xs) (memL z ys)))

anyL-++ : ∀ f xs ys → anyL f (xs ++ ys) ≡ (anyL f xs ∨ anyL f ys)
anyL-++ f []       ys = refl
anyL-++ f (x ∷ xs) ys =
  trans (cong (f x ∨_) (anyL-++ f xs ys)) (sym (∨-assoc (f x) (anyL f xs) (anyL f ys)))

module _ (z : Nat) (σ : Sub) where
  -- y ↦ "z occurs in σ's image of y"
  img : Nat → Bool
  img y = memL z (fvTm (lookupₛ σ y))

  mutual
    fv-tm : ∀ t → memL z (fvTm (t [ σ ]tm)) ≡ anyL img (fvTm t)
    fv-tm (var i)     = ∨-false (img i)
    fv-tm (coh Γ A τ) = fv-sub τ
    fv-tm (cst ())

    fv-sub : ∀ τ → memL z (fvSub (τ ∘ σ)) ≡ anyL img (fvSub τ)
    fv-sub ⟨⟩       = refl
    fv-sub (τ ,ₛ t) =
      trans (memL-++ z (fvSub (τ ∘ σ)) (fvTm (t [ σ ]tm)))
      (trans (∨-cong (fv-sub τ) (fv-tm t))
             (sym (anyL-++ img (fvSub τ) (fvTm t))))

  fv-ty : ∀ A → memL z (fvTy (A [ σ ]ty)) ≡ anyL img (fvTy A)
  fv-ty ⋆           = refl
  fv-ty (arr A t u) =
    trans (memL-++ z (fvTy (A [ σ ]ty)) (fvTm (t [ σ ]tm) ++ fvTm (u [ σ ]tm)))
    (trans (∨-cong (fv-ty A)
             (trans (memL-++ z (fvTm (t [ σ ]tm)) (fvTm (u [ σ ]tm)))
                    (∨-cong (fv-tm t) (fv-tm u))))
    (trans (cong (anyL img (fvTy A) ∨_) (sym (anyL-++ img (fvTm t) (fvTm u))))
           (sym (anyL-++ img (fvTy A) (fvTm t ++ fvTm u)))))
