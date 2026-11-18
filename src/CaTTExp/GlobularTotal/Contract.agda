------------------------------------------------------------------------
-- F2c, lemma (1c): pasting contexts are contractible strictly.
--
-- In Θ = ctxOf τ, a diagram of Θ is determined by its labels (Uniq),
-- and the labels of Θ's own tree and of its boundaries are all of Θ,
-- ∂⁻Θ and ∂⁺Θ (LabRange, LabBd). So:
--
--   full-nf : labels a = varsCtx Θ  ⟹  a ≡ idTree τ
--   src-nf  : labels a = ∂⁻ Θ       ⟹  a ≡ bd false (dimCtx Θ ∸ 1) (idTree τ)
--   tgt-nf  : labels a = ∂⁺ Θ       ⟹  a ≡ bd true  (dimCtx Θ ∸ 1) (idTree τ)
--
-- for every diagram a of Θ. With (1′) for u in Θ this gives the normal
-- forms of the endpoints of a coherence from its side condition.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Contract where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; idTree)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex; uniq)
open import CaTTExp.GlobularTotal.PsOrd using (ps-ord)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.LabBd using (lab-∂⁻; lab-∂⁺)
open import CaTTExp.GlobularTotal.ExBd using (ex-bd)

private
  ∨-cong : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → (a ∨ b) ≡ (a' ∨ b')
  ∨-cong refl refl = refl

  -- y ∈ [n-1, …, 0] iff y < n
  mem-down : ∀ y n → memL y (downFrom n) ≡ (y <ℕ n)
  mem-down y zero    = lem y
    where
    lem : ∀ y → false ≡ (y <ℕ 0)
    lem zero    = refl
    lem (suc y) = refl
  mem-down y (suc n) = trans (cong ((y ==ℕ n) ∨_) (mem-down y n)) (step y n)
    where
    step : ∀ y n → ((y ==ℕ n) ∨ (y <ℕ n)) ≡ (y <ℕ suc n)
    step zero    zero    = refl
    step zero    (suc n) = refl
    step (suc y) zero    = lem y
      where
      lem : ∀ y → ((suc y ==ℕ 0) ∨ (suc y <ℕ 0)) ≡ (y <ℕ 0)
      lem zero    = refl
      lem (suc y) = refl
    step (suc y) (suc n) = step y n

  ctx-ps : ∀ τ → ctxOf τ ⊢ps
  ctx-ps τ = snd (psOf τ)

module _ (τ : Tree) (a : LT) (xa : Ex (ctxOf τ) 0 nothing a) where

  private
    Θ = ctxOf τ
    Tr = idTree τ
    k₀ = dimCtx Θ ∸ 1
    ord = ps-ord (ctx-ps τ)

  full-nf : (∀ y → mem y a ≡ memL y (varsCtx Θ)) → a ≡ Tr
  full-nf h = uniq Θ ord 0 nothing a Tr xa (lab-ex τ)
                (λ y → trans (h y) (trans (mem-down y (len Θ)) (sym (lab-all τ y))))

  src-nf : (∀ y → mem y a ≡ memL y (∂⁻ Θ)) → a ≡ bd false k₀ Tr
  src-nf h = uniq Θ ord 0 nothing a (bd false k₀ Tr) xa (ex-bd Θ false k₀ 0 nothing Tr (lab-ex τ))
               (λ y → trans (h y) (sym (lab-∂⁻ τ y)))

  tgt-nf : (∀ y → mem y a ≡ memL y (∂⁺ Θ)) → a ≡ bd true k₀ Tr
  tgt-nf h = uniq Θ ord 0 nothing a (bd true k₀ Tr) xa (ex-bd Θ true k₀ 0 nothing Tr (lab-ex τ))
               (λ y → trans (h y) (sym (lab-∂⁺ τ y)))
