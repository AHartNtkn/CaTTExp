------------------------------------------------------------------------
-- The binder kernel's existing mark judgments are instances of the one
-- judgment of CaTTExp.Binder.FreeModelMark (notes/unified-engine.md
-- §3.5).
--
--   varMark   (rule (MARK) alone)            = markTm with no clauses
--   headMark  (MARK) + (HEAD-inv), used by    = markTm with headHas b y m
--             UniMark for J2's UNI-inv            := (m is inv) ∧ inv? b y
--
-- Both equalities are pointwise, for every context, mark and term, so
-- every theorem proved for markTm (renaming, substitution, upward
-- closure) holds for them, and a later clause (for coherences or for
-- further head marks) extends them without a new metatheory.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.FreeModelMarkInstances
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊

-- Entailment by equality.
_≡M_ : Mark → Mark → Bool
n ≡M m = m ==M n

import CaTTExp.Binder.FreeModelMark as FMM

private
  module FM = FMM 𝕊 side _≡M_ (λ _ _ → false) (λ _ _ _ → false) (λ _ _ _ _ → false)

  ∈M-any : ∀ m ns → (m ∈M ns) ≡ FM.anyB (λ n → n ≡M m) ns
  ∈M-any m []       = refl
  ∈M-any m (n ∷ ns) = cong ((m ==M n) ∨_) (∈M-any m ns)

module VarInstance where
  open import CaTTExp.Binder.FreeModelMark 𝕊 side _≡M_
    (λ _ _ → false) (λ _ _ _ → false) (λ _ _ _ _ → false)

  varMark-is-markTm : ∀ Γ m t → varMark Γ m t ≡ markTm Γ m t
  varMark-is-markTm Γ m (var i)       = ∈M-any m (marksAt Γ i)
  varMark-is-markTm Γ m (bvar _ _)    = refl
  varMark-is-markTm Γ m (coh _ _ _)   = refl
  varMark-is-markTm Γ m (cst _)       = refl
  varMark-is-markTm Γ m (bnd _ _ _ _) = refl

module HeadInstance (inv? : B → Nat → Bool) where
  open import CaTTExp.Binder.HeadMark 𝕊 side inv? using (headMark; isInv)

  headHas : B → Nat → Mark → Bool
  headHas b y m = isInv m ∧ inv? b y

  open import CaTTExp.Binder.FreeModelMark 𝕊 side _≡M_
    (λ _ _ → false) headHas (λ _ _ _ _ → false)

  private
    ∨false : ∀ a → (a ∨ false) ≡ a
    ∨false true  = refl
    ∨false false = refl

  headMark-is-markTm : ∀ Γ m t → headMark Γ m t ≡ markTm Γ m t
  headMark-is-markTm Γ m (var i)       = trans (∨false (m ∈M marksAt Γ i)) (∈M-any m (marksAt Γ i))
  headMark-is-markTm Γ m (bvar _ _)    = refl
  headMark-is-markTm Γ m (coh _ _ _)   = refl
  headMark-is-markTm Γ m (cst _)       = refl
  headMark-is-markTm Γ m (bnd b y _ _) = refl
