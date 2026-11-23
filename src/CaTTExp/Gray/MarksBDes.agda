------------------------------------------------------------------------
-- Two-tier L with the destructors of DES (CaTTExp.Binder.Des), over
-- any base signature 𝕊₀: the Gray mark judgment with (DES)/(DES-inv)
-- (all four formers carry minv) satisfies the binder kernel's MarkRen,
-- MarkSub and MarkVar, so the kernel's substitution theorem applies.
--
-- The interface facts are proved here: formerMarks is constant, so
-- FormerStable; the cell argument (entry 2n of Dⁿ, an n-cell) is no
-- higher than the result (an n-cell for f⁻ˡ, f⁻ʳ, an (n+1)-cell for
-- λ_f, ρ_f), so CellDim. Remaining parameters: constants are closed
-- (as for Binder.Subst), and the mark-free kernel has presupposition
-- (tm-ty), which the kernel is adding.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.Des
import CaTTExp.Binder.DesLaws
import CaTTExp.Binder.Laws
import CaTTExp.Binder.Rename
import CaTTExp.Binder.Subst
import CaTTExp.Gray.MarksB
import CaTTExp.Gray.MarksBSubst
import CaTTExp.Gray.MarksBKernel
import CaTTExp.Gray.DimB
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s)

module CaTTExp.Gray.MarksBDes (𝕊₀ : Old.Signature) where

private
  bi = desBinders (Old.Signature.K 𝕊₀)

𝕊 : Signature
𝕊 = extend 𝕊₀ bi

open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open CaTTExp.Binder.Laws 𝕊 using (Closed)

desMarks : DesF → Nat → Ctx → List Mark
desMarks _ _ _ = minv ∷ []

open CaTTExp.Gray.MarksB 𝕊₀ bi cellArgD desMarks public using (mark; judge; judgeT; markVar)
module Kernel = CaTTExp.Gray.MarksB.Kernel 𝕊₀ bi cellArgD desMarks
open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArgD using (graySideD)
private
  module MS = CaTTExp.Gray.MarksBSubst 𝕊₀ bi cellArgD desMarks
  module MK = CaTTExp.Gray.MarksBKernel 𝕊₀ bi cellArgD desMarks
  module DB = CaTTExp.Gray.DimB 𝕊₀ bi cellArgD
  module RR = CaTTExp.Binder.Rename 𝕊 graySideD mark
  module RS = CaTTExp.Binder.Subst 𝕊 graySideD mark

------------------------------------------------------------------------
-- The interface facts.

fstab : MS.FormerStable
fstab _ _ _ _ = refl

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  len-diskB : ∀ n → len (diskB n) ≡ suc (n + n)
  len-diskB zero    = refl
  len-diskB (suc n) = cong (λ m → suc (suc m)) (trans (len-diskB n) (sym (+-suc n n)))

  dim-tyB : ∀ n → dim (tyB n) ≡ n
  dim-tyB zero    = refl
  dim-tyB (suc n) = cong suc (dim-tyB n)

  -- Entry 2n+2 of D^{n+1} is the cell, of type tyB (n+1).
  look-cell : ∀ n → lookup (argsD n) (suc n + suc n) ≡ just (tyB (suc n))
  look-cell n with suc n + suc n ==ℕ suc (len (diskB n)) in e
  ... | true  = refl
  ... | false = ⊥-elim (subst T e (subst (λ m → T (suc n + suc n ==ℕ m)) eqn (==ℕ-refl (suc n + suc n))))
    where
    eqn : suc n + suc n ≡ suc (len (diskB n))
    eqn = trans (cong suc (+-suc n n)) (cong suc (sym (len-diskB n)))

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  ≤-refl : ∀ n → n ≤ n
  ≤-refl zero    = z≤n
  ≤-refl (suc n) = s≤s (≤-refl n)

  ≤-suc : ∀ n → n ≤ suc n
  ≤-suc zero    = z≤n
  ≤-suc (suc n) = s≤s (≤-suc n)

cellDim : DB.CellDim
cellDim (des k zero)    y Θ j C ec ()
cellDim (des k (suc n)) y Θ j C refl ok eC
  with just-inj (trans (sym (look-cell n)) eC)
... | refl = res-dim k
  where
  res-dim : ∀ k → dim (tyB (suc n)) ≤ dim (res (des k (suc n)) y Θ)
  res-dim linvK  rewrite dim-tyB n = ≤-refl (suc n)
  res-dim rinvK  rewrite dim-tyB n = ≤-refl (suc n)
  res-dim unitLK rewrite dim-tyB n = ≤-suc (suc n)
  res-dim unitRK rewrite dim-tyB n = ≤-suc (suc n)

------------------------------------------------------------------------
-- The kernel hypotheses, and substitution for Gray + DES.

module _ (closed : Closed) (tm-ty : ∀ {Γ t A} → Γ MS.Fg.F.⊢tm t ∶ A → Γ MS.Fg.F.⊢ty A) where

  private
    laws = CaTTExp.Binder.DesLaws.desLaws 𝕊₀
    dimOK = DB.dimOK cellDim tm-ty

  markSub : RS.MarkSub
  markSub {Γ} {Δ} {σ} {t} {A} {m} = MK.markSub closed laws fstab tm-ty dimOK {Γ} {Δ} {σ} {t} {A} {m}

  markRen : RR.MarkRen
  markRen {Γ} {Γ′} {ρ} {t} {A} {m} = MK.markRen closed laws fstab tm-ty dimOK {Γ} {Γ′} {ρ} {t} {A} {m}

  -- Substitution in two-tier L with destructors and its marks.
  tm[] : ∀ {Γ Δ t A σ} → Γ Kernel.⊢tm t ∶ A → Δ Kernel.⊢sub σ ∶ Γ → Δ Kernel.⊢tm t [ σ ]tm ∶ A [ σ ]ty
  tm[] = RS.tm[] closed laws (λ {Γ} {Γ′} {ρ} {t} {A} {m} → markRen {Γ} {Γ′} {ρ} {t} {A} {m})
                             (λ {Γ} {Δ} {σ} {t} {A} {m} → markSub {Γ} {Δ} {σ} {t} {A} {m}) markVar
