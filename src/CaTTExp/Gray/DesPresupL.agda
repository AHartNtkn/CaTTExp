------------------------------------------------------------------------
-- Presupposition and substitution for two-tier L with the destructors
-- of DES, with the Gray mark judgment, over any base signature 𝕊₀.
--
--   gray-tm-ty : Closed → SigOK (mark-free) → SigOK (Gray marks) →
--                Γ ⊢tm t ∶ A → Γ ⊢ty A
--   gray-tm[]  : Closed → SigOK (mark-free) →
--                Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t[σ] ∶ A[σ]
--
-- The kernel's presupposition for DES (CaTTExp.Binder.DesPresup) needs
-- L's side condition to accept DES's composite and identity heads in
-- every dimension. Gray.DesSideL proves both over pure syntax
-- (comp-BK, id-Dsk), and Gray.SupportIota carries L's side condition
-- from pure syntax to every signature (graySide-ι). The derivation is
-- then in two steps:
--  * the mark-free kernel (CaTTExp.Binder.Forget) has presupposition,
--    since its mark hypotheses are trivial;
--  * that is the parameter of Gray.MarksBDes, which then gives the Gray
--    mark judgment's MarkRen and MarkSub, hence presupposition and
--    substitution for the kernel with Gray marks.
-- SigOK (constants have well-formed types) is assumed for each of the
-- two kernels, as in Binder.DesSideCatt for plain CaTT.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Des
import CaTTExp.Pure as P
import CaTTExp.Derived as D
import CaTTExp.Gray.Pure as G
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Binder.Forget
import CaTTExp.Binder.Presup
import CaTTExp.Binder.Pasting
import CaTTExp.Gray.DimB
import CaTTExp.Gray.MarksBDes

module CaTTExp.Gray.DesPresupL (𝕊₀ : Old.Signature) where

open import CaTTExp.Binder.DesPresup 𝕊₀
open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open PS using (tyP; diskP; compP; emb-tyP; emb-diskP; emb-compP)
open import CaTTExp.Binder.DesSideCatt 𝕊₀ using (dbl-dd; tyP-aL; diskP-Dsk; compP-BK)
open import CaTTExp.Binder.Laws 𝕊 using (Closed)
open import CaTTExp.Gray.DesSide 𝕊₀ (desBinders (Old.Signature.K 𝕊₀)) cellArgD using (graySideD)
open import CaTTExp.Gray.SupportIota 𝕊₀ using (graySide-ι)
open import CaTTExp.Gray.DesSideL using (comp-BK; id-Dsk)

private
  module DB = CaTTExp.Gray.DimB 𝕊₀ (desBinders (Old.Signature.K 𝕊₀)) cellArgD
  module BP = CaTTExp.Binder.Pasting 𝕊
  module MD = CaTTExp.Gray.MarksBDes 𝕊₀
  module Fg = CaTTExp.Binder.Forget 𝕊 graySideD

------------------------------------------------------------------------
-- The side hypotheses, over 𝕊₀.

side-pure : ∀ Θ A t u → T (G.graySide Θ A t u) →
            T (graySideD (BP.embCtx Θ) (BP.embTy A) (BP.embTm t) (BP.embTm u))
side-pure Θ A t u p rewrite DB.dι-ctx Θ | DB.dι-ty A | DB.dι-tm t | DB.dι-tm u =
  subst T (sym (graySide-ι Θ A t u)) p

side-comp : ∀ n → T (graySideD (compPC n) (tyD n) (var (n + n)) (var (3 + (n + n))))
side-comp n =
  subst (λ X → T (graySideD (fst X) (snd X) (var (n + n)) (var (3 + (n + n)))))
        (cong₂ _,_ (emb-compP n) (emb-tyP n))
        (side-pure (compP n) (tyP n) (P.var (n + n)) (P.var (3 + (n + n))) pure)
  where
  pure : T (G.graySide (compP n) (tyP n) (P.var (n + n)) (P.var (3 + (n + n))))
  pure rewrite compP-BK n | tyP-aL n =
    subst (λ d → T (G.graySide (D.BK n 0) (aL n) (P.var d) (P.var (3 + d)))) (dbl-dd n) (comp-BK n)

side-id : ∀ n → T (graySideD (diskD n) (tyD n) (var (n + n)) (var (n + n)))
side-id n =
  subst (λ X → T (graySideD (fst X) (snd X) (var (n + n)) (var (n + n))))
        (cong₂ _,_ (emb-diskP n) (emb-tyP n))
        (side-pure (diskP n) (tyP n) (P.var (n + n)) (P.var (n + n)) pure)
  where
  pure : T (G.graySide (diskP n) (tyP n) (P.var (n + n)) (P.var (n + n)))
  pure rewrite diskP-Dsk n | tyP-aL n =
    subst (λ d → T (G.graySide (D.Dsk n) (aL n) (P.var d) (P.var d))) (dbl-dd n) (id-Dsk n)

------------------------------------------------------------------------
-- Presupposition, mark-free and with Gray marks, and substitution.

private
  module TF = Typed graySideD Fg.noMark
  module TG = Typed graySideD MD.mark
  module PF = CaTTExp.Binder.Presup 𝕊 graySideD Fg.noMark
  module PG = CaTTExp.Binder.Presup 𝕊 graySideD MD.mark
  module KG = MD.Kernel

module _ (closed : Closed) (sigF : PF.SigOK) where

  free-tm-ty : ∀ {Γ t A} → Γ Fg.F.⊢tm t ∶ A → Γ Fg.F.⊢ty A
  free-tm-ty = TF.des-tm-ty closed (λ _ _ _ → tt) (λ _ _ _ → tt) Fg.markVarF side-comp side-id sigF

  gray-tm[] : ∀ {Γ Δ t A σ} → Γ KG.⊢tm t ∶ A → Δ KG.⊢sub σ ∶ Γ → Δ KG.⊢tm t [ σ ]tm ∶ A [ σ ]ty
  gray-tm[] = MD.tm[] closed free-tm-ty

  module _ (sigG : PG.SigOK) where

    gray-tm-ty : ∀ {Γ t A} → Γ KG.⊢tm t ∶ A → Γ KG.⊢ty A
    gray-tm-ty =
      TG.des-tm-ty closed
        (λ {Γ} {Γ′} {ρ} {t} {A} {m} → MD.markRen closed free-tm-ty {Γ} {Γ′} {ρ} {t} {A} {m})
        (λ {Γ} {Δ} {σ} {t} {A} {m} → MD.markSub closed free-tm-ty {Γ} {Δ} {σ} {t} {A} {m})
        MD.markVar side-comp side-id sigG
