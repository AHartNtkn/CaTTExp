------------------------------------------------------------------------
-- Two-tier L accepts the coherences in DES's result types, in every
-- dimension: the side hypotheses of the kernel's presupposition for
-- the DES instance (CaTTExp.Binder.DesPresup), at L's side condition
-- on binder syntax (CaTTExp.Gray.DesSide), over pure L.
--
--   side-comp n : graySideD (compPC n) (tyD n) (var 2n) (var (2n+3))
--   side-id n   : graySideD (diskD n)  (tyD n) (var 2n) (var 2n)
--
-- The composite of two (n+1)-cells along an n-cell is, after erasure,
-- literally CaTTExp.Derived's composite head (BK n 0, wK n 0), which
-- two-tier L accepts for every n (Gray.WhiskerZeroSide for n = 0,
-- Gray.WhiskerSide for n ≥ 1).
--
-- The identity over Dⁿ is, after erasure, coh over Derived's disk Dsk n
-- with both sides its top cell. For n = 0 it is accepted by the
-- operation case (by evaluation). For n ≥ 1, Dsk n = Σ Dsk (n−1) is a
-- single hom, and the top cell uses every variable of the disk
-- (Finster–Mimram's coherence condition, Binder.DesSideCatt.coh-Dsk),
-- so the coherence case holds (Gray.SingleHomSide.Cells.coh-side).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
import CaTTExp.Gray.Pure as G
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
open import CaTTExp.Gray.WhiskerSide using (gside-BK0)
open import CaTTExp.Gray.WhiskerZeroSide using (gside-BK0-0)
open import CaTTExp.Gray.WhiskerSigma using (Σ-Dsk)
open import CaTTExp.Gray.SingleHomSide using (module Cells)
open import CaTTExp.Gray.SingleHom P.∅ using (objsΣ)
open import CaTTExp.Suspension P.∅ using (Σctx)
open import CaTTExp.Binder.DesSideCatt P.∅ using (coh-Dsk)
import CaTTExp.Subst as SubstM

module CaTTExp.Gray.DesSideL where

𝕊 : Signature
𝕊 = extend P.∅ (desBinders P.K)

open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open import CaTTExp.Gray.DesSide P.∅ (desBinders P.K) cellArgD using (graySideD; dTy; dCtx)

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  dbl≡ : ∀ n → n + n ≡ dbl n
  dbl≡ zero    = refl
  dbl≡ (suc n) = cong suc (trans (+-suc n n) (cong suc (dbl≡ n)))

  d-tyD : ∀ n → dTy (tyD n) ≡ just (aL n)
  d-tyD zero = refl
  d-tyD (suc n) rewrite d-tyD n | dbl≡ n = refl

  d-diskD : ∀ n → dCtx (diskD n) ≡ just (D.Dsk n)
  d-diskD zero = refl
  d-diskD (suc n) rewrite d-diskD n | d-tyD n | dbl≡ n = refl

  d-compPC : ∀ n → dCtx (compPC n) ≡ just (D.BK n 0)
  d-compPC n rewrite d-diskD (suc n) | d-tyD n | dbl≡ n = refl

comp-BK : ∀ n → T (G.graySide (D.BK n 0) (aL n) (G.var (dbl n)) (G.var (D.zK n 0)))
comp-BK zero    = gside-BK0-0
comp-BK (suc k) = gside-BK0 k

side-comp : ∀ n → T (graySideD (compPC n) (tyD n) (var (n + n)) (var (3 + (n + n))))
side-comp n rewrite d-compPC n | d-tyD n | dbl≡ n = comp-BK n

private
  closedL : SubstM.Closed P.∅ G.graySide
  closedL ()

open import CaTTExp.DerivedWithBase G.graySide closedL using (ps-wf)

private
  endsTy-aL : ∀ m → G.endsTy (aL (suc m)) ≡ just (G.var 0 , G.var 1)
  endsTy-aL zero    = refl
  endsTy-aL (suc m) = endsTy-aL m

id-Dsk : ∀ n → T (G.graySide (D.Dsk n) (aL n) (G.var (dbl n)) (G.var (dbl n)))
id-Dsk zero    = tt
id-Dsk (suc k) =
  subst (λ Γ → T (G.graySide Γ (aL (suc k)) (G.var (dbl (suc k))) (G.var (dbl (suc k))))) (Σ-Dsk k)
    (Cells.coh-side-gray PΘ dt dt ok ic)
  where
  Γ = Σctx (D.Dsk k)
  PΘ : D.Dsk k G.⊢ps
  PΘ = G.ps (snd (D.toStar k (dbl k) (D.dsk-ps k)))
  dt : Γ G.⊢tm G.var (dbl (suc k)) ∶ aL (suc k)
  dt = subst (λ Δ → Δ G.⊢tm G.var (dbl (suc k)) ∶ aL (suc k)) (sym (Σ-Dsk k))
             (snd (ps-wf (D.dsk-ps (suc k))))
  ok : T (G.endsOK Γ (aL (suc k)))
  ok rewrite endsTy-aL k | objsΣ (D.Dsk k) = tt
  ic : T (P.isCoh Γ (aL (suc k)) (G.var (dbl (suc k))) (G.var (dbl (suc k))))
  ic = subst (λ Δ → T (P.isCoh Δ (aL (suc k)) (G.var (dbl (suc k))) (G.var (dbl (suc k))))) (sym (Σ-Dsk k))
             (coh-Dsk (suc k))

side-id : ∀ n → T (graySideD (diskD n) (tyD n) (var (n + n)) (var (n + n)))
side-id n rewrite d-diskD n | d-tyD n | dbl≡ n = id-Dsk n
