------------------------------------------------------------------------
-- Two-tier L with binding formers: the Gray side condition on binder
-- syntax, and conservativity over binder-free L (ledger E4, DES).
--
-- The coh side condition of L (CaTTExp.Gray.Support.graySide) reads
-- supports off terms. A destructor occurrence linv t, rinv t, unitL t,
-- unitR t (notes/invertibility-markings.md §1.1, spec §3.3) has the
-- support of its cell argument t: in any model its value is built from
-- ⟦t⟧ alone, exactly as ICaTT's Var(linv e) = Var(e). So the side
-- condition on binder syntax is graySide after *erasing* each
-- destructor to its cell argument:
--
--   dTm (bnd b y Δ ts) = dTm (ts j)   if cellArg b = just j
--                      = nothing      otherwise (other formers, bvar)
--
-- and `graySideD` fails whenever erasure fails. `cellArg` is a
-- parameter, so the module serves any interface in which some formers
-- are destructors (DES) and others are rejected by L's coh rule.
--
-- On binder-free syntax erasure is the identity (`de-tm` etc.), so the
-- two side conditions agree (`graySideD-agree`), and Binder.Embed's
-- conservativity theorems apply: the extension of binder-free L by any
-- binder interface and any mark judgment derives nothing new about
-- the binder-free fragment (`open Theorems`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Syntax as OSyn
import CaTTExp.Binder.Syntax as NSyn
open import CaTTExp.Binder.Embed
open import CaTTExp.Binder.Signature using (Signature)
import CaTTExp.Binder.Mark as BM

module CaTTExp.Gray.DesSide
  (𝕊₀ : Old.Signature)
  (bi : Binders (Old.Signature.K 𝕊₀))
  (cellArg : Binders.B bi → Maybe Nat)
  where

private
  K = Old.Signature.K 𝕊₀
  B = Binders.B bi
  module O = OSyn K
  module N = NSyn K B
  open Emb K B

open import CaTTExp.Gray.Support 𝕊₀ using (graySide)

------------------------------------------------------------------------
-- Erasure of destructors.

mutual
  dTy : N.Ty → Maybe O.Ty
  dTy N.⋆           = just O.⋆
  dTy (N.arr A t u) = dTy A >>= λ A₀ → dTm t >>= λ t₀ → dTm u >>= λ u₀ → just (O.arr A₀ t₀ u₀)

  dTm : N.Tm → Maybe O.Tm
  dTm (N.var i)        = just (O.var i)
  dTm (N.bvar _ _)     = nothing
  dTm (N.coh Γ A σ)    = dCtx Γ >>= λ Γ₀ → dTy A >>= λ A₀ → dSub σ >>= λ σ₀ → just (O.coh Γ₀ A₀ σ₀)
  dTm (N.cst k)        = just (O.cst k)
  dTm (N.bnd b _ _ ts) = dCell (cellArg b) ts

  -- The cell argument of a destructor, erased.
  dCell : Maybe Nat → N.Sub → Maybe O.Tm
  dCell nothing  ts = nothing
  dCell (just j) ts = dArg j ts

  dArg : Nat → N.Sub → Maybe O.Tm
  dArg j N.⟨⟩       = nothing
  dArg j (σ N.,ₛ t) = if j ==ℕ N.lenₛ σ then dTm t else dArg j σ

  dCtx : N.Ctx → Maybe O.Ctx
  dCtx N.ε       = just O.ε
  -- Marks are erased with the rest (L's coh rule never sees them).
  dCtx (Γ N.▸[ _ ] A) = dCtx Γ >>= λ Γ₀ → dTy A >>= λ A₀ → just (Γ₀ O.▸ A₀)

  dSub : N.Sub → Maybe O.Sub
  dSub N.⟨⟩       = just O.⟨⟩
  dSub (σ N.,ₛ t) = dSub σ >>= λ σ₀ → dTm t >>= λ t₀ → just (σ₀ O.,ₛ t₀)

-- The side condition of L on binder syntax.
graySideD : N.Ctx → N.Ty → N.Tm → N.Tm → Bool
graySideD Δ A t u with dCtx Δ | dTy A | dTm t | dTm u
... | just Δ₀ | just A₀ | just t₀ | just u₀ = graySide Δ₀ A₀ t₀ u₀
... | _       | _       | _       | _       = false

------------------------------------------------------------------------
-- Erasure is the identity on binder-free syntax.

mutual
  de-ty : ∀ A → dTy (eTy A) ≡ just A
  de-ty O.⋆ = refl
  de-ty (O.arr A t u) rewrite de-ty A | de-tm t | de-tm u = refl

  de-tm : ∀ t → dTm (eTm t) ≡ just t
  de-tm (O.var i) = refl
  de-tm (O.coh Γ A σ) rewrite de-ctx Γ | de-ty A | de-sub σ = refl
  de-tm (O.cst k) = refl

  de-ctx : ∀ Γ → dCtx (eCtx Γ) ≡ just Γ
  de-ctx O.ε = refl
  de-ctx (Γ O.▸ A) rewrite de-ctx Γ | de-ty A = refl

  de-sub : ∀ σ → dSub (eSub σ) ≡ just σ
  de-sub O.⟨⟩ = refl
  de-sub (σ O.,ₛ t) rewrite de-sub σ | de-tm t = refl

------------------------------------------------------------------------
-- Conservativity of L + binders over L, for every mark judgment on
-- binder syntax (binder-free L has no marked entries).

module _ (mark : Signature.Ctx (extend 𝕊₀ bi) → BM.Mark → Signature.Tm (extend 𝕊₀ bi) → Bool) where

  open Conservative 𝕊₀ bi graySide graySideD mark public

  graySideD-agree : Agree
  graySideD-agree Δ A t u rewrite de-ctx Δ | de-ty A | de-tm t | de-tm u = refl

  open Theorems graySideD-agree public
