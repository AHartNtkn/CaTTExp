------------------------------------------------------------------------
-- Checks of RCProc.Descent.LiftOp by evaluation.  Γ is one point x,
-- selected, in its cylinder context x⁻, x⁺, x↑ : x⁻ → x⁺.  The identity
-- 1_x (rcP's answer to the query (x, x)) has a lax square 1_x↑ : a → b
-- (Lift, by Naturality.DimOne's K₁) and an oplax square 1_x↑ᵒᵖ : b → a
-- (LiftOp, by the direct op filler), with a = 1_{x⁻} ∗₀ x↑ and
-- b = x↑ ∗₀ 1_{x⁺} the boundary cells of endsT.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.LiftOpExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_)
open import CaTTExp.RCProc using (rcS)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (ansT)
open import CaTTExp.RCProc.GlueP using (treeCtx; varT)
open import CaTTExp.RCProc.Strip using (idT)
open import CaTTExp.RCProc.Descent.Lift
open import CaTTExp.RCProc.Descent.Fill
open import CaTTExp.RCProc.Descent.LiftOp

private
  Γ : Ctx
  Γ = ctxOf leaf

  wΓ : Γ ⊢ctx
  wΓ = treeCtx leaf

  Y : Sel
  Y = ◇ ◂ true

  recS : RecAll
  recS {Δ} _ a b = decTy (ty b) (ty a) >>= λ p →
                   rcS (der a) (subst (Δ ⊢tm tm b ∶_) p (der b)) >>= λ r → just (ansT r)

  F : FillO
  F = fillC 4 recS

  G : FillOpO
  G = fillDirectOp F recS

  ix : Maybe (TTm Γ)
  ix = varT wΓ 0 >>= idT

  D : Maybe (TDatum Γ (cylCtx Γ Y))
  D = genD Γ Y wΓ

  up op : Maybe (TTm (cylCtx Γ Y))
  up = D >>= λ D′ → ix >>= liftT F D′
  op = D >>= λ D′ → ix >>= liftOpT F G D′ (λ _ → nothing)

  ends : Maybe (TTm (cylCtx Γ Y) × TTm (cylCtx Γ Y))
  ends = D >>= λ D′ → ix >>= endsT F D′

  has : Maybe (TTm (cylCtx Γ Y)) → (TTm (cylCtx Γ Y) × TTm (cylCtx Γ Y) → Ty) → Bool
  has m f = is-just (m >>= λ w → ends >>= λ ab → decTy (ty w) (f ab) >>= λ _ → just tt)

  fwd bwd : TTm (cylCtx Γ Y) × TTm (cylCtx Γ Y) → Ty
  fwd ab = arr (ty (fst ab)) (tm (fst ab)) (tm (snd ab))
  bwd ab = arr (ty (fst ab)) (tm (snd ab)) (tm (fst ab))

_ : is-just op ≡ true
_ = refl

-- the lax square goes a → b, the oplax one b → a
_ : has up fwd ≡ true
_ = refl

_ : has op bwd ≡ true
_ = refl

_ : has op fwd ≡ false
_ = refl
