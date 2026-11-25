------------------------------------------------------------------------
-- Checks of RCProc.Descent.Lift and .Fill by evaluation.  Γ is the
-- chain x —f→ y —g→ z, with g and z selected (levels x0 y1 f2 z3 g4),
-- in its cylinder context Γ↑Y with the generic datum.  The cylinder of
-- the composite f ;₀ g is built (its head is 1-dimensional: the filler
-- is Naturality.DimOne's K₁), and it has type a_t → b_t, with a_t, b_t
-- the boundary cells of endsT.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.FillExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_)
open import CaTTExp.RCProc using (rcS)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; ansT; decTm)
open import CaTTExp.RCProc.GlueP using (treeCtx; varT)
open import CaTTExp.RCProc.Descent.Lift
open import CaTTExp.RCProc.Descent.Fill

private
  T₂ : Tree
  T₂ = node (leaf ∷ leaf ∷ [])

  Γ : Ctx
  Γ = ctxOf T₂

  wΓ : Γ ⊢ctx
  wΓ = treeCtx T₂

  Y : Sel
  Y = ◇ ◂ false ◂ false ◂ false ◂ true ◂ true

  recS : RecAll
  recS {Δ} _ a b = decTy (ty b) (ty a) >>= λ p →
                   rcS (der a) (subst (Δ ⊢tm tm b ∶_) p (der b)) >>= λ r → just (ansT r)

  fg : Maybe (TTm Γ)
  fg = varT wΓ 2 >>= λ f → varT wΓ 4 >>= λ g → rcomp? 0 0 f g

  D : Maybe (TDatum Γ (cylCtx Γ Y))
  D = genD Γ Y wΓ

  up : Maybe (TTm (cylCtx Γ Y))
  ends : Maybe (TTm (cylCtx Γ Y) × TTm (cylCtx Γ Y))
  up   = D >>= λ D′ → fg >>= liftT (fillC 4 recS) D′
  ends = D >>= λ D′ → fg >>= endsT (fillC 4 recS) D′

_ : is-just D ≡ true
_ = refl

_ : is-just up ≡ true
_ = refl

-- the cylinder goes from a_t to b_t
_ : is-just (up >>= λ u → ends >>= λ ab → decTy (ty u) (arr (ty (fst ab)) (tm (fst ab)) (tm (snd ab))) >>= λ _ → just tt) ≡ true
_ = refl

-- (and not from b_t to a_t)
_ : is-just (up >>= λ u → ends >>= λ ab → decTy (ty u) (arr (ty (fst ab)) (tm (snd ab)) (tm (fst ab))) >>= λ _ → just tt) ≡ false
_ = refl
