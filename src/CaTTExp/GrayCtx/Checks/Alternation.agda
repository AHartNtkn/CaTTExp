------------------------------------------------------------------------
-- The alternation in Γ ⊗ D¹ is forced: in D² ⊗ D¹, the type of α⊗e with
-- the end copies used as in dimension 1 (no alternation) is not even a
-- well-formed type, while the construction's choice is.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.Alternation where
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Cube using (fromJust)
-- D² ⊗ D¹: x0 y1 f2 g3 α4 | x5 y6 f7 g8 α9 | xe10 ye11 fe12 ge13 αe14
Γ : Ctx
Γ = dropLast (fromJust (cyl right 1 (ctxOf (chain 2))))
  where
  dropLast : Ctx → Ctx
  dropLast (Δ ▸ _) = Δ
  dropLast ε = ε
okTy : Maybe Ty → Bool
okTy nothing = false
okTy (just A) = is-just (checkCtx Γ >>= λ w → (λ _ → tt) <$> checkTy Γ w A)
αty : Nat → Nat → Maybe Ty
αty εS εT = rw F Γ (var εS) (var 11) >>= λ l → lw F Γ (var 10) (var εT) >>= λ r →
  vcomp Γ (var 12 ∷ l ∷ []) >>= λ S → vcomp Γ (r ∷ var 13 ∷ []) >>= λ T →
  tyOf Γ S >>= λ C → just (arr C S T)
-- alternating (the construction): ε = a = α₀ (4), ε′ = b = α₁ (9)
alternating-ok : okTy (αty 4 9) ≡ true
alternating-ok = refl
-- non-alternating (same copies as in dimension 1): ε = b, ε′ = a
non-alternating-ill-typed : okTy (αty 9 4) ≡ false
non-alternating-ill-typed = refl
-- (the elaborator does produce a candidate type; it is the certified
-- checker that rejects it)
non-alternating-elaborates : is-just (αty 9 4) ≡ true
non-alternating-elaborates = refl
