------------------------------------------------------------------------
-- Certified checks of the repaired Gray rule (ledger D3, standard 9),
-- for one globe factor D¹, in both factor orders (CaTTExp.GrayCtx.
-- Templates):
--
-- * (B): the disk types TsE sd p are boundary templates, p ≤ 4, both
--   orders; a template of the wrong order is rejected.
-- * (C): the template for binary composition of 1-cells passes rule
--   (C), both orders; the template of the wrong order is rejected.
-- * M ⊗ D¹ (T₁M, built by equations (5)–(8) of the answer) is a
--   well-formed CaTT context, certified by the checker, for the
--   walking arrow, the triangle α : f ; g ⇒ h and the lax square
--   α : f ; g ⇒ h ; k, both orders.
-- * On disks (globular, no coherences) T₁M is the all-dimension
--   cylinder cylE of CaTTExp.GrayCtx.NaturalAll, for D⁰ … D³.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.Templates where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.NaturalAll using (cylE)
open import CaTTExp.GrayCtx.Templates
open import CaTTExp.GrayCtx.Checks.Base using (WF; wf?; cert; D)

------------------------------------------------------------------------
-- (B)

B-ok : ∀ sd p → T (p <ℕ 5) → T (checkB sd p (Uctx sd p) (Btmpl sd p))
B-ok right 0 _ = tt
B-ok right 1 _ = tt
B-ok right 2 _ = tt
B-ok right 3 _ = tt
B-ok right 4 _ = tt
B-ok left  0 _ = tt
B-ok left  1 _ = tt
B-ok left  2 _ = tt
B-ok left  3 _ = tt
B-ok left  4 _ = tt

-- The orders are not interchangeable (from p = 1 on).
B-wrong-order₁ : checkB right 1 (Uctx right 1) (Btmpl left 1) ≡ false
B-wrong-order₁ = refl

B-wrong-order₂ : checkB left 2 (Uctx left 2) (Btmpl right 2) ≡ false
B-wrong-order₂ = refl

------------------------------------------------------------------------
-- (C)

C-ok-left : T (compOK left)
C-ok-left = tt

C-ok-right : T (compOK right)
C-ok-right = tt

C-wrong-order : (compC right >>= λ C → just (checkC left Comp₂P compA C)) ≡ just false
C-wrong-order = refl

------------------------------------------------------------------------
-- M ⊗ D¹ for the walking arrow, the triangle and the lax square.

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp a b f c g = coh Comp₂P compA (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g)

-- a —f→ b,  a, b : ⋆
Arrow : Ctx
Arrow = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1)

-- a —f→ b —g→ c,  h : a → c,  α : f ; g ⇒ h
Triangle : Ctx
Triangle =
  ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)
    ▸ arr ⋆ (var 0) (var 3)
    ▸ arr (arr ⋆ (var 0) (var 3)) (comp (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)

-- a —f→ b —g→ c,  a —h→ d —k→ c,  α : f ; g ⇒ h ; k
LaxSquare : Ctx
LaxSquare =
  ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)
    ▸ ⋆ ▸ arr ⋆ (var 0) (var 5) ▸ arr ⋆ (var 5) (var 3)
    ▸ arr (arr ⋆ (var 0) (var 3)) (comp (var 0) (var 1) (var 2) (var 3) (var 4))
                                  (comp (var 0) (var 5) (var 6) (var 3) (var 7))

⊗D¹ : Side → Ctx → Maybe Ctx
⊗D¹ sd = T1.T1 sd (Ctmpl sd)

arrow-left : WF (⊗D¹ left Arrow)
arrow-left = cert (wf? (⊗D¹ left Arrow)) tt

arrow-right : WF (⊗D¹ right Arrow)
arrow-right = cert (wf? (⊗D¹ right Arrow)) tt

triangle-left : WF (⊗D¹ left Triangle)
triangle-left = cert (wf? (⊗D¹ left Triangle)) tt

triangle-right : WF (⊗D¹ right Triangle)
triangle-right = cert (wf? (⊗D¹ right Triangle)) tt

laxSquare-left : WF (⊗D¹ left LaxSquare)
laxSquare-left = cert (wf? (⊗D¹ left LaxSquare)) tt

laxSquare-right : WF (⊗D¹ right LaxSquare)
laxSquare-right = cert (wf? (⊗D¹ right LaxSquare)) tt

-- Size: (2·1 + 1)·|Var(M)| variables.
laxSquare-size : (⊗D¹ left LaxSquare >>= λ Γ → just (len Γ)) ≡ just 27
laxSquare-size = refl

------------------------------------------------------------------------
-- Agreement with the all-dimension cylinder on disks.

private
  eqM : Maybe Ctx → Ctx → Bool
  eqM (just Γ) Δ = Γ ==Ctx Δ
  eqM nothing  Δ = false

  eqM-sound : ∀ m Δ → T (eqM m Δ) → m ≡ just Δ
  eqM-sound (just Γ) Δ h = cong just (==Ctx-sound Γ Δ h)

T₁≡cylE : ∀ sd n → T (n <ℕ 4) → ⊗D¹ sd (D n) ≡ just (cylE sd (D n))
T₁≡cylE sd n h = eqM-sound _ _ (go sd n h)
  where
  go : ∀ sd n → T (n <ℕ 4) → T (eqM (⊗D¹ sd (D n)) (cylE sd (D n)))
  go right 0 _ = tt
  go right 1 _ = tt
  go right 2 _ = tt
  go right 3 _ = tt
  go left  0 _ = tt
  go left  1 _ = tt
  go left  2 _ = tt
  go left  3 _ = tt

arrow-is-D1 : Arrow ≡ D 1
arrow-is-D1 = refl
