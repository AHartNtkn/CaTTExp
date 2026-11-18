------------------------------------------------------------------------
-- B16: the d = 4 instance of the all-dimensions collapse (B9,
-- limits-metatheory.md §3) on the specified transfor shapes of
-- CaTTExp.Cones (the intended calculus: specified shapes, unrestricted
-- transfors).
--
-- Step 1 of the B9 proof, for k = d − 2 = 2: an arbitrary 4-cell
-- z : a ⇛ b becomes, up to invertible coherences, the top f-component
-- of a 2-transfor over the arrow diagram x → y substituted by
-- (Y, Y, 1_Y):
--
--   x-, y-components: the boundaries of a, b (μ_x = b, μ_y = a);
--   p_f = ρ (inverse right unitor), m_f = N (its naturality), coherences;
--   μ_f = C_a ;₃ G(z), with C_a a full-support coherence over D³ and
--   G(u) = (ρ_r ∗₁ (u ∗₀ 1_Y)) ∗₂ N_{α₁}.
--
--  C1  θ is a well-typed substitution Ω₄ → Tr₂ in the CaTT core, where
--      Ω₄ = D⁴ and Tr₂ = Cones.ctrf 2 (x → y). So with unrestricted
--      transfors the instance is admitted and the rest of the B9
--      argument applies to it.
--  C2  Not vacuous: putting a in place of b at μ_x is rejected.
--  C3  Under P (and under L with f marked), μ_f is marked (Cones marks
--      m⁻_f, m⁺_f, μ_f) and the image of μ_f has no certificate unless
--      z is certified, so the repaired rule refuses the instance. The
--      other marked images (coherences N) are certified.
--
-- Not formalized: steps 2–5 of the proof (uni, endpoint reduction, and
-- that F(w)_f is a coherence-case coh), which need the star and uni
-- judgments; see notes/catt-lim-formalization.md §3.
------------------------------------------------------------------------
module CaTTExp.Lim.Collapse4 where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Cones
open import CaTTExp.Lim.Repaired using (cert)

-- A coherence over the disk Dⁿ with the given source and target (cells
-- of Dⁿ), applied to the n-cell u.
autoC : Nat → Cell → Cell → Cell → Cell
autoC n s t u = coh (Disk n) A ⟪ diskList u ⟫ , A [ ⟪ diskList u ⟫ ]ty
  where A = arr (snd s) (fst s) (fst t)

1c : Cell → Cell          -- identity on a 0-cell
1c = idC

-- ρ_r : r ⇒ r ∗₀ 1_Y, over D¹ = (c, Y, r).
ρ : Cell → Cell
ρ = autoC 1 r (binC 0 r (1c Y))
  where r = gen (Disk 1) 2 ; Y = gen (Disk 1) 1

-- N_α : ρ_r ∗₁ (α ∗₀ 1_Y) ⇛ α ∗₁ ρ_s, over D² = (c, Y, r, s, α).
N : Cell → Cell
N = autoC 2 (binC 1 (ρ r) (binC 0 α (1c Y))) (binC 1 α (ρ s))
  where D = Disk 2 ; Y = gen D 1 ; r = gen D 2 ; s = gen D 3 ; α = gen D 4

-- In D³ = (c, Y, r, s, α₀, α₁, a):
--   G(u) = (ρ_r ∗₁ (u ∗₀ 1_Y)) ∗₂ N_{α₁}
--   C_a  : N_{α₀} ∗₂ (a ∗₁ ρ_s) ⇛ G(a)
G : Cell → Cell → Cell → Cell → Cell
G Y r α₁ u = binC 2 (binC 1 (ρ r) (binC 0 u (1c Y))) (N α₁)

C : Cell → Cell
C = autoC 3 (binC 2 (N α₀) (binC 1 a (ρ s))) (G Y r α₁ a)
  where D = Disk 3 ; Y = gen D 1 ; r = gen D 2 ; s = gen D 3
        α₀ = gen D 4 ; α₁ = gen D 5 ; a = gen D 6

------------------------------------------------------------------------
-- Ω₄ = D⁴ = (c0, Y1, r2 s3 : c → Y, α₀4 α₁5 : r ⇒ s, a6 b7 : α₀ ⇛ α₁,
--            z8 : a ⇛ b), an arbitrary 4-cell.

Ω₄ : Ctx
Ω₄ = Disk 4

module _ where
  private
    g = gen Ω₄
  c Y r s α₀ α₁ a b z : Cell
  c = g 0 ; Y = g 1 ; r = g 2 ; s = g 3 ; α₀ = g 4 ; α₁ = g 5
  a = g 6 ; b = g 7 ; z = g 8

-- The f-component at level 2: C_a ; G(z) : N_{α₀} ∗₂ (a ∗₁ ρ_s) ⇛ G(b).
μf : Cell
μf = binC 3 (C a) (G Y r α₁ z)

-- The 2-transfor over x → y with x, y ↦ Y and f ↦ 1_Y.
-- Tr₂ levels: x0 y1 f2 c3 | p⁻_x4 p⁺_x5 m⁻_x6 m⁺_x7 μ_x8 |
--             p⁻_y9 p⁺_y10 m⁻_y11 m⁺_y12 μ_y13 |
--             p⁻_f14 p⁺_f15 m⁻_f16 m⁺_f17 μ_f18.
θ : Sub
θ = ⟪ map fst
      ( Y ∷ Y ∷ 1c Y ∷ c
      ∷ r ∷ s ∷ α₀ ∷ α₁ ∷ b
      ∷ r ∷ s ∷ α₀ ∷ α₁ ∷ a
      ∷ ρ r ∷ ρ s ∷ N α₀ ∷ N α₁ ∷ μf ∷ []) ⟫

Arr : ExCtx
Arr = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ []

Tr₂ : Ctrf
Tr₂ = from-just (ctrf 2 Arr)

Tr₂Ctx : Ctx
Tr₂Ctx = evCtx (Ctrf.ctx Tr₂)

instance-typed : Ω₄ ⊢sub θ ∶ Tr₂Ctx
instance-typed = from-just (checkCtx Ω₄ >>= λ w → checkSub Ω₄ w θ Tr₂Ctx)

------------------------------------------------------------------------
-- C2. Not vacuous.

θbad : Sub
θbad = ⟪ map fst
      ( Y ∷ Y ∷ 1c Y ∷ c
      ∷ r ∷ s ∷ α₀ ∷ α₁ ∷ a
      ∷ r ∷ s ∷ α₀ ∷ α₁ ∷ a
      ∷ ρ r ∷ ρ s ∷ N α₀ ∷ N α₁ ∷ μf ∷ []) ⟫

C2 : is-just (checkCtx Ω₄ >>= λ w → checkSub Ω₄ w θbad Tr₂Ctx) ≡ false
C2 = refl

------------------------------------------------------------------------
-- C3. Marks and certificates (z is level 8 of Ω₄).

_ : Ctrf.marked Tr₂ ≡ (16 ∷ 17 ∷ 18 ∷ [])
_ = refl

C3-rejected : cert [] (fst μf) ≡ false
C3-rejected = refl

C3-if-z-certified : cert (8 ∷ []) (fst μf) ≡ true
C3-if-z-certified = refl

_ : (cert [] (fst (N α₀)) ∧ cert [] (fst (N α₁))) ≡ true
_ = refl
