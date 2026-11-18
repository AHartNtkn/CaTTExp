------------------------------------------------------------------------
-- Cross-check against the independent cylinder construction of the
-- free-objects thread (CaTTExp.Free.Cylinder, convention I ⊗ Γ with
-- layout x⁻, x⁺, x↑ at levels 3i, 3i+1, 3i+2).
--
-- For globular Γ it should coincide, up to the renaming of variables,
-- with `cyl left 1 Γ` (D¹ ⊗ Γ, layout: copy 0, copy 1, generators).
-- `agree Γ` compares every variable's type syntactically.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.CrossFree where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab using (length)
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Cube using (fromJust)
open import CaTTExp.GrayCtx.Checks.Base using (D; HComp; VComp)
import CaTTExp.Free.Cylinder as Free

-- Free's variables, in Free's order, as variables of `cyl left 1 Γ`.
ρ : Nat → Sub
ρ N = go (upto N) ⟨⟩
  where
  go : List Nat → Sub → Sub
  go []       σ = σ
  go (i ∷ is) σ = go is (σ ,ₛ var i ,ₛ var (N + i) ,ₛ var (N + N + i))

-- Free's level of each of our variables is not needed: we compare
-- Free's type at level k, renamed, with ours at ρ(k).
agreeWith : Side → Ctx → Bool
agreeWith sd Γ = all ok (upto (3 * N))
  where
  open import Agda.Builtin.Nat using (_*_)
  N = len Γ
  Fr = Free.cyl Γ
  Me = fromJust (cyl sd 1 Γ)
  σ  = ρ N
  ok : Nat → Bool
  ok k with lookup Fr k | lookupₛ σ k
  ... | just A | var j with lookup Me j
  ...   | just B  = (A [ σ ]ty) ==Ty B
  ...   | nothing = false
  ok k | _ | _ = false

agree : Ctx → Bool
agree = agreeWith left

-- Non-vacuity: the lax cylinder Γ ⊗ D¹ does not agree with Free's
-- (oplax) one.
_ : agreeWith right (D 1) ≡ false
_ = refl

Sphere₁ Loop Loop² : Ctx
Sphere₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
Loop  = ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0)
Loop² = Loop ▸ arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)

cross-D¹ : agree (D 1) ≡ true
cross-D¹ = refl
cross-D² : agree (D 2) ≡ true
cross-D² = refl
cross-D³ : agree (D 3) ≡ true
cross-D³ = refl
cross-D⁴ : agree (D 4) ≡ true
cross-D⁴ = refl
cross-HComp : agree HComp ≡ true
cross-HComp = refl
cross-VComp : agree VComp ≡ true
cross-VComp = refl
cross-Sphere₁ : agree Sphere₁ ≡ true
cross-Sphere₁ = refl
cross-Loop : agree Loop ≡ true
cross-Loop = refl
cross-Loop² : agree Loop² ≡ true
cross-Loop² = refl
