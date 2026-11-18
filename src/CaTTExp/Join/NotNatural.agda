------------------------------------------------------------------------
-- The source-only joining completion is not natural under maps that
-- send a seed to a composite (r7 §2).
--
-- Vertices (K14 words):  x = bacrqp, u = abpcqr, w₁ = abcpqr,
--                        w₂ = bapcqr, v = bacpqr.
-- Inner arrows:  p : u → w₁,  e : w₁ → v,  q : u → w₂,  f : w₂ → v.
-- Source seed τ : x → v; target seed A = h_z : x → w₂.
--
-- The functor Path(Q) → Path(Q′) fixing inner arrows and sending
-- τ ↦ A ; f does not extend to the completions: the source has
-- j τ (e ∷ []) : x → w₁ with j τ (e ∷ []) ; e = τ (src-eqn), and no
-- word H : x → w₁ of the target completion has H ; e = A ; f
-- (no-extension). Restricted naturality, for maps sending seeds to
-- seeds, is CaTTExp.Join.Natural.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
import CaTTExp.Join.Completion as Completion

module CaTTExp.Join.NotNatural where

data Vx : Set where
  x u w₁ w₂ v : Vx

data Ex : Vx → Vx → Set where
  p : Ex u w₁
  e : Ex w₁ v
  q : Ex u w₂
  f : Ex w₂ v

-- Source seeds and target seeds.
data Pτ : Vx → Vx → Set where
  τ : Pτ x v

data PA : Vx → Vx → Set where
  A : PA x w₂

module S = Completion Ex Pτ
module T = Completion Ex PA

-- In the source completion, j τ e factors τ through w₁.
src-eqn : S.jn τ (e ∷ []) ∷ S.inn e ∷ [] S.~ S.ι (S.op τ ∷ [])
src-eqn = S.fwd (S.ctr τ e [] [])

-- The image of τ under the functor.
Fτ : T.Word x v
Fτ = T.ι (T.op A ∷ T.oe f ∷ [])

-- The only word x → w₁ of the target completion.
only : (H : T.Word x w₁) → H ≡ T.jn A (q ∷ []) ∷ T.inn p ∷ []
only (T.inn () ∷ _)
only (T.jn A [] ∷ T.inn f ∷ T.inn () ∷ _)
only (T.jn A [] ∷ T.inn f ∷ T.jn () _ ∷ _)
only (T.jn A [] ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn p ∷ []) = refl
only (T.jn A (q ∷ []) ∷ T.inn p ∷ T.inn e ∷ T.inn () ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn p ∷ T.inn e ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn p ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn q ∷ T.inn f ∷ T.inn () ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn q ∷ T.inn f ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ []) ∷ T.inn q ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ []) ∷ T.jn () _ ∷ _)
only (T.jn A (q ∷ f ∷ (() ∷ _)) ∷ _)
only (T.jn A (p ∷ e ∷ (() ∷ _)) ∷ _)
only (T.jn A (e ∷ (() ∷ _)) ∷ _)
only (T.jn A (f ∷ (() ∷ _)) ∷ _)

private
  nH : T.Normal (T.jn A (q ∷ []) ∷ T.inn p ∷ T.inn e ∷ [])
  nH _ (T.skip _ (T.skip _ (T.skip _ ())))

  nAf : T.Normal Fτ
  nAf _ (T.skip _ (T.skip _ ()))

-- No extension: no H with H ; e = A ; f.
no-extension : (H : T.Word x w₁) → ¬ (H ++ᵖ (T.inn e ∷ []) T.~ Fτ)
no-extension H r with only H
... | refl with T.nf-unique nH nAf r
...   | ()
