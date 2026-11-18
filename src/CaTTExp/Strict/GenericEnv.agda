------------------------------------------------------------------------
-- The generic environment of a pasting context in the free model
-- (ledger item A3a, general case).
--
-- The free model is the strict ω-category 𝒯 of trees labelled by
-- variables (CaTTExp.Strict.TreeCat Nat), with no constants. The
-- generic environment η Γ sends a variable v : A to its disc: the
-- tree whose spine at each height j < dim A runs from the j-source to
-- the j-target of v, with v on top. On a pasting context it is valid
-- (`η-valid`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.GenericEnv (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd; PsCtx; ==→≡; <→≢)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)
import CaTTExp.Strict.TreeCat Nat as TC
open TC using (𝒯) public

-- No constants in the free model.
M𝒯 : K → LT Nat → Set
M𝒯 _ _ = ⊥

import CaTTExp.Strict.OmegaEval 𝕊 𝒯 M𝒯 as E𝒯

------------------------------------------------------------------------
-- Discs.

vn : Tm → Nat
vn (var a) = a
vn _       = 0

discT : Ty → LT Nat → LT Nat
discT ⋆           T = T
discT (arr B s u) T = discT B (node (vn s) (cons T (vn u) nil))

disc : Nat → Ty → LT Nat
disc v A = discT A (node v nil)

private
  +-suc : ∀ d k → d + suc k ≡ suc (d + k)
  +-suc zero    k = refl
  +-suc (suc d) k = cong suc (+-suc d k)

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

bdm-discT : ∀ B j T → bdm (j + dim B) (discT B T) ≡ discT B (bdm j T)
bdm-discT ⋆           j T rewrite +-zero j = refl
bdm-discT (arr B s u) j T rewrite +-suc j (dim B) = bdm-discT B (suc j) (node (vn s) (cons T (vn u) nil))

bdp-discT : ∀ B j T → bdp (j + dim B) (discT B T) ≡ discT B (bdp j T)
bdp-discT ⋆           j T rewrite +-zero j = refl
bdp-discT (arr B s u) j T rewrite +-suc j (dim B) = bdp-discT B (suc j) (node (vn s) (cons T (vn u) nil))

------------------------------------------------------------------------
-- The generic environment.

η : Ctx → E𝒯.Env
η ε       = E𝒯.[]ₑ
η (Γ ▸ A) = η Γ E𝒯.,ₑ disc (len Γ) A

lenₑ-η : ∀ Γ → E𝒯.lenₑ (η Γ) ≡ len Γ
lenₑ-η ε       = refl
lenₑ-η (Γ ▸ A) = cong suc (lenₑ-η Γ)

lookE-η : ∀ Γ v {A} → lookup Γ v ≡ just A → E𝒯.lookE (η Γ) v ≡ just (disc v A)
lookE-η ε       v ()
lookE-η (Γ ▸ B) v p rewrite lenₑ-η Γ with v ==ℕ len Γ in e
... | true  rewrite ==→≡ v (len Γ) e = cong (λ X → just (disc (len Γ) X)) (just-inj p)
  where
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl
... | false = lookE-η Γ v p

η-valid : ∀ {Θ} → ArrOrd Θ → PsCtx Θ → E𝒯.ValidEnv (η Θ) Θ
η-valid {Θ} ord sh v A p = disc v A , lookE-η Θ v p , bdm-discT A 0 (node v nil) , bd (sh v A p) p
  where
  bd : ∀ {A} → PsTy A → lookup Θ v ≡ just A → E𝒯.Bd (disc v A) A (η Θ)
  bd ⋆ₚ _ = tt
  bd (arrₚ {B} {a} {b} _) q =
    let (la , lb , _) = ord v B a b q
    in E𝒯.ev-var (trans (lookE-η Θ a la) (cong just (sym (bdm-discT B 0 (node a (cons (node v nil) b nil)))))) ,
       E𝒯.ev-var (trans (lookE-η Θ b lb) (cong just (sym (bdp-discT B 0 (node a (cons (node v nil) b nil))))))
