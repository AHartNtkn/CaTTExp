------------------------------------------------------------------------
-- Maps of codes from closed matrices, checked by computation.
--
-- `mkMap M cd ca cc` builds a Map from a matrix M given boolean
-- certificates (normally `tt`) that M preserves degree, augmentation,
-- and commutes with ∂^±, each checked over the finite bases.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.CheckMap (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code)
open import CaTTExp.Gray.Biclosed.Steiner.Maps nmFB

allb : ∀ {A : Set} → List A → (A → Bool) → Bool
allb []       p = true
allb (x ∷ xs) p = p x ∧ allb xs p

private
  ∨-elim : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
  ∨-elim {true}  _ = inj₁ tt
  ∨-elim {false} p = inj₂ p

  all-at : ∀ {A : Set} (E : Enum A) (p : A → Bool) a xs → T (allb xs p) →
           (Σl xs (δ E a) ≡ 0 → ⊥) → T (p a)
  all-at E p a []       _ nz = ⊥-elim (nz refl)
  all-at E p a (x ∷ xs) h nz = go (eqb E a x) refl
    where
      go : ∀ b → eqb E a x ≡ b → T (p a)
      go true  e with eqb-sound E {a} {x} (subst T (sym e) tt)
      ... | refl = ∧-fst h
      go false e = all-at E p a xs (∧-snd {p x} h)
                     (λ z → nz (trans (cong (λ b → (if b then 1 else 0) + Σl xs (δ E a)) e) z))

-- a check over a finite enumeration holds everywhere
allE : ∀ {A : Set} (E : Enum A) (p : A → Bool) → T (allb (els E) p) → ∀ a → T (p a)
allE E p h a = all-at E p a (els E) h (λ z → one≢zero (trans (sym (count E a)) z))
  where one≢zero : 1 ≡ 0 → ⊥
        one≢zero ()

module _ {K L : Code} (M : Mat K L) where
  degB : Bool
  degB = allb (els′ K) (λ k → allb (els′ L) (λ l → (M k l ==ℕ 0) ∨ (deg L l ==ℕ deg K k)))

  augB : Bool
  augB = allb (els′ K) (λ k → not (deg K k ==ℕ 0) ∨ (Σl (els′ L) (M k) ==ℕ 1))

  chainB : Bool
  chainB = allb (els′ K) (λ k → allb (els′ L) (λ n →
             ((M · ∂ L true) ⊕ (∂ K false · M)) k n ==ℕ ((M · ∂ L false) ⊕ (∂ K true · M)) k n))

  mkMap : T degB → T augB → T chainB → Map K L
  mkMap cd ca cc = record
    { mat = M
    ; mdeg = λ k l → dg k l (∨-elim (allE (enumEl L) _ (allE (enumEl K) _ cd k) l))
    ; maug = λ k z → au k z (∨-elim (allE (enumEl K) _ ca k))
    ; mchain = λ k n → ==ℕ-sound _ _ (allE (enumEl L) _ (allE (enumEl K) _ cc k) n) }
    where
      dg : ∀ k l → T (M k l ==ℕ 0) ⊎ T (deg L l ==ℕ deg K k) → M k l ≡ 0 ⊎ deg L l ≡ deg K k
      dg k l (inj₁ p) = inj₁ (==ℕ-sound _ _ p)
      dg k l (inj₂ p) = inj₂ (==ℕ-sound _ _ p)
      au : ∀ k → deg K k ≡ 0 → T (not (deg K k ==ℕ 0)) ⊎ T (Σl (els′ L) (M k) ==ℕ 1) → Σl (els′ L) (M k) ≡ 1
      au k z (inj₁ p) rewrite z = ⊥-elim p
      au k z (inj₂ p) = ==ℕ-sound _ _ p
