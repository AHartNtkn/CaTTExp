------------------------------------------------------------------------
-- The decision procedure run on small terms (factors and generator
-- labels are natural numbers).
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Examples where

open import CaTTExp.Gray.NBE.Base

_≟N_ : (x y : Nat) → Dec (x ≡ y)
zero  ≟N zero  = yes refl
zero  ≟N suc _ = no λ ()
suc _ ≟N zero  = no λ ()
suc x ≟N suc y with x ≟N y
... | yes refl = yes refl
... | no n     = no λ { refl → n refl }

open import CaTTExp.Gray.NBE.Syntax Nat Nat
open import CaTTExp.Gray.NBE.Decide Nat Nat _≟N_ _≟N_

a : Formula
a = 1 ∷ []

g0 : Triple
g0 = tri [] (gen 0) []

-- η-expansion of a generator: κ_a(T_a[g] ; e_a) normalizes to g.
eta-exp : normalize (tri [] (cur Ld a (2 ∷ []) (wrap Ld a g0 ∷ evT Ld a (2 ∷ []) ∷ [])) [] ∷ [])
        ≡ g0 ∷ []
eta-exp = refl

-- β: T_a[κ_a(g)] ; e_a normalizes to g.
beta-red : normalize (tri a (cur Ld a (2 ∷ []) (g0 ∷ [])) [] ∷ evT Ld a (2 ∷ []) ∷ [])
         ≡ g0 ∷ []
beta-red = refl

-- N: a preceding generator is absorbed into a following curry.
nat : normalize (g0 ∷ tri [] (cur Rd a (2 ∷ []) (tri [] (gen 1) [] ∷ [])) [] ∷ [])
    ≡ tri [] (cur Rd a (2 ∷ []) (tri [] (gen 0) a ∷ tri [] (gen 1) [] ∷ [])) [] ∷ []
nat = refl

-- Two different generators are not convertible.
distinct : (g0 ∷ []) ≈ (tri [] (gen 1) [] ∷ []) → ⊥
distinct p with ≈→nf p
... | ()
