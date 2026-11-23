------------------------------------------------------------------------
-- Marks on context entries (notes/invertibility-markings.md §1.2):
-- inv, ps, and grpd_k (on objects). The same three marks as
-- CaTTExp.Gray.Marks, as a type of their own so that every instance of
-- the binder kernel shares it.
--
-- The binder kernel does not interpret marks. A marked entry
-- Γ ▸[ ms ] A constrains what may be substituted for it: each mark
-- m ∈ ms must hold of the substituted term, as decided by the kernel's
-- `mark` parameter (CaTTExp.Binder.TypingWith).
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Binder.Mark where

data Mark : Set where
  minv mps : Mark
  mgrpd    : Nat → Mark

_==M_ : Mark → Mark → Bool
minv    ==M minv    = true
mps     ==M mps     = true
mgrpd k ==M mgrpd l = k ==ℕ l
_       ==M _       = false

==M-sound : ∀ m n → T (m ==M n) → m ≡ n
==M-sound minv      minv      _ = refl
==M-sound mps       mps       _ = refl
==M-sound (mgrpd k) (mgrpd l) p = cong mgrpd (==ℕ-sound k l p)

_==Ms_ : List Mark → List Mark → Bool
[]       ==Ms []       = true
(m ∷ ms) ==Ms (n ∷ ns) = (m ==M n) ∧ (ms ==Ms ns)
_        ==Ms _        = false

==Ms-sound : ∀ ms ns → T (ms ==Ms ns) → ms ≡ ns
==Ms-sound []       []       _ = refl
==Ms-sound (m ∷ ms) (n ∷ ns) p with m ==M n in e
... | true = cong₂ _∷_ (==M-sound m n (subst T (sym e) tt)) (==Ms-sound ms ns p)

==M-refl : ∀ m → T (m ==M m)
==M-refl minv      = tt
==M-refl mps       = tt
==M-refl (mgrpd k) = ==ℕ-refl k

==Ms-refl : ∀ ms → T (ms ==Ms ms)
==Ms-refl []       = tt
==Ms-refl (m ∷ ms) with m ==M m | ==M-refl m
... | true | _ = ==Ms-refl ms

-- Membership.
_∈M_ : Mark → List Mark → Bool
m ∈M []       = false
m ∈M (n ∷ ns) = (m ==M n) ∨ (m ∈M ns)
