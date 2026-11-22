------------------------------------------------------------------------
-- Finite universes from a positive conserved weight (ledger S3a,
-- obligation (b) of notes/uniform-checker.md §1.7).
--
-- r10 Response 3 and (K65) make each layer finite the same way: words
-- are lists of letters from a finite alphabet, every letter has
-- positive weight, and every equation preserves the total weight. So
-- the words of a class all lie among the words of one weight, and
-- there are finitely many of those. This module proves that once:
-- from a finite alphabet with positive weights and a weight-preserving
-- one-step relation (given with its neighbour list), it builds the
-- Presentation of Present.agda, with U x the words of x's weight.
--
-- What each degree must still supply: its alphabet of contextual
-- letters (finite, by the (K65) bounds), the weights, and the one-step
-- relation with its neighbour list.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; _≤_; z≤n; s≤s; lengthL)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Arith
open import CaTTExp.Uniform.Grid using (∈-filter⁺; ∈-filter⁻)
open import CaTTExp.Uniform.Present using (Presentation)

module CaTTExp.Uniform.WordPresent
  {L : Set} (_≟L_ : (a b : L) → Dec (a ≡ b))
  (alph : List L) (alph-has : ∀ l → l ∈L alph)
  -- a letter l weighs suc (wt l), so every weight is positive
  (wt : L → Nat)
  where

Word : Set
Word = List L

_≟W_ : (x y : Word) → Dec (x ≡ y)
[]       ≟W []       = yes refl
[]       ≟W (_ ∷ _)  = no λ ()
(_ ∷ _)  ≟W []       = no λ ()
(a ∷ as) ≟W (b ∷ bs) with a ≟L b | as ≟W bs
... | yes refl | yes refl = yes refl
... | no ne    | _        = no λ { refl → ne refl }
... | yes _    | no ne    = no λ { refl → ne refl }

weight : Word → Nat
weight []       = zero
weight (l ∷ ls) = suc (wt l) + weight ls

length≤weight : ∀ ls → lengthL ls ≤ weight ls
length≤weight []       = z≤n
length≤weight (l ∷ ls) = s≤s (≤-trans (length≤weight ls) (≤-+ˡ (wt l) (weight ls)))

-- All words of length exactly k, and of length at most k.
ofLen : Nat → List Word
ofLen zero    = [] ∷ []
ofLen (suc k) = concatK (mapK (λ l → mapK (l ∷_) (ofLen k)) alph)

ofLen-has : ∀ ls → ls ∈L ofLen (lengthL ls)
ofLen-has []       = here
ofLen-has (l ∷ ls) =
  ∈-concat⁺ (mapK (λ l′ → mapK (l′ ∷_) (ofLen (lengthL ls))) alph)
    (∈-map⁺ (l ∷_) (ofLen-has ls))
    (∈-map⁺ (λ l′ → mapK (l′ ∷_) (ofLen (lengthL ls))) (alph-has l))

upTo : Nat → List Word
upTo zero    = ofLen zero
upTo (suc k) = ofLen (suc k) ++ upTo k

upTo-has : ∀ {k} ls → lengthL ls ≤ k → ls ∈L upTo k
upTo-has {zero}  [] z≤n = here
upTo-has {suc k} ls le with lengthL ls ≟N suc k
... | yes e = ∈-++ˡ (upTo k) (subst (λ n → ls ∈L ofLen n) e (ofLen-has ls))
... | no ne = ∈-++ʳ (ofLen (suc k)) (upTo-has ls (shrink le ne))
  where
  shrink : ∀ {a b} → a ≤ suc b → ¬ (a ≡ suc b) → a ≤ b
  shrink {zero}  z≤n      _  = z≤n
  shrink {suc a} {zero}  (s≤s z≤n) ne′ = ⊥-elim (ne′ refl)
  shrink {suc a} {suc b} (s≤s le′) ne′ = s≤s (shrink le′ λ e → ne′ (cong suc e))

-- The words of weight exactly n: a finite list containing every one.
sameW : Nat → Word → Bool
sameW n y = isYes (weight y ≟N n)

ofWeight : Nat → List Word
ofWeight n = filter (sameW n) (upTo n)

ofWeight-has : ∀ ls → ls ∈L ofWeight (weight ls)
ofWeight-has ls =
  ∈-filter⁺ (sameW (weight ls)) (upTo (weight ls))
    (upTo-has ls (length≤weight ls)) (isYes-complete (weight ls ≟N weight ls) refl)

ofWeight-sound : ∀ {n ls} → ls ∈L ofWeight n → weight ls ≡ n
ofWeight-sound {n} {ls} m = isYes-sound (weight ls ≟N n) (snd (∈-filter⁻ (sameW n) (upTo n) m))

ofWeight-complete : ∀ {n} ls → weight ls ≡ n → ls ∈L ofWeight n
ofWeight-complete ls refl = ofWeight-has ls

------------------------------------------------------------------------
-- A weight-preserving one-step relation gives a Presentation.

module Steps
  (Step     : Word → Word → Set)
  (nb       : Word → List Word)
  (nb-sound : ∀ {x y} → y ∈L nb x → Step x y ⊎ Step y x)
  (nb-fwd   : ∀ {x y} → Step x y → y ∈L nb x)
  (nb-bwd   : ∀ {x y} → Step y x → y ∈L nb x)
  (step-wt  : ∀ {x y} → Step x y → weight y ≡ weight x)
  where

  presentation : Presentation Word
  presentation = record
    { _≟_      = _≟W_
    ; Step     = Step
    ; nb       = nb
    ; nb-sound = nb-sound
    ; nb-fwd   = nb-fwd
    ; nb-bwd   = nb-bwd
    ; U        = λ x → ofWeight (weight x)
    ; U-has    = ofWeight-has
    ; U-closed = λ {x} {y} {z} my mz →
        ofWeight-complete {weight x} z (trans (nb-wt (nb-sound mz)) (ofWeight-sound {weight x} my))
    ; U-step   = λ s → cong ofWeight (sym (step-wt s))
    }
    where
    nb-wt : ∀ {y z} → Step y z ⊎ Step z y → weight z ≡ weight y
    nb-wt (inj₁ s) = step-wt s
    nb-wt (inj₂ s) = sym (step-wt s)
