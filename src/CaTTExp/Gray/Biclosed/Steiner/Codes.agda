------------------------------------------------------------------------
-- Codes for finite directed complexes (S1 of the 𝔖̂ instance,
-- notes/gray-model-formal-plan.md).
--
-- A finite basis (`FB`) is a finite type of cells with a degree and the
-- two boundary parts ∂⁻, ∂⁺ as ℕ-matrices. An atomic code is a globe λDⁿ or a named
-- basis (a parameter, for named shapes). A code is a list of atomic
-- codes, read as their Gray tensor: the basis of K = a₁ … aₙ is the
-- tuples (b₁, …, bₙ), of degree Σ deg bᵢ, with the Leibniz rule
--   ∂^α (b , x) = ∂^α b ⊗ x + b ⊗ ∂^{α′} x,   α′ = α flipped iff deg b is odd
-- (Steiner 2004 §7; conventions.md §2). So ⊗ of codes is ++, strictly
-- associative and unital, and the n-ary tensors needed by the Day
-- multicategory are concatenation.
--
-- λDⁿ has a top cell and a source and a target cell of each degree
-- d < n (`Globe`). Every cell of degree d ≥ 1 has ∂⁻ = the source cell
-- of degree d − 1 and ∂⁺ = the target cell of degree d − 1.
--
-- Steiner's hypotheses (loop-freeness, unitality) are not needed for
-- the Model instance and are not stated here.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.Codes where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Globe public

record FB : Set₁ where
  field
    Cell  : Set
    enumC : Enum Cell
    fdeg  : Cell → Nat
    fbd   : Bool → Cell → Cell → Nat
open FB public

even : Nat → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

flip : Nat → Bool → Bool
flip d α = if even d then α else not α

-- λDⁿ
globeFB : Nat → FB
globeFB n = record { Cell = GCell n ; enumC = enumG n ; fdeg = gdeg ; fbd = gbd }

data AC : Set where
  globe : Nat → AC
  named : Nat → AC

Code : Set
Code = List AC

module Codes (nmFB : Nat → FB) where

  fbA : AC → FB
  fbA (globe n) = globeFB n
  fbA (named i) = nmFB i

  Ix : AC → Set
  Ix a = Cell (fbA a)

  degA : ∀ a → Ix a → Nat
  degA a = fdeg (fbA a)

  bdA : ∀ a → Bool → Ix a → Ix a → Nat
  bdA a = fbd (fbA a)

  enumA : ∀ a → Enum (Ix a)
  enumA a = enumC (fbA a)

  El : Code → Set
  El []      = ⊤
  El (a ∷ K) = Ix a × El K

  enumEl : ∀ K → Enum (El K)
  enumEl []      = enum⊤
  enumEl (a ∷ K) = enum× (enumA a) (enumEl K)

  els′ : ∀ K → List (El K)
  els′ K = els (enumEl K)

  δE : ∀ K → El K → El K → Nat
  δE K = δ (enumEl K)

  deg : ∀ K → El K → Nat
  deg []      tt      = 0
  deg (a ∷ K) (i , x) = degA a i + deg K x

  -- ∂^α as a matrix: bd K α x y is the coefficient of y in ∂^α x.
  bd : ∀ K → Bool → El K → El K → Nat
  bd []      α tt      tt      = 0
  bd (a ∷ K) α (i , x) (j , y) =
    bdA a α i j * δE K x y + δ (enumA a) i j * bd K (flip (degA a i) α) x y

  -- The unit code and the globes.
  unitC : Code
  unitC = []

  D : Nat → Code
  D n = globe n ∷ []
