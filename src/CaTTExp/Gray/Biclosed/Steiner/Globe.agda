------------------------------------------------------------------------
-- The cells of the globe λDⁿ (S1/S5 of the 𝔖̂ instance).
--
-- λDⁿ has a top cell of degree n and, for each d < n, a source and a
-- target cell of degree d. A cell of degree d + 1 has ∂⁻ = the source
-- cell of degree d and ∂⁺ = the target cell of degree d; cells of
-- degree 0 have no boundary. Each boundary is a single cell (`gb`), and
-- the boundary matrix is its indicator (`gbd`).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.Globe where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum

------------------------------------------------------------------------
-- Fin helpers.

fromℕ : ∀ n → Fin (suc n)
fromℕ zero    = fz
fromℕ (suc n) = fs (fromℕ n)

inject₁ : ∀ {n} → Fin n → Fin (suc n)
inject₁ fz     = fz
inject₁ (fs i) = fs (inject₁ i)

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

toℕ-inject₁ : ∀ {n} (i : Fin n) → toℕ (inject₁ i) ≡ toℕ i
toℕ-inject₁ fz     = refl
toℕ-inject₁ (fs i) = cong suc (toℕ-inject₁ i)

mapM : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mapM f nothing  = nothing
mapM f (just x) = just (f x)

-- lower i is nothing at the maximum and just j at inject₁ j
lower : ∀ {n} → Fin (suc n) → Maybe (Fin n)
lower {zero}  fz     = nothing
lower {suc n} fz     = just fz
lower {suc n} (fs i) = mapM fs (lower i)

lower-max : ∀ n → lower (fromℕ n) ≡ nothing
lower-max zero    = refl
lower-max (suc n) = cong (mapM fs) (lower-max n)

lower-inj : ∀ {n} (i : Fin n) → lower (inject₁ i) ≡ just i
lower-inj {suc n} fz     = refl
lower-inj {suc n} (fs i) = cong (mapM fs) (lower-inj i)

-- a view: every i : Fin (suc n) is the maximum or an inject₁
data LV : ∀ {n} → Fin (suc n) → Set where
  isMax : ∀ {n} → LV (fromℕ n)
  isInj : ∀ {n} (j : Fin n) → LV (inject₁ j)

lv : ∀ {n} (i : Fin (suc n)) → LV i
lv {zero}  fz     = isMax
lv {suc n} fz     = isInj fz
lv {suc n} (fs i) with lv i
... | isMax   = isMax
... | isInj j = isInj (fs j)

------------------------------------------------------------------------
-- Cells.

data GCell (n : Nat) : Set where
  top : GCell n
  src : Fin n → GCell n
  tgt : Fin n → GCell n

eqG : ∀ {n} → GCell n → GCell n → Bool
eqG top     top     = true
eqG (src i) (src j) = eqFin i j
eqG (tgt i) (tgt j) = eqFin i j
eqG _       _       = false

private
  eqG-sound : ∀ {n} {x y : GCell n} → T (eqG x y) → x ≡ y
  eqG-sound {x = top}   {top}   _ = refl
  eqG-sound {x = src i} {src j} p = cong src (eqFin-sound p)
  eqG-sound {x = tgt i} {tgt j} p = cong tgt (eqFin-sound p)
  eqG-sound {x = top}   {src _} ()
  eqG-sound {x = top}   {tgt _} ()
  eqG-sound {x = src _} {top}   ()
  eqG-sound {x = src _} {tgt _} ()
  eqG-sound {x = tgt _} {top}   ()
  eqG-sound {x = tgt _} {src _} ()

  eqG-refl : ∀ {n} (x : GCell n) → T (eqG x x)
  eqG-refl top     = tt
  eqG-refl (src i) = eqFin-refl i
  eqG-refl (tgt i) = eqFin-refl i

  δG : ∀ {n} → GCell n → GCell n → Nat
  δG x y = if eqG x y then 1 else 0

  Σ0 : ∀ {A : Set} (xs : List A) (f : A → Nat) → (∀ x → f x ≡ 0) → Σl xs f ≡ 0
  Σ0 xs f z = trans (Σ-cong xs z) (Σ-0 xs)

  cellsG : ∀ n → List (GCell n)
  cellsG n = top ∷ (map src (allFin n) ++ map tgt (allFin n))

  ΣG : ∀ n (f : GCell n → Nat) → Σl (cellsG n) f ≡ f top + (Σl (allFin n) (λ i → f (src i)) + Σl (allFin n) (λ i → f (tgt i)))
  ΣG n f = cong (f top +_) (trans (Σ-++ (map src (allFin n)) (map tgt (allFin n)) f)
                                  (cong₂ _+_ (Σ-map src (allFin n) f) (Σ-map tgt (allFin n) f)))

  countG : ∀ {n} (x : GCell n) → Σl (cellsG n) (δG x) ≡ 1
  countG {n} top     = trans (ΣG n (δG top)) (cong suc (cong₂ _+_ (Σ-0 (allFin n)) (Σ-0 (allFin n))))
  countG {n} (src i) = trans (ΣG n (δG (src i))) (cong₂ _+_ (count (enumFin n) i) (Σ-0 (allFin n)))
  countG {n} (tgt i) = trans (ΣG n (δG (tgt i))) (trans (cong (_+ Σl (allFin n) (λ j → δG (tgt i) (tgt j))) (Σ-0 (allFin n)))
                                                     (count (enumFin n) i))

enumG : ∀ n → Enum (GCell n)
enumG n = record { els = cellsG n ; eqb = eqG ; eqb-sound = eqG-sound ; eqb-refl = eqG-refl ; count = countG }

------------------------------------------------------------------------
-- Degrees and boundaries.

gdeg : ∀ {n} → GCell n → Nat
gdeg {n} top = n
gdeg (src i) = toℕ i
gdeg (tgt i) = toℕ i

side : ∀ {n} → Bool → Fin n → GCell n
side true  i = tgt i
side false i = src i

-- the boundary cell of a cell of positive degree
gb : ∀ {n} → Bool → GCell n → Maybe (GCell n)
gb {zero}  β top     = nothing
gb {suc n} β top     = just (side β (fromℕ n))
gb β (src fz)        = nothing
gb β (src (fs i))    = just (side β (inject₁ i))
gb β (tgt fz)        = nothing
gb β (tgt (fs i))    = just (side β (inject₁ i))

-- indicator of a Maybe-cell
ind : ∀ {A : Set} (E : Enum A) → Maybe A → A → Nat
ind E nothing  y = 0
ind E (just x) y = δ E x y

gbd : ∀ {n} → Bool → GCell n → GCell n → Nat
gbd {n} β x = ind (enumG n) (gb β x)
