------------------------------------------------------------------------
-- Every composable tuple of a pasting context has degree at most
-- d = dimK (homs Γ):
--
--   deg-wft : Γ ⊢ps → WFT Γ x y w → deg Γ w ≤ d
--
-- Strict.TopCell.deg-bound is the case x = first, y = last object. In
-- general the first entry of w starts at some object o of Γ, the tuple
-- walks through the homs after o in order (`walk'`, the analogue of
-- TopCell.walk with an arbitrary end), and the dimensions of those homs
-- sum to at most d.
------------------------------------------------------------------------
module CaTTExp.Strict.DegBound where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Pasting
open import CaTTExp.Strict.Bridge
open import CaTTExp.Strict.TopCell
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Arithmetic of sumHd.

private
  le-refl' : ∀ n → T (n <ℕ suc n)
  le-refl' zero    = tt
  le-refl' (suc n) = le-refl' n

  lengthN-++ : ∀ (xs ys : List Nat) → lengthN (xs ++ ys) ≡ lengthN xs + lengthN ys
  lengthN-++ []       ys = refl
  lengthN-++ (x ∷ xs) ys = cong suc (lengthN-++ xs ys)

sumHd-mono : ∀ Γ k a b → T (a <ℕ suc b) → T (sumHd Γ k a <ℕ suc (sumHd Γ k b))
sumHd-mono Γ k zero    b       _ = tt
sumHd-mono Γ k (suc a) zero    ()
sumHd-mono Γ k (suc a) (suc b) p =
  le-add (hd (homAt Γ k)) (hd (homAt Γ k)) (sumHd Γ (suc k) a) (sumHd Γ (suc k) b)
         (le-refl' (hd (homAt Γ k))) (sumHd-mono Γ (suc k) a b p)

-- dropping the first a homs
sumHd-drop : ∀ Γ k a b → T (sumHd Γ (a + k) b <ℕ suc (sumHd Γ k (a + b)))
sumHd-drop Γ k zero    b = le-refl' (sumHd Γ k b)
sumHd-drop Γ k (suc a) b =
  le-trans (sumHd Γ (suc a + k) b) (sumHd Γ (suc k) (a + b)) (hd (homAt Γ k) + sumHd Γ (suc k) (a + b))
    (subst (λ j → T (sumHd Γ j b <ℕ suc (sumHd Γ (suc k) (a + b)))) (+-suc a k) (sumHd-drop Γ (suc k) a b))
    (le-+l (hd (homAt Γ k)) (sumHd Γ (suc k) (a + b)))

------------------------------------------------------------------------
-- A composable tuple from any object walks through the later homs.

walk' : ∀ {Γ} (P : Γ ⊢ps) pre o rest → objL Γ ≡ pre ++ o ∷ rest → ∀ y w →
        WFT Γ o y w → T (lengthN w <ℕ suc (lengthN rest)) × Walk Γ (suc (lengthN pre)) w
walk' P pre o rest eq y [] _ = tt , tt
walk' {Γ} P pre o [] eq y (v ∷ w) (z , ev , p) =
  ⊥-elim (lt-irr o (AllL-∈ pre (Inc-before pre o [] inc) (pairs-last pre o mem)))
  where
  inc = subst Inc eq (Inc-objL Γ)
  mem = subst (λ xs → (o , z) ∈ pairs xs) eq (hom-ends P v ev)
walk' {Γ} P pre o (o' ∷ r) eq y (v ∷ w) (z , ev , p)
  with pairs-unique-src _ (subst Inc eq (Inc-objL Γ)) (subst (λ xs → (o , z) ∈ pairs xs) eq (hom-ends P v ev))
                        (pairs-mid pre o o' r)
... | refl with endsL-inv (lookup Γ v) ev
...   | (A , lv , evA) =
  fst rec ,
  subst T (cong (λ m → m <ℕ suc (hd (homAt Γ (suc (lengthN pre))))) (cong hdimTy (sym lv)))
        (OneHom.v-bound P pre o o' r eq v A lv evA) ,
  subst (λ j → Walk Γ (suc j) w) (lengthN-snoc pre o) (snd rec)
  where
  rec = walk' P (pre ++ o ∷ []) o' r (trans eq (sym (++-assocL pre (o ∷ []) (o' ∷ r)))) y w p

------------------------------------------------------------------------
-- The bound.

private
  ∈-split : ∀ {x : Nat} xs → x ∈ xs → Σ (List Nat) λ pre → Σ (List Nat) λ rest → xs ≡ pre ++ x ∷ rest
  ∈-split (x ∷ xs) hd∈     = [] , xs , refl
  ∈-split (y ∷ xs) (tl∈ m) with ∈-split xs m
  ... | pre , rest , e = y ∷ pre , rest , cong (y ∷_) e

  suc-inj' : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj' refl = refl

deg-wft : ∀ {Γ} → Γ ⊢ps → ∀ x y w → WFT Γ x y w → T (deg Γ w <ℕ suc (dimK (homs Γ)))
deg-wft P x y [] _ = tt
deg-wft {Γ} P x y (v ∷ w) wf@(z , ev , p)
  with ∈-split (objL Γ) (∈-pairs-fst (objL Γ) (hom-ends P v ev))
... | pre , rest , eq with walk' P pre x rest eq y (v ∷ w) wf
...   | lw , W =
  le-trans (deg Γ (v ∷ w)) (sumHd Γ (suc lp) (lengthN (v ∷ w))) (dimK (homs Γ))
    (deg-le Γ (suc lp) (v ∷ w) W)
    (le-trans (sumHd Γ (suc lp) (lengthN (v ∷ w))) (sumHd Γ (suc lp) (lengthN rest)) (dimK (homs Γ))
      (sumHd-mono Γ (suc lp) (lengthN (v ∷ w)) (lengthN rest) lw)
      bound)
  where
  open Shape (shape P) renaming (rest to rest₀)
  lp = lengthN pre
  len₀ : lengthN rest₀ ≡ lp + lengthN rest
  len₀ = suc-inj' (trans (cong lengthN (trans (sym eqo) eq))
                    (trans (lengthN-++ pre (x ∷ rest)) (+-suc lp (lengthN rest))))
  bound : T (sumHd Γ (suc lp) (lengthN rest) <ℕ suc (dimK (homs Γ)))
  bound = subst (λ m → T (sumHd Γ (suc lp) (lengthN rest) <ℕ suc m))
            (sym (trans eqd (cong (sumHd Γ 1) len₀)))
            (subst (λ j → T (sumHd Γ j (lengthN rest) <ℕ suc (sumHd Γ 1 (lp + lengthN rest))))
                   (trans (+-suc lp 0) (cong suc (+-zero lp)))
                   (sumHd-drop Γ 1 lp (lengthN rest)))
