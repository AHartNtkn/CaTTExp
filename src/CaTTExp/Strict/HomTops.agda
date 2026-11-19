------------------------------------------------------------------------
-- The top chain of the total cell T of a pasting context, hom by hom.
--
-- For a pasting context with homs h₁ … hₙ, T's top chain (degree
-- N = Σ dim hₖ) is the product of the top chains of the homs:
--
--   topT-prod : chainT sg N hs ≈ prodL (map topsH hs)
--
-- where topsH h is the set of cells of h of its top dimension.
------------------------------------------------------------------------
module CaTTExp.Strict.HomTops where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L using (==-true)
open import CaTTExp.Strict.Tensor
open import CaTTExp.Strict.TotalCell using (Ph; Ch; HC; chainT-cons; total-cell)
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Products of lists of bags.

prodL : List Bag → Bag
prodL []       = [] ∷ []
prodL (X ∷ Xs) = prod X (prodL Xs)

-- The cells of a hom of its top dimension.
topsH : Hom → Bag
topsH h = Ph h true (hd h)

Ph-top : ∀ h b → Ph h b (hd h) ≡ topsH h
Ph-top h b rewrite ==-true (hd h) = refl

------------------------------------------------------------------------
-- Picking one term out of sumB.

private
  data Split (i j a b : Nat) : Set where
    left  : ∀ d → i ≡ suc (a + d) → Split i j a b
    right : ∀ d → j ≡ suc (b + d) → Split i j a b

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  split : ∀ i j a b → i + j ≡ a + b → (i ≡ a → ⊥) → Split i j a b
  split zero    j zero    b e ne = ⊥-elim (ne refl)
  split zero    j (suc a) b e ne = right a (trans e (cong suc (+-comm a b)))
  split (suc i) j zero    b e ne = left i refl
  split (suc i) j (suc a) b e ne with split i j a b (suc-inj e) (λ q → ne (cong suc q))
  ... | left d q  = left d (cong suc q)
  ... | right d q = right d q

  sumB-zero : ∀ k f → (∀ i j → i + j ≡ k → f i j ≈ []) → sumB k f ≈ []
  sumB-zero k f h = ≈-trans (sumB-ext k f (λ _ _ → []) h) (≡→≈ (sumB-nil k))

sumB-pick : ∀ k f a b → a + b ≡ k → (∀ i j → i + j ≡ k → (i ≡ a → ⊥) → f i j ≈ []) → sumB k f ≈ f a b
sumB-pick zero    f zero    zero    e h = ≈-refl
sumB-pick zero    f zero    (suc b) () h
sumB-pick zero    f (suc a) b       () h
sumB-pick (suc k) f zero    b       e h rewrite e =
  ≈-trans (++-cong (≈-refl {f 0 (suc k)})
                   (sumB-zero k (λ i j → f (suc i) j) (λ i j e′ → h (suc i) j (cong suc e′) (λ ()))))
          (≡→≈ (++-[]R (f 0 (suc k))))
  where
  ++-[]R : ∀ (X : Bag) → X ++ [] ≡ X
  ++-[]R []      = refl
  ++-[]R (x ∷ X) = cong (x ∷_) (++-[]R X)
sumB-pick (suc k) f (suc a) b       e h =
  ≈-trans (++-cong (h 0 (suc k) refl (λ ()))
                   (sumB-pick k (λ i j → f (suc i) j) a b (suc-inj e)
                      (λ i j e′ ne → h (suc i) j (cong suc e′) (λ q → ne (suc-inj q)))))
          ≈-refl

------------------------------------------------------------------------
-- The top of T.

topT-prod : ∀ {Γ} os hs → HC Γ os hs → ∀ sg → Ch hs sg (dimK hs) ≈ prodL (map topsH hs)
topT-prod (o ∷ [])      []       tt        sg = ≈-refl
topT-prod (o ∷ o' ∷ os) (h ∷ hs) (ch , cs) sg =
  ≈-trans (chainT-cons h hs sg (hd h + dimK hs))
  (≈-trans (sumB-pick (hd h + dimK hs) _ (hd h) (dimK hs) refl zero-off)
  (≈-trans (prod-congˡ (Ch hs (flipN (hd h) sg) (dimK hs)) (≡→≈ (Ph-top h sg)))
           (prod-congʳ (topsH h) (topT-prod (o' ∷ os) hs cs (flipN (hd h) sg)))))
  where
  cT = total-cell (o' ∷ os) hs cs
  zero-off : ∀ i j → i + j ≡ hd h + dimK hs → (i ≡ hd h → ⊥) →
             prod (Ph h sg i) (Ch hs (flipN i sg) j) ≈ []
  zero-off i j e ne with split i j (hd h) (dimK hs) e ne
  ... | left d refl  = prod-congˡ (Ch hs (flipN i sg) j) (above ch sg d)
  ... | right d refl = ≈-trans (prod-congʳ (Ph h sg i) (above cT (flipN i sg) d)) (≡→≈ (prod-nilʳ (Ph h sg i)))
topT-prod (_ ∷ []) (_ ∷ _) ()
topT-prod (_ ∷ _ ∷ _) [] ()
topT-prod [] _ ()
