------------------------------------------------------------------------
-- F2c, step (P1) of lemmas 3–5, first part: the labels of a pasting
-- context's own tree are pairwise distinct.
--
--   nd-idTree : ND (idTree τ)
--
-- `ND a`: no label of a occurs twice (among a node's objects, between
-- the objects and the branches, and between different branches). This
-- is what lets the filler read the substitution λ : Θ_τ → Γ off a
-- single pass over the pairs `zipLab (idTree τ) N`: every variable of
-- Θ_τ has one position, so `find` returns the label of N there.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LabDistinct where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; labT; labCs; idTree)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.LabRange using (labT-range; labCs-range; InR; _⊎_; inl; inr)

private
  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  not-true : ∀ b → (b ≡ true → ⊥) → b ≡ false
  not-true true  f = ⊥-elim (f refl)
  not-true false f = refl

  -- order
  le-lt : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
  le-lt zero    b       (suc c) p q = tt
  le-lt a       b       zero    p ()
  le-lt (suc a) zero    (suc c) () q
  le-lt (suc a) (suc b) (suc c) p q = le-lt a b c p q

  lt-le : ∀ a b c → T (a <ℕ b) → T (b <ℕ suc c) → T (a <ℕ c)
  lt-le zero    (suc b) (suc c) p q = tt
  lt-le zero    (suc b) zero    p ()
  lt-le (suc a) (suc b) (suc c) p q = lt-le a b c p q
  lt-le (suc a) (suc b) zero    p ()
  lt-le a       zero    c       () q

  irr : ∀ a → T (a <ℕ a) → ⊥
  irr zero    ()
  irr (suc a) p = irr a p

  le-suc : ∀ a → T (a <ℕ suc (suc a))
  le-suc zero    = tt
  le-suc (suc a) = le-suc a

  lt-suc : ∀ a → T (a <ℕ suc a)
  lt-suc zero    = tt
  lt-suc (suc a) = lt-suc a

  -- y in [a, b) and b ≤ c, c ≤ y is absurd
  out : ∀ y a b → InR a b y → ∀ c → T (b <ℕ suc c) → T (c <ℕ suc y) → ⊥
  out y a b (_ , q) c p r = irr y (lt-le y b y q (le-trans b c y p r))
    where
    le-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
    le-trans zero    b       c       p q = tt
    le-trans (suc a) zero    c       () q
    le-trans (suc a) (suc b) zero    p ()
    le-trans (suc a) (suc b) (suc c) p q = le-trans a b c p q

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

------------------------------------------------------------------------
-- No repeated labels.

NodupL : List Nat → Set
NodupL []       = ⊤
NodupL (x ∷ xs) = (memL x xs ≡ false) × NodupL xs

mutual
  ND : LT → Set
  ND (lt os cs) = NodupL os × (∀ y → memL y os ≡ true → memCs y cs ≡ false) × NDs cs

  NDs : List LT → Set
  NDs []       = ⊤
  NDs (c ∷ cs) = ND c × (∀ y → mem y c ≡ true → memCs y cs ≡ false) × NDs cs

------------------------------------------------------------------------
-- The tree of a pasting context.

private
  -- labels of labT t x n are x or in [n, n′)
  inT : ∀ t x n y → mem y (fst (labT t x n)) ≡ true → (y ≡ x) ⊎ InR n (snd (labT t x n)) y
  inT t x n = fst (labT-range t x n)

  monoT : ∀ t x n → T (n <ℕ suc (snd (labT t x n)))
  monoT t x n = snd (snd (labT-range t x n))

  inCs : ∀ cs n y → (memL y (fst (labCs cs n)) ∨ memCs y (fst (snd (labCs cs n)))) ≡ true →
         InR n (snd (snd (labCs cs n))) y
  inCs cs n = fst (labCs-range cs n)

  monoCs : ∀ cs n → T (n <ℕ suc (snd (snd (labCs cs n))))
  monoCs cs n = snd (snd (labCs-range cs n))

mutual
  nd-labT : ∀ t x n → T (x <ℕ n) → ND (fst (labT t x n))
  nd-labT (node cs) x n p with labCs cs n | labCs-range cs n | nd-labCs cs n
  ... | os , ls , n' | sub , _ , _ | ndo , dis , nds =
    (x∉os , ndo) , disj , nds
    where
    x∉ : ∀ m → (memL x os ∨ memCs x ls) ≡ m → m ≡ true → ⊥
    x∉ m e refl with sub x e
    ... | (q , _) = irr x (lt-le x n x p q)

    x∉os : memL x os ≡ false
    x∉os = not-true _ (λ h → x∉ _ refl (∨-inl _ _ h))

    disj : ∀ y → ((y ==ℕ x) ∨ memL y os) ≡ true → memCs y ls ≡ false
    disj y m with ∨-split (y ==ℕ x) (memL y os) m
    ... | inr h = dis y h
    ... | inl h with ==ℕ-sound y x (≡-T h)
    ...   | refl = not-true _ (λ h' → x∉ _ refl (∨-inr (memL y os) _ h'))

  nd-labCs : ∀ cs n → NodupL (fst (labCs cs n))
                    × (∀ y → memL y (fst (labCs cs n)) ≡ true → memCs y (fst (snd (labCs cs n))) ≡ false)
                    × NDs (fst (snd (labCs cs n)))
  nd-labCs [] n = tt , (λ y ()) , tt
  nd-labCs (c ∷ cs) n
    with labT c (suc n) (suc (suc n)) | inT c (suc n) (suc (suc n)) | monoT c (suc n) (suc (suc n))
       | nd-labT c (suc n) (suc (suc n)) (lt-suc (suc n))
  ... | l , n₁ | lsub | lmono | ndl
    with labCs cs n₁ | inCs cs n₁ | monoCs cs n₁ | nd-labCs cs n₁
  ...   | os , ls , n₂ | sub | mono | ndo , dis , nds =
    (n∉os , ndo) , disj , (ndl , l∩ls , nds)
    where
    lab-l : ∀ y → mem y l ≡ true → T (n <ℕ y) × T (y <ℕ n₁)
    lab-l y m with lsub y m
    ... | inl refl = lt-suc n , lt-le (suc n) (suc (suc n)) n₁ (lt-suc (suc n)) lmono
    ... | inr (p , q) = lt-le n (suc (suc n)) y (le-suc n) p , q

    lab-r : ∀ y → (memL y os ∨ memCs y ls) ≡ true → T (n₁ <ℕ suc y)
    lab-r y m = fst (sub y m)

    -- n < n₁
    n<n₁ : T (n <ℕ n₁)
    n<n₁ = lt-le n (suc (suc n)) n₁ (le-suc n) lmono

    n∉os : memL n os ≡ false
    n∉os = not-true _ (λ h → irr n (lt-le n n₁ n n<n₁ (lab-r n (∨-inl _ _ h))))

    l∩ls : ∀ y → mem y l ≡ true → memCs y ls ≡ false
    l∩ls y m = not-true _ (λ h → irr y (lt-le y n₁ y (snd (lab-l y m)) (lab-r y (∨-inr (memL y os) _ h))))

    disj : ∀ y → ((y ==ℕ n) ∨ memL y os) ≡ true → (mem y l ∨ memCs y ls) ≡ false
    disj y m with ∨-split (y ==ℕ n) (memL y os) m
    ... | inl h with ==ℕ-sound y n (≡-T h)
    ...   | refl = not-true _ λ h' → case (∨-split (mem y l) (memCs y ls) h')
      where
      case : (mem y l ≡ true) ⊎ (memCs y ls ≡ true) → ⊥
      case (inl a) = irr y (fst (lab-l y a))
      case (inr b) = irr y (lt-le y n₁ y n<n₁ (lab-r y (∨-inr (memL y os) _ b)))
    disj y m | inr h = not-true _ λ h' → case (∨-split (mem y l) (memCs y ls) h')
      where
      case : (mem y l ≡ true) ⊎ (memCs y ls ≡ true) → ⊥
      case (inl a) = irr y (lt-le y n₁ y (snd (lab-l y a)) (lab-r y (∨-inl _ _ h)))
      case (inr b) with dis y h
      ... | e = true≢false (trans (sym b) e)
        where
        true≢false : true ≡ false → ⊥
        true≢false ()

------------------------------------------------------------------------

nd-idTree : ∀ τ → ND (idTree τ)
nd-idTree τ = nd-labT τ 0 1 tt
