------------------------------------------------------------------------
-- F2c toward (1′): the labelled tree of a pasting context carries
-- every variable of it.
--
--   lab-all : mem y (idTree τ) ≡ (y <ℕ len (ctxOf τ))
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LabRange where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; labT; labCs; idTree)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.Labels using (bool-ext)
open import CaTTExp.GlobularTotal.LabEx using (B)

-- Exported, since labT-range's statement uses it.
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

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

  -- a ≤ b as a < suc b
  _≤_ : Nat → Nat → Set
  a ≤ b = T (a <ℕ suc b)

  ≤-refl : ∀ a → a ≤ a
  ≤-refl zero    = tt
  ≤-refl (suc a) = ≤-refl a

  ≤-trans : ∀ a b c → a ≤ b → b ≤ c → a ≤ c
  ≤-trans zero    b       c       p q = tt
  ≤-trans (suc a) zero    c       () q
  ≤-trans (suc a) (suc b) zero    p ()
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

  ≤-suc : ∀ a → a ≤ suc a
  ≤-suc zero    = tt
  ≤-suc (suc a) = ≤-suc a

  <→≤ : ∀ a b → T (a <ℕ b) → suc a ≤ b
  <→≤ zero    (suc b) p = tt
  <→≤ (suc a) (suc b) p = <→≤ a b p
  <→≤ a       zero    ()

  ≤-<-trans : ∀ a b c → a ≤ b → T (b <ℕ c) → T (a <ℕ c)
  ≤-<-trans zero    b       (suc c) p q = tt
  ≤-<-trans (suc a) (suc b) (suc c) p q = ≤-<-trans a b c p q
  ≤-<-trans a       b       zero    p ()
  ≤-<-trans (suc a) zero    (suc c) () q

  <-irr : ∀ a → T (a <ℕ a) → ⊥
  <-irr zero    ()
  <-irr (suc a) p = <-irr a p

  -- y not below a, so a ≤ y
  not<→≤ : ∀ y a → (y <ℕ a) ≡ false → a ≤ y
  not<→≤ y       zero    e = tt
  not<→≤ zero    (suc a) ()
  not<→≤ (suc y) (suc a) e = not<→≤ y a e

  ≢→suc : ∀ y n → (y ==ℕ n) ≡ false → n ≤ y → suc n ≤ y
  ≢→suc zero    zero    () p
  ≢→suc (suc y) zero    e  p = tt
  ≢→suc zero    (suc n) e  ()
  ≢→suc (suc y) (suc n) e  p = ≢→suc y n e p

InR : Nat → Nat → Nat → Set
InR a b y = (a ≤ y) × T (y <ℕ b)

mutual
  labT-range : ∀ t x n →
      (∀ y → mem y (fst (labT t x n)) ≡ true → (y ≡ x) ⊎ InR n (snd (labT t x n)) y)
    × (∀ y → (y ≡ x) ⊎ InR n (snd (labT t x n)) y → mem y (fst (labT t x n)) ≡ true)
    × (n ≤ snd (labT t x n))
  labT-range (node cs) x n with labCs cs n | labCs-range cs n
  ... | os , ls , n' | sub , sup , mono = ⊆ , ⊇ , mono
    where
    ⊆ : ∀ y → ((((y ==ℕ x) ∨ memL y os) ∨ memCs y ls) ≡ true) → (y ≡ x) ⊎ InR n n' y
    ⊆ y m with ∨-split ((y ==ℕ x) ∨ memL y os) (memCs y ls) m
    ... | inr mc = inr (sub y (∨-inr (memL y os) _ mc))
    ... | inl mo with ∨-split (y ==ℕ x) (memL y os) mo
    ...   | inl h = inl (==ℕ-sound y x (≡-T h))
    ...   | inr h = inr (sub y (∨-inl _ _ h))

    ⊇ : ∀ y → (y ≡ x) ⊎ InR n n' y → (((y ==ℕ x) ∨ memL y os) ∨ memCs y ls) ≡ true
    ⊇ y (inl refl) = ∨-inl _ _ (∨-inl _ _ (T-≡ (==ℕ-refl y)))
    ⊇ y (inr r) with ∨-split (memL y os) (memCs y ls) (sup y r)
    ... | inl h = ∨-inl _ _ (∨-inr (y ==ℕ x) _ h)
    ... | inr h = ∨-inr ((y ==ℕ x) ∨ memL y os) _ h

  labCs-range : ∀ cs n →
      (∀ y → (memL y (fst (labCs cs n)) ∨ memCs y (fst (snd (labCs cs n)))) ≡ true →
             InR n (snd (snd (labCs cs n))) y)
    × (∀ y → InR n (snd (snd (labCs cs n))) y →
             (memL y (fst (labCs cs n)) ∨ memCs y (fst (snd (labCs cs n)))) ≡ true)
    × (n ≤ snd (snd (labCs cs n)))
  labCs-range [] n = (λ y ()) , (λ y r → ⊥-elim (<-irr n (≤-<-trans n y n (fst r) (snd r)))) , ≤-refl n
  labCs-range (c ∷ cs) n with labT c (suc n) (suc (suc n)) | labT-range c (suc n) (suc (suc n))
  ... | l , n₁ | lsub , lsup , lmono with labCs cs n₁ | labCs-range cs n₁
  ...   | os , ls , n₂ | sub , sup , mono = ⊆ , ⊇ , n≤n₂
    where
    n≤n₂ : n ≤ n₂
    n≤n₂ = ≤-trans n (suc (suc n)) n₂ (≤-trans n (suc n) (suc (suc n)) (≤-suc n) (≤-suc (suc n)))
             (≤-trans (suc (suc n)) n₁ n₂ lmono mono)

    sn<n₂ : T (suc n <ℕ n₂)
    sn<n₂ = ≤-trans (suc (suc n)) n₁ n₂ lmono mono

    n<n₂ : T (n <ℕ n₂)
    n<n₂ = ≤-<-trans n (suc n) n₂ (≤-suc n) sn<n₂

    n≤n₁ : n ≤ n₁
    n≤n₁ = ≤-trans n (suc (suc n)) n₁ (≤-trans n (suc n) (suc (suc n)) (≤-suc n) (≤-suc (suc n))) lmono

    <≤ : ∀ y → T (y <ℕ n₁) → T (y <ℕ n₂)
    <≤ y p = ≤-<-trans (suc y) n₁ (suc n₂) (<→≤ y n₁ p) mono

    from-rest : ∀ y → InR n₁ n₂ y → InR n n₂ y
    from-rest y (p , q) = ≤-trans n n₁ y n≤n₁ p , q

    ⊆ : ∀ y → (((y ==ℕ n) ∨ memL y os) ∨ (mem y l ∨ memCs y ls)) ≡ true → InR n n₂ y
    ⊆ y m with ∨-split ((y ==ℕ n) ∨ memL y os) (mem y l ∨ memCs y ls) m
    ... | inl mo with ∨-split (y ==ℕ n) (memL y os) mo
    ...   | inl h with ==ℕ-sound y n (≡-T h)
    ...     | refl = ≤-refl y , n<n₂
    ⊆ y m | inl mo | inr h = from-rest y (sub y (∨-inl _ _ h))
    ⊆ y m | inr ml with ∨-split (mem y l) (memCs y ls) ml
    ...   | inr h = from-rest y (sub y (∨-inr (memL y os) _ h))
    ...   | inl h with lsub y h
    ...     | inl refl = ≤-suc n , sn<n₂
    ...     | inr (p , q) = ≤-trans n (suc (suc n)) y (≤-trans n (suc n) (suc (suc n)) (≤-suc n) (≤-suc (suc n))) p
                          , <≤ y q

    ⊇ : ∀ y → InR n n₂ y → (((y ==ℕ n) ∨ memL y os) ∨ (mem y l ∨ memCs y ls)) ≡ true
    ⊇ y (p , q) with y ==ℕ n in e
    ... | true = refl
    ... | false with y ==ℕ suc n in e'
    ...   | true rewrite ==ℕ-sound y (suc n) (≡-T e') =
              ∨-inr (memL (suc n) os) _ (∨-inl _ _ (lsup (suc n) (inl refl)))
    ...   | false with y <ℕ n₁ in e''
    ...     | true = ∨-inr (memL y os) _ (∨-inl _ _ (lsup y (inr (ssn≤y , ≡-T e''))))
      where ssn≤y = ≢→suc y (suc n) e' (≢→suc y n e p)
    ...     | false with ∨-split (memL y os) (memCs y ls) (sup y (not<→≤ y n₁ e'' , q))
    ...       | inl h = ∨-inl _ _ h
    ...       | inr h = ∨-inr (memL y os) _ (∨-inr (mem y l) _ h)

private
  ctxOf-build : ∀ τ → ctxOf τ ≡ fst (build τ pss)
  ctxOf-build τ with build τ pss
  ... | _ = refl

lab-all : ∀ τ y → mem y (idTree τ) ≡ (y <ℕ len (ctxOf τ))
lab-all τ y with labT-range τ 0 1 | fst (B τ pss)
... | sub , sup , mono | e
  rewrite ctxOf-build τ | sym e = bool-ext _ _ to from
  where
  n' = snd (labT τ 0 1)

  to : mem y (idTree τ) ≡ true → (y <ℕ n') ≡ true
  to m with sub y m
  ... | inl refl = T-≡ (≤-<-trans 0 0 n' tt mono)
  ... | inr (_ , q) = T-≡ q

  from : (y <ℕ n') ≡ true → mem y (idTree τ) ≡ true
  from q with y ==ℕ 0 in e₀
  ... | true  = sup y (inl (==ℕ-sound y 0 (≡-T e₀)))
  ... | false = sup y (inr (≢→suc y 0 e₀ tt , ≡-T q))
