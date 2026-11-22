------------------------------------------------------------------------
-- The four-cube pair of r3 item 41, computed in 𝒮 (D7g examples).
--
-- In ν(λD¹⊗λD¹⊗λD¹⊗λD¹) write a 1-path from (s,s,s,s) to (t,t,t,t) as
-- the order in which coordinates change, and i for the square that
-- swaps positions i, i+1.  From 4321 to 1234 the 2-cells
--   u = 212321,  v = 123212
-- are parallel; their top chains are U and V below (computed with the
-- conventions of Codes: Leibniz signs, ∂⁻ = source).  A 3-cell between
-- them is a map m : λD³ → K₄ whose faces have top chains U and V.
-- `no-uv` and `no-vu`: there is none, in either direction.  The proof
-- reads off three (resp. two) coordinates of m's chain condition.
-- No postulates.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.FourCube (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Globe
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (globe; Code)
open import CaTTExp.Gray.Biclosed.Steiner.Maps nmFB

K₄ : Code
K₄ = globe 1 ∷ globe 1 ∷ globe 1 ∷ globe 1 ∷ []

private
  T′ S′ G′ : GCell 1
  T′ = top
  S′ = src fz
  G′ = tgt fz

c : GCell 1 → GCell 1 → GCell 1 → GCell 1 → El K₄
c a b d e = a , b , d , e , tt

------------------------------------------------------------------------
-- Sums against a matrix column certified by computation.

allb : ∀ {A : Set} → List A → (A → Bool) → Bool
allb []       p = true
allb (x ∷ xs) p = p x ∧ allb xs p

Σ-certify : ∀ {A : Set} (xs : List A) (f b e : A → Nat) → T (allb xs (λ l → b l ==ℕ e l)) →
            Σl xs (λ l → f l * b l) ≡ Σl xs (λ l → f l * e l)
Σ-certify []       f b e _ = refl
Σ-certify (x ∷ xs) f b e p =
  cong₂ _+_ (cong (f x *_) (==ℕ-sound (b x) (e x) (∧-fst p))) (Σ-certify xs f b e (∧-snd {b x ==ℕ e x} p))

Σ-certifyˡ : ∀ {A : Set} (xs : List A) (f b e : A → Nat) → T (allb xs (λ l → b l ==ℕ e l)) →
             Σl xs (λ l → b l * f l) ≡ Σl xs (λ l → e l * f l)
Σ-certifyˡ []       f b e _ = refl
Σ-certifyˡ (x ∷ xs) f b e p =
  cong₂ _+_ (cong (_* f x) (==ℕ-sound (b x) (e x) (∧-fst p))) (Σ-certifyˡ xs f b e (∧-snd {b x ==ℕ e x} p))

module _ (L : Code) (f : El L → Nat) where
  Σ0 : Σl (els′ L) (λ l → f l * 0) ≡ 0
  Σ0 = go (els′ L)
    where go : ∀ xs → Σl xs (λ l → f l * 0) ≡ 0
          go []       = refl
          go (x ∷ xs) = cong₂ _+_ (*-zero (f x)) (go xs)

  Σ1 : ∀ a → Σl (els′ L) (λ l → f l * δE L l a) ≡ f a
  Σ1 a = Σ-δʳ (enumEl L) a f

  Σ2 : ∀ a b → Σl (els′ L) (λ l → f l * (δE L l a + δE L l b)) ≡ f a + f b
  Σ2 a b = trans (Σ-cong (els′ L) (λ l → distribˡ (f l) (δE L l a) (δE L l b)))
                 (trans (Σ-+ (els′ L) _ _) (cong₂ _+_ (Σ1 a) (Σ1 b)))

------------------------------------------------------------------------
-- The two 2-cells.

U V : El K₄ → Nat
U l = δE K₄ l (c S′ T′ T′ G′) + δE K₄ l (c S′ T′ S′ T′) + δE K₄ l (c S′ G′ T′ T′)
    + δE K₄ l (c T′ G′ G′ T′) + δE K₄ l (c T′ G′ T′ S′) + δE K₄ l (c T′ T′ S′ S′)
V l = δE K₄ l (c S′ S′ T′ T′) + δE K₄ l (c S′ T′ G′ T′) + δE K₄ l (c T′ G′ G′ T′)
    + δE K₄ l (c T′ T′ G′ S′) + δE K₄ l (c T′ S′ T′ S′) + δE K₄ l (c G′ T′ T′ S′)

------------------------------------------------------------------------
-- The chain condition of a 3-cell at a 2-cell n.

top₃ s₃ t₃ : El (D 3)
top₃ = top , tt
s₃ = src (fs (fs fz)) , tt
t₃ = tgt (fs (fs fz)) , tt

module Cell (m : Map (D 3) K₄) where
  x : El K₄ → Nat
  x = mat m top₃

  side3 : ∀ α n → Σl (els′ (D 3)) (λ j → bd (D 3) α top₃ j * mat m j n) ≡ mat m (if α then t₃ else s₃) n
  side3 true  n = trans (Σ-certifyˡ (els′ (D 3)) (λ j → mat m j n) (bd (D 3) true top₃) (δE (D 3) t₃) tt)
                        (Σ-δ (enumEl (D 3)) t₃ (λ j → mat m j n))
  side3 false n = trans (Σ-certifyˡ (els′ (D 3)) (λ j → mat m j n) (bd (D 3) false top₃) (δE (D 3) s₃) tt)
                        (Σ-δ (enumEl (D 3)) s₃ (λ j → mat m j n))

  -- the chain condition at n, with ∂^± of n's cofaces given as eP, eM
  chainAt : ∀ n (eP eM : El K₄ → Nat) →
            T (allb (els′ K₄) (λ l → bd K₄ true l n ==ℕ eP l)) →
            T (allb (els′ K₄) (λ l → bd K₄ false l n ==ℕ eM l)) →
            Σl (els′ K₄) (λ l → x l * eP l) + mat m s₃ n ≡ Σl (els′ K₄) (λ l → x l * eM l) + mat m t₃ n
  chainAt n eP eM cP cM =
    trans (sym (cong₂ _+_ (Σ-certify (els′ K₄) x (λ l → bd K₄ true l n) eP cP) (side3 false n)))
    (trans (mchain m top₃ n)
           (cong₂ _+_ (Σ-certify (els′ K₄) x (λ l → bd K₄ false l n) eM cM) (side3 true n)))

  -- the coordinates used
  e-TTSS : mat m s₃ (c T′ T′ S′ S′) ≡ x (c T′ T′ T′ S′) + x (c T′ T′ S′ T′) + mat m t₃ (c T′ T′ S′ S′)
  e-TTSS = trans (sym (cong (_+ mat m s₃ (c T′ T′ S′ S′)) (Σ0 K₄ x)))
           (trans (chainAt (c T′ T′ S′ S′) (λ _ → 0) (λ l → δE K₄ l (c T′ T′ T′ S′) + δE K₄ l (c T′ T′ S′ T′)) tt tt)
                  (cong (_+ mat m t₃ (c T′ T′ S′ S′)) (Σ2 K₄ x (c T′ T′ T′ S′) (c T′ T′ S′ T′))))

  e-TTGS : x (c T′ T′ T′ S′) + mat m s₃ (c T′ T′ G′ S′) ≡ x (c T′ T′ G′ T′) + mat m t₃ (c T′ T′ G′ S′)
  e-TTGS = trans (sym (cong (_+ mat m s₃ (c T′ T′ G′ S′)) (Σ1 K₄ x (c T′ T′ T′ S′))))
           (trans (chainAt (c T′ T′ G′ S′) (λ l → δE K₄ l (c T′ T′ T′ S′)) (λ l → δE K₄ l (c T′ T′ G′ T′)) tt tt)
                  (cong (_+ mat m t₃ (c T′ T′ G′ S′)) (Σ1 K₄ x (c T′ T′ G′ T′))))

  e-STST : x (c S′ T′ T′ T′) + mat m s₃ (c S′ T′ S′ T′) ≡ x (c T′ T′ S′ T′) + mat m t₃ (c S′ T′ S′ T′)
  e-STST = trans (sym (cong (_+ mat m s₃ (c S′ T′ S′ T′)) (Σ1 K₄ x (c S′ T′ T′ T′))))
           (trans (chainAt (c S′ T′ S′ T′) (λ l → δE K₄ l (c S′ T′ T′ T′)) (λ l → δE K₄ l (c T′ T′ S′ T′)) tt tt)
                  (cong (_+ mat m t₃ (c S′ T′ S′ T′)) (Σ1 K₄ x (c T′ T′ S′ T′))))

  e-TGGT : mat m s₃ (c T′ G′ G′ T′) ≡ x (c T′ T′ G′ T′) + x (c T′ G′ T′ T′) + mat m t₃ (c T′ G′ G′ T′)
  e-TGGT = trans (sym (cong (_+ mat m s₃ (c T′ G′ G′ T′)) (Σ0 K₄ x)))
           (trans (chainAt (c T′ G′ G′ T′) (λ _ → 0) (λ l → δE K₄ l (c T′ T′ G′ T′) + δE K₄ l (c T′ G′ T′ T′)) tt tt)
                  (cong (_+ mat m t₃ (c T′ G′ G′ T′)) (Σ2 K₄ x (c T′ T′ G′ T′) (c T′ G′ T′ T′))))

------------------------------------------------------------------------
-- No 3-cell u ⇒ v, and none v ⇒ u.

private
  s≢z : ∀ {k} → suc k ≡ 0 → ⊥
  s≢z ()

  +-zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r zero    b e = e
  +-zero-r (suc a) b ()

  +-zero-l : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l zero    b e = refl
  +-zero-l (suc a) b ()

no-uv : ∀ (m : Map (D 3) K₄) → (∀ n → mat m s₃ n ≡ U n) → (∀ n → mat m t₃ n ≡ V n) → ⊥
no-uv m hs ht = s≢z (trans stst (cong (_+ 0) xTTST0))
  where
    open Cell m
    -- x(TTTS) = x(TTGT) + 1
    ttgs : x (c T′ T′ T′ S′) + 0 ≡ x (c T′ T′ G′ T′) + 1
    ttgs = trans (cong (x (c T′ T′ T′ S′) +_) (sym (hs (c T′ T′ G′ S′))))
                 (trans e-TTGS (cong (x (c T′ T′ G′ T′) +_) (ht (c T′ T′ G′ S′))))
    -- 1 = x(TTTS) + x(TTST)
    ttss : 1 ≡ x (c T′ T′ T′ S′) + x (c T′ T′ S′ T′) + 0
    ttss = trans (sym (hs (c T′ T′ S′ S′)))
                 (trans e-TTSS (cong (x (c T′ T′ T′ S′) + x (c T′ T′ S′ T′) +_) (ht (c T′ T′ S′ S′))))
    xTTTS-pos : Σ Nat (λ k → x (c T′ T′ T′ S′) ≡ suc k)
    xTTTS-pos = x (c T′ T′ G′ T′) ,
      trans (sym (+-zero _)) (trans ttgs (+-suc (x (c T′ T′ G′ T′)) 0 ⟨trans⟩ cong suc (+-zero _)))
      where _⟨trans⟩_ = trans
    xTTST0 : x (c T′ T′ S′ T′) ≡ 0
    xTTST0 with xTTTS-pos
    ... | k , e = +-zero-r k (x (c T′ T′ S′ T′))
                    (cong pred (trans (sym (cong (λ z → z + x (c T′ T′ S′ T′)) e))
                                      (trans (sym (+-zero _)) (sym ttss))))
      where pred : Nat → Nat
            pred zero = zero
            pred (suc n) = n
    -- x(STTT) + 1 = x(TTST)
    stst : suc (x (c S′ T′ T′ T′)) ≡ x (c T′ T′ S′ T′) + 0
    stst = trans (sym (+-suc (x (c S′ T′ T′ T′)) 0 ⟨trans⟩ cong suc (+-zero _)))
           (trans (cong (x (c S′ T′ T′ T′) +_) (sym (hs (c S′ T′ S′ T′))))
           (trans e-STST (cong (x (c T′ T′ S′ T′) +_) (ht (c S′ T′ S′ T′)))))
      where _⟨trans⟩_ = trans

no-vu : ∀ (m : Map (D 3) K₄) → (∀ n → mat m s₃ n ≡ V n) → (∀ n → mat m t₃ n ≡ U n) → ⊥
no-vu m hs ht = s≢z (trans (sym (trans (+-suc (x (c T′ T′ T′ S′)) 0) (cong suc (+-zero _)))) ttgs′)
  where
    open Cell m
    _⟨trans⟩_ = trans
    -- 1 = x(TTGT) + x(TGTT) + 1, so x(TTGT) = 0
    tggt : 1 ≡ x (c T′ T′ G′ T′) + x (c T′ G′ T′ T′) + 1
    tggt = trans (sym (hs (c T′ G′ G′ T′)))
                 (trans e-TGGT (cong (x (c T′ T′ G′ T′) + x (c T′ G′ T′ T′) +_) (ht (c T′ G′ G′ T′))))
    xTTGT0 : x (c T′ T′ G′ T′) ≡ 0
    xTTGT0 = +-zero-l (x (c T′ T′ G′ T′)) (x (c T′ G′ T′ T′))
               (+-cancelʳ 1 (sym tggt))
    -- x(TTTS) + 1 = x(TTGT) + 0 = 0
    ttgs′ : x (c T′ T′ T′ S′) + 1 ≡ 0
    ttgs′ = trans (cong (x (c T′ T′ T′ S′) +_) (sym (hs (c T′ T′ G′ S′))))
            (trans e-TTGS (trans (cong (x (c T′ T′ G′ T′) +_) (ht (c T′ T′ G′ S′)))
                                 (trans (+-zero _) xTTGT0)))
