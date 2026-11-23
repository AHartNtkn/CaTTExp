------------------------------------------------------------------------
-- Maps of augmented directed complexes between codes (S2 of the 𝔖̂
-- instance, notes/gray-model-formal-plan.md).
--
-- A map K → L is an ℕ-matrix (so it preserves the positive cone) that
-- preserves degrees and the augmentation and commutes with ∂:
--   f ∂⁺ + ∂⁻ f = f ∂⁻ + ∂⁺ f,
-- which is ∂ f = f ∂ for ∂ = ∂⁺ − ∂⁻, written without subtraction.
-- Matrices act on the right: (f · g) k m = Σ_l f k l · g l m is "f then
-- g". Maps compose, identities are Kronecker deltas, and the category
-- laws hold for the pointwise equality of matrices.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Maps (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes
open Codes nmFB public

Mat : Code → Code → Set
Mat K L = El K → El L → Nat

infixl 7 _·_
_·_ : ∀ {K L M} → Mat K L → Mat L M → Mat K M
_·_ {L = L} f g k m = Σl (els′ L) (λ l → f k l * g l m)

infixl 6 _⊕_
_⊕_ : ∀ {K L} → Mat K L → Mat K L → Mat K L
(f ⊕ g) k l = f k l + g k l

_≐_ : ∀ {K L} → Mat K L → Mat K L → Set
f ≐ g = ∀ k l → f k l ≡ g k l

------------------------------------------------------------------------
-- Matrix algebra.

module _ {K L M : Code} where
  ·-cong : ∀ {f f′ : Mat K L} {g g′ : Mat L M} → f ≐ f′ → g ≐ g′ → (f · g) ≐ (f′ · g′)
  ·-cong ef eg k m = Σ-cong (els′ L) (λ l → cong₂ _*_ (ef k l) (eg l m))

  ·-⊕ʳ : ∀ (f : Mat K L) (g h : Mat L M) → (f · (g ⊕ h)) ≐ ((f · g) ⊕ (f · h))
  ·-⊕ʳ f g h k m = trans (Σ-cong (els′ L) (λ l → distribˡ (f k l) (g l m) (h l m)))
                         (Σ-+ (els′ L) _ _)

  ·-⊕ˡ : ∀ (f g : Mat K L) (h : Mat L M) → ((f ⊕ g) · h) ≐ ((f · h) ⊕ (g · h))
  ·-⊕ˡ f g h k m = trans (Σ-cong (els′ L) (λ l → distribʳ (f k l) (g k l) (h l m)))
                         (Σ-+ (els′ L) _ _)

·-assoc : ∀ {K L M N} (f : Mat K L) (g : Mat L M) (h : Mat M N) → ((f · g) · h) ≐ (f · (g · h))
·-assoc {K} {L} {M} {N} f g h k n =
  trans (Σ-cong (els′ M) (λ m → Σ-*ʳ (els′ L) (h m n) (λ l → f k l * g l m)))
  (trans (Σ-swap (els′ M) (els′ L) (λ m l → f k l * g l m * h m n))
  (Σ-cong (els′ L) (λ l → trans (Σ-cong (els′ M) (λ m → *-assoc (f k l) (g l m) (h m n)))
                                 (sym (Σ-*ˡ (els′ M) (f k l) (λ m → g l m * h m n))))))

δ-·ˡ : ∀ {K L} (f : Mat K L) → (δE K · f) ≐ f
δ-·ˡ {K} f k l = Σ-δ (enumEl K) k (λ k′ → f k′ l)

δ-·ʳ : ∀ {K L} (f : Mat K L) → (f · δE L) ≐ f
δ-·ʳ {K} {L} f k l = Σ-δʳ (enumEl L) l (f k)

------------------------------------------------------------------------
-- Maps.

∂ : ∀ K → Bool → Mat K K
∂ K = bd K

record Map (K L : Code) : Set where
  field
    mat    : Mat K L
    mdeg   : ∀ k l → mat k l ≡ 0 ⊎ deg L l ≡ deg K k
    maug   : ∀ k → deg K k ≡ 0 → Σl (els′ L) (mat k) ≡ 1
    mchain : ((mat · ∂ L true) ⊕ (∂ K false · mat)) ≐ ((mat · ∂ L false) ⊕ (∂ K true · mat))
open Map public

record _≈M_ {K L} (f g : Map K L) : Set where
  constructor ≈m
  field ≈mat : mat f ≐ mat g
open _≈M_ public

------------------------------------------------------------------------
-- Identities.

private
  δ-cases : ∀ {A} (E : Enum A) x y → δ E x y ≡ 0 ⊎ x ≡ y
  δ-cases E x y = go (eqb E x y) refl
    where go : ∀ b → eqb E x y ≡ b → δ E x y ≡ 0 ⊎ x ≡ y
          go true  e = inj₂ (eqb-sound E (subst T (sym e) tt))
          go false e = inj₁ (cong (λ b → if b then 1 else 0) e)

idMap : ∀ K → Map K K
idMap K = record
  { mat = δE K
  ; mdeg = λ k l → dg (δ-cases (enumEl K) k l)
  ; maug = λ k _ → count (enumEl K) k
  ; mchain = λ k m →
      trans (cong₂ _+_ (δ-·ˡ (∂ K true) k m) (δ-·ʳ (∂ K false) k m))
      (trans (+-comm (∂ K true k m) (∂ K false k m))
             (sym (cong₂ _+_ (δ-·ˡ (∂ K false) k m) (δ-·ʳ (∂ K true) k m)))) }
  where
    dg : ∀ {k l} → δE K k l ≡ 0 ⊎ k ≡ l → δE K k l ≡ 0 ⊎ deg K l ≡ deg K k
    dg (inj₁ z)    = inj₁ z
    dg (inj₂ refl) = inj₂ refl

------------------------------------------------------------------------
-- Composition ("f then g").

private
  Σ-zero : ∀ {A : Set} (xs : List A) (f : A → Nat) → (∀ x → f x ≡ 0) → Σl xs f ≡ 0
  Σ-zero xs f z = trans (Σ-cong xs z) (Σ-0 xs)

  *-zeroˡ : ∀ {a} b → a ≡ 0 → a * b ≡ 0
  *-zeroˡ b refl = refl

  *-zeroʳ : ∀ a {b} → b ≡ 0 → a * b ≡ 0
  *-zeroʳ a refl = *-zero a

module _ {K L M : Code} (f : Map K L) (g : Map L M) where
  private
    F = mat f
    G = mat g

  ∘deg : ∀ k m → (F · G) k m ≡ 0 ⊎ deg M m ≡ deg K k
  ∘deg k m = go (deg M m ==ℕ deg K k) refl
    where
      go : ∀ b → (deg M m ==ℕ deg K k) ≡ b → (F · G) k m ≡ 0 ⊎ deg M m ≡ deg K k
      go true  e = inj₂ (==-sound _ _ (subst T (sym e) tt))
      go false e = inj₁ (Σ-zero (els′ L) _ term)
        where
          term : ∀ l → F k l * G l m ≡ 0
          term l with mdeg f k l | mdeg g l m
          ... | inj₁ z  | _      = *-zeroˡ (G l m) z
          ... | inj₂ _  | inj₁ z = *-zeroʳ (F k l) z
          ... | inj₂ d₁ | inj₂ d₂ = ⊥-elim (==-false _ _ e (trans d₂ d₁))

  ∘aug : ∀ k → deg K k ≡ 0 → Σl (els′ M) ((F · G) k) ≡ 1
  ∘aug k dk =
    trans (Σ-swap (els′ M) (els′ L) (λ m l → F k l * G l m))
    (trans (Σ-cong (els′ L) (λ l → sym (Σ-*ˡ (els′ M) (F k l) (G l))))
    (trans (Σ-cong (els′ L) term) (maug f k dk)))
    where
      term : ∀ l → F k l * Σl (els′ M) (G l) ≡ F k l
      term l with mdeg f k l
      ... | inj₁ z = trans (*-zeroˡ _ z) (sym z)
      ... | inj₂ d = trans (cong (F k l *_) (maug g l (trans d dk))) (*-one (F k l))

  -- f∂⁺g… : the chain condition of the composite, by cancellation.
  ∘chain : ((F · G · ∂ M true) ⊕ (∂ K false · (F · G))) ≐ ((F · G · ∂ M false) ⊕ (∂ K true · (F · G)))
  ∘chain k n = +-cancelʳ (X k n + Y k n) total
    where
      X = F · (∂ L false · G)
      Y = F · (∂ L true · G)
      -- g's condition, premultiplied by f
      eg : ∀ k n → (F · (G · ∂ M true)) k n + X k n ≡ (F · (G · ∂ M false)) k n + Y k n
      eg k n = trans (sym (·-⊕ʳ F (G · ∂ M true) (∂ L false · G) k n))
               (trans (·-cong {f = F} (λ _ _ → refl) (mchain g) k n)
                      (·-⊕ʳ F (G · ∂ M false) (∂ L true · G) k n))
      -- f's condition, postmultiplied by g
      ef : ∀ k n → ((F · ∂ L true) · G) k n + ((∂ K false · F) · G) k n
                 ≡ ((F · ∂ L false) · G) k n + ((∂ K true · F) · G) k n
      ef k n = trans (sym (·-⊕ˡ (F · ∂ L true) (∂ K false · F) G k n))
               (trans (·-cong {g = G} {g′ = G} (mchain f) (λ _ _ → refl) k n)
                      (·-⊕ˡ (F · ∂ L false) (∂ K true · F) G k n))
      a1 = ·-assoc F G (∂ M true) k n
      a2 = ·-assoc F G (∂ M false) k n
      a3 = ·-assoc (∂ K false) F G k n
      a4 = ·-assoc (∂ K true) F G k n
      a5 = ·-assoc F (∂ L true) G k n
      a6 = ·-assoc F (∂ L false) G k n
      total : ((F · G · ∂ M true) k n + (∂ K false · (F · G)) k n) + (X k n + Y k n)
            ≡ ((F · G · ∂ M false) k n + (∂ K true · (F · G)) k n) + (X k n + Y k n)
      total =
        let p = (F · G · ∂ M true) k n ; q = (∂ K false · (F · G)) k n
            p′ = (F · G · ∂ M false) k n ; q′ = (∂ K true · (F · G)) k n
            x = X k n ; y = Y k n
            -- eg: p + x ≡ p′ + y ; ef: y + q ≡ x + q′
            e1 : p + x ≡ p′ + y
            e1 = trans (cong (_+ x) a1) (trans (eg k n) (cong (_+ y) (sym a2)))
            e2 : y + q ≡ x + q′
            e2 = trans (cong₂ _+_ (sym a5) (sym a3)) (trans (ef k n) (cong₂ _+_ a6 a4))
        in trans (+-inter p q x y)
           (trans (cong₂ _+_ e1 (trans (+-comm q y) e2))
           (trans (+-inter p′ y x q′)
           (trans (cong₂ _+_ (+-comm p′ x) (+-comm y q′))
           (trans (+-inter x p′ q′ y)
           (trans (+-comm (x + q′) (p′ + y))
           (trans (cong ((p′ + y) +_) (+-comm x q′))
           (trans (+-inter p′ y q′ x)
                  (cong ((p′ + q′) +_) (+-comm y x)))))))))

infixr 9 _∘M_
_∘M_ : ∀ {K L M} → Map L M → Map K L → Map K M
g ∘M f = record { mat = mat f · mat g ; mdeg = ∘deg f g ; maug = ∘aug f g ; mchain = ∘chain f g }

------------------------------------------------------------------------
-- Category laws.

∘M-idl : ∀ {K L} (f : Map K L) → (idMap L ∘M f) ≈M f
∘M-idl f = ≈m (δ-·ʳ (mat f))

∘M-idr : ∀ {K L} (f : Map K L) → (f ∘M idMap K) ≈M f
∘M-idr f = ≈m (δ-·ˡ (mat f))

∘M-assoc : ∀ {K L M N} (h : Map M N) (g : Map L M) (f : Map K L) → ((h ∘M g) ∘M f) ≈M (h ∘M (g ∘M f))
∘M-assoc h g f = ≈m (λ k n → sym (·-assoc (mat f) (mat g) (mat h) k n))

∘M-cong : ∀ {K L M} {g g′ : Map L M} {f f′ : Map K L} → g ≈M g′ → f ≈M f′ → (g ∘M f) ≈M (g′ ∘M f′)
∘M-cong eg ef = ≈m (·-cong (≈mat ef) (≈mat eg))
