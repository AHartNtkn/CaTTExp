------------------------------------------------------------------------
-- Bags in normal form, and the ADC of a complex given on bags
-- (ledger A5, N3: the strict model of L as a strict ω-category).
--
-- Chains of the complexes of `Strict.Complex` are bags (lists up to
-- `_≈_`). Steiner's ν as a strict ω-category (`Strict.Nu`) wants a
-- cancellative commutative monoid with propositional equality. Sorting
-- gives one: tuples are ordered lexicographically (`_≤T_`, a total
-- order), `sort` is insertion sort, and two bags are ≈ exactly when
-- their sorted forms are equal (`norm-≈`, `sorted-unique`). The monoid
-- `SB` has sorted bags as elements (with their proof of sortedness,
-- which is unique), X ⊕ Y = sort (X ++ Y).
--
-- `BagADC ∂ isB` is then an `ADC` for any boundary ∂ : Bool → Tuple →
-- Bag and any decidable family of basis predicates isB : Nat → Tuple →
-- Bool: ∂^± are extended additively, πⱼ keeps the elements with isB j,
-- and ε counts those with isB 0.
------------------------------------------------------------------------
module CaTTExp.Strict.SortBag where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; tri; tri<; tri≡; tri>; ≤-trans; <→≤; <-irrefl; ≤-<-⊥)
open import CaTTExp.Strict.Tables using (CMon)
open import CaTTExp.Strict.Nu using (ADC)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- The lexicographic order on tuples.

infix 4 _≤T_
data _≤T_ : Tuple → Tuple → Set where
  nil : ∀ {ys} → [] ≤T ys
  lt  : ∀ {x y xs ys} → x < y → (x ∷ xs) ≤T (y ∷ ys)
  eq  : ∀ {x xs ys} → xs ≤T ys → (x ∷ xs) ≤T (x ∷ ys)

≤T-refl : ∀ a → a ≤T a
≤T-refl []       = nil
≤T-refl (x ∷ xs) = eq (≤T-refl xs)

≤T-total : ∀ a b → (a ≤T b) ⊎ (b ≤T a)
≤T-total []       b        = inj₁ nil
≤T-total (x ∷ xs) []       = inj₂ nil
≤T-total (x ∷ xs) (y ∷ ys) with tri x y
... | tri< p    = inj₁ (lt p)
... | tri> p    = inj₂ (lt p)
... | tri≡ refl with ≤T-total xs ys
...   | inj₁ q = inj₁ (eq q)
...   | inj₂ q = inj₂ (eq q)

≤T-antisym : ∀ {a b} → a ≤T b → b ≤T a → a ≡ b
≤T-antisym nil    nil    = refl
≤T-antisym (lt p) (lt q) = ⊥-elim (≤-<-⊥ (<→≤ p) q)
≤T-antisym (lt p) (eq q) = ⊥-elim (<-irrefl p)
≤T-antisym (eq p) (lt q) = ⊥-elim (<-irrefl q)
≤T-antisym {x ∷ _} (eq p) (eq q) = cong (x ∷_) (≤T-antisym p q)

≤T-trans : ∀ {a b c} → a ≤T b → b ≤T c → a ≤T c
≤T-trans nil    _      = nil
≤T-trans (lt p) (lt q) = lt (≤-trans p (<→≤ q))
≤T-trans (lt p) (eq q) = lt p
≤T-trans (eq p) (lt q) = lt q
≤T-trans (eq p) (eq q) = eq (≤T-trans p q)

private
  ≤-prop : ∀ {m n} (p q : m ≤ n) → p ≡ q
  ≤-prop z≤n     z≤n     = refl
  ≤-prop (s≤s p) (s≤s q) = cong s≤s (≤-prop p q)

≤T-prop : ∀ {a b} (p q : a ≤T b) → p ≡ q
≤T-prop nil    nil    = refl
≤T-prop (lt p) (lt q) = cong lt (≤-prop p q)
≤T-prop (lt p) (eq q) = ⊥-elim (<-irrefl p)
≤T-prop (eq p) (lt q) = ⊥-elim (<-irrefl q)
≤T-prop (eq p) (eq q) = cong eq (≤T-prop p q)

------------------------------------------------------------------------
-- Sorted bags.

Sorted : Bag → Set
Sorted []      = ⊤
Sorted (a ∷ X) = All (a ≤T_) X × Sorted X

private
  All-prop : ∀ {P : Tuple → Set} → (∀ a (p q : P a) → p ≡ q) → ∀ X (u v : All P X) → u ≡ v
  All-prop h []      tt       tt       = refl
  All-prop h (x ∷ X) (p , ps) (q , qs) = cong₂ _,_ (h x p q) (All-prop h X ps qs)

Sorted-prop : ∀ X (u v : Sorted X) → u ≡ v
Sorted-prop []      tt       tt       = refl
Sorted-prop (a ∷ X) (p , ps) (q , qs) =
  cong₂ _,_ (All-prop (λ b → ≤T-prop) X p q) (Sorted-prop X ps qs)

ins : Tuple → Bag → Bag
ins a []      = a ∷ []
ins a (b ∷ X) with ≤T-total a b
... | inj₁ _ = a ∷ b ∷ X
... | inj₂ _ = b ∷ ins a X

sort : Bag → Bag
sort []      = []
sort (a ∷ X) = ins a (sort X)

private
  cons-cong : ∀ b {X Y} → X ≈ Y → b ∷ X ≈ b ∷ Y
  cons-cong b p = ++-cong (≈-refl {b ∷ []}) p

  swap2 : ∀ a b X → b ∷ a ∷ X ≈ a ∷ b ∷ X
  swap2 a b X = ++-cong {b ∷ a ∷ []} {a ∷ b ∷ []} {X} {X} (++-comm (b ∷ []) (a ∷ [])) ≈-refl

ins-≈ : ∀ a X → ins a X ≈ a ∷ X
ins-≈ a []      = ≈-refl
ins-≈ a (b ∷ X) with ≤T-total a b
... | inj₁ _ = ≈-refl
... | inj₂ _ = ≈-trans (cons-cong b (ins-≈ a X)) (swap2 a b X)

sort-≈ : ∀ X → sort X ≈ X
sort-≈ []      = ≈-refl
sort-≈ (a ∷ X) = ≈-trans (ins-≈ a (sort X)) (cons-cong a (sort-≈ X))

private
  All-ins : ∀ {P : Tuple → Set} a X → P a → All P X → All P (ins a X)
  All-ins a []      pa _        = pa , tt
  All-ins a (b ∷ X) pa (pb , ps) with ≤T-total a b
  ... | inj₁ _ = pa , pb , ps
  ... | inj₂ _ = pb , All-ins a X pa ps

ins-sorted : ∀ a X → Sorted X → Sorted (ins a X)
ins-sorted a []      _         = tt , tt
ins-sorted a (b ∷ X) (hb , sX) with ≤T-total a b
... | inj₁ ab = (ab , All-map X (λ c bc → ≤T-trans ab bc) hb) , hb , sX
... | inj₂ ba = All-ins {b ≤T_} a X ba hb , ins-sorted a X sX

sort-sorted : ∀ X → Sorted (sort X)
sort-sorted []      = tt
sort-sorted (a ∷ X) = ins-sorted a (sort X) (sort-sorted X)

------------------------------------------------------------------------
-- Sorted bags with the same counts are equal.

private
  sucz : ∀ {n} → suc n ≡ 0 → ⊥
  sucz ()

  cnt-head : ∀ a X → count a (a ∷ X) ≡ suc (count a X)
  cnt-head a X rewrite eqT-refl a = refl

  All-cnt : ∀ {P : Tuple → Set} a Y → (count a Y ≡ 0 → ⊥) → All P Y → P a
  All-cnt a []      nz _        = ⊥-elim (nz refl)
  All-cnt a (y ∷ Y) nz (p , ps) with eqT a y in e
  ... | true  = subst _ (sym (eqT-sound a y (subst T (sym e) tt))) p
  ... | false = All-cnt a Y nz ps

sorted-unique : ∀ X Y → Sorted X → Sorted Y → X ≈ Y → X ≡ Y
sorted-unique []      []      _         _         p = refl
sorted-unique []      (b ∷ Y) _         _         p = ⊥-elim (sucz (sym (trans (at p b) (cnt-head b Y))))
sorted-unique (a ∷ X) []      _         _         p = ⊥-elim (sucz (trans (sym (cnt-head a X)) (at p a)))
sorted-unique (a ∷ X) (b ∷ Y) (ha , sX) (hb , sY) p with ≤T-antisym ab ba
  where
  ba : b ≤T a
  ba = All-cnt {b ≤T_} a (b ∷ Y) (λ z → sucz (trans (sym (cnt-head a X)) (trans (at p a) z))) (≤T-refl b , hb)
  ab : a ≤T b
  ab = All-cnt {a ≤T_} b (a ∷ X) (λ z → sucz (trans (sym (cnt-head b Y)) (trans (sym (at p b)) z))) (≤T-refl a , ha)
... | refl = cong (a ∷_) (sorted-unique X Y sX sY (++-cancelˡ X Y (a ∷ []) p))

sort-id : ∀ X → Sorted X → sort X ≡ X
sort-id X s = sorted-unique (sort X) X (sort-sorted X) s (sort-≈ X)

norm-≈ : ∀ {X Y} → X ≈ Y → sort X ≡ sort Y
norm-≈ {X} {Y} p =
  sorted-unique (sort X) (sort Y) (sort-sorted X) (sort-sorted Y)
    (≈-trans (sort-≈ X) (≈-trans p (≈-sym (sort-≈ Y))))

------------------------------------------------------------------------
-- The monoid of sorted bags.

SB : Set
SB = Σ Bag Sorted

mkSB : Bag → SB
mkSB X = sort X , sort-sorted X

SB-≡ : ∀ (u v : SB) → fst u ≡ fst v → u ≡ v
SB-≡ (X , s) (.X , s′) refl = cong (X ,_) (Sorted-prop X s s′)

mkSB-≈ : ∀ {X Y} → X ≈ Y → mkSB X ≡ mkSB Y
mkSB-≈ p = SB-≡ _ _ (norm-≈ p)

mkSB-id : ∀ (u : SB) → mkSB (fst u) ≡ u
mkSB-id (X , s) = SB-≡ _ _ (sort-id X s)

infixl 6 _⊕S_
_⊕S_ : SB → SB → SB
u ⊕S v = mkSB (fst u ++ fst v)

εS : SB
εS = [] , tt

⊕S-id : ∀ u → εS ⊕S u ≡ u
⊕S-id u = mkSB-id u

⊕S-comm : ∀ u v → u ⊕S v ≡ v ⊕S u
⊕S-comm u v = mkSB-≈ (++-comm (fst u) (fst v))

⊕S-assoc : ∀ u v w → (u ⊕S v) ⊕S w ≡ u ⊕S (v ⊕S w)
⊕S-assoc u v w = mkSB-≈
  (≈-trans (++-cong (sort-≈ (fst u ++ fst v)) (≈-refl {fst w}))
  (≈-trans (++-assoc (fst u) (fst v) (fst w))
           (++-cong (≈-refl {fst u}) (≈-sym (sort-≈ (fst v ++ fst w))))))

-- u ⊕ v, as a bag, is u ++ v up to ≈.
⊕S-≈ : ∀ u v → fst (u ⊕S v) ≈ fst u ++ fst v
⊕S-≈ u v = sort-≈ (fst u ++ fst v)

⊕S-cancel : ∀ u v w → u ⊕S w ≡ v ⊕S w → u ≡ v
⊕S-cancel u v w e =
  SB-≡ u v (sorted-unique (fst u) (fst v) (snd u) (snd v)
    (++-cancelʳ (fst u) (fst v) (fst w)
      (≈-trans (≈-sym (⊕S-≈ u w)) (≈-trans (≡→≈ (cong fst e)) (⊕S-≈ v w)))))

SBMon : CMon
SBMon = record { M = SB ; ε = εS ; _⊕_ = _⊕S_ ; ⊕-id = ⊕S-id ; ⊕-comm = ⊕S-comm ; ⊕-assoc = ⊕S-assoc }

------------------------------------------------------------------------
-- Additive maps of bags induce monoid maps.

module Lift (f : Bag → Bag) (f-cong : ∀ {X Y} → X ≈ Y → f X ≈ f Y)
            (f-++ : ∀ X Y → f (X ++ Y) ≈ f X ++ f Y) (f-[] : f [] ≈ []) where

  F : SB → SB
  F u = mkSB (f (fst u))

  F-ε : F εS ≡ εS
  F-ε = SB-≡ _ _ (trans (norm-≈ f-[]) refl)

  F-⊕ : ∀ u v → F (u ⊕S v) ≡ F u ⊕S F v
  F-⊕ u v = mkSB-≈
    (≈-trans (f-cong (sort-≈ (fst u ++ fst v)))
    (≈-trans (f-++ (fst u) (fst v))
             (≈-sym (++-cong (sort-≈ (f (fst u))) (sort-≈ (f (fst v)))))))

  F-≈ : ∀ u → fst (F u) ≈ f (fst u)
  F-≈ u = sort-≈ (f (fst u))

-- Keep the elements satisfying p.
filt : (Tuple → Bool) → Bag → Bag
filt p = cm (λ x → if p x then x ∷ [] else [])

len : Bag → Nat
len []      = 0
len (_ ∷ X) = suc (len X)

------------------------------------------------------------------------
-- A complex on bags as an ADC.

module BagADC (∂ : Bool → Tuple → Bag) (isB : Nat → Tuple → Bool) where

  private
    module D⁺ = Lift (cm (∂ true))  (λ {X} {Y} → cm-cong (∂ true) X Y)  (λ X Y → ≡→≈ (cm-++ (∂ true) X Y))  ≈-refl
    module D⁻ = Lift (cm (∂ false)) (λ {X} {Y} → cm-cong (∂ false) X Y) (λ X Y → ≡→≈ (cm-++ (∂ false) X Y)) ≈-refl
    module Pj (j : Nat) = Lift (filt (isB j)) (λ {X} {Y} → cm-cong _ X Y) (λ X Y → ≡→≈ (cm-++ _ X Y)) ≈-refl

  dS : Bool → SB → SB
  dS true  = D⁺.F
  dS false = D⁻.F

  πS : Nat → SB → SB
  πS j = Pj.F j

  augS : SB → Nat
  augS u = len (filt (isB 0) (fst u))

  adc : ADC
  adc = record
    { 𝕄 = SBMon
    ; cancel = ⊕S-cancel
    ; ∂⁺ = D⁺.F ; ∂⁻ = D⁻.F
    ; ∂⁺-ε = D⁺.F-ε ; ∂⁻-ε = D⁻.F-ε
    ; ∂⁺-⊕ = D⁺.F-⊕ ; ∂⁻-⊕ = D⁻.F-⊕
    ; π = πS ; π-ε = λ j → Pj.F-ε j ; π-⊕ = λ j → Pj.F-⊕ j
    ; aug = augS }
