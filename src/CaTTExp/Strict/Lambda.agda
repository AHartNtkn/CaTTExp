------------------------------------------------------------------------
-- The chain complex λΓ of a context, and multiplicity-freeness of its
-- cells (ledger item A3a).
--
-- λΓ has one basis element (v) per variable v, of degree dim v, and an
-- arrow f : x → y has ∂⁺f = y, ∂⁻f = x. When Γ is *ordered* (every
-- type has variable endpoints x < y of the same type, as in a pasting
-- context), the top chain of every cell of ν(λΓ) has no two elements
-- with the same endpoints; in particular it counts every variable at
-- most once.
--
-- Proof (a cut argument). Let c be the top chain of an (n+1)-cell
-- with source and target tops s and u, so ∂⁺c + s = ∂⁻c + u. Fix a
-- pair (x, y) and let k₀ be the type of x. Count, on both sides, the
-- elements of type k₀ below level y ("low"). Since every arrow in c
-- goes upwards, low(∂⁻c) = low(∂⁺c) + cross(c), where cross(c) counts
-- the arrows of c of base type k₀ that cross level y. So
--     cross(c) + low(u) = low(s) ≤ 1,
-- the last step by induction (s has at most one element of each
-- type). Every element of c with endpoints (x, y) crosses level y.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Strict.Lambda (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.PsFacts 𝕊
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)

------------------------------------------------------------------------
-- Basis elements of degree k.

Basλ : Ctx → Nat → Tuple → Set
Basλ Γ k t = Σ Nat λ v → (t ≡ tup v) × Σ Ty λ A → (lookup Γ v ≡ just A) × (dim A ≡ k)

-- Ordered contexts.
Ordered : Ctx → Set
Ordered Γ = ArrOrd Γ × PsCtx Γ

------------------------------------------------------------------------
-- Order on naturals.

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-+ʳ : ∀ a b → a ≤ a + b
≤-+ʳ zero    b = z≤n
≤-+ʳ (suc a) b = s≤s (≤-+ʳ a b)

≤-suc : ∀ {a b} → a ≤ b → a ≤ suc b
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

------------------------------------------------------------------------
-- Counting the elements of a bag that satisfy a predicate.

ind : (Tuple → Bool) → Tuple → Bag
ind P a = if P a then [] ∷ [] else []

countP : (Tuple → Bool) → Bag → Nat
countP P X = count [] (cm (ind P) X)

countP-++ : ∀ P X Y → countP P (X ++ Y) ≡ countP P X + countP P Y
countP-++ P X Y = trans (cong (count []) (cm-++ (ind P) X Y)) (count-++ [] (cm (ind P) X) (cm (ind P) Y))

countP-≈ : ∀ P {X Y} → X ≈ Y → countP P X ≡ countP P Y
countP-≈ P {X} {Y} p = at (cm-cong (ind P) X Y p) []

countP-∷ : ∀ P a X → countP P (a ∷ X) ≡ (if P a then suc (countP P X) else countP P X)
countP-∷ P a X with P a
... | true  = refl
... | false = refl

countP-single : ∀ P a → countP P (a ∷ []) ≤ 1
countP-single P a rewrite countP-∷ P a [] with P a
... | true  = s≤s z≤n
... | false = z≤n

countP-mono : ∀ {Q} P P′ X → All Q X → (∀ a → Q a → T (P a) → T (P′ a)) → countP P X ≤ countP P′ X
countP-mono P P′ []      _       _ = z≤n
countP-mono P P′ (a ∷ X) (q , qs) f
  rewrite countP-∷ P a X | countP-∷ P′ a X with P a in e | P′ a in e′
... | true  | true  = s≤s (countP-mono P P′ X qs f)
... | true  | false = ⊥-elim (subst T e′ (f a q (subst T (sym e) tt)))
... | false | true  = ≤-suc (countP-mono P P′ X qs f)
... | false | false = countP-mono P P′ X qs f

countP-zero : ∀ {Q} P X → All Q X → (∀ a → Q a → P a ≡ false) → countP P X ≡ 0
countP-zero P []      _        _ = refl
countP-zero P (a ∷ X) (q , qs) f rewrite countP-∷ P a X | f a q = countP-zero P X qs f

count-countP : ∀ a X → count a X ≡ countP (eqT a) X
count-countP a []      = refl
count-countP a (x ∷ X) rewrite countP-∷ (eqT a) x X with eqT a x
... | true  = cong suc (count-countP a X)
... | false = count-countP a X

------------------------------------------------------------------------
-- Endpoint keys: the type of an (n+1)-variable is determined by its
-- endpoints.

Key : Set
Key = Maybe (Nat × Nat)

keyTy : Ty → Key
keyTy (arr _ (var x) (var y)) = just (x , y)
keyTy _                       = nothing

keyM : Maybe Ty → Key
keyM (just A) = keyTy A
keyM nothing  = nothing

key : Ctx → Nat → Key
key Γ v = keyM (lookup Γ v)

keyEq : Key → Key → Bool
keyEq nothing        nothing          = true
keyEq (just (a , b)) (just (c , d))   = (a ==ℕ c) ∧ (b ==ℕ d)
keyEq _              _                = false

keyEq-refl : ∀ k → keyEq k k ≡ true
keyEq-refl nothing        = refl
keyEq-refl (just (a , b)) rewrite ==-refl a | ==-refl b = refl

hasKey : Ctx → Key → Tuple → Bool
hasKey Γ k (v ∷ []) = keyEq (key Γ v) k
hasKey Γ k _        = false

-- A bag with no two elements of the same type.
NRT : Ctx → Bag → Set
NRT Γ X = ∀ k → countP (hasKey Γ k) X ≤ 1

------------------------------------------------------------------------
-- The cut.

private
  ∧-T : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-T {true} {true} _ _ = tt

  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  <-self′ : ∀ n → (n <ℕ n) ≡ false
  <-self′ zero    = refl
  <-self′ (suc n) = <-self′ n

  ≡-==true : ∀ {m n} → (m ==ℕ n) ≡ true → m ≡ n
  ≡-==true {m} {n} = ==→≡ m n

-- Below level h and of key k₀.
low : Ctx → Nat → Key → Tuple → Bool
low Γ h k₀ (v ∷ []) = (v <ℕ h) ∧ keyEq (key Γ v) k₀
low Γ h k₀ _        = false

crossT : Nat → Key → Maybe Ty → Bool
crossT h k₀ (just (arr B (var x) (var y))) = (x <ℕ h) ∧ (not (y <ℕ h) ∧ keyEq (keyTy B) k₀)
crossT h k₀ _                              = false

-- Arrows of base key k₀ crossing level h.
cross : Ctx → Nat → Key → Tuple → Bool
cross Γ h k₀ (w ∷ []) = crossT h k₀ (lookup Γ w)
cross Γ h k₀ _        = false

module _ (Γ : Ctx) (oΓ : Ordered Γ) (h : Nat) (k₀ : Key) where

  private
    ordΓ = fst oΓ
    shp = snd oΓ

  -- One arrow: low(∂⁻w) = low(∂⁺w) + cross(w).
  cut-one : ∀ n w → Basλ Γ (suc n) w →
            countP (low Γ h k₀) (∂λ Γ false w) ≡ countP (low Γ h k₀) (∂λ Γ true w) + countP (cross Γ h k₀) (w ∷ [])
  cut-one n .(v ∷ []) (v , refl , A , eq , dA) with shp v A eq
  ... | ⋆ₚ = ⊥-elim (zero≢suc dA)
    where
    zero≢suc : ∀ {m} → zero ≡ suc m → ⊥
    zero≢suc ()
  ... | arrₚ {B} {x} {y} _ =
    let (lx , ly , xy) = ordΓ v B x y eq in
    helper (x <ℕ h) refl (y <ℕ h) refl lx ly xy
    where
    helper : ∀ bx → (x <ℕ h) ≡ bx → ∀ by → (y <ℕ h) ≡ by →
             lookup Γ x ≡ just B → lookup Γ y ≡ just B → T (x <ℕ y) →
             countP (low Γ h k₀) (∂T false (lookup Γ v)) ≡ countP (low Γ h k₀) (∂T true (lookup Γ v)) + countP (cross Γ h k₀) (tup v ∷ [])
    helper bx ex by ey lx ly xy
      rewrite countP-∷ (cross Γ h k₀) (tup v) [] | eq
            | countP-∷ (low Γ h k₀) (tup x) [] | countP-∷ (low Γ h k₀) (tup y) []
            | lx | ly | ex | ey = fin bx by (keyEq (keyTy B) k₀) ex ey
      where
      fin : ∀ bx by kb → (x <ℕ h) ≡ bx → (y <ℕ h) ≡ by →
            (if bx ∧ kb then 1 else 0) ≡ (if by ∧ kb then 1 else 0) + (if bx ∧ (not by ∧ kb) then 1 else 0)
      fin true  true  true  _ _ = refl
      fin true  false true  _ _ = refl
      fin false false true  _ _ = refl
      fin false true  true  e₁ e₂ = ⊥-elim (subst T e₁ (<-trans x y h xy (subst T (sym e₂) tt)))
      fin true  true  false _ _ = refl
      fin true  false false _ _ = refl
      fin false false false _ _ = refl
      fin false true  false _ _ = refl

  cut : ∀ n c → All (Basλ Γ (suc n)) c →
        countP (low Γ h k₀) (cm (∂λ Γ false) c) ≡ countP (low Γ h k₀) (cm (∂λ Γ true) c) + countP (cross Γ h k₀) c
  cut n []      _        = refl
  cut n (w ∷ c) (b , bs) =
    let L = low Γ h k₀
        C = cross Γ h k₀ in
    trans (countP-++ L (∂λ Γ false w) (cm (∂λ Γ false) c))
   (trans (cong₂ _+_ (cut-one n w b) (cut n c bs))
   (trans (+-interchange (countP L (∂λ Γ true w)) (countP C (w ∷ [])) (countP L (cm (∂λ Γ true) c)) (countP C c))
          (cong₂ _+_ (sym (countP-++ L (∂λ Γ true w) (cm (∂λ Γ true) c)))
                     (sym (countP-++ C (w ∷ []) c)))))

------------------------------------------------------------------------
-- Multiplicity-freeness.

module MF (Γ : Ctx) (oΓ : Ordered Γ) where

  open Cells (∂λ Γ) (Basλ Γ)

  private
    ordΓ = fst oΓ
    shp = snd oΓ

    a+b≤1 : ∀ a b c → a + b ≡ c → c ≤ 1 → a ≤ 1
    a+b≤1 a b c p q = ≤-trans (subst (a ≤_) p (≤-+ʳ a b)) q

    -- Elements of the top chain of an (n+1)-cell are arrows.
    arrow-key : ∀ n w → Basλ Γ (suc n) w → hasKey Γ nothing w ≡ false
    arrow-key n .(v ∷ []) (v , refl , A , eq , dA) with shp v A eq
    ... | ⋆ₚ = ⊥-elim (z≢s dA)
      where
      z≢s : ∀ {m} → zero ≡ suc m → ⊥
      z≢s ()
    ... | arrₚ _ rewrite eq = refl

  NRT-cell : ∀ n X → IsCell n X → NRT Γ (top X)
  NRT-cell zero (base c) (w , p , _) k =
    subst (_≤ 1) (sym (countP-≈ (hasKey Γ k) p)) (countP-single (hasKey Γ k) w)
  NRT-cell (suc n) (step S U c) (cS , cU , _ , ch , a) nothing =
    subst (_≤ 1) (sym (countP-zero (hasKey Γ nothing) c a (arrow-key n))) z≤n
  NRT-cell (suc n) (step S U c) (cS , cU , _ , ch , a) (just (x , y)) =
    ≤-trans (countP-mono (hasKey Γ (just (x , y))) (cross Γ y k₀) c a into)
            (a+b≤1 (countP (cross Γ y k₀) c) (countP L (top U)) (countP L (top S)) balance
                   (≤-trans (countP-mono {λ _ → ⊤} L (hasKey Γ k₀) (top S) (all-tt (top S)) low-key)
                            (NRT-cell n S cS k₀)))
    where
    k₀ = key Γ x
    L = low Γ y k₀
    C = cross Γ y k₀

    all-tt : ∀ X → All (λ _ → ⊤) X
    all-tt []      = tt
    all-tt (_ ∷ X) = tt , all-tt X

    low-key : ∀ t → ⊤ → T (L t) → T (hasKey Γ k₀ t)
    low-key (v ∷ []) _ p = ∧-r (v <ℕ y) _ p

    into : ∀ t → Basλ Γ (suc n) t → T (hasKey Γ (just (x , y)) t) → T (C t)
    into .(v ∷ []) (v , refl , A , eq , dA) p with shp v A eq
    ... | ⋆ₚ = ⊥-elim (z≢s dA)
      where
      z≢s : ∀ {m} → zero ≡ suc m → ⊥
      z≢s ()
    ... | arrₚ {B} {x′} {y′} _ rewrite eq =
      let ex = ==→≡ x′ x (T→≡ (∧-l (x′ ==ℕ x) _ p))
          ey = ==→≡ y′ y (T→≡ (∧-r (x′ ==ℕ x) _ p))
          (lx , ly , xy) = ordΓ v B x′ y′ eq
      in helper ex ey lx xy
      where
      helper : x′ ≡ x → y′ ≡ y → lookup Γ x′ ≡ just B → T (x′ <ℕ y′) →
               T ((x′ <ℕ y) ∧ (not (y′ <ℕ y) ∧ keyEq (keyTy B) (key Γ x)))
      helper refl refl lx xy rewrite lx | <-self′ y′ | keyEq-refl (keyTy B) = ∧-T xy tt

    -- cross(c) + low(u) = low(s).
    balance : countP C c + countP L (top U) ≡ countP L (top S)
    balance =
      +-cancelˡ (countP L (cm (∂λ Γ true) c)) _ _
        (trans (sym (+-assoc (countP L (cm (∂λ Γ true) c)) (countP C c) (countP L (top U))))
        (trans (cong (_+ countP L (top U)) (sym (cut Γ oΓ y k₀ n c a)))
        (trans (sym (countP-++ L (cm (∂λ Γ false) c) (top U)))
        (trans (sym (countP-≈ L ch))
               (countP-++ L (cm (∂λ Γ true) c) (top S))))))

  -- Every variable occurs at most once in the top chain of a cell.
  MF-cell : ∀ n X → IsCell n X → ∀ v → count (tup v) (top X) ≤ 1
  MF-cell n X cX v =
    subst (_≤ 1) (sym (count-countP (tup v) (top X)))
      (≤-trans (countP-mono {λ _ → ⊤} (eqT (tup v)) (hasKey Γ (key Γ v)) (top X) (all-tt (top X)) same)
               (NRT-cell n X cX (key Γ v)))
    where
    all-tt : ∀ X → All (λ _ → ⊤) X
    all-tt []      = tt
    all-tt (_ ∷ X) = tt , all-tt X
    same : ∀ t → ⊤ → T (eqT (tup v) t) → T (hasKey Γ (key Γ v) t)
    same t _ p rewrite sym (eqT-sound (tup v) t p) = subst T (sym (keyEq-refl (key Γ v))) tt
