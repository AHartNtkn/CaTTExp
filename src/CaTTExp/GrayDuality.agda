------------------------------------------------------------------------
-- Dualities and the Gray tensor: the sign lemma.
--
-- Companion to notes/closed-structure.md, Part D (ledger item D8).
--
-- A duality D_K of strict ω-categories reverses the cells whose
-- dimension lies in K.  On Steiner complexes it multiplies the boundary
-- of an n-dimensional generator by a sign ε n, with ε n = false
-- ("−1") iff n ∈ K.  The Gray tensor has Leibniz boundary
--   ∂(x ⊗ y) = ∂x ⊗ y + (−1)^|x| x ⊗ ∂y.
-- Comparing coefficients, the canonical generator correspondence
--   D_K(X ⊗ Y) → D_K X ⊗ D_K Y,   x ⊗ y ↦ x ⊗ y        is a chain map  iff  IdC ε
--   D_K(X ⊗ Y) → D_K Y ⊗ D_K X,   x ⊗ y ↦ y ⊗ x        is a chain map  iff  SwapC ε
-- (for all X, Y; the coefficient comparison is in the note and is
-- checked numerically by scripts/duality_check.py).  This module proves
-- the arithmetic consequence: IdC ε holds exactly for the two constant
-- sign patterns and SwapC ε exactly for the two alternating ones, and
-- derives which ambient dualities are symmetries of two-tier L.
------------------------------------------------------------------------
module CaTTExp.GrayDuality where

open import CaTTExp.Prelude

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infix 0 _↔_
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

------------------------------------------------------------------------
-- Signs: true is +1, false is −1.

infixl 7 _·_
_·_ : Bool → Bool → Bool
true  · b = b
false · b = not b

-- (−1)^n
alt : Nat → Bool
alt zero    = true
alt (suc n) = not (alt n)

·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
·-assoc true  b c = refl
·-assoc false true  c = refl
·-assoc false false c = not-not c
  where
  not-not : ∀ c → c ≡ not (not c)
  not-not true  = refl
  not-not false = refl

·-comm : ∀ a b → a · b ≡ b · a
·-comm true  true  = refl
·-comm true  false = refl
·-comm false true  = refl
·-comm false false = refl

·-self : ∀ a b → a · (a · b) ≡ b
·-self true  b = refl
·-self false true  = refl
·-self false false = refl

not-· : ∀ a b → not a · b ≡ not (a · b)
not-· true  true  = refl
not-· true  false = refl
not-· false true  = refl
not-· false false = refl

+-suc : ∀ p q → p + suc q ≡ suc (p + q)
+-suc zero    q = refl
+-suc (suc p) q = cong suc (+-suc p q)

alt-+ : ∀ p q → alt (p + q) ≡ alt p · alt q
alt-+ zero    q = refl
alt-+ (suc p) q = trans (cong not (alt-+ p q)) (sym (not-· (alt p) (alt q)))

------------------------------------------------------------------------
-- Sign patterns.  Only ε n for n ≥ 1 matters (0-cells have no boundary).

Sign : Set
Sign = Nat → Bool

-- identity correspondence is a chain map (coefficients of ∂x ⊗ y, x ⊗ ∂y)
IdC : Sign → Set
IdC ε = (∀ p q → ε (suc p + q) ≡ ε (suc p))
      × (∀ p q → ε (p + suc q) ≡ ε (suc q))

-- swap correspondence x ⊗ y ↦ y ⊗ x is a chain map
SwapC : Sign → Set
SwapC ε = (∀ p q → ε (suc p + q) ≡ alt q · ε (suc p))
        × (∀ p q → alt p · ε (p + suc q) ≡ ε (suc q))

Const : Sign → Set
Const ε = ∀ n → ε (suc n) ≡ ε 1

Alt : Sign → Set
Alt ε = ∀ n → ε (suc (suc n)) ≡ not (ε (suc n))

------------------------------------------------------------------------
-- The sign lemma.

IdC↔Const : ∀ ε → IdC ε ↔ Const ε
IdC↔Const ε = to , from
  where
  to : IdC ε → Const ε
  to (h₁ , _) n = h₁ zero n
  from : Const ε → IdC ε
  from c = (λ p q → trans (c (p + q)) (sym (c p)))
         , (λ p q → trans (cong ε (+-suc p q)) (trans (c (p + q)) (sym (c q))))

-- under Alt, ε (suc n) = (−1)^n · ε 1
alt-closed : ∀ ε → Alt ε → ∀ n → ε (suc n) ≡ alt n · ε 1
alt-closed ε a zero    = refl
alt-closed ε a (suc n) =
  trans (a n) (trans (cong not (alt-closed ε a n)) (sym (not-· (alt n) (ε 1))))

SwapC↔Alt : ∀ ε → SwapC ε ↔ Alt ε
SwapC↔Alt ε = to , from
  where
  to : SwapC ε → Alt ε
  to (h₁ , _) n =
    trans (h₁ zero (suc n))
          (trans (not-· (alt n) (ε 1)) (cong not (sym (h₁ zero n))))
  e = alt-closed ε
  from : Alt ε → SwapC ε
  from a = first , second
    where
    first : ∀ p q → ε (suc p + q) ≡ alt q · ε (suc p)
    first p q =
      trans (e a (p + q))
      (trans (cong (λ s → s · ε 1) (trans (alt-+ p q) (·-comm (alt p) (alt q))))
      (trans (·-assoc (alt q) (alt p) (ε 1))
             (cong (λ s → alt q · s) (sym (e a p)))))
    second : ∀ p q → alt p · ε (p + suc q) ≡ ε (suc q)
    second p q =
      trans (cong (λ s → alt p · s)
                  (trans (cong ε (+-suc p q)) (e a (p + q))))
      (trans (cong (λ s → alt p · (s · ε 1)) (alt-+ p q))
      (trans (cong (λ s → alt p · s) (·-assoc (alt p) (alt q) (ε 1)))
      (trans (·-self (alt p) (alt q · ε 1))
             (sym (e a q)))))

------------------------------------------------------------------------
-- Two-tier L.  An ambient duality D_J (J ⊆ {1,2,…}) acts on the homs by
-- the shifted duality K = J − 1, and if 1 ∈ J it also reverses the
-- order of the objects in a wedge, hence the order of the Gray factors.
-- So D_J maps two-tier L to itself (a symmetry) iff
--   1 ∉ J and the identity correspondence works for K, or
--   1 ∈ J and the swap correspondence works for K;
-- and it maps L to its factor-reversed (oplax) version iff the other way
-- round.  (This reduction is argued in the note; here it is the
-- definition.)

shift : Sign → Sign
shift J n = J (suc n)

Symmetry : Sign → Set
Symmetry J = (J 1 ≡ true × IdC (shift J)) ⊎ (J 1 ≡ false × SwapC (shift J))

ToOplax : Sign → Set
ToOplax J = (J 1 ≡ true × SwapC (shift J)) ⊎ (J 1 ≡ false × IdC (shift J))

-- The four symmetries: J = ∅, {2,3,4,…}, {1,3,5,…} (odd), {1,2,4,6,…}.
symmetry-classification : ∀ J →
  Symmetry J ↔ ((J 1 ≡ true × Const (shift J)) ⊎ (J 1 ≡ false × Alt (shift J)))
symmetry-classification J = to , from
  where
  to : _
  to (inj₁ (j , h)) = inj₁ (j , fst (IdC↔Const (shift J)) h)
  to (inj₂ (j , h)) = inj₂ (j , fst (SwapC↔Alt (shift J)) h)
  from : _
  from (inj₁ (j , h)) = inj₁ (j , snd (IdC↔Const (shift J)) h)
  from (inj₂ (j , h)) = inj₂ (j , snd (SwapC↔Alt (shift J)) h)

-- The four lax/oplax swaps: J = {1}, all, {2,4,6,…} (even), {3,5,7,…}.
to-oplax-classification : ∀ J →
  ToOplax J ↔ ((J 1 ≡ true × Alt (shift J)) ⊎ (J 1 ≡ false × Const (shift J)))
to-oplax-classification J = to , from
  where
  to : _
  to (inj₁ (j , h)) = inj₁ (j , fst (SwapC↔Alt (shift J)) h)
  to (inj₂ (j , h)) = inj₂ (j , fst (IdC↔Const (shift J)) h)
  from : _
  from (inj₁ (j , h)) = inj₁ (j , snd (SwapC↔Alt (shift J)) h)
  from (inj₂ (j , h)) = inj₂ (j , snd (IdC↔Const (shift J)) h)

-- A duality that is neither: reversing only the 3-cells of the ambient
-- (J = {3}, so K = {2} in the homs).  The identity test already fails at
-- (p, q) = (1, 1) and the swap test at (p, q) = (1, 3).
J₃ : Sign
J₃ (suc (suc (suc zero))) = false
J₃ _ = true

J₃-not-symmetry : Symmetry J₃ → ⊥
J₃-not-symmetry (inj₁ (_ , h)) = bad (fst h zero (suc zero))
  where
  bad : shift J₃ 2 ≡ shift J₃ 1 → ⊥
  bad ()
J₃-not-symmetry (inj₂ (() , _))

J₃-not-oplax : ToOplax J₃ → ⊥
J₃-not-oplax (inj₁ (_ , h)) = bad (fst h zero (suc (suc (suc zero))))
  where
  bad : shift J₃ 4 ≡ alt 3 · shift J₃ 1 → ⊥
  bad ()
J₃-not-oplax (inj₂ (() , _))
