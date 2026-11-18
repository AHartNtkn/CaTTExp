------------------------------------------------------------------------
-- F2c toward (1′): boundaries of diagrams, and dimensions of labels.
--
--   ex-bd     : Ex Θ e par a → Ex Θ e par (bd β k a)
--   bd-dim    : Ex Θ e par a → y a label of bd β k a → dim y ≤ e + k
--   thin-dim  : Ex Θ 0 nothing a → bd β k a ≡ a → y a label of a → dim y ≤ k
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.ExBd where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; bdL; module Lists)
open Lists using (headN; lastN)
open import CaTTExp.GlobularTotal.Uniq

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  ≤-refl : ∀ a → T (a <ℕ suc a)
  ≤-refl zero    = tt
  ≤-refl (suc a) = ≤-refl a

  ≤-+ : ∀ e k → T (e <ℕ suc (e + k))
  ≤-+ zero    k = tt
  ≤-+ (suc e) k = ≤-+ e k

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  all-last : ∀ {P : Nat → Set} o os → AllN P (o ∷ os) → P (lastN (o ∷ os))
  all-last o []        (p , _)  = p
  all-last o (o' ∷ os) (_ , pp) = all-last o' os pp

module _ (Θ : Ctx) where

  mutual
    ex-bd : ∀ β k e par a → Ex Θ e par a → Ex Θ e par (bd β k a)
    ex-bd false zero    e par (lt []       cs) (_ , x) = ⊥-elim (no-obj e cs x)
    ex-bd true  zero    e par (lt []       cs) (_ , x) = ⊥-elim (no-obj e cs x)
    ex-bd false zero    e par (lt (o ∷ os) cs) ((co , _) , _) = (co , tt) , tt
    ex-bd true  zero    e par (lt (o ∷ os) cs) (oks , _)      = (all-last o os oks , tt) , tt
    ex-bd false (suc k) e par (lt os cs) (oks , x) = oks , exCs-bd false k e os cs x
    ex-bd true  (suc k) e par (lt os cs) (oks , x) = oks , exCs-bd true  k e os cs x

    exCs-bd : ∀ β k e os cs → ExCs Θ e os cs → ExCs Θ e os (bdL β k cs)
    exCs-bd β k e []            cs       ()
    exCs-bd β k e (o ∷ [])      []       x = tt
    exCs-bd β k e (o ∷ [])      (c ∷ cs) ()
    exCs-bd β k e (o ∷ o' ∷ os) []       ()
    exCs-bd β k e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) =
      ex-bd β k (suc e) (just (o , o')) c xc , exCs-bd β k e (o' ∷ os) cs xs

    no-obj : ∀ e cs → ExCs Θ e [] cs → ⊥
    no-obj e []      ()
    no-obj e (_ ∷ _) ()

  private
    cell-dim : ∀ e par o → Cell Θ e par o → dimOf Θ o ≡ e
    cell-dim e nothing        o (_ , d) = d
    cell-dim e (just (p , q)) o (_ , d) = d

    objs-dim : ∀ e par os y → AllN (Cell Θ e par) os → memL y os ≡ true → dimOf Θ y ≡ e
    objs-dim e par []       y _        ()
    objs-dim e par (o ∷ os) y (c , cs) m with ∨-split (y ==ℕ o) (memL y os) m
    ... | inl h with ==ℕ-sound y o (≡-T h)
    ...   | refl = cell-dim e par y c
    objs-dim e par (o ∷ os) y (c , cs) m | inr h = objs-dim e par os y cs h

  private
    ≤-e+ : ∀ e k → T (e <ℕ suc (e + k))
    ≤-e+ = ≤-+

    leaf-dim : ∀ e par h y → Cell Θ e par h → mem y (lt (h ∷ []) []) ≡ true →
               ∀ k → T (dimOf Θ y <ℕ suc (e + k))
    leaf-dim e par h y c m k with ∨-split (memL y (h ∷ [])) false m
    ... | inr ()
    ... | inl m' with ∨-split (y ==ℕ h) false m'
    ...   | inr ()
    ...   | inl h' with ==ℕ-sound y h (≡-T h')
    ...     | refl rewrite cell-dim e par y c = ≤-+ e k

  -- Labels of a k-boundary of a depth-e diagram have dimension ≤ e + k.
  mutual
    bd-dim : ∀ β k e par a y → Ex Θ e par a → mem y (bd β k a) ≡ true →
             T (dimOf Θ y <ℕ suc (e + k))
    bd-dim β     zero    e par (lt []       cs) y (_ , x) m = ⊥-elim (no-obj e cs x)
    bd-dim false zero    e par (lt (o ∷ os) cs) y ((co , _) , _) m = leaf-dim e par o y co m 0
    bd-dim true  zero    e par (lt (o ∷ os) cs) y (oks , _) m =
      leaf-dim e par (lastN (o ∷ os)) y (all-last o os oks) m 0
    bd-dim false (suc k) e par (lt os cs) y (oks , x) m = node-dim false k e par os cs y oks x m
    bd-dim true  (suc k) e par (lt os cs) y (oks , x) m = node-dim true  k e par os cs y oks x m

    node-dim : ∀ β k e par os cs y → AllN (Cell Θ e par) os → ExCs Θ e os cs →
               (memL y os ∨ memCs y (bdL β k cs)) ≡ true → T (dimOf Θ y <ℕ suc (e + suc k))
    node-dim β k e par os cs y oks x m with ∨-split (memL y os) (memCs y (bdL β k cs)) m
    ... | inl mo rewrite objs-dim e par os y oks mo = ≤-+ e (suc k)
    ... | inr mc rewrite +-suc e k = bdCs-dim β k e os cs y x mc

    bdCs-dim : ∀ β k e os cs y → ExCs Θ e os cs → memCs y (bdL β k cs) ≡ true →
             T (dimOf Θ y <ℕ suc (suc (e + k)))
    bdCs-dim β k e []            cs       y () m
    bdCs-dim β k e (o ∷ [])      []       y x ()
    bdCs-dim β k e (o ∷ [])      (c ∷ cs) y () m
    bdCs-dim β k e (o ∷ o' ∷ os) []       y () m
    bdCs-dim β k e (o ∷ o' ∷ os) (c ∷ cs) y (xc , xs) m
      with ∨-split (mem y (bd β k c)) (memCs y (bdL β k cs)) m
    ... | inl mc = bd-dim β k (suc e) (just (o , o')) c y xc mc
    ... | inr ms = bdCs-dim β k e (o' ∷ os) cs y xs ms

  -- In a diagram of dimension ≤ k, every label has dimension ≤ k.
  thin-dim : ∀ β k a y → Ex Θ 0 nothing a → bd β k a ≡ a → mem y a ≡ true →
             T (dimOf Θ y <ℕ suc k)
  thin-dim β k a y x th m = bd-dim β k 0 nothing a y x (subst (λ t → mem y t ≡ true) (sym th) m)
