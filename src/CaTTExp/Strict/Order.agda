------------------------------------------------------------------------
-- A total order on the basis of K(Γ) for a pasting context Γ, with
-- negative faces before and positive faces after
-- (notes/conjectures/answered/steiner-support-formalizable-2026-11-18.md).
--
--   _<ₒ_ Γ : Tuple → Tuple → Bool
--
--  * Each hom is ordered by creation order, where the pse step at the
--    current cell x inserts the new cell f and its target y right after
--    x (`olist`: one list for all of Γ, objects included; a hom's order
--    is its restriction).
--  * Tuples are ordered lexicographically, with the comparison reversed
--    when the hom-dimension sum before the first differing entry is odd.
--
-- Facts:
--   <ₒ-irrefl, <ₒ-trans, <ₒ-tri   (strict total order on tuples of
--                                  variables of Γ of equal length);
--   ord-neg : y ∈ ∂T Γ false x → T (y <ₒ x)  (for a pasting context Γ),
--   ord-pos : y ∈ ∂T Γ true x  → T (x <ₒ y),
-- and `count-in` turns a positive count into membership.
------------------------------------------------------------------------
module CaTTExp.Strict.Order where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex renaming (here to hereB)
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Gray.PsFacts ∅ as PF
open import CaTTExp.Gray.Cover using (Any; here; there; _⊎_; inj₁; inj₂; any-++⁻)

infix 4 _∈ᴸ_
_∈ᴸ_ : Nat → List Nat → Set
a ∈ᴸ L = Any (a ≡_) L

------------------------------------------------------------------------
-- Booleans and numbers.

private
  ==-refl≡ : ∀ n → (n ==ℕ n) ≡ true
  ==-refl≡ zero    = refl
  ==-refl≡ (suc n) = ==-refl≡ n

  T≡ : ∀ {b} → T b → b ≡ true
  T≡ {true} _ = refl

  ≡T : ∀ {b} → b ≡ true → T b
  ≡T refl = tt

  F≡ : ∀ {b} → (T b → ⊥) → b ≡ false
  F≡ {true}  f = ⊥-elim (f tt)
  F≡ {false} _ = refl

  <-irr : ∀ n → T (n <ℕ n) → ⊥
  <-irr zero    ()
  <-irr (suc n) p = <-irr n p

  <-trans' : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  <-trans' zero    (suc b) (suc c) _ _ = tt
  <-trans' (suc a) (suc b) (suc c) p q = <-trans' a b c p q

  <-suc : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-suc zero    b       _ = tt
  <-suc (suc a) (suc b) p = <-suc a b p

  <-+2 : ∀ a b → T (a <ℕ b) → T (a <ℕ suc (suc b))
  <-+2 a b p = <-suc a (suc b) (<-suc a b p)

  n<s : ∀ n → T (n <ℕ suc n)
  n<s zero    = tt
  n<s (suc n) = n<s n

  ≢-< : ∀ a b → (a ==ℕ b) ≡ false → T (a <ℕ b) ⊎ T (b <ℕ a)
  ≢-< zero    zero    ()
  ≢-< zero    (suc b) _ = inj₁ tt
  ≢-< (suc a) zero    _ = inj₂ tt
  ≢-< (suc a) (suc b) q = ≢-< a b q

  <-≢ : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-≢ zero    (suc b) _ = refl
  <-≢ (suc a) (suc b) p = <-≢ a b p

  ≤→≯ : ∀ a b → T (b <ℕ a) → T (a <ℕ suc b) → ⊥
  ≤→≯ (suc a) zero    _ ()
  ≤→≯ (suc a) (suc b) p q = ≤→≯ a b p q

  subst₂ : ∀ {A : Set} (P : A → A → Set) {x y u v} → x ≡ y → u ≡ v → P x u → P y v
  subst₂ P refl refl p = p

  ==-sym : ∀ a b → (a ==ℕ b) ≡ (b ==ℕ a)
  ==-sym zero    zero    = refl
  ==-sym zero    (suc b) = refl
  ==-sym (suc a) zero    = refl
  ==-sym (suc a) (suc b) = ==-sym a b

------------------------------------------------------------------------
-- Positions in a list (first occurrence; the length if absent).

pos : Nat → List Nat → Nat
pos a []      = 0
pos a (z ∷ L) = if z ==ℕ a then 0 else suc (pos a L)

lenL : List Nat → Nat
lenL []      = 0
lenL (_ ∷ L) = suc (lenL L)

pos-in : ∀ a L → T (pos a L <ℕ lenL L) → a ∈ᴸ L
pos-in a (z ∷ L) p with z ==ℕ a in q
... | true  = here (sym (==ℕ-sound z a (≡T q)))
... | false = there (pos-in a L p)

pos-lt : ∀ a L → a ∈ᴸ L → T (pos a L <ℕ lenL L)
pos-lt a (z ∷ L) m with z ==ℕ a in q
... | true = tt
pos-lt a (z ∷ L) (here e)  | false = ⊥-elim (bad (trans (cong (z ==ℕ_) (sym e)) q))
  where
  bad : (z ==ℕ z) ≡ false → ⊥
  bad r = ⊥-elim (subst T (trans (sym (==-refl≡ z)) r) tt)
pos-lt a (z ∷ L) (there m) | false = pos-lt a L m

-- Equal positions of present elements are equal elements.
pos-inj : ∀ a b L → a ∈ᴸ L → pos a L ≡ pos b L → a ≡ b
pos-inj a b (z ∷ L) m e with z ==ℕ a in qa | z ==ℕ b in qb
... | true  | true  = trans (sym (==ℕ-sound z a (≡T qa))) (==ℕ-sound z b (≡T qb))
... | true  | false = ⊥-elim (zero≢suc e)
  where
  zero≢suc : ∀ {n} → 0 ≡ suc n → ⊥
  zero≢suc ()
... | false | true  = ⊥-elim (suc≢zero e)
  where
  suc≢zero : ∀ {n} → suc n ≡ 0 → ⊥
  suc≢zero ()
pos-inj a b (z ∷ L) (here e)  e' | false | false =
  ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) qa)) tt)
pos-inj a b (z ∷ L) (there m) e' | false | false = pos-inj a b L m (suc-inj e')
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

------------------------------------------------------------------------
-- Insertion right after x.

insAfter : Nat → List Nat → List Nat → List Nat
insAfter x new []      = []
insAfter x new (z ∷ L) = if z ==ℕ x then (z ∷ (new ++ L)) else (z ∷ insAfter x new L)

module Ins (x f y : Nat) where
  new = f ∷ y ∷ []

  ins-mem : ∀ L {a} → a ∈ᴸ L → a ∈ᴸ insAfter x new L
  ins-mem (z ∷ L) m with z ==ℕ x
  ins-mem (z ∷ L) (here e)  | true  = here e
  ins-mem (z ∷ L) (there m) | true  = there (there (there m))
  ins-mem (z ∷ L) (here e)  | false = here e
  ins-mem (z ∷ L) (there m) | false = there (ins-mem L m)

  ins-new-f : ∀ L → x ∈ᴸ L → f ∈ᴸ insAfter x new L
  ins-new-f (z ∷ L) m with z ==ℕ x in q
  ... | true = there (here refl)
  ins-new-f (z ∷ L) (here e)  | false = ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-new-f (z ∷ L) (there m) | false = there (ins-new-f L m)

  ins-new-y : ∀ L → x ∈ᴸ L → y ∈ᴸ insAfter x new L
  ins-new-y (z ∷ L) m with z ==ℕ x in q
  ... | true = there (there (here refl))
  ins-new-y (z ∷ L) (here e)  | false = ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-new-y (z ∷ L) (there m) | false = there (ins-new-y L m)

  ins-back : ∀ L {a} → a ∈ᴸ insAfter x new L → a ∈ᴸ L ⊎ (a ≡ f ⊎ a ≡ y)
  ins-back (z ∷ L) m with z ==ℕ x
  ins-back (z ∷ L) (here e)                  | true = inj₁ (here e)
  ins-back (z ∷ L) (there (here e))          | true = inj₂ (inj₁ e)
  ins-back (z ∷ L) (there (there (here e)))  | true = inj₂ (inj₂ e)
  ins-back (z ∷ L) (there (there (there m))) | true = inj₁ (there m)
  ins-back (z ∷ L) (here e)  | false = inj₁ (here e)
  ins-back (z ∷ L) (there m) | false with ins-back L m
  ... | inj₁ a = inj₁ (there a)
  ... | inj₂ b = inj₂ b

  -- Old elements: positions up to x are kept, later ones move by 2.
  ins-le : ∀ L a → x ∈ᴸ L → T (pos a L <ℕ suc (pos x L)) → pos a (insAfter x new L) ≡ pos a L
  ins-le (z ∷ L) a m p with z ==ℕ x in q
  ins-le (z ∷ L) a m p | true with z ==ℕ a
  ... | true  = refl
  ... | false = ⊥-elim (no<1 (pos a L) p)
    where
    no<1 : ∀ n → T (suc n <ℕ 1) → ⊥
    no<1 zero    ()
    no<1 (suc n) ()
  ins-le (z ∷ L) a (here e) p | false =
    ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-le (z ∷ L) a (there m) p | false with z ==ℕ a
  ... | true  = refl
  ... | false = cong suc (ins-le L a m p)

  ins-gt : ∀ L a → x ∈ᴸ L → (f ==ℕ a) ≡ false → (y ==ℕ a) ≡ false →
           T (pos x L <ℕ pos a L) → pos a (insAfter x new L) ≡ suc (suc (pos a L))
  ins-gt (z ∷ L) a m nf ny p with z ==ℕ x in q
  ins-gt (z ∷ L) a m nf ny p | true with z ==ℕ a
  ... | true  = ⊥-elim p
  ... | false rewrite nf | ny = refl
  ins-gt (z ∷ L) a (here e) nf ny p | false =
    ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-gt (z ∷ L) a (there m) nf ny p | false with z ==ℕ a
  ... | true  = ⊥-elim p
  ... | false = cong suc (ins-gt L a m nf ny p)

  -- The new elements, when fresh.
  ins-f : ∀ L → x ∈ᴸ L → (f ∈ᴸ L → ⊥) → pos f (insAfter x new L) ≡ suc (pos x L)
  ins-f (z ∷ L) m nf with z ==ℕ x in q
  ... | true rewrite F≡ {z ==ℕ f} (λ t → nf (here (sym (==ℕ-sound z f t)))) | ==-refl≡ f = refl
  ins-f (z ∷ L) (here e) nf | false =
    ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-f (z ∷ L) (there m) nf | false
    rewrite F≡ {z ==ℕ f} (λ t → nf (here (sym (==ℕ-sound z f t)))) = cong suc (ins-f L m (λ m' → nf (there m')))

  ins-y : ∀ L → x ∈ᴸ L → (y ∈ᴸ L → ⊥) → (f ==ℕ y) ≡ false →
          pos y (insAfter x new L) ≡ suc (suc (pos x L))
  ins-y (z ∷ L) m ny fy with z ==ℕ x in q
  ... | true rewrite F≡ {z ==ℕ y} (λ t → ny (here (sym (==ℕ-sound z y t)))) | fy | ==-refl≡ y = refl
  ins-y (z ∷ L) (here e) ny fy | false =
    ⊥-elim (subst T (trans (sym (==-refl≡ z)) (trans (cong (z ==ℕ_) (sym e)) q)) tt)
  ins-y (z ∷ L) (there m) ny fy | false
    rewrite F≡ {z ==ℕ y} (λ t → ny (here (sym (==ℕ-sound z y t)))) = cong suc (ins-y L m (λ m' → ny (there m')) fy)

------------------------------------------------------------------------
-- The creation order of a context.

olistStep : Ctx → Ty → List Nat → List Nat
olistStep Γ (arr _ (var x) _) L = insAfter x (suc (len Γ) ∷ len Γ ∷ []) L
olistStep Γ _                 L = L

olist : Ctx → List Nat
olist ε             = []
olist (ε ▸ _)       = 0 ∷ []
olist (Γ ▸ A ▸ F)   = olistStep Γ F (olist Γ)

------------------------------------------------------------------------
-- The invariant on pasting contexts.

record OInv (Γ : Ctx) : Set where
  field
    present : ∀ v → T (v <ℕ len Γ) → v ∈ᴸ olist Γ
    bound   : ∀ a → a ∈ᴸ olist Γ → T (a <ℕ len Γ)
    faces   : ∀ v C s t → lookup Γ v ≡ just (arr C (var s) (var t)) →
              (s ∈ᴸ olist Γ) × (t ∈ᴸ olist Γ) ×
              T (pos s (olist Γ) <ℕ pos v (olist Γ)) × T (pos v (olist Γ) <ℕ pos t (olist Γ))

open OInv public

private
  lookup-lt : ∀ Γ v {C} → lookup Γ v ≡ just C → T (v <ℕ len Γ)
  lookup-lt (Γ ▸ A) v e with v ==ℕ len Γ in q
  ... | true  = subst (λ w → T (w <ℕ suc (len Γ))) (sym (==ℕ-sound v (len Γ) (≡T q))) (n<s (len Γ))
  ... | false = <-suc v (len Γ) (lookup-lt Γ v e)

  lt-ne : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  lt-ne = <-≢

  lt-split2 : ∀ v n → T (v <ℕ suc (suc n)) → T (v <ℕ n) ⊎ (v ≡ n ⊎ v ≡ suc n)
  lt-split2 zero    zero    _ = inj₂ (inj₁ refl)
  lt-split2 zero    (suc n) _ = inj₁ tt
  lt-split2 (suc v) zero    p with v
  ... | zero = inj₂ (inj₂ refl)
  ... | suc _ = ⊥-elim p
  lt-split2 (suc v) (suc n) p with lt-split2 v n p
  ... | inj₁ a = inj₁ a
  ... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong suc e))
  ... | inj₂ (inj₂ e) = inj₂ (inj₂ (cong suc e))

oinv0 : OInv (ε ▸ ⋆)
oinv0 = record
  { present = λ { zero _ → here refl ; (suc v) () }
  ; bound   = λ { a (here refl) → tt ; a (there ()) }
  ; faces   = λ { zero C s t () ; (suc v) C s t () }
  }

module Step (Γ : Ctx) (x : Nat) (A : Ty) (I : OInv Γ) (lx : lookup Γ x ≡ just A) where
  private
    y = len Γ
    f = suc (len Γ)
    L = olist Γ
    open Ins x f y
    L' = insAfter x new L
    Γ' = Γ ▸ A ▸ arr A (var x) (var y)

    xin : x ∈ᴸ L
    xin = present I x (lookup-lt Γ x lx)

    fresh : ∀ a → a ∈ᴸ L → T (a <ℕ y)
    fresh = bound I

    nf : f ∈ᴸ L → ⊥
    nf m = <-irr y (<-trans' y f y (n<s y) (fresh f m))

    ny : y ∈ᴸ L → ⊥
    ny m = <-irr y (fresh y m)

    fy : (f ==ℕ y) ≡ false
    fy = ==-sym'
      where
      ==-sym' : (suc (len Γ) ==ℕ len Γ) ≡ false
      ==-sym' = trans (==-sym (suc (len Γ)) (len Γ)) (<-≢ (len Γ) (suc (len Γ)) (n<s (len Γ)))

    old-f : ∀ a → a ∈ᴸ L → (f ==ℕ a) ≡ false
    old-f a m = trans (==-sym f a) (<-≢ a f (<-suc a y (fresh a m)))

    old-y : ∀ a → a ∈ᴸ L → (y ==ℕ a) ≡ false
    old-y a m = trans (==-sym y a) (<-≢ a y (fresh a m))

    -- Order between old elements is kept.
    keep : ∀ a b → a ∈ᴸ L → b ∈ᴸ L → T (pos a L <ℕ pos b L) → T (pos a L' <ℕ pos b L')
    keep a b ma mb p with ≤-dec a | ≤-dec b
      where
      ≤-dec : ∀ c → T (pos c L <ℕ suc (pos x L)) ⊎ T (pos x L <ℕ pos c L)
      ≤-dec c with pos c L ==ℕ pos x L in q
      ... | true  = inj₁ (subst (λ n → T (n <ℕ suc (pos x L))) (sym (==ℕ-sound (pos c L) (pos x L) (≡T q))) (n<s (pos x L)))
      ... | false with ≢-< (pos c L) (pos x L) q
      ...   | inj₁ r = inj₁ (<-suc (pos c L) (pos x L) r)
      ...   | inj₂ r = inj₂ r
    ... | inj₁ ra | inj₁ rb rewrite ins-le L a xin ra | ins-le L b xin rb = p
    ... | inj₁ ra | inj₂ rb rewrite ins-le L a xin ra | ins-gt L b xin (old-f b mb) (old-y b mb) rb = <-+2 (pos a L) (pos b L) p
    ... | inj₂ ra | inj₁ rb = ⊥-elim (≤→≯ (pos b L) (pos x L) (<-trans' (pos x L) (pos a L) (pos b L) ra p) rb)
    ... | inj₂ ra | inj₂ rb rewrite ins-gt L a xin (old-f a ma) (old-y a ma) ra
                                  | ins-gt L b xin (old-f b mb) (old-y b mb) rb = p

    pos-f : pos f L' ≡ suc (pos x L)
    pos-f = ins-f L xin nf

    pos-y : pos y L' ≡ suc (suc (pos x L))
    pos-y = ins-y L xin ny fy

    pos-x : pos x L' ≡ pos x L
    pos-x = ins-le L x xin (n<s (pos x L))

  oinv : OInv Γ'
  oinv = record { present = pres ; bound = bnd ; faces = fcs }
    where
    pres : ∀ v → T (v <ℕ suc (suc (len Γ))) → v ∈ᴸ L'
    pres v p with lt-split2 v (len Γ) p
    ... | inj₁ a          = ins-mem L (present I v a)
    ... | inj₂ (inj₁ refl) = ins-new-y L xin
    ... | inj₂ (inj₂ refl) = ins-new-f L xin

    bnd : ∀ a → a ∈ᴸ L' → T (a <ℕ suc (suc (len Γ)))
    bnd a m with ins-back L m
    ... | inj₁ a'          = <-+2 a (len Γ) (bound I a a')
    ... | inj₂ (inj₁ refl) = n<s (suc (len Γ))
    ... | inj₂ (inj₂ refl) = <-suc (len Γ) (suc (len Γ)) (n<s (len Γ))

    fcs : ∀ v C s t → lookup Γ' v ≡ just (arr C (var s) (var t)) →
          (s ∈ᴸ L') × (t ∈ᴸ L') × T (pos s L' <ℕ pos v L') × T (pos v L' <ℕ pos t L')
    fcs v C s t e with v ==ℕ suc (len Γ) in q1
    fcs v C s t refl | true rewrite ==ℕ-sound v f (≡T q1) =
      ins-mem L xin , ins-new-y L xin ,
      subst₂ (λ m n → T (m <ℕ n)) (sym pos-x) (sym pos-f) (n<s (pos x L)) ,
      subst₂ (λ m n → T (m <ℕ n)) (sym pos-f) (sym pos-y) (n<s (suc (pos x L)))
    ... | false with v ==ℕ len Γ in q2
    fcs v C s t refl | false | true rewrite ==ℕ-sound v y (≡T q2) with faces I x C s t lx
    ... | ms , mt , qs , qt =
      ins-mem L ms , ins-mem L mt ,
      subst₂ (λ m n → T (m <ℕ n)) (sym (ins-le L s xin (<-suc (pos s L) (pos x L) qs))) (sym pos-y)
        (<-+2 (pos s L) (pos x L) qs) ,
      subst₂ (λ m n → T (m <ℕ n)) (sym pos-y) (sym (ins-gt L t xin (old-f t mt) (old-y t mt) qt))
        qt
    fcs v C s t e | false | false with faces I v C s t e
    ... | ms , mt , qs , qt =
      ins-mem L ms , ins-mem L mt ,
      keep s v ms mv qs , keep v t mv mt qt
      where
      mv : v ∈ᴸ L
      mv = present I v (lookup-lt Γ v e)

oinv-ps : ∀ {Γ x A} → Γ ⊢ps x ∶ A → OInv Γ
oinv-ps pss = oinv0
oinv-ps (pse {Γ} {x} {A} d) = Step.oinv Γ x A (oinv-ps d) (snd (PF.ps-facts d))
oinv-ps (psd d) = oinv-ps d

oinv-⊢ps : ∀ {Γ} → Γ ⊢ps → OInv Γ
oinv-⊢ps (ps d) = oinv-ps d

------------------------------------------------------------------------
-- The order on tuples: lexicographic in the positions p, with the
-- comparison reversed after an odd hom-dimension (h) prefix.

module Lex (p h : Nat → Nat) where

  cmp : Bool → Nat → Nat → Bool
  cmp s a b = if s then (p a <ℕ p b) else (p b <ℕ p a)

  ltT : Bool → Tuple → Tuple → Bool
  ltT s []      []      = false
  ltT s (a ∷ x) (b ∷ y) = if a ==ℕ b then ltT (flipN (h a) s) x y else cmp s a b
  ltT s []      (_ ∷ _) = false
  ltT s (_ ∷ _) []      = false

  ltT-swap : ∀ s x y → ltT s x y ≡ ltT (not s) y x
  ltT-swap s []      []      = refl
  ltT-swap s []      (_ ∷ _) = refl
  ltT-swap s (_ ∷ _) []      = refl
  ltT-swap s (a ∷ x) (b ∷ y) with a ==ℕ b in q
  ... | true rewrite ==ℕ-sound a b (≡T q) | ==-refl≡ b | flipN-not (h b) s = ltT-swap (flipN (h b) s) x y
  ... | false rewrite trans (==-sym b a) q with s
  ...   | true  = refl
  ...   | false = refl

  ltT-irrefl : ∀ s x → ltT s x x ≡ false
  ltT-irrefl s []      = refl
  ltT-irrefl s (a ∷ x) rewrite ==-refl≡ a = ltT-irrefl (flipN (h a) s) x

  private
    cmp-ne : ∀ s a b → T (cmp s a b) → (a ==ℕ b) ≡ false
    cmp-ne s a b c with a ==ℕ b in q
    ... | false = refl
    ... | true rewrite ==ℕ-sound a b (≡T q) with s
    ...   | true  = ⊥-elim (<-irr (p b) c)
    ...   | false = ⊥-elim (<-irr (p b) c)

    cmp-trans : ∀ s a b c → T (cmp s a b) → T (cmp s b c) → T (cmp s a c)
    cmp-trans true  a b c u v = <-trans' (p a) (p b) (p c) u v
    cmp-trans false a b c u v = <-trans' (p c) (p b) (p a) v u

  ltT-trans : ∀ s x y z → T (ltT s x y) → T (ltT s y z) → T (ltT s x z)
  ltT-trans s (a ∷ x) (b ∷ y) (c ∷ z) u v with a ==ℕ b in q1 | b ==ℕ c in q2
  ... | true  | true  rewrite ==ℕ-sound a b (≡T q1) | ==ℕ-sound b c (≡T q2) | ==-refl≡ c =
    ltT-trans (flipN (h c) s) x y z u v
  ... | true  | false rewrite ==ℕ-sound a b (≡T q1) | q2 = v
  ... | false | true  rewrite sym (==ℕ-sound b c (≡T q2)) | q1 = u
  ... | false | false rewrite cmp-ne s a c (cmp-trans s a b c u v) = cmp-trans s a b c u v
  ltT-trans s []      []      z       () v
  ltT-trans s []      (_ ∷ _) z       () v
  ltT-trans s (_ ∷ _) []      z       () v
  ltT-trans s (a ∷ x) (b ∷ y) []      u  ()

  -- Totality on tuples of equal length whose entries have distinct
  -- positions when distinct.
  ltT-tri : ∀ s x y → lenL x ≡ lenL y → (∀ {a b} → a ∈ᴸ x → b ∈ᴸ y → p a ≡ p b → a ≡ b) →
            (x ≡ y) ⊎ (T (ltT s x y) ⊎ T (ltT s y x))
  ltT-tri s []      []      _ _   = inj₁ refl
  ltT-tri s (a ∷ x) (b ∷ y) l inj with a ==ℕ b in q
  ... | true rewrite ==ℕ-sound a b (≡T q) | ==-refl≡ b
    with ltT-tri (flipN (h b) s) x y (suc-inj l) (λ ma mb → inj (there ma) (there mb))
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
  ...   | inj₁ e        = inj₁ (cong (b ∷_) e)
  ...   | inj₂ (inj₁ u) = inj₂ (inj₁ u)
  ...   | inj₂ (inj₂ v) = inj₂ (inj₂ v)
  ltT-tri s (a ∷ x) (b ∷ y) l inj | false rewrite trans (==-sym b a) q
    with ≢-< (p a) (p b) (F≡ (λ e → ne (inj (here refl) (here refl) (==ℕ-sound (p a) (p b) e))))
    where
    ne : a ≡ b → ⊥
    ne refl with trans (sym (==-refl≡ a)) q
    ... | ()
  ... | inj₁ r with s
  ...   | true  = inj₂ (inj₁ r)
  ...   | false = inj₂ (inj₂ r)
  ltT-tri s (a ∷ x) (b ∷ y) l inj | false | inj₂ r with s
  ...   | true  = inj₂ (inj₂ r)
  ...   | false = inj₂ (inj₁ r)
  ltT-tri s []      (_ ∷ _) () _
  ltT-tri s (_ ∷ _) []      () _

------------------------------------------------------------------------
-- The order of a context, and its faces.

module _ (Γ : Ctx) where
  private
    P : Nat → Nat
    P a = pos a (olist Γ)
  open Lex P (hdimV Γ) public using (ltT; ltT-swap; ltT-irrefl; ltT-trans; ltT-tri)

  infix 4 _<ₒ_
  _<ₒ_ : Tuple → Tuple → Bool
  x <ₒ y = ltT true x y

  <ₒ-irrefl : ∀ x → (x <ₒ x) ≡ false
  <ₒ-irrefl = ltT-irrefl true

  <ₒ-trans : ∀ x y z → T (x <ₒ y) → T (y <ₒ z) → T (x <ₒ z)
  <ₒ-trans = ltT-trans true

  -- Distinct tuples of variables of Γ of equal length are comparable.
  <ₒ-tri : OInv Γ → ∀ x y → lenL x ≡ lenL y →
           (∀ {a} → a ∈ᴸ x → T (a <ℕ len Γ)) → (∀ {b} → b ∈ᴸ y → T (b <ℕ len Γ)) →
           (x ≡ y) ⊎ (T (x <ₒ y) ⊎ T (y <ₒ x))
  <ₒ-tri I x y l vx vy =
    ltT-tri true x y l (λ ma mb e → pos-inj _ _ (olist Γ) (present I _ (vx ma)) e)

  private
    facesTy-inv : ∀ m {s t} → facesTy m ≡ just (s , t) → Σ Ty λ C → m ≡ just (arr C (var s) (var t))
    facesTy-inv (just (arr (arr B a b) (var s) (var t))) refl = arr B a b , refl
    facesTy-inv nothing ()
    facesTy-inv (just ⋆) ()
    facesTy-inv (just (arr ⋆ _ _)) ()
    facesTy-inv (just (arr (arr B a b) (var s) (coh _ _ _))) ()
    facesTy-inv (just (arr (arr B a b) (var s) (cst ())))
    facesTy-inv (just (arr (arr B a b) (coh _ _ _) _)) ()
    facesTy-inv (just (arr (arr B a b) (cst ()) _))

    consB-mem : ∀ v Z {c} → Any (c ≡_) (consB v Z) → Σ Tuple λ c' → (c ≡ v ∷ c') × Any (c' ≡_) Z
    consB-mem v (z ∷ Z) (here refl) = z , refl , here refl
    consB-mem v (z ∷ Z) (there m) with consB-mem v Z m
    ... | c' , e , m' = c' , e , there m'

    ne-of-lt : ∀ a b → T (P a <ℕ P b) → (a ==ℕ b) ≡ false
    ne-of-lt a b l with a ==ℕ b in q
    ... | false = refl
    ... | true rewrite ==ℕ-sound a b (≡T q) = ⊥-elim (<-irr (P b) l)

  -- A face for sign σ lies on the side `not σ` of the tuple.
  face-ord : OInv Γ → ∀ σ w {c} → Any (c ≡_) (∂T Γ σ w) → T (ltT (not σ) c w)
  face-ord I σ (v ∷ w) m with any-++⁻ (hereB σ (facesTy (lookup Γ v)) w) m
  ... | inj₂ b with consB-mem v (∂T Γ (flipN (hdimV Γ v) σ) w) b
  ...   | c' , refl , m' rewrite ==-refl≡ v | flipN-not (hdimV Γ v) σ = face-ord I (flipN (hdimV Γ v) σ) w m'
  face-ord I σ (v ∷ w) m | inj₁ a with facesTy (lookup Γ v) in e
  face-ord I σ (v ∷ w) m | inj₁ (here refl) | just (s , t) with facesTy-inv (lookup Γ v) e
  ... | C , l with faces I v C s t l
  ...   | _ , _ , ls , lt with σ
  ...     | false rewrite ne-of-lt s v ls = ls
  ...     | true  rewrite trans (==-sym t v) (ne-of-lt v t lt) = lt
  face-ord I σ (v ∷ w) m | inj₁ (there ()) | just _

  -- Negative faces come before, positive faces after.
  ord-neg : OInv Γ → ∀ x {y} → Any (y ≡_) (∂T Γ false x) → T (y <ₒ x)
  ord-neg I x m = face-ord I false x m

  ord-pos : OInv Γ → ∀ x {y} → Any (y ≡_) (∂T Γ true x) → T (x <ₒ y)
  ord-pos I x {y} m = subst T (ltT-swap false y x) (face-ord I true x m)

-- A positive count means membership.
count-in : ∀ y B {n} → count y B ≡ suc n → Any (y ≡_) B
count-in y (x ∷ X) e with eqT y x in q
... | true  = here (eqT-sound y x (≡T q))
... | false = there (count-in y X e)

------------------------------------------------------------------------
-- Example: the 2-disc x, y, f, g : x → y, α : f ⇒ g is ordered
-- x < f < α < g < y.

private
  D2 : Ctx
  D2 = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
         ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)

  _ : olist D2 ≡ 0 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []
  _ = refl
