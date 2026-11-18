------------------------------------------------------------------------
-- Definitions shared by strict-model soundness and the proofs of its
-- hypotheses: the total cell's tower twT, set equality of supports,
-- and the statements TCell (proved in Strict.Bridge), BSupp and its
-- instance BBdry (the remaining hypothesis of Strict.Soundness). Split
-- from Strict.Soundness so that the proofs can be imported there.
------------------------------------------------------------------------
module CaTTExp.Strict.Hyp where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst
open import CaTTExp.Strict.L
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Subst ∅ graySide as S
import CaTTExp.Gray.Graded ∅ as Gr

------------------------------------------------------------------------
-- Finite sets via CaTTExp.Gray.Support's memT.

SetEq : TSet → TSet → Set
SetEq X Y = ∀ a → memT a X ≡ memT a Y

private
  ∨-assoc : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

  ∨-false : ∀ a → a ∨ false ≡ a
  ∨-false true  = refl
  ∨-false false = refl

  bool-flat : ∀ s y u t → (s ∨ y) ∨ ((u ∨ y) ∨ t) ≡ t ∨ (y ∨ (s ∨ u))
  bool-flat true true true true = refl
  bool-flat true true true false = refl
  bool-flat true true false true = refl
  bool-flat true true false false = refl
  bool-flat true false true true = refl
  bool-flat true false true false = refl
  bool-flat true false false true = refl
  bool-flat true false false false = refl
  bool-flat false true true true = refl
  bool-flat false true true false = refl
  bool-flat false true false true = refl
  bool-flat false true false false = refl
  bool-flat false false true true = refl
  bool-flat false false true false = refl
  bool-flat false false false true = refl
  bool-flat false false false false = refl

  bool-tw : ∀ l f t c → (l ∨ f) ∨ ((l ∨ t) ∨ c) ≡ (l ∨ (f ∨ t)) ∨ c
  bool-tw true true true true = refl
  bool-tw true true true false = refl
  bool-tw true true false true = refl
  bool-tw true true false false = refl
  bool-tw true false true true = refl
  bool-tw true false true false = refl
  bool-tw true false false true = refl
  bool-tw true false false false = refl
  bool-tw false true true true = refl
  bool-tw false true true false = refl
  bool-tw false true false true = refl
  bool-tw false true false false = refl
  bool-tw false false true true = refl
  bool-tw false false true false = refl
  bool-tw false false false true = refl
  bool-tw false false false false = refl

memT-++ : ∀ a X Y → memT a (X ++ Y) ≡ memT a X ∨ memT a Y
memT-++ a []      Y = refl
memT-++ a (x ∷ X) Y = trans (cong ((a ==T x) ∨_) (memT-++ a X Y)) (sym (∨-assoc (a ==T x) (memT a X) (memT a Y)))

==T-sound : ∀ a b → T (a ==T b) → a ≡ b
==T-sound []       []       _ = refl
==T-sound (x ∷ xs) (y ∷ ys) p =
  cong₂ _∷_ (==ℕ-sound x y (∧-fst p)) (==T-sound xs ys (∧-snd {x ==ℕ y} p))

==T-refl : ∀ a → T (a ==T a)
==T-refl []       = tt
==T-refl (x ∷ xs) = T-∧ (==ℕ-refl x) (==T-refl xs)
  where
  T-∧ : ∀ {a b} → T a → T b → T (a ∧ b)
  T-∧ {true} _ q = q

private
  T-∧ : ∀ {a b} → T a → T b → T (a ∧ b)
  T-∧ {true} _ q = q

  T-∨r : ∀ a {b} → T b → T (a ∨ b)
  T-∨r true  _ = tt
  T-∨r false q = q

⊆T-sound : ∀ xs ys → T (⊆T xs ys) → ∀ a → T (memT a xs) → T (memT a ys)
⊆T-sound (x ∷ xs) ys p a m with a ==T x in e
... | true  = subst (λ z → T (memT z ys)) (sym (==T-sound a x (subst T (sym e) tt))) (∧-fst p)
... | false = ⊆T-sound xs ys (∧-snd {memT x ys} p) a m

⊆T-complete : ∀ xs ys → (∀ a → T (memT a xs) → T (memT a ys)) → T (⊆T xs ys)
⊆T-complete []       ys f = tt
⊆T-complete (x ∷ xs) ys f =
  T-∧ (f x (subst (λ b → T (b ∨ memT x xs)) (sym (T→≡ (==T-refl x))) tt))
      (⊆T-complete xs ys (λ a m → f a (T-∨r (a ==T x) m)))
  where
  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

≈T-via : ∀ A B F → T (≈T A F) → T (≈T B F) → T (≈T A B)
≈T-via A B F p q =
  T-∧ (⊆T-complete A B (λ a m → ⊆T-sound F B (∧-snd {⊆T B F} q) a (⊆T-sound A F (∧-fst p) a m)))
      (⊆T-complete B A (λ a m → ⊆T-sound F A (∧-snd {⊆T A F} p) a (⊆T-sound B F (∧-fst q) a m)))

------------------------------------------------------------------------
-- The flattened table of t : A is its support (CaTTExp.Gray.Support's
-- supp t A), as a set.

flat-supp : ∀ t A s u → SetEq (flat (towerOf t (arr A s u))) (supp t (arr A s u))
flat-supp t ⋆ s u a = sym (trans (memT-++ a (topS t) []) (∨-false (memT a (topS t))))
flat-supp t (arr B a' b') s u a =
  trans (memT-++ a (flat (towerOf s A')) _)
 (trans (cong₂ _∨_ (flat-supp s B a' b' a) (memT-++ a (flat (towerOf u A')) (topS t)))
 (trans (cong₂ (λ X Y → X ∨ (Y ∨ memT a (topS t)))
          (memT-++ a (topS s) (suppTy A')) (trans (flat-supp u B a' b' a) (memT-++ a (topS u) (suppTy A'))))
 (trans (bool-flat (memT a (topS s)) (memT a (suppTy A')) (memT a (topS u)) (memT a (topS t)))
        (sym (trans (memT-++ a (topS t) _)
              (cong (memT a (topS t) ∨_)
                (trans (memT-++ a (suppTy A') _) (cong (memT a (suppTy A') ∨_) (memT-++ a (topS s) (topS u))))))))))
  where
  A' = arr B a' b'

------------------------------------------------------------------------
-- The total cell T and its boundaries, as towers.

twT : List Hom → Bool → Nat → Tower
twT hs sg zero    = base (chainT sg zero hs)
twT hs sg (suc m) = step (twT hs false m) (twT hs true m) (chainT sg (suc m) hs)

flat-twT : ∀ hs sg m → SetEq (flat (twT hs sg m)) (lowerT m hs ++ chainT sg m hs)
flat-twT hs sg zero    a = refl
flat-twT hs sg (suc m) a =
  trans (memT-++ a (flat (twT hs false m)) _)
 (trans (cong₂ _∨_ (trans (flat-twT hs false m a) (memT-++ a (lowerT m hs) _))
                   (trans (memT-++ a (flat (twT hs true m)) _)
                          (cong (_∨ memT a (chainT sg (suc m) hs))
                                (trans (flat-twT hs true m a) (memT-++ a (lowerT m hs) _)))))
 (trans (bool-tw (memT a (lowerT m hs)) (memT a (chainT false m hs)) (memT a (chainT true m hs))
                 (memT a (chainT sg (suc m) hs)))
        (sym (trans (memT-++ a (lowerT (suc m) hs) _)
              (cong (_∨ memT a (chainT sg (suc m) hs))
                (trans (memT-++ a (lowerT m hs) _)
                       (cong (memT a (lowerT m hs) ∨_) (memT-++ a (chainT false m hs) (chainT true m hs)))))))))

------------------------------------------------------------------------
-- Endpoints.

endsV→endsTy : ∀ A {x y} → endsV A ≡ just (x , y) → endsTy A ≡ just (var x , var y)
endsV→endsTy ⋆ ()
endsV→endsTy (arr ⋆ (var x) (var y)) refl = refl
endsV→endsTy (arr ⋆ (var x) (coh _ _ _)) ()
endsV→endsTy (arr ⋆ (var x) (cst ()))
endsV→endsTy (arr ⋆ (coh _ _ _) _) ()
endsV→endsTy (arr ⋆ (cst ()) _)
endsV→endsTy (arr (arr B s t) _ _) e = endsV→endsTy (arr B s t) e

------------------------------------------------------------------------
-- The theorem.

closed : S.Closed
closed ()

-- The two hypotheses, named so that every module using them states the
-- same thing.
TCell : Set
TCell = ∀ {Θ} → Θ ⊢ps → ∀ A x y → T (endsOK Θ A) → endsTy A ≡ just (var x , var y) →
        IsCellL Θ x y (dimK (homs Θ)) (twT (homs Θ) true (dimK (homs Θ)))

-- Two cells in the same hom x → y.
BSupp : Set
BSupp = ∀ {Θ} → Θ ⊢ps → ∀ x y n X Y L M →
        IsCellL Θ x y n X → IsCellL Θ x y n Y →
        SetEq (flat X) L → SetEq (flat Y) M → T (≈T (down Θ L) (down Θ M)) → X ≈w Y

-- The instance soundness uses: a cell with the same closed support as
-- a boundary ∂^sg T of the total cell T (dimension d = n + 1) is that
-- boundary. (Q3a of notes/conjectures/outbox/steiner-support-formalizable.md.)
BBdry : Set
BBdry = ∀ {Θ} → Θ ⊢ps → ∀ x y n sg X L → suc n ≡ dimK (homs Θ) →
        IsCellL Θ x y n X → IsCellL Θ x y n (twT (homs Θ) sg n) →
        SetEq (flat X) L →
        T (≈T (down Θ L) (down Θ (lowerT n (homs Θ) ++ chainT sg n (homs Θ)))) →
        X ≈w twT (homs Θ) sg n

bsupp→bbdry : BSupp → BBdry
bsupp→bbdry B {Θ} P x y n sg X L _ cX cT fX p =
  B P x y n X (twT (homs Θ) sg n) L (lowerT n (homs Θ) ++ chainT sg n (homs Θ)) cX cT fX (flat-twT (homs Θ) sg n) p

-- The side condition compares downsets on generators (Support's
-- `sameDown`); B-supp is about the closures `down`. In a pasting
-- context the two agree on every comparison the side condition makes
-- (CaTTExp.Gray.Graded.PsSide, from Gray.DownAgree), using that the
-- context's types are variable towers.
inv-gr : ∀ {Γ} → PsInv Γ → Gr.Inv Γ
inv-gr p i ⋆           e = tt
inv-gr p i (arr B s t) e = p i (arr B s t) e

