------------------------------------------------------------------------
-- Sums of atoms are determined by their rows above r (ledger A5,
-- step L3; outside response §1.1).
--
-- For a count vector c (how often each basis element occurs), Esum c
-- is the row function Σᵢ cᵢ⟨i⟩. If c and c′ count only elements of
-- degree in (r, L], and Esum c and Esum c′ agree on the rows above r,
-- then c = c′ (`esum-inj`). The proof descends through the degrees:
-- at row d, coordinate i of degree d receives cᵢ from ⟨i⟩ and
-- otherwise only contributions of atoms of degree > d.
------------------------------------------------------------------------
module CaTTExp.Strict.AtomSum where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; <→≤; ≤-<-⊥; Tri; tri; tri<; tri≡; tri>)
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero; +-suc; +-cancelˡ)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Cancelling all but one term of a sum.

private
  sum : ∀ {m} → Vec Nat m → Nat
  sum []      = 0
  sum (a ∷ u) = a + sum u

  ext0 : ∀ {m} (a b : Vec Nat m) → (∀ k → at0 a k ≡ at0 b k) → sum a ≡ sum b
  ext0 a b h = cong sum (vext a b h)

cancel-except : ∀ {m} (a b : Vec Nat m) i → (∀ k → (k ≡ i → ⊥) → at0 a k ≡ at0 b k) →
                sum a ≡ sum b → at0 a i ≡ at0 b i
cancel-except [] [] i h e = refl
cancel-except (x ∷ a) (y ∷ b) zero h e =
  +-cancelʳ′ x y (sum a) (trans e (cong (y +_) (sym (ext0 a b (λ k → h (suc k) (λ ()))))))
  where
  +-cancelʳ′ : ∀ x y s → x + s ≡ y + s → x ≡ y
  +-cancelʳ′ x y s p = +-cancelˡ s x y (trans (+-comm s x) (trans p (+-comm y s)))
cancel-except (x ∷ a) (y ∷ b) (suc i) h e =
  cancel-except a b i (λ k ne → h (suc k) (λ q → ne (suc-inj″ q)))
    (+-cancelˡ x (sum a) (sum b) (trans e (cong (_+ sum b) (sym (h 0 (λ ()))))))
  where
  suc-inj″ : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj″ refl = refl

module Sum {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L

  ----------------------------------------------------------------------
  -- Σ cᵢ⟨i⟩, row by row; one component (fst or snd) at a time.

  Side : Set
  Side = Row → Vec Nat N

  esum : ∀ {m} → Side → Vec Nat m → Nat → Nat → Vec Nat N
  esum σ []      o j = 0c
  esum σ (k ∷ c) o j = (k ⊙ σ (ent o j)) +c esum σ c (suc o) j

  -- The terms of coordinate d.
  terms : ∀ {m} → Side → Vec Nat m → Nat → Nat → Nat → Vec Nat m
  terms σ []      o j d = []
  terms σ (k ∷ c) o j d = (k * at0 (σ (ent o j)) d) ∷ terms σ c (suc o) j d

  private
    at-⊙ : ∀ k (v : Vec Nat N) d → at0 (k ⊙ v) d ≡ k * at0 v d
    at-⊙ zero    v d = at-0c {N} d
    at-⊙ (suc k) v d = trans (at-+c v (k ⊙ v) d) (cong (at0 v d +_) (at-⊙ k v d))

  at-esum : ∀ {m} σ (c : Vec Nat m) o j d → at0 (esum σ c o j) d ≡ sum (terms σ c o j d)
  at-esum σ []      o j d = at-0c {N} d
  at-esum σ (k ∷ c) o j d = trans (at-+c (k ⊙ σ (ent o j)) (esum σ c (suc o) j) d)
                                  (cong₂ _+_ (at-⊙ k (σ (ent o j)) d) (at-esum σ c (suc o) j d))

  at-terms : ∀ {m} σ (c : Vec Nat m) o j d k → at0 (terms σ c o j d) k ≡ at0 c k * at0 (σ (ent (k + o) j)) d
  at-terms σ []      o j d k       = refl
  at-terms σ (x ∷ c) o j d zero    = refl
  at-terms σ (x ∷ c) o j d (suc k) = trans (at-terms σ c (suc o) j d k) (cong (λ t → at0 (x ∷ c) (suc k) * at0 (σ (ent t j)) d) (+-suc k o))

  ----------------------------------------------------------------------
  -- Injectivity: count vectors supported on degrees in (r, L].

  private
    at-unit-self : ∀ {m} i → i < m → at0 (unit {m} i) i ≡ 1
    at-unit-self {suc m} zero    _       = refl
    at-unit-self {suc m} (suc i) (s≤s l) = at-unit-self {m} i l

    at-unit-other : ∀ {m} k i → (k ≡ i → ⊥) → at0 (unit {m} k) i ≡ 0
    at-unit-other {m} k i ne with tri k i
    ... | tri< l    = unit-Lo {m} k i l
    ... | tri≡ e    = ⊥-elim (ne e)
    ... | tri> l    = unit-Hi {m} k i l

    ent-top : ∀ k → ent k (deg k) ≡ (unit k , unit k)
    ent-top k = Cells.Deg.ent-in dd deg-dp deg-dm k (deg k) 0 (sym (+-zero (deg k)))

    -- Coordinate i of fst (ent k d), for deg i ≡ d ≤ deg k and k ≠ i
    -- with deg k ≡ d, or deg k < d.
    ent-col0 : ∀ k i → (k ≡ i → ⊥) → deg k ≤ deg i → at0 (fst (ent k (deg i))) i ≡ 0
    ent-col0 k i ne l with tri (deg k) (deg i)
    ... | tri< kl = cong (λ e → at0 (fst e) i) (ent-zero k (deg i) kl) ∙ at-0c {N} i
      where _∙_ = trans
    ... | tri≡ e  = trans (cong (λ t → at0 (fst (ent k t)) i) (sym e))
                          (trans (cong (λ e → at0 (fst e) i) (ent-top k)) (at-unit-other {N} k i ne))
    ... | tri> kl = ⊥-elim (≤-<-⊥ l kl)

  Supp : Nat → Vec Nat N → Set
  Supp r c = ∀ k → ((deg k ≤ r) ⊎ (L < deg k)) → at0 c k ≡ 0

  module _ (r : Nat) (c1 c2 : Vec Nat N) (s1 : Supp r c1) (s2 : Supp r c2)
           (ag : ∀ j → r < j → j ≤ L → esum fst c1 0 j ≡ esum fst c2 0 j) where

    private
      R : Nat → Set
      R t = ∀ i → t ≤ deg i → at0 c1 i ≡ at0 c2 i

      at-out : ∀ {m} (c : Vec Nat m) i → (i < m → ⊥) → at0 c i ≡ 0
      at-out []      i       _  = refl
      at-out (x ∷ c) zero    ne = ⊥-elim (ne (s≤s z≤n))
      at-out (x ∷ c) (suc i) ne = at-out c i (λ l → ne (s≤s l))

      *-zero : ∀ n → n * 0 ≡ 0
      *-zero zero    = refl
      *-zero (suc n) = *-zero n

      *-one : ∀ n → n * 1 ≡ n
      *-one zero    = refl
      *-one (suc n) = cong suc (*-one n)

      ≤-≡ : ∀ {a b} → a ≡ b → a ≤ b
      ≤-≡ refl = ≤-refl _

      both0 : ∀ i → ((deg i ≤ r) ⊎ (L < deg i)) → at0 c1 i ≡ at0 c2 i
      both0 i h = trans (s1 i h) (sym (s2 i h))

      -- Row deg i, coordinate i.
      row : ∀ t → R (suc t) → ∀ i → deg i ≡ t → r < t → t ≤ L → at0 c1 i ≡ at0 c2 i
      row t ih i refl rt tL with tri i N
      ... | tri≡ e = trans (at-out c1 i (λ l → ≤-<-⊥ (≤-refl′ e) l)) (sym (at-out c2 i (λ l → ≤-<-⊥ (≤-refl′ e) l)))
        where
        ≤-refl′ : ∀ {a b} → a ≡ b → b ≤ a
        ≤-refl′ refl = ≤-refl _
      ... | tri> l = trans (at-out c1 i (λ l′ → ≤-<-⊥ (<→≤ l) l′)) (sym (at-out c2 i (λ l′ → ≤-<-⊥ (<→≤ l) l′)))
      ... | tri< iN = goal
        where
        tk : ∀ (c : Vec Nat N) k → at0 (terms fst c 0 (deg i) i) k ≡ at0 c k * at0 (fst (ent k (deg i))) i
        tk c k = trans (at-terms fst c 0 (deg i) i k) (cong (λ t → at0 c k * at0 (fst (ent t (deg i))) i) (+-zero k))
        x : Nat → Nat
        x k = at0 (fst (ent k (deg i))) i
        x-self : x i ≡ 1
        x-self = trans (cong (λ e → at0 (fst e) i) (ent-top i)) (at-unit-self {N} i iN)
        e : sum (terms fst c1 0 (deg i) i) ≡ sum (terms fst c2 0 (deg i) i)
        e = trans (sym (at-esum fst c1 0 (deg i) i))
              (trans (cong (λ v → at0 v i) (ag (deg i) rt tL)) (at-esum fst c2 0 (deg i) i))
        h : ∀ k → (k ≡ i → ⊥) → at0 (terms fst c1 0 (deg i) i) k ≡ at0 (terms fst c2 0 (deg i) i) k
        h k ne with tri (deg i) (deg k)
        ... | tri< l = trans (tk c1 k) (trans (cong (_* x k) (ih k l)) (sym (tk c2 k)))
        ... | tri≡ q = trans (tk c1 k) (trans (cong (at0 c1 k *_) z) (trans (*-zero (at0 c1 k))
                         (sym (trans (tk c2 k) (trans (cong (at0 c2 k *_) z) (*-zero (at0 c2 k)))))))
          where z = ent-col0 k i ne (≤-≡ (sym q))
        ... | tri> l = trans (tk c1 k) (trans (cong (at0 c1 k *_) z) (trans (*-zero (at0 c1 k))
                         (sym (trans (tk c2 k) (trans (cong (at0 c2 k *_) z) (*-zero (at0 c2 k)))))))
          where z = ent-col0 k i ne (<→≤ l)
        goal : at0 c1 i ≡ at0 c2 i
        goal = trans (sym (*-one (at0 c1 i)))
                 (trans (cong (at0 c1 i *_) (sym x-self))
                   (trans (sym (tk c1 i)) (trans (cancel-except (terms fst c1 0 (deg i) i) (terms fst c2 0 (deg i) i) i h e)
                     (trans (tk c2 i) (trans (cong (at0 c2 i *_) x-self) (*-one (at0 c2 i)))))))

      down : ∀ t → R (suc t) → R t
      down t ih i ti with tri t (deg i)
      ... | tri< l    = ih i l
      ... | tri> l    = ⊥-elim (≤-<-⊥ ti l)
      ... | tri≡ refl with tri r (deg i) | tri L (deg i)
      ... | _      | tri< lL = both0 i (inj₂ lL)
      ... | tri< rl | tri≡ e  = row (deg i) ih i refl rl (≤-≡ (sym e))
      ... | tri< rl | tri> lL = row (deg i) ih i refl rl (<→≤ lL)
      ... | tri≡ e  | _       = both0 i (inj₁ (≤-≡ (sym e)))
      ... | tri> l  | _       = both0 i (inj₁ (<→≤ l))

      desc : ∀ n t → n + t ≡ suc L → R t
      desc zero    t refl = λ i l → both0 i (inj₂ l)
      desc (suc n) t e    = down t (desc n (suc t) (trans (+-suc n t) e))

    esum-inj : c1 ≡ c2
    esum-inj = vext c1 c2 (λ i → desc (suc L) 0 (+-zero (suc L)) i z≤n)
