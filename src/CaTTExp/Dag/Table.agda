------------------------------------------------------------------------
-- Sharing-aware syntax: CaTT terms as a table of items addressed by
-- natural numbers ("ids"), every reference pointing to a smaller id.
--
--   V i        the variable of level i
--   C h as     coh over the head h, applied to the arguments as
--              (LAST ARGUMENT FIRST, matching the snoc order of Sub)
--   E          the empty context
--   S c A      the context c extended by the type A
--   H c A      a coherence head: the context c and the type A
--
-- A type is an RTy: ⋆ᵣ, or arrᵣ A s t with s and t ids of term items.
--
-- The table is any function R : Nat → Maybe Item. `Unfold R` turns ids
-- back into ordinary CaTT syntax (CaTTExp.Syntax), with fuel; when the
-- table is decreasing the fuel does not matter (Unfold.tm-irr), so the
-- denotation of an id is ⟦ n ⟧ = tmU (suc n) n.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure

module CaTTExp.Dag.Table where

data RTy : Set where
  ⋆ᵣ   : RTy
  arrᵣ : RTy → Nat → Nat → RTy

data Item : Set where
  V : Nat → Item
  C : Nat → List Nat → Item
  E : Item
  S : Nat → RTy → Item
  H : Nat → RTy → Item

------------------------------------------------------------------------
-- Equality of RTy, and lists of ids

_==R_ : RTy → RTy → Bool
⋆ᵣ          ==R ⋆ᵣ            = true
arrᵣ A s t  ==R arrᵣ B s' t'  = (A ==R B) ∧ ((s ==ℕ s') ∧ (t ==ℕ t'))
_           ==R _             = false

==R-sound : ∀ A B → T (A ==R B) → A ≡ B
==R-sound ⋆ᵣ ⋆ᵣ _ = refl
==R-sound (arrᵣ A s t) (arrᵣ B s' t') p
  with ==R-sound A B (∧-fst p)
     | ==ℕ-sound s s' (∧-fst (∧-snd {A ==R B} p))
     | ==ℕ-sound t t' (∧-snd {s ==ℕ s'} (∧-snd {A ==R B} p))
... | refl | refl | refl = refl

-- All ids occurring in an RTy are below k.
belowR : Nat → RTy → Bool
belowR k ⋆ᵣ           = true
belowR k (arrᵣ A s t) = belowR k A ∧ ((s <ℕ k) ∧ (t <ℕ k))

belowL : Nat → List Nat → Bool
belowL k []       = true
belowL k (a ∷ as) = (a <ℕ k) ∧ belowL k as

-- Every reference of the item stored at id k points below k.
decItem : Nat → Item → Bool
decItem k (V _)    = true
decItem k (C h as) = (h <ℕ k) ∧ belowL k as
decItem k E        = true
decItem k (S c A)  = (c <ℕ k) ∧ belowR k A
decItem k (H c A)  = (c <ℕ k) ∧ belowR k A

------------------------------------------------------------------------
-- Arithmetic on the builtin order

∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro {true} _ q = q

<-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans zero    (suc b) (suc c) _ _ = tt
<-trans (suc a) (suc b) (suc c) p q = <-trans a b c p q

<-suc : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
<-suc zero    _       _ = tt
<-suc (suc a) (suc b) p = <-suc a b p

-- a < b and b < suc f give a < f
<-pred : ∀ a b f → T (a <ℕ b) → T (b <ℕ suc f) → T (a <ℕ f)
<-pred zero    (suc b) (suc f) _ _ = tt
<-pred (suc a) (suc b) (suc f) p q = <-pred a b f p q

<-suc-self : ∀ n → T (n <ℕ suc n)
<-suc-self zero    = tt
<-suc-self (suc n) = <-suc-self n

belowR-mono : ∀ j k A → T (j <ℕ suc k) → T (belowR j A) → T (belowR k A)
belowR-mono j k ⋆ᵣ _ _ = tt
belowR-mono j k (arrᵣ A s t) jk p =
  let q = ∧-snd {belowR j A} p in
  ∧-intro (belowR-mono j k A jk (∧-fst p))
    (∧-intro (<-pred s j k (∧-fst q) jk) (<-pred t j k (∧-snd {s <ℕ j} q) jk))

belowL-mono : ∀ j k as → T (j <ℕ suc k) → T (belowL j as) → T (belowL k as)
belowL-mono j k []       _  _ = tt
belowL-mono j k (a ∷ as) jk p =
  ∧-intro (<-pred a j k (∧-fst p) jk) (belowL-mono j k as jk (∧-snd {a <ℕ j} p))
