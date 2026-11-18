------------------------------------------------------------------------
-- F2c: every pasting context lists the source of each cell before its
-- target, the hypothesis `Ord` of CaTTExp.GlobularTotal.Uniq.
--
--   ps-ord : Γ ⊢ps → lookup Γ y ≡ just (arr B (var a) (var b)) → a < b
--
-- by induction on the ⊢ps derivation, carrying that the dangling
-- variable is in scope, has its type, and that type's endpoints are in
-- scope with the right types.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.PsOrd where

open import CaTTExp.Prelude
open import CaTTExp.Pure

private
  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  ==-refl : ∀ a → (a ==ℕ a) ≡ true
  ==-refl a = T-≡ (==ℕ-refl a)

  ==-sound : ∀ a b → (a ==ℕ b) ≡ true → a ≡ b
  ==-sound a b e = ==ℕ-sound a b (≡-T e)

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  lookup-weak : ∀ Γ C y → T (y <ℕ len Γ) → lookup (Γ ▸ C) y ≡ lookup Γ y
  lookup-weak Γ C y p rewrite <-ne y (len Γ) p = refl

  lookup-top : ∀ Γ C → lookup (Γ ▸ C) (len Γ) ≡ just C
  lookup-top Γ C rewrite ==-refl (len Γ) = refl

Ord : Ctx → Set
Ord Γ = ∀ y B a b → lookup Γ y ≡ just (arr B (var a) (var b)) → T (a <ℕ b)

-- The endpoints of A are in scope with the right types.
TyIn : Ctx → Ty → Set
TyIn Γ ⋆                       = ⊤
TyIn Γ (arr B (var a) (var b)) =
  T (a <ℕ len Γ) × T (b <ℕ len Γ) × (lookup Γ a ≡ just B) × (lookup Γ b ≡ just B) × TyIn Γ B
TyIn Γ (arr B _ _)             = ⊥

private
  tyin-weak : ∀ Γ C A → TyIn Γ A → TyIn (Γ ▸ C) A
  tyin-weak Γ C ⋆ _ = tt
  tyin-weak Γ C (arr B (var a) (var b)) (pa , pb , ea , eb , t) =
    <-weak a (len Γ) pa , <-weak b (len Γ) pb ,
    trans (lookup-weak Γ C a pa) ea , trans (lookup-weak Γ C b pb) eb ,
    tyin-weak Γ C B t
  tyin-weak Γ C (arr B (var a) (coh _ _ _)) ()
  tyin-weak Γ C (arr B (var a) (cst ()))    _
  tyin-weak Γ C (arr B (coh _ _ _) _)       ()
  tyin-weak Γ C (arr B (cst ()) _)          _

Inv : Ctx → Nat → Ty → Set
Inv Γ x A = T (x <ℕ len Γ) × (lookup Γ x ≡ just A) × TyIn Γ A × Ord Γ

inv : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Inv Γ x A
inv pss = tt , refl , tt , ord₀
  where
  ord₀ : Ord (ε ▸ ⋆)
  ord₀ y B a b e with y ==ℕ 0
  ord₀ y B a b () | true
  ord₀ y B a b () | false
inv (pse {Γ} {x} {A} d) with inv d
... | px , ex , tA , oΓ =
  <-suc (suc (len Γ)) ,
  lookup-top (Γ ▸ A) _ ,
  ( <-weak x (suc (len Γ)) (<-weak x (len Γ) px)
  , <-weak (len Γ) (suc (len Γ)) (<-suc (len Γ))
  , trans (lookup-weak (Γ ▸ A) _ x (<-weak x (len Γ) px)) (trans (lookup-weak Γ A x px) ex)
  , trans (lookup-weak (Γ ▸ A) _ (len Γ) (<-suc (len Γ))) (lookup-top Γ A)
  , tyin-weak (Γ ▸ A) _ A (tyin-weak Γ A A tA) ) ,
  ord′
  where
  ord′ : Ord (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
  ord′ y B a b e with y ==ℕ suc (len Γ) in e₁
  ... | true with just-inj e
  ...   | refl = px
  ord′ y B a b e | false with y ==ℕ len Γ in e₂
  ... | true rewrite ==-sound y (len Γ) e₂ = oΓ x B a b (trans ex e)
  ... | false = oΓ y B a b e
inv (psd d) with inv d
... | _ , _ , (_ , pb , _ , eb , tB) , oΓ = pb , eb , tB , oΓ

ps-ord : ∀ {Γ} → Γ ⊢ps → Ord Γ
ps-ord (ps d) = snd (snd (snd (inv d)))
