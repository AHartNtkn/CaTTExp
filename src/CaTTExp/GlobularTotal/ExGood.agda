------------------------------------------------------------------------
-- F2c: diagrams of Θ are compatible (FlatBd.Good) under any images of
-- Θ's variables that respect their types.
--
-- `TypedImg J` says: for each variable y : A of Θ, J y is a well-formed
-- tree of dimension at most dim A, and if A = (a → b) over B, the
-- dim B boundaries of J y are J a and J b. The images of a typed
-- substitution (by the induction (1′)) are of this kind. Then
--
--   ex-good : Ex e nothing a → Good J e Top a
--
-- so 1b's compatibility hypotheses reduce to typing of the images.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.ExGood where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.FlatBd
open import CaTTExp.GlobularTotal.Uniq

private
  Top : LT → Set
  Top _ = ⊤

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

Bnd : (Nat → Maybe LT) → Ty → LT → Set
Bnd J ⋆                        x = ⊤
Bnd J (arr B (var a) (var b))  x = (J a ≡ just (bd false (dim B) x)) × (J b ≡ just (bd true (dim B) x))
Bnd J (arr B _ _)              x = ⊥

module _ (Θ : Ctx) (J : Nat → Maybe LT) where

  TypedImg : Set
  TypedImg = ∀ y A → lookup Θ y ≡ just A →
             Σ LT λ x → (J y ≡ just x) × WF x × (∀ β i → bd β (dim A + i) x ≡ x) × Bnd J A x

  private
    dimOf-lookup : ∀ y A → lookup Θ y ≡ just A → dimOf Θ y ≡ dim A
    dimOf-lookup y A e with lookup Θ y
    dimOf-lookup y A refl | .(just A) = refl

  module _ (ti : TypedImg) where

    private
      dim-fix : ∀ e o A x → lookup Θ o ≡ just A → dimOf Θ o ≡ e →
                (∀ β i → bd β (dim A + i) x ≡ x) → ∀ β i → bd β (e + i) x ≡ x
      dim-fix e o A x eo d dx β i =
        subst (λ n → bd β (n + i) x ≡ x) (trans (sym (dimOf-lookup o A eo)) d) (dx β i)

      ok-root : ∀ e o → Cell Θ e nothing o → Ok J e Top o
      ok-root e o ((A , eo) , d) with ti o A eo
      ... | x , ex , wx , dx , _ = x , ex , wx , dim-fix e o A x eo d dx , tt

      ok-br : ∀ e p q o → Cell Θ (suc e) (just (p , q)) o → Ok J (suc e) (Par J e p q) o
      ok-br e p q o ((B , eo) , d) with ti o (arr B (var p) (var q)) eo
      ... | x , ex , wx , dx , (ep , eq) =
        x , ex , wx , dim-fix (suc e) o _ x eo d dx ,
        subst (λ n → (J p ≡ just (bd false n x)) × (J q ≡ just (bd true n x))) dB (ep , eq)
        where
        dB : dim B ≡ e
        dB = suc-inj (trans (sym (dimOf-lookup o _ eo)) d)

      all-root : ∀ e os → AllN (Cell Θ e nothing) os → AllL J (Ok J e Top) os
      all-root e []       _        = tt
      all-root e (o ∷ os) (c , cs) = ok-root e o c , all-root e os cs

      all-br : ∀ e p q os → AllN (Cell Θ (suc e) (just (p , q))) os →
               AllL J (Ok J (suc e) (Par J e p q)) os
      all-br e p q []       _        = tt
      all-br e p q (o ∷ os) (c , cs) = ok-br e p q o c , all-br e p q os cs

    mutual
      ex-good : ∀ e a → Ex Θ e nothing a → Good J e Top a
      ex-good e (lt os cs) (oks , x) = all-root e os oks , exCs-good e os cs x

      ex-good-br : ∀ e p q a → Ex Θ (suc e) (just (p , q)) a → Good J (suc e) (Par J e p q) a
      ex-good-br e p q (lt os cs) (oks , x) = all-br e p q os oks , exCs-good (suc e) os cs x

      exCs-good : ∀ e os cs → ExCs Θ e os cs → GoodCs J e os cs
      exCs-good e []            cs       ()
      exCs-good e (o ∷ [])      []       x = tt
      exCs-good e (o ∷ [])      (c ∷ cs) ()
      exCs-good e (o ∷ o' ∷ os) []       ()
      exCs-good e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) =
        ex-good-br e o o' c xc , exCs-good e (o' ∷ os) cs xs
