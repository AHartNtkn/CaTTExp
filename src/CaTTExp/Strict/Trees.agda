------------------------------------------------------------------------
-- Labelled Batanin trees (ledger item A3a, general case).
--
-- A tree at level k labelled in A is `node x₀ [(T₁, x₁) … (Tₘ, xₘ)]`:
-- x₀ … xₘ label the k-cells along the spine, and Tᵢ is a tree at level
-- k+1 labelling the pasting diagram between x_{i−1} and xᵢ. Truncation
-- (`bdm`, `bdp`) and gluing (`glue`) take a height d relative to the
-- tree's own level.
------------------------------------------------------------------------
module CaTTExp.Strict.Trees where

open import CaTTExp.Prelude

mutual
  data LT (A : Set) : Set where
    node : A → Br A → LT A

  data Br (A : Set) : Set where
    nil  : Br A
    cons : LT A → A → Br A → Br A

module _ {A : Set} where

  lastv : A → Br A → A
  lastv x nil          = x
  lastv x (cons _ y r) = lastv y r

  infixr 5 _++B_
  _++B_ : Br A → Br A → Br A
  nil          ++B r′ = r′
  cons T y r   ++B r′ = cons T y (r ++B r′)

  rootLT : LT A → A
  rootLT (node x _) = x

  kidsLT : LT A → Br A
  kidsLT (node _ r) = r

  hdB : LT A → Br A → LT A
  hdB d nil          = d
  hdB d (cons T _ _) = T

  vB : A → Br A → A
  vB d nil          = d
  vB d (cons _ y _) = y

  tlB : Br A → Br A
  tlB nil          = nil
  tlB (cons _ _ r) = r


  ------------------------------------------------------------------------
  -- Truncation at relative height d (the tree's own level is 0).

  mutual
    bdm : Nat → LT A → LT A
    bdm zero    (node x r) = node x nil
    bdm (suc d) (node x r) = node x (bdmB d r)

    bdmB : Nat → Br A → Br A
    bdmB d nil          = nil
    bdmB d (cons T y r) = cons (bdm d T) y (bdmB d r)

  mutual
    bdp : Nat → LT A → LT A
    bdp zero    (node x r) = node (lastv x r) nil
    bdp (suc d) (node x r) = node x (bdpB d r)

    bdpB : Nat → Br A → Br A
    bdpB d nil          = nil
    bdpB d (cons T y r) = cons (bdp d T) y (bdpB d r)

  ------------------------------------------------------------------------
  -- Gluing along relative height d.

  mutual
    glue : Nat → LT A → LT A → LT A
    glue zero    (node x r₁) (node _ r₂) = node x (r₁ ++B r₂)
    glue (suc d) (node x r₁) (node _ r₂) = node x (glueB d r₁ r₂)

    glueB : Nat → Br A → Br A → Br A
    glueB d nil            _              = nil
    glueB d (cons T y r)   nil            = cons T y r
    glueB d (cons T₁ y r₁) (cons T₂ _ r₂) = cons (glue d T₁ T₂) y (glueB d r₁ r₂)

  cons-T : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → T ≡ T′
  cons-T {T = T} e = cong (hdB T) e

  cons-y : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → y ≡ y′
  cons-y {y = y} e = cong (vB y) e

  cons-r : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → r ≡ r′
  cons-r e = cong tlB e

  node-x : ∀ {x x′ r r′} → node x r ≡ node x′ r′ → x ≡ x′
  node-x e = cong rootLT e

  node-r : ∀ {x x′ r r′} → node x r ≡ node x′ r′ → r ≡ r′
  node-r e = cong kidsLT e

