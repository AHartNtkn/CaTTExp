------------------------------------------------------------------------
-- Strict ω-categories over a setoid (ledger C5b, step M1 of the 𝔖
-- instance).
--
-- Same axioms as CaTTExp.Strict.Omega.ωCat (Street 1987 §1; Steiner
-- 2004 Def. 2.1), but cells form a setoid: equations hold up to an
-- equivalence _≈_, and composition depends only on the ≈-classes of
-- its arguments (comp-cong), not on the composability proof. This is
-- what the Gray tensor and the closures of *arbitrary* strict
-- ω-categories need: they are presented by generators and relations,
-- and --safe Agda has no quotients.
--
-- Every ωCat is an ωCatS with ≈ = ≡ (`fromωCat`). Strict functors
-- preserve ≈, boundaries and composites up to ≈; functors are compared
-- pointwise. Nothing is postulated.
------------------------------------------------------------------------
module CaTTExp.Strict.OmegaS where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; _<_; ωCat; uip)

record ωCatS : Set₁ where
  infix 4 _≈_
  field
    C     : Set
    _≈_   : C → C → Set
    ≈-refl  : ∀ {x} → x ≈ x
    ≈-sym   : ∀ {x y} → x ≈ y → y ≈ x
    ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    src  : Nat → C → C
    tgt  : Nat → C → C
    comp : ∀ n (x y : C) → tgt n x ≈ src n y → C

    src-cong  : ∀ n {x x′} → x ≈ x′ → src n x ≈ src n x′
    tgt-cong  : ∀ n {x x′} → x ≈ x′ → tgt n x ≈ tgt n x′
    comp-cong : ∀ n {x x′ y y′} p p′ → x ≈ x′ → y ≈ y′ → comp n x y p ≈ comp n x′ y′ p′

    -- (i) boundaries of boundaries
    src-src-< : ∀ {m n} x → m < n → src m (src n x) ≈ src m x
    src-tgt-< : ∀ {m n} x → m < n → src m (tgt n x) ≈ src m x
    tgt-src-< : ∀ {m n} x → m < n → tgt m (src n x) ≈ tgt m x
    tgt-tgt-< : ∀ {m n} x → m < n → tgt m (tgt n x) ≈ tgt m x
    src-src-≥ : ∀ {m n} x → n ≤ m → src m (src n x) ≈ src n x
    tgt-src-≥ : ∀ {m n} x → n ≤ m → tgt m (src n x) ≈ src n x
    src-tgt-≥ : ∀ {m n} x → n ≤ m → src m (tgt n x) ≈ tgt n x
    tgt-tgt-≥ : ∀ {m n} x → n ≤ m → tgt m (tgt n x) ≈ tgt n x

    -- (iii) boundaries of composites
    src-comp : ∀ n x y p → src n (comp n x y p) ≈ src n x
    tgt-comp : ∀ n x y p → tgt n (comp n x y p) ≈ tgt n y
    src-comp-< : ∀ {m n} x y p → m < n → src m (comp n x y p) ≈ src m x
    tgt-comp-< : ∀ {m n} x y p → m < n → tgt m (comp n x y p) ≈ tgt m y
    src-comp-> : ∀ {m n} x y p → n < m → ∀ q → src m (comp n x y p) ≈ comp n (src m x) (src m y) q
    tgt-comp-> : ∀ {m n} x y p → n < m → ∀ q → tgt m (comp n x y p) ≈ comp n (tgt m x) (tgt m y) q

    -- (iv) units
    unit-l : ∀ n x p → comp n (src n x) x p ≈ x
    unit-r : ∀ n x p → comp n x (tgt n x) p ≈ x

    -- (v) associativity
    assoc : ∀ n x y z p q p′ q′ → comp n (comp n x y p) z q ≈ comp n x (comp n y z p′) q′

    -- (vi) interchange
    interchange : ∀ {m n} x y z w → m < n → ∀ p q r r₁ r₂ r₃ →
                  comp m (comp n x y p) (comp n z w q) r ≈ comp n (comp m x z r₁) (comp m y w r₂) r₃

------------------------------------------------------------------------
-- Every ωCat is an ωCatS, with ≈ = ≡.

fromωCat : ωCat → ωCatS
fromωCat 𝒞 = record
  { C = C ; _≈_ = _≡_ ; ≈-refl = refl ; ≈-sym = sym ; ≈-trans = trans
  ; src = src ; tgt = tgt ; comp = comp
  ; src-cong = λ n → cong (src n) ; tgt-cong = λ n → cong (tgt n)
  ; comp-cong = λ n p p′ ex ey → cc n p p′ ex ey
  ; src-src-< = src-src-< ; src-tgt-< = src-tgt-< ; tgt-src-< = tgt-src-< ; tgt-tgt-< = tgt-tgt-<
  ; src-src-≥ = src-src-≥ ; tgt-src-≥ = tgt-src-≥ ; src-tgt-≥ = src-tgt-≥ ; tgt-tgt-≥ = tgt-tgt-≥
  ; src-comp = src-comp ; tgt-comp = tgt-comp ; src-comp-< = src-comp-< ; tgt-comp-< = tgt-comp-<
  ; src-comp-> = src-comp-> ; tgt-comp-> = tgt-comp->
  ; unit-l = unit-l ; unit-r = unit-r ; assoc = assoc ; interchange = interchange }
  where
    open ωCat 𝒞
    cc : ∀ n {x x′ y y′} (p : tgt n x ≡ src n y) (p′ : tgt n x′ ≡ src n y′) →
         x ≡ x′ → y ≡ y′ → comp n x y p ≡ comp n x′ y′ p′
    cc n p p′ refl refl = cong (comp n _ _) (uip p p′)

------------------------------------------------------------------------
-- Strict functors.

record Functor (𝒜 ℬ : ωCatS) : Set where
  private
    module A = ωCatS 𝒜
    module B = ωCatS ℬ
  field
    F      : A.C → B.C
    F-cong : ∀ {x x′} → x A.≈ x′ → F x B.≈ F x′
    F-src  : ∀ n x → F (A.src n x) B.≈ B.src n (F x)
    F-tgt  : ∀ n x → F (A.tgt n x) B.≈ B.tgt n (F x)

  -- composability of images
  F-comp-ok : ∀ n {x y} → A.tgt n x A.≈ A.src n y → B.tgt n (F x) B.≈ B.src n (F y)
  F-comp-ok n {x} {y} p = B.≈-trans (B.≈-sym (F-tgt n x)) (B.≈-trans (F-cong p) (F-src n y))

  field
    F-comp : ∀ n x y p → F (A.comp n x y p) B.≈ B.comp n (F x) (F y) (F-comp-ok n p)

open Functor public

-- Pointwise equality of functors.
_≃_ : ∀ {𝒜 ℬ} → Functor 𝒜 ℬ → Functor 𝒜 ℬ → Set
_≃_ {𝒜} {ℬ} f g = ∀ x → F f x B.≈ F g x
  where module B = ωCatS ℬ

module _ {𝒜 : ωCatS} where
  private module A = ωCatS 𝒜

  idF : Functor 𝒜 𝒜
  idF = record
    { F = λ x → x ; F-cong = λ e → e
    ; F-src = λ _ _ → A.≈-refl ; F-tgt = λ _ _ → A.≈-refl
    ; F-comp = λ n x y p → A.comp-cong n p _ A.≈-refl A.≈-refl }

module _ {𝒜 ℬ 𝒞 : ωCatS} where
  private
    module A = ωCatS 𝒜
    module B = ωCatS ℬ
    module K = ωCatS 𝒞

  _∘F_ : Functor ℬ 𝒞 → Functor 𝒜 ℬ → Functor 𝒜 𝒞
  g ∘F f = record
    { F = λ x → F g (F f x)
    ; F-cong = λ e → F-cong g (F-cong f e)
    ; F-src = λ n x → K.≈-trans (F-cong g (F-src f n x)) (F-src g n (F f x))
    ; F-tgt = λ n x → K.≈-trans (F-cong g (F-tgt f n x)) (F-tgt g n (F f x))
    ; F-comp = λ n x y p →
        K.≈-trans (F-cong g (F-comp f n x y p))
        (K.≈-trans (F-comp g n (F f x) (F f y) (F-comp-ok f n p))
                   (K.comp-cong n _ _ K.≈-refl K.≈-refl)) }

  ∘F-cong : ∀ {g g′ : Functor ℬ 𝒞} {f f′ : Functor 𝒜 ℬ} → g ≃ g′ → f ≃ f′ → (g ∘F f) ≃ (g′ ∘F f′)
  ∘F-cong {g} {g′} {f} {f′} eg ef x = K.≈-trans (F-cong g (ef x)) (eg (F f′ x))

------------------------------------------------------------------------
-- Category laws for functors, up to ≃.

module _ {𝒜 ℬ : ωCatS} (f : Functor 𝒜 ℬ) where
  private module B = ωCatS ℬ

  ∘F-idl : (idF ∘F f) ≃ f
  ∘F-idl x = B.≈-refl

  ∘F-idr : (f ∘F idF) ≃ f
  ∘F-idr x = B.≈-refl

module _ {𝒜 ℬ 𝒞 𝒟 : ωCatS} (h : Functor 𝒞 𝒟) (g : Functor ℬ 𝒞) (f : Functor 𝒜 ℬ) where
  private module D = ωCatS 𝒟

  ∘F-assoc : ((h ∘F g) ∘F f) ≃ (h ∘F (g ∘F f))
  ∘F-assoc x = D.≈-refl
