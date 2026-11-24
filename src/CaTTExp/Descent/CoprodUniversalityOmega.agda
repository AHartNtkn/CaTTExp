------------------------------------------------------------------------
-- Ledger F12d (notes/descent-vs-init.md §5b): soundness of U-⊔ and U-∅
-- in strict ω-categories (the ωCat record of CaTTExp.Strict.Omega,
-- functors of CaTTExp.Strict.Expr).
--
--   (U-⊔)  f : W → A ⊔ B  ⟹  (W ×_{A⊔B} A) ⊔ (W ×_{A⊔B} B) → W  invertible
--   (U-∅)  f : W → ∅      ⟹  f invertible
--
-- Machine-checked (no postulates; K is used, as in Strict.Omega):
--   * `_⊕_`: the coproduct of two strict ω-categories (disjoint union),
--     with injections, copairing (`copair`) and uniqueness of copairing
--     up to pointwise equality (`copair-uni`);
--   * `Pb`: for a functor f : W → A ⊕ B and a side s, the full
--     sub-ω-category of W on the cells sent to side s, with its legs,
--     and its universal property as the pullback of the injection
--     (`Pb.fac`, `Pb.fac-incl`, `Pb.fac-leg`, `Pb.fac-uni`);
--   * `U-⊔`: the comparison Pb true ⊕ Pb false → W is a functor with a
--     two-sided inverse functor (pointwise);
--   * `U-∅`: the empty ω-category 𝟘 is initial, and every functor
--     W → 𝟘 has an inverse functor.
--
-- Scope and honesty notes.
--   * This is the strict (1-categorical, strict ω-category) model:
--     equality of functors is pointwise equality of cell maps.  The
--     claim for Cat_(∞,ω) is cited in the note (DESC-grpd soundness,
--     spec §9.2), not encoded.
--   * The pullback is constructed for the coproduct injections only,
--     which is all U-⊔ mentions.
------------------------------------------------------------------------
module CaTTExp.Descent.CoprodUniversalityOmega where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Expr using (Functor)

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

unL : ∀ {A B : Set} {a a′ : A} → inl {B = B} a ≡ inl a′ → a ≡ a′
unL refl = refl

unR : ∀ {A B : Set} {b b′ : B} → inr {A = A} b ≡ inr b′ → b ≡ b′
unR refl = refl

------------------------------------------------------------------------
-- A bijective functor has an inverse functor.

module Inverse {𝒳 𝒴 : ωCat} (Φ : Functor 𝒳 𝒴) (G : ωCat.C 𝒴 → ωCat.C 𝒳)
               (GF : ∀ x → G (Functor.F Φ x) ≡ x) (FG : ∀ y → Functor.F Φ (G y) ≡ y) where
  private
    module X = ωCat 𝒳
    module Y = ωCat 𝒴
    module XB = Basics 𝒳
  open Functor Φ

  G-src : ∀ n y → G (Y.src n y) ≡ X.src n (G y)
  G-src n y = trans (cong (λ v → G (Y.src n v)) (sym (FG y)))
                (trans (cong G (sym (F-src n (G y)))) (GF _))

  G-tgt : ∀ n y → G (Y.tgt n y) ≡ X.tgt n (G y)
  G-tgt n y = trans (cong (λ v → G (Y.tgt n v)) (sym (FG y)))
                (trans (cong G (sym (F-tgt n (G y)))) (GF _))

  G-comp : ∀ n y y′ p q → G (Y.comp n y y′ p) ≡ X.comp n (G y) (G y′) q
  G-comp n y y′ p q =
    trans (cong G (Basics.comp-cong 𝒴 n p p″ (sym (FG y)) (sym (FG y′))))
      (trans (cong G (sym (F-comp n (G y) (G y′) q p″))) (GF _))
    where
      p″ : Y.tgt n (F (G y)) ≡ Y.src n (F (G y′))
      p″ = trans (cong (Y.tgt n) (FG y)) (trans p (cong (Y.src n) (sym (FG y′))))

  inverse : Functor 𝒴 𝒳
  Functor.F      inverse = G
  Functor.F-src  inverse = G-src
  Functor.F-tgt  inverse = G-tgt
  Functor.F-comp inverse = G-comp

------------------------------------------------------------------------
-- The coproduct of two strict ω-categories.

module Sum (𝒜 ℬ : ωCat) where
  private
    module A = ωCat 𝒜
    module B = ωCat ℬ

  Cs : Set
  Cs = A.C ⊎ B.C

  srcS tgtS : Nat → Cs → Cs
  srcS n (inl a) = inl (A.src n a)
  srcS n (inr b) = inr (B.src n b)
  tgtS n (inl a) = inl (A.tgt n a)
  tgtS n (inr b) = inr (B.tgt n b)

  compS : ∀ n (x y : Cs) → tgtS n x ≡ srcS n y → Cs
  compS n (inl x) (inl y) p = inl (A.comp n x y (unL p))
  compS n (inr x) (inr y) p = inr (B.comp n x y (unR p))
  compS n (inl x) (inr y) ()
  compS n (inr x) (inl y) ()

  open ωCat

  _⊕_ : ωCat
  C    _⊕_ = Cs
  src  _⊕_ = srcS
  tgt  _⊕_ = tgtS
  comp _⊕_ = compS
  src-src-< _⊕_ (inl a) l = cong inl (A.src-src-< a l)
  src-src-< _⊕_ (inr b) l = cong inr (B.src-src-< b l)
  src-tgt-< _⊕_ (inl a) l = cong inl (A.src-tgt-< a l)
  src-tgt-< _⊕_ (inr b) l = cong inr (B.src-tgt-< b l)
  tgt-src-< _⊕_ (inl a) l = cong inl (A.tgt-src-< a l)
  tgt-src-< _⊕_ (inr b) l = cong inr (B.tgt-src-< b l)
  tgt-tgt-< _⊕_ (inl a) l = cong inl (A.tgt-tgt-< a l)
  tgt-tgt-< _⊕_ (inr b) l = cong inr (B.tgt-tgt-< b l)
  src-src-≥ _⊕_ (inl a) l = cong inl (A.src-src-≥ a l)
  src-src-≥ _⊕_ (inr b) l = cong inr (B.src-src-≥ b l)
  tgt-src-≥ _⊕_ (inl a) l = cong inl (A.tgt-src-≥ a l)
  tgt-src-≥ _⊕_ (inr b) l = cong inr (B.tgt-src-≥ b l)
  src-tgt-≥ _⊕_ (inl a) l = cong inl (A.src-tgt-≥ a l)
  src-tgt-≥ _⊕_ (inr b) l = cong inr (B.src-tgt-≥ b l)
  tgt-tgt-≥ _⊕_ (inl a) l = cong inl (A.tgt-tgt-≥ a l)
  tgt-tgt-≥ _⊕_ (inr b) l = cong inr (B.tgt-tgt-≥ b l)
  src-comp _⊕_ n (inl x) (inl y) p = cong inl (A.src-comp n x y (unL p))
  src-comp _⊕_ n (inr x) (inr y) p = cong inr (B.src-comp n x y (unR p))
  src-comp _⊕_ n (inl x) (inr y) ()
  src-comp _⊕_ n (inr x) (inl y) ()
  tgt-comp _⊕_ n (inl x) (inl y) p = cong inl (A.tgt-comp n x y (unL p))
  tgt-comp _⊕_ n (inr x) (inr y) p = cong inr (B.tgt-comp n x y (unR p))
  tgt-comp _⊕_ n (inl x) (inr y) ()
  tgt-comp _⊕_ n (inr x) (inl y) ()
  src-comp-< _⊕_ (inl x) (inl y) p l = cong inl (A.src-comp-< x y (unL p) l)
  src-comp-< _⊕_ (inr x) (inr y) p l = cong inr (B.src-comp-< x y (unR p) l)
  src-comp-< _⊕_ (inl x) (inr y) () l
  src-comp-< _⊕_ (inr x) (inl y) () l
  tgt-comp-< _⊕_ (inl x) (inl y) p l = cong inl (A.tgt-comp-< x y (unL p) l)
  tgt-comp-< _⊕_ (inr x) (inr y) p l = cong inr (B.tgt-comp-< x y (unR p) l)
  tgt-comp-< _⊕_ (inl x) (inr y) () l
  tgt-comp-< _⊕_ (inr x) (inl y) () l
  src-comp-> _⊕_ (inl x) (inl y) p l q = cong inl (A.src-comp-> x y (unL p) l (unL q))
  src-comp-> _⊕_ (inr x) (inr y) p l q = cong inr (B.src-comp-> x y (unR p) l (unR q))
  src-comp-> _⊕_ (inl x) (inr y) () l q
  src-comp-> _⊕_ (inr x) (inl y) () l q
  tgt-comp-> _⊕_ (inl x) (inl y) p l q = cong inl (A.tgt-comp-> x y (unL p) l (unL q))
  tgt-comp-> _⊕_ (inr x) (inr y) p l q = cong inr (B.tgt-comp-> x y (unR p) l (unR q))
  tgt-comp-> _⊕_ (inl x) (inr y) () l q
  tgt-comp-> _⊕_ (inr x) (inl y) () l q
  unit-l _⊕_ n (inl a) p = cong inl (A.unit-l n a (unL p))
  unit-l _⊕_ n (inr b) p = cong inr (B.unit-l n b (unR p))
  unit-r _⊕_ n (inl a) p = cong inl (A.unit-r n a (unL p))
  unit-r _⊕_ n (inr b) p = cong inr (B.unit-r n b (unR p))
  assoc _⊕_ n (inl x) (inl y) (inl z) p q p′ q′ =
    cong inl (A.assoc n x y z (unL p) (unL q) (unL p′) (unL q′))
  assoc _⊕_ n (inr x) (inr y) (inr z) p q p′ q′ =
    cong inr (B.assoc n x y z (unR p) (unR q) (unR p′) (unR q′))
  assoc _⊕_ n (inl x) (inr y) z () q p′ q′
  assoc _⊕_ n (inr x) (inl y) z () q p′ q′
  assoc _⊕_ n (inl x) (inl y) (inr z) p q () q′
  assoc _⊕_ n (inr x) (inr y) (inl z) p q () q′
  interchange _⊕_ (inl x) (inl y) (inl z) (inl w) l p q r r₁ r₂ r₃ =
    cong inl (A.interchange x y z w l (unL p) (unL q) (unL r) (unL r₁) (unL r₂) (unL r₃))
  interchange _⊕_ (inr x) (inr y) (inr z) (inr w) l p q r r₁ r₂ r₃ =
    cong inr (B.interchange x y z w l (unR p) (unR q) (unR r) (unR r₁) (unR r₂) (unR r₃))
  interchange _⊕_ (inl x) (inr y) z w l () q r r₁ r₂ r₃
  interchange _⊕_ (inr x) (inl y) z w l () q r r₁ r₂ r₃
  interchange _⊕_ (inl x) (inl y) (inr z) w l p q r () r₂ r₃
  interchange _⊕_ (inr x) (inr y) (inl z) w l p q r () r₂ r₃
  interchange _⊕_ (inl x) (inl y) (inl z) (inr w) l p () r r₁ r₂ r₃
  interchange _⊕_ (inr x) (inr y) (inr z) (inl w) l p () r r₁ r₂ r₃

  ι₁ : Functor 𝒜 _⊕_
  Functor.F      ι₁ = inl
  Functor.F-src  ι₁ n x = refl
  Functor.F-tgt  ι₁ n x = refl
  Functor.F-comp ι₁ n x y p q = cong inl (cong (A.comp n x y) (uip p (unL q)))

  ι₂ : Functor ℬ _⊕_
  Functor.F      ι₂ = inr
  Functor.F-src  ι₂ n x = refl
  Functor.F-tgt  ι₂ n x = refl
  Functor.F-comp ι₂ n x y p q = cong inr (cong (B.comp n x y) (uip p (unR q)))

  module _ {𝒟 : ωCat} (Gf : Functor 𝒜 𝒟) (Hf : Functor ℬ 𝒟) where
    private
      module D = ωCat 𝒟
      module Gm = Functor Gf
      module Hm = Functor Hf

    [_] : Cs → D.C
    [ inl a ] = Gm.F a
    [ inr b ] = Hm.F b

    copair : Functor _⊕_ 𝒟
    Functor.F      copair = [_]
    Functor.F-src  copair n (inl a) = Gm.F-src n a
    Functor.F-src  copair n (inr b) = Hm.F-src n b
    Functor.F-tgt  copair n (inl a) = Gm.F-tgt n a
    Functor.F-tgt  copair n (inr b) = Hm.F-tgt n b
    Functor.F-comp copair n (inl x) (inl y) p q = Gm.F-comp n x y (unL p) q
    Functor.F-comp copair n (inr x) (inr y) p q = Hm.F-comp n x y (unR p) q
    Functor.F-comp copair n (inl x) (inr y) () q
    Functor.F-comp copair n (inr x) (inl y) () q

    copair-uni : (K : Functor _⊕_ 𝒟) →
                 (∀ a → Functor.F K (inl a) ≡ Gm.F a) → (∀ b → Functor.F K (inr b) ≡ Hm.F b) →
                 ∀ x → Functor.F K x ≡ [ x ]
    copair-uni K kl kr (inl a) = kl a
    copair-uni K kl kr (inr b) = kr b

------------------------------------------------------------------------
-- Pullbacks of the injections along a functor W → A ⊕ B, and U-⊔.

module Universality (𝒜 ℬ 𝒲 : ωCat) where
  open Sum 𝒜 ℬ
  private
    module A = ωCat 𝒜
    module B = ωCat ℬ
    module W = ωCat 𝒲
    module S = ωCat _⊕_

  -- the side of a cell of A ⊕ B
  Is : Bool → Cs → Set
  Is true  (inl _) = ⊤
  Is true  (inr _) = ⊥
  Is false (inl _) = ⊥
  Is false (inr _) = ⊤

  Is-prop : ∀ s x (u v : Is s x) → u ≡ v
  Is-prop true  (inl _) tt tt = refl
  Is-prop false (inr _) tt tt = refl

  Is-src : ∀ s n x → Is s x → Is s (srcS n x)
  Is-src true  n (inl _) u = u
  Is-src false n (inr _) u = u

  Is-tgt : ∀ s n x → Is s x → Is s (tgtS n x)
  Is-tgt true  n (inl _) u = u
  Is-tgt false n (inr _) u = u

  Is-comp : ∀ s n x y p → Is s x → Is s y → Is s (compS n x y p)
  Is-comp true  n (inl _) (inl _) p u v = tt
  Is-comp false n (inr _) (inr _) p u v = tt

  -- the base of side s, its cells, and the injection
  Base : Bool → ωCat
  Base true  = 𝒜
  Base false = ℬ

  get : ∀ s (x : Cs) → Is s x → ωCat.C (Base s)
  get true  (inl a) _ = a
  get false (inr b) _ = b

  put : ∀ s → ωCat.C (Base s) → Cs
  put true  = inl
  put false = inr

  put-get : ∀ s x (u : Is s x) → put s (get s x u) ≡ x
  put-get true  (inl a) u = refl
  put-get false (inr b) u = refl

  Is-put : ∀ s c → Is s (put s c)
  Is-put true  c = tt
  Is-put false c = tt

  inj : ∀ s → Functor (Base s) _⊕_
  inj true  = ι₁
  inj false = ι₂

  get-src : ∀ s n x (u : Is s x) (v : Is s (srcS n x)) →
            get s (srcS n x) v ≡ ωCat.src (Base s) n (get s x u)
  get-src true  n (inl a) u v = refl
  get-src false n (inr b) u v = refl

  get-tgt : ∀ s n x (u : Is s x) (v : Is s (tgtS n x)) →
            get s (tgtS n x) v ≡ ωCat.tgt (Base s) n (get s x u)
  get-tgt true  n (inl a) u v = refl
  get-tgt false n (inr b) u v = refl

  get-comp : ∀ s n x y r (u : Is s x) (v : Is s y) (uv : Is s (compS n x y r))
               (q : ωCat.tgt (Base s) n (get s x u) ≡ ωCat.src (Base s) n (get s y v)) →
             get s (compS n x y r) uv ≡ ωCat.comp (Base s) n (get s x u) (get s y v) q
  get-comp true  n (inl a) (inl a′) r u v uv q = cong (A.comp n a a′) (uip _ q)
  get-comp false n (inr b) (inr b′) r u v uv q = cong (B.comp n b b′) (uip _ q)

  get-put : ∀ s c (u : Is s (put s c)) → get s (put s c) u ≡ c
  get-put true  c u = refl
  get-put false c u = refl

  module Pb (f : Functor 𝒲 _⊕_) (s : Bool) where
    open Functor f

    P : W.C → Set
    P w = Is s (F w)

    P-src : ∀ n w → P w → P (W.src n w)
    P-src n w u = subst (Is s) (sym (F-src n w)) (Is-src s n (F w) u)

    P-tgt : ∀ n w → P w → P (W.tgt n w)
    P-tgt n w u = subst (Is s) (sym (F-tgt n w)) (Is-tgt s n (F w) u)

    q-of : ∀ n w w′ → W.tgt n w ≡ W.src n w′ → S.tgt n (F w) ≡ S.src n (F w′)
    q-of n w w′ p = trans (sym (F-tgt n w)) (trans (cong F p) (F-src n w′))

    P-comp : ∀ n w w′ p → P w → P w′ → P (W.comp n w w′ p)
    P-comp n w w′ p u v =
      subst (Is s) (sym (F-comp n w w′ p (q-of n w w′ p)))
        (Is-comp s n (F w) (F w′) _ u v)

    Cell : Set
    Cell = Σ W.C P

    Σ≡ : ∀ {w w′ : W.C} {u : P w} {v : P w′} → w ≡ w′ → _≡_ {A = Cell} (w , u) (w′ , v)
    Σ≡ {w} {u = u} {v} refl = cong (λ z → (w , z)) (Is-prop s (F w) u v)

    srcP tgtP : Nat → Cell → Cell
    srcP n (w , u) = W.src n w , P-src n w u
    tgtP n (w , u) = W.tgt n w , P-tgt n w u

    compP : ∀ n (x y : Cell) → tgtP n x ≡ srcP n y → Cell
    compP n (w , u) (w′ , v) p = W.comp n w w′ (cong fst p) , P-comp n w w′ _ u v

    open ωCat

    ob : ωCat
    C    ob = Cell
    src  ob = srcP
    tgt  ob = tgtP
    comp ob = compP
    src-src-< ob (w , _) l = Σ≡ (W.src-src-< w l)
    src-tgt-< ob (w , _) l = Σ≡ (W.src-tgt-< w l)
    tgt-src-< ob (w , _) l = Σ≡ (W.tgt-src-< w l)
    tgt-tgt-< ob (w , _) l = Σ≡ (W.tgt-tgt-< w l)
    src-src-≥ ob (w , _) l = Σ≡ (W.src-src-≥ w l)
    tgt-src-≥ ob (w , _) l = Σ≡ (W.tgt-src-≥ w l)
    src-tgt-≥ ob (w , _) l = Σ≡ (W.src-tgt-≥ w l)
    tgt-tgt-≥ ob (w , _) l = Σ≡ (W.tgt-tgt-≥ w l)
    src-comp ob n (w , _) (w′ , _) p = Σ≡ (W.src-comp n w w′ _)
    tgt-comp ob n (w , _) (w′ , _) p = Σ≡ (W.tgt-comp n w w′ _)
    src-comp-< ob (w , _) (w′ , _) p l = Σ≡ (W.src-comp-< w w′ _ l)
    tgt-comp-< ob (w , _) (w′ , _) p l = Σ≡ (W.tgt-comp-< w w′ _ l)
    src-comp-> ob (w , _) (w′ , _) p l q = Σ≡ (W.src-comp-> w w′ _ l _)
    tgt-comp-> ob (w , _) (w′ , _) p l q = Σ≡ (W.tgt-comp-> w w′ _ l _)
    unit-l ob n (w , _) p = Σ≡ (W.unit-l n w _)
    unit-r ob n (w , _) p = Σ≡ (W.unit-r n w _)
    assoc ob n (x , _) (y , _) (z , _) p q p′ q′ =
      Σ≡ (W.assoc n x y z (cong fst p) (cong fst q) (cong fst p′) (cong fst q′))
    interchange ob (x , _) (y , _) (z , _) (w , _) l p q r r₁ r₂ r₃ =
      Σ≡ (W.interchange x y z w l (cong fst p) (cong fst q) (cong fst r)
                                    (cong fst r₁) (cong fst r₂) (cong fst r₃))

    -- the inclusion into W and the leg to the base
    incl : Functor ob 𝒲
    Functor.F      incl = fst
    Functor.F-src  incl n x = refl
    Functor.F-tgt  incl n x = refl
    Functor.F-comp incl n (w , _) (w′ , _) p q = cong (W.comp n w w′) (uip _ q)

    -- facts about `get` along equalities in A ⊕ B
    get-resp : ∀ {x y : Cs} (e : x ≡ y) (u : Is s x) (v : Is s y) → get s x u ≡ get s y v
    get-resp {x} refl u v = cong (get s x) (Is-prop s x u v)

    leg : Functor ob (Base s)
    Functor.F      leg (w , u) = get s (F w) u
    Functor.F-src  leg n (w , u) =
      trans (get-resp (F-src n w) _ (Is-src s n (F w) u)) (get-src s n (F w) u _)
    Functor.F-tgt  leg n (w , u) =
      trans (get-resp (F-tgt n w) _ (Is-tgt s n (F w) u)) (get-tgt s n (F w) u _)
    Functor.F-comp leg n (w , u) (w′ , v) p q =
      trans (get-resp (F-comp n w w′ (cong fst p) (q-of n w w′ (cong fst p))) _
                      (Is-comp s n (F w) (F w′) _ u v))
            (get-comp s n (F w) (F w′) _ u v _ q)

    square : ∀ c → F (Functor.F incl c) ≡ put s (Functor.F leg c)
    square (w , u) = sym (put-get s (F w) u)

    -- universal property as the pullback of inj s along f
    module _ {𝒵 : ωCat} (U : Functor 𝒵 𝒲) (V : Functor 𝒵 (Base s))
             (sq : ∀ z → F (Functor.F U z) ≡ put s (Functor.F V z)) where
      private
        module Z = ωCat 𝒵
        module Um = Functor U
        module Vm = Functor V

      pf : ∀ z → P (Um.F z)
      pf z = subst (Is s) (sym (sq z)) (Is-put s (Vm.F z))

      fac : Functor 𝒵 ob
      Functor.F      fac z = Um.F z , pf z
      Functor.F-src  fac n z = Σ≡ (Um.F-src n z)
      Functor.F-tgt  fac n z = Σ≡ (Um.F-tgt n z)
      Functor.F-comp fac n z z′ p q = Σ≡ (Um.F-comp n z z′ p _)

      fac-incl : ∀ z → Functor.F incl (Functor.F fac z) ≡ Um.F z
      fac-incl z = refl

      fac-leg : ∀ z → Functor.F leg (Functor.F fac z) ≡ Vm.F z
      fac-leg z = trans (get-resp (sq z) _ (Is-put s (Vm.F z))) (get-put s (Vm.F z) _)

      fac-uni : (K : Functor 𝒵 ob) → (∀ z → fst (Functor.F K z) ≡ Um.F z) →
                ∀ z → Functor.F K z ≡ Functor.F fac z
      fac-uni K e z = Σ≡ (e z)

  ----------------------------------------------------------------------
  -- U-⊔: the comparison Pb true ⊕ Pb false → W is invertible

  module U-⊔ (f : Functor 𝒲 _⊕_) where
    open Functor f
    module P₁ = Pb f true
    module P₂ = Pb f false
    open Sum P₁.ob P₂.ob renaming (_⊕_ to Q; Cs to QC; copair to qcopair; [_] to q[_])

    comparison : Functor Q 𝒲
    comparison = qcopair P₁.incl P₂.incl

    split′ : (w : W.C) (x : Cs) → F w ≡ x → QC
    split′ w (inl a) e = inl (w , subst (Is true)  (sym e) tt)
    split′ w (inr b) e = inr (w , subst (Is false) (sym e) tt)

    split : W.C → QC
    split w = split′ w (F w) refl

    comparison-split : ∀ w → Functor.F comparison (split w) ≡ w
    comparison-split w = go (F w) refl
      where
        go : ∀ x (e : F w ≡ x) → Functor.F comparison (split′ w x e) ≡ w
        go (inl a) e = refl
        go (inr b) e = refl

    split-comparison : ∀ c → split (Functor.F comparison c) ≡ c
    split-comparison (inl (w , u)) = go (F w) refl u
      where
        go : ∀ x (e : F w ≡ x) (u : Is true (F w)) → split′ w x e ≡ inl (w , u)
        go (inl a) e u = cong inl (P₁.Σ≡ refl)
        go (inr b) e u = ⊥-elim (subst (Is true) e u)
    split-comparison (inr (w , u)) = go (F w) refl u
      where
        go : ∀ x (e : F w ≡ x) (u : Is false (F w)) → split′ w x e ≡ inr (w , u)
        go (inl a) e u = ⊥-elim (subst (Is false) e u)
        go (inr b) e u = cong inr (P₂.Σ≡ refl)

    inverse : Functor 𝒲 Q
    inverse = Inverse.inverse comparison split split-comparison comparison-split

------------------------------------------------------------------------
-- U-∅: the empty ω-category is initial and strict.

𝟘 : ωCat
ωCat.C 𝟘 = ⊥
ωCat.src 𝟘 n ()
ωCat.tgt 𝟘 n ()
ωCat.comp 𝟘 n () y p
ωCat.src-src-< 𝟘 () l
ωCat.src-tgt-< 𝟘 () l
ωCat.tgt-src-< 𝟘 () l
ωCat.tgt-tgt-< 𝟘 () l
ωCat.src-src-≥ 𝟘 () l
ωCat.tgt-src-≥ 𝟘 () l
ωCat.src-tgt-≥ 𝟘 () l
ωCat.tgt-tgt-≥ 𝟘 () l
ωCat.src-comp 𝟘 n () y p
ωCat.tgt-comp 𝟘 n () y p
ωCat.src-comp-< 𝟘 () y p l
ωCat.tgt-comp-< 𝟘 () y p l
ωCat.src-comp-> 𝟘 () y p l q
ωCat.tgt-comp-> 𝟘 () y p l q
ωCat.unit-l 𝟘 n () p
ωCat.unit-r 𝟘 n () p
ωCat.assoc 𝟘 n () y z p q p′ q′
ωCat.interchange 𝟘 () y z w l p q r r₁ r₂ r₃

¡ : ∀ {𝒟 : ωCat} → Functor 𝟘 𝒟
Functor.F      ¡ ()
Functor.F-src  ¡ n ()
Functor.F-tgt  ¡ n ()
Functor.F-comp ¡ n () y p q

¡-uni : ∀ {𝒟 : ωCat} (K : Functor 𝟘 𝒟) → ∀ x → Functor.F K x ≡ Functor.F (¡ {𝒟}) x
¡-uni K ()

U-∅ : ∀ {𝒲 : ωCat} (f : Functor 𝒲 𝟘) →
      (∀ w → Functor.F (¡ {𝒲}) (Functor.F f w) ≡ w) × (∀ x → Functor.F f (Functor.F (¡ {𝒲}) x) ≡ x)
U-∅ f = (λ w → ⊥-elim (Functor.F f w)) , (λ ())
