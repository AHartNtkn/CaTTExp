------------------------------------------------------------------------
-- Carrier pieces and poset zigzags for descent over Sd(c)
-- (RC r9 Response 15; notes/relative-coherence.md §7.14).
--
-- Response 15 glues prescribed-boundary lifting over a finite poset P
-- of carriers with three rules (zigzag to a constant, grouping along a
-- monotone map, cocartesian grouping) and applies them to Campion's
-- decomposition poset Sd(c).  The lifting, the bridges and the
-- transfers are raw-term constructions and are NOT formalised here.
-- This module checks the order-theoretic bookkeeping they rest on:
--
--   Part 1 (pieces).  For generators with carriers in a preorder and
--   faces carried at or below their carrier, the pieces
--   V p = base ∪ {x | p_x ≤ p}
--     * are closed under faces and monotone in p;
--     * a monotone F : P → Q gives carriers F ∘ p_x that again satisfy
--       the face condition, and F ≤ G gives V_{F c} ⊆ V_{G c}
--       (the domains of F_* and of the bridges F_* ⇒ G_*);
--     * grouping along u : P → Q gives exactly the unions of original
--       pieces over u⁻¹(↓q);
--     * for a cocartesian u, reassigning each carrier to its least
--       extension over q is monotone and gives exactly the original
--       pieces over the fibre.
--   Part 2 (zigzags).
--     * a least or greatest element gives a one-step zigzag;
--     * on nonempty proper downsets of a preorder that has a
--       non-minimal element, I ↦ I ∩ Min is a monotone map into the same
--       poset, below the identity and below the constant Min;
--     * on nonempty chains bounded by t, C ↦ C ∪ {t} is monotone, above
--       the identity and above the constant {t}.
--
-- The finite preorders are given with an explicit procedure that finds
-- a minimal element below any element (true for every finite preorder
-- with decidable order); no postulates.
------------------------------------------------------------------------
module CaTTExp.CarrierGluing where

open import CaTTExp.Prelude

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record Preorder : Set₁ where
  field
    Car     : Set
    _≤_     : Car → Car → Set
    ≤-refl  : ∀ {x} → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

------------------------------------------------------------------------
-- Part 1: carrier pieces.

record Carriers (P : Preorder) : Set₁ where
  open Preorder P
  field
    Gen      : Set
    carrier  : Gen → Maybe Car          -- nothing: in the base B′
    Face     : Gen → Gen → Set          -- Face x y: y occurs in a face of x
    base-closed : ∀ {x y} → carrier x ≡ nothing → Face x y → carrier y ≡ nothing
    face-le  : ∀ {x y c} → carrier x ≡ just c → Face x y →
               (carrier y ≡ nothing) ⊎ Σ Car (λ d → (carrier y ≡ just d) × (d ≤ c))

module Pieces {P : Preorder} (C : Carriers P) where
  open Preorder P
  open Carriers C

  -- Membership in the piece V p.
  In : Car → Gen → Set
  In p x = (carrier x ≡ nothing) ⊎ Σ Car (λ c → (carrier x ≡ just c) × (c ≤ p))

  piece-mono : ∀ {p q x} → p ≤ q → In p x → In q x
  piece-mono pq (inj₁ e)           = inj₁ e
  piece-mono pq (inj₂ (c , e , l)) = inj₂ (c , e , ≤-trans l pq)

  piece-closed : ∀ {p x y} → In p x → Face x y → In p y
  piece-closed (inj₁ e) f = inj₁ (base-closed e f)
  piece-closed (inj₂ (c , e , l)) f with face-le e f
  ... | inj₁ e′           = inj₁ e′
  ... | inj₂ (d , e′ , m) = inj₂ (d , e′ , ≤-trans m l)

  -- Every generator lies in the piece at its own carrier.
  own-piece : ∀ {x c} → carrier x ≡ just c → In c x
  own-piece e = inj₂ (_ , e , ≤-refl)

-- Transporting carriers along a monotone map.
record Monotone (P Q : Preorder) : Set where
  open Preorder
  field
    fun  : Car P → Car Q
    mono : ∀ {x y} → _≤_ P x y → _≤_ Q (fun x) (fun y)

mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just a) = just (f a)

module Transport {P Q : Preorder} (C : Carriers P) (F : Monotone P Q) where
  open Carriers C
  open Monotone F
  private
    module P = Preorder P
    module Q = Preorder Q

  -- The regrouped carriers u ∘ p_x again satisfy the face condition.
  regroup : Carriers Q
  regroup = record
    { Gen = Gen ; carrier = λ x → mapMaybe fun (carrier x) ; Face = Face
    ; base-closed = bc ; face-le = fl }
    where
    bc : ∀ {x y} → mapMaybe fun (carrier x) ≡ nothing → Face x y →
         mapMaybe fun (carrier y) ≡ nothing
    bc {x} {y} e f with carrier x in ex
    bc {x} {y} refl f | nothing with carrier y in ey
    ... | nothing = refl
    ... | just d with () ← trans (sym (base-closed ex f)) ey
    fl : ∀ {x y c} → mapMaybe fun (carrier x) ≡ just c → Face x y →
         (mapMaybe fun (carrier y) ≡ nothing) ⊎
         Σ (Preorder.Car Q) (λ d → (mapMaybe fun (carrier y) ≡ just d) × Q._≤_ d c)
    fl {x} {y} e f with carrier x in ex
    fl {x} {y} refl f | just c with face-le ex f
    ... | inj₁ ey rewrite ey = inj₁ refl
    ... | inj₂ (d , ey , m) rewrite ey = inj₂ (fun d , refl , mono m)

  module PP = Pieces C
  module QQ = Pieces regroup

  -- The regrouped piece at q is the union of the original pieces V p
  -- over p with u p ≤ q.
  grouped→union : ∀ {q x} → QQ.In q x →
                  (carrier x ≡ nothing) ⊎ Σ P.Car (λ p → Q._≤_ (fun p) q × PP.In p x)
  grouped→union {q} {x} (inj₁ e) with carrier x in ex
  ... | nothing = inj₁ refl
  grouped→union {q} {x} (inj₂ (c , e , l)) with carrier x in ex
  grouped→union {q} {x} (inj₂ (c , refl , l)) | just p = inj₂ (p , l , inj₂ (p , refl , P.≤-refl))

  union→grouped : ∀ {q x p} → Q._≤_ (fun p) q → PP.In p x → QQ.In q x
  union→grouped {q} {x} l (inj₁ e) rewrite e = inj₁ refl
  union→grouped {q} {x} l (inj₂ (c , e , m)) rewrite e =
    inj₂ (fun c , refl , Q.≤-trans (mono m) l)

-- Endomaps of the carrier poset (the zigzag rule).  F_* sends x into
-- V_{F p_x}; the images of its faces lie in pieces contained in that
-- one, and for F ≤ G pointwise V_{F p} ⊆ V_{G p}, the piece where the
-- bridge F_* ⇒ G_* on x is lifted.
module Endo {P : Preorder} (C : Carriers P) (F : Monotone P P) where
  open Preorder P
  open Carriers C
  open Monotone F
  open Pieces C

  face-target : ∀ {x y c d z} → carrier x ≡ just c → Face x y → carrier y ≡ just d →
                In (fun d) z → In (fun c) z
  face-target {x} {y} ex f ey m with face-le ex f
  ... | inj₁ e with () ← trans (sym e) ey
  ... | inj₂ (d′ , e′ , l) with trans (sym e′) ey
  ... | refl = piece-mono (mono l) m

  bridge-nest : (G : Monotone P P) → (∀ p → fun p ≤ Monotone.fun G p) →
                ∀ {p z} → In (fun p) z → In (Monotone.fun G p) z
  bridge-nest G F≤G {p} = piece-mono (F≤G p)

------------------------------------------------------------------------
-- Cocartesian grouping: reassign a carrier p (with u p ≤ q) to its
-- least extension over q.  The hypotheses are the definition of a
-- least extension in the fibre over q.

module Cocartesian {P Q : Preorder} (u : Monotone P Q) (q : Preorder.Car Q)
  (ext       : (p : Preorder.Car P) → Preorder._≤_ Q (Monotone.fun u p) q → Preorder.Car P)
  (ext-ge    : ∀ p l → Preorder._≤_ P p (ext p l))
  (ext-over  : ∀ p l → Preorder._≤_ Q (Monotone.fun u (ext p l)) q)
  (ext-least : ∀ p l r → Preorder._≤_ Q (Monotone.fun u r) q →
               Preorder._≤_ P p r → Preorder._≤_ P (ext p l) r)
  where
  open Preorder P

  -- Over the fibre (indeed over u⁻¹(↓q)), ext p ≤ r exactly when p ≤ r,
  -- so the reassigned pieces are the original ones.
  ext-le→le : ∀ p l r → ext p l ≤ r → p ≤ r
  ext-le→le p l r m = ≤-trans (ext-ge p l) m

  le→ext-le : ∀ p l r → Preorder._≤_ Q (Monotone.fun u r) q → p ≤ r → ext p l ≤ r
  le→ext-le = ext-least

  -- The reassignment is monotone.
  ext-mono : ∀ p p′ l l′ → p ≤ p′ → ext p l ≤ ext p′ l′
  ext-mono p p′ l l′ m = ext-least p l (ext p′ l′) (ext-over p′ l′) (≤-trans m (ext-ge p′ l′))

------------------------------------------------------------------------
-- Part 2: zigzags.

record Zigzag₁ (P : Preorder) : Set where
  -- id and a constant joined through one monotone map: id ≥ F ≤ const m
  -- or id ≤ F ≥ const m (both are used).
  open Preorder P
  field
    F    : Car → Car
    m    : Car
    mono : ∀ {x y} → x ≤ y → F x ≤ F y
    with-id    : (∀ x → F x ≤ x) ⊎ (∀ x → x ≤ F x)
    with-const : (∀ x → F x ≤ m) ⊎ (∀ x → m ≤ F x)

least-zigzag : (P : Preorder) (b : Preorder.Car P) → (∀ x → Preorder._≤_ P b x) → Zigzag₁ P
least-zigzag P b least = record
  { F = λ x → x ; m = b ; mono = λ l → l
  ; with-id = inj₁ (λ x → Preorder.≤-refl P) ; with-const = inj₂ least }

greatest-zigzag : (P : Preorder) (t : Preorder.Car P) → (∀ x → Preorder._≤_ P x t) → Zigzag₁ P
greatest-zigzag P t greatest = record
  { F = λ x → x ; m = t ; mono = λ l → l
  ; with-id = inj₁ (λ x → Preorder.≤-refl P) ; with-const = inj₁ greatest }

-- Nonempty proper downsets of a preorder, ordered by inclusion.
module Ideals (Q : Preorder)
  -- every element has a minimal element below it (finite, decidable order)
  (minBelow : ∀ x → Σ (Preorder.Car Q) λ y →
                Preorder._≤_ Q y x × (∀ z → Preorder._≤_ Q z y → Preorder._≤_ Q y z))
  -- the preorder has a non-minimal element (At_k has a strict inequality)
  (w : Preorder.Car Q) (w′ : Preorder.Car Q)
  (w′≤w : Preorder._≤_ Q w′ w) (w≰w′ : ¬ Preorder._≤_ Q w w′)
  where
  open Preorder Q

  Minimal : Car → Set
  Minimal y = ∀ z → z ≤ y → y ≤ z

  record Ideal : Set₁ where
    field
      mem      : Car → Set
      down     : ∀ {x y} → y ≤ x → mem x → mem y
      nonempty : Σ Car mem
      proper   : Σ Car (λ v → ¬ mem v)
  open Ideal

  _⊑_ : Ideal → Ideal → Set
  I ⊑ J = ∀ x → mem I x → mem J x

  w-not-min : ¬ Minimal w
  w-not-min mw = w≰w′ (mw w′ w′≤w)

  minimal-down : ∀ {x y} → y ≤ x → Minimal x → Minimal y
  minimal-down {x} {y} yx mx z zy = ≤-trans yx (mx z (≤-trans zy yx))

  -- The ideal of minimal elements.
  Min : Ideal
  Min = record
    { mem = Minimal ; down = minimal-down
    ; nonempty = fst (minBelow w) , snd (snd (minBelow w))
    ; proper = w , w-not-min }

  -- I ↦ I ∩ Min.
  cut : Ideal → Ideal
  cut I = record
    { mem = λ x → mem I x × Minimal x
    ; down = λ yx m → down I yx (fst m) , minimal-down yx (snd m)
    ; nonempty = ne
    ; proper = w , (λ m → w-not-min (snd m)) }
    where
    ne : Σ Car (λ x → mem I x × Minimal x)
    ne with nonempty I
    ... | x , ix with minBelow x
    ... | y , yx , my = y , down I yx ix , my

  cut-mono  : ∀ I J → I ⊑ J → cut I ⊑ cut J
  cut-mono I J IJ x m = IJ x (fst m) , snd m

  cut-below-id : ∀ I → cut I ⊑ I
  cut-below-id I x m = fst m

  cut-below-Min : ∀ I → cut I ⊑ Min
  cut-below-Min I x m = snd m

-- Nonempty chains bounded by t, ordered by inclusion: the zigzag
-- C ⊆ C ∪ {t} ⊇ {t} used over each downset of the max projection.
module Chains (T : Preorder) (t : Preorder.Car T) where
  open Preorder T

  record Chain : Set₁ where
    field
      mem      : Car → Set
      nonempty : Σ Car mem
      chain    : ∀ {x y} → mem x → mem y → (x ≤ y) ⊎ (y ≤ x)
      bounded  : ∀ {x} → mem x → x ≤ t
  open Chain

  _⊑_ : Chain → Chain → Set
  C ⊑ D = ∀ x → mem C x → mem D x

  single : Chain
  single = record
    { mem = λ x → x ≡ t ; nonempty = t , refl
    ; chain = λ { refl refl → inj₁ ≤-refl } ; bounded = λ { refl → ≤-refl } }

  addTop : Chain → Chain
  addTop C = record
    { mem = λ x → mem C x ⊎ (x ≡ t)
    ; nonempty = t , inj₂ refl
    ; chain = ch
    ; bounded = λ { (inj₁ m) → bounded C m ; (inj₂ refl) → ≤-refl } }
    where
    ch : ∀ {x y} → mem C x ⊎ (x ≡ t) → mem C y ⊎ (y ≡ t) → (x ≤ y) ⊎ (y ≤ x)
    ch (inj₁ mx) (inj₁ my) = chain C mx my
    ch (inj₁ mx) (inj₂ refl) = inj₁ (bounded C mx)
    ch (inj₂ refl) (inj₁ my) = inj₂ (bounded C my)
    ch (inj₂ refl) (inj₂ refl) = inj₁ ≤-refl

  addTop-mono : ∀ C D → C ⊑ D → addTop C ⊑ addTop D
  addTop-mono C D CD x (inj₁ m) = inj₁ (CD x m)
  addTop-mono C D CD x (inj₂ e) = inj₂ e

  addTop-above-id : ∀ C → C ⊑ addTop C
  addTop-above-id C x m = inj₁ m

  addTop-above-single : ∀ C → single ⊑ addTop C
  addTop-above-single C x e = inj₂ e
