------------------------------------------------------------------------
-- Ledger F12c (notes/coinductive.md §4; researcher response 1 to
-- notes/conjectures/answered/dependent-m-types-without-descent-2026-11-23.md).
--
-- Rectangular bands: no terminal p-dialgebra for the first injection
-- 1 → 1 + 1, nor for the finite-ordinal family Fin → ℕ.
--
-- A rectangular band is a set with an idempotent multiplication
-- satisfying (xy)z = xz = x(yz).  The category R of rectangular bands
-- (pairs of sets, with the empty band) is locally finitely presentable
-- and cartesian closed, with disjoint but non-universal coproducts;
-- 1 + 1 is the 2 × 2 grid (Bool × Bool).
--
-- Machine-checked (no postulates):
--   * `inactive-product`: in the category of bands, for any band map
--     p : E → A, if two labels x, y have empty p-fibres but x·y lies in
--     the image of p, and A has two distinct points, then no
--     p-dialgebra is terminal.  Dialgebras are carriers C with a band
--     map h : C → A and a transition defined exactly on the pullback
--     C ×_A E, as a band map; terminality is unique existence of
--     dialgebra maps, with uniqueness only pointwise (so the negative
--     result is the stronger one).
--   * `no-first`: the instance p = first injection 1 → 1 + 1 in R.
--   * `no-fin`: the instance p : Fin → ℕ in R (ℕ = (ℕ, ℕ) is R's NNO).
--
-- Scope and honesty notes.
--   * NOT encoded: that R satisfies the setting's axioms (finite limits
--     and colimits, cartesian closure, initial algebras of positive
--     signatures via local presentability), that the grids are the
--     coproduct 1 + 1 and the NNO of R, and that the pullback of bands
--     is the one used here.  These are argued in notes/coinductive.md
--     §4 and in the researcher response, and verified there.
--   * The transition is indexed by proofs of h c ≡ p e; comparing two
--     such indexed values uses K (Agda's default), the analogue of
--     proof irrelevance in the Lean certificate tools/DependentMTypes.lean.
------------------------------------------------------------------------
module CaTTExp.Coinductive.RectBandNoDialgebra where

open import CaTTExp.Prelude

record Band : Set₁ where
  field
    Car  : Set
    mul  : Car → Car → Car
    idem : ∀ x → mul x x ≡ x
open Band

grid : Set → Set → Band
Car  (grid L R) = Σ L (λ _ → R)
mul  (grid L R) (a , _) (_ , d) = a , d
idem (grid L R) (a , b) = refl

record BMap (B C : Band) : Set where
  field
    fn  : Car B → Car C
    hom : ∀ x y → fn (mul B x y) ≡ mul C (fn x) (fn y)
open BMap

_∘B_ : ∀ {A B C} → BMap B C → BMap A B → BMap A C
fn  (g ∘B f) x = fn g (fn f x)
hom (g ∘B f) x y = trans (cong (fn g) (hom f x y)) (hom g (fn f x) (fn f y))

idB : ∀ {B} → BMap B B
fn  idB x = x
hom idB x y = refl

constB : ∀ {B C} → Car C → BMap B C
fn  (constB z) _ = z
hom (constB {C = C} z) _ _ = sym (idem C z)

unit : Band
unit = grid ⊤ ⊤

module _ {E A : Band} (p : BMap E A) where

  record Dial : Set₁ where
    field
      C  : Band
      h  : BMap C A
      t  : (c : Car C) (e : Car E) → fn h c ≡ fn p e → Car C
      -- t is a band map on the pullback C ×_A E
      tm : ∀ c d e f (ce : fn h c ≡ fn p e) (df : fn h d ≡ fn p f) →
           t (mul C c d) (mul E e f)
             (trans (hom h c d) (trans (cong₂ (mul A) ce df) (sym (hom p e f))))
           ≡ mul C (t c e ce) (t d f df)
  open Dial

  record Hom (D T : Dial) : Set where
    field
      map  : BMap (C D) (C T)
      root : ∀ c → fn (h T) (fn map c) ≡ fn (h D) c
      step : ∀ c e (w : fn (h D) c ≡ fn p e) →
             fn map (t D c e w) ≡ t T (fn map c) e (trans (root c) w)
  open Hom

  -- the transition does not depend on the equality proof (K)
  t-irr : ∀ (V : Dial) {i e} (u v : fn (h V) i ≡ fn p e) → t V i e u ≡ t V i e v
  t-irr V u v = cong (t V _ _) (uip u v)
    where
      uip : ∀ {X : Set} {x y : X} (u v : x ≡ y) → u ≡ v
      uip refl refl = refl

  comp : ∀ {D T V} → Hom T V → Hom D T → Hom D V
  map  (comp g f) = map g ∘B map f
  root (comp g f) c = trans (root g _) (root f c)
  step (comp {D} {T} {V} g f) c e w =
    trans (cong (fn (map g)) (step f c e w))
      (trans (step g _ e _) (t-irr V _ _))

  IsTerminal : Dial → Set₁
  IsTerminal T = ∀ D → Σ (Hom D T) (λ f → ∀ (g : Hom D T) → ∀ x → fn (map g) x ≡ fn (map f) x)

  -- carrier A, root the identity, constant transition at a
  constantStep : Car A → Dial
  C  (constantStep a) = A
  h  (constantStep a) = idB
  t  (constantStep a) _ _ _ = a
  tm (constantStep a) _ _ _ _ _ _ = sym (idem A a)

  -- the singleton over a label with empty fibre
  inactive : (a : Car A) → (∀ e → fn p e ≡ a → ⊥) → Dial
  C  (inactive a off) = unit
  h  (inactive a off) = constB a
  t  (inactive a off) _ e w = ⊥-elim (off e (sym w))
  tm (inactive a off) _ _ e _ w _ = ⊥-elim (off e (sym w))

  incl : ∀ a (off : ∀ e → fn p e ≡ a → ⊥) z → Hom (inactive a off) (constantStep z)
  map  (incl a off z) = constB a
  root (incl a off z) _ = refl
  step (incl a off z) _ e w = ⊥-elim (off e (sym w))

  -- Two labels with empty fibres whose product has a fibre point.
  inactive-product :
    (x y : Car A) (offX : ∀ e → fn p e ≡ x → ⊥) (offY : ∀ e → fn p e ≡ y → ⊥)
    (e : Car E) (onXY : mul A x y ≡ fn p e)
    (a b : Car A) (different : a ≡ b → ⊥) →
    Σ Dial IsTerminal → ⊥
  inactive-product x y offX offY e onXY a b different (T , term) =
    different (trans (sym (root f a)) (trans (cong (fn (h T)) next) (root g b)))
    where
      f = fst (term (constantStep a))
      g = fst (term (constantStep b))
      agree : ∀ z (off : ∀ d → fn p d ≡ z → ⊥) → fn (map f) z ≡ fn (map g) z
      agree z off =
        let k = term (inactive z off)
        in trans (snd k (comp f (incl z off a)) (tt , tt))
                 (sym (snd k (comp g (incl z off b)) (tt , tt)))
      same : fn (map f) (mul A x y) ≡ fn (map g) (mul A x y)
      same = trans (hom (map f) x y)
               (trans (cong₂ (mul (C T)) (agree x offX) (agree y offY))
                 (sym (hom (map g) x y)))
      transport : ∀ {i j} → i ≡ j → (hi : fn (h T) i ≡ fn p e) (hj : fn (h T) j ≡ fn p e) →
                  t T i e hi ≡ t T j e hj
      transport refl hi hj = t-irr T hi hj
      next : fn (map f) a ≡ fn (map g) b
      next = trans (step f (mul A x y) e onXY)
               (trans (transport same _ _) (sym (step g (mul A x y) e onXY)))

------------------------------------------------------------------------
-- Instances in R.

data Two : Set where
  O I : Two

O≢I : O ≡ I → ⊥
O≢I ()

-- 1 + 1 in R is the grid Two × Two; the first injection hits (O, O).
twoBand : Band
twoBand = grid Two Two

first : BMap unit twoBand
first = constB (O , O)

no-first : Σ (Dial first) (IsTerminal first) → ⊥
no-first = inactive-product first (O , I) (I , O)
  (λ _ w → O≢I (cong snd w)) (λ _ w → O≢I (cong fst w))
  (tt , tt) refl (O , O) (I , I) (λ w → O≢I (cong fst w))

-- ℕ in R is the grid ℕ × ℕ; Fin is the grid on {(n, i) | i < n}.
data Fin : Nat → Set where
  fz : ∀ {n} → Fin (suc n)
  fs : ∀ {n} → Fin n → Fin (suc n)

FinPos : Set
FinPos = Σ Nat Fin

natBand finBand : Band
natBand = grid Nat Nat
finBand = grid FinPos FinPos

finShape : BMap finBand natBand
fn  finShape ((n , _) , (m , _)) = n , m
hom finShape _ _ = refl

fin0 : ∀ (q : FinPos) → fst q ≡ 0 → ⊥
fin0 (.0 , ()) refl

0≢1 : 0 ≡ 1 → ⊥
0≢1 ()

no-fin : Σ (Dial finShape) (IsTerminal finShape) → ⊥
no-fin = inactive-product finShape (1 , 0) (0 , 1)
  (λ { ((n , i) , q) w → fin0 q (cong snd w) })
  (λ { ((n , i) , q) w → fin0 (n , i) (cong fst w) })
  ((1 , fz) , (1 , fz)) refl (0 , 0) (1 , 1) (λ w → 0≢1 (cong fst w))
