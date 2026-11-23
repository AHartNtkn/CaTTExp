------------------------------------------------------------------------
-- Ledger F10f, part 4, second half (notes/universe-free-principles.md
-- §3.3, relative G₁ and G⁺).
--
-- Relative G₁, 1-truncated, in its *strict* form.  Data:
--   * cocartesian fibrations p0 : E0 → Bs and p1 : E1 → Bs of small
--     1-categories (CocartLemmas.Cat, classical cocartesian arrows);
--   * a functor F : E0 → E1 over Bs up to a natural isomorphism
--     θ : p0 ⇒ p1 ∘ F (the invariant form: no equality of objects of
--     Bs is assumed).
-- The collage W = Coll E0 E1 F (from CaTTExp.Descent.Collage) maps to
-- the strict cylinder Bs × I by Q (inA x ↦ (p0 x, 0), inB y ↦
-- (p1 y, 1), a heteromorphism h : F x → y ↦ (p1 h ∘ θ x, 0→1)).
--
-- What is machine-checked:
--   * Q is a functor (`Q`);
--   * `inB-cocart`, `hetero-cocart`: p1-cocartesian arrows of E1, and
--     p1-cocartesian heteromorphisms F x → y, are Q-cocartesian;
--   * `inA-cocart`: if χ is p0-cocartesian and F χ is p1-cocartesian,
--     then χ is Q-cocartesian;
--   * `inA-cocart⁻¹₀`, `inA-cocart⁻¹₁`, the converse: if χ is
--     Q-cocartesian then χ is p0-cocartesian AND F χ is
--     p1-cocartesian;
--   * `opfibQ`: if p0, p1 are opfibrations and F sends p0's chosen
--     lifts to p1-cocartesian arrows, then Q is an opfibration, with
--     the inA part and the inB part restricting to p0 and p1
--     (`Q-A`, `Q-B`, by refl); by construction the lift over
--     (id, 0→1) at inA x is a p1-cocartesian heteromorphism out of
--     F x, so transport is F up to the isomorphism θ⁻ x (not stated as
--     a separate lemma);
--   * `opfibQ⁻¹`, the converse of opfibQ: if Q is an opfibration, F
--     sends p0's chosen lifts to p1-cocartesian arrows.  So over the
--     strict cylinder Bs × I the hypothesis of opfibQ is necessary;
--   * G⁺'s edge instance in the special case of a constant edge map
--     (`gplus-opfib`): for g : C → D, the map Bs × g : Bs × C → Bs × D
--     over Bs (product projections, which are opfibrations,
--     `proj-opfib`) satisfies the hypothesis, so its collage is an
--     opfibration over Bs × I.
--     (Not machine-checked, argued: a general G⁺ edge (b, c) ↦
--     (b, γ_e(b, c)), with γ_e depending on b, need not satisfy the
--     hypothesis when Bs has non-invertible arrows.  Take Bs = I,
--     C = ⊤, D = I, γ_e(b, ∗) = b: the edge map sends the chosen lift
--     (0→1, id) to (0→1, 0→1), which is not cocartesian for the
--     projection, so by opfibQ⁻¹ its collage is not an opfibration over
--     the strict cylinder.  The hypothesis holds whenever γ_e(β, id) is
--     invertible for every β.  General G⁺ therefore needs the lax form.)
--
-- What is NOT machine-checked, and why.
--   * §3.3 states relative G₁ for *any* F over Bs, over the Gray
--     cylinder Bs ⊗ ⟦D¹⟧, whose lax squares absorb a failure of F to
--     preserve cocartesian arrows (oriented straightening: lax
--     transformations ↔ arbitrary maps over the base).  The Gray
--     cylinder of a 1-category is a 2-category and is not encoded
--     here.  Its 1-categorical shadow, that Q is a *locally*
--     cocartesian fibration over Bs × I for any F (lifts cocartesian
--     after pulling back along each arrow; composites of lifts need
--     not be cocartesian), is expressible with `Over` but is not
--     stated here; `inB-cocart` and `hetero-cocart` already hold with
--     no hypothesis on F.  Over the strict cylinder, `opfibQ⁻¹` shows
--     that the extra hypothesis is needed for Q to be a (global)
--     opfibration.  So the lax form of relative G₁, and with it
--     general G⁺, is not encoded; the strict form is.
--   * As in Collage.agda, the hom-sets of W are *defined*, not derived
--     from DESC-or and DJ (§3.3 steps 1–4).
--   * The reduction of G⁺ to relative G₁ (the suspension pushout and
--     DESC-glue) is not encoded; only the constant-edge instance is.
------------------------------------------------------------------------
module CaTTExp.Descent.RelCollage where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas
open import CaTTExp.Descent.Collage

------------------------------------------------------------------------
-- Product categories.

Prod : Cat → Cat → Cat
Prod C D = record
  { Ob    = C.Ob × D.Ob
  ; Hom   = λ x y → C.Hom (fst x) (fst y) × D.Hom (snd x) (snd y)
  ; id    = λ {x} → C.id {fst x} , D.id {snd x}
  ; _∘_   = λ g f → (fst g C.∘ fst f) , (snd g D.∘ snd f)
  ; idl   = λ f → cong₂ _,_ (C.idl (fst f)) (D.idl (snd f))
  ; idr   = λ f → cong₂ _,_ (C.idr (fst f)) (D.idr (snd f))
  ; assoc = λ h g f → cong₂ _,_ (C.assoc (fst h) (fst g) (fst f))
                                (D.assoc (snd h) (snd g) (snd f)) }
  where
  module C = Cat C
  module D = Cat D

------------------------------------------------------------------------
-- Relative G₁ over the strict cylinder.

module RelG₁ (E0 E1 Bs : Cat)
             (p0 : Functor E0 Bs) (p1 : Functor E1 Bs) (F : Functor E0 E1)
             (θ : ∀ x → Cat.Hom Bs (Functor.F₀ p0 x) (Functor.F₀ p1 (Functor.F₀ F x)))
             (θ-nat : ∀ {x x'} (u : Cat.Hom E0 x x')
                    → Cat._∘_ Bs (θ x') (Functor.F₁ p0 u)
                      ≡ Cat._∘_ Bs (Functor.F₁ p1 (Functor.F₁ F u)) (θ x))
             (θ-iso : ∀ x → Cat.IsIso Bs (θ x)) where

  private
    module E0 = Cat E0
    module E1 = Cat E1
    module Bs = Cat Bs
    module p0 = Functor p0
    module p1 = Functor p1
    module F  = Functor F

    θ⁻ : ∀ x → Bs.Hom (p1.F₀ (F.F₀ x)) (p0.F₀ x)
    θ⁻ x = Bs.IsIso.inv (θ-iso x)

    congˡ : ∀ {x y z} {g g' : Bs.Hom y z} (f : Bs.Hom x y) → g ≡ g' → g Bs.∘ f ≡ g' Bs.∘ f
    congˡ f refl = refl
    congʳ : ∀ {x y z} (g : Bs.Hom y z) {f f' : Bs.Hom x y} → f ≡ f' → g Bs.∘ f ≡ g Bs.∘ f'
    congʳ g refl = refl

    -- Right cancellation of an isomorphism.
    cancel : ∀ {x y z} {t : Bs.Hom x y} {a b : Bs.Hom y z}
           → Bs.IsIso t → a Bs.∘ t ≡ b Bs.∘ t → a ≡ b
    cancel {t = t} {a} {b} i e =
      a                            ≡⟨ sym (Bs.idr a) ⟩
      a Bs.∘ Bs.id                 ≡⟨ congʳ a (sym (Bs.IsIso.right i)) ⟩
      a Bs.∘ (t Bs.∘ t⁻)           ≡⟨ sym (Bs.assoc a t t⁻) ⟩
      (a Bs.∘ t) Bs.∘ t⁻           ≡⟨ congˡ t⁻ e ⟩
      (b Bs.∘ t) Bs.∘ t⁻           ≡⟨ Bs.assoc b t t⁻ ⟩
      b Bs.∘ (t Bs.∘ t⁻)           ≡⟨ congʳ b (Bs.IsIso.right i) ⟩
      b Bs.∘ Bs.id                 ≡⟨ Bs.idr b ⟩
      b ∎
      where t⁻ = Bs.IsIso.inv i

    -- (γ ∘ θ⁻ x) ∘ θ x ≡ γ.
    unθ : ∀ x {c} (γ : Bs.Hom (p0.F₀ x) c) → (γ Bs.∘ θ⁻ x) Bs.∘ θ x ≡ γ
    unθ x γ = trans (Bs.assoc γ (θ⁻ x) (θ x))
                (trans (congʳ γ (Bs.IsIso.left (θ-iso x))) (Bs.idr γ))

  BI : Cat
  BI = Prod Bs I

  Wc : Cat
  Wc = Coll E0 E1 F

  private
    WOb  = CObj E0 E1 F
    WHom = CHom E0 E1 F

  ----------------------------------------------------------------------
  -- The projection Q : W → Bs × I.

  Q₀ : WOb → Cat.Ob BI
  Q₀ (inA x) = p0.F₀ x , o0
  Q₀ (inB y) = p1.F₀ y , o1

  Q₁ : ∀ {u v} → WHom u v → Cat.Hom BI (Q₀ u) (Q₀ v)
  Q₁ {inA x} {inA x'} f = p0.F₁ f , tt
  Q₁ {inA x} {inB y}  h = (p1.F₁ h Bs.∘ θ x) , tt
  Q₁ {inB y} {inB y'} g = p1.F₁ g , tt
  Q₁ {inB y} {inA x}  ()

  private
    pr : ∀ {S : Set} {s : S} {a b : Bs.Ob} {f g : Bs.Hom a b}
       → f ≡ g → _≡_ {A = Bs.Hom a b × S} (f , s) (g , s)
    pr refl = refl

    Q-id : ∀ {u} → Q₁ {u} {u} (Cat.id Wc {u}) ≡ Cat.id BI {Q₀ u}
    Q-id {inA x} = pr p0.F-id
    Q-id {inB y} = pr p1.F-id

    Q-∘ : ∀ {x y z} (g : WHom y z) (f : WHom x y)
        → Q₁ {x} {z} (Cat._∘_ Wc {x} {y} {z} g f)
          ≡ Cat._∘_ BI {Q₀ x} {Q₀ y} {Q₀ z} (Q₁ {y} {z} g) (Q₁ {x} {y} f)
    Q-∘ {inA _} {inA _} {inA _} g f = pr (p0.F-∘ g f)
    Q-∘ {inA x} {inA x'} {inB _} g f = pr (
      p1.F₁ (g E1.∘ F.F₁ f) Bs.∘ θ x                 ≡⟨ congˡ (θ x) (p1.F-∘ g (F.F₁ f)) ⟩
      (p1.F₁ g Bs.∘ p1.F₁ (F.F₁ f)) Bs.∘ θ x          ≡⟨ Bs.assoc _ _ _ ⟩
      p1.F₁ g Bs.∘ (p1.F₁ (F.F₁ f) Bs.∘ θ x)          ≡⟨ congʳ (p1.F₁ g) (sym (θ-nat f)) ⟩
      p1.F₁ g Bs.∘ (θ x' Bs.∘ p0.F₁ f)                ≡⟨ sym (Bs.assoc _ _ _) ⟩
      (p1.F₁ g Bs.∘ θ x') Bs.∘ p0.F₁ f ∎)
    Q-∘ {inA x} {inB _} {inB _} g f = pr (
      p1.F₁ (g E1.∘ f) Bs.∘ θ x                       ≡⟨ congˡ (θ x) (p1.F-∘ g f) ⟩
      (p1.F₁ g Bs.∘ p1.F₁ f) Bs.∘ θ x                  ≡⟨ Bs.assoc _ _ _ ⟩
      p1.F₁ g Bs.∘ (p1.F₁ f Bs.∘ θ x) ∎)
    Q-∘ {inB _} {inB _} {inB _} g f = pr (p1.F-∘ g f)
    Q-∘ {inA _} {inB _} {inA _} () f
    Q-∘ {inB _} {inA _} {_}     g ()
    Q-∘ {inB _} {inB _} {inA _} () f

  Q : Functor Wc BI
  Q = record { F₀ = Q₀ ; F₁ = λ {u} {v} → Q₁ {u} {v}
             ; F-id = λ {u} → Q-id {u} ; F-∘ = λ {x} {y} {z} g f → Q-∘ {x} {y} {z} g f }

  module O0 = Over E0 Bs p0
  module O1 = Over E1 Bs p1
  module OQ = Over Wc BI Q

  -- The two parts of W, and the heteromorphisms, over Bs × I
  -- (true by definition of Q).
  Q-A : ∀ {x x'} (u : E0.Hom x x') → Q₁ {inA x} {inA x'} u ≡ (p0.F₁ u , tt)
  Q-A u = refl

  Q-B : ∀ {y y'} (v : E1.Hom y y') → Q₁ {inB y} {inB y'} v ≡ (p1.F₁ v , tt)
  Q-B v = refl

  Q-het : ∀ {x y} (h : E1.Hom (F.F₀ x) y) → Q₁ {inA x} {inB y} h ≡ ((p1.F₁ h Bs.∘ θ x) , tt)
  Q-het h = refl

  ----------------------------------------------------------------------
  -- Cocartesian arrows of E1 stay cocartesian in W.

  inB-cocart : ∀ {y y'} (χ : E1.Hom y y') → O1.IsCocart χ
             → OQ.IsCocart {inB y} {inB y'} χ
  inB-cocart {y} {y'} χ c = record { fact = fa ; fact-P = faP ; fact-∘ = fa∘ ; uniq = un }
    where
    module c = O1.IsCocart c
    fa : ∀ {z} (τ : WHom (inB y) z) (γ : Cat.Hom BI (Q₀ (inB y')) (Q₀ z))
       → Q₁ {inB y} {z} τ ≡ Cat._∘_ BI {Q₀ (inB y)} {Q₀ (inB y')} {Q₀ z} γ (Q₁ {inB y} {inB y'} χ) → WHom (inB y') z
    fa {inB z} τ (γ , _) p = c.fact τ γ (cong fst p)
    fa {inA z} () γ p
    faP : ∀ {z} (τ : WHom (inB y) z) (γ : Cat.Hom BI (Q₀ (inB y')) (Q₀ z))
          (p : Q₁ {inB y} {z} τ ≡ Cat._∘_ BI {Q₀ (inB y)} {Q₀ (inB y')} {Q₀ z} γ (Q₁ {inB y} {inB y'} χ))
        → Q₁ {inB y'} {z} (fa {z} τ γ p) ≡ γ
    faP {inB z} τ (γ , _) p = pr (c.fact-P τ γ (cong fst p))
    faP {inA z} () γ p
    fa∘ : ∀ {z} (τ : WHom (inB y) z) (γ : Cat.Hom BI (Q₀ (inB y')) (Q₀ z))
          (p : Q₁ {inB y} {z} τ ≡ Cat._∘_ BI {Q₀ (inB y)} {Q₀ (inB y')} {Q₀ z} γ (Q₁ {inB y} {inB y'} χ))
        → Cat._∘_ Wc {inB y} {inB y'} {z} (fa {z} τ γ p) χ ≡ τ
    fa∘ {inB z} τ (γ , _) p = c.fact-∘ τ γ (cong fst p)
    fa∘ {inA z} () γ p
    un : ∀ {z} (g g' : WHom (inB y') z) → Q₁ {inB y'} {z} g ≡ Q₁ {inB y'} {z} g'
       → Cat._∘_ Wc {inB y} {inB y'} {z} g χ ≡ Cat._∘_ Wc {inB y} {inB y'} {z} g' χ → g ≡ g'
    un {inB z} g g' q r = c.uniq g g' (cong fst q) r
    un {inA z} () g' q r

  ----------------------------------------------------------------------
  -- Cocartesian heteromorphisms.

  hetero-cocart : ∀ {x y} (χ : E1.Hom (F.F₀ x) y) → O1.IsCocart χ
                → OQ.IsCocart {inA x} {inB y} χ
  hetero-cocart {x} {y} χ c = record { fact = fa ; fact-P = faP ; fact-∘ = fa∘ ; uniq = un }
    where
    module c = O1.IsCocart c
    p' : ∀ {z} (τ : E1.Hom (F.F₀ x) z) (γ : Bs.Hom (p1.F₀ y) (p1.F₀ z))
       → p1.F₁ τ Bs.∘ θ x ≡ γ Bs.∘ (p1.F₁ χ Bs.∘ θ x)
       → p1.F₁ τ ≡ γ Bs.∘ p1.F₁ χ
    p' τ γ e = cancel (θ-iso x) (trans e (sym (Bs.assoc γ (p1.F₁ χ) (θ x))))
    fa : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inB y)) (Q₀ z))
       → Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inB y)} {Q₀ z} γ (Q₁ {inA x} {inB y} χ) → WHom (inB y) z
    fa {inB z} τ (γ , _) p = c.fact τ γ (p' τ γ (cong fst p))
    fa {inA z} τ (γ , ()) p
    faP : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inB y)) (Q₀ z))
          (p : Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inB y)} {Q₀ z} γ (Q₁ {inA x} {inB y} χ))
        → Q₁ {inB y} {z} (fa {z} τ γ p) ≡ γ
    faP {inB z} τ (γ , _) p = pr (c.fact-P τ γ (p' τ γ (cong fst p)))
    faP {inA z} τ (γ , ()) p
    fa∘ : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inB y)) (Q₀ z))
          (p : Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inB y)} {Q₀ z} γ (Q₁ {inA x} {inB y} χ))
        → Cat._∘_ Wc {inA x} {inB y} {z} (fa {z} τ γ p) χ ≡ τ
    fa∘ {inB z} τ (γ , _) p = c.fact-∘ τ γ (p' τ γ (cong fst p))
    fa∘ {inA z} τ (γ , ()) p
    un : ∀ {z} (g g' : WHom (inB y) z) → Q₁ {inB y} {z} g ≡ Q₁ {inB y} {z} g'
       → Cat._∘_ Wc {inA x} {inB y} {z} g χ ≡ Cat._∘_ Wc {inA x} {inB y} {z} g' χ → g ≡ g'
    un {inB z} g g' q r = c.uniq g g' (cong fst q) r
    un {inA z} () g' q r

  ----------------------------------------------------------------------
  -- Arrows of E0: Q-cocartesian iff p0-cocartesian with F χ
  -- p1-cocartesian.

  private
    -- If γ ∘ p0 χ ≡ p1 τ ∘ θ x, then p1 τ ≡ (γ ∘ θ⁻ x') ∘ p1 (F χ).
    shift : ∀ {x x' z} (χ : E0.Hom x x') (τ : E1.Hom (F.F₀ x) z)
              (γ : Bs.Hom (p0.F₀ x') (p1.F₀ z))
          → p1.F₁ τ Bs.∘ θ x ≡ γ Bs.∘ p0.F₁ χ
          → p1.F₁ τ ≡ (γ Bs.∘ θ⁻ x') Bs.∘ p1.F₁ (F.F₁ χ)
    shift {x} {x'} χ τ γ e = cancel (θ-iso x) (
      p1.F₁ τ Bs.∘ θ x                                     ≡⟨ e ⟩
      γ Bs.∘ p0.F₁ χ                                       ≡⟨ congˡ (p0.F₁ χ) (sym (unθ x' γ)) ⟩
      ((γ Bs.∘ θ⁻ x') Bs.∘ θ x') Bs.∘ p0.F₁ χ              ≡⟨ Bs.assoc _ _ _ ⟩
      (γ Bs.∘ θ⁻ x') Bs.∘ (θ x' Bs.∘ p0.F₁ χ)              ≡⟨ congʳ _ (θ-nat χ) ⟩
      (γ Bs.∘ θ⁻ x') Bs.∘ (p1.F₁ (F.F₁ χ) Bs.∘ θ x)        ≡⟨ sym (Bs.assoc _ _ _) ⟩
      ((γ Bs.∘ θ⁻ x') Bs.∘ p1.F₁ (F.F₁ χ)) Bs.∘ θ x ∎)

  inA-cocart : ∀ {x x'} (χ : E0.Hom x x') → O0.IsCocart χ → O1.IsCocart (F.F₁ χ)
             → OQ.IsCocart {inA x} {inA x'} χ
  inA-cocart {x} {x'} χ c0 c1 = record { fact = fa ; fact-P = faP ; fact-∘ = fa∘ ; uniq = un }
    where
    module c0 = O0.IsCocart c0
    module c1 = O1.IsCocart c1
    fa : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inA x')) (Q₀ z))
       → Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inA x')} {Q₀ z} γ (Q₁ {inA x} {inA x'} χ) → WHom (inA x') z
    fa {inA z} τ (γ , _) p = c0.fact τ γ (cong fst p)
    fa {inB z} τ (γ , _) p = c1.fact τ (γ Bs.∘ θ⁻ x') (shift χ τ γ (cong fst p))
    faP : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inA x')) (Q₀ z))
          (p : Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inA x')} {Q₀ z} γ (Q₁ {inA x} {inA x'} χ))
        → Q₁ {inA x'} {z} (fa {z} τ γ p) ≡ γ
    faP {inA z} τ (γ , _) p = pr (c0.fact-P τ γ (cong fst p))
    faP {inB z} τ (γ , _) p =
      pr (trans (congˡ (θ x') (c1.fact-P τ (γ Bs.∘ θ⁻ x') (shift χ τ γ (cong fst p))))
                (unθ x' γ))
    fa∘ : ∀ {z} (τ : WHom (inA x) z) (γ : Cat.Hom BI (Q₀ (inA x')) (Q₀ z))
          (p : Q₁ {inA x} {z} τ ≡ Cat._∘_ BI {Q₀ (inA x)} {Q₀ (inA x')} {Q₀ z} γ (Q₁ {inA x} {inA x'} χ))
        → Cat._∘_ Wc {inA x} {inA x'} {z} (fa {z} τ γ p) χ ≡ τ
    fa∘ {inA z} τ (γ , _) p = c0.fact-∘ τ γ (cong fst p)
    fa∘ {inB z} τ (γ , _) p = c1.fact-∘ τ (γ Bs.∘ θ⁻ x') (shift χ τ γ (cong fst p))
    un : ∀ {z} (g g' : WHom (inA x') z) → Q₁ {inA x'} {z} g ≡ Q₁ {inA x'} {z} g'
       → Cat._∘_ Wc {inA x} {inA x'} {z} g χ ≡ Cat._∘_ Wc {inA x} {inA x'} {z} g' χ → g ≡ g'
    un {inA z} g g' q r = c0.uniq g g' (cong fst q) r
    un {inB z} g g' q r = c1.uniq g g' (cancel (θ-iso x') (cong fst q)) r

  -- Converse, first half: a Q-cocartesian arrow of E0 is p0-cocartesian.
  inA-cocart⁻¹₀ : ∀ {x x'} (χ : E0.Hom x x') → OQ.IsCocart {inA x} {inA x'} χ
                → O0.IsCocart χ
  inA-cocart⁻¹₀ {x} {x'} χ cQ = record
    { fact   = λ {z} τ γ p → cQ.fact {inA z} τ (γ , tt) (pr p)
    ; fact-P = λ {z} τ γ p → cong fst (cQ.fact-P {inA z} τ (γ , tt) (pr p))
    ; fact-∘ = λ {z} τ γ p → cQ.fact-∘ {inA z} τ (γ , tt) (pr p)
    ; uniq   = λ {z} g g' q r → cQ.uniq {inA z} g g' (pr q) r }
    where module cQ = OQ.IsCocart cQ

  -- Converse, second half: if χ is Q-cocartesian then F χ is
  -- p1-cocartesian.  Over the strict cylinder this hypothesis cannot
  -- be dropped.
  inA-cocart⁻¹₁ : ∀ {x x'} (χ : E0.Hom x x') → OQ.IsCocart {inA x} {inA x'} χ
                → O1.IsCocart (F.F₁ χ)
  inA-cocart⁻¹₁ {x} {x'} χ cQ = record
    { fact   = λ {z} τ γ p → cQ.fact {inB z} τ ((γ Bs.∘ θ x') , tt) (pr (e τ γ p))
    ; fact-P = λ {z} τ γ p →
        cancel (θ-iso x') (cong fst (cQ.fact-P {inB z} τ ((γ Bs.∘ θ x') , tt) (pr (e τ γ p))))
    ; fact-∘ = λ {z} τ γ p → cQ.fact-∘ {inB z} τ ((γ Bs.∘ θ x') , tt) (pr (e τ γ p))
    ; uniq   = λ {z} g g' q r → cQ.uniq {inB z} g g' (pr (congˡ (θ x') q)) r }
    where
    module cQ = OQ.IsCocart cQ
    e : ∀ {z} (τ : E1.Hom (F.F₀ x) z) (γ : Bs.Hom (p1.F₀ (F.F₀ x')) (p1.F₀ z))
      → p1.F₁ τ ≡ γ Bs.∘ p1.F₁ (F.F₁ χ)
      → p1.F₁ τ Bs.∘ θ x ≡ (γ Bs.∘ θ x') Bs.∘ p0.F₁ χ
    e τ γ p =
      p1.F₁ τ Bs.∘ θ x                          ≡⟨ congˡ (θ x) p ⟩
      (γ Bs.∘ p1.F₁ (F.F₁ χ)) Bs.∘ θ x          ≡⟨ Bs.assoc _ _ _ ⟩
      γ Bs.∘ (p1.F₁ (F.F₁ χ) Bs.∘ θ x)          ≡⟨ congʳ γ (sym (θ-nat χ)) ⟩
      γ Bs.∘ (θ x' Bs.∘ p0.F₁ χ)                ≡⟨ sym (Bs.assoc _ _ _) ⟩
      (γ Bs.∘ θ x') Bs.∘ p0.F₁ χ ∎

  ----------------------------------------------------------------------
  -- Q is an opfibration.

  private
    pair-iso : ∀ {a b} (i : IOb) {t : Bs.Hom a b} → Bs.IsIso t
             → Cat.IsIso BI {a , i} {b , i} (t , Cat.id I {i})
    pair-iso o0 j = record { inv = Bs.IsIso.inv j , tt
                           ; left = pr (Bs.IsIso.left j) ; right = pr (Bs.IsIso.right j) }
    pair-iso o1 j = record { inv = Bs.IsIso.inv j , tt
                           ; left = pr (Bs.IsIso.left j) ; right = pr (Bs.IsIso.right j) }

  module _ (lift0 : O0.Opfib) (lift1 : O1.Opfib)
           (F-lift : ∀ x {c} (β : Bs.Hom (p0.F₀ x) c)
                   → O1.IsCocart (F.F₁ (O0.HasLift.χ (lift0 x β)))) where

    opfibQ : OQ.Opfib
    opfibQ (inA x) {c , o0} (β , _) = record
      { tgt = inA L.tgt ; χ = L.χ ; cocart = inA-cocart L.χ L.cocart (F-lift x β)
      ; θ = L.θ , tt ; θ-iso = pair-iso o0 L.θ-iso ; tri = pr L.tri }
      where module L = O0.HasLift (lift0 x β)
    opfibQ (inA x) {c , o1} (β , _) = record
      { tgt = inB L.tgt ; χ = L.χ ; cocart = hetero-cocart L.χ L.cocart
      ; θ = L.θ , tt ; θ-iso = pair-iso o1 L.θ-iso
      ; tri = pr (
          L.θ Bs.∘ (p1.F₁ L.χ Bs.∘ θ x)          ≡⟨ sym (Bs.assoc _ _ _) ⟩
          (L.θ Bs.∘ p1.F₁ L.χ) Bs.∘ θ x          ≡⟨ congˡ (θ x) L.tri ⟩
          (β Bs.∘ θ⁻ x) Bs.∘ θ x                 ≡⟨ unθ x β ⟩
          β ∎) }
      where module L = O1.HasLift (lift1 (F.F₀ x) (β Bs.∘ θ⁻ x))
    opfibQ (inB y) {c , o1} (β , _) = record
      { tgt = inB L.tgt ; χ = L.χ ; cocart = inB-cocart L.χ L.cocart
      ; θ = L.θ , tt ; θ-iso = pair-iso o1 L.θ-iso ; tri = pr L.tri }
      where module L = O1.HasLift (lift1 y β)
    opfibQ (inB y) {c , o0} (β , ())

  ----------------------------------------------------------------------
  -- The converse of opfibQ: if Q is an opfibration, F sends p0's chosen
  -- lifts to p1-cocartesian arrows.  So over the strict cylinder the
  -- hypothesis of opfibQ is necessary.

  private
    iso-∘ : ∀ {a b c} {f : Bs.Hom b c} {g : Bs.Hom a b}
          → Bs.IsIso f → Bs.IsIso g → Bs.IsIso (f Bs.∘ g)
    iso-∘ {f = f} {g} i j = record
      { inv   = g⁻ Bs.∘ f⁻
      ; left  =
          (g⁻ Bs.∘ f⁻) Bs.∘ (f Bs.∘ g)     ≡⟨ Bs.assoc _ _ _ ⟩
          g⁻ Bs.∘ (f⁻ Bs.∘ (f Bs.∘ g))     ≡⟨ congʳ g⁻ (sym (Bs.assoc _ _ _)) ⟩
          g⁻ Bs.∘ ((f⁻ Bs.∘ f) Bs.∘ g)     ≡⟨ congʳ g⁻ (congˡ g (Bs.IsIso.left i)) ⟩
          g⁻ Bs.∘ (Bs.id Bs.∘ g)           ≡⟨ congʳ g⁻ (Bs.idl g) ⟩
          g⁻ Bs.∘ g                        ≡⟨ Bs.IsIso.left j ⟩
          Bs.id ∎
      ; right =
          (f Bs.∘ g) Bs.∘ (g⁻ Bs.∘ f⁻)     ≡⟨ Bs.assoc _ _ _ ⟩
          f Bs.∘ (g Bs.∘ (g⁻ Bs.∘ f⁻))     ≡⟨ congʳ f (sym (Bs.assoc _ _ _)) ⟩
          f Bs.∘ ((g Bs.∘ g⁻) Bs.∘ f⁻)     ≡⟨ congʳ f (congˡ f⁻ (Bs.IsIso.right j)) ⟩
          f Bs.∘ (Bs.id Bs.∘ f⁻)           ≡⟨ congʳ f (Bs.idl f⁻) ⟩
          f Bs.∘ f⁻                        ≡⟨ Bs.IsIso.right i ⟩
          Bs.id ∎ }
      where
      f⁻ = Bs.IsIso.inv i
      g⁻ = Bs.IsIso.inv j

    F-iso : ∀ {a b} {u : E0.Hom a b} → E0.IsIso u → E1.IsIso (F.F₁ u)
    F-iso {u = u} i = record
      { inv   = F.F₁ (E0.IsIso.inv i)
      ; left  = trans (sym (F.F-∘ _ u)) (trans (cong F.F₁ (E0.IsIso.left i)) F.F-id)
      ; right = trans (sym (F.F-∘ u _)) (trans (cong F.F₁ (E0.IsIso.right i)) F.F-id) }

    module BIm = Cat BI

  opfibQ⁻¹ : (lift0 : O0.Opfib) → OQ.Opfib
           → ∀ x {c} (β : Bs.Hom (p0.F₀ x) c)
           → O1.IsCocart (F.F₁ (O0.HasLift.χ (lift0 x β)))
  opfibQ⁻¹ lift0 oQ x {c} β = go (oQ (inA x) {c , o0} (β , tt))
    where
    module L = O0.HasLift (lift0 x β)
    θL⁻ = Bs.IsIso.inv L.θ-iso
    go : OQ.HasLift (inA x) {c , o0} (β , tt) → O1.IsCocart (F.F₁ L.χ)
    go record { tgt = inB y ; θ = (_ , ()) }
    go record { tgt = inA x' ; χ = χ' ; cocart = cQ ; θ = (t , _) ; θ-iso = ti ; tri = tr } =
      subst (λ k → O1.IsCocart (F.F₁ k)) g∘
        (subst O1.IsCocart (sym (F.F-∘ g χ')) (O1.iso-post c1' (F-iso g-iso)))
      where
      c0' = inA-cocart⁻¹₀ χ' cQ
      c1' = inA-cocart⁻¹₁ χ' cQ
      t-iso : Bs.IsIso t
      t-iso = record { inv = fst (BIm.IsIso.inv ti)
                     ; left = cong fst (BIm.IsIso.left ti) ; right = cong fst (BIm.IsIso.right ti) }
      θL⁻-iso : Bs.IsIso θL⁻
      θL⁻-iso = record { inv = L.θ ; left = Bs.IsIso.right L.θ-iso ; right = Bs.IsIso.left L.θ-iso }
      γ = θL⁻ Bs.∘ t
      pf : p0.F₁ L.χ ≡ γ Bs.∘ p0.F₁ χ'
      pf =
        p0.F₁ L.χ                          ≡⟨ sym (Bs.idl _) ⟩
        Bs.id Bs.∘ p0.F₁ L.χ               ≡⟨ congˡ _ (sym (Bs.IsIso.left L.θ-iso)) ⟩
        (θL⁻ Bs.∘ L.θ) Bs.∘ p0.F₁ L.χ      ≡⟨ Bs.assoc _ _ _ ⟩
        θL⁻ Bs.∘ (L.θ Bs.∘ p0.F₁ L.χ)      ≡⟨ congʳ θL⁻ L.tri ⟩
        θL⁻ Bs.∘ β                         ≡⟨ congʳ θL⁻ (sym (cong fst tr)) ⟩
        θL⁻ Bs.∘ (t Bs.∘ p0.F₁ χ')         ≡⟨ sym (Bs.assoc _ _ _) ⟩
        γ Bs.∘ p0.F₁ χ' ∎
      g  = O0.IsCocart.fact   c0' L.χ γ pf
      g∘ = O0.IsCocart.fact-∘ c0' L.χ γ pf
      g-iso : E0.IsIso g
      g-iso = O0.compare-iso c0' L.cocart g∘
                (subst Bs.IsIso (sym (O0.IsCocart.fact-P c0' L.χ γ pf)) (iso-∘ θL⁻-iso t-iso))

------------------------------------------------------------------------
-- G⁺'s constant-edge case: Bs × g : Bs × C → Bs × D over Bs.

module Proj (Bs C : Cat) where
  private
    module Bs = Cat Bs
    module C  = Cat C

  π : Functor (Prod Bs C) Bs
  π = record { F₀ = fst ; F₁ = fst ; F-id = refl ; F-∘ = λ _ _ → refl }

  module Oπ = Over (Prod Bs C) Bs π

  -- (β , id) is cocartesian for the projection.
  pair-cocart : ∀ {b b' : Bs.Ob} {c : C.Ob} (β : Bs.Hom b b')
              → Oπ.IsCocart {b , c} {b' , c} (β , C.id)
  pair-cocart β = record
    { fact   = λ τ γ p → γ , snd τ
    ; fact-P = λ τ γ p → refl
    ; fact-∘ = λ τ γ p → cong₂ _,_ (sym p) (C.idr (snd τ))
    ; uniq   = λ g g' q r →
        cong₂ _,_ q (trans (sym (C.idr (snd g))) (trans (cong snd r) (C.idr (snd g')))) }

  proj-opfib : Oπ.Opfib
  proj-opfib (b , c) {b'} β = record
    { tgt = b' , c ; χ = β , C.id ; cocart = pair-cocart β
    ; θ = Bs.id ; θ-iso = record { inv = Bs.id ; left = Bs.idl Bs.id ; right = Bs.idl Bs.id }
    ; tri = Bs.idl β }

module GPlus (Bs C D : Cat) (g : Functor C D) where
  private
    module Bs = Cat Bs
    module C  = Cat C
    module D  = Cat D
    module g  = Functor g
    module PC = Proj Bs C
    module PD = Proj Bs D

  Bs×g : Functor (Prod Bs C) (Prod Bs D)
  Bs×g = record
    { F₀ = λ x → fst x , g.F₀ (snd x)
    ; F₁ = λ f → fst f , g.F₁ (snd f)
    ; F-id = cong (λ k → Bs.id , k) g.F-id
    ; F-∘ = λ h f → cong (λ k → (fst h Bs.∘ fst f) , k) (g.F-∘ (snd h) (snd f)) }

  private
    module R = RelG₁ (Prod Bs C) (Prod Bs D) Bs PC.π PD.π Bs×g
                 (λ _ → Bs.id) (λ u → trans (Bs.idl _) (sym (Bs.idr _)))
                 (λ _ → record { inv = Bs.id ; left = Bs.idl Bs.id ; right = Bs.idl Bs.id })

  -- Bs × g sends the chosen lifts (β , id) to cocartesian arrows.
  F-lift : ∀ x {c} (β : Bs.Hom (fst x) c)
         → PD.Oπ.IsCocart (Functor.F₁ Bs×g (Over.HasLift.χ (PC.proj-opfib x β)))
  F-lift x β = subst (λ k → PD.Oπ.IsCocart (β , k)) (sym g.F-id) (PD.pair-cocart β)

  -- So the collage of Bs × g is an opfibration over Bs × I.
  gplus-opfib : R.OQ.Opfib
  gplus-opfib = R.opfibQ PC.proj-opfib PD.proj-opfib F-lift
