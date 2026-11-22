------------------------------------------------------------------------
-- Ledger F10f, part 2 (notes/universe-free-principles.md §5, steps 2–3).
--
-- DJ (directed J, the fibrational Yoneda lemma) for a 1-categorical
-- opfibration, derived by Riehl–Verity's argument (FYL Lemmas 6.2.9
-- and 6.2.12, dualised): the map out of the comma is built from
-- cocartesian lifts, and uniqueness comes from comparing cocartesian
-- arrows.  Uses the lemmas of CaTTExp.Descent.CocartLemmas.
--
-- Setting: P : E → B a functor of 1-categories with cocartesian lifts
-- up to an isomorphism in the base (`Opfib`), and a ↓ B the comma
-- with projection π (CocartLemmas.Comma).
--
-- A "CF-morphism a ↓ B → E over B" (`CFMor`) is a functor h together
-- with a natural isomorphism ζ : P ∘ h ≅ π, sending every arrow to a
-- P-cocartesian arrow.  (Every arrow of a ↓ B is π-cocartesian,
-- CocartLemmas.Comma.dj-cocart, so this is "preserves cocartesian
-- arrows".)
--
--   dj-sec : (module DJSec, which assumes the full opfibration
--            structure `lift : Opfib`) for every e : E, with a := P e,
--            a CFMor h and an isomorphism u : e ≅ h(ι) in E, where
--            ι = (a, id), lying over a:  ζ_ι ∘ P u ≡ id.
--   dj-ext : two CFMors h, h' and any ρ : h(ι) → h'(ι) over a
--            (ζ'_ι ∘ P ρ ≡ ζ_ι), invertible or not, give a natural
--            transformation κ : h ⇒ h' over B (ζ' ∘ P κ ≡ ζ) with
--            κ_ι ≡ ρ.
--   dj-uni : if moreover ρ is invertible, every component of κ is.
--   dj-ext-uni : two natural transformations over B that agree at ι
--            agree componentwise.  With dj-ext: evaluation at ι is
--            surjective onto maps over a, and injective up to
--            componentwise equality (no function extensionality).
--
-- Scope and honesty notes.
--   * 1-truncated, classical cocartesian arrows, strict equations
--     (≡ with K), as in CocartLemmas.
--   * dj-sec is stated for a := P e, i.e. e lies over a on the nose
--     at the level of objects of B; the general "P e ≅ a" case is the
--     same after composing with the iso, and is not encoded.
--   * In a 1-category the content of DJ's higher levels is that
--     evaluation at ι is an equivalence; that content is exactly
--     dj-sec (essential surjectivity, with the on-the-nose caveat
--     above), dj-ext (fullness) and dj-ext-uni (faithfulness,
--     componentwise).  Functoriality of ρ ↦ κ is not stated; it
--     follows from dj-ext-uni.  The (∞,ω) higher levels (§5 step 4)
--     are not encoded.
------------------------------------------------------------------------
module CaTTExp.Descent.DJOneTruncated where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas

module DJ (E B : Cat) (P : Functor E B) (a : Cat.Ob B) where
  open Cat E
  open Functor P
  open Over E B P
  module C = Comma B a
  module aB = Cat C.aB

  private
    Σ≡ : ∀ {c d} {f : B.Hom a c} {f' : B.Hom a d} {g g' : B.Hom c d}
           {p : g B.∘ f ≡ f'} {p' : g' B.∘ f ≡ f'}
       → g ≡ g' → _≡_ {A = Σ (B.Hom c d) (λ k → k B.∘ f ≡ f')} (g , p) (g' , p')
    Σ≡ {p = p} {p'} refl = cong (λ r → (_ , r)) (uip p p')

    ∘-congˡ : ∀ {x y z} {g g' : Hom y z} (f : Hom x y) → g ≡ g' → g ∘ f ≡ g' ∘ f
    ∘-congˡ f refl = refl
    ∘-congʳ : ∀ {x y z} (g : Hom y z) {f f' : Hom x y} → f ≡ f' → g ∘ f ≡ g ∘ f'
    ∘-congʳ g refl = refl
    B∘-congˡ : ∀ {x y z} {g g' : B.Hom y z} (f : B.Hom x y) → g ≡ g' → g B.∘ f ≡ g' B.∘ f
    B∘-congˡ f refl = refl
    B∘-congʳ : ∀ {x y z} (g : B.Hom y z) {f f' : B.Hom x y} → f ≡ f' → g B.∘ f ≡ g B.∘ f'
    B∘-congʳ g refl = refl

    -- (g ∘ f) ∘ k  ≡  g ∘ (f ∘ k), with the inner pair cancelling.
    B-cancel-mid : ∀ {w x y z} (g : B.Hom y z) (f : B.Hom x y) (f⁻ : B.Hom y x)
                   (k : B.Hom w y) → f B.∘ f⁻ ≡ B.id
                 → (g B.∘ f) B.∘ (f⁻ B.∘ k) ≡ g B.∘ k
    B-cancel-mid g f f⁻ k r =
      (g B.∘ f) B.∘ (f⁻ B.∘ k)    ≡⟨ B.assoc g f (f⁻ B.∘ k) ⟩
      g B.∘ (f B.∘ (f⁻ B.∘ k))    ≡⟨ B∘-congʳ g (sym (B.assoc f f⁻ k)) ⟩
      g B.∘ ((f B.∘ f⁻) B.∘ k)    ≡⟨ B∘-congʳ g (B∘-congˡ k r) ⟩
      g B.∘ (B.id B.∘ k)          ≡⟨ B∘-congʳ g (B.idl k) ⟩
      g B.∘ k ∎

  ----------------------------------------------------------------------
  -- Two more lemmas on cocartesian arrows.

  id-cocart : ∀ {e} → IsCocart (id {e})
  id-cocart = record
    { fact   = λ τ γ p → τ
    ; fact-P = λ τ γ p → trans p (trans (B∘-congʳ γ F-id) (B.idr γ))
    ; fact-∘ = λ τ γ p → idr τ
    ; uniq   = λ g g' q r → trans (sym (idr g)) (trans r (idr g'))
    }

  iso-pre : ∀ {e₀ e e'} {ρ : Hom e₀ e} {χ : Hom e e'}
          → IsCocart χ → IsIso ρ → IsCocart (χ ∘ ρ)
  iso-pre {ρ = ρ} {χ} c i = record
    { fact   = λ τ γ p → IsCocart.fact c (τ ∘ ρ⁻) γ (p' τ γ p)
    ; fact-P = λ τ γ p → IsCocart.fact-P c (τ ∘ ρ⁻) γ (p' τ γ p)
    ; fact-∘ = λ τ γ p →
        IsCocart.fact c (τ ∘ ρ⁻) γ (p' τ γ p) ∘ (χ ∘ ρ)
          ≡⟨ sym (assoc _ χ ρ) ⟩
        (IsCocart.fact c (τ ∘ ρ⁻) γ (p' τ γ p) ∘ χ) ∘ ρ
          ≡⟨ ∘-congˡ ρ (IsCocart.fact-∘ c (τ ∘ ρ⁻) γ (p' τ γ p)) ⟩
        (τ ∘ ρ⁻) ∘ ρ
          ≡⟨ assoc τ ρ⁻ ρ ⟩
        τ ∘ (ρ⁻ ∘ ρ)
          ≡⟨ ∘-congʳ τ (IsIso.left i) ⟩
        τ ∘ id
          ≡⟨ idr τ ⟩
        τ ∎
    ; uniq   = λ g g' q r →
        IsCocart.uniq c g g' q
          (g ∘ χ                    ≡⟨ sym (idr (g ∘ χ)) ⟩
           (g ∘ χ) ∘ id             ≡⟨ ∘-congʳ (g ∘ χ) (sym (IsIso.right i)) ⟩
           (g ∘ χ) ∘ (ρ ∘ ρ⁻)       ≡⟨ sym (assoc (g ∘ χ) ρ ρ⁻) ⟩
           ((g ∘ χ) ∘ ρ) ∘ ρ⁻       ≡⟨ ∘-congˡ ρ⁻ (trans (assoc g χ ρ) (trans r (sym (assoc g' χ ρ)))) ⟩
           ((g' ∘ χ) ∘ ρ) ∘ ρ⁻      ≡⟨ assoc (g' ∘ χ) ρ ρ⁻ ⟩
           (g' ∘ χ) ∘ (ρ ∘ ρ⁻)      ≡⟨ ∘-congʳ (g' ∘ χ) (IsIso.right i) ⟩
           (g' ∘ χ) ∘ id            ≡⟨ idr (g' ∘ χ) ⟩
           g' ∘ χ ∎)
    }
    where
    ρ⁻ = IsIso.inv i
    p' : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ (χ ∘ ρ)
       → F₁ (τ ∘ ρ⁻) ≡ γ B.∘ F₁ χ
    p' τ γ p =
      F₁ (τ ∘ ρ⁻)                          ≡⟨ F-∘ τ ρ⁻ ⟩
      F₁ τ B.∘ F₁ ρ⁻                       ≡⟨ B∘-congˡ (F₁ ρ⁻) p ⟩
      (γ B.∘ F₁ (χ ∘ ρ)) B.∘ F₁ ρ⁻         ≡⟨ B∘-congˡ (F₁ ρ⁻) (B∘-congʳ γ (F-∘ χ ρ)) ⟩
      (γ B.∘ (F₁ χ B.∘ F₁ ρ)) B.∘ F₁ ρ⁻    ≡⟨ B.assoc γ _ (F₁ ρ⁻) ⟩
      γ B.∘ ((F₁ χ B.∘ F₁ ρ) B.∘ F₁ ρ⁻)    ≡⟨ B∘-congʳ γ (B.assoc (F₁ χ) (F₁ ρ) (F₁ ρ⁻)) ⟩
      γ B.∘ (F₁ χ B.∘ (F₁ ρ B.∘ F₁ ρ⁻))    ≡⟨ B∘-congʳ γ (B∘-congʳ (F₁ χ) (trans (sym (F-∘ ρ ρ⁻)) (trans (cong F₁ (IsIso.right i)) F-id))) ⟩
      γ B.∘ (F₁ χ B.∘ B.id)                ≡⟨ B∘-congʳ γ (B.idr (F₁ χ)) ⟩
      γ B.∘ F₁ χ ∎

  ----------------------------------------------------------------------
  -- CF-morphisms a ↓ B → E over B.

  record CFMor : Set where
    field
      h₀     : aB.Ob → Ob
      h₁     : ∀ {x y} → aB.Hom x y → Hom (h₀ x) (h₀ y)
      h-id   : ∀ {x} → h₁ (aB.id {x}) ≡ id
      h-∘    : ∀ {x y z} (g : aB.Hom y z) (f : aB.Hom x y)
             → h₁ (g aB.∘ f) ≡ h₁ g ∘ h₁ f
      ζ      : ∀ x → B.Hom (F₀ (h₀ x)) (fst x)
      ζ-iso  : ∀ x → B.IsIso (ζ x)
      ζ-nat  : ∀ {x y} (g : aB.Hom x y) → ζ y B.∘ F₁ (h₁ g) ≡ fst g B.∘ ζ x
      cocart : ∀ {x y} (g : aB.Hom x y) → IsCocart (h₁ g)

  ----------------------------------------------------------------------
  -- DJ-ext / DJ-uni.

  module Uni (h h' : CFMor) where
    private
      module h  = CFMor h
      module h' = CFMor h'
      ζ⁻ : ∀ x → B.Hom (fst x) (F₀ (h.h₀ x))
      ζ⁻ x = B.IsIso.inv (h.ζ-iso x)
      ζ'⁻ : ∀ x → B.Hom (fst x) (F₀ (h'.h₀ x))
      ζ'⁻ x = B.IsIso.inv (h'.ζ-iso x)

    -- η_x : ι → x in a ↓ B, for x = (c, f): the arrow f.
    η : ∀ x → aB.Hom C.ι x
    η (c , f) = f , B.idr f

    η-nat : ∀ {x y} (g : aB.Hom x y) → g aB.∘ η x ≡ η y
    η-nat {c , f} {d , f'} (g , p) = Σ≡ p

    η-ι : η C.ι ≡ aB.id
    η-ι = Σ≡ refl

    module _ (ρ : Hom (h.h₀ C.ι) (h'.h₀ C.ι))
             (ρ-over : h'.ζ C.ι B.∘ F₁ ρ ≡ h.ζ C.ι) where

      -- P h'(η_x) expressed through ζ': ζ'_x ∘ P h'(η_x) ≡ f ∘ ζ'_ι.
      γ : ∀ x → B.Hom (F₀ (h.h₀ x)) (F₀ (h'.h₀ x))
      γ x = ζ'⁻ x B.∘ h.ζ x

      cond : ∀ x → F₁ (h'.h₁ (η x) ∘ ρ) ≡ γ x B.∘ F₁ (h.h₁ (η x))
      cond x =
        F₁ (h'.h₁ (η x) ∘ ρ)
          ≡⟨ F-∘ _ ρ ⟩
        F₁ (h'.h₁ (η x)) B.∘ F₁ ρ
          ≡⟨ B∘-congˡ (F₁ ρ) (sym (B.idl _)) ⟩
        (B.id B.∘ F₁ (h'.h₁ (η x))) B.∘ F₁ ρ
          ≡⟨ B∘-congˡ (F₁ ρ) (B∘-congˡ _ (sym (B.IsIso.left (h'.ζ-iso x)))) ⟩
        ((ζ'⁻ x B.∘ h'.ζ x) B.∘ F₁ (h'.h₁ (η x))) B.∘ F₁ ρ
          ≡⟨ B∘-congˡ (F₁ ρ) (B.assoc _ _ _) ⟩
        (ζ'⁻ x B.∘ (h'.ζ x B.∘ F₁ (h'.h₁ (η x)))) B.∘ F₁ ρ
          ≡⟨ B∘-congˡ (F₁ ρ) (B∘-congʳ (ζ'⁻ x) (h'.ζ-nat (η x))) ⟩
        (ζ'⁻ x B.∘ (fst (η x) B.∘ h'.ζ C.ι)) B.∘ F₁ ρ
          ≡⟨ B.assoc _ _ _ ⟩
        ζ'⁻ x B.∘ ((fst (η x) B.∘ h'.ζ C.ι) B.∘ F₁ ρ)
          ≡⟨ B∘-congʳ (ζ'⁻ x) (B.assoc _ _ _) ⟩
        ζ'⁻ x B.∘ (fst (η x) B.∘ (h'.ζ C.ι B.∘ F₁ ρ))
          ≡⟨ B∘-congʳ (ζ'⁻ x) (B∘-congʳ (fst (η x)) ρ-over) ⟩
        ζ'⁻ x B.∘ (fst (η x) B.∘ h.ζ C.ι)
          ≡⟨ B∘-congʳ (ζ'⁻ x) (sym (h.ζ-nat (η x))) ⟩
        ζ'⁻ x B.∘ (h.ζ x B.∘ F₁ (h.h₁ (η x)))
          ≡⟨ sym (B.assoc _ _ _) ⟩
        γ x B.∘ F₁ (h.h₁ (η x)) ∎

      -- The components.
      κ : ∀ x → Hom (h.h₀ x) (h'.h₀ x)
      κ x = IsCocart.fact (h.cocart (η x)) (h'.h₁ (η x) ∘ ρ) (γ x) (cond x)

      κ-P : ∀ x → F₁ (κ x) ≡ γ x
      κ-P x = IsCocart.fact-P (h.cocart (η x)) (h'.h₁ (η x) ∘ ρ) (γ x) (cond x)

      κ-η : ∀ x → κ x ∘ h.h₁ (η x) ≡ h'.h₁ (η x) ∘ ρ
      κ-η x = IsCocart.fact-∘ (h.cocart (η x)) (h'.h₁ (η x) ∘ ρ) (γ x) (cond x)

      -- Each component is invertible (compare two cocartesian arrows
      -- out of h(ι); P κ_x = ζ'⁻¹ ζ is invertible).
      γ-iso : ∀ x → B.IsIso (γ x)
      γ-iso x = record
        { inv   = B.IsIso.inv (h.ζ-iso x) B.∘ h'.ζ x
        ; left  = trans (B-cancel-mid _ (h'.ζ x) (ζ'⁻ x) (h.ζ x) (B.IsIso.right (h'.ζ-iso x)))
                        (B.IsIso.left (h.ζ-iso x))
        ; right = trans (B-cancel-mid (ζ'⁻ x) (h.ζ x) (B.IsIso.inv (h.ζ-iso x)) (h'.ζ x)
                          (B.IsIso.right (h.ζ-iso x)))
                        (B.IsIso.left (h'.ζ-iso x))
        }

      -- Invertibility needs ρ invertible; nothing else below does.
      κ-iso : IsIso ρ → ∀ x → IsIso (κ x)
      κ-iso ρ-iso x = compare-iso (h.cocart (η x)) (iso-pre (h'.cocart (η x)) ρ-iso) (κ-η x)
                  (subst B.IsIso (sym (κ-P x)) (γ-iso x))

      -- Naturality: κ_y ∘ h g ≡ h' g ∘ κ_x, by uniqueness against the
      -- cocartesian arrow h(η_x).
      κ-nat : ∀ {x y} (g : aB.Hom x y) → κ y ∘ h.h₁ g ≡ h'.h₁ g ∘ κ x
      κ-nat {x} {y} g = IsCocart.uniq (h.cocart (η x)) (κ y ∘ h.h₁ g) (h'.h₁ g ∘ κ x) P-eq ∘-eq
        where
        P-eq : F₁ (κ y ∘ h.h₁ g) ≡ F₁ (h'.h₁ g ∘ κ x)
        P-eq =
          F₁ (κ y ∘ h.h₁ g)
            ≡⟨ F-∘ _ _ ⟩
          F₁ (κ y) B.∘ F₁ (h.h₁ g)
            ≡⟨ B∘-congˡ _ (κ-P y) ⟩
          (ζ'⁻ y B.∘ h.ζ y) B.∘ F₁ (h.h₁ g)
            ≡⟨ B.assoc _ _ _ ⟩
          ζ'⁻ y B.∘ (h.ζ y B.∘ F₁ (h.h₁ g))
            ≡⟨ B∘-congʳ (ζ'⁻ y) (h.ζ-nat g) ⟩
          ζ'⁻ y B.∘ (fst g B.∘ h.ζ x)
            ≡⟨ B∘-congʳ (ζ'⁻ y) (B∘-congˡ (h.ζ x) (sym (B.idr (fst g)))) ⟩
          ζ'⁻ y B.∘ ((fst g B.∘ B.id) B.∘ h.ζ x)
            ≡⟨ B∘-congʳ (ζ'⁻ y) (B∘-congˡ (h.ζ x) (B∘-congʳ (fst g) (sym (B.IsIso.right (h'.ζ-iso x))))) ⟩
          ζ'⁻ y B.∘ ((fst g B.∘ (h'.ζ x B.∘ ζ'⁻ x)) B.∘ h.ζ x)
            ≡⟨ B∘-congʳ (ζ'⁻ y) (B∘-congˡ (h.ζ x) (sym (B.assoc _ _ _))) ⟩
          ζ'⁻ y B.∘ (((fst g B.∘ h'.ζ x) B.∘ ζ'⁻ x) B.∘ h.ζ x)
            ≡⟨ B∘-congʳ (ζ'⁻ y) (B.assoc _ _ _) ⟩
          ζ'⁻ y B.∘ ((fst g B.∘ h'.ζ x) B.∘ γ x)
            ≡⟨ B∘-congʳ (ζ'⁻ y) (B∘-congˡ (γ x) (sym (h'.ζ-nat g))) ⟩
          ζ'⁻ y B.∘ ((h'.ζ y B.∘ F₁ (h'.h₁ g)) B.∘ γ x)
            ≡⟨ sym (B.assoc _ _ _) ⟩
          (ζ'⁻ y B.∘ (h'.ζ y B.∘ F₁ (h'.h₁ g))) B.∘ γ x
            ≡⟨ B∘-congˡ (γ x) (sym (B.assoc _ _ _)) ⟩
          ((ζ'⁻ y B.∘ h'.ζ y) B.∘ F₁ (h'.h₁ g)) B.∘ γ x
            ≡⟨ B∘-congˡ (γ x) (B∘-congˡ _ (B.IsIso.left (h'.ζ-iso y))) ⟩
          (B.id B.∘ F₁ (h'.h₁ g)) B.∘ γ x
            ≡⟨ B∘-congˡ (γ x) (B.idl _) ⟩
          F₁ (h'.h₁ g) B.∘ γ x
            ≡⟨ B∘-congʳ _ (sym (κ-P x)) ⟩
          F₁ (h'.h₁ g) B.∘ F₁ (κ x)
            ≡⟨ sym (F-∘ _ _) ⟩
          F₁ (h'.h₁ g ∘ κ x) ∎
        ∘-eq : (κ y ∘ h.h₁ g) ∘ h.h₁ (η x) ≡ (h'.h₁ g ∘ κ x) ∘ h.h₁ (η x)
        ∘-eq =
          (κ y ∘ h.h₁ g) ∘ h.h₁ (η x)    ≡⟨ assoc _ _ _ ⟩
          κ y ∘ (h.h₁ g ∘ h.h₁ (η x))    ≡⟨ ∘-congʳ (κ y) (sym (h.h-∘ g (η x))) ⟩
          κ y ∘ h.h₁ (g aB.∘ η x)        ≡⟨ ∘-congʳ (κ y) (cong h.h₁ (η-nat g)) ⟩
          κ y ∘ h.h₁ (η y)               ≡⟨ κ-η y ⟩
          h'.h₁ (η y) ∘ ρ                ≡⟨ ∘-congˡ ρ (cong h'.h₁ (sym (η-nat g))) ⟩
          h'.h₁ (g aB.∘ η x) ∘ ρ         ≡⟨ ∘-congˡ ρ (h'.h-∘ g (η x)) ⟩
          (h'.h₁ g ∘ h'.h₁ (η x)) ∘ ρ    ≡⟨ assoc _ _ _ ⟩
          h'.h₁ g ∘ (h'.h₁ (η x) ∘ ρ)    ≡⟨ ∘-congʳ (h'.h₁ g) (sym (κ-η x)) ⟩
          h'.h₁ g ∘ (κ x ∘ h.h₁ (η x))   ≡⟨ sym (assoc _ _ _) ⟩
          (h'.h₁ g ∘ κ x) ∘ h.h₁ (η x) ∎

      -- The component at ι is ρ.
      κ-ι : κ C.ι ≡ ρ
      κ-ι =
        κ C.ι                         ≡⟨ sym (idr (κ C.ι)) ⟩
        κ C.ι ∘ id                    ≡⟨ ∘-congʳ (κ C.ι) (sym (trans (cong h.h₁ η-ι) h.h-id)) ⟩
        κ C.ι ∘ h.h₁ (η C.ι)          ≡⟨ κ-η C.ι ⟩
        h'.h₁ (η C.ι) ∘ ρ             ≡⟨ ∘-congˡ ρ (trans (cong h'.h₁ η-ι) h'.h-id) ⟩
        id ∘ ρ                        ≡⟨ idl ρ ⟩
        ρ ∎

      -- κ lies over B: ζ'_x ∘ P κ_x ≡ ζ_x.
      κ-over : ∀ x → h'.ζ x B.∘ F₁ (κ x) ≡ h.ζ x
      κ-over x =
        h'.ζ x B.∘ F₁ (κ x)                ≡⟨ B∘-congʳ (h'.ζ x) (κ-P x) ⟩
        h'.ζ x B.∘ (ζ'⁻ x B.∘ h.ζ x)       ≡⟨ sym (B.assoc _ _ _) ⟩
        (h'.ζ x B.∘ ζ'⁻ x) B.∘ h.ζ x       ≡⟨ B∘-congˡ (h.ζ x) (B.IsIso.right (h'.ζ-iso x)) ⟩
        B.id B.∘ h.ζ x                     ≡⟨ B.idl _ ⟩
        h.ζ x ∎

  -- A natural transformation h ⇒ h' over B.
  record NatOver (h h' : CFMor) : Set where
    private
      module h  = CFMor h
      module h' = CFMor h'
    field
      κ      : ∀ x → Hom (h.h₀ x) (h'.h₀ x)
      κ-nat  : ∀ {x y} (g : aB.Hom x y) → κ y ∘ h.h₁ g ≡ h'.h₁ g ∘ κ x
      κ-over : ∀ x → h'.ζ x B.∘ F₁ (κ x) ≡ h.ζ x

  -- DJ-uni, existence half for any ρ over a (not necessarily
  -- invertible): a natural transformation over B with component ρ at ι.
  dj-ext : (h h' : CFMor)
         → (ρ : Hom (CFMor.h₀ h C.ι) (CFMor.h₀ h' C.ι))
         → CFMor.ζ h' C.ι B.∘ F₁ ρ ≡ CFMor.ζ h C.ι
         → Σ (NatOver h h') (λ n → NatOver.κ n C.ι ≡ ρ)
  dj-ext h h' ρ o =
    record { κ = U.κ ρ o ; κ-nat = U.κ-nat ρ o ; κ-over = U.κ-over ρ o } , U.κ-ι ρ o
    where module U = Uni h h'

  -- Uniqueness: a natural transformation over B is determined by its
  -- component at ι.
  dj-ext-uni : (h h' : CFMor) (n n' : NatOver h h')
             → NatOver.κ n C.ι ≡ NatOver.κ n' C.ι
             → ∀ x → NatOver.κ n x ≡ NatOver.κ n' x
  dj-ext-uni h h' n n' eι x =
    IsCocart.uniq (h.cocart (η x)) (n.κ x) (n'.κ x) P-eq ∘-eq
    where
    module h  = CFMor h
    module h' = CFMor h'
    module n  = NatOver n
    module n' = NatOver n'
    module U  = Uni h h'
    η = U.η
    ζ'⁻ = B.IsIso.inv (h'.ζ-iso x)
    unζ : ∀ (k : B.Hom (F₀ (h.h₀ x)) (F₀ (h'.h₀ x))) → h'.ζ x B.∘ k ≡ h.ζ x → k ≡ ζ'⁻ B.∘ h.ζ x
    unζ k p =
      k                              ≡⟨ sym (B.idl k) ⟩
      B.id B.∘ k                     ≡⟨ B∘-congˡ k (sym (B.IsIso.left (h'.ζ-iso x))) ⟩
      (ζ'⁻ B.∘ h'.ζ x) B.∘ k         ≡⟨ B.assoc _ _ _ ⟩
      ζ'⁻ B.∘ (h'.ζ x B.∘ k)         ≡⟨ B∘-congʳ ζ'⁻ p ⟩
      ζ'⁻ B.∘ h.ζ x ∎
    P-eq : F₁ (n.κ x) ≡ F₁ (n'.κ x)
    P-eq = trans (unζ _ (n.κ-over x)) (sym (unζ _ (n'.κ-over x)))
    ∘-eq : n.κ x ∘ h.h₁ (η x) ≡ n'.κ x ∘ h.h₁ (η x)
    ∘-eq =
      n.κ x ∘ h.h₁ (η x)          ≡⟨ n.κ-nat (η x) ⟩
      h'.h₁ (η x) ∘ n.κ C.ι       ≡⟨ ∘-congʳ (h'.h₁ (η x)) eι ⟩
      h'.h₁ (η x) ∘ n'.κ C.ι      ≡⟨ sym (n'.κ-nat (η x)) ⟩
      n'.κ x ∘ h.h₁ (η x) ∎

  -- DJ-uni, packaged: for invertible ρ the transformation is a natural
  -- isomorphism.
  dj-uni : (h h' : CFMor)
         → (ρ : Hom (CFMor.h₀ h C.ι) (CFMor.h₀ h' C.ι)) → IsIso ρ
         → CFMor.ζ h' C.ι B.∘ F₁ ρ ≡ CFMor.ζ h C.ι
         → Σ (NatOver h h') (λ n → NatOver.κ n C.ι ≡ ρ × (∀ x → IsIso (NatOver.κ n x)))
  dj-uni h h' ρ i o = fst e , snd e , U.κ-iso ρ o i
    where
    module U = Uni h h'
    e = dj-ext h h' ρ o

------------------------------------------------------------------------
-- DJ-sec, with a := P e.

module DJSec (E B : Cat) (P : Functor E B) (lift : Over.Opfib E B P) (e : Cat.Ob E) where
  open Cat E
  open Functor P
  open Over E B P
  open DJ E B P (F₀ e)

  private
    B∘-congˡ : ∀ {x y z} {g g' : B.Hom y z} (f : B.Hom x y) → g ≡ g' → g B.∘ f ≡ g' B.∘ f
    B∘-congˡ f refl = refl
    B∘-congʳ : ∀ {x y z} (g : B.Hom y z) {f f' : B.Hom x y} → f ≡ f' → g B.∘ f ≡ g B.∘ f'
    B∘-congʳ g refl = refl
    ∘-congʳ : ∀ {x y z} (g : Hom y z) {f f' : Hom x y} → f ≡ f' → g ∘ f ≡ g ∘ f'
    ∘-congʳ g refl = refl

  L : (x : aB.Ob) → HasLift e (snd x)
  L x = lift e (snd x)

  tgt : aB.Ob → Ob
  tgt x = HasLift.tgt (L x)
  χ : ∀ x → Hom e (tgt x)
  χ x = HasLift.χ (L x)
  θ : ∀ x → B.Hom (F₀ (tgt x)) (fst x)
  θ x = HasLift.θ (L x)
  θ⁻ : ∀ x → B.Hom (fst x) (F₀ (tgt x))
  θ⁻ x = B.IsIso.inv (HasLift.θ-iso (L x))
  θ-l : ∀ x → θ⁻ x B.∘ θ x ≡ B.id
  θ-l x = B.IsIso.left (HasLift.θ-iso (L x))
  θ-r : ∀ x → θ x B.∘ θ⁻ x ≡ B.id
  θ-r x = B.IsIso.right (HasLift.θ-iso (L x))
  tri : ∀ x → θ x B.∘ F₁ (χ x) ≡ snd x
  tri x = HasLift.tri (L x)
  cχ : ∀ x → IsCocart (χ x)
  cχ x = HasLift.cocart (L x)

  -- The base arrow over which h(g) lies.
  base : ∀ {x y} (g : aB.Hom x y) → B.Hom (F₀ (tgt x)) (F₀ (tgt y))
  base {x} {y} g = θ⁻ y B.∘ (fst g B.∘ θ x)

  cond : ∀ {x y} (g : aB.Hom x y) → F₁ (χ y) ≡ base g B.∘ F₁ (χ x)
  cond {x} {y} g =
    F₁ (χ y)                                   ≡⟨ sym (B.idl _) ⟩
    B.id B.∘ F₁ (χ y)                          ≡⟨ B∘-congˡ _ (sym (θ-l y)) ⟩
    (θ⁻ y B.∘ θ y) B.∘ F₁ (χ y)                ≡⟨ B.assoc _ _ _ ⟩
    θ⁻ y B.∘ (θ y B.∘ F₁ (χ y))                ≡⟨ B∘-congʳ (θ⁻ y) (tri y) ⟩
    θ⁻ y B.∘ snd y                             ≡⟨ B∘-congʳ (θ⁻ y) (sym (snd g)) ⟩
    θ⁻ y B.∘ (fst g B.∘ snd x)                 ≡⟨ B∘-congʳ (θ⁻ y) (B∘-congʳ (fst g) (sym (tri x))) ⟩
    θ⁻ y B.∘ (fst g B.∘ (θ x B.∘ F₁ (χ x)))    ≡⟨ B∘-congʳ (θ⁻ y) (sym (B.assoc _ _ _)) ⟩
    θ⁻ y B.∘ ((fst g B.∘ θ x) B.∘ F₁ (χ x))    ≡⟨ sym (B.assoc _ _ _) ⟩
    base g B.∘ F₁ (χ x) ∎

  h₁ : ∀ {x y} → aB.Hom x y → Hom (tgt x) (tgt y)
  h₁ {x} {y} g = IsCocart.fact (cχ x) (χ y) (base g) (cond g)

  h₁-P : ∀ {x y} (g : aB.Hom x y) → F₁ (h₁ g) ≡ base g
  h₁-P {x} {y} g = IsCocart.fact-P (cχ x) (χ y) (base g) (cond g)

  h₁-χ : ∀ {x y} (g : aB.Hom x y) → h₁ g ∘ χ x ≡ χ y
  h₁-χ {x} {y} g = IsCocart.fact-∘ (cχ x) (χ y) (base g) (cond g)

  h-id : ∀ {x} → h₁ (aB.id {x}) ≡ id
  h-id {x} = IsCocart.uniq (cχ x) (h₁ aB.id) id
    (trans (h₁-P aB.id)
      (trans (B∘-congʳ (θ⁻ x) (B.idl (θ x))) (trans (θ-l x) (sym F-id))))
    (trans (h₁-χ aB.id) (sym (idl (χ x))))

  h-∘ : ∀ {x y z} (g : aB.Hom y z) (f : aB.Hom x y) → h₁ (g aB.∘ f) ≡ h₁ g ∘ h₁ f
  h-∘ {x} {y} {z} g f = IsCocart.uniq (cχ x) (h₁ (g aB.∘ f)) (h₁ g ∘ h₁ f) P-eq ∘-eq
    where
    P-eq : F₁ (h₁ (g aB.∘ f)) ≡ F₁ (h₁ g ∘ h₁ f)
    P-eq =
      F₁ (h₁ (g aB.∘ f))
        ≡⟨ h₁-P (g aB.∘ f) ⟩
      θ⁻ z B.∘ ((fst g B.∘ fst f) B.∘ θ x)
        ≡⟨ B∘-congʳ (θ⁻ z) (B.assoc _ _ _) ⟩
      θ⁻ z B.∘ (fst g B.∘ (fst f B.∘ θ x))
        ≡⟨ B∘-congʳ (θ⁻ z) (B∘-congʳ (fst g) (sym (B.idl _))) ⟩
      θ⁻ z B.∘ (fst g B.∘ (B.id B.∘ (fst f B.∘ θ x)))
        ≡⟨ B∘-congʳ (θ⁻ z) (B∘-congʳ (fst g) (B∘-congˡ _ (sym (θ-r y)))) ⟩
      θ⁻ z B.∘ (fst g B.∘ ((θ y B.∘ θ⁻ y) B.∘ (fst f B.∘ θ x)))
        ≡⟨ B∘-congʳ (θ⁻ z) (B∘-congʳ (fst g) (B.assoc _ _ _)) ⟩
      θ⁻ z B.∘ (fst g B.∘ (θ y B.∘ base f))
        ≡⟨ B∘-congʳ (θ⁻ z) (sym (B.assoc _ _ _)) ⟩
      θ⁻ z B.∘ ((fst g B.∘ θ y) B.∘ base f)
        ≡⟨ sym (B.assoc _ _ _) ⟩
      base g B.∘ base f
        ≡⟨ sym (trans (F-∘ (h₁ g) (h₁ f)) (trans (B∘-congˡ _ (h₁-P g)) (B∘-congʳ _ (h₁-P f)))) ⟩
      F₁ (h₁ g ∘ h₁ f) ∎
    ∘-eq : h₁ (g aB.∘ f) ∘ χ x ≡ (h₁ g ∘ h₁ f) ∘ χ x
    ∘-eq = trans (h₁-χ (g aB.∘ f))
             (sym (trans (assoc _ _ _) (trans (∘-congʳ (h₁ g) (h₁-χ f)) (h₁-χ g))))

  ζ-nat : ∀ {x y} (g : aB.Hom x y) → θ y B.∘ F₁ (h₁ g) ≡ fst g B.∘ θ x
  ζ-nat {x} {y} g =
    trans (B∘-congʳ (θ y) (h₁-P g))
      (trans (sym (B.assoc _ _ _))
        (trans (B∘-congˡ _ (θ-r y)) (B.idl _)))

  h-cocart : ∀ {x y} (g : aB.Hom x y) → IsCocart (h₁ g)
  h-cocart {x} {y} g = cancel (cχ x) (subst IsCocart (sym (h₁-χ g)) (cχ y))

  h : CFMor
  h = record
    { h₀ = tgt ; h₁ = h₁ ; h-id = h-id ; h-∘ = h-∘
    ; ζ = θ ; ζ-iso = λ x → HasLift.θ-iso (L x) ; ζ-nat = ζ-nat ; cocart = h-cocart }

  -- h(ι) ≅ e: the lift of the identity is invertible.
  Pχι-iso : B.IsIso (F₁ (χ C.ι))
  Pχι-iso = record
    { inv   = θ C.ι
    ; left  = tri C.ι
    ; right = trans (B∘-congˡ (θ C.ι) Pχ≡θ⁻) (θ-l C.ι)
    }
    where
    Pχ≡θ⁻ : F₁ (χ C.ι) ≡ θ⁻ C.ι
    Pχ≡θ⁻ =
      F₁ (χ C.ι)                              ≡⟨ sym (B.idl _) ⟩
      B.id B.∘ F₁ (χ C.ι)                     ≡⟨ B∘-congˡ _ (sym (θ-l C.ι)) ⟩
      (θ⁻ C.ι B.∘ θ C.ι) B.∘ F₁ (χ C.ι)       ≡⟨ B.assoc _ _ _ ⟩
      θ⁻ C.ι B.∘ (θ C.ι B.∘ F₁ (χ C.ι))       ≡⟨ B∘-congʳ _ (tri C.ι) ⟩
      θ⁻ C.ι B.∘ B.id                         ≡⟨ B.idr _ ⟩
      θ⁻ C.ι ∎

  ι-iso : IsIso (χ C.ι)
  ι-iso = compare-iso id-cocart (cχ C.ι) (idr (χ C.ι)) Pχι-iso

  -- DJ-sec, packaged.
  dj-sec : Σ CFMor (λ k → Σ (Hom e (CFMor.h₀ k C.ι))
             (λ u → IsIso u × (CFMor.ζ k C.ι B.∘ F₁ u ≡ B.id)))
  dj-sec = h , (χ C.ι , (ι-iso , tri C.ι))
