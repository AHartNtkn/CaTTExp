------------------------------------------------------------------------
-- Ledger F10f, part 1 (notes/universe-free-principles.md §5).
--
-- §5 derives DJ (directed J, the fibrational Yoneda lemma) from the
-- limit rules, following Riehl–Verity, "Fibrations and Yoneda's lemma
-- in an ∞-cosmos", §4–§6.  Their argument works representably: for
-- each object X, a cocartesian 2-cell is a cocartesian arrow for the
-- functor  p ∘ – : hom(X, E) → hom(X, B)  of hom-categories.  This
-- module machine-checks, for a functor P : E → B of 1-categories, the
-- lemmas about cocartesian arrows that the §5 proof uses:
--
--   iso-post    (RV Obs. 4.1.2)  a cocartesian arrow followed by an
--                                isomorphism is cocartesian;
--   comp        (RV Lemma 5.1.8) cocartesian arrows compose;
--   cancel      (RV Lemma 5.1.9) left cancellation: if χ and ψ ∘ χ are
--                                cocartesian, so is ψ;
--   compare-iso (RV Obs. 4.1.3)  two cocartesian arrows out of the same
--                                object, related by γ with P γ invertible,
--                                are related by an invertible γ;
--   all-cocart  (RV Prop. 4.2.5) if P has cocartesian lifts (up to an
--                                isomorphism in the base) and reflects
--                                isomorphisms, every arrow is cocartesian;
--   comma       (RV Ex. 4.2.11)  for the comma a ↓ B with its projection,
--                                lifts exist and isomorphisms are
--                                reflected, so every arrow of a ↓ B is
--                                cocartesian (step 1 of §5, "DJ-cocart").
--
-- Scope and honesty notes.
--   * 1-truncated: categories with hom-sets and strict equations
--     (propositional ≡, with K, as everywhere in this development).
--     "Cocartesian" is the classical notion: the induced arrow is
--     unique.  RV's weak notion (induction + conservativity) is the
--     right one in a homotopy 2-category; in a 1-category the two
--     agree, and the classical one is what is checked here.
--   * Lifts are required only up to an isomorphism in the base
--     (`HasLift`), the invariant form, so no equality of objects of B
--     is ever assumed.
--   * NOT encoded here: the 2-categorical assembly of §5 steps 2–4
--     (the comma 2-cell φ, whiskering, DJ-sec, DJ-uni and the higher
--     levels).  That is F10f part 2.
------------------------------------------------------------------------
module CaTTExp.Descent.CocartLemmas where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Equational reasoning and UIP (K is available: the library is --safe
-- but not --without-K).

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
x ∎ = refl

uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

------------------------------------------------------------------------
-- Categories and functors.

record Cat : Set₁ where
  infixr 9 _∘_
  field
    Ob    : Set
    Hom   : Ob → Ob → Set
    id    : ∀ {x} → Hom x x
    _∘_   : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idl   : ∀ {x y} (f : Hom x y) → id ∘ f ≡ f
    idr   : ∀ {x y} (f : Hom x y) → f ∘ id ≡ f
    assoc : ∀ {w x y z} (h : Hom y z) (g : Hom x y) (f : Hom w x)
          → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  record IsIso {x y : Ob} (f : Hom x y) : Set where
    field
      inv   : Hom y x
      left  : inv ∘ f ≡ id
      right : f ∘ inv ≡ id

record Functor (E B : Cat) : Set where
  private
    module E = Cat E
    module B = Cat B
  field
    F₀   : E.Ob → B.Ob
    F₁   : ∀ {x y} → E.Hom x y → B.Hom (F₀ x) (F₀ y)
    F-id : ∀ {x} → F₁ (E.id {x}) ≡ B.id
    F-∘  : ∀ {x y z} (g : E.Hom y z) (f : E.Hom x y)
         → F₁ (g E.∘ f) ≡ F₁ g B.∘ F₁ f

------------------------------------------------------------------------
-- Cocartesian arrows for a functor P : E → B.

module Over (E B : Cat) (P : Functor E B) where
  open Cat E
  module B = Cat B
  open Functor P

  record IsCocart {e e' : Ob} (χ : Hom e e') : Set where
    field
      fact   : ∀ {x} (τ : Hom e x) (γ : B.Hom (F₀ e') (F₀ x))
             → F₁ τ ≡ γ B.∘ F₁ χ → Hom e' x
      fact-P : ∀ {x} (τ : Hom e x) (γ : B.Hom (F₀ e') (F₀ x))
               (p : F₁ τ ≡ γ B.∘ F₁ χ) → F₁ (fact τ γ p) ≡ γ
      fact-∘ : ∀ {x} (τ : Hom e x) (γ : B.Hom (F₀ e') (F₀ x))
               (p : F₁ τ ≡ γ B.∘ F₁ χ) → fact τ γ p ∘ χ ≡ τ
      uniq   : ∀ {x} (g g' : Hom e' x) → F₁ g ≡ F₁ g'
             → g ∘ χ ≡ g' ∘ χ → g ≡ g'
  open IsCocart

  -- Small helpers.
  private
    ∘-congˡ : ∀ {x y z} {g g' : Hom y z} (f : Hom x y) → g ≡ g' → g ∘ f ≡ g' ∘ f
    ∘-congˡ f refl = refl
    ∘-congʳ : ∀ {x y z} (g : Hom y z) {f f' : Hom x y} → f ≡ f' → g ∘ f ≡ g ∘ f'
    ∘-congʳ g refl = refl
    B∘-congˡ : ∀ {x y z} {g g' : B.Hom y z} (f : B.Hom x y) → g ≡ g' → g B.∘ f ≡ g' B.∘ f
    B∘-congˡ f refl = refl
    B∘-congʳ : ∀ {x y z} (g : B.Hom y z) {f f' : B.Hom x y} → f ≡ f' → g B.∘ f ≡ g B.∘ f'
    B∘-congʳ g refl = refl

  ----------------------------------------------------------------------
  -- iso-post: χ cocartesian, α invertible  ⟹  α ∘ χ cocartesian.

  iso-post : ∀ {e e' e''} {χ : Hom e e'} {α : Hom e' e''}
           → IsCocart χ → IsIso α → IsCocart (α ∘ χ)
  iso-post {χ = χ} {α} c i = record
    { fact   = λ τ γ p → fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ α⁻
    ; fact-P = λ τ γ p →
        F₁ (fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ α⁻)
          ≡⟨ F-∘ _ _ ⟩
        F₁ (fact c τ (γ B.∘ F₁ α) (p' τ γ p)) B.∘ F₁ α⁻
          ≡⟨ B∘-congˡ (F₁ α⁻) (fact-P c τ (γ B.∘ F₁ α) (p' τ γ p)) ⟩
        (γ B.∘ F₁ α) B.∘ F₁ α⁻
          ≡⟨ B.assoc _ _ _ ⟩
        γ B.∘ (F₁ α B.∘ F₁ α⁻)
          ≡⟨ B∘-congʳ γ (sym (F-∘ α α⁻)) ⟩
        γ B.∘ F₁ (α ∘ α⁻)
          ≡⟨ B∘-congʳ γ (trans (cong F₁ (IsIso.right i)) F-id) ⟩
        γ B.∘ B.id
          ≡⟨ B.idr γ ⟩
        γ ∎
    ; fact-∘ = λ τ γ p →
        (fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ α⁻) ∘ (α ∘ χ)
          ≡⟨ assoc _ _ _ ⟩
        fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ (α⁻ ∘ (α ∘ χ))
          ≡⟨ ∘-congʳ _ (sym (assoc _ _ _)) ⟩
        fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ ((α⁻ ∘ α) ∘ χ)
          ≡⟨ ∘-congʳ _ (trans (∘-congˡ χ (IsIso.left i)) (idl χ)) ⟩
        fact c τ (γ B.∘ F₁ α) (p' τ γ p) ∘ χ
          ≡⟨ fact-∘ c τ (γ B.∘ F₁ α) (p' τ γ p) ⟩
        τ ∎
    ; uniq   = λ g g' q r →
        let gα≡g'α : g ∘ α ≡ g' ∘ α
            gα≡g'α = uniq c (g ∘ α) (g' ∘ α)
                       (trans (F-∘ g α) (trans (B∘-congˡ (F₁ α) q) (sym (F-∘ g' α))))
                       (trans (assoc g α χ) (trans r (sym (assoc g' α χ))))
        in g                  ≡⟨ sym (idr g) ⟩
           g ∘ id             ≡⟨ ∘-congʳ g (sym (IsIso.right i)) ⟩
           g ∘ (α ∘ α⁻)       ≡⟨ sym (assoc g α α⁻) ⟩
           (g ∘ α) ∘ α⁻       ≡⟨ ∘-congˡ α⁻ gα≡g'α ⟩
           (g' ∘ α) ∘ α⁻      ≡⟨ assoc g' α α⁻ ⟩
           g' ∘ (α ∘ α⁻)      ≡⟨ ∘-congʳ g' (IsIso.right i) ⟩
           g' ∘ id            ≡⟨ idr g' ⟩
           g' ∎
    }
    where
    α⁻ = IsIso.inv i
    p' : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ (α ∘ χ)
       → F₁ τ ≡ (γ B.∘ F₁ α) B.∘ F₁ χ
    p' τ γ p = trans p (trans (B∘-congʳ γ (F-∘ α χ)) (sym (B.assoc γ (F₁ α) (F₁ χ))))

  ----------------------------------------------------------------------
  -- comp: cocartesian arrows compose.

  comp : ∀ {e e' e''} {χ : Hom e e'} {ψ : Hom e' e''}
       → IsCocart χ → IsCocart ψ → IsCocart (ψ ∘ χ)
  comp {χ = χ} {ψ} cχ cψ = record
    { fact   = λ τ γ p → fact cψ (δ τ γ p) γ (fact-P cχ τ (γ B.∘ F₁ ψ) (p₁ τ γ p))
    ; fact-P = λ τ γ p → fact-P cψ (δ τ γ p) γ (fact-P cχ τ (γ B.∘ F₁ ψ) (p₁ τ γ p))
    ; fact-∘ = λ τ γ p →
        trans (sym (assoc _ ψ χ))
          (trans (∘-congˡ χ (fact-∘ cψ (δ τ γ p) γ (fact-P cχ τ (γ B.∘ F₁ ψ) (p₁ τ γ p))))
                 (fact-∘ cχ τ (γ B.∘ F₁ ψ) (p₁ τ γ p)))
    ; uniq   = λ g g' q r →
        uniq cψ g g' q
          (uniq cχ (g ∘ ψ) (g' ∘ ψ)
             (trans (F-∘ g ψ) (trans (B∘-congˡ (F₁ ψ) q) (sym (F-∘ g' ψ))))
             (trans (assoc g ψ χ) (trans r (sym (assoc g' ψ χ)))))
    }
    where
    p₁ : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ (ψ ∘ χ)
       → F₁ τ ≡ (γ B.∘ F₁ ψ) B.∘ F₁ χ
    p₁ τ γ p = trans p (trans (B∘-congʳ γ (F-∘ ψ χ)) (sym (B.assoc γ (F₁ ψ) (F₁ χ))))
    δ : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ (ψ ∘ χ) → Hom _ x
    δ τ γ p = fact cχ τ (γ B.∘ F₁ ψ) (p₁ τ γ p)

  ----------------------------------------------------------------------
  -- cancel: χ and ψ ∘ χ cocartesian  ⟹  ψ cocartesian.

  cancel : ∀ {e e' e''} {χ : Hom e e'} {ψ : Hom e' e''}
         → IsCocart χ → IsCocart (ψ ∘ χ) → IsCocart ψ
  cancel {χ = χ} {ψ} cχ cψχ = record
    { fact   = λ τ γ p → g τ γ p
    ; fact-P = λ τ γ p → fact-P cψχ (τ ∘ χ) γ (q τ γ p)
    ; fact-∘ = λ τ γ p →
        uniq cχ (g τ γ p ∘ ψ) τ
          (trans (F-∘ _ ψ) (trans (B∘-congˡ (F₁ ψ) (fact-P cψχ (τ ∘ χ) γ (q τ γ p))) (sym p)))
          (trans (assoc _ ψ χ) (fact-∘ cψχ (τ ∘ χ) γ (q τ γ p)))
    ; uniq   = λ h h' r s →
        uniq cψχ h h' r
          (trans (sym (assoc h ψ χ)) (trans (∘-congˡ χ s) (assoc h' ψ χ)))
    }
    where
    q : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ ψ
      → F₁ (τ ∘ χ) ≡ γ B.∘ F₁ (ψ ∘ χ)
    q τ γ p =
      F₁ (τ ∘ χ)                 ≡⟨ F-∘ τ χ ⟩
      F₁ τ B.∘ F₁ χ              ≡⟨ B∘-congˡ (F₁ χ) p ⟩
      (γ B.∘ F₁ ψ) B.∘ F₁ χ      ≡⟨ B.assoc γ (F₁ ψ) (F₁ χ) ⟩
      γ B.∘ (F₁ ψ B.∘ F₁ χ)      ≡⟨ B∘-congʳ γ (sym (F-∘ ψ χ)) ⟩
      γ B.∘ F₁ (ψ ∘ χ) ∎
    g : ∀ {x} (τ : Hom _ x) γ → F₁ τ ≡ γ B.∘ F₁ ψ → Hom _ x
    g τ γ p = fact cψχ (τ ∘ χ) γ (q τ γ p)

  ----------------------------------------------------------------------
  -- compare-iso: two cocartesian arrows out of e, and γ between their
  -- targets with γ ∘ χ ≡ χ' and P γ invertible  ⟹  γ invertible.

  compare-iso : ∀ {e e' e''} {χ : Hom e e'} {χ' : Hom e e''} {γ : Hom e' e''}
              → IsCocart χ → IsCocart χ' → γ ∘ χ ≡ χ'
              → B.IsIso (F₁ γ) → IsIso γ
  compare-iso {χ = χ} {χ'} {γ} c c' tri i = record
    { inv   = γ'
    ; left  = uniq c (γ' ∘ γ) id
                (trans (F-∘ γ' γ)
                  (trans (B∘-congˡ (F₁ γ) (fact-P c' χ Pγ⁻ p))
                    (trans (B.IsIso.left i) (sym F-id))))
                (trans (assoc γ' γ χ)
                  (trans (∘-congʳ γ' tri)
                    (trans (fact-∘ c' χ Pγ⁻ p) (sym (idl χ)))))
    ; right = uniq c' (γ ∘ γ') id
                (trans (F-∘ γ γ')
                  (trans (B∘-congʳ (F₁ γ) (fact-P c' χ Pγ⁻ p))
                    (trans (B.IsIso.right i) (sym F-id))))
                (trans (assoc γ γ' χ')
                  (trans (∘-congʳ γ (fact-∘ c' χ Pγ⁻ p))
                    (trans tri (sym (idl χ')))))
    }
    where
    Pγ⁻ = B.IsIso.inv i
    p : F₁ χ ≡ Pγ⁻ B.∘ F₁ χ'
    p = F₁ χ                          ≡⟨ sym (B.idl (F₁ χ)) ⟩
        B.id B.∘ F₁ χ                 ≡⟨ B∘-congˡ (F₁ χ) (sym (B.IsIso.left i)) ⟩
        (Pγ⁻ B.∘ F₁ γ) B.∘ F₁ χ       ≡⟨ B.assoc Pγ⁻ (F₁ γ) (F₁ χ) ⟩
        Pγ⁻ B.∘ (F₁ γ B.∘ F₁ χ)       ≡⟨ B∘-congʳ Pγ⁻ (sym (F-∘ γ χ)) ⟩
        Pγ⁻ B.∘ F₁ (γ ∘ χ)            ≡⟨ B∘-congʳ Pγ⁻ (cong F₁ tri) ⟩
        Pγ⁻ B.∘ F₁ χ' ∎
    γ' : Hom _ _
    γ' = fact c' χ Pγ⁻ p

  ----------------------------------------------------------------------
  -- Lifts up to an isomorphism in the base, and reflection of
  -- isomorphisms ("groupoidal" in RV's sense, for a 1-category).

  record HasLift (e : Ob) {c : B.Ob} (f : B.Hom (F₀ e) c) : Set where
    field
      tgt    : Ob
      χ      : Hom e tgt
      cocart : IsCocart χ
      θ      : B.Hom (F₀ tgt) c
      θ-iso  : B.IsIso θ
      tri    : θ B.∘ F₁ χ ≡ f

  Opfib : Set
  Opfib = ∀ (e : Ob) {c : B.Ob} (f : B.Hom (F₀ e) c) → HasLift e f

  ReflectsIso : Set
  ReflectsIso = ∀ {x y} (f : Hom x y) → B.IsIso (F₁ f) → IsIso f

  -- all-cocart: with lifts and reflection of isomorphisms, every arrow
  -- of E is cocartesian.
  all-cocart : Opfib → ReflectsIso → ∀ {e x} (f : Hom e x) → IsCocart f
  all-cocart lift refl-iso {e} {x} f =
    subst IsCocart (fact-∘ (HasLift.cocart L) f (HasLift.θ L) (sym (HasLift.tri L)))
      (iso-post (HasLift.cocart L) g-iso)
    where
    L = lift e (F₁ f)
    g : Hom (HasLift.tgt L) x
    g = fact (HasLift.cocart L) f (HasLift.θ L) (sym (HasLift.tri L))
    g-iso : IsIso g
    g-iso = refl-iso g
              (subst B.IsIso
                 (sym (fact-P (HasLift.cocart L) f (HasLift.θ L) (sym (HasLift.tri L))))
                 (HasLift.θ-iso L))

------------------------------------------------------------------------
-- The comma a ↓ B and its projection (DJ-cocart, §5 step 1).

module Comma (B : Cat) (a : Cat.Ob B) where
  open Cat B

  private
    Σ≡ : ∀ {c d} {f : Hom a c} {f' : Hom a d} {g g' : Hom c d}
           {p : g ∘ f ≡ f'} {p' : g' ∘ f ≡ f'}
       → g ≡ g' → _≡_ {A = Σ (Hom c d) (λ k → k ∘ f ≡ f')} (g , p) (g' , p')
    Σ≡ {p = p} {p'} refl = cong (λ r → (_ , r)) (uip p p')

  -- Objects: (c, f : a → c).  Arrows (c, f) → (d, f'): g : c → d with
  -- g ∘ f ≡ f'.
  aB : Cat
  aB = record
    { Ob    = Σ Ob (λ c → Hom a c)
    ; Hom   = λ x y → Σ (Hom (fst x) (fst y)) (λ g → g ∘ snd x ≡ snd y)
    ; id    = λ {x} → id , idl (snd x)
    ; _∘_   = λ {x} {y} {z} h g →
                (fst h ∘ fst g) ,
                trans (assoc (fst h) (fst g) (snd x))
                  (trans (cong (fst h ∘_) (snd g)) (snd h))
    ; idl   = λ f → Σ≡ (idl (fst f))
    ; idr   = λ f → Σ≡ (idr (fst f))
    ; assoc = λ h g f → Σ≡ (assoc (fst h) (fst g) (fst f))
    }

  π : Functor aB B
  π = record { F₀ = fst ; F₁ = fst ; F-id = refl ; F-∘ = λ g f → refl }

  -- ι = (a, id_a).
  ι : Cat.Ob aB
  ι = a , id

  open Over aB B π

  -- Lifts: from (c, f) along k : c → d, the arrow k : (c, f) → (d, k ∘ f),
  -- with θ = id.  It is cocartesian.
  lift-cocart : ∀ {c d} (f : Hom a c) (k : Hom c d)
              → IsCocart {e = c , f} {e' = d , k ∘ f} (k , refl)
  lift-cocart {c} {d} f k = record
    { fact   = λ τ γ p → γ , fact-eq τ γ p
    ; fact-P = λ τ γ p → refl
    ; fact-∘ = λ τ γ p → Σ≡ (sym p)
    ; uniq   = λ g g' q r → Σ≡ q
    }
    where
    fact-eq : ∀ {x} (τ : Cat.Hom aB (c , f) x) (γ : Hom d (fst x))
            → fst τ ≡ γ ∘ k → γ ∘ (k ∘ f) ≡ snd x
    fact-eq τ γ p = trans (sym (assoc γ k f)) (trans (cong (_∘ f) (sym p)) (snd τ))

  opfib : Opfib
  opfib (c , f) {d} k = record
    { tgt    = d , k ∘ f
    ; χ      = k , refl
    ; cocart = lift-cocart f k
    ; θ      = id
    ; θ-iso  = record { inv = id ; left = idl id ; right = idl id }
    ; tri    = idl k
    }

  reflects : ReflectsIso
  reflects {x} {y} (g , p) i = record
    { inv   = ginv , q
    ; left  = Σ≡ (IsIso.left i)
    ; right = Σ≡ (IsIso.right i)
    }
    where
    ginv = IsIso.inv i
    q : ginv ∘ snd y ≡ snd x
    q = ginv ∘ snd y            ≡⟨ cong (ginv ∘_) (sym p) ⟩
        ginv ∘ (g ∘ snd x)      ≡⟨ sym (assoc ginv g (snd x)) ⟩
        (ginv ∘ g) ∘ snd x      ≡⟨ cong (_∘ snd x) (IsIso.left i) ⟩
        id ∘ snd x              ≡⟨ idl (snd x) ⟩
        snd x ∎

  -- DJ-cocart (§5 step 1): π is an opfibration and every arrow of
  -- a ↓ B is π-cocartesian.
  dj-cocart : ∀ {x y} (g : Cat.Hom aB x y) → IsCocart g
  dj-cocart = all-cocart opfib reflects
