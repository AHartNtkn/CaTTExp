------------------------------------------------------------------------
-- Equations behind standardisation (ledger A5, step L4; Steiner
-- Prop. 4.2, outside response §3.1), stated for expressions in any
-- strict ω-category.
--
-- cmpR r f fs is the right-nested r-composite of the non-empty list
-- f ∷ fs. For k < r and an r-dimensional D:
--   (f₁ #ᵣ ⋯ #ᵣ fₘ) #ₖ D = (f₁ #ₖ D) #ᵣ ⋯ #ᵣ (fₘ #ₖ D)       (dist-r)
--   D #ₖ (f₁ #ᵣ ⋯ #ᵣ fₘ) = (D #ₖ f₁) #ᵣ ⋯ #ᵣ (D #ₖ fₘ)       (dist-l)
-- and Y #ₖ Z = (Y #ₖ ∂ᵣ⁻Z) #ᵣ (∂ᵣ⁺Y #ₖ Z)                   (split)
-- and r-composites of lists concatenate (cat).
------------------------------------------------------------------------
module CaTTExp.Strict.StdSem where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Expr

module _ {G : Set} where
  cmpR : Nat → Expr G → List (Expr G) → Expr G
  cmpR r f []       = f
  cmpR r f (g ∷ gs) = cmp r f (cmpR r g gs)

  mapE : (Expr G → Expr G) → List (Expr G) → List (Expr G)
  mapE h []       = []
  mapE h (g ∷ gs) = h g ∷ mapE h gs

module StdSem (𝒞 : ωCat) {G : Set} (ι : G → ωCat.C 𝒞) where
  open ωCat 𝒞
  open Eval 𝒞 ι

  comp-cong : ∀ n {x x′ y y′} p p′ → x ≡ x′ → y ≡ y′ → comp n x y p ≡ comp n x′ y′ p′
  comp-cong n p p′ refl refl = cong (comp n _ _) (uip p p′)

  -- An r-dimensional cell.
  Dim : Nat → C → Set
  Dim r d = src r d ≡ d

  Dim-tgt : ∀ {r d} → Dim r d → tgt r d ≡ d
  Dim-tgt {r} {d} e = trans (cong (tgt r) (sym e)) (trans (tgt-src-≥ d (≤-refl r)) e)

  -- d #ᵣ d = d for r-dimensional d.
  idem : ∀ {r d} (e : Dim r d) q → comp r d d q ≡ d
  idem {r} {d} e q = trans (comp-cong r q u refl (sym (Dim-tgt e))) (unit-r r d u)
    where
    u : tgt r d ≡ src r (tgt r d)
    u = sym (src-tgt-≥ d (≤-refl r))

  private
    Ev-sub : ∀ {e x y} → x ≡ y → Ev e x → Ev e y
    Ev-sub refl v = v

  ----------------------------------------------------------------------
  -- Distribution over an r-dimensional cell on the right.

  dist-r : ∀ {k r} → k < r → ∀ f fs D {y d} → Ev (cmpR r f fs) y → Ev D d → Dim r d →
           (p : tgt k y ≡ src k d) →
           Ev (cmpR r (cmp k f D) (mapE (λ g → cmp k g D) fs)) (comp k y d p)
  dist-r l f []       D a vd dd p = ev-cmp _ a vd p
  dist-r {k} {r} l f (g ∷ gs) D (ev-cmp .r {x = y₁} {y = y′} a b q) vd dd p =
    Ev-sub (sym eq) (ev-cmp r (ev-cmp k a vd p₁) ih q₂)
    where
    p′ : tgt k y′ ≡ src k _
    p′ = trans (sym (tgt-comp-< y₁ y′ q l)) p
    ih = dist-r l g gs D b vd dd p′
    p₁ : tgt k y₁ ≡ src k _
    p₁ = trans (sym (tgt-tgt-< y₁ l)) (trans (cong (tgt k) q) (trans (tgt-src-< y′ l) p′))
    qa : tgt k (tgt r y₁) ≡ src k (tgt r _)
    qa = trans (tgt-tgt-< y₁ l) (trans p₁ (sym (src-tgt-< _ l)))
    qb : tgt k (src r y′) ≡ src k (src r _)
    qb = trans (tgt-src-< y′ l) (trans p′ (sym (src-src-< _ l)))
    q₂ : tgt r (comp k y₁ _ p₁) ≡ src r (comp k y′ _ p′)
    q₂ = trans (tgt-comp-> y₁ _ p₁ l qa)
               (trans (comp-cong k qa qb q (trans (Dim-tgt dd) (sym dd)))
                      (sym (src-comp-> y′ _ p′ l qb)))
    qd : tgt r _ ≡ src r _
    qd = trans (Dim-tgt dd) (sym dd)
    r₀ : tgt k (comp r y₁ y′ q) ≡ src k (comp r _ _ qd)
    r₀ = trans p (cong (src k) (sym (idem dd qd)))
    eq : comp k (comp r y₁ y′ q) _ p ≡ comp r (comp k y₁ _ p₁) (comp k y′ _ p′) q₂
    eq = trans (comp-cong k p r₀ refl (sym (idem dd qd)))
               (interchange y₁ y′ _ _ l q qd r₀ p₁ p′ q₂)

  ----------------------------------------------------------------------
  -- Distribution over an r-dimensional cell on the left.

  dist-l : ∀ {k r} → k < r → ∀ f fs D {y d} → Ev (cmpR r f fs) y → Ev D d → Dim r d →
           (p : tgt k d ≡ src k y) →
           Ev (cmpR r (cmp k D f) (mapE (λ g → cmp k D g) fs)) (comp k d y p)
  dist-l l f []       D a vd dd p = ev-cmp _ vd a p
  dist-l {k} {r} l f (g ∷ gs) D (ev-cmp .r {x = y₁} {y = y′} a b q) vd dd p =
    Ev-sub (sym eq) (ev-cmp r (ev-cmp k vd a p₁) ih q₂)
    where
    p₁ : tgt k _ ≡ src k y₁
    p₁ = trans p (src-comp-< y₁ y′ q l)
    p′ : tgt k _ ≡ src k y′
    p′ = trans p₁ (trans (sym (src-tgt-< y₁ l)) (trans (cong (src k) q) (src-src-< y′ l)))
    ih = dist-l l g gs D b vd dd p′
    qa : tgt k (tgt r _) ≡ src k (tgt r y₁)
    qa = trans (tgt-tgt-< _ l) (trans p₁ (sym (src-tgt-< y₁ l)))
    qb : tgt k (src r _) ≡ src k (src r y′)
    qb = trans (tgt-src-< _ l) (trans p′ (sym (src-src-< y′ l)))
    q₂ : tgt r (comp k _ y₁ p₁) ≡ src r (comp k _ y′ p′)
    q₂ = trans (tgt-comp-> _ y₁ p₁ l qa)
               (trans (comp-cong k qa qb (trans (Dim-tgt dd) (sym dd)) q)
                      (sym (src-comp-> _ y′ p′ l qb)))
    qd : tgt r _ ≡ src r _
    qd = trans (Dim-tgt dd) (sym dd)
    r₀ : tgt k (comp r _ _ qd) ≡ src k (comp r y₁ y′ q)
    r₀ = trans (cong (tgt k) (idem dd qd)) p
    eq : comp k _ (comp r y₁ y′ q) p ≡ comp r (comp k _ y₁ p₁) (comp k _ y′ p′) q₂
    eq = trans (comp-cong k p r₀ (sym (idem dd qd)) refl)
               (interchange _ _ y₁ y′ l qd q r₀ p₁ p′ q₂)

  ----------------------------------------------------------------------
  -- Y #ₖ Z = (Y #ₖ ∂ᵣ⁻Z) #ᵣ (∂ᵣ⁺Y #ₖ Z), for k < r.

  split : ∀ {k r} → k < r → ∀ y z (p : tgt k y ≡ src k z) →
          Σ (tgt k y ≡ src k (src r z)) λ p₁ →
          Σ (tgt k (tgt r y) ≡ src k z) λ p₂ →
          Σ (tgt r (comp k y (src r z) p₁) ≡ src r (comp k (tgt r y) z p₂)) λ q →
          comp k y z p ≡ comp r (comp k y (src r z) p₁) (comp k (tgt r y) z p₂) q
  split {k} {r} l y z p = p₁ , p₂ , q , eq
    where
    p₁ = trans p (sym (src-src-< z l))
    p₂ = trans (tgt-tgt-< y l) p
    qa : tgt k (tgt r y) ≡ src k (tgt r (src r z))
    qa = trans (tgt-tgt-< y l) (trans p (sym (trans (src-tgt-< (src r z) l) (src-src-< z l))))
    qb : tgt k (src r (tgt r y)) ≡ src k (src r z)
    qb = trans (tgt-src-< (tgt r y) l) (trans (tgt-tgt-< y l) p₁)
    q : tgt r (comp k y (src r z) p₁) ≡ src r (comp k (tgt r y) z p₂)
    q = trans (tgt-comp-> y (src r z) p₁ l qa)
              (trans (comp-cong k qa qb (sym (src-tgt-≥ y (≤-refl r))) (tgt-src-≥ z (≤-refl r)))
                     (sym (src-comp-> (tgt r y) z p₂ l qb)))
    u₁ : tgt r y ≡ src r (tgt r y)
    u₁ = sym (src-tgt-≥ y (≤-refl r))
    u₂ : tgt r (src r z) ≡ src r z
    u₂ = tgt-src-≥ z (≤-refl r)
    r₀ : tgt k (comp r y (tgt r y) u₁) ≡ src k (comp r (src r z) z u₂)
    r₀ = trans (cong (tgt k) (unit-r r y u₁)) (trans p (cong (src k) (sym (unit-l r z u₂))))
    eq = trans (comp-cong k p r₀ (sym (unit-r r y u₁)) (sym (unit-l r z u₂)))
               (interchange y (tgt r y) (src r z) z l u₁ u₂ r₀ p₁ p₂ q)

  ----------------------------------------------------------------------
  -- Concatenation of r-composites.

  _++E_ : List (Expr G) → List (Expr G) → List (Expr G)
  _++E_ = _++_

  cat : ∀ r f fs g gs {y z} → Ev (cmpR r f fs) y → Ev (cmpR r g gs) z → (p : tgt r y ≡ src r z) →
        Ev (cmpR r f (fs ++ (g ∷ gs))) (comp r y z p)
  cat r f []       g gs a b p = ev-cmp r a b p
  cat r f (h ∷ hs) g gs (ev-cmp .r {x = y₁} {y = y′} a a′ q) b p =
    Ev-sub (sym (assoc r y₁ y′ _ q p q′ p′′)) (ev-cmp r a (cat r h hs g gs a′ b q′) p′′)
    where
    q′ : tgt r y′ ≡ src r _
    q′ = trans (sym (tgt-comp r y₁ y′ q)) p
    p′′ : tgt r y₁ ≡ src r (comp r y′ _ q′)
    p′′ = trans q (sym (src-comp r y′ _ q′))

  ----------------------------------------------------------------------
  -- A k-dimensional left factor is absorbed: Y #ₖ Z = Z when Y is
  -- k-dimensional; similarly on the right.

  absorb-l : ∀ {k y z} → Dim k y → (p : tgt k y ≡ src k z) → comp k y z p ≡ z
  absorb-l {k} {y} {z} dy p =
    trans (comp-cong k p (tgt-src-≥ z (≤-refl k)) (trans (sym (Dim-tgt dy)) p) refl) (unit-l k z _)

  absorb-r : ∀ {k y z} → Dim k z → (p : tgt k y ≡ src k z) → comp k y z p ≡ y
  absorb-r {k} {y} {z} dz p =
    trans (comp-cong k p (sym (src-tgt-≥ y (≤-refl k))) refl (trans (sym dz) (sym p))) (unit-r k y _)

  ----------------------------------------------------------------------
  -- The other form: Y #ₖ Z = (∂ᵣ⁻Y #ₖ Z) #ᵣ (Y #ₖ ∂ᵣ⁺Z), for k < r.

  split′ : ∀ {k r} → k < r → ∀ y z (p : tgt k y ≡ src k z) →
           Σ (tgt k (src r y) ≡ src k z) λ p₁ →
           Σ (tgt k y ≡ src k (tgt r z)) λ p₂ →
           Σ (tgt r (comp k (src r y) z p₁) ≡ src r (comp k y (tgt r z) p₂)) λ q →
           comp k y z p ≡ comp r (comp k (src r y) z p₁) (comp k y (tgt r z) p₂) q
  split′ {k} {r} l y z p = p₁ , p₂ , q , eq
    where
    p₁ = trans (tgt-src-< y l) p
    p₂ = trans p (sym (src-tgt-< z l))
    qa : tgt k (tgt r (src r y)) ≡ src k (tgt r z)
    qa = trans (tgt-tgt-< (src r y) l) (trans p₁ (sym (src-tgt-< z l)))
    qb : tgt k (src r y) ≡ src k (src r (tgt r z))
    qb = trans p₁ (trans (sym (src-tgt-< z l)) (sym (src-src-< (tgt r z) l)))
    q : tgt r (comp k (src r y) z p₁) ≡ src r (comp k y (tgt r z) p₂)
    q = trans (tgt-comp-> (src r y) z p₁ l qa)
              (trans (comp-cong k qa qb (tgt-src-≥ y (≤-refl r)) (sym (src-tgt-≥ z (≤-refl r))))
                     (sym (src-comp-> y (tgt r z) p₂ l qb)))
    u₁ : tgt r (src r y) ≡ src r y
    u₁ = tgt-src-≥ y (≤-refl r)
    u₂ : tgt r z ≡ src r (tgt r z)
    u₂ = sym (src-tgt-≥ z (≤-refl r))
    r₀ : tgt k (comp r (src r y) y u₁) ≡ src k (comp r z (tgt r z) u₂)
    r₀ = trans (cong (tgt k) (unit-l r y u₁)) (trans p (cong (src k) (sym (unit-r r z u₂))))
    eq = trans (comp-cong k p r₀ (sym (unit-l r y u₁)) (sym (unit-r r z u₂)))
               (interchange (src r y) y z (tgt r z) l u₁ u₂ r₀ p₁ p₂ q)
