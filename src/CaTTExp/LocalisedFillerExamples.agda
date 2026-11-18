------------------------------------------------------------------------
-- Examples for the localised-graph filler (CaTTExp.LocalisedFiller,
-- F4a). Every cell is returned with a derivation from the certified
-- checker.
------------------------------------------------------------------------
module CaTTExp.LocalisedFillerExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.LocalisedFiller

private
  v : Nat → Tm
  v = var

------------------------------------------------------------------------
-- ℤ: the loop s : x → x with inverse data. Levels:
-- x0 s1 s̄2 ρ3 ρ̄4 λ5 λ̄6.

x s s̄ : Tm
x = v 0 ; s = v 1 ; s̄ = v 2

_⨾_ : Tm → Tm → Tm
f ⨾ g = comp x x f x g

hom : Ty
hom = arr ⋆ x x

Z : Ctx
Z = ε ▸ ⋆ ▸ hom ▸ hom
      ▸ arr hom (s ⨾ s̄) (id x) ▸ arr hom (id x) (s ⨾ s̄)
      ▸ arr hom (s̄ ⨾ s) (id x) ▸ arr hom (id x) (s̄ ⨾ s)

dZ : List InvData
dZ = invd 1 2 3 4 5 6 ∷ []

-- 1 - 1 = 0.
cancel : Z ⊢tm _ ∶ arr hom (s ⨾ s̄) (id x)
cancel = snd (from-just (fill Z dZ (s ⨾ s̄) (id x) hom))

-- 1 - 1 + 1 = 1, in both bracketings.
_ : is-just (fill Z dZ ((s ⨾ s̄) ⨾ s) s hom) ≡ true
_ = refl

back-forth : Z ⊢tm _ ∶ arr hom (s ⨾ (s̄ ⨾ s)) s
back-forth = snd (from-just (fill Z dZ (s ⨾ (s̄ ⨾ s)) s hom))

-- (1 + 1) - (1 + 1) = 0: two nested cancellations.
nested : Z ⊢tm _ ∶ arr hom ((s ⨾ s) ⨾ (s̄ ⨾ s̄)) (id x)
nested = snd (from-just (fill Z dZ ((s ⨾ s) ⨾ (s̄ ⨾ s̄)) (id x) hom))

-- s̄ ; s and s ; s̄ are both 0: one cancellation forward, one backward.
swap : Z ⊢tm _ ∶ arr hom (s̄ ⨾ s) (s ⨾ s̄)
swap = snd (from-just (fill Z dZ (s̄ ⨾ s) (s ⨾ s̄) hom))

-- -1 + 2 = 1 + 0, with units.
mixed : Z ⊢tm _ ∶ arr hom (s̄ ⨾ (s ⨾ s)) (s ⨾ id x)
mixed = snd (from-just (fill Z dZ (s̄ ⨾ (s ⨾ s)) (s ⨾ id x) hom))

-- Negative: 1 and -1 have different reduced words; so do 2 and 0.
_ : is-just (fill Z dZ s s̄ hom) ≡ false
_ = refl

_ : is-just (fill Z dZ (s ⨾ s) (id x) hom) ≡ false
_ = refl

------------------------------------------------------------------------
-- Two objects: m : x → y inverted, and an ordinary edge g : y → x.
-- Levels: x0 y1 m2 m̄3 g4 ρ5 ρ̄6 λ7 λ̄8.

private
  X Y m m̄ g : Tm
  X = v 0 ; Y = v 1 ; m = v 2 ; m̄ = v 3 ; g = v 4

  c : Tm → Tm → Tm → Tm → Tm → Tm
  c = comp

E : Ctx
E = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ X Y ▸ arr ⋆ Y X ▸ arr ⋆ Y X
      ▸ arr (arr ⋆ X X) (c X Y m X m̄) (id X) ▸ arr (arr ⋆ X X) (id X) (c X Y m X m̄)
      ▸ arr (arr ⋆ Y Y) (c Y X m̄ Y m) (id Y) ▸ arr (arr ⋆ Y Y) (id Y) (c Y X m̄ Y m)

dE : List InvData
dE = invd 2 3 5 6 7 8 ∷ []

-- (m̄ ; m) ; g ⇒ g.
mg : E ⊢tm _ ∶ arr (arr ⋆ Y X) (c Y Y (c Y X m̄ Y m) X g) g
mg = snd (from-just (fill E dE (c Y Y (c Y X m̄ Y m) X g) g (arr ⋆ Y X)))

-- g ; (m ; m̄) ⇒ (m̄ ; m) ; g: both reduce to g.
gm : E ⊢tm _ ∶ arr (arr ⋆ Y X) (c Y X g X (c X Y m X m̄)) (c Y Y (c Y X m̄ Y m) X g)
gm = snd (from-just (fill E dE (c Y X g X (c X Y m X m̄)) (c Y Y (c Y X m̄ Y m) X g) (arr ⋆ Y X)))

-- Negative: g and m̄ are different edges y → x.
_ : is-just (fill E dE g m̄ (arr ⋆ Y X)) ≡ false
_ = refl
