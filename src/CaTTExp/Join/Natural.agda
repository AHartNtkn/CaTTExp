------------------------------------------------------------------------
-- Restricted naturality of the source-only joining completion
-- (r7 §2, last paragraph).
--
-- A quiver map that sends inner arrows to inner PATHS and positive
-- seeds to positive SEEDS extends to the completions:
--
--   j α R  ↦  j (f α) (f R),
--
-- the extension respects the equations (1) (map-~), composition
-- (map-++), the inclusion of the original paths (map-ι) and seed lists
-- (map-seeds). CaTTExp.Join.NotNatural shows that sending a seed to a
-- composite cannot be extended in general.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
import CaTTExp.Join.Completion as Completion

module CaTTExp.Join.Natural
  {V V′ : Set} (E P : V → V → Set) (E′ P′ : V′ → V′ → Set)
  (f₀ : V → V′)
  (fE : ∀ {a b} → E a b → Path E′ (f₀ a) (f₀ b))
  (fP : ∀ {a b} → P a b → P′ (f₀ a) (f₀ b)) where

module C  = Completion E P
module C′ = Completion E′ P′
open C  using (inn; jn; oe; op; ctr; skip; ε; _◅_; fwd; rfl; sym~; trans~)
open C′ using () renaming (inn to inn′; jn to jn′; oe to oe′; op to op′)

mapI : ∀ {a b} → C.IPath a b → C′.IPath (f₀ a) (f₀ b)
mapI []      = []
mapI (e ∷ R) = fE e ++ᵖ mapI R

mapG : ∀ {a b} → C.Gen a b → C′.Word (f₀ a) (f₀ b)
mapG (inn e)  = C′.innW (fE e)
mapG (jn α R) = jn′ (fP α) (mapI R) ∷ []

mapW : ∀ {a b} → C.Word a b → C′.Word (f₀ a) (f₀ b)
mapW []      = []
mapW (g ∷ w) = mapG g ++ᵖ mapW w

map-++ : ∀ {a b c} (p : C.Word a b) (q : C.Word b c) →
         mapW (p ++ᵖ q) ≡ mapW p ++ᵖ mapW q
map-++ []      q = refl
map-++ (g ∷ p) q = trans (cong (mapG g ++ᵖ_) (map-++ p q))
                         (sym (++ᵖ-assoc (mapG g) (mapW p) (mapW q)))

-- A joining generator swallows an inner path, one contraction per arrow.
absorb : ∀ {s t u v c} (β : P′ s t) (p : C′.IPath u v) (R : C′.IPath v t)
         (w : C′.Word v c) →
         jn′ β (p ++ᵖ R) ∷ (C′.innW p ++ᵖ w) C′.⇒* jn′ β R ∷ w
absorb β []      R w = C′.ε
absorb β (e ∷ p) R w = C′.ctr β e (p ++ᵖ R) (C′.innW p ++ᵖ w) C′.◅ absorb β p R w

map-⇒ : ∀ {a b} {w w′ : C.Word a b} → w C.⇒ w′ → mapW w C′.⇒* mapW w′
map-⇒ (ctr α e R w) = absorb (fP α) (fE e) (mapI R) (mapW w)
map-⇒ (skip g s)    = C′.⇒*-++ˡ (mapG g) (map-⇒ s)

map-~ : ∀ {a b} {w w′ : C.Word a b} → w C.~ w′ → mapW w C′.~ mapW w′
map-~ (fwd s)      = C′.⇒*→~ (map-⇒ s)
map-~ rfl          = C′.rfl
map-~ (sym~ p)     = C′.sym~ (map-~ p)
map-~ (trans~ p q) = C′.trans~ (map-~ p) (map-~ q)

-- The underlying map of original paths.
oeP : ∀ {x y} → Path E′ x y → Path C′.Orig x y
oeP []      = []
oeP (e ∷ q) = oe′ e ∷ oeP q

mapO : ∀ {a b} → Path C.Orig a b → Path C′.Orig (f₀ a) (f₀ b)
mapO []         = []
mapO (oe e ∷ p) = oeP (fE e) ++ᵖ mapO p
mapO (op α ∷ p) = op′ (fP α) ∷ mapO p

innW-oeP : ∀ {x y z} (q : Path E′ x y) (r : Path C′.Orig y z) →
           C′.innW q ++ᵖ C′.ι r ≡ C′.ι (oeP q ++ᵖ r)
innW-oeP []      r = refl
innW-oeP (e ∷ q) r = cong (inn′ e ∷_) (innW-oeP q r)

map-ι : ∀ {a b} (p : Path C.Orig a b) → mapW (C.ι p) ≡ C′.ι (mapO p)
map-ι []         = refl
map-ι (oe e ∷ p) = trans (cong (C′.innW (fE e) ++ᵖ_) (map-ι p)) (innW-oeP (fE e) (mapO p))
map-ι (op α ∷ p) = cong (jn′ (fP α) [] ∷_) (map-ι p)

-- Seeds go to seeds.
mapS : C.Seed → C′.Seed
mapS (C.seed α) = C′.seed (fP α)

mapL : List C.Seed → List C′.Seed
mapL []       = []
mapL (x ∷ xs) = mapS x ∷ mapL xs

private
  seeds-++ : ∀ {a b c} (p : C′.Word a b) (q : C′.Word b c) →
             C′.seeds (p ++ᵖ q) ≡ C′.seeds p ++ C′.seeds q
  seeds-++ []            q = refl
  seeds-++ (inn′ e ∷ p)  q = seeds-++ p q
  seeds-++ (jn′ α R ∷ p) q = cong (C′.seed α ∷_) (seeds-++ p q)

  seeds-inn : ∀ {a b} (p : C′.IPath a b) → C′.seeds (C′.innW p) ≡ []
  seeds-inn []      = refl
  seeds-inn (e ∷ p) = seeds-inn p

map-seeds : ∀ {a b} (w : C.Word a b) → C′.seeds (mapW w) ≡ mapL (C.seeds w)
map-seeds []           = refl
map-seeds (inn e ∷ w)  =
  trans (seeds-++ (C′.innW (fE e)) (mapW w))
        (trans (cong (_++ C′.seeds (mapW w)) (seeds-inn (fE e))) (map-seeds w))
map-seeds (jn α R ∷ w) = cong (C′.seed (fP α) ∷_) (map-seeds w)
