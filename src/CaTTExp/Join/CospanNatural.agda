------------------------------------------------------------------------
-- Naturality of the cospan completion.
--
-- Let F : Path(Q) → Path(Q′) be a functor of free categories that
--   * sends each inner arrow to an inner path (fE), and
--   * sends each seed to a word that contains a seed (fP).
-- A word containing a seed is uniquely  pre ; β ; post  with β its
-- last seed and post inner, which is what fP returns. This is the
-- class of maps in r7 §2 (τ ↦ A ; f is one), and it is closed under
-- composition.
--
-- F extends to the cospan completions by
--
--   j α I R  ↦  pre ; j β (post ; F I) (F R),
--
-- the extension respects the equations (map-~), composition (map-++)
-- and agrees with F on original paths up to the equations (map-ι).
-- Compare CaTTExp.Join.NotNatural, where the same F has no extension
-- to r7's completion.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
import CaTTExp.Join.Cospan as Cospan

module CaTTExp.Join.CospanNatural
  {V V′ : Set} (E P : V → V → Set) (E′ P′ : V′ → V′ → Set) where

module C  = Cospan E P
module C′ = Cospan E′ P′
open C  using (inn; jn; oe; op; ctr; exp; skip; fwd; rfl; sym~; trans~)
open C′ using () renaming (inn to inn′; jn to jn′; oe to oe′; op to op′)

-- A word of Q′ with a last seed: pre ; β ; post.
record SeedWord (a b : V′) : Set where
  constructor sw
  field
    {c d} : V′
    pre   : Path C′.Orig a c
    β     : P′ c d
    post  : Path E′ d b
open SeedWord

module Map (f₀ : V → V′)
           (fE : ∀ {a b} → E a b → Path E′ (f₀ a) (f₀ b))
           (fP : ∀ {a b} → P a b → SeedWord (f₀ a) (f₀ b)) where

  mapI : ∀ {a b} → C.IPath a b → C′.IPath (f₀ a) (f₀ b)
  mapI []      = []
  mapI (e ∷ R) = fE e ++ᵖ mapI R

  mapW : ∀ {a b} → C.Word a b → C′.Word (f₀ a) (f₀ b)
  mapW []             = []
  mapW (inn e ∷ w)    = C′.innW (fE e) ++ᵖ mapW w
  mapW (jn α I R ∷ w) =
    C′.ι (pre (fP α)) ++ᵖ (jn′ (β (fP α)) (post (fP α) ++ᵖ mapI I) (mapI R) ∷ mapW w)

  ----------------------------------------------------------------------
  -- Bookkeeping.

  private
    innW-++w : ∀ {a b c d} (p : C′.IPath a b) (q : C′.IPath b c) (w : C′.Word c d) →
               C′.innW (p ++ᵖ q) ++ᵖ w ≡ C′.innW p ++ᵖ (C′.innW q ++ᵖ w)
    innW-++w []      q w = refl
    innW-++w (e ∷ p) q w = cong (inn′ e ∷_) (innW-++w p q w)

    mapW-innW : ∀ {a b c} (I : C.IPath a b) (w : C.Word b c) →
                mapW (C.innW I ++ᵖ w) ≡ C′.innW (mapI I) ++ᵖ mapW w
    mapW-innW []      w = refl
    mapW-innW (e ∷ I) w =
      trans (cong (C′.innW (fE e) ++ᵖ_) (mapW-innW I w))
            (sym (innW-++w (fE e) (mapI I) (mapW w)))

    -- A joining generator swallows an inner path, one contraction per arrow.
    absorb : ∀ {s t m u v c} (b : P′ s t) (J : C′.IPath t m) (p : C′.IPath u v)
             (R : C′.IPath v m) (w : C′.Word v c) →
             jn′ b J (p ++ᵖ R) ∷ (C′.innW p ++ᵖ w) C′.⇒* jn′ b J R ∷ w
    absorb b J []      R w = C′.ε
    absorb b J (e ∷ p) R w = C′.ctr b J e (p ++ᵖ R) (C′.innW p ++ᵖ w) C′.◅ absorb b J p R w

    -- (C0): j β J [] expands to β ; J.
    expand : ∀ {s t m c} (b : P′ s t) (J : C′.IPath t m) (w : C′.Word m c) →
             jn′ b J [] ∷ w C′.⇒* jn′ b [] [] ∷ (C′.innW J ++ᵖ w)
    expand b []      w = C′.ε
    expand b (e ∷ J) w = C′.exp b e J w C′.◅ C′.ε

  ----------------------------------------------------------------------
  -- The extension respects the equations.

  map-⇒ : ∀ {a b} {w w′ : C.Word a b} → w C.⇒ w′ → mapW w C′.~ mapW w′
  map-⇒ (ctr α I e R w) =
    C′.⇒*→~ (C′.⇒*-++ˡ (C′.ι (pre (fP α)))
               (absorb (β (fP α)) (post (fP α) ++ᵖ mapI I) (fE e) (mapI R) (mapW w)))
  map-⇒ (exp α e I w) =
    C′.trans~
      (C′.⇒*→~ (C′.⇒*-++ˡ pr (expand b (q ++ᵖ (fE e ++ᵖ mapI I)) (mapW w))))
      (C′.sym~ (C′.trans~
        (C′.⇒*→~ (C′.⇒*-++ˡ pr (expand b (q ++ᵖ []) _)))
        (subst (λ z → C′.ι (pre (fP α)) ++ᵖ (jn′ b [] [] ∷ z) C′.~
                      C′.ι (pre (fP α)) ++ᵖ (jn′ b [] [] ∷
                        (C′.innW (q ++ᵖ (fE e ++ᵖ mapI I)) ++ᵖ mapW w)))
               (sym eq) C′.rfl)))
    where
    pr = C′.ι (pre (fP α))
    b  = β (fP α)
    q  = post (fP α)
    eq : C′.innW (q ++ᵖ []) ++ᵖ (C′.innW (fE e) ++ᵖ mapW (C.innW I ++ᵖ w)) ≡
         C′.innW (q ++ᵖ (fE e ++ᵖ mapI I)) ++ᵖ mapW w
    eq = trans (innW-++w q [] _)
         (trans (cong (λ z → C′.innW q ++ᵖ (C′.innW (fE e) ++ᵖ z)) (mapW-innW I w))
         (trans (cong (C′.innW q ++ᵖ_) (sym (innW-++w (fE e) (mapI I) (mapW w))))
                (sym (innW-++w q (fE e ++ᵖ mapI I) (mapW w)))))
  map-⇒ (skip (inn e) s)    = C′.~-++ˡ (C′.innW (fE e)) (map-⇒ s)
  map-⇒ (skip (jn α I R) s) =
    C′.~-++ˡ (C′.ι (pre (fP α)))
      (C′.~-++ˡ (jn′ (β (fP α)) (post (fP α) ++ᵖ mapI I) (mapI R) ∷ []) (map-⇒ s))

  map-~ : ∀ {a b} {w w′ : C.Word a b} → w C.~ w′ → mapW w C′.~ mapW w′
  map-~ (fwd s)      = map-⇒ s
  map-~ rfl          = C′.rfl
  map-~ (sym~ p)     = C′.sym~ (map-~ p)
  map-~ (trans~ p q) = C′.trans~ (map-~ p) (map-~ q)

  -- Composition.
  map-++ : ∀ {a b c} (p : C.Word a b) (q : C.Word b c) →
           mapW (p ++ᵖ q) ≡ mapW p ++ᵖ mapW q
  map-++ []             q = refl
  map-++ (inn e ∷ p)    q = trans (cong (C′.innW (fE e) ++ᵖ_) (map-++ p q))
                                  (sym (++ᵖ-assoc (C′.innW (fE e)) (mapW p) (mapW q)))
  map-++ (jn α I R ∷ p) q =
    trans (cong (λ z → C′.ι (pre (fP α)) ++ᵖ
                       (jn′ (β (fP α)) (post (fP α) ++ᵖ mapI I) (mapI R) ∷ z))
                (map-++ p q))
          (sym (++ᵖ-assoc (C′.ι (pre (fP α))) _ (mapW q)))

  ----------------------------------------------------------------------
  -- Agreement with F on original paths.

  oeP : ∀ {x y} → Path E′ x y → Path C′.Orig x y
  oeP []      = []
  oeP (e ∷ q) = oe′ e ∷ oeP q

  mapO : ∀ {a b} → Path C.Orig a b → Path C′.Orig (f₀ a) (f₀ b)
  mapO []         = []
  mapO (oe e ∷ p) = oeP (fE e) ++ᵖ mapO p
  mapO (op α ∷ p) = pre (fP α) ++ᵖ (op′ (β (fP α)) ∷ (oeP (post (fP α)) ++ᵖ mapO p))

  private
    innW-oeP : ∀ {x y z} (q : Path E′ x y) (r : Path C′.Orig y z) →
               C′.innW q ++ᵖ C′.ι r ≡ C′.ι (oeP q ++ᵖ r)
    innW-oeP []      r = refl
    innW-oeP (e ∷ q) r = cong (inn′ e ∷_) (innW-oeP q r)

  map-ι : ∀ {a b} (p : Path C.Orig a b) → mapW (C.ι p) C′.~ C′.ι (mapO p)
  map-ι []         = C′.rfl
  map-ι (oe e ∷ p) =
    subst (λ z → C′.innW (fE e) ++ᵖ mapW (C.ι p) C′.~ z) (innW-oeP (fE e) (mapO p))
          (C′.~-++ˡ (C′.innW (fE e)) (map-ι p))
  map-ι (op α ∷ p) =
    C′.trans~
      (C′.⇒*→~ (C′.⇒*-++ˡ pr (expand b (q ++ᵖ []) (mapW (C.ι p)))))
      (subst (λ z → pr ++ᵖ (jn′ b [] [] ∷ (C′.innW (q ++ᵖ []) ++ᵖ mapW (C.ι p))) C′.~ z)
             (sym (C′.ι-++ (pre (fP α)) _))
             (C′.~-++ˡ pr (C′.~-++ˡ (jn′ b [] [] ∷ [])
               (subst (λ z → C′.innW (q ++ᵖ []) ++ᵖ mapW (C.ι p) C′.~ z)
                      (innW-oeP q (mapO p))
                      (subst (λ z → C′.innW z ++ᵖ mapW (C.ι p) C′.~ C′.innW q ++ᵖ C′.ι (mapO p))
                             (sym (++ᵖ-[] q))
                             (C′.~-++ˡ (C′.innW q) (map-ι p)))))))
    where
    pr = C′.ι (pre (fP α))
    b  = β (fP α)
    q  = post (fP α)
