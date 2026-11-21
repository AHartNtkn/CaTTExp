------------------------------------------------------------------------
-- The mirror of the biclosed rows (ledger D8, closed-structure.md §D.5).
--
-- For an alternating object duality (K = odd, i.e. (–)^op, or K = even,
-- i.e. (–)^co) the Gray tensor reverses:  (X ⊗ Y)^K ≅ Y^K ⊗ X^K
-- (GrayDuality, SwapC↔Alt).  So a multimap X₁ ⊗ … ⊗ Xₙ → Z becomes a
-- multimap Xₙ^K ⊗ … ⊗ X₁^K → Z^K, the lax hom A\C becomes the oplax hom
-- C^K/A^K, and the pair, probe and unit rows go to rows of the same kind
-- at the mirrored slot.  This module defines that mirror on the syntax
-- of the biclosed checker and checks that the row table of F.7.4 §2 is
-- closed under it.
--
-- The mirror (mirFm, mirM, mirRow, mirTm):
--   obj i ↦ obj i            (the variable now names the dual object)
--   rep Θ ↦ rep (mirSh Θ)    Δ ⊠ Θ ↦ mirSh Θ ⊠ mirSh Δ, disk n ↦ disk n
--                            (⟦Dⁿ⟧^K ≅ ⟦Dⁿ⟧), named n ↦ named n (the name
--                            now denotes the dual shape)
--   A ⊗ B ↦ B* ⊗ A*,   A\C ↦ C*/A*,   C/A ↦ A*\C*
--   (X₁, …, Xₙ ▸ Z) ↦ (Xₙ*, …, X₁* ▸ Z*)
--   m_{U,V} ↦ m_{V*,U*},  e^ℓ_{A,C} ↦ e^r_{A*,C*},  e^r ↦ e^ℓ,
--   p_{Δ,Θ} ↦ p_{Θ*,Δ*},  pt ↦ pt,  1_A ↦ 1_{A*},
--   f ∘ (g₁, …, gₙ) ↦ f* ∘ (gₙ*, …, g₁*).
--
-- Proved (no postulates):
--   * mirFm-invol, mirM-invol, mirRow-invol: the mirror is an involution;
--   * H-mir, B-mir: the two vertex types of the mirrored row are the
--     mirrors of the original ones;
--   * rmap-mir: the restriction r of the mirrored row is the mirror of
--     r, for every term x;
--   * rowsOf-mir: every row read off a multimap type M has its mirror
--     among the rows read off the mirror of M (and conversely, by
--     involution), so the candidate templates of F.7.4's decision
--     procedure are mirror-closed.
--
-- Not covered here (stated in the note): the time-slot direction (the
-- slot ⟦Dᵏ⟧ keeps its gap's mirror, and its source and target swap iff
-- k ∈ K), the invertible collars of the generic contexts (their
-- orientation reverses with the slot's, so the mirrored context is a
-- template context only up to inverting collars), and the probe
-- restrictions along L-substitutions, which need the duality to be a
-- symmetry of the L core (GrayDualityUniform: false for every K ≠ ∅ in
-- the uniform core).  On `glue` and `here` mirTm acts structurally; no
-- claim is made about it there.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Mirror where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.GrayDuality using (_⊎_; inj₁; inj₂)
open import CaTTExp.Gray.Biclosed.Rows
open import CaTTExp.Gray.Biclosed.Templates
  using (rowsOf; outRows; slotRow; slotRows; _∈_; here!; there!;
         ∈-++ˡ; ∈-++ʳ; ++-assoc)

------------------------------------------------------------------------
-- Lists

rev : ∀ {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

rev-++ : ∀ {A : Set} (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-++ []       ys = sym (++-[] (rev ys))
rev-++ (x ∷ xs) ys =
  trans (cong (_++ (x ∷ [])) (rev-++ xs ys))
        (++-assoc (rev ys) (rev xs) (x ∷ []))

map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- reverse-and-map
rmapL : ∀ {A B : Set} → (A → B) → List A → List B
rmapL f xs = rev (map f xs)

rmapL-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) →
           rmapL f (xs ++ ys) ≡ rmapL f ys ++ rmapL f xs
rmapL-++ f xs ys = trans (cong rev (map-++ f xs ys)) (rev-++ (map f xs) (map f ys))

-- rmapL f (L ++ x ∷ R) = rmapL f R ++ f x ∷ rmapL f L
rmapL-split : ∀ {A B : Set} (f : A → B) (L : List A) x (R : List A) →
              rmapL f (L ++ x ∷ R) ≡ rmapL f R ++ f x ∷ rmapL f L
rmapL-split f L x R =
  trans (rmapL-++ f L (x ∷ R))
        (++-assoc (rmapL f R) (f x ∷ []) (rmapL f L))

rev-map-rev : ∀ {A B : Set} (f : A → B) (xs : List A) →
              rev (map f (rev xs)) ≡ map f xs
rev-map-rev f []       = refl
rev-map-rev f (x ∷ xs) =
  trans (cong rev (map-++ f (rev xs) (x ∷ [])))
        (trans (rev-++ (map f (rev xs)) (f x ∷ []))
               (cong (f x ∷_) (rev-map-rev f xs)))

map-∘ : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : List A) →
        map g (map f xs) ≡ map (λ x → g (f x)) xs
map-∘ g f []       = refl
map-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (map-∘ g f xs)

map-id : ∀ {A : Set} (f : A → A) → (∀ x → f x ≡ x) → ∀ xs → map f xs ≡ xs
map-id f h []       = refl
map-id f h (x ∷ xs) = cong₂ _∷_ (h x) (map-id f h xs)

map-rev : ∀ {A B : Set} (f : A → B) (xs : List A) → map f (rev xs) ≡ rev (map f xs)
map-rev f []       = refl
map-rev f (x ∷ xs) = trans (map-++ f (rev xs) (x ∷ [])) (cong (_++ (f x ∷ [])) (map-rev f xs))

rev-rev : ∀ {A : Set} (xs : List A) → rev (rev xs) ≡ xs
rev-rev []       = refl
rev-rev (x ∷ xs) = trans (rev-++ (rev xs) (x ∷ [])) (cong (x ∷_) (rev-rev xs))

-- rmapL of an involution is an involution
rmapL-invol : ∀ {A : Set} (f : A → A) → (∀ x → f (f x) ≡ x) →
              ∀ xs → rmapL f (rmapL f xs) ≡ xs
rmapL-invol f h xs =
  trans (cong rev (map-rev f (map f xs)))
        (trans (rev-rev (map f (map f xs)))
               (trans (map-∘ f f xs) (map-id _ h xs)))

------------------------------------------------------------------------
-- The mirror

mirSh : Shape → Shape
mirSh (disk n)  = disk n
mirSh (named n) = named n
mirSh (a ⊠ b)   = mirSh b ⊠ mirSh a

mirFm : Fm → Fm
mirFm (obj i)  = obj i
mirFm (rep θ)  = rep (mirSh θ)
mirFm (shp θ)  = shp (mirSh θ)
mirFm (a ⊗ b)  = mirFm b ⊗ mirFm a
mirFm (a \\ c) = mirFm c // mirFm a
mirFm (c // a) = mirFm a \\ mirFm c

mirL : List Fm → List Fm
mirL = rmapL mirFm

mirM : MTy → MTy
mirM (xs ▸ z) = mirL xs ▸ mirFm z

mirRow : Row → Row
mirRow (pairR L U V R Z)  = pairR (mirL R) (mirFm V) (mirFm U) (mirL L) (mirFm Z)
mirRow (probeR L Δ Θ R Z) = probeR (mirL R) (mirSh Θ) (mirSh Δ) (mirL L) (mirFm Z)
mirRow (unitR L R Z)      = unitR (mirL R) (mirL L) (mirFm Z)
mirRow (shapeR L Θ R Z)   = shapeR (mirL R) (mirSh Θ) (mirL L) (mirFm Z)
mirRow (evLR Φ A C)       = evRR (mirL Φ) (mirFm A) (mirFm C)
mirRow (evRR Φ A C)       = evLR (mirL Φ) (mirFm A) (mirFm C)

mutual
  mirTm : Tm → Tm
  mirTm (var i)          = var i
  mirTm (mP u v)         = mP (mirFm v) (mirFm u)
  mirTm (eL a c)         = eR (mirFm a) (mirFm c)
  mirTm (eR a c)         = eL (mirFm a) (mirFm c)
  mirTm (pP d θ)         = pP (mirSh θ) (mirSh d)
  mirTm pt               = pt
  mirTm (iP θ)           = iP (mirSh θ)
  mirTm (idt a)          = idt (mirFm a)
  mirTm (comp f gs)      = comp (mirTm f) (mirTs gs)
  mirTm (glue a x b)     = glue (mirTm a) (mirTm x) (mirTm b)
  mirTm (here t e φs ts) = here t e φs ts

  -- reverse the argument list and mirror each argument
  mirTs : List Tm → List Tm
  mirTs []       = []
  mirTs (g ∷ gs) = mirTs gs ++ (mirTm g ∷ [])

mirTs≡ : ∀ gs → mirTs gs ≡ rmapL mirTm gs
mirTs≡ []       = refl
mirTs≡ (g ∷ gs) = cong (_++ (mirTm g ∷ [])) (mirTs≡ gs)

------------------------------------------------------------------------
-- Involution

mirSh-invol : ∀ θ → mirSh (mirSh θ) ≡ θ
mirSh-invol (disk n)  = refl
mirSh-invol (named n) = refl
mirSh-invol (a ⊠ b)   = cong₂ _⊠_ (mirSh-invol a) (mirSh-invol b)

mirFm-invol : ∀ a → mirFm (mirFm a) ≡ a
mirFm-invol (obj i)  = refl
mirFm-invol (rep θ)  = cong rep (mirSh-invol θ)
mirFm-invol (shp θ)  = cong shp (mirSh-invol θ)
mirFm-invol (a ⊗ b)  = cong₂ _⊗_ (mirFm-invol a) (mirFm-invol b)
mirFm-invol (a \\ c) = cong₂ _\\_ (mirFm-invol a) (mirFm-invol c)
mirFm-invol (c // a) = cong₂ _//_ (mirFm-invol c) (mirFm-invol a)

mirL-invol : ∀ xs → mirL (mirL xs) ≡ xs
mirL-invol = rmapL-invol mirFm mirFm-invol

mirM-invol : ∀ M → mirM (mirM M) ≡ M
mirM-invol (xs ▸ z) = cong₂ _▸_ (mirL-invol xs) (mirFm-invol z)

mirRow-invol : ∀ ρ → mirRow (mirRow ρ) ≡ ρ
mirRow-invol (pairR L U V R Z) rewrite mirL-invol L | mirL-invol R
  | mirFm-invol U | mirFm-invol V | mirFm-invol Z = refl
mirRow-invol (probeR L Δ Θ R Z) rewrite mirL-invol L | mirL-invol R
  | mirSh-invol Δ | mirSh-invol Θ | mirFm-invol Z = refl
mirRow-invol (unitR L R Z) rewrite mirL-invol L | mirL-invol R
  | mirFm-invol Z = refl
mirRow-invol (shapeR L Θ R Z) rewrite mirL-invol L | mirL-invol R
  | mirSh-invol Θ | mirFm-invol Z = refl
mirRow-invol (evLR Φ A C) rewrite mirL-invol Φ | mirFm-invol A
  | mirFm-invol C = refl
mirRow-invol (evRR Φ A C) rewrite mirL-invol Φ | mirFm-invol A
  | mirFm-invol C = refl

------------------------------------------------------------------------
-- The vertex types and the restriction commute with the mirror.

H-mir : ∀ ρ → H (mirRow ρ) ≡ mirM (H ρ)
H-mir (pairR L U V R Z)  = cong (_▸ mirFm Z) (sym (rmapL-split mirFm L (U ⊗ V) R))
H-mir (probeR L Δ Θ R Z) = cong (_▸ mirFm Z) (sym (rmapL-split mirFm L (rep (Δ ⊠ Θ)) R))
H-mir (unitR L R Z)      = cong (_▸ mirFm Z) (sym (rmapL-split mirFm L (rep (disk 0)) R))
H-mir (shapeR L Θ R Z)   = cong (_▸ mirFm Z) (sym (rmapL-split mirFm L (shp Θ) R))
H-mir (evLR Φ A C)       = refl
H-mir (evRR Φ A C)       = refl

B-mir : ∀ ρ → B (mirRow ρ) ≡ mirM (B ρ)
B-mir (pairR L U V R Z) = cong (_▸ mirFm Z) (sym
  (trans (rmapL-split mirFm L U (V ∷ R))
         (trans (cong (λ s → s ++ mirFm U ∷ mirL L) (rmapL-++ mirFm (V ∷ []) R))
                (++-assoc (mirL R) (mirFm V ∷ []) (mirFm U ∷ mirL L)))))
B-mir (probeR L Δ Θ R Z) = cong (_▸ mirFm Z) (sym
  (trans (rmapL-split mirFm L (rep Δ) (rep Θ ∷ R))
         (trans (cong (λ s → s ++ rep (mirSh Δ) ∷ mirL L) (rmapL-++ mirFm (rep Θ ∷ []) R))
                (++-assoc (mirL R) (rep (mirSh Θ) ∷ []) (rep (mirSh Δ) ∷ mirL L)))))
B-mir (unitR L R Z) = cong (_▸ mirFm Z) (sym (rmapL-++ mirFm L R))
B-mir (shapeR L Θ R Z) = cong (_▸ mirFm Z) (sym (rmapL-split mirFm L (rep Θ) R))
B-mir (evLR Φ A C)  = refl
B-mir (evRR Φ A C)  = cong (_▸ mirFm C) (sym (rmapL-++ mirFm Φ (A ∷ [])))

-- identities: mirror of ids L is ids of the mirror of L, reversed
ids-mir : ∀ L → rmapL mirTm (ids L) ≡ ids (mirL L)
ids-mir L =
  trans (cong rev (map-∘ mirTm idt L))
        (trans (cong rev (sym (map-∘ idt mirFm L)))
               (sym (map-rev idt (map mirFm L))))

rmap-mir : ∀ ρ x → rmap (mirRow ρ) (mirTm x) ≡ mirTm (rmap ρ x)
rmap-mir (pairR L U V R Z) x = cong (comp (mirTm x)) (sym
  (trans (mirTs≡ (ids L ++ mP U V ∷ ids R))
    (trans (rmapL-split mirTm (ids L) (mP U V) (ids R))
           (cong₂ (λ a b → a ++ mP (mirFm V) (mirFm U) ∷ b) (ids-mir R) (ids-mir L)))))
rmap-mir (probeR L Δ Θ R Z) x = cong (comp (mirTm x)) (sym
  (trans (mirTs≡ (ids L ++ pP Δ Θ ∷ ids R))
    (trans (rmapL-split mirTm (ids L) (pP Δ Θ) (ids R))
           (cong₂ (λ a b → a ++ pP (mirSh Θ) (mirSh Δ) ∷ b) (ids-mir R) (ids-mir L)))))
rmap-mir (unitR L R Z) x = cong (comp (mirTm x)) (sym
  (trans (mirTs≡ (ids L ++ pt ∷ ids R))
    (trans (rmapL-split mirTm (ids L) pt (ids R))
           (cong₂ (λ a b → a ++ pt ∷ b) (ids-mir R) (ids-mir L)))))
rmap-mir (shapeR L Θ R Z) x = cong (comp (mirTm x)) (sym
  (trans (mirTs≡ (ids L ++ iP Θ ∷ ids R))
    (trans (rmapL-split mirTm (ids L) (iP Θ) (ids R))
           (cong₂ (λ a b → a ++ iP (mirSh Θ) ∷ b) (ids-mir R) (ids-mir L)))))
rmap-mir (evLR Φ A C) x = refl
rmap-mir (evRR Φ A C) x = refl

------------------------------------------------------------------------
-- The candidate rows of a multimap type are mirror-closed.

-- membership in slotRows, by the split of the input list
slot-split : ∀ {ρ} pre xs z → ρ ∈ slotRows pre xs z →
  Σ (List Fm) λ L → Σ Fm λ x → Σ (List Fm) λ R →
    (xs ≡ L ++ x ∷ R) × (ρ ∈ slotRow (pre ++ L) x R z)
slot-split pre [] z ()
slot-split {ρ} pre (x ∷ xs) z p = go (slotRow pre x xs z) refl p
  where
  go : ∀ ys → ys ≡ slotRow pre x xs z → ρ ∈ (ys ++ slotRows (pre ++ x ∷ []) xs z) →
       Σ (List Fm) λ L → Σ Fm λ y → Σ (List Fm) λ R →
         (x ∷ xs ≡ L ++ y ∷ R) × (ρ ∈ slotRow (pre ++ L) y R z)
  tailCase : ρ ∈ slotRows (pre ++ x ∷ []) xs z →
       Σ (List Fm) λ L → Σ Fm λ y → Σ (List Fm) λ R →
         (x ∷ xs ≡ L ++ y ∷ R) × (ρ ∈ slotRow (pre ++ L) y R z)
  tailCase q with slot-split (pre ++ x ∷ []) xs z q
  ... | L , y , R , eq , m =
        (x ∷ L) , y , R , cong (x ∷_) eq ,
        subst (λ s → ρ ∈ slotRow s y R z) (++-assoc pre (x ∷ []) L) m
  go [] e q = tailCase q
  go (r ∷ rs) e here! =
        [] , x , xs , refl ,
        subst (λ s → ρ ∈ slotRow s x xs z) (sym (++-[] pre)) (subst (ρ ∈_) e here!)
  go (r ∷ []) e (there! q) = tailCase q
  go (r ∷ r′ ∷ rs) e (there! q) = ⊥-elim (one-row pre x xs z r r′ rs e)
    where
    one-row : ∀ pre x xs z r r′ rs → r ∷ r′ ∷ rs ≡ slotRow pre x xs z → ⊥
    one-row pre (obj _) xs z r r′ rs ()
    one-row pre (rep (disk zero)) xs z r r′ rs ()
    one-row pre (rep (disk (suc _))) xs z r r′ rs ()
    one-row pre (rep (named _)) xs z r r′ rs ()
    one-row pre (rep (_ ⊠ _)) xs z r r′ rs ()
    one-row pre (_ ⊗ _) xs z r r′ rs ()
    one-row pre (shp _) xs z r r′ rs ()
    one-row pre (_ \\ _) xs z r r′ rs ()
    one-row pre (_ // _) xs z r r′ rs ()

-- and back: a slot row at a split is in slotRows
slot-in : ∀ {ρ} pre L x R z → ρ ∈ slotRow (pre ++ L) x R z →
          ρ ∈ slotRows pre (L ++ x ∷ R) z
slot-in pre [] x R z m =
  ∈-++ˡ (slotRows (pre ++ x ∷ []) R z) (subst (λ s → _ ∈ slotRow s x R z) (++-[] pre) m)
slot-in pre (y ∷ L) x R z m =
  ∈-++ʳ (slotRow pre y (L ++ x ∷ R) z)
        (slot-in (pre ++ y ∷ []) L x R z
          (subst (λ s → _ ∈ slotRow s x R z) (sym (++-assoc pre (y ∷ []) L)) m))

-- the mirror of a slot row at (L, x, R) is a slot row at (R*, x*, L*)
slotRow-mir : ∀ {ρ} L x R z → ρ ∈ slotRow L x R z →
              mirRow ρ ∈ slotRow (mirL R) (mirFm x) (mirL L) (mirFm z)
slotRow-mir L (u ⊗ v)           R z here! = here!
slotRow-mir L (rep (d ⊠ θ))     R z here! = here!
slotRow-mir L (rep (disk zero)) R z here! = here!
slotRow-mir L (u ⊗ v)           R z (there! ())
slotRow-mir L (rep (d ⊠ θ))     R z (there! ())
slotRow-mir L (rep (disk zero)) R z (there! ())
slotRow-mir L (shp θ)           R z here! = here!
slotRow-mir L (shp θ)           R z (there! ())
slotRow-mir L (obj _)              R z ()
slotRow-mir L (rep (disk (suc _))) R z ()
slotRow-mir L (rep (named _))      R z ()
slotRow-mir L (_ \\ _)             R z ()
slotRow-mir L (_ // _)             R z ()

outRows-mir : ∀ {ρ} xs z → ρ ∈ outRows xs z → mirRow ρ ∈ outRows (mirL xs) (mirFm z)
outRows-mir xs (a \\ c) here! = here!
outRows-mir xs (c // a) here! = here!
outRows-mir xs (a \\ c) (there! ())
outRows-mir xs (c // a) (there! ())
outRows-mir xs (obj _) ()
outRows-mir xs (rep _) ()
outRows-mir xs (shp _) ()
outRows-mir xs (_ ⊗ _) ()

∈-++-split : ∀ {A : Set} {x : A} xs ys → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
∈-++-split []       ys p          = inj₂ p
∈-++-split (y ∷ xs) ys here!      = inj₁ here!
∈-++-split (y ∷ xs) ys (there! p) with ∈-++-split xs ys p
... | inj₁ q = inj₁ (there! q)
... | inj₂ q = inj₂ q

rowsOf-mir : ∀ {ρ} M → ρ ∈ rowsOf M → mirRow ρ ∈ rowsOf (mirM M)
rowsOf-mir {ρ} (xs ▸ z) p with ∈-++-split (outRows xs z) (slotRows [] xs z) p
... | inj₁ q = ∈-++ˡ (slotRows [] (mirL xs) (mirFm z)) (outRows-mir xs z q)
... | inj₂ q with slot-split [] xs z q
...   | L , x , R , refl , m =
        ∈-++ʳ (outRows (mirL (L ++ x ∷ R)) (mirFm z))
          (subst (λ s → mirRow ρ ∈ slotRows [] s (mirFm z))
                 (sym (rmapL-split mirFm L x R))
                 (slot-in [] (mirL R) (mirFm x) (mirL L) (mirFm z)
                          (slotRow-mir L x R z m)))

-- and conversely, since the mirror is an involution
rowsOf-mir⁻ : ∀ {ρ} M → mirRow ρ ∈ rowsOf (mirM M) → ρ ∈ rowsOf M
rowsOf-mir⁻ {ρ} M p =
  subst (λ r → r ∈ rowsOf M) (mirRow-invol ρ)
    (subst (λ N → mirRow (mirRow ρ) ∈ rowsOf N) (mirM-invol M)
           (rowsOf-mir (mirM M) p))
