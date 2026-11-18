{-# OPTIONS --safe --guardedness #-}
------------------------------------------------------------------------
-- Lifts of invertible cells are invertible (open-issues C4;
-- notes/free-objects-proofs.md §1).
--
-- The LIFT schema of notes/free-objects.md §1.3 says that a restriction
-- functor R : X → Y is an equivalence in the coinductive sense: every
-- object of Y is invertibly connected to the image of an object of X,
-- and the same holds for every induced functor on hom ω-categories.
--
-- Theorem `reflect`: such an R reflects invertibility. If R v is
-- invertible then v is invertible. Corollary `lift-inv`: the lift of an
-- invertible cell is invertible.
--
-- Setting. An ω-category is modelled by its tower of hom-sets (a
-- coinductive globular set) with 0-composition, identities and the two
-- whiskerings at every level; higher compositions are the
-- 0-compositions of the hom towers. Invertibility is the coinductive
-- notion of Fujii–Hoshino–Maehara (arXiv 2303.14907, Def. 3.1.1).
--
-- Hypotheses. Exactly I1, I2 and I4 of the note, as fields of records
-- that the theorem takes as arguments (nothing is postulated):
--   * `Closed`  : invertibles are closed under composition (I1) and
--                 under whiskering (I2), at every level;
--   * `FunOps`  : R preserves composition and identities up to
--                 invertible cells (I4), at every level.
-- I3 (invariance of invertibility under invertible cells) is derived
-- below from I1 and I2. I5 is not needed.
------------------------------------------------------------------------
module CaTTExp.Free.Reflect where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Towers of hom-sets.

record Glob : Set₁ where
  coinductive
  field
    Ob  : Set
    Hom : Ob → Ob → Glob
open Glob public

-- The 1-cells of G from a to b.
Cell : (G : Glob) → Ob G → Ob G → Set
Cell G a b = Ob (Hom G a b)

record Ops (G : Glob) : Set where
  coinductive
  field
    comp : ∀ {a b c} → Cell G a b → Cell G b c → Cell G a c
    idc  : ∀ a → Cell G a a
    wl   : ∀ {a b c} (f : Cell G a b) {g g' : Cell G b c} →
           Cell (Hom G b c) g g' → Cell (Hom G a c) (comp f g) (comp f g')
    wr   : ∀ {a b c} {f f' : Cell G a b} →
           Cell (Hom G a b) f f' → (g : Cell G b c) →
           Cell (Hom G a c) (comp f g) (comp f' g)
    hom  : ∀ a b → Ops (Hom G a b)
open Ops public

------------------------------------------------------------------------
-- Coinductive invertibility: an inverse, and invertible witnesses
-- f·g → id and g·f → id.

record Inv {G : Glob} (O : Ops G) {a b : Ob G} (f : Cell G a b) : Set where
  coinductive
  field
    inv        : Cell G b a
    unit       : Cell (Hom G a a) (comp O f inv) (idc O a)
    unit-inv   : Inv (hom O a a) unit
    counit     : Cell (Hom G b b) (comp O inv f) (idc O b)
    counit-inv : Inv (hom O b b) counit
open Inv public

-- I1 and I2, at every level.
record Closed {G : Glob} (O : Ops G) : Set where
  coinductive
  field
    comp-inv : ∀ {a b c} {f : Cell G a b} {g : Cell G b c} →
               Inv O f → Inv O g → Inv O (comp O f g)
    wl-inv   : ∀ {a b c} (f : Cell G a b) {g g' : Cell G b c}
               {θ : Cell (Hom G b c) g g'} →
               Inv (hom O b c) θ → Inv (hom O a c) (wl O f θ)
    wr-inv   : ∀ {a b c} {f f' : Cell G a b} {θ : Cell (Hom G a b) f f'}
               (g : Cell G b c) →
               Inv (hom O a b) θ → Inv (hom O a c) (wr O θ g)
    hom-closed : ∀ a b → Closed (hom O a b)
open Closed public

------------------------------------------------------------------------
-- Functors between towers.

record Fun (G H : Glob) : Set where
  coinductive
  field
    ob  : Ob G → Ob H
    hom : ∀ a b → Fun (Hom G a b) (Hom H (ob a) (ob b))
open Fun public

-- The action of R on 1-cells.
fmap : ∀ {G H} (R : Fun G H) {a b} → Cell G a b → Cell H (ob R a) (ob R b)
fmap R {a} {b} f = ob (hom R a b) f

-- I4: R preserves composition and identities up to invertible cells.
record FunOps {G H : Glob} (R : Fun G H) (OG : Ops G) (OH : Ops H) : Set where
  coinductive
  field
    pres-comp     : ∀ {a b c} (f : Cell G a b) (g : Cell G b c) →
                    Cell (Hom H (ob R a) (ob R c))
                         (fmap R (comp OG f g)) (comp OH (fmap R f) (fmap R g))
    pres-comp-inv : ∀ {a b c} (f : Cell G a b) (g : Cell G b c) →
                    Inv (hom OH (ob R a) (ob R c)) (pres-comp f g)
    pres-id       : ∀ a → Cell (Hom H (ob R a) (ob R a))
                               (idc OH (ob R a)) (fmap R (idc OG a))
    pres-id-inv   : ∀ a → Inv (hom OH (ob R a) (ob R a)) (pres-id a)
    hom-ops       : ∀ a b → FunOps (hom R a b) (hom OG a b) (hom OH (ob R a) (ob R b))
open FunOps public

-- The LIFT schema (free-objects.md §1.3): LIFT₀ at this level, and the
-- same schema for every induced functor on homs (LIFTₖ₊₁).
record Equiv {G H : Glob} (R : Fun G H) (OH : Ops H) : Set where
  coinductive
  field
    lift0 : (y : Ob H) → Σ (Ob G) λ x → Σ (Cell H (ob R x) y) λ θ → Inv OH θ
    homEq : ∀ a b → Equiv (hom R a b) (hom OH (ob R a) (ob R b))
open Equiv public

------------------------------------------------------------------------
-- I3, derived: if θ : c → c' is invertible and c' is invertible, then
-- c is invertible (with the same inverse as c').

conn-inv : ∀ {G} {O : Ops G} → Closed O → ∀ {a b} {c c' : Cell G a b}
           (θ : Cell (Hom G a b) c c') → Inv (hom O a b) θ → Inv O c' → Inv O c
inv        (conn-inv {O = O} C θ θi i) = inv i
unit       (conn-inv {O = O} C {a} θ θi i) =
  comp (hom O a a) (wr O θ (inv i)) (unit i)
unit-inv   (conn-inv {O = O} C {a} {b} θ θi i) =
  comp-inv (hom-closed C a a) (wr-inv C (inv i) θi) (unit-inv i)
counit     (conn-inv {O = O} C {b = b} θ θi i) =
  comp (hom O b b) (wl O (inv i) θ) (counit i)
counit-inv (conn-inv {O = O} C {a} {b} θ θi i) =
  comp-inv (hom-closed C b b) (wl-inv C (inv i) θi) (counit-inv i)

------------------------------------------------------------------------
-- One step of the proof (free-objects-proofs.md §1.3, steps 1–3): from
-- an inverse of R f, build an inverse w of f and the witnesses p, q,
-- together with the invertibility of R p and R q.

module Step {G H : Glob} {OG : Ops G} {OH : Ops H}
            (R : Fun G H) (RO : FunOps R OG OH) (E : Equiv R OH) (C : Closed OH)
            {a b : Ob G} {f : Cell G a b} (i : Inv OH (fmap R f)) where

  -- Step 1: lift the inverse of R f.
  private
    L : Σ (Cell G b a) λ w → Σ (Cell (Hom H (ob R b) (ob R a)) (fmap R w) (inv i)) λ θ →
          Inv (hom OH (ob R b) (ob R a)) θ
    L = lift0 (homEq E b a) (inv i)

  w : Cell G b a
  w = fst L

  θ : Cell (Hom H (ob R b) (ob R a)) (fmap R w) (inv i)
  θ = fst (snd L)

  θi : Inv (hom OH (ob R b) (ob R a)) θ
  θi = snd (snd L)

  -- Step 2: the invertible cell c : R(f·w) → R(id) in Y, and its dual.
  private
    Ha = Hom H (ob R a) (ob R a)
    Hb = Hom H (ob R b) (ob R b)
    Oa = hom OH (ob R a) (ob R a)
    Ob' = hom OH (ob R b) (ob R b)
    Ca = hom-closed C (ob R a) (ob R a)
    Cb = hom-closed C (ob R b) (ob R b)

  cU : Cell Ha (fmap R (comp OG f w)) (fmap R (idc OG a))
  cU = comp Oa (pres-comp RO f w)
        (comp Oa (wl OH (fmap R f) θ)
          (comp Oa (unit i) (pres-id RO a)))

  cU-inv : Inv Oa cU
  cU-inv = comp-inv Ca (pres-comp-inv RO f w)
            (comp-inv Ca (wl-inv C (fmap R f) θi)
              (comp-inv Ca (unit-inv i) (pres-id-inv RO a)))

  cC : Cell Hb (fmap R (comp OG w f)) (fmap R (idc OG b))
  cC = comp Ob' (pres-comp RO w f)
        (comp Ob' (wr OH θ (fmap R f))
          (comp Ob' (counit i) (pres-id RO b)))

  cC-inv : Inv Ob' cC
  cC-inv = comp-inv Cb (pres-comp-inv RO w f)
            (comp-inv Cb (wr-inv C (fmap R f) θi)
              (comp-inv Cb (counit-inv i) (pres-id-inv RO b)))

  -- Step 3: lift c one level up, and see that R p is invertible (I3).
  private
    LU = lift0 (homEq (homEq E a a) (comp OG f w) (idc OG a)) cU
    LC = lift0 (homEq (homEq E b b) (comp OG w f) (idc OG b)) cC

  p : Cell (Hom G a a) (comp OG f w) (idc OG a)
  p = fst LU

  Rp-inv : Inv Oa (fmap (hom R a a) p)
  Rp-inv = conn-inv Ca (fst (snd LU)) (snd (snd LU)) cU-inv

  q : Cell (Hom G b b) (comp OG w f) (idc OG b)
  q = fst LC

  Rq-inv : Inv Ob' (fmap (hom R b b) q)
  Rq-inv = conn-inv Cb (fst (snd LC)) (snd (snd LC)) cC-inv

------------------------------------------------------------------------
-- Theorem 1 (reflection), by guarded corecursion.

reflect : ∀ {G H} {OG : Ops G} {OH : Ops H}
          (R : Fun G H) → FunOps R OG OH → Equiv R OH → Closed OH →
          ∀ {a b} {f : Cell G a b} → Inv OH (fmap R f) → Inv OG f
inv        (reflect R RO E C i) = Step.w R RO E C i
unit       (reflect R RO E C i) = Step.p R RO E C i
unit-inv   (reflect R RO E C {a} i) =
  reflect (hom R a a) (hom-ops RO a a) (homEq E a a)
          (hom-closed C _ _) (Step.Rp-inv R RO E C i)
counit     (reflect R RO E C i) = Step.q R RO E C i
counit-inv (reflect R RO E C {b = b} i) =
  reflect (hom R b b) (hom-ops RO b b) (homEq E b b)
          (hom-closed C _ _) (Step.Rq-inv R RO E C i)

------------------------------------------------------------------------
-- Corollary 1: the cell produced by LIFTₖ₊₁ from an invertible cell is
-- invertible. (Corollary 2 of the note, "maps agreeing on generators up
-- to an invertible cell are invertibly related", is this statement for
-- R = restriction along η_Γ.)

lift-inv : ∀ {G H} {OG : Ops G} {OH : Ops H}
           (R : Fun G H) → FunOps R OG OH → (E : Equiv R OH) → Closed OH →
           ∀ {a b} (θ : Cell H (ob R a) (ob R b)) → Inv OH θ →
           Inv OG (fst (lift0 (homEq E a b) θ))
lift-inv R RO E C {a} {b} θ θi =
  reflect R RO E C
    (conn-inv C (fst (snd (lift0 (homEq E a b) θ)))
                (snd (snd (lift0 (homEq E a b) θ))) θi)

------------------------------------------------------------------------
-- Sanity check that the hypotheses are jointly satisfiable: the
-- terminal tower, with the identity functor, meets all of them. (This
-- only shows the records are not vacuous; the content of the theorem
-- is the general statement above.)

module Terminal where
  𝟙 : Glob
  Ob  𝟙     = ⊤
  Hom 𝟙 _ _ = 𝟙

  O𝟙 : Ops 𝟙
  comp O𝟙 _ _   = tt
  idc  O𝟙 _     = tt
  wl   O𝟙 _ _   = tt
  wr   O𝟙 _ _   = tt
  hom  O𝟙 _ _   = O𝟙

  inv𝟙 : ∀ {a b} (f : Cell 𝟙 a b) → Inv O𝟙 f
  inv        (inv𝟙 f) = tt
  unit       (inv𝟙 f) = tt
  unit-inv   (inv𝟙 f) = inv𝟙 tt
  counit     (inv𝟙 f) = tt
  counit-inv (inv𝟙 f) = inv𝟙 tt

  C𝟙 : Closed O𝟙
  comp-inv   C𝟙 _ _   = inv𝟙 tt
  wl-inv     C𝟙 _ _   = inv𝟙 tt
  wr-inv     C𝟙 _ _   = inv𝟙 tt
  hom-closed C𝟙 _ _   = C𝟙

  Id : Fun 𝟙 𝟙
  ob  Id x     = x
  hom Id _ _   = Id

  IdO : FunOps Id O𝟙 O𝟙
  pres-comp     IdO _ _ = tt
  pres-comp-inv IdO _ _ = inv𝟙 tt
  pres-id       IdO _   = tt
  pres-id-inv   IdO _   = inv𝟙 tt
  hom-ops       IdO _ _ = IdO

  IdE : Equiv Id O𝟙
  lift0 IdE y   = y , tt , inv𝟙 tt
  homEq IdE _ _ = IdE

  _ : Inv O𝟙 {tt} {tt} tt
  _ = reflect Id IdO IdE C𝟙 (inv𝟙 tt)
