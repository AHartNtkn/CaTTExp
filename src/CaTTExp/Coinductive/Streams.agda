------------------------------------------------------------------------
-- Ledger F12b, Prop S (notes/descent-vs-init.md §5,
-- notes/coinductive.md §1).
--
-- Streams from initiality: for every formula B, Str := ℕ \ B with
--   head := e^ℓ ∘₀ z̄    (evaluation at the point zero),
--   tail := curL (e^ℓ ∘₀ s)  (precomposition with succ)
-- is a final coalgebra of X ↦ B × X, using only INIT for ℕ, the left
-- and right evaluation rows of chapter 8 and GB-shape at D⁰
-- (weakening, to turn INIT's element z : ⊤ → ℕ into a point).  No
-- descent, no products, no ⊗ and no L-× are used.
--
-- Setting.  The abstract model interface of the biclosed kernel
-- (Gray/Biclosed/Model.agda: a planar multicategory of formulas with
-- invertible left and right evaluation rows), plus the weakening row
-- and ⊤ of Gray/Biclosed/FunSets.agda (`Weak`).  On top we assume an
-- object N with INIT for the context (X, z : ⊤ → X, s : X → X), stated
-- as the record `INITℕ` below: for every formula Y and every model
-- (z′ : (⊤ ▸ Y), s′ : (Y ▸ Y)), a model morphism rec, unique up to ≈.
-- That is INIT-form, INIT-J1 and INIT-J2 at level 1; INIT is assumed,
-- not constructed (as in HIT/DependentElim.agda).
--
-- A coalgebra of B × – is a formula C with h : (C ▸ B) and t : (C ▸ C)
-- (the two components of C → B × C; see the scope notes).  A coalgebra
-- morphism g : (C ▸ C′) has h′ ∘ g ≈ h and t′ ∘ g ≈ g ∘ t.
--
-- Proved (no postulates):
--   transpose-mor   coalgebra morphisms C → Str are sent by
--                   g ↦ curR (e^ℓ ∘₁ g) to model morphisms
--                   ℕ → (B / C, wk(curR h), t^*) ...
--   untranspose-mor ... and back by f ↦ curL (e^r ∘₀ f);
--   round-trip-1/2  the two assignments are mutually inverse up to ≈;
--   corec-mor       corec C := curL (e^r ∘₀ rec) is a coalgebra
--                   morphism C → Str (existence);
--   corec-uni       every coalgebra morphism C → Str is ≈ corec C
--                   (uniqueness);
--   Str-final       the two packaged as finality.
--
-- Scope and honesty notes.
--   * Parameter-free: coalgebras and models are closed formulas with
--     closed operations (no ambient context Γ).  INIT is assumed only
--     for such models, a special case of §9.3's INIT-J1/J2.
--   * 1-truncated: ≈ stands for an invertible cell and is a relation,
--     so INIT-J2 is "unique up to ≈" and the cells of a strong morphism
--     are propositions.  The bijection transpose-mor / untranspose-mor
--     is the level-1 shadow of the hom-space equivalence that gives
--     finality at all levels in the system (via GB-cut at every n);
--     levels ≥ 2 are not encoded.
--   * Coalgebras are given as pairs (h, t), not as one map into B × C.
--     With binary products (FunSets' ×F) the two are equivalent by the
--     universal property of ×; that translation is not encoded here.
--   * The model interface and INITℕ are abstract records; no concrete
--     model satisfying INITℕ is constructed in this file.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Coinductive.Streams (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.FunSets 𝔐
  using (Weak; module WeakDefs; _≈⟨_⟩_; _∎; T-pc0; T-pc1; seq00; seq01)
open Model 𝔐

------------------------------------------------------------------------
-- INIT for ℕ = μ(X, z : ⊤ → X, s : X → X), at level 1.

record INITℕ (𝕎 : Weak) : Set where
  open Weak 𝕎
  field
    N     : Fm
    z     : V
    T-z   : z ∶ ((⊤F ∷ []) ▸ N)
    s     : V
    T-s   : s ∶ ((N ∷ []) ▸ N)

    -- INIT-J1: a model morphism into every model
    rec   : Fm → V → V → V
    T-rec : ∀ {Y z′ s′} → z′ ∶ ((⊤F ∷ []) ▸ Y) → s′ ∶ ((Y ∷ []) ▸ Y) →
            rec Y z′ s′ ∶ ((N ∷ []) ▸ Y)
    rec-z : ∀ {Y z′ s′} → z′ ∶ ((⊤F ∷ []) ▸ Y) → s′ ∶ ((Y ∷ []) ▸ Y) →
            pc (rec Y z′ s′) 0 z ≈ z′
    rec-s : ∀ {Y z′ s′} → z′ ∶ ((⊤F ∷ []) ▸ Y) → s′ ∶ ((Y ∷ []) ▸ Y) →
            pc (rec Y z′ s′) 0 s ≈ pc s′ 0 (rec Y z′ s′)

    -- INIT-J2: every model morphism is ≈ rec
    uni   : ∀ {Y z′ s′ f} → z′ ∶ ((⊤F ∷ []) ▸ Y) → s′ ∶ ((Y ∷ []) ▸ Y) →
            f ∶ ((N ∷ []) ▸ Y) →
            pc f 0 z ≈ z′ → pc f 0 s ≈ pc s′ 0 f → f ≈ rec Y z′ s′

------------------------------------------------------------------------
-- Coalgebras of B × –.

record Coalg (B : Fm) : Set where
  field
    C   : Fm
    h   : V
    T-h : h ∶ ((C ∷ []) ▸ B)
    t   : V
    T-t : t ∶ ((C ∷ []) ▸ C)

record IsCoalgMor {B : Fm} (K K′ : Coalg B) (g : V) : Set where
  private
    module K  = Coalg K
    module K′ = Coalg K′
  field
    T-g   : g ∶ ((K.C ∷ []) ▸ K′.C)
    mor-h : pc K′.h 0 g ≈ K.h
    mor-t : pc K′.t 0 g ≈ pc g 0 K.t

------------------------------------------------------------------------
-- Prop S.

module PropS (𝕎 : Weak) (I : INITℕ 𝕎) (B : Fm) where
  open Weak 𝕎
  open WeakDefs 𝕎
  open INITℕ I

  Str : Fm
  Str = N \\ B

  ev : V
  ev = evL N B

  T-ev : ev ∶ ((N ∷ Str ∷ []) ▸ B)
  T-ev = T-evL N B

  -- the point zero ( ▸ N), by GB-shape at D⁰
  z̄ : V
  z̄ = ρ 0 z

  T-z̄ : z̄ ∶ ([] ▸ N)
  T-z̄ = T-pc0 (T-pc0 T-z T-ι) (T-cor cpt)

  head : V
  head = pc ev 0 z̄

  T-head : head ∶ ((Str ∷ []) ▸ B)
  T-head = T-pc0 T-ev T-z̄

  tail : V
  tail = curL N B (pc ev 0 s)

  T-tail : tail ∶ ((Str ∷ []) ▸ Str)
  T-tail = T-curL (T-pc0 T-ev T-s)

  StrC : Coalg B
  StrC = record { C = Str ; h = head ; T-h = T-head ; t = tail ; T-t = T-tail }

  -- injectivity of the two rows up to ≈
  evL-inj : ∀ {x y Φ} → x ∶ (Φ ▸ Str) → y ∶ (Φ ▸ Str) →
            pc ev 1 x ≈ pc ev 1 y → x ≈ y
  evL-inj px py e =
    ≈-trans (≈-sym (curL-l px)) (≈-trans (curL-cong N B e) (curL-l py))

  ----------------------------------------------------------------------
  -- Fix a coalgebra (C, h, t).

  module _ (K : Coalg B) where
    open Coalg K

    P : Fm
    P = B // C

    evr : V
    evr = evR C B

    T-evr : evr ∶ ((P ∷ C ∷ []) ▸ B)
    T-evr = T-evR C B

    evR-inj : ∀ {x y Φ} → x ∶ (Φ ▸ P) → y ∶ (Φ ▸ P) →
              pc evr 0 x ≈ pc evr 0 y → x ≈ y
    evR-inj px py e =
      ≈-trans (≈-sym (curR-l px)) (≈-trans (curR-cong C B e) (curR-l py))

    -- the model (B / C, z′, t*) of (X, z : ⊤ → X, s : X → X)
    h̄ : V
    h̄ = curR C B h

    T-h̄ : h̄ ∶ ([] ▸ P)
    T-h̄ = T-curR {Φ = []} T-h

    z′ : V
    z′ = wk 0 h̄

    T-z′ : z′ ∶ ((⊤F ∷ []) ▸ P)
    T-z′ = T-wk {P = []} {Q = []} T-h̄

    t* : V
    t* = curR C B (pc evr 1 t)

    T-t* : t* ∶ ((P ∷ []) ▸ P)
    T-t* = T-curR {Φ = P ∷ []} (T-pc1 T-evr T-t)

    IsModelMor : V → Set
    IsModelMor f = (f ∶ ((N ∷ []) ▸ P)) × (pc f 0 z ≈ z′) × (pc f 0 s ≈ pc t* 0 f)

    -- the two transposes
    up : V → V
    up g = curR C B (pc ev 1 g)

    down : V → V
    down f = curL N B (pc evr 0 f)

    T-up : ∀ {g} → g ∶ ((C ∷ []) ▸ Str) → up g ∶ ((N ∷ []) ▸ P)
    T-up pg = T-curR {Φ = N ∷ []} (T-pc1 T-ev pg)

    T-down : ∀ {f} → f ∶ ((N ∷ []) ▸ P) → down f ∶ ((C ∷ []) ▸ Str)
    T-down pf = T-curL (T-pc0 T-evr pf)

    round-trip-1 : ∀ {g} → g ∶ ((C ∷ []) ▸ Str) → down (up g) ≈ g
    round-trip-1 pg =
      evL-inj (T-down (T-up pg)) pg
        (≈-trans (curL-r (T-pc0 T-evr (T-up pg))) (curR-r {Φ = N ∷ []} (T-pc1 T-ev pg)))

    round-trip-2 : ∀ {f} → f ∶ ((N ∷ []) ▸ P) → up (down f) ≈ f
    round-trip-2 pf =
      evR-inj (T-up (T-down pf)) pf
        (≈-trans (curR-r {Φ = N ∷ []} (T-pc1 T-ev (T-down pf))) (curL-r (T-pc0 T-evr pf)))

    ------------------------------------------------------------------
    -- The two conditions, read through the transposes.
    -- For k : (N, C ▸ B) with k ≈ e^ℓ ∘₁ g ≈ e^r ∘₀ f:
    --   head ∘ g ≈ h            ⟺  k ∘₀ z̄ ≈ h          ⟺  f ∘ z ≈ z′
    --   tail ∘ g ≈ g ∘ t        ⟺  k ∘₀ s ≈ k ∘₁ t      ⟺  f ∘ s ≈ t* ∘ f

    -- (a) head ∘ g  ≈  (e^ℓ ∘₁ g) ∘₀ z̄
    head-g : ∀ {g} → g ∶ ((C ∷ []) ▸ Str) →
             pc head 0 g ≈ pc (pc ev 1 g) 0 z̄
    head-g pg = par {P = []} {M = []} T-ev T-z̄ pg

    -- (b) e^ℓ ∘₁ (tail ∘ g)  ≈  (e^ℓ ∘₁ g) ∘₀ s
    tail-g : ∀ {g} → g ∶ ((C ∷ []) ▸ Str) →
             pc ev 1 (pc tail 0 g) ≈ pc (pc ev 1 g) 0 s
    tail-g {g} pg =
      pc ev 1 (pc tail 0 g)
        ≈⟨ ≈-sym (seq {P = N ∷ []} {P′ = []} T-ev T-tail pg) ⟩
      pc (pc ev 1 tail) 1 _
        ≈⟨ pc-cong 1 (curL-r (T-pc0 T-ev T-s)) ≈-refl ⟩
      pc (pc ev 0 s) 1 _
        ≈⟨ par {P = []} {M = []} T-ev T-s pg ⟩
      pc (pc ev 1 _) 0 s ∎

    -- (c) e^ℓ ∘₁ (g ∘ t)  ≈  (e^ℓ ∘₁ g) ∘₁ t
    gt : ∀ {g} → g ∶ ((C ∷ []) ▸ Str) →
         pc ev 1 (pc g 0 t) ≈ pc (pc ev 1 g) 1 t
    gt pg = ≈-sym (seq {P = N ∷ []} {P′ = []} T-ev pg T-t)

    -- (d) e^r ∘₀ (f ∘ s)  ≈  (e^r ∘₀ f) ∘₀ s
    fs : ∀ {f} → f ∶ ((N ∷ []) ▸ P) →
         pc evr 0 (pc f 0 s) ≈ pc (pc evr 0 f) 0 s
    fs pf = ≈-sym (seq00 T-evr pf T-s)

    -- (e) e^r ∘₀ (t* ∘ f)  ≈  (e^r ∘₀ f) ∘₁ t
    t*f : ∀ {f} → f ∶ ((N ∷ []) ▸ P) →
          pc evr 0 (pc t* 0 f) ≈ pc (pc evr 0 f) 1 t
    t*f pf =
      pc evr 0 (pc t* 0 _)
        ≈⟨ ≈-sym (seq00 T-evr T-t* pf) ⟩
      pc (pc evr 0 t*) 0 _
        ≈⟨ pc-cong 0 (curR-r {Φ = P ∷ []} (T-pc1 T-evr T-t)) ≈-refl ⟩
      pc (pc evr 1 t) 0 _
        ≈⟨ ≈-sym (par {P = []} {M = []} T-evr pf T-t) ⟩
      pc (pc evr 0 _) 1 t ∎

    -- (f) the point of f ∘ z is f ∘₀ z̄, and it is the transpose of
    --     (e^r ∘₀ f) ∘₀ z̄
    ρfz : ∀ {f} → f ∶ ((N ∷ []) ▸ P) → ρ 0 (pc f 0 z) ≈ pc f 0 z̄
    ρfz pf =
      pc (pc (pc _ 0 z) 0 ι) 0 (cor cpt)
        ≈⟨ pc-cong 0 (seq00 pf T-z T-ι) ≈-refl ⟩
      pc (pc _ 0 (pc z 0 ι)) 0 (cor cpt)
        ≈⟨ seq00 pf (T-pc0 T-z T-ι) (T-cor cpt) ⟩
      pc _ 0 z̄ ∎

    fz̄ : ∀ {f} → f ∶ ((N ∷ []) ▸ P) →
         pc evr 0 (pc f 0 z̄) ≈ pc (pc evr 0 f) 0 z̄
    fz̄ pf = ≈-sym (seq00 T-evr pf T-z̄)

    -- condition on z, in terms of k := e^r ∘₀ f
    z-cond : ∀ {f} → f ∶ ((N ∷ []) ▸ P) →
             pc (pc evr 0 f) 0 z̄ ≈ h → pc f 0 z ≈ z′
    z-cond pf e =
      ρ-inj {P = []} (T-pc0 pf T-z) T-z′
        (ρ 0 (pc _ 0 z)
           ≈⟨ ρfz pf ⟩
         pc _ 0 z̄
           ≈⟨ evR-inj (T-pc0 pf T-z̄) T-h̄
                (≈-trans (fz̄ pf) (≈-trans e (≈-sym (curR-r {Φ = []} T-h)))) ⟩
         h̄
           ≈⟨ ≈-sym (ρ-wk {P = []} {Q = []} T-h̄) ⟩
         ρ 0 z′ ∎)

    z-cond⁻ : ∀ {f} → f ∶ ((N ∷ []) ▸ P) →
              pc f 0 z ≈ z′ → pc (pc evr 0 f) 0 z̄ ≈ h
    z-cond⁻ pf e =
      pc (pc evr 0 _) 0 z̄
        ≈⟨ ≈-sym (fz̄ pf) ⟩
      pc evr 0 (pc _ 0 z̄)
        ≈⟨ pc-cong 0 ≈-refl
             (≈-trans (≈-sym (ρfz pf))
               (≈-trans (pc-cong 0 (pc-cong 0 e ≈-refl) ≈-refl)
                        (ρ-wk {P = []} {Q = []} T-h̄))) ⟩
      pc evr 0 h̄
        ≈⟨ curR-r {Φ = []} T-h ⟩
      h ∎

    ------------------------------------------------------------------
    -- Coalgebra morphisms into Str  ↔  model morphisms ℕ → B / C.

    transpose-mor : ∀ {g} → IsCoalgMor K StrC g → IsModelMor (up g)
    transpose-mor {g} m = T-up pg , zc , sc
      where
        open IsCoalgMor m renaming (T-g to pg)
        k≈ : pc evr 0 (up g) ≈ pc ev 1 g
        k≈ = curR-r {Φ = N ∷ []} (T-pc1 T-ev pg)
        zc : pc (up g) 0 z ≈ z′
        zc = z-cond (T-up pg)
               (≈-trans (pc-cong 0 k≈ ≈-refl)
                 (≈-trans (≈-sym (head-g pg)) mor-h))
        sc : pc (up g) 0 s ≈ pc t* 0 (up g)
        sc = evR-inj (T-pc0 (T-up pg) T-s) (T-pc0 T-t* (T-up pg))
               (pc evr 0 (pc (up g) 0 s)
                  ≈⟨ fs (T-up pg) ⟩
                pc (pc evr 0 (up g)) 0 s
                  ≈⟨ pc-cong 0 k≈ ≈-refl ⟩
                pc (pc ev 1 g) 0 s
                  ≈⟨ ≈-sym (tail-g pg) ⟩
                pc ev 1 (pc tail 0 g)
                  ≈⟨ pc-cong 1 ≈-refl mor-t ⟩
                pc ev 1 (pc g 0 t)
                  ≈⟨ gt pg ⟩
                pc (pc ev 1 g) 1 t
                  ≈⟨ pc-cong 1 (≈-sym k≈) ≈-refl ⟩
                pc (pc evr 0 (up g)) 1 t
                  ≈⟨ ≈-sym (t*f (T-up pg)) ⟩
                pc evr 0 (pc t* 0 (up g)) ∎)

    untranspose-mor : ∀ {f} → IsModelMor f → IsCoalgMor K StrC (down f)
    untranspose-mor {f} (pf , zc , sc) = record
      { T-g   = T-down pf
      ; mor-h = mh
      ; mor-t = mt
      }
      where
        k≈ : pc ev 1 (down f) ≈ pc evr 0 f
        k≈ = curL-r (T-pc0 T-evr pf)
        mh : pc head 0 (down f) ≈ h
        mh = ≈-trans (head-g (T-down pf))
               (≈-trans (pc-cong 0 k≈ ≈-refl) (z-cond⁻ pf zc))
        mt : pc tail 0 (down f) ≈ pc (down f) 0 t
        mt = evL-inj (T-pc0 T-tail (T-down pf)) (T-pc0 (T-down pf) T-t)
               (pc ev 1 (pc tail 0 (down f))
                  ≈⟨ tail-g (T-down pf) ⟩
                pc (pc ev 1 (down f)) 0 s
                  ≈⟨ pc-cong 0 k≈ ≈-refl ⟩
                pc (pc evr 0 f) 0 s
                  ≈⟨ ≈-sym (fs pf) ⟩
                pc evr 0 (pc f 0 s)
                  ≈⟨ pc-cong 0 ≈-refl sc ⟩
                pc evr 0 (pc t* 0 f)
                  ≈⟨ t*f pf ⟩
                pc (pc evr 0 f) 1 t
                  ≈⟨ pc-cong 1 (≈-sym k≈) ≈-refl ⟩
                pc (pc ev 1 (down f)) 1 t
                  ≈⟨ ≈-sym (gt (T-down pf)) ⟩
                pc ev 1 (pc (down f) 0 t) ∎)

    ------------------------------------------------------------------
    -- Finality.

    corec : V
    corec = down (rec P z′ t*)

    corec-mor : IsCoalgMor K StrC corec
    corec-mor = untranspose-mor
      (T-rec T-z′ T-t* , rec-z T-z′ T-t* , rec-s T-z′ T-t*)

    corec-uni : ∀ {g} → IsCoalgMor K StrC g → g ≈ corec
    corec-uni {g} m =
      g
        ≈⟨ ≈-sym (round-trip-1 pg) ⟩
      down (up g)
        ≈⟨ curL-cong N B (pc-cong 0 ≈-refl
             (uni T-z′ T-t* (fst mm) (fst (snd mm)) (snd (snd mm)))) ⟩
      corec ∎
      where
        pg = IsCoalgMor.T-g m
        mm = transpose-mor m

  -- Str is a final coalgebra: a morphism from every coalgebra, and any
  -- two morphisms with the same source are ≈.
  record Final (T : Coalg B) : Set where
    field
      !     : Coalg B → V
      !-mor : ∀ K → IsCoalgMor K T (! K)
      !-uni : ∀ K {g} → IsCoalgMor K T g → g ≈ ! K

  Str-final : Final StrC
  Str-final = record { ! = corec ; !-mor = corec-mor ; !-uni = corec-uni }
