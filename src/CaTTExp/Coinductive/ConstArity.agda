------------------------------------------------------------------------
-- Ledger F12b (notes/coinductive.md §2): M-types with a constant arity
-- object, from initiality.
--
-- For formulas A (labels) and E (arity), the functor X ↦ A × (E \ X)
-- has a final coalgebra M := L \ A, where L is the snoc-list object
--   L = μ(X, n : ⊤ → X, c : (X, E ▸ X)).
-- Prop S (Streams.agda) is the case with no arity input.  Only INIT
-- for L, the left and right evaluation rows and GB-shape at D⁰ are
-- used: no descent, no products, no L-×.
--
-- Coalgebras are stated in multimap form: h : (C ▸ A) and
-- t : (E, C ▸ C).  By the left row, t is the same as a map
-- C → E \ C, so (h, t) is the pair of components of C → A × (E \ C).
-- A morphism g : (C ▸ C′) has h′ ∘ g ≈ h and t′ ∘₁ g ≈ g ∘₀ t.
--
-- Orientation.  The lax hom E \ X keeps E to the left of X, so the
-- address list must be a snoc list: the label at address ℓ·e of the
-- tree rooted at c is the label at address ℓ of the subtree t(e, c).
-- Both sides of that equation are multimaps (L, E, C ▸ A), in that
-- order; with cons lists the orders would not match.  The mirror
-- statement (X / E with cons lists) is the image under the mirror
-- duality of chapter 8 §8.7 and is not encoded.
--
-- Proved (no postulates): transpose-mor, untranspose-mor, round-trip-1,
-- round-trip-2, corec-mor, corec-uni, M-final, as in Streams.agda.
--
-- Scope and honesty notes.
--   * 1-truncated, as in Streams.agda: ≈ is a relation, INIT-J2 is
--     uniqueness up to ≈, levels ≥ 2 are not encoded.
--   * INIT for L is assumed (record INITL), with its constructor given
--     as the multimap c : (X, E ▸ X).  In the kernel the constructor is
--     a map X ⊗ E → X, and the pair row identifies the two; that
--     translation is not encoded.
--   * Coalgebras are pairs (h, t); the translation to a single map into
--     A × (E \ C) (products plus the left row) is not encoded.
--   * No concrete model of INITL is constructed here.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Coinductive.ConstArity (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.FunSets 𝔐
  using (Weak; module WeakDefs; _≈⟨_⟩_; _∎; T-pc0; T-pc1; seq00; seq01)
open Model 𝔐

------------------------------------------------------------------------
-- INIT for snoc lists L = μ(X, n : ⊤ → X, c : (X, E ▸ X)), at level 1.

record INITL (𝕎 : Weak) (E : Fm) : Set where
  open Weak 𝕎
  field
    L     : Fm
    n     : V
    T-n   : n ∶ ((⊤F ∷ []) ▸ L)
    c     : V
    T-c   : c ∶ ((L ∷ E ∷ []) ▸ L)

    rec   : Fm → V → V → V
    T-rec : ∀ {Y n′ c′} → n′ ∶ ((⊤F ∷ []) ▸ Y) → c′ ∶ ((Y ∷ E ∷ []) ▸ Y) →
            rec Y n′ c′ ∶ ((L ∷ []) ▸ Y)
    rec-n : ∀ {Y n′ c′} → n′ ∶ ((⊤F ∷ []) ▸ Y) → c′ ∶ ((Y ∷ E ∷ []) ▸ Y) →
            pc (rec Y n′ c′) 0 n ≈ n′
    rec-c : ∀ {Y n′ c′} → n′ ∶ ((⊤F ∷ []) ▸ Y) → c′ ∶ ((Y ∷ E ∷ []) ▸ Y) →
            pc (rec Y n′ c′) 0 c ≈ pc c′ 0 (rec Y n′ c′)

    uni   : ∀ {Y n′ c′ f} → n′ ∶ ((⊤F ∷ []) ▸ Y) → c′ ∶ ((Y ∷ E ∷ []) ▸ Y) →
            f ∶ ((L ∷ []) ▸ Y) →
            pc f 0 n ≈ n′ → pc f 0 c ≈ pc c′ 0 f → f ≈ rec Y n′ c′

------------------------------------------------------------------------
-- Coalgebras of A × (E \ –), in multimap form.

record Coalg (A E : Fm) : Set where
  field
    C   : Fm
    h   : V
    T-h : h ∶ ((C ∷ []) ▸ A)
    t   : V
    T-t : t ∶ ((E ∷ C ∷ []) ▸ C)

record IsCoalgMor {A E : Fm} (K K′ : Coalg A E) (g : V) : Set where
  private
    module K  = Coalg K
    module K′ = Coalg K′
  field
    T-g   : g ∶ ((K.C ∷ []) ▸ K′.C)
    mor-h : pc K′.h 0 g ≈ K.h
    mor-t : pc K′.t 1 g ≈ pc g 0 K.t

------------------------------------------------------------------------

module FinalM (𝕎 : Weak) (A E : Fm) (I : INITL 𝕎 E) where
  open Weak 𝕎
  open WeakDefs 𝕎
  open INITL I

  M : Fm
  M = L \\ A

  ev : V
  ev = evL L A

  T-ev : ev ∶ ((L ∷ M ∷ []) ▸ A)
  T-ev = T-evL L A

  n̄ : V
  n̄ = ρ 0 n

  T-n̄ : n̄ ∶ ([] ▸ L)
  T-n̄ = T-pc0 (T-pc0 T-n T-ι) (T-cor cpt)

  head : V
  head = pc ev 0 n̄

  T-head : head ∶ ((M ∷ []) ▸ A)
  T-head = T-pc0 T-ev T-n̄

  -- tail(e, m) is the subtree at e: its label at ℓ is m's label at ℓ·e
  tail : V
  tail = curL L A (pc ev 0 c)

  T-tail : tail ∶ ((E ∷ M ∷ []) ▸ M)
  T-tail = T-curL (T-pc0 T-ev T-c)

  MC : Coalg A E
  MC = record { C = M ; h = head ; T-h = T-head ; t = tail ; T-t = T-tail }

  evL-inj : ∀ {x y Φ} → x ∶ (Φ ▸ M) → y ∶ (Φ ▸ M) →
            pc ev 1 x ≈ pc ev 1 y → x ≈ y
  evL-inj px py e =
    ≈-trans (≈-sym (curL-l px)) (≈-trans (curL-cong L A e) (curL-l py))

  module _ (K : Coalg A E) where
    open Coalg K

    P : Fm
    P = A // C

    evr : V
    evr = evR C A

    T-evr : evr ∶ ((P ∷ C ∷ []) ▸ A)
    T-evr = T-evR C A

    evR-inj : ∀ {x y Φ} → x ∶ (Φ ▸ P) → y ∶ (Φ ▸ P) →
              pc evr 0 x ≈ pc evr 0 y → x ≈ y
    evR-inj px py e =
      ≈-trans (≈-sym (curR-l px)) (≈-trans (curR-cong C A e) (curR-l py))

    -- the model (A / C, n′, c′) of the list context
    h̄ : V
    h̄ = curR C A h

    T-h̄ : h̄ ∶ ([] ▸ P)
    T-h̄ = T-curR {Φ = []} T-h

    n′ : V
    n′ = wk 0 h̄

    T-n′ : n′ ∶ ((⊤F ∷ []) ▸ P)
    T-n′ = T-wk {P = []} {Q = []} T-h̄

    c′ : V
    c′ = curR C A (pc evr 1 t)

    T-c′ : c′ ∶ ((P ∷ E ∷ []) ▸ P)
    T-c′ = T-curR {Φ = P ∷ E ∷ []} (T-pc1 T-evr T-t)

    IsModelMor : V → Set
    IsModelMor f = (f ∶ ((L ∷ []) ▸ P)) × (pc f 0 n ≈ n′) × (pc f 0 c ≈ pc c′ 0 f)

    up : V → V
    up g = curR C A (pc ev 1 g)

    down : V → V
    down f = curL L A (pc evr 0 f)

    T-up : ∀ {g} → g ∶ ((C ∷ []) ▸ M) → up g ∶ ((L ∷ []) ▸ P)
    T-up pg = T-curR {Φ = L ∷ []} (T-pc1 T-ev pg)

    T-down : ∀ {f} → f ∶ ((L ∷ []) ▸ P) → down f ∶ ((C ∷ []) ▸ M)
    T-down pf = T-curL (T-pc0 T-evr pf)

    round-trip-1 : ∀ {g} → g ∶ ((C ∷ []) ▸ M) → down (up g) ≈ g
    round-trip-1 pg =
      evL-inj (T-down (T-up pg)) pg
        (≈-trans (curL-r (T-pc0 T-evr (T-up pg)))
                 (curR-r {Φ = L ∷ []} (T-pc1 T-ev pg)))

    round-trip-2 : ∀ {f} → f ∶ ((L ∷ []) ▸ P) → up (down f) ≈ f
    round-trip-2 pf =
      evR-inj (T-up (T-down pf)) pf
        (≈-trans (curR-r {Φ = L ∷ []} (T-pc1 T-ev (T-down pf)))
                 (curL-r (T-pc0 T-evr pf)))

    ------------------------------------------------------------------
    -- The conditions through the transposes, with k : (L, C ▸ A):
    --   head ∘ g ≈ h          ⟺  k ∘₀ n̄ ≈ h        ⟺  f ∘ n ≈ n′
    --   tail ∘₁ g ≈ g ∘₀ t    ⟺  k ∘₀ c ≈ k ∘₁ t    ⟺  f ∘₀ c ≈ c′ ∘₀ f

    head-g : ∀ {g} → g ∶ ((C ∷ []) ▸ M) →
             pc head 0 g ≈ pc (pc ev 1 g) 0 n̄
    head-g pg = par {P = []} {M = []} T-ev T-n̄ pg

    -- e^ℓ ∘₁ (tail ∘₁ g)  ≈  (e^ℓ ∘₁ g) ∘₀ c       : (L, E, C ▸ A)
    tail-g : ∀ {g} → g ∶ ((C ∷ []) ▸ M) →
             pc ev 1 (pc tail 1 g) ≈ pc (pc ev 1 g) 0 c
    tail-g {g} pg =
      pc ev 1 (pc tail 1 g)
        ≈⟨ ≈-sym (seq {P = L ∷ []} {P′ = E ∷ []} T-ev T-tail pg) ⟩
      pc (pc ev 1 tail) 2 g
        ≈⟨ pc-cong 2 (curL-r (T-pc0 T-ev T-c)) ≈-refl ⟩
      pc (pc ev 0 c) 2 g
        ≈⟨ par {P = []} {M = []} T-ev T-c pg ⟩
      pc (pc ev 1 g) 0 c ∎

    -- e^ℓ ∘₁ (g ∘₀ t)  ≈  (e^ℓ ∘₁ g) ∘₁ t           : (L, E, C ▸ A)
    gt : ∀ {g} → g ∶ ((C ∷ []) ▸ M) →
         pc ev 1 (pc g 0 t) ≈ pc (pc ev 1 g) 1 t
    gt pg = ≈-sym (seq {P = L ∷ []} {P′ = []} T-ev pg T-t)

    -- e^r ∘₀ (f ∘₀ c)  ≈  (e^r ∘₀ f) ∘₀ c           : (L, E, C ▸ A)
    fc : ∀ {f} → f ∶ ((L ∷ []) ▸ P) →
         pc evr 0 (pc f 0 c) ≈ pc (pc evr 0 f) 0 c
    fc pf = ≈-sym (seq00 T-evr pf T-c)

    -- e^r ∘₀ (c′ ∘₀ f)  ≈  (e^r ∘₀ f) ∘₁ t          : (L, E, C ▸ A)
    c′f : ∀ {f} → f ∶ ((L ∷ []) ▸ P) →
          pc evr 0 (pc c′ 0 f) ≈ pc (pc evr 0 f) 1 t
    c′f {f} pf =
      pc evr 0 (pc c′ 0 f)
        ≈⟨ ≈-sym (seq00 T-evr T-c′ pf) ⟩
      pc (pc evr 0 c′) 0 f
        ≈⟨ pc-cong 0 (curR-r {Φ = P ∷ E ∷ []} (T-pc1 T-evr T-t)) ≈-refl ⟩
      pc (pc evr 1 t) 0 f
        ≈⟨ ≈-sym (par {P = []} {M = []} T-evr pf T-t) ⟩
      pc (pc evr 0 f) 1 t ∎

    ρfn : ∀ {f} → f ∶ ((L ∷ []) ▸ P) → ρ 0 (pc f 0 n) ≈ pc f 0 n̄
    ρfn {f} pf =
      pc (pc (pc f 0 n) 0 ι) 0 (cor cpt)
        ≈⟨ pc-cong 0 (seq00 pf T-n T-ι) ≈-refl ⟩
      pc (pc f 0 (pc n 0 ι)) 0 (cor cpt)
        ≈⟨ seq00 pf (T-pc0 T-n T-ι) (T-cor cpt) ⟩
      pc f 0 n̄ ∎

    fn̄ : ∀ {f} → f ∶ ((L ∷ []) ▸ P) →
         pc evr 0 (pc f 0 n̄) ≈ pc (pc evr 0 f) 0 n̄
    fn̄ pf = ≈-sym (seq00 T-evr pf T-n̄)

    n-cond : ∀ {f} → f ∶ ((L ∷ []) ▸ P) →
             pc (pc evr 0 f) 0 n̄ ≈ h → pc f 0 n ≈ n′
    n-cond {f} pf e =
      ρ-inj {P = []} (T-pc0 pf T-n) T-n′
        (ρ 0 (pc f 0 n)
           ≈⟨ ρfn pf ⟩
         pc f 0 n̄
           ≈⟨ evR-inj (T-pc0 pf T-n̄) T-h̄
                (≈-trans (fn̄ pf) (≈-trans e (≈-sym (curR-r {Φ = []} T-h)))) ⟩
         h̄
           ≈⟨ ≈-sym (ρ-wk {P = []} {Q = []} T-h̄) ⟩
         ρ 0 n′ ∎)

    n-cond⁻ : ∀ {f} → f ∶ ((L ∷ []) ▸ P) →
              pc f 0 n ≈ n′ → pc (pc evr 0 f) 0 n̄ ≈ h
    n-cond⁻ {f} pf e =
      pc (pc evr 0 f) 0 n̄
        ≈⟨ ≈-sym (fn̄ pf) ⟩
      pc evr 0 (pc f 0 n̄)
        ≈⟨ pc-cong 0 ≈-refl
             (≈-trans (≈-sym (ρfn pf))
               (≈-trans (pc-cong 0 (pc-cong 0 e ≈-refl) ≈-refl)
                        (ρ-wk {P = []} {Q = []} T-h̄))) ⟩
      pc evr 0 h̄
        ≈⟨ curR-r {Φ = []} T-h ⟩
      h ∎

    transpose-mor : ∀ {g} → IsCoalgMor K MC g → IsModelMor (up g)
    transpose-mor {g} m = T-up pg , nc , cc
      where
        open IsCoalgMor m renaming (T-g to pg)
        k≈ : pc evr 0 (up g) ≈ pc ev 1 g
        k≈ = curR-r {Φ = L ∷ []} (T-pc1 T-ev pg)
        nc : pc (up g) 0 n ≈ n′
        nc = n-cond (T-up pg)
               (≈-trans (pc-cong 0 k≈ ≈-refl)
                 (≈-trans (≈-sym (head-g pg)) mor-h))
        cc : pc (up g) 0 c ≈ pc c′ 0 (up g)
        cc = evR-inj (T-pc0 (T-up pg) T-c) (T-pc0 T-c′ (T-up pg))
               (pc evr 0 (pc (up g) 0 c)
                  ≈⟨ fc (T-up pg) ⟩
                pc (pc evr 0 (up g)) 0 c
                  ≈⟨ pc-cong 0 k≈ ≈-refl ⟩
                pc (pc ev 1 g) 0 c
                  ≈⟨ ≈-sym (tail-g pg) ⟩
                pc ev 1 (pc tail 1 g)
                  ≈⟨ pc-cong 1 ≈-refl mor-t ⟩
                pc ev 1 (pc g 0 t)
                  ≈⟨ gt pg ⟩
                pc (pc ev 1 g) 1 t
                  ≈⟨ pc-cong 1 (≈-sym k≈) ≈-refl ⟩
                pc (pc evr 0 (up g)) 1 t
                  ≈⟨ ≈-sym (c′f (T-up pg)) ⟩
                pc evr 0 (pc c′ 0 (up g)) ∎)

    untranspose-mor : ∀ {f} → IsModelMor f → IsCoalgMor K MC (down f)
    untranspose-mor {f} (pf , nc , cc) = record
      { T-g   = T-down pf
      ; mor-h = mh
      ; mor-t = mt
      }
      where
        k≈ : pc ev 1 (down f) ≈ pc evr 0 f
        k≈ = curL-r (T-pc0 T-evr pf)
        mh : pc head 0 (down f) ≈ h
        mh = ≈-trans (head-g (T-down pf))
               (≈-trans (pc-cong 0 k≈ ≈-refl) (n-cond⁻ pf nc))
        mt : pc tail 1 (down f) ≈ pc (down f) 0 t
        mt = evL-inj (T-pc1 T-tail (T-down pf)) (T-pc0 (T-down pf) T-t)
               (pc ev 1 (pc tail 1 (down f))
                  ≈⟨ tail-g (T-down pf) ⟩
                pc (pc ev 1 (down f)) 0 c
                  ≈⟨ pc-cong 0 k≈ ≈-refl ⟩
                pc (pc evr 0 f) 0 c
                  ≈⟨ ≈-sym (fc pf) ⟩
                pc evr 0 (pc f 0 c)
                  ≈⟨ pc-cong 0 ≈-refl cc ⟩
                pc evr 0 (pc c′ 0 f)
                  ≈⟨ c′f pf ⟩
                pc (pc evr 0 f) 1 t
                  ≈⟨ pc-cong 1 (≈-sym k≈) ≈-refl ⟩
                pc (pc ev 1 (down f)) 1 t
                  ≈⟨ ≈-sym (gt (T-down pf)) ⟩
                pc ev 1 (pc (down f) 0 t) ∎)

    corec : V
    corec = down (rec P n′ c′)

    corec-mor : IsCoalgMor K MC corec
    corec-mor = untranspose-mor
      (T-rec T-n′ T-c′ , rec-n T-n′ T-c′ , rec-c T-n′ T-c′)

    corec-uni : ∀ {g} → IsCoalgMor K MC g → g ≈ corec
    corec-uni {g} m =
      g
        ≈⟨ ≈-sym (round-trip-1 pg) ⟩
      down (up g)
        ≈⟨ curL-cong L A (pc-cong 0 ≈-refl
             (uni T-n′ T-c′ (fst mm) (fst (snd mm)) (snd (snd mm)))) ⟩
      corec ∎
      where
        pg = IsCoalgMor.T-g m
        mm = transpose-mor m

  record Final (T : Coalg A E) : Set where
    field
      !     : Coalg A E → V
      !-mor : ∀ K → IsCoalgMor K T (! K)
      !-uni : ∀ K {g} → IsCoalgMor K T g → g ≈ ! K

  M-final : Final MC
  M-final = record { ! = corec ; !-mor = corec-mor ; !-uni = corec-uni }
