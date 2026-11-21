------------------------------------------------------------------------
-- F8d: function sets from the biclosed rules
-- (notes/ordinary-math.md §6.5.2, ledger F8, F8a, F8b, F8d).
--
-- Over the abstract model interface of Model.agda we add
--   * a terminal formula ⊤F with  bang X : (X ▸ ⊤F)  unique up to ≈;
--   * binary products _×F_ with projections and pairing, and their
--     universal property against multimaps (X₁, …, Xₙ ▸ A ×F B), n ≥ 1.
--     (In the kernel this is ×'s `uni` at the apex X₁ ⊗ … ⊗ Xₙ,
--     transported along the pair row; here it is taken directly.  n = 0
--     is excluded: its apex would be the probe unit ⟦D⁰⟧.);
--   * the row GB-shape at Θ = D⁰ with ⟦D⁰⟧♭ := ⊤F: a corolla
--     ι : (⟦D⁰⟧ ▸ ⊤F) whose precomposition at any input position is
--     invertible.  (The kernel's ⟦D⁰⟧♭ ≃ ⊤ is a chapter 7 fact that this
--     file takes as the definition ⟦D⁰⟧♭ := ⊤F.)
-- From these we derive weakening, the projections out of ⊗ and the
-- comparison κ_{A,W} : (A, W ▸ A ×F W), and prove its naturality.
--
-- Then the row L-× at set targets: for a predicate isSet on formulas,
-- precomposition with κ is invertible on multimaps into a set.
-- From it we derive, with [A, B] := A\B, the cartesian exponential:
--   ev : (A ×F [A,B] ▸ B),   λ f : (W ▸ [A,B]) for f : (A ×F W ▸ B),
--   β  : ev ∘ (A × λ f) ≈ f,
--   η  : λ (ev ∘ (A × g)) ≈ g,
--   and uniqueness: ev ∘ (A × g) ≈ ev ∘ (A × h) implies g ≈ h.
--
-- Scope: this is the 1-truncated content of Proposition 6.5 (≈ stands
-- for an invertible cell; cells above level 1 and the dcut instances
-- are not encoded), and the countermodels of Theorem 6.4 are not
-- encoded.  No postulates.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.FunSets (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open Model 𝔐

infixr 2 _≈⟨_⟩_
infix  3 _∎

_≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y ≈ z → x ≈ z
x ≈⟨ p ⟩ q = ≈-trans p q

_∎ : ∀ x → x ≈ x
x ∎ = ≈-refl

-- typing of one-place composition at positions 0 and 1
T-pc0 : ∀ {f g Y Q Z Xs} → f ∶ ((Y ∷ Q) ▸ Z) → g ∶ (Xs ▸ Y) →
        pc f 0 g ∶ ((Xs ++ Q) ▸ Z)
T-pc0 pf pg = T-pc {P = []} pf pg

T-pc1 : ∀ {f g X Y Q Z Xs} → f ∶ ((X ∷ Y ∷ Q) ▸ Z) → g ∶ (Xs ▸ Y) →
        pc f 1 g ∶ ((X ∷ Xs ++ Q) ▸ Z)
T-pc1 {X = X} pf pg = T-pc {P = X ∷ []} pf pg

-- Markl's sequential law at positions (0, 0) and (0, 1), both directions
seq00 : ∀ {f g h Y Q Z X Q′ Ws} →
        f ∶ ((Y ∷ Q) ▸ Z) → g ∶ ((X ∷ Q′) ▸ Y) → h ∶ (Ws ▸ X) →
        pc (pc f 0 g) 0 h ≈ pc f 0 (pc g 0 h)
seq00 pf pg ph = seq {P = []} {P′ = []} pf pg ph

seq01 : ∀ {f g h Y Q Z X₀ X Q′ Ws} →
        f ∶ ((Y ∷ Q) ▸ Z) → g ∶ ((X₀ ∷ X ∷ Q′) ▸ Y) → h ∶ (Ws ▸ X) →
        pc (pc f 0 g) 1 h ≈ pc f 0 (pc g 1 h)
seq01 {X₀ = X₀} pf pg ph = seq {P = []} {P′ = X₀ ∷ []} pf pg ph

seq10 : ∀ {f g h P₀ Y Q Z X Q′ Ws} →
        f ∶ ((P₀ ∷ Y ∷ Q) ▸ Z) → g ∶ ((X ∷ Q′) ▸ Y) → h ∶ (Ws ▸ X) →
        pc (pc f 1 g) 1 h ≈ pc f 1 (pc g 0 h)
seq10 {P₀ = P₀} pf pg ph = seq {P = P₀ ∷ []} {P′ = []} pf pg ph

------------------------------------------------------------------------
-- ⊤, products and the weakening row (GB-shape at D⁰)

record Weak : Set₁ where
  infixr 6 _×F_
  field
    ⊤F    : Fm
    _×F_  : Fm → Fm → Fm

    bang   : Fm → V
    T-bang : ∀ X → bang X ∶ ((X ∷ []) ▸ ⊤F)
    bang-η : ∀ {f X} → f ∶ ((X ∷ []) ▸ ⊤F) → f ≈ bang X

    p1 p2 : Fm → Fm → V
    T-p1  : ∀ A B → p1 A B ∶ (((A ×F B) ∷ []) ▸ A)
    T-p2  : ∀ A B → p2 A B ∶ (((A ×F B) ∷ []) ▸ B)
    pair  : V → V → V
    T-pair : ∀ {f g X Xs A B} → f ∶ ((X ∷ Xs) ▸ A) → g ∶ ((X ∷ Xs) ▸ B) → pair f g ∶ ((X ∷ Xs) ▸ (A ×F B))
    p1-β  : ∀ {f g X Xs A B} → f ∶ ((X ∷ Xs) ▸ A) → g ∶ ((X ∷ Xs) ▸ B) → pc (p1 A B) 0 (pair f g) ≈ f
    p2-β  : ∀ {f g X Xs A B} → f ∶ ((X ∷ Xs) ▸ A) → g ∶ ((X ∷ Xs) ▸ B) → pc (p2 A B) 0 (pair f g) ≈ g
    pair-η : ∀ {h X Xs A B} → h ∶ ((X ∷ Xs) ▸ (A ×F B)) →
             h ≈ pair (pc (p1 A B) 0 h) (pc (p2 A B) 0 h)
    pair-cong : ∀ {f f′ g g′} → f ≈ f′ → g ≈ g′ → pair f g ≈ pair f′ g′

    -- the shape row at Θ = D⁰, with ⟦D⁰⟧♭ := ⊤F
    ι     : V
    T-ι   : ι ∶ ((D 0 ∷ []) ▸ ⊤F)
    unI   : Nat → V → V
    T-unI : ∀ {y P Q Z} → y ∶ ((P ++ D 0 ∷ Q) ▸ Z) → unI (length P) y ∶ ((P ++ ⊤F ∷ Q) ▸ Z)
    unI-l : ∀ {x P Q Z} → x ∶ ((P ++ ⊤F ∷ Q) ▸ Z) → unI (length P) (pc x (length P) ι) ≈ x
    unI-r : ∀ {y P Q Z} → y ∶ ((P ++ D 0 ∷ Q) ▸ Z) → pc (unI (length P) y) (length P) ι ≈ y
    unI-cong : ∀ {y y′} i → y ≈ y′ → unI i y ≈ unI i y′

module WeakDefs (𝕎 : Weak) where
  open Weak 𝕎

  -- weakening at position i:  (P ++ Q ▸ Z)  ↦  (P ++ ⊤F ∷ Q ▸ Z)
  wk : Nat → V → V
  wk i x = unI i (unC cpt i x)

  T-wk : ∀ {x P Q Z} → x ∶ ((P ++ Q) ▸ Z) → wk (length P) x ∶ ((P ++ ⊤F ∷ Q) ▸ Z)
  T-wk {P = P} px = T-unI {P = P} (T-unC {P = P} {c = cpt} px)

  -- restriction back along ι and pt
  ρ : Nat → V → V
  ρ i y = pc (pc y i ι) i (cor cpt)

  ρ-wk : ∀ {x P Q Z} → x ∶ ((P ++ Q) ▸ Z) → ρ (length P) (wk (length P) x) ≈ x
  ρ-wk {x} {P} px =
    ≈-trans (pc-cong (length P) (unI-r {P = P} (T-unC {P = P} {c = cpt} px)) ≈-refl)
            (unC-r {P = P} {c = cpt} px)

  -- multimaps with a ⊤F input are determined by their restriction
  wk-ρ : ∀ {y P Q Z} → y ∶ ((P ++ ⊤F ∷ Q) ▸ Z) → wk (length P) (ρ (length P) y) ≈ y
  wk-ρ {y} {P} py =
    ≈-trans (unI-cong (length P) (unC-l {P = P} {c = cpt} (T-pc {P = P} py T-ι)))
            (unI-l {P = P} py)

  ρ-inj : ∀ {y y′ P Q Z} → y ∶ ((P ++ ⊤F ∷ Q) ▸ Z) → y′ ∶ ((P ++ ⊤F ∷ Q) ▸ Z) →
          ρ (length P) y ≈ ρ (length P) y′ → y ≈ y′
  ρ-inj {y} {y′} {P} py py′ e =
    ≈-trans (≈-sym (wk-ρ {P = P} py))
            (≈-trans (unI-cong (length P) (unC-cong cpt (length P) e)) (wk-ρ {P = P} py′))

  -- projections out of ⊗ and the comparison κ
  πA : Fm → Fm → V
  πA A W = pc (wk 1 (idv A)) 1 (bang W)

  πW : Fm → Fm → V
  πW A W = pc (wk 0 (idv W)) 0 (bang A)

  T-wk1 : ∀ A → wk 1 (idv A) ∶ ((A ∷ ⊤F ∷ []) ▸ A)
  T-wk1 A = T-wk {P = A ∷ []} {Q = []} (T-id A)

  T-wk0 : ∀ W → wk 0 (idv W) ∶ ((⊤F ∷ W ∷ []) ▸ W)
  T-wk0 W = T-wk {P = []} {Q = W ∷ []} (T-id W)

  T-πA : ∀ A W → πA A W ∶ ((A ∷ W ∷ []) ▸ A)
  T-πA A W = T-pc1 (T-wk1 A) (T-bang W)

  T-πW : ∀ A W → πW A W ∶ ((A ∷ W ∷ []) ▸ W)
  T-πW A W = T-pc0 (T-wk0 W) (T-bang A)

  κ : Fm → Fm → V
  κ A W = pair (πA A W) (πW A W)

  T-κ : ∀ A W → κ A W ∶ ((A ∷ W ∷ []) ▸ (A ×F W))
  T-κ A W = T-pair (T-πA A W) (T-πW A W)

  -- A × g  for  g : (W ▸ C)
  prodMap : Fm → Fm → V → V
  prodMap A W g = pair (p1 A W) (pc g 0 (p2 A W))

  T-prodMap : ∀ {g A W C} → g ∶ ((W ∷ []) ▸ C) → prodMap A W g ∶ (((A ×F W) ∷ []) ▸ (A ×F C))
  T-prodMap {A = A} {W} pg = T-pair (T-p1 A W) (T-pc0 pg (T-p2 A W))

  -- naturality of weakening:  wk₀(1_C) ∘₁ g  ≈  g ∘₀ wk₀(1_W)
  wk-nat : ∀ {g W C} → g ∶ ((W ∷ []) ▸ C) →
           pc (wk 0 (idv C)) 1 g ≈ pc g 0 (wk 0 (idv W))
  wk-nat {g} {W} {C} pg = ρ-inj {P = []} pL pR (≈-trans lhs (≈-sym rhs))
    where
      F  = wk 0 (idv C)
      pF = T-wk0 C
      pL : pc F 1 g ∶ ((⊤F ∷ W ∷ []) ▸ C)
      pL = T-pc1 pF pg
      pR : pc g 0 (wk 0 (idv W)) ∶ ((⊤F ∷ W ∷ []) ▸ C)
      pR = T-pc0 pg (T-wk0 W)
      G  = pc F 0 ι
      pG : G ∶ ((D 0 ∷ C ∷ []) ▸ C)
      pG = T-pc0 pF T-ι
      -- ρ of the left side is g
      lhs : ρ 0 (pc F 1 g) ≈ g
      lhs =
        pc (pc (pc F 1 g) 0 ι) 0 (cor cpt)
          ≈⟨ pc-cong 0 (≈-sym (par {P = []} {M = []} pF T-ι pg)) ≈-refl ⟩
        pc (pc G 1 g) 0 (cor cpt)
          ≈⟨ ≈-sym (par {P = []} {M = []} pG (T-cor cpt) pg) ⟩
        pc (pc G 0 (cor cpt)) 0 g
          ≈⟨ pc-cong 0 (ρ-wk {P = []} (T-id C)) ≈-refl ⟩
        pc (idv C) 0 g
          ≈⟨ unit-l pg ⟩
        g ∎
      -- ρ of the right side is g
      rhs : ρ 0 (pc g 0 (wk 0 (idv W))) ≈ g
      rhs =
        pc (pc (pc g 0 (wk 0 (idv W))) 0 ι) 0 (cor cpt)
          ≈⟨ pc-cong 0 (seq00 pg (T-wk0 W) T-ι) ≈-refl ⟩
        pc (pc g 0 (pc (wk 0 (idv W)) 0 ι)) 0 (cor cpt)
          ≈⟨ seq00 pg (T-pc0 (T-wk0 W) T-ι) (T-cor cpt) ⟩
        pc g 0 (ρ 0 (wk 0 (idv W)))
          ≈⟨ pc-cong 0 ≈-refl (ρ-wk {P = []} (T-id W)) ⟩
        pc g 0 (idv W)
          ≈⟨ unit-r {P = []} {Q = []} pg ⟩
        g ∎

  -- naturality of κ:  (A × g) ∘ κ_{A,W}  ≈  κ_{A,C} ∘₁ g
  κ-nat : ∀ {g A W C} → g ∶ ((W ∷ []) ▸ C) →
          pc (prodMap A W g) 0 (κ A W) ≈ pc (κ A C) 1 g
  κ-nat {g} {A} {W} {C} pg =
    ≈-trans (pair-η pL)
      (≈-trans (pair-cong (≈-trans c1L (≈-sym c1R)) (≈-trans c2L (≈-sym c2R)))
               (≈-sym (pair-η pR)))
    where
      pM = T-prodMap {A = A} pg
      pL : pc (prodMap A W g) 0 (κ A W) ∶ ((A ∷ W ∷ []) ▸ (A ×F C))
      pL = T-pc0 pM (T-κ A W)
      pR : pc (κ A C) 1 g ∶ ((A ∷ W ∷ []) ▸ (A ×F C))
      pR = T-pc1 (T-κ A C) pg
      c1L : pc (p1 A C) 0 (pc (prodMap A W g) 0 (κ A W)) ≈ πA A W
      c1L =
        _ ≈⟨ ≈-sym (seq00 (T-p1 A C) pM (T-κ A W)) ⟩
        pc (pc (p1 A C) 0 (prodMap A W g)) 0 (κ A W)
          ≈⟨ pc-cong 0 (p1-β (T-p1 A W) (T-pc0 pg (T-p2 A W))) ≈-refl ⟩
        pc (p1 A W) 0 (κ A W)
          ≈⟨ p1-β (T-πA A W) (T-πW A W) ⟩
        πA A W ∎
      c1R : pc (p1 A C) 0 (pc (κ A C) 1 g) ≈ πA A W
      c1R =
        _ ≈⟨ ≈-sym (seq01 (T-p1 A C) (T-κ A C) pg) ⟩
        pc (pc (p1 A C) 0 (κ A C)) 1 g
          ≈⟨ pc-cong 1 (p1-β (T-πA A C) (T-πW A C)) ≈-refl ⟩
        pc (πA A C) 1 g
          ≈⟨ seq10 (T-wk1 A) (T-bang C) pg ⟩
        pc (wk 1 (idv A)) 1 (pc (bang C) 0 g)
          ≈⟨ pc-cong 1 ≈-refl (bang-η (T-pc0 (T-bang C) pg)) ⟩
        πA A W ∎
      c2L : pc (p2 A C) 0 (pc (prodMap A W g) 0 (κ A W)) ≈ pc g 0 (πW A W)
      c2L =
        _ ≈⟨ ≈-sym (seq00 (T-p2 A C) pM (T-κ A W)) ⟩
        pc (pc (p2 A C) 0 (prodMap A W g)) 0 (κ A W)
          ≈⟨ pc-cong 0 (p2-β (T-p1 A W) (T-pc0 pg (T-p2 A W))) ≈-refl ⟩
        pc (pc g 0 (p2 A W)) 0 (κ A W)
          ≈⟨ seq00 pg (T-p2 A W) (T-κ A W) ⟩
        pc g 0 (pc (p2 A W) 0 (κ A W))
          ≈⟨ pc-cong 0 ≈-refl (p2-β (T-πA A W) (T-πW A W)) ⟩
        pc g 0 (πW A W) ∎
      c2R : pc (p2 A C) 0 (pc (κ A C) 1 g) ≈ pc g 0 (πW A W)
      c2R =
        _ ≈⟨ ≈-sym (seq01 (T-p2 A C) (T-κ A C) pg) ⟩
        pc (pc (p2 A C) 0 (κ A C)) 1 g
          ≈⟨ pc-cong 1 (p2-β (T-πA A C) (T-πW A C)) ≈-refl ⟩
        pc (pc (wk 0 (idv C)) 0 (bang A)) 1 g
          ≈⟨ par {P = []} {M = []} (T-wk0 C) (T-bang A) pg ⟩
        pc (pc (wk 0 (idv C)) 1 g) 0 (bang A)
          ≈⟨ pc-cong 0 (wk-nat pg) ≈-refl ⟩
        pc (pc g 0 (wk 0 (idv W))) 0 (bang A)
          ≈⟨ seq00 pg (T-wk0 W) (T-bang A) ⟩
        pc g 0 (πW A W) ∎

------------------------------------------------------------------------
-- The contraction row L-× at set targets

module _ (𝕎 : Weak) where
 open Weak 𝕎
 open WeakDefs 𝕎
 record Contr : Set₁ where
  field
    isSet : Fm → Set
    unK   : Fm → Fm → V → V
    T-unK : ∀ {y A W B} → isSet B → y ∶ ((A ∷ W ∷ []) ▸ B) → unK A W y ∶ (((A ×F W) ∷ []) ▸ B)
    unK-l : ∀ {x A W B} → isSet B → x ∶ (((A ×F W) ∷ []) ▸ B) → unK A W (pc x 0 (κ A W)) ≈ x
    unK-r : ∀ {y A W B} → isSet B → y ∶ ((A ∷ W ∷ []) ▸ B) → pc (unK A W y) 0 (κ A W) ≈ y
    unK-cong : ∀ {y y′} A W → y ≈ y′ → unK A W y ≈ unK A W y′

------------------------------------------------------------------------
-- F8 derived: [A, B] := A\B

module Exp (𝕎 : Weak) (ℂ : Contr 𝕎) where
  open Weak 𝕎
  open WeakDefs 𝕎
  open Contr ℂ

  κ-inj : ∀ {x x′ A W B} → isSet B →
          x ∶ (((A ×F W) ∷ []) ▸ B) → x′ ∶ (((A ×F W) ∷ []) ▸ B) →
          pc x 0 (κ A W) ≈ pc x′ 0 (κ A W) → x ≈ x′
  κ-inj {A = A} {W} sB px px′ e =
    ≈-trans (≈-sym (unK-l sB px)) (≈-trans (unK-cong A W e) (unK-l sB px′))

  Exp : Fm → Fm → Fm
  Exp A B = A \\ B

  ev : Fm → Fm → V
  ev A B = unK A (A \\ B) (evL A B)

  T-ev : ∀ {A B} → isSet B → ev A B ∶ (((A ×F (A \\ B)) ∷ []) ▸ B)
  T-ev {A} {B} sB = T-unK sB (T-evL A B)

  lam : Fm → Fm → Fm → V → V
  lam A W B f = curL A B (pc f 0 (κ A W))

  T-lam : ∀ {f A W B} → f ∶ (((A ×F W) ∷ []) ▸ B) → lam A W B f ∶ ((W ∷ []) ▸ (A \\ B))
  T-lam {A = A} {W} pf = T-curL (T-pc0 pf (T-κ A W))

  lam-cong : ∀ {f f′} A W B → f ≈ f′ → lam A W B f ≈ lam A W B f′
  lam-cong A W B e = curL-cong A B (pc-cong 0 e ≈-refl)

  -- the key computation:  (ev ∘ (A × g)) ∘ κ  ≈  e^ℓ ∘₁ g
  ev-κ : ∀ {g A W B} → isSet B → g ∶ ((W ∷ []) ▸ (A \\ B)) →
         pc (pc (ev A B) 0 (prodMap A W g)) 0 (κ A W) ≈ pc (evL A B) 1 g
  ev-κ {g} {A} {W} {B} sB pg =
    _ ≈⟨ seq00 (T-ev sB) (T-prodMap pg) (T-κ A W) ⟩
    pc (ev A B) 0 (pc (prodMap A W g) 0 (κ A W))
      ≈⟨ pc-cong 0 ≈-refl (κ-nat pg) ⟩
    pc (ev A B) 0 (pc (κ A (A \\ B)) 1 g)
      ≈⟨ ≈-sym (seq01 (T-ev sB) (T-κ A (A \\ B)) pg) ⟩
    pc (pc (ev A B) 0 (κ A (A \\ B))) 1 g
      ≈⟨ pc-cong 1 (unK-r sB (T-evL A B)) ≈-refl ⟩
    pc (evL A B) 1 g ∎

  -- (exp-λ), β
  β : ∀ {f A W B} → isSet B → f ∶ (((A ×F W) ∷ []) ▸ B) →
      pc (ev A B) 0 (prodMap A W (lam A W B f)) ≈ f
  β {f} {A} {W} {B} sB pf =
    κ-inj sB (T-pc0 (T-ev sB) (T-prodMap (T-lam pf))) pf
      (≈-trans (ev-κ sB (T-lam pf)) (curL-r (T-pc0 pf (T-κ A W))))

  -- η: every map into [A, B] is the λ of its transpose
  η : ∀ {g A W B} → isSet B → g ∶ ((W ∷ []) ▸ (A \\ B)) →
      lam A W B (pc (ev A B) 0 (prodMap A W g)) ≈ g
  η {g} {A} {W} {B} sB pg =
    ≈-trans (curL-cong A B (ev-κ sB pg)) (curL-l pg)

  -- (exp-uni) at level 1, 1-truncated: transposes determine the map
  uni : ∀ {g h A W B} → isSet B → g ∶ ((W ∷ []) ▸ (A \\ B)) → h ∶ ((W ∷ []) ▸ (A \\ B)) →
        pc (ev A B) 0 (prodMap A W g) ≈ pc (ev A B) 0 (prodMap A W h) → g ≈ h
  uni {A = A} {W} {B} sB pg ph e =
    ≈-trans (≈-sym (η sB pg)) (≈-trans (lam-cong A W B e) (η sB ph))
