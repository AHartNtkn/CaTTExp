------------------------------------------------------------------------
-- Models of the biclosed kernel (Theorem S, notes/free-objects-proofs.md
-- §5.4): the structure a semantics needs to interpret the Gray/Biclosed
-- syntax.
--
-- A model is a planar multicategory whose objects are the formulas
-- (the interpretation of object variables is fixed inside the model),
-- given by one-place composition with Markl's sequential, parallel and
-- unit laws, up to an equivalence ≈ and with an extrinsic typing
-- judgement v ∶ (X₁, …, Xₙ ▸ Z).  On top of that:
--   * representability: precomposition with m_{U,V}, p_{Δ,Θ} or pt at
--     any input position is invertible (the pair, probe-pair and unit
--     rows of F.7.4 §2);
--   * closures: v ↦ e^ℓ ∘₁ v and v ↦ e^r ∘₀ v are invertible (the left
--     and right evaluation rows), for every list of inputs Φ;
--   * globes: δ^±_n : ⟦Dⁿ⟧ → ⟦Dⁿ⁺¹⟧ (nullary at n = 0, since ⟦D⁰⟧ is the
--     unit) and σ_n : ⟦Dⁿ⁺¹⟧ → ⟦Dⁿ⟧ with σ ∘ δ^± = 1 (= pt at n = 0).
-- An n-cell of (X₁, …, Xₖ ▸ Z) at gap g is an operation with ⟦Dⁿ⟧ in
-- input position g; its faces are restrictions along δ^±.
--
-- The strict model 𝔖 of the paper (strict ω-categories, Gray tensor,
-- its closures, ⟦Θ⟧ = ν(λΘ)) is a model in this sense: these are the
-- standard facts of a monoidal biclosed category with a co-globular
-- object.  Concrete models are in other modules.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Model where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps

-- the k-globe as a formula; ⟦D⁰⟧ is the unit
D : Nat → Fm
D k = rep (disk k)

-- inputs of the faces δ^±_n : (dsrc n ▸ D (n+1))
dsrc : Nat → List Fm
dsrc zero    = []
dsrc (suc n) = D (suc n) ∷ []

-- the three representing corollas
data Cor : Set where
  cm  : Fm → Fm → Cor          -- m_{U,V}
  cp  : Shape → Shape → Cor    -- p_{Δ,Θ}
  cpt : Cor                    -- pt

corIns : Cor → List Fm
corIns (cm U W) = U ∷ W ∷ []
corIns (cp Δ Θ) = rep Δ ∷ rep Θ ∷ []
corIns cpt      = []

corOut : Cor → Fm
corOut (cm U W) = U ⊗ W
corOut (cp Δ Θ) = rep (Δ ⊠ Θ)
corOut cpt      = D 0

record Model : Set₁ where
  infix 4 _≈_ _∶_
  field
    V     : Set
    _≈_   : V → V → Set
    ≈-refl  : ∀ {x} → x ≈ x
    ≈-sym   : ∀ {x y} → x ≈ y → y ≈ x
    ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    _∶_   : V → MTy → Set
    ∶-≈   : ∀ {x y M} → x ≈ y → x ∶ M → y ∶ M

    -- operations
    pc    : V → Nat → V → V      -- f ∘ᵢ g
    idv   : Fm → V
    cor   : Cor → V
    evL   : Fm → Fm → V          -- e^ℓ_{A,C} : (A, A\C ▸ C)
    evR   : Fm → Fm → V          -- e^r_{A,C} : (C/A, A ▸ C)
    δ     : Bool → Nat → V       -- δ^α_n : (dsrc n ▸ D (n+1)); true is +
    σ     : Nat → V              -- σ_n : (D (n+1) ▸ D n)

    -- inverses of the rows
    unC   : Cor → Nat → V → V    -- inverse of x ↦ x ∘ᵢ c
    curL  : Fm → Fm → V → V      -- inverse of x ↦ e^ℓ ∘₁ x
    curR  : Fm → Fm → V → V      -- inverse of x ↦ e^r ∘₀ x

    -- typing
    T-pc  : ∀ {f g P Y Q Z Xs} → f ∶ ((P ++ Y ∷ Q) ▸ Z) → g ∶ (Xs ▸ Y) →
            pc f (length P) g ∶ ((P ++ Xs ++ Q) ▸ Z)
    T-id  : ∀ A → idv A ∶ ((A ∷ []) ▸ A)
    T-cor : ∀ c → cor c ∶ (corIns c ▸ corOut c)
    T-evL : ∀ A C → evL A C ∶ ((A ∷ (A \\ C) ∷ []) ▸ C)
    T-evR : ∀ A C → evR A C ∶ (((C // A) ∷ A ∷ []) ▸ C)
    T-δ   : ∀ α n → δ α n ∶ (dsrc n ▸ D (suc n))
    T-σ   : ∀ n → σ n ∶ ((D (suc n) ∷ []) ▸ D n)

    -- congruence
    pc-cong : ∀ {f f′ g g′} i → f ≈ f′ → g ≈ g′ → pc f i g ≈ pc f′ i g′

    -- Markl's laws for one-place composition (planar)
    seq : ∀ {f g h P Y Q Z P′ X Q′ Ws} →
          f ∶ ((P ++ Y ∷ Q) ▸ Z) → g ∶ ((P′ ++ X ∷ Q′) ▸ Y) → h ∶ (Ws ▸ X) →
          pc (pc f (length P) g) (length P + length P′) h
            ≈ pc f (length P) (pc g (length P′) h)
    par : ∀ {f g h P Y M W Q Z Xs Ws} →
          f ∶ ((P ++ Y ∷ M ++ W ∷ Q) ▸ Z) → g ∶ (Xs ▸ Y) → h ∶ (Ws ▸ W) →
          pc (pc f (length P) g) (length P + length Xs + length M) h
            ≈ pc (pc f (length P + suc (length M)) h) (length P) g
    unit-l : ∀ {g Xs Y} → g ∶ (Xs ▸ Y) → pc (idv Y) 0 g ≈ g
    unit-r : ∀ {f P Y Q Z} → f ∶ ((P ++ Y ∷ Q) ▸ Z) → pc f (length P) (idv Y) ≈ f

    -- representability: precomposition with a corolla is invertible
    T-unC : ∀ {y P c Q Z} → y ∶ ((P ++ corIns c ++ Q) ▸ Z) →
            unC c (length P) y ∶ ((P ++ corOut c ∷ Q) ▸ Z)
    unC-l : ∀ {x P c Q Z} → x ∶ ((P ++ corOut c ∷ Q) ▸ Z) →
            unC c (length P) (pc x (length P) (cor c)) ≈ x
    unC-r : ∀ {y P c Q Z} → y ∶ ((P ++ corIns c ++ Q) ▸ Z) →
            pc (unC c (length P) y) (length P) (cor c) ≈ y
    unC-cong : ∀ {y y′} c i → y ≈ y′ → unC c i y ≈ unC c i y′

    -- closures: the evaluation rows are invertible
    T-curL : ∀ {y A Φ C} → y ∶ ((A ∷ Φ) ▸ C) → curL A C y ∶ (Φ ▸ (A \\ C))
    curL-l : ∀ {x A Φ C} → x ∶ (Φ ▸ (A \\ C)) → curL A C (pc (evL A C) 1 x) ≈ x
    curL-r : ∀ {y A Φ C} → y ∶ ((A ∷ Φ) ▸ C) → pc (evL A C) 1 (curL A C y) ≈ y
    curL-cong : ∀ {y y′} A C → y ≈ y′ → curL A C y ≈ curL A C y′
    T-curR : ∀ {y A Φ C} → y ∶ ((Φ ++ A ∷ []) ▸ C) → curR A C y ∶ (Φ ▸ (C // A))
    curR-l : ∀ {x A Φ C} → x ∶ (Φ ▸ (C // A)) → curR A C (pc (evR A C) 0 x) ≈ x
    curR-r : ∀ {y A Φ C} → y ∶ ((Φ ++ A ∷ []) ▸ C) → pc (evR A C) 0 (curR A C y) ≈ y
    curR-cong : ∀ {y y′} A C → y ≈ y′ → curR A C y ≈ curR A C y′

    -- globes: σ is a retraction of both faces
    σδ-suc : ∀ α n → pc (σ (suc n)) 0 (δ α (suc n)) ≈ idv (D (suc n))
    σδ-0   : ∀ α → pc (σ 0) 0 (δ α 0) ≈ cor cpt
