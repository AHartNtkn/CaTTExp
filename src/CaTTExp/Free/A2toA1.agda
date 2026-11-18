{-# OPTIONS --safe --guardedness #-}
------------------------------------------------------------------------
-- From A2's rules to A1's universal property (open-issues C7;
-- notes/free-objects.md §3.3; notes/free-objects-proofs.md §3).
--
-- free-objects.md §3.3 derives A1's universal property for
-- ⟦Γ, x : A⟧ = ⟦Γ⟧[x : A] by chaining three maps:
--
--   Hom(⟦Γ,x⟧, C) ──ATTACH──▶ Hom(⟦Γ⟧, C) ×_{Diag(∂D)} Diag(D)
--                 ──P(R_Γ)──▶ Diag(Γ, C)   ×_{Diag(∂D)} Diag(D)
--                 ──Dec────▶ Diag((Γ, x), C)
--
-- This module proves that the chain gives A1's LIFT schema for every
-- context, by induction on the context, from:
--   * A2's LIFT for 0 (base) and for each attachment (`a2-equiv`);
--   * C3 (`dec-equiv`): the decomposition map is an equivalence
--     (free-objects-proofs.md Thm 3 gives an isomorphism onto the
--     strict pullback);
--   * pullback stability (`pb-equiv`): the map induced on pullbacks by
--     an equivalence R_Γ is an equivalence. This is the step that needs
--     the boundary restriction to be an ω-equifibration
--     (free-objects-proofs.md §2.2, open item C3b).
-- All three are explicit hypotheses (record fields / arguments); the
-- content proved here is that LIFT-equivalences compose, coinductively,
-- and that the induction goes through. Combined with
-- CaTTExp.Free.Reflect, the derived A1 restrictions reflect
-- invertibility.
------------------------------------------------------------------------
module CaTTExp.Free.A2toA1 where

open import CaTTExp.Prelude
open import CaTTExp.Free.Reflect

------------------------------------------------------------------------
-- Composition of functors between towers.

infixr 9 _∘F_
_∘F_ : ∀ {G H K} → Fun H K → Fun G H → Fun G K
ob  (S ∘F R) x   = ob S (ob R x)
hom (S ∘F R) a b = hom S (ob R a) (ob R b) ∘F hom R a b

-- Functors preserve invertible cells (I5 of free-objects-proofs §1.2;
-- Fujii–Hoshino–Maehara 2303.14907 Prop. 3.2.1), at every level.
record PresInv {H K : Glob} (S : Fun H K) (OH : Ops H) (OK : Ops K) : Set where
  coinductive
  field
    pres     : ∀ {a b} {f : Cell H a b} → Inv OH f → Inv OK (fmap S f)
    hom-pres : ∀ a b → PresInv (hom S a b) (hom OH a b) (hom OK (ob S a) (ob S b))
open PresInv public

------------------------------------------------------------------------
-- LIFT-equivalences compose.

Equiv-∘ : ∀ {G H K} {OH : Ops H} {OK : Ops K} {R : Fun G H} {S : Fun H K} →
          Equiv R OH → Equiv S OK → PresInv S OH OK → Closed OK →
          Equiv (S ∘F R) OK
lift0 (Equiv-∘ {OK = OK} {R = R} {S = S} ER ES P C) z =
  let y , φ , φi = lift0 ES z
      x , θ , θi = lift0 ER y
  in x , comp OK (fmap S θ) φ , comp-inv C (pres P θi) φi
homEq (Equiv-∘ {R = R} ER ES P C) a b =
  Equiv-∘ (homEq ER a b) (homEq ES (ob R a) (ob R b))
          (hom-pres P (ob R a) (ob R b)) (hom-closed C _ _)

------------------------------------------------------------------------
-- The data of A2, for a fixed target C, indexed by contexts presented
-- as lists of attachments (the context's types are irrelevant to the
-- argument, so they are an arbitrary type `Sph` of spheres).

data Ctx' (Sph : Set) : Set where
  ε   : Ctx' Sph
  _▸_ : Ctx' Sph → Sph → Ctx' Sph

record A2Data (Sph : Set) : Set₁ where
  field
    -- Hom(⟦Γ⟧, C) and Diag(Γ, C).
    H D        : Ctx' Sph → Glob
    OD         : ∀ Γ → Ops (D Γ)
    -- The pullbacks Hom(⟦Γ⟧,C) ×_{Diag(∂D)} Diag(D) and
    -- Diag(Γ,C) ×_{Diag(∂D)} Diag(D), with their operations.
    PH PD      : ∀ Γ → Sph → Glob
    OPH        : ∀ Γ A → Ops (PH Γ A)
    OPD        : ∀ Γ A → Ops (PD Γ A)
    -- A1's restriction for the empty context (Hom(0, C) → Diag(ε, C)).
    R₀         : Fun (H ε) (D ε)
    -- ATTACH's restriction G ↦ (G ∘ ι, G x).
    a2         : ∀ Γ A → Fun (H (Γ ▸ A)) (PH Γ A)
    -- The map on pullbacks induced by a map Hom(⟦Γ⟧,C) → Diag(Γ,C).
    P          : ∀ {Γ A} → Fun (H Γ) (D Γ) → Fun (PH Γ A) (PD Γ A)
    -- The decomposition map of C3.
    dec        : ∀ Γ A → Fun (PD Γ A) (D (Γ ▸ A))

  -- A1's restriction along η_Γ, as the chain of free-objects.md §3.3.
  R₁ : ∀ Γ → Fun (H Γ) (D Γ)
  R₁ ε       = R₀
  R₁ (Γ ▸ A) = dec Γ A ∘F P (R₁ Γ) ∘F a2 Γ A

record A2Hyp {Sph : Set} (𝔻 : A2Data Sph) : Set where
  open A2Data 𝔻
  field
    -- A2's universal properties: the LIFT schema for 0 and for ATTACH.
    init-equiv : Equiv R₀ (OD ε)
    a2-equiv   : ∀ Γ A → Equiv (a2 Γ A) (OPH Γ A)
    -- Pullback stability (the open item C3b).
    pb-equiv   : ∀ Γ A → Equiv (R₁ Γ) (OD Γ) → Equiv (P {Γ} {A} (R₁ Γ)) (OPD Γ A)
    -- C3: the decomposition map is an equivalence.
    dec-equiv  : ∀ Γ A → Equiv (dec Γ A) (OD (Γ ▸ A))
    -- I5 for the two outer maps, and I1–I2 for their targets.
    P-pres     : ∀ Γ A → PresInv (P {Γ} {A} (R₁ Γ)) (OPH Γ A) (OPD Γ A)
    dec-pres   : ∀ Γ A → PresInv (dec Γ A) (OPD Γ A) (OD (Γ ▸ A))
    closedD    : ∀ Γ → Closed (OD Γ)
    closedPD   : ∀ Γ A → Closed (OPD Γ A)

------------------------------------------------------------------------
-- Theorem: A1's LIFT schema holds for every context.

module _ {Sph : Set} (𝔻 : A2Data Sph) (𝕙 : A2Hyp 𝔻) where
  open A2Data 𝔻
  open A2Hyp 𝕙

  A1-lift : ∀ Γ → Equiv (R₁ Γ) (OD Γ)
  A1-lift ε       = init-equiv
  A1-lift (Γ ▸ A) =
    Equiv-∘ (Equiv-∘ (a2-equiv Γ A) (pb-equiv Γ A (A1-lift Γ))
                     (P-pres Γ A) (closedPD Γ A))
            (dec-equiv Γ A) (dec-pres Γ A) (closedD (Γ ▸ A))
