------------------------------------------------------------------------
-- Ledger F11f (notes/higher-inductive.md §5, Theorem D).
--
-- Dependent elimination from initiality (Awodey–Gambino–Sojakova),
-- for an arbitrary category of models over an ambient category.
--
-- Setting.  An ambient category 𝒞, a category of models 𝓜 and a
-- forgetful functor U : 𝓜 → 𝒞.  An initial object η of 𝓜 plays μΔ
-- (INIT-form, INIT-J1 = existence of `rec`, INIT-J2 = uniqueness).
-- Nothing about the shape of Δ is assumed: point constructors, cell
-- constructors, recursive constructors and marks all only change 𝓜.
--
-- A family over μΔ is any map p : E → U η of 𝒞 (no fibration
-- condition).  A dependent model over η is an object M_E of 𝓜 with
-- U M_E ≡ E and a model morphism q : M_E → η whose underlying map is p
-- (Theorem D's "model-morphism structure on p").
--
-- Proved (no postulates):
--   section      U(rec M_E) is a section of p:  p ∘ U(rec) ≡ id;
--   computation  rec M_E is a model morphism η → M_E (by construction);
--   unique       any model morphism s : η → M_E has q ∘ s ≡ id, and
--                any two such s are equal.
--
-- Scope and honesty notes.
--   * 1-truncated: hom-sets, strict equations.  In the system,
--     INIT-J1/J2 give invertible cells and a contractible space of
--     model morphisms; here those are equalities.  The higher clause of
--     INIT (cells between model morphisms) is not encoded.
--   * The category 𝓜 is abstract: this file does NOT construct the
--     category of models of a positive context, does NOT prove that
--     initial models exist (INIT is assumed as `Initial`), and does NOT
--     derive the fibrewise (directed path-over) reading of §5.
--   * U is only used on morphisms of 𝓜 to state the section equation;
--     the transport of `U M_E ≡ E` is avoided by stating everything for
--     E := U M_E.
------------------------------------------------------------------------
module CaTTExp.HIT.DependentElim where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas using (Cat; Functor)

record Initial (𝓜 : Cat) : Set where
  open Cat 𝓜
  field
    η    : Ob
    rec  : (M : Ob) → Hom η M
    uni  : ∀ {M} (h : Hom η M) → h ≡ rec M

module TheoremD (𝒞 𝓜 : Cat) (U : Functor 𝓜 𝒞) (I : Initial 𝓜) where
  private
    module C = Cat 𝒞
    module M = Cat 𝓜
    module U = Functor U
  open Initial I

  -- Any two endomorphisms of the initial object agree, so each is id.
  endo-id : (h : M.Hom η η) → h ≡ M.id
  endo-id h = trans (uni h) (sym (uni M.id))

  -- A dependent model: an object over η via a model morphism q.
  -- Its underlying family is p := U q : U M_E → U η.
  module _ (ME : M.Ob) (q : M.Hom ME η) where

    s : M.Hom η ME
    s = rec ME

    -- s is a model morphism η → M_E (computation rule): by construction.

    -- q ∘ s ≡ id in 𝓜 (p ∘ s ≅ 1 as model morphisms, INIT-J2).
    over : q M.∘ s ≡ M.id
    over = endo-id (q M.∘ s)

    -- Underlying: U s is a section of the family p = U q.
    section : U.F₁ q C.∘ U.F₁ s ≡ C.id
    section = trans (sym (U.F-∘ q s)) (trans (cong U.F₁ over) U.F-id)

    -- Uniqueness: every model morphism η → M_E is s, and lies over η.
    unique : (s' : M.Hom η ME) → s' ≡ s
    unique s' = uni s'

    unique-over : (s' : M.Hom η ME) → q M.∘ s' ≡ M.id
    unique-over s' = endo-id (q M.∘ s')
