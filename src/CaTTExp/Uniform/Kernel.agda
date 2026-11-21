------------------------------------------------------------------------
-- The kernel's typing rules and certified checker, with the uniform
-- side condition (coh_S) of spec/02-lax-core.md §2.3 (ledger S3).
--
-- Parameters: for every pasting context Δ and type A,
--   layer Δ A    the layer of F_{V+S}(Δ) holding the strict images of
--                terms of type A, with the letters one dimension up;
--   graded Δ A   a bound on the length of paths in that layer;
--   ⟦_⟧ Δ A      the strict interpretation of terms (partial: it may
--                fail on ill-typed input).
--
-- The side condition is then
--
--   side Δ A t u = true  ⟺  ⟦t⟧ = just x, ⟦u⟧ = just y, and SC x y
--
-- (side-sound, side-complete), with SC as in CaTTExp.Uniform.Rule:
-- a path of letters from x to y whose support is full. The typing
-- rules are CaTTExp.TypingWith at this side condition, whose coh rule
-- is then exactly (coh_S); the checker is CaTTExp.CheckWith, sound by
-- construction and complete by CaTTExp.Completeness.
--
-- Since 2026-11-21 this module is KernelDec instantiated with the
-- bounded decision Rule.Decide.sc?; KernelDec takes any decision of
-- SC, including RuleFin's search for layers with loops, which have no
-- length bound. Prefer KernelDec for new instances.
--
-- This module does not construct the layers of F_{V+S}: it is the
-- kernel checker relative to them. CaTTExp.Uniform.Grid constructs
-- the layer in which the switch laws act (degree four, suspended
-- grids), for every setting S.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Uniform.Rule

module CaTTExp.Uniform.Kernel
  (𝕊      : Signature)
  (layer  : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Layer)
  (graded : ∀ Δ A → Graded (layer Δ A))
  (⟦_⟧    : ∀ Δ A → Signature.Tm 𝕊 → Maybe (Layer.Cell (layer Δ A)))
  where

open import CaTTExp.Uniform.KernelDec 𝕊 layer (λ Δ A → Decide.sc? (layer Δ A) (graded Δ A)) ⟦_⟧ public
