------------------------------------------------------------------------
-- K2 (GB-shape): the shape row, at every Θ.
--
-- The row (design-decisions §4.7, spec §8.8):
--   H = (L, ⟦Θ⟧♭, R ▸ Z),  B = (L, ⟦Θ⟧, R ▸ Z),  r(x) = x ∘ᵢ ι_Θ,
-- with ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭) the shape map (Syntax: shp, iP, shapeR).
-- ⟦Θ⟧♭ is a data atom: it is not representable (nonRep), so a template
-- over a shape row is sorted like any data row (SortDisc).
--
-- The row is wired into every generic theorem of the development, which
-- quantify over all rows and so over all Θ.  This module states them
-- for the shape row (no postulates):
--   * iota-typed    : ι_Θ has type (⟦Θ⟧ ▸ ⟦Θ⟧♭) in every context;
--   * shape-cand    : the shape row is a candidate row of its own H
--                     (so admit? finds it);
--   * shape-ok      : the canonical one-slot shape templates satisfy the
--                     side conditions okT, at every Θ, gap-free cut and
--                     every directed gap, every dimension;
--   * shape-adm     : their goals (c and ε) are admissible and admit?
--                     accepts them;
--   * shape-typed   : their contexts and goals are well typed;
--   * shape-rmap    : r sends a cell of the H-tower to one of the
--                     B-tower (the typing of r at every level).
-- Soundness in the model (Soundness.sound, iP case: ι_Θ is the
-- corolla cι Θ) and in the poset model (PosetModel: ⟦Θ⟧♭ is the poset
-- of ⟦Θ⟧ and ι_Θ the identity) cover the row; Mirror sends the shape
-- row at Θ to the shape row at Θ*.  Examples checks shape rows at
-- Θ = named 0, D¹, D¹ ⊠ named 0 by evaluation, including the
-- rejection of reversed directed goals.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.ShapeRow where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates
open import CaTTExp.Gray.Biclosed.TemplatesTyped using (templates-typed; infer-rmap)

-- ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭)
iota-typed : ∀ Γ Θ → infer Γ (iP Θ) ≡ just (op ((rep Θ ∷ []) ▸ shp Θ))
iota-typed Γ Θ = refl

-- the row has the advertised vertex types and restriction
shape-H : ∀ L Θ R Z → H (shapeR L Θ R Z) ≡ (L ++ shp Θ ∷ R) ▸ Z
shape-H L Θ R Z = refl

shape-B : ∀ L Θ R Z → B (shapeR L Θ R Z) ≡ (L ++ rep Θ ∷ R) ▸ Z
shape-B L Θ R Z = refl

shape-r : ∀ L Θ R Z x → rmap (shapeR L Θ R Z) x ≡ comp x (ids L ++ iP Θ ∷ ids R)
shape-r L Θ R Z x = refl

-- admit? looks for it: it is a candidate row of its own H
shape-cand : ∀ L Θ R Z → shapeR L Θ R Z ∈ rowsOf ((L ++ shp Θ ∷ R) ▸ Z)
shape-cand L Θ R Z = rowsOf-complete (shapeR L Θ R Z)

------------------------------------------------------------------------
-- The canonical one-slot templates, at every Θ

-- (X, ⟦Θ⟧♭ ▸ Z) against (X, ⟦Θ⟧ ▸ Z)
ρΘ : Shape → Row
ρΘ Θ = shapeR (obj 0 ∷ []) Θ [] (obj 1)

-- (GB-cut) at dimension 0 has gap 2 and mode inv; at dimension n + 1
-- every gap g ≤ 2 and either mode is allowed.
cutT : Shape → Tmpl
cutT Θ = tmpl (ρΘ Θ) 2 inv zero

dcutT : Shape → Nat → Mode → Nat → Tmpl
dcutT Θ g m n = tmpl (ρΘ Θ) g m (suc n)

shape-ok-cut : ∀ Θ → T (okT (cutT Θ))
shape-ok-cut Θ = tt

shape-ok-dcut : ∀ Θ g m n → T (leq g 2) → T (okT (dcutT Θ g m n))
shape-ok-dcut Θ g m n le = le

module AtTemplate (t : Tmpl) (ok : T (okT t)) where
  shape-adm-c : Admissible (ctx t) (cgoal t)
  shape-adm-c = adm-c t ok refl refl

  shape-adm-ε : Admissible (ctx t) (egoal t)
  shape-adm-ε = adm-ε t ok refl refl

  shape-admit-c : T (admit? (ctx t) (cgoal t))
  shape-admit-c = admit?-complete shape-adm-c

  shape-admit-ε : T (admit? (ctx t) (egoal t))
  shape-admit-ε = admit?-complete shape-adm-ε

  shape-typed : T (wtGoal (ctx t) (cgoal t)) × T (wf (ctx t) (egoal t))
  shape-typed = templates-typed t ok

-- r is typed at every level of the tower
shape-rmap : ∀ L Θ R Z g m n Γ k x →
             infer Γ x ≡ just (tyU (tmpl (shapeR L Θ R Z) g m n) k) →
             infer Γ (rmap (shapeR L Θ R Z) x) ≡ just (tyRU (tmpl (shapeR L Θ R Z) g m n) k)
shape-rmap L Θ R Z g m n = infer-rmap (tmpl (shapeR L Θ R Z) g m n)

-- the module above, instantiated at the canonical templates: literally
-- every Θ, every gap g ≤ 2, mode and dimension
module AtCut (Θ : Shape) = AtTemplate (cutT Θ) (shape-ok-cut Θ)
module AtDcut (Θ : Shape) (g : Nat) (m : Mode) (n : Nat) (le : T (leq g 2)) =
  AtTemplate (dcutT Θ g m n) (shape-ok-dcut Θ g m n le)

shape-admit-cut : ∀ Θ → T (admit? (ctx (cutT Θ)) (cgoal (cutT Θ)))
shape-admit-cut Θ = AtCut.shape-admit-c Θ

shape-typed-dcut : ∀ Θ g m n (le : T (leq g 2)) →
  T (wtGoal (ctx (dcutT Θ g m n)) (cgoal (dcutT Θ g m n))) × T (wf (ctx (dcutT Θ g m n)) (egoal (dcutT Θ g m n)))
shape-typed-dcut Θ g m n le = AtDcut.shape-typed Θ g m n le
