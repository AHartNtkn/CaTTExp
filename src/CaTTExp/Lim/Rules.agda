------------------------------------------------------------------------
-- Mikhail's recognition judgments for cones, Gray shapes and conical
-- transfors (arXiv 2412.13310v2, §3.1, §4.1, §4.2, restated in
-- Def. 4.15), over named contexts.
--
--   Cone Γ c Π      :  Γ, c : Ob, Π  cone (Γ; c)            (EK), (KE)
--   Gray1 / PGray1  :  M₁; M₂; M₃  gray / pgray M₁           (n = 1)
--   Ctrf1 / PCtrf1  :  Γ; c : Ob; M₁; M₂; M₃  ctrf / pctrf   (n = 1)
--
-- The gray and ctrf judgments are a schema in n; here they are the
-- instance n = 1 (natural transformations, resp. cone morphisms), which
-- is the instance the defects concern. They are parameterised by a
-- `Variant` recording the two places where the printed rule and its
-- repair differ:
--
--   copy   : the type given to the duplicate x′. Printed: "x′ : X",
--            i.e. X verbatim. Repaired: X with the earlier variables of
--            the block renamed to their duplicates.
--   srcVia : which boundary of an earlier connecting cell p the source
--            condition tests (y ∝ via(p)). Printed: τ. Repaired: σ.
--
-- Representation choices (not changes to the rules):
--  * Premises "K ⊢ s →_A t" are stated as well-formedness of the
--    conclusion context K, p : s →_A t (WfCtx), which also records that
--    the new name p is fresh. Rules that append to a middle block ask
--    for well-formedness of the whole resulting context.
--  * In `dup`, the duplicate's type is an index X′ with a premise
--    X′ ≡ copy …, so that derivations can be inverted by unification.
------------------------------------------------------------------------
module CaTTExp.Lim.Rules where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Conditions

------------------------------------------------------------------------
-- Cones (EK), (KE). These are the same in the printed and repaired
-- versions; the repair restricts which cone is used (Repaired.agda).

coneCtx : NCtx → Name → NCtx → NCtx
coneCtx Γ c Π = (Γ ▹ c ∶ ⋆) ⧺ Π

data Cone : NCtx → Name → NCtx → Set where
  EK : ∀ {c} → Cone ∅ c ∅
  KE : ∀ {Γ c Π x X p A s t} →
       Cone Γ c Π →
       WfCtx (coneCtx (Γ ▹ x ∶ X) c (Π ▹ p ∶ arr A s t)) →
       -- τCond‾(s : A, x : X, c : Ob, Π)
       T (condBar (coneCtx (Γ ▹ x ∶ X) c Π) τ s A x c (names Π)) →
       -- σCond(t : A, x : X, Π)
       T (cond (coneCtx (Γ ▹ x ∶ X) c Π) σ τ t A x (names Π)) →
       Cone (Γ ▹ x ∶ X) c (Π ▹ p ∶ arr A s t)

------------------------------------------------------------------------
-- Variants of the transfor rules.

record Variant : Set where
  field
    copy   : (Mold Mnew : NCtx) → Ty → Ty
    srcVia : Side

-- Rename the variables of one block to the positionally matching
-- variables of its duplicate block.
copyMap : NCtx → NCtx → Name → Name
copyMap ∅            _             n = n
copyMap (M ▹ _ ∶ _)  ∅             n = n
copyMap (M ▹ x ∶ _)  (M' ▹ x' ∶ _) n = if n ==ℕ x then x' else copyMap M M' n

printed : Variant
printed = record { copy = λ _ _ X → X ; srcVia = τ }

-- Only the copy is repaired: isolates the selector defect.
copyFixed : Variant
copyFixed = record { copy = λ M M' X → rnTy (copyMap M M') X ; srcVia = τ }

-- Both repairs.
fixed : Variant
fixed = record { copy = λ M M' X → rnTy (copyMap M M') X ; srcVia = σ }

------------------------------------------------------------------------
-- Gray shapes, n = 1:  M₁; M₂; M₃ gray M₁.

grayCtx : NCtx → NCtx → NCtx → NCtx
grayCtx M1 M2 M3 = (M1 ⧺ M2) ⧺ M3

module Gray (V : Variant) where
  open Variant V

  mutual
    data Gray1 : NCtx → NCtx → NCtx → Set where
      base  : Gray1 ∅ ∅ ∅
      close : ∀ {M1 M2 M3} → PGray1 M1 M2 M3 → T (size M1 ==ℕ size M3) →
              Gray1 M1 M2 M3

    data PGray1 : NCtx → NCtx → NCtx → Set where
      newv : ∀ {M1 M2 M3 x X} → Gray1 M1 M2 M3 →
             WfCtx (grayCtx (M1 ▹ x ∶ X) M2 M3) →
             PGray1 (M1 ▹ x ∶ X) M2 M3
      dup  : ∀ {M1 M2 M3 x X x' X' p A s t} →
             PGray1 (M1 ▹ x ∶ X) M2 M3 →
             T (size M1 ==ℕ size M2) →
             X' ≡ copy M1 M2 X →
             WfCtx (grayCtx (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t)) →
             -- τCond(s : A, x : X, M₃)
             T (cond (grayCtx (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) τ srcVia s A x (names M3)) →
             -- σCond(t : A, x′ : X, M₃)
             T (cond (grayCtx (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) σ τ t A x' (names M3)) →
             PGray1 (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t)

------------------------------------------------------------------------
-- Conical transfors, n = 1:  Γ; c : Ob; M₁; M₂; M₃ ctrf (Γ; c).

ctrfCtx : NCtx → Name → NCtx → NCtx → NCtx → NCtx
ctrfCtx Γ c M1 M2 M3 = ((coneCtx Γ c M1) ⧺ M2) ⧺ M3

module Ctrf (V : Variant) where
  open Variant V

  mutual
    data Ctrf1 : NCtx → Name → NCtx → NCtx → NCtx → Set where
      base  : ∀ {c} → Ctrf1 ∅ c ∅ ∅ ∅
      close : ∀ {Γ c M1 M2 M3} → PCtrf1 Γ c M1 M2 M3 → T (size M1 ==ℕ size M3) →
              Ctrf1 Γ c M1 M2 M3

    data PCtrf1 : NCtx → Name → NCtx → NCtx → NCtx → Set where
      newv : ∀ {Γ c M1 M2 M3 x X p P} →
             Ctrf1 Γ c M1 M2 M3 →
             Cone (Γ ▹ x ∶ X) c (M1 ▹ p ∶ P) →
             WfCtx (ctrfCtx (Γ ▹ x ∶ X) c (M1 ▹ p ∶ P) M2 M3) →
             PCtrf1 (Γ ▹ x ∶ X) c (M1 ▹ p ∶ P) M2 M3
      dup  : ∀ {Γ c M1 M2 M3 x X x' X' p A s t} →
             PCtrf1 Γ c (M1 ▹ x ∶ X) M2 M3 →
             T (size M1 ==ℕ size M2) →
             X' ≡ copy M1 M2 X →
             WfCtx (ctrfCtx Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t)) →
             -- τCond(s : A, x : X, FV(M₃))
             T (cond (ctrfCtx Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) τ srcVia s A x (names M3)) →
             -- σCond(t : A, x′ : X, FV(M₃))
             T (cond (ctrfCtx Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) σ τ t A x' (names M3)) →
             PCtrf1 Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t)

------------------------------------------------------------------------
-- Certified recognisers: every `just` carries a derivation. (They are
-- not proved complete; negative results are proved by inversion.)

private
  decTy : (A B : Ty) → Maybe (A ≡ B)
  decTy A B = go (A ==Ty B) (==Ty-sound A B)
    where
    go : (b : Bool) → (T b → A ≡ B) → Maybe (A ≡ B)
    go true  f = just (f tt)
    go false _ = nothing

  _<|>_ : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
  just x  <|> _ = just x
  nothing <|> m = m

cone? : (Γ : NCtx) (c : Name) (Π : NCtx) → Maybe (Cone Γ c Π)
cone? ∅ c ∅ = just EK
cone? (Γ ▹ x ∶ X) c (Π ▹ p ∶ arr A s t) =
  cone? Γ c Π >>= λ d →
  wf? _ >>= λ w →
  guard (condBar (coneCtx (Γ ▹ x ∶ X) c Π) τ s A x c (names Π)) λ h₁ →
  guard (cond (coneCtx (Γ ▹ x ∶ X) c Π) σ τ t A x (names Π)) λ h₂ →
  just (KE d w h₁ h₂)
cone? _ _ _ = nothing

module GrayCheck (V : Variant) where
  open Variant V
  open Gray V

  mutual
    gray? : (M1 M2 M3 : NCtx) → Maybe (Gray1 M1 M2 M3)
    gray? ∅ ∅ ∅ = just base
    gray? M1 M2 M3 =
      pgray? M1 M2 M3 >>= λ d → guard (size M1 ==ℕ size M3) λ e → just (close d e)

    pgray? : (M1 M2 M3 : NCtx) → Maybe (PGray1 M1 M2 M3)
    pgray? M1 M2 M3 = tryDup M1 M2 M3 <|> tryNew M1 M2 M3

    tryDup : (M1 M2 M3 : NCtx) → Maybe (PGray1 M1 M2 M3)
    tryDup (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t) =
      pgray? (M1 ▹ x ∶ X) M2 M3 >>= λ d →
      guard (size M1 ==ℕ size M2) λ e →
      decTy X' (copy M1 M2 X) >>= λ q →
      wf? _ >>= λ w →
      guard (cond (grayCtx (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) τ srcVia s A x (names M3)) λ h₁ →
      guard (cond (grayCtx (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) σ τ t A x' (names M3)) λ h₂ →
      just (dup d e q w h₁ h₂)
    tryDup _ _ _ = nothing

    tryNew : (M1 M2 M3 : NCtx) → Maybe (PGray1 M1 M2 M3)
    tryNew (M1 ▹ x ∶ X) M2 M3 =
      gray? M1 M2 M3 >>= λ d → wf? _ >>= λ w → just (newv d w)
    tryNew _ _ _ = nothing

module CtrfCheck (V : Variant) where
  open Variant V
  open Ctrf V

  mutual
    ctrf? : (Γ : NCtx) (c : Name) (M1 M2 M3 : NCtx) → Maybe (Ctrf1 Γ c M1 M2 M3)
    ctrf? ∅ c ∅ ∅ ∅ = just base
    ctrf? Γ c M1 M2 M3 =
      pctrf? Γ c M1 M2 M3 >>= λ d → guard (size M1 ==ℕ size M3) λ e → just (close d e)

    pctrf? : (Γ : NCtx) (c : Name) (M1 M2 M3 : NCtx) → Maybe (PCtrf1 Γ c M1 M2 M3)
    pctrf? Γ c M1 M2 M3 = tryDup Γ c M1 M2 M3 <|> tryNew Γ c M1 M2 M3

    tryDup : (Γ : NCtx) (c : Name) (M1 M2 M3 : NCtx) → Maybe (PCtrf1 Γ c M1 M2 M3)
    tryDup Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') (M3 ▹ p ∶ arr A s t) =
      pctrf? Γ c (M1 ▹ x ∶ X) M2 M3 >>= λ d →
      guard (size M1 ==ℕ size M2) λ e →
      decTy X' (copy M1 M2 X) >>= λ q →
      wf? _ >>= λ w →
      guard (cond (ctrfCtx Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) τ srcVia s A x (names M3)) λ h₁ →
      guard (cond (ctrfCtx Γ c (M1 ▹ x ∶ X) (M2 ▹ x' ∶ X') M3) σ τ t A x' (names M3)) λ h₂ →
      just (dup d e q w h₁ h₂)
    tryDup _ _ _ _ _ = nothing

    tryNew : (Γ : NCtx) (c : Name) (M1 M2 M3 : NCtx) → Maybe (PCtrf1 Γ c M1 M2 M3)
    tryNew (Γ ▹ x ∶ X) c (M1 ▹ p ∶ P) M2 M3 =
      ctrf? Γ c M1 M2 M3 >>= λ d →
      cone? (Γ ▹ x ∶ X) c (M1 ▹ p ∶ P) >>= λ k →
      wf? _ >>= λ w → just (newv d k w)
    tryNew _ _ _ _ _ = nothing
