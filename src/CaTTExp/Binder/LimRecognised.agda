------------------------------------------------------------------------
-- The cone shape of the kernel's limit heads is Mikhail's specified
-- cone, recognised by his rules (ledger S27 (h)).
--
-- CaTTExp.Lim.Rules formalises Mikhail's recognition judgments for
-- cones over named contexts, and CaTTExp.Lim.Repaired the repair R1
-- that the spec adopted (§6.1): the cone is *specified* by a fixed
-- construction (`coneC`, Mikhail's Thm 3.3, globular diagrams of
-- every dimension), and that specified cone passes the recognition rules
-- (`SpecCone`). The kernel's limit heads (CaTTExp.Binder.LimHeads) take
-- the specified cone of CaTTExp.Cones as their shape (`coneShape`).
--
-- Here the two meet: on the diagrams of Lim/Defects and Lim/Repaired
-- (the arrow, the loop, and Mikhail's Example 4.1 with a 2-cell), the
-- full cone context Γ, c, coneC Γ c lowered to de Bruijn levels is
-- exactly `coneShape` of the lowered diagram. So on those diagrams the
-- types of the universal cone's cells λ_{Γ,g} are the types of a cone
-- that Mikhail's rules recognise (`recognised-*`). The agreement holds
-- for every well-formed globular diagram, in every dimension (`agrees`,
-- from CaTTExp.Lim.ConeAgree, S27 (h′)); recognition by the rules is
-- checked on the three diagrams only.
------------------------------------------------------------------------
module CaTTExp.Binder.LimRecognised where

open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Rules
open import CaTTExp.Lim.Repaired
open import CaTTExp.Lim.Defects using (Γarr; Parr; Γloop; Πcanonical)
open import CaTTExp.Binder.LimHeadsExamples using (coneShape)
open import CaTTExp.Lim.ConeAgree using (gwf; named; cone-agrees)

-- The specified cone context Γ, c, coneC Γ c, at de Bruijn levels.
specified : NCtx → Name → Maybe P.Ctx
specified Γ c = coneC Γ c >>= λ Π → lower (coneCtx Γ c Π)

-- It is the kernel's cone shape.
arr-agrees : specified Γarr 3 ≡ (lower Γarr >>= coneShape)
arr-agrees = refl

loop-agrees : specified Γloop 3 ≡ (lower Γloop >>= coneShape)
loop-agrees = refl

ex41-agrees : specified Γ41 5 ≡ (lower Γ41 >>= coneShape)
ex41-agrees = refl

-- And it is recognised by Mikhail's cone rules.
recognised-arr : SpecCone Γarr 3 Parr
recognised-arr = spec refl (from-just (cone? Γarr 3 Parr))

recognised-loop : SpecCone Γloop 3 Πcanonical
recognised-loop = canonical-accepted

recognised-41 : SpecCone Γ41 5 (from-just (coneC Γ41 5))
recognised-41 = cone41

-- In general: every well-formed globular diagram, in every dimension,
-- named canonically, with apex the next name.
agrees : ∀ Γ → T (gwf Γ) →
         specified (named Γ) (P.len Γ) ≡ (lower (named Γ) >>= coneShape)
agrees = cone-agrees
