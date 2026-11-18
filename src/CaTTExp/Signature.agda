------------------------------------------------------------------------
-- A signature of closed constants for CaTT.
--
-- `ty k` is the type of constant k, and `Valid k` is the side condition
-- under which k may be used. Nothing here requires `ty k` to be well
-- formed in ε; presupposition lemmas (Γ ⊢ t : A implies Γ ⊢ A) need that
-- as an extra hypothesis on the signature. Pure CaTT uses the empty signature. A
-- signature whose constants are the cells of a computad gives "CaTT
-- over that computad".
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Syntax as Syntax

module CaTTExp.Signature where

record Signature : Set₁ where
  field
    K         : Set
    _==K_     : K → K → Bool
    ==K-sound : ∀ k l → T (k ==K l) → k ≡ l
    ty        : K → Syntax.Ty K
    Valid     : K → Set
    -- Validity must be decidable, so the checker can decide it.
    valid?    : (k : K) → Maybe (Valid k)

  open Syntax K public
  open Equality _==K_ ==K-sound public
