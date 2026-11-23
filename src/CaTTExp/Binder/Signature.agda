------------------------------------------------------------------------
-- A signature for CaTT with binding formers (spec §1.6): closed
-- constants as in CaTTExp.Signature, plus a set B of binding formers
-- with a *binder interface*. A binder occurrence `bnd b y Δ ts` is
-- typed by three syntactic functions of the former b, the selector y
-- and the telescope Δ:
--
--   bside b y Δ   its decidable side condition (for INIT: positivity);
--   bargs b y Δ   the telescope its arguments ts must inhabit, written
--                 locally nameless (bvar 0 j is the j-th argument);
--   bres  b y Δ   its type, in which bvar 0 j is the j-th argument.
--
-- Like the coh rule's side condition, these see only the binder's own
-- data, never the context it is used in. CaTTExp.Binder.Subst states
-- the stability laws they need (`BinderLaws`); every other result
-- (checker, completeness) holds for any interface.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax

module CaTTExp.Binder.Signature where

record Signature : Set₁ where
  field
    K         : Set
    _==K_     : K → K → Bool
    ==K-sound : ∀ k l → T (k ==K l) → k ≡ l
    B         : Set
    _==B_     : B → B → Bool
    ==B-sound : ∀ b c → T (b ==B c) → b ≡ c
    ty        : K → Syntax.Ty K B
    Valid     : K → Set
    valid?    : (k : K) → Maybe (Valid k)
    -- The binder interface.
    bside     : B → Nat → Syntax.Ctx K B → Bool
    bargs     : B → Nat → Syntax.Ctx K B → Syntax.Ctx K B
    bres      : B → Nat → Syntax.Ctx K B → Syntax.Ty K B

  open Syntax K B public
  open Equality _==K_ ==K-sound _==B_ ==B-sound public
