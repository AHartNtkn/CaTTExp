------------------------------------------------------------------------
-- A rough pretty printer for raw terms, for reading off constructions
-- (used only for documentation; nothing depends on it).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Show where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

infixr 5 _<>_
_<>_ : String → String → String
_<>_ = primStringAppend

showTree : Tree → String
showTree t = go t
  where
  mutual
    go : Tree → String
    go (node []) = "•"
    go (node ts) = "(" <> gos ts <> ")"
    gos : List Tree → String
    gos []       = ""
    gos (t ∷ []) = go t
    gos (t ∷ ts) = go t <> " " <> gos ts

module _ (name : Nat → String) where
  shape : Ctx → String
  shape P with treeOf P
  ... | just t  = showTree t
  ... | nothing = "?"

  topsOf : Ctx → List Nat
  topsOf P with treeOf P
  ... | just t  = tops t
  ... | nothing = []

  mutual
    -- Fuel-bounded (only used for display).
    showTm′ : Nat → Tm → String
    showTm′ zero    _           = "…"
    showTm′ (suc k) (var i)     = name i
    showTm′ (suc k) (coh P A σ) = shape P <> "{" <> showTops k (topsOf P) σ <> "}"
    showTm′ (suc k) (cst ())

    showTops : Nat → List Nat → Sub → String
    showTops k []       σ = ""
    showTops k (n ∷ []) σ = showTm′ k (lookupₛ σ n)
    showTops k (n ∷ ns) σ = showTm′ k (lookupₛ σ n) <> ", " <> showTops k ns σ

  showTm : Tm → String
  showTm = showTm′ 64

  showTy : Ty → String
  showTy ⋆ = "⋆"
  showTy (arr A s t) = showTm s <> "  ⇒  " <> showTm t

