------------------------------------------------------------------------
-- INIT over any binder-free signature: the extension of a signature 𝕊₀
-- of CaTTExp.Signature by INIT's formers is, definitionally, INIT's
-- signature over the base 𝕊₀ (`same`), and CaTT with INIT is
-- conservative over CaTT with 𝕊₀ (CaTTExp.Binder.Embed.CaTT).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Embed

module CaTTExp.Binder.InitEmbed
  (𝕊₀ : Old.Signature)
  -- Which constants of 𝕊₀ are the terminal object ⊤.
  (top? : Old.Signature.K 𝕊₀ → Bool)
  where

open Old.Signature 𝕊₀

initBinders : Binders K
initBinders = record
  { B         = Former
  ; _==B_     = _==F_
  ; ==B-sound = ==F-sound
  ; bside     = Construction.side K top?
  ; bargs     = Construction.args K top?
  ; bres      = Construction.res K top?
  }

initBase : Base
initBase = record
  { K         = K
  ; _==K_     = _==K_
  ; ==K-sound = ==K-sound
  ; ty        = λ k → Emb.eTy K Former (ty k)
  ; Valid     = Valid
  ; valid?    = valid?
  ; top?      = top?
  }

same : initSig initBase ≡ extend 𝕊₀ initBinders
same = refl

open CaTT 𝕊₀ initBinders public
