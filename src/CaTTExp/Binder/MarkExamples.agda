------------------------------------------------------------------------
-- Marked entries, checked by the certified checker with the mark
-- judgment of rule (MARK) only (CaTTExp.Binder.Typing, `varMark`).
--
-- A toy signature with one binding former `f` whose argument
-- telescope has one entry marked inv: f's argument must have the mark
-- inv. A variable has the marks of its entry, so `f(x)` is accepted
-- when x is marked inv and rejected when x is unmarked or marked ps.
-- Every statement is `refl`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Syntax as Syn

module CaTTExp.Binder.MarkExamples where

data F : Set where
  f : F

data K₀ : Set where

𝕊 : Signature
𝕊 = record
  { K         = K₀
  ; _==K_     = λ ()
  ; ==K-sound = λ ()
  ; B         = F
  ; _==B_     = λ _ _ → true
  ; ==B-sound = λ { f f _ → refl }
  ; ty        = λ ()
  ; Valid     = λ _ → ⊤
  ; valid?    = λ ()
  ; bside     = λ _ _ _ → true
  ; bargs     = λ _ _ _ → Syn.ε Syn.▸[ Syn.minv ∷ [] ] Syn.⋆
  ; bres      = λ _ _ _ → Syn.⋆
  }

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

fx : Tm
fx = bnd f 0 ε (⟨⟩ ,ₛ var 0)

accepts : Ctx → Bool
accepts Γ = is-just (infer Γ fx)

-- Marked contexts are well formed.
ctx-inv : is-just (ctx? (ε ▸[ minv ∷ [] ] ⋆)) ≡ true
ctx-inv = refl

-- x marked inv (possibly among other marks): accepted.
ok-inv : accepts (ε ▸[ minv ∷ [] ] ⋆) ≡ true
ok-inv = refl

ok-ps-inv : accepts (ε ▸[ mps ∷ minv ∷ [] ] ⋆) ≡ true
ok-ps-inv = refl

-- x unmarked, or marked ps only: rejected.
no-unmarked : accepts (ε ▸ ⋆) ≡ false
no-unmarked = refl

no-ps : accepts (ε ▸[ mps ∷ [] ] ⋆) ≡ false
no-ps = refl

-- A marked context is not a pasting context, so coh over it is
-- rejected: the identity coherence over (x : ⋆) is accepted, over
-- (x : ⋆ marked inv) it is not.
idOver : Ctx → Tm
idOver Δ = coh Δ (arr ⋆ (var 0) (var 0)) (⟨⟩ ,ₛ var 0)

coh-unmarked : is-just (infer (ε ▸ ⋆) (idOver (ε ▸ ⋆))) ≡ true
coh-unmarked = refl

coh-marked : is-just (infer (ε ▸ ⋆) (idOver (ε ▸[ minv ∷ [] ] ⋆))) ≡ false
coh-marked = refl
