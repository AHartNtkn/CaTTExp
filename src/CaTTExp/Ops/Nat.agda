------------------------------------------------------------------------
-- The recursor of the natural numbers as declared operations (ledger
-- F9, notes/ordinary-math.md §4, route II's `rec`, which is a rule
-- because it is not derivable from R-A and limits: §4.5).
--
-- Signature: ⊤, N : ⋆, zero : ⊤ → N, succ : N → N.
-- Generic context RC = (A : ⋆, a : ⊤ → A, f : A → A), and over it:
--   rec  : N → A
--   recZ : zero ; rec ⇒ a
--   recS : succ ; rec ⇒ rec ; f
-- Generic context RU = RC, h : N → A, hz : zero ; h ⇒ a,
-- hs : succ ; h ⇒ h ; f, and over it the uniqueness cells
--   uniq : h ⇒ rec      uniq⁻ : rec ⇒ h
-- (composition is diagrammatic: f ; g is "f then g").
--
-- Parameters come by substitution: rec[σ] is the recursor for the
-- data σ(A), σ(a), σ(f), which may be any terms of any context, so the
-- rule holds over every parameter context at once. No definitional
-- equation is added: recZ and recS are cells. Higher uniqueness (cells
-- between two uniqueness cells, …) is not declared here; for a set A it
-- is T-fill (CaTTExp.Trunc).
------------------------------------------------------------------------
module CaTTExp.Ops.Nat where

open import CaTTExp.Prelude
open import CaTTExp.Signature

data NK : Set where
  top nat zer suc′ : NK

_==NK_ : NK → NK → Bool
top  ==NK top  = true
nat  ==NK nat  = true
zer  ==NK zer  = true
suc′ ==NK suc′ = true
_    ==NK _    = false

==NK-sound : ∀ k l → T (k ==NK l) → k ≡ l
==NK-sound top  top  _ = refl
==NK-sound nat  nat  _ = refl
==NK-sound zer  zer  _ = refl
==NK-sound suc′ suc′ _ = refl
==NK-sound top  nat  ()
==NK-sound top  zer  ()
==NK-sound top  suc′ ()
==NK-sound nat  top  ()
==NK-sound nat  zer  ()
==NK-sound nat  suc′ ()
==NK-sound zer  top  ()
==NK-sound zer  nat  ()
==NK-sound zer  suc′ ()
==NK-sound suc′ top  ()
==NK-sound suc′ nat  ()
==NK-sound suc′ zer  ()

open import CaTTExp.Syntax NK using (Ty; Tm; Ctx; Sub; ⋆; arr; var; coh; cst; ε; _▸_; ⟨⟩; _,ₛ_)

tyN : NK → Ty
tyN top  = ⋆
tyN nat  = ⋆
tyN zer  = arr ⋆ (cst top) (cst nat)
tyN suc′ = arr ⋆ (cst nat) (cst nat)

ℕsig : Signature
ℕsig = record
  { K = NK ; _==K_ = _==NK_ ; ==K-sound = ==NK-sound
  ; ty = tyN ; Valid = λ _ → ⊤ ; valid? = λ _ → just tt }

open Signature ℕsig hiding (Ty; Tm; Ctx; Sub; ⋆; arr; var; coh; cst; ε; _▸_; ⟨⟩; _,ₛ_)

------------------------------------------------------------------------
-- Syntax helpers.

v : Nat → Tm
v = var

𝟙 N Z S : Tm
𝟙 = cst top ; N = cst nat ; Z = cst zer ; S = cst suc′

⟪_⟫ : List Tm → Sub
⟪ ts ⟫ = go ⟨⟩ ts
  where
  go : Sub → List Tm → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ t) ts

-- Diagrammatic composite f ; g of f : x → y, g : y → z.
Comp₂ : Ctx
Comp₂ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ ⋆ ▸ arr ⋆ (v 1) (v 3)

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh Comp₂ (arr ⋆ (v 0) (v 3)) ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

------------------------------------------------------------------------
-- The generic contexts and the declared operations.

RC : Ctx
RC = ε ▸ ⋆ ▸ arr ⋆ 𝟙 (v 0) ▸ arr ⋆ (v 0) (v 0)

private
  A a f : Tm
  A = v 0 ; a = v 1 ; f = v 2

recTy : Ty
recTy = arr ⋆ N A

-- rec over the variables of RC (they keep their indices in RU).
rec₀ : Tm
rec₀ = coh RC recTy ⟪ A ∷ a ∷ f ∷ [] ⟫

recZTy recSTy : Ty
recZTy = arr (arr ⋆ 𝟙 A) (comp 𝟙 N Z A rec₀) a
recSTy = arr (arr ⋆ N A) (comp N N S A rec₀) (comp N A rec₀ A f)

RU : Ctx
RU = RC ▸ arr ⋆ N A
        ▸ arr (arr ⋆ 𝟙 A) (comp 𝟙 N Z A (v 3)) a
        ▸ arr (arr ⋆ N A) (comp N N S A (v 3)) (comp N A (v 3) A f)

uniqTy uniq⁻Ty : Ty
uniqTy  = arr (arr ⋆ N A) (v 3) rec₀
uniq⁻Ty = arr (arr ⋆ N A) rec₀ (v 3)

ops : List (Σ Ctx (λ _ → Ty))
ops = (RC , recTy) ∷ (RC , recZTy) ∷ (RC , recSTy) ∷ (RU , uniqTy) ∷ (RU , uniq⁻Ty) ∷ []

open import CaTTExp.Ops.Check ℕsig ops public
import CaTTExp.Ops.Subst ℕsig ops as OS
open import CaTTExp.Typing ℕsig using (cattSide)
import CaTTExp.Subst ℕsig cattSide as S0

------------------------------------------------------------------------
-- The hypotheses of the substitution theorem hold.

closedN : S0.Closed
closedN top  = tt
closedN nat  = tt
closedN zer  = tt , tt , tt
closedN suc′ = tt , tt , tt

opsScoped : OS.OpsScoped
opsScoped here                                 = _ , _
opsScoped (there here)                         = _ , _
opsScoped (there (there here))                 = _ , _
opsScoped (there (there (there here)))         = _ , _
opsScoped (there (there (there (there here)))) = _ , _

-- So substitution is admissible: every instance of the recursor in any
-- context is well typed.
tm[] = OS.tm[] closedN opsScoped

------------------------------------------------------------------------
-- The operations, applied.

rec : Tm → Tm → Tm → Tm
rec A a f = coh RC recTy ⟪ A ∷ a ∷ f ∷ [] ⟫

recZ recS : Tm → Tm → Tm → Tm
recZ A a f = coh RC recZTy ⟪ A ∷ a ∷ f ∷ [] ⟫
recS A a f = coh RC recSTy ⟪ A ∷ a ∷ f ∷ [] ⟫

uniq : Tm → Tm → Tm → Tm → Tm → Tm → Tm
uniq A a f h hz hs = coh RU uniqTy ⟪ A ∷ a ∷ f ∷ h ∷ hz ∷ hs ∷ [] ⟫

------------------------------------------------------------------------
-- Every declaration is well formed: its context is a context and its
-- type a type in it (checked once, by the certified checker).

wfOp : Σ Ctx (λ _ → Ty) → Bool
wfOp (Δ , B) = is-just (checkCtx Δ >>= λ w → checkTy Δ w B)

allWf : List (Σ Ctx (λ _ → Ty)) → Bool
allWf []       = true
allWf (o ∷ os) = wfOp o ∧ allWf os

_ : allWf ops ≡ true
_ = refl
