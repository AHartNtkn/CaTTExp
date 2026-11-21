------------------------------------------------------------------------
-- D7h: the coherence term must record its instance (defect and repair).
--
-- In the paper (closed-structure.md F.7.4 §2) every biclosed rule "has
-- the shape of coh": its conclusion is a term c_{ρ,n}[σ] that records
-- the instance σ, including σ(b).  Until 2026-11-20 the Agda syntax
-- wrote an instance as `here (sY σ A)`: substitution pushed σ into the
-- goal type and kept nothing else.  The goal c does not mention b, so
-- the instance term of c did not depend on σ(b).
--
-- The defect (machine-checked against the old syntax in commit 014c1da
-- of this file).  Left evaluation row, Φ = (X), n = 0: the template
-- context is (b : (A, X ▸ C)).  In Γ = (b₁ b₂ : (A, X ▸ C)) the
-- instances b ↦ b₁ and b ↦ b₂ were both kernel instances (KInst), both
-- c terms were the one term here (X ▸ A\C), and the two ε types were
-- r(here (X ▸ A\C)) ⊨ b₁ and r(here (X ▸ A\C)) ⊨ b₂.  So no
-- interpretation giving each term one meaning could be sound: it would
-- make b₁ ≅ b₂ for all b₁, b₂.  The unit row adds a second ambiguity:
-- H = (⟦D⁰⟧, ⟦D⁰⟧ ▸ Z) has two unit rows with the same H and B.
--
-- The repair (Syntax, Typing): a coherence term is here t e φs ts, with
-- the template t, the goal e, and the instance as lists.  This module
-- checks the example again under the repaired syntax.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.HereAmbiguity where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing

-- left evaluation, Φ = (X), with A = obj 0, X = obj 1, C = obj 2
ρ : Row
ρ = evLR (obj 1 ∷ []) (obj 0) (obj 2)

t₀ : Tmpl
t₀ = tmpl ρ 1 inv 0

BTy : CTy
BTy = op ((obj 0 ∷ obj 1 ∷ []) ▸ obj 2)

HTy : CTy
HTy = op ((obj 1 ∷ []) ▸ (obj 0 \\ obj 2))

-- the template context is a single b of type B
ctx-t₀ : ctx t₀ ≡ BTy ∷ []
ctx-t₀ = refl

Γ : Ctx
Γ = BTy ∷ BTy ∷ []

φ₀ : List Fm
φ₀ = obj 0 ∷ obj 1 ∷ obj 2 ∷ []

-- the two curries, of b₁ and of b₂
c₁ c₂ : Tm
c₁ = here t₀ gc φ₀ (var 0 ∷ [])
c₂ = here t₀ gc φ₀ (var 1 ∷ [])

c₁-typed : infer Γ c₁ ≡ just HTy
c₁-typed = refl

c₂-typed : infer Γ c₂ ≡ just HTy
c₂-typed = refl

-- they are now different terms
c-differ : c₁ ≡ c₂ → ⊥
c-differ ()

-- and each ε has its own c in its source
ε₁-typed : infer Γ (here t₀ gε φ₀ (var 0 ∷ [])) ≡ just (hom inv 2 BTy (rmap ρ c₁) (var 0))
ε₁-typed = refl

ε₂-typed : infer Γ (here t₀ gε φ₀ (var 1 ∷ [])) ≡ just (hom inv 2 BTy (rmap ρ c₂) (var 1))
ε₂-typed = refl

-- the checker rejects instances that do not fit the template
reject-short : infer Γ (here t₀ gc φ₀ []) ≡ nothing
reject-short = refl

reject-type : infer Γ (here t₀ gc φ₀ (mP (obj 0) (obj 1) ∷ [])) ≡ nothing
reject-type = refl

-- a non-template (directed at n = 0) is rejected whatever the instance
reject-okT : infer Γ (here (tmpl ρ 1 dir 0) gc φ₀ (var 0 ∷ [])) ≡ nothing
reject-okT = refl
