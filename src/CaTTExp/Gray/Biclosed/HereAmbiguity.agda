------------------------------------------------------------------------
-- The term `here` forgets the instance's premises (finding, ledger D7h).
--
-- In the paper (closed-structure.md F.7.4 §2) every biclosed rule "has
-- the shape of coh": its conclusion is a term c_{ρ,n}[σ], which records
-- the instance σ, including σ(b).  The Agda syntax instead writes an
-- instance as here (sY σ A): substitution pushes σ into the goal type
-- and keeps nothing else.  The goal c_{ρ,n} does not mention b, so the
-- instance term of c does not depend on σ(b).
--
-- Witness.  Left evaluation row (Φ = X), n = 0: the template context is
-- (b : (A, X ▸ C)), the goal c is here (X ▸ A\C), and the goal ε is an
-- invertible cell r(here (X ▸ A\C)) ⊨ b.  In Γ = (b₁ b₂ : (A, X ▸ C)),
-- the instances b ↦ b₁ and b ↦ b₂ are both kernel instances (KInst,
-- hence AdmI).  Their ε-types have the *same* source term
-- r(here (X ▸ A\C)) and the targets b₁ and b₂.  So under any reading in
-- which a term has one denotation and ⊨ relates only isomorphic
-- operations, the two hypotheses b₁, b₂ are forced to be isomorphic,
-- which fails in the intended model (two non-isomorphic maps).  A
-- denotation of `here` has to depend on the derivation, not on the
-- term.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.HereAmbiguity where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates
open import CaTTExp.Gray.Biclosed.Subst
open import CaTTExp.Gray.Biclosed.SortDisc using (KInst; kinst-ε; DSub)

-- left evaluation, Φ = (X), with A = obj 0, X = obj 1, C = obj 2
ρ : Row
ρ = evLR (obj 1 ∷ []) (obj 0) (obj 2)

t₀ : Tmpl
t₀ = tmpl ρ 1 inv 0

ok₀ : T (okT t₀)
ok₀ = tt

BTy : CTy
BTy = op ((obj 0 ∷ obj 1 ∷ []) ▸ obj 2)

-- the template context is a single b of type B
ctx-t₀ : ctx t₀ ≡ BTy ∷ []
ctx-t₀ = refl

Γ : Ctx
Γ = BTy ∷ BTy ∷ []

σ₁ σ₂ : Sub
σ₁ = sub obj (λ _ → var 0)
σ₂ = sub obj (λ _ → var 1)

private
  typed : ∀ k → lookup Γ k ≡ just BTy → Γ ⊢ sub obj (λ _ → var k) ∶ ctx t₀
  typed k e = ⊢in λ { zero A refl → e ; (suc i) A () }

σ₁-typed : Γ ⊢ σ₁ ∶ ctx t₀
σ₁-typed = typed 0 refl

σ₂-typed : Γ ⊢ σ₂ ∶ ctx t₀
σ₂-typed = typed 1 refl

-- the data variable of the template is C = obj 2; both σ fix it
private
  dsub : ∀ k → DSub (2 ∷ []) (2 ∷ []) (sub obj (λ _ → var k))
  dsub k _ here!       = tt , λ { j refl → here! }
  dsub k _ (there! ())

ε₁ : KInst (2 ∷ []) Γ (sY σ₁ (egoal t₀))
ε₁ = kinst-ε t₀ ok₀ σ₁ σ₁-typed (dsub 0) refl

ε₂ : KInst (2 ∷ []) Γ (sY σ₂ (egoal t₀))
ε₂ = kinst-ε t₀ ok₀ σ₂ σ₂-typed (dsub 1) refl

-- the instance term of c is the same for both
same-c : sT σ₁ (here (cgoal t₀)) ≡ sT σ₂ (here (cgoal t₀))
same-c = refl

-- both ε-types: one source, two targets
src : Tm
src = rmap ρ (here (cgoal t₀))

ε₁-type : sY σ₁ (egoal t₀) ≡ hom inv 2 BTy src (var 0)
ε₁-type = refl

ε₂-type : sY σ₂ (egoal t₀) ≡ hom inv 2 BTy src (var 1)
ε₂-type = refl

-- and the two targets are different terms
targets-differ : var 0 ≡ var 1 → ⊥
targets-differ ()
