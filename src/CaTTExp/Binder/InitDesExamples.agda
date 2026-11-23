------------------------------------------------------------------------
-- INIT beside DES (CaTTExp.Binder.InitDes): INIT's cells are inv, so
-- their inverses are well typed. Every statement is `refl`, by the
-- certified checker (CaTTExp.Binder.CheckWith) with the Gray mark
-- judgment of CaTTExp.Gray.MarksB (INIT's and DES's former marks) as
-- the kernel's mark parameter, and plain CaTT's coh side condition
-- (INIT's result types contain coherences on binder terms, which L's
-- side condition on binder syntax, `graySideD`, does not erase).
--
-- On ℕ = μ(X, z : ⊤ → X, s : X → X) with a model (A, a, f):
--  * rec_z and rec_s are inv, rec is not;
--  * the left and right inverses of rec_z and rec_s, and their unit
--    cells, are accepted; rec has no inverse (rejected);
--  * over the arguments of uni: uni and uni_s are inv, and their left
--    inverses are accepted.
-- Marks of μ and η: with s marked inv in the telescope, η_s is inv; in
-- the circle with X : grpd₁, μ carries grpd₁.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Syntax as OSyn
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.InitDes

module CaTTExp.Binder.InitDesExamples where

data NK : Set where
  ⊤c : NK

𝕊₀ : Old.Signature
𝕊₀ = record
  { K         = NK
  ; _==K_     = λ _ _ → true
  ; ==K-sound = λ { ⊤c ⊤c _ → refl }
  ; ty        = λ _ → OSyn.⋆
  ; Valid     = λ _ → ⊤
  ; valid?    = λ _ → just tt
  }

open Over 𝕊₀ (λ _ → true)
open import CaTTExp.Binder.Signature
open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.CheckWith 𝕊 cattSide mark

X : Tm
X = bvar 0 0

one : Tm
one = cst ⊤c

ok : ∀ {a} {A : Set a} → Maybe A → Bool
ok = is-just

-- ℕ, and a model (A, a : ⊤ → A, f : A → A).
Δℕ : Ctx
Δℕ = ε ▸ ⋆ ▸ arr ⋆ one X ▸ arr ⋆ X X

Γm : Ctx
Γm = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr ⋆ (var 0) (var 0)

recℕ rz rs : Tm
recℕ = bnd (ini rec) 0 Δℕ (fresh 0 3)
rz   = bnd (ini recY) 1 Δℕ (fresh 0 3)
rs   = bnd (ini recY) 2 Δℕ (fresh 0 3)

-- The boundary of a type, as arguments of a disk.
sph : Ty → Sub
sph ⋆           = ⟨⟩
sph (arr A u v) = sph A ,ₛ u ,ₛ v

-- The destructor of kind k on t, at t's dimension.
desOn : Ctx → DesKind → Tm → Maybe Tm
desOn Γ k t = infer Γ t >>= λ r → just (bnd (dz (des k (dim (fst r)))) 0 ε (sph (fst r) ,ₛ t))

accepts : Ctx → Maybe Tm → Bool
accepts Γ nothing  = false
accepts Γ (just u) = ok (infer Γ u)

allKinds : Ctx → Tm → List Bool
allKinds Γ t = accepts Γ (desOn Γ linvK t) ∷ accepts Γ (desOn Γ rinvK t) ∷
               accepts Γ (desOn Γ unitLK t) ∷ accepts Γ (desOn Γ unitRK t) ∷ []

-- rec_z, rec_s are inv; rec is not.
_ : (mark Γm minv rz ∷ mark Γm minv rs ∷ mark Γm minv recℕ ∷ []) ≡ (true ∷ true ∷ false ∷ [])
_ = refl

-- Their inverses and unit cells are well typed; rec⁻ˡ is rejected.
_ : (allKinds Γm rz ∷ allKinds Γm rs ∷ []) ≡ ((true ∷ true ∷ true ∷ true ∷ []) ∷ (true ∷ true ∷ true ∷ true ∷ []) ∷ [])
_ = refl

_ : accepts Γm (desOn Γm linvK recℕ) ≡ false
_ = refl

-- uni and uni_s over uni's arguments: inv, with left inverses.
Γu : Ctx
Γu = openTel 0 (args (ini uni) 0 Δℕ)

un us : Tm
un = bnd (ini uni) 0 Δℕ (fresh 0 9)
us = bnd (ini uniY) 2 Δℕ (fresh 0 9)

_ : (mark Γu minv un ∷ mark Γu minv us ∷ accepts Γu (desOn Γu linvK un) ∷ accepts Γu (desOn Γu linvK us) ∷ [])
  ≡ (true ∷ true ∷ true ∷ true ∷ [])
_ = refl

-- Marks of μ and η are the telescope's: s marked inv gives η_s inv
-- (and z, unmarked, gives η_z not inv); X : grpd₁ gives μ grpd₁.
Δinv : Ctx
Δinv = ε ▸ ⋆ ▸ arr ⋆ one X ▸[ minv ∷ [] ] arr ⋆ X X

Δ○g : Ctx
Δ○g = ε ▸[ mgrpd 1 ∷ [] ] ⋆ ▸ arr ⋆ one X ▸ arr (arr ⋆ one X) (bvar 0 1) (bvar 0 1)

_ : (mark ε minv (bnd (ini η) 2 Δinv ⟨⟩) ∷ mark ε minv (bnd (ini η) 1 Δinv ⟨⟩) ∷
     mark ε (mgrpd 1) (bnd (ini μ) 0 Δ○g ⟨⟩) ∷ mark ε (mgrpd 1) (bnd (ini μ) 0 Δℕ ⟨⟩) ∷ [])
  ≡ (true ∷ false ∷ true ∷ false ∷ [])
_ = refl
