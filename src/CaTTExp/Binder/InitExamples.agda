------------------------------------------------------------------------
-- INIT examples, checked by the certified checker
-- (CaTTExp.Binder.CheckWith with plain CaTT's side condition).
--
-- Every statement below is `refl`: the checker, which is sound and
-- complete, accepts (or rejects) the term, so the term is (or is not)
-- derivable. Positive: ℕ with all six formers, and the circle (a cell
-- variable) with μ and η. Negative: the side condition (positivity and
-- the former's selection) rejects a non-⊤ parameter target, a second
-- object variable, a source mentioning X, rec_y at y = 0 or at a cell,
-- and uni on a signature with a cell.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Init

module CaTTExp.Binder.InitExamples where

data NK : Set where
  ⊤c : NK

base : Base
base = record
  { K         = NK
  ; _==K_     = λ _ _ → true
  ; ==K-sound = λ { ⊤c ⊤c _ → refl }
  ; ty        = λ _ → Syntax.⋆
  ; Valid     = λ _ → ⊤
  ; valid?    = λ _ → just tt
  ; top?      = λ _ → true
  }
  where import CaTTExp.Binder.Syntax NK Former as Syntax

𝕊 = initSig base

open import CaTTExp.Binder.Signature
open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide

X : Tm
X = bvar 0 0

one : Tm
one = cst ⊤c

-- ℕ := μ(X, z : ⊤ → X, s : X → X).
Δℕ : Ctx
Δℕ = ε ▸ ⋆ ▸ arr ⋆ one X ▸ arr ⋆ X X

-- A model in context: (A, z : ⊤ → A, s : A → A).
Γm : Ctx
Γm = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr ⋆ (var 0) (var 0)

sideOf : Former → Nat → Ctx → Bool
sideOf = Construction.side NK (λ _ → true)

-- Tuples of verdicts, compared at a fixed type.
B2 = Bool × Bool
B3 = Bool × Bool × Bool
B4 = Bool × Bool × Bool × Bool

_≡₂_ : B2 → B2 → Set
_≡₂_ = _≡_
_≡₃_ : B3 → B3 → Set
_≡₃_ = _≡_
_≡₄_ : B4 → B4 → Set
_≡₄_ = _≡_

ok : ∀ {a} {A : Set a} → Maybe A → Bool
ok = is-just

-- Result types, when the checker succeeds.
tyOf : Ctx → Tm → Maybe Ty
tyOf Γ t = infer Γ t >>= λ r → just (fst r)

t-μ   = tyOf ε (bnd μ 0 Δℕ ⟨⟩)
t-η1  = tyOf ε (bnd η 1 Δℕ ⟨⟩)
t-η2  = tyOf ε (bnd η 2 Δℕ ⟨⟩)
t-rec = tyOf Γm (bnd rec 0 Δℕ (fresh 0 3))
t-r1  = tyOf Γm (bnd recY 1 Δℕ (fresh 0 3))
t-r2  = tyOf Γm (bnd recY 2 Δℕ (fresh 0 3))

-- uni and uni_y: the context is the argument telescope opened.
Γu : Ctx
Γu = openTel 0 (Construction.args NK (λ _ → true) uni 0 Δℕ)

t-ctxu = ok (ctx? Γu)
t-uni  = tyOf Γu (bnd uni 0 Δℕ (fresh 0 9))
t-u1   = tyOf Γu (bnd uniY 1 Δℕ (fresh 0 9))
t-u2   = tyOf Γu (bnd uniY 2 Δℕ (fresh 0 9))

μℕ : Tm
μℕ = bnd μ 0 Δℕ ⟨⟩

_ : t-μ ≡ just ⋆
_ = refl

_ : t-η1 ≡ just (arr ⋆ one μℕ)
_ = refl

_ : t-η2 ≡ just (arr ⋆ μℕ μℕ)
_ = refl

_ : t-rec ≡ just (arr ⋆ μℕ (var 0))
_ = refl

_ : (ok t-r1 , ok t-r2) ≡₂ (true , true)
_ = refl

_ : (t-ctxu , ok t-uni , ok t-u1 , ok t-u2) ≡₄ (true , true , true , true)
_ = refl

------------------------------------------------------------------------
-- A cell variable: the circle (X, b : ⊤ → X, l : b ⇒ b).

Δ○ : Ctx
Δ○ = ε ▸ ⋆ ▸ arr ⋆ one X ▸ arr (arr ⋆ one X) (bvar 0 1) (bvar 0 1)

μ○ : Tm
μ○ = bnd μ 0 Δ○ ⟨⟩

_ : tyOf ε μ○ ≡ just ⋆
_ = refl

_ : tyOf ε (bnd η 1 Δ○ ⟨⟩) ≡ just (arr ⋆ one μ○)
_ = refl

_ : ok (tyOf ε (bnd η 2 Δ○ ⟨⟩)) ≡ true
_ = refl

-- rec into a model (A, a : ⊤ → A, p : a ⇒ a) is accepted; rec_y at the
-- cell and uni need the higher naturality data (S26a follow-up).
Γ○ : Ctx
Γ○ = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr (arr ⋆ one (var 0)) (var 1) (var 1)

_ : tyOf Γ○ (bnd rec 0 Δ○ (fresh 0 3)) ≡ just (arr ⋆ μ○ (var 0))
_ = refl

_ : ok (tyOf Γ○ (bnd recY 2 Δ○ (fresh 0 3))) ≡ false
_ = refl

_ : (sideOf recY 2 Δ○ , sideOf uni 0 Δ○ , sideOf uniY 1 Δ○) ≡₃ (false , false , false)
_ = refl

------------------------------------------------------------------------
-- Rejections by the side condition.

-- A map into a parameter that is not ⊤: (X, f : X → A) in context A.
Δbad₁ : Ctx
Δbad₁ = ε ▸ ⋆ ▸ arr ⋆ X (var 0)

_ : (sideOf μ 0 Δbad₁ , ok (tyOf (ε ▸ ⋆) (bnd μ 0 Δbad₁ ⟨⟩))) ≡₂ (false , false)
_ = refl

-- A second object variable.
Δbad₂ : Ctx
Δbad₂ = ε ▸ ⋆ ▸ ⋆

_ : (sideOf μ 0 Δbad₂ , ok (tyOf ε (bnd μ 0 Δbad₂ ⟨⟩))) ≡₂ (false , false)
_ = refl

-- A source mentioning X other than X itself: s : μ(Y, X → Y) → X.
Δbad₃ : Ctx
Δbad₃ = ε ▸ ⋆ ▸ arr ⋆ (bnd μ 0 (ε ▸ ⋆ ▸ arr ⋆ (bvar 1 0) (bvar 0 0)) ⟨⟩) X

_ : sideOf μ 0 Δbad₃ ≡ false
_ = refl

-- rec_y at y = 0, and η at y = 0.
_ : (sideOf recY 0 Δℕ , sideOf η 0 Δℕ) ≡₂ (false , false)
_ = refl

------------------------------------------------------------------------
-- The shapes of INIT-J1 and INIT-J2 on ℕ, in the model (A, z, s):
-- rec_y at s is the naturality cell  η_s ; rec ⇒ rec ; s,  and uni is
-- a cell between the two model morphisms of its arguments.

private
  cmpℕ : Tm → Tm → Tm → Tm → Tm → Tm
  cmpℕ = Construction.cmp NK (λ _ → true)

  recℕ : Tm
  recℕ = bnd rec 0 Δℕ (fresh 0 3)

_ : t-r2 ≡ just (arr (arr ⋆ μℕ (var 0))
                     (cmpℕ μℕ μℕ (var 0) (bnd η 2 Δℕ ⟨⟩) recℕ)
                     (cmpℕ μℕ (var 0) (var 0) recℕ (var 2)))
_ = refl

-- In Γu = (A, z, s, h, θ_z, θ_s, h′, θ′_z, θ′_s): uni is h ⇒ h′, and
-- uni_y at s is the modification condition, both sides from
-- η_s ; h to h′ ; s.
private
  module C = Construction NK (λ _ → true)
  uℕ : Tm
  uℕ = bnd uni 0 Δℕ (fresh 0 9)

_ : t-uni ≡ just (arr (arr ⋆ μℕ (var 0)) (var 3) (var 6))
_ = refl

_ : t-u2 ≡ just
      (let src = C.cmp μℕ μℕ (var 0) (bnd η 2 Δℕ ⟨⟩) (var 3)
           tgt = C.cmp μℕ (var 0) (var 0) (var 6) (var 2) in
       arr (arr (arr ⋆ μℕ (var 0)) src tgt)
           (C.vcomp μℕ (var 0) src (C.cmp μℕ μℕ (var 0) (bnd η 2 Δℕ ⟨⟩) (var 6))
                    (C.lwh μℕ μℕ (var 0) (bnd η 2 Δℕ ⟨⟩) (var 3) (var 6) uℕ) tgt (var 8))
           (C.vcomp μℕ (var 0) src (C.cmp μℕ (var 0) (var 0) (var 3) (var 2)) (var 5) tgt
                    (C.rwh μℕ (var 0) (var 0) (var 3) (var 6) uℕ (var 2))))
_ = refl
