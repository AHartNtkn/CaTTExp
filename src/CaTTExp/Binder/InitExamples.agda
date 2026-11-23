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
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

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

-- rec into a model (A, a : ⊤ → A, p : a ⇒ a), its cells at b and at
-- the 2-cell l (a 3-cell), and uni and uni_y at b, are accepted.
Γ○ : Ctx
Γ○ = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr (arr ⋆ one (var 0)) (var 1) (var 1)

rec○ : Tm
rec○ = bnd rec 0 Δ○ (fresh 0 3)

_ : tyOf Γ○ rec○ ≡ just (arr ⋆ μ○ (var 0))
_ = refl

_ : (ok (tyOf Γ○ (bnd recY 1 Δ○ (fresh 0 3))) , ok (tyOf Γ○ (bnd recY 2 Δ○ (fresh 0 3)))) ≡₂ (true , true)
_ = refl

-- rec_y at l: the naturality cylinder (η_l ▷ rec) · θ_b ⇛ θ_b · (1 ◁ p).
private
  module C○ = Construction NK (λ _ → true)
  ηb ηl θb : Tm
  ηb = bnd η 1 Δ○ ⟨⟩
  ηl = bnd η 2 Δ○ ⟨⟩
  θb = bnd recY 1 Δ○ (fresh 0 3)

_ : tyOf Γ○ (bnd recY 2 Δ○ (fresh 0 3)) ≡ just
      (let i1  = C○.idm one
           src = C○.cmp one μ○ (var 0) ηb rec○
           tgt = C○.cmp one one (var 0) i1 (var 1) in
       arr (arr (arr ⋆ one (var 0)) src tgt)
           (C○.vcomp one (var 0) src src (C○.rwh one μ○ (var 0) ηb ηb ηl rec○) tgt θb)
           (C○.vcomp one (var 0) src (C○.cmp one one (var 0) i1 (var 1)) θb tgt
                     (C○.lwh one one (var 0) i1 (var 1) (var 1) (var 2))))
_ = refl

Γu○ : Ctx
Γu○ = openTel 0 (Construction.args NK (λ _ → true) uni 0 Δ○)

_ : (ok (ctx? Γu○) , ok (tyOf Γu○ (bnd uni 0 Δ○ (fresh 0 9))) , ok (tyOf Γu○ (bnd uniY 1 Δ○ (fresh 0 9))))
      ≡₃ (true , true , true)
_ = refl

-- uni_y at the 2-cell (a modification condition between 3-cells) is
-- not stated yet (ledger S26b).
_ : sideOf uniY 2 Δ○ ≡ false
_ = refl

-- A 3-cell variable m : l ⇛ l: μ, η and rec accept it; rec_y at it and
-- uni do not (ledger S26b).
Δ○₃ : Ctx
Δ○₃ = Δ○ ▸ arr (arr (arr ⋆ one X) (bvar 0 1) (bvar 0 1)) (bvar 0 2) (bvar 0 2)

_ : (ok (tyOf ε (bnd μ 0 Δ○₃ ⟨⟩)) , sideOf recY 3 Δ○₃ , sideOf uni 0 Δ○₃) ≡₃ (true , false , false)
_ = refl

------------------------------------------------------------------------
-- Rejections by the side condition.

-- A map into a parameter that is not ⊤: (X, f : X → A) in context A.
Δbad₁ : Ctx
Δbad₁ = ε ▸ ⋆ ▸ arr ⋆ X (var 0)

_ : (sideOf μ 0 Δbad₁ , ok (tyOf (ε ▸ ⋆) (bnd μ 0 Δbad₁ ⟨⟩))) ≡₂ (false , false)
_ = refl

-- An object variable after an operation (sorts come first).
Δbad₂ : Ctx
Δbad₂ = ε ▸ ⋆ ▸ arr ⋆ one X ▸ ⋆

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

------------------------------------------------------------------------
-- Several sorts (spec §9.3, F11b over ⊤): even and odd naturals,
-- (E, O : ⋆, z : ⊤ → E, s : E → O, t : O → E).

E O : Tm
E = bvar 0 0
O = bvar 0 1

Δeo : Ctx
Δeo = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ one E ▸ arr ⋆ E O ▸ arr ⋆ O E

μE μO : Tm
μE = bnd μ 0 Δeo ⟨⟩
μO = bnd μ 1 Δeo ⟨⟩

_ : _≡_ {A = Maybe Ty × Maybe Ty} (tyOf ε μE , tyOf ε μO) (just ⋆ , just ⋆)
_ = refl

_ : tyOf ε (bnd η 3 Δeo ⟨⟩) ≡ just (arr ⋆ μE μO)
_ = refl

-- A model (A, B, a, f, g) in context.
Γeo : Ctx
Γeo = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 1) (var 0)

_ : _≡_ {A = Maybe Ty × Maybe Ty} (tyOf Γeo (bnd rec 0 Δeo (fresh 0 5)) , tyOf Γeo (bnd rec 1 Δeo (fresh 0 5)))
      (just (arr ⋆ μE (var 0)) , just (arr ⋆ μO (var 1)))
_ = refl

-- rec_y at s : E → O is  η_s ; rec_O ⇒ rec_E ; f.
_ : tyOf Γeo (bnd recY 3 Δeo (fresh 0 5)) ≡ just
      (arr (arr ⋆ μE (var 1))
           (C○.cmp μE μO (var 1) (bnd η 3 Δeo ⟨⟩) (bnd rec 1 Δeo (fresh 0 5)))
           (C○.cmp μE (var 0) (var 1) (bnd rec 0 Δeo (fresh 0 5)) (var 3)))
_ = refl

Γueo : Ctx
Γueo = openTel 0 (Construction.args NK (λ _ → true) uni 0 Δeo)

_ : (ok (ctx? Γueo) , ok (tyOf Γueo (bnd uni 0 Δeo (fresh 0 15))) , ok (tyOf Γueo (bnd uni 1 Δeo (fresh 0 15))))
      ≡₃ (true , true , true)
_ = refl

_ : (ok (tyOf Γueo (bnd uniY 2 Δeo (fresh 0 15))) , ok (tyOf Γueo (bnd uniY 3 Δeo (fresh 0 15))) ,
     ok (tyOf Γueo (bnd uniY 4 Δeo (fresh 0 15))))
      ≡₃ (true , true , true)
_ = refl

-- uni at the sort O is the 2-cell h_O ⇒ h′_O.
_ : tyOf Γueo (bnd uni 1 Δeo (fresh 0 15)) ≡ just (arr (arr ⋆ μO (var 1)) (var 6) (var 11))
_ = refl

-- Selectors: μ, rec and uni at sorts only; η, rec_y, uni_y after them.
_ : (sideOf μ 2 Δeo , sideOf η 1 Δeo , sideOf rec 2 Δeo) ≡₃ (false , false , false)
_ = refl

------------------------------------------------------------------------
-- Marks in the telescope (S26d): the integers
-- ℤ := μ(X, z : ⊤ → X, s : X → X inv) (spec §9.5). A model must
-- certify the inv mark: rec into (A, z′, s′) is accepted when s′ is a
-- variable marked inv, and rejected when s′ is unmarked. With the
-- (MARK)-only judgment of this file, that is all the kernel knows about
-- inv; the Gray judgment adds (DES), (DES-inv) and INIT's own inv rules
-- (ledger S26e).

Δℤ : Ctx
Δℤ = ε ▸ ⋆ ▸ arr ⋆ one X ▸[ minv ∷ [] ] arr ⋆ X X

μℤ : Tm
μℤ = bnd μ 0 Δℤ ⟨⟩

Γℤ : List Mark → Ctx
Γℤ ms = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸[ ms ] arr ⋆ (var 0) (var 0)

_ : ( ok (tyOf ε μℤ) , ok (tyOf ε (bnd η 2 Δℤ ⟨⟩))
    , ok (tyOf (Γℤ (minv ∷ [])) (bnd rec 0 Δℤ (fresh 0 3)))
    , ok (tyOf (Γℤ []) (bnd rec 0 Δℤ (fresh 0 3)))) ≡₄ (true , true , true , false)
_ = refl

_ : tyOf (Γℤ (minv ∷ [])) (bnd rec 0 Δℤ (fresh 0 3)) ≡ just (arr ⋆ μℤ (var 0))
_ = refl

-- rec_y at s, and uni over the marked telescope (its model argument
-- is marked like Δℤ, so the opened context has s′ marked inv).
Γuℤ : Ctx
Γuℤ = openTel 0 (Construction.args NK (λ _ → true) uni 0 Δℤ)

_ : ( ok (tyOf (Γℤ (minv ∷ [])) (bnd recY 2 Δℤ (fresh 0 3)))
    , ok (ctx? Γuℤ) , ok (tyOf Γuℤ (bnd uni 0 Δℤ (fresh 0 9)))
    , ok (tyOf Γuℤ (bnd uniY 2 Δℤ (fresh 0 9)))) ≡₄ (true , true , true , true)
_ = refl

-- Positivity rejects inv on a sort, and a mark other than inv on an
-- operation.
_ : ( sideOf μ 0 (ε ▸[ minv ∷ [] ] ⋆ ▸ arr ⋆ one X ▸ arr ⋆ X X)
    , sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ one X ▸[ mps ∷ [] ] arr ⋆ X X)
    , sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ one X ▸[ mgrpd 1 ∷ [] ] arr ⋆ X X)
    , sideOf μ 0 Δℤ) ≡₄ (false , false , false , true)
_ = refl

------------------------------------------------------------------------
-- Sort marks (S26d): the circle S¹ = μ(X : grpd₁, b : ⊤ → X, l : b ⇒ b)
-- and the truncation ‖A‖₀ = μ(X : ⋆^{≤0}, g : A → X), A a parameter.
-- A model's carrier must certify the mark: with the (MARK)-only
-- judgment, a carrier variable carrying it.

ΔS¹ : Ctx
ΔS¹ = ε ▸[ mgrpd 1 ∷ [] ] ⋆ ▸ arr ⋆ one X ▸ arr (arr ⋆ one X) (bvar 0 1) (bvar 0 1)

ΓS¹ : List Mark → Ctx
ΓS¹ ms = ε ▸[ ms ] ⋆ ▸ arr ⋆ one (var 0) ▸ arr (arr ⋆ one (var 0)) (var 1) (var 1)

_ : ( ok (tyOf ε (bnd μ 0 ΔS¹ ⟨⟩))
    , ok (tyOf (ΓS¹ (mgrpd 1 ∷ [])) (bnd rec 0 ΔS¹ (fresh 0 3)))
    , ok (tyOf (ΓS¹ (mgrpd 1 ∷ [])) (bnd recY 2 ΔS¹ (fresh 0 3)))
    , ok (tyOf (ΓS¹ []) (bnd rec 0 ΔS¹ (fresh 0 3)))) ≡₄ (true , true , true , false)
_ = refl

-- In context (A : ⋆): ‖A‖₀ with n = 0, i.e. mtrunc 2.
Δtr : Ctx
Δtr = ε ▸[ mtrunc 2 ∷ [] ] ⋆ ▸ arr ⋆ (var 0) X

Γtr : List Mark → Ctx
Γtr ms = ε ▸ ⋆ ▸[ ms ] ⋆ ▸ arr ⋆ (var 0) (var 1)

_ : ( ok (tyOf (ε ▸ ⋆) (bnd μ 0 Δtr ⟨⟩))
    , ok (tyOf (Γtr (mtrunc 2 ∷ [])) (bnd rec 0 Δtr (⟨⟩ ,ₛ var 1 ,ₛ var 2)))
    , ok (tyOf (Γtr (mtrunc 3 ∷ [])) (bnd rec 0 Δtr (⟨⟩ ,ₛ var 1 ,ₛ var 2)))
    , ok (tyOf (Γtr []) (bnd rec 0 Δtr (⟨⟩ ,ₛ var 1 ,ₛ var 2)))) ≡₄ (true , true , false , false)
_ = refl
