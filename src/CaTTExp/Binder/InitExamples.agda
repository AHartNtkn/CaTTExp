------------------------------------------------------------------------
-- INIT examples, checked by the certified checker
-- (CaTTExp.Binder.CheckWith with plain CaTT's side condition).
--
-- Every statement below is `refl`: the checker, which is sound and
-- complete, accepts (or rejects) the term, so the term is (or is not)
-- derivable. Positive: ℕ with all six formers (the shapes of rec_y
-- pinned: naturality cylinders, an X-free factor omitted), the circle
-- with every former but uni_y at the loop, a 3-cell entry (rec_y and
-- uni), even/odd naturals, marks, a sort over a base with its
-- companion cell (rec_y at it and uni over it: the cylinder of the
-- composite a ; p), and a fixed point e : z ; s ⇒ z. Result types are
-- checked well formed (`wfTy`). Negative: the side condition rejects a
-- non-⊤ parameter target, a second object variable, a source
-- mentioning X, rec_y at y = 0, uni_y at a 2-cell or 3-cell (ledger
-- C1d (2)), and ill-formed companions.
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
open import CaTTExp.Naturality.DimOne using (K₁)
import CaTTExp.Binder.Cyl 𝕊 K₁ as Cy

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
sideOf = Construction.side NK Former (λ b → b) (λ _ → true)

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

-- The checker types a term (its arguments and side condition); that its
-- result type is well formed is checked separately, since
-- presupposition for INIT is not proved yet (ledger S26i).
wfTy : Ctx → Tm → Bool
wfTy Γ t = ok (tyOf Γ t >>= λ A → ctx? (Γ ▸ A) >>= λ _ → just tt)

t-μ   = tyOf ε (bnd μ 0 Δℕ ⟨⟩)
t-η1  = tyOf ε (bnd η 1 Δℕ ⟨⟩)
t-η2  = tyOf ε (bnd η 2 Δℕ ⟨⟩)
t-rec = tyOf Γm (bnd rec 0 Δℕ (fresh 0 3))
t-r1  = tyOf Γm (bnd recY 1 Δℕ (fresh 0 3))
t-r2  = tyOf Γm (bnd recY 2 Δℕ (fresh 0 3))

-- uni and uni_y: the context is the argument telescope opened.
Γu : Ctx
Γu = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δℕ)

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

-- rec_y at l is the cylinder of l: a 3-cell between the two pastings
-- of its naturality square; its type is well formed.
_ : wfTy Γ○ (bnd recY 2 Δ○ (fresh 0 3)) ≡ true
_ = refl

Γu○ : Ctx
Γu○ = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δ○)

_ : (ok (ctx? Γu○) , ok (tyOf Γu○ (bnd uni 0 Δ○ (fresh 0 9))) , ok (tyOf Γu○ (bnd uniY 1 Δ○ (fresh 0 9))))
      ≡₃ (true , true , true)
_ = refl

-- uni_y at the 2-cell l would be the cylinder of θ_l, whose boundaries
-- are 2-dimensional coherences: it needs a filler of dimension 2
-- (ledger C1d (2)), so it is not stated. At b, and uni at X, it is,
-- with well-formed types.
_ : ( sideOf uniY 2 Δ○ ∷ wfTy Γu○ (bnd uniY 1 Δ○ (fresh 0 9)) ∷ wfTy Γu○ (bnd uni 0 Δ○ (fresh 0 9)) ∷ [])
  ≡ (false ∷ true ∷ true ∷ [])
_ = refl

-- A 3-cell variable m : l ⇛ l: rec_y at it is its cylinder, a 4-cell
-- (cells of any dimension with variable boundaries), and uni is stated
-- over the telescope; their types are well formed.
Δ○₃ : Ctx
Δ○₃ = Δ○ ▸ arr (arr (arr ⋆ one X) (bvar 0 1) (bvar 0 1)) (bvar 0 2) (bvar 0 2)

Γ○₃ : Ctx
Γ○₃ = Γ○ ▸ arr (arr (arr ⋆ one (var 0)) (var 1) (var 1)) (var 2) (var 2)

Γu○₃ : Ctx
Γu○₃ = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δ○₃)

_ : ( ok (tyOf ε (bnd μ 0 Δ○₃ ⟨⟩)) ∷ sideOf recY 3 Δ○₃ ∷ sideOf uni 0 Δ○₃
    ∷ wfTy Γ○₃ (bnd recY 3 Δ○₃ (fresh 0 4)) ∷ ok (ctx? Γu○₃) ∷ wfTy Γu○₃ (bnd uni 0 Δ○₃ (fresh 0 12))
    ∷ sideOf uniY 3 Δ○₃ ∷ [])
  ≡ (true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ false ∷ [])
_ = refl

------------------------------------------------------------------------
-- Rejections by the side condition.

-- A map into a parameter that is not ⊤, after an operation (so not a
-- structure map, and not a companion): (X, z : ⊤ → X, f : X → A) in
-- context A. ((X, f : X → A) alone is a sort over A; see below.)
Δbad₁ : Ctx
Δbad₁ = ε ▸ ⋆ ▸ arr ⋆ one X ▸ arr ⋆ X (var 0)

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
-- rec_y at s is the naturality cell  η_s ▹ rec ⇒ rec ◃ s  (the typed
-- whiskers of CaTTExp.DerivedBoundary), rec_y at z is  η_z ▹ rec ⇒ z
-- (the factor at the X-free source ⊤ is omitted, not an identity),
-- and uni is a cell between the two model morphisms of its arguments.

private
  recℕ : Tm
  recℕ = bnd rec 0 Δℕ (fresh 0 3)

_ : t-r2 ≡ just (arr (arr ⋆ μℕ (var 0))
                     (Cy.rwT 0 0 (bnd η 2 Δℕ ⟨⟩) (arr ⋆ μℕ μℕ) (var 0) recℕ)
                     (Cy.lwT 0 0 recℕ μℕ (var 2) (arr ⋆ (var 0) (var 0))))
_ = refl

_ : t-r1 ≡ just (arr (arr ⋆ one (var 0))
                     (Cy.rwT 0 0 (bnd η 1 Δℕ ⟨⟩) (arr ⋆ one μℕ) (var 0) recℕ)
                     (var 1))
_ = refl

-- In Γu = (A, z, s, h, θ_z, θ_s, h′, θ′_z, θ′_s): uni is h ⇒ h′, and
-- uni_y at s is the modification condition, the cylinder of θ_s.
_ : t-uni ≡ just (arr (arr ⋆ μℕ (var 0)) (var 3) (var 6))
_ = refl

_ : (wfTy Γu (bnd uniY 1 Δℕ (fresh 0 9)) , wfTy Γu (bnd uniY 2 Δℕ (fresh 0 9)) , wfTy Γm (bnd recY 2 Δℕ (fresh 0 3)))
      ≡₃ (true , true , true)
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

-- rec_y at s : E → O is  η_s ▹ rec_O ⇒ rec_E ◃ f.
_ : tyOf Γeo (bnd recY 3 Δeo (fresh 0 5)) ≡ just
      (arr (arr ⋆ μE (var 1))
           (Cy.rwT 0 0 (bnd η 3 Δeo ⟨⟩) (arr ⋆ μE μO) (var 1) (bnd rec 1 Δeo (fresh 0 5)))
           (Cy.lwT 0 0 (bnd rec 0 Δeo (fresh 0 5)) μE (var 3) (arr ⋆ (var 0) (var 1))))
_ = refl

Γueo : Ctx
Γueo = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δeo)

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
Γuℤ = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δℤ)

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

------------------------------------------------------------------------
-- Sorts over bases (S26c step 2). In context (B : ⋆, s : ⊤ → B), the
-- sort X over B with a point over s:
--   μ(X, p : X → B, a : ⊤ → X, c : a ; p ⇒ s inv).
-- p is the header (structure map), c the companion of the operation a.

-- The composite x ; q of maps x : S → Y, q : Y → Z.
cmp : Tm → Tm → Tm → Tm → Tm → Tm
cmp S Y Z x q =
  coh (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3))
      (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ S ,ₛ Y ,ₛ x ,ₛ Z ,ₛ q)

-- The companion type a ; p ⇒ s, for a and p entries of the telescope.
cmpTyB : Nat → Nat → Ty
cmpTyB a p = arr (arr ⋆ one (var 0)) (cmp one X (var 0) (bvar 0 a) (bvar 0 p)) (var 1)

Γb : Ctx
Γb = ε ▸ ⋆ ▸ arr ⋆ one (var 0)

Δb : Ctx
Δb = ε ▸ ⋆ ▸ arr ⋆ X (var 0) ▸ arr ⋆ one X ▸[ minv ∷ [] ] cmpTyB 2 1

-- A model: (A, q : A → B, a′ : ⊤ → A, c′ : a′ ; q ⇒ s inv).
Γbm : List Mark → Ctx
Γbm ms = Γb ▸ ⋆ ▸ arr ⋆ (var 2) (var 0) ▸ arr ⋆ one (var 2)
            ▸[ ms ] arr (arr ⋆ one (var 0)) (cmp one (var 2) (var 0) (var 4) (var 3)) (var 1)

σbm : Sub
σbm = ⟨⟩ ,ₛ var 2 ,ₛ var 3 ,ₛ var 4 ,ₛ var 5

_ : ( sideOf μ 0 Δb
    ∷ ok (tyOf Γb (bnd μ 0 Δb ⟨⟩))
    ∷ ok (tyOf Γb (bnd η 1 Δb ⟨⟩))
    ∷ ok (tyOf Γb (bnd η 2 Δb ⟨⟩))
    ∷ ok (tyOf Γb (bnd η 3 Δb ⟨⟩))
    ∷ ok (tyOf (Γbm (minv ∷ [])) (bnd rec 0 Δb σbm))
    ∷ ok (tyOf (Γbm []) (bnd rec 0 Δb σbm))
    ∷ ok (tyOf (Γbm (minv ∷ [])) (bnd recY 1 Δb σbm))
    ∷ ok (tyOf (Γbm (minv ∷ [])) (bnd recY 2 Δb σbm))
    ∷ []) ≡ (true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ false ∷ true ∷ true ∷ [])
_ = refl

-- A sort over A with no operations: (X, p : X → A).
_ : sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ X (var 0)) ≡ true
_ = refl

-- Rejections: no companion; the companion unmarked; a companion whose
-- source is not a ; p; a cell into the based sort; an X-free non-⊤
-- target with no companion; the structure map after an operation.
_ : ( sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ X (var 0) ▸ arr ⋆ one X)
    ∷ sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ X (var 0) ▸ arr ⋆ one X ▸ cmpTyB 2 1)
    ∷ sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ X (var 0) ▸ arr ⋆ one X
                    ▸[ minv ∷ [] ] arr (arr ⋆ one (var 0)) (var 1) (var 1))
    ∷ sideOf μ 0 (Δb ▸ arr (arr ⋆ one X) (bvar 0 2) (bvar 0 2))
    ∷ sideOf μ 0 (Δb ▸ arr ⋆ one (var 0))
    ∷ sideOf μ 0 (ε ▸ ⋆ ▸ arr ⋆ one X ▸ arr ⋆ X (var 0) ▸[ minv ∷ [] ] cmpTyB 1 2)
    ∷ []) ≡ (false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ [])
_ = refl

-- rec_y at the companion c (a 2-cell whose source a ; p is a composite)
-- is its cylinder, with the composite's cylinder filled by K₁; uni is
-- stated over Δb. Their types are well formed.
Γub : Ctx
Γub = Γb ⧺ openTel 2 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δb)

_ : ( sideOf recY 3 Δb ∷ wfTy (Γbm (minv ∷ [])) (bnd recY 3 Δb σbm)
    ∷ sideOf uni 0 Δb ∷ ok (ctx? Γub) ∷ wfTy Γub (bnd uni 0 Δb (fresh 2 12))
    ∷ wfTy Γub (bnd uniY 2 Δb (fresh 2 12)) ∷ [])
  ≡ (true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ [])
_ = refl

------------------------------------------------------------------------
-- A 2-cell with a composite boundary between maps: a fixed point,
-- μ(X, z : ⊤ → X, s : X → X, e : z ; s ⇒ z). rec_y at e is a 3-cell
-- whose boundary contains the cylinder of z ; s (K₁); uni is stated.

Δfp : Ctx
Δfp = Δℕ ▸ arr (arr ⋆ one X) (cmp one X X (bvar 0 1) (bvar 0 2)) (bvar 0 1)

Γfp : Ctx
Γfp = Γm ▸ arr (arr ⋆ one (var 0)) (cmp one (var 0) (var 0) (var 1) (var 2)) (var 1)

Γufp : Ctx
Γufp = openTel 0 (Construction.args NK Former (λ b → b) (λ _ → true) uni 0 Δfp)

_ : ( sideOf μ 0 Δfp ∷ sideOf recY 3 Δfp ∷ wfTy Γfp (bnd recY 3 Δfp (fresh 0 4))
    ∷ ok (ctx? Γufp) ∷ wfTy Γufp (bnd uni 0 Δfp (fresh 0 12)) ∷ wfTy Γufp (bnd uniY 2 Δfp (fresh 0 12))
    ∷ sideOf uniY 3 Δfp ∷ [])
  ≡ (true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ false ∷ [])
_ = refl
