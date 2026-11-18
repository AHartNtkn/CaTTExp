------------------------------------------------------------------------
-- h-levels (ledger F3/F9, notes/ordinary-math.md §2.2): CaTT with
-- truncation marks on objects and the use rules T-fill, T-inv and T-ctr.
--
-- A context Γ comes with marks M : Nat → Maybe Nat on its variables
-- (the declarations `C : ⋆^{≤n}` of T-var): M i = just m reads
-- "variable i trunc (m − 2)"
-- (so m = 0 is contractible, 1 a proposition, 2 a set, 3 a 1-category).
-- A *cell into C of level j* is a term whose type is an iterated arrow
-- over `c → C`: level 0 is a map c → C, level j + 1 a cell between two
-- level-j cells.
--
-- The three use rules are operations over a fixed, non-pasting context
-- applied to a substitution, i.e. `coh` terms whose context is one of
--
--   TF k : c, C, a₀ b₀ : c → C, a₁ b₁ : a₀ → b₀, …, aₖ bₖ : aₖ₋₁ → bₖ₋₁
--          with type  aₖ → bₖ                    (T-fill at level k)
--   TI j : TF j, u : aⱼ → bⱼ   with type  bⱼ → aⱼ   (T-inv at level j+1)
--   TC   : c, C               with type  c → C     (T-ctr)
--
-- and whose image of C is marked low enough. Pure CaTT never accepts
-- these contexts (they are not pasting contexts), so the extension is
-- conservative on the coh rule. As in T-var, the mark is a property of
-- the image σ(C), so substitution into a marked tuple needs the mark
-- (the certificate); no definitional equality is added.
--
-- Marks are per context (per declaration). A substitution into a
-- marked context must respect the marks (`Resp`), and with that
-- certificate substitution is admissible (CaTTExp.Trunc.Subst).
-- Constants of the signature carry no marks.
-- Narrower than T-var: Resp lets a marked variable go only to a
-- *variable* with a mark at most as high. T-var allows any object
-- term C[σ] with a derivation of `C[σ] trunc n`; here only variables
-- carry marks, so a marked variable cannot yet be sent to a compound
-- object (e.g. a limit). Marks on compound objects need the closure
-- rules (T-lim, T-hom, …) as rules of the judgment.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Trunc.Typing (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊 public
open import CaTTExp.Typing 𝕊 using (cattSide)

------------------------------------------------------------------------
-- The generic contexts.

dbl : Nat → Nat
dbl zero    = zero
dbl (suc k) = suc (suc (dbl k))

-- Type of level-j cells into C = var 1 from c = var 0, in TF j.
globeTy : Nat → Ty
globeTy zero    = arr ⋆ (var 0) (var 1)
globeTy (suc j) = arr (globeTy j) (var (2 + dbl j)) (var (3 + dbl j))

TF : Nat → Ctx
TF zero    = ε ▸ ⋆ ▸ ⋆ ▸ globeTy 0 ▸ globeTy 0
TF (suc k) = TF k ▸ globeTy (suc k) ▸ globeTy (suc k)

TFty : Nat → Ty
TFty k = arr (globeTy k) (var (2 + dbl k)) (var (3 + dbl k))

TI : Nat → Ctx
TI j = TF j ▸ globeTy (suc j)

TIty : Nat → Ty
TIty j = arr (globeTy j) (var (3 + dbl j)) (var (2 + dbl j))

TC : Ctx
TC = ε ▸ ⋆ ▸ ⋆

TCty : Ty
TCty = arr ⋆ (var 0) (var 1)

-- `allows mark j`: the object is marked with some m ≤ j.
allows : Maybe Nat → Nat → Bool
allows nothing  _ = false
allows (just m) j = m <ℕ suc j

Marks : Set
Marks = Nat → Maybe Nat

none : Marks
none _ = nothing

-- The mark of an object term: only variables carry marks.
markOf : Marks → Tm → Maybe Nat
markOf M (var i) = M i
markOf M _       = nothing

-- The image of C under σ.
objOf : Sub → Tm
objOf σ = lookupₛ σ 1

-- σ (from a context with marks M into one with marks N) respects marks:
-- each marked variable goes to a variable marked at most as high (T-var
-- with T-cum).
Resp : Marks → Marks → Sub → Set
Resp M N σ = ∀ i m → M i ≡ just m → T (allows (markOf N (lookupₛ σ i)) m)

------------------------------------------------------------------------
-- Typing: CaTTExp.TypingWith with cattSide, plus the three rules.

infix 4 _∣_⊢ctx _∣_⊢ty_ _∣_⊢tm_∶_ _∣_⊢sub_∶_

mutual
  data _∣_⊢ctx : Ctx → Marks → Set where
    ε-wf : ∀ {M} → ε ∣ M ⊢ctx
    ▸-wf : ∀ {Γ M A} → Γ ∣ M ⊢ctx → Γ ∣ M ⊢ty A → Γ ▸ A ∣ M ⊢ctx

  data _∣_⊢ty_ (Γ : Ctx) (M : Marks) : Ty → Set where
    ⋆-wf   : Γ ∣ M ⊢ctx → Γ ∣ M ⊢ty ⋆
    arr-wf : ∀ {A t u} → Γ ∣ M ⊢tm t ∶ A → Γ ∣ M ⊢tm u ∶ A → Γ ∣ M ⊢ty arr A t u

  data _∣_⊢tm_∶_ (Γ : Ctx) (M : Marks) : Tm → Ty → Set where
    var-wf   : ∀ {i A} → Γ ∣ M ⊢ctx → lookup Γ i ≡ just A → Γ ∣ M ⊢tm var i ∶ A
    -- plain coh: its own pasting context is unmarked
    coh-wf   : ∀ {Δ A t u σ} →
               Δ ⊢ps → Δ ∣ none ⊢ctx → Δ ∣ none ⊢ty arr A t u →
               T (cattSide Δ A t u) →
               Γ ∣ M ⊢sub σ ∶ Δ →
               Γ ∣ M ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
    cst-wf   : ∀ {k} → Γ ∣ M ⊢ctx → Valid k → Γ ∣ M ⊢tm cst k ∶ ty k
    -- (T-fill)
    tfill-wf : ∀ {k σ} → Γ ∣ M ⊢sub σ ∶ TF k → T (allows (markOf M (objOf σ)) (suc k)) →
               Γ ∣ M ⊢tm coh (TF k) (TFty k) σ ∶ TFty k [ σ ]ty
    -- (T-inv): the inverse of a cell of level j + 1
    tinv-wf  : ∀ {j σ} → Γ ∣ M ⊢sub σ ∶ TI j → T (allows (markOf M (objOf σ)) (suc (suc j))) →
               Γ ∣ M ⊢tm coh (TI j) (TIty j) σ ∶ TIty j [ σ ]ty
    -- (T-ctr)
    tctr-wf  : ∀ {σ} → Γ ∣ M ⊢sub σ ∶ TC → T (allows (markOf M (objOf σ)) 0) →
               Γ ∣ M ⊢tm coh TC TCty σ ∶ TCty [ σ ]ty

  data _∣_⊢sub_∶_ (Γ : Ctx) (M : Marks) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ∣ M ⊢ctx → Γ ∣ M ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ∣ M ⊢sub σ ∶ Δ → Γ ∣ M ⊢tm t ∶ A [ σ ]ty →
            Γ ∣ M ⊢sub σ ,ₛ t ∶ Δ ▸ A
