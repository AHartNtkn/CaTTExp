------------------------------------------------------------------------
-- h-levels (ledger F3/F9, notes/ordinary-math.md §2.2): CaTT with
-- truncation marks on objects and the use rules T-fill, T-inv and T-ctr.
--
-- An object term C may carry a mark μ C = just m, read "C trunc (m − 2)"
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
-- Simplification: μ is one global function on raw terms, so a
-- variable index is marked in every context, not per declaration as
-- T-var specifies. Per-declaration marks are left to the T-var item.
--
-- Levels: T-fill needs level k ≥ n + 1 = m − 1, i.e. m ≤ k + 1;
-- T-inv inverts a cell of level j + 1 ≥ n + 1, i.e. m ≤ j + 2
-- (levels ≥ n + 2 are also derivable, Prop. 2.1; level 0 is excluded);
-- T-ctr needs m = 0.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Trunc.Typing
  (𝕊 : Signature)
  (μ : Signature.Tm 𝕊 → Maybe Nat)
  where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊 public
open import CaTTExp.Typing 𝕊 using (cattSide)

------------------------------------------------------------------------
-- The generic contexts.

-- Type of level-j cells into C = var 1 from c = var 0, in TF j.
globeTy : Nat → Ty
globeTy zero    = arr ⋆ (var 0) (var 1)
globeTy (suc j) = arr (globeTy j) (var (2 + (j + j))) (var (3 + (j + j)))

TF : Nat → Ctx
TF zero    = ε ▸ ⋆ ▸ ⋆ ▸ globeTy 0 ▸ globeTy 0
TF (suc k) = TF k ▸ globeTy (suc k) ▸ globeTy (suc k)

TFty : Nat → Ty
TFty k = arr (globeTy k) (var (2 + (k + k))) (var (3 + (k + k)))

TI : Nat → Ctx
TI j = TF j ▸ globeTy (suc j)

TIty : Nat → Ty
TIty j = arr (globeTy j) (var (3 + (j + j))) (var (2 + (j + j)))

TC : Ctx
TC = ε ▸ ⋆ ▸ ⋆

TCty : Ty
TCty = arr ⋆ (var 0) (var 1)

-- `allows mark j`: the object is marked with some m ≤ j.
allows : Maybe Nat → Nat → Bool
allows nothing  _ = false
allows (just m) j = m <ℕ suc j

-- The image of C under σ.
objOf : Sub → Tm
objOf σ = lookupₛ σ 1

------------------------------------------------------------------------
-- Typing: CaTTExp.TypingWith with cattSide, plus the three rules.

infix 4 _⊢ctx _⊢ty_ _⊢tm_∶_ _⊢sub_∶_

mutual
  data _⊢ctx : Ctx → Set where
    ε-wf : ε ⊢ctx
    ▸-wf : ∀ {Γ A} → Γ ⊢ctx → Γ ⊢ty A → Γ ▸ A ⊢ctx

  data _⊢ty_ (Γ : Ctx) : Ty → Set where
    ⋆-wf   : Γ ⊢ctx → Γ ⊢ty ⋆
    arr-wf : ∀ {A t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Γ ⊢ty arr A t u

  data _⊢tm_∶_ (Γ : Ctx) : Tm → Ty → Set where
    var-wf   : ∀ {i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢tm var i ∶ A
    coh-wf   : ∀ {Δ A t u σ} →
               Δ ⊢ps → Δ ⊢ctx → Δ ⊢ty arr A t u →
               T (cattSide Δ A t u) →
               Γ ⊢sub σ ∶ Δ →
               Γ ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
    cst-wf   : ∀ {k} → Γ ⊢ctx → Valid k → Γ ⊢tm cst k ∶ ty k
    -- (T-fill)
    tfill-wf : ∀ {k σ} → Γ ⊢sub σ ∶ TF k → T (allows (μ (objOf σ)) (suc k)) →
               Γ ⊢tm coh (TF k) (TFty k) σ ∶ TFty k [ σ ]ty
    -- (T-inv): the inverse of a cell of level j + 1
    tinv-wf  : ∀ {j σ} → Γ ⊢sub σ ∶ TI j → T (allows (μ (objOf σ)) (suc (suc j))) →
               Γ ⊢tm coh (TI j) (TIty j) σ ∶ TIty j [ σ ]ty
    -- (T-ctr)
    tctr-wf  : ∀ {σ} → Γ ⊢sub σ ∶ TC → T (allows (μ (objOf σ)) 0) →
               Γ ⊢tm coh TC TCty σ ∶ TCty [ σ ]ty

  data _⊢sub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ⊢ctx → Γ ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ⊢sub σ ∶ Δ → Γ ⊢tm t ∶ A [ σ ]ty →
            Γ ⊢sub σ ,ₛ t ∶ Δ ▸ A
