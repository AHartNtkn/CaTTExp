------------------------------------------------------------------------
-- The coherence mark rule of plain CaTT (P), as an instance of the
-- one mark judgment (notes/unified-engine.md §3.4).
--
-- In P, the free model of a pasting context Δ with a set M of its
-- generators inverted makes the head's value invertible exactly when
--   (COH-inv) the head is in the coherence case, or
--   (OP-inv)  it is in the operation case and every generator of Δ of
--             top dimension is in M
-- (spec §3.3 restricted to one hom; the composite of Δ is invertible
-- in the localisation iff its top cells are). Both clauses are
-- positive, so CaTTExp.Binder.FreeModelMark gives renaming and
-- substitution for this judgment with no further proof, and the
-- kernel's checker decides it.
--
-- The examples, all by evaluation:
--   * the composite of two inv-marked arrows is inv;
--   * with one argument unmarked, it is not;
--   * substituting inv-marked variables for unmarked ones creates the
--     mark (the instance is stronger than its pattern);
--   * identities and associators (coherence case) are inv unmarked.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Syntax as Syn
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.FreeModelMarkCatt where

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
  ; bargs     = λ _ _ _ → Syn.ε Syn.▸[ BM.minv ∷ [] ] Syn.⋆
  ; bres      = λ _ _ _ → Syn.⋆
  }

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊 using (cattSide; isCoh; isOp)

-- Entailment: equality of marks (S36 supplies the real order).
_⊑_ : Mark → Mark → Bool
m ⊑ n = m ==M n

⊑-refl : ∀ m → T (m ⊑ m)
⊑-refl = ==M-refl

⊑-trans : ∀ {l m n} → T (l ⊑ m) → T (m ⊑ n) → T (l ⊑ n)
⊑-trans {l} {m} {n} p q rewrite ==M-sound l m p = q

open import CaTTExp.Binder.FreeModelMarkPos 𝕊 _⊑_

-- Variables of Δ of top dimension.
private
  indexed : Nat → Ctx → List (Nat × Ty)
  indexed _ ε             = []
  indexed n (Γ ▸[ _ ] A) = (len Γ , A) ∷ indexed n Γ

topVars : Ctx → List Nat
topVars Δ = go (indexed 0 Δ)
  where
    go : List (Nat × Ty) → List Nat
    go []             = []
    go ((i , A) ∷ xs) = if dim A ==ℕ dimCtx Δ then i ∷ go xs else go xs

private
  cohCase : Ty → Ctx → Bool
  cohCase (arr A t u) Δ = isCoh Δ A t u
  cohCase ⋆           Δ = false

  opCase : Ty → Ctx → Bool
  opCase (arr A t u) Δ = isOp Δ A t u
  opCase ⋆           Δ = false

atoms : List Nat → List Pos
atoms []       = []
atoms (i ∷ is) = atom i minv ∷ atoms is

clauses : List Clause
clauses =
  record { concl = minv ; when = λ Δ A → cohCase A Δ ; body = λ _ _ → yes } ∷
  record { concl = minv ; when = λ Δ A → opCase A Δ
         ; body = λ Δ _ → allP (atoms (topVars Δ)) } ∷ []

cohHas : Ctx → Ty → (Nat → Mark → Bool) → Mark → Bool
cohHas = cohHasC clauses

K₀-elim : ∀ {A : Set} → K₀ → A
K₀-elim ()

open import CaTTExp.Binder.FreeModelMark 𝕊 cattSide _⊑_ (λ k _ → K₀-elim k) (λ _ _ _ → false) cohHas

hyp : Hyp
hyp = record
  { ⊑-refl   = ⊑-refl
  ; ⊑-trans  = λ {l} {m} {n} → ⊑-trans {l} {m} {n}
  ; cst-up   = λ {k} → K₀-elim k
  ; head-up  = λ ()
  ; coh-up   = λ {Δ} {A} {f} {m} {n} → cohC-up (λ {l} {m} {n} → ⊑-trans {l} {m} {n}) clauses {Δ} {A} {f} {m} {n}
  ; coh-mono = λ {Δ} {A} {f} {g} {m} → cohC-mono (λ {l} {m} {n} → ⊑-trans {l} {m} {n}) clauses {Δ} {A} {f} {g} {m}
  }

open Laws hyp public using (markVar; markRen; markSub; up)

------------------------------------------------------------------------
-- Examples.

-- The composable pair (x, y, f : x → y, z, g : y → z).
pair : Ctx
pair = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)

-- The composite head: coh_{pair, x → z}.
compTy : Ty
compTy = arr ⋆ (var 0) (var 3)

comp : Sub → Tm
comp σ = coh pair compTy σ

-- A context with two arrows f : a → b, g : b → c, with marks ms, ns.
arrows : List Mark → List Mark → Ctx
arrows ms ns = ε ▸ ⋆ ▸ ⋆ ▸[ ms ] arr ⋆ (var 0) (var 1) ▸ ⋆ ▸[ ns ] arr ⋆ (var 1) (var 3)

idSub : Sub
idSub = ⟨⟩ ,ₛ var 0 ,ₛ var 1 ,ₛ var 2 ,ₛ var 3 ,ₛ var 4

inv1 : List Mark
inv1 = minv ∷ []

-- The head is in the operation case and its top variables are f and g.
pair-tops : topVars pair ≡ 4 ∷ 2 ∷ []
pair-tops = refl

pair-side : cattSide pair ⋆ (var 0) (var 3) ≡ true
pair-side = refl

-- f, g both inv: the composite is inv.
comp-inv : markTm (arrows inv1 inv1) minv (comp idSub) ≡ true
comp-inv = refl

-- g unmarked: the composite is not derivably inv.
comp-not-inv : markTm (arrows inv1 []) minv (comp idSub) ≡ false
comp-not-inv = refl

-- The identity on an object (coherence case) is inv with no marks.
point : Ctx
point = ε ▸ ⋆

idHead : Tm
idHead = coh point (arr ⋆ (var 0) (var 0)) (⟨⟩ ,ₛ var 0)

id-inv : markTm (ε ▸ ⋆) minv idHead ≡ true
id-inv = refl

-- Substitution only adds marks: in the unmarked pair the composite of
-- the variables is not inv; after substituting inv-marked variables it
-- is (markSub proves the general direction).
comp-unmarked : markTm (arrows [] []) minv (comp idSub) ≡ false
comp-unmarked = refl

comp-substituted : markTm (arrows inv1 inv1) minv (comp idSub [ idSub ]tm) ≡ true
comp-substituted = refl
