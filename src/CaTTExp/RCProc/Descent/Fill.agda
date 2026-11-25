------------------------------------------------------------------------
-- The direct naturality filler (ledger S20 (i), stage 4d; notes/
-- rc-generator.md §1, stage 4 plan): for a coherence head c = coh Q B id
-- and a selection Y, the filler c↑ : a_c ⇛ b_c in the cylinder context
-- Q↑Y as one answer of a recursion oracle.
--
-- Q↑Y is well formed by Naturality.CylCtx.cylCtx-ok (for contexts whose
-- types have variable boundaries, as every pasting context, with the
-- trivial filler family: `VarBd`), whose generic datum `gen Y` is valid,
-- so it gives typed copies and typed cylinders of the variables.  Its
-- side conditions (variable boundaries, length, up-closure of Y) are
-- decided here.  a_c, b_c are built by RCProc.Descent.Lift.endsT with
-- the fillers of the coherences in B's boundaries from this same
-- function (fuel-bounded), and the answer is the oracle's.  So every
-- `just` is a typed term of Q↑Y.
--
-- This is the filler of shape sO of Naturality.General.  It is correct
-- (typed) always; it can only answer when a_c and b_c have equal strict
-- images, which fails for compositions with a selected top cell (those
-- need layered fillers).
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.Fill where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (idS; id-wf)
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; lenSel; selAt; anySel; anyL; module Cyl)
import CaTTExp.Naturality.DimOne as D1
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.PureMetatheory using (closed)
open import CaTTExp.Naturality.Typing using (UpSel; module Hyp)
open import CaTTExp.Naturality.CylCtx using (module VarBd)
import CaTTExp.Naturality.Typing as Ty
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (decℕ)
open import CaTTExp.RCProc.GlueP using (varT)
open import CaTTExp.RCProc.Descent.Lift

private
  module VB = VarBd K0 (λ _ _ _ → tt)

decCtx : (Γ Δ : Ctx) → Maybe (Γ ≡ Δ)
decCtx Γ Δ = go (Γ ==Ctx Δ) (==Ctx-sound Γ Δ)
  where
  go : (b : Bool) → (T b → Γ ≡ Δ) → Maybe (Γ ≡ Δ)
  go true  f = just (f tt)
  go false _ = nothing

-- A recursion oracle in every context.
RecAll : Set
RecAll = ∀ {Δ} → Δ ⊢ctx → TTm Δ → TTm Δ → Maybe (TTm Δ)

goodTy? : (A : Ty) → Maybe (VB.GoodTy A)
goodTy? ⋆                       = just tt
goodTy? (arr A (var _) (var _)) = goodTy? A >>= λ g → just (g , tt , tt)
goodTy? (arr _ _ _)             = nothing

goodCtx? : (Q : Ctx) → Maybe (VB.GoodCtx Q)
goodCtx? ε       = just tt
goodCtx? (Q ▸ A) = goodCtx? Q >>= λ g → goodTy? A >>= λ h → just (g , h)

-- Up-closure of a selection, decided: every unselected variable has a
-- type mentioning no selected variable.
private
  okM : Sel → Nat → Maybe Ty → Bool
  okM Y q nothing  = true
  okM Y q (just A) = selAt Y q ∨ not (anyL (selAt Y) (fvTy A))

  allB : Ctx → Sel → Nat → Bool
  allB Q Y zero    = true
  allB Q Y (suc n) = allB Q Y n ∧ okM Y n (lookup Q n)

  lt-low : ∀ q n → T (q <ℕ suc n) → (q ==ℕ n) ≡ false → T (q <ℕ n)
  lt-low zero    zero    _ ()
  lt-low zero    (suc n) _ _ = tt
  lt-low (suc q) zero    () _
  lt-low (suc q) (suc n) l e = lt-low q n l e

  get : ∀ Q Y n q → T (allB Q Y n) → T (q <ℕ n) → T (okM Y q (lookup Q q))
  get Q Y zero    q _ ()
  get Q Y (suc n) q a l with q ==ℕ n in e
  ... | true  = subst (λ m → T (okM Y m (lookup Q m))) (sym (==ℕ-sound q n (subst T (sym e) tt))) (∧-snd {allB Q Y n} a)
  ... | false = get Q Y n q (∧-fst a) (lt-low q n l e)

  not-T : ∀ b → T (false ∨ not b) → b ≡ false
  not-T false _ = refl
  not-T true  ()

upSel? : ∀ Q Y → Q ⊢ctx → Maybe (UpSel Q Y)
upSel? Q Y wQ = go (allB Q Y (len Q)) refl
  where
  go : (b : Bool) → allB Q Y (len Q) ≡ b → Maybe (UpSel Q Y)
  go false _ = nothing
  go true  e = just λ q A lq sq →
    let ok = get Q Y (len Q) q (subst T (sym e) tt) (fst (Sb.ctx-lookup closed wQ lq))
        ok′ = subst (λ m → T (okM Y q m)) lq ok
    in not-T (anyL (selAt Y) (fvTy A)) (subst (λ c → T (c ∨ not (anyL (selAt Y) (fvTy A)))) sq ok′)

-- The generic datum of Q↑Y, typed (for Q with variable boundaries and
-- an up-closed Y of the right length; decided).
genD : (Q : Ctx) → (Y : Sel) → Q ⊢ctx → Maybe (TDatum Q (cylCtx Q Y))
genD Q Y wQ =
  goodCtx? Q >>= λ gQ →
  decℕ (lenSel Y) (len Q) >>= λ eY →
  upSel? Q Y wQ >>= λ up →
  just (go (VB.cylCtx-ok Q Y wQ gQ eY up))
  where
  C = cylCtx Q Y
  go : (C ⊢ctx) × Ty.Hyp.ValidD K0 (C0.gen Y) Q C → TDatum Q C
  go (wC , V) = record { wΔ  = wC
                       ; mmT = C0.genMm Y , Ty.Hyp.ValidD.vmm V
                       ; mpT = C0.genMp Y , Ty.Hyp.ValidD.vmp V
                       ; sel = selAt Y
                       ; thT = λ x → if selAt Y x then thVar (lookupₛ (C0.genTh Y) x) else nothing }
    where
    thVar : Tm → Maybe (TTm C)
    thVar (var i) = varT wC i
    thVar _       = nothing

-- The direct filler: one query (a_c, b_c) on Q↑Y, the cylinders in
-- B's boundaries from the oracle `inner`.
fillDirect : FillO → RecAll → FillO
fillDirect inner rec h Y =
  genD Q Y (hwQ h) >>= λ D → endsT inner D c >>= λ ab → rec (wΔ D) (fst ab) (snd ab)
  where
  Q = hQ h
  B = arr (hA h) (hs h) (hu h)
  c : TTm Q
  c = tt[ C0.cohId Q B ∶ B [ idS (len Q) ]ty , coh-wf (hps h) (hwQ h) (hwB h) (hsd h) (id-wf (hwQ h)) ]

-- The explicit filler of a 1-dimensional coherence (Naturality.DimOne's
-- K₁, typed by K₁-ok), moved to Q↑Y as built here (the two cylinder
-- contexts agree for pasting contexts; the equality is decided).
fill1 : FillO
fill1 h Y = go (hA h) (hwB h) (hsd h)
  where
  Q = hQ h
  go : (A : Ty) → Q ⊢ty arr A (hs h) (hu h) → T (cattSide Q A (hs h) (hu h)) → Maybe (TTm (cylCtx Q Y))
  go (arr _ _ _) _  _  = nothing
  go ⋆           wB sd =
    decℕ (lenSel Y) (len Q) >>= λ eY →
    upSel? Q Y (hwQ h) >>= λ up →
    anyY (anySel Y) refl >>= λ aY →
    decCtx (Cyl.cylCtx D1.K₁ Q Y) (cylCtx Q Y) >>= λ e →
    just tt[ D1.K₁ Q B Y ∶ CyT , subst (λ X → X ⊢tm D1.K₁ Q B Y ∶ CyT) e (D1.K₁-ok (hps h) (hwQ h) wB sd eY up aY tt) ]
    where
    B = arr ⋆ (hs h) (hu h)
    CyT = Cyl.cylTy D1.K₁ (Cyl.gen D1.K₁ Y) (Cyl.cohId D1.K₁ Q B) B
    anyY : (b : Bool) → anySel Y ≡ b → Maybe (T (anySel Y))
    anyY true  e = just (subst T (sym e) tt)
    anyY false _ = nothing

-- Fuel-bounded combination: the explicit 1-dimensional filler, else
-- the direct filler with this oracle for the boundaries.
fillC : Nat → RecAll → FillO
fillC zero    rec h Y = nothing
fillC (suc f) rec h Y = orElse (fill1 h Y) (fillDirect (fillC f rec) rec h Y)
  where
  orElse : ∀ {a} {X : Set a} → Maybe X → Maybe X → Maybe X
  orElse (just x) _ = just x
  orElse nothing  m = m
