------------------------------------------------------------------------
-- INIT and DES in one signature, with INIT's invertibility rules
-- (ledger S26e step 3, spec §9.3).
--
-- The formers are INIT's and DES's side by side (`IDF`); each interface
-- is the one of CaTTExp.Binder.Init / CaTTExp.Binder.Des over this
-- former set (both constructions are generic in it, by an injection),
-- and the stability laws are theirs, former by former
-- (CaTTExp.Binder.InitLawsGen, CaTTExp.Binder.DesLawsGen).
--
-- Marks of former occurrences (`formerMarks` of CaTTExp.Gray.MarksB):
--
--   μ_k, η_y      the marks of entry k, y of the telescope: the generic
--                 model satisfies the telescope's marks (a sort marked
--                 grpd₁ gives μ_k grpd₁; an operation marked inv gives
--                 η_y inv);
--   rec_k         none (a map out of μ, not invertible in general);
--   rec_y, uni,   inv (INIT-J1/J2: the naturality cells of rec, and the
--   uni_y         modification between two morphisms out of μ and its
--                 components, are invertible);
--   DES           inv ((DES), (DES-inv)).
--
-- These are syntax-directed axioms on the head former, so the mark
-- judgment stays decidable. Since a destructor's argument entry is
-- marked inv and the kernel checks it through the mark judgment, the
-- inverses rec_y⁻ˡ, uni⁻ˡ, uni_y⁻ˡ, … are well typed (CaTTExp.Binder.
-- InitDesExamples).
--
-- `formerMarks` does not see a substitution of the telescope (the
-- marks are read off its entries, which substitution keeps), and
-- INIT's formers have no cell argument, so CaTTExp.Gray.MarksBKernel
-- gives MarkSub and MarkRen, and substitution holds for L + INIT + DES
-- with these marks, under the same parameters as for DES alone
-- (CaTTExp.Gray.MarksBDes): constants closed, and presupposition of
-- the mark-free kernel (ledger S26i).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Des
import CaTTExp.Binder.Syntax as NSyn
import CaTTExp.Binder.Laws
import CaTTExp.Binder.SyntaxLemmas
import CaTTExp.Binder.InitLawsGen
import CaTTExp.Binder.DesLawsGen
import CaTTExp.Binder.Rename
import CaTTExp.Binder.Subst
import CaTTExp.Gray.MarksB
import CaTTExp.Gray.MarksBSubst
import CaTTExp.Gray.MarksBKernel
import CaTTExp.Gray.DimB
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s)

module CaTTExp.Binder.InitDes where

------------------------------------------------------------------------
-- The formers.

data IDF : Set where
  ini : Former → IDF
  dz  : DesF → IDF

_==I_ : IDF → IDF → Bool
ini b ==I ini c = b ==F c
dz b  ==I dz c  = b ==D c
_     ==I _     = false

==I-sound : ∀ b c → T (b ==I c) → b ≡ c
==I-sound (ini b) (ini c) p = cong ini (==F-sound b c p)
==I-sound (dz b)  (dz c)  p = cong dz (==D-sound b c p)
==I-sound (ini _) (dz _)  ()
==I-sound (dz _)  (ini _) ()

==I-refl : ∀ b → T (b ==I b)
==I-refl (ini b) = ==F-refl b
==I-refl (dz b)  = ==D-refl b

------------------------------------------------------------------------
-- The interface, over constants K with a test for ⊤.

module Interface (K : Set) (top? : K → Bool) where

  open NSyn K IDF
  module IC = Construction K IDF ini top?
  module DC = DesConstruction K IDF dz

  side : IDF → Nat → Ctx → Bool
  side (ini b) = IC.side b
  side (dz b)  = DC.side b

  args : IDF → Nat → Ctx → Ctx
  args (ini b) = IC.args b
  args (dz b)  = DC.args b

  res : IDF → Nat → Ctx → Ty
  res (ini b) = IC.res b
  res (dz b)  = DC.res b

  initDesBinders : Binders K
  initDesBinders = record
    { B = IDF ; _==B_ = _==I_ ; ==B-sound = ==I-sound
    ; bside = side ; bargs = args ; bres = res
    }

  -- The marks of an occurrence, by its former.
  initDesMarks : IDF → Nat → Ctx → List Mark
  initDesMarks (ini μ)    y Δ = marksAt Δ y
  initDesMarks (ini η)    y Δ = marksAt Δ y
  initDesMarks (ini rec)  y Δ = []
  initDesMarks (ini recY) y Δ = minv ∷ []
  initDesMarks (ini uni)  y Δ = minv ∷ []
  initDesMarks (ini uniY) y Δ = minv ∷ []
  initDesMarks (dz _)     y Δ = minv ∷ []

  -- Erasure to L: DES's destructors to their cell; INIT's formers have
  -- no cell argument (L's coh rule rejects them).
  cellArgI : IDF → Maybe Nat
  cellArgI (ini _) = nothing
  cellArgI (dz b)  = cellArgD b

------------------------------------------------------------------------
-- Over a binder-free base signature 𝕊₀ (L's, for the Gray marks).

module Over (𝕊₀ : Old.Signature) (top? : Old.Signature.K 𝕊₀ → Bool) where

  open Interface (Old.Signature.K 𝕊₀) top? public

  bi : Binders (Old.Signature.K 𝕊₀)
  bi = initDesBinders

  𝕊 : Signature
  𝕊 = extend 𝕊₀ bi

  open Signature 𝕊
  open CaTTExp.Binder.Laws 𝕊 using (BinderLaws; Closed)
  private
    module IL = CaTTExp.Binder.InitLawsGen K IDF ini top?
    module DL = CaTTExp.Binder.DesLawsGen K IDF dz

  -- The stability laws, former by former.
  laws : BinderLaws
  laws = record
    { side-stable = λ { (ini b) → IL.side-stableI b ; (dz b) → DL.side-stableD b }
    ; args-stable = λ { (ini b) → IL.args-stableI b ; (dz b) → DL.args-stableD b }
    ; res-stable  = λ { (ini b) → IL.res-stableI b  ; (dz b) → DL.res-stableD b }
    ; res-sc      = λ { (ini b) → IL.res-scI b      ; (dz b) → DL.res-scD b }
    }

  ----------------------------------------------------------------------
  -- The Gray mark judgment with INIT's and DES's former marks.

  open CaTTExp.Gray.MarksB 𝕊₀ bi cellArgI initDesMarks public using (mark; judge; judgeT; markVar)
  module Kernel = CaTTExp.Gray.MarksB.Kernel 𝕊₀ bi cellArgI initDesMarks
  open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArgI using (graySideD) public
  private
    module MS = CaTTExp.Gray.MarksBSubst 𝕊₀ bi cellArgI initDesMarks
    module MK = CaTTExp.Gray.MarksBKernel 𝕊₀ bi cellArgI initDesMarks
    module DB = CaTTExp.Gray.DimB 𝕊₀ bi cellArgI
    module RR = CaTTExp.Binder.Rename 𝕊 graySideD mark
    module RS = CaTTExp.Binder.Subst 𝕊 graySideD mark
    module SL = CaTTExp.Binder.SyntaxLemmas K B

  -- Substitution keeps the marks of the telescope's entries.
  marksAt-[] : ∀ Δ σ y → marksAt (Δ [ σ ]tel) y ≡ marksAt Δ y
  marksAt-[] ε              σ y = refl
  marksAt-[] (Δ ▸[ ms ] A) σ y rewrite SL.len-tel[] Δ σ | marksAt-[] Δ σ y = refl

  fstab : MS.FormerStable
  fstab (ini μ)    y Δ σ = marksAt-[] Δ σ y
  fstab (ini η)    y Δ σ = marksAt-[] Δ σ y
  fstab (ini rec)  y Δ σ = refl
  fstab (ini recY) y Δ σ = refl
  fstab (ini uni)  y Δ σ = refl
  fstab (ini uniY) y Δ σ = refl
  fstab (dz _)     y Δ σ = refl

  ----------------------------------------------------------------------
  -- A destructor's cell is no higher than its result (as in
  -- CaTTExp.Gray.MarksBDes); INIT's formers have no cell argument.

  private
    open DesConstruction K IDF dz using (tyB; diskB; argsD)

    +-suc : ∀ a b → a + suc b ≡ suc (a + b)
    +-suc zero    b = refl
    +-suc (suc a) b = cong suc (+-suc a b)

    len-diskB : ∀ n → len (diskB n) ≡ suc (n + n)
    len-diskB zero    = refl
    len-diskB (suc n) = cong (λ m → suc (suc m)) (trans (len-diskB n) (sym (+-suc n n)))

    dim-tyB : ∀ n → dim (tyB n) ≡ n
    dim-tyB zero    = refl
    dim-tyB (suc n) = cong suc (dim-tyB n)

    look-cell : ∀ n → lookup (argsD n) (suc n + suc n) ≡ just (tyB (suc n))
    look-cell n with suc n + suc n ==ℕ suc (len (diskB n)) in e
    ... | true  = refl
    ... | false = ⊥-elim (subst T e (subst (λ m → T (suc n + suc n ==ℕ m)) eqn (==ℕ-refl (suc n + suc n))))
      where
      eqn : suc n + suc n ≡ suc (len (diskB n))
      eqn = trans (cong suc (+-suc n n)) (cong suc (sym (len-diskB n)))

    just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
    just-inj refl = refl

    ≤-refl : ∀ n → n ≤ n
    ≤-refl zero    = z≤n
    ≤-refl (suc n) = s≤s (≤-refl n)

    ≤-suc : ∀ n → n ≤ suc n
    ≤-suc zero    = z≤n
    ≤-suc (suc n) = s≤s (≤-suc n)

  cellDim : DB.CellDim
  cellDim (ini _)          y Θ j C () ok eC
  cellDim (dz (des k zero))    y Θ j C ec ()
  cellDim (dz (des k (suc n))) y Θ j C refl ok eC
    with just-inj (trans (sym (look-cell n)) eC)
  ... | refl = res-dim k
    where
    res-dim : ∀ k → dim (tyB (suc n)) ≤ dim (res (dz (des k (suc n))) y Θ)
    res-dim linvK  rewrite dim-tyB n = ≤-refl (suc n)
    res-dim rinvK  rewrite dim-tyB n = ≤-refl (suc n)
    res-dim unitLK rewrite dim-tyB n = ≤-suc (suc n)
    res-dim unitRK rewrite dim-tyB n = ≤-suc (suc n)

  ----------------------------------------------------------------------
  -- The kernel hypotheses, and substitution for L + INIT + DES.

  module _ (closed : Closed) (tm-ty : ∀ {Γ t A} → Γ MS.Fg.F.⊢tm t ∶ A → Γ MS.Fg.F.⊢ty A) where

    private
      dimOK = DB.dimOK cellDim tm-ty

    markSub : RS.MarkSub
    markSub {Γ} {Δ} {σ} {t} {A} {m} = MK.markSub closed laws fstab tm-ty dimOK {Γ} {Δ} {σ} {t} {A} {m}

    markRen : RR.MarkRen
    markRen {Γ} {Γ′} {ρ} {t} {A} {m} = MK.markRen closed laws fstab tm-ty dimOK {Γ} {Γ′} {ρ} {t} {A} {m}

    -- Substitution in two-tier L with INIT, destructors and their marks.
    tm[] : ∀ {Γ Δ t A σ} → Γ Kernel.⊢tm t ∶ A → Δ Kernel.⊢sub σ ∶ Γ → Δ Kernel.⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[] = RS.tm[] closed laws (λ {Γ} {Γ′} {ρ} {t} {A} {m} → markRen {Γ} {Γ′} {ρ} {t} {A} {m})
                               (λ {Γ} {Δ} {σ} {t} {A} {m} → markSub {Γ} {Δ} {σ} {t} {A} {m}) markVar
