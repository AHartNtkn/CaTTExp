------------------------------------------------------------------------
-- Chapter 6's limit heads as operation heads (spec §1.6, §6.1; ledger
-- S27 (b)):
--
--   lim_Γ      arity Γ, type ⋆                                  (lim)
--   λ_{Γ,g}    arity Γ, type: the type of cell g of the cone
--              shape over Γ, with the apex c := lim_Γ[id] and the
--              earlier cells g′ < g := λ_{Γ,g′}[id]           (ucone)
--
-- so that, by rule (op), Δ ⊢ lim_Γ[γ] : ⋆ and λ_{Γ,g}[γ] has the type
-- of cell g of Cone(Γ; lim_Γ[γ])[γ]: together the λ_{Γ,g}[γ] are the
-- universal cone λ : Cone(Γ; lim_Γ[γ])[γ] of §6.1, one head per cell.
--
-- The diagram base Γ is a pure context (CaTTExp.Pure), carried by the
-- head (`limF Γ`, `legF Γ`), and the cone shape is a parameter
-- `shape : P.Ctx → Maybe P.Ctx` returning the whole cone context
-- (Γ, c : ⋆, the cells). Its validity is decided: Γ and the shape are
-- well-formed pure contexts and the shape starts with Γ, c : ⋆. The
-- specified cone of CaTTExp.Cones (globular bases) is the instance used
-- in CaTTExp.Binder.LimHeadsExamples; a cocone shape gives colimits the
-- same way (spec §6.3).
--
-- As a HeadSpec (CaTTExp.Binder.HeadSpec), the family gets BinderLaws,
-- hence substitution, weakening, the certified checker and its
-- completeness, and each valid head's rule is (op), with no proof
-- specific to limits. The universal filler uni (§6.2) has the generic
-- horn H_n(Γ) as arity; it is not encoded here (horns exist in Agda
-- only for the arrow, n ≤ 1, CaTTExp.Lim.Horn; ledger S27, HEADS).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
import CaTTExp.Binder.Syntax as Syn
open import CaTTExp.Binder.HeadSpec using (HeadSpec)

module CaTTExp.Binder.LimHeads where

data LimF : Set where
  limF : P.Ctx → LimF
  legF : P.Ctx → LimF

_==L_ : LimF → LimF → Bool
limF Γ ==L limF Δ = Γ P.==Ctx Δ
legF Γ ==L legF Δ = Γ P.==Ctx Δ
_      ==L _      = false

==L-sound : ∀ a b → T (a ==L b) → a ≡ b
==L-sound (limF Γ) (limF Δ) p = cong limF (P.==Ctx-sound Γ Δ p)
==L-sound (legF Γ) (legF Δ) p = cong legF (P.==Ctx-sound Γ Δ p)

-- Pure syntax inside the syntax over any constants and formers.
module PureEmb (K B : Set) where
  open Syn K B

  mutual
    peTy : P.Ty → Ty
    peTy P.⋆           = ⋆
    peTy (P.arr A t u) = arr (peTy A) (peTm t) (peTm u)

    peTm : P.Tm → Tm
    peTm (P.var i)     = var i
    peTm (P.coh Θ A τ) = coh (peCtx Θ) (peTy A) (peSub τ)
    peTm (P.cst ())

    peCtx : P.Ctx → Ctx
    peCtx P.ε       = ε
    peCtx (Γ P.▸ A) = peCtx Γ ▸ peTy A

    peSub : P.Sub → Sub
    peSub P.⟨⟩       = ⟨⟩
    peSub (σ P.,ₛ t) = peSub σ ,ₛ peTm t

-- The construction, over any former set into which LimF injects.
module LimConstruction (K B : Set) (inj : LimF → B) (shape : P.Ctx → Maybe P.Ctx) where
  open Syn K B
  open PureEmb K B

  -- The first k entries of a context (dropping from the right).
  dropR : Nat → P.Ctx → P.Ctx
  dropR zero    Γ         = Γ
  dropR (suc k) P.ε       = P.ε
  dropR (suc k) (Γ P.▸ _) = dropR k Γ

  -- The decided validity of a shape at Γ: Γ and K are well formed and
  -- K starts with Γ, c : ⋆.
  shapeOK : P.Ctx → P.Ctx → Bool
  shapeOK Γ K =
    is-just (P.checkCtx Γ) ∧ is-just (P.checkCtx K) ∧
    (suc (P.len Γ) <ℕ suc (P.len K)) ∧
    (dropR (P.len K ∸ suc (P.len Γ)) K P.==Ctx (Γ P.▸ P.⋆))

  -- lim_Γ[id_Γ] and λ_{Γ,j}[id_Γ].
  limId : P.Ctx → Tm
  limId Γ = bnd (inj (limF Γ)) 0 ε (fresh 0 (P.len Γ))

  legId : P.Ctx → Nat → Tm
  legId Γ j = bnd (inj (legF Γ)) j ε (fresh 0 (P.len Γ))

  -- The substitution from the first len Γ + 1 + g entries of the cone
  -- context to Γ: variables of Γ to themselves, the apex to lim_Γ[id],
  -- the cells before g to the legs.
  coneSub : P.Ctx → Nat → Sub
  coneSub Γ zero    = fresh 0 (P.len Γ) ,ₛ limId Γ
  coneSub Γ (suc g) = coneSub Γ g ,ₛ legId Γ g

  -- The type of cell g of the shape over Γ.
  cellTy : P.Ctx → Nat → Maybe P.Ty
  cellTy Γ g = shape Γ >>= λ K → P.lookup K (suc (P.len Γ + g))

  hctx : LimF → Nat → Ctx
  hctx (limF Γ) _ = peCtx Γ
  hctx (legF Γ) _ = peCtx Γ

  hty : LimF → Nat → Ty
  hty (limF Γ) _ = ⋆
  hty (legF Γ) g with cellTy Γ g
  ... | just A  = peTy A [ coneSub Γ g ]ty
  ... | nothing = ⋆

  hok : LimF → Nat → Bool
  hok (limF Γ) y = (y ==ℕ 0) ∧ is-just (P.checkCtx Γ)
  hok (legF Γ) g with shape Γ
  ... | just K  = shapeOK Γ K ∧ is-just (P.lookup K (suc (P.len Γ + g)))
  ... | nothing = false

limSpec : (K : Set) (shape : P.Ctx → Maybe P.Ctx) → HeadSpec K
limSpec K shape = record
  { H         = LimF
  ; _==H_     = _==L_
  ; ==H-sound = ==L-sound
  ; hctx      = hctx
  ; hty       = hty
  ; hok       = hok
  }
  where open LimConstruction K LimF (λ b → b) shape
