------------------------------------------------------------------------
-- Conservativity of binders over the binder-free kernel.
--
-- Any signature 𝕊₀ of CaTTExp.Signature, extended with any binder
-- interface (`extend`), embeds into the kernel with binders: the
-- embedding e of syntax preserves and reflects every judgment,
--
--   Γ ⊢ctx                ⇔  e Γ ⊢ctx
--   Γ ⊢ty A               ⇔  e Γ ⊢ty e A
--   Γ ⊢tm t ∶ A           ⇔  e Γ ⊢tm e t ∶ e A
--   Γ ⊢sub σ ∶ Δ          ⇔  e Γ ⊢sub e σ ∶ e Δ
--   Δ ⊢ps                 ⇔  e Δ ⊢ps
--
-- provided the two coh side conditions agree on embedded syntax
-- (`Agree`). Plain CaTT's side condition does (`cattSide-agree`), so
-- for CaTT itself the statement is unconditional (`CaTT`). Reflection
-- also says that a binder-free term of the extended theory has only
-- binder-free types (`tm-types`): adding binders derives nothing new
-- about the binder-free fragment.
--
-- Pasting contexts are compared through pure syntax (CaTTExp.Pure),
-- which both kernels' pasting judgments contain (`PEmb`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Syntax as OSyn
import CaTTExp.Binder.Syntax as NSyn
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
import CaTTExp.TypingWith
import CaTTExp.Typing
import CaTTExp.Binder.Typing
import CaTTExp.Pasting
import CaTTExp.Binder.TypingWith
import CaTTExp.Binder.Pasting

module CaTTExp.Binder.Embed where

------------------------------------------------------------------------
-- The embedding of syntax, and its left inverse.

module Emb (K B : Set) where
  private
    module O = OSyn K
    module N = NSyn K B

  mutual
    eTy : O.Ty → N.Ty
    eTy O.⋆           = N.⋆
    eTy (O.arr A t u) = N.arr (eTy A) (eTm t) (eTm u)

    eTm : O.Tm → N.Tm
    eTm (O.var i)     = N.var i
    eTm (O.coh Γ A σ) = N.coh (eCtx Γ) (eTy A) (eSub σ)
    eTm (O.cst k)     = N.cst k

    eCtx : O.Ctx → N.Ctx
    eCtx O.ε       = N.ε
    eCtx (Γ O.▸ A) = eCtx Γ N.▸ eTy A

    eSub : O.Sub → N.Sub
    eSub O.⟨⟩       = N.⟨⟩
    eSub (σ O.,ₛ t) = eSub σ N.,ₛ eTm t

  mutual
    uTy : N.Ty → Maybe O.Ty
    uTy N.⋆           = just O.⋆
    uTy (N.arr A t u) = uTy A >>= λ A₀ → uTm t >>= λ t₀ → uTm u >>= λ u₀ → just (O.arr A₀ t₀ u₀)

    uTm : N.Tm → Maybe O.Tm
    uTm (N.var i)       = just (O.var i)
    uTm (N.bvar _ _)    = nothing
    uTm (N.coh Γ A σ)   = uCtx Γ >>= λ Γ₀ → uTy A >>= λ A₀ → uSub σ >>= λ σ₀ → just (O.coh Γ₀ A₀ σ₀)
    uTm (N.cst k)       = just (O.cst k)
    uTm (N.bnd _ _ _ _) = nothing

    uCtx : N.Ctx → Maybe O.Ctx
    uCtx N.ε       = just O.ε
    uCtx (Γ N.▸ A) = uCtx Γ >>= λ Γ₀ → uTy A >>= λ A₀ → just (Γ₀ O.▸ A₀)

    uSub : N.Sub → Maybe O.Sub
    uSub N.⟨⟩       = just O.⟨⟩
    uSub (σ N.,ₛ t) = uSub σ >>= λ σ₀ → uTm t >>= λ t₀ → just (σ₀ O.,ₛ t₀)

  mutual
    ue-ty : ∀ A → uTy (eTy A) ≡ just A
    ue-ty O.⋆ = refl
    ue-ty (O.arr A t u) rewrite ue-ty A | ue-tm t | ue-tm u = refl

    ue-tm : ∀ t → uTm (eTm t) ≡ just t
    ue-tm (O.var i) = refl
    ue-tm (O.coh Γ A σ) rewrite ue-ctx Γ | ue-ty A | ue-sub σ = refl
    ue-tm (O.cst k) = refl

    ue-ctx : ∀ Γ → uCtx (eCtx Γ) ≡ just Γ
    ue-ctx O.ε = refl
    ue-ctx (Γ O.▸ A) rewrite ue-ctx Γ | ue-ty A = refl

    ue-sub : ∀ σ → uSub (eSub σ) ≡ just σ
    ue-sub O.⟨⟩ = refl
    ue-sub (σ O.,ₛ t) rewrite ue-sub σ | ue-tm t = refl

  private
    inj : ∀ {X Y : Set} (e : X → Y) (u : Y → Maybe X) → (∀ x → u (e x) ≡ just x) →
          ∀ {x y} → e x ≡ e y → x ≡ y
    inj e u ue {x} {y} p = just-inj (trans (sym (ue x)) (trans (cong u p) (ue y)))
      where
      just-inj : ∀ {a b : _} → just a ≡ just b → a ≡ b
      just-inj refl = refl

  eTy-inj : ∀ {A A′} → eTy A ≡ eTy A′ → A ≡ A′
  eTy-inj = inj eTy uTy ue-ty

  eCtx-inj : ∀ {Γ Γ′} → eCtx Γ ≡ eCtx Γ′ → Γ ≡ Γ′
  eCtx-inj = inj eCtx uCtx ue-ctx

  ----------------------------------------------------------------------
  -- The embedding commutes with the operations on syntax.

  mapM : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
  mapM f nothing  = nothing
  mapM f (just x) = just (f x)

  len-e : ∀ Γ → N.len (eCtx Γ) ≡ O.len Γ
  len-e O.ε       = refl
  len-e (Γ O.▸ _) = cong suc (len-e Γ)

  lenₛ-e : ∀ σ → N.lenₛ (eSub σ) ≡ O.lenₛ σ
  lenₛ-e O.⟨⟩       = refl
  lenₛ-e (σ O.,ₛ _) = cong suc (lenₛ-e σ)

  lookup-e : ∀ Γ i → N.lookup (eCtx Γ) i ≡ mapM eTy (O.lookup Γ i)
  lookup-e O.ε i = refl
  lookup-e (Γ O.▸ A) i rewrite len-e Γ with i ==ℕ O.len Γ
  ... | true  = refl
  ... | false = lookup-e Γ i

  lookupₛ-e : ∀ σ i → N.lookupₛ (eSub σ) i ≡ eTm (O.lookupₛ σ i)
  lookupₛ-e O.⟨⟩ i = refl
  lookupₛ-e (σ O.,ₛ t) i rewrite lenₛ-e σ with i ==ℕ O.lenₛ σ
  ... | true  = refl
  ... | false = lookupₛ-e σ i

  mutual
    e-[]ty : ∀ A σ → eTy (A O.[ σ ]ty) ≡ eTy A N.[ eSub σ ]ty
    e-[]ty O.⋆ σ = refl
    e-[]ty (O.arr A t u) σ rewrite e-[]ty A σ | e-[]tm t σ | e-[]tm u σ = refl

    e-[]tm : ∀ t σ → eTm (t O.[ σ ]tm) ≡ eTm t N.[ eSub σ ]tm
    e-[]tm (O.var i) σ = sym (lookupₛ-e σ i)
    e-[]tm (O.coh Γ A τ) σ rewrite e-∘ τ σ = refl
    e-[]tm (O.cst k) σ = refl

    e-∘ : ∀ τ σ → eSub (τ O.∘ σ) ≡ eSub τ N.∘ eSub σ
    e-∘ O.⟨⟩ σ = refl
    e-∘ (τ O.,ₛ t) σ rewrite e-∘ τ σ | e-[]tm t σ = refl

  dim-e : ∀ A → N.dim (eTy A) ≡ O.dim A
  dim-e O.⋆           = refl
  dim-e (O.arr A _ _) = cong suc (dim-e A)

  dimCtx-e : ∀ Γ → N.dimCtx (eCtx Γ) ≡ O.dimCtx Γ
  dimCtx-e O.ε       = refl
  dimCtx-e (Γ O.▸ A) rewrite dim-e A | dimCtx-e Γ = refl

  mutual
    fvTy-e : ∀ A → N.fvTy (eTy A) ≡ O.fvTy A
    fvTy-e O.⋆ = refl
    fvTy-e (O.arr A t u) rewrite fvTy-e A | fvTm-e t | fvTm-e u = refl

    fvTm-e : ∀ t → N.fvTm (eTm t) ≡ O.fvTm t
    fvTm-e (O.var i)     = refl
    fvTm-e (O.coh _ _ σ) = fvSub-e σ
    fvTm-e (O.cst _)     = refl

    fvSub-e : ∀ σ → N.fvSub (eSub σ) ≡ O.fvSub σ
    fvSub-e O.⟨⟩ = refl
    fvSub-e (σ O.,ₛ t) rewrite fvSub-e σ | fvTm-e t = refl

  fvTmTy-e : ∀ t A → N.fvTmTy (eTm t) (eTy A) ≡ O.fvTmTy t A
  fvTmTy-e t A rewrite fvTm-e t | fvTy-e A = refl

  downFrom-e : ∀ n → N.downFrom n ≡ O.downFrom n
  downFrom-e zero    = refl
  downFrom-e (suc n) = cong (n ∷_) (downFrom-e n)

  varsCtx-e : ∀ Γ → N.varsCtx (eCtx Γ) ≡ O.varsCtx Γ
  varsCtx-e Γ = trans (cong N.downFrom (len-e Γ)) (downFrom-e (O.len Γ))

  srcVars-e : ∀ i Γ → N.srcVars i (eCtx Γ) ≡ O.srcVars i Γ
  srcVars-e i O.ε                 = refl
  srcVars-e i (O.ε O.▸ _)         = refl
  srcVars-e i (Γ O.▸ A O.▸ _) rewrite dim-e A | len-e Γ | srcVars-e i Γ = refl

  dropLast-e : ∀ xs → N.dropLastᴸ xs ≡ O.dropLastᴸ xs
  dropLast-e []           = refl
  dropLast-e (x ∷ [])     = refl
  dropLast-e (x ∷ y ∷ xs) = cong (x ∷_) (dropLast-e (y ∷ xs))

  tgtVars-e : ∀ i Γ → N.tgtVars i (eCtx Γ) ≡ O.tgtVars i Γ
  tgtVars-e i O.ε                 = refl
  tgtVars-e i (O.ε O.▸ _)         = refl
  tgtVars-e i (Γ O.▸ A O.▸ _) rewrite dim-e A | len-e Γ | tgtVars-e i Γ | dropLast-e (O.tgtVars i Γ) = refl

  ∂⁻-e : ∀ Γ → N.∂⁻ (eCtx Γ) ≡ O.∂⁻ Γ
  ∂⁻-e Γ rewrite dimCtx-e Γ = srcVars-e _ Γ

  ∂⁺-e : ∀ Γ → N.∂⁺ (eCtx Γ) ≡ O.∂⁺ Γ
  ∂⁺-e Γ rewrite dimCtx-e Γ = tgtVars-e _ Γ

------------------------------------------------------------------------
-- Pure syntax (no constants) inside any binder-free syntax, and pasting
-- derivations across the two: pasting contexts mention variables only.

module PEmb (𝕊₀ : Old.Signature) where
  private
    module O  = Old.Signature 𝕊₀
    module OP = CaTTExp.Pasting 𝕊₀
    module PP = CaTTExp.Pasting P.∅

  mutual
    pTy : P.Ty → O.Ty
    pTy P.⋆           = O.⋆
    pTy (P.arr A t u) = O.arr (pTy A) (pTm t) (pTm u)

    pTm : P.Tm → O.Tm
    pTm (P.var i)     = O.var i
    pTm (P.coh Γ A σ) = O.coh (pCtx Γ) (pTy A) (pSub σ)
    pTm (P.cst ())

    pCtx : P.Ctx → O.Ctx
    pCtx P.ε       = O.ε
    pCtx (Γ P.▸ A) = pCtx Γ O.▸ pTy A

    pSub : P.Sub → O.Sub
    pSub P.⟨⟩       = O.⟨⟩
    pSub (σ P.,ₛ t) = pSub σ O.,ₛ pTm t

  len-p : ∀ Γ → O.len (pCtx Γ) ≡ P.len Γ
  len-p P.ε       = refl
  len-p (Γ P.▸ _) = cong suc (len-p Γ)

  up : ∀ {Γ x A} → Γ PP.⊢ps x ∶ A → pCtx Γ OP.⊢ps x ∶ pTy A
  up PP.pss = OP.pss
  up (PP.pse {Γ} d) rewrite sym (len-p Γ) = OP.pse (up d)
  up (PP.psd d) = OP.psd (up d)

  private
    inv-arr : ∀ Bp {A x y} → pTy Bp ≡ O.arr A (O.var x) (O.var y) →
              Σ P.Ty λ Ap → (Bp ≡ P.arr Ap (P.var x) (P.var y)) × (pTy Ap ≡ A)
    inv-arr (P.arr Ap (P.var _) (P.var _)) refl = Ap , refl , refl

  down : ∀ {Γ x A} → Γ OP.⊢ps x ∶ A →
         Σ P.Ctx λ Γp → Σ P.Ty λ Ap → (pCtx Γp ≡ Γ) × (pTy Ap ≡ A) × (Γp PP.⊢ps x ∶ Ap)
  down OP.pss = (P.ε P.▸ P.⋆) , P.⋆ , refl , refl , PP.pss
  down (OP.pse d) with down d
  ... | Γp , Ap , refl , refl , dp rewrite len-p Γp =
    (Γp P.▸ Ap P.▸ P.arr Ap (P.var _) (P.var (P.len Γp))) , P.arr Ap (P.var _) (P.var (P.len Γp)) ,
    refl , refl , PP.pse dp
  down (OP.psd d) with down d
  ... | Γp , Bp , refl , eB , dp with inv-arr Bp eB
  ...   | Ap , refl , eA = Γp , Ap , refl , eA , PP.psd dp

------------------------------------------------------------------------
-- A binder interface over constants K, and the extension of a
-- binder-free signature by it.

record Binders (K : Set) : Set₁ where
  field
    B         : Set
    _==B_     : B → B → Bool
    ==B-sound : ∀ b c → T (b ==B c) → b ≡ c
    bside     : B → Nat → NSyn.Ctx K B → Bool
    bargs     : B → Nat → NSyn.Ctx K B → NSyn.Ctx K B
    bres      : B → Nat → NSyn.Ctx K B → NSyn.Ty K B

extend : (𝕊₀ : Old.Signature) → Binders (Old.Signature.K 𝕊₀) → Signature
extend 𝕊₀ bi = record
  { K         = K
  ; _==K_     = _==K_
  ; ==K-sound = ==K-sound
  ; B         = B
  ; _==B_     = _==B_
  ; ==B-sound = ==B-sound
  ; ty        = λ k → Emb.eTy K B (ty k)
  ; Valid     = Valid
  ; valid?    = valid?
  ; bside     = bside
  ; bargs     = bargs
  ; bres      = bres
  }
  where
  open Old.Signature 𝕊₀
  open Binders bi

------------------------------------------------------------------------
-- Preservation and reflection.

module Conservative
  (𝕊₀ : Old.Signature)
  (bi : Binders (Old.Signature.K 𝕊₀))
  (side₀ : Old.Signature.Ctx 𝕊₀ → Old.Signature.Ty 𝕊₀ → Old.Signature.Tm 𝕊₀ → Old.Signature.Tm 𝕊₀ → Bool)
  (side : Signature.Ctx (extend 𝕊₀ bi) → Signature.Ty (extend 𝕊₀ bi) →
          Signature.Tm (extend 𝕊₀ bi) → Signature.Tm (extend 𝕊₀ bi) → Bool)
  where

  𝕊 : Signature
  𝕊 = extend 𝕊₀ bi

  private
    module O  = Old.Signature 𝕊₀
    module OT = CaTTExp.TypingWith 𝕊₀ side₀
    module N  = Signature 𝕊
    module NT = CaTTExp.Binder.TypingWith 𝕊 side
    module BP = CaTTExp.Binder.Pasting 𝕊
    module PP = CaTTExp.Pasting P.∅
    open module E = Emb O.K (Binders.B bi)
    open PEmb 𝕊₀

  -- The two side conditions agree on binder-free syntax.
  Agree : Set
  Agree = ∀ Δ A t u → side (eCtx Δ) (eTy A) (eTm t) (eTm u) ≡ side₀ Δ A t u

  ----------------------------------------------------------------------
  -- Pasting contexts.

  private
    mutual
      ep-ty : ∀ A → eTy (pTy A) ≡ BP.embTy A
      ep-ty P.⋆ = refl
      ep-ty (P.arr A t u) rewrite ep-ty A | ep-tm t | ep-tm u = refl

      ep-tm : ∀ t → eTm (pTm t) ≡ BP.embTm t
      ep-tm (P.var i) = refl
      ep-tm (P.coh Γ A σ) rewrite ep-ctx Γ | ep-ty A | ep-sub σ = refl
      ep-tm (P.cst ())

      ep-ctx : ∀ Γ → eCtx (pCtx Γ) ≡ BP.embCtx Γ
      ep-ctx P.ε = refl
      ep-ctx (Γ P.▸ A) rewrite ep-ctx Γ | ep-ty A = refl

      ep-sub : ∀ σ → eSub (pSub σ) ≡ BP.embSub σ
      ep-sub P.⟨⟩ = refl
      ep-sub (σ P.,ₛ t) rewrite ep-sub σ | ep-tm t = refl

    ⋆-p : ∀ Ap → pTy Ap ≡ O.⋆ → Ap ≡ P.⋆
    ⋆-p P.⋆ _ = refl

  ps-pres : ∀ {Δ} → Δ OT.⊢ps → eCtx Δ BP.⊢ps
  ps-pres (OT.ps d) with down d
  ... | Γp , Ap , refl , eA , dp rewrite ⋆-p Ap eA =
    Γp , trans (cong BP.toPure (ep-ctx Γp)) (BP.toPure-ps dp) , PP.ps dp

  ps-reflect : ∀ {Δ} → eCtx Δ BP.⊢ps → Δ OT.⊢ps
  ps-reflect {Δ} (Δp , e , PP.ps d) =
    subst OT._⊢ps (eCtx-inj (trans (ep-ctx Δp) (BP.toPure-sound (eCtx Δ) e))) (OT.ps (up d))

  module Theorems (agree : Agree) where

    ----------------------------------------------------------------------
    -- Preservation.

    private
      lookup-pres : ∀ Γ i {A} → O.lookup Γ i ≡ just A → N.lookup (eCtx Γ) i ≡ just (eTy A)
      lookup-pres Γ i e rewrite lookup-e Γ i | e = refl

    mutual
      ctx-pres : ∀ {Γ} → Γ OT.⊢ctx → eCtx Γ NT.⊢ctx
      ctx-pres OT.ε-wf       = NT.ε-wf
      ctx-pres (OT.▸-wf w a) = NT.▸-wf (ctx-pres w) (ty-pres a)

      ty-pres : ∀ {Γ A} → Γ OT.⊢ty A → eCtx Γ NT.⊢ty eTy A
      ty-pres (OT.⋆-wf w)    = NT.⋆-wf (ctx-pres w)
      ty-pres (OT.arr-wf d e) = NT.arr-wf (tm-pres d) (tm-pres e)

      tm-pres : ∀ {Γ t A} → Γ OT.⊢tm t ∶ A → eCtx Γ NT.⊢tm eTm t ∶ eTy A
      tm-pres {Γ} (OT.var-wf {i} w e) = NT.var-wf (ctx-pres w) (lookup-pres Γ i e)
      tm-pres {Γ} (OT.coh-wf {Δ} {A} {t} {u} {σ} p w a ok s) =
        subst (eCtx Γ NT.⊢tm eTm (O.coh Δ (O.arr A t u) σ) ∶_) (sym (e-[]ty (O.arr A t u) σ))
          (NT.coh-wf (ps-pres p) (ctx-pres w) (ty-pres a) ok′ (sub-pres s))
        where
        ok′ : T (side (eCtx Δ) (eTy A) (eTm t) (eTm u))
        ok′ = subst T (sym (agree Δ A t u)) ok
      tm-pres (OT.cst-wf w v) = NT.cst-wf (ctx-pres w) v

      sub-pres : ∀ {Γ σ Δ} → Γ OT.⊢sub σ ∶ Δ → eCtx Γ NT.⊢sub eSub σ ∶ eCtx Δ
      sub-pres (OT.⟨⟩-wf w) = NT.⟨⟩-wf (ctx-pres w)
      sub-pres {Γ} (OT.,-wf {σ} {Δ} {t} {A} s d) =
        NT.,-wf (sub-pres s) (subst (eCtx Γ NT.⊢tm eTm t ∶_) (e-[]ty A σ) (tm-pres d))

    --------------------------------------------------------------------
    -- Reflection: a derivation about embedded syntax comes from one in
    -- the binder-free theory.

    private
      mapM-just : ∀ m {A′} → mapM eTy m ≡ just A′ → Σ O.Ty λ A → (eTy A ≡ A′) × (m ≡ just A)
      mapM-just (just A) refl = A , refl , refl

      lookup-refl : ∀ Γ i {A′} → N.lookup (eCtx Γ) i ≡ just A′ →
                    Σ O.Ty λ A → (eTy A ≡ A′) × (O.lookup Γ i ≡ just A)
      lookup-refl Γ i e = mapM-just (O.lookup Γ i) (trans (sym (lookup-e Γ i)) e)

    mutual
      ctx-reflect : ∀ {Γ′} → Γ′ NT.⊢ctx → ∀ {Γ} → eCtx Γ ≡ Γ′ → Γ OT.⊢ctx
      ctx-reflect NT.ε-wf {O.ε} refl = OT.ε-wf
      ctx-reflect NT.ε-wf {_ O.▸ _} ()
      ctx-reflect (NT.▸-wf w a) {Γ O.▸ A} refl = OT.▸-wf (ctx-reflect w refl) (ty-reflect a refl refl)
      ctx-reflect (NT.▸-wf w a) {O.ε} ()

      ty-reflect : ∀ {Γ′ A′} → Γ′ NT.⊢ty A′ → ∀ {Γ A} → eCtx Γ ≡ Γ′ → eTy A ≡ A′ → Γ OT.⊢ty A
      ty-reflect (NT.⋆-wf w) {A = O.⋆} eΓ refl = OT.⋆-wf (ctx-reflect w eΓ)
      ty-reflect (NT.⋆-wf w) {A = O.arr _ _ _} eΓ ()
      ty-reflect (NT.arr-wf d e) {A = O.⋆} eΓ ()
      ty-reflect (NT.arr-wf d e) {A = O.arr A t u} eΓ refl =
        OT.arr-wf (tm-reflect-at d eΓ refl refl) (tm-reflect-at e eΓ refl refl)

      tm-reflect : ∀ {Γ′ t′ A′} → Γ′ NT.⊢tm t′ ∶ A′ → ∀ {Γ t} → eCtx Γ ≡ Γ′ → eTm t ≡ t′ →
                   Σ O.Ty λ A → (eTy A ≡ A′) × (Γ OT.⊢tm t ∶ A)
      tm-reflect (NT.var-wf {i} w e) {Γ} {O.var _} refl refl with lookup-refl Γ i e
      ... | A , eA , e₀ = A , eA , OT.var-wf (ctx-reflect w refl) e₀
      tm-reflect (NT.var-wf w e) {t = O.coh _ _ _} _ ()
      tm-reflect (NT.var-wf w e) {t = O.cst _} _ ()
      tm-reflect (NT.coh-wf p w a ok s) {Γ} {O.coh Δ (O.arr A t u) σ} refl refl =
        (O.arr A t u) O.[ σ ]ty , e-[]ty (O.arr A t u) σ ,
        OT.coh-wf (ps-reflect p) (ctx-reflect w refl) (ty-reflect a refl refl)
          (subst T (agree Δ A t u) ok) (sub-reflect s refl refl refl)
      tm-reflect (NT.coh-wf p w a ok s) {t = O.coh _ O.⋆ _} _ ()
      tm-reflect (NT.coh-wf p w a ok s) {t = O.var _} _ ()
      tm-reflect (NT.coh-wf p w a ok s) {t = O.cst _} _ ()
      tm-reflect (NT.cst-wf w v) {t = O.cst k} refl refl = O.ty k , refl , OT.cst-wf (ctx-reflect w refl) v
      tm-reflect (NT.cst-wf w v) {t = O.var _} _ ()
      tm-reflect (NT.cst-wf w v) {t = O.coh _ _ _} _ ()
      tm-reflect (NT.bnd-wf _ _ _ _ _) {t = O.var _} _ ()
      tm-reflect (NT.bnd-wf _ _ _ _ _) {t = O.coh _ _ _} _ ()
      tm-reflect (NT.bnd-wf _ _ _ _ _) {t = O.cst _} _ ()

      tm-reflect-at : ∀ {Γ′ t′ A′} → Γ′ NT.⊢tm t′ ∶ A′ → ∀ {Γ t A} →
                      eCtx Γ ≡ Γ′ → eTm t ≡ t′ → eTy A ≡ A′ → Γ OT.⊢tm t ∶ A
      tm-reflect-at d {Γ} {t} eΓ et eA with tm-reflect d eΓ et
      ... | A₁ , e₁ , d₁ = subst (Γ OT.⊢tm t ∶_) (eTy-inj (trans e₁ (sym eA))) d₁

      sub-reflect : ∀ {Γ′ σ′ Δ′} → Γ′ NT.⊢sub σ′ ∶ Δ′ → ∀ {Γ σ Δ} →
                    eCtx Γ ≡ Γ′ → eSub σ ≡ σ′ → eCtx Δ ≡ Δ′ → Γ OT.⊢sub σ ∶ Δ
      sub-reflect (NT.⟨⟩-wf w) {σ = O.⟨⟩} {O.ε} eΓ refl refl = OT.⟨⟩-wf (ctx-reflect w eΓ)
      sub-reflect (NT.⟨⟩-wf w) {σ = O.⟨⟩} {_ O.▸ _} _ _ ()
      sub-reflect (NT.⟨⟩-wf w) {σ = _ O.,ₛ _} _ ()
      sub-reflect (NT.,-wf s d) {Γ} {σ O.,ₛ t} {Δ O.▸ A} eΓ refl refl =
        OT.,-wf (sub-reflect s eΓ refl refl) (tm-reflect-at d eΓ refl (e-[]ty A σ))
      sub-reflect (NT.,-wf s d) {σ = _ O.,ₛ _} {O.ε} _ _ ()
      sub-reflect (NT.,-wf s d) {σ = O.⟨⟩} _ ()

    --------------------------------------------------------------------
    -- The equivalences.

    ctx-iff : ∀ Γ → (Γ OT.⊢ctx → eCtx Γ NT.⊢ctx) × (eCtx Γ NT.⊢ctx → Γ OT.⊢ctx)
    ctx-iff Γ = ctx-pres , λ w → ctx-reflect w refl

    ty-iff : ∀ Γ A → (Γ OT.⊢ty A → eCtx Γ NT.⊢ty eTy A) × (eCtx Γ NT.⊢ty eTy A → Γ OT.⊢ty A)
    ty-iff Γ A = ty-pres , λ a → ty-reflect a refl refl

    tm-iff : ∀ Γ t A → (Γ OT.⊢tm t ∶ A → eCtx Γ NT.⊢tm eTm t ∶ eTy A) ×
                       (eCtx Γ NT.⊢tm eTm t ∶ eTy A → Γ OT.⊢tm t ∶ A)
    tm-iff Γ t A = tm-pres , λ d → tm-reflect-at d refl refl refl

    sub-iff : ∀ Γ σ Δ → (Γ OT.⊢sub σ ∶ Δ → eCtx Γ NT.⊢sub eSub σ ∶ eCtx Δ) ×
                        (eCtx Γ NT.⊢sub eSub σ ∶ eCtx Δ → Γ OT.⊢sub σ ∶ Δ)
    sub-iff Γ σ Δ = sub-pres , λ s → sub-reflect s refl refl refl

    -- A binder-free term has, in the extended theory, only binder-free
    -- types, and these are its types in the binder-free theory.
    tm-types : ∀ {Γ t A′} → eCtx Γ NT.⊢tm eTm t ∶ A′ →
               Σ O.Ty λ A → (eTy A ≡ A′) × (Γ OT.⊢tm t ∶ A)
    tm-types d = tm-reflect d refl refl

------------------------------------------------------------------------
-- Plain CaTT: Finster–Mimram's side condition agrees on embedded
-- syntax, so CaTT with any binders is conservative over CaTT, for every
-- signature of constants.

module CaTT (𝕊₀ : Old.Signature) (bi : Binders (Old.Signature.K 𝕊₀)) where

  private
    module OC = CaTTExp.Typing 𝕊₀
    module NC = CaTTExp.Binder.Typing (extend 𝕊₀ bi)
    open Emb (Old.Signature.K 𝕊₀) (Binders.B bi)

  open Conservative 𝕊₀ bi OC.cattSide NC.cattSide public

  cattSide-agree : Agree
  cattSide-agree Δ A t u
    rewrite fvTmTy-e t A | fvTmTy-e u A | varsCtx-e Δ | ∂⁻-e Δ | ∂⁺-e Δ = refl

  open Theorems cattSide-agree public
