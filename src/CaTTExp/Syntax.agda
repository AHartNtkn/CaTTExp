------------------------------------------------------------------------
-- Raw syntax of CaTT, relative to a set K of closed constants.
--
-- Variables are de Bruijn *levels*: `var i` is the i-th entry of the
-- context counted from the left. With levels, extending a context
-- never renames anything, so no weakening operation is needed.
--
-- K is an extension point. Pure CaTT takes K = ⊥. A signature of
-- closed constants is what "CaTT over a computad" needs, and it is
-- how the sketch in CaTTExp.Sketch.Representables adds new objects.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Syntax (K : Set) where

infixl 5 _▸_ _,ₛ_

mutual
  data Ty : Set where
    ⋆   : Ty
    -- `arr A t u` is t →_A u.
    arr : Ty → Tm → Tm → Ty

  data Tm : Set where
    var : Nat → Tm
    -- coh Γ A σ: the coherence (or operation) over the pasting
    -- context Γ with type A (always an arrow), applied to σ.
    coh : Ctx → Ty → Sub → Tm
    -- A closed constant from the signature.
    cst : K → Tm

  data Ctx : Set where
    ε   : Ctx
    _▸_ : Ctx → Ty → Ctx

  -- A substitution Δ → Γ lists one term (in Δ) per variable of Γ,
  -- in the same order as Γ.
  data Sub : Set where
    ⟨⟩   : Sub
    _,ₛ_ : Sub → Tm → Sub

------------------------------------------------------------------------
-- Lengths and lookup by level

len : Ctx → Nat
len ε       = 0
len (Γ ▸ _) = suc (len Γ)

lenₛ : Sub → Nat
lenₛ ⟨⟩       = 0
lenₛ (σ ,ₛ _) = suc (lenₛ σ)

lookup : Ctx → Nat → Maybe Ty
lookup ε       i = nothing
lookup (Γ ▸ A) i = if i ==ℕ len Γ then just A else lookup Γ i

lookupₛ : Sub → Nat → Tm
lookupₛ ⟨⟩       i = var i      -- out of range: unreachable for typed σ
lookupₛ (σ ,ₛ t) i = if i ==ℕ lenₛ σ then t else lookupₛ σ i

------------------------------------------------------------------------
-- Substitution. Closed constants and the bodies of coh are closed, so
-- only the argument substitution of a coh is acted on.

mutual
  _[_]ty : Ty → Sub → Ty
  ⋆         [ σ ]ty = ⋆
  arr A t u [ σ ]ty = arr (A [ σ ]ty) (t [ σ ]tm) (u [ σ ]tm)

  _[_]tm : Tm → Sub → Tm
  var i       [ σ ]tm = lookupₛ σ i
  coh Γ A τ   [ σ ]tm = coh Γ A (τ ∘ σ)
  cst k       [ σ ]tm = cst k

  -- (τ ∘ σ) : first τ, then σ, i.e. apply σ to every term of τ.
  _∘_ : Sub → Sub → Sub
  ⟨⟩       ∘ σ = ⟨⟩
  (τ ,ₛ t) ∘ σ = (τ ∘ σ) ,ₛ (t [ σ ]tm)

-- The identity substitution on Γ.
idₛ : Ctx → Sub
idₛ Γ = go (len Γ)
  where
  go : Nat → Sub
  go zero    = ⟨⟩
  go (suc n) = go n ,ₛ var n

------------------------------------------------------------------------
-- Dimension and free variables

dim : Ty → Nat
dim ⋆           = 0
dim (arr A _ _) = suc (dim A)

dimCtx : Ctx → Nat
dimCtx ε       = 0
dimCtx (Γ ▸ A) = max (dim A) (dimCtx Γ)

mutual
  fvTy : Ty → List Nat
  fvTy ⋆           = []
  fvTy (arr A t u) = fvTy A ++ fvTm t ++ fvTm u

  fvTm : Tm → List Nat
  fvTm (var i)     = i ∷ []
  fvTm (coh _ _ σ) = fvSub σ
  fvTm (cst _)     = []

  fvSub : Sub → List Nat
  fvSub ⟨⟩       = []
  fvSub (σ ,ₛ t) = fvSub σ ++ fvTm t

-- Var(t : A) in Finster–Mimram: the variables of a term together with
-- those of its type.
fvTmTy : Tm → Ty → List Nat
fvTmTy t A = fvTm t ++ fvTy A

-- All variables of a context.
-- n-1, …, 1, 0
downFrom : Nat → List Nat
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

varsCtx : Ctx → List Nat
varsCtx Γ = downFrom (len Γ)

------------------------------------------------------------------------
-- Source and target of a pasting context (as sets of levels).
--
-- These follow Finster–Mimram's ∂⁻ᵢ and ∂⁺ᵢ, computed on a context
-- that is already known to be a ps-context: after the first object it
-- is a sequence of pairs (y : A, f : x →_A y). We return variable sets
-- rather than sub-contexts: requiring `t : A` to be well typed in Γ with
-- Var(t : A) = Var(∂⁻Γ) is equivalent to typing it in ∂⁻Γ, because the
-- boundary is downward closed.

dropLast : List Nat → List Nat
dropLast []           = []
dropLast (x ∷ [])     = []
dropLast (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

snoc : List Nat → Nat → List Nat
snoc xs x = xs ++ (x ∷ [])

-- ∂⁻ᵢ
srcVars : Nat → Ctx → List Nat
srcVars i ε               = []
srcVars i (ε ▸ _)         = 0 ∷ []
srcVars i (Γ ▸ A ▸ B)     =
  if i <ℕ suc (dim A)            -- dim A ≥ i
  then srcVars i Γ
  else snoc (snoc (srcVars i Γ) (len Γ)) (suc (len Γ))

-- ∂⁺ᵢ
tgtVars : Nat → Ctx → List Nat
tgtVars i ε               = []
tgtVars i (ε ▸ _)         = 0 ∷ []
tgtVars i (Γ ▸ A ▸ B)     =
  if i <ℕ dim A                  -- dim A > i
  then tgtVars i Γ
  else if dim A ==ℕ i
  then snoc (dropLast (tgtVars i Γ)) (len Γ)
  else snoc (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))

∂⁻ ∂⁺ : Ctx → List Nat
∂⁻ Γ = srcVars (dimCtx Γ ∸ 1) Γ
∂⁺ Γ = tgtVars (dimCtx Γ ∸ 1) Γ

------------------------------------------------------------------------
-- Boolean syntactic equality, with soundness, given one on K.

module Equality (_==K_ : K → K → Bool)
                (==K-sound : ∀ k l → T (k ==K l) → k ≡ l) where

  mutual
    _==Ty_ : Ty → Ty → Bool
    ⋆         ==Ty ⋆            = true
    arr A t u ==Ty arr B t' u'  = (A ==Ty B) ∧ (t ==Tm t') ∧ (u ==Tm u')
    _         ==Ty _            = false

    _==Tm_ : Tm → Tm → Bool
    var i     ==Tm var j        = i ==ℕ j
    coh Γ A σ ==Tm coh Δ B τ    = (Γ ==Ctx Δ) ∧ (A ==Ty B) ∧ (σ ==Sub τ)
    cst k     ==Tm cst l        = k ==K l
    _         ==Tm _            = false

    _==Ctx_ : Ctx → Ctx → Bool
    ε       ==Ctx ε       = true
    (Γ ▸ A) ==Ctx (Δ ▸ B) = (Γ ==Ctx Δ) ∧ (A ==Ty B)
    _       ==Ctx _       = false

    _==Sub_ : Sub → Sub → Bool
    ⟨⟩       ==Sub ⟨⟩       = true
    (σ ,ₛ t) ==Sub (τ ,ₛ u) = (σ ==Sub τ) ∧ (t ==Tm u)
    _        ==Sub _        = false

  mutual
    ==Ty-sound : ∀ A B → T (A ==Ty B) → A ≡ B
    ==Ty-sound ⋆ ⋆ _ = refl
    ==Ty-sound (arr A t u) (arr B t' u') p =
      let q = ∧-snd {A ==Ty B} p in
      cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
        (==Ty-sound A B (∧-fst p))
        (cong₂ _,_ (==Tm-sound t t' (∧-fst q)) (==Tm-sound u u' (∧-snd {t ==Tm t'} q)))

    ==Tm-sound : ∀ t u → T (t ==Tm u) → t ≡ u
    ==Tm-sound (var i) (var j) p = cong var (==ℕ-sound i j p)
    ==Tm-sound (coh Γ A σ) (coh Δ B τ) p =
      let q = ∧-snd {Γ ==Ctx Δ} p in
      cong₂ (λ X (Y : Ty × Sub) → coh X (fst Y) (snd Y))
        (==Ctx-sound Γ Δ (∧-fst p))
        (cong₂ _,_ (==Ty-sound A B (∧-fst q)) (==Sub-sound σ τ (∧-snd {A ==Ty B} q)))
    ==Tm-sound (cst k) (cst l) p = cong cst (==K-sound k l p)

    ==Ctx-sound : ∀ Γ Δ → T (Γ ==Ctx Δ) → Γ ≡ Δ
    ==Ctx-sound ε ε _ = refl
    ==Ctx-sound (Γ ▸ A) (Δ ▸ B) p =
      cong₂ _▸_ (==Ctx-sound Γ Δ (∧-fst p)) (==Ty-sound A B (∧-snd {Γ ==Ctx Δ} p))

    ==Sub-sound : ∀ σ τ → T (σ ==Sub τ) → σ ≡ τ
    ==Sub-sound ⟨⟩ ⟨⟩ _ = refl
    ==Sub-sound (σ ,ₛ t) (τ ,ₛ u) p =
      cong₂ _,ₛ_ (==Sub-sound σ τ (∧-fst p)) (==Tm-sound t u (∧-snd {σ ==Sub τ} p))
