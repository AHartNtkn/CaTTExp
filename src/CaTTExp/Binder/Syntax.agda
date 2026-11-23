------------------------------------------------------------------------
-- Raw syntax of CaTT with binding formers (spec §1.1, "Binders"),
-- relative to a set K of closed constants and a set B of binding
-- formers.
--
-- Free variables are de Bruijn *levels* (`var i`), as in
-- CaTTExp.Syntax. Variables bound by a binder are *locally nameless*:
-- `bvar d j` is entry j (counted from the left) of the telescope of the
-- d-th enclosing binder (d = 0 is the innermost). So
--
--  * substitution acts on free variables only and passes under a binder
--    unchanged: no shift, and no capture as long as the substituted
--    terms are locally closed (well-typed terms are, since no typing
--    rule types a `bvar`);
--  * extending a context never renames anything, binders included.
--
-- A binder occurrence is `bnd b y Δ ts`:
--   b   the former (for INIT: μ, η, rec, rec_y, uni, uni_y);
--   y   a selector, an entry of the telescope counted from 0 (η_y, ...);
--   Δ   the bound telescope, in which bvar 0 j is Δ's own entry j and
--       `var i` are parameters from the surrounding context;
--   ts  the argument terms, in the surrounding scope.
-- Typing a binder *opens* its telescope with fresh variables
-- (`openTel`), and instantiates an argument telescope with the
-- arguments (`opTy 0 ts`).
--
-- The binder-free fragment (no bvar, no bnd) is exactly
-- CaTTExp.Syntax; CaTTExp.Binder.Embed proves the typing rules of the
-- two agree there.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Binder.Syntax (K : Set) (B : Set) where

infixl 5 _▸_ _,ₛ_

mutual
  data Ty : Set where
    ⋆   : Ty
    -- `arr A t u` is t →_A u.
    arr : Ty → Tm → Tm → Ty

  data Tm : Set where
    var  : Nat → Tm
    -- A bound variable: entry j of the d-th enclosing binder.
    bvar : Nat → Nat → Tm
    -- coh Γ A σ: Γ and A are closed; only σ is in the surrounding scope.
    coh  : Ctx → Ty → Sub → Tm
    cst  : K → Tm
    -- A binding former, its selector, its telescope and its arguments.
    bnd  : B → Nat → Ctx → Sub → Tm

  data Ctx : Set where
    ε   : Ctx
    _▸_ : Ctx → Ty → Ctx

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

-- Entry j of a list of terms, or a default.
pickOr : Sub → Nat → Tm → Tm
pickOr ⟨⟩       j d = d
pickOr (σ ,ₛ t) j d = if j ==ℕ lenₛ σ then t else pickOr σ j d

infixl 6 _⧺_ _++ₛ_
_⧺_ : Ctx → Ctx → Ctx
Γ ⧺ ε       = Γ
Γ ⧺ (Ξ ▸ A) = (Γ ⧺ Ξ) ▸ A

_++ₛ_ : Sub → Sub → Sub
σ ++ₛ ⟨⟩       = σ
σ ++ₛ (τ ,ₛ t) = (σ ++ₛ τ) ,ₛ t

------------------------------------------------------------------------
-- Substitution of free variables. Closed constants and the bodies of
-- coh are closed; a binder's telescope is acted on entry by entry, and
-- its bound variables are left alone.

mutual
  _[_]ty : Ty → Sub → Ty
  ⋆         [ σ ]ty = ⋆
  arr A t u [ σ ]ty = arr (A [ σ ]ty) (t [ σ ]tm) (u [ σ ]tm)

  _[_]tm : Tm → Sub → Tm
  var i       [ σ ]tm = lookupₛ σ i
  bvar d j    [ σ ]tm = bvar d j
  coh Γ A τ   [ σ ]tm = coh Γ A (τ ∘ σ)
  cst k       [ σ ]tm = cst k
  bnd b y Δ τ [ σ ]tm = bnd b y (Δ [ σ ]tel) (τ ∘ σ)

  _[_]tel : Ctx → Sub → Ctx
  ε       [ σ ]tel = ε
  (Δ ▸ A) [ σ ]tel = (Δ [ σ ]tel) ▸ (A [ σ ]ty)

  -- (τ ∘ σ) : apply σ to every term of τ.
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
-- Shifting: bvar e j with e ≥ c refers outside the term (c binders
-- deep), so it is one binder further away once the term is moved under
-- a binder.

mutual
  shTy : Nat → Ty → Ty
  shTy c ⋆           = ⋆
  shTy c (arr A t u) = arr (shTy c A) (shTm c t) (shTm c u)

  shTm : Nat → Tm → Tm
  shTm c (var i)       = var i
  shTm c (bvar e j)    = if e <ℕ c then bvar e j else bvar (suc e) j
  shTm c (coh Γ A σ)   = coh Γ A (shSub c σ)
  shTm c (cst k)       = cst k
  shTm c (bnd b y Δ σ) = bnd b y (shTel (suc c) Δ) (shSub c σ)

  shTel : Nat → Ctx → Ctx
  shTel c ε       = ε
  shTel c (Δ ▸ A) = shTel c Δ ▸ shTy c A

  shSub : Nat → Sub → Sub
  shSub c ⟨⟩       = ⟨⟩
  shSub c (σ ,ₛ t) = shSub c σ ,ₛ shTm c t

------------------------------------------------------------------------
-- Opening: replace the bound variables of the binder at depth d by
-- the terms ts (entry j by the j-th term). Under a further binder the
-- depth goes up by one and ts is shifted, so that bound variables in ts
-- keep referring to the same binders. Bound variables of other binders
-- are left alone; in well-formed syntax none refers past the binder
-- opened.

mutual
  opTy : Nat → Sub → Ty → Ty
  opTy d ts ⋆           = ⋆
  opTy d ts (arr A t u) = arr (opTy d ts A) (opTm d ts t) (opTm d ts u)

  opTm : Nat → Sub → Tm → Tm
  opTm d ts (var i)       = var i
  opTm d ts (bvar e j)    = if e ==ℕ d then pickOr ts j (bvar e j) else bvar e j
  opTm d ts (coh Γ A σ)   = coh Γ A (opSub d ts σ)
  opTm d ts (cst k)       = cst k
  opTm d ts (bnd b y Δ σ) = bnd b y (opTel (suc d) (shSub 0 ts) Δ) (opSub d ts σ)

  opTel : Nat → Sub → Ctx → Ctx
  opTel d ts ε       = ε
  opTel d ts (Δ ▸ A) = opTel d ts Δ ▸ opTy d ts A

  opSub : Nat → Sub → Sub → Sub
  opSub d ts ⟨⟩       = ⟨⟩
  opSub d ts (σ ,ₛ t) = opSub d ts σ ,ₛ opTm d ts t

-- k fresh variables starting at level n: var n, …, var (n + k - 1).
fresh : Nat → Nat → Sub
fresh n zero    = ⟨⟩
fresh n (suc k) = fresh n k ,ₛ var (n + k)

-- A telescope opened at level n: entry k is opened with the k fresh
-- variables for the entries before it, so it is a context extension of
-- any context of length n.
openTel : Nat → Ctx → Ctx
openTel n ε       = ε
openTel n (Δ ▸ A) = openTel n Δ ▸ opTy 0 (fresh n (len Δ)) A

------------------------------------------------------------------------
-- Dimension

dim : Ty → Nat
dim ⋆           = 0
dim (arr A _ _) = suc (dim A)

dimCtx : Ctx → Nat
dimCtx ε       = 0
dimCtx (Γ ▸ A) = max (dim A) (dimCtx Γ)

------------------------------------------------------------------------
-- Free variables (levels). A binder's free variables are those of its
-- telescope and of its arguments.

mutual
  fvTy : Ty → List Nat
  fvTy ⋆           = []
  fvTy (arr A t u) = fvTy A ++ fvTm t ++ fvTm u

  fvTm : Tm → List Nat
  fvTm (var i)       = i ∷ []
  fvTm (bvar _ _)    = []
  fvTm (coh _ _ σ)   = fvSub σ
  fvTm (cst _)       = []
  fvTm (bnd _ _ Δ σ) = fvTel Δ ++ fvSub σ

  fvTel : Ctx → List Nat
  fvTel ε       = []
  fvTel (Δ ▸ A) = fvTel Δ ++ fvTy A

  fvSub : Sub → List Nat
  fvSub ⟨⟩       = []
  fvSub (σ ,ₛ t) = fvSub σ ++ fvTm t

fvTmTy : Tm → Ty → List Nat
fvTmTy t A = fvTm t ++ fvTy A

downFrom : Nat → List Nat
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

varsCtx : Ctx → List Nat
varsCtx Γ = downFrom (len Γ)

------------------------------------------------------------------------
-- Boolean scoping: every free variable is below n. Bound variables are
-- not counted.

mutual
  scTy? : Nat → Ty → Bool
  scTy? n ⋆           = true
  scTy? n (arr A t u) = scTy? n A ∧ scTm? n t ∧ scTm? n u

  scTm? : Nat → Tm → Bool
  scTm? n (var i)       = i <ℕ n
  scTm? n (bvar _ _)    = true
  scTm? n (coh _ _ σ)   = scSub? n σ
  scTm? n (cst _)       = true
  scTm? n (bnd _ _ Δ σ) = scTel? n Δ ∧ scSub? n σ

  scTel? : Nat → Ctx → Bool
  scTel? n ε       = true
  scTel? n (Δ ▸ A) = scTel? n Δ ∧ scTy? n A

  scSub? : Nat → Sub → Bool
  scSub? n ⟨⟩       = true
  scSub? n (σ ,ₛ t) = scSub? n σ ∧ scTm? n t

------------------------------------------------------------------------
-- Local closure: every bound variable refers to a binder inside the
-- term (at depth d, bvar e j needs e < d).

mutual
  lcTy? : Nat → Ty → Bool
  lcTy? d ⋆           = true
  lcTy? d (arr A t u) = lcTy? d A ∧ lcTm? d t ∧ lcTm? d u

  lcTm? : Nat → Tm → Bool
  lcTm? d (var _)       = true
  lcTm? d (bvar e _)    = e <ℕ d
  lcTm? d (coh _ _ σ)   = lcSub? d σ
  lcTm? d (cst _)       = true
  lcTm? d (bnd _ _ Δ σ) = lcTel? (suc d) Δ ∧ lcSub? d σ

  lcTel? : Nat → Ctx → Bool
  lcTel? d ε       = true
  lcTel? d (Δ ▸ A) = lcTel? d Δ ∧ lcTy? d A

  lcSub? : Nat → Sub → Bool
  lcSub? d ⟨⟩       = true
  lcSub? d (σ ,ₛ t) = lcSub? d σ ∧ lcTm? d t

------------------------------------------------------------------------
-- Size, used as fuel by the checker (opening a telescope with fresh
-- variables does not change sizes, but it is not a structural
-- subterm, so the checker recurses on fuel).

mutual
  sizeTy : Ty → Nat
  sizeTy ⋆           = 1
  sizeTy (arr A t u) = suc (sizeTy A + sizeTm t + sizeTm u)

  sizeTm : Tm → Nat
  sizeTm (var _)       = 1
  sizeTm (bvar _ _)    = 1
  sizeTm (coh Γ A σ)   = suc (sizeTel Γ + sizeTy A + sizeSub σ)
  sizeTm (cst _)       = 1
  sizeTm (bnd _ _ Δ σ) = suc (sizeTel Δ + sizeSub σ)

  sizeTel : Ctx → Nat
  sizeTel ε       = 1
  sizeTel (Δ ▸ A) = suc (sizeTel Δ + sizeTy A)

  sizeSub : Sub → Nat
  sizeSub ⟨⟩       = 1
  sizeSub (σ ,ₛ t) = suc (sizeSub σ + sizeTm t)

------------------------------------------------------------------------
-- Source and target of a pasting context (as sets of levels), as in
-- CaTTExp.Syntax.

dropLastᴸ : List Nat → List Nat
dropLastᴸ []           = []
dropLastᴸ (x ∷ [])     = []
dropLastᴸ (x ∷ y ∷ xs) = x ∷ dropLastᴸ (y ∷ xs)

snoc : List Nat → Nat → List Nat
snoc xs x = xs ++ (x ∷ [])

srcVars : Nat → Ctx → List Nat
srcVars i ε               = []
srcVars i (ε ▸ _)         = 0 ∷ []
srcVars i (Γ ▸ A ▸ B)     =
  if i <ℕ suc (dim A)
  then srcVars i Γ
  else snoc (snoc (srcVars i Γ) (len Γ)) (suc (len Γ))

tgtVars : Nat → Ctx → List Nat
tgtVars i ε               = []
tgtVars i (ε ▸ _)         = 0 ∷ []
tgtVars i (Γ ▸ A ▸ B)     =
  if i <ℕ dim A
  then tgtVars i Γ
  else if dim A ==ℕ i
  then snoc (dropLastᴸ (tgtVars i Γ)) (len Γ)
  else snoc (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))

∂⁻ ∂⁺ : Ctx → List Nat
∂⁻ Γ = srcVars (dimCtx Γ ∸ 1) Γ
∂⁺ Γ = tgtVars (dimCtx Γ ∸ 1) Γ

------------------------------------------------------------------------
-- Boolean syntactic equality, with soundness, given ones on K and B.

module Equality (_==K_ : K → K → Bool)
                (==K-sound : ∀ k l → T (k ==K l) → k ≡ l)
                (_==B_ : B → B → Bool)
                (==B-sound : ∀ b c → T (b ==B c) → b ≡ c) where

  mutual
    _==Ty_ : Ty → Ty → Bool
    ⋆         ==Ty ⋆            = true
    arr A t u ==Ty arr B t' u'  = (A ==Ty B) ∧ (t ==Tm t') ∧ (u ==Tm u')
    _         ==Ty _            = false

    _==Tm_ : Tm → Tm → Bool
    var i       ==Tm var j        = i ==ℕ j
    bvar d i    ==Tm bvar e j     = (d ==ℕ e) ∧ (i ==ℕ j)
    coh Γ A σ   ==Tm coh Δ B τ    = (Γ ==Ctx Δ) ∧ (A ==Ty B) ∧ (σ ==Sub τ)
    cst k       ==Tm cst l        = k ==K l
    bnd b y Δ σ ==Tm bnd c z Θ τ  = (b ==B c) ∧ (y ==ℕ z) ∧ (Δ ==Ctx Θ) ∧ (σ ==Sub τ)
    _           ==Tm _            = false

    _==Ctx_ : Ctx → Ctx → Bool
    ε       ==Ctx ε       = true
    (Γ ▸ A) ==Ctx (Δ ▸ B) = (Γ ==Ctx Δ) ∧ (A ==Ty B)
    _       ==Ctx _       = false

    _==Sub_ : Sub → Sub → Bool
    ⟨⟩       ==Sub ⟨⟩       = true
    (σ ,ₛ t) ==Sub (τ ,ₛ u) = (σ ==Sub τ) ∧ (t ==Tm u)
    _        ==Sub _        = false

  private
    T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
    T∧ {true} p = tt , p

  mutual
    ==Ty-sound : ∀ A B → T (A ==Ty B) → A ≡ B
    ==Ty-sound ⋆ ⋆ _ = refl
    ==Ty-sound (arr A t u) (arr B t' u') p =
      let (a , q) = T∧ {A ==Ty B} p
          (b , c) = T∧ {t ==Tm t'} q
      in cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
           (==Ty-sound A B a) (cong₂ _,_ (==Tm-sound t t' b) (==Tm-sound u u' c))

    ==Tm-sound : ∀ t u → T (t ==Tm u) → t ≡ u
    ==Tm-sound (var i) (var j) p = cong var (==ℕ-sound i j p)
    ==Tm-sound (bvar d i) (bvar e j) p =
      let (a , b) = T∧ {d ==ℕ e} p
      in cong₂ bvar (==ℕ-sound d e a) (==ℕ-sound i j b)
    ==Tm-sound (coh Γ A σ) (coh Δ B τ) p =
      let (a , q) = T∧ {Γ ==Ctx Δ} p
          (b , c) = T∧ {A ==Ty B} q
      in cong₂ (λ X (Y : Ty × Sub) → coh X (fst Y) (snd Y))
           (==Ctx-sound Γ Δ a) (cong₂ _,_ (==Ty-sound A B b) (==Sub-sound σ τ c))
    ==Tm-sound (cst k) (cst l) p = cong cst (==K-sound k l p)
    ==Tm-sound (bnd b y Δ σ) (bnd c z Θ τ) p =
      let (a₁ , q₁) = T∧ {b ==B c} p
          (a₂ , q₂) = T∧ {y ==ℕ z} q₁
          (a₃ , a₄) = T∧ {Δ ==Ctx Θ} q₂
      in cong₂ (λ (X : B × Nat) (Y : Ctx × Sub) → bnd (fst X) (snd X) (fst Y) (snd Y))
           (cong₂ _,_ (==B-sound b c a₁) (==ℕ-sound y z a₂))
           (cong₂ _,_ (==Ctx-sound Δ Θ a₃) (==Sub-sound σ τ a₄))

    ==Ctx-sound : ∀ Γ Δ → T (Γ ==Ctx Δ) → Γ ≡ Δ
    ==Ctx-sound ε ε _ = refl
    ==Ctx-sound (Γ ▸ A) (Δ ▸ B) p =
      let (a , b) = T∧ {Γ ==Ctx Δ} p
      in cong₂ _▸_ (==Ctx-sound Γ Δ a) (==Ty-sound A B b)

    ==Sub-sound : ∀ σ τ → T (σ ==Sub τ) → σ ≡ τ
    ==Sub-sound ⟨⟩ ⟨⟩ _ = refl
    ==Sub-sound (σ ,ₛ t) (τ ,ₛ u) p =
      let (a , b) = T∧ {σ ==Sub τ} p
      in cong₂ _,ₛ_ (==Sub-sound σ τ a) (==Tm-sound t u b)
