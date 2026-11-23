------------------------------------------------------------------------
-- INIT (spec §9.3, syntax §1.1) as an instance of the binder
-- interface: six binding formers over a telescope X. Δ, a decidable
-- positivity check, and the stability laws (CaTTExp.Binder.Laws).
--
-- The telescope Δ of every former is (X : ⋆, A₁, …, A_{m-1}); its
-- entry j is bvar 0 j inside Δ, so X is bvar 0 0. Writing μT for
-- bnd μ 0 Δ ⟨⟩ and ηT y for bnd η y Δ ⟨⟩, the generic model is
-- η = ⟨μT, ηT 1, …, ηT (m-1)⟩, and a model with carrier A is a list of
-- arguments for the telescope Δ itself (A for X, then the rest).
--
--   former  arguments (bargs)          type (bres), bvar 0 j = argument j
--   μ       none                       ⋆
--   η_y     none                       A_y opened at η
--   rec     a model (A, σ) : Δ         μT → A
--   rec_y   a model (A, σ) : Δ         the cell of rec at y (below)
--   uni     a model, and two model     h ⇒ h′, the 2-cell between the
--           morphisms (h, θ), (h′, θ′)  carrier maps
--           from η to it
--   uni_y   the same                   the compatibility 3-cell at y
--
-- The cell of a model morphism h : A₁ → A₂ at a map variable
-- y : S → T is
--
--   s¹_y ; T(h)  ⇒  S(h) ; s²_y      (an arrow S¹ → T² in the ambient)
--
-- where T(h) = h if T is X and the identity of T otherwise (likewise
-- S(h)). For uni_y, with u : h ⇒ h′ the cell uni and T(u) = u or an
-- identity 2-cell, the two sides are
--
--   (η_y ◁ T(u)) · θ′_y     and     θ_y · (S(u) ▷ σ_y).
--
-- Composites, whiskerings and identities are coherences over the usual
-- pasting contexts. INIT's model-morphism cells are meant invertible;
-- the Agda kernel has no invertibility marks, so the types here carry
-- no `inv` (the marks are a separate judgment, spec chapter 3).
--
-- Positivity (`positive`). This instance's fragment of §9.3's check,
-- for the object terms the Agda kernel has (variables, constants,
-- binders; it has no limit or colimit formers yet):
--   * the first entry is X : ⋆, and no other entry is an object;
--   * every other entry is a map or a cell (of any dimension) whose
--     underlying arrow type is S → T with
--       S = X, or S mentions no variable bound by the telescope;
--       T = X, or T is a constant the base signature marks as ⊤.
-- The arrow context Δ^→ (model morphisms) is stated at maps and at
-- globular 2-cells l : f ⇒ g between map entries f, g, where its
-- component is a 3-cell between the two pastings of the naturality
-- square (`cell3Ty`). So rec_y needs entry y to be a map or a globular
-- 2-cell; uni needs every entry after X to be one; uni_y needs that and
-- entry y a map. Cells of higher dimension, or with composite
-- boundaries, are accepted by μ, η_y and rec only (ledger S26b).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.Init where

data Former : Set where
  μ η rec recY uni uniY : Former

private
  code : Former → Nat
  code μ    = 0
  code η    = 1
  code rec  = 2
  code recY = 3
  code uni  = 4
  code uniY = 5

  decode : Nat → Former
  decode 0 = μ
  decode 1 = η
  decode 2 = rec
  decode 3 = recY
  decode 4 = uni
  decode _ = uniY

  decode-code : ∀ b → decode (code b) ≡ b
  decode-code μ    = refl
  decode-code η    = refl
  decode-code rec  = refl
  decode-code recY = refl
  decode-code uni  = refl
  decode-code uniY = refl

_==F_ : Former → Former → Bool
b ==F c = code b ==ℕ code c

==F-sound : ∀ b c → T (b ==F c) → b ≡ c
==F-sound b c p = trans (sym (decode-code b)) (trans (cong decode (==ℕ-sound _ _ p)) (decode-code c))

==F-refl : ∀ b → T (b ==F b)
==F-refl b = ==ℕ-refl (code b)

------------------------------------------------------------------------
-- The construction, over constants K, with a test for ⊤.

module Construction (K : Set) (top? : K → Bool) where

  open Syntax K Former

  -- Lists of terms, left to right.
  ⟪_⟫ : List Tm → Sub
  ⟪ ts ⟫ = go ⟨⟩ ts
    where
    go : Sub → List Tm → Sub
    go σ []       = σ
    go σ (t ∷ ts) = go (σ ,ₛ t) ts

  ----------------------------------------------------------------------
  -- Pasting contexts and coherences used by the types.

  private
    v : Nat → Tm
    v = var

  PC0 PC1 PC2 PCv PClw PCrw : Ctx
  PC0  = ε ▸ ⋆
  PC1  = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)
  PC2  = PC1 ▸ ⋆ ▸ arr ⋆ (v 1) (v 3)
  PCv  = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5)
  PClw = PC2 ▸ arr ⋆ (v 1) (v 3) ▸ arr (arr ⋆ (v 1) (v 3)) (v 4) (v 5)
  PCrw = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ ⋆ ▸ arr ⋆ (v 1) (v 5)

  -- f ; g for f : a → b, g : b → c.
  cmp : Tm → Tm → Tm → Tm → Tm → Tm
  cmp a b c f g = coh PC2 (arr ⋆ (v 0) (v 3)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g)

  -- The identity of an object, and the identity 2-cell of a map.
  idm : Tm → Tm
  idm a = coh PC0 (arr ⋆ (v 0) (v 0)) (⟨⟩ ,ₛ a)

  id2 : Tm → Tm → Tm → Tm
  id2 a b f = coh PC1 (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f)

  -- α · β for α : f ⇒ g, β : g ⇒ h between maps a → b.
  vcomp : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  vcomp a b f g α h β =
    coh PCv (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ g ,ₛ α ,ₛ h ,ₛ β)

  -- f ◁ α for f : a → b, α : g ⇒ g′ between maps b → c.
  lwh : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  lwh a b c f g g′ α =
    coh PClw (arr (arr ⋆ (v 0) (v 3)) (cmp (v 0) (v 1) (v 3) (v 2) (v 4)) (cmp (v 0) (v 1) (v 3) (v 2) (v 5)))
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g ,ₛ g′ ,ₛ α)

  -- α ▷ g for α : f ⇒ f′ between maps a → b, g : b → c.
  rwh : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  rwh a b c f f′ α g =
    coh PCrw (arr (arr ⋆ (v 0) (v 5)) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 6)))
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ f′ ,ₛ α ,ₛ c ,ₛ g)

  ----------------------------------------------------------------------
  -- Positivity.

  isX? : Tm → Bool
  isX? (bvar e j) = (e ==ℕ 0) ∧ (j ==ℕ 0)
  isX? _          = false

  isTop? : Tm → Bool
  isTop? (cst k) = top? k
  isTop? _       = false

  -- Does the syntax mention a variable of the binder at depth d?
  mutual
    mTy : Nat → Ty → Bool
    mTy d ⋆           = false
    mTy d (arr A t u) = mTy d A ∨ mTm d t ∨ mTm d u

    mTm : Nat → Tm → Bool
    mTm d (var _)       = false
    mTm d (bvar e _)    = e ==ℕ d
    mTm d (coh _ _ σ)   = mSub d σ
    mTm d (cst _)       = false
    mTm d (bnd _ _ Δ σ) = mTel (suc d) Δ ∨ mSub d σ

    mTel : Nat → Ctx → Bool
    mTel d ε       = false
    mTel d (Δ ▸ A) = mTel d Δ ∨ mTy d A

    mSub : Nat → Sub → Bool
    mSub d ⟨⟩       = false
    mSub d (σ ,ₛ t) = mSub d σ ∨ mTm d t

  srcOK tgtOK : Tm → Bool
  srcOK S = isX? S ∨ not (mTm 0 S)
  tgtOK T = isX? T ∨ isTop? T

  -- The underlying arrow S → T of a map or cell type.
  base : Ty → Maybe (Tm × Tm)
  base ⋆                       = nothing
  base (arr ⋆ s t)             = just (s , t)
  base (arr (arr A a b) _ _)   = base (arr A a b)

  okBase : Maybe (Tm × Tm) → Bool
  okBase nothing        = false
  okBase (just (S , T)) = srcOK S ∧ tgtOK T

  entryOK : Ty → Bool
  entryOK A = okBase (base A)

  positive : Ctx → Bool
  positive ε                 = false
  positive (ε ▸ ⋆)           = true
  positive (ε ▸ arr _ _ _)   = false
  positive (Δ ▸ B ▸ A)       = positive (Δ ▸ B) ∧ entryOK A

  -- A variable of the binder at depth 0, other than through a parameter.
  bv0? : Tm → Maybe Nat
  bv0? (bvar zero j) = just j
  bv0? _             = nothing

  both : Maybe Nat → Maybe Nat → Maybe (Nat × Nat)
  both (just i) (just j) = just (i , j)
  both _        _        = nothing

  -- A globular 2-cell between two earlier entries: f ⇒ g for f, g : S → T
  -- variables of the telescope. Returns the entries of f and g.
  glob : Ty → Maybe (Nat × Nat)
  glob ⋆                             = nothing
  glob (arr ⋆ _ _)                   = nothing
  glob (arr (arr ⋆ _ _) f g)         = both (bv0? f) (bv0? g)
  glob (arr (arr (arr _ _ _) _ _) _ _) = nothing

  -- Entries whose model-morphism component the kernel states: maps, and
  -- globular 2-cells (ledger S26b for the rest).
  low : Ty → Bool
  low A = (dim A ==ℕ 1) ∨ is-just (glob A)

  -- Every entry after X is low.
  lowOnly : Ctx → Bool
  lowOnly ε           = true
  lowOnly (ε ▸ _)     = true
  lowOnly (Δ ▸ B ▸ A) = lowOnly (Δ ▸ B) ∧ low A

  isLow? : Maybe Ty → Bool
  isLow? nothing  = false
  isLow? (just A) = low A

  isMap? : Maybe Ty → Bool
  isMap? nothing  = false
  isMap? (just A) = dim A ==ℕ 1

  inner : Nat → Ctx → Bool
  inner y Δ = (0 <ℕ y) ∧ (y <ℕ len Δ)

  sel : Former → Nat → Ctx → Bool
  sel μ    y Δ = y ==ℕ 0
  sel η    y Δ = inner y Δ
  sel rec  y Δ = y ==ℕ 0
  sel recY y Δ = inner y Δ ∧ isLow? (lookup Δ y)
  sel uni  y Δ = (y ==ℕ 0) ∧ lowOnly Δ
  sel uniY y Δ = (inner y Δ ∧ lowOnly Δ) ∧ isMap? (lookup Δ y)

  side : Former → Nat → Ctx → Bool
  side b y Δ = positive Δ ∧ sel b y Δ

  ----------------------------------------------------------------------
  -- Models and model morphisms.

  μT : Ctx → Tm
  μT Δ = bnd μ 0 Δ ⟨⟩

  ηAt : Ctx → Nat → Tm
  ηAt Δ zero    = μT Δ
  ηAt Δ (suc j) = bnd η (suc j) Δ ⟨⟩

  -- The first k components of the generic model.
  ηPre : Ctx → Nat → Sub
  ηPre Δ zero    = ⟨⟩
  ηPre Δ (suc k) = ηPre Δ k ,ₛ ηAt Δ k

  -- The first k arguments, bvar 0 0, …, bvar 0 (k - 1).
  bvPre : Nat → Sub
  bvPre zero    = ⟨⟩
  bvPre (suc k) = bvPre k ,ₛ bvar 0 k

  baseOf : Maybe Ty → Maybe (Tm × Tm)
  baseOf nothing  = nothing
  baseOf (just A) = base A

  entryBase : Ctx → Nat → Maybe (Tm × Tm)
  entryBase Δ y = baseOf (lookup Δ y)

  withBase : Maybe (Tm × Tm) → (Tm → Tm → Ty) → Ty
  withBase nothing        k = ⋆
  withBase (just (S , T)) k = k S T

  -- The action on h of an object S of the telescope, at a model M₁.
  act : Tm → Sub → Tm → Tm
  act S M₁ h = if isX? S then h else idm (opTm 0 M₁ S)

  -- The cell of a model morphism h : M₁ → M₂ at a map y : S → T, whose
  -- components in the two models are s₁ and s₂.
  cellTy : Tm → Tm → Sub → Sub → Tm → Tm → Tm → Ty
  cellTy S T M₁ M₂ s₁ s₂ h =
    arr (arr ⋆ (opTm 0 M₁ S) (opTm 0 M₂ T))
        (cmp (opTm 0 M₁ S) (opTm 0 M₁ T) (opTm 0 M₂ T) s₁ (act T M₁ h))
        (cmp (opTm 0 M₁ S) (opTm 0 M₂ S) (opTm 0 M₂ T) (act S M₁ h) s₂)

  -- The 3-cell of a model morphism h : M₁ → M₂ at a 2-cell l : f ⇒ g
  -- between maps S → T, given its cells θf, θg at f and g: the two
  -- pastings of the naturality square
  --   (l₁ ▷ T(h)) · θg   ⇛   θf · (S(h) ◁ l₂).
  cell3Ty : Tm → Tm → Sub → Sub → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Ty
  cell3Ty S T M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg =
    let S₁  = opTm 0 M₁ S
        S₂  = opTm 0 M₂ S
        T₁  = opTm 0 M₁ T
        T₂  = opTm 0 M₂ T
        Th  = act T M₁ h
        Sh  = act S M₁ h
        src = cmp S₁ T₁ T₂ f₁ Th
        tgt = cmp S₁ S₂ T₂ Sh g₂
    in arr (arr (arr ⋆ S₁ T₂) src tgt)
           (vcomp S₁ T₂ src (cmp S₁ T₁ T₂ g₁ Th) (rwh S₁ T₁ T₂ f₁ g₁ l₁ Th) tgt θg)
           (vcomp S₁ T₂ src (cmp S₁ S₂ T₂ Sh f₂) θf tgt (lwh S₁ S₂ T₂ Sh f₂ g₂ l₂))

  globM : Maybe Ty → Maybe (Nat × Nat)
  globM nothing  = nothing
  globM (just A) = glob A

  globAt : Ctx → Nat → Maybe (Nat × Nat)
  globAt Δ y = globM (lookup Δ y)

  -- The component at y of a morphism from η to the model given by the
  -- first m arguments, with carrier map h and components th i at the
  -- earlier entries: a cell at a map, a 3-cell at a globular 2-cell.
  θSel : Ctx → Nat → Tm → (Nat → Tm) → Tm → Tm → Maybe (Nat × Nat) → Ty
  θSel Δ y h th S T nothing        =
    cellTy S T (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h
  θSel Δ y h th S T (just (i , j)) =
    cell3Ty S T (ηPre Δ (len Δ)) (bvPre (len Δ))
            (ηAt Δ i) (ηAt Δ j) (ηAt Δ y) (bvar 0 i) (bvar 0 j) (bvar 0 y) h (th i) (th j)

  θBody : Ctx → Nat → Tm → (Nat → Tm) → Tm → Tm → Ty
  θBody Δ y h th S T = θSel Δ y h th S T (globAt Δ y)

  θTy : Ctx → Nat → Tm → (Nat → Tm) → Ty
  θTy Δ y h th = withBase (entryBase Δ y) (θBody Δ y h th)

  -- The components θ_1, …, θ_k of a morphism with carrier map bvar 0 o,
  -- θ_i being bvar 0 (o + i).
  θTel : Ctx → Nat → Nat → Ctx
  θTel Δ o zero    = ε
  θTel Δ o (suc k) = θTel Δ o k ▸ θTy Δ (suc k) (bvar 0 o) (λ i → bvar 0 (o + i))

  -- A model morphism from η to the model given by the first m
  -- arguments, starting at argument o: the carrier map, then its cells.
  morTel : Ctx → Nat → Ctx
  morTel Δ o = (ε ▸ arr ⋆ (μT Δ) (bvar 0 0)) ⧺ θTel Δ o (len Δ ∸ 1)

  -- The compatibility cell of uni at y.
  uniYBody : Ctx → Nat → Tm → Tm → Ty
  uniYBody Δ y S T =
    let m   = len Δ
        M₁  = ηPre Δ m
        M₂  = bvPre m
        S₁  = opTm 0 M₁ S
        S₂  = opTm 0 M₂ S
        T₁  = opTm 0 M₁ T
        T₂  = opTm 0 M₂ T
        h   = bvar 0 m
        h′  = bvar 0 (m + m)
        u   = bnd uni 0 Δ (bvPre (m + m + m))
        ηy  = ηAt Δ y
        σy  = bvar 0 y
        Th  = act T M₁ h
        Th′ = act T M₁ h′
        Sh  = act S M₁ h
        Sh′ = act S M₁ h′
        Tu  = if isX? T then u else id2 T₁ T₁ (idm T₁)
        Su  = if isX? S then u else id2 S₁ S₁ (idm S₁)
        src = cmp S₁ T₁ T₂ ηy Th
        tgt = cmp S₁ S₂ T₂ Sh′ σy
    in arr (arr (arr ⋆ S₁ T₂) src tgt)
           (vcomp S₁ T₂ src (cmp S₁ T₁ T₂ ηy Th′) (lwh S₁ T₁ T₂ ηy Th Th′ Tu) tgt
                  (bvar 0 (m + m + y)))
           (vcomp S₁ T₂ src (cmp S₁ S₂ T₂ Sh σy) (bvar 0 (m + y)) tgt
                  (rwh S₁ S₂ T₂ Sh Sh′ Su σy))

  uniYTy : Ctx → Nat → Ty
  uniYTy Δ y = withBase (entryBase Δ y) (uniYBody Δ y)

  ηRes : Ctx → Nat → Maybe Ty → Ty
  ηRes Δ y nothing  = ⋆
  ηRes Δ y (just A) = opTy 0 (ηPre Δ y) A

  args : Former → Nat → Ctx → Ctx
  args μ    y Δ = ε
  args η    y Δ = ε
  args rec  y Δ = Δ
  args recY y Δ = Δ
  args uni  y Δ = Δ ⧺ morTel Δ (len Δ) ⧺ morTel Δ (len Δ + len Δ)
  args uniY y Δ = Δ ⧺ morTel Δ (len Δ) ⧺ morTel Δ (len Δ + len Δ)

  res : Former → Nat → Ctx → Ty
  res μ    y Δ = ⋆
  res η    y Δ = ηRes Δ y (lookup Δ y)
  res rec  y Δ = arr ⋆ (μT Δ) (bvar 0 0)
  res recY y Δ = θTy Δ y (bnd rec 0 Δ (bvPre (len Δ))) (λ i → bnd recY i Δ (bvPre (len Δ)))
  res uni  y Δ = arr (arr ⋆ (μT Δ) (bvar 0 0)) (bvar 0 (len Δ)) (bvar 0 (len Δ + len Δ))
  res uniY y Δ = uniYTy Δ y

------------------------------------------------------------------------
-- The signature: constants from a base, binding formers INIT's.

record Base : Set₁ where
  field
    K         : Set
    _==K_     : K → K → Bool
    ==K-sound : ∀ k l → T (k ==K l) → k ≡ l
    ty        : K → Syntax.Ty K Former
    Valid     : K → Set
    valid?    : (k : K) → Maybe (Valid k)
    -- Which constants are the terminal object ⊤ (allowed as targets).
    top?      : K → Bool

initSig : Base → Signature
initSig b = record
  { K         = K
  ; _==K_     = _==K_
  ; ==K-sound = ==K-sound
  ; B         = Former
  ; _==B_     = _==F_
  ; ==B-sound = ==F-sound
  ; ty        = ty
  ; Valid     = Valid
  ; valid?    = valid?
  ; bside     = Construction.side K top?
  ; bargs     = Construction.args K top?
  ; bres      = Construction.res K top?
  }
  where open Base b
