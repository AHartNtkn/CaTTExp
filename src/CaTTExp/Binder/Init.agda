------------------------------------------------------------------------
-- INIT (spec §9.3, syntax §1.1) as an instance of the binder
-- interface: six binding formers over a telescope X. Δ, a decidable
-- positivity check, and the stability laws (CaTTExp.Binder.Laws).
--
-- The telescope Δ of every former opens with its sort variables
-- X₀, …, X_{n-1} : ⋆ (n ≥ 1; spec §9.3 "several sorts", here all over
-- ⊤), followed by maps and cells A_n, …, A_{m-1}; entry j is bvar 0 j.
-- Writing μ_k for bnd μ k Δ ⟨⟩ and ηT y for bnd η y Δ ⟨⟩, the generic
-- model is η = ⟨μ_0, …, μ_{n-1}, ηT n, …, ηT (m-1)⟩, and a model is a
-- list of arguments for the telescope Δ itself (carriers, then the
-- rest). μ, rec and uni are indexed by a sort k < n; η, rec_y and uni_y
-- by an entry y ≥ n. With one sort this is the single-sorted rule.
--
--   former  arguments (bargs)          type (bres), bvar 0 j = argument j
--   μ_k     none                       ⋆
--   η_y     none                       A_y opened at η
--   rec_k   a model (A, σ) : Δ         μ_k → A_k
--   rec_y   a model (A, σ) : Δ         the cell of rec at y (below)
--   uni_k   a model, and two model     h_k ⇒ h′_k, the 2-cell between
--           morphisms (h, θ), (h′, θ′)  the carrier maps at sort k
--           from η to it
--   uni_y   the same                   the compatibility 3-cell at y
--
-- The components of a model morphism h : A₁ → A₂ are the naturality
-- cylinders of the entries (CaTTExp.Binder.Cyl, the construction of
-- CaTTExp.Naturality.Raw in binder syntax): at a sort X_k the map
-- h_k : A₁_k → A₂_k, at an entry y : A_y the cell
--
--   θ_y : a_y → b_y,   e.g. at a map y : S → T,  y¹ ▹ h_T  ⇒  h_S ◃ y²,
--
-- with the typed whiskers of CaTTExp.DerivedBoundary, a factor at an
-- X-free source or target omitted (not an identity), and at a k-cell
-- the nested whiskers of all its iterated boundaries; the cylinder of
-- a composite boundary is filled by CaTTExp.Naturality.DimOne's K₁.
-- uni_y is the cylinder of θ_y over the arrow context: the
-- modification between h and h′ whose components are the uni_i.
--
-- Composites, whiskerings and identities are coherences over the usual
-- pasting contexts. INIT's model-morphism cells are meant invertible;
-- the types here carry no `inv`: that INIT's cells are inv belongs to
-- the kernel's mark judgment (spec chapter 3; ledger S26e).
--
-- Positivity (`positive`). This instance's fragment of §9.3's check,
-- for the object terms the Agda kernel has (variables, constants,
-- binders; it has no limit or colimit formers yet):
--   * the leading entries are the sorts X_k : ⋆ (at least one), and no
--     later entry is an object;
--   * every other entry is a map or a cell (of any dimension) whose
--     underlying arrow type is S → T with
--       S a sort, or S mentions no variable bound by the telescope;
--       T a sort, or T mentions no variable bound by the telescope;
--   * sorts over bases (`basedOK`): the X-free targets allowed are ⊤
--     (a constant the base marks as ⊤), the base B_k of a structure
--     map p : X_k → B_k in the header right after the sorts, and the
--     target of a companion cell c : a ; p_k ⇒ s (marked inv), which
--     must follow every operation a into a based sort X_k (see the
--     block before `positive`);
--   * marks (spec §9.3): a sort may be marked grpd_k or ⋆^{≤n}
--     (S¹ = μ(X : grpd, b, l : b ⇒ b), ‖A‖_n = μ(X : ⋆^{≤n}, g : A → X)),
--     and an operation or cell may be marked inv (ℤ = μ(X, z, s inv)).
--     A model is an argument list for Δ itself, so the kernel's mark
--     premise makes it certify every mark. That μ_k and the generic
--     model η carry the marks of Δ is the mark judgment's business
--     (ledger S26d/S26e).
-- The arrow context Δ^→ (model morphisms) is stated where K₁ fills the
-- cylinders: every touched coherence in an entry's boundaries has
-- dimension 1 (`goodTy`). That covers cells of every dimension with
-- variable boundaries, and composite boundaries of maps (the companion
-- cells of sorts over bases). rec_y needs the entries up to y good; uni
-- needs every entry good; uni_y needs that and θ_y's cylinder filled
-- by K₁, i.e. y a map (at a k-cell, k ≥ 2, θ_y's boundaries are
-- k-dimensional coherences; their fillers are ledger C1d (2), and so
-- are composite boundaries of 2-cells, e.g. the torus).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Signature
open import CaTTExp.Naturality.DimOne using (K₁)

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

  -- The syntax as a signature (only its syntax is used: the cylinders
  -- of CaTTExp.Binder.Cyl are stated over a signature).
  𝕊c : Signature
  𝕊c = record
    { K = K ; _==K_ = λ _ _ → false ; ==K-sound = λ _ _ ()
    ; B = Former ; _==B_ = _==F_ ; ==B-sound = ==F-sound
    ; ty = λ _ → ⋆ ; Valid = λ _ → ⊤ ; valid? = λ _ → nothing
    ; bside = λ _ _ _ → false ; bargs = λ _ _ Δ → Δ ; bres = λ _ _ _ → ⋆
    }

  open import CaTTExp.Binder.Cyl 𝕊c K₁ public using (Datum; datum; cylTy)
  open import CaTTExp.Binder.CylOK 𝕊c public using (goodTy)

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

  PC1 PC2 : Ctx
  PC1  = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)
  PC2  = PC1 ▸ ⋆ ▸ arr ⋆ (v 1) (v 3)

  -- f ; g for f : a → b, g : b → c (the source of a companion cell).
  cmp : Tm → Tm → Tm → Tm → Tm → Tm
  cmp a b c f g = coh PC2 (arr ⋆ (v 0) (v 3)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g)

  ----------------------------------------------------------------------
  -- Sorts. The telescope opens with its sort variables X₀, …, X_{m-1},
  -- the leading entries of type ⋆; `sorts Δ` is m.

  isStar : Ty → Bool
  isStar ⋆           = true
  isStar (arr _ _ _) = false

  sorts : Ctx → Nat
  sorts ε       = 0
  sorts (Δ ▸[ _ ] A) = if (sorts Δ ==ℕ len Δ) ∧ isStar A then suc (len Δ) else sorts Δ

  -- Which sort a term is, if it is one.
  srt : Nat → Tm → Maybe Nat
  srt m (bvar zero j) = if j <ℕ m then just j else nothing
  srt m _             = nothing

  isSort : Nat → Tm → Bool
  isSort m t = is-just (srt m t)

  ----------------------------------------------------------------------
  -- Positivity.

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
    mTel d (Δ ▸[ _ ] A) = mTel d Δ ∨ mTy d A

    mSub : Nat → Sub → Bool
    mSub d ⟨⟩       = false
    mSub d (σ ,ₛ t) = mSub d σ ∨ mTm d t

  srcOK tgtOK : Nat → Tm → Bool
  srcOK m S = isSort m S ∨ not (mTm 0 S)
  tgtOK m T = isSort m T ∨ not (mTm 0 T)

  -- The underlying arrow S → T of a map or cell type.
  base : Ty → Maybe (Tm × Tm)
  base ⋆                       = nothing
  base (arr ⋆ s t)             = just (s , t)
  base (arr (arr A a b) _ _)   = base (arr A a b)

  okBase : Nat → Maybe (Tm × Tm) → Bool
  okBase m nothing        = false
  okBase m (just (S , T)) = srcOK m S ∧ tgtOK m T

  entryOK : Nat → Ty → Bool
  entryOK m A = okBase m (base A)

  -- Marks (spec §9.3): a sort may be restricted to a reflective class
  -- closed under limits and filtered colimits, `grpd_k` or ⋆^{≤n}; an
  -- operation or cell may be marked inv.
  isInvMark isSortMark : Mark → Bool
  isInvMark minv = true
  isInvMark _    = false
  isSortMark (mgrpd _)  = true
  isSortMark (mtrunc _) = true
  isSortMark _          = false

  marksOKAt : Nat → Nat → List Mark → Bool
  marksOKAt m j ms = if j <ℕ m then all isSortMark ms else all isInvMark ms

  -- Every entry after the sorts is a map or cell with a good base, and
  -- marks are as above.
  posFrom : Nat → Ctx → Bool
  posFrom m ε             = true
  posFrom m (Δ ▸[ ms ] A) = posFrom m Δ ∧ marksOKAt m (len Δ) ms ∧ ((len Δ <ℕ m) ∨ entryOK m A)

  -- A variable of the binder at depth 0, other than through a parameter.
  bv0? : Tm → Maybe Nat
  bv0? (bvar zero j) = just j
  bv0? _             = nothing

  -- Entries whose model-morphism component the kernel states: every
  -- touched coherence in their boundaries has dimension 1, so that
  -- CaTTExp.Naturality.DimOne's K₁ fills its cylinder (`goodTy`, all
  -- bound variables selected). Cells of any dimension with variable
  -- boundaries are good; so are composite boundaries of maps.
  allSel : Nat → Bool
  allSel _ = true

  -- Every entry below m is good.
  okBelow : Nat → Ctx → Bool
  okBelow m ε       = true
  okBelow m (Δ ▸[ _ ] A) = okBelow m Δ ∧ (not (len Δ <ℕ m) ∨ goodTy allSel A)

  ----------------------------------------------------------------------
  -- Targets, and sorts over bases (spec §9.3 "several sorts, over
  -- bases"; the syntax of notes/higher-inductive.md §8 as fixed by the
  -- HIT thread). `posFrom` checks sources, and that targets are sorts or
  -- X-free. `basedOK` checks which X-free targets are allowed:
  --
  --   * the header: right after the sorts, structure maps p : X_k → B_k
  --     (B_k X-free; at most one per sort, in increasing order of k).
  --     X_k is then a sort over the base B_k;
  --   * in the body, an X-free target must be ⊤, unless the entry is
  --     the companion cell of an operation (below);
  --   * an operation a : S → X_k into a based sort must be a map (not a
  --     cell), followed by its companion c : a ; p_k ⇒ s marked inv,
  --     where s : S → B_k is a term (not a new variable: a definition,
  --     so that a is a map S → s*X_k into a pullback of X_k).
  --
  -- The companion's source is recognised as the binary composite of
  -- a and p_k (a coherence over PC2 with arguments S, X_k, a, B_k, p_k);
  -- that its types fit is the telescope's typing premise. Cells of
  -- dimension ≥ 2 into a based sort are not accepted yet (ledger S26c).

  baseOf : Maybe Ty → Maybe (Tm × Tm)
  baseOf nothing  = nothing
  baseOf (just A) = base A

  entryBase : Ctx → Nat → Maybe (Tm × Tm)
  entryBase Δ y = baseOf (lookup Δ y)

  -- A header entry X_k → B (B X-free): k.
  hdrShape : Nat → Ty → Maybe Nat
  hdrShape n ⋆                     = nothing
  hdrShape n (arr ⋆ S B)           = if mTm 0 B then nothing else srt n S
  hdrShape n (arr (arr _ _ _) _ _) = nothing

  isPC2 : Ctx → Bool
  isPC2 (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)) = true
  isPC2 _ = false

  isCmpTy : Ty → Bool
  isCmpTy (arr ⋆ (var 0) (var 3)) = true
  isCmpTy _                       = false

  tri : Maybe Nat → Maybe Nat → Maybe Nat → Maybe (Nat × Nat × Nat)
  tri (just x) (just y) (just z) = just (x , y , z)
  tri _        _        _        = nothing

  -- The arguments X_k, a, p of a binary composite S → X_k → B.
  cmpSub : Sub → Maybe (Nat × Nat × Nat)
  cmpSub (⟨⟩ ,ₛ _ ,ₛ x ,ₛ a ,ₛ _ ,ₛ q) = tri (bv0? x) (bv0? a) (bv0? q)
  cmpSub _                             = nothing

  cmpTm : Tm → Maybe (Nat × Nat × Nat)
  cmpTm (coh Γ A τ) = if isPC2 Γ ∧ isCmpTy A then cmpSub τ else nothing
  cmpTm _           = nothing

  -- A companion cell (a ; p) ⇒ s between maps: (k, a, p).
  cmpShape : Ty → Maybe (Nat × Nat × Nat)
  cmpShape (arr (arr ⋆ _ _) u _) = cmpTm u
  cmpShape _                     = nothing

  -- Per-entry data, as functions of the index.
  mapMT : ∀ {X : Set} → (Ty → X) → X → Maybe Ty → X
  mapMT f d nothing  = d
  mapMT f d (just A) = f A

  tgtSrtB : Nat → Maybe (Tm × Tm) → Maybe Nat
  tgtSrtB n nothing        = nothing
  tgtSrtB n (just (_ , T)) = srt n T

  tgtTopB : Maybe (Tm × Tm) → Bool
  tgtTopB nothing        = false
  tgtTopB (just (_ , T)) = isTop? T

  record Info : Set where
    field
      hs : Nat → Maybe Nat                -- header shape
      ts : Nat → Maybe Nat                -- target sort
      tp : Nat → Bool                     -- target ⊤
      dm : Nat → Nat                      -- dimension
      cm : Nat → Maybe (Nat × Nat × Nat)  -- companion shape
      iv : Nat → Bool                     -- marked inv

  infoOf : Ctx → Info
  infoOf Δ = record
    { hs = λ j → mapMT (hdrShape (sorts Δ)) nothing (lookup Δ j)
    ; ts = λ j → tgtSrtB (sorts Δ) (entryBase Δ j)
    ; tp = λ j → tgtTopB (entryBase Δ j)
    ; dm = λ j → mapMT dim 0 (lookup Δ j)
    ; cm = λ j → mapMT cmpShape nothing (lookup Δ j)
    ; iv = λ j → minv ∈M marksAt Δ j
    }

  eqMN : Maybe Nat → Nat → Bool
  eqMN nothing  _ = false
  eqMN (just x) y = x ==ℕ y

  -- Length of the header starting at j, sorts at least lo.
  hdrGo : (Nat → Maybe Nat) → Nat → Nat → Nat → Nat
  hdrGo hs zero    j lo = 0
  hdrGo hs (suc f) j lo = step (hs j)
    where
    step : Maybe Nat → Nat
    step nothing  = 0
    step (just k) = if k <ℕ lo then 0 else suc (hdrGo hs f (suc j) (suc k))

  -- The header entry of sort k among c entries from j.
  findHdr : (Nat → Maybe Nat) → Nat → Nat → Nat → Maybe Nat
  findHdr hs k zero    j = nothing
  findHdr hs k (suc c) j = if eqMN (hs j) k then just j else findHdr hs k c (suc j)

  cmpIs : Maybe (Nat × Nat × Nat) → Nat → Nat → Nat → Bool
  cmpIs nothing              k j p = false
  cmpIs (just (k′ , j′ , p′)) k j p = (k′ ==ℕ k) ∧ (j′ ==ℕ j) ∧ (p′ ==ℕ p)

  -- Entry j of the body, given the header length h.
  okBased : Info → Nat → Nat → Nat → Maybe Nat → Bool
  okBased I j k h nothing  = true
  okBased I j k h (just p) =
    (Info.dm I j ==ℕ 1) ∧ cmpIs (Info.cm I (suc j)) k j p ∧ Info.iv I (suc j)

  okComp : Info → Nat → Nat → Nat → Maybe (Nat × Nat × Nat) → Bool
  okComp I n h j nothing              = false
  okComp I n h j (just (k , j′ , p)) = (suc j′ ==ℕ j) ∧ eqMN (findHdr (Info.hs I) k h n) p

  okTgt : Info → Nat → Nat → Nat → Maybe Nat → Bool
  okTgt I n h j (just k) = okBased I j k h (findHdr (Info.hs I) k h n)
  okTgt I n h j nothing  = Info.tp I j ∨ okComp I n h j (Info.cm I j)

  okB : Nat → Nat → Info → Nat → Bool
  okB n L I j =
    if j <ℕ (n + hdrGo (Info.hs I) L n 0) then true
    else okTgt I n (hdrGo (Info.hs I) L n 0) j (Info.ts I j)

  allBelow : Nat → (Nat → Bool) → Bool
  allBelow zero    f = true
  allBelow (suc L) f = allBelow L f ∧ f L

  basedOK : Ctx → Bool
  basedOK Δ = allBelow (len Δ) (okB (sorts Δ) (len Δ) (infoOf Δ))

  positive : Ctx → Bool
  positive Δ = ((0 <ℕ sorts Δ) ∧ posFrom (sorts Δ) Δ) ∧ basedOK Δ


  ----------------------------------------------------------------------
  -- Models and model morphisms.

  -- The carrier of sort k.
  μAt : Ctx → Nat → Tm
  μAt Δ k = bnd μ k Δ ⟨⟩

  -- Component j of the generic model.
  ηAt : Ctx → Nat → Tm
  ηAt Δ j = if j <ℕ sorts Δ then bnd μ j Δ ⟨⟩ else bnd η j Δ ⟨⟩

  -- The first k components of the generic model.
  ηPre : Ctx → Nat → Sub
  ηPre Δ zero    = ⟨⟩
  ηPre Δ (suc k) = ηPre Δ k ,ₛ ηAt Δ k

  -- The first k arguments, bvar 0 0, …, bvar 0 (k - 1).
  bvPre : Nat → Sub
  bvPre zero    = ⟨⟩
  bvPre (suc k) = bvPre k ,ₛ bvar 0 k

  -- The first k arguments from o, bvar 0 o, …, bvar 0 (o + k - 1).
  bvFrom : Nat → Nat → Sub
  bvFrom o zero    = ⟨⟩
  bvFrom o (suc k) = bvFrom o k ,ₛ bvar 0 (o + k)

  mty : Maybe Ty → Ty
  mty nothing  = ⋆
  mty (just A) = A

  -- The type of entry j of the telescope (its earlier entries bvar 0 i).
  entryTy : Ctx → Nat → Ty
  entryTy Δ j = mty (lookup Δ j)

  -- A morphism from the generic model η to the model given by the first
  -- len Δ arguments, with components th, as a cylinder datum: every
  -- entry selected, η and the arguments as the two copies.
  morD : Ctx → (Nat → Tm) → Datum
  morD Δ th = datum (ηPre Δ (len Δ)) (bvPre (len Δ)) allSel th

  -- Its component at k is a cylinder of entry k (CaTTExp.Binder.Cyl):
  -- the carrier map at a sort, the naturality cell θ_k at a map, its
  -- naturality (k+1)-cell at a k-cell; boundaries untouched by the
  -- telescope (X-free) are omitted, and the cylinder of a composite
  -- boundary is filled by K₁.
  θTy : Ctx → Nat → (Nat → Tm) → Ty
  θTy Δ k th = cylTy (morD Δ th) (bvar 0 k) (entryTy Δ k)

  -- The type of component k of a morphism from η to the model given by
  -- the first len Δ arguments, whose components are bvar 0 (o + i).
  morEntry : Ctx → Nat → Nat → Ty
  morEntry Δ o k = θTy Δ k (λ i → bvar 0 (o + i))

  morPre : Ctx → Nat → Nat → Ctx
  morPre Δ o zero    = ε
  morPre Δ o (suc k) = morPre Δ o k ▸ morEntry Δ o k

  -- A model morphism from η to the model given by the first len Δ
  -- arguments, starting at argument o.
  morTel : Ctx → Nat → Ctx
  morTel Δ o = morPre Δ o (len Δ)

  -- The components of rec: rec_k at a sort, rec_i otherwise.
  recTh : Ctx → Nat → Tm
  recTh Δ i = if i <ℕ sorts Δ then bnd rec i Δ (bvPre (len Δ)) else bnd recY i Δ (bvPre (len Δ))

  -- uni: a modification between the morphisms h (arguments from m)
  -- and h′ (from m + m), m = len Δ, as a cylinder datum over the
  -- arguments: h selected, the model fixed; its components uni_k at a
  -- sort, uni_i otherwise. uni_i's type is the cylinder of θ_i.
  uniTh : Ctx → Nat → Tm
  uniTh Δ i = if i <ℕ sorts Δ then bnd uni i Δ (bvPre (len Δ + len Δ + len Δ))
              else bnd uniY i Δ (bvPre (len Δ + len Δ + len Δ))

  modSel : Nat → Nat → Bool
  modSel m j = not (j <ℕ m) ∧ (j <ℕ m + m)

  modD : Ctx → Datum
  modD Δ = datum (bvPre (len Δ + len Δ)) (bvPre (len Δ) ++ₛ bvFrom (len Δ + len Δ) (len Δ))
                 (modSel (len Δ)) (λ j → uniTh Δ (j ∸ len Δ))

  uniYTy : Ctx → Nat → Ty
  uniYTy Δ y = cylTy (modD Δ) (bvar 0 (len Δ + y)) (morEntry Δ (len Δ) y)

  -- uni_y is stated where the modification's cylinder is filled by K₁:
  -- at maps (at a k-cell, k ≥ 2, θ_y's boundaries are coherences of
  -- dimension k; their cylinders need fillers of dimension k, ledger
  -- C1d (2)).
  good2 : Ctx → Nat → Bool
  good2 Δ y = goodTy (modSel (len Δ)) (morEntry Δ (len Δ) y)

  -- y is a sort, or an entry after the sorts.
  isSortIx inner : Nat → Ctx → Bool
  isSortIx y Δ = y <ℕ sorts Δ
  inner    y Δ = not (y <ℕ sorts Δ) ∧ (y <ℕ len Δ)

  sel : Former → Nat → Ctx → Bool
  sel μ    y Δ = isSortIx y Δ
  sel η    y Δ = inner y Δ
  sel rec  y Δ = isSortIx y Δ
  sel recY y Δ = inner y Δ ∧ okBelow (suc y) Δ
  sel uni  y Δ = isSortIx y Δ ∧ okBelow (len Δ) Δ
  sel uniY y Δ = (inner y Δ ∧ okBelow (len Δ) Δ) ∧ good2 Δ y

  side : Former → Nat → Ctx → Bool
  side b y Δ = positive Δ ∧ sel b y Δ

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
  res rec  y Δ = arr ⋆ (μAt Δ y) (bvar 0 y)
  res recY y Δ = θTy Δ y (recTh Δ)
  res uni  y Δ = arr (arr ⋆ (μAt Δ y) (bvar 0 y)) (bvar 0 (len Δ + y)) (bvar 0 (len Δ + len Δ + y))
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
