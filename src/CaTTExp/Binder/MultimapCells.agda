------------------------------------------------------------------------
-- Cells between unary multimaps as kernel cells (ledger S26j, step 2).
--
-- Step 1 (CaTTExp.Binder.Multimap) made every unary multimap derivable
-- in the biclosed checker a kernel 1-cell. This module extends that
-- to cells between unary multimaps, which is where (GB-dcut)'s directed
-- goals and (GB-cut)'s higher goals live.
--
-- Which cells. A kernel k-cell between maps X → Z is a k-cell of the
-- hom 𝒦(X, Z) = Hom_lax(X, Z) = X\Z (notes/conventions.md §4: "2-cells
-- of 𝒦 are lax transformations", and evaluation X ⊗ Hom_lax(X, Y) → Y
-- puts the argument first). By the left-evaluation row such a cell is
-- a multimap (X, ⟦Dᵏ⟧ ▸ Z): its time slot is in gap 1, after the input
-- (spec §8.1: "(B, ⟦Dᵏ⟧ ▸ C) is a lax k-cell between maps B → C").
-- So the admitted cell types (`okTy`) are a unary operation (X ▸ Z)
-- over atom formulas, and cells `hom m 1 A s t` over admitted A. An
-- invertible cell (mode inv) is an entry marked inv; an invertible
-- result is a plain kernel cell (its invertibility is not passed to the
-- kernel's mark judgment here).
--
-- The head. mmc_{k,Φ,t} has arity k objects followed by one kernel
-- cell per entry of Φ (marked inv when the entry is), and type the
-- kernel image of t's biclosed type. Types mention the boundaries of
-- cells, which are biclosed terms; their kernel image (`trTm`) is the
-- argument for a variable, and otherwise the mmc head of the term on
-- its **canonical support**: the entries it uses, closed under the
-- entries their types use, and the atoms they use, each kept in its
-- original order and renumbered (`canon`). The side condition requires
-- every head to be canonical (every entry and every atom is used),
-- like coh's requirement that its pasting context be exactly the
-- support of its type. So each biclosed term in a context has one
-- kernel image, and
-- a term written directly and the same term met as a boundary are the
-- same kernel term (`MultimapCellsExamples`, `curry-boundary`).
--
-- This file is the construction; the stability laws are
-- `MultimapCellsLaws`. The presupposition law for mmc is not yet
-- proved (ledger S26j). Its biclosed half is: the canonical head of
-- every inferring term passes the side condition with the renamed type
-- (`MultimapCellsWf.sub-mmcTy`). What remains is the kernel half (the
-- kernel images commute with the renaming onto a support). Step 1's
-- heads keep their presupposition law
-- (`MultimapPresup`). Like mm, mmc trusts `infer`, so it inherits its
-- two caveats: `glue`'s stated typing rule, and no sort discipline
-- (`here` instances are AdmI, not the data-sorted KInst; SortDisc).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Embed using (Binders)
open import CaTTExp.Binder.GrayForm
open import CaTTExp.Binder.Multimap using (MMI; mmi; atoms; mctx; mterm; _==MM_; ==MM-sound; atomFm)
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
import CaTTExp.Gray.Biclosed.SubstDef as GS

module CaTTExp.Binder.MultimapCells where

------------------------------------------------------------------------
-- Admitted types.

okTy : Nat → GB.CTy → Bool
okTy k (GB.op ((x ∷ []) GB.▸ z)) = atomFm k x ∧ atomFm k z
okTy k (GB.op _)                 = false
okTy k (GB.hom _ g A _ _)        = (g ==ℕ 1) ∧ okTy k A

------------------------------------------------------------------------
-- Supports.

-- Membership and position in a list of naturals.
idx : Nat → List Nat → Nat
idx i []       = 0
idx i (j ∷ js) = if i ==ℕ j then 0 else suc (idx i js)

-- Context variables of a term, in order of occurrence.
mutual
  varsT : GB.Tm → List Nat
  varsT (GB.var i)          = i ∷ []
  varsT (GB.comp f gs)      = varsT f ++ varsTs gs
  varsT (GB.glue a x b)     = varsT a ++ varsT x ++ varsT b
  varsT (GB.here _ _ _ ts)  = varsTs ts
  varsT _                   = []

  varsTs : List GB.Tm → List Nat
  varsTs []       = []
  varsTs (t ∷ ts) = varsT t ++ varsTs ts

varsY : GB.CTy → List Nat
varsY (GB.op _)          = []
varsY (GB.hom _ _ A s t) = varsY A ++ varsT s ++ varsT t

-- Object atoms of formulas, terms and types, in order of occurrence.
atF : GB.Fm → List Nat
atF (GB.obj i)  = i ∷ []
atF (GB.rep _)  = []
atF (GB.shp _)  = []
atF (x GB.⊗ y)  = atF x ++ atF y
atF (x GB.\\ y) = atF x ++ atF y
atF (x GB.// y) = atF x ++ atF y

atFs : List GB.Fm → List Nat
atFs []       = []
atFs (x ∷ xs) = atF x ++ atFs xs

mutual
  atT : GB.Tm → List Nat
  atT (GB.mP U V)         = atF U ++ atF V
  atT (GB.eL A C)         = atF A ++ atF C
  atT (GB.eR A C)         = atF A ++ atF C
  atT (GB.idt A)          = atF A
  atT (GB.comp f gs)      = atT f ++ atTs gs
  atT (GB.glue a x b)     = atT a ++ atT x ++ atT b
  atT (GB.here _ _ φs ts) = atFs φs ++ atTs ts
  atT _                   = []

  atTs : List GB.Tm → List Nat
  atTs []       = []
  atTs (t ∷ ts) = atT t ++ atTs ts

atY : GB.CTy → List Nat
atY (GB.op (xs GB.▸ z))  = atFs xs ++ atF z
atY (GB.hom _ _ A s t)   = atY A ++ atT s ++ atT t

nthY : GB.Ctx → Nat → GB.CTy
nthY Φ j with GT.lookup Φ j
... | just A  = A
... | nothing = GB.op ([] GB.▸ GB.obj 0)

-- The entries a term needs: the variables it uses, closed under the
-- dependencies of their types, listed in context order. In a
-- well-formed context entry j's type mentions only entries below j, so
-- one sweep from the top closes the set.
upTo : Nat → List Nat
upTo zero    = []
upTo (suc n) = upTo n ++ (n ∷ [])

closeFrom : GB.Ctx → Nat → List Nat → List Nat
closeFrom Φ zero    S = S
closeFrom Φ (suc j) S = closeFrom Φ j (if elem j S then S ++ varsY (nthY Φ j) else S)

record Canon : Set where
  constructor canonOf
  field
    cidx   : MMI          -- the canonical head
    catoms : List Nat     -- its atoms, as atoms of the original
    cvars  : List Nat     -- its entries, as entries of the original
open Canon public

-- The entries of a term's support and its atoms, in increasing order.
supVars : GB.Ctx → GB.Tm → List Nat
supVars Φ u = filter (λ j → elem j (closeFrom Φ (GT.length Φ) (varsT u))) (upTo (GT.length Φ))

concatAt : GB.Ctx → List Nat
concatAt []       = []
concatAt (A ∷ As) = atY A ++ concatAt As

atYM : Maybe GB.CTy → List Nat
atYM (just A) = atY A
atYM nothing  = []

-- The atoms of the support's types, of the term, and of its type.
supAtomsOf : GB.Ctx → GB.Tm → List Nat
supAtomsOf Φ u = concatAt (GT.map (nthY Φ) (supVars Φ u)) ++ atT u ++ atYM (GT.infer Φ u)

supAtoms : Nat → GB.Ctx → GB.Tm → List Nat
supAtoms k Φ u = filter (λ i → elem i (supAtomsOf Φ u)) (upTo k)

-- The renaming onto a support: atoms and entries to their positions.
-- Entries outside the support (never used by the term) go to pt.
renOf : List Nat → List Nat → GS.Sub
renOf as vs = GS.sub (λ i → GB.obj (idx i as))
                     (λ j → if elem j vs then GB.var (idx j vs) else GB.pt)

canon : Nat → GB.Ctx → GB.Tm → Canon
canon k Φ u = canonOf (mmi (GT.length as) Φ′ (GS.sT ren u)) as vs
  where
  vs  = supVars Φ u
  as  = supAtoms k Φ u
  ren = renOf as vs
  Φ′  = GT.map (GS.sY ren) (GT.map (nthY Φ) vs)

------------------------------------------------------------------------
-- The type of an mmc head.

isCanon : MMI → Bool
isCanon (mmi k Φ t) = cidx (canon k Φ t) ==MM mmi k Φ t

-- Every atom the head mentions, in its context or its term, is one of
-- its k atoms.
atomsBelow : Nat → GB.Ctx → GB.Tm → Bool
atomsBelow k Φ t = all (λ i → i <ℕ k) (concatAt Φ ++ atT t)

mmcTy : MMI → Maybe GB.CTy
mmcTy (mmi k Φ t) =
  if isCanon (mmi k Φ t) ∧ all (okTy k) Φ ∧ GT.wfCtx Φ ∧ atomsBelow k Φ t
  then (GT.infer Φ t >>= λ A → if okTy k A then just A else nothing)
  else nothing

------------------------------------------------------------------------
-- The construction.

module CellsConstruction (K B : Set) (injG : GBF → B) (injC : MMI → B) where

  open Syntax K B
  open GrayFormConstruction K B injG public

  fmB : GB.Fm → Tm
  fmB (GB.obj i)  = bvar 0 i
  fmB (GB.rep _)  = bvar 0 0   -- unreachable under atomFm
  fmB (GB.shp _)  = bvar 0 0   -- unreachable under atomFm
  fmB (x GB.⊗ y)  = fmB x ⊗ᵗ fmB y
  fmB (x GB.\\ y) = fmB x \\ᵗ fmB y
  fmB (x GB.// y) = fmB x //ᵗ fmB y

  -- Bound variables 0 j for j in a list, after ρ.
  bvsOf : Sub → List Nat → Sub
  bvsOf ρ []       = ρ
  bvsOf ρ (j ∷ js) = bvsOf (ρ ,ₛ bvar 0 j) js

  -- The kernel arguments of a canonical support, inside a telescope
  -- with k atoms in front.
  supArgs : Nat → Canon → Sub
  supArgs k c = bvsOf (bvsOf ⟨⟩ (catoms c)) (GT.map (k +_) (cvars c))

  -- The image of a term that is not a variable.
  trHead : Nat → GB.Ctx → GB.Tm → Tm
  trHead k Φ u = bnd (injC (cidx (canon k Φ u))) 0 ε (supArgs k (canon k Φ u))

  trTm : Nat → GB.Ctx → GB.Tm → Tm
  trTm k Φ (GB.var j) = bvar 0 (k + j)
  trTm k Φ u          = trHead k Φ u

  trTy : Nat → GB.Ctx → GB.CTy → Ty
  trTy k Φ (GB.op ((x ∷ []) GB.▸ z)) = arr ⋆ (fmB x) (fmB z)
  trTy k Φ (GB.op _)                 = ⋆
  trTy k Φ (GB.hom _ _ A s t)        = arr (trTy k Φ A) (trTm k Φ s) (trTm k Φ t)

  marksOf : GB.CTy → List Mark
  marksOf (GB.hom GB.inv _ _ _ _) = minv ∷ []
  marksOf _                       = []

  atomsTel : Nat → Ctx
  atomsTel zero    = ε
  atomsTel (suc k) = atomsTel k ▸ ⋆

  -- Entry j's type is read over the whole Φ: its boundaries only use
  -- entries below j, and their canonical images do not depend on the
  -- rest of Φ.
  cellsTel : Nat → GB.Ctx → Ctx → GB.Ctx → Ctx
  cellsTel k Φ Θ []       = Θ
  cellsTel k Φ Θ (A ∷ As) = cellsTel k Φ (Θ ▸[ marksOf A ] trTy k Φ A) As

  arity : Nat → GB.Ctx → Ctx
  arity k Φ = cellsTel k Φ (atomsTel k) Φ

  sideC : MMI → Nat → Ctx → Bool
  sideC b y Δ = (y ==ℕ 0) ∧ isε Δ ∧ is-just (mmcTy b)

  argsC : MMI → Nat → Ctx → Ctx
  argsC (mmi k Φ t) y Δ = arity k Φ

  resC : MMI → Nat → Ctx → Ty
  resC b y Δ with mmcTy b
  ... | just A  = trTy (atoms b) (mctx b) A
  ... | nothing = ⋆

  mmcApp : MMI → Sub → Tm
  mmcApp b ts = bnd (injC b) 0 ε ts

------------------------------------------------------------------------
-- The Gray object formers and the mmc heads together.

data GCF : Set where
  gform : GBF → GCF
  mmc   : MMI → GCF

_==GC_ : GCF → GCF → Bool
gform a ==GC gform b = a ==G b
mmc a   ==GC mmc b   = a ==MM b
_       ==GC _       = false

==GC-sound : ∀ a b → T (a ==GC b) → a ≡ b
==GC-sound (gform a) (gform b) p = cong gform (==G-sound a b p)
==GC-sound (mmc a)   (mmc b)   p = cong mmc (==MM-sound a b p)
==GC-sound (gform _) (mmc _)   ()
==GC-sound (mmc _)   (gform _) ()

module GCInterface (K : Set) where
  open Syntax K GCF
  open CellsConstruction K GCF gform mmc public

  sideGC : GCF → Nat → Ctx → Bool
  sideGC (gform b) = side b
  sideGC (mmc b)   = sideC b

  argsGC : GCF → Nat → Ctx → Ctx
  argsGC (gform b) = args b
  argsGC (mmc b)   = argsC b

  resGC : GCF → Nat → Ctx → Ty
  resGC (gform b) = res b
  resGC (mmc b)   = resC b

cellBinders : (K : Set) → Binders K
cellBinders K = record
  { B = GCF ; _==B_ = _==GC_ ; ==B-sound = ==GC-sound
  ; bside = sideGC ; bargs = argsGC ; bres = resGC }
  where open GCInterface K
