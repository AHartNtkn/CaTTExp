------------------------------------------------------------------------
-- Unary multimaps as kernel 1-cells (ledger S26j, step 1; spec §8.1:
-- "with n = 1 a multimap is an ambient 1-cell").
--
-- The universal properties of ⊗, \ and / (spec §8.2–8.3) are rules of
-- the multimap judgment, implemented over its own syntax by the checker
-- of CaTTExp.Gray.Biclosed.Typing (`infer`: corollas, planar
-- composition, whiskering, collars, and the template instances `here`
-- of (GB-cut) and (GB-dcut)). This module makes every **unary**
-- multimap derivable there into a kernel 1-cell, by one head family,
-- in the style of the coh rule:
--
--   mm_{k,Φ,t}  with  arity  a₀ … a_{k-1} : ⋆,  f_j : ⟦X_j⟧ → ⟦Z_j⟧ (j < |Φ|)
--               and   type   ⟦X⟧ → ⟦Z⟧
--
-- for a multimap context Φ whose entries are unary operations
-- (X_j ▸ Z_j), and a multimap term t with infer Φ t = (X ▸ Z). The
-- formulas X_j, Z_j, X, Z are built from object atoms obj i (i < k)
-- with ⊗, \ and /, and ⟦–⟧ reads them as kernel objects with the heads
-- of CaTTExp.Binder.GrayForm, atom i being the argument a_i. So the
-- arguments of mm are kernel objects and kernel 1-cells, and the
-- side condition, like coh's, sees only the head's own data (k, Φ, t),
-- never the context of use. Intermediate formulas inside t may be
-- representables (probe rows); only Φ and the result must be
-- atom formulas.
--
-- Example (`MultimapExamples`): from a kernel 1-cell f : A ⊗ B → C,
-- the left-evaluation row at n = 0 gives its curry B → A\C as a kernel
-- 1-cell; from g : B → A\C, the evaluation gives back A ⊗ B → C.
--
-- What this does *not* give. Multimaps with n ≠ 1 inputs, and cells
-- between multimaps (time slots), remain judgments of the Biclosed
-- syntax only: Φ may contain only unary entries, and the result must
-- be a unary operation (not a higher cell). Their kernel form is S26j's
-- remaining part. The side condition trusts `infer`, so mm inherits
-- its caveat that `glue`'s typing rule is stated in the Biclosed
-- checker, not derived from L (spec §8.1 Status). `infer` alone does
-- not impose the sort discipline (Gray.Biclosed.SortDisc: its `here`
-- instances are AdmI instances, a strict superset of the data-sorted
-- kernel instances KInst), so the side condition also asks that Φ and
-- t be sorted (`sortedT`, `sortedY` below): every here node sends its
-- template's data variable to a non-representable formula over the
-- atoms, which is SortDisc's DSub (`MultimapSorted.dataInst-dsub`).
--
-- The construction is over any set B of formers into which the Gray
-- object formers and the mm heads inject, so it sits beside DES, INIT
-- and the other heads.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Embed using (Binders)
open import CaTTExp.Binder.GrayForm
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
open import CaTTExp.Gray.Biclosed.SortDisc using (nonRep; headVar; tmplData)

module CaTTExp.Binder.Multimap where

------------------------------------------------------------------------
-- The index of an mm head: the number of atoms, the multimap context,
-- the multimap term.

record MMI : Set where
  constructor mmi
  field
    atoms : Nat
    mctx  : GB.Ctx
    mterm : GB.Tm
open MMI public

_==MM_ : MMI → MMI → Bool
mmi k Φ t ==MM mmi l Ψ u = (k ==ℕ l) ∧ GB.eqCtx Φ Ψ ∧ GB.eqTm t u

==MM-sound : ∀ a b → T (a ==MM b) → a ≡ b
==MM-sound (mmi k Φ t) (mmi l Ψ u) p =
  let p₁ = ∧-fst p ; p₂ = ∧-snd {k ==ℕ l} p in
  cong₃ (==ℕ-sound k l p₁) (GB.eqCtx-sound Φ Ψ (∧-fst p₂)) (GB.eqTm-sound t u (∧-snd {GB.eqCtx Φ Ψ} p₂))
  where
  cong₃ : ∀ {k l Φ Ψ t u} → k ≡ l → Φ ≡ Ψ → t ≡ u → mmi k Φ t ≡ mmi l Ψ u
  cong₃ refl refl refl = refl

------------------------------------------------------------------------
-- Atom formulas and unary multimap types.

-- Built from obj i, i < k, with ⊗, \ and /.
atomFm : Nat → GB.Fm → Bool
atomFm k (GB.obj i)  = i <ℕ k
atomFm k (GB.rep _)  = false
atomFm k (GB.shp _)  = false
atomFm k (x GB.⊗ y)  = atomFm k x ∧ atomFm k y
atomFm k (x GB.\\ y) = atomFm k x ∧ atomFm k y
atomFm k (x GB.// y) = atomFm k x ∧ atomFm k y

-- A unary operation type (X ▸ Z) over atoms below k.
unaryTy : Nat → GB.CTy → Maybe (GB.Fm × GB.Fm)
unaryTy k (GB.op ((x ∷ []) GB.▸ z)) = if atomFm k x ∧ atomFm k z then just (x , z) else nothing
unaryTy k _                         = nothing

allUnary : Nat → GB.Ctx → Maybe (List (GB.Fm × GB.Fm))
allUnary k []       = just []
allUnary k (A ∷ As) = unaryTy k A >>= λ p → allUnary k As >>= λ ps → just (p ∷ ps)

------------------------------------------------------------------------
-- The sort discipline (spec §8.1, F.7.4 §2; `Gray.Biclosed.SortDisc`).
-- `infer` types every template instance (AdmI); the kernel's instances
-- (KInst) are those whose substitution is data-sorted: the template's
-- data variable goes to a non-representable formula whose head
-- variable, if any, is data-sorted. Over the atoms of a head every atom
-- is a data object, so a here node is data-sorted when its template's
-- data variable is given, by a non-representable formula, whose head
-- variable if any is an atom below k (`dataInst`; `MultimapSorted`
-- shows this is SortDisc's DSub). A term, or a type's boundaries, is
-- sorted when all its here nodes are.

headBelow : Nat → Maybe Nat → Bool
headBelow k nothing  = true
headBelow k (just i) = i <ℕ k

dataFm : Nat → List GB.Fm → Nat → Bool
dataFm k φs i = (i <ℕ GT.length φs) ∧ nonRep (GT.nthF φs i) ∧ headBelow k (headVar (GT.nthF φs i))

dataInst : Nat → GB.Tmpl → List GB.Fm → Bool
dataInst k t φs = all (dataFm k φs) (tmplData t)

mutual
  sortedT : Nat → GB.Tm → Bool
  sortedT k (GB.comp f gs)      = sortedT k f ∧ sortedTs k gs
  sortedT k (GB.glue a x b)     = sortedT k a ∧ sortedT k x ∧ sortedT k b
  sortedT k (GB.here t _ φs ts) = dataInst k t φs ∧ sortedTs k ts
  sortedT k _                   = true

  sortedTs : Nat → List GB.Tm → Bool
  sortedTs k []       = true
  sortedTs k (t ∷ ts) = sortedT k t ∧ sortedTs k ts

sortedY : Nat → GB.CTy → Bool
sortedY k (GB.op _)          = true
sortedY k (GB.hom _ _ A s t) = sortedY k A ∧ sortedT k s ∧ sortedT k t

-- The type of an mm head: Φ is all unary (entries `ps`), Φ is well
-- formed, Φ and t are sorted, and t has a unary type (X ▸ Z) over the
-- atoms.
mmTy : MMI → Maybe (List (GB.Fm × GB.Fm) × (GB.Fm × GB.Fm))
mmTy (mmi k Φ t) =
  allUnary k Φ >>= λ ps →
  ((if GT.wfCtx Φ ∧ all (sortedY k) Φ ∧ sortedT k t then GT.infer Φ t else nothing) >>= unaryTy k) >>= λ xz →
  just (ps , xz)

------------------------------------------------------------------------
-- The construction.

module MultimapConstruction (K B : Set) (injG : GBF → B) (injM : MMI → B) where

  open Syntax K B
  open GrayFormConstruction K B injG public

  -- A formula read with the atoms given by `at` (bound variables for
  -- the interface, kernel terms for examples).
  fmWith : (Nat → Tm) → GB.Fm → Tm
  fmWith at (GB.obj i)  = at i
  fmWith at (GB.rep _)  = at 0   -- unreachable under atomFm
  fmWith at (GB.shp _)  = at 0   -- unreachable under atomFm
  fmWith at (x GB.⊗ y)  = fmWith at x ⊗ᵗ fmWith at y
  fmWith at (x GB.\\ y) = fmWith at x \\ᵗ fmWith at y
  fmWith at (x GB.// y) = fmWith at x //ᵗ fmWith at y

  fmB : GB.Fm → Tm
  fmB = fmWith (bvar 0)

  -- The arity: k objects, then one 1-cell per entry of Φ.
  atomsTel : Nat → Ctx
  atomsTel zero    = ε
  atomsTel (suc k) = atomsTel k ▸ ⋆

  cellsTel : Ctx → List (GB.Fm × GB.Fm) → Ctx
  cellsTel Θ []             = Θ
  cellsTel Θ ((x , z) ∷ ps) = cellsTel (Θ ▸ arr ⋆ (fmB x) (fmB z)) ps

  arity : Nat → List (GB.Fm × GB.Fm) → Ctx
  arity k ps = cellsTel (atomsTel k) ps

  sideM : MMI → Nat → Ctx → Bool
  sideM b y Δ = (y ==ℕ 0) ∧ isε Δ ∧ is-just (mmTy b)

  argsM : MMI → Nat → Ctx → Ctx
  argsM b y Δ with mmTy b
  ... | just (ps , _) = arity (atoms b) ps
  ... | nothing       = ε

  resM : MMI → Nat → Ctx → Ty
  resM b y Δ with mmTy b
  ... | just (_ , (x , z)) = arr ⋆ (fmB x) (fmB z)
  ... | nothing            = ⋆

  -- The head applied to atoms and cells.
  mmApp : MMI → Sub → Tm
  mmApp b ts = bnd (injM b) 0 ε ts

------------------------------------------------------------------------
-- The Gray object formers and the mm heads together.

data GMF : Set where
  gform : GBF → GMF
  mmh   : MMI → GMF

_==GM_ : GMF → GMF → Bool
gform a ==GM gform b = a ==G b
mmh a   ==GM mmh b   = a ==MM b
_       ==GM _       = false

==GM-sound : ∀ a b → T (a ==GM b) → a ≡ b
==GM-sound (gform a) (gform b) p = cong gform (==G-sound a b p)
==GM-sound (mmh a)   (mmh b)   p = cong mmh (==MM-sound a b p)
==GM-sound (gform _) (mmh _)   ()
==GM-sound (mmh _)   (gform _) ()

module GMInterface (K : Set) where
  open Syntax K GMF
  open MultimapConstruction K GMF gform mmh public

  sideGM : GMF → Nat → Ctx → Bool
  sideGM (gform b) = side b
  sideGM (mmh b)   = sideM b

  argsGM : GMF → Nat → Ctx → Ctx
  argsGM (gform b) = args b
  argsGM (mmh b)   = argsM b

  resGM : GMF → Nat → Ctx → Ty
  resGM (gform b) = res b
  resGM (mmh b)   = resM b

multimapBinders : (K : Set) → Binders K
multimapBinders K = record
  { B = GMF ; _==B_ = _==GM_ ; ==B-sound = ==GM-sound
  ; bside = sideGM ; bargs = argsGM ; bres = resGM }
  where open GMInterface K
