------------------------------------------------------------------------
-- The invertibility and pseudo marks of two-tier L (CaTTExp.Gray.Marks,
-- notes/invertibility-markings.md §1.2) on binder syntax, with the
-- destructor rules (ledger E4):
--
--   (DES)      unitL t, unitR t are inv
--   (DES-inv)  linv t, rinv t are inv
--
-- Both are stated without premises: a destructor occurrence is only
-- well typed when its cell argument is inv, because the destructors'
-- argument telescope Dⁿ marks its top entry `minv` and the binder
-- kernel checks that mark on the argument (CaTTExp.Binder.TypingWith).
-- So "the occurrence is well formed" already contains "t inv".
-- `formerInv b y` says which formers (with selector y) are inv this
-- way; other formers (INIT's) get their clauses from their own
-- interface, and otherwise only (OBJ-k).
--
-- Every other rule is CaTTExp.Gray.Marks unchanged:
--   * marks of variables are read from their context entries
--     (`marksAt`), instead of a separate list;
--   * the coh rules (COH-inv), (OP-inv), (OP-ps) reuse Gray.Marks'
--     invC/psC on the coh's pasting context, type and boundary *erased*
--     to binder-free syntax by CaTTExp.Gray.DesSide (destructors erased
--     to their cell, as for L's side condition), with the judgments of
--     the substitution's entries computed here;
--   * (OBJ-k), (INV⇒PS), (PS*) as in Gray.Marks.
--
-- `mark` is the kernel's mark parameter: minv ↦ inv, mps ↦ ps, and
-- mgrpd k ↦ "a variable whose entry is marked grpd_k′ with k′ ≤ k"
-- (invertibility-markings.md §1.2, precision from PR #41).
-- `markVar` proves the kernel's hypothesis MarkVar (rule MARK).
-- Renaming and substitution stability (MarkRen, MarkSub) are the
-- binder-syntax counterparts of Gray.MarksSubst / Gray.MarksFuel and are
-- not proved here.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Syntax as NSyn
open import CaTTExp.Binder.Embed
import CaTTExp.Binder.Mark
import CaTTExp.Binder.TypingWith
import CaTTExp.Gray.Marks
import CaTTExp.Gray.Support

module CaTTExp.Gray.MarksB
  (𝕊₀ : Old.Signature)
  (bi : Binders (Old.Signature.K 𝕊₀))
  (cellArg : Binders.B bi → Maybe Nat)
  (formerInv : Binders.B bi → Nat → Bool)
  where

private
  K = Old.Signature.K 𝕊₀
  B = Binders.B bi
  module N = NSyn K B
  module GM = CaTTExp.Gray.Marks 𝕊₀
  module GS = CaTTExp.Gray.Support 𝕊₀
open N
open GM using (IP; ip; jinv; jps; jpss; invC; psC)
open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArg using (dCtx; dTy; dTm)

------------------------------------------------------------------------
-- Syntactic types and the auxiliary tests of Gray.Marks, on binder
-- syntax.

typeOf : Ctx → Tm → Maybe Ty
typeOf Γ (var i)       = lookup Γ i
typeOf Γ (bvar _ _)    = nothing
typeOf Γ (coh Θ A γ)   = just (A [ γ ]ty)
typeOf Γ (cst k)       = just (Emb.eTy K B (Old.Signature.ty 𝕊₀ k))
typeOf Γ (bnd b y Δ ts) = just (opTy 0 ts (Binders.bres bi b y Δ))

hdAtLeast : Nat → Maybe Ty → Bool
hdAtLeast n (just A) = n <ℕ dim A
hdAtLeast n nothing  = false

endsTy : Ty → Maybe (Tm × Tm)
endsTy ⋆                = nothing
endsTy (arr ⋆ s t)      = just (s , t)
endsTy (arr (arr A a b) _ _) = endsTy (arr A a b)

grpdLe : Nat → Mark → Bool
grpdLe h (mgrpd k) = k <ℕ suc h
grpdLe h _         = false

anyM : (Mark → Bool) → List Mark → Bool
anyM p []       = false
anyM p (m ∷ ms) = p m ∨ anyM p ms

-- (OBJ-k): the 0-target of t is a variable marked grpd_k, k ≤ hd(t).
objAt : Ctx → Nat → Maybe (Tm × Tm) → Bool
objAt Γ n (just (_ , var C)) = anyM (grpdLe (n ∸ 1)) (marksAt Γ C) ∧ (1 <ℕ n)
objAt Γ n _                  = false

objRule : Ctx → Maybe Ty → Bool
objRule Γ nothing  = false
objRule Γ (just A) = objAt Γ (dim A) (endsTy A)

-- The coh rules on the erased coh, given the judgments of γ.
cohRules : Ctx → Ty → Tm → Tm → List IP → Bool × Bool
cohRules Θ A t u comps with dCtx Θ | dTy A | dTm t | dTm u
... | just Θ₀ | just A₀ | just t₀ | just u₀ = invC Θ₀ A₀ t₀ u₀ comps , psC Θ₀ A₀ t₀ u₀ comps
... | _       | _       | _       | _       = false , false

------------------------------------------------------------------------
-- The judgments (fuel n, as in Gray.Marks).

mutual
  judge : Nat → Ctx → Tm → IP
  judge n Γ (var x) =
    let i = (minv ∈M marksAt Γ x) ∨ objRule Γ (lookup Γ x)
        p = (mps ∈M marksAt Γ x) ∨ (i ∧ hdAtLeast 1 (lookup Γ x))
    in ip i p (star n Γ (lookup Γ x) p)
  judge n Γ (bvar _ _) = ip false false false
  judge n Γ (cst k) =
    let A = typeOf Γ (cst k)
        i = objRule Γ A
        p = i ∧ hdAtLeast 1 A
    in ip i p (star n Γ A p)
  judge n Γ (coh Θ ⋆ γ) = ip false false false
  judge n Γ (coh Θ (arr A t u) γ) =
    let comps = judgeSub n Γ γ
        rs    = cohRules Θ A t u comps
        ty'   = just (arr A t u [ γ ]ty)
        i     = fst rs ∨ objRule Γ ty'
        p     = snd rs ∨ (i ∧ hdAtLeast 1 ty')
    in ip i p (star n Γ ty' p)
  judge n Γ (bnd b y Δ ts) =
    let A = typeOf Γ (bnd b y Δ ts)
        i = formerInv b y ∨ objRule Γ A                -- (DES), (DES-inv)
        p = i ∧ hdAtLeast 1 A                          -- (INV⇒PS)
    in ip i p (star n Γ A p)

  judgeSub : Nat → Ctx → Sub → List IP
  judgeSub n Γ ⟨⟩       = []
  judgeSub n Γ (γ ,ₛ t) = judgeSub n Γ γ ++ (judge n Γ t ∷ [])

  star : Nat → Ctx → Maybe Ty → Bool → Bool
  star n Γ nothing  p = false
  star n Γ (just A) p = (dim A ==ℕ 1) ∨ (p ∧ ((dim A ==ℕ 2) ∨ bdStar n Γ A))

  bdStar : Nat → Ctx → Ty → Bool
  bdStar zero    Γ A           = false
  bdStar (suc n) Γ ⋆           = false
  bdStar (suc n) Γ (arr A s u) = jpss (judge n Γ s) ∧ jpss (judge n Γ u)

fuelOf : Ctx → Tm → Nat
fuelOf Γ t with typeOf Γ t
... | just A  = dim A
... | nothing = 0

judgeT : Ctx → Tm → IP
judgeT Γ t = judge (fuelOf Γ t) Γ t

------------------------------------------------------------------------
-- The kernel's mark parameter.

isVarGrpd : Ctx → Nat → Tm → Bool
isVarGrpd Γ k (var C) = anyM (grpdLe k) (marksAt Γ C)
isVarGrpd Γ k _       = false

mark : Ctx → Mark → Tm → Bool
mark Γ minv      t = jinv (judgeT Γ t)
mark Γ mps       t = jps (judgeT Γ t)
mark Γ (mgrpd k) t = isVarGrpd Γ k t

------------------------------------------------------------------------
-- (MARK): a variable has the marks of its entry.

private
  ∨l : ∀ a {b} → T a → T (a ∨ b)
  ∨l true _ = tt

  T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
  T∧ {true} p = tt , p

  ∧T : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧T {true} _ q = q

  -- Gray.Marks' judgments of a variable do not depend on the fuel at
  -- the inv and ps components.
  var-inv : ∀ Γ x → T (minv ∈M marksAt Γ x) → T (mark Γ minv (var x))
  var-inv Γ x p = ∨l (minv ∈M marksAt Γ x) p

  var-ps : ∀ Γ x → T (mps ∈M marksAt Γ x) → T (mark Γ mps (var x))
  var-ps Γ x p = ∨l (mps ∈M marksAt Γ x) p

  grpd-self : ∀ k ms → T (mgrpd k ∈M ms) → T (anyM (grpdLe k) ms)
  grpd-self k (minv ∷ ms) p = grpd-self k ms p
  grpd-self k (mps ∷ ms) p = grpd-self k ms p
  grpd-self k (mgrpd l ∷ ms) p with k ==ℕ l in e
  ... | true  rewrite ==ℕ-sound k l (subst T (sym e) tt) = ∨l (l <ℕ suc l) (<ℕ-suc l)
    where
    <ℕ-suc : ∀ l → T (l <ℕ suc l)
    <ℕ-suc zero    = tt
    <ℕ-suc (suc l) = <ℕ-suc l
  ... | false = T∨r (l <ℕ suc k) (grpd-self k ms p)
    where
    T∨r : ∀ a {b} → T b → T (a ∨ b)
    T∨r true  _ = tt
    T∨r false q = q

  self : ∀ Γ x m → T (m ∈M marksAt Γ x) → T (mark Γ m (var x))
  self Γ x minv      p = var-inv Γ x p
  self Γ x mps       p = var-ps Γ x p
  self Γ x (mgrpd k) p = grpd-self k (marksAt Γ x) p

  all-self : ∀ Γ x ms → (∀ m → T (m ∈M ms) → T (m ∈M marksAt Γ x)) →
             T (all (λ m → mark Γ m (var x)) ms)
  all-self Γ x []       _ = tt
  all-self Γ x (m ∷ ms) h =
    ∧T (self Γ x m (h m (∨l (m ==M m) (==M-refl m))))
       (all-self Γ x ms (λ n q → h n (T∨r′ (n ==M m) q)))
    where
    T∨r′ : ∀ a {b} → T b → T (a ∨ b)
    T∨r′ true  _ = tt
    T∨r′ false q = q

-- The hypothesis MarkVar of CaTTExp.Binder.Subst, for this judgment
-- (stated without the typing premises, which it does not need).
markVar′ : ∀ Γ i → T (all (λ m → mark Γ m (var i)) (marksAt Γ i))
markVar′ Γ i = all-self Γ i (marksAt Γ i) (λ m p → p)

------------------------------------------------------------------------
-- The kernel: binder-syntax L with these marks, and MarkVar for it.

open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArg using (graySideD)
import CaTTExp.Binder.Subst

module Kernel = CaTTExp.Binder.TypingWith (extend 𝕊₀ bi) graySideD mark

markVar : CaTTExp.Binder.Subst.MarkVar (extend 𝕊₀ bi) graySideD mark
markVar {Γ} {i} _ _ = markVar′ Γ i
