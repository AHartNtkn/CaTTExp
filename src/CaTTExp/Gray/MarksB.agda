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
-- `formerMarks b y Δ` lists the marks an occurrence bnd b y Δ ts
-- carries by virtue of its former (selector y, telescope Δ), as
-- `marksAt` does for a variable: DES gives minv on all four formers;
-- INIT gives η_y minv exactly when entry y of Δ is marked minv, and μ_k
-- the marks of sort k (mgrpd for S¹ as X : grpd₁); other formers (INIT's) get their clauses from their own
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
-- mgrpd k ↦ "a variable whose entry, or a former occurrence whose
-- formerMarks, carry grpd_k′ with k′ ≤ k", and mtrunc k likewise with
-- truncation marks (the minimal reading of spec §9.1 T-var)
-- (invertibility-markings.md §1.2, precision from PR #41).
-- `markVar` proves the kernel's hypothesis MarkVar (rule MARK).
-- Renaming and substitution stability (MarkRen, MarkSub) are proved in
-- CaTTExp.Gray.MarksBKernel (instantiated for DES in Gray.MarksBDes).
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
  (formerMarks : Binders.B bi → Nat → NSyn.Ctx (Old.Signature.K 𝕊₀) (Binders.B bi) → List NSyn.Mark)
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

-- The numbered marks: mgrpd (tr = false) and mtrunc (tr = true).
mk : Bool → Nat → Mark
mk false k = mgrpd k
mk true  k = mtrunc k

markAt : Bool → Mark → Maybe Nat
markAt false (mgrpd j)  = just j
markAt true  (mtrunc j) = just j
markAt _     _          = nothing

leAt : Nat → Maybe Nat → Bool
leAt h (just j) = j <ℕ suc h
leAt h nothing  = false

-- m is the numbered mark of kind tr at some k′ ≤ h.
atLe : Bool → Nat → Mark → Bool
atLe tr h m = leAt h (markAt tr m)

grpdLe : Nat → Mark → Bool
grpdLe = atLe false

anyM : (Mark → Bool) → List Mark → Bool
anyM p []       = false
anyM p (m ∷ ms) = p m ∨ anyM p ms

-- A term carries a mark grpd_k′ with k′ ≤ h: a variable through its
-- entry, a former occurrence through formerMarks (μ_k of a sort marked
-- grpd, spec §9.3).
-- Likewise for truncation marks (the minimal reading of spec §9.1 T-var:
-- a variable or former occurrence marked ⋆^{≤k′−2}, k′ ≤ h).
isAt : Ctx → Bool → Nat → Tm → Bool
isAt Γ tr h (var C)        = anyM (atLe tr h) (marksAt Γ C)
isAt Γ tr h (bnd b y Δ ts) = anyM (atLe tr h) (formerMarks b y Δ)
isAt Γ tr h _              = false

isGrpd : Ctx → Nat → Tm → Bool
isGrpd Γ = isAt Γ false

-- (OBJ-k): the 0-target of t carries grpd_k, k ≤ hd(t).
objAt : Ctx → Nat → Maybe (Tm × Tm) → Bool
objAt Γ n (just (_ , c)) = isGrpd Γ (n ∸ 1) c ∧ (1 <ℕ n)
objAt Γ n nothing        = false

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
        ms = formerMarks b y Δ
        i = (minv ∈M ms) ∨ objRule Γ A                 -- (DES), (DES-inv)
        p = (mps ∈M ms) ∨ (i ∧ hdAtLeast 1 A)          -- (INV⇒PS)
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

mark : Ctx → Mark → Tm → Bool
mark Γ minv      t = jinv (judgeT Γ t)
mark Γ mps       t = jps (judgeT Γ t)
mark Γ (mgrpd k) t  = isAt Γ false k t
mark Γ (mtrunc k) t = isAt Γ true k t

------------------------------------------------------------------------
-- A numbered mark in a list gives the atLe test at its number.

markAt-mk : ∀ tr k → markAt tr (mk tr k) ≡ just k
markAt-mk false k = refl
markAt-mk true  k = refl

at-self : ∀ tr k ms m → markAt tr m ≡ just k → T (m ∈M ms) → T (anyM (atLe tr k) ms)
at-self tr k (n ∷ ms) m e p with m ==M n in q
... | true rewrite sym (==M-sound m n (subst T (sym q) tt)) | e = or-l {k <ℕ suc k} (lt-self k)
  where
  or-l : ∀ {a b} → T a → T (a ∨ b)
  or-l {true} _ = tt
  lt-self : ∀ k → T (k <ℕ suc k)
  lt-self zero    = tt
  lt-self (suc k) = lt-self k
... | false = or-r (atLe tr k n) (at-self tr k ms m e p)
  where
  or-r : ∀ a {b} → T b → T (a ∨ b)
  or-r true  _ = tt
  or-r false q = q

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

  <ℕ-suc : ∀ l → T (l <ℕ suc l)
  <ℕ-suc zero    = tt
  <ℕ-suc (suc l) = <ℕ-suc l

  T∨r : ∀ a {b} → T b → T (a ∨ b)
  T∨r true  _ = tt
  T∨r false q = q

  self : ∀ Γ x m → T (m ∈M marksAt Γ x) → T (mark Γ m (var x))
  self Γ x minv      p = var-inv Γ x p
  self Γ x mps       p = var-ps Γ x p
  self Γ x (mgrpd k)  p = at-self false k (marksAt Γ x) (mgrpd k) refl p
  self Γ x (mtrunc k) p = at-self true k (marksAt Γ x) (mtrunc k) refl p

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
