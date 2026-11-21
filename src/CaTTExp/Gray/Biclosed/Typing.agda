------------------------------------------------------------------------
-- D7d: a type checker for the multimap / cell syntax of F.7.4.
--
-- infer Γ t computes the cell type of t, wf Γ A checks a cell type,
-- wfCtx checks a context entry by entry.  The rules:
--   * corollas have their F.7.4 §2 types;
--   * comp f gs is planar substitution when everything is an
--     operation, and whiskering when exactly one of f, gs is a higher
--     cell (the boundary is whiskered and the time-slot gap is moved
--     by the number of inputs to its left);
--   * glue a⁻ x a⁺ adjoins invertible collars a± : p± ≅ q± to a cell x
--     whose faces at the collars' level are q⁻, q⁺ (this is an L-core
--     composite; its typing rule is stated here, not derived from L);
--   * here t e φs ts, goal e of template t at the instance (φs, ts), has
--     the substituted goal type when t satisfies the template side
--     conditions (okT), the lists cover the template's variables, and
--     each ts[i] has the substituted type of the i-th template entry.
--     This is CaTT's rule for coh(Γ, A)[σ]: the term records σ.
-- So infer is a derivability check for the kernel, up to the stated
-- typing rule of glue and the sort discipline (SortDisc).  Until
-- 2026-11-20 the coherence term was `here A`, typed at every
-- well-formed A, which forgot the instance (HereAmbiguity.agda).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Typing where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps public
open import CaTTExp.Gray.Biclosed.SubstDef public
open import CaTTExp.Gray.Biclosed.Rows public

------------------------------------------------------------------------
-- Cell-type helpers

dim : CTy → Nat
dim (op _)          = 0
dim (hom _ _ A _ _) = suc (dim A)

baseM : CTy → MTy
baseM (op M)          = M
baseM (hom _ _ A _ _) = baseM A

isHom : CTy → Bool
isHom (op _) = false
isHom _      = true

eqMaybeTy : Maybe CTy → CTy → Bool
eqMaybeTy nothing  _ = false
eqMaybeTy (just A) B = eqTy A B

-- the composite of operations
compOp : MTy → List MTy → Maybe MTy
compOp (ys ▸ z) ms = if eqFms ys (map out ms) then just (concatIns ms ▸ z) else nothing

mapM : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mapM f nothing  = nothing
mapM f (just x) = just (f x)

-- f is a higher cell, the arguments are operations
liftF : List Tm → List MTy → CTy → Maybe CTy
liftF gs ms (op M)          = mapM op (compOp M ms)
liftF gs ms (hom m g U s t) = liftF gs ms U >>= λ U′ →
  just (hom m (sumIns (take g ms)) U′ (comp s gs) (comp t gs))

-- f is an operation of type Mf, argument j is a higher cell
liftG : Tm → List Tm → Nat → MTy → List MTy → CTy → Maybe CTy
liftG f gs j Mf ms (op M)          = mapM op (compOp Mf (setAt j M ms))
liftG f gs j Mf ms (hom m g U s t) = liftG f gs j Mf ms U >>= λ U′ →
  just (hom m (sumIns (take j ms) + g) U′ (comp f (setAt j s gs)) (comp f (setAt j t gs)))

-- index of the unique higher cell in a list (nothing if none or several)
countHom : List CTy → Nat
countHom []       = 0
countHom (A ∷ As) = (if isHom A then 1 else 0) + countHom As

firstHom : Nat → List CTy → Maybe (Σ Nat (λ _ → CTy))
firstHom _ []       = nothing
firstHom i (A ∷ As) = if isHom A then just (i , A) else firstHom (suc i) As

compTy : Tm → List Tm → CTy → List CTy → Maybe CTy
compTy f gs (op Mf) tgs with countHom tgs ==ℕ 0 | countHom tgs ==ℕ 1 | firstHom 0 tgs
... | true  | _    | _              = mapM op (compOp Mf (map baseM tgs))
... | false | true | just (j , tj) = liftG f gs j Mf (map baseM tgs) tj
... | _     | _    | _              = nothing
compTy f gs tf@(hom _ _ _ _ _) tgs =
  if countHom tgs ==ℕ 0 then liftF gs (map baseM tgs) tf else nothing

-- adjoin collars a⁻ : pm ≅ qm and a⁺ : pp ≅ qp (both of type Tc) to x
glueTy : Tm → Tm → CTy → Tm → Tm → Tm → Tm → CTy → Maybe CTy
glueTy am ap Tc qm qp pm pp (op _) = nothing
glueTy am ap Tc qm qp pm pp (hom m g U s t) =
  if eqTy U Tc ∧ eqTm s qm ∧ eqTm t qp
  then just (hom m g Tc pm pp)
  else (glueTy am ap Tc qm qp pm pp U >>= λ U′ →
        just (hom m g U′ (glue am s ap) (glue am t ap)))

glueTop : Tm → Tm → CTy → CTy → CTy → Maybe CTy
glueTop am ap (hom inv g Tc pm qm) (hom inv g′ Tc′ pp qp) tx =
  if (g ==ℕ g′) ∧ eqTy Tc Tc′ then glueTy am ap Tc qm qp pm pp tx else nothing
glueTop _ _ _ _ _ = nothing

------------------------------------------------------------------------
-- Inference

mutual
  infer : Ctx → Tm → Maybe CTy
  infer Γ (var i)   = lookup Γ i
  infer Γ (mP U V)  = just (op ((U ∷ V ∷ []) ▸ (U ⊗ V)))
  infer Γ (eL A C)  = just (op ((A ∷ (A \\ C) ∷ []) ▸ C))
  infer Γ (eR A C)  = just (op (((C // A) ∷ A ∷ []) ▸ C))
  infer Γ (pP Δ Θ)  = just (op ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)))
  infer Γ pt        = just (op ([] ▸ rep (disk 0)))
  infer Γ (iP Θ)    = just (op ((rep Θ ∷ []) ▸ shp Θ))
  infer Γ (idt A)   = just (op ((A ∷ []) ▸ A))
  infer Γ (comp f gs) with infer Γ f | inferL Γ gs
  ... | just tf | just tgs = compTy f gs tf tgs
  ... | _       | _        = nothing
  infer Γ (glue am x ap) with infer Γ am | infer Γ ap | infer Γ x
  ... | just ta | just tb | just tx = glueTop am ap ta tb tx
  ... | _       | _       | _       = nothing
  infer Γ (here t e φs ts) =
    if okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t)
         ∧ argsOk Γ (instS φs ts) ts (ctx t)
    then just (sY (instS φs ts) (goal t e)) else nothing

  -- the instance's terms have the substituted types of the template
  -- context, entry by entry
  argsOk : Ctx → Sub → List Tm → Ctx → Bool
  argsOk Γ σ []       []       = true
  argsOk Γ σ (x ∷ xs) (A ∷ As) = eqMaybeTy (infer Γ x) (sY σ A) ∧ argsOk Γ σ xs As
  argsOk Γ σ _        _        = false

  inferL : Ctx → List Tm → Maybe (List CTy)
  inferL Γ []       = just []
  inferL Γ (t ∷ ts) with infer Γ t | inferL Γ ts
  ... | just A | just As = just (A ∷ As)
  ... | _      | _       = nothing

  wf : Ctx → CTy → Bool
  wf Γ (op _)          = true
  wf Γ (hom _ _ A s t) = wf Γ A ∧ eqMaybeTy (infer Γ s) A ∧ eqMaybeTy (infer Γ t) A

-- each entry is well formed in the context of the entries before it
wfCtxFrom : Ctx → Ctx → Bool
wfCtxFrom acc []       = true
wfCtxFrom acc (A ∷ As) = wf acc A ∧ wfCtxFrom (acc ++ (A ∷ [])) As

wfCtx : Ctx → Bool
wfCtx = wfCtxFrom []

-- a goal is well typed: context and goal type are well formed
wtGoal : Ctx → CTy → Bool
wtGoal Γ A = wfCtx Γ ∧ wf Γ A
