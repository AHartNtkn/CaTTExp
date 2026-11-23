------------------------------------------------------------------------
-- Substitution preserves the mark judgments of CaTTExp.Gray.MarksB
-- (binder syntax, with destructors and per-former marks), with a fuel
-- shift: the binder-syntax counterpart of CaTTExp.Gray.MarksSubst.
--
--   Γ ⊢ t ∶ A,  Δ ⊢ σ ∶ Γ,  σ respects the marks (Resp N)
--     ⇒  judge k Γ t ≤ judge (k + N) Δ (t[σ])      (inv, ps, ps*)
--
-- The derivations are those of the mark-free instance
-- (CaTTExp.Binder.Forget): the judgment never reads a mark premise, and
-- there substitution needs no mark hypotheses. A marked derivation is
-- forgotten into one first.
--
-- New against MarksSubst:
--   * a former occurrence keeps its marks under substitution when
--     formerMarks does not see the substitution (`FormerStable`: true
--     for DES, constant marks, and for INIT, whose marks are read off
--     the telescope's entries, which substitution keeps);
--   * (OBJ-k) reads the 0-target's grpd marks from a variable or a
--     former occurrence (`isGrpd`), so Resp asks a grpd-marked variable
--     to go to a term that carries the mark (a variable or μ_k);
--   * the type of a derivable term is derivable (`tm-ty`) is a module
--     parameter until the kernel provides it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Syntax as NSyn
open import CaTTExp.Binder.Embed
open import CaTTExp.Binder.Signature using (Signature)
import CaTTExp.Binder.Forget
import CaTTExp.Binder.Laws
import CaTTExp.Binder.Scoping
import CaTTExp.Binder.SyntaxLemmas
import CaTTExp.Gray.Marks
import CaTTExp.Gray.MarksSubst

module CaTTExp.Gray.MarksBSubst
  (𝕊₀ : Old.Signature)
  (bi : Binders (Old.Signature.K 𝕊₀))
  (cellArg : Binders.B bi → Maybe Nat)
  (formerMarks : Binders.B bi → Nat → NSyn.Ctx (Old.Signature.K 𝕊₀) (Binders.B bi) → List NSyn.Mark)
  where

private
  𝕊 : Signature
  𝕊 = extend 𝕊₀ bi

open Signature 𝕊
open CaTTExp.Gray.Marks 𝕊₀ using (IP; ip; jinv; jps; jpss)
open CaTTExp.Gray.MarksSubst 𝕊₀ public using (_⇒B_; IP≤; Pw; []; _∷_)
open CaTTExp.Gray.MarksSubst 𝕊₀ using (invC-mono; psC-mono)
open import CaTTExp.Gray.MarksB 𝕊₀ bi cellArg formerMarks
open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArg using (graySideD; dCtx; dTy; dTm)
open CaTTExp.Binder.SyntaxLemmas K B using (assoc-ty; closed-ty; op-[]ty; LC)
open CaTTExp.Binder.Laws 𝕊 using (Closed; BinderLaws)
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s; ≤-trans)

module Fg = CaTTExp.Binder.Forget 𝕊 graySideD
open Fg.F
private
  module Sc = CaTTExp.Binder.Scoping 𝕊 graySideD Fg.noMark

------------------------------------------------------------------------
-- Booleans.

private
  ∨-mono : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∨ b) ⇒B (c ∨ d)
  ∨-mono {true}  {c = true}  f g p = tt
  ∨-mono {true}  {c = false} f g p = ⊥-elim (f tt)
  ∨-mono {false} {c = true}  f g p = tt
  ∨-mono {false} {c = false} f g p = g p

  ∧-mono : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∧ b) ⇒B (c ∧ d)
  ∧-mono {true} {c = true}  f g p = g p
  ∧-mono {true} {c = false} f g p = ⊥-elim (f tt)
  ∧-mono {false} f g ()

  ∨-r : ∀ {a b} → T b → T (a ∨ b)
  ∨-r {true}  _ = tt
  ∨-r {false} p = p

  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  ∨-case : ∀ {a b} {C : Set} → T (a ∨ b) → (T a → C) → (T b → C) → C
  ∨-case {true}  p f g = f tt
  ∨-case {false} p f g = g p

  pw-++ : ∀ {xs ys xs' ys'} → Pw IP≤ xs ys → Pw IP≤ xs' ys' → Pw IP≤ (xs ++ xs') (ys ++ ys')
  pw-++ []       q = q
  pw-++ (r ∷ p) q = r ∷ pw-++ p q

------------------------------------------------------------------------
-- Syntax under substitution.

dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[] ⋆           σ = refl
dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

endsTy-[] : ∀ A σ {s t} → endsTy A ≡ just (s , t) → endsTy (A [ σ ]ty) ≡ just (s [ σ ]tm , t [ σ ]tm)
endsTy-[] ⋆                       σ ()
endsTy-[] (arr ⋆ a b)             σ refl = refl
endsTy-[] (arr (arr A s' t') _ _) σ eq   = endsTy-[] (arr A s' t') σ eq

typeOf-sound : ∀ {Γ t A} → Γ ⊢tm t ∶ A → typeOf Γ t ≡ just A
typeOf-sound (var-wf _ eq) = eq
typeOf-sound (coh-wf _ _ _ _ _) = refl
typeOf-sound (cst-wf _ _) = refl
typeOf-sound (bnd-wf _ _ _ _ _) = refl

-- The coh rules are monotone in the judgments of the substitution.
cohInv-mono : ∀ Θ A t u {cs cs'} → Pw IP≤ cs cs' → fst (cohRules Θ A t u cs) ⇒B fst (cohRules Θ A t u cs')
cohInv-mono Θ A t u p with dCtx Θ | dTy A | dTm t | dTm u
... | just Θ₀  | just A₀  | just t₀  | just u₀  = invC-mono Θ₀ A₀ t₀ u₀ p
... | nothing  | _        | _        | _        = λ ()
... | just _   | nothing  | _        | _        = λ ()
... | just _   | just _   | nothing  | _        = λ ()
... | just _   | just _   | just _   | nothing  = λ ()

cohPs-mono : ∀ Θ A t u {cs cs'} → Pw IP≤ cs cs' → snd (cohRules Θ A t u cs) ⇒B snd (cohRules Θ A t u cs')
cohPs-mono Θ A t u p with dCtx Θ | dTy A | dTm t | dTm u
... | just Θ₀  | just A₀  | just t₀  | just u₀  = psC-mono Θ₀ A₀ t₀ u₀ p
... | nothing  | _        | _        | _        = λ ()
... | just _   | nothing  | _        | _        = λ ()
... | just _   | just _   | nothing  | _        = λ ()
... | just _   | just _   | just _   | nothing  = λ ()

-- OBJ-k and INV⇒PS are built into `judge` for every term.
inv-obj : ∀ n Γ t → objRule Γ (typeOf Γ t) ⇒B jinv (judge n Γ t)
inv-obj n Γ (var x)               p = ∨-r p
inv-obj n Γ (bvar _ _)            ()
inv-obj n Γ (cst k)               p = p
inv-obj n Γ (coh Θ ⋆ γ)           ()
inv-obj n Γ (coh Θ (arr A t u) γ) p = ∨-r p
inv-obj n Γ (bnd b y Δ ts)        p = ∨-r p

ps-inv : ∀ n Γ t → (jinv (judge n Γ t) ∧ hdAtLeast 1 (typeOf Γ t)) ⇒B jps (judge n Γ t)
ps-inv n Γ (var x)               p = ∨-r p
ps-inv n Γ (bvar _ _)            ()
ps-inv n Γ (cst k)               p = p
ps-inv n Γ (coh Θ ⋆ γ)           ()
ps-inv n Γ (coh Θ (arr A t u) γ) p = ∨-r p
ps-inv n Γ (bnd b y Δ ts)        p = ∨-r p

-- The ps* component of every judgment is (PS*) applied to its ps one.
judge-star : ∀ n Γ t → jpss (judge n Γ t) ≡ star n Γ (typeOf Γ t) (jps (judge n Γ t))
judge-star n Γ (var x)               = refl
judge-star n Γ (bvar _ _)            = refl
judge-star n Γ (cst k)               = refl
judge-star n Γ (coh Θ ⋆ γ)           = refl
judge-star n Γ (coh Θ (arr A t u) γ) = refl
judge-star n Γ (bnd b y Δ ts)        = refl

------------------------------------------------------------------------
-- Marked substitutions.

-- formerMarks does not see a substitution of the telescope.
FormerStable : Set
FormerStable = ∀ b y Δ σ → formerMarks b y (Δ [ σ ]tel) ≡ formerMarks b y Δ

record Resp (N : Nat) (Γ Δ : Ctx) (σ : Sub) : Set where
  field
    r-inv  : ∀ k x → T (minv ∈M marksAt Γ x) → T (jinv (judge (k + N) Δ (lookupₛ σ x)))
    r-ps   : ∀ k x → T (mps ∈M marksAt Γ x)  → T (jps  (judge (k + N) Δ (lookupₛ σ x)))
    r-grpd : ∀ h x → T (anyM (grpdLe h) (marksAt Γ x)) → T (isGrpd Δ h (lookupₛ σ x))
open Resp public

module _ (fstab : FormerStable) {N Γ Δ σ} (r : Resp N Γ Δ σ) where

  isGrpd-[] : ∀ h c → isGrpd Γ h c ⇒B isGrpd Δ h (c [ σ ]tm)
  isGrpd-[] h (var C)        p = r-grpd r h C p
  isGrpd-[] h (bnd b y Θ ts) p rewrite fstab b y Θ σ = p
  isGrpd-[] h (bvar _ _)     ()
  isGrpd-[] h (coh _ _ _)    ()
  isGrpd-[] h (cst _)        ()

  objAt-[] : ∀ n A → objAt Γ n (endsTy A) ⇒B objAt Δ n (endsTy (A [ σ ]ty))
  objAt-[] n A p with endsTy A in eq
  ... | just (s , c) rewrite endsTy-[] A σ eq =
    ∧-intro {isGrpd Δ (n ∸ 1) (c [ σ ]tm)} (isGrpd-[] (n ∸ 1) c (∧-fst {isGrpd Γ (n ∸ 1) c} p))
            (∧-snd {isGrpd Γ (n ∸ 1) c} p)

  objRule-[] : ∀ A → objRule Γ (just A) ⇒B objRule Δ (just (A [ σ ]ty))
  objRule-[] A p rewrite dim-[] A σ = objAt-[] (dim A) A p

private
  hd-[] : ∀ A σ → hdAtLeast 1 (just A) ⇒B hdAtLeast 1 (just (A [ σ ]ty))
  hd-[] A σ p rewrite dim-[] A σ = p

------------------------------------------------------------------------
-- What the theorem uses of σ: its variables' images are derivable at
-- the substituted types, and it is locally closed. A substitution
-- (`subD`) and a renaming (CaTTExp.Gray.MarksBKernel) both give this.

record SubD (Γ Δ : Ctx) (σ : Sub) : Set where
  field
    look : ∀ {i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Δ ⊢tm lookupₛ σ i ∶ A [ σ ]ty
    lc   : LC σ
open SubD public

------------------------------------------------------------------------
-- The theorem.

module Theorem (closed : Closed) (laws : BinderLaws) (fstab : FormerStable)
               (tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A) where

  open BinderLaws laws

  private
    lookup-sub : ∀ {Γ Δ σ i A} → Γ ⊢ctx → lookup Γ i ≡ just A →
                 Δ ⊢sub σ ∶ Γ → Δ ⊢tm lookupₛ σ i ∶ A [ σ ]ty
    lookup-sub = Fg.FS.lookup-sub closed laws (λ _ _ _ → tt) (λ _ _ _ → tt) Fg.markVarF

  subD : ∀ {Γ Δ σ} → Δ ⊢sub σ ∶ Γ → SubD Γ Δ σ
  subD sd = record { look = λ w eq → lookup-sub w eq sd ; lc = Sc.sub-lc sd }

  private
    scTyAt : ∀ {m n} A → m ≡ n → T (scTy? m A) → T (scTy? n A)
    scTyAt A refl p = p

  mutual
    judge-[] : ∀ {N Γ Δ t A σ} k → Γ ⊢tm t ∶ A → SubD Γ Δ σ → Resp N Γ Δ σ →
               IP≤ (judge k Γ t) (judge (k + N) Δ (t [ σ ]tm))
    judge-[] {N} {Γ} {Δ} {var x} {A} {σ} k d@(var-wf w eq) sd r =
      inv-part , ps-part , pss-part
      where
      s-wf : Δ ⊢tm lookupₛ σ x ∶ A [ σ ]ty
      s-wf = look sd w eq
      ty-s : typeOf Δ (lookupₛ σ x) ≡ just (A [ σ ]ty)
      ty-s = typeOf-sound s-wf
      obj : objRule Γ (lookup Γ x) ⇒B jinv (judge (k + N) Δ (lookupₛ σ x))
      obj p = inv-obj (k + N) Δ (lookupₛ σ x)
                (subst (λ m → T (objRule Δ m)) (sym ty-s)
                  (objRule-[] fstab r A (subst (λ m → T (objRule Γ m)) eq p)))
      inv-part : jinv (judge k Γ (var x)) ⇒B jinv (judge (k + N) Δ (lookupₛ σ x))
      inv-part p = ∨-case {minv ∈M marksAt Γ x} p (r-inv r k x) obj
      ps-part : jps (judge k Γ (var x)) ⇒B jps (judge (k + N) Δ (lookupₛ σ x))
      ps-part p = ∨-case {mps ∈M marksAt Γ x} p (r-ps r k x) λ q →
        ps-inv (k + N) Δ (lookupₛ σ x)
          (∧-intro (inv-part (∧-fst q))
            (subst (λ m → T (hdAtLeast 1 m)) (sym ty-s)
              (hd-[] A σ (subst (λ m → T (hdAtLeast 1 m)) eq
                (∧-snd {(minv ∈M marksAt Γ x) ∨ objRule Γ (lookup Γ x)} q)))))
      pss-part : jpss (judge k Γ (var x)) ⇒B jpss (judge (k + N) Δ (lookupₛ σ x))
      pss-part q =
        subst T (sym (judge-star (k + N) Δ (lookupₛ σ x)))
          (subst (λ m → T (star (k + N) Δ m (jps (judge (k + N) Δ (lookupₛ σ x))))) (sym ty-s)
            (star-[] k (tm-ty d) sd r ps-part
              (subst (λ m → T (star k Γ m (jps (judge k Γ (var x))))) eq q)))
    judge-[] {N} {Γ} {Δ} {coh Θ (arr A t u) γ} {_} {σ} k d@(coh-wf p w a ok γd) sd r =
      inv-part , ps-part , pss-part
      where
      B′ : Ty
      B′ = arr A t u
      pw : Pw IP≤ (judgeSub k Γ γ) (judgeSub (k + N) Δ (γ ∘ σ))
      pw = judgeSub-[] k γd sd r
      e : B′ [ γ ]ty [ σ ]ty ≡ B′ [ γ ∘ σ ]ty
      e = assoc-ty B′ γ σ (scTyAt B′ (sym (snd (Sc.sub-sc closed laws γd))) (Sc.ty-sc closed laws a))
      obj : objRule Γ (just (B′ [ γ ]ty)) ⇒B objRule Δ (just (B′ [ γ ∘ σ ]ty))
      obj q = subst (λ X → T (objRule Δ (just X))) e (objRule-[] fstab r (B′ [ γ ]ty) q)
      inv-part : jinv (judge k Γ (coh Θ B′ γ)) ⇒B jinv (judge (k + N) Δ (coh Θ B′ (γ ∘ σ)))
      inv-part = ∨-mono (cohInv-mono Θ A t u pw) obj
      hdS : hdAtLeast 1 (just (B′ [ γ ]ty)) ⇒B hdAtLeast 1 (just (B′ [ γ ∘ σ ]ty))
      hdS q = subst (λ X → T (hdAtLeast 1 (just X))) e (hd-[] (B′ [ γ ]ty) σ q)
      ps-part : jps (judge k Γ (coh Θ B′ γ)) ⇒B jps (judge (k + N) Δ (coh Θ B′ (γ ∘ σ)))
      ps-part = ∨-mono (cohPs-mono Θ A t u pw) (∧-mono inv-part hdS)
      pss-part : jpss (judge k Γ (coh Θ B′ γ)) ⇒B jpss (judge (k + N) Δ (coh Θ B′ (γ ∘ σ)))
      pss-part q = subst (λ X → T (star (k + N) Δ (just X) (jps (judge (k + N) Δ (coh Θ B′ (γ ∘ σ)))))) e
                     (star-[] k (tm-ty d) sd r ps-part q)
    judge-[] {N} {Γ} {Δ} {cst c} {_} {σ} k d@(cst-wf w v) sd r =
      inv-part , ps-part , pss-part
      where
      A′ = ty c
      e : A′ [ σ ]ty ≡ A′
      e = closed-ty A′ σ (closed c)
      inv-part : objRule Γ (just A′) ⇒B objRule Δ (just A′)
      inv-part q = subst (λ X → T (objRule Δ (just X))) e (objRule-[] fstab r A′ q)
      ps-part : (objRule Γ (just A′) ∧ hdAtLeast 1 (just A′)) ⇒B (objRule Δ (just A′) ∧ hdAtLeast 1 (just A′))
      ps-part = ∧-mono inv-part (λ q → q)
      pss-part : jpss (judge k Γ (cst c)) ⇒B jpss (judge (k + N) Δ (cst c))
      pss-part q = subst (λ X → T (star (k + N) Δ (just X) (jps (judge (k + N) Δ (cst c))))) e
                     (star-[] k (tm-ty d) sd r ps-part q)
    judge-[] {N} {Γ} {Δ} {bnd b y Θ ts} {_} {σ} k d@(bnd-wf sc lcΘ w ok as) sd r
      rewrite fstab b y Θ σ = inv-part , ps-part , pss-part
      where
      ms = formerMarks b y Θ
      lσ = SubD.lc sd
      A′  = opTy 0 ts (bres b y Θ)
      A″ = opTy 0 (ts ∘ σ) (bres b y (Θ [ σ ]tel))
      e : A′ [ σ ]ty ≡ A″
      e = trans (op-[]ty 0 ts (bres b y Θ) σ lσ) (cong (opTy 0 (ts ∘ σ)) (sym (res-stable b y Θ σ lσ ok)))
      inv-part : ((minv ∈M ms) ∨ objRule Γ (just A′)) ⇒B ((minv ∈M ms) ∨ objRule Δ (just A″))
      inv-part = ∨-mono (λ q → q) (λ q → subst (λ X → T (objRule Δ (just X))) e (objRule-[] fstab r A′ q))
      hdS : hdAtLeast 1 (just A′) ⇒B hdAtLeast 1 (just A″)
      hdS q = subst (λ X → T (hdAtLeast 1 (just X))) e (hd-[] A′ σ q)
      ps-part : ((mps ∈M ms) ∨ (((minv ∈M ms) ∨ objRule Γ (just A′)) ∧ hdAtLeast 1 (just A′))) ⇒B
                ((mps ∈M ms) ∨ (((minv ∈M ms) ∨ objRule Δ (just A″)) ∧ hdAtLeast 1 (just A″)))
      ps-part = ∨-mono (λ q → q) (∧-mono inv-part hdS)
      pss-part : star k Γ (just A′) ((mps ∈M ms) ∨ (((minv ∈M ms) ∨ objRule Γ (just A′)) ∧ hdAtLeast 1 (just A′))) ⇒B
                 star (k + N) Δ (just A″) ((mps ∈M ms) ∨ (((minv ∈M ms) ∨ objRule Δ (just A″)) ∧ hdAtLeast 1 (just A″)))
      pss-part q = subst (λ X → T (star (k + N) Δ (just X) P″)) e (star-[] k (tm-ty d) sd r ps-part q)
        where P″ = (mps ∈M ms) ∨ (((minv ∈M ms) ∨ objRule Δ (just A″)) ∧ hdAtLeast 1 (just A″))

    judgeSub-[] : ∀ {N Γ Δ Θ γ σ} k → Γ ⊢sub γ ∶ Θ → SubD Γ Δ σ → Resp N Γ Δ σ →
                  Pw IP≤ (judgeSub k Γ γ) (judgeSub (k + N) Δ (γ ∘ σ))
    judgeSub-[] k (⟨⟩-wf _)      sd r = []
    judgeSub-[] k (,-wf γd td _) sd r = pw-++ (judgeSub-[] k γd sd r) (judge-[] k td sd r ∷ [])

    star-[] : ∀ {N Γ Δ A σ p p'} k → Γ ⊢ty A → SubD Γ Δ σ → Resp N Γ Δ σ →
              p ⇒B p' → star k Γ (just A) p ⇒B star (k + N) Δ (just (A [ σ ]ty)) p'
    star-[] {A = A} {σ} k a sd r pp rewrite dim-[] A σ =
      ∨-mono (λ q → q) (∧-mono pp (∨-mono (λ q → q) (bdStar-[] k a sd r)))

    bdStar-[] : ∀ {N Γ Δ A σ} k → Γ ⊢ty A → SubD Γ Δ σ → Resp N Γ Δ σ →
                bdStar k Γ A ⇒B bdStar (k + N) Δ (A [ σ ]ty)
    bdStar-[] zero    a              sd r ()
    bdStar-[] (suc k) (⋆-wf _)       sd r ()
    bdStar-[] (suc k) (arr-wf ds du) sd r =
      ∧-mono (snd (snd (judge-[] k ds sd r))) (snd (snd (judge-[] k du sd r)))

  ----------------------------------------------------------------------
  -- Stability above the dimension (CaTTExp.Gray.MarksFuel.Stable), given
  -- that a derivable coh is at least as high as its pasting context.

  DimOK : Set
  DimOK = ∀ {Θ A t u} → Θ ⊢ps → Θ ⊢ty arr A t u → T (graySideD Θ A t u) → dimCtx Θ ≤ suc (dim A)

  private
    max-l : ∀ a b {n} → max a b ≤ n → a ≤ n
    max-l zero    b       _       = z≤n
    max-l (suc a) zero    l       = l
    max-l (suc a) (suc b) (s≤s l) = s≤s (max-l a b l)

    max-r : ∀ a b {n} → max a b ≤ n → b ≤ n
    max-r zero    b       l       = l
    max-r (suc a) zero    _       = z≤n
    max-r (suc a) (suc b) (s≤s l) = s≤s (max-r a b l)

  module Stable (dimOK : DimOK) where

    mutual
      stab : ∀ {Γ t A} n → Γ ⊢tm t ∶ A → dim A ≤ n → judge n Γ t ≡ judge (suc n) Γ t
      stab {Γ} {var x} n d@(var-wf w eq) le =
        cong (ip (jinv (judge n Γ (var x))) (jps (judge n Γ (var x))))
             (subst (λ m → star n Γ m P ≡ star (suc n) Γ m P) (sym eq)
                    (star-stab n (tm-ty d) le P))
        where P = jps (judge n Γ (var x))
      stab {Γ} {cst k} n d@(cst-wf w v) le =
        cong (ip (jinv (judge n Γ (cst k))) (jps (judge n Γ (cst k))))
             (star-stab n (tm-ty d) le (jps (judge n Γ (cst k))))
      stab {Γ} {coh Δ (arr B t u) γ} n d@(coh-wf psΔ cw tyΔ ok sγ) le
        rewrite sub-stab n sγ (≤-trans (dimOK psΔ tyΔ ok) (subst (_≤ n) (dim-[] (arr B t u) γ) le)) =
        cong (ip (jinv (judge (suc n) Γ (coh Δ (arr B t u) γ))) (jps (judge (suc n) Γ (coh Δ (arr B t u) γ))))
             (star-stab n (tm-ty d) le (jps (judge (suc n) Γ (coh Δ (arr B t u) γ))))
      stab {Γ} {bnd b y Θ ts} n d@(bnd-wf _ _ _ _ _) le =
        cong (ip (jinv (judge n Γ (bnd b y Θ ts))) (jps (judge n Γ (bnd b y Θ ts))))
             (star-stab n (tm-ty d) le (jps (judge n Γ (bnd b y Θ ts))))

      sub-stab : ∀ {Γ γ Δ} n → Γ ⊢sub γ ∶ Δ → dimCtx Δ ≤ n → judgeSub n Γ γ ≡ judgeSub (suc n) Γ γ
      sub-stab n (⟨⟩-wf _) le = refl
      sub-stab n (,-wf {σ = γ} {A = C} sγ tw _) le =
        cong₂ _++_ (sub-stab n sγ (max-r (dim C) _ le))
                   (cong (_∷ []) (stab n tw (subst (_≤ n) (sym (dim-[] C γ)) (max-l (dim C) _ le))))

      star-stab : ∀ {Γ A} n → Γ ⊢ty A → dim A ≤ n → ∀ p → star n Γ (just A) p ≡ star (suc n) Γ (just A) p
      star-stab {A = A} n a le p = cong (λ b → (dim A ==ℕ 1) ∨ (p ∧ ((dim A ==ℕ 2) ∨ b))) (bd-stab n a le)

      bd-stab : ∀ {Γ A} n → Γ ⊢ty A → dim A ≤ n → bdStar n Γ A ≡ bdStar (suc n) Γ A
      bd-stab zero    (⋆-wf _) le = refl
      bd-stab (suc n) (⋆-wf _) le = refl
      bd-stab (suc n) (arr-wf ds du) (s≤s le) =
        cong₂ (λ a b → jpss a ∧ jpss b) (stab n ds le) (stab n du le)

    -- Any fuel at least dim A gives the same judgments.
    fuel-stable : ∀ {Γ t A} k → Γ ⊢tm t ∶ A → judge (dim A + k) Γ t ≡ judge (dim A) Γ t
    fuel-stable {Γ} {t} {A} zero d = cong (λ n → judge n Γ t) (+-zero (dim A))
      where
      +-zero : ∀ a → a + zero ≡ a
      +-zero zero    = refl
      +-zero (suc a) = cong suc (+-zero a)
    fuel-stable {Γ} {t} {A} (suc k) d =
      trans (cong (λ n → judge n Γ t) (+-suc (dim A) k))
            (trans (sym (stab (dim A + k) d (m≤m+n (dim A) k))) (fuel-stable k d))
      where
      +-suc : ∀ a b → a + suc b ≡ suc (a + b)
      +-suc zero    b = refl
      +-suc (suc a) b = cong suc (+-suc a b)
      m≤m+n : ∀ m n → m ≤ m + n
      m≤m+n zero    n = z≤n
      m≤m+n (suc m) n = s≤s (m≤m+n m n)

    judgeT≡ : ∀ {Γ t A} → Γ ⊢tm t ∶ A → judgeT Γ t ≡ judge (dim A) Γ t
    judgeT≡ {Γ} {t} d rewrite typeOf-sound d = refl
