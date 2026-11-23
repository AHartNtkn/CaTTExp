------------------------------------------------------------------------
-- The mark judgment of CaTTExp.Gray.MarksB satisfies the binder
-- kernel's hypotheses MarkRen and MarkSub (CaTTExp.Binder.Rename,
-- CaTTExp.Binder.Subst), so renaming and substitution of the kernel
-- `MarksB.Kernel` (two-tier L with binding formers and these marks)
-- hold.
--
-- MarkSub: a well-typed σ sends each marked variable to a term with
-- its marks (the ,-wf premise), so σ respects the marks with fuel
-- shift N = dimCtx Γ; the shifted theorem of Gray.MarksBSubst and
-- fuel stability then give the user-facing judgment of t[σ].
-- MarkRen: a renaming sends a variable to a variable with the same
-- marks, so the shift is 0.
--
-- Module parameters, beyond the interface: constants are closed and
-- the binder laws hold (as for Binder.Subst); formerMarks does not see
-- a substitution of the telescope (FormerStable); the mark-free
-- kernel has presupposition (tm-ty) and DimOK.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Syntax as NSyn
open import CaTTExp.Binder.Embed
open import CaTTExp.Binder.Signature using (Signature)
import CaTTExp.Binder.Forget
import CaTTExp.Binder.Laws
import CaTTExp.Binder.Scoping
import CaTTExp.Binder.Rename
import CaTTExp.Binder.Subst
import CaTTExp.Gray.Marks
import CaTTExp.Gray.MarksBSubst

module CaTTExp.Gray.MarksBKernel
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
open import CaTTExp.Gray.MarksB 𝕊₀ bi cellArg formerMarks
open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArg using (graySideD)
open CaTTExp.Binder.Laws 𝕊 using (Closed; BinderLaws)
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s; ≤-trans)
module MS = CaTTExp.Gray.MarksBSubst 𝕊₀ bi cellArg formerMarks
open MS using (Resp; SubD; FormerStable; typeOf-sound; dim-[]; isAt-[])
module Fg = MS.Fg
module F = Fg.F
module R = Kernel
private
  module FR = CaTTExp.Binder.Rename 𝕊 graySideD Fg.noMark
  module RR = CaTTExp.Binder.Rename 𝕊 graySideD mark
  module RS = CaTTExp.Binder.Subst 𝕊 graySideD mark

------------------------------------------------------------------------
-- Lists of marks and numbers.

private
  T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
  T∧ {true} p = tt , p

  ∨-l : ∀ {a b} → T a → T (a ∨ b)
  ∨-l {true} _ = tt

  ∨-r : ∀ {a b} → T b → T (a ∨ b)
  ∨-r {true}  _ = tt
  ∨-r {false} p = p

  ∨-case : ∀ {a b} {C : Set} → T (a ∨ b) → (T a → C) → (T b → C) → C
  ∨-case {true}  p f g = f tt
  ∨-case {false} p f g = g p

  -- A property of all of ms holds of each member.
  all-∈ : ∀ (p : Mark → Bool) ms m → T (all p ms) → T (m ∈M ms) → T (p m)
  all-∈ p (n ∷ ns) m q r with m ==M n in e
  ... | true  rewrite ==M-sound m n (subst T (sym e) tt) = fst (T∧ {p n} q)
  ... | false = all-∈ p ns m (snd (T∧ {p n} q)) r

  -- A marked entry exists.
  marks-lookup : ∀ Γ x m → T (m ∈M marksAt Γ x) → Σ Ty λ A → lookup Γ x ≡ just A
  marks-lookup (Γ ▸[ ms ] B) x m p with x ==ℕ len Γ
  ... | true  = B , refl
  ... | false = marks-lookup Γ x m p

  lookup-dim : ∀ Γ x {A} → lookup Γ x ≡ just A → dim A ≤ dimCtx Γ
  lookup-dim (Γ ▸[ ms ] B) x eq with x ==ℕ len Γ
  lookup-dim (Γ ▸[ ms ] B) x refl | true = max-≥l (dim B) (dimCtx Γ)
    where
    max-≥l : ∀ a b → a ≤ max a b
    max-≥l zero    b       = z≤n
    max-≥l (suc a) zero    = ≤-refl′ (suc a)
      where ≤-refl′ : ∀ n → n ≤ n
            ≤-refl′ zero    = z≤n
            ≤-refl′ (suc n) = s≤s (≤-refl′ n)
    max-≥l (suc a) (suc b) = s≤s (max-≥l a b)
  ... | false = ≤-trans (lookup-dim Γ x eq) (max-≥r (dim B) (dimCtx Γ))
    where
    max-≥r : ∀ a b → b ≤ max a b
    max-≥r zero    b       = ≤-refl′ b
      where ≤-refl′ : ∀ n → n ≤ n
            ≤-refl′ zero    = z≤n
            ≤-refl′ (suc n) = s≤s (≤-refl′ n)
    max-≥r (suc a) zero    = z≤n
    max-≥r (suc a) (suc b) = s≤s (max-≥r a b)

  -- k + N as dim A plus something, when dim A ≤ N.
  split : ∀ a N k → a ≤ N → Σ Nat λ j → k + N ≡ a + j
  split zero    N       k _       = k + N , refl
  split (suc a) (suc N) k (s≤s l) with split a N k l
  ... | j , e = j , trans (+-suc k N) (cong suc e)
    where
    +-suc : ∀ a b → a + suc b ≡ suc (a + b)
    +-suc zero    b = refl
    +-suc (suc a) b = cong suc (+-suc a b)

  -- A grpd mark at k′ ≤ h is one at h.
  lt-trans : ∀ j k h → T (j <ℕ suc k) → T (k <ℕ suc h) → T (j <ℕ suc h)
  lt-trans zero    k       h       _ _ = tt
  lt-trans (suc j) (suc k) (suc h) p q = lt-trans j k h p q

  anyM-mono : ∀ tr k h ms → T (k <ℕ suc h) → T (anyM (atLe tr k) ms) → T (anyM (atLe tr h) ms)
  anyM-mono tr k h (n ∷ ms) l p with markAt tr n
  ... | nothing = anyM-mono tr k h ms l p
  ... | just j  =
    ∨-case {j <ℕ suc k} p (λ q → ∨-l (lt-trans j k h q l)) (λ q → ∨-r {j <ℕ suc h} (anyM-mono tr k h ms l q))

  isAt-mono : ∀ Γ tr k h c → T (k <ℕ suc h) → T (isAt Γ tr k c) → T (isAt Γ tr h c)
  isAt-mono Γ tr k h (var C)        l p = anyM-mono tr k h (marksAt Γ C) l p
  isAt-mono Γ tr k h (bnd b y Δ ts) l p = anyM-mono tr k h (formerMarks b y Δ) l p

  markAt-inv : ∀ tr n {j} → markAt tr n ≡ just j → n ≡ mk tr j
  markAt-inv false (mgrpd j)  refl = refl
  markAt-inv true  (mtrunc j) refl = refl

  anyM-witness : ∀ tr h ms → T (anyM (atLe tr h) ms) → Σ Nat λ k → T (mk tr k ∈M ms) × T (k <ℕ suc h)
  anyM-witness tr h (n ∷ ms) p with markAt tr n in e
  ... | nothing = let (k , m , l) = anyM-witness tr h ms p in k , ∨-r {mk tr k ==M n} m , l
  ... | just j  =
    ∨-case {j <ℕ suc h} p
      (λ q → j , subst (λ X → T (mk tr j ∈M (X ∷ ms))) (sym (markAt-inv tr n e)) (∨-l (==M-refl (mk tr j))) , q)
      (λ q → let (k , m , l) = anyM-witness tr h ms q in k , ∨-r {mk tr k ==M n} m , l)

  mark-mk : ∀ Δ tr k c → mark Δ (mk tr k) c ≡ isAt Δ tr k c
  mark-mk Δ false k c = refl
  mark-mk Δ true  k c = refl

------------------------------------------------------------------------
-- The context of a derivable term.

private
  mutual
    ctx-of : ∀ {Γ t A} → Γ F.⊢tm t ∶ A → Γ F.⊢ctx
    ctx-of (F.var-wf w _)         = w
    ctx-of (F.coh-wf _ _ _ _ s)   = sub-ctx s
    ctx-of (F.cst-wf w _)         = w
    ctx-of (F.bnd-wf _ _ _ _ as)  = args-ctx as

    sub-ctx : ∀ {Γ σ Δ} → Γ F.⊢sub σ ∶ Δ → Γ F.⊢ctx
    sub-ctx (F.⟨⟩-wf w)    = w
    sub-ctx (F.,-wf s _ _) = sub-ctx s

    args-ctx : ∀ {Γ ts Θ} → Γ F.⊢args ts ∶ Θ → Γ F.⊢ctx
    args-ctx (F.⟨⟩-a w)    = w
    args-ctx (F.,-a a _ _) = args-ctx a

  R-sub-len : ∀ {Δ σ Γ} → Δ R.⊢sub σ ∶ Γ → lenₛ σ ≡ len Γ
  R-sub-len (R.⟨⟩-wf _)    = refl
  R-sub-len (R.,-wf s _ _) = cong suc (R-sub-len s)

  -- A substitution sends a variable to a term with its marks.
  sub-marks : ∀ {Δ σ Γ i A} → Δ R.⊢sub σ ∶ Γ → lookup Γ i ≡ just A →
              T (R.marksOK Δ (marksAt Γ i) (lookupₛ σ i))
  sub-marks {Γ = Γ ▸[ ms ] B} {i} (R.,-wf {σ} s _ o) eq with i ==ℕ len Γ in e
  ... | true  rewrite trans (RR.==-transport i (R-sub-len s)) e = o
  ... | false rewrite trans (RR.==-transport i (R-sub-len s)) e = sub-marks s eq

------------------------------------------------------------------------
-- The theorems.

module _ (closed : Closed) (laws : BinderLaws) (fstab : FormerStable)
         (tm-ty : ∀ {Γ t A} → Γ F.⊢tm t ∶ A → Γ F.⊢ty A)
         (dimOK : MS.Theorem.DimOK closed laws fstab tm-ty) where

  private
    module Th = MS.Theorem closed laws fstab tm-ty
    module St = Th.Stable dimOK

    tm[]F : ∀ {Γ Δ t A σ} → Γ F.⊢tm t ∶ A → Δ F.⊢sub σ ∶ Γ → Δ F.⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[]F = Fg.FS.tm[] closed laws (λ _ _ _ → tt) (λ _ _ _ → tt) Fg.markVarF

    tm-renF : ∀ {Γ Γ′ t A ρ} → Γ F.⊢tm t ∶ A → Γ′ FR.⊢ren ρ ∶ Γ → Γ′ F.⊢tm t [ ρ ]tm ∶ A [ ρ ]ty
    tm-renF = FR.tm-ren closed laws (λ _ _ _ → tt)

    -- From the shifted theorem to the user-facing judgment.
    lift : ∀ {N Γ Δ t A σ} (f : IP → Bool) →
           Γ F.⊢tm t ∶ A → SubD Γ Δ σ → Resp N Γ Δ σ → Δ F.⊢tm t [ σ ]tm ∶ A [ σ ]ty →
           (∀ {x y} → MS.IP≤ x y → T (f x) → T (f y)) →
           T (f (judgeT Γ t)) → T (f (judgeT Δ (t [ σ ]tm)))
    lift {N} {Γ} {Δ} {t} {A} {σ} f d D r dσ pick p =
      subst (λ j → T (f j)) (sym (St.judgeT≡ dσ))
        (subst (λ j → T (f j)) (St.fuel-stable N dσ)
          (subst (λ n → T (f (judge (n + N) Δ (t [ σ ]tm)))) (sym (dim-[] A σ))
            (pick (Th.judge-[] (dim A) d D r) (subst (λ j → T (f j)) (St.judgeT≡ d) p))))

  ----------------------------------------------------------------------
  -- Substitution.

  module _ {Γ Δ σ} (sd : Δ R.⊢sub σ ∶ Γ) (w : Γ F.⊢ctx) where
    private
      sdF = Fg.forget-sub mark sd
      D   = Th.subD sdF
      N   = dimCtx Γ

      image : ∀ x A → lookup Γ x ≡ just A → Δ F.⊢tm lookupₛ σ x ∶ A [ σ ]ty
      image x A eq = MS.look D w eq

      -- An image at fuel k + N has the judgment it has at its dimension.
      at-fuel : ∀ k x A → lookup Γ x ≡ just A →
                judge (k + N) Δ (lookupₛ σ x) ≡ judgeT Δ (lookupₛ σ x)
      at-fuel k x A eq with split (dim (A [ σ ]ty)) N k
                                  (subst (_≤ N) (sym (dim-[] A σ)) (lookup-dim Γ x eq))
      ... | j , e = trans (cong (λ n → judge n Δ (lookupₛ σ x)) e)
                     (trans (St.fuel-stable j (image x A eq)) (sym (St.judgeT≡ (image x A eq))))

      has : ∀ x A m → lookup Γ x ≡ just A → T (m ∈M marksAt Γ x) → T (mark Δ m (lookupₛ σ x))
      has x A m eq mm = all-∈ (λ n → mark Δ n (lookupₛ σ x)) (marksAt Γ x) m (sub-marks sd eq) mm

    resp : Resp N Γ Δ σ
    resp = record
      { r-inv  = λ k x mm → let (A , eq) = marks-lookup Γ x minv mm in
                   subst (λ j → T (jinv j)) (sym (at-fuel k x A eq)) (has x A minv eq mm)
      ; r-ps   = λ k x mm → let (A , eq) = marks-lookup Γ x mps mm in
                   subst (λ j → T (jps j)) (sym (at-fuel k x A eq)) (has x A mps eq mm)
      ; r-at   = λ tr h x ma → let (k , mk′ , l) = anyM-witness tr h (marksAt Γ x) ma
                                   (A , eq)      = marks-lookup Γ x (mk tr k) mk′ in
                   isAt-mono Δ tr k h (lookupₛ σ x) l
                     (subst T (mark-mk Δ tr k (lookupₛ σ x)) (has x A (mk tr k) eq mk′))
      }

  markSub : RS.MarkSub
  markSub {Γ} {Δ} {σ} {t} {A} {minv} sd d p =
    lift jinv dF (Th.subD (Fg.forget-sub mark sd)) (resp sd (ctx-of dF)) (tm[]F dF (Fg.forget-sub mark sd))
         (λ q → fst q) p
    where dF = Fg.forget-tm mark d
  markSub {Γ} {Δ} {σ} {t} {A} {mps} sd d p =
    lift jps dF (Th.subD (Fg.forget-sub mark sd)) (resp sd (ctx-of dF)) (tm[]F dF (Fg.forget-sub mark sd))
         (λ q → fst (snd q)) p
    where dF = Fg.forget-tm mark d
  markSub {Γ} {Δ} {σ} {t} {A} {mgrpd k} sd d p =
    isAt-[] fstab (resp sd (ctx-of (Fg.forget-tm mark d))) false k t p
  markSub {Γ} {Δ} {σ} {t} {A} {mtrunc k} sd d p =
    isAt-[] fstab (resp sd (ctx-of (Fg.forget-tm mark d))) true k t p

  ----------------------------------------------------------------------
  -- Renaming.

  module _ {Γ Γ′ ρ} (r : Γ′ RR.⊢ren ρ ∶ Γ) where
    private
      open RR._⊢ren_∶_ r
      w′ = Fg.forget-ctx mark ctx

      rF : Γ′ FR.⊢ren ρ ∶ Γ
      rF = FR.mkRen w′ leq lc sc look

      D : SubD Γ Γ′ ρ
      D = record
        { look = λ {i} {A} _ eq → let (j , ej , lj , _) = look i eq in
                   subst (λ X → Γ′ F.⊢tm X ∶ A [ ρ ]ty) (sym ej) (F.var-wf w′ lj)
        ; lc   = lc }

      -- A variable goes to a variable with its marks.
      same : ∀ x m → T (m ∈M marksAt Γ x) →
             Σ Nat λ j → (lookupₛ ρ x ≡ var j) × T (m ∈M marksAt Γ′ j)
      same x m mm = let (A , eq) = marks-lookup Γ x m mm
                        (j , ej , _ , mj) = look x eq in
                    j , ej , subst (λ ms → T (m ∈M ms)) (sym mj) mm

    respR : Resp 0 Γ Γ′ ρ
    respR = record
      { r-inv  = λ k x mm → let (j , ej , mj) = same x minv mm in
                   subst (λ X → T (jinv (judge (k + 0) Γ′ X))) (sym ej) (∨-l mj)
      ; r-ps   = λ k x mm → let (j , ej , mj) = same x mps mm in
                   subst (λ X → T (jps (judge (k + 0) Γ′ X))) (sym ej) (∨-l mj)
      ; r-at   = λ tr h x ma → let (k , mk′ , l) = anyM-witness tr h (marksAt Γ x) ma
                                   (j , ej , mj)  = same x (mk tr k) mk′ in
                   subst (λ X → T (isAt Γ′ tr h X)) (sym ej)
                     (isAt-mono Γ′ tr k h (var j) l (at-self tr k (marksAt Γ′ j) (mk tr k) (markAt-mk tr k) mj))
      }

    ren-rF : Γ′ FR.⊢ren ρ ∶ Γ
    ren-rF = rF

    ren-D : SubD Γ Γ′ ρ
    ren-D = D

  markRen : RR.MarkRen
  markRen {Γ} {Γ′} {ρ} {t} {A} {minv} r d p =
    lift jinv dF (ren-D r) (respR r) (tm-renF dF (ren-rF r)) (λ q → fst q) p
    where dF = Fg.forget-tm mark d
  markRen {Γ} {Γ′} {ρ} {t} {A} {mps} r d p =
    lift jps dF (ren-D r) (respR r) (tm-renF dF (ren-rF r)) (λ q → fst (snd q)) p
    where dF = Fg.forget-tm mark d
  markRen {Γ} {Γ′} {ρ} {t} {A} {mgrpd k}  r d p = isAt-[] fstab (respR r) false k t p
  markRen {Γ} {Γ′} {ρ} {t} {A} {mtrunc k} r d p = isAt-[] fstab (respR r) true k t p
