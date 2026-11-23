------------------------------------------------------------------------
-- The whiskering interface of CaTTExp.Surface.TheoremB for any
-- CaTT-style theory over the empty signature whose side condition
-- accepts the whisker heads of CaTTExp.Derived (the hypotheses of
-- CaTTExp.DerivedWith).
--
-- This is CaTTExp.Surface.WhiskerPure with the side condition made a
-- parameter: wh Γ k p x q = (p ◃ₖ x) ▹ₖ q, `Wh-wf-pure` proves Wh-wf
-- for every surface equality E, and `Consistent` instantiates every
-- module parameter of TheoremB.Hyp/Thm at once (for the coarse E, where
-- Wh-≈ and Unit hold trivially; see WhiskerPure's header for what this
-- does and does not show).
--
-- Instances:
--  * plain CaTT: `CattInstance` at the bottom, from Derived's sideK
--    and sideLK; it recovers WhiskerPure.
--  * two-tier L: needs graySide's hypotheses for every k, j. They are
--    checked by evaluation for k + j ≤ 3
--    (CaTTExp.Surface.WhiskerGrayCheck); the general proof is open.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅; cattSide)
open import CaTTExp.Signature
open Signature ∅
import CaTTExp.Subst as SubstM
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.Derived using (nB; zK; BK; wK; LK; lK; ρsK; ρtK; λsK; λtK)

module CaTTExp.Surface.WhiskerWith
  (side : Ctx → Ty → Tm → Tm → Bool)
  (closedS : SubstM.Closed ∅ side)
  (side-BK0 : ∀ k → T (side (BK k 0) (aL k) (var (dbl k)) (var (zK k 0))))
  (side-BK  : ∀ k j → T (side (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                         (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j))))
  (side-LK  : ∀ k j → T (side (LK k (suc j)) (lK k j [ λsK k j ]ty)
                         (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j))))
  where

open import CaTTExp.TypingWith ∅ side
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn)
open import CaTTExp.DerivedBoundary
  using (σR; rwT; tyK; tgtK; srcK; hL; σL; lwT; rwT-ty0; rwT-ty; lwT-ty0; lwT-ty;
         C-sph; arr-inj₁; arr-inj₃; tyK-arr; srcK-arr; tgtK-arr; dim[])
open import CaTTExp.DerivedWith side closedS side-BK0 side-BK side-LK
  using (tm-ty; rwT-wf; lwT-wf)
open import CaTTExp.Surface.Conservativity ∅ side closedS
open import CaTTExp.Surface.TheoremB ∅ side closedS

------------------------------------------------------------------------
-- Reading a term's type off the context.

fromJust : Maybe Ty → Ty
fromJust (just A) = A
fromJust nothing  = ⋆

tyOf : Ctx → Tm → Ty
tyOf Γ (var i)     = fromJust (lookup Γ i)
tyOf Γ (coh Δ A σ) = A [ σ ]ty
tyOf Γ (cst k)     = ty k

tyOf-ok : ∀ {Γ t A} → Γ ⊢tm t ∶ A → tyOf Γ t ≡ A
tyOf-ok (var-wf _ e) rewrite e = refl
tyOf-ok (coh-wf _ _ _ _ _) = refl
tyOf-ok (cst-wf _ _) = refl

srcOf tgtOf : Ty → Tm
srcOf ⋆           = var 0
srcOf (arr _ s _) = s
tgtOf ⋆           = var 0
tgtOf (arr _ _ t) = t

------------------------------------------------------------------------
-- The whiskering operation.

-- (p ◃ₖ x) ▹ₖ q with the boundary data given explicitly; j is the
-- codimension: x is an n-cell with n = j + k + 1.
rawW : Nat → Nat → Tm → Tm → Tm → Tm → Ty → Tm → Tm
rawW k j s′ t′ p x X q =
  rwT k j (lwT k j p s′ x X) (lK k j [ σL k j p s′ x X ]ty) t′ q

wh : Ctx → Nat → Tm → Tm → Tm → Tm
wh Γ k p x q =
  rawW k (dim (tyOf Γ x) ∸ suc k) (srcOf (tyOf Γ p)) (tgtOf (tyOf Γ q))
       p x (tyOf Γ x) q

------------------------------------------------------------------------
-- Arithmetic and prefixes.

private
  +-suc′ : ∀ d k → d + suc k ≡ suc (d + k)
  +-suc′ zero    k = refl
  +-suc′ (suc d) k = cong suc (+-suc′ d k)

  +∸ : ∀ d k → (d + k) ∸ k ≡ d
  +∸ d zero    = +-zero d
    where
    +-zero : ∀ d → d + 0 ≡ d
    +-zero zero    = refl
    +-zero (suc d) = cong suc (+-zero d)
  +∸ d (suc k) rewrite +-suc′ d k = +∸ d k

  -- suc (d + k) is never k
  ne-above : ∀ d k → (suc (d + k) ==ℕ k) ≡ false
  ne-above d zero    = refl
  ne-above d (suc k) rewrite +-suc′ d k = ne-above d k

  ==-refl′ : ∀ n → (n ==ℕ n) ≡ true
  ==-refl′ zero    = refl
  ==-refl′ (suc n) = ==-refl′ n

  arr-inj₂ : ∀ {A B s t u v} → arr A s t ≡ arr B u v → s ≡ u
  arr-inj₂ refl = refl

depth : ∀ {B X} → Pre B X → Nat
depth here      = 0
depth (there p) = suc (depth p)

pre-dim′ : ∀ {C s t X} (pr : Pre (arr C s t) X) → dim X ≡ nB (dim C) (depth pr)
pre-dim′ here      = refl
pre-dim′ (there p) = cong suc (pre-dim′ p)

pre-lt : ∀ {C s t X} → Pre (arr C s t) X → T (dim C <ℕ dim X)
pre-lt {C} here = n<sn (dim C)
pre-lt {C} (there {Y} p) = <-suc (dim C) (dim Y) (pre-lt p)

j-ok : ∀ {C s t X} (pr : Pre (arr C s t) X) → dim X ∸ suc (dim C) ≡ depth pr
j-ok {C} pr rewrite pre-dim′ pr = +∸ (depth pr) (dim C)

-- The level-k boundary of a cell type with prefix arr C s t.
bd : ∀ {C s t X} → Pre (arr C s t) X →
     (tyK (dim C) X ≡ C) × (srcK (dim C) X ≡ s) × (tgtK (dim C) X ≡ t)
bd {C} {s} {t} here =
  let e = C-sph (dim C) (arr C s t) refl
  in sym (arr-inj₁ e) , sym (arr-inj₂ e) , sym (arr-inj₃ e)
bd {C} (there {Y} {u} {v} pr) =
  let lt = pre-lt pr ; (e₁ , e₂ , e₃) = bd pr
  in trans (tyK-arr (dim C) Y u v lt) e₁ ,
     trans (srcK-arr (dim C) Y u v lt) e₂ ,
     trans (tgtK-arr (dim C) Y u v lt) e₃

------------------------------------------------------------------------
-- The type of the left whisker p ◃ₖ x, written out along the prefix.

lwTy : ∀ {C s t X} → Tm → Tm → Pre (arr C s t) X → Ty
lwTy {C} {s} {t} p s′ here = arr C s′ t
lwTy {C} p s′ (there {Y} {u} {v} pr) =
  arr (lwTy p s′ pr) (lwT (dim C) (depth pr) p s′ u Y) (lwT (dim C) (depth pr) p s′ v Y)

lwTy-pre : ∀ {C s t X} p s′ (pr : Pre (arr C s t) X) → Pre (arr C s′ t) (lwTy p s′ pr)
lwTy-pre p s′ here       = here
lwTy-pre p s′ (there pr) = there (lwTy-pre p s′ pr)

lwTy-dim : ∀ {C s t X} p s′ (pr : Pre (arr C s t) X) → dim (lwTy p s′ pr) ≡ nB (dim C) (depth pr)
lwTy-dim p s′ here       = refl
lwTy-dim p s′ (there pr) = cong suc (lwTy-dim p s′ pr)

lw-ty : ∀ {C s t X} p s′ x (pr : Pre (arr C s t) X) →
        lK (dim C) (depth pr) [ σL (dim C) (depth pr) p s′ x X ]ty ≡ lwTy p s′ pr
lw-ty {C} {s} {t} p s′ x here =
  trans (lwT-ty0 (dim C) p s′ x (arr C s t) refl)
        (cong₂ (λ A b → arr A s′ b) (fst (bd {C} {s} {t} here)) (snd (snd (bd {C} {s} {t} here))))
lw-ty {C} p s′ x (there {Y} {u} {v} pr) =
  trans (lwT-ty (dim C) (depth pr) p s′ x Y u v (pre-dim′ pr))
        (cong (λ A → arr A (lwT (dim C) (depth pr) p s′ u Y) (lwT (dim C) (depth pr) p s′ v Y))
              (lw-ty p s′ u pr))

------------------------------------------------------------------------
-- Wh-wf for plain CaTT, for every E and every other parameter.

module _ (E : SurfaceEq)
         (inv-arr : ∀ {Γ A A′ a a′ b b′} → SurfaceEq._∣_≈T_ E Γ (arr A a b) (arr A′ a′ b′) →
                    (SurfaceEq._∣_≈T_ E Γ A A′) × (SurfaceEq._∣_≈t_ E Γ a a′) × (SurfaceEq._∣_≈t_ E Γ b b′))
         (dim-≈ : ∀ {Γ A A′} → SurfaceEq._∣_≈T_ E Γ A A′ → dim A ≡ dim A′)
         (Unit : Ctx → Tm → Set)
  where

  open Hyp E inv-arr dim-≈ tm-ty Unit wh

  private
    -- wh on typed arguments is rawW with the given boundary data.
    wh-eq : ∀ {Γ C s s′ t t′ p q x X} →
            Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ → Γ ⊢tm x ∶ X →
            wh Γ (dim C) p x q ≡ rawW (dim C) (dim X ∸ suc (dim C)) s′ t′ p x X q
    wh-eq dp dq dx rewrite tyOf-ok dp | tyOf-ok dq | tyOf-ok dx = refl

    -- the type of (p ◃ₖ x) ▹ₖ q is whTy
    rw-ty : ∀ {Γ C s s′ t t′ p q x X} (pr : Pre (arr C s t) X) →
            Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ → Γ ⊢tm x ∶ X →
            wK (dim C) (depth pr) [ σR (lwT (dim C) (depth pr) p s′ x X) (lwTy p s′ pr) t′ q ]ty
              ≡ whTy Γ (dim C) p q s′ t′ X
    rw-ty {C = C} {s} {s′} {t} {t′} {p} {q} {x} here dp dq dx
      rewrite ==-refl′ (dim C) =
      let (e₁ , e₂ , _) = bd {C} {s′} {t} here
      in trans (rwT-ty0 (dim C) (lwT (dim C) 0 p s′ x (arr C s t)) (lwTy {C} {s} {t} p s′ here) t′ q refl)
               (cong₂ (λ A a → arr A a t′) e₁ e₂)
    rw-ty {Γ} {C} {s} {s′} {t} {t′} {p} {q} {x} (there {Y} {u} {v} pr) dp dq dx
      with tm-ty dx
    ... | arr-wf du dv
      rewrite pre-dim′ pr | ne-above (depth pr) (dim C) =
      trans (rwT-ty k d (lwT k (suc d) p s′ x (arr Y u v)) (lwTy p s′ pr) (lwU u) (lwU v) t′ q (lwTy-dim p s′ pr))
            (cong₂ (λ A (bs : Tm × Tm) → arr A (fst bs) (snd bs))
                   (rw-ty pr dp dq du)
                   (cong₂ _,_ (bdry u du) (bdry v dv)))
      where
      k = dim C
      d = depth pr
      lwU : Tm → Tm
      lwU w = lwT k d p s′ w Y
      bdry : ∀ w → Γ ⊢tm w ∶ Y → rwT k d (lwU w) (lwTy p s′ pr) t′ q ≡ wh Γ k p w q
      bdry w dw =
        sym (trans (wh-eq dp dq dw)
                   (trans (cong (λ m → rawW k m s′ t′ p w Y q) (j-ok pr))
                          (cong (λ L → rwT k d (lwU w) L t′ q) (lw-ty p s′ w pr))))

  -- TheoremB's Wh-wf, for plain CaTT.
  Wh-wf-pure : ∀ {Γ C s s′ t t′ p q x X} →
               Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ →
               Pre (arr C s t) X → Γ ⊢tm x ∶ X →
               Γ ⊢tm wh Γ (dim C) p x q ∶ whTy Γ (dim C) p q s′ t′ X
  Wh-wf-pure {Γ} {C} {s} {s′} {t} {t′} {p} {q} {x} {X} dp dq pr dx =
    subst (Γ ⊢tm_∶ whTy Γ k p q s′ t′ X) (sym (wh-eq dp dq dx))
      (subst (λ m → Γ ⊢tm rawW k m s′ t′ p x X q ∶ whTy Γ k p q s′ t′ X) (sym (j-ok pr))
        (subst (Γ ⊢tm rwT k d L LT t′ q ∶_) (trans (cong (λ Z → wK k d [ σR L Z t′ q ]ty) (lw-ty p s′ x pr))
                                                    (rw-ty pr dp dq dx))
          (rwT-wf k d dL eLT dq′)))
    where
    k  = dim C
    d  = depth pr
    L  = lwT k d p s′ x X
    LT = lK k d [ σL k d p s′ x X ]ty
    bX  = bd pr
    bLT = bd (lwTy-pre p s′ pr)
    dp′ : Γ ⊢tm p ∶ hL k s′ X
    dp′ = subst (Γ ⊢tm p ∶_) (sym (cong₂ (λ A b → arr A s′ b) (fst bX) (fst (snd bX)))) dp
    dL : Γ ⊢tm L ∶ LT
    dL = lwT-wf k d dx (pre-dim′ pr) dp′
    eLT : dim LT ≡ nB k d
    eLT = trans (cong dim (lw-ty p s′ x pr)) (lwTy-dim p s′ pr)
    dq′ : Γ ⊢tm q ∶ arr (tyK k LT) (tgtK k LT) t′
    dq′ = subst (Γ ⊢tm q ∶_)
            (sym (trans (cong (λ Z → arr (tyK k Z) (tgtK k Z) t′) (lw-ty p s′ x pr))
                        (cong₂ (λ A b → arr A b t′) (fst bLT) (snd (snd bLT)))))
            dq

------------------------------------------------------------------------
-- Non-vacuity: all of TheoremB's hypotheses at once.

module Consistent where

  -- types related iff of equal dimension; all terms related
  coarse : SurfaceEq
  coarse = record
    { _∣_≈t_ = λ _ _ _ → ⊤ ; _∣_≈T_ = λ _ A B → dim A ≡ dim B
    ; t-refl = tt ; t-sym = λ _ → tt ; t-trans = λ _ _ → tt
    ; T-refl = refl ; T-sym = sym ; T-trans = trans
    ; arr-cong = λ e _ _ → cong suc e
    ; coh-cong = λ _ _ → tt
    ; stable-T = λ {_} {_} {A} {A′} {σ} _ e →
        trans (dim[] A σ) (trans e (sym (dim[] A′ σ)))
    }

  open SurfaceEq coarse using (_∣_≈t_; _∣_≈T_)

  inv-arr : ∀ {Γ A A′ a a′ b b′} → Γ ∣ arr A a b ≈T arr A′ a′ b′ →
            (Γ ∣ A ≈T A′) × (Γ ∣ a ≈t a′) × (Γ ∣ b ≈t b′)
  inv-arr e = cong (λ n → n ∸ 1) e , tt , tt

  open Hyp coarse (λ {Γ} {A} {A′} {a} {a′} {b} {b′} → inv-arr {Γ} {A} {A′} {a} {a′} {b} {b′})
           (λ e → e) tm-ty (λ _ _ → ⊤) wh
  open Thm (Wh-wf-pure coarse (λ {Γ} {A} {A′} {a} {a′} {b} {b′} → inv-arr {Γ} {A} {A′} {a} {a′} {b} {b′})
                       (λ e → e) (λ _ _ → ⊤))
           (λ _ _ _ _ _ _ → tt) public
