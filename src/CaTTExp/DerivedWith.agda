------------------------------------------------------------------------
-- The derived whiskers of CaTTExp.Derived / CaTTExp.DerivedBoundary,
-- typed in any CaTT-style theory over the empty signature whose side
-- condition accepts the whisker heads.
--
-- Derived proves, for plain CaTT, that
--
--   rwhisk k j : Γ ⊢sub σ ∶ BK k j → Γ ⊢tm coh (BK k j) (wK k j) σ ∶ …
--   lwhisk k j : Γ ⊢sub σ ∶ LK k j → Γ ⊢tm coh (LK k j) (lK k j) σ ∶ …
--
-- and DerivedBoundary turns these into typing rules for the whiskers
-- c ▹ₖ h (rwT) and h ◃ₖ c (lwT) of given cells. Only the typing part
-- depends on the side condition: the pasting contexts, the types and
-- all type computations are syntax. Here the typing part is redone
-- for an arbitrary side condition `side`, from three hypotheses: side
-- accepts the heads (BK k 0, wK k 0), (BK k (j+1), wK k (j+1)) and
-- (LK k (j+1), lK k (j+1)) for every k, j. (LK k 0 is BK k 0.)
--
-- Syntactic facts (scoping, avoidance, substitution lemmas) are reused
-- from the plain-CaTT development: they do not depend on the side
-- condition, even where Derived proves them through a cattSide typing
-- derivation.
--
-- Instances: plain CaTT (the hypotheses are Derived's sideK, sideLK;
-- instantiated in CaTTExp.Surface.WhiskerCatt) and two-tier L (graySide; the
-- hypotheses for all k, j are the open part of S19's two-tier L
-- interface, checked by evaluation for k + j ≤ 3 in
-- CaTTExp.Surface.WhiskerGrayCheck).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅; cattSide)
open import CaTTExp.Signature
open Signature ∅
import CaTTExp.Subst as SubstM
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
import CaTTExp.DerivedBoundary as DB
open D using (nB; zK; BK; wK; LK; LPK; lK; ρsK; ρtK; λsK; λtK; tL; bLK; hTy; ρK;
              Sph; Dsk; sphSub; dskSub)

module CaTTExp.DerivedWith
  (side : Ctx → Ty → Tm → Tm → Bool)
  (closedS : SubstM.Closed ∅ side)
  (side-BK0 : ∀ k → T (side (BK k 0) (aL k) (var (dbl k)) (var (zK k 0))))
  (side-BK  : ∀ k j → T (side (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                         (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j))))
  (side-LK  : ∀ k j → T (side (LK k (suc j)) (lK k j [ λsK k j ]ty)
                         (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j))))
  where

open import CaTTExp.TypingWith ∅ side
import CaTTExp.Subst ∅ side as Sg
open import CaTTExp.Weakening ∅ side using (wk-tm; wk-ty; wk-sub)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.GrayCtx.NaturalWF using (dim-aL; <-suc; n<sn)

------------------------------------------------------------------------
-- Scoping does not depend on the side condition (Subst's ScTy is
-- stated per side condition, so convert).

mutual
  scTy-conv : ∀ n A → Sg.ScTy n A → Sb.ScTy n A
  scTy-conv n ⋆           _           = tt
  scTy-conv n (arr A t u) (a , p , q) = scTy-conv n A a , scTm-conv n t p , scTm-conv n u q

  scTm-conv : ∀ n t → Sg.ScTm n t → Sb.ScTm n t
  scTm-conv n (var i)     p = p
  scTm-conv n (coh _ _ σ) p = scSub-conv n σ p
  scTm-conv n (cst _)     p = tt

  scSub-conv : ∀ n σ → Sg.ScSub n σ → Sb.ScSub n σ
  scSub-conv n ⟨⟩       _       = tt
  scSub-conv n (σ ,ₛ t) (p , q) = scSub-conv n σ p , scTm-conv n t q

------------------------------------------------------------------------
-- Presupposition.

lookup-wf : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
lookup-wf {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
... | true  = subst (λ X → (Γ ▸ B) ⊢ty X) (just-inj eq) (wk-ty b (▸-wf w b))
  where
  just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
  just-inj refl = refl
... | false = wk-ty (lookup-wf w eq) (▸-wf w b)

tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
tm-ty (var-wf w eq)      = lookup-wf w eq
tm-ty (coh-wf _ _ a _ s) = Sg.ty[] closedS a s
tm-ty (cst-wf {k} _ _)   = ⊥-elim k

------------------------------------------------------------------------
-- Pasting contexts are well formed.

ps-wf : ∀ {Γ x A} → Γ ⊢ps x ∶ A → (Γ ⊢ctx) × (Γ ⊢tm var x ∶ A)
ps-wf pss = let w = ▸-wf ε-wf (⋆-wf ε-wf) in w , var-wf w refl
ps-wf (pse {Γ} {x} {A} d) =
  let (w , dx) = ps-wf d
      a  = tm-ty dx
      w₁ = ▸-wf w a
      B  = arr A (var x) (var (len Γ))
      b  = arr-wf (wk-tm dx w₁) (var-wf w₁ (D.last-lookup Γ A))
      w₂ = ▸-wf w₁ b
  in w₂ , var-wf w₂ (D.last-lookup (Γ ▸ A) B)
ps-wf (psd d) with ps-wf d
... | w , df with tm-ty df
...   | arr-wf _ dy = w , dy

ps-ctx : ∀ {Γ} → Γ ⊢ps → Γ ⊢ctx
ps-ctx (ps d) = fst (ps-wf d)

------------------------------------------------------------------------
-- Spheres, disks, identities.

sph-wf : ∀ {Γ A} → Γ ⊢ty A → Γ ⊢sub sphSub A ∶ Sph (dim A)
sph-wf (⋆-wf w) = ⟨⟩-wf w
sph-wf {Γ} {arr A s t} (arr-wf ds dt) =
  ,-wf (,-wf (sph-wf (tm-ty ds)) (subst (Γ ⊢tm s ∶_) (sym (D.aL-sph A)) ds))
       (subst (Γ ⊢tm t ∶_)
         (sym (trans (Sb.ext-ty (aL (dim A)) (sphSub A) s (D.sc-aL' A)) (D.aL-sph A))) dt)

dsk-wf : ∀ {Γ c C} → Γ ⊢tm c ∶ C → Γ ⊢sub dskSub c C ∶ Dsk (dim C)
dsk-wf {Γ} {c} {C} d = ,-wf (sph-wf (tm-ty d)) (subst (Γ ⊢tm c ∶_) (sym (D.aL-sph C)) d)

id-wf : ∀ {Γ} → Γ ⊢ctx → Γ ⊢sub D.idS (len Γ) ∶ Γ
id-wf ε-wf = ⟨⟩-wf ε-wf
id-wf (▸-wf {Γ} {A} w a) =
  ,-wf (wk-sub (id-wf w) w')
       (subst ((Γ ▸ A) ⊢tm var (len Γ) ∶_) (sym (D.id-ty (len Γ) A (scTy-conv (len Γ) A (Sg.ty-sc closedS a))))
              (var-wf w' (D.last-lookup Γ A)))
  where w' = ▸-wf w a

ctx-init : ∀ {Γ A} → (Γ ▸ A) ⊢ctx → Γ ⊢ctx
ctx-init (▸-wf w _) = w

ctx-last : ∀ {Γ A} → (Γ ▸ A) ⊢ctx → Γ ⊢ty A
ctx-last (▸-wf _ a) = a

------------------------------------------------------------------------
-- Right whiskers.

wBK : ∀ k j → BK k j ⊢ctx
wBK k j = ps-ctx (D.BK-ps k j)

ρK-wf : ∀ k j v → lookup (BK k (suc j)) v ≡ just (aL (nB k j)) → BK k (suc j) ⊢sub ρK k j v ∶ BK k j
ρK-wf k j v lv =
  ,-wf (,-wf Dd (subst (BK k (suc j) ⊢tm var (zK k (suc j)) ∶_)
                      (sym (D.fix-aL1 k (nB k j) v (<-suc k (nB k j) (D.k<n j k))))
                      (var-wf w (D.lk-zK k (suc j)))))
       (subst (BK k (suc j) ⊢tm var (suc (zK k (suc j))) ∶_) (sym (D.ty-hK k j v)) (var-wf w (D.lk-hK k (suc j))))
  where
  w = wBK k (suc j)
  Dd : BK k (suc j) ⊢sub dskSub (var v) (aL (nB k j)) ∶ Dsk (nB k j)
  Dd = subst (λ m → BK k (suc j) ⊢sub dskSub (var v) (aL (nB k j)) ∶ Dsk m) (dim-aL (nB k j))
             (dsk-wf (var-wf w lv))

SideK : Nat → Nat → Set
SideK k zero    = T (side (BK k 0) (aL k) (var (dbl k)) (var (zK k 0)))
SideK k (suc j) = T (side (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                      (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j)))

sideK : ∀ k j → SideK k j
sideK k zero    = side-BK0 k
sideK k (suc j) = side-BK k j

rwhisk' : ∀ k j {Γ σ} → BK k j ⊢ty wK k j → Γ ⊢sub σ ∶ BK k j →
          Γ ⊢tm coh (BK k j) (wK k j) σ ∶ wK k j [ σ ]ty
rwhisk' k zero    a d = coh-wf (D.BK-ps k zero)    (wBK k zero)    a (sideK k zero) d
rwhisk' k (suc j) a d = coh-wf (D.BK-ps k (suc j)) (wBK k (suc j)) a (sideK k (suc j)) d

wK-wf : ∀ k j → BK k j ⊢ty wK k j
wK-wf k zero =
  arr-wf (var-wf (wBK k 0) (trans (D.lk-BK-Sph k 0 (dbl k) (<-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))))
                                  (D.lk-Sph-s k)))
         (var-wf (wBK k 0) (D.lk-zK k 0))
wK-wf k (suc j) =
  arr-wf (rwhisk' k j (wK-wf k j) (ρK-wf k j _ (D.lk-face-s k j)))
         (subst (BK k (suc j) ⊢tm coh (BK k j) (wK k j) (ρtK k j) ∶_)
                (sym (D.faces-BK k j (wK k j) (D.avoidK k j)))
                (rwhisk' k j (wK-wf k j) (ρK-wf k j _ (D.lk-face-t k j))))

rwhisk : ∀ k j {Γ σ} → Γ ⊢sub σ ∶ BK k j → Γ ⊢tm coh (BK k j) (wK k j) σ ∶ wK k j [ σ ]ty
rwhisk k j = rwhisk' k j (wK-wf k j)

------------------------------------------------------------------------
-- Left whiskers.

wLK : ∀ k j → LK k j ⊢ctx
wLK k j = ps-ctx (D.LK-ps k j)

λsK-wf : ∀ k j → LK k (suc j) ⊢sub λsK k j ∶ LK k j
λsK-wf k j =
  subst (λ n → LK k (suc j) ⊢sub D.idS n ∶ LK k j) (D.len-LK k j)
        (wk-sub (wk-sub (id-wf (wLK k j)) (ctx-init w)) w)
  where w = wLK k (suc j)

λtK-wf : ∀ k j → LK k (suc j) ⊢sub λtK k j ∶ LK k j
λtK-wf k j =
  ,-wf (subst (λ n → LK k (suc j) ⊢sub D.idS n ∶ LPK k j) (D.len-LPK k j)
              (wk-sub (wk-sub (wk-sub (id-wf (ctx-init (wLK k j))) (ctx-init (ctx-init w))) (ctx-init w)) w))
       (subst (LK k (suc j) ⊢tm var (suc (tL k j)) ∶_)
              (sym (D.id-ty (tL k j) (bLK k (suc j))
                     (subst (λ n → Sb.ScTy n (bLK k (suc j))) (D.len-LPK k j)
                            (scTy-conv _ _ (Sg.ty-sc closedS (ctx-last (wLK k j)))))))
              (var-wf w (D.lk-λt k j)))
  where w = wLK k (suc j)

lwhisk' : ∀ k j {Γ σ} → LK k j ⊢ty lK k j → Γ ⊢sub σ ∶ LK k j →
          Γ ⊢tm coh (LK k j) (lK k j) σ ∶ lK k j [ σ ]ty
lwhisk' k zero    a d = coh-wf (D.LK-ps k zero)    (wLK k zero)    a (side-BK0 k) d
lwhisk' k (suc j) a d = coh-wf (D.LK-ps k (suc j)) (wLK k (suc j)) a (side-LK k j) d

lK-wf : ∀ k j → LK k j ⊢ty lK k j
lK-wf k zero    = wK-wf k zero
lK-wf k (suc j) =
  arr-wf (lwhisk' k j (lK-wf k j) (λsK-wf k j))
         (subst (LK k (suc j) ⊢tm coh (LK k j) (lK k j) (λtK k j) ∶_)
                (sym (D.faces-LK k j (lK k j) (D.avoidLK k j)))
                (lwhisk' k j (lK-wf k j) (λtK-wf k j)))

lwhisk : ∀ k j {Γ σ} → Γ ⊢sub σ ∶ LK k j → Γ ⊢tm coh (LK k j) (lK k j) σ ∶ lK k j [ σ ]ty
lwhisk k j = lwhisk' k j (lK-wf k j)

------------------------------------------------------------------------
-- Whiskers of given cells (DerivedBoundary's rwT-wf, lwT-wf).

open DB using (σR; rwT; tyK; tgtK; srcK; hL; σLp; σL; lwT)

σR-wf : ∀ k j {Γ c C z h} → Γ ⊢tm c ∶ C → dim C ≡ nB k j →
        Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z → Γ ⊢sub σR c C z h ∶ BK k j
σR-wf k j {Γ} {c} {C} {z} {h} dc e dh with tm-ty dh
... | arr-wf _ dz =
  ,-wf (,-wf (subst (λ m → Γ ⊢sub dskSub c C ∶ Dsk m) e (dsk-wf dc))
             (subst (Γ ⊢tm z ∶_) (sym (Sb.ext-ty (aL k) (sphSub C) c (DB.sc-aL-in k j C e))) dz))
       (subst (Γ ⊢tm h ∶_) (sym (DB.ty-σR k j c C z e)) dh)

rwT-wf : ∀ k j {Γ c C z h} → Γ ⊢tm c ∶ C → dim C ≡ nB k j →
         Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z →
         Γ ⊢tm rwT k j c C z h ∶ wK k j [ σR c C z h ]ty
rwT-wf k j dc e dh = rwhisk k j (σR-wf k j dc e dh)

tgtK-wf : ∀ k j {Γ C} → Γ ⊢ty C → dim C ≡ nB k j → Γ ⊢tm tgtK k C ∶ tyK k C
tgtK-wf k zero {Γ} {arr C₀ s₀ t₀} (arr-wf ds dt) e =
  D.subst₂ (λ X Y → Γ ⊢tm X ∶ Y) (DB.arr-inj₃ eq) (DB.arr-inj₁ eq) dt
  where eq = DB.C-sph k (arr C₀ s₀ t₀) e
tgtK-wf k (suc j) {Γ} {arr C' s t} (arr-wf ds dt) e =
  D.subst₂ (λ X Y → Γ ⊢tm X ∶ Y) (sym (DB.tgtK-arr k C' s t p)) (sym (DB.tyK-arr k C' s t p))
    (tgtK-wf k j (tm-ty ds) e')
  where
  e' : dim C' ≡ nB k j
  e' = cong (λ m → m ∸ 1) e
  p : T (k <ℕ dim C')
  p = subst (λ m → T (k <ℕ m)) (sym e') (D.k<n j k)

mutual
  σLp-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
           Γ ⊢sub σLp k j h x C ∶ LPK k j
  σLp-wf k zero {Γ} {h} {x} {c} {C} dc e dh =
    ,-wf (subst (λ m → Γ ⊢sub dskSub h (hL k x C) ∶ Dsk m) (cong suc (DB.dim-tyK k C)) (dsk-wf dh))
         (subst (Γ ⊢tm tgtK k C ∶_) (sym (DB.aL-σLp0 k h x C)) (tgtK-wf k zero (tm-ty dc) e))
  σLp-wf k (suc j) {Γ} {h} {x} {c} {arr C' s t} dc e dh with tm-ty dc
  ... | arr-wf ds dt =
    ,-wf (σL-wf k j ds e' (subst (Γ ⊢tm h ∶_) (DB.hL-arr k j x C' s t e') dh))
         (subst (Γ ⊢tm t ∶_) (sym eq) dt)
    where
    e' : dim C' ≡ nB k j
    e' = cong (λ m → m ∸ 1) e
    eq : bLK k (suc j) [ σL k j h x s C' ]ty ≡ C'
    eq = trans (Sb.ext-ty (bLK k (suc j)) (σLp k j h x C') s
                  (subst (λ m → Sb.ScTy m (bLK k (suc j))) (sym (DB.lenₛ-σLp k j h x C' e')) (DB.sc-bLK k j)))
               (DB.bLK-σLp k j h x C' e')

  σL-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
          Γ ⊢sub σL k j h x c C ∶ LK k j
  σL-wf k j {Γ} {h} {x} {c} {C} dc e dh =
    ,-wf (σLp-wf k j dc e dh) (subst (Γ ⊢tm c ∶_) (sym (DB.bLK-σLp k j h x C e)) dc)

lwT-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
         Γ ⊢tm lwT k j h x c C ∶ lK k j [ σL k j h x c C ]ty
lwT-wf k j dc e dh = lwhisk k j (σL-wf k j dc e dh)
