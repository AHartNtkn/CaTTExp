------------------------------------------------------------------------
-- The part of CaTTExp.DerivedWith that needs no hypothesis about the
-- whisker heads: presupposition, pasting contexts, spheres, disks,
-- identities, and the typing of the face substitutions ρK, λsK, λtK
-- (they substitute variables only). Used by CaTTExp.DerivedWith and,
-- for two-tier L, by CaTTExp.Gray.WhiskerSide, which proves the head
-- hypotheses by induction together with the typing of the heads.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅; cattSide)
open import CaTTExp.Signature
open Signature ∅
import CaTTExp.Subst as SubstM
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
open D using (nB; zK; BK; wK; LK; LPK; lK; ρsK; ρtK; λsK; λtK; tL; bLK; hTy; ρK;
              Sph; Dsk; sphSub; dskSub)

module CaTTExp.DerivedWithBase
  (side : Ctx → Ty → Tm → Tm → Bool)
  (closedS : SubstM.Closed ∅ side)
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

