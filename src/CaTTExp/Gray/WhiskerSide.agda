------------------------------------------------------------------------
-- Two-tier L accepts the whisker heads of CaTTExp.Derived for k ≥ 1.
--
--   gside-BK0 k   : graySide accepts (BK (k+1) 0,     wK (k+1) 0)
--   gside-BK  k j : graySide accepts (BK (k+1) (j+1), wK (k+1) (j+1))
--   gside-LK  k j : graySide accepts (LK (k+1) (j+1), lK (k+1) (j+1))
--
-- These are the three hypotheses of CaTTExp.DerivedWith at graySide,
-- restricted to k ≥ 1. This is step 2(c) of the two-tier L whiskering
-- interface (notes/surface-conservativity.md §7); k = 0 is step 2(d).
--
-- Proof, by induction on j, together with the L-typing of the heads
-- (gwK-wf, glK-wf):
--  * the head (k+1, j) lives on Σ(BK k j) (Gray.WhiskerSigma), a single
--    hom, and its type and sides are suspensions;
--  * Derived proves Finster–Mimram's operation condition isOp for the
--    head (op-BK0, op-BK, op-LK; syntactic facts about free variables);
--  * the sides are L-derivable: variables for j = 0, and for j + 1
--    cohs of the head (k+1, j), typed by the induction hypothesis;
--  * so Gray.SingleHomSide.op-side-gray applies: endsOK holds for every
--    suspended type, and dim A = dim Θ is a computation.
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerSide where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (dim-aL; <-suc; n<sn)
import CaTTExp.Derived as D
open D using (nB; zK; BK; wK; LK; lK; ρsK; ρtK; λsK; λtK)
import CaTTExp.Subst as SubstM
open import CaTTExp.Typing ∅ using (isOp; cattSide)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Suspension ∅ using (Σctx; Σty; Σty[])
open import CaTTExp.Gray.SingleHom ∅ using (objsΣ; endsTyΣ)
open import CaTTExp.Gray.SingleHomSide using (op-side-gray)
open import CaTTExp.Gray.WhiskerSigma using (Σ-aL; Σ-BK; Σ-wK; Σ-ρsK; Σ-LK; Σ-lK; Σ-λsK)

private
  closedL : SubstM.Closed ∅ graySide
  closedL ()

open import CaTTExp.DerivedWithBase graySide closedL
  using (wBK; ρK-wf; wLK; λsK-wf; λtK-wf)

------------------------------------------------------------------------
-- Generalities.

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
  dim-[] ⋆           σ = refl
  dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

  dim-wK : ∀ k j → dim (wK k j) ≡ nB k j
  dim-wK k zero    = cong suc (dim-aL k)
  dim-wK k (suc j) = cong suc (trans (dim-[] (wK k j) (ρsK k j)) (dim-wK k j))

  dim-lK : ∀ k j → dim (lK k j) ≡ nB k j
  dim-lK k zero    = dim-wK k zero
  dim-lK k (suc j) = cong suc (trans (dim-[] (lK k j) (λsK k j)) (dim-lK k j))

  endsOK-ty : ∀ Γ A {a b} → endsTy A ≡ just (a , b) →
              endsOK Γ A ≡ (isVarAt a (firstL (objs Γ)) ∧ isVarAt b (lastL (objs Γ)))
  endsOK-ty Γ A e rewrite e = refl

  -- Every suspended type has the endpoints a₀, a₁ of ΣΘ.
  endsOK-Σ : ∀ Θ A → T (endsOK (Σctx Θ) (Σty A))
  endsOK-Σ Θ A =
    subst T (sym (trans (endsOK-ty (Σctx Θ) (Σty A) (endsTyΣ A))
                        (cong (λ L → isVarAt (var 0) (firstL L) ∧ isVarAt (var 1) (lastL L)) (objsΣ Θ))))
          tt

  pos-BK : ∀ k j → T (0 <ℕ dimCtx (BK k j))
  pos-BK k j = subst (λ n → T (0 <ℕ n)) (sym (D.dimCtx-BK k j)) tt

  pos-LK : ∀ k j → T (0 <ℕ dimCtx (LK k j))
  pos-LK k j = subst (λ n → T (0 <ℕ n)) (sym (D.dimCtx-LK k j)) tt

  -- op-side-gray, transported along Σ(Θ) = Γ and Σ(A₀) = A.
  side-at : ∀ {Θ Γ A₀ A t u} → Θ ⊢ps → T (0 <ℕ dimCtx Θ) → Σctx Θ ≡ Γ → Σty A₀ ≡ A →
            Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → dim A ≡ dimCtx Θ → T (isOp Γ A t u) →
            T (graySide Γ A t u)
  side-at {Θ} {A₀ = ⋆}         P pos refl refl dt du dA iop =
    op-side-gray P pos dt du (endsOK-Σ Θ ⋆) dA iop
  side-at {Θ} {A₀ = arr B a b} P pos refl refl dt du dA iop =
    op-side-gray P pos dt du (endsOK-Σ Θ (arr B a b)) dA iop

------------------------------------------------------------------------
-- Right whisker heads.

gside-BK0 : ∀ k → T (graySide (BK (suc k) 0) (aL (suc k)) (var (dbl (suc k))) (var (zK (suc k) 0)))
gside-BK0 k =
  side-at (D.BK-ps k 0) (pos-BK k 0) (Σ-BK k 0) (Σ-aL k) (gs-src k) (gz k)
          (trans (dim-aL (suc k)) (sym (D.dimCtx-BK k 0))) (D.op-BK0 (suc k))
  where
  gs-src : ∀ k → BK (suc k) 0 ⊢tm var (dbl (suc k)) ∶ aL (suc k)
  gs-src k = var-wf (wBK (suc k) 0)
               (trans (D.lk-BK-Sph (suc k) 0 (dbl (suc k)) (<-suc (dbl (suc k)) (suc (dbl (suc k))) (n<sn (dbl (suc k)))))
                      (D.lk-Sph-s (suc k)))
  gz : ∀ k → BK (suc k) 0 ⊢tm var (zK (suc k) 0) ∶ aL (suc k)
  gz k = var-wf (wBK (suc k) 0) (D.lk-zK (suc k) 0)

GSideK : Nat → Nat → Set
GSideK k zero    = T (graySide (BK (suc k) 0) (aL (suc k)) (var (dbl (suc k))) (var (zK (suc k) 0)))
GSideK k (suc j) = T (graySide (BK (suc k) (suc j)) (wK (suc k) j [ ρsK (suc k) j ]ty)
                       (coh (BK (suc k) j) (wK (suc k) j) (ρsK (suc k) j))
                       (coh (BK (suc k) j) (wK (suc k) j) (ρtK (suc k) j)))

-- The two sides of the head (k+1, j+1), given the head (k+1, j).
private
  rcoh : ∀ k j {Γ σ} → BK (suc k) j ⊢ty wK (suc k) j → GSideK k j → Γ ⊢sub σ ∶ BK (suc k) j →
         Γ ⊢tm coh (BK (suc k) j) (wK (suc k) j) σ ∶ wK (suc k) j [ σ ]ty
  rcoh k zero    a s d = coh-wf (D.BK-ps (suc k) zero)    (wBK (suc k) zero)    a s d
  rcoh k (suc j) a s d = coh-wf (D.BK-ps (suc k) (suc j)) (wBK (suc k) (suc j)) a s d

  rsrc : ∀ k j → BK (suc k) j ⊢ty wK (suc k) j → GSideK k j →
         BK (suc k) (suc j) ⊢tm coh (BK (suc k) j) (wK (suc k) j) (ρsK (suc k) j) ∶ wK (suc k) j [ ρsK (suc k) j ]ty
  rsrc k j a s = rcoh k j a s (ρK-wf (suc k) j _ (D.lk-face-s (suc k) j))

  rtgt : ∀ k j → BK (suc k) j ⊢ty wK (suc k) j → GSideK k j →
         BK (suc k) (suc j) ⊢tm coh (BK (suc k) j) (wK (suc k) j) (ρtK (suc k) j) ∶ wK (suc k) j [ ρsK (suc k) j ]ty
  rtgt k j a s =
    subst (BK (suc k) (suc j) ⊢tm coh (BK (suc k) j) (wK (suc k) j) (ρtK (suc k) j) ∶_)
          (sym (D.faces-BK (suc k) j (wK (suc k) j) (D.avoidK (suc k) j)))
          (rcoh k j a s (ρK-wf (suc k) j _ (D.lk-face-t (suc k) j)))

mutual
  gwK-wf : ∀ k j → BK (suc k) j ⊢ty wK (suc k) j
  gwK-wf k zero =
    arr-wf (var-wf (wBK (suc k) 0)
              (trans (D.lk-BK-Sph (suc k) 0 (dbl (suc k)) (<-suc (dbl (suc k)) (suc (dbl (suc k))) (n<sn (dbl (suc k)))))
                     (D.lk-Sph-s (suc k))))
           (var-wf (wBK (suc k) 0) (D.lk-zK (suc k) 0))
  gwK-wf k (suc j) = arr-wf (rsrc k j (gwK-wf k j) (gsideK k j)) (rtgt k j (gwK-wf k j) (gsideK k j))

  gsideK : ∀ k j → GSideK k j
  gsideK k zero    = gside-BK0 k
  gsideK k (suc j) =
    side-at (D.BK-ps k (suc j)) (pos-BK k (suc j)) (Σ-BK k (suc j))
            (trans (Σty[] (wK k j) (ρsK k j)) (cong₂ _[_]ty (Σ-wK k j) (Σ-ρsK k j)))
            (rsrc k j (gwK-wf k j) (gsideK k j)) (rtgt k j (gwK-wf k j) (gsideK k j))
            (trans (dim-[] (wK (suc k) j) (ρsK (suc k) j))
                   (trans (dim-wK (suc k) j) (trans (cong suc (+-suc j k)) (sym (D.dimCtx-BK k (suc j))))))
            (D.op-BK (suc k) j (Sb.ty-sc D.closed (D.wK-wf (suc k) j)) (D.avoidK (suc k) j))

gside-BK : ∀ k j → T (graySide (BK (suc k) (suc j)) (wK (suc k) j [ ρsK (suc k) j ]ty)
                      (coh (BK (suc k) j) (wK (suc k) j) (ρsK (suc k) j))
                      (coh (BK (suc k) j) (wK (suc k) j) (ρtK (suc k) j)))
gside-BK k j = gsideK k (suc j)

------------------------------------------------------------------------
-- Left whisker heads (LK k 0 is BK k 0).

GLSideK : Nat → Nat → Set
GLSideK k zero    = GSideK k zero
GLSideK k (suc j) = T (graySide (LK (suc k) (suc j)) (lK (suc k) j [ λsK (suc k) j ]ty)
                        (coh (LK (suc k) j) (lK (suc k) j) (λsK (suc k) j))
                        (coh (LK (suc k) j) (lK (suc k) j) (λtK (suc k) j)))

private
  lcoh : ∀ k j {Γ σ} → LK (suc k) j ⊢ty lK (suc k) j → GLSideK k j → Γ ⊢sub σ ∶ LK (suc k) j →
         Γ ⊢tm coh (LK (suc k) j) (lK (suc k) j) σ ∶ lK (suc k) j [ σ ]ty
  lcoh k zero    a s d = coh-wf (D.LK-ps (suc k) zero)    (wLK (suc k) zero)    a s d
  lcoh k (suc j) a s d = coh-wf (D.LK-ps (suc k) (suc j)) (wLK (suc k) (suc j)) a s d

  lsrc : ∀ k j → LK (suc k) j ⊢ty lK (suc k) j → GLSideK k j →
         LK (suc k) (suc j) ⊢tm coh (LK (suc k) j) (lK (suc k) j) (λsK (suc k) j) ∶ lK (suc k) j [ λsK (suc k) j ]ty
  lsrc k j a s = lcoh k j a s (λsK-wf (suc k) j)

  ltgt : ∀ k j → LK (suc k) j ⊢ty lK (suc k) j → GLSideK k j →
         LK (suc k) (suc j) ⊢tm coh (LK (suc k) j) (lK (suc k) j) (λtK (suc k) j) ∶ lK (suc k) j [ λsK (suc k) j ]ty
  ltgt k j a s =
    subst (LK (suc k) (suc j) ⊢tm coh (LK (suc k) j) (lK (suc k) j) (λtK (suc k) j) ∶_)
          (sym (D.faces-LK (suc k) j (lK (suc k) j) (D.avoidLK (suc k) j)))
          (lcoh k j a s (λtK-wf (suc k) j))

mutual
  glK-wf : ∀ k j → LK (suc k) j ⊢ty lK (suc k) j
  glK-wf k zero    = gwK-wf k zero
  glK-wf k (suc j) = arr-wf (lsrc k j (glK-wf k j) (glsideK k j)) (ltgt k j (glK-wf k j) (glsideK k j))

  glsideK : ∀ k j → GLSideK k j
  glsideK k zero    = gside-BK0 k
  glsideK k (suc j) =
    side-at (D.LK-ps k (suc j)) (pos-LK k (suc j)) (Σ-LK k (suc j))
            (trans (Σty[] (lK k j) (λsK k j)) (cong₂ _[_]ty (Σ-lK k j) (Σ-λsK k j)))
            (lsrc k j (glK-wf k j) (glsideK k j)) (ltgt k j (glK-wf k j) (glsideK k j))
            (trans (dim-[] (lK (suc k) j) (λsK (suc k) j))
                   (trans (dim-lK (suc k) j) (trans (cong suc (+-suc j k)) (sym (D.dimCtx-LK k (suc j))))))
            (D.op-LK (suc k) j (Sb.ty-sc D.closed (D.lK-wf (suc k) j)) (D.avoidLK (suc k) j))

gside-LK : ∀ k j → T (graySide (LK (suc k) (suc j)) (lK (suc k) j [ λsK (suc k) j ]ty)
                      (coh (LK (suc k) j) (lK (suc k) j) (λsK (suc k) j))
                      (coh (LK (suc k) j) (lK (suc k) j) (λtK (suc k) j)))
gside-LK k j = glsideK k (suc j)
