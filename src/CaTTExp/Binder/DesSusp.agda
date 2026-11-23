------------------------------------------------------------------------
-- DES suspends (ledger S27 (c), (d)): the destructors of spec §3.3,
-- given as a head family with arity contexts and types (spec §1.6;
-- CaTTExp.Binder.HeadSpec), satisfy the suspension hypotheses of
-- CaTTExp.Binder.Suspension at every dimension, with
--
--   Σ(t⁻ˡ at dimension n) = t⁻ˡ at dimension n + 1, and likewise for
--   t⁻ʳ, λ_t, ρ_t,
--
-- the arity of a destructor at n + 1 being Σ of its arity at n (the
-- disk Dⁿ⁺² is ΣDⁿ⁺¹) and its type Σ of the type at n. So the
-- hypotheses `HeadSusp` are satisfiable by a real head family, not
-- only vacuously, and the kernel with DES suspends (`des-susp`).
--
-- The family `desSpec` is DES of CaTTExp.Binder.Des written with
-- ordinary variables: its binder data is that of `desBinders` closed
-- (`args-agree`, `res-agree`), and its validity holds at every
-- dimension n ≥ 1, selector 0 (`des-valid`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Syntax as Syn
import CaTTExp.Binder.Mark as BM
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.HeadSpec

module CaTTExp.Binder.DesSusp (𝕊₀ : Old.Signature) where

K : Set
K = Old.Signature.K 𝕊₀

open Syn K DesF
open DesConstruction K DesF (λ b → b)
  using (tyD; diskD; comp; idc; tyB; argsD; bvs; b0; self)
  renaming (res to resD; args to argsDes; side to sideD)
open import CaTTExp.Binder.SyntaxLemmas K DesF
open import CaTTExp.Binder.Close K DesF

------------------------------------------------------------------------
-- The family, written with ordinary variables. m stands for n + n.

argsH : Nat → Ctx
argsH n = diskD n ▸ tyD n ▸[ minv ∷ [] ] tyD (suc n)

compPCM : Nat → Nat → Ctx
compPCM n m = diskD (suc n) ▸ tyD n ▸ arr (tyD n) (var (suc m)) (var (3 + m))

compM : Nat → Nat → Sub → Tm → Tm → Tm → Tm → Tm → Tm
compM n m bd f g α h β =
  coh (compPCM n m) (arr (tyD n) (var m) (var (3 + m))) (bd ,ₛ f ,ₛ g ,ₛ α ,ₛ h ,ₛ β)

idcM : Nat → Nat → Sub → Tm → Tm
idcM n m bd f = coh (diskD n) (arr (tyD n) (var m) (var m)) (bd ,ₛ f)

selfM : DesKind → Nat → Nat → Tm
selfM k n m = bnd (des k (suc n)) 0 ε (fresh 0 (3 + m))

tyL : Nat → Nat → Ty
tyL n m = arr (tyD n) (var (suc m)) (var m)

unitLT : Nat → Nat → Ty
unitLT n m =
  arr (arr (tyD n) (var (suc m)) (var (suc m)))
      (compM n m (fresh 0 m) (var (suc m)) (var m) (selfM linvK n m) (var (suc m)) (var (suc (suc m))))
      (idcM n m (fresh 0 m) (var (suc m)))

unitRT : Nat → Nat → Ty
unitRT n m =
  arr (arr (tyD n) (var m) (var m))
      (compM n m (fresh 0 m) (var m) (var (suc m)) (var (suc (suc m))) (var m) (selfM rinvK n m))
      (idcM n m (fresh 0 m) (var m))

okD : DesF → Nat → Bool
okD (des _ zero)    y = false
okD (des _ (suc n)) y = y ==ℕ 0

ctxD : DesF → Nat → Ctx
ctxD (des _ zero)    _ = ε
ctxD (des _ (suc n)) _ = argsH n

tyH : DesF → Nat → Ty
tyH (des _ zero)     _ = ⋆
tyH (linv (suc n))   _ = tyL n (n + n)
tyH (rinv (suc n))   _ = tyL n (n + n)
tyH (unitL (suc n))  _ = unitLT n (n + n)
tyH (unitR (suc n))  _ = unitRT n (n + n)

desSpec : HeadSpec K
desSpec = record
  { H         = DesF
  ; _==H_     = _==D_
  ; ==H-sound = ==D-sound
  ; hctx      = ctxD
  ; hty       = tyH
  ; hok       = okD
  }

------------------------------------------------------------------------
-- It is DES: closing its data gives desBinders' data.

private
  cl-tyD : ∀ n → clTy 0 (tyD n) ≡ tyB n
  cl-tyD zero    = refl
  cl-tyD (suc n) rewrite cl-tyD n = refl

  cl-diskD : ∀ n → clTel 0 (diskD n) ≡ DesConstruction.diskB K DesF (λ b → b) n
  cl-diskD zero    = refl
  cl-diskD (suc n) rewrite cl-diskD n | cl-tyD n | cl-tyD (suc n) = refl

  cl-fresh : ∀ k → clSub 0 (fresh 0 k) ≡ bvs k
  cl-fresh zero    = refl
  cl-fresh (suc k) rewrite cl-fresh k = refl

args-agree : ∀ k n y → clTel 0 (ctxD (des k (suc n)) y) ≡ argsDes (des k (suc n)) y ε
args-agree k n y rewrite cl-diskD n | cl-tyD n | cl-tyD (suc n) = refl

res-agree : ∀ k n y → clTy 0 (tyH (des k (suc n)) y) ≡ resD (des k (suc n)) y ε
res-agree linvK  n y rewrite cl-tyD n = refl
res-agree rinvK  n y rewrite cl-tyD n = refl
res-agree unitLK n y rewrite cl-tyD n | cl-fresh (n + n) | cl-fresh (3 + (n + n)) = refl
res-agree unitRK n y rewrite cl-tyD n | cl-fresh (n + n) | cl-fresh (3 + (n + n)) = refl

------------------------------------------------------------------------
-- Arithmetic and scoping.

private
  dd-suc : ∀ n → suc n + suc n ≡ suc (suc (n + n))
  dd-suc n = cong suc (+-suc n n)

  lt2 : ∀ m → T (m <ℕ suc (suc m))
  lt2 m = <-suc m (suc m) (<-self m)

  lt3 : ∀ m → T (m <ℕ suc (suc (suc m)))
  lt3 m = <-suc m (suc (suc m)) (lt2 m)

  lenD : ∀ n → len (diskD n) ≡ suc (n + n)
  lenD zero    = refl
  lenD (suc n) rewrite lenD n | +-suc n n = refl

  sc-tyD : ∀ n → T (scTy? (n + n) (tyD n))
  sc-tyD zero    = tt
  sc-tyD (suc n) = subst (λ k → T (scTy? k (tyD (suc n)))) (sym (dd-suc n)) (
    ∧T (scTy-suc (tyD n) (scTy-suc (tyD n) (sc-tyD n))) (∧T (lt2 (n + n)) (<-self (n + n))))

  sc-tyD3 : ∀ n → T (scTy? (3 + (n + n)) (tyD n))
  sc-tyD3 n = scTy-suc (tyD n) (scTy-suc (tyD n) (scTy-suc (tyD n) (sc-tyD n)))

  lc-tyD : ∀ n → T (lcTy? 0 (tyD n))
  lc-tyD zero    = tt
  lc-tyD (suc n) = ∧T (lc-tyD n) tt

  honest-step : ∀ n ms → T (honest? (diskD n)) → T (honest? (diskD n ▸ tyD n ▸[ ms ] tyD (suc n)))
  honest-step n ms h rewrite lenD n =
    ∧T (∧T h (∧T (scTy-suc (tyD n) (sc-tyD n)) (lc-tyD n)))
       (∧T (subst (λ k → T (scTy? k (tyD (suc n)))) (dd-suc n) (sc-tyD (suc n))) (lc-tyD (suc n)))

  honest-diskD : ∀ n → T (honest? (diskD n))
  honest-diskD zero    = tt
  honest-diskD (suc n) = honest-step n [] (honest-diskD n)

  fresh3 : ∀ m → T (scSub? (3 + m) (fresh 0 m))
  fresh3 m = scSub-suc (fresh 0 m) (scSub-suc (fresh 0 m) (scSub-suc (fresh 0 m) (sc-fresh 0 m)))

  sc-res : ∀ k n → T (scTy? (3 + (n + n)) (tyH (des k (suc n)) 0))
  sc-res linvK  n = ∧T (sc-tyD3 n) (∧T (lt2 (n + n)) (lt3 (n + n)))
  sc-res rinvK  n = ∧T (sc-tyD3 n) (∧T (lt2 (n + n)) (lt3 (n + n)))
  sc-res unitLK n =
    let m = n + n in
    ∧T (∧T (sc-tyD3 n) (∧T (lt2 m) (lt2 m)))
       (∧T (∧T (∧T (∧T (∧T (∧T (fresh3 m) (lt2 m)) (lt3 m)) (sc-fresh 0 (3 + m))) (lt2 m)) (<-self m))
           (∧T (fresh3 m) (lt2 m)))
  sc-res unitRK n =
    let m = n + n in
    ∧T (∧T (sc-tyD3 n) (∧T (lt3 m) (lt3 m)))
       (∧T (∧T (∧T (∧T (∧T (∧T (fresh3 m) (lt3 m)) (lt2 m)) (<-self m)) (lt3 m)) (sc-fresh 0 (3 + m)))
           (∧T (fresh3 m) (lt3 m)))

  lc-res : ∀ k n → T (lcTy? 0 (tyH (des k (suc n)) 0))
  lc-res linvK  n = ∧T (lc-tyD n) tt
  lc-res rinvK  n = ∧T (lc-tyD n) tt
  lc-res unitLK n =
    let m = n + n in
    ∧T (∧T (lc-tyD n) tt)
       (∧T (∧T (∧T (∧T (∧T (∧T (lc-fresh 0 m) tt) tt) (lc-fresh 0 (3 + m))) tt) tt)
           (∧T (lc-fresh 0 m) tt))
  lc-res unitRK n =
    let m = n + n in
    ∧T (∧T (lc-tyD n) tt)
       (∧T (∧T (∧T (∧T (∧T (∧T (lc-fresh 0 m) tt) tt) tt) tt) (lc-fresh 0 (3 + m)))
           (∧T (lc-fresh 0 m) tt))

-- Every destructor at every dimension n ≥ 1 is a valid head.
module _ where
  open Laws 𝕊₀ desSpec using (𝕊)
  open import CaTTExp.Binder.Signature
  open Signature 𝕊 using (bside)

  des-valid : ∀ k n → T (bside (des k (suc n)) 0 ε)
  des-valid k n =
    ∧T (honest-step n (minv ∷ []) (honest-diskD n))
       (∧T (subst (λ j → T (scTy? (suc (suc j)) (tyH (des k (suc n)) 0))) (sym (lenD n)) (sc-res k n))
           (lc-res k n))

------------------------------------------------------------------------
-- Suspension: a destructor at dimension n suspends to the destructor
-- of the same kind at dimension n + 1.

canΣD : DesF → Nat → Bool
canΣD = okD

sHD : DesF → Nat → DesF
sHD (des k n) _ = des k (suc n)

sYD : DesF → Nat → Nat
sYD _ _ = 0

module _ (mark : Ctx → BM.Mark → Tm → Bool) where
  open Laws 𝕊₀ desSpec using (𝕊)
  open import CaTTExp.Binder.Suspension 𝕊 mark canΣD sHD sYD
  open import CaTTExp.Binder.SpecSusp 𝕊₀ desSpec

  private
    ΣtyD : ∀ n → Σty (tyD n) ≡ tyD (suc n)
    ΣtyD zero    = refl
    ΣtyD (suc n) rewrite ΣtyD n | +-suc n n = refl

    ΣdiskD : ∀ n → Σctx (diskD n) ≡ diskD (suc n)
    ΣdiskD zero    = refl
    ΣdiskD (suc n) rewrite ΣdiskD n | ΣtyD n | ΣtyD (suc n) | +-suc n n = refl

    Σfresh : ∀ k → Σsub (fresh 0 k) ≡ fresh 0 (suc (suc k))
    Σfresh zero    = refl
    Σfresh (suc k) rewrite Σfresh k = refl

    ΣcompPC : ∀ n m → Σctx (compPCM n m) ≡ compPCM (suc n) (suc (suc m))
    ΣcompPC n m rewrite ΣdiskD (suc n) | ΣtyD n | +-suc n n = refl

    ΣtyL : ∀ n m → Σty (tyL n m) ≡ tyL (suc n) (suc (suc m))
    ΣtyL n m rewrite ΣtyD n = refl

    ΣunitL : ∀ n m → Σty (unitLT n m) ≡ unitLT (suc n) (suc (suc m))
    ΣunitL n m rewrite ΣtyD n | ΣcompPC n m | ΣdiskD n | Σfresh m | Σfresh (3 + m) | +-suc n n = refl

    ΣunitR : ∀ n m → Σty (unitRT n m) ≡ unitRT (suc n) (suc (suc m))
    ΣunitR n m rewrite ΣtyD n | ΣcompPC n m | ΣdiskD n | Σfresh m | Σfresh (3 + m) | +-suc n n = refl

    at : ∀ {F : Nat → Ty} n → F (suc (suc (n + n))) ≡ F (suc n + suc n)
    at {F} n = cong F (sym (dd-suc n))

    sok-tyD : ∀ n → T (sokTy (tyD n))
    sok-tyD zero    = tt
    sok-tyD (suc n) = ∧T (sok-tyD n) tt

    sok-diskD : ∀ n → T (sokCtx (diskD n))
    sok-diskD zero    = tt
    sok-diskD (suc n) = ∧T (∧T (sok-diskD n) (sok-tyD n)) (sok-tyD (suc n))

    sok-fresh : ∀ k → T (sokSub (fresh 0 k))
    sok-fresh zero    = tt
    sok-fresh (suc k) = ∧T (sok-fresh k) tt

    sok-compPC : ∀ n m → T (sokCtx (compPCM n m))
    sok-compPC n m = ∧T (∧T (sok-diskD (suc n)) (sok-tyD n)) (∧T (sok-tyD n) tt)

    sok-body : ∀ n m → T (sokTy (arr (tyD n) (var m) (var (3 + m))))
    sok-body n m = ∧T (sok-tyD n) tt

    sok-idc : ∀ n m → T (sokTy (arr (tyD n) (var m) (var m)))
    sok-idc n m = ∧T (sok-tyD n) tt

  des-ss : SpecSusp mark canΣD sHD sYD
  des-ss = record
    { ctx-eq  = ctx-eq
    ; ty-eq   = ty-eq
    ; hok-Σ   = λ { (des k (suc n)) y c ok → tt }
    ; sok-ctx = sok-ctx
    ; sok-ty  = sok-ty
    }
    where
    ctx-eq : ∀ h y → T (canΣD h y) → T (okD h y) → ctxD (sHD h y) (sYD h y) ≡ Σctx (ctxD h y)
    ctx-eq (des k (suc n)) y _ _ rewrite ΣdiskD n | ΣtyD n | ΣtyD (suc n) | +-suc n n = refl

    ty-eq : ∀ h y → T (canΣD h y) → T (okD h y) → tyH (sHD h y) (sYD h y) ≡ Σty (tyH h y)
    ty-eq (linv (suc n))  y _ _ = sym (trans (ΣtyL n (n + n)) (at {tyL (suc n)} n))
    ty-eq (rinv (suc n))  y _ _ = sym (trans (ΣtyL n (n + n)) (at {tyL (suc n)} n))
    ty-eq (unitL (suc n)) y _ _ = sym (trans (ΣunitL n (n + n)) (at {unitLT (suc n)} n))
    ty-eq (unitR (suc n)) y _ _ = sym (trans (ΣunitR n (n + n)) (at {unitRT (suc n)} n))

    sok-ctx : ∀ h y → T (canΣD h y) → T (okD h y) → T (sokCtx (ctxD h y))
    sok-ctx (des k (suc n)) y _ _ = ∧T (∧T (sok-diskD n) (sok-tyD n)) (sok-tyD (suc n))

    sok-ty : ∀ h y → T (canΣD h y) → T (okD h y) → T (sokTy (tyH h y))
    sok-ty (linv (suc n))  y _ _ = ∧T (sok-tyD n) tt
    sok-ty (rinv (suc n))  y _ _ = ∧T (sok-tyD n) tt
    sok-ty (unitL (suc n)) y _ _ =
      let m = n + n in
      ∧T (∧T (sok-tyD n) tt)
         (∧T (∧T (sok-compPC n m) (∧T (sok-body n m)
                 (∧T (∧T (∧T (∧T (∧T (sok-fresh m) tt) tt) (sok-fresh (3 + m))) tt) tt)))
             (∧T (sok-diskD n) (∧T (sok-idc n m) (∧T (sok-fresh m) tt))))
    sok-ty (unitR (suc n)) y _ _ =
      let m = n + n in
      ∧T (∧T (sok-tyD n) tt)
         (∧T (∧T (sok-compPC n m) (∧T (sok-body n m)
                 (∧T (∧T (∧T (∧T (∧T (sok-fresh m) tt) tt) tt) tt) (sok-fresh (3 + m)))))
             (∧T (sok-diskD n) (∧T (sok-idc n m) (∧T (sok-fresh m) tt))))

  -- The kernel with DES suspends: DES satisfies the hypotheses of
  -- CaTTExp.Binder.Suspension, at every dimension.
  des-susp : HeadSusp
  des-susp = spec-susp mark canΣD sHD sYD des-ss
