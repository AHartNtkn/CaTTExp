------------------------------------------------------------------------
-- Spheres, disks and whiskers in binder syntax, with deep types
-- (ledger S26i (2); port of the parts of CaTTExp.Derived and
-- CaTTExp.DerivedBoundary that type the whiskers of naturality
-- cylinders).
--
-- The whiskers are Binder.Cyl's: rwT k j c C z h = coh BK wK (σR …)
-- and lwT, over embedded pure pasting contexts, with the iterated
-- boundaries of C read off C (baseAt, srcAt, tgtAt). They agree with
-- the sphere's positions for k < dim C (`aL-sph-k`, `src-sph`,
-- `tgt-sph`), which is what typing the classifying substitutions needs.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Pure as P
import CaTTExp.Derived as Dv
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (n<sn)
open import CaTTExp.Naturality.Raw using (Filler)

module CaTTExp.Binder.VWhisk
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark using (MarkRen; lookupₛ-top; lookupₛ-pop; ==-self)
open import CaTTExp.Binder.Subst 𝕊 side mark using (MarkSub; MarkVar)
open import CaTTExp.Binder.Deep 𝕊 side mark
open import CaTTExp.Binder.PureEmbed 𝕊 side mark
open import CaTTExp.Binder.Cyl 𝕊 (λ _ _ _ → P.var 0)
  using (sphSub; dskSub; σR; rwT; hL; σLp; σL; lwT; baseAt; tgtAt; srcAt)
open Laws 𝕊 using (Closed; BinderLaws)

------------------------------------------------------------------------
-- Arithmetic.

private
  T≡ : ∀ {b} → T b → b ≡ true
  T≡ {true} _ = refl

  dbl-lt : ∀ k n → T (k <ℕ n) → T (suc (dbl k) <ℕ dbl n)
  dbl-lt zero    (suc n) _ = tt
  dbl-lt (suc k) (suc n) p = dbl-lt k n p

  lt-sucsuc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc (suc n))
  lt-sucsuc i n p = <-suc i (suc n) (<-suc i n p)

  dbl-le : ∀ k n → T (k <ℕ n) → T (dbl k <ℕ dbl n)
  dbl-le k n p = <-trans (dbl k) (suc (dbl k)) (dbl n) (n<sn (dbl k)) (dbl-lt k n p)

  lt-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  lt-ne zero    zero    _ ()
  lt-ne zero    (suc n) _ _ = tt
  lt-ne (suc i) zero    () _
  lt-ne (suc i) (suc n) p q = lt-ne i n p q

  eq-sound : ∀ {i n} → (i ==ℕ n) ≡ true → i ≡ n
  eq-sound {i} {n} e = ==ℕ-sound i n (subst T (sym e) tt)

  ==-suc-dim : ∀ n → (n ==ℕ suc n) ≡ false
  ==-suc-dim zero    = refl
  ==-suc-dim (suc n) = ==-suc-dim n

------------------------------------------------------------------------
-- Lookups past the top.

lk-pop : ∀ σ t i → T (i <ℕ lenₛ σ) → lookupₛ (σ ,ₛ t) i ≡ lookupₛ σ i
lk-pop σ t i p = lookupₛ-pop σ t i (<→≢ i (lenₛ σ) p)

lk-top : ∀ σ t → lookupₛ (σ ,ₛ t) (lenₛ σ) ≡ t
lk-top σ t = lookupₛ-top σ t (lenₛ σ) (==-self {lenₛ σ} refl)

------------------------------------------------------------------------
-- The generic types and spheres.

lenₛ-sph : ∀ A → lenₛ (sphSub A) ≡ dbl (dim A)
lenₛ-sph ⋆           = refl
lenₛ-sph (arr A _ _) = cong (λ n → suc (suc n)) (lenₛ-sph A)

eaL : Nat → Ty
eaL k = embTy (aL k)

sc-aL : ∀ k → T (scTy? (dbl k) (eaL k))
sc-aL zero    = tt
sc-aL (suc k) = ∧T (scTy-suc (eaL k) (scTy-suc (eaL k) (sc-aL k)))
                   (∧T (<-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))) (n<sn (suc (dbl k))))

-- aL k is scoped in the sphere of any type of dimension ≥ k.
sc-aL-in : ∀ k C → T (k <ℕ suc (dim C)) → T (scTy? (lenₛ (sphSub C)) (eaL k))
sc-aL-in k C p = subst (λ m → T (scTy? m (eaL k))) (sym (lenₛ-sph C)) (mono k (dim C) p)
  where
  mono : ∀ k n → T (k <ℕ suc n) → T (scTy? (dbl n) (eaL k))
  mono zero    zero    p = tt
  mono (suc k) zero    ()
  mono k (suc n) p with k ==ℕ suc n in e
  ... | true  = subst (λ x → T (scTy? (dbl (suc n)) (eaL x))) (sym (eq-sound {k} {suc n} e)) (sc-aL (suc n))
  ... | false = scTy-suc (eaL k) (scTy-suc (eaL k) (mono k n (lt-ne k (suc n) p e)))

-- The generic type of dimension dim A, at the sphere of A, is A.
aL-sph : ∀ A → eaL (dim A) [ sphSub A ]ty ≡ A
aL-sph ⋆           = refl
aL-sph (arr A s t)
  rewrite ext-ty (eaL (dim A)) (sphSub A ,ₛ s) t (scTy-suc (eaL (dim A)) (sc-aL-in (dim A) A (n<sn (dim A))))
        | ext-ty (eaL (dim A)) (sphSub A) s (sc-aL-in (dim A) A (n<sn (dim A)))
        | aL-sph A
        | lenₛ-sph A
        | ==-suc-dim (dbl (dim A))
        | ==-self {dbl (dim A)} refl = refl

baseAt-top : ∀ A → baseAt (dim A) A ≡ A
baseAt-top ⋆           = refl
baseAt-top (arr A s u) rewrite ==-self {dim A} refl = refl

-- Below the top, the sphere's positions are the iterated boundaries.
module _ where
  private
    sph-ext : ∀ A s u i → T (i <ℕ lenₛ (sphSub A)) → lookupₛ (sphSub (arr A s u)) i ≡ lookupₛ (sphSub A) i
    sph-ext A s u i p = trans (lk-pop (sphSub A ,ₛ s) u i (<-suc i (lenₛ (sphSub A)) p)) (lk-pop (sphSub A) s i p)

  Agree : Nat → Ty → Set
  Agree k C = (eaL k [ sphSub C ]ty ≡ baseAt k C) ×
              (lookupₛ (sphSub C) (dbl k) ≡ srcAt k C) ×
              (lookupₛ (sphSub C) (suc (dbl k)) ≡ tgtAt k C)

  agree-top : ∀ A s u → Agree (dim A) (arr A s u)
  agree-top A s u
    rewrite ==-suc-dim (dim A) | ==-self {dim A} refl | baseAt-top A =
    ( trans (ext-ty (eaL (dim A)) (sphSub A ,ₛ s) u (scTy-suc (eaL (dim A)) sc))
       (trans (ext-ty (eaL (dim A)) (sphSub A) s sc) (aL-sph A))
    , trans (cong (lookupₛ (sphSub A ,ₛ s ,ₛ u)) (sym (lenₛ-sph A)))
        (trans (lk-pop (sphSub A ,ₛ s) u (lenₛ (sphSub A)) (n<sn (lenₛ (sphSub A)))) (lk-top (sphSub A) s))
    , trans (cong (λ m → lookupₛ (sphSub A ,ₛ s ,ₛ u) (suc m)) (sym (lenₛ-sph A))) (lk-top (sphSub A ,ₛ s) u) )
    where sc = sc-aL-in (dim A) A (n<sn (dim A))

  mutual
    sph-agree : ∀ k C → T (k <ℕ dim C) → Agree k C
    sph-agree k (arr A s u) p = go (k ==ℕ dim A) refl
      where
      go : ∀ b → (k ==ℕ dim A) ≡ b → Agree k (arr A s u)
      go true  e = subst (λ x → Agree x (arr A s u)) (sym (eq-sound e)) (agree-top A s u)
      go false e = agree-low k A s u (lt-ne k (dim A) p e) e

    agree-low : ∀ k A s u → T (k <ℕ dim A) → (k ==ℕ dim A) ≡ false → Agree k (arr A s u)
    agree-low k A s u q e
      rewrite e | <→≢ k (suc (dim A)) (<-suc k (dim A) q) =
      let (ih₁ , ih₂ , ih₃) = sph-agree k A q
          lq₀ = subst (λ m → T (dbl k <ℕ m)) (sym (lenₛ-sph A)) (dbl-le k (dim A) q)
          lq₁ = subst (λ m → T (suc (dbl k) <ℕ m)) (sym (lenₛ-sph A)) (dbl-lt k (dim A) q)
          sc = sc-aL-in k A (<-suc k (dim A) q)
      in ( trans (ext-ty (eaL k) (sphSub A ,ₛ s) u (scTy-suc (eaL k) sc))
             (trans (ext-ty (eaL k) (sphSub A) s sc) ih₁)
         , trans (sph-ext A s u (dbl k) lq₀) ih₂
         , trans (sph-ext A s u (suc (dbl k)) lq₁) ih₃ )

------------------------------------------------------------------------
-- Spheres and disks are typed by deep types.

module Typed (closed : Closed) (laws : BinderLaws) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where

  sph-wf : ∀ {Γ} A → DTy Γ A → Γ ⊢sub sphSub A ∶ embCtx (Dv.Sph (dim A))
  sph-wf ⋆           w             = ⟨⟩-wf w
  sph-wf {Γ} (arr A s t) (a , ds , dt) =
    ,-wf (,-wf (sph-wf A a) (subst (Γ ⊢tm s ∶_) (sym (aL-sph A)) ds) tt)
         (subst (Γ ⊢tm t ∶_)
           (sym (trans (ext-ty (eaL (dim A)) (sphSub A) s (sc-aL-in (dim A) A (n<sn (dim A)))) (aL-sph A))) dt)
         tt

  dsk-wf : ∀ {Γ c} C → DTm Γ c C → Γ ⊢sub dskSub c C ∶ embCtx (Dv.Dsk (dim C))
  dsk-wf {Γ} {c} C (d , a) = ,-wf (sph-wf C a) (subst (Γ ⊢tm c ∶_) (sym (aL-sph C)) d) tt
