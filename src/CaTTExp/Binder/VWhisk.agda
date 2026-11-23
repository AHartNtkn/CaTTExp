------------------------------------------------------------------------
-- Spheres, disks and whiskers in binder syntax, with deep types
-- (ledger S26i (2); port of the parts of CaTTExp.Derived and
-- CaTTExp.DerivedBoundary that type the whiskers of naturality
-- cylinders).
--
-- The whiskers are Binder.Cyl's: rwT k j c C z h = coh BK wK (σR …)
-- and lwT, over embedded pure pasting contexts, with the iterated
-- boundaries of C read off C (baseAt, srcAt, tgtAt). They agree with
-- the sphere's positions for k < dim C (`sph-agree`), which is what
-- typing the classifying substitutions needs.
-- Typed (with deep types): spheres, disks, σR, σL, rwT, lwT; and the
-- types of the whiskers (rwT-ty0, rwT-ty, lwT-ty0, lwT-ty).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Pure as P
import CaTTExp.Derived as Dv
import CaTTExp.DerivedBoundary as DB
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (n<sn)
open import CaTTExp.Naturality.Raw using (Filler)

module CaTTExp.Binder.VWhisk
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  (KF : Filler)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark using (MarkRen; lookupₛ-top; lookupₛ-pop; ==-self)
open import CaTTExp.Binder.Subst 𝕊 side mark using (MarkSub; MarkVar)
open import CaTTExp.Binder.Deep 𝕊 side mark
open import CaTTExp.Binder.PureEmbed 𝕊 side mark
open import CaTTExp.Binder.Cyl 𝕊 KF
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
-- Pure scoping, spheres and dimensions, embedded.

import CaTTExp.Subst P.∅ P.cattSide as Sb

mutual
  sc-embTy : ∀ n A → Sb.ScTy n A → T (scTy? n (embTy A))
  sc-embTy n P.⋆           _           = tt
  sc-embTy n (P.arr A t u) (a , b , c) = ∧T (sc-embTy n A a) (∧T (sc-embTm n t b) (sc-embTm n u c))

  sc-embTm : ∀ n t → Sb.ScTm n t → T (scTm? n (embTm t))
  sc-embTm n (P.var i)     p = p
  sc-embTm n (P.coh _ _ σ) p = sc-embSub n σ p
  sc-embTm n (P.cst ())    _

  sc-embSub : ∀ n σ → Sb.ScSub n σ → T (scSub? n (embSub σ))
  sc-embSub n P.⟨⟩       _       = tt
  sc-embSub n (σ P.,ₛ t) (a , b) = ∧T (sc-embSub n σ a) (sc-embTm n t b)

emb-sph : ∀ A → embSub (Dv.sphSub A) ≡ sphSub (embTy A)
emb-sph P.⋆           = refl
emb-sph (P.arr A s t) = cong (λ σ → σ ,ₛ embTm s ,ₛ embTm t) (emb-sph A)

private
  arr≡ : ∀ {A A' s s' t t'} → A ≡ A' → s ≡ s' → t ≡ t' → arr A s t ≡ arr A' s' t'
  arr≡ refl refl refl = refl

-- The classifying substitution of a sphere, composed.
sph∘ : ∀ A τ → (∀ i → T (i <ℕ dbl (dim A)) → lookupₛ τ i ≡ lookupₛ (sphSub A) i) →
       sphSub (eaL (dim A)) ∘ τ ≡ sphSub A
sph∘ ⋆           τ h = refl
sph∘ (arr A s t) τ h =
  cong₂ _,ₛ_ (cong₂ _,ₛ_ (sph∘ A τ h') (trans (h (dbl (dim A)) p₁) e₁))
             (trans (h (suc (dbl (dim A))) p₂) e₂)
  where
  L = lenₛ (sphSub A)
  lA : L ≡ dbl (dim A)
  lA = lenₛ-sph A
  p₂ : T (suc (dbl (dim A)) <ℕ dbl (suc (dim A)))
  p₂ = n<sn (suc (dbl (dim A)))
  p₁ : T (dbl (dim A) <ℕ dbl (suc (dim A)))
  p₁ = <-suc (dbl (dim A)) (suc (dbl (dim A))) (n<sn (dbl (dim A)))
  e₂ : lookupₛ (sphSub A ,ₛ s ,ₛ t) (suc (dbl (dim A))) ≡ t
  e₂ = subst (λ m → lookupₛ (sphSub A ,ₛ s ,ₛ t) (suc m) ≡ t) lA (lk-top (sphSub A ,ₛ s) t)
  e₁ : lookupₛ (sphSub A ,ₛ s ,ₛ t) (dbl (dim A)) ≡ s
  e₁ = subst (λ m → lookupₛ (sphSub A ,ₛ s ,ₛ t) m ≡ s) lA
         (trans (lk-pop (sphSub A ,ₛ s) t L (n<sn L)) (lk-top (sphSub A) s))
  h' : ∀ i → T (i <ℕ dbl (dim A)) → lookupₛ τ i ≡ lookupₛ (sphSub A) i
  h' i p = trans (h i (lt-sucsuc i (dbl (dim A)) p))
             (trans (lk-pop (sphSub A ,ₛ s) t i (<-suc i L q)) (lk-pop (sphSub A) s i q))
    where q = subst (λ m → T (i <ℕ m)) (sym lA) p

------------------------------------------------------------------------
-- Right whiskers c ▹ₖ h = rwT k j c C z h: the classifying
-- substitution σR c C z h, read through the agreement lemma.

module LkσR (k j : Nat) (c : Tm) (C : Ty) (z h : Tm) (e : dim C ≡ Dv.nB k j) where
  σ = σR c C z h
  L = lenₛ (sphSub C)

  lC : L ≡ dbl (Dv.nB k j)
  lC = trans (lenₛ-sph C) (cong dbl e)

  kC : T (k <ℕ dim C)
  kC = subst (λ m → T (k <ℕ m)) (sym e) (Dv.k<n j k)

  sc : T (scTy? L (eaL k))
  sc = sc-aL-in k C (<-suc k (dim C) kC)

  ag : Agree k C
  ag = sph-agree k C kC

  q₀ : T (dbl k <ℕ L)
  q₀ = subst (λ m → T (dbl k <ℕ m)) (sym (lenₛ-sph C)) (dbl-le k (dim C) kC)

  q₁ : T (suc (dbl k) <ℕ L)
  q₁ = subst (λ m → T (suc (dbl k) <ℕ m)) (sym (lenₛ-sph C)) (dbl-lt k (dim C) kC)

  lk-σR-low : ∀ i → T (i <ℕ L) → lookupₛ σ i ≡ lookupₛ (sphSub C) i
  lk-σR-low i p =
    trans (lk-pop (sphSub C ,ₛ c ,ₛ z) h i (<-suc i (suc L) (<-suc i L p)))
    (trans (lk-pop (sphSub C ,ₛ c) z i (<-suc i L p)) (lk-pop (sphSub C) c i p))

  lk-σR-z : lookupₛ σ (Dv.zK k j) ≡ z
  lk-σR-z = subst (λ m → lookupₛ σ (suc m) ≡ z) lC
    (trans (lk-pop (sphSub C ,ₛ c ,ₛ z) h (suc L) (n<sn (suc L))) (lk-top (sphSub C ,ₛ c) z))

  lk-σR-h : lookupₛ σ (suc (Dv.zK k j)) ≡ h
  lk-σR-h = subst (λ m → lookupₛ σ (suc (suc m)) ≡ h) lC (lk-top (sphSub C ,ₛ c ,ₛ z) h)

  lk-σR-src : lookupₛ σ (dbl k) ≡ srcAt k C
  lk-σR-src = trans (lk-σR-low (dbl k) q₀) (fst (snd ag))

  dsk-aL : eaL k [ dskSub c C ]ty ≡ baseAt k C
  dsk-aL = trans (ext-ty (eaL k) (sphSub C) c sc) (fst ag)

  σR-aL : eaL k [ σ ]ty ≡ baseAt k C
  σR-aL = trans (ext-ty (eaL k) (sphSub C ,ₛ c ,ₛ z) h (scTy-suc (eaL k) (scTy-suc (eaL k) sc)))
          (trans (ext-ty (eaL k) (sphSub C ,ₛ c) z (scTy-suc (eaL k) sc)) dsk-aL)

  -- The type of the whiskering cell h, at the disk extended by z.
  hTy-σ : embTy (Dv.hTy k j) [ dskSub c C ,ₛ z ]ty ≡ arr (baseAt k C) (tgtAt k C) z
  hTy-σ =
    arr≡ (trans (ext-ty (eaL k) (sphSub C ,ₛ c) z (scTy-suc (eaL k) sc)) dsk-aL)
         (trans (lk-pop (sphSub C ,ₛ c) z (suc (dbl k)) (<-suc (suc (dbl k)) L q₁))
           (trans (lk-pop (sphSub C) c (suc (dbl k)) q₁) (snd (snd ag))))
         (subst (λ m → lookupₛ (sphSub C ,ₛ c ,ₛ z) (suc m) ≡ z) lC (lk-top (sphSub C ,ₛ c) z))

-- For j = 0: c ;ₖ h goes from s_k c to z.
rwT-ty0 : ∀ k c C z h → dim C ≡ Dv.nB k 0 →
          embTy (Dv.wK k 0) [ σR c C z h ]ty ≡ arr (baseAt k C) (srcAt k C) z
rwT-ty0 k c C z h e = arr≡ σR-aL lk-σR-src lk-σR-z
  where open LkσR k 0 c C z h e

-- For j ≥ 1 and c : s → t: c ▹ₖ h : (s ▹ₖ h) → (t ▹ₖ h).
rwT-ty : ∀ k j c C' s t z h → dim C' ≡ Dv.nB k j →
         embTy (Dv.wK k (suc j)) [ σR c (arr C' s t) z h ]ty
           ≡ arr (embTy (Dv.wK k j) [ σR s C' z h ]ty) (rwT k j s C' z h) (rwT k j t C' z h)
rwT-ty k j c C' s t z h e =
  arr≡ (trans (cong (_[ σ ]ty) (emb-[]ty (Dv.wK k j) (Dv.ρsK k j)))
         (trans (assoc-ty (embTy (Dv.wK k j)) (embSub (Dv.ρsK k j)) σ (scρ (dbl n)))
                (cong (embTy (Dv.wK k j) [_]ty) (ρ∘ (dbl n) s lk-s))))
       (cong (coh (embCtx (Dv.BK k j)) (embTy (Dv.wK k j))) (ρ∘ (dbl n) s lk-s))
       (cong (coh (embCtx (Dv.BK k j)) (embTy (Dv.wK k j))) (ρ∘ (suc (dbl n)) t lk-t))
  where
  n  = Dv.nB k j
  C  = arr C' s t
  σ  = σR c C z h
  e' : dim C ≡ Dv.nB k (suc j)
  e' = cong suc e
  module M = LkσR k (suc j) c C z h e'
  scρ : ∀ v → T (scTy? (lenₛ (embSub (Dv.ρK k j v))) (embTy (Dv.wK k j)))
  scρ v = subst (λ m → T (scTy? m (embTy (Dv.wK k j)))) (sym (lenₛ-emb (Dv.ρK k j v)))
            (sc-embTy _ (Dv.wK k j) (Dv.sc-ρK k j v (Sb.ty-sc Dv.closed (Dv.wK-wf k j))))
  L' = lenₛ (sphSub C')
  lC' : L' ≡ dbl n
  lC' = trans (lenₛ-sph C') (cong dbl e)
  low : ∀ i → T (i <ℕ dbl (dim C')) → lookupₛ σ i ≡ lookupₛ (sphSub C') i
  low i p = trans (M.lk-σR-low i (<-suc i (suc L') (<-suc i L' q)))
                  (trans (lk-pop (sphSub C' ,ₛ s) t i (<-suc i L' q)) (lk-pop (sphSub C') s i q))
    where q = subst (λ m → T (i <ℕ m)) (sym (lenₛ-sph C')) p
  lk-s : lookupₛ σ (dbl n) ≡ s
  lk-s = trans (M.lk-σR-low (dbl n)
                  (subst (λ m → T (dbl n <ℕ suc (suc m))) (sym lC') (<-suc (dbl n) (suc (dbl n)) (n<sn (dbl n)))))
               (subst (λ m → lookupₛ (sphSub C) m ≡ s) lC'
                  (trans (lk-pop (sphSub C' ,ₛ s) t L' (n<sn L')) (lk-top (sphSub C') s)))
  lk-t : lookupₛ σ (suc (dbl n)) ≡ t
  lk-t = trans (M.lk-σR-low (suc (dbl n))
                  (subst (λ m → T (suc (dbl n) <ℕ suc (suc m))) (sym lC') (n<sn (suc (dbl n)))))
               (subst (λ m → lookupₛ (sphSub C) (suc m) ≡ t) lC' (lk-top (sphSub C' ,ₛ s) t))
  sph : embSub (Dv.sphSub (aL n)) ∘ σ ≡ sphSub C'
  sph = trans (cong (_∘ σ) (emb-sph (aL n)))
              (subst (λ m → sphSub (eaL m) ∘ σ ≡ sphSub C') e (sph∘ C' σ low))
  ρ∘ : ∀ v u → lookupₛ σ v ≡ u → embSub (Dv.ρK k j v) ∘ σ ≡ σR u C' z h
  ρ∘ v u lv = cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ sph lv) M.lk-σR-z) M.lk-σR-h

------------------------------------------------------------------------
-- Boundaries of a cell type, read off it.

baseAt-arr : ∀ k C' s t → T (k <ℕ dim C') → baseAt k (arr C' s t) ≡ baseAt k C'
baseAt-arr k C' s t p rewrite <→≢ k (suc (dim C')) (<-suc k (dim C') p) = refl

srcAt-arr : ∀ k C' s t → T (k <ℕ dim C') → srcAt k (arr C' s t) ≡ srcAt k C'
srcAt-arr k C' s t p rewrite <→≢ k (dim C') p = refl

tgtAt-arr : ∀ k C' s t → T (k <ℕ dim C') → tgtAt k (arr C' s t) ≡ tgtAt k C'
tgtAt-arr k C' s t p rewrite <→≢ k (dim C') p = refl

-- A cell type of dimension k+1 is (its k-type, k-source, k-target).
C-sph : ∀ k C → dim C ≡ suc k → arr (baseAt k C) (srcAt k C) (tgtAt k C) ≡ C
C-sph k (arr C₀ s₀ t₀) refl
  rewrite ==-suc-dim (dim C₀) | ==-self {dim C₀} refl | baseAt-top C₀ = refl

dim-baseAt : ∀ k A → T (k <ℕ suc (dim A)) → dim (baseAt k A) ≡ k
dim-baseAt k ⋆           p = le0 k p
  where le0 : ∀ k → T (k <ℕ 1) → 0 ≡ k
        le0 zero _ = refl
        le0 (suc k) ()
dim-baseAt k (arr A s u) p with k ==ℕ suc (dim A) in e
... | true  = sym (eq-sound e)
... | false = dim-baseAt k A (lt-ne k (suc (dim A)) p e)

kC-of : ∀ k j C → dim C ≡ Dv.nB k j → T (k <ℕ dim C)
kC-of k j C e = subst (λ m → T (k <ℕ m)) (sym e) (Dv.k<n j k)

------------------------------------------------------------------------
-- Left whiskers h ◃ₖ c = lwT k j h x c C.

-- The sphere of h's type, extended.
module LkσL (k : Nat) (h x : Tm) (C : Ty) (kC : T (k <ℕ dim C)) where
  Bk = baseAt k C
  S = sphSub Bk

  dB : dim Bk ≡ k
  dB = dim-baseAt k C (<-suc k (dim C) kC)

  lS : lenₛ S ≡ dbl k
  lS = trans (lenₛ-sph Bk) (cong dbl dB)

  sc : T (scTy? (lenₛ S) (eaL k))
  sc = sc-aL-in k Bk (subst (λ m → T (k <ℕ suc m)) (sym dB) (n<sn k))

  Q = S ,ₛ x ,ₛ srcAt k C ,ₛ h

  sc₃ : T (scTy? (lenₛ Q) (eaL k))
  sc₃ = scTy-suc (eaL k) (scTy-suc (eaL k) (scTy-suc (eaL k) sc))

  aL-Q : eaL k [ Q ]ty ≡ Bk
  aL-Q = trans (ext-ty (eaL k) (S ,ₛ x ,ₛ srcAt k C) h (scTy-suc (eaL k) (scTy-suc (eaL k) sc)))
         (trans (ext-ty (eaL k) (S ,ₛ x) (srcAt k C) (scTy-suc (eaL k) sc))
         (trans (ext-ty (eaL k) S x sc)
                (subst (λ m → eaL m [ S ]ty ≡ Bk) dB (aL-sph Bk))))

  lk-x : ∀ u v → lookupₛ (Q ,ₛ u ,ₛ v) (dbl k) ≡ x
  lk-x u v = subst (λ m → lookupₛ (Q ,ₛ u ,ₛ v) m ≡ x) lS
    (trans (lk-pop (Q ,ₛ u) v L (<-suc L (suc (suc (suc L))) (<-suc L (suc (suc L)) (<-suc L (suc L) (n<sn L)))))
    (trans (lk-pop Q u L (<-suc L (suc (suc L)) (<-suc L (suc L) (n<sn L))))
    (trans (lk-pop (S ,ₛ x ,ₛ srcAt k C) h L (<-suc L (suc L) (n<sn L)))
    (trans (lk-pop (S ,ₛ x) (srcAt k C) L (n<sn L))
           (lk-top S x)))))
    where L = lenₛ S

  lk-src : ∀ u → lookupₛ (Q ,ₛ u) (suc (dbl k)) ≡ srcAt k C
  lk-src u = subst (λ m → lookupₛ (Q ,ₛ u) (suc m) ≡ srcAt k C) lS
    (trans (lk-pop Q u (suc L) (<-suc (suc L) (suc (suc L)) (n<sn (suc L))))
    (trans (lk-pop (S ,ₛ x ,ₛ srcAt k C) h (suc L) (n<sn (suc L)))
           (lk-top (S ,ₛ x) (srcAt k C))))
    where L = lenₛ S

  lk-tgt : ∀ u → lookupₛ (Q ,ₛ tgtAt k C ,ₛ u) (suc (suc (suc (dbl k)))) ≡ tgtAt k C
  lk-tgt u = subst (λ m → lookupₛ (Q ,ₛ tgtAt k C ,ₛ u) (suc (suc (suc m))) ≡ tgtAt k C) lS
    (trans (lk-pop (Q ,ₛ tgtAt k C) u (lenₛ Q) (n<sn (lenₛ Q))) (lk-top Q (tgtAt k C)))

  lk-tgt' : lookupₛ (Q ,ₛ tgtAt k C) (suc (suc (suc (dbl k)))) ≡ tgtAt k C
  lk-tgt' = subst (λ m → lookupₛ (Q ,ₛ tgtAt k C) (suc (suc (suc m))) ≡ tgtAt k C) lS
    (lk-top Q (tgtAt k C))

lenₛ-σLp : ∀ k j h x C → dim C ≡ Dv.nB k j → lenₛ (σLp k j h x C) ≡ Dv.tL k j
lenₛ-σLp k zero    h x C            e =
  cong (λ m → suc (suc (suc (suc m)))) (LkσL.lS k h x C (kC-of k 0 C e))
lenₛ-σLp k (suc j) h x (arr C' s t) e = cong (λ m → suc (suc m)) (lenₛ-σLp k j h x C' (cong pred e))
  where pred : Nat → Nat
        pred zero = zero
        pred (suc n) = n

sc-bLK : ∀ k j → T (scTy? (Dv.tL k j) (embTy (Dv.bLK k (suc j))))
sc-bLK k j = sc-embTy _ (Dv.bLK k (suc j)) (DB.sc-bLK k j)

-- Under σLp, the generic type of the top cell of LK k j is C.
bLK-σLp : ∀ k j h x C → dim C ≡ Dv.nB k j → embTy (Dv.bLK k (suc j)) [ σLp k j h x C ]ty ≡ C
bLK-σLp k zero h x C e =
  trans (arr≡ (trans (ext-ty (eaL k) Q (tgtAt k C) sc₃) aL-Q) (lk-src (tgtAt k C)) lk-tgt')
        (C-sph k C e)
  where open LkσL k h x C (kC-of k 0 C e)
bLK-σLp k (suc j) h x (arr C' s t) e =
  arr≡ (trans (ext-ty (embTy (Dv.bLK k (suc j))) (Pp ,ₛ s) t (scTy-suc (embTy (Dv.bLK k (suc j))) sc))
       (trans (ext-ty (embTy (Dv.bLK k (suc j))) Pp s sc) (bLK-σLp k j h x C' e')))
       (subst (λ m → lookupₛ (Pp ,ₛ s ,ₛ t) m ≡ s) lP
          (trans (lk-pop (Pp ,ₛ s) t (lenₛ Pp) (n<sn (lenₛ Pp))) (lk-top Pp s)))
       (subst (λ m → lookupₛ (Pp ,ₛ s ,ₛ t) (suc m) ≡ t) lP (lk-top (Pp ,ₛ s) t))
  where
  e' : dim C' ≡ Dv.nB k j
  e' = suc-inj e
    where suc-inj : ∀ {a b : Nat} → suc a ≡ suc b → a ≡ b
          suc-inj refl = refl
  Pp = σLp k j h x C'
  lP : lenₛ Pp ≡ Dv.tL k j
  lP = lenₛ-σLp k j h x C' e'
  sc : T (scTy? (lenₛ Pp) (embTy (Dv.bLK k (suc j))))
  sc = subst (λ m → T (scTy? m (embTy (Dv.bLK k (suc j))))) (sym lP) (sc-bLK k j)

-- For j = 0: h ;ₖ c goes from x to t_k c.
lwT-ty0 : ∀ k h x c C → dim C ≡ Dv.nB k 0 →
          embTy (Dv.lK k 0) [ σL k 0 h x c C ]ty ≡ arr (baseAt k C) x (tgtAt k C)
lwT-ty0 k h x c C e =
  arr≡ (trans (ext-ty (eaL k) (Q ,ₛ tgtAt k C) c (scTy-suc (eaL k) sc₃))
       (trans (ext-ty (eaL k) Q (tgtAt k C) sc₃) aL-Q))
       (lk-x (tgtAt k C) c) (lk-tgt c)
  where open LkσL k h x C (kC-of k 0 C e)

-- The identity on a prefix, composed.
eidS∘ : ∀ ρ τ → (∀ i → T (i <ℕ lenₛ ρ) → lookupₛ τ i ≡ lookupₛ ρ i) → embSub (Dv.idS (lenₛ ρ)) ∘ τ ≡ ρ
eidS∘ ⟨⟩       τ h = refl
eidS∘ (ρ ,ₛ u) τ h =
  cong₂ _,ₛ_ (eidS∘ ρ τ (λ i p → trans (h i (<-suc i (lenₛ ρ) p)) (lk-pop ρ u i p)))
             (trans (h (lenₛ ρ) (n<sn (lenₛ ρ))) (lk-top ρ u))

-- For j ≥ 1 and c : s → t: h ◃ₖ c : (h ◃ₖ s) → (h ◃ₖ t).
lwT-ty : ∀ k j h x c C' s t → dim C' ≡ Dv.nB k j →
         embTy (Dv.lK k (suc j)) [ σL k (suc j) h x c (arr C' s t) ]ty
           ≡ arr (embTy (Dv.lK k j) [ σL k j h x s C' ]ty) (lwT k j h x s C') (lwT k j h x t C')
lwT-ty k j h x c C' s t e =
  arr≡ (trans (cong (_[ σ ]ty) (emb-[]ty (Dv.lK k j) (Dv.λsK k j)))
         (trans (assoc-ty (embTy (Dv.lK k j)) (embSub (Dv.λsK k j)) σ scλ)
                (cong (embTy (Dv.lK k j) [_]ty) λs∘)))
       (cong (coh (embCtx (Dv.LK k j)) (embTy (Dv.lK k j))) λs∘)
       (cong (coh (embCtx (Dv.LK k j)) (embTy (Dv.lK k j))) λt∘)
  where
  Pp = σLp k j h x C'
  σ = σL k (suc j) h x c (arr C' s t)
  lP : lenₛ Pp ≡ Dv.tL k j
  lP = lenₛ-σLp k j h x C' e
  scλ : T (scTy? (lenₛ (embSub (Dv.λsK k j))) (embTy (Dv.lK k j)))
  scλ = subst (λ m → T (scTy? m (embTy (Dv.lK k j)))) (sym (lenₛ-emb (Dv.λsK k j)))
          (sc-embTy _ (Dv.lK k j)
            (subst (λ n → Sb.ScTy n (Dv.lK k j)) (sym (Dv.lenλs k j)) (Sb.ty-sc Dv.closed (Dv.lK-wf k j))))
  λs∘ : embSub (Dv.λsK k j) ∘ σ ≡ Pp ,ₛ s
  λs∘ = subst (λ m → embSub (Dv.idS (suc m)) ∘ σ ≡ Pp ,ₛ s) lP
          (eidS∘ (Pp ,ₛ s) σ (λ i p → trans (lk-pop (Pp ,ₛ s ,ₛ t) c i (<-suc i (suc (lenₛ Pp)) p))
                                           (lk-pop (Pp ,ₛ s) t i p)))
  lt : lookupₛ σ (suc (lenₛ Pp)) ≡ t
  lt = trans (lk-pop (Pp ,ₛ s ,ₛ t) c (suc (lenₛ Pp)) (n<sn (suc (lenₛ Pp)))) (lk-top (Pp ,ₛ s) t)
  λt∘ : embSub (Dv.λtK k j) ∘ σ ≡ Pp ,ₛ t
  λt∘ = subst (λ m → (embSub (Dv.idS m) ∘ σ) ,ₛ lookupₛ σ (suc m) ≡ Pp ,ₛ t) lP
          (cong₂ _,ₛ_ (eidS∘ Pp σ (λ i p → trans (lk-pop (Pp ,ₛ s ,ₛ t) c i (<-suc i (suc (lenₛ Pp)) (<-suc i (lenₛ Pp) p)))
                                            (trans (lk-pop (Pp ,ₛ s) t i (<-suc i (lenₛ Pp) p)) (lk-pop Pp s i p))))
                      lt)

------------------------------------------------------------------------
-- Spheres and disks are typed by deep types.

module Typed (closed : Closed) (laws : BinderLaws) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar)
             (sp : SidePure) where

  sph-wf : ∀ {Γ} A → DTy Γ A → Γ ⊢sub sphSub A ∶ embCtx (Dv.Sph (dim A))
  sph-wf ⋆           w             = ⟨⟩-wf w
  sph-wf {Γ} (arr A s t) (a , ds , dt) =
    ,-wf (,-wf (sph-wf A a) (subst (Γ ⊢tm s ∶_) (sym (aL-sph A)) ds) tt)
         (subst (Γ ⊢tm t ∶_)
           (sym (trans (ext-ty (eaL (dim A)) (sphSub A) s (sc-aL-in (dim A) A (n<sn (dim A)))) (aL-sph A))) dt)
         tt

  dsk-wf : ∀ {Γ c} C → DTm Γ c C → Γ ⊢sub dskSub c C ∶ embCtx (Dv.Dsk (dim C))
  dsk-wf {Γ} {c} C (d , a) = ,-wf (sph-wf C a) (subst (Γ ⊢tm c ∶_) (sym (aL-sph C)) d) tt

  -- The classifying substitution of a right whisker.
  σR-wf : ∀ k j {Γ c C z h} → dim C ≡ Dv.nB k j → DTm Γ c C →
          DTm Γ h (arr (baseAt k C) (tgtAt k C) z) →
          Γ ⊢sub σR c C z h ∶ embCtx (Dv.BK k j)
  σR-wf k j {Γ} {c} {C} {z} {h} e dc (dh , _ , _ , dz) =
    ,-wf (,-wf (subst (λ m → Γ ⊢sub dskSub c C ∶ embCtx (Dv.Dsk m)) e (dsk-wf C dc))
               (subst (Γ ⊢tm z ∶_) (sym dsk-aL) dz) tt)
         (subst (Γ ⊢tm h ∶_) (sym hTy-σ) dh) tt
    where open LkσR k j c C z h e

  -- c ▹ₖ h is well typed, with a deep type.
  rwT-wf : ∀ k j {Γ c C z h} → dim C ≡ Dv.nB k j → DTm Γ c C →
           DTm Γ h (arr (baseAt k C) (tgtAt k C) z) →
           DTm Γ (rwT k j c C z h) (embTy (Dv.wK k j) [ σR c C z h ]ty)
  rwT-wf k zero    e dc dh =
    dcoh closed laws mren msub mvar sp (Dv.BK-ps k 0) (Dv.wBK k 0) (Dv.wK-wf k 0) (Dv.sideK k 0)
      (σR-wf k 0 e dc dh)
  rwT-wf k (suc j) e dc dh =
    dcoh closed laws mren msub mvar sp (Dv.BK-ps k (suc j)) (Dv.wBK k (suc j)) (Dv.wK-wf k (suc j))
      (Dv.sideK k (suc j)) (σR-wf k (suc j) e dc dh)

  -- The boundaries of a deep type are deep.
  bdry-wf : ∀ {Γ} k C → T (k <ℕ dim C) → DTy Γ C →
            DTm Γ (srcAt k C) (baseAt k C) × DTm Γ (tgtAt k C) (baseAt k C)
  bdry-wf {Γ} k (arr A s u) p (a , ds , du) rewrite <→≢ k (suc (dim A)) p with k ==ℕ dim A in e
  ... | true  = subst (λ y → DTm Γ s (baseAt y A) × DTm Γ u (baseAt y A)) (sym (eq-sound {k} {dim A} e))
                  ((subst (Γ ⊢tm s ∶_) bt ds , a') , (subst (Γ ⊢tm u ∶_) bt du , a'))
    where bt = sym (baseAt-top A)
          a' = subst (DTy Γ) bt a
  ... | false = bdry-wf k A (lt-ne k (dim A) p e) a

  hL-arr : ∀ k x C' s t → T (k <ℕ dim C') → hL k x (arr C' s t) ≡ hL k x C'
  hL-arr k x C' s t p = arr≡ (baseAt-arr k C' s t p) refl (srcAt-arr k C' s t p)

  mutual
    σLp-wf : ∀ k j {Γ h x c C} → DTm Γ c C → dim C ≡ Dv.nB k j → DTm Γ h (hL k x C) →
             Γ ⊢sub σLp k j h x C ∶ embCtx (Dv.LPK k j)
    σLp-wf k zero {Γ} {h} {x} {c} {C} (_ , dC) e dh =
      ,-wf (subst (λ m → Γ ⊢sub dskSub h (hL k x C) ∶ embCtx (Dv.Dsk m)) (cong suc dB) (dsk-wf (hL k x C) dh))
           (subst (Γ ⊢tm tgtAt k C ∶_) (sym aL-Q) (fst (snd (bdry-wf k C kC dC)))) tt
      where kC = kC-of k 0 C e
            open LkσL k h x C kC
    σLp-wf k (suc j) {Γ} {h} {x} {c} {arr C' s t} (_ , a , ds , dt) e dh =
      ,-wf (σL-wf k j (ds , a) e' (subst (DTm Γ h) (hL-arr k x C' s t (kC-of k j C' e')) dh))
           (subst (Γ ⊢tm t ∶_) (sym eq) dt) tt
      where
      e' : dim C' ≡ Dv.nB k j
      e' = suc-inj e
        where suc-inj : ∀ {a b : Nat} → suc a ≡ suc b → a ≡ b
              suc-inj refl = refl
      eq : embTy (Dv.bLK k (suc j)) [ σL k j h x s C' ]ty ≡ C'
      eq = trans (ext-ty (embTy (Dv.bLK k (suc j))) (σLp k j h x C') s
                    (subst (λ m → T (scTy? m (embTy (Dv.bLK k (suc j))))) (sym (lenₛ-σLp k j h x C' e')) (sc-bLK k j)))
                 (bLK-σLp k j h x C' e')

    σL-wf : ∀ k j {Γ h x c C} → DTm Γ c C → dim C ≡ Dv.nB k j → DTm Γ h (hL k x C) →
            Γ ⊢sub σL k j h x c C ∶ embCtx (Dv.LK k j)
    σL-wf k j {Γ} {h} {x} {c} {C} dc e dh =
      ,-wf (σLp-wf k j dc e dh) (subst (Γ ⊢tm c ∶_) (sym (bLK-σLp k j h x C e)) (fst dc)) tt

  -- h ◃ₖ c is well typed, with a deep type.
  lwT-wf : ∀ k j {Γ h x c C} → DTm Γ c C → dim C ≡ Dv.nB k j → DTm Γ h (hL k x C) →
           DTm Γ (lwT k j h x c C) (embTy (Dv.lK k j) [ σL k j h x c C ]ty)
  lwT-wf k zero    dc e dh =
    dcoh closed laws mren msub mvar sp (Dv.LK-ps k 0) (Dv.wLK k 0) (Dv.lK-wf k 0) (Dv.sideLK k 0)
      (σL-wf k 0 dc e dh)
  lwT-wf k (suc j) dc e dh =
    dcoh closed laws mren msub mvar sp (Dv.LK-ps k (suc j)) (Dv.wLK k (suc j)) (Dv.lK-wf k (suc j))
      (Dv.sideLK k (suc j)) (σL-wf k (suc j) dc e dh)
