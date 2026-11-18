------------------------------------------------------------------------
-- Instantiation and boundary lemmas for the derived whiskering rules
-- of CaTTExp.Derived.
--
--   rwT k j c C z h = c ▹ₖ h  (c : C an n-cell, n = j+k+1, h : t_k c → z)
--   lwT k j h H z c C = h ◃ₖ c  (h : H a (k+1)-cell into s_k c, z = t_k c)
--
-- rwT-wf, lwT-wf: these are well typed whenever c and h are.
-- rwT-ty, lwT-ty: their types, by the boundary of c: for j ≥ 1 and
-- c : s → t,  c ▹ₖ h : (s ▹ₖ h) → (t ▹ₖ h)  and
--             h ◃ₖ c : (h ◃ₖ s) → (h ◃ₖ t);
-- for j = 0 the composite c ;ₖ h goes from s_k c to z.
------------------------------------------------------------------------
module CaTTExp.DerivedBoundary where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (sc-aL; sc-mono; dim-aL; <-suc; n<sn; <→≢; ≡-T)
open import CaTTExp.Derived

------------------------------------------------------------------------
-- The classifying substitution of a sphere, composed.

sph∘ : ∀ A τ → (∀ i → T (i <ℕ dbl (dim A)) → lookupₛ τ i ≡ lookupₛ (sphSub A) i) →
       sphSub (aL (dim A)) ∘ τ ≡ sphSub A
sph∘ ⋆           τ h = refl
sph∘ (arr A s t) τ h =
  cong₂ _,ₛ_ (cong₂ _,ₛ_ (sph∘ A τ h') (trans (h (dbl (dim A)) p₁) (e₁)))
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
         (trans (lk-ext (sphSub A ,ₛ s) t L (n<sn L)) (lk-top (sphSub A) s))
  h' : ∀ i → T (i <ℕ dbl (dim A)) → lookupₛ τ i ≡ lookupₛ (sphSub A) i
  h' i p = trans (h i (<-suc i (suc (dbl (dim A))) (<-suc i (dbl (dim A)) p)))
             (trans (lk-ext (sphSub A ,ₛ s) t i (<-suc i L q)) (lk-ext (sphSub A) s i q))
    where q = subst (λ m → T (i <ℕ m)) (sym lA) p

------------------------------------------------------------------------
-- Right whiskers of given cells.

σR : Tm → Ty → Tm → Tm → Sub
σR c C z h = dskSub c C ,ₛ z ,ₛ h

rwT : Nat → Nat → Tm → Ty → Tm → Tm → Tm
rwT k j c C z h = coh (BK k j) (wK k j) (σR c C z h)

-- The k-dimensional type and the k-target of a cell type C.
tyK : Nat → Ty → Ty
tyK k C = aL k [ sphSub C ]ty

tgtK : Nat → Ty → Tm
tgtK k C = lookupₛ (sphSub C) (suc (dbl k))

srcK : Nat → Ty → Tm
srcK k C = lookupₛ (sphSub C) (dbl k)

sc-aL-in : ∀ k j C → dim C ≡ nB k j → ScTy (lenₛ (sphSub C)) (aL k)
sc-aL-in k j C e =
  subst (λ m → ScTy m (aL k)) (sym (trans (lenₛ-sph C) (cong dbl e)))
    (sc-mono (dbl k) (dbl (nB k j)) (aL k) (dbl-mono k (nB k j) (<-suc k (nB k j) (k<n j k))) (sc-aL k))

ty-σR : ∀ k j c C z → dim C ≡ nB k j →
        hTy k j [ dskSub c C ,ₛ z ]ty ≡ arr (tyK k C) (tgtK k C) z
ty-σR k j c C z e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (trans (Sb.ext-ty (aL k) (sphSub C ,ₛ c) z (Sb.scTy-suc (aL k) sc))
           (Sb.ext-ty (aL k) (sphSub C) c sc))
    (cong₂ _,_
       (trans (lk-ext (sphSub C ,ₛ c) z (suc (dbl k)) (<-suc (suc (dbl k)) L q))
              (lk-ext (sphSub C) c (suc (dbl k)) q))
       (subst (λ m → lookupₛ (sphSub C ,ₛ c ,ₛ z) (suc m) ≡ z) lC (lk-top (sphSub C ,ₛ c) z)))
  where
  sc = sc-aL-in k j C e
  L  = lenₛ (sphSub C)
  lC : L ≡ dbl (nB k j)
  lC = trans (lenₛ-sph C) (cong dbl e)
  q : T (suc (dbl k) <ℕ L)
  q = subst (λ m → T (suc (dbl k) <ℕ m)) (sym lC)
        (lt-dbl (suc (dbl k)) (suc k) (nB k j) (n<sn (suc (dbl k))) (k<n j k))

σR-wf : ∀ k j {Γ c C z h} → Γ ⊢tm c ∶ C → dim C ≡ nB k j →
        Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z → Γ ⊢sub σR c C z h ∶ BK k j
σR-wf k j {Γ} {c} {C} {z} {h} dc e dh with tm-ty dh
... | arr-wf _ dz =
  ,-wf (,-wf (subst (λ m → Γ ⊢sub dskSub c C ∶ Dsk m) e (dsk-wf dc))
             (subst (Γ ⊢tm z ∶_) (sym (Sb.ext-ty (aL k) (sphSub C) c (sc-aL-in k j C e))) dz))
       (subst (Γ ⊢tm h ∶_) (sym (ty-σR k j c C z e)) dh)

-- c ▹ₖ h is well typed.
rwT-wf : ∀ k j {Γ c C z h} → Γ ⊢tm c ∶ C → dim C ≡ nB k j →
         Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z →
         Γ ⊢tm rwT k j c C z h ∶ wK k j [ σR c C z h ]ty
rwT-wf k j dc e dh = rwhisk k j (σR-wf k j dc e dh)

------------------------------------------------------------------------
-- The type of c ▹ₖ h.

module _ (k j : Nat) (c : Tm) (C : Ty) (z h : Tm) (e : dim C ≡ nB k j) where
  private
    σ = σR c C z h
    L = lenₛ (sphSub C)
    lC : L ≡ dbl (nB k j)
    lC = trans (lenₛ-sph C) (cong dbl e)

  lk-σR-low : ∀ i → T (i <ℕ L) → lookupₛ σ i ≡ lookupₛ (sphSub C) i
  lk-σR-low i p =
    trans (lk-ext (sphSub C ,ₛ c ,ₛ z) h i (<-suc i (suc L) (<-suc i L p)))
    (trans (lk-ext (sphSub C ,ₛ c) z i (<-suc i L p)) (lk-ext (sphSub C) c i p))

  lk-σR-c : lookupₛ σ (dbl (nB k j)) ≡ c
  lk-σR-c = subst (λ m → lookupₛ σ m ≡ c) lC
    (trans (lk-ext (sphSub C ,ₛ c ,ₛ z) h L (<-suc L (suc L) (n<sn L)))
    (trans (lk-ext (sphSub C ,ₛ c) z L (n<sn L)) (lk-top (sphSub C) c)))

  lk-σR-z : lookupₛ σ (zK k j) ≡ z
  lk-σR-z = subst (λ m → lookupₛ σ (suc m) ≡ z) lC
    (trans (lk-ext (sphSub C ,ₛ c ,ₛ z) h (suc L) (n<sn (suc L))) (lk-top (sphSub C ,ₛ c) z))

  lk-σR-h : lookupₛ σ (suc (zK k j)) ≡ h
  lk-σR-h = subst (λ m → lookupₛ σ (suc (suc m)) ≡ h) lC (lk-top (sphSub C ,ₛ c ,ₛ z) h)

  σR-aL : aL k [ σ ]ty ≡ tyK k C
  σR-aL = trans (Sb.ext-ty (aL k) (sphSub C ,ₛ c ,ₛ z) h (Sb.scTy-suc (aL k) (Sb.scTy-suc (aL k) sc)))
          (trans (Sb.ext-ty (aL k) (sphSub C ,ₛ c) z (Sb.scTy-suc (aL k) sc))
                 (Sb.ext-ty (aL k) (sphSub C) c sc))
    where sc = sc-aL-in k j C e

-- For j = 0: c ;ₖ h goes from s_k c to z.
rwT-ty0 : ∀ k c C z h → (e : dim C ≡ nB k 0) →
          wK k 0 [ σR c C z h ]ty ≡ arr (tyK k C) (srcK k C) z
rwT-ty0 k c C z h e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (σR-aL k 0 c C z h e)
    (cong₂ _,_ (lk-σR-low k 0 c C z h e (dbl k)
                  (subst (λ m → T (dbl k <ℕ m)) (sym (trans (lenₛ-sph C) (cong dbl e)))
                     (<-suc (dbl k) (suc (dbl k)) (n<sn (dbl k)))))
               (lk-σR-z k 0 c C z h e))

-- For j ≥ 1 and c : s → t: c ▹ₖ h : (s ▹ₖ h) → (t ▹ₖ h).
rwT-ty : ∀ k j c C' s t z h → dim C' ≡ nB k j →
         wK k (suc j) [ σR c (arr C' s t) z h ]ty
           ≡ arr (wK k j [ σR s C' z h ]ty) (rwT k j s C' z h) (rwT k j t C' z h)
rwT-ty k j c C' s t z h e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (trans (Sb.assoc-ty (wK k j) (ρsK k j) σ (sc-ρK k j (dbl n) sc))
           (cong (wK k j [_]ty) (ρ∘ (dbl n) s lk-s)))
    (cong₂ _,_ (cong (coh (BK k j) (wK k j)) (ρ∘ (dbl n) s lk-s))
               (cong (coh (BK k j) (wK k j)) (ρ∘ (suc (dbl n)) t lk-t)))
  where
  n  = nB k j
  C  = arr C' s t
  σ  = σR c C z h
  e' : dim C ≡ nB k (suc j)
  e' = cong suc e
  sc = Sb.ty-sc closed (wK-wf k j)
  L' = lenₛ (sphSub C')
  lC' : L' ≡ dbl n
  lC' = trans (lenₛ-sph C') (cong dbl e)
  low : ∀ i → T (i <ℕ dbl (dim C')) → lookupₛ σ i ≡ lookupₛ (sphSub C') i
  low i p = trans (lk-σR-low k (suc j) c C z h e' i (<-suc i (suc L') (<-suc i L' q)))
                  (trans (lk-ext (sphSub C' ,ₛ s) t i (<-suc i L' q)) (lk-ext (sphSub C') s i q))
    where q = subst (λ m → T (i <ℕ m)) (sym (lenₛ-sph C')) p
  lk-s : lookupₛ σ (dbl n) ≡ s
  lk-s = trans (lk-σR-low k (suc j) c C z h e' (dbl n)
                  (subst (λ m → T (dbl n <ℕ m)) (sym (cong suc (cong suc lC'))) (<-suc (dbl n) (suc (dbl n)) (n<sn (dbl n)))))
               (subst (λ m → lookupₛ (sphSub C) m ≡ s) lC'
                  (trans (lk-ext (sphSub C' ,ₛ s) t L' (n<sn L')) (lk-top (sphSub C') s)))
  lk-t : lookupₛ σ (suc (dbl n)) ≡ t
  lk-t = trans (lk-σR-low k (suc j) c C z h e' (suc (dbl n))
                  (subst (λ m → T (suc (dbl n) <ℕ m)) (sym (cong suc (cong suc lC'))) (n<sn (suc (dbl n)))))
               (subst (λ m → lookupₛ (sphSub C) (suc m) ≡ t) lC' (lk-top (sphSub C' ,ₛ s) t))
  sph : sphSub (aL n) ∘ σ ≡ sphSub C'
  sph = subst (λ m → sphSub (aL m) ∘ σ ≡ sphSub C') e (sph∘ C' σ low)
  ρ∘ : ∀ v u → lookupₛ σ v ≡ u → ρK k j v ∘ σ ≡ σR u C' z h
  ρ∘ v u lv = cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ sph lv) (lk-σR-z k (suc j) c C z h e'))
                         (lk-σR-h k (suc j) c C z h e')

------------------------------------------------------------------------
-- Left whiskers of given cells: h ◃ₖ c for c : C an n-cell
-- (n = j+k+1) and h : x → s_k c. The k-target of c plays z.

dim[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim[] ⋆           σ = refl
dim[] (arr A _ _) σ = cong suc (dim[] A σ)

dim-tyK : ∀ k C → dim (tyK k C) ≡ k
dim-tyK k C = trans (dim[] (aL k) (sphSub C)) (dim-aL k)

hL : Nat → Tm → Ty → Ty
hL k x C = arr (tyK k C) x (srcK k C)

σLp : Nat → Nat → Tm → Tm → Ty → Sub
σLp k zero    h x C            = dskSub h (hL k x C) ,ₛ tgtK k C
σLp k (suc j) h x ⋆            = ⟨⟩
σLp k (suc j) h x (arr C' s t) = σLp k j h x C' ,ₛ s ,ₛ t

σL : Nat → Nat → Tm → Tm → Tm → Ty → Sub
σL k j h x c C = σLp k j h x C ,ₛ c

lwT : Nat → Nat → Tm → Tm → Tm → Ty → Tm
lwT k j h x c C = coh (LK k j) (lK k j) (σL k j h x c C)

lenₛ-σLp : ∀ k j h x C → dim C ≡ nB k j → lenₛ (σLp k j h x C) ≡ tL k j
lenₛ-σLp k zero    h x C            e =
  cong (λ m → suc (suc (suc (suc m)))) (trans (lenₛ-sph (tyK k C)) (cong dbl (dim-tyK k C)))
lenₛ-σLp k (suc j) h x (arr C' s t) e = cong (λ m → suc (suc m)) (lenₛ-σLp k j h x C' (cong (λ m → m ∸ 1) e))

-- The k-dimensional data of C, read off its sphere.
module _ (k : Nat) where
  lowK : ∀ C' s t i → T (i <ℕ lenₛ (sphSub C')) → lookupₛ (sphSub (arr C' s t)) i ≡ lookupₛ (sphSub C') i
  lowK C' s t i p = trans (lk-ext (sphSub C' ,ₛ s) t i (<-suc i _ p)) (lk-ext (sphSub C') s i p)

  tyK-arr : ∀ C' s t → T (k <ℕ dim C') → tyK k (arr C' s t) ≡ tyK k C'
  tyK-arr C' s t p = trans (Sb.ext-ty (aL k) (sphSub C' ,ₛ s) t (Sb.scTy-suc (aL k) sc))
                           (Sb.ext-ty (aL k) (sphSub C') s sc)
    where sc = subst (λ m → ScTy m (aL k)) (sym (lenₛ-sph C'))
                 (sc-mono (dbl k) (dbl (dim C')) (aL k) (dbl-mono k (dim C') (<-suc k (dim C') p)) (sc-aL k))

  srcK-arr : ∀ C' s t → T (k <ℕ dim C') → srcK k (arr C' s t) ≡ srcK k C'
  srcK-arr C' s t p = lowK C' s t (dbl k)
    (subst (λ m → T (dbl k <ℕ m)) (sym (lenₛ-sph C')) (lt-dbl (dbl k) (suc k) (dim C') (n<sn' k) p))
    where n<sn' : ∀ k → T (dbl k <ℕ dbl (suc k))
          n<sn' k = <-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))

  tgtK-arr : ∀ C' s t → T (k <ℕ dim C') → tgtK k (arr C' s t) ≡ tgtK k C'
  tgtK-arr C' s t p = lowK C' s t (suc (dbl k))
    (subst (λ m → T (suc (dbl k) <ℕ m)) (sym (lenₛ-sph C'))
       (lt-dbl (suc (dbl k)) (suc k) (dim C') (n<sn (suc (dbl k))) p))

-- A cell type of dimension k+1 is (its k-type, k-source, k-target).
C-sph : ∀ k C → dim C ≡ suc k → C ≡ arr (tyK k C) (srcK k C) (tgtK k C)
C-sph k (arr C₀ s₀ t₀) e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (sym (trans (Sb.ext-ty (aL k) (sphSub C₀ ,ₛ s₀) t₀ (Sb.scTy-suc (aL k) sc))
         (trans (Sb.ext-ty (aL k) (sphSub C₀) s₀ sc)
                (subst (λ m → aL m [ sphSub C₀ ]ty ≡ C₀) e₀ (aL-sph C₀)))))
    (cong₂ _,_ (sym (subst (λ m → lookupₛ (sphSub C₀ ,ₛ s₀ ,ₛ t₀) m ≡ s₀) l₀
                       (trans (lk-ext (sphSub C₀ ,ₛ s₀) t₀ (lenₛ (sphSub C₀)) (n<sn (lenₛ (sphSub C₀)))) (lk-top (sphSub C₀) s₀))))
               (sym (subst (λ m → lookupₛ (sphSub C₀ ,ₛ s₀ ,ₛ t₀) (suc m) ≡ t₀) l₀
                       (lk-top (sphSub C₀ ,ₛ s₀) t₀))))
  where
  e₀ : dim C₀ ≡ k
  e₀ = cong (λ m → m ∸ 1) e
  l₀ : lenₛ (sphSub C₀) ≡ dbl k
  l₀ = trans (lenₛ-sph C₀) (cong dbl e₀)
  sc : ScTy (lenₛ (sphSub C₀)) (aL k)
  sc = subst (λ m → ScTy m (aL k)) (sym l₀) (sc-aL k)

-- The generic type of h's disk, under σLp, is tyK k C.
aL-σLp0 : ∀ k h x C → aL k [ sphSub (hL k x C) ,ₛ h ]ty ≡ tyK k C
aL-σLp0 k h x C =
  trans (Sb.ext-ty (aL k) (S ,ₛ x ,ₛ srcK k C) h (Sb.scTy-suc (aL k) (Sb.scTy-suc (aL k) sc)))
  (trans (Sb.ext-ty (aL k) (S ,ₛ x) (srcK k C) (Sb.scTy-suc (aL k) sc))
  (trans (Sb.ext-ty (aL k) S x sc)
         (subst (λ m → aL m [ S ]ty ≡ tyK k C) (dim-tyK k C) (aL-sph (tyK k C)))))
  where
  S = sphSub (tyK k C)
  sc : ScTy (lenₛ S) (aL k)
  sc = subst (λ m → ScTy m (aL k)) (sym (trans (lenₛ-sph (tyK k C)) (cong dbl (dim-tyK k C)))) (sc-aL k)

sc-bLK : ∀ k j → ScTy (tL k j) (bLK k (suc j))
sc-bLK k j = subst (λ m → ScTy m (bLK k (suc j))) (len-LPK k j) (Sb.ty-sc closed (ctx-last (wLK k j)))

-- Under σLp, the generic type of the top cell of LK k j is C.
bLK-σLp : ∀ k j h x C → dim C ≡ nB k j → bLK k (suc j) [ σLp k j h x C ]ty ≡ C
bLK-σLp k zero h x C e =
  trans (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
           (trans (Sb.ext-ty (aL k) (sphSub (hL k x C) ,ₛ h) (tgtK k C) (Sb.scTy-suc (aL k) sc)) (aL-σLp0 k h x C))
           (cong₂ _,_ ls lt))
        (sym (C-sph k C e))
  where
  S = sphSub (tyK k C)
  lS : lenₛ S ≡ dbl k
  lS = trans (lenₛ-sph (tyK k C)) (cong dbl (dim-tyK k C))
  sc : ScTy (lenₛ (sphSub (hL k x C))) (aL k)
  sc = subst (λ m → ScTy m (aL k)) (sym (cong (λ m → suc (suc m)) lS))
         (Sb.scTy-suc (aL k) (Sb.scTy-suc (aL k) (sc-aL k)))
  ls : lookupₛ (sphSub (hL k x C) ,ₛ h ,ₛ tgtK k C) (suc (dbl k)) ≡ srcK k C
  ls = subst (λ m → lookupₛ (sphSub (hL k x C) ,ₛ h ,ₛ tgtK k C) (suc m) ≡ srcK k C) lS
         (trans (lk-ext (sphSub (hL k x C) ,ₛ h) (tgtK k C) (suc (lenₛ S)) (<-suc (suc (lenₛ S)) (suc (suc (lenₛ S))) (n<sn (suc (lenₛ S)))))
         (trans (lk-ext (sphSub (hL k x C)) h (suc (lenₛ S)) (n<sn (suc (lenₛ S))))
                (lk-top (S ,ₛ x) (srcK k C))))
  lt : lookupₛ (sphSub (hL k x C) ,ₛ h ,ₛ tgtK k C) (suc (suc (suc (dbl k)))) ≡ tgtK k C
  lt = subst (λ m → lookupₛ (sphSub (hL k x C) ,ₛ h ,ₛ tgtK k C) (suc (suc (suc m))) ≡ tgtK k C) lS
         (lk-top (sphSub (hL k x C) ,ₛ h) (tgtK k C))
bLK-σLp k (suc j) h x (arr C' s t) e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (trans (Sb.ext-ty (bLK k (suc j)) (P ,ₛ s) t (Sb.scTy-suc (bLK k (suc j)) sc))
    (trans (Sb.ext-ty (bLK k (suc j)) P s sc) (bLK-σLp k j h x C' e')))
    (cong₂ _,_ (subst (λ m → lookupₛ (P ,ₛ s ,ₛ t) m ≡ s) lP
                  (trans (lk-ext (P ,ₛ s) t (lenₛ P) (n<sn (lenₛ P))) (lk-top P s)))
               (subst (λ m → lookupₛ (P ,ₛ s ,ₛ t) (suc m) ≡ t) lP (lk-top (P ,ₛ s) t)))
  where
  e' : dim C' ≡ nB k j
  e' = cong (λ m → m ∸ 1) e
  P = σLp k j h x C'
  lP : lenₛ P ≡ tL k j
  lP = lenₛ-σLp k j h x C' e'
  sc : ScTy (lenₛ P) (bLK k (suc j))
  sc = subst (λ m → ScTy m (bLK k (suc j))) (sym lP) (sc-bLK k j)

-- The k-target of a cell is a k-cell of type tyK.
arr-inj₁ : ∀ {A B s t u v} → arr A s t ≡ arr B u v → A ≡ B
arr-inj₁ refl = refl

arr-inj₃ : ∀ {A B s t u v} → arr A s t ≡ arr B u v → t ≡ v
arr-inj₃ refl = refl

tgtK-wf : ∀ k j {Γ C} → Γ ⊢ty C → dim C ≡ nB k j → Γ ⊢tm tgtK k C ∶ tyK k C
tgtK-wf k zero {Γ} {arr C₀ s₀ t₀} (arr-wf ds dt) e =
  subst₂ (λ X Y → Γ ⊢tm X ∶ Y) (arr-inj₃ eq) (arr-inj₁ eq) dt
  where eq = C-sph k (arr C₀ s₀ t₀) e
tgtK-wf k (suc j) {Γ} {arr C' s t} (arr-wf ds dt) e =
  subst₂ (λ X Y → Γ ⊢tm X ∶ Y) (sym (tgtK-arr k C' s t p)) (sym (tyK-arr k C' s t p))
    (tgtK-wf k j (tm-ty ds) e')
  where
  e' : dim C' ≡ nB k j
  e' = cong (λ m → m ∸ 1) e
  p : T (k <ℕ dim C')
  p = subst (λ m → T (k <ℕ m)) (sym e') (k<n j k)

hL-arr : ∀ k j x C' s t → dim C' ≡ nB k j → hL k x (arr C' s t) ≡ hL k x C'
hL-arr k j x C' s t e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (tyK-arr k C' s t p) (cong (x ,_) (srcK-arr k C' s t p))
  where p = subst (λ m → T (k <ℕ m)) (sym e) (k<n j k)

mutual
  σLp-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
           Γ ⊢sub σLp k j h x C ∶ LPK k j
  σLp-wf k zero {Γ} {h} {x} {c} {C} dc e dh =
    ,-wf (subst (λ m → Γ ⊢sub dskSub h (hL k x C) ∶ Dsk m) (cong suc (dim-tyK k C)) (dsk-wf dh))
         (subst (Γ ⊢tm tgtK k C ∶_) (sym (aL-σLp0 k h x C)) (tgtK-wf k zero (tm-ty dc) e))
  σLp-wf k (suc j) {Γ} {h} {x} {c} {arr C' s t} dc e dh with tm-ty dc
  ... | arr-wf ds dt =
    ,-wf (σL-wf k j ds e' (subst (Γ ⊢tm h ∶_) (hL-arr k j x C' s t e') dh))
         (subst (Γ ⊢tm t ∶_) (sym eq) dt)
    where
    e' : dim C' ≡ nB k j
    e' = cong (λ m → m ∸ 1) e
    eq : bLK k (suc j) [ σL k j h x s C' ]ty ≡ C'
    eq = trans (Sb.ext-ty (bLK k (suc j)) (σLp k j h x C') s
                  (subst (λ m → ScTy m (bLK k (suc j))) (sym (lenₛ-σLp k j h x C' e')) (sc-bLK k j)))
               (bLK-σLp k j h x C' e')

  σL-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
          Γ ⊢sub σL k j h x c C ∶ LK k j
  σL-wf k j {Γ} {h} {x} {c} {C} dc e dh =
    ,-wf (σLp-wf k j dc e dh) (subst (Γ ⊢tm c ∶_) (sym (bLK-σLp k j h x C e)) dc)

-- h ◃ₖ c is well typed.
lwT-wf : ∀ k j {Γ h x c C} → Γ ⊢tm c ∶ C → dim C ≡ nB k j → Γ ⊢tm h ∶ hL k x C →
         Γ ⊢tm lwT k j h x c C ∶ lK k j [ σL k j h x c C ]ty
lwT-wf k j dc e dh = lwhisk k j (σL-wf k j dc e dh)

-- For j = 0: h ;ₖ c goes from x to t_k c.
lwT-ty0 : ∀ k h x c C → dim C ≡ nB k 0 → lK k 0 [ σL k 0 h x c C ]ty ≡ arr (tyK k C) x (tgtK k C)
lwT-ty0 k h x c C e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (trans (Sb.ext-ty (aL k) (Q ,ₛ tgtK k C) c (Sb.scTy-suc (aL k) (Sb.scTy-suc (aL k) sc)))
    (trans (Sb.ext-ty (aL k) Q (tgtK k C) (Sb.scTy-suc (aL k) sc)) (aL-σLp0 k h x C)))
    (cong₂ _,_ lx lz)
  where
  S = sphSub (tyK k C)
  Q = sphSub (hL k x C) ,ₛ h
  lS : lenₛ S ≡ dbl k
  lS = trans (lenₛ-sph (tyK k C)) (cong dbl (dim-tyK k C))
  sc : ScTy (lenₛ (sphSub (hL k x C))) (aL k)
  sc = subst (λ m → ScTy m (aL k)) (sym (cong (λ m → suc (suc m)) lS))
         (Sb.scTy-suc (aL k) (Sb.scTy-suc (aL k) (sc-aL k)))
  lx : lookupₛ (Q ,ₛ tgtK k C ,ₛ c) (dbl k) ≡ x
  lx = subst (λ m → lookupₛ (Q ,ₛ tgtK k C ,ₛ c) m ≡ x) lS
         (trans (lk-ext (Q ,ₛ tgtK k C) c (lenₛ S) (<-suc (lenₛ S) _ (<-suc (lenₛ S) _ (<-suc (lenₛ S) _ (n<sn (lenₛ S))))))
         (trans (lk-ext Q (tgtK k C) (lenₛ S) (<-suc (lenₛ S) _ (<-suc (lenₛ S) _ (n<sn (lenₛ S)))))
         (trans (lk-ext (sphSub (hL k x C)) h (lenₛ S) (<-suc (lenₛ S) _ (n<sn (lenₛ S))))
         (trans (lk-ext (S ,ₛ x) (srcK k C) (lenₛ S) (n<sn (lenₛ S)))
                (lk-top S x)))))
  lz : lookupₛ (Q ,ₛ tgtK k C ,ₛ c) (zK k 0) ≡ tgtK k C
  lz = subst (λ m → lookupₛ (Q ,ₛ tgtK k C ,ₛ c) (suc (suc (suc m))) ≡ tgtK k C) lS
         (trans (lk-ext (Q ,ₛ tgtK k C) c (lenₛ Q) (n<sn (lenₛ Q))) (lk-top Q (tgtK k C)))

-- The identity on a prefix, composed.
idS∘ : ∀ ρ τ → (∀ i → T (i <ℕ lenₛ ρ) → lookupₛ τ i ≡ lookupₛ ρ i) → idS (lenₛ ρ) ∘ τ ≡ ρ
idS∘ ⟨⟩       τ h = refl
idS∘ (ρ ,ₛ u) τ h =
  cong₂ _,ₛ_ (idS∘ ρ τ (λ i p → trans (h i (<-suc i (lenₛ ρ) p)) (lk-ext ρ u i p)))
             (trans (h (lenₛ ρ) (n<sn (lenₛ ρ))) (lk-top ρ u))

-- For j ≥ 1 and c : s → t: h ◃ₖ c : (h ◃ₖ s) → (h ◃ₖ t).
lwT-ty : ∀ k j h x c C' s t → dim C' ≡ nB k j →
         lK k (suc j) [ σL k (suc j) h x c (arr C' s t) ]ty
           ≡ arr (lK k j [ σL k j h x s C' ]ty) (lwT k j h x s C') (lwT k j h x t C')
lwT-ty k j h x c C' s t e =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (trans (Sb.assoc-ty (lK k j) (λsK k j) σ
              (subst (λ n → ScTy n (lK k j)) (sym (lenλs k j)) (Sb.ty-sc closed (lK-wf k j))))
           (cong (lK k j [_]ty) λs∘))
    (cong₂ _,_ (cong (coh (LK k j) (lK k j)) λs∘) (cong (coh (LK k j) (lK k j)) λt∘))
  where
  P = σLp k j h x C'
  σ = σL k (suc j) h x c (arr C' s t)
  lP : lenₛ P ≡ tL k j
  lP = lenₛ-σLp k j h x C' e
  λs∘ : λsK k j ∘ σ ≡ P ,ₛ s
  λs∘ = subst (λ m → idS (suc m) ∘ σ ≡ P ,ₛ s) lP
          (idS∘ (P ,ₛ s) σ (λ i p → trans (lk-ext (P ,ₛ s ,ₛ t) c i (<-suc i (suc (lenₛ P)) p))
                                          (lk-ext (P ,ₛ s) t i p)))
  lt : lookupₛ σ (suc (lenₛ P)) ≡ t
  lt = trans (lk-ext (P ,ₛ s ,ₛ t) c (suc (lenₛ P)) (n<sn (suc (lenₛ P)))) (lk-top (P ,ₛ s) t)
  λt∘ : λtK k j ∘ σ ≡ P ,ₛ t
  λt∘ = subst (λ m → (idS m ∘ σ) ,ₛ lookupₛ σ (suc m) ≡ P ,ₛ t) lP
          (cong₂ _,ₛ_ (idS∘ P σ (λ i p → trans (lk-ext (P ,ₛ s ,ₛ t) c i (<-suc i (suc (lenₛ P)) (<-suc i (lenₛ P) p)))
                                         (trans (lk-ext (P ,ₛ s) t i (<-suc i (lenₛ P) p)) (lk-ext P s i p))))
                      lt)
