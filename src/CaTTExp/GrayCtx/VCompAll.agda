------------------------------------------------------------------------
-- D13, remaining part: vertical composition of lax transformations,
-- reduced to the disks.
--
-- * `cyl2E-wf`: Γ ⊗ (D¹ ∨ D¹) (cyl2E) is well formed for every
--   well-formed globular Γ of any dimension.
-- * `compE-wf`: if the disk images are well typed for the disks D^j,
--   j ≤ k, then compE is a well-typed substitution
--   Γ ⊗ (D¹ ∨ D¹) ⊢ compE : Γ ⊗ D¹ for every well-formed globular Γ
--   of dimension ≤ k. Checks.VCompAll discharges the disk hypothesis
--   for k = 2.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.VCompAll where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalWF
open import CaTTExp.GrayCtx.NaturalExplicit using (TsE)
open import CaTTExp.GrayCtx.NaturalAll using (TsE-wf; cylE; cylE-wf; Disk-wf; glob-Disk)
open import CaTTExp.GrayCtx.VCompExplicit
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Substitutions given entrywise.

lenₛ-mkSub : ∀ n e → lenₛ (mkSub n e) ≡ n
lenₛ-mkSub zero    e = refl
lenₛ-mkSub (suc n) e = cong suc (lenₛ-mkSub n e)

lk-mkSub : ∀ n e i → T (i <ℕ n) → lookupₛ (mkSub n e) i ≡ e i
lk-mkSub (suc n) e i p rewrite lenₛ-mkSub n e with i ==ℕ n in q
... | true  = cong e (sym (==ℕ-sound i n (≡-T q)))
... | false = lk-mkSub n e i (<suc-≢ i n p q)

arr≡ : ∀ {A B t t' u u'} → A ≡ B → t ≡ t' → u ≡ u' → arr A t u ≡ arr B t' u'
arr≡ refl refl refl = refl

-- (rnTy f A)[σ] ≡ A[τ] when σ ∘ f and τ agree on the scope of A.
mutual
  sub-rnTy : ∀ {n f σ τ} A → ScTy n A → (∀ j → T (j <ℕ n) → lookupₛ σ (f j) ≡ lookupₛ τ j) →
             rnTy f A [ σ ]ty ≡ A [ τ ]ty
  sub-rnTy ⋆           _           _ = refl
  sub-rnTy (arr A t u) (a , p , q) h = arr≡ (sub-rnTy A a h) (sub-rnTm t p h) (sub-rnTm u q h)

  sub-rnTm : ∀ {n f σ τ} t → ScTm n t → (∀ j → T (j <ℕ n) → lookupₛ σ (f j) ≡ lookupₛ τ j) →
             rnTm f t [ σ ]tm ≡ t [ τ ]tm
  sub-rnTm (var i)     p h = h i p
  sub-rnTm (coh Δ B ρ) p h = cong (coh Δ B) (sub-rnSub ρ p h)
  sub-rnTm (cst ())    _ _

  sub-rnSub : ∀ {n f σ τ} ρ → ScSub n ρ → (∀ j → T (j <ℕ n) → lookupₛ σ (f j) ≡ lookupₛ τ j) →
              rnSub f ρ ∘ σ ≡ ρ ∘ τ
  sub-rnSub ⟨⟩       _       _ = refl
  sub-rnSub (ρ ,ₛ t) (p , q) h = cong₂ _,ₛ_ (sub-rnSub ρ p h) (sub-rnTm t q h)

-- A[τ] ≡ rnTy g A when τ sends the scope of A to variables along g.
mutual
  sub-varTy : ∀ {n τ g} A → ScTy n A → (∀ j → T (j <ℕ n) → lookupₛ τ j ≡ var (g j)) →
              A [ τ ]ty ≡ rnTy g A
  sub-varTy ⋆           _           _ = refl
  sub-varTy (arr A t u) (a , p , q) h = arr≡ (sub-varTy A a h) (sub-varTm t p h) (sub-varTm u q h)

  sub-varTm : ∀ {n τ g} t → ScTm n t → (∀ j → T (j <ℕ n) → lookupₛ τ j ≡ var (g j)) →
              t [ τ ]tm ≡ rnTm g t
  sub-varTm (var i)     p h = h i p
  sub-varTm (coh Δ B ρ) p h = cong (coh Δ B) (sub-varSub ρ p h)
  sub-varTm (cst ())    _ _

  sub-varSub : ∀ {n τ g} ρ → ScSub n ρ → (∀ j → T (j <ℕ n) → lookupₛ τ j ≡ var (g j)) →
               ρ ∘ τ ≡ rnSub g ρ
  sub-varSub ⟨⟩       _       _ = refl
  sub-varSub (ρ ,ₛ t) (p , q) h = cong₂ _,ₛ_ (sub-varSub ρ p h) (sub-varTm t q h)

-- Both at once.
sub-rnvar : ∀ {n f σ g} A → ScTy n A → (∀ j → T (j <ℕ n) → lookupₛ σ (f j) ≡ var (g j)) →
            rnTy f A [ σ ]ty ≡ rnTy g A
sub-rnvar {n} {f} {σ} {g} A a h =
  trans (sub-rnTy {τ = mkSub n (λ j → var (g j))} A a
           (λ j p → trans (h j p) (sym (lk-mkSub n _ j p))))
        (sub-varTy A a (λ j p → lk-mkSub n _ j p))

------------------------------------------------------------------------
-- Arithmetic.

≢→F : ∀ {b} → b ≡ false → T b → ⊥
≢→F refl ()

N2 N3 N4 : Nat → Nat
N2 N = N + N
N3 N = N + (N + N)
N4 N = N + (N + (N + N))

-- a + b < a + c, nested.
lt2 : ∀ N a b → T (a <ℕ b) → T (N + (N + a) <ℕ N + (N + b))
lt2 N a b p = T-+< N (N + a) (N + b) (T-+< N a b p)

ιI-lo : ∀ N j → T (j <ℕ N + N) → ιI N j ≡ j
ιI-lo N j p rewrite T-≡ p = refl

ιI-hi : ∀ N x → ιI N (N + (N + x)) ≡ N + (N + (N + x))
ιI-hi N x rewrite +-<-l N (N + x) N | +-≮ N x = refl

ιJ-lo : ∀ N j → T (j <ℕ N + N) → ιJ N j ≡ N + j
ιJ-lo N j p rewrite T-≡ p = refl

ιJ-hi : ∀ N x → ιJ N (N + (N + x)) ≡ N + (N + (N + (N + x)))
ιJ-hi N x rewrite +-<-l N (N + x) N | +-≮ N x = refl

ιI-mono : ∀ N j k → T (j <ℕ k) → T (ιI N j <ℕ ιI N k)
ιI-mono N j k p with j <ℕ (N + N) in e₁ | k <ℕ (N + N) in e₂
... | true  | true  = p
... | true  | false = <-+ j k N p
... | false | true  = ⊥-elim (≢→F e₁ (<-trans j k (N + N) p (≡-T e₂)))
... | false | false = T-+< N j k p

ιJ-mono : ∀ N j k → T (j <ℕ k) → T (ιJ N j <ℕ ιJ N k)
ιJ-mono N j k p with j <ℕ (N + N) in e₁ | k <ℕ (N + N) in e₂
... | true  | true  = T-+< N j k p
... | true  | false = T-+< N j (N + k) (<-+ j k N p)
... | false | true  = ⊥-elim (≢→F e₁ (<-trans j k (N + N) p (≡-T e₂)))
... | false | false = T-+< N (N + j) (N + k) (T-+< N j k p)

------------------------------------------------------------------------
-- Γ ⊗ (D¹ ∨ D¹) from Γ ⊗ D¹: every level is ιI or ιJ of a level of
-- Γ ⊗ D¹, with the renamed type.

module Cyl2 (Ts : Nat → Ty) (Γ : Ctx) (w : Γ ⊢ctx) where
  N = len Γ
  g = gN Ts Γ
  G = g2 Ts Γ

  sc-tyAt : ∀ k → T (k <ℕ N) → ScTy N (tyAt Γ k)
  sc-tyAt k p = sc-mono k N (tyAt Γ k) (<-suc k N p)
    (subst (λ n → ScTy n (tyAt Γ k)) (len-mk k (tyAt Γ)) (Sb.ty-sc closed∅ (ctx-inv Γ k w p)))

  gI-lo : ∀ k → T (k <ℕ N + N) → G k ≡ rnTy (ιI N) (g k)
  gI-lo k p rewrite T-≡ p = refl

  gI-hi : ∀ x → T (x <ℕ N) → G (N + (N + (N + x))) ≡ rnTy (ιI N) (g (N + (N + x)))
  gI-hi x p = trans st (cong (λ k → rnTy (ιI N) (g k)) (+-∸ N (N + (N + x))))
    where
    st : G (N + (N + (N + x))) ≡ rnTy (ιI N) (g ((N + (N + (N + x))) ∸ N))
    st rewrite +-<-l N (N + (N + x)) N | +-≮ N (N + x)
             | +-<-l N (N + (N + x)) (N + N) | +-<-l N (N + x) N | +-≮ N x
             | +-<-l N (N + (N + x)) (N + (N + N)) | +-<-l N (N + x) (N + N) | +-<-l N x N | T-≡ p = refl

  gJ-lo : ∀ k → T (k <ℕ N) → G (N + k) ≡ rnTy (ιJ N) (g k)
  gJ-lo k p =
    trans (gI-lo (N + k) (T-+< N k N p))
    (trans (cong (rnTy (ιI N)) (gN-c1 Ts Γ k p))
    (trans (rn-compTy (ιI N) (N +_) (tyAt Γ k))
    (trans (rn-extTy (tyAt Γ k) (sc-tyAt k p)
             (λ v pv → trans (ιI-lo N (N + v) (T-+< N v N pv)) (sym (ιJ-lo N v (lt-N v N N pv)))))
           (cong (rnTy (ιJ N)) (sym (gN-c0 Ts Γ k p))))))

  gJ-mid : ∀ x → T (x <ℕ N) → G (N + (N + x)) ≡ rnTy (ιJ N) (g (N + x))
  gJ-mid x p = trans st (cong (λ k → rnTy (ιJ N) (g k)) (+-∸ N (N + x)))
    where
    st : G (N + (N + x)) ≡ rnTy (ιJ N) (g ((N + (N + x)) ∸ N))
    st rewrite +-<-l N (N + x) N | +-≮ N x
             | +-<-l N (N + x) (N + N) | +-<-l N x N | T-≡ p = refl

  gJ-hi : ∀ x → T (x <ℕ N) → G (N + (N + (N + (N + x)))) ≡ rnTy (ιJ N) (g (N + (N + x)))
  gJ-hi x p = trans st (cong (λ k → rnTy (ιJ N) (g k))
                             (trans (cong (_∸ N) (+-∸ N (N + (N + (N + x))))) (+-∸ N (N + (N + x)))))
    where
    st : G (N + (N + (N + (N + x)))) ≡ rnTy (ιJ N) (g (((N + (N + (N + (N + x)))) ∸ N) ∸ N))
    st rewrite +-<-l N (N + (N + (N + x))) N | +-≮ N (N + (N + x))
             | +-<-l N (N + (N + (N + x))) (N + N) | +-<-l N (N + (N + x)) N | +-≮ N (N + x)
             | +-<-l N (N + (N + (N + x))) (N + (N + N)) | +-<-l N (N + (N + x)) (N + N)
             | +-<-l N (N + x) N | +-≮ N x = refl

  -- G at ι k, for every k < 3N.
  gI : ∀ k → T (k <ℕ N + (N + N)) → G (ιI N k) ≡ rnTy (ιI N) (g k)
  gI k pk with view3 N k
  ... | c0 p = trans (cong G (ιI-lo N k (lt-N k N N p))) (gI-lo k (lt-N k N N p))
  ... | c1 d p refl = trans (cong G (ιI-lo N (N + d) (T-+< N d N p))) (gI-lo (N + d) (T-+< N d N p))
  ... | c2 x refl = trans (cong G (ιI-hi N x)) (gI-hi x (+<-T N x N (+<-T N (N + x) (N + N) pk)))

  gJ : ∀ k → T (k <ℕ N + (N + N)) → G (ιJ N k) ≡ rnTy (ιJ N) (g k)
  gJ k pk with view3 N k
  ... | c0 p = trans (cong G (ιJ-lo N k (lt-N k N N p))) (gJ-lo k p)
  ... | c1 d p refl = trans (cong G (ιJ-lo N (N + d) (T-+< N d N p))) (gJ-mid d p)
  ... | c2 x refl = trans (cong G (ιJ-hi N x)) (gJ-hi x (+<-T N x N (+<-T N (N + x) (N + N) pk)))

  -- Well-formedness, from that of Γ ⊗ D¹.
  module WF (wC : cylWith Ts Γ ⊢ctx) where
    L3 = N + (N + N)

    viaι : (ι : Nat → Nat) → (∀ j k → T (j <ℕ k) → T (ι j <ℕ ι k)) →
           (∀ k → T (k <ℕ L3) → G (ι k) ≡ rnTy ι (g k)) →
           ∀ k i → T (k <ℕ L3) → ι k ≡ i → mkCtx i G ⊢ctx → mkCtx i G ⊢ty G i
    viaι ι mono gι k i pk refl wi =
      subst (mkCtx (ι k) G ⊢ty_) (sym (gι k pk)) (rn-ty wi r (snd (inv-mk L3 g k wC pk)))
      where
      r : Resp ι (mkCtx k g) (mkCtx (ι k) G)
      r j A eq =
        let (pj , qj) = lk-mk-inv k g j eq in
        trans (lk-mk (ι k) G (ι j) (mono j k pj))
              (cong just (trans (gι j (<-trans j k L3 pj pk)) (cong (rnTy ι) qj)))

    VI = viaι (ιI N) (ιI-mono N) gI
    VJ = viaι (ιJ N) (ιJ-mono N) gJ

    obl : ∀ i → T (i <ℕ N + (N + (N + (N + N)))) → mkCtx i G ⊢ctx → mkCtx i G ⊢ty G i
    obl i pi wi with view3 N i
    ... | c0 p = VI i i (lt-N i N (N + N) p) (ιI-lo N i (lt-N i N N p)) wi
    ... | c1 d p refl =
      VI (N + d) (N + d) (T-+< N d (N + N) (lt-N d N N p)) (ιI-lo N (N + d) (T-+< N d N p)) wi
    ... | c2 y refl with view3 N y
    ...   | c0 p = VJ (N + y) (N + (N + y)) (T-+< N y (N + N) (lt-N y N N p))
                      (ιJ-lo N (N + y) (T-+< N y N p)) wi
    ...   | c1 x p refl = VI (N + (N + x)) (N + (N + (N + x))) (lt2 N x N p) (ιI-hi N x) wi
    ...   | c2 x refl =
      VJ (N + (N + x)) (N + (N + (N + (N + x)))) (lt2 N x N px) (ιJ-hi N x) wi
      where
      px : T (x <ℕ N)
      px = +<-T N x N (+<-T N (N + x) (N + N) (+<-T N (N + (N + x)) (N + (N + N))
             (+<-T N (N + (N + (N + x))) (N + (N + (N + N))) pi)))

    cyl2-wf : cyl2With Ts Γ ⊢ctx
    cyl2-wf = mk-wf (N + (N + (N + (N + N)))) G obl

cyl2E-wf : ∀ sd Γ → Γ ⊢ctx → T (globular Γ) → cyl2E sd Γ ⊢ctx
cyl2E-wf sd Γ w gl = Cyl2.WF.cyl2-wf (TsE sd) Γ w (cylE-wf sd Γ w gl)

------------------------------------------------------------------------
-- The five blocks of Δ ⊗ (D¹ ∨ D¹), K levels each.

data View5 (K v : Nat) : Set where
  b0 : T (v <ℕ K) → View5 K v
  b1 : ∀ u → T (u <ℕ K) → v ≡ K + u → View5 K v
  b2 : ∀ u → T (u <ℕ K) → v ≡ K + (K + u) → View5 K v
  b3 : ∀ u → T (u <ℕ K) → v ≡ K + (K + (K + u)) → View5 K v
  b4 : ∀ u → T (u <ℕ K) → v ≡ K + (K + (K + (K + u))) → View5 K v

view5 : ∀ K v → T (v <ℕ K + (K + (K + (K + K)))) → View5 K v
view5 K v pv with view3 K v
... | c0 p = b0 p
... | c1 u p e = b1 u p e
... | c2 y refl with view3 K y
...   | c0 p = b2 y p refl
...   | c1 u p refl = b3 u p refl
...   | c2 u refl = b4 u (+<-T K u K (+<-T K (K + u) (K + K) (+<-T K (K + (K + u)) (K + (K + K))
                                (+<-T K (K + (K + (K + u))) (K + (K + (K + K))) pv)))) refl

h5-0 : ∀ N M χ u → T (u <ℕ M) → h5 N M χ u ≡ χ u
h5-0 N M χ u p rewrite T-≡ p = refl

h5-1 : ∀ N M χ u → T (u <ℕ M) → h5 N M χ (M + u) ≡ N + χ u
h5-1 N M χ u p rewrite +-≮ M u | +-<-l M u M | T-≡ p | +-∸ M u = refl

h5-2 : ∀ N M χ u → T (u <ℕ M) → h5 N M χ (M + (M + u)) ≡ N + (N + χ u)
h5-2 N M χ u p
  rewrite +-≮ M (M + u) | +-<-l M (M + u) M | +-≮ M u
        | +-<-l M (M + u) (M + M) | +-<-l M u M | T-≡ p
        | +-∸ M (M + u) | +-∸ M u = refl

h5-3 : ∀ N M χ u → T (u <ℕ M) → h5 N M χ (M + (M + (M + u))) ≡ N + (N + (N + χ u))
h5-3 N M χ u p
  rewrite +-≮ M (M + (M + u)) | +-<-l M (M + (M + u)) M | +-≮ M (M + u)
        | +-<-l M (M + (M + u)) (M + M) | +-<-l M (M + u) M | +-≮ M u
        | +-<-l M (M + (M + u)) (M + (M + M)) | +-<-l M (M + u) (M + M) | +-<-l M u M | T-≡ p
        | +-∸ M (M + (M + u)) | +-∸ M (M + u) | +-∸ M u = refl

h5-4 : ∀ N M χ u → h5 N M χ (M + (M + (M + (M + u)))) ≡ N + (N + (N + (N + χ u)))
h5-4 N M χ u
  rewrite +-≮ M (M + (M + (M + u))) | +-<-l M (M + (M + (M + u))) M | +-≮ M (M + (M + u))
        | +-<-l M (M + (M + (M + u))) (M + M) | +-<-l M (M + (M + u)) M | +-≮ M (M + u)
        | +-<-l M (M + (M + (M + u))) (M + (M + M)) | +-<-l M (M + (M + u)) (M + M)
        | +-<-l M (M + u) M | +-≮ M u
        | +-∸ M (M + (M + (M + u))) | +-∸ M (M + (M + u)) | +-∸ M (M + u) | +-∸ M u = refl

------------------------------------------------------------------------
-- The disk hypothesis.

DiskCertW : Side → (Nat → Tm) → Nat → Set
DiskCertW sd img m = (cyl2E sd (Disk m) ⊢ctx)
                   × (cyl2E sd (Disk m) ⊢tm img m ∶ (TsE sd m [ compW img (Disk m) ]ty))

DiskCert : Side → Nat → Set
DiskCert sd = DiskCertW sd (imgE sd)

+-suc' : ∀ a b → a + suc b ≡ suc (a + b)
+-suc' zero    b = refl
+-suc' (suc a) b = cong suc (+-suc' a b)

entE-c0 : ∀ (img : Nat → Tm) Γ i → T (i <ℕ len Γ) → entW img Γ i ≡ var i
entE-c0 img Γ i p rewrite T-≡ p = refl

entE-c1 : ∀ (img : Nat → Tm) Γ x → T (x <ℕ len Γ) → entW img Γ (len Γ + x) ≡ var (len Γ + (len Γ + x))
entE-c1 img Γ x p rewrite +-≮ (len Γ) x | +-<-l (len Γ) x (len Γ) | T-≡ p = refl

entE-c2 : ∀ (img : Nat → Tm) Γ x → entW img Γ (len Γ + (len Γ + x)) ≡ genW img Γ x
entE-c2 img Γ x = trans st (cong (genW img Γ) (trans (cong (_∸ len Γ) (+-∸ (len Γ) (len Γ + x))) (+-∸ (len Γ) x)))
  where
  N = len Γ
  st : entW img Γ (N + (N + x)) ≡ genW img Γ (((N + (N + x)) ∸ N) ∸ N)
  st rewrite +-≮ N (N + x) | +-<-l N (N + x) N | +-≮ N x = refl

------------------------------------------------------------------------
-- Every level of Δ ⊗ (D¹ ∨ D¹) is ιI or ιJ of a level of Δ ⊗ D¹.

data Pre (L i : Nat) : Set where
  viaI : ∀ k → T (k <ℕ L + (L + L)) → ιI L k ≡ i → Pre L i
  viaJ : ∀ k → T (k <ℕ L + (L + L)) → ιJ L k ≡ i → Pre L i

pre : ∀ L i → T (i <ℕ L + (L + (L + (L + L)))) → Pre L i
pre L i pi with view5 L i pi
... | b0 p = viaI i (lt-N i L (L + L) p) (ιI-lo L i (lt-N i L L p))
... | b1 u p refl = viaI (L + u) (T-+< L u (L + L) (lt-N u L L p)) (ιI-lo L (L + u) (T-+< L u L p))
... | b2 u p refl = viaJ (L + u) (T-+< L u (L + L) (lt-N u L L p)) (ιJ-lo L (L + u) (T-+< L u L p))
... | b3 u p refl = viaI (L + (L + u)) (lt2 L u L p) (ιI-hi L u)
... | b4 u p refl = viaJ (L + (L + u)) (lt2 L u L p) (ιJ-hi L u)

------------------------------------------------------------------------
-- The theorem.

module Gen (sd : Side) (img : Nat → Tm) (Γ : Ctx) (w : Γ ⊢ctx) (gl : T (globular Γ)) where
  open Classify Γ w gl
  Ts = TsE sd
  module Mn = Main Ts (dimCtx Γ) (λ j _ → TsE-wf sd j) Γ w gl N (n<sn N) (λ x p → dimV-≤ Γ x p)
  module CΓ = Cyl2 Ts Γ w

  L5 = N + (N + (N + (N + N)))
  w2 : cyl2E sd Γ ⊢ctx
  w2 = cyl2E-wf sd Γ w gl
  wC : cylE sd Γ ⊢ctx
  wC = cylE-wf sd Γ w gl

  ιI-bd : ∀ k → T (k <ℕ N + (N + N)) → T (ιI N k <ℕ L5)
  ιI-bd k pk with view3 N k
  ... | c0 p rewrite ιI-lo N k (lt-N k N N p) = lt-N k N _ p
  ... | c1 d p refl rewrite ιI-lo N (N + d) (T-+< N d N p) = T-+< N d _ (lt-N d N _ p)
  ... | c2 x refl rewrite ιI-hi N x =
    T-+< N (N + (N + x)) _ (lt2 N x (N + N) (lt-N x N N (+<-T N x N (+<-T N (N + x) (N + N) pk))))

  ιJ-bd : ∀ k → T (k <ℕ N + (N + N)) → T (ιJ N k <ℕ L5)
  ιJ-bd k pk with view3 N k
  ... | c0 p rewrite ιJ-lo N k (lt-N k N N p) = T-+< N k _ (lt-N k N _ p)
  ... | c1 d p refl rewrite ιJ-lo N (N + d) (T-+< N d N p) = lt2 N d _ (lt-N d N _ p)
  ... | c2 x refl rewrite ιJ-hi N x =
    T-+< N (N + (N + (N + x))) _ (lt2 N (N + x) (N + N) (T-+< N x N (+<-T N x N (+<-T N (N + x) (N + N) pk))))

  -- The generator of a variable x: its disk renames into Γ along ρ.
  module X (x : Nat) (px : T (x <ℕ N)) where
    open Mn.C2 x px using (m; M; χ; h; χN; dimχ; bnd; geq)
    D = Disk m
    L = len D
    ρ = h5 N M χ
    module CD = Cyl2 Ts D (Disk-wf m)
    gD = gN Ts D
    wCD : cylE sd D ⊢ctx
    wCD = cylE-wf sd D (Disk-wf m) (glob-Disk m)

    top = M + (M + dbl m)

    M3 : M + (M + M) ≡ suc top
    M3 = trans (cong (M +_) (+-suc' M (dbl m))) (+-suc' M (M + dbl m))

    LM : L ≡ M
    LM = len-D m

    ψ = chiK D m (dbl m)

    ψid : ∀ v → T (v <ℕ M) → ψ v ≡ v
    ψid v pv = trans (chiD m m (dbl m) v (n<sn (dbl m)) (half-dbl m) pv) (fin (v ==ℕ dbl m) refl)
      where
      fin : ∀ b → (v ==ℕ dbl m) ≡ b → (if b then dbl m else v) ≡ v
      fin true  e = sym (==ℕ-sound v _ (≡-T e))
      fin false _ = refl

    hψ : ∀ v → T (v <ℕ top) → hmap M M ψ v ≡ v
    hψ v pv with view3 M v
    ... | c0 p = trans (hmap-c0 M M ψ v p) (ψid v p)
    ... | c1 d p refl = trans (hmap-c1 M M ψ d p) (cong (M +_) (ψid d p))
    ... | c2 d refl = trans (hmap-c2 M M ψ d) (cong (λ z → M + (M + z)) (ψid d d<))
      where
      d< : T (d <ℕ M)
      d< = <-suc d (dbl m) (+<-T M d (dbl m) (+<-T M (M + d) (M + dbl m) pv))

    scT : ScTy top (Ts m)
    scT = subst (λ n → ScTy n (Ts m)) (len-mk top gD) (Sb.ty-sc closed∅ (TsE-wf sd m))

    gD-top : gD top ≡ rnTy (hmap M M ψ) (Ts m)
    gD-top = trans (gD-c2 Ts m (dbl m) (n<sn (dbl m)))
                   (cong (λ k → rnTy (hmap M (suc (dbl k)) (chiK D k (dbl m))) (Ts k)) (half-dbl m))

    h-top : h top ≡ N + (N + x)
    h-top = trans (hmap-c2 N M χ (dbl m)) (cong (λ z → N + (N + z)) (chi-top Γ m x))

    geq-top : gN Ts Γ (h top) ≡ rnTy h (gD top)
    geq-top =
      trans (cong (gN Ts Γ) h-top)
      (trans (gN-c2 Ts Γ x)
      (sym (trans (cong (rnTy h) gD-top)
           (trans (rn-compTy h (hmap M M ψ) (Ts m))
                  (rn-extTy (Ts m) scT (λ v pv → cong h (hψ v pv)))))))

    hfull : ∀ k → T (k <ℕ M + (M + M)) → T (h k <ℕ N + (N + N)) × (gN Ts Γ (h k) ≡ rnTy h (gD k))
    hfull k pk with k ==ℕ top in e
    ... | true rewrite ==ℕ-sound k top (≡-T e) =
      subst (λ z → T (z <ℕ N + (N + N))) (sym h-top) (lt2 N x N px) , geq-top
    ... | false =
      let p = <suc-≢ k top (subst (λ n → T (k <ℕ n)) M3 pk) e in
      <-trans (h k) (N + (N + x)) (N + (N + N)) (bnd k p) (lt2 N x N px) , geq k p

    ρι-I : ∀ k → T (k <ℕ M + (M + M)) → ρ (ιI M k) ≡ ιI N (h k)
    ρι-I k pk with view3 M k
    ... | c0 p =
      trans (cong ρ (ιI-lo M k (lt-N k M M p)))
      (trans (h5-0 N M χ k p)
      (sym (trans (cong (ιI N) (hmap-c0 N M χ k p)) (ιI-lo N (χ k) (lt-N (χ k) N N (χN k p))))))
    ... | c1 d p refl =
      trans (cong ρ (ιI-lo M (M + d) (T-+< M d M p)))
      (trans (h5-1 N M χ d p)
      (sym (trans (cong (ιI N) (hmap-c1 N M χ d p)) (ιI-lo N (N + χ d) (T-+< N (χ d) N (χN d p))))))
    ... | c2 d refl =
      trans (cong ρ (ιI-hi M d))
      (trans (h5-3 N M χ d (+<-T M d M (+<-T M (M + d) (M + M) pk)))
      (sym (trans (cong (ιI N) (hmap-c2 N M χ d)) (ιI-hi N (χ d)))))

    ρι-J : ∀ k → T (k <ℕ M + (M + M)) → ρ (ιJ M k) ≡ ιJ N (h k)
    ρι-J k pk with view3 M k
    ... | c0 p =
      trans (cong ρ (ιJ-lo M k (lt-N k M M p)))
      (trans (h5-1 N M χ k p)
      (sym (trans (cong (ιJ N) (hmap-c0 N M χ k p)) (ιJ-lo N (χ k) (lt-N (χ k) N N (χN k p))))))
    ... | c1 d p refl =
      trans (cong ρ (ιJ-lo M (M + d) (T-+< M d M p)))
      (trans (h5-2 N M χ d p)
      (sym (trans (cong (ιJ N) (hmap-c1 N M χ d p)) (ιJ-lo N (N + χ d) (T-+< N (χ d) N (χN d p))))))
    ... | c2 d refl =
      trans (cong ρ (ιJ-hi M d))
      (trans (h5-4 N M χ d)
      (sym (trans (cong (ιJ N) (hmap-c2 N M χ d)) (ιJ-hi N (χ d)))))

    scD : ∀ k → T (k <ℕ L + (L + L)) → ScTy k (gD k)
    scD k pk = subst (λ n → ScTy n (gD k)) (len-mk k gD) (Sb.ty-sc closed∅ (snd (inv-mk (L + (L + L)) gD k wCD pk)))

    toM : ∀ k → T (k <ℕ L + (L + L)) → T (k <ℕ M + (M + M))
    toM k pk = subst (λ l → T (k <ℕ l + (l + l))) LM pk

    gen : (ιD ιG : Nat → Nat) →
          (∀ k → T (k <ℕ L + (L + L)) → g2 Ts D (ιD k) ≡ rnTy ιD (gD k)) →
          (∀ k → T (k <ℕ N + (N + N)) → g2 Ts Γ (ιG k) ≡ rnTy ιG (gN Ts Γ k)) →
          (∀ k → T (k <ℕ N + (N + N)) → T (ιG k <ℕ L5)) →
          (∀ k → T (k <ℕ M + (M + M)) → ρ (ιD k) ≡ ιG (h k)) →
          ∀ k → T (k <ℕ L + (L + L)) → ∀ {A} → g2 Ts D (ιD k) ≡ A →
          lookup (cyl2E sd Γ) (ρ (ιD k)) ≡ just (rnTy ρ A)
    gen ιD ιG gDι gGι bG ρι k pk {A} qa =
      let pkM = toM k pk
          hk = hfull k pkM in
      trans (cong (lookup (cyl2E sd Γ)) (ρι k pkM))
      (trans (lk-mk L5 (g2 Ts Γ) (ιG (h k)) (bG (h k) (fst hk)))
      (cong just
        (trans (gGι (h k) (fst hk))
        (trans (cong (rnTy ιG) (snd hk))
        (trans (rn-compTy ιG h (gD k))
        (trans (rn-extTy (gD k) (scD k pk) (λ v pv → sym (ρι v (<-trans v k (M + (M + M)) pv pkM))))
        (trans (sym (rn-compTy ρ ιD (gD k)))
        (trans (cong (rnTy ρ) (sym (gDι k pk))) (cong (rnTy ρ) qa)))))))))

    ριI-L : ∀ k → T (k <ℕ M + (M + M)) → ρ (ιI L k) ≡ ιI N (h k)
    ριI-L k pk = trans (cong (λ l → ρ (ιI l k)) LM) (ρι-I k pk)

    ριJ-L : ∀ k → T (k <ℕ M + (M + M)) → ρ (ιJ L k) ≡ ιJ N (h k)
    ριJ-L k pk = trans (cong (λ l → ρ (ιJ l k)) LM) (ρι-J k pk)

    rsp : Resp ρ (cyl2E sd D) (cyl2E sd Γ)
    rsp i' A eq =
      let (pi' , qi') = lk-mk-inv (L + (L + (L + (L + L)))) (g2 Ts D) i' eq in
      go (pre L i' pi') qi'
      where
      go : Pre L i' → g2 Ts D i' ≡ A → lookup (cyl2E sd Γ) (ρ i') ≡ just (rnTy ρ A)
      go (viaI k pk refl) qa = gen (ιI L) (ιI N) CD.gI CΓ.gI ιI-bd ριI-L k pk qa
      go (viaJ k pk refl) qa = gen (ιJ L) (ιJ N) CD.gJ CΓ.gJ ιJ-bd ριJ-L k pk qa

  ----------------------------------------------------------------------
  -- The substitution, given the disks up to dimension k.

  module SubK (k : Nat) (DC : ∀ j → T (j <ℕ suc k) → DiskCertW sd img j)
             (dk : T (dimCtx Γ <ℕ suc k)) where
    e = entW img Γ
    L3 = N + (N + N)
    g = gN Ts Γ
    G = g2 Ts Γ

    scAt : ∀ n → T (n <ℕ N) → ScTy n (tyAt Γ n)
    scAt n p = subst (λ l → ScTy l (tyAt Γ n)) (len-mk n (tyAt Γ)) (Sb.ty-sc closed∅ (ctx-inv Γ n w p))

    dimk : ∀ x → T (x <ℕ N) → T (dimV Γ x <ℕ suc k)
    dimk x p = ≤-<-trans (dimV Γ x) (dimCtx Γ) (suc k) (dimV-≤ Γ x p) dk

    -- The generator entry.
    module E (x : Nat) (px : T (x <ℕ N)) where
      open X x px public
      open Mn.C2 x px using (m; M; χ; h; χN; dimχ; bnd) public

      σD = compW img D
      σ  = mkSub (N + (N + x)) e

      DCm : DiskCertW sd img m
      DCm = DC m (dimk x px)

      lenσD : lenₛ σD ≡ L + (L + L)
      lenσD = lenₛ-mkSub (L + (L + L)) (entW img D)

      top<3L : T (top <ℕ suc (L + (L + L)))
      top<3L = subst (λ l → T (top <ℕ suc (l + (l + l)))) (sym LM)
                 (<-suc top (M + (M + M)) (subst (λ n → T (top <ℕ n)) (sym M3) (n<sn top)))

      scTσ : ScTy (lenₛ σD) (Ts m)
      scTσ = subst (λ n → ScTy n (Ts m)) (sym lenσD) (sc-mono top (L + (L + L)) (Ts m) top<3L scT)

      -- Entries of the disk substitution, in terms of M.
      eD-c0 : ∀ j → T (j <ℕ M) → entW img D j ≡ var j
      eD-c0 j p = entE-c0 img D j (subst (λ l → T (j <ℕ l)) (sym LM) p)

      eD-c1 : ∀ d → T (d <ℕ M) → entW img D (M + d) ≡ var (M + (M + d))
      eD-c1 d p = subst (λ l → entW img D (l + d) ≡ var (l + (l + d))) LM
                        (entE-c1 img D d (subst (λ l → T (d <ℕ l)) (sym LM) p))

      dimVD : ∀ d → T (d <ℕ M) → dimV D d ≡ half d
      dimVD d p = trans (cong dim (tyAt-mk M aD d p)) (dim-aL (half d))

      -- The generator entries of the boundary cells agree.
      module Bd (d : Nat) (d< : T (d <ℕ dbl m)) where
        d<M : T (d <ℕ M)
        d<M = <-suc d (dbl m) d<
        kd = half d
        Kd = suc (dbl kd)
        φ = chiK Γ kd (χ d)
        ψ' = chiK D kd d

        kd< : T (kd <ℕ suc k)
        kd< = <-trans kd m (suc k) (half-< d m d<) (dimk x px)

        imk = img kd
        scI : ScTm (Kd + (Kd + (Kd + (Kd + Kd)))) imk
        scI = subst (λ n → ScTm n imk)
                (trans (len-mk _ (g2 Ts (Disk kd))) (cong (λ l → l + (l + (l + (l + l)))) (len-D kd)))
                (Sb.tm-sc closed∅ (snd (DC kd kd<)))

        ψ'M : ∀ u → T (u <ℕ Kd) → T (ψ' u <ℕ M)
        ψ'M u pu = ≤-<-trans (ψ' u) d M (Mn.psi-bound m d u d<M pu) d<M

        cc : ∀ u → T (u <ℕ Kd) → χ (ψ' u) ≡ φ u
        cc u pu = trans (CC m x refl px d d< u pu) (cong (λ z → chiK Γ z (χ d) u) (dimχ d d<M))

        agr : Agree (Kd + (Kd + (Kd + (Kd + Kd)))) (h5 N Kd φ) (λ v → ρ (h5 M Kd ψ' v))
        agr v pv with view5 Kd v pv
        ... | b0 pu = trans (h5-0 N Kd φ v pu)
                 (sym (trans (cong ρ (h5-0 M Kd ψ' v pu)) (trans (h5-0 N M χ (ψ' v) (ψ'M v pu)) (cc v pu))))
        ... | b1 u pu refl = trans (h5-1 N Kd φ u pu)
                 (sym (trans (cong ρ (h5-1 M Kd ψ' u pu))
                      (trans (h5-1 N M χ (ψ' u) (ψ'M u pu)) (cong (N +_) (cc u pu)))))
        ... | b2 u pu refl = trans (h5-2 N Kd φ u pu)
                 (sym (trans (cong ρ (h5-2 M Kd ψ' u pu))
                      (trans (h5-2 N M χ (ψ' u) (ψ'M u pu)) (cong (λ z → N + (N + z)) (cc u pu)))))
        ... | b3 u pu refl = trans (h5-3 N Kd φ u pu)
                 (sym (trans (cong ρ (h5-3 M Kd ψ' u pu))
                      (trans (h5-3 N M χ (ψ' u) (ψ'M u pu)) (cong (λ z → N + (N + (N + z))) (cc u pu)))))
        ... | b4 u pu refl = trans (h5-4 N Kd φ u)
                 (sym (trans (cong ρ (h5-4 M Kd ψ' u))
                      (trans (h5-4 N M χ (ψ' u)) (cong (λ z → N + (N + (N + (N + z)))) (cc u pu)))))

        lhsE : genW img Γ (χ d) ≡ rnTm (h5 N Kd φ) imk
        lhsE = cong (λ z → rnTm (h5 N (suc (dbl z)) (chiK Γ z (χ d))) (img z)) (dimχ d d<M)

        rhsE : genW img D d ≡ rnTm (h5 M Kd ψ') imk
        rhsE = cong₂ (λ l z → rnTm (h5 l (suc (dbl z)) (chiK D z d)) (img z)) LM (dimVD d d<M)

        eq : genW img Γ (χ d) ≡ rnTm ρ (genW img D d)
        eq = trans lhsE
             (trans (rn-extTm imk scI agr)
             (trans (sym (rn-compTm ρ (h5 M Kd ψ') imk)) (cong (rnTm ρ) (sym rhsE))))

      cond : ∀ j → T (j <ℕ top) → lookupₛ σ (h j) ≡ lookupₛ (rnSub ρ σD) j
      cond j pj =
        trans (lk-mkSub (N + (N + x)) e (h j) (bnd j pj))
        (trans (ent j pj)
        (trans (cong (rnTm ρ) (sym (lk-mkSub (L + (L + L)) (entW img D) j jL)))
               (rn-lookup ρ σD j (subst (λ n → T (j <ℕ n)) (sym lenσD) jL))))
        where
        jL : T (j <ℕ L + (L + L))
        jL = <-trans j top (L + (L + L)) pj
               (subst (λ l → T (top <ℕ l + (l + l))) (sym LM)
                 (subst (λ n → T (top <ℕ n)) (sym M3) (n<sn top)))
        ent : ∀ j → T (j <ℕ top) → e (h j) ≡ rnTm ρ (entW img D j)
        ent j pj with view3 M j
        ... | c0 p =
          trans (cong e (hmap-c0 N M χ j p))
          (trans (entE-c0 img Γ (χ j) (χN j p))
          (sym (trans (cong (rnTm ρ) (eD-c0 j p)) (cong var (h5-0 N M χ j p)))))
        ... | c1 d p refl =
          trans (cong e (hmap-c1 N M χ d p))
          (trans (entE-c1 img Γ (χ d) (χN d p))
          (sym (trans (cong (rnTm ρ) (eD-c1 d p)) (cong var (h5-2 N M χ d p)))))
        ... | c2 d refl =
          trans (cong e (hmap-c2 N M χ d))
          (trans (entE-c2 img Γ (χ d))
          (trans (Bd.eq d d<)
          (cong (rnTm ρ) (sym (subst (λ l → entW img D (l + (l + d)) ≡ genW img D d) LM (entE-c2 img D d))))))
          where
          d< : T (d <ℕ dbl m)
          d< = +<-T M d (dbl m) (+<-T M (M + d) (M + dbl m) pj)

    entry : ∀ n → T (n <ℕ L3) → cyl2E sd Γ ⊢tm e n ∶ (g n [ mkSub n e ]ty)
    entry n pn with view3 N n
    ... | c0 p =
      subst (λ t → cyl2E sd Γ ⊢tm t ∶ (g n [ mkSub n e ]ty)) (sym (entE-c0 img Γ n p))
        (subst (cyl2E sd Γ ⊢tm var n ∶_) eqT (var-wf w2 (lk-mk L5 G n (lt-N n N _ p))))
      where
      eqT : G n ≡ g n [ mkSub n e ]ty
      eqT = trans (CΓ.gI-lo n (lt-N n N N p))
            (trans (cong (rnTy (ιI N)) (gN-c0 Ts Γ n p))
            (sym (trans (cong (_[ mkSub n e ]ty) (gN-c0 Ts Γ n p))
                 (sub-varTy (tyAt Γ n) (scAt n p)
                   (λ j pj → trans (lk-mkSub n e j pj)
                             (trans (entE-c0 img Γ j (<-trans j n N pj p))
                                    (cong var (sym (ιI-lo N j (lt-N j N N (<-trans j n N pj p)))))))))))
    ... | c1 x' p refl =
      subst (λ t → cyl2E sd Γ ⊢tm t ∶ (g (N + x') [ mkSub (N + x') e ]ty)) (sym (entE-c1 img Γ x' p))
        (subst (cyl2E sd Γ ⊢tm var (N + (N + x')) ∶_) eqT
          (var-wf w2 (lk-mk L5 G (N + (N + x')) (lt2 N x' (N + (N + N)) (lt-N x' N (N + N) p)))))
      where
      eqT : G (N + (N + x')) ≡ g (N + x') [ mkSub (N + x') e ]ty
      eqT = trans (CΓ.gJ-mid x' p)
            (trans (cong (rnTy (ιJ N)) (gN-c1 Ts Γ x' p))
            (trans (rn-compTy (ιJ N) (N +_) (tyAt Γ x'))
            (trans (rn-extTy (tyAt Γ x') (scAt x' p)
                     (λ j pj → ιJ-lo N (N + j) (T-+< N j N (<-trans j x' N pj p))))
            (sym (trans (cong (_[ mkSub (N + x') e ]ty) (gN-c1 Ts Γ x' p))
                 (sub-rnvar (tyAt Γ x') (scAt x' p)
                   (λ j pj → trans (lk-mkSub (N + x') e (N + j) (T-+< N j x' pj))
                                   (entE-c1 img Γ j (<-trans j x' N pj p)))))))))
    ... | c2 x' refl =
      subst (λ t → cyl2E sd Γ ⊢tm t ∶ (g (N + (N + x')) [ EE.σ ]ty)) (sym (entE-c2 img Γ x'))
        (subst (cyl2E sd Γ ⊢tm rnTm EE.ρ (img EE.m) ∶_) eqT (rn-tm w2 EE.rsp (snd EE.DCm)))
      where
      px' : T (x' <ℕ N)
      px' = +<-T N x' N (+<-T N (N + x') (N + N) pn)
      module EE = E x' px'
      eqT : rnTy EE.ρ (Ts EE.m [ EE.σD ]ty) ≡ g (N + (N + x')) [ EE.σ ]ty
      eqT = trans (rn-[]ty EE.ρ (Ts EE.m) EE.σD EE.scTσ)
                  (sym (trans (cong (_[ EE.σ ]ty) (gN-c2 Ts Γ x'))
                              (sub-rnTy (Ts EE.m) EE.scT EE.cond)))

    sub-all : ∀ n → T (n <ℕ suc L3) → cyl2E sd Γ ⊢sub mkSub n e ∶ mkCtx n g
    sub-all zero    _  = ⟨⟩-wf w2
    sub-all (suc n) pn = ,-wf (sub-all n (<-suc n L3 pn)) (entry n pn)

    compE-wf' : cyl2E sd Γ ⊢sub compW img Γ ∶ cylE sd Γ
    compE-wf' = sub-all L3 (n<sn L3)

-- D13 for vertical composition, reduced to the disks: if the disk
-- images img j are well typed for D^j, j ≤ k, then
-- Γ ⊗ (D¹ ∨ D¹) ⊢ compW img : Γ ⊗ D¹ (and the same for D¹ ⊗ Γ) for
-- every well-formed globular Γ of dimension ≤ k.
compW-wf : ∀ sd (img : Nat → Tm) k → (∀ j → T (j <ℕ suc k) → DiskCertW sd img j) →
           ∀ Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ suc k) →
           (cyl2E sd Γ ⊢ctx) × (cyl2E sd Γ ⊢sub compW img Γ ∶ cylE sd Γ)
compW-wf sd img k DC Γ w gl dk = cyl2E-wf sd Γ w gl , Gen.SubK.compE-wf' sd img Γ w gl k DC dk

-- The instance: the elaborator's disk images.
compE-wf : ∀ sd k → (∀ j → T (j <ℕ suc k) → DiskCert sd j) →
           ∀ Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ suc k) →
           (cyl2E sd Γ ⊢ctx) × (cyl2E sd Γ ⊢sub compE sd Γ ∶ cylE sd Γ)
compE-wf sd = compW-wf sd (imgE sd)
