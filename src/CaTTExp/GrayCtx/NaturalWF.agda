------------------------------------------------------------------------
-- D13: the disk-by-disk cylinder (CaTTExp.GrayCtx.Natural) is well
-- formed for every well-formed globular context Γ of dimension ≤ k,
-- provided the top generator types of D⁰ ⊗ D¹, …, D^k ⊗ D¹ are well
-- typed. No postulates; the disk hypothesis is discharged for k ≤ 5
-- in CaTTExp.GrayCtx.Checks.Natural, and for every k, for the
-- explicit disk types, in CaTTExp.GrayCtx.NaturalAll. `Main` also
-- gives every prefix of the cylinder up to the generators of the
-- variables below a bound B (`prefix-wf`), which that induction uses.
--
-- Proof. Copies of Γ are renamings of Γ. The generator of x is the
-- disk type T_m renamed along χ_x ⊗ D¹, and this renaming respects
-- types because
--   (CL) χ_x : D^m → Γ respects types: Γ(χ_x d) = χ_x(D^m(d));
--   (CC) χ_x ∘ χ^{D^m}_d = χ_{χ_x d}, so the generator of a boundary
--        cell d of D^m is sent to the generator of χ_x d.
-- Renaming along a type-respecting map is admissible (rn-ty).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.NaturalWF where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Natural
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)

closed∅ : Sb.Closed
closed∅ ()

------------------------------------------------------------------------
-- Arithmetic on the builtin comparisons.

T-≡ : ∀ {b} → T b → b ≡ true
T-≡ {true} _ = refl

≡-T : ∀ {b} → b ≡ true → T b
≡-T refl = tt

F-≡ : ∀ {b} → (T b → ⊥) → b ≡ false
F-≡ {true}  p = ⊥-elim (p tt)
F-≡ {false} _ = refl

<-irr : ∀ n → T (n <ℕ n) → ⊥
<-irr (suc n) p = <-irr n p

<-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
<-suc zero    n       _ = tt
<-suc (suc i) (suc n) p = <-suc i n p

<-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans zero    (suc b) (suc c) _ _ = tt
<-trans (suc a) (suc b) (suc c) p q = <-trans a b c p q

-- a ≤ b as a < suc b.
≤-<-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
≤-<-trans zero    b       (suc c) _ _ = tt
≤-<-trans (suc a) (suc b) (suc c) p q = ≤-<-trans a b c p q

<-≤-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ suc c) → T (a <ℕ c)
<-≤-trans zero    (suc b) (suc c) _ _ = tt
<-≤-trans (suc a) (suc b) (suc c) p q = <-≤-trans a b c p q

n<sn : ∀ n → T (n <ℕ suc n)
n<sn zero    = tt
n<sn (suc n) = n<sn n

<→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
<→≢ zero    (suc n) _ = refl
<→≢ (suc i) (suc n) p = <→≢ i n p

>→≢ : ∀ i n → T (n <ℕ i) → (i ==ℕ n) ≡ false
>→≢ (suc i) zero    _ = refl
>→≢ (suc i) (suc n) p = >→≢ i n p

==-refl : ∀ n → (n ==ℕ n) ≡ true
==-refl n = T-≡ (==ℕ-refl n)

-- i < suc n and i ≠ n give i < n.
<suc-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
<suc-≢ zero    zero    _ ()
<suc-≢ zero    (suc n) _ _ = tt
<suc-≢ (suc i) (suc n) p q = <suc-≢ i n p q

+-<-l : ∀ N a b → (N + a <ℕ N + b) ≡ (a <ℕ b)
+-<-l zero    a b = refl
+-<-l (suc N) a b = +-<-l N a b

+-≮ : ∀ N a → (N + a <ℕ N) ≡ false
+-≮ zero    a = refl
+-≮ (suc N) a = +-≮ N a

+-∸ : ∀ N a → (N + a) ∸ N ≡ a
+-∸ zero    a = refl
+-∸ (suc N) a = +-∸ N a

<-+r : ∀ a N → T (a <ℕ N + suc a)
<-+r a zero    = n<sn a
<-+r a (suc N) = <-suc a (N + suc a) (<-+r a N)

<-+ : ∀ a b N → T (a <ℕ b) → T (a <ℕ N + b)
<-+ a b zero    p = p
<-+ a b (suc N) p = <-suc a (N + b) (<-+ a b N p)

-- The three blocks of a cylinder layout.
data View3 (M j : Nat) : Set where
  c0 : T (j <ℕ M) → View3 M j
  c1 : ∀ d → T (d <ℕ M) → j ≡ M + d → View3 M j
  c2 : ∀ d → j ≡ M + (M + d) → View3 M j

∸-split : ∀ M j → (j <ℕ M) ≡ false → j ≡ M + (j ∸ M)
∸-split zero    j       _ = refl
∸-split (suc M) zero    ()
∸-split (suc M) (suc j) e = cong suc (∸-split M j e)

view3 : ∀ M j → View3 M j
view3 M j with j <ℕ M in e₀
... | true = c0 (≡-T e₀)
... | false with (j ∸ M) <ℕ M in e₁
...   | true  = c1 (j ∸ M) (≡-T e₁) (∸-split M j e₀)
...   | false = c2 ((j ∸ M) ∸ M) (trans (∸-split M j e₀) (cong (M +_) (∸-split M (j ∸ M) e₁)))

------------------------------------------------------------------------
-- Renaming on raw syntax.

lenₛ-rn : ∀ f σ → lenₛ (rnSub f σ) ≡ lenₛ σ
lenₛ-rn f ⟨⟩       = refl
lenₛ-rn f (σ ,ₛ t) = cong suc (lenₛ-rn f σ)

rn-lookup : ∀ f σ i → T (i <ℕ lenₛ σ) → rnTm f (lookupₛ σ i) ≡ lookupₛ (rnSub f σ) i
rn-lookup f (σ ,ₛ t) i p rewrite lenₛ-rn f σ with i ==ℕ lenₛ σ in e
... | true  = refl
... | false = rn-lookup f σ i (<suc-≢ i (lenₛ σ) p e)

mutual
  rn-[]ty : ∀ f A σ → ScTy (lenₛ σ) A → rnTy f (A [ σ ]ty) ≡ A [ rnSub f σ ]ty
  rn-[]ty f ⋆           σ _           = refl
  rn-[]ty f (arr A t u) σ (a , p , q) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (rn-[]ty f A σ a)
      (cong₂ _,_ (rn-[]tm f t σ p) (rn-[]tm f u σ q))

  rn-[]tm : ∀ f t σ → ScTm (lenₛ σ) t → rnTm f (t [ σ ]tm) ≡ t [ rnSub f σ ]tm
  rn-[]tm f (var i)     σ p = rn-lookup f σ i p
  rn-[]tm f (coh Δ A τ) σ p = cong (coh Δ A) (rn-∘ f τ σ p)
  rn-[]tm f (cst k)     σ _ = refl

  rn-∘ : ∀ f τ σ → ScSub (lenₛ σ) τ → rnSub f (τ ∘ σ) ≡ τ ∘ rnSub f σ
  rn-∘ f ⟨⟩       σ _       = refl
  rn-∘ f (τ ,ₛ t) σ (p , q) = cong₂ _,ₛ_ (rn-∘ f τ σ p) (rn-[]tm f t σ q)

mutual
  rn-compTy : ∀ f g A → rnTy f (rnTy g A) ≡ rnTy (λ v → f (g v)) A
  rn-compTy f g ⋆           = refl
  rn-compTy f g (arr A t u) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (rn-compTy f g A)
      (cong₂ _,_ (rn-compTm f g t) (rn-compTm f g u))

  rn-compTm : ∀ f g t → rnTm f (rnTm g t) ≡ rnTm (λ v → f (g v)) t
  rn-compTm f g (var i)     = refl
  rn-compTm f g (coh Δ A σ) = cong (coh Δ A) (rn-compSub f g σ)
  rn-compTm f g (cst k)     = refl

  rn-compSub : ∀ f g σ → rnSub f (rnSub g σ) ≡ rnSub (λ v → f (g v)) σ
  rn-compSub f g ⟨⟩       = refl
  rn-compSub f g (σ ,ₛ t) = cong₂ _,ₛ_ (rn-compSub f g σ) (rn-compTm f g t)

-- Renamings agreeing below n agree on terms scoped by n.
Agree : Nat → (Nat → Nat) → (Nat → Nat) → Set
Agree n f g = ∀ v → T (v <ℕ n) → f v ≡ g v

mutual
  rn-extTy : ∀ {n f g} A → ScTy n A → Agree n f g → rnTy f A ≡ rnTy g A
  rn-extTy ⋆           _           _ = refl
  rn-extTy (arr A t u) (a , p , q) h =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (rn-extTy A a h)
      (cong₂ _,_ (rn-extTm t p h) (rn-extTm u q h))

  rn-extTm : ∀ {n f g} t → ScTm n t → Agree n f g → rnTm f t ≡ rnTm g t
  rn-extTm (var i)     p h = cong var (h i p)
  rn-extTm (coh Δ A σ) p h = cong (coh Δ A) (rn-extSub σ p h)
  rn-extTm (cst k)     _ _ = refl

  rn-extSub : ∀ {n f g} σ → ScSub n σ → Agree n f g → rnSub f σ ≡ rnSub g σ
  rn-extSub ⟨⟩       _       _ = refl
  rn-extSub (σ ,ₛ t) (p , q) h = cong₂ _,ₛ_ (rn-extSub σ p h) (rn-extTm t q h)

rn-dim : ∀ f A → dim (rnTy f A) ≡ dim A
rn-dim f ⋆           = refl
rn-dim f (arr A _ _) = cong suc (rn-dim f A)

------------------------------------------------------------------------
-- Renaming along a type-respecting map is admissible.

Resp : (Nat → Nat) → Ctx → Ctx → Set
Resp f Θ Θ' = ∀ i A → lookup Θ i ≡ just A → lookup Θ' (f i) ≡ just (rnTy f A)

module _ {f : Nat → Nat} {Θ Θ' : Ctx} (w' : Θ' ⊢ctx) (r : Resp f Θ Θ') where
  mutual
    rn-ty : ∀ {A} → Θ ⊢ty A → Θ' ⊢ty rnTy f A
    rn-ty (⋆-wf _)     = ⋆-wf w'
    rn-ty (arr-wf d e) = arr-wf (rn-tm d) (rn-tm e)

    rn-tm : ∀ {t A} → Θ ⊢tm t ∶ A → Θ' ⊢tm rnTm f t ∶ rnTy f A
    rn-tm (var-wf {i} {A} _ eq) = var-wf w' (r i A eq)
    rn-tm (coh-wf {Δ} {A} {t} {u} {σ} p w a ok sσ) =
      subst (Θ' ⊢tm coh Δ (arr A t u) (rnSub f σ) ∶_)
        (sym (rn-[]ty f (arr A t u) σ
          (subst (λ n → ScTy n (arr A t u)) (sym (snd (Sb.sub-sc closed∅ sσ)))
                 (Sb.ty-sc closed∅ a))))
        (coh-wf p w a ok (rn-sub w sσ))
    rn-tm (cst-wf {k} _ _) = ⊥-elim k

    rn-sub : ∀ {Δ σ} → Δ ⊢ctx → Θ ⊢sub σ ∶ Δ → Θ' ⊢sub rnSub f σ ∶ Δ
    rn-sub _ (⟨⟩-wf _) = ⟨⟩-wf w'
    rn-sub (▸-wf wΔ b) (,-wf {σ} {Δ} {t} {B} s d) =
      ,-wf (rn-sub wΔ s)
        (subst (Θ' ⊢tm rnTm f t ∶_)
          (rn-[]ty f B σ (subst (λ n → ScTy n B) (sym (snd (Sb.sub-sc closed∅ s)))
                                (Sb.ty-sc closed∅ b)))
          (rn-tm d))

------------------------------------------------------------------------
-- Contexts given levelwise.

len-mk : ∀ n g → len (mkCtx n g) ≡ n
len-mk zero    g = refl
len-mk (suc n) g = cong suc (len-mk n g)

lk-mk : ∀ n g i → T (i <ℕ n) → lookup (mkCtx n g) i ≡ just (g i)
lk-mk (suc n) g i p rewrite len-mk n g with i ==ℕ n in e
... | true  = cong (λ j → just (g j)) (sym (==ℕ-sound i n (≡-T e)))
... | false = lk-mk n g i (<suc-≢ i n p e)

just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

lk-mk-inv : ∀ n g i {A} → lookup (mkCtx n g) i ≡ just A → T (i <ℕ n) × (g i ≡ A)
lk-mk-inv zero    g i ()
lk-mk-inv (suc n) g i eq rewrite len-mk n g with i ==ℕ n in e
... | true  rewrite ==ℕ-sound i n (≡-T e) = n<sn n , just-inj eq
... | false = let (p , q) = lk-mk-inv n g i eq in <-suc i n p , q

tyAt-mk : ∀ n g i → T (i <ℕ n) → tyAt (mkCtx n g) i ≡ g i
tyAt-mk n g i p = cong orStar (lk-mk n g i p)

mk-ext : ∀ n {g g'} → (∀ i → T (i <ℕ n) → g i ≡ g' i) → mkCtx n g ≡ mkCtx n g'
mk-ext zero    h = refl
mk-ext (suc n) h = cong₂ _▸_ (mk-ext n (λ i p → h i (<-suc i n p))) (h n (n<sn n))

ctx-mk : ∀ Γ → Γ ≡ mkCtx (len Γ) (tyAt Γ)
ctx-mk ε       = refl
ctx-mk (Γ ▸ A) =
  cong₂ _▸_ (trans (ctx-mk Γ) (mk-ext (len Γ) λ i p → lo i p))
            (cong orStar (sym (cong (λ b → if b then just A else lookup Γ (len Γ)) (==-refl (len Γ)))))
  where
  lo : ∀ i → T (i <ℕ len Γ) → tyAt Γ i ≡ tyAt (Γ ▸ A) i
  lo i p rewrite <→≢ i (len Γ) p = refl

lookup-tyAt : ∀ Γ i {A} → lookup Γ i ≡ just A → tyAt Γ i ≡ A
lookup-tyAt Γ i eq = cong orStar eq

inv-mk : ∀ n g i → mkCtx n g ⊢ctx → T (i <ℕ n) → (mkCtx i g ⊢ctx) × (mkCtx i g ⊢ty g i)
inv-mk (suc n) g i (▸-wf w a) p with i ==ℕ n in e
... | true  rewrite ==ℕ-sound i n (≡-T e) = w , a
... | false = inv-mk n g i w (<suc-≢ i n p e)

-- A well-formed context, levelwise.
ctx-inv : ∀ Γ i → Γ ⊢ctx → T (i <ℕ len Γ) → mkCtx i (tyAt Γ) ⊢ty tyAt Γ i
ctx-inv Γ i w p = snd (inv-mk (len Γ) (tyAt Γ) i (subst _⊢ctx (ctx-mk Γ) w) p)

-- Building a context level by level.
mk-wf : ∀ n g → (∀ i → T (i <ℕ n) → mkCtx i g ⊢ctx → mkCtx i g ⊢ty g i) → mkCtx n g ⊢ctx
mk-wf zero    g h = ε-wf
mk-wf (suc n) g h = let w = mk-wf n g (λ i p → h i (<-suc i n p)) in ▸-wf w (h n (n<sn n) w)

-- A lookup in a prefix is a lookup in the whole.
lk-prefix : ∀ n g i {A} → lookup (mkCtx n g) i ≡ just A → ∀ m → T (n <ℕ suc m) →
            lookup (mkCtx m g) i ≡ just A
lk-prefix n g i eq m q =
  let (p , r) = lk-mk-inv n g i eq in
  trans (lk-mk m g i (<-≤-trans i n m p q)) (cong just r)

------------------------------------------------------------------------
-- Disks.

half-dbl : ∀ k → half (dbl k) ≡ k
half-dbl zero    = refl
half-dbl (suc k) = cong suc (half-dbl k)

half-sdbl : ∀ k → half (suc (dbl k)) ≡ k
half-sdbl zero    = refl
half-sdbl (suc k) = cong suc (half-sdbl k)

dbl-half : ∀ d → T (dbl (half d) <ℕ suc d)
dbl-half zero          = tt
dbl-half (suc zero)    = tt
dbl-half (suc (suc d)) = dbl-half d

dim-aL : ∀ k → dim (aL k) ≡ k
dim-aL zero    = refl
dim-aL (suc k) = cong suc (dim-aL k)

<-dbl : ∀ k → T (dbl k <ℕ suc (suc (dbl k)))
<-dbl k = <-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))

sc-mono : ∀ a b A → T (a <ℕ suc b) → ScTy a A → ScTy b A
sc-mono a b A p s = go A s
  where
  mutual
    go : ∀ A → ScTy a A → ScTy b A
    go ⋆           _           = tt
    go (arr A t u) (x , y , z) = go A x , goT t y , goT u z
    goT : ∀ t → ScTm a t → ScTm b t
    goT (var i)     q = <-≤-trans i a b q p
    goT (coh _ _ σ) q = goS σ q
    goT (cst _)     _ = tt
    goS : ∀ σ → ScSub a σ → ScSub b σ
    goS ⟨⟩       _       = tt
    goS (σ ,ₛ t) (x , y) = goS σ x , goT t y

sc-aL : ∀ k → ScTy (dbl k) (aL k)
sc-aL zero    = tt
sc-aL (suc k) = sc-mono (dbl k) (suc (suc (dbl k))) (aL k) (<-suc (dbl k) (suc (suc (dbl k))) (<-dbl k)) (sc-aL k)
              , <-dbl k , n<sn (suc (dbl k))

sc-aD : ∀ d → ScTy (dbl (half d)) (aD d)
sc-aD d = sc-aL (half d)

-- One step of a classifying map, away from its top two levels.
chi-step : ∀ Γ k x v → T (v <ℕ suc (dbl k)) → chiK Γ (suc k) x v ≡ chiK Γ k (src Γ x) v
chi-step Γ k x v p
  rewrite <→≢ v (suc (suc (dbl k))) (<-trans v (suc (dbl k)) (suc (suc (dbl k))) p (n<sn (suc (dbl k))))
        | <→≢ v (suc (dbl k)) p = refl

chi-top : ∀ Γ m x → chiK Γ m x (dbl m) ≡ x
chi-top Γ zero    x = refl
chi-top Γ (suc k) x rewrite ==-refl (dbl k) = refl

-- Parallel cells have the same classifying map below the top.
chi-par : ∀ Γ k s t → tyAt Γ s ≡ tyAt Γ t → ∀ v → T (v <ℕ dbl k) → chiK Γ k s v ≡ chiK Γ k t v
chi-par Γ (suc j) s t e v p
  rewrite <→≢ v (suc (suc (dbl j))) p with v ==ℕ suc (dbl j)
... | true  = cong tgtT e
... | false = cong (λ z → chiK Γ j z v) (cong srcT e)

-- d < 2k+2 is below 2k, or 2k, or 2k+1.
data Vw (k d : Nat) : Set where
  below : T (d <ℕ dbl k) → Vw k d
  isS   : d ≡ dbl k → Vw k d
  isT   : d ≡ suc (dbl k) → Vw k d

vw : ∀ k d → T (d <ℕ suc (suc (dbl k))) → Vw k d
vw k d p with d ==ℕ suc (dbl k) in e₁
... | true = isT (==ℕ-sound d _ (≡-T e₁))
... | false with d ==ℕ dbl k in e₂
...   | true  = isS (==ℕ-sound d _ (≡-T e₂))
...   | false = below (<suc-≢ d (dbl k) (<suc-≢ d (suc (dbl k)) p e₁) e₂)

------------------------------------------------------------------------
-- Classifying maps in a well-formed globular context.

tyAt-▸ : ∀ Γ A i → T (i <ℕ len Γ) → tyAt (Γ ▸ A) i ≡ tyAt Γ i
tyAt-▸ Γ A i p rewrite <→≢ i (len Γ) p = refl

glob-at : ∀ Γ i → T (globular Γ) → T (i <ℕ len Γ) → T (globTy (tyAt Γ i))
glob-at (Γ ▸ A) i g p with i ==ℕ len Γ in e
... | true  = ∧-snd {globular Γ} g
... | false = glob-at Γ i (∧-fst g) (<suc-≢ i (len Γ) p e)

module Classify (Γ : Ctx) (w : Γ ⊢ctx) (gl : T (globular Γ)) where
  N = len Γ

  data Shape (x : Nat) : Set where
    pt : tyAt Γ x ≡ ⋆ → Shape x
    ar : ∀ A s t → tyAt Γ x ≡ arr A (var s) (var t) → T (s <ℕ x) → T (t <ℕ x)
       → tyAt Γ s ≡ A → tyAt Γ t ≡ A → Shape x

  private
    shape' : ∀ x B → tyAt Γ x ≡ B → mkCtx x (tyAt Γ) ⊢ty B → T (globTy B) → Shape x
    shape' x ⋆ e _ _ = pt e
    shape' x (arr A (var s) (var t)) e (arr-wf (var-wf _ es) (var-wf _ et)) _ =
      let (ls , qs) = lk-mk-inv x (tyAt Γ) s es
          (pt' , qt) = lk-mk-inv x (tyAt Γ) t et in
      ar A s t e ls pt' qs qt
    shape' x (arr A (var _) (coh _ _ _)) _ _ ()
    shape' x (arr A (var _) (cst _))     _ _ ()
    shape' x (arr A (coh _ _ _) _)       _ _ ()
    shape' x (arr A (cst _) _)           _ _ ()

  shape : ∀ x → T (x <ℕ N) → Shape x
  shape x p = shape' x (tyAt Γ x) refl (ctx-inv Γ x w p) (glob-at Γ x gl p)

  sucinj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  sucinj refl = refl

  0≢s : ∀ {a} → zero ≡ suc a → ⊥
  0≢s ()

  data V (k : Nat) : Nat → Set where
    vTop : V k (suc (suc (dbl k)))
    vT   : V k (suc (dbl k))
    vLow : ∀ {d} → T (d <ℕ suc (dbl k)) → V k d

  vw' : ∀ k d → T (d <ℕ suc (suc (suc (dbl k)))) → V k d
  vw' k d r with d ==ℕ suc (suc (dbl k)) in e₁
  ... | true rewrite ==ℕ-sound d _ (≡-T e₁) = vTop
  ... | false = low (vw k d (<suc-≢ d (suc (suc (dbl k))) r e₁))
    where
    low : Vw k d → V k d
    low (below b) = vLow (<-suc d (dbl k) b)
    low (isS refl) = vLow (n<sn (dbl k))
    low (isT refl) = vT

  CLty : Nat → Nat → Nat → Set
  CLty m x d = T (chiK Γ m x d <ℕ suc x)
             × (T (d <ℕ dbl m) → T (chiK Γ m x d <ℕ x))
             × (tyAt Γ (chiK Γ m x d) ≡ rnTy (chiK Γ m x) (aD d))

  -- (CL) χ_x respects types, and sends the boundary below x.
  CL : ∀ m x → dimV Γ x ≡ m → T (x <ℕ N) → ∀ d → T (d <ℕ suc (dbl m)) → CLty m x d
  CL zero x dm p zero _ with shape x p
  ... | pt e = n<sn x , (λ ()) , e
  ... | ar A s t e _ _ _ _ = ⊥-elim (0≢s (trans (sym dm) (cong dim e)))
  CL (suc k) x dm p d q with shape x p
  ... | pt e = ⊥-elim (0≢s (trans (sym (cong dim e)) dm))
  ... | ar A s t e ls lt es et = go d (vw' k d q)
    where
    dA : dim A ≡ k
    dA = sucinj (trans (sym (cong dim e)) dm)
    srcx : src Γ x ≡ s
    srcx = cong srcT e
    tgtx : tgt Γ x ≡ t
    tgtx = cong tgtT e
    sN : T (s <ℕ N)
    sN = <-trans s x N ls p
    χ = chiK Γ (suc k) x
    agr : ∀ n → T (n <ℕ suc (suc (dbl k))) → Agree n χ (chiK Γ k s)
    agr n r v pv = trans (chi-step Γ k x v (<-≤-trans v n (suc (dbl k)) pv r))
                         (cong (λ z → chiK Γ k z v) srcx)
    IH : ∀ d → T (d <ℕ suc (dbl k)) → CLty k s d
    IH = CL k s (trans (cong dim es) dA) sN
    χaL : rnTy χ (aL k) ≡ A
    χaL = trans (rn-extTy (aL k) (sc-aL k) (agr (dbl k) (<-dbl k)))
         (trans (sym (subst (λ D → tyAt Γ (chiK Γ k s (dbl k)) ≡ rnTy (chiK Γ k s) (aL D))
                            (half-dbl k) (snd (snd (IH (dbl k) (n<sn (dbl k)))))))
                (trans (cong (tyAt Γ) (chi-top Γ k s)) es))
    χs : χ (dbl k) ≡ s
    χs = trans (chi-step Γ k x (dbl k) (n<sn (dbl k)))
               (trans (cong (λ z → chiK Γ k z (dbl k)) srcx) (chi-top Γ k s))
    χt : χ (suc (dbl k)) ≡ t
    χt rewrite <→≢ (dbl k) (suc (dbl k)) (n<sn (dbl k)) | ==-refl (dbl k) = tgtx
    go : ∀ d → V k d → CLty (suc k) x d
    go _ vTop rewrite ==-refl (dbl k) | half-dbl k =
      n<sn x , (λ r → ⊥-elim (<-irr (dbl k) r)) ,
      trans e (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (sym χaL)
                (cong₂ _,_ (cong var (sym χs)) (cong var (sym χt))))
    go _ vT =
      subst (λ z → T (z <ℕ suc x) × (T (suc (dbl k) <ℕ dbl (suc k)) → T (z <ℕ x))
                 × (tyAt Γ z ≡ rnTy χ (aD (suc (dbl k)))))
            (sym χt)
            (<-suc t x lt , (λ _ → lt) ,
             trans et (sym (trans (cong (λ D → rnTy χ (aL D)) (half-sdbl k)) χaL)))
    go d (vLow r) =
      let (b1 , _ , b3) = IH d r
          eqd : χ d ≡ chiK Γ k s d
          eqd = trans (chi-step Γ k x d r) (cong (λ z → chiK Γ k z d) srcx)
          bnd = ≤-<-trans (dbl (half d)) d (suc (suc (dbl k))) (dbl-half d) (<-suc d (suc (dbl k)) r) in
      subst (λ z → T (z <ℕ suc x) × (T (d <ℕ dbl (suc k)) → T (z <ℕ x))
                 × (tyAt Γ z ≡ rnTy χ (aD d)))
            (sym eqd)
            (≤-<-trans (chiK Γ k s d) s (suc x) b1 (<-suc s x ls) ,
             (λ _ → ≤-<-trans (chiK Γ k s d) s x b1 ls) ,
             trans b3 (sym (rn-extTy (aD d) (sc-aD d) (agr (dbl (half d)) bnd))))

  χs-of : ∀ k x A s t → tyAt Γ x ≡ arr A (var s) (var t) → chiK Γ (suc k) x (dbl k) ≡ s
  χs-of k x A s t e = trans (chi-step Γ k x (dbl k) (n<sn (dbl k)))
                            (trans (cong (λ z → chiK Γ k z (dbl k)) (cong srcT e)) (chi-top Γ k s))

  χt-of : ∀ k x A s t → tyAt Γ x ≡ arr A (var s) (var t) → chiK Γ (suc k) x (suc (dbl k)) ≡ t
  χt-of k x A s t e rewrite <→≢ (dbl k) (suc (dbl k)) (n<sn (dbl k)) | ==-refl (dbl k) = cong tgtT e

  -- Below the top, χ_x agrees with the classifying map of its boundary cells.
  P : ∀ m x → dimV Γ x ≡ m → T (x <ℕ N) → ∀ d v → T (d <ℕ dbl m) → T (v <ℕ dbl (half d)) →
      chiK Γ m x v ≡ chiK Γ (half d) (chiK Γ m x d) v
  P zero x dm p d v () _
  P (suc k) x dm p d v q pv with shape x p
  ... | pt e = ⊥-elim (0≢s (trans (sym (cong dim e)) dm))
  ... | ar A s t e ls lt es et =
    trans (trans (chi-step Γ k x v v<) (cong (λ z → chiK Γ k z v) (cong srcT e))) (go (vw k d q))
    where
    dA : dim A ≡ k
    dA = sucinj (trans (sym (cong dim e)) dm)
    v<d : T (v <ℕ d)
    v<d = <-≤-trans v (dbl (half d)) d pv (dbl-half d)
    v< : T (v <ℕ suc (dbl k))
    v< = <-≤-trans v d (suc (dbl k)) v<d q
    go : Vw k d → chiK Γ k s v ≡ chiK Γ (half d) (chiK Γ (suc k) x d) v
    go (below b) =
      trans (P k s (trans (cong dim es) dA) (<-trans s x N ls p) d v b pv)
            (cong (λ z → chiK Γ (half d) z v)
                  (sym (trans (chi-step Γ k x d (<-suc d (dbl k) b)) (cong (λ z → chiK Γ k z d) (cong srcT e)))))
    go (isS refl) rewrite half-dbl k | χs-of k x A s t e = refl
    go (isT refl) rewrite half-sdbl k | χt-of k x A s t e =
      chi-par Γ k s t (trans es (sym et)) v pv

  -- Classifying maps of the disk itself: inclusions.
  chiD : ∀ m k z v → T (z <ℕ suc (dbl m)) → half z ≡ k → T (v <ℕ suc (dbl k)) →
         chiK (Disk m) k z v ≡ (if v ==ℕ dbl k then z else v)
  chiD m zero    z zero    _ _ _  = refl
  chiD m zero    z (suc v) _ _ ()
  chiD m (suc j) z v pz hz pv with v ==ℕ suc (suc (dbl j)) in e₁
  ... | true  = refl
  ... | false with v ==ℕ suc (dbl j) in e₂
  ...   | true  = trans (cong tgtT tz) (sym (==ℕ-sound v _ (≡-T e₂)))
    where
    tz : tyAt (Disk m) z ≡ aL (suc j)
    tz = trans (tyAt-mk (suc (dbl m)) aD z pz) (cong aL hz)
  ...   | false =
    trans (cong (λ y → chiK (Disk m) j y v) (cong srcT tz))
          (trans (chiD m j (dbl j) v dj< (half-dbl j) v<) (fin (v ==ℕ dbl j) refl))
    where
    tz : tyAt (Disk m) z ≡ aL (suc j)
    tz = trans (tyAt-mk (suc (dbl m)) aD z pz) (cong aL hz)
    v< : T (v <ℕ suc (dbl j))
    v< = <suc-≢ v (suc (dbl j)) (<suc-≢ v (suc (suc (dbl j))) pv e₁) e₂
    dj< : T (dbl j <ℕ suc (dbl m))
    dj< = <-trans (dbl j) z (suc (dbl m))
            (<-≤-trans (dbl j) (suc (suc (dbl j))) z (<-dbl j)
              (subst (λ h → T (dbl h <ℕ suc z)) hz (dbl-half z)))
            pz
    fin : ∀ b → (v ==ℕ dbl j) ≡ b → (if b then dbl j else v) ≡ v
    fin true  e = sym (==ℕ-sound v _ (≡-T e))
    fin false _ = refl

  dimV-Disk : ∀ m d → T (d <ℕ suc (dbl m)) → dimV (Disk m) d ≡ half d
  dimV-Disk m d p = trans (cong dim (tyAt-mk (suc (dbl m)) aD d p)) (dim-aL (half d))

  -- (CC) χ_x ∘ χ^{D^m}_d = χ_{χ_x d}.
  CC : ∀ m x → dimV Γ x ≡ m → T (x <ℕ N) → ∀ d → T (d <ℕ dbl m) →
       ∀ v → T (v <ℕ suc (dbl (half d))) →
       chiK Γ m x (chiK (Disk m) (half d) d v) ≡ chi Γ (chiK Γ m x d) v
  CC m x dm p d q v pv =
    trans (cong (chiK Γ m x) (chiD m (half d) d v d< refl pv))
          (trans (fin (v ==ℕ dbl (half d)) refl)
                 (cong (λ h → chiK Γ h (chiK Γ m x d) v) (sym dimχ)))
    where
    d< : T (d <ℕ suc (dbl m))
    d< = <-suc d (dbl m) q
    dimχ : dimV Γ (chiK Γ m x d) ≡ half d
    dimχ = trans (cong dim (snd (snd (CL m x dm p d d<))))
                 (trans (rn-dim (chiK Γ m x) (aD d)) (dim-aL (half d)))
    fin : ∀ b → (v ==ℕ dbl (half d)) ≡ b →
          chiK Γ m x (if b then d else v) ≡ chiK Γ (half d) (chiK Γ m x d) v
    fin true  e rewrite ==ℕ-sound v _ (≡-T e) = sym (chi-top Γ (half d) (chiK Γ m x d))
    fin false e = P m x dm p d v q (<suc-≢ v (dbl (half d)) pv e)

------------------------------------------------------------------------
-- The layout, computed.

lt-N : ∀ a N y → T (a <ℕ N) → T (a <ℕ N + y)
lt-N zero    (suc N) y _ = tt
lt-N (suc a) (suc N) y p = lt-N a N y p

+<-T : ∀ N a b → T (N + a <ℕ N + b) → T (a <ℕ b)
+<-T N a b p = subst T (+-<-l N a b) p

T-+< : ∀ N a b → T (a <ℕ b) → T (N + a <ℕ N + b)
T-+< N a b p = subst T (sym (+-<-l N a b)) p

half-< : ∀ d m → T (d <ℕ dbl m) → T (half d <ℕ m)
half-< zero          (suc m) _ = tt
half-< (suc zero)    (suc m) _ = tt
half-< (suc (suc d)) (suc m) p = half-< d m p

hmap-c0 : ∀ N M χ j → T (j <ℕ M) → hmap N M χ j ≡ χ j
hmap-c0 N M χ j p rewrite T-≡ p = refl

hmap-c1 : ∀ N M χ d → T (d <ℕ M) → hmap N M χ (M + d) ≡ N + χ d
hmap-c1 N M χ d p rewrite +-≮ M d | +-<-l M d M | T-≡ p | +-∸ M d = refl

hmap-c2 : ∀ N M χ d → hmap N M χ (M + (M + d)) ≡ N + (N + χ d)
hmap-c2 N M χ d rewrite +-≮ M (M + d) | +-<-l M (M + d) M | +-≮ M d | +-∸ M (M + d) | +-∸ M d = refl

gN-c0 : ∀ Ts Γ i → T (i <ℕ len Γ) → gN Ts Γ i ≡ tyAt Γ i
gN-c0 Ts Γ i p rewrite T-≡ p = refl

gN-c1 : ∀ Ts Γ x → T (x <ℕ len Γ) → gN Ts Γ (len Γ + x) ≡ rnTy (len Γ +_) (tyAt Γ x)
gN-c1 Ts Γ x p rewrite +-≮ (len Γ) x | +-<-l (len Γ) x (len Γ) | T-≡ p | +-∸ (len Γ) x = refl

gN-c2 : ∀ Ts Γ x → gN Ts Γ (len Γ + (len Γ + x))
      ≡ rnTy (hmap (len Γ) (suc (dbl (dimV Γ x))) (chi Γ x)) (Ts (dimV Γ x))
gN-c2 Ts Γ x
  rewrite +-≮ (len Γ) (len Γ + x) | +-<-l (len Γ) (len Γ + x) (len Γ) | +-≮ (len Γ) x
        | +-∸ (len Γ) (len Γ + x) | +-∸ (len Γ) x = refl

len-D : ∀ m → len (Disk m) ≡ suc (dbl m)
len-D m = len-mk (suc (dbl m)) aD

gD-c0 : ∀ Ts m j → T (j <ℕ suc (dbl m)) → gN Ts (Disk m) j ≡ aD j
gD-c0 Ts m j p = trans (gN-c0 Ts (Disk m) j (subst (λ L → T (j <ℕ L)) (sym (len-D m)) p))
                       (tyAt-mk (suc (dbl m)) aD j p)

gD-c1 : ∀ Ts m d → T (d <ℕ suc (dbl m)) →
        gN Ts (Disk m) (suc (dbl m) + d) ≡ rnTy (suc (dbl m) +_) (aD d)
gD-c1 Ts m d p =
  trans (subst (λ L → gN Ts (Disk m) (L + d) ≡ rnTy (L +_) (tyAt (Disk m) d)) (len-D m)
               (gN-c1 Ts (Disk m) d (subst (λ L → T (d <ℕ L)) (sym (len-D m)) p)))
        (cong (rnTy (suc (dbl m) +_)) (tyAt-mk (suc (dbl m)) aD d p))

gD-c2 : ∀ Ts m d → T (d <ℕ suc (dbl m)) →
        gN Ts (Disk m) (suc (dbl m) + (suc (dbl m) + d))
      ≡ rnTy (hmap (suc (dbl m)) (suc (dbl (half d))) (chiK (Disk m) (half d) d)) (Ts (half d))
gD-c2 Ts m d p =
  trans (subst (λ L → gN Ts (Disk m) (L + (L + d))
                    ≡ rnTy (hmap L (suc (dbl (dimV (Disk m) d))) (chi (Disk m) d)) (Ts (dimV (Disk m) d)))
               (len-D m) (gN-c2 Ts (Disk m) d))
        (cong (λ h → rnTy (hmap (suc (dbl m)) (suc (dbl h)) (chiK (Disk m) h d)) (Ts h))
              (dimV-Disk m d p))
  where
  dimV-Disk : ∀ m d → T (d <ℕ suc (dbl m)) → dimV (Disk m) d ≡ half d
  dimV-Disk m d p = trans (cong dim (tyAt-mk (suc (dbl m)) aD d p)) (dim-aL (half d))


------------------------------------------------------------------------
-- The theorem.

module Main (Ts : Nat → Ty) (k : Nat)
            (H : ∀ j → T (j <ℕ suc k) → diskPre Ts j ⊢ty Ts j)
            (Γ : Ctx) (w : Γ ⊢ctx) (gl : T (globular Γ))
            (B : Nat) (BN : T (B <ℕ suc (len Γ)))
            (dk : ∀ x → T (x <ℕ B) → T (dimV Γ x <ℕ suc k)) where
  open Classify Γ w gl

  g : Nat → Ty
  g = gN Ts Γ

  psi-bound : ∀ m d v → T (d <ℕ suc (dbl m)) → T (v <ℕ suc (dbl (half d))) →
              T (chiK (Disk m) (half d) d v <ℕ suc d)
  psi-bound m d v p q rewrite chiD m (half d) d v p refl q = fin (v ==ℕ dbl (half d))
    where
    fin : ∀ b → T ((if b then d else v) <ℕ suc d)
    fin true  = n<sn d
    fin false = ≤-<-trans v (dbl (half d)) (suc d) q (dbl-half d)

  -- The generator block of a variable x < B: its disk renames into
  -- the cylinder along h, respecting types.
  module C2 (x : Nat) (pB : T (x <ℕ B)) where
    px : T (x <ℕ N)
    px = <-≤-trans x B N pB BN
    m = dimV Γ x
    M = suc (dbl m)
    χ = chiK Γ m x
    h = hmap N M χ
    CLx = CL m x refl px
    χN : ∀ j → T (j <ℕ M) → T (χ j <ℕ N)
    χN j pj = ≤-<-trans (χ j) x N (fst (CLx j pj)) px
    dq : ∀ d → T (M + (M + d) <ℕ M + (M + dbl m)) → T (d <ℕ dbl m)
    dq d p = +<-T M d (dbl m) (+<-T M (M + d) (M + dbl m) p)
    dimχ : ∀ d → T (d <ℕ M) → dimV Γ (χ d) ≡ half d
    dimχ d p = trans (cong dim (snd (snd (CLx d p)))) (trans (rn-dim χ (aD d)) (dim-aL (half d)))
    <M : ∀ v j → T (v <ℕ dbl (half j)) → T (j <ℕ M) → T (v <ℕ M)
    <M v j pv pj = <-trans v j M (<-≤-trans v (dbl (half j)) j pv (dbl-half j)) pj

    bnd : ∀ j → T (j <ℕ M + (M + dbl m)) → T (h j <ℕ N + (N + x))
    bnd j pj with view3 M j
    ... | c0 p rewrite hmap-c0 N M χ j p = lt-N (χ j) N (N + x) (χN j p)
    ... | c1 d p refl rewrite hmap-c1 N M χ d p = T-+< N (χ d) (N + x) (lt-N (χ d) N x (χN d p))
    ... | c2 d refl rewrite hmap-c2 N M χ d =
      T-+< N (N + χ d) (N + x) (T-+< N (χ d) x (fst (snd (CLx d (<-suc d (dbl m) (dq d pj)))) (dq d pj)))

    geq : ∀ j → T (j <ℕ M + (M + dbl m)) → g (h j) ≡ rnTy h (gN Ts (Disk m) j)
    geq j pj with view3 M j
    ... | c0 p =
      trans (cong g (hmap-c0 N M χ j p))
      (trans (gN-c0 Ts Γ (χ j) (χN j p))
      (trans (snd (snd (CLx j p)))
      (sym (trans (cong (rnTy h) (gD-c0 Ts m j p))
                  (rn-extTy (aD j) (sc-aD j) (λ v pv → hmap-c0 N M χ v (<M v j pv p)))))))
    ... | c1 d p refl =
      trans (cong g (hmap-c1 N M χ d p))
      (trans (gN-c1 Ts Γ (χ d) (χN d p))
      (trans (cong (rnTy (N +_)) (snd (snd (CLx d p))))
      (trans (rn-compTy (N +_) χ (aD d))
      (sym (trans (cong (rnTy h) (gD-c1 Ts m d p))
           (trans (rn-compTy h (M +_) (aD d))
                  (rn-extTy (aD d) (sc-aD d) (λ v pv → hmap-c1 N M χ v (<M v d pv p)))))))))
    ... | c2 d refl =
      trans (cong g (hmap-c2 N M χ d))
      (trans (gN-c2 Ts Γ (χ d))
      (trans (cong (λ e → rnTy (hmap N (suc (dbl e)) (chiK Γ e (χ d))) (Ts e)) (dimχ d d<M))
      (sym (trans (cong (rnTy h) (gD-c2 Ts m d d<M))
           (trans (rn-compTy h (hmap M Kd ψ) (Ts kd))
                  (sym (rn-extTy (Ts kd) scT agr)))))))
      where
      d< : T (d <ℕ dbl m)
      d< = dq d pj
      d<M : T (d <ℕ M)
      d<M = <-suc d (dbl m) d<
      kd = half d
      Kd = suc (dbl kd)
      ψ = chiK (Disk m) kd d
      φ = chiK Γ kd (χ d)
      hk : T (kd <ℕ suc k)
      hk = <-trans kd m (suc k) (half-< d m d<) (dk x pB)
      scT : ScTy (Kd + (Kd + dbl kd)) (Ts kd)
      scT = subst (λ n → ScTy n (Ts kd)) (len-mk (Kd + (Kd + dbl kd)) (gN Ts (Disk kd)))
                  (Sb.ty-sc closed∅ (H kd hk))
      ψM : ∀ v → T (v <ℕ Kd) → T (ψ v <ℕ M)
      ψM v pv = ≤-<-trans (ψ v) d M (psi-bound m d v d<M pv) d<M
      cc : ∀ v → T (v <ℕ Kd) → χ (ψ v) ≡ φ v
      cc v pv = trans (CC m x refl px d d< v pv) (cong (λ e → chiK Γ e (χ d) v) (dimχ d d<M))
      agr : Agree (Kd + (Kd + dbl kd)) (hmap N Kd φ) (λ v → h (hmap M Kd ψ v))
      agr v pv with view3 Kd v
      ... | c0 p' rewrite hmap-c0 N Kd φ v p' | hmap-c0 M Kd ψ v p' | hmap-c0 N M χ (ψ v) (ψM v p') =
        sym (cc v p')
      ... | c1 u p' refl rewrite hmap-c1 N Kd φ u p' | hmap-c1 M Kd ψ u p' | hmap-c1 N M χ (ψ u) (ψM u p') =
        cong (N +_) (sym (cc u p'))
      ... | c2 u refl rewrite hmap-c2 N Kd φ u | hmap-c2 M Kd ψ u | hmap-c2 N M χ (ψ u) =
        cong (λ z → N + (N + z)) (sym (cc u (<-suc u (dbl kd) (+<-T Kd u (dbl kd) (+<-T Kd (Kd + u) (Kd + dbl kd) pv)))))

    r : Resp h (diskPre Ts m) (mkCtx (N + (N + x)) g)
    r j B eq =
      let (pj , qj) = lk-mk-inv (M + (M + dbl m)) (gN Ts (Disk m)) j eq in
      trans (lk-mk (N + (N + x)) g (h j) (bnd j pj))
            (cong just (trans (geq j pj) (cong (rnTy h) qj)))

  obl : ∀ n → T (n <ℕ N + (N + B)) → mkCtx n g ⊢ctx → mkCtx n g ⊢ty g n
  obl n pn wn with view3 N n
  ... | c0 p =
    subst (mkCtx n g ⊢ty_) (sym (gN-c0 Ts Γ n p))
      (subst (_⊢ty tyAt Γ n) (mk-ext n (λ i pi → sym (gN-c0 Ts Γ i (<-trans i n N pi p))))
        (ctx-inv Γ n w p))
  ... | c1 x px refl =
    subst (mkCtx (N + x) g ⊢ty_) (sym (gN-c1 Ts Γ x px)) (rn-ty wn r (ctx-inv Γ x w px))
    where
    r : Resp (N +_) (mkCtx x (tyAt Γ)) (mkCtx (N + x) g)
    r i A eq = let (pi , qi) = lk-mk-inv x (tyAt Γ) i eq in
      trans (lk-mk (N + x) g (N + i) (T-+< N i x pi))
            (cong just (trans (gN-c1 Ts Γ i (<-trans i x N pi px)) (cong (rnTy (N +_)) qi)))
  ... | c2 x refl =
    subst (mkCtx (N + (N + x)) g ⊢ty_) (sym (gN-c2 Ts Γ x))
      (rn-ty wn (C2.r x pB) (H (dimV Γ x) (dk x pB)))
    where
    pB : T (x <ℕ B)
    pB = +<-T N x B (+<-T N (N + x) (N + B) pn)

  -- The prefix up to the generators of the variables below B.
  prefix-wf : mkCtx (N + (N + B)) g ⊢ctx
  prefix-wf = mk-wf (N + (N + B)) g obl

  cylWith-wf : B ≡ len Γ → cylWith Ts Γ ⊢ctx
  cylWith-wf e = subst (λ b → mkCtx (N + (N + b)) g ⊢ctx) e prefix-wf

------------------------------------------------------------------------
-- From the parametrised theorem to cylN.

-- Every variable's dimension is at most dimCtx Γ.
max-l : ∀ a b → T (a <ℕ suc (max a b))
max-l zero    b       = tt
max-l (suc a) zero    = n<sn a
max-l (suc a) (suc b) = max-l a b

max-r : ∀ a b → T (b <ℕ suc (max a b))
max-r zero    b       = n<sn b
max-r (suc a) zero    = tt
max-r (suc a) (suc b) = max-r a b

dimV-≤ : ∀ Γ x → T (x <ℕ len Γ) → T (dimV Γ x <ℕ suc (dimCtx Γ))
dimV-≤ (Γ ▸ A) x p with x ==ℕ len Γ in e
... | true  = max-l (dim A) (dimCtx Γ)
... | false = ≤-<-trans (dimV Γ x) (dimCtx Γ) (suc (max (dim A) (dimCtx Γ)))
                (dimV-≤ Γ x (<suc-≢ x (len Γ) p e)) (max-r (dim A) (dimCtx Γ))

-- The disk list is consistent: its j-th entry is T_j.
length : List Ty → Nat
length []       = zero
length (_ ∷ As) = suc (length As)

length-snoc : ∀ As A → length (snocL As A) ≡ suc (length As)
length-snoc []       A = refl
length-snoc (_ ∷ As) A = cong suc (length-snoc As A)

nth-snoc : ∀ As A i → T (i <ℕ length As) → nth (snocL As A) i ≡ nth As i
nth-snoc (_ ∷ As) A zero    _ = refl
nth-snoc (_ ∷ As) A (suc i) p = nth-snoc As A i p

length-diskTys : ∀ sd k → length (diskTys sd k) ≡ suc k
length-diskTys sd zero    = refl
length-diskTys sd (suc k) = trans (length-snoc (diskTys sd k) _) (cong suc (length-diskTys sd k))

nth-diskTys : ∀ sd k j → T (j <ℕ suc k) → nth (diskTys sd k) j ≡ TsF sd j
nth-diskTys sd zero    zero    _ = refl
nth-diskTys sd (suc k) j p with j ==ℕ suc k in e
... | true  rewrite ==ℕ-sound j (suc k) (≡-T e) = refl
... | false =
  trans (nth-snoc (diskTys sd k) _ j (subst (λ L → T (j <ℕ L)) (sym (length-diskTys sd k))
                                            (<suc-≢ j (suc k) p e)))
        (nth-diskTys sd k j (<suc-≢ j (suc k) p e))

-- gN only reads Ts at the dimensions of Γ.
gN-ext : ∀ Ts Ts' Γ → (∀ x → T (x <ℕ len Γ) → Ts (dimV Γ x) ≡ Ts' (dimV Γ x)) →
         ∀ i → T (i <ℕ len Γ + (len Γ + len Γ)) → gN Ts Γ i ≡ gN Ts' Γ i
gN-ext Ts Ts' Γ h i p with view3 (len Γ) i
... | c0 q = trans (gN-c0 Ts Γ i q) (sym (gN-c0 Ts' Γ i q))
... | c1 x q refl = trans (gN-c1 Ts Γ x q) (sym (gN-c1 Ts' Γ x q))
... | c2 x refl =
  trans (gN-c2 Ts Γ x)
        (trans (cong (rnTy (hmap (len Γ) (suc (dbl (dimV Γ x))) (chi Γ x)))
                     (h x (+<-T (len Γ) x (len Γ) (+<-T (len Γ) (len Γ + x) (len Γ + len Γ) p))))
               (sym (gN-c2 Ts' Γ x)))

cylN-TsF : ∀ sd Γ → cylN sd Γ ≡ cylWith (TsF sd) Γ
cylN-TsF sd Γ =
  mk-ext (len Γ + (len Γ + len Γ))
    (gN-ext (nth (diskTys sd (dimCtx Γ))) (TsF sd) Γ
      (λ x p → nth-diskTys sd (dimCtx Γ) (dimV Γ x) (dimV-≤ Γ x p)))

-- D13, reduced to the disks: if the top generator of every D^j ⊗ D¹
-- (j ≤ k) is well typed, Γ ⊗ D¹ and D¹ ⊗ Γ are well formed for every
-- well-formed globular Γ of dimension ≤ k.
cylN-wf : ∀ sd k → (∀ j → T (j <ℕ suc k) → diskPre (TsF sd) j ⊢ty TsF sd j) →
          ∀ Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ suc k) → cylN sd Γ ⊢ctx
cylN-wf sd k H Γ w gl dk =
  subst _⊢ctx (sym (cylN-TsF sd Γ))
    (Main.cylWith-wf (TsF sd) k H Γ w gl (len Γ) (n<sn (len Γ))
       (λ x p → ≤-<-trans (dimV Γ x) (dimCtx Γ) (suc k) (dimV-≤ Γ x p) dk) refl)

-- The same, with no bound on the dimension, from all the disks.
cylN-wf-all : ∀ sd → (∀ j → diskPre (TsF sd) j ⊢ty TsF sd j) →
              ∀ Γ → Γ ⊢ctx → T (globular Γ) → cylN sd Γ ⊢ctx
cylN-wf-all sd H Γ w gl = cylN-wf sd (dimCtx Γ) (λ j _ → H j) Γ w gl (n<sn (dimCtx Γ))

------------------------------------------------------------------------
-- Discharging the disk hypothesis from a computed list of disk types.

dimV-D : ∀ m d → T (d <ℕ suc (dbl m)) → dimV (Disk m) d ≡ half d
dimV-D m d p = trans (cong dim (tyAt-mk (suc (dbl m)) aD d p)) (dim-aL (half d))

half-≤ : ∀ d m → T (d <ℕ suc (dbl m)) → T (half d <ℕ suc m)
half-≤ zero          m       _ = tt
half-≤ (suc zero)    m       _ = tt
half-≤ (suc (suc d)) (suc m) p = half-≤ d m p

-- If Ts agrees with TsF below suc k, its disk prefixes agree with TsF's.
diskPre-TsF : ∀ sd Ts k → (∀ j → T (j <ℕ suc k) → Ts j ≡ TsF sd j) →
              ∀ j → T (j <ℕ suc k) → diskPre Ts j ≡ diskPre (TsF sd) j
diskPre-TsF sd Ts k e j pj =
  mk-ext (M + (M + dbl j))
    (λ i p → gN-ext Ts (TsF sd) (Disk j)
               (λ x px → e (dimV (Disk j) x)
                  (subst (λ h → T (h <ℕ suc k)) (sym (dimV-D j x (subst (λ L → T (x <ℕ L)) (len-D j) px)))
                     (≤-<-trans (half x) j (suc k) (half-≤ x j (subst (λ L → T (x <ℕ L)) (len-D j) px)) pj)))
               i (lj i p))
  where
  M = suc (dbl j)
  lj : ∀ i → T (i <ℕ M + (M + dbl j)) → T (i <ℕ len (Disk j) + (len (Disk j) + len (Disk j)))
  lj i p = subst (λ L → T (i <ℕ L + (L + L))) (sym (len-D j)) (
    <-trans i (M + (M + dbl j)) (M + (M + M)) p (T-+< M (M + dbl j) (M + M) (T-+< M (dbl j) M (n<sn (dbl j)))))
