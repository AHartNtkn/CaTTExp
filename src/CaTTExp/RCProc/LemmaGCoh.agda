------------------------------------------------------------------------
-- Lemma G step (3): over the column context colCtx m n, the column
-- coherence H_{m′,n′}[ς] and κ̃ ∗₁ H_{m,n} ∗₁ κ̃ are parallel and full,
-- so one coherence connects them in each direction (ledger S20 (i), 3d).
--
-- This file: fullness of ς (`ς-full`, every variable of colCtx m n
-- occurs in ς); the edges of column substitutions (`appCh-edges`,
-- `ch-edges`) and of lifted chains (`pathCh-liftChF`); and the
-- comparison itself (`module Cmp`): over Δ = colCtx m n, with ι the
-- identity,
--
--   X = H_{m′,n′}[ς] : c⁻′[ς] ⇒ c⁺′[ς]
--   Y = κ̃⁻ ∗₁ H_{m,n}[ι] ∗₁ κ̃⁺ : c⁻′[ς] ⇒ c⁺′[ς]
--
-- (κ̃∓ the chain fillers between c∓′[ς] and c∓[ι], whose paths agree,
-- `path⁻`, `path⁺`), both full in Δ (`fullX`, `fullY`), so
-- Q⇒ θ = coh Δ (X ⇒ Y) θ and Q⇐ θ = coh Δ (Y ⇒ X) θ are typed for every
-- θ : Γ → Δ (`Q⇒-wf`, `Q⇐-wf`).
------------------------------------------------------------------------
module CaTTExp.RCProc.LemmaGCoh where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal using (path; pathCh; ∣_∣; zero<; lookupₛ-there₂)
open import CaTTExp.GraphFillerTotal.Chains
  using (chainC; vtx; _≤_; _<_; z≤n; +-zero; s≤s; ≤-refl; ≤-case; _⊎_; inj₁; inj₂;
         _∈_; ∈-here; ∈-there; ∈-++l; ∈-++r; ∈-++; ∈-single)
open import CaTTExp.RCProc.Column using (C₀; colCtx; chainFrom)
open import CaTTExp.RCProc.LiftF using (liftChF; liftF-lk; InSegF; liftChF-fs; module Typed)
open import CaTTExp.RCProc.ColSub using (vfF; efF; appCh; colSub; module ColCtx)
open import CaTTExp.RCProc.LemmaGSub using (ςL; ς)
open import CaTTExp.RCProc.Edges using (bd; edgesAt; edgesAt-keep; lt-bd; ++-[])
open import CaTTExp.RCProc.LiftF using (liftF)
open import CaTTExp.Derived using (lk-ext; lk-top)
open import CaTTExp.GraphFillerTotal using (∣++∣; sub-len)

------------------------------------------------------------------------
-- Every level of chainFrom Γ x n is in Γ or on the new chain.

private
  shift : ∀ vf ef n i →
          InSegF (λ j → vf (suc j)) (λ j → ef (suc j)) 0 n i → InSegF vf ef 0 (suc n) i
  shift vf ef n i (inj₁ (j , _ , jle , e)) = inj₁ (suc j , z≤n , s≤s jle , e)
  shift vf ef n i (inj₂ (j , _ , jlt , e)) = inj₂ (suc j , z≤n , s≤s jlt , e)

cover-from : ∀ Γ x n i → i < len (chainFrom Γ x n) →
             i < len Γ ⊎ InSegF (vfF (len Γ) x) (efF (len Γ) x) 0 n i
cover-from Γ x zero    i h = inj₁ h
cover-from Γ x (suc n) i h with cover-from (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n i h
... | inj₂ s = inj₂ (shift (vfF (len Γ) x) (efF (len Γ) x) n i s)
... | inj₁ (s≤s p) with ≤-case p
...   | inj₂ refl = inj₂ (inj₂ (0 , z≤n , s≤s z≤n , refl))
...   | inj₁ (s≤s q) with ≤-case q
...     | inj₂ refl = inj₂ (inj₁ (1 , z≤n , s≤s z≤n , refl))
...     | inj₁ r    = inj₁ r

prefix-cover : ∀ m i → i < len (C₀ m) → InSegF (vfF 1 0) (efF 1 0) 0 m i
prefix-cover m i h with cover-from (ε ▸ ⋆) 0 m i h
... | inj₁ (s≤s z≤n) = inj₁ (0 , z≤n , z≤n , refl)
... | inj₂ s         = s

------------------------------------------------------------------------
-- Free variables of appCh σ τ.

appCh-fvl : ∀ σ τ {i} → i ∈ fvSub σ → i ∈ fvSub (appCh σ τ)
appCh-fvl σ ⟨⟩            h = h
appCh-fvl σ (⟨⟩ ,ₛ _)     h = h
appCh-fvl σ (τ ,ₛ a ,ₛ b) h = ∈-++l (fvSub (appCh σ τ) ++ fvTm a) (fvTm b) (∈-++l (fvSub (appCh σ τ)) (fvTm a) (appCh-fvl σ τ h))

appCh-fvr : ∀ σ k τ {Γ y i} → Γ ⊢sub τ ∶ chainC k → lookupₛ τ 0 ≡ var y →
            i ∈ fvSub τ → i ∈ fvSub (appCh σ τ) ⊎ i ≡ y
appCh-fvr σ zero (⟨⟩ ,ₛ x₀) _ refl h = inj₂ (∈-single h)
appCh-fvr σ zero (_ ,ₛ _ ,ₛ _) (,-wf () _) _ _
appCh-fvr σ (suc k) (τ ,ₛ a ,ₛ b) (,-wf (,-wf sτ _) _) e h with ∈-++ (fvSub τ ++ fvTm a) (fvTm b) h
... | inj₂ q = inj₁ (∈-++r (fvSub (appCh σ τ) ++ fvTm a) (fvTm b) q)
... | inj₁ q with ∈-++ (fvSub τ) (fvTm a) q
...   | inj₂ r = inj₁ (∈-++l (fvSub (appCh σ τ) ++ fvTm a) (fvTm b) (∈-++r (fvSub (appCh σ τ)) (fvTm a) r))
...   | inj₁ r with appCh-fvr σ k τ sτ (trans (sym (lookupₛ-there₂ τ a b 0 (zero< sτ))) e) r
...     | inj₁ u = inj₁ (∈-++l (fvSub (appCh σ τ) ++ fvTm a) (fvTm b) (∈-++l (fvSub (appCh σ τ)) (fvTm a) u))
...     | inj₂ u = inj₂ u

------------------------------------------------------------------------
-- ς uses every variable of colCtx m n.

module _ {Γ m′ n′ τ′ τs} (sτ′ : Γ ⊢sub τ′ ∶ chainC m′) (sτs : Γ ⊢sub τs ∶ chainC n′) where
  private
    m = ∣ pathCh τ′ ∣
    n = ∣ pathCh τs ∣
    open ColCtx m n using (L; Ra; suf)
    P  = liftChF (vfF 1 0) (efF 1 0) τ′ 0
    Ts = liftChF (vfF (len Ra) L) (efF (len Ra) L) τs 0
    Bk = P ,ₛ var L ,ₛ var (suc L) ,ₛ var (suc (suc L)) ,ₛ var (suc (suc (suc L)))

    inBk : ∀ {i} → i ∈ fvSub Bk → i ∈ fvSub (ς τ′ τs)
    inBk = appCh-fvl Bk Ts

    -- The four 2-disc variables.
    F₀ F₁ F₂ F₃ : List Nat
    F₀ = fvSub P
    F₁ = F₀ ++ (L ∷ [])
    F₂ = F₁ ++ (suc L ∷ [])
    F₃ = F₂ ++ (suc (suc L) ∷ [])
    l₁ l₂ l₃ : List Nat
    l₁ = suc L ∷ []
    l₂ = suc (suc L) ∷ []
    l₃ = suc (suc (suc L)) ∷ []

    up₁ : ∀ {i} → i ∈ F₁ → i ∈ fvSub Bk
    up₁ h = ∈-++l F₃ l₃ (∈-++l F₂ l₂ (∈-++l F₁ l₁ h))

    v₀ : L ∈ fvSub Bk
    v₀ = up₁ (∈-++r F₀ (L ∷ []) (∈-here L []))
    v₁ : suc L ∈ fvSub Bk
    v₁ = ∈-++l F₃ l₃ (∈-++l F₂ l₂ (∈-++r F₁ l₁ (∈-here (suc L) [])))
    v₂ : suc (suc L) ∈ fvSub Bk
    v₂ = ∈-++l F₃ l₃ (∈-++r F₂ l₂ (∈-here (suc (suc L)) []))
    v₃ : suc (suc (suc L)) ∈ fvSub Bk
    v₃ = ∈-++r F₃ l₃ (∈-here (suc (suc (suc L))) [])

    inP : ∀ i → i < L → i ∈ fvSub Bk
    inP i h = up₁ (∈-++l F₀ (L ∷ []) (liftChF-fs (vfF 1 0) (efF 1 0) m′ τ′ 0 sτ′ i (prefix-cover m i h)))

  ς-full : ∀ i → i < len (colCtx m n) → i ∈ fvSub (ς τ′ τs)
  ς-full i h with cover-from Ra L n i h
  ... | inj₂ s with appCh-fvr Bk n′ Ts (Typed.liftChF-ty (vfF (len Ra) L) (efF (len Ra) L) suf n′ τs 0 sτs (subst (_≤ n) (sym (+-zero n)) ≤-refl)) (fst (snd (liftF-lk (vfF (len Ra) L) (efF (len Ra) L) n′ τs 0 sτs)))
                    (liftChF-fs (vfF (len Ra) L) (efF (len Ra) L) n′ τs 0 sτs i s)
  ...   | inj₁ u    = u
  ...   | inj₂ refl = inBk v₀
  ς-full i h | inj₁ (s≤s p) with ≤-case p
  ... | inj₂ refl = inBk v₃
  ... | inj₁ (s≤s p₁) with ≤-case p₁
  ...   | inj₂ refl = inBk v₂
  ...   | inj₁ (s≤s p₂) with ≤-case p₂
  ...     | inj₂ refl = inBk v₁
  ...     | inj₁ (s≤s p₃) with ≤-case p₃
  ...       | inj₂ refl = inBk v₀
  ...       | inj₁ q    = inBk (inP i q)

------------------------------------------------------------------------
-- Edge lists.

private
  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc′ zero    (suc n) _ = tt
  <-suc′ (suc i) (suc n) p = <-suc′ i n p

  ++-assoc : ∀ (as bs cs : List Nat) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
  ++-assoc []       bs cs = refl
  ++-assoc (a ∷ as) bs cs = cong (a ∷_) (++-assoc as bs cs)

  lk-at : ∀ σ a n → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a) n ≡ a
  lk-at σ a .(lenₛ σ) refl = lk-top σ a

-- The edges of an identity-like substitution from L on.
E : Nat → Nat → List Nat
E L zero    = []
E L (suc k) = suc L ∷ E (suc (suc L)) k

-- The edge levels ef (o+1), …, ef (o+k).
efs : (Nat → Nat) → Nat → Nat → List Nat
efs ef o zero    = []
efs ef o (suc k) = ef (suc o) ∷ efs ef (suc o) k

efs-++ : ∀ ef o a b → efs ef o (a + b) ≡ efs ef o a ++ efs ef (a + o) b
efs-++ ef o zero    b = refl
efs-++ ef o (suc a) b =
  cong (ef (suc o) ∷_) (trans (efs-++ ef (suc o) a b) (cong (λ k → efs ef (suc o) a ++ efs ef k b) (+-suc a o)))
  where open import CaTTExp.GraphFillerTotal.Chains using (+-suc)

efs-shift : ∀ ef o k → efs ef (suc o) k ≡ efs (λ j → ef (suc j)) o k
efs-shift ef o zero    = refl
efs-shift ef o (suc k) = cong (ef (suc (suc o)) ∷_) (efs-shift ef (suc o) k)

efsF-E : ∀ L x k → efs (efF L x) 0 k ≡ E L k
efsF-E L x zero    = refl
efsF-E L x (suc k) = cong (suc L ∷_) (trans (efs-shift (efF L x) 0 k) (efsF-E (suc (suc L)) L k))

module _ (vf ef : Nat → Nat) where
  mutual
    path-liftF : ∀ u o → path (liftF vf ef u o) ≡ efs ef o ∣ path u ∣
    path-liftF (var _)     o = refl
    path-liftF (coh _ _ τ) o = pathCh-liftChF τ o
    path-liftF (cst ())    o

    pathCh-liftChF : ∀ τ o → pathCh (liftChF vf ef τ o) ≡ efs ef o ∣ pathCh τ ∣
    pathCh-liftChF ⟨⟩            o = refl
    pathCh-liftChF (⟨⟩ ,ₛ _)     o = refl
    pathCh-liftChF (τ ,ₛ _ ,ₛ e) o =
      trans (cong₂ _++_ (pathCh-liftChF τ o) (path-liftF e (∣ pathCh τ ∣ + o)))
            (trans (sym (efs-++ ef o ∣ pathCh τ ∣ ∣ path e ∣))
                   (cong (efs ef o) (sym (∣++∣ (pathCh τ) (path e)))))

------------------------------------------------------------------------
-- edgesAt.

edgesAt-id : ∀ σ L k → (∀ i → T (i <ℕ bd L k) → lookupₛ σ i ≡ var i) → edgesAt σ L k ≡ E L k
edgesAt-id σ L zero    h = refl
edgesAt-id σ L (suc k) h =
  cong₂ _++_ (cong path (h (suc L) (lt-bd (suc L) (suc (suc L)) k (self (suc L)))))
             (edgesAt-id σ (suc (suc L)) k h)

edgesAt-snoc : ∀ σ L k → edgesAt σ L (suc k) ≡ edgesAt σ L k ++ path (lookupₛ σ (suc (bd L k)))
edgesAt-snoc σ L zero    = ++-[] _
edgesAt-snoc σ L (suc k) =
  trans (cong (path (lookupₛ σ (suc L)) ++_) (edgesAt-snoc σ (suc (suc L)) k))
        (sym (++-assoc (path (lookupₛ σ (suc L))) (edgesAt σ (suc (suc L)) k) _))

bd-suc : ∀ L k → suc (suc (bd L k)) ≡ bd (suc (suc L)) k
bd-suc L zero    = refl
bd-suc L (suc k) = bd-suc (suc (suc L)) k

module _ {Γ} (σ : Sub) where
  appCh-len : ∀ k τ → Γ ⊢sub τ ∶ chainC k → lenₛ (appCh σ τ) ≡ bd (lenₛ σ) k
  appCh-len zero (⟨⟩ ,ₛ _) _ = refl
  appCh-len zero (_ ,ₛ _ ,ₛ _) (,-wf () _)
  appCh-len (suc k) (τ ,ₛ a ,ₛ b) (,-wf (,-wf sτ _) _) =
    trans (cong (λ n → suc (suc n)) (appCh-len k τ sτ)) (bd-suc (lenₛ σ) k)

  appCh-keep : ∀ k τ → Γ ⊢sub τ ∶ chainC k → ∀ i → T (i <ℕ lenₛ σ) → lookupₛ (appCh σ τ) i ≡ lookupₛ σ i
  appCh-keep zero (⟨⟩ ,ₛ _) _ i p = refl
  appCh-keep zero (_ ,ₛ _ ,ₛ _) (,-wf () _) _ _
  appCh-keep (suc k) (τ ,ₛ a ,ₛ b) (,-wf (,-wf sτ _) _) i p =
    trans (lk-ext (appCh σ τ ,ₛ a) b i (<-suc′ i _ q))
          (trans (lk-ext (appCh σ τ) a i q) (appCh-keep k τ sτ i p))
    where
    q : T (i <ℕ lenₛ (appCh σ τ))
    q = subst (λ n → T (i <ℕ n)) (sym (appCh-len k τ sτ)) (lt-bd i (lenₛ σ) k p)

  appCh-edges : ∀ k τ → Γ ⊢sub τ ∶ chainC k → edgesAt (appCh σ τ) (lenₛ σ) k ≡ pathCh τ
  appCh-edges zero (⟨⟩ ,ₛ _) _ = refl
  appCh-edges zero (_ ,ₛ _ ,ₛ _) (,-wf () _)
  appCh-edges (suc k) (τ ,ₛ a ,ₛ b) (,-wf (,-wf sτ _) _) =
    trans (edgesAt-snoc X (lenₛ σ) k)
          (cong₂ _++_ (trans (edgesAt-keep (appCh σ τ) X (lenₛ σ) k keep) (appCh-edges k τ sτ))
                      (cong path (lk-at (appCh σ τ ,ₛ a) b _ (cong suc (appCh-len k τ sτ)))))
    where
    X = appCh σ τ ,ₛ a ,ₛ b
    keep : ∀ i → T (i <ℕ bd (lenₛ σ) k) → lookupₛ X i ≡ lookupₛ (appCh σ τ) i
    keep i p = trans (lk-ext (appCh σ τ ,ₛ a) b i (<-suc′ i _ q)) (lk-ext (appCh σ τ) a i q)
      where
      q : T (i <ℕ lenₛ (appCh σ τ))
      q = subst (λ n → T (i <ℕ n)) (sym (appCh-len k τ sτ)) p

appCh-self : ∀ {Γ} k τ → Γ ⊢sub τ ∶ chainC k → appCh (⟨⟩ ,ₛ lookupₛ τ 0) τ ≡ τ
appCh-self zero (⟨⟩ ,ₛ _) _ = refl
appCh-self zero (_ ,ₛ _ ,ₛ _) (,-wf () _)
appCh-self (suc k) (τ ,ₛ a ,ₛ b) (,-wf (,-wf sτ _) _) =
  cong (λ X → X ,ₛ a ,ₛ b)
       (trans (cong (λ t → appCh (⟨⟩ ,ₛ t) τ) (lookupₛ-there₂ τ a b 0 (zero< sτ))) (appCh-self k τ sτ))

ch-edges : ∀ {Γ} k τ → Γ ⊢sub τ ∶ chainC k → edgesAt τ 1 k ≡ pathCh τ
ch-edges k τ sτ =
  trans (cong (λ X → edgesAt X 1 k) (sym (appCh-self k τ sτ))) (appCh-edges (⟨⟩ ,ₛ lookupₛ τ 0) k τ sτ)

------------------------------------------------------------------------
-- The comparison coherence over colCtx m n.

open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (idS; id-wf; lookup-renS; lenₛ-renS; tm-ty; sphSub)
open import CaTTExp.PsRaiseCongr using (c⁻; c⁺; A^)
open import CaTTExp.RCProc.Column using (flagAt; leaves; colEnd)
open import CaTTExp.RCProc.EgPath using (path-c⁻; path-c⁺)
open import CaTTExp.RCProc.Eg using (vcomp)
open import CaTTExp.RCProc.Glue using (transA)
open import CaTTExp.GraphFillerTotal using (fill₁; total; lookup-fv; sc-fv; downFrom-mem)
open import CaTTExp.GraphFillerTotal.Chains using (dbl; +-suc; <→T; ∨-inl; all-intro; elem-downFrom)
open import CaTTExp.RCProc.LemmaGSub using (ς-wf; ς-end)
open import CaTTExp.RCProc.ColSub using (end-lt)
import CaTTExp.RCProc.Whisker as W

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  zT : ∀ n → 0 < n → T (0 <ℕ n)
  zT (suc n) _ = tt

  l2 : ∀ N → T (N <ℕ suc (suc N))
  l2 N = <-suc′ N (suc N) (self N)
  l3 : ∀ N → T (N <ℕ suc (suc (suc N)))
  l3 N = <-suc′ N (suc (suc N)) (l2 N)

  up4 : ∀ i N → T (i <ℕ N) → T (i <ℕ suc (suc (suc (suc N))))
  up4 i N p = <-suc′ i _ (<-suc′ i _ (<-suc′ i _ (<-suc′ i _ p)))

  bd-dbl : ∀ L k → bd L k ≡ dbl k + L
  bd-dbl L zero    = refl
  bd-dbl L (suc k) = trans (bd-dbl (suc (suc L)) k)
                           (trans (+-suc (dbl k) (suc L)) (cong suc (+-suc (dbl k) L)))

  vtx-bd : ∀ k → vtx (suc k) ≡ bd 1 k
  vtx-bd k = sym (trans (bd-dbl 1 k) (trans (+-suc (dbl k) 0) (cong suc (+-zero (dbl k)))))

  len-chainFrom : ∀ Γ x n → len (chainFrom Γ x n) ≡ bd (len Γ) n
  len-chainFrom Γ x zero    = refl
  len-chainFrom Γ x (suc n) = len-chainFrom (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n

  sc-fvTy : ∀ n A {i} → S.ScTy n A → i ∈ fvTy A → i < n
  sc-fvTy n ⋆ _ ()
  sc-fvTy n (arr A t u) (a , p , q) mem with ∈-++ (fvTy A) (fvTm t ++ fvTm u) mem
  ... | inj₁ r = sc-fvTy n A a r
  ... | inj₂ r with ∈-++ (fvTm t) (fvTm u) r
  ...   | inj₁ r′ = sc-fv n t p r′
  ...   | inj₂ r′ = sc-fv n u q r′

-- A typed term whose free variables (with its type's) cover the context is full.
full-intro : ∀ {Δ t A} → Δ ⊢tm t ∶ A → (∀ i → i < len Δ → i ∈ fvTmTy t A) →
             T (≈? (fvTmTy t A) (varsCtx Δ))
full-intro {Δ} {t} {A} d cov =
  ∧-intro (all-intro (λ x → elem x ys) xs (λ i mem → elem-downFrom (bound i mem)))
          (all-intro (λ x → elem x xs) ys (λ i mem → cov i (downFrom-mem (len Δ) mem)))
  where
  xs = fvTmTy t A
  ys = downFrom (len Δ)
  bound : ∀ i → i ∈ xs → i < len Δ
  bound i mem with ∈-++ (fvTm t) (fvTy A) mem
  ... | inj₁ q = sc-fv (len Δ) t (S.tm-sc closed d) q
  ... | inj₂ q = sc-fvTy (len Δ) A (S.tm-ty-sc closed d) q

module Cmp {Γ m′ n′ τ′ τs} (sτ′ : Γ ⊢sub τ′ ∶ chainC m′) (sτs : Γ ⊢sub τs ∶ chainC n′) where
  m n : Nat
  m = ∣ pathCh τ′ ∣
  n = ∣ pathCh τs ∣

  open ColCtx m n using (L; Ra; col-ps; col-wf; pre; suf)

  Δ : Ctx
  Δ = colCtx m n

  ι σς : Sub
  ι  = idS (len Δ)
  σς = ς τ′ τs

  A_Δ : Ty
  A_Δ = arr ⋆ (var 0) (var (colEnd m n))

  c⁻′ c⁺′ c⁻₀ c⁺₀ : Tm
  c⁻′ = c⁻ (flagAt m′) (node []) (leaves (m′ + n′)) ⋆ (var 0) (var (vtx (suc (m′ + n′)))) [ σς ]tm
  c⁺′ = c⁺ (flagAt m′) (node []) (leaves (m′ + n′)) ⋆ (var 0) (var (vtx (suc (m′ + n′)))) [ σς ]tm
  c⁻₀ = c⁻ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n)))) [ ι ]tm
  c⁺₀ = c⁺ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n)))) [ ι ]tm

  X H₀ κ̃⁻ κ̃⁺ Y : Tm
  X   = W.Col.H m′ n′ σς
  H₀  = W.Col.H m n ι
  κ̃⁻  = fill₁ Δ c⁻′ c⁻₀ A_Δ
  κ̃⁺  = fill₁ Δ c⁺₀ c⁺′ A_Δ
  Y   = vcomp A_Δ c⁻′ c⁻₀ c⁺′ κ̃⁻ (vcomp A_Δ c⁻₀ c⁺₀ c⁺′ H₀ κ̃⁺)

  Bnd : Ty
  Bnd = arr A_Δ c⁻′ c⁺′

  Q⇒ Q⇐ : Sub → Tm
  Q⇒ θ = coh Δ (arr Bnd X Y) θ
  Q⇐ θ = coh Δ (arr Bnd Y X) θ

  private
    P  = liftChF (vfF 1 0) (efF 1 0) τ′ 0
    Ts = liftChF (vfF (len Ra) L) (efF (len Ra) L) τs 0
    B₁ = P ,ₛ var L
    B₂ = B₁ ,ₛ var (suc L)
    B₃ = B₂ ,ₛ var (suc (suc L))
    Bk = B₃ ,ₛ var (suc (suc (suc L)))

    le : ∀ k → k + 0 ≤ k
    le k = subst (_≤ k) (sym (+-zero k)) ≤-refl

    sP : Δ ⊢sub P ∶ chainC m′
    sP = Typed.liftChF-ty (vfF 1 0) (efF 1 0) pre m′ τ′ 0 sτ′ (le m)
    sTs : Δ ⊢sub Ts ∶ chainC n′
    sTs = Typed.liftChF-ty (vfF (len Ra) L) (efF (len Ra) L) suf n′ τs 0 sτs (le n)

    lP₀ : lenₛ P ≡ lenₛ τ′
    lP₀ = fst (liftF-lk (vfF 1 0) (efF 1 0) m′ τ′ 0 sτ′)
    lP : lenₛ P ≡ bd 1 m′
    lP = trans lP₀ (trans (sub-len sτ′) (vtx-bd m′))
    lC : L ≡ bd 1 m
    lC = len-chainFrom (ε ▸ ⋆) 0 m
    lΔ : len Δ ≡ bd (len Ra) n
    lΔ = len-chainFrom Ra L n

    -- ς below its 2-disc block.
    keepBk : ∀ i → T (i <ℕ lenₛ Bk) → lookupₛ σς i ≡ lookupₛ Bk i
    keepBk = appCh-keep Bk n′ Ts sTs
    lkBkP : ∀ i → T (i <ℕ lenₛ P) → lookupₛ Bk i ≡ lookupₛ P i
    lkBkP i p = trans (lk-ext B₃ _ i u₃) (trans (lk-ext B₂ _ i u₂) (trans (lk-ext B₁ _ i u₁) (lk-ext P _ i p)))
      where
      u₁ = <-suc′ i _ p
      u₂ = <-suc′ i _ u₁
      u₃ = <-suc′ i _ u₂
    ltBk : ∀ i → T (i <ℕ lenₛ P) → T (i <ℕ lenₛ Bk)
    ltBk i p = up4 i (lenₛ P) p

    ς0 : lookupₛ σς 0 ≡ var 0
    ς0 = trans (keepBk 0 (ltBk 0 z)) (trans (lkBkP 0 z) (fst (snd (liftF-lk (vfF 1 0) (efF 1 0) m′ τ′ 0 sτ′))))
      where z = zT (lenₛ P) (subst (0 <_) (sym lP₀) (zero< sτ′))

    A′eq : A^ (flagAt m′) (node []) (leaves (m′ + n′)) ⋆ (var 0) (var (vtx (suc (m′ + n′)))) [ σς ]ty ≡ A_Δ
    A′eq = trans (cong (_[ σς ]ty) (W.Col.A^-eq m′ n′)) (cong₂ (arr ⋆) ς0 (ς-end sτ′ sτs))

    -- ι.
    bound : ∀ i → T (i <ℕ suc (suc (suc (suc L)))) → T (i <ℕ len Δ)
    bound i p = subst (λ k → T (i <ℕ k)) (sym lΔ) (lt-bd i (len Ra) n p)
    lkι : ∀ i → T (i <ℕ len Δ) → lookupₛ ι i ≡ var i
    lkι i p = lookup-renS (len Δ) (λ j → j) i p

    A₀eq : A^ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n)))) [ ι ]ty ≡ A_Δ
    A₀eq = trans (cong (_[ ι ]ty) (W.Col.A^-eq m n))
                 (cong₂ (arr ⋆) (lkι 0 (bound 0 tt))
                                (lkι (colEnd m n) (end-lt Ra L n (<-suc′ L _ (l3 L)))))

  dX : Δ ⊢tm X ∶ Bnd
  dX = subst (λ Z → Δ ⊢tm X ∶ arr Z c⁻′ c⁺′) A′eq (W.Col.H-wf m′ n′ (ς-wf sτ′ sτs))

  dH₀ : Δ ⊢tm H₀ ∶ arr A_Δ c⁻₀ c⁺₀
  dH₀ = subst (λ Z → Δ ⊢tm H₀ ∶ arr Z c⁻₀ c⁺₀) A₀eq (W.Col.H-wf m n (id-wf col-wf))

  -- The boundary paths.
  Ef : Nat → Nat → List Nat
  Ef K j = E 1 m ++ ((j ∷ []) ++ E (suc (suc (suc (suc K)))) n)

  private
    pre-edges : edgesAt σς 1 m′ ≡ E 1 m
    pre-edges =
      trans (edgesAt-keep P σς 1 m′ h)
      (trans (ch-edges m′ P sP)
      (trans (pathCh-liftChF (vfF 1 0) (efF 1 0) τ′ 0) (efsF-E 1 0 m)))
      where
      h : ∀ i → T (i <ℕ bd 1 m′) → lookupₛ σς i ≡ lookupₛ P i
      h i p = trans (keepBk i (ltBk i q)) (lkBkP i q)
        where q = subst (λ k → T (i <ℕ k)) (sym lP) p

    suf-edges : edgesAt σς (suc (suc (suc (suc (bd 1 m′))))) n′ ≡ E (suc (suc (suc (suc L)))) n
    suf-edges =
      trans (cong (λ k → edgesAt σς (suc (suc (suc (suc k)))) n′) (sym lP))
      (trans (appCh-edges Bk n′ Ts sTs)
      (trans (pathCh-liftChF (vfF (len Ra) L) (efF (len Ra) L) τs 0) (efsF-E (len Ra) L n)))

    mid⁻ : lookupₛ σς (suc (bd 1 m′)) ≡ var (suc L)
    mid⁻ = subst (λ k → lookupₛ σς (suc k) ≡ var (suc L)) lP
             (trans (keepBk (suc (lenₛ P)) (l3 (lenₛ P)))
                    (trans (lk-ext B₃ _ (suc (lenₛ P)) (l2 (lenₛ P)))
                           (trans (lk-ext B₂ _ (suc (lenₛ P)) (self (lenₛ P))) (lk-top B₁ (var (suc L))))))

    mid⁺ : lookupₛ σς (suc (suc (bd 1 m′))) ≡ var (suc (suc L))
    mid⁺ = subst (λ k → lookupₛ σς (suc (suc k)) ≡ var (suc (suc L))) lP
             (trans (keepBk (suc (suc (lenₛ P))) (l2 (lenₛ P)))
                    (trans (lk-ext B₃ _ (suc (suc (lenₛ P))) (self (lenₛ P))) (lk-top B₂ (var (suc (suc L))))))

    ι-pre : edgesAt ι 1 m ≡ E 1 m
    ι-pre = edgesAt-id ι 1 m λ i p →
      lkι i (bound i (up4 i L (subst (λ k → T (i <ℕ k)) (sym lC) p)))

    ι-suf : edgesAt ι (suc (suc (suc (suc (bd 1 m))))) n ≡ E (suc (suc (suc (suc L)))) n
    ι-suf = trans (cong (λ k → edgesAt ι (suc (suc (suc (suc k)))) n) (sym lC))
                  (edgesAt-id ι (len Ra) n λ i p → lkι i (subst (λ k → T (i <ℕ k)) (sym lΔ) p))

    ι-mid⁻ : lookupₛ ι (suc (bd 1 m)) ≡ var (suc L)
    ι-mid⁻ = subst (λ k → lookupₛ ι (suc k) ≡ var (suc L)) lC (lkι (suc L) (bound (suc L) (l3 L)))

    ι-mid⁺ : lookupₛ ι (suc (suc (bd 1 m))) ≡ var (suc (suc L))
    ι-mid⁺ = subst (λ k → lookupₛ ι (suc (suc k)) ≡ var (suc (suc L))) lC (lkι (suc (suc L)) (bound (suc (suc L)) (l2 L)))

  path⁻ : path c⁻′ ≡ path c⁻₀
  path⁻ =
    trans (path-c⁻ m′ n′ ⋆ (var 0) (var (vtx (suc (m′ + n′)))) σς)
    (trans (cong₂ _++_ pre-edges (cong₂ _++_ (cong path mid⁻) suf-edges))
    (sym (trans (path-c⁻ m n ⋆ (var 0) (var (vtx (suc (m + n)))) ι)
                (cong₂ _++_ ι-pre (cong₂ _++_ (cong path ι-mid⁻) ι-suf)))))

  path⁺ : path c⁺₀ ≡ path c⁺′
  path⁺ =
    trans (trans (path-c⁺ m n ⋆ (var 0) (var (vtx (suc (m + n)))) ι)
                 (cong₂ _++_ ι-pre (cong₂ _++_ (cong path ι-mid⁺) ι-suf)))
    (sym (trans (path-c⁺ m′ n′ ⋆ (var 0) (var (vtx (suc (m′ + n′)))) σς)
                (cong₂ _++_ pre-edges (cong₂ _++_ (cong path mid⁺) suf-edges))))

  private
    sidesX : Σ (Δ ⊢tm c⁻′ ∶ A_Δ) λ _ → Δ ⊢tm c⁺′ ∶ A_Δ
    sidesX with tm-ty dX
    ... | arr-wf d⁻ d⁺ = d⁻ , d⁺

    sides₀ : Σ (Δ ⊢tm c⁻₀ ∶ A_Δ) λ _ → Δ ⊢tm c⁺₀ ∶ A_Δ
    sides₀ with tm-ty dH₀
    ... | arr-wf d⁻ d⁺ = d⁻ , d⁺

  dκ⁻ : Δ ⊢tm κ̃⁻ ∶ arr A_Δ c⁻′ c⁻₀
  dκ⁻ = total (fst sidesX) (fst sides₀) path⁻

  dκ⁺ : Δ ⊢tm κ̃⁺ ∶ arr A_Δ c⁺₀ c⁺′
  dκ⁺ = total (snd sides₀) (snd sidesX) path⁺

  dY : Δ ⊢tm Y ∶ Bnd
  dY = snd (transA (κ̃⁻ , dκ⁻) (transA (H₀ , dH₀) (κ̃⁺ , dκ⁺)))

  -- Fullness.
  fullX : T (≈? (fvTmTy X Bnd) (varsCtx Δ))
  fullX = full-intro dX λ i h → ∈-++l {i} (fvSub σς) (fvTy Bnd) (ς-full sτ′ sτs i h)

  fullY : T (≈? (fvTmTy Y Bnd) (varsCtx Δ))
  fullY = full-intro dY λ i h → ∈-++l {i} (fvTm Y) (fvTy Bnd) (inY i (inι i h))
    where
    inι : ∀ i → i < len Δ → i ∈ fvSub ι
    inι i h = lookup-fv ι i (subst (i <_) (sym (lenₛ-renS (len Δ) (λ j → j))) h) (lkι i (<→T h))
    C₁ = arr A_Δ c⁻′ c⁻₀
    C₂ = arr A_Δ c⁻₀ c⁺₀
    Y₂ = vcomp A_Δ c⁻₀ c⁺₀ c⁺′ H₀ κ̃⁺
    inY : ∀ i → i ∈ fvSub ι → i ∈ fvTm Y
    inY i q =
      ∈-++r {i} ((fvSub (sphSub C₁) ++ fvTm κ̃⁻) ++ fvTm c⁺′) (fvTm Y₂)
        (∈-++l {i} ((fvSub (sphSub C₂) ++ fvTm H₀) ++ fvTm c⁺′) (fvTm κ̃⁺)
          (∈-++l {i} (fvSub (sphSub C₂) ++ fvTm H₀) (fvTm c⁺′) (∈-++r {i} (fvSub (sphSub C₂)) (fvTm H₀) q)))

  Q⇒-wf : ∀ {Γ′ θ} → Γ′ ⊢sub θ ∶ Δ → Γ′ ⊢tm Q⇒ θ ∶ arr Bnd X Y [ θ ]ty
  Q⇒-wf sθ = coh-wf col-ps col-wf (arr-wf dX dY) (∨-inl (isOp Δ Bnd X Y) (∧-intro fullX fullY)) sθ

  Q⇐-wf : ∀ {Γ′ θ} → Γ′ ⊢sub θ ∶ Δ → Γ′ ⊢tm Q⇐ θ ∶ arr Bnd Y X [ θ ]ty
  Q⇐-wf sθ = coh-wf col-ps col-wf (arr-wf dY dX) (∨-inl (isOp Δ Bnd Y X) (∧-intro fullY fullX)) sθ
