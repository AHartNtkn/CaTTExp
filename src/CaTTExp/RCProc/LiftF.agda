------------------------------------------------------------------------
-- Lifting 1-cells into a chain embedded in any context (ledger S20 (i),
-- stage 3d, Lemma G step (1)).
--
-- GraphFillerTotal.lift re-reads a 1-cell u of Γ inside chainC K, its
-- path starting at the vertex x_o. Here the chain is any embedding
-- `ChainIn Δ vf ef K` of a K-step chain in a context Δ: vertex j is the
-- variable vf j, edge j + 1 (from vf j to vf (j + 1)) is ef (j + 1).
-- `liftF` is the lift along the embedding; it is typed in Δ
-- (`liftF-ty`), and substituting a σ that sends the chain along the
-- path of u back gives u (`liftF-sub`). GraphFillerTotal.lift is the
-- instance Δ = chainC K, vf = vtx, ef = edge.
------------------------------------------------------------------------
module CaTTExp.RCProc.LiftF where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.GraphFillerTotal
  using (path; pathCh; ∣_∣; ∣++∣; pathlen; coh-view; CohV; cohV; sub-len; lookupₛ-there₂;
         edge-ty; last-var; ⋆-var; tgtOf; endOf; walk; walkCh; walk-end; zero<; last-obj)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx; vtx-<; ≤-+l; lookupₛ-there; lookupₛ-here; _≤_; _<_; z≤n; s≤s; ≤-refl; ≤-step; ≤-trans; +-suc)

record ChainIn (Δ : Ctx) (vf ef : Nat → Nat) (K : Nat) : Set where
  field
    wΔ : Δ ⊢ctx
    lv : ∀ j → j ≤ K → lookup Δ (vf j) ≡ just ⋆
    le : ∀ j → j < K → lookup Δ (ef (suc j)) ≡ just (arr ⋆ (var (vf j)) (var (vf (suc j))))

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

module _ (vf ef : Nat → Nat) where
  mutual
    liftF : Tm → Nat → Tm
    liftF (var _)     o = var (ef (suc o))
    liftF (coh Θ A τ) o = coh Θ A (liftChF τ o)
    liftF (cst k)     o = cst k

    liftChF : Sub → Nat → Sub
    liftChF ⟨⟩            o = ⟨⟩
    liftChF (⟨⟩ ,ₛ _)     o = ⟨⟩ ,ₛ var (vf o)
    liftChF (τ ,ₛ _ ,ₛ e) o =
      liftChF τ o ,ₛ var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o))) ,ₛ liftF e (∣ pathCh τ ∣ + o)

  -- Lengths and end points.
  liftF-lk : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k →
             (lenₛ (liftChF τ o) ≡ lenₛ τ) × (lookupₛ (liftChF τ o) 0 ≡ var (vf o)) ×
             (lookupₛ (liftChF τ o) (vtx k) ≡ var (vf (∣ pathCh τ ∣ + o)))
  liftF-lk zero (⟨⟩ ,ₛ x) o _ = refl , refl , refl
  liftF-lk zero (_ ,ₛ _ ,ₛ _) o (,-wf () _)
  liftF-lk (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) _) =
    let (l , l0 , lk) = liftF-lk k τ o s
        lτ = liftChF τ o
        v  = var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
        ln = trans l (sub-len s) in
    cong (λ n → suc (suc n)) l ,
    trans (lookupₛ-there₂ lτ v (liftF e (∣ pathCh τ ∣ + o)) 0 (subst (0 <_) (sym ln) (s≤s z≤n))) l0 ,
    trans (lookupₛ-there (lτ ,ₛ v) _ (vtx (suc k)) (subst (vtx (suc k) <_) (cong suc (sym ln)) ≤-refl))
     (trans (lookupₛ-here lτ v (vtx (suc k)) (sym ln))
            (cong (λ n → var (vf n)) (pathlen τ e o)))

  -- Typing, in any context carrying the chain.
  module Typed {Δ K} (C : ChainIn Δ vf ef K) where
    open ChainIn C

    mutual
      liftF-ty : ∀ {Γ B a b} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → ∣ path u ∣ + o ≤ K →
                 Δ ⊢tm liftF u o ∶ arr ⋆ (var (vf o)) (var (vf (∣ path u ∣ + o)))
      liftF-ty (var e) o _ _ p = var-wf wΔ (le o p)
      liftF-ty (coh Θ A τ) o d eq p with coh-view d eq
      ... | cohV k pP w a ok s _ _ =
        let (_ , l0 , lk) = liftF-lk k τ o s in
        subst (Δ ⊢tm liftF (coh Θ A τ) o ∶_) (cong₂ (arr ⋆) l0 lk)
              (coh-wf pP w a ok (liftChF-ty k τ o s p))
      liftF-ty (cst k) _ (cst-wf {()} _ _) _ _

      liftChF-ty : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k → ∣ pathCh τ ∣ + o ≤ K →
                   Δ ⊢sub liftChF τ o ∶ chainC k
      liftChF-ty zero (⟨⟩ ,ₛ x) o _ p = ,-wf (⟨⟩-wf wΔ) (var-wf wΔ (lv o p))
      liftChF-ty zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _
      liftChF-ty (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) de) p =
        ,-wf (,-wf sτ (var-wf wΔ (lv (n₂ + o') le₂)))
             (subst (Δ ⊢tm liftF e o' ∶_)
                    (sym (trans (edge-ty sτ) (cong (λ t → arr ⋆ t (var (vf (n₂ + o')))) lk)))
                    (liftF-ty e o' de refl le₂))
        where
        n₁ = ∣ pathCh τ ∣
        n₂ = ∣ path e ∣
        o' = n₁ + o
        le₂ : n₂ + o' ≤ K
        le₂ = subst (_≤ K) (sym (pathlen τ e o)) p
        le₁ : o' ≤ K
        le₁ = ≤-trans (≤-+l n₂ o') le₂
        sτ = liftChF-ty k τ o s le₁
        lk = snd (snd (liftF-lk k τ o s))

  -- Substituting back along the path.
  SegF : Ctx → Sub → Nat → Nat → List Nat → Set
  SegF Γ σ o x []      = lookupₛ σ (vf o) ≡ var x
  SegF Γ σ o x (e ∷ p) = (lookupₛ σ (vf o) ≡ var x) × (lookupₛ σ (ef (suc o)) ≡ var e) ×
                         SegF Γ σ (suc o) (tgtOf Γ e) p

  segF-end : ∀ {Γ σ o x} p → SegF Γ σ o x p → lookupₛ σ (vf (∣ p ∣ + o)) ≡ var (endOf Γ x p)
  segF-end []      h = h
  segF-end {Γ} {σ} {o} (e ∷ p) (_ , _ , h) =
    subst (λ n → lookupₛ σ (vf n) ≡ var (endOf Γ (tgtOf Γ e) p)) (+-suc ∣ p ∣ o) (segF-end p h)

  segF-split : ∀ {Γ σ o x} p q → SegF Γ σ o x (p ++ q) →
               SegF Γ σ o x p × SegF Γ σ (∣ p ∣ + o) (endOf Γ x p) q
  segF-split []      []      h           = h , h
  segF-split []      (e ∷ q) h           = fst h , h
  segF-split {Γ} {σ} {o} (e ∷ p) q (h , he , r) =
    let (a , b) = segF-split p q r in
    (h , he , a) , subst (λ n → SegF Γ σ n (endOf Γ (tgtOf Γ e) p) q) (+-suc ∣ p ∣ o) b

  mutual
    liftF-sub : ∀ {Γ B x y σ} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ (var x) (var y) →
                SegF Γ σ o x (path u) → liftF u o [ σ ]tm ≡ u
    liftF-sub (var e) o _ _ (_ , he , _) = he
    liftF-sub (coh Θ A τ) o d eq sg with coh-view d eq
    ... | cohV k _ _ _ _ s ex _ = cong (coh Θ A) (liftChF-sub k τ o s ex sg)
    liftF-sub (cst k) _ (cst-wf {()} _ _) _ _

    liftChF-sub : ∀ {Γ x σ} k τ o → Γ ⊢sub τ ∶ chainC k → lookupₛ τ 0 ≡ var x →
                  SegF Γ σ o x (pathCh τ) → liftChF τ o ∘ σ ≡ τ
    liftChF-sub zero (⟨⟩ ,ₛ x₀) o _ ex sg = cong (⟨⟩ ,ₛ_) (trans sg (sym ex))
    liftChF-sub zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _ _
    liftChF-sub {Γ} {x} {σ} (suc k) (τ ,ₛ x' ,ₛ e) o (,-wf (,-wf s dx) de) ex sg
      with last-var s | ⋆-var dx refl
    ... | w , lw | z , refl =
      cong₃ (λ a b c → a ,ₛ b ,ₛ c) (liftChF-sub k τ o s ex' sg₁) obj (liftF-sub e o' de eqe sg₂)
      where
      o' = ∣ pathCh τ ∣ + o
      ex' : lookupₛ τ 0 ≡ var x
      ex' = trans (sym (lookupₛ-there₂ τ (var z) e 0 (zero< s))) ex
      wk : endOf Γ x (pathCh τ) ≡ w
      wk = walk-end (walkCh k τ s ex' lw)
      eqe : arr ⋆ (var (vtx k)) (var (vtx (suc k))) [ τ ,ₛ var z ]ty ≡ arr ⋆ (var w) (var z)
      eqe = trans (edge-ty s) (cong (λ t → arr ⋆ t (var z)) lw)
      halves = segF-split (pathCh τ) (path e) sg
      sg₁ = fst halves
      sg₂ : SegF Γ σ o' w (path e)
      sg₂ = subst (λ t → SegF Γ σ o' t (path e)) wk (snd halves)
      obj : lookupₛ σ (vf (∣ path e ∣ + o')) ≡ var z
      obj = trans (segF-end (path e) sg₂) (cong var (walk-end (walk e de eqe)))

------------------------------------------------------------------------
-- Fullness: the lift of u uses every level of its segment (except
-- possibly its two end vertices, when u is a variable).

open import CaTTExp.GraphFillerTotal.Chains using (_⊎_; inj₁; inj₂; _∈_; ∈-here; ∈-++l; ∈-++r; ≤-suc-case; ≤-case; ≤-total; ≤-pred; +-assoc; +-comm)
open import CaTTExp.GraphFillerTotal using (lookup-fv)

private
  swap : ∀ a b c → b + (a + c) ≡ (a + b) + c
  swap a b c = trans (sym (+-assoc b a c)) (cong (_+ c) (+-comm b a))

  antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
  antisym z≤n     z≤n     = refl
  antisym (s≤s a) (s≤s b) = cong suc (antisym a b)

  ¬suc≤ : ∀ {n} → suc n ≤ n → ⊥
  ¬suc≤ (s≤s p) = ¬suc≤ p

module _ (vf ef : Nat → Nat) where
  -- The levels of the segment of length n starting at vertex o.
  InSegF : Nat → Nat → Nat → Set
  InSegF o n m =
    (Σ Nat λ j → (o ≤ j) × (j ≤ n + o) × (m ≡ vf j)) ⊎
    (Σ Nat λ j → (o ≤ j) × (j < n + o) × (m ≡ ef (suc j)))

  insegF-split : ∀ n₁ n₂ o m → InSegF o (n₁ + n₂) m → InSegF o n₁ m ⊎ InSegF (n₁ + o) n₂ m
  insegF-split n₁ n₂ o m (inj₁ (j , oj , jle , e)) with ≤-total j (n₁ + o)
  ... | inj₁ q = inj₁ (inj₁ (j , oj , q , e))
  ... | inj₂ q = inj₂ (inj₁ (j , ≤-trans (≤-step ≤-refl) q ,
                             subst (j ≤_) (sym (swap n₁ n₂ o)) jle , e))
  insegF-split n₁ n₂ o m (inj₂ (j , oj , jlt , e)) with ≤-total (suc j) (n₁ + o)
  ... | inj₁ q = inj₁ (inj₂ (j , oj , q , e))
  ... | inj₂ q = inj₂ (inj₂ (j , ≤-pred q , subst (suc j ≤_) (sym (swap n₁ n₂ o)) jlt , e))

  mutual
    liftF-fs : ∀ {Γ B a b} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → ∀ m → InSegF o ∣ path u ∣ m →
               (m ∈ fvTm (liftF vf ef u o)) ⊎ (m ≡ vf o ⊎ m ≡ vf (∣ path u ∣ + o))
    liftF-fs (var e) o _ _ m (inj₁ (j , oj , jle , refl)) with ≤-suc-case jle
    ... | inj₁ q    = inj₂ (inj₁ (cong vf (antisym q oj)))
    ... | inj₂ refl = inj₂ (inj₂ refl)
    liftF-fs (var e) o _ _ m (inj₂ (j , oj , s≤s jlt , refl)) with antisym jlt oj
    ... | refl = inj₁ (∈-here (ef (suc j)) [])
    liftF-fs (coh Θ A τ) o d eq m h with coh-view d eq
    ... | cohV k _ _ _ _ s _ _ = inj₁ (liftChF-fs k τ o s m h)
    liftF-fs (cst k) _ (cst-wf {()} _ _) _ _ _

    liftChF-fs : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k → ∀ m → InSegF o ∣ pathCh τ ∣ m →
                 m ∈ fvSub (liftChF vf ef τ o)
    liftChF-fs zero (⟨⟩ ,ₛ x) o _ m (inj₁ (j , oj , jle , refl)) with antisym oj jle
    ... | refl = ∈-here (vf j) []
    liftChF-fs zero (⟨⟩ ,ₛ x) o _ m (inj₂ (j , oj , jlt , _)) = ⊥-elim (¬suc≤ (≤-trans jlt oj))
    liftChF-fs zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _ _
    liftChF-fs (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) de) m h
      with insegF-split ∣ pathCh τ ∣ ∣ path e ∣ o m
             (subst (λ n → InSegF o n m) (∣++∣ (pathCh τ) (path e)) h)
    ... | inj₁ h₁ = ∈-++l (fvSub lτ ++ fvTm v) (fvTm le′)
                      (∈-++l (fvSub lτ) (fvTm v) (liftChF-fs k τ o s m h₁))
      where
      lτ  = liftChF vf ef τ o
      v   = var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
      le′ = liftF vf ef e (∣ pathCh τ ∣ + o)
    ... | inj₂ h₂ with liftF-fs e (∣ pathCh τ ∣ + o) de refl m h₂
    ...   | inj₁ q = ∈-++r (fvSub lτ ++ fvTm v) (fvTm le′) q
      where
      lτ  = liftChF vf ef τ o
      v   = var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
      le′ = liftF vf ef e (∣ pathCh τ ∣ + o)
    ...   | inj₂ (inj₁ refl) =
      ∈-++l (fvSub lτ ++ fvTm v) (fvTm le′) (∈-++l (fvSub lτ) (fvTm v)
        (lookup-fv lτ (vtx k)
           (subst (vtx k <_) (sym (trans (fst (liftF-lk vf ef k τ o s)) (sub-len s))) (vtx-< ≤-refl))
           (snd (snd (liftF-lk vf ef k τ o s)))))
      where
      lτ  = liftChF vf ef τ o
      v   = var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
      le′ = liftF vf ef e (∣ pathCh τ ∣ + o)
    ...   | inj₂ (inj₂ refl) =
      ∈-++l (fvSub lτ ++ fvTm v) (fvTm le′) (∈-++r (fvSub lτ) (fvTm v) (∈-here (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o))) []))
      where
      lτ  = liftChF vf ef τ o
      v   = var (vf (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
      le′ = liftF vf ef e (∣ pathCh τ ∣ + o)
