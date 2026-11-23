------------------------------------------------------------------------
-- Substitutions into column contexts (ledger S20 (i), stage 3d,
-- Lemma G step (2)).
--
-- `chainFrom Γ x n` carries an n-step chain from x (`chainIn-from`),
-- with vertex indices `vfF (len Γ) x` and edge indices `efF (len Γ) x`.
-- The column context colCtx m n carries two: its prefix (in C₀ m) and
-- its suffix (from the 2-disc's target vertex). A column substitution
-- is built from a chain substitution for the prefix, the column data
-- (w, s, t, x) and a chain substitution for the suffix (`colSub`,
-- typed by `colSub-wf`; `colSub-wf′` also gives its value at the end).
------------------------------------------------------------------------
module CaTTExp.RCProc.ColSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.Derived using (ps-wf; lk-ext; lk-top)
open import CaTTExp.PsRaise using (Raised)
open import CaTTExp.GrayCtx.Lift using (raiseT)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; _≤_; _<_; z≤n; s≤s)
open import CaTTExp.RCProc.Column using (chainFrom; endFrom; C₀; e₀; colCtx; chainT; flagAt; raised-ctx)
open import CaTTExp.RCProc.LiftF using (ChainIn)

------------------------------------------------------------------------
-- Chains from a point.

vfF : Nat → Nat → Nat → Nat
vfF L x zero    = x
vfF L x (suc j) = vfF (suc (suc L)) L j

efF : Nat → Nat → Nat → Nat
efF L x j = suc (vfF L x j)

endFrom-vf : ∀ Γ x n → endFrom Γ x n ≡ vfF (len Γ) x n
endFrom-vf Γ x zero    = refl
endFrom-vf Γ x (suc n) = endFrom-vf (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n

-- Context extensions keep lookups.
Ext : Ctx → Ctx → Set
Ext Γ Δ = ∀ i {A} → lookup Γ i ≡ just A → lookup Δ i ≡ just A

ext-from : ∀ Γ x n → Ext Γ (chainFrom Γ x n)
ext-from Γ x zero    i e = e
ext-from Γ x (suc n) i e =
  ext-from (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n i
    (lookup-wk (Γ ▸ ⋆) i _ (lookup-wk Γ i ⋆ e))

ext-raised : ∀ Γ x A → Ext Γ (Raised Γ x A)
ext-raised Γ x A i e =
  lookup-wk _ i _ (lookup-wk _ i _ (lookup-wk _ i _ (lookup-wk Γ i A e)))

chainIn-from : ∀ Γ x n → chainFrom Γ x n ⊢ctx → lookup Γ x ≡ just ⋆ →
               ChainIn (chainFrom Γ x n) (vfF (len Γ) x) (efF (len Γ) x) n
chainIn-from Γ x n w lx = record { wΔ = w ; lv = lv n Γ x lx ; le = le n Γ x lx }
  where
  lv : ∀ n Γ x → lookup Γ x ≡ just ⋆ → ∀ j → j ≤ n → lookup (chainFrom Γ x n) (vfF (len Γ) x j) ≡ just ⋆
  lv n       Γ x lx zero    _       = ext-from Γ x n x lx
  lv (suc n) Γ x lx (suc j) (s≤s p) =
    lv n (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ)
       (lookup-wk (Γ ▸ ⋆) (len Γ) _ (lookup-top Γ ⋆)) j p
  le : ∀ n Γ x → lookup Γ x ≡ just ⋆ → ∀ j → j < n →
       lookup (chainFrom Γ x n) (efF (len Γ) x (suc j))
         ≡ just (arr ⋆ (var (vfF (len Γ) x j)) (var (vfF (len Γ) x (suc j))))
  le (suc n) Γ x lx zero    _       =
    ext-from (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n (suc (len Γ))
      (lookup-top (Γ ▸ ⋆) (arr ⋆ (var x) (var (len Γ))))
  le (suc n) Γ x lx (suc j) (s≤s p) =
    le n (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ)
       (lookup-wk (Γ ▸ ⋆) (len Γ) _ (lookup-top Γ ⋆)) j p

chainIn-ext : ∀ {Δ Δ′ vf ef K} → ChainIn Δ vf ef K → Δ′ ⊢ctx → Ext Δ Δ′ → ChainIn Δ′ vf ef K
chainIn-ext C w e = record { wΔ = w ; lv = λ j p → e _ (ChainIn.lv C j p) ; le = λ j p → e _ (ChainIn.le C j p) }

------------------------------------------------------------------------
-- The column context and its two chains.

module ColCtx (m n : Nat) where
  L : Nat
  L = len (C₀ m)

  Ra : Ctx
  Ra = Raised (C₀ m) (e₀ m) ⋆

  col-ps : colCtx m n ⊢ps
  col-ps = subst _⊢ps (raised-ctx m n) (snd (psOf (raiseT (flagAt m) (chainT (suc (m + n))))))

  col-wf : colCtx m n ⊢ctx
  col-wf with col-ps
  ... | ps d = fst (ps-wf d)

  -- The context grows: C₀ m ⊆ Raised ⊆ colCtx.
  ext-C : Ext (C₀ m) (colCtx m n)
  ext-C i e = ext-from Ra L n i (ext-raised (C₀ m) (e₀ m) ⋆ i e)

  private
    ctx-C : C₀ m ⊢ctx
    ctx-C = chainC-ctx′
      where
      open import CaTTExp.GraphFillerTotal.Chains using (chainC-wf)
      open import CaTTExp.RCProc.Column using (C₀-chainC)
      chainC-ctx′ : C₀ m ⊢ctx
      chainC-ctx′ = subst _⊢ctx (sym (C₀-chainC m)) (chainC-wf m)

  pre : ChainIn (colCtx m n) (vfF 1 0) (efF 1 0) m
  pre = chainIn-ext (chainIn-from (ε ▸ ⋆) 0 m ctx-C refl) col-wf ext-C

  -- The 2-disc's target vertex w is at L, and the suffix starts there.
  lw : lookup Ra L ≡ just ⋆
  lw = lookup-wk _ L _ (lookup-wk _ L _ (lookup-wk _ L _ (lookup-top (C₀ m) ⋆)))

  suf : ChainIn (colCtx m n) (vfF (len Ra) L) (efF (len Ra) L) n
  suf = chainIn-from Ra L n col-wf lw

------------------------------------------------------------------------
-- Appending a chain substitution (its tail) after σ.

appCh : Sub → Sub → Sub
appCh σ ⟨⟩            = σ
appCh σ (⟨⟩ ,ₛ _)     = σ
appCh σ (τ ,ₛ a ,ₛ b) = appCh σ τ ,ₛ a ,ₛ b

appCh-∘ : ∀ σ τ θ → appCh σ τ ∘ θ ≡ appCh (σ ∘ θ) (τ ∘ θ)
appCh-∘ σ ⟨⟩            θ = refl
appCh-∘ σ (⟨⟩ ,ₛ _)     θ = refl
appCh-∘ σ (τ ,ₛ a ,ₛ b) θ = cong (λ X → X ,ₛ a [ θ ]tm ,ₛ b [ θ ]tm) (appCh-∘ σ τ θ)

-- chainFrom, one step at the end.
chainFrom-snoc : ∀ Θ x k → chainFrom Θ x (suc k)
                 ≡ chainFrom Θ x k ▸ ⋆ ▸ arr ⋆ (var (endFrom Θ x k)) (var (len (chainFrom Θ x k)))
chainFrom-snoc Θ x zero    = refl
chainFrom-snoc Θ x (suc k) = chainFrom-snoc (Θ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Θ))) (len Θ) k

open import CaTTExp.GraphFillerTotal using (sub-len; last-obj; edge-ty)
open import CaTTExp.GraphFillerTotal.Chains using (vtx; lookupₛ-here; lookupₛ-there; T→<)

private
  len-snoc : ∀ Θ x k → len (chainFrom Θ x (suc k)) ≡ suc (suc (len (chainFrom Θ x k)))
  len-snoc Θ x k = cong len (chainFrom-snoc Θ x k)

end-lt : ∀ Θ x k → T (x <ℕ len Θ) → T (endFrom Θ x k <ℕ len (chainFrom Θ x k))
end-lt Θ x zero    p = p
end-lt Θ x (suc k) p = end-lt (Θ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Θ))) (len Θ) k (self₂ (len Θ))
  where
  self₂ : ∀ n → T (n <ℕ suc (suc n))
  self₂ zero    = tt
  self₂ (suc n) = self₂ n

appCh-wf : ∀ {Γ σ Θ x′} k {τ} → T (x′ <ℕ len Θ) → Γ ⊢sub σ ∶ Θ → Γ ⊢sub τ ∶ chainC k → lookupₛ τ 0 ≡ lookupₛ σ x′ →
           (Γ ⊢sub appCh σ τ ∶ chainFrom Θ x′ k) × (lookupₛ (appCh σ τ) (endFrom Θ x′ k) ≡ lookupₛ τ (vtx k))
appCh-wf zero {⟨⟩ ,ₛ x₀} _ sσ _ e = sσ , sym e
appCh-wf zero {_ ,ₛ _ ,ₛ _} _ sσ (,-wf () _) e
appCh-wf {Γ} {σ} {Θ} {x′} (suc k) {τ ,ₛ a ,ₛ b} px sσ (,-wf (,-wf sτ da) db) e =
  subst (Γ ⊢sub appCh σ τ ,ₛ a ,ₛ b ∶_) (sym (chainFrom-snoc Θ x′ k))
    (,-wf (,-wf s₁ da) (subst (Γ ⊢tm b ∶_) (sym eF) db)) ,
  trans (cong (lookupₛ (appCh σ τ ,ₛ a ,ₛ b)) (end-snoc Θ x′ k))
        (trans (lookupₛ-there (appCh σ τ ,ₛ a) b _ (subst (len (chainFrom Θ x′ k) <_) (cong suc (sym ln)) ≤-refl′))
               (trans (lookupₛ-here (appCh σ τ) a _ (sym ln)) (sym (last-obj sτ))))
  where
  IH = appCh-wf k px sσ sτ (trans (sym (CaTTExp.GraphFillerTotal.lookupₛ-there₂ τ a b 0 (CaTTExp.GraphFillerTotal.zero< sτ))) e)
  s₁ = fst IH
  ln : lenₛ (appCh σ τ) ≡ len (chainFrom Θ x′ k)
  ln = snd (S.sub-sc closed s₁)
  ≤-refl′ : ∀ {n} → n ≤ n
  ≤-refl′ = CaTTExp.GraphFillerTotal.Chains.≤-refl
  end-snoc : ∀ Θ x k → endFrom Θ x (suc k) ≡ len (chainFrom Θ x k)
  end-snoc Θ x zero    = refl
  end-snoc Θ x (suc k) = end-snoc (Θ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Θ))) (len Θ) k
  eF : arr ⋆ (var (endFrom Θ x′ k)) (var (len (chainFrom Θ x′ k))) [ appCh σ τ ,ₛ a ]ty
       ≡ arr ⋆ (var (vtx k)) (var (vtx (suc k))) [ τ ,ₛ a ]ty
  eF = trans (cong₂ (arr ⋆)
                (trans (lookupₛ-there (appCh σ τ) a _ (T→< _ _ (subst (λ n → T (endFrom Θ x′ k <ℕ n)) (sym ln) (end-lt Θ x′ k px)))) (snd IH))
                (lookupₛ-here (appCh σ τ) a _ (sym ln)))
             (sym (edge-ty sτ))

------------------------------------------------------------------------
-- Typing into a raised context and into a column context.

private
  <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc′ zero    (suc n) _ = tt
  <-suc′ (suc i) (suc n) p = <-suc′ i n p

  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  lk-at : ∀ σ a n → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a) n ≡ a
  lk-at σ a .(lenₛ σ) refl = lk-top σ a

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

raised-wf : ∀ {Γ σ Θ y v w s t x} → Γ ⊢sub σ ∶ Θ → T (y <ℕ len Θ) → lookupₛ σ y ≡ var v →
            Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t →
            Γ ⊢sub σ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x ∶ Raised Θ y ⋆
raised-wf {Γ} {σ} {Θ} {y} {v} {w} {s} {t} {x} sσ py ly dx with CaTTExp.Derived.tm-ty dx
... | arr-wf ds dt with CaTTExp.Derived.tm-ty ds
...   | arr-wf _ dw =
  ,-wf (,-wf (,-wf (,-wf sσ dw) (subst (Γ ⊢tm s ∶_) (sym F₁) ds))
             (subst (Γ ⊢tm t ∶_) (sym F₂) dt))
       (subst (Γ ⊢tm var x ∶_) (sym (cong₃ arr F₃ ls lt)) dx)
  where
  L = len Θ
  l : lenₛ σ ≡ L
  l = snd (S.sub-sc closed sσ)
  yσ : T (y <ℕ lenₛ σ)
  yσ = subst (λ n → T (y <ℕ n)) (sym l) py
  F = arr ⋆ (var y) (var L)
  σ₁ = σ ,ₛ var w
  σ₂ = σ₁ ,ₛ s
  σ₃ = σ₂ ,ₛ t
  F₁ : F [ σ₁ ]ty ≡ arr ⋆ (var v) (var w)
  F₁ = cong₂ (arr ⋆) (trans (lk-ext σ (var w) y yσ) ly) (lk-at σ (var w) L l)
  scF₀ : S.ScTy (suc (lenₛ σ)) F
  scF₀ = tt , <-suc′ y (lenₛ σ) yσ , subst (λ k → T (L <ℕ suc k)) (sym l) (self L)
  F₂ : F [ σ₂ ]ty ≡ arr ⋆ (var v) (var w)
  F₂ = trans (S.ext-ty F σ₁ s scF₀) F₁
  F₃ : F [ σ₃ ]ty ≡ arr ⋆ (var v) (var w)
  F₃ = trans (S.ext-ty F σ₂ t (S.scTy-suc F scF₀)) F₂
  ls : lookupₛ σ₃ (suc L) ≡ s
  ls = trans (lk-ext σ₂ t (suc L) (subst (λ n → T (suc L <ℕ suc (suc n))) (sym l) (self (suc L))))
             (lk-at σ₁ s (suc L) (cong suc l))
  lt : lookupₛ σ₃ (suc (suc L)) ≡ t
  lt = lk-at σ₂ t (suc (suc L)) (cong (λ n → suc (suc n)) l)

-- A column substitution: prefix chain τ, column data, suffix chain τs.
colSub : Sub → Nat → Tm → Tm → Nat → Sub → Sub
colSub τ w s t x τs = appCh (τ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x) τs

open import CaTTExp.RCProc.Column using (C₀-chainC; e₀-vtx)

-- With the end of the column: colEnd m n = endFrom (Raised (C₀ m) (e₀ m) ⋆) (len (C₀ m)) n.
colSub-wf′ : ∀ {Γ τ v w s t x τs} m n → Γ ⊢sub τ ∶ chainC m → lookupₛ τ (vtx m) ≡ var v →
             Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t →
             Γ ⊢sub τs ∶ chainC n → lookupₛ τs 0 ≡ var w →
             (Γ ⊢sub colSub τ w s t x τs ∶ colCtx m n) ×
             (lookupₛ (colSub τ w s t x τs) (endFrom (Raised (C₀ m) (e₀ m) ⋆) (len (C₀ m)) n) ≡ lookupₛ τs (vtx n))
colSub-wf′ {Γ} {τ} {v} {w} {s} {t} {x} {τs} m n sτ lv dx sτs lw =
  appCh-wf n (self₄ L) sR sτs (trans lw (sym lwσ))
  where
  L = len (C₀ m)
  sC : Γ ⊢sub τ ∶ C₀ m
  sC = subst (Γ ⊢sub τ ∶_) (sym (C₀-chainC m)) sτ
  lC : lenₛ τ ≡ L
  lC = snd (S.sub-sc closed sC)
  py : T (e₀ m <ℕ L)
  py = subst₂′ (λ a b → T (a <ℕ b)) (sym (e₀-vtx m)) (cong len (sym (C₀-chainC m))) (vtx-lt m)
    where
    subst₂′ : ∀ {A B : Set} (P : A → B → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
    subst₂′ P refl refl p = p
    vtx-lt : ∀ m → T (vtx m <ℕ len (chainC m))
    vtx-lt m = subst (λ n → T (vtx m <ℕ n)) (sym (CaTTExp.GraphFillerTotal.Chains.len-chain m)) (vs m)
      where
      vs : ∀ m → T (vtx m <ℕ vtx (suc m))
      vs zero    = tt
      vs (suc m) = vs′ m
        where
        vs′ : ∀ m → T (vtx (suc m) <ℕ vtx (suc (suc m)))
        vs′ zero    = tt
        vs′ (suc m) = vs′ m
  sR : Γ ⊢sub τ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x ∶ Raised (C₀ m) (e₀ m) ⋆
  sR = raised-wf sC py (trans (cong (lookupₛ τ) (e₀-vtx m)) lv) dx
  self₄ : ∀ n → T (n <ℕ suc (suc (suc (suc n))))
  self₄ zero    = tt
  self₄ (suc n) = self₄ n
  lwσ : lookupₛ (τ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x) L ≡ var w
  lwσ = trans (lk-ext (τ ,ₛ var w ,ₛ s ,ₛ t) (var x) L (subst (λ k → T (L <ℕ suc (suc (suc k)))) (sym lC) (s₃ L)))
        (trans (lk-ext (τ ,ₛ var w ,ₛ s) t L (subst (λ k → T (L <ℕ suc (suc k))) (sym lC) (s₂ L)))
        (trans (lk-ext (τ ,ₛ var w) s L (subst (λ k → T (L <ℕ suc k)) (sym lC) (self L)))
               (lk-at τ (var w) L lC)))
    where
    s₂ : ∀ n → T (n <ℕ suc (suc n))
    s₂ zero = tt
    s₂ (suc n) = s₂ n
    s₃ : ∀ n → T (n <ℕ suc (suc (suc n)))
    s₃ zero = tt
    s₃ (suc n) = s₃ n

colSub-wf : ∀ {Γ τ v w s t x τs} m n → Γ ⊢sub τ ∶ chainC m → lookupₛ τ (vtx m) ≡ var v →
            Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t →
            Γ ⊢sub τs ∶ chainC n → lookupₛ τs 0 ≡ var w →
            Γ ⊢sub colSub τ w s t x τs ∶ colCtx m n
colSub-wf m n sτ lv dx sτs lw = fst (colSub-wf′ m n sτ lv dx sτs lw)
