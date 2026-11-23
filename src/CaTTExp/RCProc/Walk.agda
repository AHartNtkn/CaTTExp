------------------------------------------------------------------------
-- Walks into chain extensions (ledger S20 (i), stage 3c).
--
-- GraphFillerTotal types the walk substitution `wgo` into `chainC`.
-- Here the target is any context Θ extended by a chain from x′
-- (`Column.chainFrom Θ x′ ∣p∣`), as needed for the suffix chain of a
-- column context (`wgoF-ty`), with its value at the end (`wgoF-end`).
------------------------------------------------------------------------
module CaTTExp.RCProc.Walk where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.Derived using (lk-ext; lk-top)
open import CaTTExp.GraphFillerTotal
  using (∣_∣; Walk; nil; cons; wgo; tgtOf; tgtOf-eq; endOf; lookup-wf)
open import CaTTExp.RCProc.Column using (chainFrom; endFrom)

private
  neq : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  neq zero    (suc n) _ = refl
  neq (suc i) (suc n) p = neq i n p

  <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc′ zero    (suc n) _ = tt
  <-suc′ (suc i) (suc n) p = <-suc′ i n p

  lookup-lt : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
  lookup-lt ε       i ()
  lookup-lt (Γ ▸ B) i eq with i ==ℕ len Γ in e
  ... | true  = subst (λ j → T (j <ℕ suc (len Γ))) (sym (==ℕ-sound i (len Γ) (subst T (sym e) tt))) (self (len Γ))
    where
    self : ∀ n → T (n <ℕ suc n)
    self zero    = tt
    self (suc n) = self n
  ... | false = <-suc′ i (len Γ) (lookup-lt Γ i eq)

  lk-y : ∀ σ a b n → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a ,ₛ b) n ≡ a
  lk-y σ a b .(lenₛ σ) refl = trans (lk-ext (σ ,ₛ a) b (lenₛ σ) (self (lenₛ σ))) (lk-top σ a)
    where
    self : ∀ n → T (n <ℕ suc n)
    self zero    = tt
    self (suc n) = self n

  lk-1 : ∀ σ a i → T (i <ℕ lenₛ σ) → lookupₛ (σ ,ₛ a) i ≡ lookupₛ σ i
  lk-1 = lk-ext

wgoF-end : ∀ Γ Θ σ x′ x p → lenₛ σ ≡ len Θ → lookupₛ σ x′ ≡ var x →
           lookupₛ (wgo Γ σ x p) (endFrom Θ x′ ∣ p ∣) ≡ var (endOf Γ x p)
wgoF-end Γ Θ σ x′ x []      l lx = lx
wgoF-end Γ Θ σ x′ x (e ∷ p) l lx =
  wgoF-end Γ (Θ ▸ ⋆ ▸ arr ⋆ (var x′) (var (len Θ))) (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (len Θ) (tgtOf Γ e) p
    (cong (λ n → suc (suc n)) l) (lk-y σ _ _ (len Θ) l)

wgoF-ty : ∀ {Γ Θ σ x′ x p y} → Γ ⊢sub σ ∶ Θ → lookup Θ x′ ≡ just ⋆ → lookupₛ σ x′ ≡ var x →
          Walk Γ x p y → Γ ⊢sub wgo Γ σ x p ∶ chainFrom Θ x′ ∣ p ∣
wgoF-ty s lΘ lx nil = s
wgoF-ty {Γ} {Θ} {σ} {x′} {x} s lΘ lx (cons {z = z} {e = e} {p = p} le w)
  with lookup-wf (S.sub-ctx closed s) le
... | arr-wf _ dz =
  subst (λ t → Γ ⊢sub wgo Γ (σ ,ₛ var t ,ₛ var e) t p ∶ chainFrom Θ′ (len Θ) ∣ p ∣) (sym (tgtOf-eq {Γ} le))
    (wgoF-ty s₁ (lookup-wk (Θ ▸ ⋆) (len Θ) F (lookup-top Θ ⋆)) (lk-y σ (var z) (var e) (len Θ) l) w)
  where
  F  = arr ⋆ (var x′) (var (len Θ))
  Θ′ = Θ ▸ ⋆ ▸ F
  l : lenₛ σ ≡ len Θ
  l = snd (S.sub-sc closed s)
  x< : T (x′ <ℕ lenₛ σ)
  x< = subst (λ n → T (x′ <ℕ n)) (sym l) (lookup-lt Θ x′ lΘ)
  eF : F [ σ ,ₛ var z ]ty ≡ arr ⋆ (var x) (var z)
  eF = cong₂ (arr ⋆) (trans (lk-1 σ (var z) x′ x<) lx)
         (subst (λ n → lookupₛ (σ ,ₛ var z) n ≡ var z) l (lk-top σ (var z)))
  s₁ : Γ ⊢sub σ ,ₛ var z ,ₛ var e ∶ Θ′
  s₁ = ,-wf (,-wf s dz) (subst (Γ ⊢tm var e ∶_) (sym eF) (var-wf (S.sub-ctx closed s) le))

------------------------------------------------------------------------
-- θ_g: the substitution of a whiskered generator (λ, x, ρ) into the
-- column context: the walk λ, then w, s, t, x (x : s ⇒ t, s t : v → w),
-- then the walk ρ.

open import CaTTExp.Derived using (tm-ty; subst₂)
open import CaTTExp.GraphFillerTotal using (wsub; wgo-ty; wgo-seg; seg-head; seg-end; walk-end; Seg; tm-ctx; wgo-keep)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx; +-zero; T→<)
open import CaTTExp.RCProc.Column using (C₀; e₀; colCtx; colEnd; C₀-chainC; e₀-vtx)
open import CaTTExp.PsRaise using (Raised)
open import CaTTExp.RCProc.Edges using (bd; edgesAt; lt-bd; wgo-len; edgesAt-keep; wgo-edges)

θg : Ctx → Nat → List Nat → Nat → Tm → Tm → Nat → List Nat → Sub
θg Γ a λ′ w s t x ρ = wgo Γ (wsub Γ a λ′ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x) w ρ

module _ {Γ a λ′ v w s t x ρ b}
         (da : Γ ⊢tm var a ∶ ⋆) (wλ : Walk Γ a λ′ v)
         (dx : Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t) (wρ : Walk Γ w ρ b) where
  private
    m = ∣ λ′ ∣
    C = C₀ m
    σλ = wsub Γ a λ′
    wΓ = tm-ctx da

    sλ′ : Γ ⊢sub σλ ∶ chainC m
    sλ′ = subst (λ k → Γ ⊢sub σλ ∶ chainC k) (+-zero m)
                (wgo-ty (,-wf (⟨⟩-wf wΓ) da) refl wλ)

    sλ : Γ ⊢sub σλ ∶ C
    sλ = subst (Γ ⊢sub σλ ∶_) (sym (C₀-chainC m)) sλ′

    lC : lenₛ σλ ≡ len C
    lC = snd (S.sub-sc closed sλ)

    sg : Seg Γ σλ 0 a λ′
    sg = wgo-seg λ′ refl refl

    lv : lookupₛ σλ (e₀ m) ≡ var v
    lv = trans (cong (lookupₛ σλ) (trans (e₀-vtx m) (cong vtx (sym (+-zero m)))))
               (trans (seg-end λ′ sg) (cong var (walk-end wλ)))

    e< : T (e₀ m <ℕ lenₛ σλ)
    e< = subst (λ k → T (e₀ m <ℕ k)) (sym lC) (lookup-lt C (e₀ m) le)
      where
      le : lookup C (e₀ m) ≡ just ⋆
      le = subst₂ (λ Δ i → lookup Δ i ≡ just ⋆) (sym (C₀-chainC m)) (sym (e₀-vtx m))
             (CaTTExp.GraphFillerTotal.Chains.lookup-vtx m m CaTTExp.GraphFillerTotal.Chains.≤-refl)

    tys : Σ (Γ ⊢tm s ∶ arr ⋆ (var v) (var w)) λ _ → Γ ⊢tm t ∶ arr ⋆ (var v) (var w)
    tys with tm-ty dx
    ... | arr-wf ds dt = ds , dt

    dw : Γ ⊢tm var w ∶ ⋆
    dw with tm-ty (fst tys)
    ... | arr-wf _ q = q

    F = arr ⋆ (var (e₀ m)) (var (len C))

    σ₁ = σλ ,ₛ var w
    σ₂ = σ₁ ,ₛ s
    σ₃ = σ₂ ,ₛ t

    l₁ : lenₛ σλ ≡ len C
    l₁ = lC

    -- F under the three extensions.
    F₁ : F [ σ₁ ]ty ≡ arr ⋆ (var v) (var w)
    F₁ = cong₂ (arr ⋆) (trans (lk-1 σλ (var w) (e₀ m) e<) lv)
                       (subst (λ k → lookupₛ σ₁ k ≡ var w) lC (lk-top σλ (var w)))

    <s : ∀ i → T (i <ℕ lenₛ σ₁) → T (i <ℕ lenₛ σ₂)
    <s i p = <-suc′ i (lenₛ σ₁) p

    lt-e : T (e₀ m <ℕ lenₛ σ₁)
    lt-e = <-suc′ (e₀ m) (lenₛ σλ) e<

    lt-C : T (len C <ℕ lenₛ σ₁)
    lt-C = subst (λ k → T (len C <ℕ suc k)) (sym lC) (self (len C))
      where
      self : ∀ n → T (n <ℕ suc n)
      self zero    = tt
      self (suc n) = self n

    F₂ : F [ σ₂ ]ty ≡ arr ⋆ (var v) (var w)
    F₂ = trans (cong₂ (arr ⋆) (lk-1 σ₁ s (e₀ m) lt-e) (lk-1 σ₁ s (len C) lt-C)) F₁

    F₃ : F [ σ₃ ]ty ≡ arr ⋆ (var v) (var w)
    F₃ = trans (cong₂ (arr ⋆) (lk-1 σ₂ t (e₀ m) (<s (e₀ m) lt-e)) (lk-1 σ₂ t (len C) (<s (len C) lt-C))) F₂

    ls : lookupₛ σ₃ (suc (len C)) ≡ s
    ls = trans (lk-1 σ₂ t (suc (len C)) (subst (λ k → T (suc (len C) <ℕ suc (suc k))) (sym lC) (self (suc (len C)))))
               (subst (λ k → lookupₛ σ₂ (suc k) ≡ s) lC (lk-top σ₁ s))
      where
      self : ∀ n → T (n <ℕ suc n)
      self zero    = tt
      self (suc n) = self n

    lt : lookupₛ σ₃ (suc (suc (len C))) ≡ t
    lt = subst (λ k → lookupₛ σ₃ (suc (suc k)) ≡ t) lC (lk-top σ₂ t)

    sCol : Γ ⊢sub σ₃ ,ₛ var x ∶ Raised C (e₀ m) ⋆
    sCol = ,-wf (,-wf (,-wf (,-wf sλ dw) (subst (Γ ⊢tm s ∶_) (sym F₁) (fst tys)))
                                         (subst (Γ ⊢tm t ∶_) (sym F₂) (snd tys)))
                (subst (Γ ⊢tm var x ∶_) (sym (cong₃ arr F₃ ls lt)) dx)
      where
      cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
              a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
      cong₃ f refl refl refl = refl

    lyC : lookup (Raised C (e₀ m) ⋆) (len C) ≡ just ⋆
    lyC = lookup-wk (C ▸ ⋆ ▸ F ▸ F) (len C) _ (lookup-wk (C ▸ ⋆ ▸ F) (len C) F
            (lookup-wk (C ▸ ⋆) (len C) F (lookup-top C ⋆)))

    lyσ : lookupₛ (σ₃ ,ₛ var x) (len C) ≡ var w
    lyσ = trans (lk-1 σ₃ (var x) (len C) (<-suc′ (len C) (lenₛ σ₂) (<s (len C) lt-C)))
            (trans (lk-1 σ₂ t (len C) (<s (len C) lt-C)) (trans (lk-1 σ₁ s (len C) lt-C)
              (subst (λ k → lookupₛ σ₁ k ≡ var w) lC (lk-top σλ (var w)))))

  θg-wf : Γ ⊢sub θg Γ a λ′ w s t x ρ ∶ colCtx m ∣ ρ ∣
  θg-wf = wgoF-ty sCol lyC lyσ wρ

  θg-0 : lookupₛ (θg Γ a λ′ w s t x ρ) 0 ≡ var a
  θg-0 = trans (wgo-keep (σ₃ ,ₛ var x) w ρ 0 (T→< 0 _ tt))
           (trans (lk-1 σ₃ (var x) 0 tt) (trans (lk-1 σ₂ t 0 tt) (trans (lk-1 σ₁ s 0 tt)
             (trans (lk-1 σλ (var w) 0 (zero< λ′)) (seg-head λ′ sg)))))
    where
    zero< : ∀ p → T (0 <ℕ lenₛ (wsub Γ a p))
    zero< p = pos (⟨⟩ ,ₛ var a) a p tt
      where
      pos : ∀ σ y q → T (0 <ℕ lenₛ σ) → T (0 <ℕ lenₛ (wgo Γ σ y q))
      pos σ y []      h = h
      pos σ y (e ∷ q) h = pos (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) q tt

  θg-end : lookupₛ (θg Γ a λ′ w s t x ρ) (colEnd m ∣ ρ ∣) ≡ var b
  θg-end = trans (wgoF-end Γ (Raised C (e₀ m) ⋆) (σ₃ ,ₛ var x) (len C) w ρ (snd (S.sub-sc closed sCol)) lyσ)
                 (cong var (walk-end wρ))

  -- The edges of θ_g: λ, then the slots of s and t, then ρ
  -- (CaTTExp.RCProc.Edges).
  private
    L₀ = bd 1 m
    σ₄ = σ₃ ,ₛ var x

    bL : L₀ ≡ len C
    bL = trans (sym (wgo-len Γ (⟨⟩ ,ₛ var a) a λ′)) lC

    self′ : ∀ n → T (n <ℕ suc n)
    self′ zero    = tt
    self′ (suc n) = self′ n

    keep₄ : ∀ i → T (i <ℕ lenₛ σ₄) → lookupₛ (θg Γ a λ′ w s t x ρ) i ≡ lookupₛ σ₄ i
    keep₄ i p = wgo-keep σ₄ w ρ i (T→< i (lenₛ σ₄) p)


  private
    s1 = <-suc′
    nσ = lenₛ σλ
    nC = len C

  θg-λ : edgesAt (θg Γ a λ′ w s t x ρ) 1 m ≡ λ′
  θg-λ = trans (edgesAt-keep σλ (θg Γ a λ′ w s t x ρ) 1 m h) (wgo-edges Γ (⟨⟩ ,ₛ var a) a λ′)
    where
    h : ∀ i → T (i <ℕ L₀) → lookupₛ (θg Γ a λ′ w s t x ρ) i ≡ lookupₛ σλ i
    h i p = trans (keep₄ i b4)
              (trans (lk-1 σ₃ (var x) i b3)
              (trans (lk-1 σ₂ t i b2)
              (trans (lk-1 σ₁ s i b1) (lk-1 σλ (var w) i iσ))))
      where
      iσ : T (i <ℕ nσ)
      iσ = subst (λ k → T (i <ℕ k)) (trans bL (sym lC)) p
      b1 = s1 i nσ iσ
      b2 = s1 i (suc nσ) b1
      b3 = s1 i (suc (suc nσ)) b2
      b4 = s1 i (suc (suc (suc nσ))) b3

  private
    c3 : T (nC <ℕ suc (suc (suc nC)))
    c3 = s1 nC (suc (suc nC)) (s1 nC (suc nC) (self′ nC))

    c2 : T (nC <ℕ suc (suc nC))
    c2 = s1 nC (suc nC) (self′ nC)

    lift : ∀ i (k : Nat → Nat) → T (i <ℕ k nC) → T (i <ℕ k nσ)
    lift i k p = subst (λ n → T (i <ℕ k n)) (sym lC) p

  θg-s : lookupₛ (θg Γ a λ′ w s t x ρ) (suc L₀) ≡ s
  θg-s = subst (λ k → lookupₛ (θg Γ a λ′ w s t x ρ) (suc k) ≡ s) (sym bL)
           (trans (keep₄ (suc nC) (lift (suc nC) (λ n → suc (suc (suc (suc n)))) c3))
                  (trans (lk-1 σ₃ (var x) (suc nC) (lift (suc nC) (λ n → suc (suc (suc n))) c2)) ls))

  θg-t : lookupₛ (θg Γ a λ′ w s t x ρ) (suc (suc L₀)) ≡ t
  θg-t = subst (λ k → lookupₛ (θg Γ a λ′ w s t x ρ) (suc (suc k)) ≡ t) (sym bL)
           (trans (keep₄ (suc (suc nC)) (lift (suc (suc nC)) (λ n → suc (suc (suc (suc n)))) c2))
                  (trans (lk-1 σ₃ (var x) (suc (suc nC)) (lift (suc (suc nC)) (λ n → suc (suc (suc n))) (self′ nC))) lt))

  θg-ρ : edgesAt (θg Γ a λ′ w s t x ρ) (suc (suc (suc (suc L₀)))) ∣ ρ ∣ ≡ ρ
  θg-ρ = subst (λ k → edgesAt (θg Γ a λ′ w s t x ρ) (suc (suc (suc (suc k)))) ∣ ρ ∣ ≡ ρ)
           (wgo-len Γ (⟨⟩ ,ₛ var a) a λ′) (wgo-edges Γ σ₄ w ρ)
