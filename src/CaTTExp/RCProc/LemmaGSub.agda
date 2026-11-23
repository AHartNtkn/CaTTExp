------------------------------------------------------------------------
-- Lemma G step (2): a column substitution with composite chain edges
-- factors through the expanded column context (ledger S20 (i), 3d).
--
-- Let θ′ = colSub τ′ w s t x τs : Γ → colCtx m′ n′ (prefix chain τ′
-- from a, suffix chain τs from w, x : s ⇒ t over v → w), and put
-- λ′ = pathCh τ′, ρ′ = pathCh τs, m = ∣λ′∣, n = ∣ρ′∣. The substitution
--
--   ς = colSub (liftF τ′) L (var (L+1)) (var (L+2)) (L+3) (liftF τs)
--       : colCtx m n → colCtx m′ n′           (L = len (C₀ m))
--
-- re-reads τ′ and τs inside the two chains of colCtx m n (LiftF), and
-- θ′ = ς ∘ θ_g with θ_g = θg Γ a λ′ w s t x ρ′ (`factor`). ς is typed
-- (`ς-wf`).
------------------------------------------------------------------------
module CaTTExp.RCProc.LemmaGSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (lk-ext; lk-top)
open import CaTTExp.GraphFillerTotal
  using (path; pathCh; ∣_∣; wgo; wsub; tgtOf; wgo-keep; Walk; walkCh; last-var; sub-len)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx; T→<; _≤_; ≤-refl; +-zero)
open import CaTTExp.RCProc.Column using (C₀; e₀; colCtx; C₀-chainC; e₀-vtx)
open import CaTTExp.RCProc.LiftF using (ChainIn; liftF; liftChF; liftF-lk; module Typed; SegF; liftChF-sub)
open import CaTTExp.RCProc.ColSub
open import CaTTExp.RCProc.Walk using (θg)
open import CaTTExp.RCProc.Edges using (bd; wgo-len)
open import CaTTExp.RCProc.Column using (chainFrom; colEnd)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top)
open import CaTTExp.GraphFillerTotal.Chains using (chainC-wf)

private
  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc′ zero    (suc n) _ = tt
  <-suc′ (suc i) (suc n) p = <-suc′ i n p

  lk-at : ∀ σ a n → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a) n ≡ a
  lk-at σ a .(lenₛ σ) refl = lk-top σ a

  l2 : ∀ N → T (N <ℕ suc (suc N))
  l2 N = <-suc′ N (suc N) (self N)
  l3 : ∀ N → T (N <ℕ suc (suc (suc N)))
  l3 N = <-suc′ N (suc (suc N)) (l2 N)
  l4 : ∀ N → T (N <ℕ suc (suc (suc (suc N))))
  l4 N = <-suc′ N (suc (suc (suc N))) (l3 N)

  len-chainFrom : ∀ Γ x n → len (chainFrom Γ x n) ≡ bd (len Γ) n
  len-chainFrom Γ x zero    = refl
  len-chainFrom Γ x (suc n) = len-chainFrom (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n

------------------------------------------------------------------------
-- Segments of walk substitutions, with the chainFrom indexing.

segF-unshift : ∀ vf ef {Γ σ o x} p →
               SegF (λ j → vf (suc j)) (λ j → ef (suc j)) Γ σ o x p → SegF vf ef Γ σ (suc o) x p
segF-unshift vf ef []      h            = h
segF-unshift vf ef (e ∷ p) (h , he , r) = h , he , segF-unshift vf ef p r

wgo-segF : ∀ Γ σ x′ y p → T (x′ <ℕ lenₛ σ) → lookupₛ σ x′ ≡ var y →
           SegF (vfF (lenₛ σ) x′) (efF (lenₛ σ) x′) Γ (wgo Γ σ y p) 0 y p
wgo-segF Γ σ x′ y []      px lx = lx
wgo-segF Γ σ x′ y (e ∷ p) px lx =
  trans (wgo-keep σ₁ z p x′ (T→< _ _ (<-suc′ x′ _ (<-suc′ x′ _ px))))
        (trans (lk-ext (σ ,ₛ var z) (var e) x′ (<-suc′ x′ _ px)) (trans (lk-ext σ (var z) x′ px) lx)) ,
  trans (wgo-keep σ₁ z p (suc (lenₛ σ)) (T→< _ _ (self (suc (lenₛ σ))))) (lk-top (σ ,ₛ var z) (var e)) ,
  segF-unshift (vfF (lenₛ σ) x′) (efF (lenₛ σ) x′) p
    (wgo-segF Γ σ₁ (lenₛ σ) z p (<-suc′ (lenₛ σ) (suc (lenₛ σ)) (self (lenₛ σ)))
       (trans (lk-ext (σ ,ₛ var z) (var e) (lenₛ σ) (self (lenₛ σ))) (lk-top σ (var z))))
  where
  z  = tgtOf Γ e
  σ₁ = σ ,ₛ var z ,ₛ var e

-- Extending σ by a walk does not change ρ ∘ σ when ρ is scoped in σ.
ext-wgo : ∀ Γ ρ σ y p → S.ScSub (lenₛ σ) ρ → ρ ∘ wgo Γ σ y p ≡ ρ ∘ σ
ext-wgo Γ ρ σ y []      sc = refl
ext-wgo Γ ρ σ y (e ∷ p) sc =
  trans (ext-wgo Γ ρ σ₁ (tgtOf Γ e) p (S.scSub-suc ρ (S.scSub-suc ρ sc)))
        (trans (S.ext-sub ρ (σ ,ₛ var (tgtOf Γ e)) (var e) (S.scSub-suc ρ sc))
               (S.ext-sub ρ σ (var (tgtOf Γ e)) sc))
  where σ₁ = σ ,ₛ var (tgtOf Γ e) ,ₛ var e

------------------------------------------------------------------------
-- The 2-disc block: four variables after a scoped ρ, read through a
-- walk extension of σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d.

module _ (σ : Sub) (a b c d : Tm) where
  private
    N  = lenₛ σ
    σ₁ = σ ,ₛ a
    σ₂ = σ₁ ,ₛ b
    σ₃ = σ₂ ,ₛ c
    σ₄ = σ₃ ,ₛ d

  lk4-0 : lookupₛ σ₄ N ≡ a
  lk4-0 = trans (lk-ext σ₃ d N (l3 N)) (trans (lk-ext σ₂ c N (l2 N)) (trans (lk-ext σ₁ b N (self N)) (lk-top σ a)))

  blk : ∀ Γ y p ρ → S.ScSub N ρ →
        (ρ ,ₛ var N ,ₛ var (suc N) ,ₛ var (suc (suc N)) ,ₛ var (suc (suc (suc N)))) ∘ wgo Γ σ₄ y p
        ≡ (ρ ∘ σ) ,ₛ a ,ₛ b ,ₛ c ,ₛ d
  blk Γ y p ρ sc =
    trans (ext-wgo Γ B σ₄ y p ((((sc₄ , l4 N) , l3 N) , l2 N) , self N))
          (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ eρ lk4-0) e₁) e₂) (lk-top σ₃ d))
    where
    B = ρ ,ₛ var N ,ₛ var (suc N) ,ₛ var (suc (suc N)) ,ₛ var (suc (suc (suc N)))
    sc₁ = S.scSub-suc ρ sc
    sc₂ = S.scSub-suc ρ sc₁
    sc₃ = S.scSub-suc ρ sc₂
    sc₄ = S.scSub-suc ρ sc₃
    eρ : ρ ∘ σ₄ ≡ ρ ∘ σ
    eρ = trans (S.ext-sub ρ σ₃ d sc₃) (trans (S.ext-sub ρ σ₂ c sc₂) (trans (S.ext-sub ρ σ₁ b sc₁) (S.ext-sub ρ σ a sc)))
    e₁ : lookupₛ σ₄ (suc N) ≡ b
    e₁ = trans (lk-ext σ₃ d (suc N) (l2 N)) (trans (lk-ext σ₂ c (suc N) (self N)) (lk-top σ₁ b))
    e₂ : lookupₛ σ₄ (suc (suc N)) ≡ c
    e₂ = trans (lk-ext σ₃ d (suc (suc N)) (self N)) (lk-top σ₂ c)

------------------------------------------------------------------------
-- ς, and θ′ = ς ∘ θ_g.

ςL : Nat → Sub → Sub → Sub
ςL L τ′ τs =
  colSub (liftChF (vfF 1 0) (efF 1 0) τ′ 0) L (var (suc L)) (var (suc (suc L))) (suc (suc (suc L)))
         (liftChF (vfF (suc (suc (suc (suc L)))) L) (efF (suc (suc (suc (suc L)))) L) τs 0)

ς : Sub → Sub → Sub
ς τ′ τs = ςL (len (C₀ ∣ pathCh τ′ ∣)) τ′ τs

module _ {Γ a w s t x m′ n′ τ′ τs}
         (sτ′ : Γ ⊢sub τ′ ∶ chainC m′) (l0 : lookupₛ τ′ 0 ≡ var a)
         (sτs : Γ ⊢sub τs ∶ chainC n′) (lw : lookupₛ τs 0 ≡ var w) where
  private
    m  = ∣ pathCh τ′ ∣
    σλ = wsub Γ a (pathCh τ′)
    P  = liftChF (vfF 1 0) (efF 1 0) τ′ 0

    ctxC : C₀ m ⊢ctx
    ctxC = subst _⊢ctx (sym (C₀-chainC m)) (chainC-wf m)

    scP : S.ScSub (len (C₀ m)) P
    scP = fst (S.sub-sc closed (Typed.liftChF-ty (vfF 1 0) (efF 1 0) (chainIn-from (ε ▸ ⋆) 0 m ctxC refl)
                                  m′ τ′ 0 sτ′ (subst (_≤ m) (sym (+-zero m)) ≤-refl)))

    lσ : lenₛ σλ ≡ len (C₀ m)
    lσ = trans (wgo-len Γ (⟨⟩ ,ₛ var a) a (pathCh τ′)) (sym (len-chainFrom (ε ▸ ⋆) 0 m))

    factorL : ∀ L → lenₛ σλ ≡ L → S.ScSub L P →
              ςL L τ′ τs ∘ θg Γ a (pathCh τ′) w s t x (pathCh τs) ≡ colSub τ′ w s t x τs
    factorL .(lenₛ σλ) refl sc =
      trans (appCh-∘ (P ,ₛ var N ,ₛ var (suc N) ,ₛ var (suc (suc N)) ,ₛ var (suc (suc (suc N)))) Ts θ)
            (cong₂ appCh
              (trans (blk σλ (var w) s t (var x) Γ w (pathCh τs) P sc)
                     (cong (λ X → X ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x)
                           (liftChF-sub (vfF 1 0) (efF 1 0) m′ τ′ 0 sτ′ l0
                              (wgo-segF Γ (⟨⟩ ,ₛ var a) 0 a (pathCh τ′) tt refl))))
              (liftChF-sub (vfF (suc (suc (suc (suc N)))) N) (efF (suc (suc (suc (suc N)))) N) n′ τs 0 sτs lw
                 (wgo-segF Γ σ₄ (lenₛ σλ) w (pathCh τs) (l4 (lenₛ σλ)) (lk4-0 σλ (var w) s t (var x)))))
      where
      θ  = θg Γ a (pathCh τ′) w s t x (pathCh τs)
      N  = lenₛ σλ
      Ts = liftChF (vfF (suc (suc (suc (suc N)))) N) (efF (suc (suc (suc (suc N)))) N) τs 0
      σ₄ = σλ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x

  factor : ς τ′ τs ∘ θg Γ a (pathCh τ′) w s t x (pathCh τs) ≡ colSub τ′ w s t x τs
  factor = factorL (len (C₀ m)) lσ scP

-- ς is a substitution colCtx m n → colCtx m′ n′.
module _ {Γ m′ n′ τ′ τs} (sτ′ : Γ ⊢sub τ′ ∶ chainC m′) (sτs : Γ ⊢sub τs ∶ chainC n′) where
  private
    m = ∣ pathCh τ′ ∣
    n = ∣ pathCh τs ∣
    open ColCtx m n using (L; Ra; col-wf; pre; suf)

    le : ∀ k → k + 0 ≤ k
    le k = subst (_≤ k) (sym (+-zero k)) ≤-refl

    P  = liftChF (vfF 1 0) (efF 1 0) τ′ 0
    Ts = liftChF (vfF (len Ra) L) (efF (len Ra) L) τs 0

    lvP : lookupₛ P (vtx m′) ≡ var (e₀ m)
    lvP = trans (snd (snd (liftF-lk (vfF 1 0) (efF 1 0) m′ τ′ 0 sτ′)))
                (cong var (trans (cong (vfF 1 0) (+-zero m)) (sym (endFrom-vf (ε ▸ ⋆) 0 m))))

    dX : colCtx m n ⊢tm var (suc (suc (suc L))) ∶
         arr (arr ⋆ (var (e₀ m)) (var L)) (var (suc L)) (var (suc (suc L)))
    dX = var-wf col-wf (ext-from Ra L n (suc (suc (suc L))) (lookup-top (C₀ m ▸ ⋆ ▸ F ▸ F) _))
      where F = arr ⋆ (var (e₀ m)) (var L)

  private
    wf′ = colSub-wf′ m′ n′
            (Typed.liftChF-ty (vfF 1 0) (efF 1 0) pre m′ τ′ 0 sτ′ (le m)) lvP dX
            (Typed.liftChF-ty (vfF (len Ra) L) (efF (len Ra) L) suf n′ τs 0 sτs (le n))
            (fst (snd (liftF-lk (vfF (len Ra) L) (efF (len Ra) L) n′ τs 0 sτs)))

  ς-wf : colCtx m n ⊢sub ς τ′ τs ∶ colCtx m′ n′
  ς-wf = fst wf′

  -- ς sends the end of colCtx m′ n′ to the end of colCtx m n.
  ς-end : lookupₛ (ς τ′ τs) (colEnd m′ n′) ≡ var (colEnd m n)
  ς-end = trans (snd wf′)
          (trans (snd (snd (liftF-lk (vfF (len Ra) L) (efF (len Ra) L) n′ τs 0 sτs)))
                 (cong var (trans (cong (vfF (len Ra) L) (+-zero n)) (sym (endFrom-vf Ra L n)))))
