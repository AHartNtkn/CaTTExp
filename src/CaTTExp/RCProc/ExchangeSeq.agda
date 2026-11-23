------------------------------------------------------------------------
-- Exchange-equivalent 2-paths have connected terms (ledger S20 (i),
-- stage 3e, the sorting half; notes/relative-coherence.md §2 Step 4).
--
-- Over a context Γ with key and boundary lists p∓ satisfying BdOK, and
-- a point a with Γ ⊢ a : ⋆: for every chain S —(w ∷ P)→ T whose source
-- S is a walk a ⇝ b, and every 2-path Q with (w ∷ P) ~ Q
-- (TwoPath._~_, exchange steps anywhere in the path, both directions),
--
--   term a b (w ∷ P) ⇄ term a b Q        (`seqE`)
--
-- by 3-cells both ways. One exchange step is `xchE`: at the front it is
-- Lemma E part (2) (`ExchangeGamma.Setup.Main.exchange`), with a tail it
-- is reassociated around it (Glue3Eqv.assocE, congLE), and under a
-- common first generator it is congRE. The identity case is
-- Glue3Eqv.reflE.
------------------------------------------------------------------------
module CaTTExp.RCProc.ExchangeSeq where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ctx; tm-ty; subst₂)
open import CaTTExp.GraphFillerTotal using (path; Walk; nil; cons; walk; walk-++; walk-end; endOf)
open import CaTTExp.RCProc.Path1 using (B)
open import CaTTExp.RCProc.Eg using (vcomp)
open import CaTTExp.RCProc.TwoPath using (module TwoPaths; NE; assoc4)
open import CaTTExp.RCProc.TwoPathCtx using (ctxComp2; Var2)
open import CaTTExp.RCProc.TwoPathTerm using (module Term)
open import CaTTExp.RCProc.ExchangeGamma using (module Setup)
open import CaTTExp.RCProc.Glue3Eqv

module Seq (Γ : Ctx) (key : Nat → Nat) (p⁻ p⁺ : Nat → List Nat) where
  open Term Γ key p⁻ p⁺
  open TwoPaths (ctxComp2 Γ key p⁻ p⁺) using (Xch; xch; skip; _~_; done; fwd; bwd; xch-chain; xch-chain⁻)

  private
    just-inj : ∀ {A B : Ty} → just A ≡ just B → A ≡ B
    just-inj refl = refl

    arr-inj₂ : ∀ {A A′ s s′ t t′} → arr A s t ≡ arr A′ s′ t′ → s ≡ s′
    arr-inj₂ refl = refl

    var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
    var-inj refl = refl

    walk-split : ∀ l {r x y} → Walk Γ x (l ++ r) y → Σ Nat λ m → Walk Γ x l m × Walk Γ m r y
    walk-split []      w          = _ , nil , w
    walk-split (e ∷ l) (cons le w) with walk-split l w
    ... | m , w₁ , w₂ = m , cons le w₁ , w₂

    walk-start : ∀ {x x′ p y y′} → NE p → Walk Γ x p y → Walk Γ x′ p y′ → x ≡ x′
    walk-start (d , D , refl) (cons l₁ _) (cons l₂ _) =
      var-inj (arr-inj₂ (just-inj (trans (sym l₁) l₂)))

  module _ (ok : BdOK) {a b} (da : Γ ⊢tm var a ∶ ⋆) where
    private
      wΓ = tm-ctx da
      A  = arr ⋆ (var a) (var b)

      vc : Tm → Tm → Tm → Tm → Tm → Tm
      vc = vcomp A

      -- A walk along the source of a 2-variable runs between its ends.
      seg : ∀ α {v w s t x y} → lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
            Walk Γ x (p⁻ α) y → (x ≡ v) × (y ≡ w)
      seg α {v} {w} {s} lk wp = e₁ , trans (sym (walk-end wp)) (trans (cong (λ z → endOf Γ z (p⁻ α)) e₁) (walk-end ws))
        where
        bd = ok α lk
        ds : Γ ⊢tm s ∶ arr ⋆ (var v) (var w)
        ds with tm-ty (var-wf wΓ lk)
        ... | arr-wf d _ = d
        ws : Walk Γ v (p⁻ α) w
        ws = subst (λ q → Walk Γ v q w) (fst bd) (walk s ds refl)
        e₁ = walk-start (snd (snd bd)) wp ws

      tyB : ∀ {u X Y X′ Y′} → X ≡ X′ → Y ≡ Y′ → Γ ⊢tm u ∶ arr A (B Γ a X) (B Γ a Y) →
            Γ ⊢tm u ∶ arr A (B Γ a X′) (B Γ a Y′)
      tyB refl refl d = d

      -- One exchange step at the front, with no tail.
      base : ∀ l α m β c → Var2 Γ α → Var2 Γ β → Walk Γ a (l ++ p⁻ α ++ m ++ p⁻ β ++ c) b →
             Eqv Γ (arr A (B Γ a (l ++ p⁻ α ++ m ++ p⁻ β ++ c)) (B Γ a ((l ++ p⁺ α ++ m) ++ p⁺ β ++ c)))
                   (term a b (wg l α (m ++ p⁻ β ++ c) ∷ wg (l ++ p⁺ α ++ m) β c ∷ []))
                   (term a b (wg (l ++ p⁻ α ++ m) β c ∷ wg l α (m ++ p⁺ β ++ c) ∷ []))
      base l α m β c (v₁ , w₁ , s₁ , t₁ , lα) (v₂ , w₂ , s₂ , t₂ , lβ) W
        with walk-split l W
      ... | x₁ , wl , W₁ with walk-split (p⁻ α) W₁
      ... | x₂ , wp , W₂ with walk-split m W₂
      ... | x₃ , wm , W₃ with walk-split (p⁻ β) W₃
      ... | x₄ , wq , wc =
        Setup.Main.exchange da
          (subst (Walk Γ a l) (fst (seg α lα wp)) wl) lα
          (subst₂ (λ x y → Walk Γ x m y) (snd (seg α lα wp)) (fst (seg β lβ wq)) wm) lβ
          (subst (λ z → Walk Γ z c b) (snd (seg β lβ wq)) wc)
          key p⁻ p⁺ ok

    -- Typing of one generator along a walk of its source, and the walk
    -- of its target.
    private
      stp : ∀ l α r → Var2 Γ α → Walk Γ a (l ++ p⁻ α ++ r) b →
            (Γ ⊢tm egW a b (wg l α r) ∶ arr A (B Γ a (l ++ p⁻ α ++ r)) (B Γ a (l ++ p⁺ α ++ r))) ×
            Walk Γ a (l ++ p⁺ α ++ r) b
      stp = step-wf ok da

      skipC : ∀ l g r {w′ P w″ Q T} → Var2 Γ g → Walk Γ a (l ++ p⁻ g ++ r) b →
              Chain (l ++ p⁺ g ++ r) (w′ ∷ P) T → Chain (l ++ p⁺ g ++ r) (w″ ∷ Q) T →
              Eqv Γ (arr A (B Γ a (l ++ p⁺ g ++ r)) (B Γ a T)) (term a b (w′ ∷ P)) (term a b (w″ ∷ Q)) →
              Eqv Γ (arr A (B Γ a (l ++ p⁻ g ++ r)) (B Γ a T))
                    (term a b (wg l g r ∷ w′ ∷ P)) (term a b (wg l g r ∷ w″ ∷ Q))
      skipC l g r {w′} {P} {w″} {Q} Gw W ch chQ ih =
        substE (cong (λ X → vc (B Γ a (l ++ p⁻ g ++ r)) (B Γ a (l ++ p⁺ g ++ r)) (B Γ a X) (egW a b (wg l g r)) (term a b (w′ ∷ P)))
                     (sym (tgtL-ok ok {a} {b} da ch)))
               (cong (λ X → vc (B Γ a (l ++ p⁻ g ++ r)) (B Γ a (l ++ p⁺ g ++ r)) (B Γ a X) (egW a b (wg l g r)) (term a b (w″ ∷ Q)))
                     (sym (tgtL-ok ok {a} {b} da chQ)))
               (congRE (fst (stp l g r Gw W)) ih)

    -- One exchange step anywhere.
    xchE : ∀ {S P Q T} → Xch P Q → Chain S P T → Walk Γ a S b →
           Eqv Γ (arr A (B Γ a S) (B Γ a T)) (term a b P) (term a b Q)
    xchE (xch l α m β c {[]}) (cons Gα refl (cons Gβ e₂ nil)) W =
      base l α m β c Gα Gβ W
    xchE {T = T} (xch l α m β c {w₃ ∷ R}) (cons Gα refl (cons Gβ e₂ ch)) W =
      substE3 (cong (λ X → arr A (B Γ a S₀) (B Γ a X)) (tgtL-ok ok {a} {b} da ch)) eL eR
        (symE (assocE dg₁ dg₂ dr) ⊙
         congLE dr (base l α m β c Gα Gβ W) ⊙
         substE (cong (λ Z → vc (B Γ a S₀) (B Γ a T₀) BT Z r) (sym eQ)) refl (assocE dh₁ dh₂ dr))
      where
      S₀ = l ++ p⁻ α ++ m ++ p⁻ β ++ c
      M₀ = l ++ p⁺ α ++ m ++ p⁻ β ++ c
      T₀ = (l ++ p⁺ α ++ m) ++ p⁺ β ++ c
      N₀ = (l ++ p⁻ α ++ m) ++ p⁺ β ++ c
      a₁ : (l ++ p⁻ α ++ m) ++ p⁻ β ++ c ≡ S₀
      a₁ = assoc4 l (p⁻ α) m (p⁻ β ++ c)
      a₂ : N₀ ≡ l ++ p⁻ α ++ m ++ p⁺ β ++ c
      a₂ = assoc4 l (p⁻ α) m (p⁺ β ++ c)
      a₃ : T₀ ≡ l ++ p⁺ α ++ m ++ p⁺ β ++ c
      a₃ = assoc4 l (p⁺ α) m (p⁺ β ++ c)
      BT = B Γ a (tgtL (w₃ ∷ R))
      g₁ = egW a b (wg l α (m ++ p⁻ β ++ c))
      g₂ = egW a b (wg (l ++ p⁺ α ++ m) β c)
      h₁ = egW a b (wg (l ++ p⁻ α ++ m) β c)
      h₂ = egW a b (wg l α (m ++ p⁺ β ++ c))
      r  = term a b (w₃ ∷ R)
      st₁ = stp l α (m ++ p⁻ β ++ c) Gα W
      st₂ = stp (l ++ p⁺ α ++ m) β c Gβ (subst (λ X → Walk Γ a X b) (sym e₂) (snd st₁))
      sq₁ = stp (l ++ p⁻ α ++ m) β c Gβ (subst (λ X → Walk Γ a X b) (sym a₁) W)
      sq₂ = stp l α (m ++ p⁺ β ++ c) Gα (subst (λ X → Walk Γ a X b) a₂ (snd sq₁))
      dg₁ : Γ ⊢tm g₁ ∶ arr A (B Γ a S₀) (B Γ a M₀)
      dg₁ = fst st₁
      dg₂ : Γ ⊢tm g₂ ∶ arr A (B Γ a M₀) (B Γ a T₀)
      dg₂ = tyB e₂ refl (fst st₂)
      dr : Γ ⊢tm r ∶ arr A (B Γ a T₀) BT
      dr = subst (λ X → Γ ⊢tm r ∶ arr A (B Γ a T₀) (B Γ a X)) (sym (tgtL-ok ok {a} {b} da ch)) (term-wf ok da ch (snd st₂))
      dh₁ : Γ ⊢tm h₁ ∶ arr A (B Γ a S₀) (B Γ a N₀)
      dh₁ = tyB a₁ refl (fst sq₁)
      dh₂ : Γ ⊢tm h₂ ∶ arr A (B Γ a N₀) (B Γ a T₀)
      dh₂ = tyB (sym a₂) (sym a₃) (fst sq₂)
      eL : vc (B Γ a S₀) (B Γ a M₀) BT g₁ (vc (B Γ a M₀) (B Γ a T₀) BT g₂ r) ≡
           term a b (wg l α (m ++ p⁻ β ++ c) ∷ wg (l ++ p⁺ α ++ m) β c ∷ w₃ ∷ R)
      eL = cong (λ Z → vc (B Γ a S₀) (B Γ a M₀) BT g₁ (vc (B Γ a Z) (B Γ a T₀) BT g₂ r)) (sym e₂)
      eQ : term a b (wg (l ++ p⁻ α ++ m) β c ∷ wg l α (m ++ p⁺ β ++ c) ∷ []) ≡
           vc (B Γ a S₀) (B Γ a N₀) (B Γ a T₀) h₁ h₂
      eQ = cong₂ (λ X Y → vc (B Γ a X) (B Γ a N₀) (B Γ a Y) h₁ h₂) a₁ (sym a₃)
      eR : vc (B Γ a S₀) (B Γ a N₀) BT h₁ (vc (B Γ a N₀) (B Γ a T₀) BT h₂ r) ≡
           term a b (wg (l ++ p⁻ α ++ m) β c ∷ wg l α (m ++ p⁺ β ++ c) ∷ w₃ ∷ R)
      eR = trans (cong₂ (λ X Y → vc (B Γ a X) (B Γ a N₀) BT h₁ (vc (B Γ a Y) (B Γ a T₀) BT h₂ r)) (sym a₁) a₂)
                 (cong (λ Z → vc (B Γ a ((l ++ p⁻ α ++ m) ++ p⁻ β ++ c)) (B Γ a N₀) BT h₁
                                 (vc (B Γ a (l ++ p⁻ α ++ m ++ p⁺ β ++ c)) (B Γ a Z) BT h₂ r)) a₃)
    xchE (skip (wg l g r) x@(xch _ _ _ _ _)) (cons Gw refl ch) W =
      skipC l g r Gw W ch (xch-chain x ch) (xchE x ch (snd (stp l g r Gw W)))
    xchE (skip (wg l g r) x@(skip _ _)) (cons Gw refl ch) W =
      skipC l g r Gw W ch (xch-chain x ch) (xchE x ch (snd (stp l g r Gw W)))

    -- Exchange-equivalent 2-paths.
    seqE : ∀ {S w P Q T} → (w ∷ P) ~ Q → Chain S (w ∷ P) T → Walk Γ a S b →
           Eqv Γ (arr A (B Γ a S) (B Γ a T)) (term a b (w ∷ P)) (term a b Q)
    seqE done ch W = reflE (term-wf ok da ch W)
    seqE (fwd x@(xch _ _ _ _ _) e) ch W = xchE x ch W ⊙ seqE e (xch-chain x ch) W
    seqE (fwd x@(skip _ _) e) ch W = xchE x ch W ⊙ seqE e (xch-chain x ch) W
    seqE (bwd x@(xch _ _ _ _ _) e) ch W = symE (xchE x (xch-chain⁻ x ch) W) ⊙ seqE e (xch-chain⁻ x ch) W
    seqE (bwd x@(skip _ _) e) ch W = symE (xchE x (xch-chain⁻ x ch) W) ⊙ seqE e (xch-chain⁻ x ch) W
