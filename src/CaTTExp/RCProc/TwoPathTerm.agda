------------------------------------------------------------------------
-- The term of a 2-path (ledger S20 (i), stage 3c; notes/
-- relative-coherence.md §2 Step 3).
--
-- Over a context Γ with boundary lists p⁻ α, p⁺ α for its 2-variables
-- (the data of RCProc.TwoPathCtx), a whiskered generator wg l α r,
-- with α : s ⇒ t over v → w, gives the cell (RCProc.Eg)
--
--   egW (wg l α r) : B Γ a (l ++ p⁻ α ++ r) ⇒ B Γ a (l ++ p⁺ α ++ r)
--
-- and a nonempty 2-path P = w₁ … wₙ gives the vertical composite
--
--   term a b P = egW w₁ ∗₁ (egW w₂ ∗₁ (… ∗₁ egW wₙ)) : B Γ a S ⇒ B Γ a T.
--
-- `term` is computed from Γ, p∓ and the 2-path alone. `term-wf` types
-- it for every chain S —P→ T (TwoPath.Chain) whose source S is a walk
-- a ⇝ b in Γ, when each 2-variable's boundaries have paths p∓ α and
-- p⁻ α is nonempty (`BdOK`).
------------------------------------------------------------------------
module CaTTExp.RCProc.TwoPathTerm where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ctx)
open import CaTTExp.GraphFillerTotal using (path; Walk; nil; cons; walk; walk-++; walk-end; endOf)
open import CaTTExp.RCProc.Glue using (Ans; transA)
open import CaTTExp.RCProc.Path1 using (B)
open import CaTTExp.RCProc.Eg using (eg; eg-wf; vcomp)
open import CaTTExp.RCProc.TwoPath using (Comp2; module TwoPaths; NE)
open import CaTTExp.RCProc.TwoPathCtx using (ctxComp2; Var2)

-- The data of a 2-variable's type: s ⇒ t over v → w.
private
  g-w : Maybe Ty → Nat
  g-w (just (arr (arr ⋆ _ (var w)) _ _)) = w
  g-w _                                  = 0

  g-s g-t : Maybe Ty → Tm
  g-s (just (arr _ s _)) = s
  g-s _                  = var 0
  g-t (just (arr _ _ t)) = t
  g-t _                  = var 0

module Term (Γ : Ctx) (key : Nat → Nat) (p⁻ p⁺ : Nat → List Nat) where
  open TwoPaths (ctxComp2 Γ key p⁻ p⁺) public using (WG; wg; src1; tgt1; Chain; nil; cons)

  egW : Nat → Nat → WG → Tm
  egW a b (wg l α r) =
    eg Γ a l (g-w (lookup Γ α)) (g-s (lookup Γ α)) (g-t (lookup Γ α)) α r b (p⁻ α) (p⁺ α)

  -- The target 1-path of a nonempty 2-path.
  tgtL : List WG → List Nat
  tgtL []           = []
  tgtL (w ∷ [])     = tgt1 w
  tgtL (w ∷ w′ ∷ P) = tgtL (w′ ∷ P)

  term : Nat → Nat → List WG → Tm
  term a b []           = var a      -- the empty 2-path: unused
  term a b (w ∷ [])     = egW a b w
  term a b (w ∷ w′ ∷ P) =
    vcomp (arr ⋆ (var a) (var b)) (B Γ a (src1 w)) (B Γ a (tgt1 w)) (B Γ a (tgtL (w′ ∷ P)))
          (egW a b w) (term a b (w′ ∷ P))

  ----------------------------------------------------------------------
  -- Typing.

  -- Each 2-variable's boundaries have the paths p∓ α, and p⁻ α is
  -- nonempty.
  BdOK : Set
  BdOK = ∀ α {v w s t} → lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
         (path s ≡ p⁻ α) × (path t ≡ p⁺ α) × NE (p⁻ α)

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

    -- Two walks along the same nonempty path start at the same point.
    walk-start : ∀ {x x′ p y y′} → NE p → Walk Γ x p y → Walk Γ x′ p y′ → x ≡ x′
    walk-start (d , D , refl) (cons l₁ _) (cons l₂ _) =
      var-inj (arr-inj₂ (just-inj (trans (sym l₁) l₂)))

    egW-eq : ∀ a b l α r {v w s t} → lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
             egW a b (wg l α r) ≡ eg Γ a l w s t α r b (p⁻ α) (p⁺ α)
    egW-eq a b l α r e rewrite e = refl

  module _ (ok : BdOK) {a b} (da : Γ ⊢tm var a ∶ ⋆) where
    private
      wΓ = tm-ctx da
      A  = arr ⋆ (var a) (var b)

      -- One step: the typed cell of a whiskered generator, and the
      -- walk of its target.
      step : ∀ l α r → Var2 Γ α → Walk Γ a (l ++ p⁻ α ++ r) b →
             (Γ ⊢tm egW a b (wg l α r) ∶ arr A (B Γ a (l ++ p⁻ α ++ r)) (B Γ a (l ++ p⁺ α ++ r))) ×
             Walk Γ a (l ++ p⁺ α ++ r) b
      step l α r (v , w , s , t , lk) W with walk-split l W
      ... | m₁ , wl , W′ with walk-split (p⁻ α) W′
      ... | m₂ , wp , wr =
        subst (λ X → Γ ⊢tm X ∶ arr A (B Γ a (l ++ p⁻ α ++ r)) (B Γ a (l ++ p⁺ α ++ r))) (sym (egW-eq a b l α r lk))
              (eg-wf da wλ dx wρ ps₁ pt₁) ,
        walk-++ wλ (walk-++ (subst (λ q → Walk Γ v q w) pt₁ (walk t (snd tys) refl)) wρ)
        where
        bd = ok α lk
        ps₁ = fst bd
        pt₁ = fst (snd bd)
        dx : Γ ⊢tm var α ∶ arr (arr ⋆ (var v) (var w)) s t
        dx = var-wf wΓ lk
        tys : Σ (Γ ⊢tm s ∶ arr ⋆ (var v) (var w)) λ _ → Γ ⊢tm t ∶ arr ⋆ (var v) (var w)
        tys with CaTTExp.Derived.tm-ty dx
        ... | arr-wf d₁ d₂ = d₁ , d₂
        ws : Walk Γ v (p⁻ α) w
        ws = subst (λ q → Walk Γ v q w) ps₁ (walk s (fst tys) refl)
        e₁ : m₁ ≡ v
        e₁ = walk-start (snd (snd bd)) wp ws
        e₂ : m₂ ≡ w
        e₂ = trans (sym (walk-end wp)) (trans (cong (λ z → endOf Γ z (p⁻ α)) e₁) (walk-end ws))
        wλ : Walk Γ a l v
        wλ = subst (Walk Γ a l) e₁ wl
        wρ : Walk Γ w r b
        wρ = subst (λ z → Walk Γ z r b) e₂ wr

    tgtL-ok : ∀ {S w P T} → Chain S (w ∷ P) T → tgtL (w ∷ P) ≡ T
    tgtL-ok (cons _ _ nil)            = refl
    tgtL-ok (cons _ _ (cons g e ch))  = tgtL-ok (cons g e ch)

    term-wf : ∀ {S w P T} → Chain S (w ∷ P) T → Walk Γ a S b →
              Γ ⊢tm term a b (w ∷ P) ∶ arr A (B Γ a S) (B Γ a T)
    term-wf {S} {wg l α r} {[]} (cons Gα refl nil) W = fst (step l α r Gα W)
    term-wf {S} {wg l α r} {w′ ∷ P} {T} (cons Gα refl ch) W =
      subst (λ X → Γ ⊢tm vcomp A (B Γ a S) (B Γ a T₁) (B Γ a X) (egW a b (wg l α r)) (term a b (w′ ∷ P))
                         ∶ arr A (B Γ a S) (B Γ a T))
            (sym (tgtL-ok ch))
            (snd (transA (egW a b (wg l α r) , fst st) (term a b (w′ ∷ P) , term-wf ch (snd st))))
      where
      T₁ = l ++ p⁺ α ++ r
      st = step l α r Gα W
