------------------------------------------------------------------------
-- BdOK from Key2Ctx (ledger S20 (i), stage 3c; the strict-image lemma
-- for the boundaries of 2-variables).
--
-- Under the hypothesis of Theorem A (TwoPathCtx.Key2Ctx Γ), every
-- 2-variable α : s ⇒ t of Γ has path s ≡ p⁻ α and path t ≡ p⁺ α, and
-- p⁻ α is nonempty (`key2-bdok`), so TwoPathTerm.term-wf applies with
-- Key2Ctx's own boundary lists.
--
-- Proof. top ⟦ s ⟧ (η Γ) ≈ tups (path s) (StrictPath.top-path) and
-- ≈ tups (p⁻ α) (Key2Ctx.img⁻), so path s and p⁻ α have the same bag
-- (TwoPathCtx.tups-≋). Both are 1-paths (path s is the walk of s;
-- p⁻ α by Key2.bd). Under Key2 two 1-paths with the same nonempty bag
-- start at the same point (`same-start`: their first edges have the
-- least key, keys strictly increasing along a 1-path), and then they
-- are equal (TwoPath.path-unique).
------------------------------------------------------------------------
module CaTTExp.RCProc.Key2Bd where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ty)
open import CaTTExp.Strict.Bag using (_≈_; ≈-trans; ≈-sym)
open import CaTTExp.Strict.Cell using (top)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (⟦_⟧; η)
open import CaTTExp.GraphFillerTotal using (path; Walk; nil; cons; walk)
open import CaTTExp.RCProc.TwoPath
open import CaTTExp.Gray.Cover using (inj₁; inj₂)
open import CaTTExp.Strict.Omega using (_<_; <-irrefl)
open import CaTTExp.RCProc.TwoPathCtx
open import CaTTExp.RCProc.StrictPath using (top-path)
open import CaTTExp.RCProc.TwoPathTerm using (module Term)

module _ {Γ : Ctx} (wΓ : Γ ⊢ctx) (K : Key2Ctx Γ) where
  open Key2Ctx K
  open Comp2 comp2 using (s₀; t₀)
  open TwoPaths comp2
  open Theorem order

  private
    -- A walk of Γ is a 1-path of its 2-computad.
    toPath1 : ∀ {x p y} → Walk Γ x p y → Path1 x p y
    toPath1 nil = nil
    toPath1 (cons {x = x} {z = z} {e = e} le w) =
      cons (x , z , le) (src₀-ok Γ e le) (subst (λ m → Path1 m _ _) (sym (tgt₀-ok Γ e le)) (toPath1 w))

    z≢s : ∀ {k} → 0 ≡ suc k → ⊥
    z≢s ()

    -- Two 1-paths with the same nonempty bag start at the same point.
    same-start : ∀ {x x′ y y′ p q} → Path1 x p y → Path1 x′ q y′ → p ≋ q → NE q → x ≡ x′
    same-start {q = Q} nil _ b (f , F , refl) with cnt-∈ {f} {Q} here
    ... | k , e = ⊥-elim (z≢s (trans (at≋ b f) e))
    same-start (cons {e = e} ee s₁ p) (cons {e = f} ef s₂ q) b _ with dec≡ e f
    ... | inj₁ refl = trans (sym s₁) s₂
    ... | inj₂ ne = ⊥-elim (<-irrefl (<-trans kef kfe))
      where
      e∈q : e ∈ _
      e∈q = ∈-tail (λ z → ne (sym z)) (≋-∈ b here)
      f∈p : f ∈ _
      f∈p = ∈-tail ne (≋-∈ (≋-sym b) here)
      kfe : key f < key e
      kfe = <-trans (snd (Key2.k₁ order f ef)) (path-gt q e∈q)
      kef : key e < key f
      kef = <-trans (snd (Key2.k₁ order e ee)) (path-gt p f∈p)

    -- A boundary s : v → w of a 2-variable, with bag p, is p.
    bd-path : ∀ {v w a b s P} → Γ ⊢tm s ∶ arr ⋆ (var v) (var w) →
              top (⟦ s ⟧ (η Γ)) ≈ tups P →
              Path1 a P b → NE P → path s ≡ P
    bd-path {P = P} ds img pa ne =
      path-unique pS (subst (λ z → Path1 z P _) (sym st) pa) bag
      where
      pS  = toPath1 (walk _ ds refl)
      bag = tups-≋ _ P (≈-trans (≈-sym (top-path ds refl)) img)
      st  = same-start pS pa bag ne

  key2-bdok : Term.BdOK Γ key p⁻ p⁺
  key2-bdok α {v} {w} {s} {t} lk with tm-ty (var-wf wΓ lk) | Key2.bd order α Gα
    where Gα = v , w , s , t , lk
  ... | arr-wf ds dt | a , b , pa , qa , lt =
    bd-path ds (img⁻ α lk) pa (ne⁻ Gα) , bd-path dt (img⁺ α lk) qa (ne⁺ Gα) , ne⁻ Gα
    where Gα = v , w , s , t , lk
