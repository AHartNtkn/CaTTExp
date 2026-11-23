------------------------------------------------------------------------
-- Substitution facts for Lemma E part (2) (ledger S20 (i), stage 3e).
--
--   wgo-app      : a walk substitution after σ is σ with the walk's
--                  chain substitution appended (ColSub.appCh);
--   pathCh-wgo∘  : the path of (walk substitution) ∘ θ reads the paths
--                  of θ at the walk's edges (`pmap`);
--   pmap-chEdges : at the edges of a chain block this is Edges.edgesAt.
------------------------------------------------------------------------
module CaTTExp.RCProc.ExchangeSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal using (path; pathCh; wgo; wsub; tgtOf)
open import CaTTExp.RCProc.ColSub using (appCh)
open import CaTTExp.RCProc.Edges using (edgesAt; ++-[])
open import CaTTExp.RCProc.Exchange using (chEdges; ++-assoc)

appCh-snoc2 : ∀ σ x a b τ → appCh σ (appCh (⟨⟩ ,ₛ x ,ₛ a ,ₛ b) τ) ≡ appCh (σ ,ₛ a ,ₛ b) τ
appCh-snoc2 σ x a b ⟨⟩            = refl
appCh-snoc2 σ x a b (⟨⟩ ,ₛ _)     = refl
appCh-snoc2 σ x a b (τ ,ₛ c ,ₛ d) = cong (λ X → X ,ₛ c ,ₛ d) (appCh-snoc2 σ x a b τ)

wgo-app : ∀ Γ σ x p → wgo Γ σ x p ≡ appCh σ (wsub Γ x p)
wgo-app Γ σ x []      = refl
wgo-app Γ σ x (e ∷ p) =
  trans (wgo-app Γ (σ ,ₛ var v ,ₛ var e) v p)
        (trans (sym (appCh-snoc2 σ (var x) (var v) (var e) (wsub Γ v p)))
               (cong (appCh σ) (sym (wgo-app Γ (⟨⟩ ,ₛ var x ,ₛ var v ,ₛ var e) v p))))
  where v = tgtOf Γ e

-- The paths of θ at a list of positions.
pmap : Sub → List Nat → List Nat
pmap θ []      = []
pmap θ (e ∷ p) = path (lookupₛ θ e) ++ pmap θ p

pmap-++ : ∀ θ p q → pmap θ (p ++ q) ≡ pmap θ p ++ pmap θ q
pmap-++ θ []      q = refl
pmap-++ θ (e ∷ p) q = trans (cong (path (lookupₛ θ e) ++_) (pmap-++ θ p q))
                            (sym (++-assoc (path (lookupₛ θ e)) (pmap θ p) (pmap θ q)))

pmap-chEdges : ∀ θ L k → pmap θ (chEdges L k) ≡ edgesAt θ L k
pmap-chEdges θ L zero    = refl
pmap-chEdges θ L (suc k) = cong (path (lookupₛ θ (suc L)) ++_) (pmap-chEdges θ (suc (suc L)) k)

pathCh-wgo∘ : ∀ Γ σ x p θ → pathCh (wgo Γ σ x p ∘ θ) ≡ pathCh (σ ∘ θ) ++ pmap θ p
pathCh-wgo∘ Γ σ x []      θ = sym (++-[] (pathCh (σ ∘ θ)))
pathCh-wgo∘ Γ σ x (e ∷ p) θ =
  trans (pathCh-wgo∘ Γ (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p θ)
        (++-assoc (pathCh (σ ∘ θ)) (path (lookupₛ θ e)) (pmap θ p))
