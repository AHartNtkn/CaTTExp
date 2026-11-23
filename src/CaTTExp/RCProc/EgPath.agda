------------------------------------------------------------------------
-- The paths of the two sides of H_g[θ_g] (ledger S20 (i), stage 3c).
--
-- On the chain tree with leaf m raised, the inclusions incl∓ are
-- explicit: pairs (var L, var (L+1)) for the plain leaves and
-- (var L, var (L+j)) at leaf m (j = 1 for incl⁻, j = 2 for incl⁺;
-- `inclM-flag`, `inclP-flag`). So the path of c∓[θ] is read off θ
-- (`path-c∓`), and for θ = θ_g it is λ ++ path s ++ ρ, resp.
-- λ ++ path t ++ ρ (`path-c⁻θg`, `path-c⁺θg`).
------------------------------------------------------------------------
module CaTTExp.RCProc.EgPath where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Derived using (++-assoc; ps-wf)
open import CaTTExp.DerivedBoundary using (idS∘)
open import CaTTExp.GraphFillerTotal using (path; pathCh)
open import CaTTExp.PsRaise using (Sim; half; simL; pseS; psdS; leafR; incl; inclM; inclP; inclM-wf; inclP-wf)
open import CaTTExp.RCProc.Column using (leaves; falses; flagAt)
open import CaTTExp.RCProc.Edges using (bd; edgesAt; ++-[])

pairsOn : Sub → Nat → Nat → Sub
pairsOn σ L zero    = σ
pairsOn σ L (suc k) = pairsOn (σ ,ₛ var L ,ₛ var (suc L)) (suc (suc L)) k

-- m plain leaves, the raised leaf (its edge read at L + j), k plain leaves.
flag : Nat → Sub → Nat → Nat → Nat → Sub
flag j σ L zero    k = pairsOn (σ ,ₛ var L ,ₛ var (j + L)) (suc (suc (suc (suc L)))) k
flag j σ L (suc m) k = flag j (σ ,ₛ var L ,ₛ var (suc L)) (suc (suc L)) m k

simL-leaves : ∀ k {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) S →
              (fst (simL (leaves k) [] d d^ S) ≡ pairsOn (fst S) (len Δ) k) ×
              (fst (snd (simL (leaves k) [] d d^ S)) ≡ pairsOn (fst (snd S)) (len Δ) k)
simL-leaves zero    d d^ S = refl , refl
simL-leaves (suc k) d d^ S = simL-leaves k (psd (pse d)) (psd (pse d^)) (psdS (pseS d d^ S))

simL-flag : ∀ m k {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) S →
            (fst (simL (leaves (suc (m + k))) (flagAt m) d d^ S) ≡ flag 1 (fst S) (len Δ) m k) ×
            (fst (snd (simL (leaves (suc (m + k))) (flagAt m) d d^ S)) ≡ flag 2 (fst (snd S)) (len Δ) m k)
simL-flag zero    k d d^ S = simL-leaves k (psd (pse d)) (psd (psd (pse (pse d^)))) (leafR d d^ S)
simL-flag (suc m) k d d^ S = simL-flag m k (psd (pse d)) (psd (pse d^)) (psdS (pseS d d^ S))

private
  σ₀ : Sub
  σ₀ = ⟨⟩ ,ₛ var 0

  -- The starting state of `incl` (PsRaise's private `base`, verbatim).
  base : Sim (ε ▸ ⋆) 0 ⋆ (ε ▸ ⋆) 0 ⋆
  base = s , s , h , h
    where
    s = ⟨⟩ ,ₛ var 0
    w = fst (ps-wf pss)
    h = half (,-wf (⟨⟩-wf w) (var-wf w refl)) refl refl

inclM-flag : ∀ m n → inclM (flagAt m) (node []) (leaves (m + n)) ≡ flag 1 σ₀ 1 m n
inclM-flag zero    n = fst (simL-flag zero n pss pss base)
inclM-flag (suc m) n = fst (simL-flag (suc m) n pss pss base)

inclP-flag : ∀ m n → inclP (flagAt m) (node []) (leaves (m + n)) ≡ flag 2 σ₀ 1 m n
inclP-flag zero    n = snd (simL-flag zero n pss pss base)
inclP-flag (suc m) n = snd (simL-flag (suc m) n pss pss base)

------------------------------------------------------------------------
-- Paths of the composites.

pathCh-pairs : ∀ σ a L k θ → pathCh (pairsOn (σ ,ₛ a) L k ∘ θ) ≡ pathCh ((σ ,ₛ a) ∘ θ) ++ edgesAt θ L k
pathCh-pairs σ a L zero    θ = sym (++-[] _)
pathCh-pairs σ a L (suc k) θ =
  trans (pathCh-pairs (σ ,ₛ a ,ₛ var L) (var (suc L)) (suc (suc L)) k θ)
        (++-assoc (pathCh ((σ ,ₛ a) ∘ θ)) (path (lookupₛ θ (suc L))) (edgesAt θ (suc (suc L)) k))

pathCh-flag : ∀ j σ a L m k θ →
              pathCh (flag j (σ ,ₛ a) L m k ∘ θ)
                ≡ pathCh ((σ ,ₛ a) ∘ θ) ++ (edgesAt θ L m ++ (path (lookupₛ θ (j + bd L m)) ++ edgesAt θ (suc (suc (suc (suc (bd L m))))) k))
pathCh-flag j σ a L zero    k θ =
  trans (pathCh-pairs (σ ,ₛ a ,ₛ var L) (var (j + L)) (suc (suc (suc (suc L)))) k θ)
        (++-assoc (pathCh ((σ ,ₛ a) ∘ θ)) (path (lookupₛ θ (j + L))) _)
pathCh-flag j σ a L (suc m) k θ =
  trans (pathCh-flag j (σ ,ₛ a ,ₛ var L) (var (suc L)) (suc (suc L)) m k θ)
        (trans (++-assoc (pathCh ((σ ,ₛ a) ∘ θ)) (path (lookupₛ θ (suc L))) _)
               (cong (pathCh ((σ ,ₛ a) ∘ θ) ++_)
                     (sym (++-assoc (path (lookupₛ θ (suc L))) (edgesAt θ (suc (suc L)) m) _))))

------------------------------------------------------------------------
-- The paths of c∓[θ].

open import CaTTExp.PsRaiseCongr using (c⁻; c⁺)
open import CaTTExp.Derived using (idS)

private
  idS-incl : ∀ (ρ : Sub) n → lenₛ ρ ≡ n → idS n ∘ ρ ≡ ρ
  idS-incl ρ .(lenₛ ρ) refl = idS∘ ρ ρ (λ _ _ → refl)

module _ (m n : Nat) (B : Ty) (s u : Tm) (θ : Sub) where
  private
    bs = flagAt m
    ts = leaves (m + n)
    nP = len (ctxOf (node (node [] ∷ ts)))

  path-c⁻ : path (c⁻ bs (node []) ts B s u [ θ ]tm)
              ≡ edgesAt θ 1 m ++ (path (lookupₛ θ (suc (bd 1 m))) ++ edgesAt θ (suc (suc (suc (suc (bd 1 m))))) n)
  path-c⁻ =
    trans (cong (λ X → pathCh (X ∘ θ))
                (trans (idS-incl (inclM bs (node []) ts) nP (snd (Sb.sub-sc closed (inclM-wf bs (node []) ts))))
                       (inclM-flag m n)))
          (pathCh-flag 1 ⟨⟩ (var 0) 1 m n θ)

  path-c⁺ : path (c⁺ bs (node []) ts B s u [ θ ]tm)
              ≡ edgesAt θ 1 m ++ (path (lookupₛ θ (suc (suc (bd 1 m)))) ++ edgesAt θ (suc (suc (suc (suc (bd 1 m))))) n)
  path-c⁺ =
    trans (cong (λ X → pathCh (X ∘ θ))
                (trans (idS-incl (inclP bs (node []) ts) nP (snd (Sb.sub-sc closed (inclP-wf bs (node []) ts))))
                       (inclP-flag m n)))
          (pathCh-flag 2 ⟨⟩ (var 0) 1 m n θ)
