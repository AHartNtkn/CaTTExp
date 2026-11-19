------------------------------------------------------------------------
-- Atoms of an ordered globular basis in closed form (ledger A5, (N3)).
--
-- For a `GData` presentation, the rows of the atom ⟨x⟩ are single
-- generators: at depth d ≤ deg x below the top, ⟨x⟩ is
-- (s^d x, t^d x), and one step further it vanishes. Since Σ D is again
-- a `GData`, this also gives the atoms of the suspension.
------------------------------------------------------------------------
module CaTTExp.Strict.GlobAtoms where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.GlobBasis

-- Iterates.
iter : (Nat → Nat) → Nat → Nat → Nat
iter f zero    x = x
iter f (suc d) x = iter f d (f x)

iter-suc : ∀ f d x → iter f (suc d) x ≡ f (iter f d x)
iter-suc f zero    x = refl
iter-suc f (suc d) x = iter-suc f d (f x)

private
  ∸-suc : ∀ g d → suc d ≤ g → g ∸ suc d ≡ (g ∸ 1) ∸ d
  ∸-suc (suc g) d _ = refl

  ≤-pred∸ : ∀ g d → suc d ≤ g → d ≤ g ∸ 1
  ≤-pred∸ (suc g) d (s≤s l) = l

module GA (D : GData) where
  open GData D
  open GB D
  open Basis basis
  open Atom basis
  private
    module FO = FreeOn D 0

    up : ∀ x → x < N → 1 ≤ gd x → 1 ≤ deg x
    up x xN p = subst (1 ≤_) (sym (gdeg-at x xN)) p

  -- Faces stay in range and lose one degree at each step.
  iter-ok : ∀ f → (∀ x → x < N → 1 ≤ gd x → f x < N) → (∀ x → x < N → 1 ≤ gd x → gd (f x) ≡ gd x ∸ 1) →
            ∀ d x → x < N → d ≤ gd x → (iter f d x < N) × (gd (iter f d x) ≡ gd x ∸ d)
  iter-ok f fN df zero    x xN _ = xN , refl
  iter-ok f fN df (suc d) x xN l =
    let p  = ≤-trans (s≤s z≤n) l
        ih = iter-ok f fN df d (f x) (fN x xN p) (subst (d ≤_) (sym (df x xN p)) (≤-pred∸ (gd x) d l))
    in fst ih , trans (snd ih) (trans (cong (_∸ d) (df x xN p)) (sym (∸-suc (gd x) d l)))

  -- ⟨x⟩ at depth d ≤ deg x is (s^d x, t^d x).
  entK-glob : ∀ d x → x < N → d ≤ gd x → entK x d ≡ (unit (iter s d x) , unit (iter t d x))
  entK-glob zero    x xN _ = refl
  entK-glob (suc d) x xN l =
    trans (FO.claim x xN (up x xN p) d)
      (cong₂ _,_ (cong fst (entK-glob d (s x) (sN x xN p) ls)) (cong snd (entK-glob d (t x) (tN x xN p) lt)))
    where
    p  = ≤-trans (s≤s z≤n) l
    ls = subst (d ≤_) (sym (ds x xN p)) (≤-pred∸ (gd x) d l)
    lt = subst (d ≤_) (sym (dt x xN p)) (≤-pred∸ (gd x) d l)

  private
    lin-unit : ∀ {M m} i → i < m → (vs : Vec (Vec Nat M) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {M} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {M} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    bd0 : ∀ f p → gd p ≡ 0 → bd f p ≡ 0c
    bd0 f p e rewrite e = refl

    ∸c-00 : ∀ {m} → 0c {m} ∸c 0c ≡ 0c
    ∸c-00 {zero}  = refl
    ∸c-00 {suc m} = cong (0 ∷_) ∸c-00

    ∸-self : ∀ n → n ∸ n ≡ 0
    ∸-self zero    = refl
    ∸-self (suc n) = ∸-self n

  -- The boundaries of a point vanish.
  dm-pt : ∀ p → p < N → gd p ≡ 0 → lin (unit p) bminus ≡ 0c
  dm-pt p pN e = trans (lin-unit p pN bminus) (trans (bm-at p pN) (bd0 s p e))
  dp-pt : ∀ p → p < N → gd p ≡ 0 → lin (unit p) bplus ≡ 0c
  dp-pt p pN e = trans (lin-unit p pN bplus) (trans (bp-at p pN) (bd0 t p e))

  -- One step below the bottom, ⟨x⟩ vanishes.
  entK-bot : ∀ x → x < N → entK x (suc (gd x)) ≡ (0c , 0c)
  entK-bot x xN =
    trans (cong step (entK-glob (gd x) x xN (≤-refl _)))
      (cong₂ _,_ (trans (cong₂ _∸c_ (dm-pt _ sN′ sd) (dp-pt _ sN′ sd)) ∸c-00)
                 (trans (cong₂ _∸c_ (dp-pt _ tN′ td) (dm-pt _ tN′ td)) ∸c-00))
    where
    sok = iter-ok s sN ds (gd x) x xN (≤-refl _)
    tok = iter-ok t tN dt (gd x) x xN (≤-refl _)
    sN′ = fst sok
    tN′ = fst tok
    sd = trans (snd sok) (∸-self (gd x))
    td = trans (snd tok) (∸-self (gd x))
