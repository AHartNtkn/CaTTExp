------------------------------------------------------------------------
-- The degree-4 grid layer as an instance of Present (ledger S3a).
--
-- Grid.agda builds the 4-cells of F_{V+S} on a suspended m × n grid
-- by hand: valid raw paths, split steps, the charge universe, first
-- word of each component. Present.agda proves that construction
-- correct for any presentation. This module checks that the grid is
-- such a presentation, with carrier the valid raw paths, and that the
-- generic equality is exactly Grid's: equiv-to and equiv-from.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import CaTTExp.Join.SwitchLaws using (Switches)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Grid
open import CaTTExp.Uniform.Present

module CaTTExp.Uniform.GridPresent (m n : Nat) where

open OnGrid m n

V : Set
V = Σ RawPath Valid

private
  uip : ∀ {B : Set} {x y : B} (a b : x ≡ y) → a ≡ b
  uip refl refl = refl

  valid-irr : ∀ {p} (a b : Valid p) → a ≡ b
  valid-irr = uip

  v-≡ : ∀ {p} {a b : Valid p} → _≡_ {A = V} (p , a) (p , b)
  v-≡ {p} {a} {b} = cong (p ,_) (valid-irr {p} a b)

_≟V_ : (x y : V) → Dec (x ≡ y)
(p , a) ≟V (q , b) with p ≟P q
... | yes refl = yes v-≡
... | no ne    = no λ e → ne (cong fst e)

-- Lists of valid paths, carrying their proofs.
lift : (xs : List RawPath) → (∀ {q} → q ∈L xs → Valid q) → List V
lift []       h = []
lift (q ∷ qs) h = (q , h here) ∷ lift qs (λ k → h (there k))

lift⁻ : ∀ xs (h : ∀ {q} → q ∈L xs → Valid q) {v} → v ∈L lift xs h → fst v ∈L xs
lift⁻ (q ∷ qs) h here      = here
lift⁻ (q ∷ qs) h (there k) = there (lift⁻ qs (λ k′ → h (there k′)) k)

lift⁺ : ∀ xs (h : ∀ {q} → q ∈L xs → Valid q) {q} (vq : Valid q) → q ∈L xs → (q , vq) ∈L lift xs h
lift⁺ (q ∷ qs) h vq here      = subst (λ v → v ∈L lift (q ∷ qs) h) (v-≡ {q} {h here} {vq}) here
lift⁺ (q ∷ qs) h vq (there k) = there (lift⁺ qs (λ k′ → h (there k′)) vq k)

private
  Uc-valid : ∀ c {q} → q ∈L Uc c → Valid q
  Uc-valid c k = allPaths-sound c start end (fst (∈-filter⁻ _ (allPaths c start end) k))

Uv : Nat → List V
Uv c = lift (Uc c) (Uc-valid c)

presentation : Switches → Presentation V
presentation sw = record
  { _≟_      = _≟V_
  ; Step     = λ x y → Step sw (fst x) (fst y)
  ; nb       = nbV
  ; nb-sound = λ {x} k → snd (snd (nb-sound sw (fst x) (lift⁻ _ _ k)))
  ; nb-fwd   = λ {x} {y} s → lift⁺ _ _ (snd y) (nb-fwd (snd x) (snd y) s)
  ; nb-bwd   = λ {x} {y} s → lift⁺ _ _ (snd y) (nb-bwd (snd x) (snd y) s)
  ; U        = λ x → Uv (charge (fst x))
  ; U-has    = λ x → lift⁺ _ _ (snd x) (U-has (snd x))
  ; U-closed = λ {x} {y} {z} k k′ →
      lift⁺ _ _ (snd z) (Setting.U-closed sw {fst x} {fst y} {fst z} (lift⁻ _ _ k) (lift⁻ _ _ k′))
  ; U-step   = λ s → cong Uv (sym (step-charge s))
  }
  where
  nbV : V → List V
  nbV (p , _) = lift (nb sw p) (λ k → fst (snd (nb-sound sw p k)))

module _ (sw : Switches) where
  module P = Present (presentation sw)

  -- The generic equality is Grid's equality on valid paths.
  equiv-to : ∀ {x y} → x P.≈ y → sw ⊢ fst x ≈ fst y
  equiv-to P.≈-refl        = ≈-refl
  equiv-to {x} {y} (P.≈-step s) = ≈-step (snd x) (snd y) s
  equiv-to (P.≈-sym d)     = ≈-sym (equiv-to d)
  equiv-to (P.≈-trans d e) = ≈-trans (equiv-to d) (equiv-to e)

  equiv-from : ∀ {p q} (vp : Valid p) (vq : Valid q) → sw ⊢ p ≈ q → (p , vp) P.≈ (q , vq)
  equiv-from {p} vp vq ≈-refl = subst (λ v → (p , vp) P.≈ v) (v-≡ {p} {vp} {vq}) P.≈-refl
  equiv-from vp vq (≈-step _ _ s) = P.≈-step s
  equiv-from vp vq (≈-sym d) = P.≈-sym (equiv-from vq vp d)
  equiv-from vp vq (≈-trans {q = r} d e) =
    P.≈-trans (equiv-from vp vr d) (equiv-from vr vq e)
    where vr = fst (≈-valid d) vp

  -- The generic normal form is Grid's: both take the first path of the
  -- charge universe connected to the input.
  private
    module G = Setting sw

    bool-ext : ∀ {a b} → (T a → T b) → (T b → T a) → a ≡ b
    bool-ext {true}  {true}  f g = refl
    bool-ext {false} {false} f g = refl
    bool-ext {true}  {false} f g = ⊥-elim (f tt)
    bool-ext {false} {true}  f g = ⊥-elim (g tt)

    conn-same : ∀ {p} (vp : Valid p) {q} (vq : Valid q) → P.conn (p , vp) (q , vq) ≡ G.conn p q
    conn-same vp vq = bool-ext
      (λ t → G.conn-complete vp (equiv-to (P.conn-sound _ _ t)))
      (λ t → P.conn-complete (equiv-from vp vq (G.conn-sound _ _ t)))

    head-lift : ∀ (f : V → Bool) (g : RawPath → Bool) (d : V) xs (h : ∀ {q} → q ∈L xs → Valid q) →
      (∀ {q} (k : q ∈L xs) → f (q , h k) ≡ g q) →
      fst (P.headOr d (filter f (lift xs h))) ≡ G.headOr (fst d) (filter g xs)
    head-lift f g d []       h fg = refl
    head-lift f g d (q ∷ qs) h fg with f (q , h here) | g q | fg here
    ... | true  | true  | refl = refl
    ... | false | false | refl = head-lift f g d qs (λ k → h (there k)) (λ k → fg (there k))

  nf-agree : ∀ {p} (vp : Valid p) → fst (P.nf (p , vp)) ≡ G.nf p
  nf-agree {p} vp =
    head-lift (P.conn (p , vp)) (G.conn p) (p , vp) (Uc (charge p)) (Uc-valid (charge p))
      (λ k → conn-same vp (Uc-valid (charge p) k))
