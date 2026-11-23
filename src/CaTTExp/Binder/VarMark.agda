------------------------------------------------------------------------
-- The mark judgment with rule (MARK) only (`varMark`, a variable has
-- the marks of its entry) satisfies the hypotheses of renaming and
-- substitution (MarkRen, MarkSub, MarkVar), for every side condition.
-- It is the mark judgment of CaTTExp.Binder.Typing.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.VarMark
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B using (T∧; ∧T)
open import CaTTExp.Binder.TypingWith 𝕊 side varMark
open import CaTTExp.Binder.Rename 𝕊 side varMark
open import CaTTExp.Binder.Subst 𝕊 side varMark

private
  T∨ʳ : ∀ a {b} → T b → T (a ∨ b)
  T∨ʳ true  _ = tt
  T∨ʳ false p = p

  -- Every mark of ms is in n ∷ ns if it is in ns.
  ∈-weak : ∀ n ns ms → T (all (λ m → m ∈M ns) ms) → T (all (λ m → m ∈M (n ∷ ns)) ms)
  ∈-weak n ns []       _ = tt
  ∈-weak n ns (m ∷ ms) p =
    let (a , b) = T∧ {m ∈M ns} p in ∧T (T∨ʳ (m ==M n) a) (∈-weak n ns ms b)

  ∈-self : ∀ ms → T (all (λ m → m ∈M ms) ms)
  ∈-self []       = tt
  ∈-self (m ∷ ms) with m ==M m | ==M-refl m
  ... | true | _ = ∈-weak m ms ms (∈-self ms)

  -- A property of all of ms holds of each member.
  all-∈ : ∀ (p : Mark → Bool) ms m → T (all p ms) → T (m ∈M ms) → T (p m)
  all-∈ p (n ∷ ns) m q r with m ==M n in e
  ... | true  rewrite ==M-sound m n (subst T (sym e) tt) = fst (T∧ {p n} q)
  ... | false = all-∈ p ns m (snd (T∧ {p n} q)) r

  sub-len : ∀ {Δ σ Γ} → Δ ⊢sub σ ∶ Γ → lenₛ σ ≡ len Γ
  sub-len (⟨⟩-wf _)    = refl
  sub-len (,-wf s _ _) = cong suc (sub-len s)

  -- A substitution sends a variable to a term with its marks.
  sub-marks : ∀ {Δ σ Γ i A} → Δ ⊢sub σ ∶ Γ → lookup Γ i ≡ just A →
              T (marksOK Δ (marksAt Γ i) (lookupₛ σ i))
  sub-marks {Γ = Γ ▸[ ms ] B} {i} (,-wf {σ} s _ o) eq with i ==ℕ len Γ in e
  ... | true  rewrite trans (==-transport i (sub-len s)) e = o
  ... | false rewrite trans (==-transport i (sub-len s)) e = sub-marks s eq

markVar : MarkVar
markVar {Γ} {i} _ _ = ∈-self (marksAt Γ i)

markRen : MarkRen
markRen {Γ} {Γ′} {ρ} {var i} {m = m} r (var-wf _ eq) p with _⊢ren_∶_.look r i eq
... | j , ej , _ , mj rewrite ej | mj = p

markSub : MarkSub
markSub {Γ} {Δ} {σ} {var i} {m = m} s (var-wf _ eq) p =
  all-∈ (λ n → varMark Δ n (lookupₛ σ i)) (marksAt Γ i) m (sub-marks s eq) p
