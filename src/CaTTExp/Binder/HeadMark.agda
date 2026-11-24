------------------------------------------------------------------------
-- A mark judgment with rule (MARK) and one axiom for head occurrences
-- (ledger S27 (e″)):
--
--   (MARK)     a variable has the marks of its entry;
--   (HEAD-inv) an occurrence bnd b y Δ ts is inv when inv? b y.
--
-- The axiom has no premise on the arguments, like (DES) and (DES-inv)
-- of CaTTExp.Gray.MarksB: the occurrence is only well typed when its
-- arguments meet the arity's marks, which the kernel checks. Chapter 6
-- uses it for J2's conclusion that every comparison component
-- uni^y_{Γ,n}[σ] is inv (CaTTExp.Binder.UniMark).
--
-- `headMark` satisfies the hypotheses of renaming and substitution
-- (MarkRen, MarkSub, MarkVar) for every side condition and every
-- choice of inv?: renaming and substitution keep an occurrence's
-- former and selector, and act on variables as for `varMark`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.HeadMark
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (inv? : Signature.B 𝕊 → Nat → Bool)
  where

open Signature 𝕊

isInv : Mark → Bool
isInv minv = true
isInv _    = false

formerInv : Mark → Tm → Bool
formerInv m (bnd b y _ _) = isInv m ∧ inv? b y
formerInv m _             = false

headMark : Ctx → Mark → Tm → Bool
headMark Γ m t = varMark Γ m t ∨ formerInv m t

open import CaTTExp.Binder.SyntaxLemmas K B using (T∧; ∧T)
open import CaTTExp.Binder.TypingWith 𝕊 side headMark
open import CaTTExp.Binder.Rename 𝕊 side headMark
open import CaTTExp.Binder.Subst 𝕊 side headMark

private
  T∨ʳ : ∀ a {b} → T b → T (a ∨ b)
  T∨ʳ true  _ = tt
  T∨ʳ false p = p

  T∨ˡ : ∀ {a} b → T a → T (a ∨ b)
  T∨ˡ {true} b _ = tt

  ∨f : ∀ {a} → T (a ∨ false) → T a
  ∨f {true}  _ = tt
  ∨f {false} ()

  ∈-weak : ∀ n ns ms → T (all (λ m → m ∈M ns) ms) → T (all (λ m → m ∈M (n ∷ ns)) ms)
  ∈-weak n ns []       _ = tt
  ∈-weak n ns (m ∷ ms) p =
    let (a , b) = T∧ {m ∈M ns} p in ∧T (T∨ʳ (m ==M n) a) (∈-weak n ns ms b)

  ∈-self : ∀ ms → T (all (λ m → m ∈M ms) ms)
  ∈-self []       = tt
  ∈-self (m ∷ ms) with m ==M m | ==M-refl m
  ... | true | _ = ∈-weak m ms ms (∈-self ms)

  all-∨ : ∀ (p : Mark → Bool) ms → T (all p ms) → T (all (λ m → p m ∨ false) ms)
  all-∨ p []       _ = tt
  all-∨ p (m ∷ ms) q = let (a , b) = T∧ {p m} q in ∧T (T∨ˡ false a) (all-∨ p ms b)

  all-∈ : ∀ (p : Mark → Bool) ms m → T (all p ms) → T (m ∈M ms) → T (p m)
  all-∈ p (n ∷ ns) m q r with m ==M n in e
  ... | true  rewrite ==M-sound m n (subst T (sym e) tt) = fst (T∧ {p n} q)
  ... | false = all-∈ p ns m (snd (T∧ {p n} q)) r

  sub-len : ∀ {Δ σ Γ} → Δ ⊢sub σ ∶ Γ → lenₛ σ ≡ len Γ
  sub-len (⟨⟩-wf _)    = refl
  sub-len (,-wf s _ _) = cong suc (sub-len s)

  sub-marks : ∀ {Δ σ Γ i A} → Δ ⊢sub σ ∶ Γ → lookup Γ i ≡ just A →
              T (marksOK Δ (marksAt Γ i) (lookupₛ σ i))
  sub-marks {Γ = Γ ▸[ ms ] B} {i} (,-wf {σ} s _ o) eq with i ==ℕ len Γ in e
  ... | true  rewrite trans (==-transport i (sub-len s)) e = o
  ... | false rewrite trans (==-transport i (sub-len s)) e = sub-marks s eq

markVar : MarkVar
markVar {Γ} {i} _ _ = all-∨ (λ m → m ∈M marksAt Γ i) (marksAt Γ i) (∈-self (marksAt Γ i))

markRen : MarkRen
markRen {Γ} {Γ′} {ρ} {var i} {m = m} r (var-wf _ eq) p with _⊢ren_∶_.look r i eq
... | j , ej , _ , mj rewrite ej | mj = p
markRen {t = bnd b y Δ τ} _ _ p = p
markRen {t = bvar _ _}    _ _ ()
markRen {t = coh _ _ _}   _ _ ()
markRen {t = cst _}       _ _ ()

markSub : MarkSub
markSub {Γ} {Δ} {σ} {var i} {m = m} s (var-wf _ eq) p =
  all-∈ (λ n → headMark Δ n (lookupₛ σ i)) (marksAt Γ i) m (sub-marks s eq) (∨f p)
markSub {t = bnd b y Δ τ} _ _ p = p
markSub {t = bvar _ _}    _ _ ()
markSub {t = coh _ _ _}   _ _ ()
markSub {t = cst _}       _ _ ()
