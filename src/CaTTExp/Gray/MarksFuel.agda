------------------------------------------------------------------------
-- Fuel for the mark judgments (CaTTExp.Gray.Marks).
--
-- `judge n` takes fuel n for the descent into boundaries that (PS*)
-- needs. Two facts:
--
--   fuel-mono   : judge n ≤ judge (suc n), for every input (each of
--                 inv, ps, ps* only becomes true with more fuel);
--   fuel-stable : for a derivable Γ ⊢ t : A, judge n t ≡ judge (dim A) t
--                 for every n ≥ dim A, so `judgeT` (fuel = dim t) is the
--                 limit, and substitution preserves the user-facing
--                 judgments without a fuel shift (`inv-[]ᵀ`, `ps-[]ᵀ`,
--                 `ps*-[]ᵀ`).
--
-- fuel-stable uses that a derivable coh is at least as high as its
-- pasting context: dim Θ ≤ dim (t →_A u) (`DimOK`, a module
-- parameter: true for L, not yet proved here), and that the signature's constants have
-- well-formed types (`SigOK`; trivial for pure L).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.MarksFuel (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Typing 𝕊
open import CaTTExp.Gray.Marks 𝕊
open import CaTTExp.Gray.MarksSubst 𝕊
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s; ≤-refl; ≤-trans; ≤-step)
import CaTTExp.Subst 𝕊 graySide as S

private
  id⇒ : ∀ {a} → a ⇒B a
  id⇒ p = p

  ∨-m : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∨ b) ⇒B (c ∨ d)
  ∨-m {true}  {c = true}  f g p = tt
  ∨-m {true}  {c = false} f g p = ⊥-elim (f tt)
  ∨-m {false} {c = true}  f g p = tt
  ∨-m {false} {c = false} f g p = g p

  ∧-m : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∧ b) ⇒B (c ∧ d)
  ∧-m {true} {c = true}  f g p = g p
  ∧-m {true} {c = false} f g p = ⊥-elim (f tt)
  ∧-m {false} f g ()

  pw-snoc : ∀ {xs ys x y} → Pw IP≤ xs ys → IP≤ x y → Pw IP≤ (xs ++ (x ∷ [])) (ys ++ (y ∷ []))
  pw-snoc []       q = q ∷ []
  pw-snoc (r ∷ rs) q = r ∷ pw-snoc rs q

------------------------------------------------------------------------
-- Monotonicity in the fuel.

mutual
  fuel-mono : ∀ n ms Γ t → IP≤ (judge n ms Γ t) (judge (suc n) ms Γ t)
  fuel-mono n ms Γ (var x) = id⇒ , id⇒ , star-mono n ms Γ (lookup Γ x) id⇒
  fuel-mono n ms Γ (cst k) = id⇒ , id⇒ , star-mono n ms Γ (just (ty k)) id⇒
  fuel-mono n ms Γ (coh Θ ⋆ γ) = id⇒ , id⇒ , id⇒
  fuel-mono n ms Γ (coh Θ (arr A t u) γ) = i⇒ , p⇒ , star-mono n ms Γ (just (arr A t u [ γ ]ty)) p⇒
    where
    cm = sub-mono n ms Γ γ
    ty' = just (arr A t u [ γ ]ty)
    i⇒ : (invC Θ A t u (judgeSub n ms Γ γ) ∨ objRule ms ty') ⇒B
         (invC Θ A t u (judgeSub (suc n) ms Γ γ) ∨ objRule ms ty')
    i⇒ = ∨-m (invC-mono Θ A t u cm) id⇒
    p⇒ : (psC Θ A t u (judgeSub n ms Γ γ) ∨ ((invC Θ A t u (judgeSub n ms Γ γ) ∨ objRule ms ty') ∧ hdAtLeast 1 ty')) ⇒B
         (psC Θ A t u (judgeSub (suc n) ms Γ γ) ∨ ((invC Θ A t u (judgeSub (suc n) ms Γ γ) ∨ objRule ms ty') ∧ hdAtLeast 1 ty'))
    p⇒ = ∨-m (psC-mono Θ A t u cm) (∧-m i⇒ id⇒)

  sub-mono : ∀ n ms Γ γ → Pw IP≤ (judgeSub n ms Γ γ) (judgeSub (suc n) ms Γ γ)
  sub-mono n ms Γ ⟨⟩       = []
  sub-mono n ms Γ (γ ,ₛ t) = pw-snoc (sub-mono n ms Γ γ) (fuel-mono n ms Γ t)

  star-mono : ∀ n ms Γ m {p p'} → p ⇒B p' → star n ms Γ m p ⇒B star (suc n) ms Γ m p'
  star-mono n ms Γ nothing  pp ()
  star-mono n ms Γ (just A) pp = ∨-m id⇒ (∧-m pp (∨-m id⇒ (bd-mono n ms Γ A)))

  bd-mono : ∀ n ms Γ A → bdStar n ms Γ A ⇒B bdStar (suc n) ms Γ A
  bd-mono zero    ms Γ A ()
  bd-mono (suc n) ms Γ ⋆ ()
  bd-mono (suc n) ms Γ (arr A s u) =
    ∧-m (snd (snd (fuel-mono n ms Γ s))) (snd (snd (fuel-mono n ms Γ u)))

------------------------------------------------------------------------
-- Stability above the dimension.

-- A derivable coh is at least as high as its pasting context.
DimOK : Set
DimOK = ∀ {Θ A t u} → Θ ⊢ps → Θ ⊢ty arr A t u → T (graySide Θ A t u) → dimCtx Θ ≤ suc (dim A)

-- The constants' types are well formed wherever they are used.
SigOK : Set
SigOK = ∀ {Γ k} → Γ ⊢ctx → Valid k → Γ ⊢ty ty k

private
  max-l : ∀ a b {n} → max a b ≤ n → a ≤ n
  max-l zero    b       _       = z≤n
  max-l (suc a) zero    l       = l
  max-l (suc a) (suc b) (s≤s l) = s≤s (max-l a b l)

  max-r : ∀ a b {n} → max a b ≤ n → b ≤ n
  max-r zero    b       l       = l
  max-r (suc a) zero    _       = z≤n
  max-r (suc a) (suc b) (s≤s l) = s≤s (max-r a b l)

  tm-ty : ∀ (closed : S.Closed) → SigOK → ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
  tm-ty closed sig (var-wf w eq)          = lookup-valid w eq
  tm-ty closed sig (coh-wf _ _ tyΔ _ sσ)  = S.ty[] closed tyΔ sσ
  tm-ty closed sig (cst-wf w v)           = sig w v

module Stable (closed : S.Closed) (sig : SigOK) (dimOK : DimOK) (ms : Marks) where

  mutual
    stab : ∀ {Γ t A} n → Γ ⊢tm t ∶ A → dim A ≤ n → judge n ms Γ t ≡ judge (suc n) ms Γ t
    stab {Γ} {var x} n (var-wf w eq) le =
      cong (ip (jinv (judge n ms Γ (var x))) (jps (judge n ms Γ (var x))))
           (subst (λ m → star n ms Γ m P ≡ star (suc n) ms Γ m P) (sym eq)
                  (star-stab n (lookup-valid w eq) le P))
      where P = jps (judge n ms Γ (var x))
    stab {Γ} {cst k} n (cst-wf w v) le =
      cong (ip (jinv (judge n ms Γ (cst k))) (jps (judge n ms Γ (cst k))))
           (star-stab n (sig w v) le (jps (judge n ms Γ (cst k))))
    stab {Γ} {coh Δ (arr B t u) γ} n (coh-wf psΔ cw tyΔ ok sγ) le
      rewrite sub-stab n sγ (≤-trans (dimOK psΔ tyΔ ok) (subst (_≤ n) (dim-[] (arr B t u) γ) le)) =
      cong (ip (jinv (judge (suc n) ms Γ (coh Δ (arr B t u) γ))) (jps (judge (suc n) ms Γ (coh Δ (arr B t u) γ))))
           (star-stab n (S.ty[] closed tyΔ sγ) le (jps (judge (suc n) ms Γ (coh Δ (arr B t u) γ))))

    sub-stab : ∀ {Γ γ Δ} n → Γ ⊢sub γ ∶ Δ → dimCtx Δ ≤ n → judgeSub n ms Γ γ ≡ judgeSub (suc n) ms Γ γ
    sub-stab n (⟨⟩-wf _) le = refl
    sub-stab n (,-wf {σ = γ} {A = C} sγ tw) le =
      cong₂ _++_ (sub-stab n sγ (max-r (dim C) _ le))
                 (cong (_∷ []) (stab n tw (subst (_≤ n) (sym (dim-[] C γ)) (max-l (dim C) _ le))))

    star-stab : ∀ {Γ A} n → Γ ⊢ty A → dim A ≤ n → ∀ p → star n ms Γ (just A) p ≡ star (suc n) ms Γ (just A) p
    star-stab {A = A} n a le p = cong (λ b → (dim A ==ℕ 1) ∨ (p ∧ ((dim A ==ℕ 2) ∨ b))) (bd-stab n a le)

    bd-stab : ∀ {Γ A} n → Γ ⊢ty A → dim A ≤ n → bdStar n ms Γ A ≡ bdStar (suc n) ms Γ A
    bd-stab zero    (⋆-wf _) le = refl
    bd-stab (suc n) (⋆-wf _) le = refl
    bd-stab (suc n) (arr-wf ds du) (s≤s le) =
      cong₂ (λ a b → jpss a ∧ jpss b) (stab n ds le) (stab n du le)

  -- Any fuel at least dim A gives the same judgments.
  fuel-stable : ∀ {Γ t A} k → Γ ⊢tm t ∶ A → judge (dim A + k) ms Γ t ≡ judge (dim A) ms Γ t
  fuel-stable {Γ} {t} {A} zero d = cong (λ n → judge n ms Γ t) (+-zero (dim A))
    where
    +-zero : ∀ a → a + zero ≡ a
    +-zero zero    = refl
    +-zero (suc a) = cong suc (+-zero a)
  fuel-stable {Γ} {t} {A} (suc k) d =
    trans (cong (λ n → judge n ms Γ t) (+-suc (dim A) k))
          (trans (sym (stab (dim A + k) d (m≤m+n (dim A) k))) (fuel-stable k d))
    where
    +-suc : ∀ a b → a + suc b ≡ suc (a + b)
    +-suc zero    b = refl
    +-suc (suc a) b = cong suc (+-suc a b)
    m≤m+n : ∀ m n → m ≤ m + n
    m≤m+n zero    n = z≤n
    m≤m+n (suc m) n = s≤s (m≤m+n m n)

  judgeT≡ : ∀ {Γ t A} → Γ ⊢tm t ∶ A → judgeT ms Γ t ≡ judge (dim A) ms Γ t
  judgeT≡ {Γ} {t} d rewrite typeOf-sound d = refl

------------------------------------------------------------------------
-- Substitution preserves the user-facing judgments (no fuel shift).

module _ (closed : S.Closed) (sig : SigOK) (dimOK : DimOK) where
  private
    lift : ∀ {N ms ms' Γ Δ t A σ} (f : IP → Bool) →
           (∀ k → T (f (judge k ms Γ t)) → T (f (judge (k + N) ms' Δ (t [ σ ]tm)))) →
           Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ →
           T (f (judgeT ms Γ t)) → T (f (judgeT ms' Δ (t [ σ ]tm)))
    lift {N} {ms} {ms'} {Γ} {Δ} {t} {A} {σ} f th d sd p =
      subst (λ j → T (f j)) (sym (Stable.judgeT≡ closed sig dimOK ms' dσ))
        (subst (λ j → T (f j)) (Stable.fuel-stable closed sig dimOK ms' N dσ)
          (subst (λ n → T (f (judge (n + N) ms' Δ (t [ σ ]tm)))) (sym (dim-[] A σ))
            (th (dim A) (subst (λ j → T (f j)) (Stable.judgeT≡ closed sig dimOK ms d) p))))
      where
      dσ = S.tm[] closed d sd

  inv-[]ᵀ : ∀ {N ms ms' Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
            T ((ms , Γ) ⊢ t inv) → T ((ms' , Δ) ⊢ t [ σ ]tm inv)
  inv-[]ᵀ d sd r = lift jinv (λ k → inv-[] closed k d sd r) d sd

  ps-[]ᵀ : ∀ {N ms ms' Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
           T ((ms , Γ) ⊢ t ps) → T ((ms' , Δ) ⊢ t [ σ ]tm ps)
  ps-[]ᵀ d sd r = lift jps (λ k → ps-[] closed k d sd r) d sd

  ps*-[]ᵀ : ∀ {N ms ms' Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
            T ((ms , Γ) ⊢ t ps*) → T ((ms' , Δ) ⊢ t [ σ ]tm ps*)
  ps*-[]ᵀ d sd r = lift jpss (λ k → ps*-[] closed k d sd r) d sd
