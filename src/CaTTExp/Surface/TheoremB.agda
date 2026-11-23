------------------------------------------------------------------------
-- Theorem B of notes/surface-conservativity.md §3.2: kernel conversion
-- (KC) follows from relative coherence (EL) and whiskering.
--
-- Setting: the kernel TypingWith 𝕊 side and a surface equality E as in
-- CaTTExp.Surface.Conservativity. Hypotheses, all module parameters:
--
--  (Inv)   arr-inversion: Γ ∣ arr A a b ≈ arr A′ a′ b′ gives A ≈ A′,
--          a ≈ a′, b ≈ b′;
--  (Dim)   ≈ on types preserves dimension;
--  presup  the kernel's presupposition lemma;
--  (W)     a raw whiskering operation `wh Γ j p x q` (p ∗ⱼ x ∗ⱼ q) with
--          access to the context Γ (a context-free `wh` cannot satisfy
--          Wh-wf: a variable's dimension depends on Γ),
--            Wh-wf : its typing rule, stated with the explicit type
--                    transformer `whTy` defined below, and
--            Wh-≈  : p, q "units" ⇒ wh Γ j p x q ≈ x;
--  Unit    the predicate "≈ an identity", left abstract: EL produces
--          cells satisfying it and Wh-≈ consumes it (instantiate it as
--          "≈ the kernel's identity" to get Definition 2.3 exactly);
--  (EL)    at Γ: parallel kernel terms u ≈ u′ are joined by a kernel
--          cell u → u′ satisfying Unit.
--
-- Result: `kc-from-el : ELAt Γ → KCAt Γ`, and with Theorem A
-- (`conservative-from-el`) conservativity at Γ from EL at Γ and at
-- pasting contexts.
--
-- The proof builds, by recursion on a kernel type B with B ≈ B′, a
-- transport map tr taking every cell over B (every cell whose type
-- has B as a prefix) to the corresponding cell over B′: over
-- B = arr C a b, transport over C first, then whisker at level dim C
-- with the EL-cells a′ → tr a and tr b → b′. A term of type A goes to
-- a term of type exactly A′.
--
-- Not done here: discharging (W) for a particular kernel (constructing
-- `wh` from coherences over the linear pasting contexts
-- Σʲ(D¹ ∨ Dᵐ⁻ʲ ∨ D¹) and proving Wh-wf and Wh-≈). Until that is done
-- the hypotheses are not known to be jointly satisfiable, so the
-- module proves the reduction KC ⇐ EL given (W), not KC ⇐ EL outright.
-- Wh-wf is syntactic: the boundary terms of the whiskering head,
-- after substitution, must be exactly the recursive `wh` calls on
-- the boundaries. The construction must be made to satisfy this.
-- ELAt is undimensioned (EL in every dimension); the proof only uses
-- it below dim B, so a dimensioned version is a routine refinement.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Subst as SubstM

module CaTTExp.Surface.TheoremB
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (closed : SubstM.Closed 𝕊 side)
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side
open import CaTTExp.Surface.Conservativity 𝕊 side closed

------------------------------------------------------------------------
-- Prefixes: Pre B X says X = arr (… (arr B u₁ v₁) …) uₖ vₖ.

data Pre (B : Ty) : Ty → Set where
  here  : Pre B B
  there : ∀ {Y u v} → Pre B Y → Pre B (arr Y u v)

pre-down : ∀ {C a b X} → Pre (arr C a b) X → Pre C X
pre-down here      = there here
pre-down (there p) = there (pre-down p)

------------------------------------------------------------------------
-- Arithmetic.

private
  +-suc : ∀ k n → k + suc n ≡ suc (k + n)
  +-suc zero    n = refl
  +-suc (suc k) n = cong suc (+-suc k n)

  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  -- k + suc n is never n
  ==-above : ∀ k n → ((k + suc n) ==ℕ n) ≡ false
  ==-above k zero    rewrite +-suc k zero = refl
  ==-above k (suc n) rewrite +-suc k (suc n) | sym (+-suc k n) = ==-above k n

  pre-dim : ∀ {B X} → Pre B X → Σ Nat λ k → dim X ≡ k + dim B
  pre-dim here = 0 , refl
  pre-dim (there p) with pre-dim p
  ... | k , e = suc k , cong suc e

  ifte : ∀ {a} {A : Set a} → Bool → A → A → A
  ifte true  x _ = x
  ifte false _ y = y

module _ (E : SurfaceEq) where
  open SurfaceEq E

  module Hyp
    (inv-arr : ∀ {Γ A A′ a a′ b b′} → Γ ∣ arr A a b ≈T arr A′ a′ b′ →
               (Γ ∣ A ≈T A′) × (Γ ∣ a ≈t a′) × (Γ ∣ b ≈t b′))
    (dim-≈   : ∀ {Γ A A′} → Γ ∣ A ≈T A′ → dim A ≡ dim A′)
    (presup  : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A)
    (Unit    : Ctx → Tm → Set)
    (wh      : Ctx → Nat → Tm → Tm → Tm → Tm)
    where

    -- The type of p ∗ⱼ x ∗ⱼ q, for x : X whose level-j pair is (s, t)
    -- and p : s′ → s, q : t → t′: the level-j pair becomes (s′, t′),
    -- every higher pair is whiskered.
    whTy : Ctx → Nat → Tm → Tm → Tm → Tm → Ty → Ty
    whTy Γ j p q s′ t′ ⋆           = ⋆
    whTy Γ j p q s′ t′ (arr Y u v) =
      ifte (dim Y ==ℕ j) (arr Y s′ t′)
                         (arr (whTy Γ j p q s′ t′ Y) (wh Γ j p u q) (wh Γ j p v q))

    module Thm
      (Wh-wf : ∀ {Γ C s s′ t t′ p q x X} →
               Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ →
               Pre (arr C s t) X → Γ ⊢tm x ∶ X →
               Γ ⊢tm wh Γ (dim C) p x q ∶ whTy Γ (dim C) p q s′ t′ X)
      (Wh-≈  : ∀ {Γ C s s′ t t′ p q x X} →
               Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ →
               Unit Γ p → Unit Γ q →
               Pre (arr C s t) X → Γ ⊢tm x ∶ X →
               Γ ∣ wh Γ (dim C) p x q ≈t x)
      where

      ELAt : Ctx → Set
      ELAt Γ = ∀ {C u u′} → Γ ⊢tm u ∶ C → Γ ⊢tm u′ ∶ C → Γ ∣ u ≈t u′ →
               Σ Tm λ e → (Γ ⊢tm e ∶ arr C u u′) × Unit Γ e

      -- the type a transport map gives a cell over B
      trTy : (Tm → Tm) → Ty → ∀ {B X} → Pre B X → Ty
      trTy tr B′ here                    = B′
      trTy tr B′ (there {Y} {u} {v} p)   = arr (trTy tr B′ p) (tr u) (tr v)

      record Transport (Γ : Ctx) (B B′ : Ty) : Set where
        field
          tr    : Tm → Tm
          tr-wf : ∀ {x X} (pr : Pre B X) → Γ ⊢tm x ∶ X → Γ ⊢tm tr x ∶ trTy tr B′ pr
          tr-≈  : ∀ {x X} → Pre B X → Γ ⊢tm x ∶ X → Γ ∣ tr x ≈t x

      private
        trTy-id : ∀ {B X} (pr : Pre B X) → trTy (λ x → x) B pr ≡ X
        trTy-id here = refl
        trTy-id (there {Y} {u} {v} p) = cong (λ Z → arr Z u v) (trTy-id p)

        -- transporting over C keeps the prefix arr C′ (tr a) (tr b)
        pre-tr : ∀ {C a b X} (tr : Tm → Tm) (C′ : Ty) (pr : Pre (arr C a b) X) →
                 Pre (arr C′ (tr a) (tr b)) (trTy tr C′ (pre-down pr))
        pre-tr tr C′ here      = here
        pre-tr tr C′ (there p) = there (pre-tr tr C′ p)

        dim-ne : ∀ {B Y} (C : Ty) → Pre B Y → dim B ≡ suc (dim C) →
                 (dim Y ==ℕ dim C) ≡ false
        dim-ne C pr e with pre-dim pr
        ... | k , e′ rewrite e′ | e = ==-above k (dim C)

        -- the whiskered type of a transported cell is the transported type
        wh-trTy : ∀ {Γ C a b C′ a′ b′ X} (tr₀ : Tm → Tm) (p q : Tm) →
                  (pr : Pre (arr C a b) X) →
                  whTy Γ (dim C′) p q a′ b′ (trTy tr₀ C′ (pre-down pr))
                  ≡ trTy (λ x → wh Γ (dim C′) p (tr₀ x) q) (arr C′ a′ b′) pr
        wh-trTy {C′ = C′} tr₀ p q here rewrite ==-refl (dim C′) = refl
        wh-trTy {Γ} {C} {a} {b} {C′} {a′} {b′} tr₀ p q (there {Y} {u} {v} pr)
          rewrite dim-ne C′ (pre-tr {a = a} {b = b} tr₀ C′ pr) refl =
          cong (λ Z → arr Z (wh Γ (dim C′) p (tr₀ u) q) (wh Γ (dim C′) p (tr₀ v) q))
               (wh-trTy {Γ} {C} {a} {b} {C′} {a′} {b′} tr₀ p q pr)

        dim⋆arr : ∀ {n} → 0 ≡ suc n → ⊥
        dim⋆arr ()

      transport : ∀ {Γ B B′} → ELAt Γ → Γ ⊢ty B → Γ ⊢ty B′ → Γ ∣ B ≈T B′ →
                  Transport Γ B B′
      transport el (⋆-wf _) (⋆-wf _) _ = record
        { tr    = λ x → x
        ; tr-wf = λ pr d → subst (_ ⊢tm _ ∶_) (sym (trTy-id pr)) d
        ; tr-≈  = λ _ _ → t-refl
        }
      transport el (⋆-wf _) (arr-wf _ _) e = ⊥-elim (dim⋆arr (dim-≈ e))
      transport el (arr-wf _ _) (⋆-wf _) e = ⊥-elim (dim⋆arr (sym (dim-≈ e)))
      transport {Γ} el (arr-wf {C} {a} {b} da db) (arr-wf {C′} {a′} {b′} da′ db′) e
        with inv-arr e
      ... | eC , ea , eb = record { tr = tr ; tr-wf = tr-wf ; tr-≈ = tr-≈ }
        where
        T₀ = transport el (presup da) (presup da′) eC
        open Transport T₀ renaming (tr to tr₀; tr-wf to tr₀-wf; tr-≈ to tr₀-≈)

        a₁ = tr₀ a
        b₁ = tr₀ b
        wa₁ : Γ ⊢tm a₁ ∶ C′
        wa₁ = tr₀-wf here da
        wb₁ : Γ ⊢tm b₁ ∶ C′
        wb₁ = tr₀-wf here db

        P = el da′ wa₁ (t-trans (t-sym ea) (t-sym (tr₀-≈ here da)))
        Q = el wb₁ db′ (t-trans (tr₀-≈ here db) eb)
        p = fst P
        q = fst Q

        tr : Tm → Tm
        tr x = wh Γ (dim C′) p (tr₀ x) q

        tr-wf : ∀ {x X} (pr : Pre (arr C a b) X) → Γ ⊢tm x ∶ X →
                Γ ⊢tm tr x ∶ trTy tr (arr C′ a′ b′) pr
        tr-wf pr dx =
          subst (Γ ⊢tm tr _ ∶_) (wh-trTy {Γ} tr₀ p q pr)
            (Wh-wf (fst (snd P)) (fst (snd Q))
                   (pre-tr tr₀ C′ pr) (tr₀-wf (pre-down pr) dx))

        tr-≈ : ∀ {x X} → Pre (arr C a b) X → Γ ⊢tm x ∶ X → Γ ∣ tr x ≈t x
        tr-≈ pr dx =
          t-trans (Wh-≈ (fst (snd P)) (fst (snd Q)) (snd (snd P)) (snd (snd Q))
                        (pre-tr tr₀ C′ pr) (tr₀-wf (pre-down pr) dx))
                  (tr₀-≈ (pre-down pr) dx)

      -- Theorem B: EL at Γ gives kernel conversion at Γ.
      kc-from-el : ∀ {Γ} → ELAt Γ → KCAt E Γ
      kc-from-el el {t} {A} {A′} dt wA′ e =
        let T = transport el (presup dt) wA′ e
        in Transport.tr T t , Transport.tr-wf T here dt , Transport.tr-≈ T here dt

      -- With Theorem A: EL at Γ and at every pasting context, plus (SC),
      -- give conservativity at Γ.
      conservative-from-el :
        SideResp E → (∀ {Δ} → Δ ⊢ps → ELAt Δ) →
        ∀ {Γ t B} → ELAt Γ → Γ ⊢ty B → _⊢ˢtm_∶_ E Γ t B →
        Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (Γ ∣ t′ ≈t t)
      conservative-from-el sc el-ps elΓ =
        Conservative.conservative E sc (λ ps → kc-from-el (el-ps ps)) (kc-from-el elΓ)
