------------------------------------------------------------------------
-- Operation heads (spec §1.1, §1.6; ledger S27 (b)) in the kernel with
-- binders.
--
-- Spec §1.1 has a third term former besides variables and coherences:
-- an operation head h applied to a substitution, h[σ], where h has an
-- arity context Γ_h, a type A_h over Γ_h and a decidable validity
-- predicate, and h[σ] : A_h[σ] for σ : Γ_h. Chapters 6–8 add families
-- of heads indexed by syntax (lim_Γ, λ_{Γ,g}, uni_{Γ,n}, ⟦Γ⟧, …).
--
-- In CaTTExp.Binder a head is a binding former whose data are closed:
--
--   h_Θ[σ]  is  bnd h y Θ σ    with  bargs h y Θ = Γ_h,  bres h y Θ = A_h,
--
-- where the index Θ (a context, for families indexed by syntax; ε for a
-- plain head) and the selector y (λ_{Γ,g}'s g, uni's component) are
-- part of the head, the arity Γ_h is written with bound variables
-- (bvar 0 j is argument j) and A_h is over it. DES (`Binder.Des`) is
-- already of this form. The binder rule then *is* spec §1.1's rule (op):
-- its telescope premise is the well-formedness of the index, its
-- argument premise is σ : Γ_h, and its type is A_h[σ].
--
-- This module proves, once for every head:
--
--  * `HeadAt b`: b's index, arity and type are closed (mention no free
--    variable) wherever its side condition holds. That is the whole
--    requirement: `head-laws` derives the stability laws `BinderLaws`
--    from it, so substitution (`Binder.Subst`), weakening
--    (`Binder.Rename`), the certified checker and its completeness
--    (`Binder.CheckWith`, `Binder.Completeness`) hold for heads with no
--    further proof. This is spec §1.5's "the proof is the coherence
--    case": nothing in a head's data is touched by substitution.
--  * `HeadOK b`: Γ_h ⊢ A_h, stated in the empty context (the arity
--    opened at level 0). `head-presup` derives PresupLaws' `res-wf`
--    from it in every context, by weakening the closed arity past any
--    prefix (`tel-wk`), so presupposition (`Binder.Presup.tm-ty`) holds
--    for heads.
--
-- Laws are stated per former, so a signature mixing heads with real
-- binders (INIT) proves BinderLaws by cases, using `head-*` on its
-- heads; `head-laws` is the all-heads case.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.Heads (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open Laws 𝕊

------------------------------------------------------------------------
-- Closed syntax.

-- A former is a head when, under its side condition, its index
-- telescope, its arity and its type mention no free variable.
HeadAt : B → Set
HeadAt b = ∀ y Δ → T (bside b y Δ) →
           T (scTel? 0 Δ) × T (scTel? 0 (bargs b y Δ)) × T (scTy? 0 (bres b y Δ))

closed-tel : ∀ Δ σ → T (scTel? 0 Δ) → Δ [ σ ]tel ≡ Δ
closed-tel ε             σ _ = refl
closed-tel (Δ ▸[ ms ] A) σ p =
  let (a , b) = T∧ {scTel? 0 Δ} p in cong₂ (_▸[ ms ]_) (closed-tel Δ σ a) (closed-ty A σ b)

scTel-mono : ∀ n Δ → T (scTel? 0 Δ) → T (scTel? n Δ)
scTel-mono n ε             _ = tt
scTel-mono n (Δ ▸[ _ ] A) p =
  let (a , b) = T∧ {scTel? 0 Δ} p in ∧T (scTel-mono n Δ a) (scTy-mono n A b)

------------------------------------------------------------------------
-- The stability laws hold at every head.

module _ {b : B} (h : HeadAt b) where

  head-side-stable : ∀ y Δ σ → LC σ → T (bside b y Δ) → T (bside b y (Δ [ σ ]tel))
  head-side-stable y Δ σ _ p rewrite closed-tel Δ σ (fst (h y Δ p)) = p

  head-args-stable : ∀ y Δ σ → LC σ → T (bside b y Δ) →
                     bargs b y (Δ [ σ ]tel) ≡ (bargs b y Δ) [ σ ]tel
  head-args-stable y Δ σ _ p
    rewrite closed-tel Δ σ (fst (h y Δ p)) =
    sym (closed-tel (bargs b y Δ) σ (fst (snd (h y Δ p))))

  head-res-stable : ∀ y Δ σ → LC σ → T (bside b y Δ) →
                    bres b y (Δ [ σ ]tel) ≡ (bres b y Δ) [ σ ]ty
  head-res-stable y Δ σ _ p
    rewrite closed-tel Δ σ (fst (h y Δ p)) =
    sym (closed-ty (bres b y Δ) σ (snd (snd (h y Δ p))))

  head-res-sc : ∀ y Δ n → T (bside b y Δ) → T (scTel? n Δ) → T (scTy? n (bres b y Δ))
  head-res-sc y Δ n p _ = scTy-mono n (bres b y Δ) (snd (snd (h y Δ p)))

  head-bargs-sc : ∀ y Δ n → T (bside b y Δ) → T (scTel? n Δ) → T (scTel? n (bargs b y Δ))
  head-bargs-sc y Δ n p _ = scTel-mono n (bargs b y Δ) (fst (snd (h y Δ p)))

-- A signature all of whose formers are heads satisfies BinderLaws.
head-laws : (∀ b → HeadAt b) → BinderLaws
head-laws h = record
  { side-stable = λ b → head-side-stable (h b)
  ; args-stable = λ b → head-args-stable (h b)
  ; res-stable  = λ b → head-res-stable (h b)
  ; res-sc      = λ b → head-res-sc (h b)
  }

------------------------------------------------------------------------
-- Presupposition: Γ_h ⊢ A_h in the empty context gives it after any
-- context.

module Typed
  (side : Ctx → Ty → Tm → Tm → Bool)
  (mark : Ctx → BM.Mark → Tm → Bool)
  where

  open import CaTTExp.Binder.TypingWith 𝕊 side mark
  open import CaTTExp.Binder.Scoping 𝕊 side mark
  open import CaTTExp.Binder.Rename 𝕊 side mark
  open import CaTTExp.Binder.Subst 𝕊 side mark
  open import CaTTExp.Binder.Presup 𝕊 side mark

  -- The arity context of a head, opened in the empty context, and its
  -- type over it.
  arity : B → Nat → Ctx → Ctx
  arity b y Δ = openTel 0 (bargs b y Δ)

  resTy : B → Nat → Ctx → Ty
  resTy b y Δ = opTy 0 (fresh 0 (len (bargs b y Δ))) (bres b y Δ)

  -- Γ_h ⊢ A_h for every valid instance of b.
  HeadOK : B → Set
  HeadOK b = ∀ y Δ → T (bside b y Δ) → arity b y Δ ⊢ty resTy b y Δ

  ++ₛ-idl : ∀ ts → (⟨⟩ ++ₛ ts) ≡ ts
  ++ₛ-idl ⟨⟩        = refl
  ++ₛ-idl (ts ,ₛ t) = cong (_,ₛ t) (++ₛ-idl ts)

  private
    ⧺-ctx : ∀ {Γ} Ξ → (Γ ⧺ Ξ) ⊢ctx → Γ ⊢ctx
    ⧺-ctx ε             w          = w
    ⧺-ctx (Ξ ▸[ _ ] _)  (▸-wf w _) = ⧺-ctx Ξ w

    -- Opening a closed type at 0, then substituting ts, is opening it
    -- with ts.
    open-inst₀ : ∀ ts A → LC ts → T (scTy? 0 A) →
                 (opTy 0 (fresh 0 (lenₛ ts)) A) [ ts ]ty ≡ opTy 0 ts A
    open-inst₀ ts A lts p =
      trans (op-[]ty 0 (fresh 0 (lenₛ ts)) A ts lts)
            (cong₂ (opTy 0)
              (subst (λ ρ → fresh 0 (lenₛ ts) ∘ ρ ≡ ts) (++ₛ-idl ts) (fresh-∘-++ ⟨⟩ ts))
              (closed-ty A ts p))

  module _ (closed : Closed) (laws : BinderLaws)
           (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where

    -- Arguments for a closed telescope are a substitution from the
    -- telescope opened in the empty context.
    args-sub₀ : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → T (scTel? 0 Θ) →
                openTel 0 Θ ⊢ctx → Γ ⊢sub ts ∶ openTel 0 Θ
    args-sub₀ (⟨⟩-a w) _ _ = ⟨⟩-wf w
    args-sub₀ {Γ} {ts ,ₛ t} {Θ ▸[ ms ] A} (,-a a d o) p (▸-wf w _) =
      ,-wf (args-sub₀ a pΘ w)
           (subst (Γ ⊢tm t ∶_)
                  (sym (subst (λ k → (opTy 0 (fresh 0 k) A) [ ts ]ty ≡ opTy 0 ts A)
                              (args-len a) (open-inst₀ ts A (args-lc a) pA)))
                  d)
           o
      where
      pΘ = fst (T∧ {scTel? 0 Θ} p)
      pA = snd (T∧ {scTel? 0 Θ} p)

    -- A closed telescope well formed in the empty context is well
    -- formed after any context.
    tel-wk : ∀ {Γ} Θ → Γ ⊢ctx → T (scTel? 0 Θ) → openTel 0 Θ ⊢ctx →
             (Γ ⧺ openTel (len Γ) Θ) ⊢ctx
    tel-wk ε             w _ _ = w
    tel-wk {Γ} (Θ ▸[ ms ] A) w p (▸-wf wΘ a) =
      ▸-wf wΓΘ
        (subst ((Γ ⧺ openTel (len Γ) Θ) ⊢ty_) eq
          (ty[] closed laws mren msub mvar a
             (args-sub₀ (fresh-args closed laws mren msub mvar Θ pΘ wΓΘ) pΘ wΘ)))
      where
      pΘ = fst (T∧ {scTel? 0 Θ} p)
      pA = snd (T∧ {scTel? 0 Θ} p)
      wΓΘ = tel-wk Θ w pΘ wΘ
      eq : (opTy 0 (fresh 0 (len Θ)) A) [ fresh (len Γ) (len Θ) ]ty
           ≡ opTy 0 (fresh (len Γ) (len Θ)) A
      eq = subst (λ k → (opTy 0 (fresh 0 k) A) [ fresh (len Γ) (len Θ) ]ty
                        ≡ opTy 0 (fresh (len Γ) (len Θ)) A)
                 (lenₛ-fresh (len Γ) (len Θ))
                 (open-inst₀ (fresh (len Γ) (len Θ)) A (lc-fresh (len Γ) (len Θ)) pA)

    -- PresupLaws' res-wf at a head with HeadOK.
    head-res-wf : ∀ {b} → HeadAt b → HeadOK b →
                  ∀ {Γ y Δ} → T (scTel? (len Γ) Δ) → T (lcTel? 1 Δ) →
                  (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (bside b y Δ) →
                  (Γ ⧺ openTel (len Γ) (bargs b y Δ)) ⊢ty
                    opTy 0 (fresh (len Γ) (len (bargs b y Δ))) (bres b y Δ)
    head-res-wf {b} h ok {Γ} {y} {Δ} _ _ wt p =
      subst ((Γ ⧺ openTel (len Γ) Θ) ⊢ty_) eq
        (ty[] closed laws mren msub mvar a
           (args-sub₀ (fresh-args closed laws mren msub mvar Θ pΘ wΓΘ) pΘ (ty-ctx a)))
      where
      Θ  = bargs b y Δ
      R  = bres b y Δ
      pΘ = fst (snd (h y Δ p))
      pR = snd (snd (h y Δ p))
      a  = ok y Δ p
      wΓΘ = tel-wk Θ (⧺-ctx (openTel (len Γ) Δ) wt) pΘ (ty-ctx a)
      eq : (opTy 0 (fresh 0 (len Θ)) R) [ fresh (len Γ) (len Θ) ]ty
           ≡ opTy 0 (fresh (len Γ) (len Θ)) R
      eq = subst (λ k → (opTy 0 (fresh 0 k) R) [ fresh (len Γ) (len Θ) ]ty
                        ≡ opTy 0 (fresh (len Γ) (len Θ)) R)
                 (lenₛ-fresh (len Γ) (len Θ))
                 (open-inst₀ (fresh (len Γ) (len Θ)) R (lc-fresh (len Γ) (len Θ)) pR)

  -- A signature all of whose formers are heads with HeadOK satisfies
  -- PresupLaws (for its own BinderLaws, `head-laws`).
  head-presup : Closed → (h : ∀ b → HeadAt b) → (∀ b → HeadOK b) →
                MarkRen → MarkSub → MarkVar → PresupLaws
  head-presup closed h ok mren msub mvar = record
    { bargs-sc = λ b → head-bargs-sc (h b)
    ; res-wf   = λ {Γ} {b} → head-res-wf closed (head-laws h) mren msub mvar (h b) (ok b) {Γ}
    }
