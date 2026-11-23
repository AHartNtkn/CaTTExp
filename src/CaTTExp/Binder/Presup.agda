------------------------------------------------------------------------
-- Presupposition for CaTT with binders (ledger S26i):
--
--   Γ ⊢ t ∶ A   implies   Γ ⊢ A
--
-- for every coh side condition, every mark judgment for which
-- substitution is admissible (CaTTExp.Binder.Subst's hypotheses), and
-- every signature whose constants have well-formed types (`SigOK`) and
-- whose binder interface satisfies `PresupLaws`:
--
--  * bargs-sc: the argument telescope is scoped where Δ is;
--  * res-wf:  the result type is well formed over the argument
--             telescope opened after Γ.
--
-- These mention the typing judgment, so they are a record of their own
-- rather than fields of BinderLaws (which is purely syntactic).
--
-- The bnd case instantiates res-wf with the arguments: a well-typed
-- argument list ts for Θ gives the substitution id_Γ ++ ts from
-- Γ ⧺ openTel Θ to Γ (`args-sub′`), and substituting by it turns the
-- opened result type into opTy 0 ts (bres b y Δ).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.Presup
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Scoping 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark
open import CaTTExp.Binder.Subst 𝕊 side mark
open Laws 𝕊

-- Constants have well-formed types in every context.
SigOK : Set
SigOK = ∀ {Γ k} → Γ ⊢ctx → Valid k → Γ ⊢ty ty k

record PresupLaws : Set where
  field
    bargs-sc : ∀ b y Δ n → T (bside b y Δ) → T (scTel? n Δ) → T (scTel? n (bargs b y Δ))
    res-wf  : ∀ {Γ b y Δ} → T (scTel? (len Γ) Δ) → T (lcTel? 1 Δ) →
              (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (bside b y Δ) →
              (Γ ⧺ openTel (len Γ) (bargs b y Δ)) ⊢ty
                opTy 0 (fresh (len Γ) (len (bargs b y Δ))) (bres b y Δ)

------------------------------------------------------------------------
-- Judgments presuppose their context.

mutual
  tm-ctx : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx
  tm-ctx (var-wf w _)            = w
  tm-ctx (coh-wf _ _ _ _ s)      = sub-ctx′ s
  tm-ctx (cst-wf w _)            = w
  tm-ctx (bnd-wf _ _ _ _ as)     = args-ctx as

  ty-ctx : ∀ {Γ A} → Γ ⊢ty A → Γ ⊢ctx
  ty-ctx (⋆-wf w)     = w
  ty-ctx (arr-wf d _) = tm-ctx d

  sub-ctx′ : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ctx
  sub-ctx′ (⟨⟩-wf w)    = w
  sub-ctx′ (,-wf s _ _) = sub-ctx′ s

  args-ctx : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → Γ ⊢ctx
  args-ctx (⟨⟩-a w)    = w
  args-ctx (,-a a _ _) = args-ctx a

args-len : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → lenₛ ts ≡ len Θ
args-len (⟨⟩-a _)    = refl
args-len (,-a a _ _) = cong suc (args-len a)

-- The fresh variables after σ, substituted by σ ++ ts, give ts.
fresh-∘-++ : ∀ σ ts → fresh (lenₛ σ) (lenₛ ts) ∘ (σ ++ₛ ts) ≡ ts
fresh-∘-++ σ ⟨⟩       = refl
fresh-∘-++ σ (ts ,ₛ t) =
  cong₂ _,ₛ_
    (trans (ext-sub (fresh (lenₛ σ) (lenₛ ts)) (σ ++ₛ ts) t
              (subst (λ m → T (scSub? m (fresh (lenₛ σ) (lenₛ ts)))) (sym (lenₛ-++ σ ts))
                     (sc-fresh (lenₛ σ) (lenₛ ts))))
           (fresh-∘-++ σ ts))
    (subst (λ b → (if b then t else lookupₛ (σ ++ₛ ts) (lenₛ σ + lenₛ ts)) ≡ t)
           (sym (==-self (sym (lenₛ-++ σ ts)))) refl)

module _ (closed : Closed) (laws : BinderLaws)
         (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where

  private
    idn : Nat → Sub
    idn n = fresh 0 n

    -- Opening at n, then substituting id_n ++ ts, is opening with ts.
    open-inst : ∀ n ts A → LC ts → T (scTy? n A) →
                (opTy 0 (fresh n (lenₛ ts)) A) [ idn n ++ₛ ts ]ty ≡ opTy 0 ts A
    open-inst n ts A lts p =
      trans (op-[]ty 0 (fresh n (lenₛ ts)) A (idn n ++ₛ ts) (lc-++ (idn n) ts (lc-fresh 0 n) lts))
            (cong₂ (opTy 0)
              (subst (λ m → fresh m (lenₛ ts) ∘ (idn n ++ₛ ts) ≡ ts) (lenₛ-fresh 0 n)
                     (fresh-∘-++ (idn n) ts))
              (trans (ext-ty-++ A (idn n) ts
                        (subst (λ m → T (scTy? m A)) (sym (lenₛ-fresh 0 n)) p))
                     (id-ty n A p)))

  -- Well-typed arguments for Θ are a substitution from Γ ⧺ openTel Θ.
  args-sub′ : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → T (scTel? (len Γ) Θ) →
              (Γ ⧺ openTel (len Γ) Θ) ⊢ctx →
              Γ ⊢sub (idn (len Γ) ++ₛ ts) ∶ (Γ ⧺ openTel (len Γ) Θ)
  args-sub′ {Γ} (⟨⟩-a w) _ _ = id-sub′ w
    where
    id-sub′ : ∀ {Γ} → Γ ⊢ctx → Γ ⊢sub fresh 0 (len Γ) ∶ Γ
    id-sub′ {ε} w = ⟨⟩-wf w
    id-sub′ {Γ ▸[ ms ] A} w@(▸-wf wΓ a) =
      ,-wf (wk-sub closed laws mren wΓ (id-sub′ wΓ) w)
           (subst (λ X → (Γ ▸[ ms ] A) ⊢tm var (len Γ) ∶ X)
                  (sym (id-ty (len Γ) A (ty-sc closed laws a)))
                  (var-wf w (lookup-top Γ {ms} A (len Γ) (==-self {len Γ} refl))))
           (subst (λ ns → T (marksOK (Γ ▸[ ms ] A) ns (var (len Γ))))
                  (marksAt-top Γ ms A (len Γ) (==-self {len Γ} refl))
                  (mvar w (lookup-top Γ {ms} A (len Γ) (==-self {len Γ} refl))))
  args-sub′ {Γ} {ts ,ₛ t} {Θ ▸[ ms ] A} (,-a a d o) p (▸-wf w x) =
    ,-wf (args-sub′ a pΘ w)
         (subst (Γ ⊢tm t ∶_)
                (sym (subst (λ k → (opTy 0 (fresh (len Γ) k) A) [ idn (len Γ) ++ₛ ts ]ty ≡ opTy 0 ts A)
                            (args-len a)
                            (open-inst (len Γ) ts A (args-lc a) pA)))
                d)
         o
    where
    pΘ = fst (T∧ {scTel? (len Γ) Θ} p)
    pA = snd (T∧ {scTel? (len Γ) Θ} p)

  -- A variable's type is well formed.
  lookup-ty : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
  lookup-ty {Γ ▸[ ms ] C} {i} w@(▸-wf wΓ c) eq with i ==ℕ len Γ
  ... | true  = subst ((Γ ▸[ ms ] C) ⊢ty_) (just-inj eq) (wk-ty closed laws mren c w)
  ... | false = wk-ty closed laws mren (lookup-ty wΓ eq) w

  -- The fresh variables of an opened closed telescope are arguments
  -- for it (their marks by MarkVar).
  fresh-args : ∀ {Γ} Θ → T (scTel? 0 Θ) → (Γ ⧺ openTel (len Γ) Θ) ⊢ctx →
               (Γ ⧺ openTel (len Γ) Θ) ⊢args fresh (len Γ) (len Θ) ∶ Θ
  fresh-args ε _ w = ⟨⟩-a w
  fresh-args {Γ} (Θ ▸[ ms ] A) p w@(▸-wf wΘ _) =
    ,-a (wk-args closed laws mren (fresh-args Θ pΘ wΘ) w pΘ)
        (var-wf w top)
        (subst (λ ns → T (marksOK C ns (var (len Γ + len Θ))))
               (marksAt-top (Γ ⧺ openTel (len Γ) Θ) ms X (len Γ + len Θ) eqT)
               (mvar w top))
    where
    pΘ = fst (T∧ {scTel? 0 Θ} p)
    X  = opTy 0 (fresh (len Γ) (len Θ)) A
    C  = (Γ ⧺ openTel (len Γ) Θ) ▸[ ms ] X
    eqT : ((len Γ + len Θ) ==ℕ len (Γ ⧺ openTel (len Γ) Θ)) ≡ true
    eqT = ==-self (sym (trans (len-⧺ Γ (openTel (len Γ) Θ)) (cong (len Γ +_) (len-openTel (len Γ) Θ))))
    top : lookup C (len Γ + len Θ) ≡ just X
    top = lookup-top (Γ ⧺ openTel (len Γ) Θ) {ms} X (len Γ + len Θ) eqT

  ----------------------------------------------------------------------
  -- The theorem.

  module _ (sig : SigOK) (plaws : PresupLaws) where

    open PresupLaws plaws

    tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
    tm-ty (var-wf w eq)          = lookup-ty w eq
    tm-ty (coh-wf _ _ a _ s)     = ty[] closed laws mren msub mvar a s
    tm-ty (cst-wf w v)           = sig w v
    tm-ty {Γ} (bnd-wf {b} {y} {Δ} {ts} sc l wt ok as) =
      subst (Γ ⊢ty_)
        (subst (λ k → (opTy 0 (fresh (len Γ) k) R) [ fresh 0 (len Γ) ++ₛ ts ]ty ≡ opTy 0 ts R)
               (args-len as)
               (open-inst (len Γ) ts R (args-lc as) (res-sc b y Δ (len Γ) ok sc)))
        (ty[] closed laws mren msub mvar (res-wf sc l wt ok)
              (args-sub′ as (bargs-sc b y Δ (len Γ) ok sc) (ty-ctx (res-wf sc l wt ok))))
      where
      open BinderLaws laws
      R = bres b y Δ
