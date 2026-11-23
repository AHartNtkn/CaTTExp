------------------------------------------------------------------------
-- Admissibility of substitution for CaTT with binders (spec §1.5),
-- for every coh side condition, every binder interface satisfying
-- BinderLaws, and every mark judgment that is stable under renaming
-- and substitution of well-typed terms (MarkRen, MarkSub) and gives a
-- variable the marks of its entry (MarkVar):
--
--   Γ ⊢ t ∶ A   and   Δ ⊢ σ ∶ Γ   imply   Δ ⊢ t[σ] ∶ A[σ]
--
-- and likewise for types, substitutions and binder arguments.
--
-- At a binder, σ acts on the parameters only (bound variables are
-- locally nameless, so there is nothing to shift). The telescope
-- premise is transported by extending σ with the fresh variables of the
-- opened telescope (`tel-sub`), which needs weakening of σ
-- (CaTTExp.Binder.Rename); the argument premise by commuting opening
-- with substitution; the side condition, argument telescope and result
-- type by BinderLaws. A mark premise is transported by MarkSub; the
-- fresh variable for a marked telescope entry has its marks by MarkVar.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.Subst
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Scoping 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark
open Laws 𝕊

-- Hypotheses on the mark judgment: it is stable under substitution
-- of well-typed terms by well-typed substitutions, and a variable has
-- the marks of its entry (rule (MARK)).
MarkSub : Set
MarkSub = ∀ {Γ Δ σ t A m} → Δ ⊢sub σ ∶ Γ → Γ ⊢tm t ∶ A →
          T (mark Γ m t) → T (mark Δ m (t [ σ ]tm))

MarkVar : Set
MarkVar = ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → T (marksOK Γ (marksAt Γ i) (var i))

module _ (closed : Closed) (laws : BinderLaws)
         (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where

  open BinderLaws laws

  private
    scTyAt : ∀ {m n} A → m ≡ n → T (scTy? m A) → T (scTy? n A)
    scTyAt A refl p = p

  marksOK-sub : ∀ {Γ Δ σ t A} ms → Δ ⊢sub σ ∶ Γ → Γ ⊢tm t ∶ A →
                T (marksOK Γ ms t) → T (marksOK Δ ms (t [ σ ]tm))
  marksOK-sub []       s d _ = tt
  marksOK-sub {Γ} {t = t} (m ∷ ms) s d p =
    let (a , b) = T∧ {mark Γ m t} p in ∧T (msub s d a) (marksOK-sub ms s d b)

  ----------------------------------------------------------------------
  -- Variables.

  lookup-sub : ∀ {Γ Δ σ i A} → Γ ⊢ctx → lookup Γ i ≡ just A →
               Δ ⊢sub σ ∶ Γ → Δ ⊢tm lookupₛ σ i ∶ A [ σ ]ty
  lookup-sub {Γ ▸[ _ ] B} {Δ} {σ ,ₛ s} {i} {A} (▸-wf w b) eq (,-wf sd d _)
    with sub-sc closed laws sd
  ... | (_ , l) with i ==ℕ len Γ in e
  ...   | true  rewrite l | e =
          subst (λ X → Δ ⊢tm s ∶ X [ σ ,ₛ s ]ty) (just-inj eq)
            (subst (Δ ⊢tm s ∶_)
              (sym (ext-ty B σ s (scTyAt B (sym l) (ty-sc closed laws b)))) d)
  ...   | false rewrite l | e =
          subst (Δ ⊢tm lookupₛ σ i ∶_)
            (sym (ext-ty A σ s (scTyAt A (sym l) (snd (ctx-lookup closed laws w eq)))))
            (lookup-sub w eq sd)

  ----------------------------------------------------------------------
  -- The theorem.

  mutual
    tm[] : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[] (var-wf w eq) s = lookup-sub w eq s
    tm[] {Δ = Δ} {σ = σ} (coh-wf {Δ = Θ} {A} {t} {u} {τ} p w a ok sτ) s =
      subst (Δ ⊢tm coh Θ (arr A t u) (τ ∘ σ) ∶_)
        (sym (assoc-ty (arr A t u) τ σ
               (scTyAt (arr A t u) (sym (snd (sub-sc closed laws sτ))) (ty-sc closed laws a))))
        (coh-wf p w a ok (sub∘ w sτ s))
    tm[] {Δ = Δ} {σ = σ} (cst-wf {k} _ v) s =
      subst (Δ ⊢tm cst k ∶_) (sym (closed-ty (ty k) σ (closed k))) (cst-wf (sub-ctx closed laws s) v)
    tm[] {Γ} {Γ′} {σ = σ} (bnd-wf {b} {y} {Δ} {ts} scΔ l wt ok as) s =
      subst (Γ′ ⊢tm bnd b y (Δ [ σ ]tel) (ts ∘ σ) ∶_)
        (trans (cong (opTy 0 (ts ∘ σ)) (res-stable b y Δ σ lσ ok))
               (sym (op-[]ty 0 ts (bres b y Δ) σ lσ)))
        (bnd-wf (sc-tel[] Δ σ (subst (λ n → T (scTel? n Δ)) (sym (snd (sub-sc closed laws s))) scΔ)
                          (fst (sub-sc closed laws s)))
                (lc-tel[] 1 Δ σ l lσ)
                (fst (tel-sub Δ wt s scΔ))
                (side-stable b y Δ σ lσ ok)
                (subst (Γ′ ⊢args ts ∘ σ ∶_) (sym (args-stable b y Δ σ lσ ok)) (args-sub as s)))
      where
      lσ = sub-lc s

    ty[] : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
    ty[] (⋆-wf _)     s = ⋆-wf (sub-ctx closed laws s)
    ty[] (arr-wf d e) s = arr-wf (tm[] d s) (tm[] e s)

    -- Composition of substitutions.
    sub∘ : ∀ {Θ Γ Δ τ σ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
    sub∘ _ (⟨⟩-wf _) s = ⟨⟩-wf (sub-ctx closed laws s)
    sub∘ {Θ ▸[ ms ] A} {Δ = Δ} {τ ,ₛ t} {σ} (▸-wf w a) (,-wf sτ d o) s =
      ,-wf (sub∘ w sτ s)
        (subst (Δ ⊢tm t [ σ ]tm ∶_)
          (assoc-ty A τ σ (scTyAt A (sym (snd (sub-sc closed laws sτ))) (ty-sc closed laws a)))
          (tm[] d s))
        (marksOK-sub ms s d o)

    args-sub : ∀ {Γ Γ′ ts Θ σ} → Γ ⊢args ts ∶ Θ → Γ′ ⊢sub σ ∶ Γ → Γ′ ⊢args ts ∘ σ ∶ Θ [ σ ]tel
    args-sub (⟨⟩-a _) s = ⟨⟩-a (sub-ctx closed laws s)
    args-sub {Γ′ = Γ′} {σ = σ} (,-a {ts} {Θ} {t} {ms} {A} a d o) s =
      ,-a (args-sub a s) (subst (Γ′ ⊢tm t [ σ ]tm ∶_) (op-[]ty 0 ts A σ (sub-lc s)) (tm[] d s))
          (marksOK-sub ms s d o)

    -- A substitution extends under an opened telescope.
    tel-sub : ∀ {Γ Γ′ σ} Δ → (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → Γ′ ⊢sub σ ∶ Γ → T (scTel? (len Γ) Δ) →
              ((Γ′ ⧺ openTel (len Γ′) (Δ [ σ ]tel)) ⊢ctx) ×
              ((Γ′ ⧺ openTel (len Γ′) (Δ [ σ ]tel)) ⊢sub (σ ++ₛ fresh (len Γ′) (len Δ)) ∶ (Γ ⧺ openTel (len Γ) Δ))
    tel-sub ε _ s _ = sub-ctx closed laws s , s
    tel-sub {Γ} {Γ′} {σ} (Δ ▸[ ms ] A) (▸-wf wΞ a) s p =
      subst (λ Z → (((Γ′ ⧺ Ξ′) ▸[ ms ] Z) ⊢ctx) × (((Γ′ ⧺ Ξ′) ▸[ ms ] Z) ⊢sub σ′ ,ₛ var (n′ + k) ∶ ((Γ ⧺ Ξ) ▸[ ms ] X)))
            E (w″ , s″)
      where
      n  = len Γ
      n′ = len Γ′
      k  = len Δ
      Ξ  = openTel n Δ
      Ξ′ = openTel n′ (Δ [ σ ]tel)
      X  = opTy 0 (fresh n k) A
      pΔ = fst (T∧ {scTel? n Δ} p)
      pA = snd (T∧ {scTel? n Δ} p)
      σ′ = σ ++ₛ fresh n′ k
      IH = tel-sub Δ wΞ s pΔ
      w′ : (Γ′ ⧺ Ξ′) ⊢ctx
      w′ = fst IH
      s′ : (Γ′ ⧺ Ξ′) ⊢sub σ′ ∶ (Γ ⧺ Ξ)
      s′ = snd IH
      X′ = X [ σ′ ]ty
      lenσ : lenₛ σ ≡ n
      lenσ = snd (sub-sc closed laws s)
      lσ′ : LC σ′
      lσ′ = lc-++ σ (fresh n′ k) (sub-lc s) (lc-fresh n′ k)
      lenΞ′ : len (Γ′ ⧺ Ξ′) ≡ n′ + k
      lenΞ′ = trans (len-⧺ Γ′ Ξ′) (cong (n′ +_) (trans (len-openTel n′ (Δ [ σ ]tel)) (len-tel[] Δ σ)))

      E : X′ ≡ opTy 0 (fresh n′ (len (Δ [ σ ]tel))) (A [ σ ]ty)
      E = trans (op-[]ty 0 (fresh n k) A σ′ lσ′)
                (cong₂ (opTy 0)
                  (trans (cong (λ m → fresh m k ∘ σ′) (sym lenσ))
                         (trans (fresh-∘ σ n′ k) (cong (fresh n′) (sym (len-tel[] Δ σ)))))
                  (ext-ty-++ A σ (fresh n′ k) (subst (λ m → T (scTy? m A)) (sym lenσ) pA)))

      w″ : ((Γ′ ⧺ Ξ′) ▸[ ms ] X′) ⊢ctx
      w″ = ▸-wf w′ (ty[] a s′)

      top : lookup ((Γ′ ⧺ Ξ′) ▸[ ms ] X′) (n′ + k) ≡ just X′
      top = lookup-top (Γ′ ⧺ Ξ′) {ms} X′ (n′ + k) (==-self (sym lenΞ′))

      s″ : ((Γ′ ⧺ Ξ′) ▸[ ms ] X′) ⊢sub σ′ ,ₛ var (n′ + k) ∶ ((Γ ⧺ Ξ) ▸[ ms ] X)
      s″ = ,-wf (wk-sub closed laws mren wΞ s′ w″)
                (var-wf w″ top)
                (subst (λ ns → T (marksOK ((Γ′ ⧺ Ξ′) ▸[ ms ] X′) ns (var (n′ + k))))
                       (marksAt-top (Γ′ ⧺ Ξ′) ms X′ (n′ + k) (==-self (sym lenΞ′)))
                       (mvar w″ top))
