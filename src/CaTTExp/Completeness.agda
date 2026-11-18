------------------------------------------------------------------------
-- Completeness of the certified checker (ledger item A2), for every
-- side condition.
--
--   Γ ⊢ctx          implies  checkCtx Γ succeeds;
--   Γ ⊢ty A         implies  checkTy Γ w A succeeds, for every w;
--   Γ ⊢tm t ∶ A     implies  inferTm Γ w t succeeds, returning type A;
--   Γ ⊢sub σ ∶ Δ    implies  checkSub Γ w σ Δ succeeds.
--
-- Together with soundness (every success carries a derivation) this
-- makes the checker a decision procedure for all four judgments.
--
-- Two hypotheses on the signature, both necessary: the equality test
-- on constants must be reflexive (otherwise the checker cannot
-- recognise a constant's type), and `valid?` must succeed on valid
-- constants. Pure CaTT satisfies both vacuously.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Completeness
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (==K-refl : ∀ k → T (Signature._==K_ 𝕊 k k))
  (valid?-complete : ∀ k → Signature.Valid 𝕊 k → T (is-just (Signature.valid? 𝕊 k)))
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side
open import CaTTExp.CheckWith 𝕊 side
open import CaTTExp.PastingCheck 𝕊 using (checkPs; checkPs-complete)

------------------------------------------------------------------------
-- Reflexivity of syntactic equality.

private
  and3 : ∀ {a b c} → T a → T b → T c → T (a ∧ b ∧ c)
  and3 {true} {true} _ _ c = c

  and2 : ∀ {a b} → T a → T b → T (a ∧ b)
  and2 {true} _ b = b

mutual
  ==Ty-refl : ∀ A → T (A ==Ty A)
  ==Ty-refl ⋆           = tt
  ==Ty-refl (arr A t u) = and3 (==Ty-refl A) (==Tm-refl t) (==Tm-refl u)

  ==Tm-refl : ∀ t → T (t ==Tm t)
  ==Tm-refl (var i)     = ==ℕ-refl i
  ==Tm-refl (coh Γ A σ) = and3 (==Ctx-refl Γ) (==Ty-refl A) (==Sub-refl σ)
  ==Tm-refl (cst k)     = ==K-refl k

  ==Ctx-refl : ∀ Γ → T (Γ ==Ctx Γ)
  ==Ctx-refl ε       = tt
  ==Ctx-refl (Γ ▸ A) = and2 (==Ctx-refl Γ) (==Ty-refl A)

  ==Sub-refl : ∀ σ → T (σ ==Sub σ)
  ==Sub-refl ⟨⟩       = tt
  ==Sub-refl (σ ,ₛ t) = and2 (==Sub-refl σ) (==Tm-refl t)

------------------------------------------------------------------------
-- Uniqueness of types: the term determines its type.

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

tm-unique : ∀ {Γ t A B} → Γ ⊢tm t ∶ A → Γ ⊢tm t ∶ B → A ≡ B
tm-unique (var-wf _ e) (var-wf _ e′)                 = just-inj (trans (sym e) e′)
tm-unique (coh-wf _ _ _ _ _) (coh-wf _ _ _ _ _)      = refl
tm-unique (cst-wf _ _) (cst-wf _ _)                  = refl

------------------------------------------------------------------------
-- Success of the building blocks.

Succeeds : ∀ {a} {A : Set a} → Maybe A → Set
Succeeds m = T (is-just m)

private
  bind-ok : ∀ {a b} {A : Set a} {B : Set b} (m : Maybe A) (f : A → Maybe B) →
            Succeeds m → (∀ x → Succeeds (f x)) → Succeeds (m >>= f)
  bind-ok (just x) f _ k = k x

  guard-ok : ∀ {a} {Z : Set a} b (k : T b → Maybe Z) → T b → (∀ p → Succeeds (k p)) →
             Succeeds (guard b k)
  guard-ok true k _ h = h tt

  castWith-ok : ∀ {Γ t A B} b (e : T b → A ≡ B) (d : Γ ⊢tm t ∶ A) → T b → Succeeds (castWith b e d)
  castWith-ok true _ _ _ = tt

  castTy-ok : ∀ {Γ t} A B (d : Γ ⊢tm t ∶ A) → A ≡ B → Succeeds (castTy A B d)
  castTy-ok A .A d refl = castWith-ok (A ==Ty A) (==Ty-sound A A) d (==Ty-refl A)

  inferVar-ok : ∀ {Γ i A} (w : Γ ⊢ctx) (m : Maybe Ty) (e : lookup Γ i ≡ m) → m ≡ just A →
                Succeeds (inferVar Γ i w m e)
  inferVar-ok w .(just _) e refl = tt

------------------------------------------------------------------------
-- The theorem.

mutual
  checkCtx-complete : ∀ {Γ} → Γ ⊢ctx → Succeeds (checkCtx Γ)
  checkCtx-complete ε-wf = tt
  checkCtx-complete {Γ ▸ A} (▸-wf w a) =
    bind-ok (checkCtx Γ) _ (checkCtx-complete w) λ w′ →
    bind-ok (checkTy Γ w′ A) _ (checkTy-complete a w′) λ _ → tt

  checkTy-complete : ∀ {Γ A} → Γ ⊢ty A → (w : Γ ⊢ctx) → Succeeds (checkTy Γ w A)
  checkTy-complete (⋆-wf _) w = tt
  checkTy-complete {Γ} (arr-wf {A} {t} {u} d e) w =
    bind-ok (inferTm Γ w t) _ (inferTm-complete d w) λ { (A₁ , d₁) →
    bind-ok (inferTm Γ w u) _ (inferTm-complete e w) λ { (A₂ , d₂) →
    bind-ok (castTy A₁ A d₁) _ (castTy-ok A₁ A d₁ (tm-unique d₁ d)) λ _ →
    bind-ok (castTy A₂ A d₂) _ (castTy-ok A₂ A d₂ (tm-unique d₂ e)) λ _ → tt } }

  inferTm-complete : ∀ {Γ t A} → Γ ⊢tm t ∶ A → (w : Γ ⊢ctx) → Succeeds (inferTm Γ w t)
  inferTm-complete {Γ} {var i} (var-wf _ e) w = inferVar-ok w (lookup Γ i) refl e
  inferTm-complete {Γ} (coh-wf {Δ} {A} {t} {u} {σ} p wΔ a ok s) w =
    bind-ok (checkPs Δ) _ (checkPs-complete p) λ _ →
    bind-ok (checkCtx Δ) _ (checkCtx-complete wΔ) λ wΔ′ →
    bind-ok (checkTy Δ wΔ′ (arr A t u)) _ (checkTy-complete a wΔ′) λ _ →
    guard-ok (side Δ A t u) _ ok λ _ →
    bind-ok (checkSub Γ w σ Δ) _ (checkSub-complete s w) λ _ → tt
  inferTm-complete (cst-wf {k} _ v) w =
    bind-ok (valid? k) _ (valid?-complete k v) λ _ → tt

  checkSub-complete : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → (w : Γ ⊢ctx) → Succeeds (checkSub Γ w σ Δ)
  checkSub-complete (⟨⟩-wf _) w = tt
  checkSub-complete {Γ} (,-wf {σ} {Δ} {t} {A} s d) w =
    bind-ok (checkSub Γ w σ Δ) _ (checkSub-complete s w) λ _ →
    bind-ok (inferTm Γ w t) _ (inferTm-complete d w) λ { (B , d′) →
    bind-ok (castTy B (A [ σ ]ty) d′) _ (castTy-ok B _ d′ (tm-unique d′ d)) λ _ → tt }

-- The inferred type is the type of any derivation.
inferTm-type : ∀ {Γ t A B w} {d : Γ ⊢tm t ∶ B} → Γ ⊢tm t ∶ A →
               inferTm Γ w t ≡ just (B , d) → A ≡ B
inferTm-type {d = d} e _ = tm-unique e d

-- Decidability of the four judgments.
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

private
  decide : ∀ {P : Set} (m : Maybe P) → (P → Succeeds m) → Dec P
  decide (just p) _ = yes p
  decide nothing  c = no c

dec-ctx : ∀ Γ → Dec (Γ ⊢ctx)
dec-ctx Γ = decide (checkCtx Γ) checkCtx-complete

dec-ty : ∀ Γ (w : Γ ⊢ctx) A → Dec (Γ ⊢ty A)
dec-ty Γ w A = decide (checkTy Γ w A) λ a → checkTy-complete a w

dec-sub : ∀ Γ (w : Γ ⊢ctx) σ Δ → Dec (Γ ⊢sub σ ∶ Δ)
dec-sub Γ w σ Δ = decide (checkSub Γ w σ Δ) λ s → checkSub-complete s w

dec-tm : ∀ Γ (w : Γ ⊢ctx) t A → Dec (Γ ⊢tm t ∶ A)
dec-tm Γ w t A = go (inferTm Γ w t) (λ d → inferTm-complete d w)
  where
  go : (m : Maybe (Σ Ty (Γ ⊢tm t ∶_))) → (∀ {B} → Γ ⊢tm t ∶ B → Succeeds m) → Dec (Γ ⊢tm t ∶ A)
  go nothing        c = no c
  go (just (B , d)) _ = cast (B ==Ty A) (==Ty-sound B A) λ b≡ → no λ e → b≡ (T-of (sym (tm-unique e d)))
    where
    T-of : B ≡ A → T (B ==Ty A)
    T-of refl = ==Ty-refl B
    cast : (b : Bool) → (T b → B ≡ A) → ((T b → ⊥) → Dec (Γ ⊢tm t ∶ A)) → Dec (Γ ⊢tm t ∶ A)
    cast true  eq _ = yes (subst (Γ ⊢tm t ∶_) (eq tt) d)
    cast false _  k = k λ ()
