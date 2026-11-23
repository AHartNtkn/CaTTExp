------------------------------------------------------------------------
-- Completeness of the certified checker for CaTT with binders, for
-- every side condition and every binder interface:
--
--   Γ ⊢ctx            implies  checkCtx f Γ succeeds,
--   Γ ⊢ty A           implies  checkTy f Γ w A succeeds, for every w,
--   Γ ⊢tm t ∶ A       implies  inferTm f Γ w t succeeds,
--   Γ ⊢sub σ ∶ Δ      implies  checkSub f Γ w σ Δ succeeds,
--   Γ ⊢args ts ∶ Θ    implies  checkArgs f Γ w ts Θ succeeds,
--
-- whenever the fuel f is at least the size of the input. With soundness
-- (every success carries a derivation) all five judgments are
-- decidable (`dec-ctx`, `dec-ty`, `dec-tm`, `dec-sub`, `dec-args`).
--
-- Hypotheses, as for CaTTExp.Completeness: equality of constants and
-- of binding formers is reflexive, and `valid?` succeeds on valid
-- constants.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.Completeness
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  (==K-refl : ∀ k → T (Signature._==K_ 𝕊 k k))
  (==B-refl : ∀ b → T (Signature._==B_ 𝕊 b b))
  (valid?-complete : ∀ k → Signature.Valid 𝕊 k → T (is-just (Signature.valid? 𝕊 k)))
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B using (T∧; ∧T; T→≡; sh-fresh)
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.CheckWith 𝕊 side mark

------------------------------------------------------------------------
-- Reflexivity of syntactic equality.

mutual
  ==Ty-refl : ∀ A → T (A ==Ty A)
  ==Ty-refl ⋆           = tt
  ==Ty-refl (arr A t u) = ∧T (==Ty-refl A) (∧T (==Tm-refl t) (==Tm-refl u))

  ==Tm-refl : ∀ t → T (t ==Tm t)
  ==Tm-refl (var i)       = ==ℕ-refl i
  ==Tm-refl (bvar d j)    = ∧T (==ℕ-refl d) (==ℕ-refl j)
  ==Tm-refl (coh Γ A σ)   = ∧T (==Ctx-refl Γ) (∧T (==Ty-refl A) (==Sub-refl σ))
  ==Tm-refl (cst k)       = ==K-refl k
  ==Tm-refl (bnd b y Δ σ) = ∧T (==B-refl b) (∧T (==ℕ-refl y) (∧T (==Ctx-refl Δ) (==Sub-refl σ)))

  ==Ctx-refl : ∀ Γ → T (Γ ==Ctx Γ)
  ==Ctx-refl ε       = tt
  ==Ctx-refl (Γ ▸[ ms ] A) = ∧T (==Ctx-refl Γ) (∧T (==Ms-refl ms) (==Ty-refl A))

  ==Sub-refl : ∀ σ → T (σ ==Sub σ)
  ==Sub-refl ⟨⟩       = tt
  ==Sub-refl (σ ,ₛ t) = ∧T (==Sub-refl σ) (==Tm-refl t)

------------------------------------------------------------------------
-- Uniqueness of types: the term determines its type.

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

tm-unique : ∀ {Γ t A B} → Γ ⊢tm t ∶ A → Γ ⊢tm t ∶ B → A ≡ B
tm-unique (var-wf _ e) (var-wf _ e′)               = just-inj (trans (sym e) e′)
tm-unique (coh-wf _ _ _ _ _) (coh-wf _ _ _ _ _)    = refl
tm-unique (cst-wf _ _) (cst-wf _ _)                = refl
tm-unique (bnd-wf _ _ _ _ _) (bnd-wf _ _ _ _ _)    = refl

------------------------------------------------------------------------
-- Fuel.

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-+ˡ : ∀ a b {f} → a + b ≤ f → a ≤ f
≤-+ˡ zero    b p       = z≤n
≤-+ˡ (suc a) b (s≤s p) = s≤s (≤-+ˡ a b p)

≤-+ʳ : ∀ a b {f} → a + b ≤ f → b ≤ f
≤-+ʳ zero    b p       = p
≤-+ʳ (suc a) b (s≤s p) = ≤-step (≤-+ʳ a b p)

-- Opening with fresh variables preserves size.
private
  size-pick : ∀ n k j t → sizeTm t ≡ 1 → sizeTm (pickOr (fresh n k) j t) ≡ 1
  size-pick n zero    j t e = e
  size-pick n (suc k) j t e with j ==ℕ lenₛ (fresh n k)
  ... | true  = refl
  ... | false = size-pick n k j t e

  mutual
    size-opTy : ∀ d n k A → sizeTy (opTy d (fresh n k) A) ≡ sizeTy A
    size-opTy d n k ⋆ = refl
    size-opTy d n k (arr A t u) =
      cong suc (cong₂ _+_ (cong₂ _+_ (size-opTy d n k A) (size-opTm d n k t)) (size-opTm d n k u))

    size-opTm : ∀ d n k t → sizeTm (opTm d (fresh n k) t) ≡ sizeTm t
    size-opTm d n k (var i) = refl
    size-opTm d n k (bvar e j) with e ==ℕ d
    ... | true  = size-pick n k j (bvar e j) refl
    ... | false = refl
    size-opTm d n k (coh Γ A σ) = cong (λ x → suc (sizeTel Γ + sizeTy A + x)) (size-opSub d n k σ)
    size-opTm d n k (cst c) = refl
    size-opTm d n k (bnd b y Δ σ) rewrite sh-fresh 0 n k =
      cong suc (cong₂ _+_ (size-opTel (suc d) n k Δ) (size-opSub d n k σ))

    size-opTel : ∀ d n k Δ → sizeTel (opTel d (fresh n k) Δ) ≡ sizeTel Δ
    size-opTel d n k ε = refl
    size-opTel d n k (Δ ▸[ _ ] A) = cong suc (cong₂ _+_ (size-opTel d n k Δ) (size-opTy d n k A))

    size-opSub : ∀ d n k σ → sizeSub (opSub d (fresh n k) σ) ≡ sizeSub σ
    size-opSub d n k ⟨⟩ = refl
    size-opSub d n k (σ ,ₛ t) = cong suc (cong₂ _+_ (size-opSub d n k σ) (size-opTm d n k t))

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
  checkCtx-complete : ∀ {Γ} → Γ ⊢ctx → ∀ f → sizeTel Γ ≤ f → Succeeds (checkCtx f Γ)
  checkCtx-complete ε-wf (suc f) _ = tt
  checkCtx-complete {Γ ▸[ _ ] A} (▸-wf w a) (suc f) (s≤s p) =
    bind-ok (checkCtx f Γ) _ (checkCtx-complete w f (≤-+ˡ (sizeTel Γ) (sizeTy A) p)) λ w′ →
    bind-ok (checkTy f Γ w′ A) _ (checkTy-complete a w′ f (≤-+ʳ (sizeTel Γ) (sizeTy A) p)) λ _ → tt

  checkTy-complete : ∀ {Γ A} → Γ ⊢ty A → (w : Γ ⊢ctx) → ∀ f → sizeTy A ≤ f → Succeeds (checkTy f Γ w A)
  checkTy-complete (⋆-wf _) w (suc f) _ = tt
  checkTy-complete {Γ} (arr-wf {A} {t} {u} d e) w (suc f) (s≤s p) =
    bind-ok (inferTm f Γ w t) _
      (inferTm-complete d w f (≤-+ʳ (sizeTy A) (sizeTm t) (≤-+ˡ (sizeTy A + sizeTm t) (sizeTm u) p)))
      λ { (A₁ , d₁) →
    bind-ok (inferTm f Γ w u) _ (inferTm-complete e w f (≤-+ʳ (sizeTy A + sizeTm t) (sizeTm u) p))
      λ { (A₂ , d₂) →
    bind-ok (castTy A₁ A d₁) _ (castTy-ok A₁ A d₁ (tm-unique d₁ d)) λ _ →
    bind-ok (castTy A₂ A d₂) _ (castTy-ok A₂ A d₂ (tm-unique d₂ e)) λ _ → tt } }

  inferTm-complete : ∀ {Γ t A} → Γ ⊢tm t ∶ A → (w : Γ ⊢ctx) → ∀ f → sizeTm t ≤ f →
                     Succeeds (inferTm f Γ w t)
  inferTm-complete {Γ} {var i} (var-wf _ e) w (suc f) _ = inferVar-ok w (lookup Γ i) refl e
  inferTm-complete {Γ} (coh-wf {Δ} {A} {t} {u} {σ} p wΔ a ok s) w (suc f) (s≤s q) =
    bind-ok (checkPs Δ) _ (checkPs-complete {Δ} p) λ _ →
    bind-ok (checkCtx f Δ) _ (checkCtx-complete wΔ f (≤-+ˡ (sizeTel Δ) (sizeTy (arr A t u)) q₁)) λ wΔ′ →
    bind-ok (checkTy f Δ wΔ′ (arr A t u)) _ (checkTy-complete a wΔ′ f (≤-+ʳ (sizeTel Δ) (sizeTy (arr A t u)) q₁)) λ _ →
    guard-ok (side Δ A t u) _ ok λ _ →
    bind-ok (checkSub f Γ w σ Δ) _ (checkSub-complete s w f (≤-+ʳ (sizeTel Δ + sizeTy (arr A t u)) (sizeSub σ) q)) λ _ → tt
    where
    q₁ = ≤-+ˡ (sizeTel Δ + sizeTy (arr A t u)) (sizeSub σ) q
  inferTm-complete (cst-wf {k} _ v) w (suc f) _ =
    bind-ok (valid? k) _ (valid?-complete k v) λ _ → tt
  inferTm-complete {Γ} (bnd-wf {b} {y} {Δ} {ts} sc l wt ok as) w (suc f) (s≤s q) =
    guard-ok (scTel? (len Γ) Δ) _ sc λ _ →
    guard-ok (lcTel? 1 Δ) _ l λ _ →
    bind-ok (checkTel f Γ w Δ) _ (checkTel-complete Δ wt w f (≤-+ˡ (sizeTel Δ) (sizeSub ts) q)) λ _ →
    guard-ok (bside b y Δ) _ ok λ _ →
    bind-ok (checkArgs f Γ w ts (bargs b y Δ)) _
      (checkArgs-complete as w f (≤-+ʳ (sizeTel Δ) (sizeSub ts) q)) λ _ → tt

  checkTel-complete : ∀ {Γ} Δ → (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → (w : Γ ⊢ctx) → ∀ f → sizeTel Δ ≤ f →
                      Succeeds (checkTel f Γ w Δ)
  checkTel-complete ε _ w (suc f) _ = tt
  checkTel-complete {Γ} (Δ ▸[ _ ] A) (▸-wf wΞ a) w (suc f) (s≤s p) =
    bind-ok (checkTel f Γ w Δ) _ (checkTel-complete Δ wΞ w f (≤-+ˡ (sizeTel Δ) (sizeTy A) p)) λ w′ →
    bind-ok (checkTy f (Γ ⧺ openTel (len Γ) Δ) w′ (opTy 0 (fresh (len Γ) (len Δ)) A)) _
      (checkTy-complete a w′ f
        (subst (_≤ f) (sym (size-opTy 0 (len Γ) (len Δ) A)) (≤-+ʳ (sizeTel Δ) (sizeTy A) p))) λ _ → tt

  checkSub-complete : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → (w : Γ ⊢ctx) → ∀ f → sizeSub σ ≤ f →
                      Succeeds (checkSub f Γ w σ Δ)
  checkSub-complete (⟨⟩-wf _) w (suc f) _ = tt
  checkSub-complete {Γ} (,-wf {σ} {Δ} {t} {ms} {A} s d o) w (suc f) (s≤s p) =
    bind-ok (checkSub f Γ w σ Δ) _ (checkSub-complete s w f (≤-+ˡ (sizeSub σ) (sizeTm t) p)) λ _ →
    bind-ok (inferTm f Γ w t) _ (inferTm-complete d w f (≤-+ʳ (sizeSub σ) (sizeTm t) p)) λ { (B , d′) →
    bind-ok (castTy B (A [ σ ]ty) d′) _ (castTy-ok B _ d′ (tm-unique d′ d)) λ _ →
    guard-ok (marksOK Γ ms t) _ o λ _ → tt }

  checkArgs-complete : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → (w : Γ ⊢ctx) → ∀ f → sizeSub ts ≤ f →
                       Succeeds (checkArgs f Γ w ts Θ)
  checkArgs-complete (⟨⟩-a _) w (suc f) _ = tt
  checkArgs-complete {Γ} (,-a {ts} {Θ} {t} {ms} {A} s d o) w (suc f) (s≤s p) =
    bind-ok (checkArgs f Γ w ts Θ) _ (checkArgs-complete s w f (≤-+ˡ (sizeSub ts) (sizeTm t) p)) λ _ →
    bind-ok (inferTm f Γ w t) _ (inferTm-complete d w f (≤-+ʳ (sizeSub ts) (sizeTm t) p)) λ { (B , d′) →
    bind-ok (castTy B (opTy 0 ts A) d′) _ (castTy-ok B _ d′ (tm-unique d′ d)) λ _ →
    guard-ok (marksOK Γ ms t) _ o λ _ → tt }

-- The entry points succeed on well-typed input.
ctx?-complete : ∀ {Γ} → Γ ⊢ctx → Succeeds (ctx? Γ)
ctx?-complete {Γ} w = checkCtx-complete w (sizeTel Γ) (≤-refl _)

infer-complete : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx → Succeeds (infer Γ t)
infer-complete {Γ} {t} d w =
  bind-ok (ctx? Γ) _ (ctx?-complete w) λ w′ → inferTm-complete d w′ (sizeTm t) (≤-refl _)

------------------------------------------------------------------------
-- Decidability of the five judgments.

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

private
  decide : ∀ {P : Set} (m : Maybe P) → (P → Succeeds m) → Dec P
  decide (just p) _ = yes p
  decide nothing  c = no c

dec-ctx : ∀ Γ → Dec (Γ ⊢ctx)
dec-ctx Γ = decide (ctx? Γ) ctx?-complete

dec-ty : ∀ Γ (w : Γ ⊢ctx) A → Dec (Γ ⊢ty A)
dec-ty Γ w A = decide (checkTy (sizeTy A) Γ w A) λ a → checkTy-complete a w (sizeTy A) (≤-refl _)

dec-sub : ∀ Γ (w : Γ ⊢ctx) σ Δ → Dec (Γ ⊢sub σ ∶ Δ)
dec-sub Γ w σ Δ = decide (checkSub (sizeSub σ) Γ w σ Δ) λ s → checkSub-complete s w (sizeSub σ) (≤-refl _)

dec-args : ∀ Γ (w : Γ ⊢ctx) ts Θ → Dec (Γ ⊢args ts ∶ Θ)
dec-args Γ w ts Θ = decide (checkArgs (sizeSub ts) Γ w ts Θ) λ s → checkArgs-complete s w (sizeSub ts) (≤-refl _)

dec-tm : ∀ Γ (w : Γ ⊢ctx) t A → Dec (Γ ⊢tm t ∶ A)
dec-tm Γ w t A = go (inferTm (sizeTm t) Γ w t) (λ d → inferTm-complete d w (sizeTm t) (≤-refl _))
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
