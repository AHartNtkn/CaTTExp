------------------------------------------------------------------------
-- D7e: admissible goals as substitution instances of templates.
--
-- AdmI Γ A: A is the image of a template goal (c or ε) under a
-- substitution σ with Γ ⊢ σ ∶ ctx t.  Main results (no postulates):
--   * adm→inst      : every generic admissible goal is an instance
--                     (identity substitution);
--   * inst-subst    : instances are closed under well-typed
--                     substitution (composition of substitutions);
--   * inst-typed    : every instance is a well-formed type in Γ
--                     (D7f + the substitution lemma);
--   * inst-dir      : the direction of a directed instance comes from
--                     the instance of b: its top cell goes from σ(u⁻)
--                     to σ(u⁺), σ(b) is a directed cell from σ(β⁻) to
--                     σ(β⁺), and σ(a⁻), σ(a⁺) are invertible collars
--                     from r(σ(u±)) to the collared σ(β±).
-- no-reverse and dir-needs-dir (Templates) hold for generic contexts
-- only.  For instances they fail syntactically (sending b to an
-- identity can make σ(u⁻) = σ(u⁺)), and `here` inhabits every
-- well-formed type, so the absence of reverse cells is a semantic
-- statement (r3, the walking square) and stays on paper.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Instances where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates
open import CaTTExp.Gray.Biclosed.TemplatesTyped
  using (templates-typed; module Fixed)
open import CaTTExp.Gray.Biclosed.Subst

------------------------------------------------------------------------
-- Identity and composition of substitutions

idS : Sub
idS = sub obj var

_⨾_ : Sub → Sub → Sub
σ ⨾ τ = sub (λ i → sF (fo τ) (fo σ i)) (λ i → sT τ (tm σ i))

sF-id : ∀ a → sF obj a ≡ a
sF-id (obj i)  = refl
sF-id (rep s)  = refl
sF-id (a ⊗ b)  = cong₂ _⊗_ (sF-id a) (sF-id b)
sF-id (a \\ b) = cong₂ _\\_ (sF-id a) (sF-id b)
sF-id (a // b) = cong₂ _//_ (sF-id a) (sF-id b)

sFs-id : ∀ as → sFs obj as ≡ as
sFs-id []       = refl
sFs-id (a ∷ as) = cong₂ _∷_ (sF-id a) (sFs-id as)

sM-id : ∀ M → sM obj M ≡ M
sM-id (xs ▸ z) = cong₂ _▸_ (sFs-id xs) (sF-id z)

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

mutual
  sT-id : ∀ x → sT idS x ≡ x
  sT-id (var i)      = refl
  sT-id (mP U V)     = cong₂ mP (sF-id U) (sF-id V)
  sT-id (eL A C)     = cong₂ eL (sF-id A) (sF-id C)
  sT-id (eR A C)     = cong₂ eR (sF-id A) (sF-id C)
  sT-id (pP Δ Θ)     = refl
  sT-id pt           = refl
  sT-id (idt A)      = cong idt (sF-id A)
  sT-id (comp f gs)  = cong₂ comp (sT-id f) (sTs-id gs)
  sT-id (glue a x b) = cong₃ glue (sT-id a) (sT-id x) (sT-id b)
  sT-id (here A)     = cong here (sY-id A)

  sTs-id : ∀ xs → sTs idS xs ≡ xs
  sTs-id []       = refl
  sTs-id (x ∷ xs) = cong₂ _∷_ (sT-id x) (sTs-id xs)

  sY-id : ∀ A → sY idS A ≡ A
  sY-id (op M)          = cong op (sM-id M)
  sY-id (hom m g A s t) =
    trans (cong (λ A′ → hom m g A′ (sT idS s) (sT idS t)) (sY-id A))
          (cong₂ (hom m g A) (sT-id s) (sT-id t))

module Comp (σ τ : Sub) where
  sF-⨾ : ∀ a → sF (fo τ) (sF (fo σ) a) ≡ sF (fo (σ ⨾ τ)) a
  sF-⨾ (obj i)  = refl
  sF-⨾ (rep s)  = refl
  sF-⨾ (a ⊗ b)  = cong₂ _⊗_ (sF-⨾ a) (sF-⨾ b)
  sF-⨾ (a \\ b) = cong₂ _\\_ (sF-⨾ a) (sF-⨾ b)
  sF-⨾ (a // b) = cong₂ _//_ (sF-⨾ a) (sF-⨾ b)

  sFs-⨾ : ∀ as → sFs (fo τ) (sFs (fo σ) as) ≡ sFs (fo (σ ⨾ τ)) as
  sFs-⨾ []       = refl
  sFs-⨾ (a ∷ as) = cong₂ _∷_ (sF-⨾ a) (sFs-⨾ as)

  sM-⨾ : ∀ M → sM (fo τ) (sM (fo σ) M) ≡ sM (fo (σ ⨾ τ)) M
  sM-⨾ (xs ▸ z) = cong₂ _▸_ (sFs-⨾ xs) (sF-⨾ z)

  mutual
    sT-⨾ : ∀ x → sT τ (sT σ x) ≡ sT (σ ⨾ τ) x
    sT-⨾ (var i)      = refl
    sT-⨾ (mP U V)     = cong₂ mP (sF-⨾ U) (sF-⨾ V)
    sT-⨾ (eL A C)     = cong₂ eL (sF-⨾ A) (sF-⨾ C)
    sT-⨾ (eR A C)     = cong₂ eR (sF-⨾ A) (sF-⨾ C)
    sT-⨾ (pP Δ Θ)     = refl
    sT-⨾ pt           = refl
    sT-⨾ (idt A)      = cong idt (sF-⨾ A)
    sT-⨾ (comp f gs)  = cong₂ comp (sT-⨾ f) (sTs-⨾ gs)
    sT-⨾ (glue a x b) = cong₃ glue (sT-⨾ a) (sT-⨾ x) (sT-⨾ b)
    sT-⨾ (here A)     = cong here (sY-⨾ A)

    sTs-⨾ : ∀ xs → sTs τ (sTs σ xs) ≡ sTs (σ ⨾ τ) xs
    sTs-⨾ []       = refl
    sTs-⨾ (x ∷ xs) = cong₂ _∷_ (sT-⨾ x) (sTs-⨾ xs)

    sY-⨾ : ∀ A → sY τ (sY σ A) ≡ sY (σ ⨾ τ) A
    sY-⨾ (op M)          = cong op (sM-⨾ M)
    sY-⨾ (hom m g A s t) =
      trans (cong (λ A′ → hom m g A′ (sT τ (sT σ s)) (sT τ (sT σ t))) (sY-⨾ A))
            (cong₂ (hom m g (sY (σ ⨾ τ) A)) (sT-⨾ s) (sT-⨾ t))

-- typing of identity and composite substitutions
id-typed : ∀ Γ → Γ ⊢ idS ∶ Γ
id-typed Γ = ⊢in λ i A e → subst (λ B → _ ≡ just B) (sym (sY-id A)) e

⨾-typed : ∀ {Θ Γ Δ σ τ} → Γ ⊢ σ ∶ Δ → Θ ⊢ τ ∶ Γ → Θ ⊢ (σ ⨾ τ) ∶ Δ
⨾-typed {σ = σ} {τ} h k = ⊢in λ i A e →
  subst (λ B → _ ≡ just B) (Comp.sY-⨾ σ τ A) (sub-infer k (tm σ i) (sY σ A) (app h i A e))

------------------------------------------------------------------------
-- Admissible instances

data AdmI (Γ : Ctx) (A : CTy) : Set where
  inst-c : (t : Tmpl) → T (okT t) → (σ : Sub) → Γ ⊢ σ ∶ ctx t →
           A ≡ sY σ (cgoal t) → AdmI Γ A
  inst-ε : (t : Tmpl) → T (okT t) → (σ : Sub) → Γ ⊢ σ ∶ ctx t →
           A ≡ sY σ (egoal t) → AdmI Γ A

-- the generic judgement is the identity instance
adm→inst : ∀ {Γ A} → Admissible Γ A → AdmI Γ A
adm→inst (adm-c t ok refl refl) = inst-c t ok idS (id-typed _) (sym (sY-id _))
adm→inst (adm-ε t ok refl refl) = inst-ε t ok idS (id-typed _) (sym (sY-id _))

-- closure under substitution
inst-subst : ∀ {Θ Γ A τ} → AdmI Γ A → Θ ⊢ τ ∶ Γ → AdmI Θ (sY τ A)
inst-subst {τ = τ} (inst-c t ok σ h refl) k =
  inst-c t ok (σ ⨾ τ) (⨾-typed h k) (Comp.sY-⨾ σ τ (cgoal t))
inst-subst {τ = τ} (inst-ε t ok σ h refl) k =
  inst-ε t ok (σ ⨾ τ) (⨾-typed h k) (Comp.sY-⨾ σ τ (egoal t))

-- every instance is a well-formed type
inst-typed : ∀ {Γ A} → AdmI Γ A → T (wf Γ A)
inst-typed (inst-c t _ σ h refl) =
  sub-wf h (cgoal t) (∧-snd {wfCtx (ctx t)} (fst (templates-typed t)))
inst-typed (inst-ε t _ σ h refl) = sub-wf h (egoal t) (snd (templates-typed t))

------------------------------------------------------------------------
-- The direction of a directed instance comes from the instance of b

module _ (ρ : Row) (g k : Nat) where
  private
    t  = tmpl ρ g dir (suc k)
    g′ = rgap ρ g
  open Fixed t using (lookup-at)

  lookup-b : lookup (ctx t) (pos (suc k) 0) ≡ just (tyB t (suc k))
  lookup-b = lookup-at (suc k) (tyB t (suc k) ∷ []) 0

  lookup-top : ∀ o → lookup (ctx t) (pos k o) ≡ lookup (block t k ++ tyB t (suc k) ∷ []) o
  lookup-top o =
    trans (cong (λ Γ → lookup Γ (pos k o))
                (++-assoc (levels t k) (block t k) (tyB t (suc k) ∷ [])))
          (lookup-at k (block t k ++ tyB t (suc k) ∷ []) o)

  inst-dir : ∀ Γ σ → Γ ⊢ σ ∶ ctx t →
      sY σ (cgoal t) ≡ hom dir g (sY σ (tyU t k)) (tm σ (uM k)) (tm σ (uP k))
    × infer Γ (tm σ (pos (suc k) 0))
        ≡ just (hom dir g′ (sY σ (tyB t k)) (tm σ (bM k)) (tm σ (bP k)))
    × infer Γ (tm σ (aM k))
        ≡ just (hom inv g′ (sY σ (tyRU t k)) (sT σ (rmap ρ (var (uM k))))
                                             (sT σ (chain t k (var (bM k)))))
    × infer Γ (tm σ (aP k))
        ≡ just (hom inv g′ (sY σ (tyRU t k)) (sT σ (rmap ρ (var (uP k))))
                                             (sT σ (chain t k (var (bP k)))))
  inst-dir Γ σ h =
    refl ,
    app h (pos (suc k) 0) (tyB t (suc k)) lookup-b ,
    app h (aM k) _ (lookup-top 4) ,
    app h (aP k) _ (lookup-top 5)
