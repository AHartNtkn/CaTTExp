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
-- identity can make σ(u⁻) = σ(u⁺)), so the absence of reverse cells
-- is a semantic statement (r3, the walking square).  Since D7h the
-- instance term is here t e φs ts, which records σ; AdmI still speaks
-- about goal types, as before.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Instances where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates
open import CaTTExp.Gray.Biclosed.TemplatesTyped
  using (templates-typed; module Fixed)
open import CaTTExp.Gray.Biclosed.Subst

open import CaTTExp.Gray.Biclosed.SubstDef public
  using (idS; _⨾_; sF-id; sFs-id; sM-id; sT-id; sTs-id; sY-id; module Comp)

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
inst-typed (inst-c t ok σ h refl) =
  sub-wf h (cgoal t) (∧-snd {wfCtx (ctx t)} (fst (templates-typed t ok)))
inst-typed (inst-ε t ok σ h refl) = sub-wf h (egoal t) (snd (templates-typed t ok))

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
