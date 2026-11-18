------------------------------------------------------------------------
-- Soundness of CaTT, with constants, in every strict ω-category ν(K)
-- (ledger item A3a).
--
-- K is an arbitrary chain complex with a basis (∂, Bas), and M sends
-- each constant to a tower. If every valid constant k is sent to a cell
-- of ν(K) of dimension dim (ty k) with the boundary ty k prescribes
-- (IsModel), then every derivable t : A, interpreted in an environment
-- of cells with the boundaries their types prescribe, is a cell with
-- the boundary A prescribes:
--
--     sound : IsModel ∂ Bas → Γ ⊢tm t ∶ A → ValidEnv ∂ Bas ρ Γ →
--             IsCell (dim A) ⟦t⟧ρ × Bd ⟦t⟧ρ A ρ
--
-- The proof reduces to the constant-free case (CaTTExp.Strict.CaTT):
-- the source, target and type of a coh over a pasting context are
-- constant-free (CaTTExp.Strict.Purity.pure-side), and a coh's
-- interpretation depends on its substitution only through the
-- environment it produces. Nothing is postulated.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst
open import CaTTExp.Strict.Cell using (Tower)

module CaTTExp.Strict.Sound
  (𝕊 : Signature)
  (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊))
  (M : Signature.K 𝕊 → Tower)
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.PsFacts 𝕊 using (==-refl; ==→≡; lookup-top)
open import CaTTExp.Strict.Interp 𝕊 M
open import CaTTExp.Strict.Dim 𝕊 closed using (dim-[]; just-inj′)
open import CaTTExp.Strict.Purity 𝕊 closed using (pure-side)
open import CaTTExp.Strict.CaTT 𝕊 closed M
  using (ValidEnv; Par-Bd; sound-tm; chain-eq; all-top)
import CaTTExp.Subst 𝕊 cattSide as Sb
open Sb using (ScTy)

------------------------------------------------------------------------
-- The hypothesis on the constants.

IsModel : (Bool → Tuple → Bag) → (Nat → Tuple → Set) → Set
IsModel ∂ Bas = ∀ k → Valid k → Cells.IsCell ∂ Bas (dim (ty k)) (M k) × Bd (M k) (ty k) []ₑ

-- A closed type prescribes the same boundary in every environment.
Bd-closed : ∀ X A ρ → ScTy 0 A → Bd X A []ₑ → Bd X A ρ
Bd-closed X A []ₑ      _  b = b
Bd-closed X A (ρ ,ₑ Y) sc b = Bd-wk X A ρ Y (Sb.scTy-mono (lenₑ ρ) A sc) (Bd-closed X A ρ sc b)

------------------------------------------------------------------------
-- Soundness.

private
  VE : (Bool → Tuple → Bag) → (Nat → Tuple → Set) → Tower → Ty → Env → Set
  VE ∂ Bas X A ρ = Cells.IsCell ∂ Bas (dim A) X × Bd X A ρ

  lookupₑ-top : ∀ ρ X n → lenₑ ρ ≡ n → lookupₑ (ρ ,ₑ X) n ≡ X
  lookupₑ-top ρ X n refl rewrite ==-refl (lenₑ ρ) = refl

  lookupₑ-skip : ∀ ρ X v → (v ==ℕ lenₑ ρ) ≡ false → lookupₑ (ρ ,ₑ X) v ≡ lookupₑ ρ v
  lookupₑ-skip ρ X v e rewrite e = refl

  lookup-skip : ∀ Δ B v → (v ==ℕ len Δ) ≡ false → lookup (Δ ▸ B) v ≡ lookup Δ v
  lookup-skip Δ B v e rewrite e = refl

module _ (∂ : Bool → Tuple → Bag) (Bas : Nat → Tuple → Set) (model : IsModel ∂ Bas) where

  mutual
    sound : ∀ {Γ t A ρ} → Γ ⊢tm t ∶ A → ValidEnv ∂ Bas ρ Γ → VE ∂ Bas (⟦ t ⟧ ρ) A ρ
    sound (var-wf {i} w eq) vρ = vρ i _ eq
    sound {ρ = ρ} (cst-wf {k} _ v) _ =
      let (c , b) = model k v in c , Bd-closed (M k) (ty k) ρ (closed k) b
    sound {Γ} {ρ = ρ} (coh-wf {Δ = Θ} {A = B} {t = s} {u = u} {σ = σ} pΘ@(ps d) wΘ (arr-wf ds du) side sσ) vρ =
      subst (λ m → Cells.IsCell ∂ Bas (suc m) X) (sym (dim-[] B σ)) cell ,
      Bd-[]← X (arr B s u) σ ρ scC (≈w-refl (⟦ s ⟧ ρ′) , ≈w-refl (⟦ u ⟧ ρ′))
      where
      cf = pure-side d ds du side
      cfs = fst (snd cf)
      cfu = snd (snd cf)
      ρ′ = ⟦ σ ⟧ₛ ρ
      X = ⟦ coh Θ (arr B s u) σ ⟧ ρ
      lσ : lenₛ σ ≡ len Θ
      lσ = snd (Sb.sub-sc closed sσ)
      scC : ScTy (lenₛ σ) (arr B s u)
      scC = subst (λ n → ScTy n (arr B s u)) (sym lσ) (Sb.ty-sc closed (arr-wf ds du))
      vρ′ = sound-sub sσ vρ wΘ
      lρ′ : lenₑ ρ′ ≡ len Θ
      lρ′ = trans (lenₑ-⟦⟧ₛ σ ρ) lσ
      S = sound-tm ∂ Bas ds cfs vρ′
      U = sound-tm ∂ Bas du cfu vρ′
      cell : Cells.IsCell ∂ Bas (suc (dim B)) X
      cell = fst S , fst U , Par-Bd (⟦ s ⟧ ρ′) (⟦ u ⟧ ρ′) B ρ′ (snd S) (snd U) ,
             chain-eq ∂ Bas pΘ wΘ ds du cfs cfu side vρ′ lρ′ ,
             all-top ∂ Bas {Θ} {B} vρ′

    sound-sub : ∀ {Γ σ Δ ρ} → Γ ⊢sub σ ∶ Δ → ValidEnv ∂ Bas ρ Γ → Δ ⊢ctx → ValidEnv ∂ Bas (⟦ σ ⟧ₛ ρ) Δ
    sound-sub (⟨⟩-wf _) vρ _ v A ()
    sound-sub {ρ = ρ} (,-wf {σ = σ} {Δ = Δ} {t = t} {A = B} sσ dt) vρ (▸-wf wΔ bB) v A eq =
      split (v ==ℕ len Δ) refl
      where
      ρσ = ⟦ σ ⟧ₛ ρ
      lσ′ : lenₛ σ ≡ len Δ
      lσ′ = snd (Sb.sub-sc closed sσ)
      lσ : lenₑ ρσ ≡ len Δ
      lσ = trans (lenₑ-⟦⟧ₛ σ ρ) lσ′
      IH = sound-sub sσ vρ wΔ
      Tt = sound dt vρ
      split : ∀ b → (v ==ℕ len Δ) ≡ b → VE ∂ Bas (lookupₑ (ρσ ,ₑ ⟦ t ⟧ ρ) v) A (ρσ ,ₑ ⟦ t ⟧ ρ)
      split true e with ==→≡ v (len Δ) e
      ... | refl with just-inj′ (trans (sym eq) (lookup-top Δ B))
      ...   | refl =
        subst (λ Y → VE ∂ Bas Y B (ρσ ,ₑ ⟦ t ⟧ ρ)) (sym (lookupₑ-top ρσ (⟦ t ⟧ ρ) (len Δ) lσ))
          (subst (λ m → Cells.IsCell ∂ Bas m (⟦ t ⟧ ρ)) (dim-[] B σ) (fst Tt) ,
           Bd-wk (⟦ t ⟧ ρ) B ρσ (⟦ t ⟧ ρ)
             (subst (λ m → ScTy m B) (sym lσ) (Sb.ty-sc closed bB))
             (Bd-[]→ (⟦ t ⟧ ρ) B σ ρ (subst (λ m → ScTy m B) (sym lσ′) (Sb.ty-sc closed bB)) (snd Tt)))
      split false e =
        let eqΔ = trans (sym (lookup-skip Δ B v e)) eq
            (c , b) = IH v A eqΔ
            (_ , sc) = Sb.ctx-lookup closed wΔ eqΔ
        in subst (λ Y → VE ∂ Bas Y A (ρσ ,ₑ ⟦ t ⟧ ρ))
             (sym (lookupₑ-skip ρσ (⟦ t ⟧ ρ) v (trans (cong (v ==ℕ_) lσ) e)))
             (c , Bd-wk (lookupₑ ρσ v) A ρσ (⟦ t ⟧ ρ) (subst (λ m → ScTy m A) (sym lσ) sc) b)
