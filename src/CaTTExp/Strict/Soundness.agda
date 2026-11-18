------------------------------------------------------------------------
-- Soundness of two-tier L in its strict model.
--
-- Every derivable term t : A over a pasting context Γ is a cell of
-- ν(K(Γ)), the free strict Gray-enriched category on Γ (hom by hom, the
-- strict ω-category of the Steiner complex λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ):
--
--     sound-tm : PsInv Γ → Γ ⊢tm t ∶ A → IsCellTm Γ t A
--
-- where a coh is interpreted as the image, under the chain map of its
-- substitution, of
--   * the total cell T of its pasting context (operation case), or
--   * the identity on its source (coherence case).
-- This is Theorem 1(1) of notes/pseudo-vs-gray.md §3.6.
--
-- It rests on no hypothesis. The facts about Steiner complexes it uses
-- are theorems:
--  * the table T of the Gray tensor ⟨Θ₁⟩ ⊗ … ⊗ ⟨Θₙ⟩ is a cell
--    (CaTTExp.Strict.Bridge, `T-cell`; also checked by evaluation on 18
--    shapes in CaTTExp.Strict.CheckCells);
--  * in the operation case, a cell in a hom x → y whose downward-closed
--    support (CaTTExp.Gray.Support's `down`) equals that of a boundary
--    ∂^sg T of the total cell T is that boundary (BBdry). This is an
--    instance of "support determines the cell" (BSupp), proved without
--    atoms in CaTTExp.Strict.Recon (`b-supp`, `b-bdry`), following
--    notes/conjectures/answered/steiner-support-formalizable-2026-11-18.md;
--    the literature proof is Hadzihasanovic, arXiv 2404.07273,
--    Prop. 8.3.17 and Thm 11.2.18;
--  * in the coherence case, two cells whose supports both equal T's
--    have equal top chains (CaTTExp.Strict.CohCase, `coh-top`).
------------------------------------------------------------------------
module CaTTExp.Strict.Soundness where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst
open import CaTTExp.Strict.L
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Subst ∅ graySide as S
import CaTTExp.Gray.Graded ∅ as Gr

open import CaTTExp.Strict.Hyp public
open import CaTTExp.Strict.Bridge using (T-cell)
open import CaTTExp.Strict.CohCase using (coh-top)
open import CaTTExp.Strict.Recon using (b-bdry)

module Soundness where

  -- Composites of 1-cells (the coh's type is a 1-cell type).
  sound-op⋆ : ∀ {Γ Δ t u σ} → Δ ⊢ps → T (graySide Δ ⋆ t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
              IsCellTm Δ t ⋆ → IsCellTm Δ u ⋆ →
              IsCellTm Γ (coh Δ (arr ⋆ t u) σ) (arr ⋆ t u [ σ ]ty)
  sound-op⋆ {Γ} {Δ} {σ = σ} psΔ ok sσ cellσ (i , refl , li) (j , refl , lj) =
    let (i' , σi , li') = cellσ i ⋆ li
        (j' , σj , lj') = cellσ j ⋆ lj
        d0 : dimK hs ≡ 0
        d0 = ==ℕ-sound (dimK hs) 0 (∧-fst ok)
        cT = T-cell psΔ (arr ⋆ (var i) (var j)) i j (∧-snd {dimK hs ==ℕ 0} ok) refl
        tr = SM.transport-σ i j i' j' (dimK hs) (twT hs true (dimK hs)) σi σj cT
        tr0 = subst (λ m → IsCellL Γ i' j' m (mapTw (applyF (topsSub σ)) (twT hs true m))) d0 tr
    in (i' , j') , ends-sub→ (arr ⋆ (var i) (var j)) σ refl σi σj , li' , lj' ,
       subst (λ m → IsCellL Γ i' j' 0 (base (applyF (topsSub σ) (chainT true m hs)))) (sym d0) tr0
    where
    hs = homs Δ
    module SM = SubstMap cellσ (snd (S.sub-sc closed sσ)) (psInv psΔ)

  sound-arr : ∀ {Γ Δ t u σ} → ∀ A₀ a₀ b₀ → Δ ⊢ps →
              T (graySide Δ (arr A₀ a₀ b₀) t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
              Δ ⊢tm t ∶ arr A₀ a₀ b₀ → Δ ⊢tm u ∶ arr A₀ a₀ b₀ →
              IsCellTm Δ t (arr A₀ a₀ b₀) → IsCellTm Δ u (arr A₀ a₀ b₀) →
              IsCellTm Γ (coh Δ (arr (arr A₀ a₀ b₀) t u) σ) (arr (arr A₀ a₀ b₀) t u [ σ ]ty)
  sound-arr {Γ} {Δ} {t} {u} {σ} A₀ a₀ b₀ psΔ ok sσ cellσ d e
            ((e₁ , e₂) , ee , l₁ , l₂ , cT) ((e₁' , e₂') , ee' , _ , _ , cU') =
    let (x' , σx , lx') = cellσ e₁ ⋆ l₁
        (y' , σy , ly') = cellσ e₂ ⋆ l₂
        trΓ = SM.transport-σ e₁ e₂ x' y' (dim A) (X₀ (cohCase Δ A t u)) σx σy
                (cellX (cohCase Δ A t u) refl)
        G   = towerOf (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
        Geq : mapTw (applyF (topsSub σ)) (X₀ (cohCase Δ A t u)) ≈w G
        Geq = ≈w-sym (towerOf (t [ σ ]tm) (A [ σ ]ty)) _ (tower-sub t A σ sct scA) ,
              ≈w-sym (towerOf (u [ σ ]tm) (A [ σ ]ty)) _ (tower-sub u A σ scu scA) ,
              ≈-refl
    in (x' , y') , ends-sub→ A σ ee σx σy , lx' , ly' ,
       subst (λ m → IsCellL Γ x' y' m G) (sym (dim-sub A σ))
         (Cells.IsCell-≈ (∂T Γ) (Basis Γ x' y') (dim A) _ G Geq trΓ)
    where
    A = arr A₀ a₀ b₀
    hs = homs Δ
    n = dim A₀
    lenσ = snd (S.sub-sc closed sσ)
    module SM = SubstMap cellσ lenσ (psInv psΔ)
    module HD = Gr.PsSide Δ (inv-gr (psInv psΔ)) A₀ a₀ b₀ t u
    sct : S.ScTm (lenₛ σ) t
    sct = subst (λ m → S.ScTm m t) (sym lenσ) (S.tm-sc closed d)
    scA : S.ScTy (lenₛ σ) A
    scA = subst (λ m → S.ScTy m A) (sym lenσ) (S.tm-ty-sc closed d)
    scu : S.ScTm (lenₛ σ) u
    scu = subst (λ m → S.ScTm m u) (sym lenσ) (S.tm-sc closed e)
    cU : IsCellL Δ e₁ e₂ n (towerOf u A)
    cU = subst (λ e' → IsCellL Δ (fst e') (snd e') n (towerOf u A)) (just-inj (trans (sym ee') ee)) cU'
    X₀ : Bool → Tower
    X₀ b = step (towerOf t A) (towerOf u A) (if b then [] else topT hs)
    opcell : suc n ≡ dimK hs → ∀ m → suc n ≡ m → IsCellL Δ e₁ e₂ m (twT hs true m) →
             T (≈T (down Δ (supp t A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT false (m ∸ 1) hs))) →
             T (≈T (down Δ (supp u A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT true (m ∸ 1) hs))) →
             ∀ C → C ≡ chainT true m hs → IsCellL Δ e₁ e₂ (suc n) (step (towerOf t A) (towerOf u A) C)
    opcell sn .(suc n) refl cTT pt pu C refl =
      let c₋ = fst cTT
          c₊ = fst (snd cTT)
          et = b-bdry psΔ e₁ e₂ n false (towerOf t A) (supp t A) sn cT c₋ (flat-supp t A₀ a₀ b₀) pt
          eu = b-bdry psΔ e₁ e₂ n true (towerOf u A) (supp u A) sn cU c₊ (flat-supp u A₀ a₀ b₀) pu
      in Cells.IsCell-≈ (∂T Δ) (Basis Δ e₁ e₂) (suc n) (twT hs true (suc n)) _
           (≈w-sym (towerOf t A) _ et , ≈w-sym (towerOf u A) _ eu , ≈-refl) cTT
    cellX : ∀ b → cohCase Δ A t u ≡ b → IsCellL Δ e₁ e₂ (dim A) (X₀ b)
    cellX true ec =
      let cc = subst T (sym ec) tt
          pt = HD.coh-t (∧-fst (∧-snd {endsOK Δ A} cc))
          pu = HD.coh-u (∧-snd {sameDown Δ (supp t A) (fullT hs)} (∧-snd {endsOK Δ A} cc))
      in cT , cU , Par-same t u A₀ a₀ b₀ ,
         coh-top psΔ A₀ a₀ b₀ t u e₁ e₂ (∧-fst cc) ee cT cU pt pu , tt
    cellX false ec =
      let oc = subst (λ b → T (b ∨ opCase Δ A t u)) ec ok
          okE = ∧-fst oc
          dA  = ==ℕ-sound (dim A) (dimK hs) (∧-fst (∧-snd {endsOK Δ A} oc))
          rest = ∧-snd {dim A ==ℕ dimK hs} (∧-snd {endsOK Δ A} oc)
          pt = HD.op-t (∧-fst rest)
          pu = HD.op-u (∧-snd {sameDown Δ (supp t A) (bdryT false hs)} rest)
      in opcell dA (dimK hs) dA (T-cell psΔ A e₁ e₂ okE (endsV→endsTy A ee)) pt pu (topT hs) refl

  mutual
    sound-tm : ∀ {Γ t A} → PsInv Γ → Γ ⊢tm t ∶ A → IsCellTm Γ t A
    sound-tm inv (var-wf _ eq) = var-cell inv _ _ eq
    sound-tm inv (coh-wf {A = A} psΔ ctxΔ tyΔ ok sσ) = sound-coh inv A psΔ ctxΔ tyΔ ok sσ
    sound-tm inv (cst-wf {()} _ _)

    sound-ty : ∀ {Γ A t u} → PsInv Γ → Γ ⊢ty arr A t u → IsCellTm Γ t A × IsCellTm Γ u A
    sound-ty inv (arr-wf d e) = sound-tm inv d , sound-tm inv e

    sound-sub : ∀ {Γ σ Δ} → PsInv Γ → Δ ⊢ctx → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ
    sound-sub inv ε-wf (⟨⟩-wf _) v B ()
    sound-sub {Γ} inv (▸-wf {Δ} {A} w a) (,-wf {σ} {_} {t} sσ d) v B eq with S.sub-sc closed sσ
    ... | (_ , l) with v ==ℕ len Δ in e
    ...   | true rewrite l | e =
      subst (λ X → IsCellTm Γ t (X [ σ ,ₛ t ]ty)) (just-inj eq)
        (subst (IsCellTm Γ t)
          (sym (S.ext-ty A σ t (subst (λ n → S.ScTy n A) (sym l) (S.ty-sc closed a))))
          (sound-tm inv d))
    ...   | false rewrite l | e =
      subst (IsCellTm Γ (lookupₛ σ v))
        (sym (S.ext-ty B σ t (subst (λ n → S.ScTy n B) (sym l) (snd (S.ctx-lookup closed w eq)))))
        (sound-sub inv w sσ v B eq)

    sound-coh : ∀ {Γ Δ t u σ} → PsInv Γ → ∀ A → Δ ⊢ps → Δ ⊢ctx → Δ ⊢ty arr A t u →
                T (graySide Δ A t u) → Γ ⊢sub σ ∶ Δ →
                IsCellTm Γ (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv ⋆ psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-op⋆ psΔ ok sσ (sound-sub inv ctxΔ sσ) (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv (arr A₀ a₀ b₀) psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-arr A₀ a₀ b₀ psΔ ok sσ (sound-sub inv ctxΔ sσ) d e
        (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)

