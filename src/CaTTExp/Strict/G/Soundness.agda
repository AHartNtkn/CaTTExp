------------------------------------------------------------------------
-- Soundness in the strict model of two-tier L with a parameterised
-- coherence-case predicate cc (S30; copy of CaTTExp.Strict.Soundness
-- over CaTTExp.Gray.SupportG; the parameterised analogue of Theorem 1(1)
-- of notes/pseudo-vs-gray.md §3.6).
--
-- Every term t : A derivable with side condition SupportG.sideG over a
-- pasting context Γ is a cell of ν(K(Γ)):
--
--     Soundness.sound-tm : PsInv Γ → Γ ⊢tm t ∶ A → IsCellTm Γ t A
--
-- where a coh is interpreted as the image, under the chain map of its
-- substitution, of the total cell T of its pasting context (operation
-- case, stated with closure comparisons) or the identity on its source
-- (cc-case).
--
-- It rests on one hypothesis, `CohSound` (cc forces equal closed
-- supports). In the coherence case, two cells with equal closed supports
-- are equal (`Strict.Recon.b-supp`), so the coh's image is an identity.
-- The operation case uses `Strict.Bridge.T-cell` and `Strict.Recon.b-bdry`
-- as in the original.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Pure using (∅)

module CaTTExp.Strict.G.Soundness
  (cc : Signature.Ctx ∅ → Signature.Ty ∅ → List (List Nat) → List (List Nat) → Bool)
  where

open Signature ∅
open import CaTTExp.Pure using (⟪_⟫)
open import CaTTExp.Gray.SupportG ∅ cc hiding (Tuple)
open import CaTTExp.TypingWith ∅ sideG
open import CaTTExp.PastingTrees ∅
import CaTTExp.Subst ∅ sideG as S


open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.G.Subst cc
open import CaTTExp.Strict.G.L cc
open import CaTTExp.Strict.Hyp public hiding (flat-supp; closed; inv-gr)
open import CaTTExp.Strict.G.Hyp cc using (flat-supp; closed)
open import CaTTExp.Strict.Bridge using (T-cell)
open import CaTTExp.Strict.Recon using (b-supp; b-bdry)

-- The one hypothesis on the coherence-case predicate: it forces the two
-- closed supports to agree. By (B) the two images are then equal.
CohSound : Set
CohSound = ∀ Θ A St Su → T (cc Θ A St Su) → T (sameDownClosure Θ St Su)

module Soundness (hcc : CohSound) where

  -- Composites of 1-cells (the coh's type is a 1-cell type).
  sound-op⋆ : ∀ {Γ Δ t u σ} → Δ ⊢ps → T (sideG Δ ⋆ t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
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

  -- The cell of K(Δ) of which a coh of type t →_A u (A ≠ ⋆) is the
  -- image: T in the operation case, the identity on t in the coherence
  -- case. Exposed for Strict.SuppFV.
  cohX : Ctx → Ty → Tm → Tm → Tower
  cohX Δ A t u = step (towerOf t A) (towerOf u A) (if cohG Δ A t u then [] else topT (homs Δ))

  cohX-cell : ∀ {Δ t u} A₀ a₀ b₀ → Δ ⊢ps → T (sideG Δ (arr A₀ a₀ b₀) t u) →
              ∀ e₁ e₂ → endsV (arr A₀ a₀ b₀) ≡ just (e₁ , e₂) →
              IsCellL Δ e₁ e₂ (dim A₀) (towerOf t (arr A₀ a₀ b₀)) →
              IsCellL Δ e₁ e₂ (dim A₀) (towerOf u (arr A₀ a₀ b₀)) →
              IsCellL Δ e₁ e₂ (dim (arr A₀ a₀ b₀)) (cohX Δ (arr A₀ a₀ b₀) t u)
  cohX-cell {Δ} {t} {u} A₀ a₀ b₀ psΔ ok e₁ e₂ ee cT cU = cellX (cohG Δ A t u) refl
    where
    A = arr A₀ a₀ b₀
    hs = homs Δ
    n = dim A₀
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
    top≈ : ∀ X Y → X ≈w Y → top X ≈ top Y
    top≈ (base c)     (base c')     e           = e
    top≈ (step _ _ c) (step _ _ c') (_ , _ , e) = e
    top≈ (base _)     (step _ _ _)  ()
    top≈ (step _ _ _) (base _)      ()
    cellX : ∀ b → cohG Δ A t u ≡ b → IsCellL Δ e₁ e₂ (dim A) (X₀ b)
    cellX true ec =
      let cc' : T (cc Δ A (supp t A) (supp u A))
          cc' = subst T (sym ec) tt
          eq = b-supp psΔ e₁ e₂ n (towerOf t A) (towerOf u A) (supp t A) (supp u A) cT cU
                      (flat-supp t A₀ a₀ b₀) (flat-supp u A₀ a₀ b₀)
                      (hcc Δ A (supp t A) (supp u A) cc')
      in cT , cU , Par-same t u A₀ a₀ b₀ , top≈ (towerOf t A) (towerOf u A) eq , tt
    cellX false ec =
      let oc = subst (λ b → T (b ∨ opCaseC Δ A t u)) ec ok
          okE = ∧-fst oc
          dA  = ==ℕ-sound (dim A) (dimK hs) (∧-fst (∧-snd {endsOK Δ A} oc))
          rest = ∧-snd {dim A ==ℕ dimK hs} (∧-snd {endsOK Δ A} oc)
          pt = ∧-fst rest
          pu = ∧-snd {sameDownClosure Δ (supp t A) (bdryT false hs)} rest
      in opcell dA (dimK hs) dA (T-cell psΔ A e₁ e₂ okE (endsV→endsTy A ee)) pt pu (topT hs) refl

  -- The coh is the image of cohX under σ.
  cohX-image : ∀ {Γ Δ t u σ} A₀ a₀ b₀ → Γ ⊢sub σ ∶ Δ →
               Δ ⊢tm t ∶ arr A₀ a₀ b₀ → Δ ⊢tm u ∶ arr A₀ a₀ b₀ →
               mapTw (applyF (topsSub σ)) (cohX Δ (arr A₀ a₀ b₀) t u) ≈w
               towerOf (coh Δ (arr (arr A₀ a₀ b₀) t u) σ) (arr (arr A₀ a₀ b₀) t u [ σ ]ty)
  cohX-image {Γ} {Δ} {t} {u} {σ} A₀ a₀ b₀ sσ d e =
    ≈w-sym (towerOf (t [ σ ]tm) (A [ σ ]ty)) _ (tower-sub t A σ sct scA) ,
    ≈w-sym (towerOf (u [ σ ]tm) (A [ σ ]ty)) _ (tower-sub u A σ scu scA) ,
    ≈-refl
    where
    A = arr A₀ a₀ b₀
    lenσ = snd (S.sub-sc closed sσ)
    sct : S.ScTm (lenₛ σ) t
    sct = subst (λ m → S.ScTm m t) (sym lenσ) (S.tm-sc closed d)
    scA : S.ScTy (lenₛ σ) A
    scA = subst (λ m → S.ScTy m A) (sym lenσ) (S.tm-ty-sc closed d)
    scu : S.ScTm (lenₛ σ) u
    scu = subst (λ m → S.ScTm m u) (sym lenσ) (S.tm-sc closed e)

  sound-arr : ∀ {Γ Δ t u σ} → ∀ A₀ a₀ b₀ → Δ ⊢ps →
              T (sideG Δ (arr A₀ a₀ b₀) t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
              Δ ⊢tm t ∶ arr A₀ a₀ b₀ → Δ ⊢tm u ∶ arr A₀ a₀ b₀ →
              IsCellTm Δ t (arr A₀ a₀ b₀) → IsCellTm Δ u (arr A₀ a₀ b₀) →
              IsCellTm Γ (coh Δ (arr (arr A₀ a₀ b₀) t u) σ) (arr (arr A₀ a₀ b₀) t u [ σ ]ty)
  sound-arr {Γ} {Δ} {t} {u} {σ} A₀ a₀ b₀ psΔ ok sσ cellσ d e
            ((e₁ , e₂) , ee , l₁ , l₂ , cT) ((e₁' , e₂') , ee' , _ , _ , cU') =
    let (x' , σx , lx') = cellσ e₁ ⋆ l₁
        (y' , σy , ly') = cellσ e₂ ⋆ l₂
        trΓ = SM.transport-σ e₁ e₂ x' y' (dim A) (cohX Δ A t u) σx σy
                (cohX-cell A₀ a₀ b₀ psΔ ok e₁ e₂ ee cT cU)
        G   = towerOf (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
    in (x' , y') , ends-sub→ A σ ee σx σy , lx' , ly' ,
       subst (λ m → IsCellL Γ x' y' m G) (sym (dim-sub A σ))
         (Cells.IsCell-≈ (∂T Γ) (Basis Γ x' y') (dim A) _ G (cohX-image A₀ a₀ b₀ sσ d e) trΓ)
    where
    A = arr A₀ a₀ b₀
    module SM = SubstMap cellσ (snd (S.sub-sc closed sσ)) (psInv psΔ)
    cU : IsCellL Δ e₁ e₂ (dim A₀) (towerOf u A)
    cU = subst (λ e' → IsCellL Δ (fst e') (snd e') (dim A₀) (towerOf u A)) (just-inj (trans (sym ee') ee)) cU'

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
                T (sideG Δ A t u) → Γ ⊢sub σ ∶ Δ →
                IsCellTm Γ (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv ⋆ psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-op⋆ psΔ ok sσ (sound-sub inv ctxΔ sσ) (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv (arr A₀ a₀ b₀) psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-arr A₀ a₀ b₀ psΔ ok sσ (sound-sub inv ctxΔ sσ) d e
        (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)

