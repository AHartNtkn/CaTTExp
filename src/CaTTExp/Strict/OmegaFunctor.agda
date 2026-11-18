------------------------------------------------------------------------
-- Interpretation commutes with structure-preserving relations (ledger
-- item A3a, general case).
--
-- Φ relates cells of 𝒜 to cells of ℬ. If Φ is functional and preserves
-- sources, targets and composites, then it carries composites of
-- labelled trees (`map-cp`) and hence interpretations of CaTT terms
-- (`fl`): if τ and ρ are Φ-related environments and t denotes a in 𝒜
-- at τ, then t denotes some b in ℬ at ρ with Φ a b. Partial maps (the
-- composite of a tree of trees) are the intended instance, which is
-- why Φ is a relation.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.OmegaFunctor
  (𝕊 : Signature) (𝒜 ℬ : ωCat)
  (MA : Signature.K 𝕊 → ωCat.C 𝒜 → Set) (MB : Signature.K 𝕊 → ωCat.C ℬ → Set)
  (Φ : ωCat.C 𝒜 → ωCat.C ℬ → Set)
  (Φ-src  : ∀ n {x y} → Φ x y → Φ (ωCat.src 𝒜 n x) (ωCat.src ℬ n y))
  (Φ-tgt  : ∀ n {x y} → Φ x y → Φ (ωCat.tgt 𝒜 n x) (ωCat.tgt ℬ n y))
  (Φ-det  : ∀ {x y y′} → Φ x y → Φ x y′ → y ≡ y′)
  (Φ-comp : ∀ n {x y x′ y′} → Φ x y → Φ x′ y′ → ∀ p q →
            Φ (ωCat.comp 𝒜 n x x′ p) (ωCat.comp ℬ n y y′ q))
  (Φ-cst  : ∀ {k a} → MA k a → Σ (ωCat.C ℬ) λ b → MB k b × Φ a b)
  where

open Signature 𝕊
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
import CaTTExp.Strict.OmegaPasting
import CaTTExp.Strict.OmegaEval
private
  module A = ωCat 𝒜
  module B = ωCat ℬ
  module PA = CaTTExp.Strict.OmegaPasting 𝒜
  module PB = CaTTExp.Strict.OmegaPasting ℬ
  module EA = CaTTExp.Strict.OmegaEval 𝕊 𝒜 MA
  module EB = CaTTExp.Strict.OmegaEval 𝕊 ℬ MB

------------------------------------------------------------------------
-- Trees of related labels.

mutual
  data TR : LT A.C → LT B.C → Set where
    tr-node : ∀ {x y r s} → Φ x y → BR r s → TR (node x r) (node y s)

  data BR : Br A.C → Br B.C → Set where
    br-nil  : BR nil nil
    br-cons : ∀ {T U x y r s} → TR T U → Φ x y → BR r s → BR (cons T x r) (cons U y s)

module _ {L : Set} (f : L → A.C) (g : L → B.C) (pw : ∀ w → Φ (f w) (g w)) where
  mutual
    tr-map : ∀ T → TR (mapLT f T) (mapLT g T)
    tr-map (node x r) = tr-node (pw x) (br-map r)

    br-map : ∀ r → BR (mapB f r) (mapB g r)
    br-map nil          = br-nil
    br-map (cons T y r) = br-cons (tr-map T) (pw y) (br-map r)

------------------------------------------------------------------------
-- Composites are carried along.

Φ-dim : ∀ {k x y} → Φ x y → A.src k x ≡ x → B.src k y ≡ y
Φ-dim {k} {x} {y} φ d = sym (Φ-det φ (subst (λ z → Φ z (B.src k y)) d (Φ-src k φ)))

mutual
  map-cp : ∀ {k T U a} → PA.Cp k T a → TR T U → Σ B.C λ b → PB.Cp k U b × Φ a b
  map-cp (PA.cp u) (tr-node φ r) =
    let (b , v , ψ) = map-cpB u φ r in b , PB.cp v , ψ

  map-cpB : ∀ {k x r a y s} → PA.CpB k x r a → Φ x y → BR r s →
            Σ B.C λ b → PB.CpB k y s b × Φ a b
  map-cpB (PA.cnil d) φ br-nil = _ , PB.cnil (Φ-dim φ d) , φ
  map-cpB {k} (PA.ccons ca e cb p) φ (br-cons t ψ r) =
    let (a′ , ca′ , χa) = map-cp ca t
        (b′ , cb′ , χb) = map-cpB cb ψ r
        e′ = Φ-det (subst (λ z → Φ z (B.src k a′)) e (Φ-src k χa)) φ
        q  = Φ-det (subst (λ z → Φ z (B.tgt k a′)) p (Φ-tgt k χa)) (Φ-src k χb)
    in B.comp k a′ b′ q , PB.ccons ca′ e′ cb′ q , Φ-comp k χa χb p q

------------------------------------------------------------------------
-- Interpretations are carried along.

infixl 5 _,ᵣ_
data EnvR : EA.Env → EB.Env → Set where
  []ᵣ  : EnvR EA.[]ₑ EB.[]ₑ
  _,ᵣ_ : ∀ {τ ρ X Y} → EnvR τ ρ → Φ X Y → EnvR (τ EA.,ₑ X) (ρ EB.,ₑ Y)

envR-len : ∀ {τ ρ} → EnvR τ ρ → EA.lenₑ τ ≡ EB.lenₑ ρ
envR-len []ᵣ       = refl
envR-len (r ,ᵣ _) = cong suc (envR-len r)

envR-look : ∀ {τ ρ} → EnvR τ ρ → ∀ i {X} → EA.lookE τ i ≡ just X →
            Σ B.C λ Y → (EB.lookE ρ i ≡ just Y) × Φ X Y
envR-look []ᵣ i ()
envR-look (_,ᵣ_ {τ} {ρ} {X} {Y} r φ) i p rewrite sym (envR-len r) with i ==ℕ EA.lenₑ τ
... | true  = Y , refl , subst (λ Z → Φ Z Y) (just-inj p) φ
  where
  just-inj : ∀ {Z : Set} {a b : Z} → just a ≡ just b → a ≡ b
  just-inj refl = refl
... | false = envR-look r i p

envR-lkd : ∀ {τ ρ X Y} → EnvR τ ρ → Φ X Y → ∀ i → Φ (EA.lkd τ X i) (EB.lkd ρ Y i)
envR-lkd []ᵣ φ i = φ
envR-lkd (_,ᵣ_ {τ} r ψ) φ i rewrite sym (envR-len r) with i ==ℕ EA.lenₑ τ
... | true  = ψ
... | false = envR-lkd r φ i

mutual
  fl : ∀ {τ ρ t a} → EA.Ev τ t a → EnvR τ ρ → Σ B.C λ b → EB.Ev ρ t b × Φ a b
  fl (EA.ev-var {i} p) r = let (Y , q , φ) = envR-look r i p in Y , EB.ev-var q , φ
  fl (EA.ev-coh {Θ} {X = X} s u) r with fls s r
  ... | (ρ′ EB.,ₑ Y) , s′ , (r′ ,ᵣ φ) =
    let pw = envR-lkd (r′ ,ᵣ φ) φ
        (b , u′ , ψ) = map-cp u (tr-map _ _ pw (tr Θ))
    in b , EB.ev-coh s′ u′ , ψ
  fl (EA.ev-cst m) r = let (b , m′ , φ) = Φ-cst m in b , EB.ev-cst m′ , φ

  fls : ∀ {τ ρ σ τ′} → EA.EvS τ σ τ′ → EnvR τ ρ → Σ EB.Env λ ρ′ → EB.EvS ρ σ ρ′ × EnvR τ′ ρ′
  fls EA.evs-nil        r = EB.[]ₑ , EB.evs-nil , []ᵣ
  fls (EA.evs-cons s e) r =
    let (ρ′ , s′ , r′) = fls s r
        (b , e′ , φ)   = fl e r
    in (ρ′ EB.,ₑ b) , EB.evs-cons s′ e′ , (r′ ,ᵣ φ)
