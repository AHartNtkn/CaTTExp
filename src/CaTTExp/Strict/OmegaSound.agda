------------------------------------------------------------------------
-- Soundness of CaTT, with constants, in every strict ω-category
-- (ledger item A3a, general case).
--
-- 𝒞 is any strict ω-category (CaTTExp.Strict.Omega) and M sends each
-- constant to a cell of 𝒞. If every valid constant k is sent to a cell
-- of dimension ≤ dim (ty k) with the boundary ty k prescribes, then
-- every derivable t : A, interpreted in an environment of cells with
-- the boundaries their types prescribe, denotes a cell with the
-- boundary A prescribes (`sound-in`):
--
--     Γ ⊢tm t ∶ A → ValidEnv ρ Γ → Σ c. Ev ρ t c × Dim≤ (dim A) c × Bd c A ρ
--
-- The interpretation is a relation (CaTTExp.Strict.OmegaEval), since
-- composition in 𝒞 is partial, and it is deterministic, so this says
-- that ⟦t⟧ρ is defined and well typed.
--
-- The proof follows the outside answer
-- (notes/conjectures/answered/strict-omega-pasting-formal-2026-11-18.md).
-- A coh over Θ denotes the composite of the tree of Θ labelled by its
-- substitution's environment, which exists (CaTTExp.Strict.PsComposite).
-- Its boundaries are computed in the free model 𝒯 of trees of
-- variables: there the sides s and u of the coh, which are constant-free
-- (CaTTExp.Strict.Purity), denote the boundaries of tr Θ
-- (CaTTExp.Strict.Key), and the functor lemma (CaTTExp.Strict.
-- OmegaFree) carries this to 𝒞. The free-model step calls soundness
-- itself, in 𝒯, on the sub-derivations of s and u, so `sound` takes the
-- model as an argument. Nothing is postulated.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst

module CaTTExp.Strict.OmegaSound
  (𝕊 : Signature) (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊))
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Pasting 𝕊 using (ps)
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
open import CaTTExp.Strict.PsFacts 𝕊 using (ps-facts; ord; shape; dang; lookup-<; lookup-top; ==→≡)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)
open import CaTTExp.Strict.ConstFree 𝕊 using (CFTm; CFSub)
open import CaTTExp.Strict.Purity 𝕊 closed using (pure-side)
open import CaTTExp.Strict.GenericEnv 𝕊 using (𝒯; M𝒯; η; η-valid)
open import CaTTExp.Strict.Key 𝕊 closed using (key)
import CaTTExp.Strict.OmegaEval
import CaTTExp.Strict.OmegaFree
import CaTTExp.Strict.PsComposite
import CaTTExp.Subst 𝕊 cattSide as Sb
open Sb using (ScTy)

------------------------------------------------------------------------
-- Which constants a term uses.

mutual
  CK : (K → Set) → Tm → Set
  CK P (var _)     = ⊤
  CK P (coh _ _ σ) = CKS P σ
  CK P (cst k)     = P k

  CKS : (K → Set) → Sub → Set
  CKS P ⟨⟩       = ⊤
  CKS P (σ ,ₛ t) = CKS P σ × CK P t

mutual
  cf→ck : ∀ {P} t → CFTm t → CK P t
  cf→ck (var _)     _        = tt
  cf→ck (coh _ _ σ) (_ , cs) = cfs→cks σ cs
  cf→ck (cst _)     ()

  cfs→cks : ∀ {P} σ → CFSub σ → CKS P σ
  cfs→cks ⟨⟩       _        = tt
  cfs→cks (σ ,ₛ t) (cs , c) = cfs→cks σ cs , cf→ck t c

mutual
  ck-⊤ : ∀ t → CK (λ _ → ⊤) t
  ck-⊤ (var _)     = tt
  ck-⊤ (coh _ _ σ) = cks-⊤ σ
  ck-⊤ (cst _)     = tt

  cks-⊤ : ∀ σ → CKS (λ _ → ⊤) σ
  cks-⊤ ⟨⟩       = tt
  cks-⊤ (σ ,ₛ t) = cks-⊤ σ , ck-⊤ t

------------------------------------------------------------------------
-- Models: a strict ω-category, a deterministic choice of cells for
-- constants, and the constants (Ok) known to denote well-typed cells.

record Model : Set₁ where
  field
    𝒞     : ωCat
    Mk    : K → ωCat.C 𝒞 → Set
    mdet  : CaTTExp.Strict.OmegaEval.Mk-det 𝕊 𝒞 Mk
    Ok    : K → Set
    model : ∀ k → Valid k → Ok k →
            Σ (ωCat.C 𝒞) λ c → Mk k c × CaTTExp.Strict.OmegaEval.VE 𝕊 𝒞 Mk c (ty k)
                                          (CaTTExp.Strict.OmegaEval.[]ₑ)
open Model

module OE (𝔐 : Model) = CaTTExp.Strict.OmegaEval 𝕊 (𝒞 𝔐) (Mk 𝔐)

-- The free model, with no constants.
𝔗 : Model
𝔗 = record { 𝒞 = 𝒯 ; Mk = M𝒯 ; mdet = λ () ; Ok = λ _ → ⊥ ; model = λ k v () }

------------------------------------------------------------------------
-- Facts about one model.

module Facts (𝔐 : Model) where
  open ωCat (𝒞 𝔐)
  open Basics (𝒞 𝔐)
  open OE 𝔐

  private
    ==-r : ∀ n → (n ==ℕ n) ≡ true
    ==-r zero    = refl
    ==-r (suc n) = ==-r n

    just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
    just-inj refl = refl

    <s-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
    <s-≢ zero    zero    _ ()
    <s-≢ zero    (suc n) _ _ = tt
    <s-≢ (suc i) zero    () _
    <s-≢ (suc i) (suc n) p q = <s-≢ i n p q

    <s-≢′ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
    <s-≢′ zero    (suc n) _ = refl
    <s-≢′ (suc i) (suc n) p = <s-≢′ i n p

    lookE-< : ∀ ρ i {c} → lookE ρ i ≡ just c → T (i <ℕ lenₑ ρ)
    lookE-< []ₑ      i ()
    lookE-< (ρ ,ₑ X) i p with i ==ℕ lenₑ ρ in e
    ... | true  rewrite ==→≡ i (lenₑ ρ) e = n<s (lenₑ ρ)
      where
      n<s : ∀ n → T (n <ℕ suc n)
      n<s zero    = tt
      n<s (suc n) = n<s n
    ... | false = <s i (lenₑ ρ) (lookE-< ρ i p)
      where
      <s : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
      <s zero    (suc n) _ = tt
      <s (suc i) (suc n) q = <s i n q

  -- Lookup with a default agrees with lookup where the latter is defined.
  lookE→lkd : ∀ ρ d v {c} → lookE ρ v ≡ just c → lkd ρ d v ≡ c
  lookE→lkd []ₑ      d v ()
  lookE→lkd (ρ ,ₑ X) d v p with v ==ℕ lenₑ ρ
  ... | true  = just-inj p
  ... | false = lookE→lkd ρ d v p

  lkd-default : ∀ ρ d d′ v → T (v <ℕ lenₑ ρ) → lkd ρ d v ≡ lkd ρ d′ v
  lkd-default []ₑ      d d′ v ()
  lkd-default (ρ ,ₑ X) d d′ v l with v ==ℕ lenₑ ρ in e
  ... | true  = refl
  ... | false = lkd-default ρ d d′ v (<s-≢ v (lenₑ ρ) l e)

  -- A closed type prescribes the same boundary in every environment.
  Bd-closed : ∀ c A ρ → Bd c A []ₑ → Bd c A ρ
  Bd-closed c A []ₑ      b = b
  Bd-closed c A (ρ ,ₑ X) b = Bd-wk c A ρ X (Bd-closed c A ρ b)

  lookE-top : ∀ ρ X n → lenₑ ρ ≡ n → lookE (ρ ,ₑ X) n ≡ just X
  lookE-top ρ X n refl rewrite ==-r (lenₑ ρ) = refl

  lookE-skip : ∀ ρ X v → (v ==ℕ lenₑ ρ) ≡ false → lookE (ρ ,ₑ X) v ≡ lookE ρ v
  lookE-skip ρ X v e rewrite e = refl

  lookup-skip : ∀ Δ B v → (v ==ℕ len Δ) ≡ false → lookup (Δ ▸ B) v ≡ lookup Δ v
  lookup-skip Δ B v e rewrite e = refl

  -- Extending a valid environment by a valid cell.
  valid-ext : ∀ {Γ Δ B σ ρ ρσ c} → Γ ⊢sub σ ∶ Δ → Δ ⊢ctx → Δ ⊢ty B → EvS ρ σ ρσ →
              ValidEnv ρσ Δ → VE c (B [ σ ]ty) ρ → ValidEnv (ρσ ,ₑ c) (Δ ▸ B)
  valid-ext {Γ} {Δ} {B} {σ} {ρ} {ρσ} {c} sσ wΔ bB es vσ (dc , bc) v A eq = split (v ==ℕ len Δ) refl
    where
    lσ′ : lenₛ σ ≡ len Δ
    lσ′ = snd (Sb.sub-sc closed sσ)
    lσ : lenₑ ρσ ≡ len Δ
    lσ = trans (lenₑ-EvS es) lσ′
    split : ∀ b → (v ==ℕ len Δ) ≡ b → Σ C λ c′ → (lookE (ρσ ,ₑ c) v ≡ just c′) × VE c′ A (ρσ ,ₑ c)
    split true e with ==→≡ v (len Δ) e
    ... | refl with just-inj (trans (sym eq) (lookup-top Δ B))
    ...   | refl =
      c , lookE-top ρσ c (len Δ) lσ ,
      subst (λ m → Dim≤ m c) (dim-[] B σ) dc ,
      Bd-wk c B ρσ c (Bd-[]→ (mdet 𝔐) c B es (subst (λ m → ScTy m B) (sym lσ′) (Sb.ty-sc closed bB)) bc)
    split false e =
      let eqΔ = trans (sym (lookup-skip Δ B v e)) eq
          (c′ , lk , dc′ , bc′) = vσ v A eqΔ
      in c′ , trans (lookE-skip ρσ c v (trans (cong (v ==ℕ_) lσ) e)) lk , dc′ , Bd-wk c′ A ρσ c bc′

------------------------------------------------------------------------
-- The coh case, given the free-model interpretations of its sides.

module Coh (𝔐 : Model) where
  open ωCat (𝒞 𝔐)
  open Basics (𝒞 𝔐)
  open OE 𝔐
  open Facts 𝔐
  module E𝒯 = OE 𝔗

  private
    abs0 : ∀ z → T (z <ℕ 0) → ⊥
    abs0 zero    ()
    abs0 (suc z) ()

  coh-case : ∀ {Γ Θ z B s u σ ρ} (d : Θ ⊢ps z ∶ ⋆) → Θ ⊢tm s ∶ B → Θ ⊢tm u ∶ B →
             T (cattSide Θ B s u) → Γ ⊢sub σ ∶ Θ →
             ∀ ρ′ → EvS ρ σ ρ′ → ValidEnv ρ′ Θ → lenₑ ρ′ ≡ len Θ →
             (Σ (LT Nat) λ X → E𝒯.Ev (η Θ) s X × E𝒯.VE X B (η Θ)) →
             (Σ (LT Nat) λ X → E𝒯.Ev (η Θ) u X × E𝒯.VE X B (η Θ)) →
             Σ C λ c → Ev ρ (coh Θ (arr B s u) σ) c × VE c (arr B s u [ σ ]ty) ρ
  coh-case {Θ = Θ} {z} d ds du side sσ []ₑ es vρ′ l _ _ =
    ⊥-elim (abs0 z (subst (λ n → T (z <ℕ n)) (sym l) (lookup-< Θ z (dang (ps-facts d)))))
  coh-case {Γ} {Θ} {z} {B} {s} {u} {σ} {ρ} d ds du side sσ (ρ″ ,ₑ X₀) es vρ′ l
           (Xs , evs , ves) (Xu , evu , veu) =
    c , ev-coh es cpc ,
    subst (λ m → Dim≤ (suc m) c) (sym (dim-[] B σ)) dimc ,
    Bd-[]← c (arr B s u) es (ev-s , ev-u)
    where
    ρ′ = ρ″ ,ₑ X₀
    λ′ = lkd ρ′ X₀
    module F = CaTTExp.Strict.OmegaFree 𝕊 (𝒞 𝔐) (Mk 𝔐) λ′
    module P = CaTTExp.Strict.PsComposite 𝕊 (𝒞 𝔐) (Mk 𝔐) λ′
    o  = ord (ps-facts d)
    sh = shape (ps-facts d)
    k  = dim B
    Tr = tr Θ

    bdl : ∀ x A → PsTy A → Bd x A ρ′ → F.BdL x A
    bdl x ⋆                       ⋆ₚ       _                        = tt
    bdl x (arr A (var a) (var b)) (arrₚ _) (ev-var qa , ev-var qb) =
      sym (lookE→lkd ρ′ X₀ a qa) , sym (lookE→lkd ρ′ X₀ b qb)

    good : F.Good Θ
    good v A p =
      let (c′ , lk , dc , bc) = vρ′ v A p
          e = lookE→lkd ρ′ X₀ v lk
      in subst (Dim≤ (dim A)) (sym e) dc , subst (λ y → F.BdL y A) (sym e) (bdl c′ A (sh v A p) bc)

    ex = P.comp-ex d good
    c = fst ex
    cpc : F.Φ Tr c
    cpc = snd ex

    agree : ∀ v → T (v <ℕ len Θ) → lkd ρ′ (λ′ 0) v ≡ λ′ v
    agree v lt = lkd-default ρ′ (λ′ 0) X₀ v (subst (λ n → T (v <ℕ n)) (sym l) lt)

    R : F.EnvR (η Θ) ρ′
    R = F.η-R {Θ} o sh good ρ′ l (λ v A q → q) agree

    K3 = key d ds du side evs ves evu veu

    ev-s : Ev ρ′ s (src k c)
    ev-s = let (b , e , φ) = F.fl evs R
           in subst (Ev ρ′ s) (F.Φ-det (subst (λ X → F.Φ X b) (fst K3) φ) (F.Φ-src k cpc)) e

    ev-u : Ev ρ′ u (tgt k c)
    ev-u = let (b , e , φ) = F.fl evu R
           in subst (Ev ρ′ u) (F.Φ-det (subst (λ X → F.Φ X b) (fst (snd K3)) φ) (F.Φ-tgt k cpc)) e

    dimc : Dim≤ (suc k) c
    dimc = F.Φ-det (subst (λ X → F.Φ X (src (suc k) c)) (snd (snd K3)) (F.Φ-src (suc k) cpc)) cpc

------------------------------------------------------------------------
-- Soundness in any model.

Res : (𝔐 : Model) → OE.Env 𝔐 → Tm → Ty → Set
Res 𝔐 ρ t A = Σ (ωCat.C (𝒞 𝔐)) λ c → OE.Ev 𝔐 ρ t c × OE.VE 𝔐 c A ρ

mutual
  sound : ∀ 𝔐 {Γ t A ρ} → Γ ⊢tm t ∶ A → CK (Ok 𝔐) t → OE.ValidEnv 𝔐 ρ Γ → Res 𝔐 ρ t A
  sound 𝔐 (var-wf {i} {A} w eq) _ vρ =
    let (c , lk , ve) = vρ i A eq in c , OE.ev-var {𝔐} lk , ve
  sound 𝔐 {ρ = ρ} (cst-wf {k} _ v) ok _ =
    let (c , m , dc , bc) = model 𝔐 k v ok in c , OE.ev-cst {𝔐} m , dc , Facts.Bd-closed 𝔐 c (ty k) ρ bc
  sound 𝔐 (coh-wf {Δ = Θ} {A = B} {t = s} {u = u} {σ = σ} (ps d) wΘ (arr-wf ds du) side sσ) ck vρ =
    let (ρ′ , es , vρ′) = sound-sub 𝔐 sσ ck vρ wΘ
        lσ = snd (Sb.sub-sc closed sσ)
        (_ , cfs , cfu) = pure-side d ds du side
        o = ord (ps-facts d)
        sh = shape (ps-facts d)
    in Coh.coh-case 𝔐 d ds du side sσ ρ′ es vρ′ (trans (OE.lenₑ-EvS 𝔐 es) lσ)
         (sound 𝔗 ds (cf→ck s cfs) (η-valid o sh))
         (sound 𝔗 du (cf→ck u cfu) (η-valid o sh))

  sound-sub : ∀ 𝔐 {Γ σ Δ ρ} → Γ ⊢sub σ ∶ Δ → CKS (Ok 𝔐) σ → OE.ValidEnv 𝔐 ρ Γ → Δ ⊢ctx →
              Σ (OE.Env 𝔐) λ ρ′ → OE.EvS 𝔐 ρ σ ρ′ × OE.ValidEnv 𝔐 ρ′ Δ
  sound-sub 𝔐 (⟨⟩-wf _) _ vρ _ = OE.[]ₑ {𝔐} , OE.evs-nil {𝔐} , λ v A ()
  sound-sub 𝔐 (,-wf sσ dt) (ck , ct) vρ (▸-wf wΔ bB) =
    let (ρσ , es , vσ) = sound-sub 𝔐 sσ ck vρ wΔ
        (c , et , ve) = sound 𝔐 dt ct vρ
    in OE._,ₑ_ {𝔐} ρσ c , OE.evs-cons {𝔐} es et , Facts.valid-ext 𝔐 sσ wΔ bB es vσ ve

------------------------------------------------------------------------
-- The theorem: CaTT is sound in every strict ω-category 𝒞 with a cell
-- M k for each constant k, whenever each valid constant is sent to a
-- cell of the shape its type prescribes.

module _ (𝒞′ : ωCat) (M : K → ωCat.C 𝒞′) where
  module OEM = CaTTExp.Strict.OmegaEval 𝕊 𝒞′ (λ k c → M k ≡ c)

  IsModel : Set
  IsModel = ∀ k → Valid k → OEM.VE (M k) (ty k) OEM.[]ₑ

  model-of : IsModel → Model
  model-of isM = record
    { 𝒞 = 𝒞′ ; Mk = λ k c → M k ≡ c ; mdet = λ p q → trans (sym p) q ; Ok = λ _ → ⊤
    ; model = λ k v _ → M k , refl , isM k v }

  sound-in : IsModel → ∀ {Γ t A ρ} → Γ ⊢tm t ∶ A → OEM.ValidEnv ρ Γ →
             Σ (ωCat.C 𝒞′) λ c → OEM.Ev ρ t c × OEM.VE c A ρ
  sound-in isM {t = t} dt vρ = sound (model-of isM) dt (ck-⊤ t) vρ
