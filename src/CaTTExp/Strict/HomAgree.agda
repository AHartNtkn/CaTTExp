------------------------------------------------------------------------
-- On a single hom, the strict model of L agrees with the CaTT tower
-- interpretation (ledger A5, N3: the refinement left open by
-- Strict.StrictNu).
--
-- Let Θ be a pasting context and Γ = ΣΘ its suspension: a single hom
-- from the object 0 to the object 1. Every derivable t : arr A s u
-- over Γ has endpoints (x, y) with x = y or (x, y) = (0, 1) (`ends`),
-- and with ⟦_⟧ the CaTT interpretation of Strict.Interp in the generic
-- environment η Γ:
--
--   agree : Γ ⊢tm t ∶ arr A s u → endsV (arr A s u) ≡ just (x , y) →
--           (x ≡ y → top (⟦ t ⟧ η) ≈ []) ×
--           (x ≢ y → topS t ≈ top (⟦ t ⟧ η))
--
-- So in the hom 0 → 1 the strict model's top chain of every term,
-- including every coh image (the σ-image of T in the operation case,
-- 0 in the coherence case), is the top chain of the CaTT composite: the sum of the
-- σ-images of the top-dimensional variables of Δ when dim A + 1 =
-- dim Δ, and 0 otherwise. In a hom x → x both read the term as an
-- identity (CaTT: top chain 0; strict model: the unit of K(Γ)(x, x)
-- in degree 0, and 0 above).
--
-- The derivation is any derivation of two-tier L over Γ; the coh
-- contexts Δ inside it may have many homs. The proof is by induction
-- on the derivation; the coh case is Strict.HomCore's `cohAgree`,
-- with the hypotheses on σ supplied by the induction (`flatH`,
-- `jumpH`) and by soundness (Strict.Soundness), and the dimension
-- bound of the coherence case by Gray.CohDim's `cohB<`.
------------------------------------------------------------------------
module CaTTExp.Strict.HomAgree where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst using (nth-topsSub)
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Hyp using (closed)
open import CaTTExp.Strict.Soundness using (module Soundness)
open import CaTTExp.Strict.SigmaFacts using (ends01; short; s0; s1)
open import CaTTExp.Strict.TopCell using (Shape; shape)
open import CaTTExp.Strict.HomCore using (U; module Core)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂; _≤_)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.PsFacts ∅ using (ps-facts; PsFacts)
open import CaTTExp.Gray.MarksFuel ∅ using (SigOK)
open import CaTTExp.Strict.PsFacts ∅ using (Wb)
open import CaTTExp.Suspension ∅ using (Σctx; Σps′)
import CaTTExp.Subst ∅ graySide as S
import CaTTExp.Gray.CohDim ∅ as CD

private
  M∅ : K → Tower
  M∅ ()

import CaTTExp.Strict.Interp ∅ M∅ as I
open I using (⟦_⟧; ⟦_⟧ₛ; lookupₑ)

------------------------------------------------------------------------
-- Small facts.

private
  1≢0 : 1 ≡ 0 → ⊥
  1≢0 ()

  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

  pf : ∀ {Δ} → Δ ⊢ps → PsFacts Δ
  pf (ps d) = fst (ps-facts d)

  sig : SigOK
  sig {k = ()} _ _

  or-case : ∀ {C : Set} a {b} → T (a ∨ b) → (T a → C) → (T b → C) → C
  or-case true  p f g = f tt
  or-case false p f g = g p

  srcD : ∀ {Δ A t u} → Δ ⊢ty arr A t u → Δ ⊢tm t ∶ A
  srcD (arr-wf d _) = d

  vn : Tm → Nat
  vn (var a) = a
  vn _       = 0

  -- The endpoints that endsOK accepts.
  endsOK→ : ∀ Δ A → T (endsOK Δ A) → endsV A ≡ just (firstL (objs Δ) , lastL (objs Δ))
  endsOK→ Δ ⋆ ()
  endsOK→ Δ (arr ⋆ (var i) (var j)) p =
    cong₂ (λ a b → just (a , b)) (==ℕ-sound i _ (∧-fst p)) (==ℕ-sound j _ (∧-snd {i ==ℕ firstL (objs Δ)} p))
  endsOK→ Δ (arr ⋆ (var i) (coh _ _ _)) p = ⊥-elim (∧-snd {i ==ℕ firstL (objs Δ)} p)
  endsOK→ Δ (arr ⋆ (var i) (cst ())) p
  endsOK→ Δ (arr ⋆ (coh _ _ _) _) ()
  endsOK→ Δ (arr ⋆ (cst ()) _) p
  endsOK→ Δ (arr (arr B s t) _ _) p = endsOK→ Δ (arr B s t) p

------------------------------------------------------------------------
-- The single hom.

module _ {Θ : Ctx} (PΘ : Θ ⊢ps) where
  private
    Γ : Ctx
    Γ = Σctx Θ

    invΓ : PsInv Γ
    invΓ = psInv (Σps′ PΘ)

    ηΓ : I.Env
    ηΓ = I.η Γ

  -- Agreement for a term t in the hom x → y.
  Agr₀ : Nat → Nat → Tm → Set
  Agr₀ x y t = (x ≡ y → top (⟦ t ⟧ ηΓ) ≈ []) × ((x ≡ y → ⊥) → topS t ≈ top (⟦ t ⟧ ηΓ))

  -- Agreement for a term t of type C.
  Agr : Tm → Ty → Set
  Agr t C = ∀ x y → endsV C ≡ just (x , y) → Agr₀ x y t

  ----------------------------------------------------------------------
  -- Cells of the single hom.

  private
    no-loop : ∀ {x} a → WFT Γ x x (a ∷ []) → ⊥
    no-loop a (z , e , refl) with ends01 Θ a e
    ... | p , q = 1≢0 (trans (sym q) p)

    ends-w : ∀ {x y} w → WFT Γ x y w → (x ≡ y) ⊎ ((x ≡ 0) × (y ≡ 1))
    ends-w w wf with short Θ w wf
    ends-w [] wf | s0 = inj₁ wf
    ends-w (a ∷ []) (z , e , refl) | s1 .a = inj₂ (ends01 Θ a e)

    bottom : ∀ {x y} n X → IsCellL Γ x y n X → Σ Tuple λ w → Basis Γ x y 0 w
    bottom zero    (base c)       (w , _ , b) = w , b
    bottom (suc n) (step S' U' c) (cS , _)    = bottom n S' cS

    basis-flat : ∀ {x} k w → Basis Γ x x k w → (w ≡ []) × (k ≡ 0)
    basis-flat k w (wf , d) with short Θ w wf
    basis-flat k [] (wf , d) | s0 = refl , sym d
    basis-flat k (a ∷ []) (wf , d) | s1 .a = ⊥-elim (no-loop a wf)

  -- The endpoints of a cell are equal, or 0 and 1.
  ends-cell : ∀ {x y} n X → IsCellL Γ x y n X → (x ≡ y) ⊎ ((x ≡ 0) × (y ≡ 1))
  ends-cell n X c with bottom n X c
  ... | w , wf , _ = ends-w w wf

  -- A cell of a hom x → x is the unit in degree 0, and 0 above.
  top-flat : ∀ {x} n X → IsCellL Γ x x n X → top X ≈ U (n ==ℕ 0)
  top-flat zero (base c) (w , p , b) with basis-flat 0 w b
  ... | refl , _ = p
  top-flat {x} (suc n) (step S' U' c) (_ , _ , _ , _ , a) = go c a
    where
    go : ∀ c → All (Basis Γ x x (suc n)) c → c ≈ []
    go []      _       = ≈-refl
    go (w ∷ c) (b , _) with basis-flat (suc n) w b
    ... | _ , ()

  private
    top-flat′ : ∀ {x y} → x ≡ y → ∀ n X → IsCellL Γ x y n X → top X ≈ U (n ==ℕ 0)
    top-flat′ refl = top-flat

  ----------------------------------------------------------------------
  -- Variables.

  agree-var : ∀ i C → lookup Γ i ≡ just C → Agr (var i) C
  agree-var i C lc x y ec = flatP , jumpP
    where
    eli : endsL (lookup Γ i) ≡ just (x , y)
    eli = trans (cong endsL lc) ec
    flatP : x ≡ y → top (⟦ var i ⟧ ηΓ) ≈ []
    flatP refl = ⊥-elim (no-loop i (_ , eli , refl))
    jumpP : (x ≡ y → ⊥) → topS (var i) ≈ top (⟦ var i ⟧ ηΓ)
    jumpP _ rewrite I.η-top Γ i | T-true (lookup-lt Γ i lc) = ≈-refl

  ----------------------------------------------------------------------
  -- A coh, given agreement for the terms of its substitution.

  module CohStep {Δ t' u' σ} (A : Ty) (psΔ : Δ ⊢ps) (ctxΔ : Δ ⊢ctx) (tyΔ : Δ ⊢ty arr A t' u')
                 (ok : T (graySide Δ A t' u')) (sσ : Γ ⊢sub σ ∶ Δ)
                 (IH : ∀ v B → lookup Δ v ≡ just B → Agr (lookupₛ σ v) (B [ σ ]ty)) where
    private
      cellσ : Cellular Γ σ Δ
      cellσ = Soundness.sound-sub invΓ ctxΔ sσ

      lenσ : lenₛ σ ≡ len Δ
      lenσ = snd (S.sub-sc closed sσ)

      ρ′ : I.Env
      ρ′ = ⟦ σ ⟧ₛ ηΓ

    R : List TSet
    R = topsSub σ

    F : Nat → Bag
    F v = top (lookupₑ ρ′ v)

    img : Nat → Nat
    img o = vn (lookupₛ σ o)

    private
      lt : ∀ v {B} → lookup Δ v ≡ just B → T (v <ℕ lenₛ σ)
      lt v lv = subst (λ n → T (v <ℕ n)) (sym lenσ) (lookup-lt Δ v lv)

      F≡ : ∀ v {B} → lookup Δ v ≡ just B → F v ≡ top (⟦ lookupₛ σ v ⟧ ηΓ)
      F≡ v lv = cong top (I.lookup-⟦⟧ₛ σ ηΓ v (lt v lv))

      R≡ : ∀ v {B} → lookup Δ v ≡ just B → nth v R ≡ topS (lookupₛ σ v)
      R≡ v lv = nth-topsSub σ v (lt v lv)

      -- What σ does on a variable v of Δ in the hom a → b.
      VFacts : Nat → Nat → Nat → Set
      VFacts v a b = ((img a ≡ img b) → topS (lookupₛ σ v) ≈ U (hdimV Δ v ==ℕ 0)) ×
                     ((img a ≡ img b → ⊥) → (img a ≡ 0) × (img b ≡ 1)) ×
                     Agr₀ (img a) (img b) (lookupₛ σ v)

      vfacts : ∀ v a b B → lookup Δ v ≡ just B → endsV B ≡ just (a , b) → VFacts v a b
      vfacts v a b ⋆ lv ()
      vfacts v a b (arr B₀ s₀ s₁) lv eB with cellσ v (arr B₀ s₀ s₁) lv
      ... | (x' , y') , ee , _ , _ , c with ends-sub (arr B₀ s₀ s₁) σ eB ee
      ...   | σa , σb = flatP , ends , agr
        where
        ia : img a ≡ x'
        ia = cong vn σa
        ib : img b ≡ y'
        ib = cong vn σb
        hd≡ : hdimV Δ v ≡ dim (B₀ [ σ ]ty)
        hd≡ = trans (cong hdimTy lv) (sym (dim-sub B₀ σ))
        flatP : img a ≡ img b → topS (lookupₛ σ v) ≈ U (hdimV Δ v ==ℕ 0)
        flatP q = subst (λ n → topS (lookupₛ σ v) ≈ U (n ==ℕ 0)) (sym hd≡)
                   (subst (_≈ U (dim (B₀ [ σ ]ty) ==ℕ 0)) (top-towerOf (lookupₛ σ v) (B₀ [ σ ]ty) (s₀ [ σ ]tm) (s₁ [ σ ]tm))
                     (top-flat′ (trans (sym ia) (trans q ib)) _ _ c))
        ends : (img a ≡ img b → ⊥) → (img a ≡ 0) × (img b ≡ 1)
        ends ne with ends-cell _ _ c
        ... | inj₁ q         = ⊥-elim (ne (trans ia (trans q (sym ib))))
        ... | inj₂ (p₀ , p₁) = trans ia p₀ , trans ib p₁
        agr : Agr₀ (img a) (img b) (lookupₛ σ v)
        agr = subst₂ (λ x y → Agr₀ x y (lookupₛ σ v)) (sym ia) (sym ib) (IH v (arr B₀ s₀ s₁) lv x' y' ee)
          where
          subst₂ : ∀ {X : Set} (P : X → X → Set) {x y u w} → x ≡ y → u ≡ w → P x u → P y w
          subst₂ P refl refl p = p

      vfacts′ : ∀ v a b → endsL (lookup Δ v) ≡ just (a , b) →
                Σ Ty λ B → (lookup Δ v ≡ just B) × VFacts v a b
      vfacts′ v a b ev with endsL-inv (lookup Δ v) ev
      ... | B , lv , eB = B , lv , vfacts v a b B lv eB

    flatH : ∀ v a b → endsL (lookup Δ v) ≡ just (a , b) → img a ≡ img b →
            (F v ≈ []) × (nth v R ≈ U (hdimV Δ v ==ℕ 0))
    flatH v a b ev q with vfacts′ v a b ev
    ... | B , lv , fl , _ , agr =
      subst (_≈ []) (sym (F≡ v lv)) (fst agr q) ,
      subst (_≈ U (hdimV Δ v ==ℕ 0)) (sym (R≡ v lv)) (fl q)

    jumpH : ∀ v a b → endsL (lookup Δ v) ≡ just (a , b) → (img a ≡ img b → ⊥) →
            (img a ≡ 0) × (img b ≡ 1) × (nth v R ≈ F v)
    jumpH v a b ev ne with vfacts′ v a b ev
    ... | B , lv , _ , en , agr =
      fst (en ne) , snd (en ne) ,
      subst₂′ (R≡ v lv) (F≡ v lv) (snd agr ne)
      where
      subst₂′ : ∀ {X X' Y Y'} → X' ≡ X → Y' ≡ Y → X ≈ Y → X' ≈ Y'
      subst₂′ refl refl p = p

    module C = Core psΔ R F img flatH jumpH

    -- The CaTT top chain is Core's.
    ct≈ : I.cohTop Δ A ρ′ ≈ C.cohTop′ A
    ct≈ with suc (dim A) ==ℕ dimCtx Δ
    ... | true  = cm-ext' _ _ (Wb Δ (dimCtx Δ)) pt
      where
      pt : ∀ w → I.Fv ρ′ w ≈ C.Fs w
      pt []          = ≈-refl
      pt (v ∷ [])    = ≈-refl
      pt (_ ∷ _ ∷ _) = ≈-refl
    ... | false = ≈-refl

    -- The side condition: endpoints and dimensions.
    private
      cc : Bool
      cc = cohCase Δ A t' u'

      ends-A : endsV (arr A t' u') ≡ just (firstL (objs Δ) , lastL (objs Δ))
      ends-A = go A refl
        where
        go : ∀ A′ → A ≡ A′ → endsV (arr A t' u') ≡ just (firstL (objs Δ) , lastL (objs Δ))
        go ⋆ refl = endsOK→ Δ (arr ⋆ t' u') (∧-snd {dimK (homs Δ) ==ℕ 0} ok)
        go (arr B s s') refl = endsOK→ Δ A eok
          where
          eok : T (endsOK Δ A)
          eok = or-case (cohCase Δ A t' u') ok (∧-fst {endsOK Δ A}) (∧-fst {endsOK Δ A})

      hc : cc ≡ true → suc (dimK (homs Δ)) ≤ dim A
      hc = go A refl
        where
        go : ∀ A′ → A ≡ A′ → cc ≡ true → suc (dimK (homs Δ)) ≤ dim A
        go ⋆ refl ()
        go (arr B s s') refl e = CD.cohB< closed (λ {G} {k} → sig {G} {k}) Δ (pf psΔ) B s s' t' (srcD tyΔ) u' (subst T (sym e) tt)

      ho : cc ≡ false → dim A ≡ dimK (homs Δ)
      ho = go A refl
        where
        go : ∀ A′ → A ≡ A′ → cc ≡ false → dim A ≡ dimK (homs Δ)
        go ⋆ refl _ = sym (==ℕ-sound (dimK (homs Δ)) 0 (∧-fst ok))
        go (arr B s s') refl e =
          ==ℕ-sound (dim A) _ (∧-fst (∧-snd {endsOK Δ A} (subst (λ b → T (b ∨ opCase Δ A t' u')) e ok)))

    open Shape (shape psΔ)

    agree-coh : Agr (coh Δ (arr A t' u') σ) (arr A t' u' [ σ ]ty)
    agree-coh x y ec = flatP , jumpP
      where
      es = ends-sub (arr A t' u') σ ends-A ec
      ix : img o ≡ x
      ix = trans (cong img (sym efst)) (cong vn (fst es))
      iy : img (lastL (o ∷ rest)) ≡ y
      iy = trans (cong img (sym elst)) (cong vn (snd es))
      ca = C.cohAgree o rest eqo A cc hc ho
      flatP : x ≡ y → I.cohTop Δ A ρ′ ≈ []
      flatP q = ≈-trans ct≈ (fst ca (trans ix (trans q (sym iy))))
      jumpP : (x ≡ y → ⊥) → applyF R (if cc then [] else topT (homs Δ)) ≈ I.cohTop Δ A ρ′
      jumpP ne = ≈-trans (snd ca (λ q → ne (trans (sym ix) (trans q iy)))) (≈-sym ct≈)

  ----------------------------------------------------------------------
  -- The induction.

  mutual
    agree-tm : ∀ {t C} → Γ ⊢tm t ∶ C → Agr t C
    agree-tm (var-wf _ lc) = agree-var _ _ lc
    agree-tm (coh-wf {A = A} psΔ ctxΔ tyΔ ok sσ) =
      CohStep.agree-coh A psΔ ctxΔ tyΔ ok sσ (agree-sub ctxΔ sσ)
    agree-tm (cst-wf {()} _ _)

    agree-sub : ∀ {σ Δ} → Δ ⊢ctx → Γ ⊢sub σ ∶ Δ →
                ∀ v B → lookup Δ v ≡ just B → Agr (lookupₛ σ v) (B [ σ ]ty)
    agree-sub ε-wf (⟨⟩-wf _) v B ()
    agree-sub (▸-wf {Δ} {A} w a) (,-wf {σ} {_} {t} sσ d) v B eq with S.sub-sc closed sσ
    ... | (_ , l) with v ==ℕ len Δ in e
    ...   | true rewrite l | e =
      subst (λ X → Agr t (X [ σ ,ₛ t ]ty)) (just-inj eq)
        (subst (Agr t)
          (sym (S.ext-ty A σ t (subst (λ n → S.ScTy n A) (sym l) (S.ty-sc closed a))))
          (agree-tm d))
    ...   | false rewrite l | e =
      subst (Agr (lookupₛ σ v))
        (sym (S.ext-ty B σ t (subst (λ n → S.ScTy n B) (sym l) (snd (S.ctx-lookup closed w eq)))))
        (agree-sub w sσ v B eq)

  ----------------------------------------------------------------------
  -- The results.

  -- Every derivable term of the single hom lies in a hom x → x or 0 → 1.
  ends : ∀ {t A s u} → Γ ⊢tm t ∶ arr A s u →
         Σ (Nat × Nat) λ e → (endsV (arr A s u) ≡ just e) × ((fst e ≡ snd e) ⊎ ((fst e ≡ 0) × (snd e ≡ 1)))
  ends dt with Soundness.sound-tm invΓ dt
  ... | e , ee , _ , _ , c = e , ee , ends-cell _ _ c

  -- The strict model's top chain is the CaTT composite's.
  agree : ∀ {t A s u x y} → Γ ⊢tm t ∶ arr A s u → endsV (arr A s u) ≡ just (x , y) →
          (x ≡ y → top (⟦ t ⟧ ηΓ) ≈ []) × ((x ≡ y → ⊥) → topS t ≈ top (⟦ t ⟧ ηΓ))
  agree dt e = agree-tm dt _ _ e

  -- In the hom 0 → 1.
  agree01 : ∀ {t A s u} → Γ ⊢tm t ∶ arr A s u → endsV (arr A s u) ≡ just (0 , 1) →
            topS t ≈ top (⟦ t ⟧ ηΓ)
  agree01 dt e = snd (agree dt e) (λ ())
