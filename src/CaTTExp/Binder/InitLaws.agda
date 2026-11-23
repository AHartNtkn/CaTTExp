------------------------------------------------------------------------
-- INIT's binder interface satisfies the stability laws
-- (CaTTExp.Binder.Laws.BinderLaws), so substitution, renaming and
-- weakening are admissible for CaTT + INIT (CaTTExp.Binder.Subst,
-- CaTTExp.Binder.Rename), for every coh side condition.
--
-- Under a substitution σ of the parameters by locally closed terms:
--  * positivity is preserved (X stays X, and a parameter-only object
--    stays parameter-only; a non-⊤ target may become ⊤, never the
--    reverse), and the selector conditions are unchanged;
--  * the argument telescopes and result types commute with σ, because
--    each is built from Δ by opening, the coherences of
--    CaTTExp.Binder.Init, and a case split on "is this object X?",
--    which σ cannot change.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.InitLaws (bs : Base) where

open Base bs using (top?)

private
  𝕊 : Signature
  𝕊 = initSig bs

open Signature 𝕊
open Construction K top?
open import CaTTExp.Binder.SyntaxLemmas K B
open Laws 𝕊

------------------------------------------------------------------------
-- Generic helpers.

if-[]tm : ∀ c x y σ → (if c then x else y) [ σ ]tm ≡ (if c then (x [ σ ]tm) else (y [ σ ]tm))
if-[]tm true  x y σ = refl
if-[]tm false x y σ = refl

⧺-[] : ∀ Γ Ξ σ → (Γ ⧺ Ξ) [ σ ]tel ≡ (Γ [ σ ]tel) ⧺ (Ξ [ σ ]tel)
⧺-[] Γ ε       σ = refl
⧺-[] Γ (Ξ ▸ A) σ = cong (_▸ (A [ σ ]ty)) (⧺-[] Γ Ξ σ)

dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[] ⋆           σ = refl
dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

-- Locally closed terms are not X and mention no bound variable.
isX-lc : ∀ t → T (lcTm? 0 t) → isX? t ≡ false
isX-lc (var _)       _ = refl
isX-lc (bvar e j)    ()
isX-lc (coh _ _ _)   _ = refl
isX-lc (cst _)       _ = refl
isX-lc (bnd _ _ _ _) _ = refl

private
  ∨ff : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
  ∨ff refl refl = refl

mutual
  mTy-lc : ∀ d A → T (lcTy? d A) → mTy d A ≡ false
  mTy-lc d ⋆ _ = refl
  mTy-lc d (arr A t u) p =
    let (a , q) = T∧ {lcTy? d A} p ; (b , c) = T∧ {lcTm? d t} q in
    ∨ff (mTy-lc d A a) (∨ff (mTm-lc d t b) (mTm-lc d u c))

  mTm-lc : ∀ d t → T (lcTm? d t) → mTm d t ≡ false
  mTm-lc d (var _) _ = refl
  mTm-lc d (bvar e _) p = <→≢ e d p
  mTm-lc d (coh _ _ σ) p = mSub-lc d σ p
  mTm-lc d (cst _) _ = refl
  mTm-lc d (bnd _ _ Δ σ) p =
    let (a , c) = T∧ {lcTel? (suc d) Δ} p in ∨ff (mTel-lc (suc d) Δ a) (mSub-lc d σ c)

  mTel-lc : ∀ d Δ → T (lcTel? d Δ) → mTel d Δ ≡ false
  mTel-lc d ε _ = refl
  mTel-lc d (Δ ▸ A) p = let (a , b) = T∧ {lcTel? d Δ} p in ∨ff (mTel-lc d Δ a) (mTy-lc d A b)

  mSub-lc : ∀ d σ → T (lcSub? d σ) → mSub d σ ≡ false
  mSub-lc d ⟨⟩ _ = refl
  mSub-lc d (σ ,ₛ t) p = let (a , b) = T∧ {lcSub? d σ} p in ∨ff (mSub-lc d σ a) (mTm-lc d t b)

------------------------------------------------------------------------
-- Substitution by a locally closed σ.

module _ (σ : Sub) (l : LC σ) where

  isX-[] : ∀ t → isX? (t [ σ ]tm) ≡ isX? t
  isX-[] (var i)       = isX-lc (lookupₛ σ i) (lc-lookup σ i l)
  isX-[] (bvar _ _)    = refl
  isX-[] (coh _ _ _)   = refl
  isX-[] (cst _)       = refl
  isX-[] (bnd _ _ _ _) = refl

  mutual
    mTy-[] : ∀ d A → mTy d (A [ σ ]ty) ≡ mTy d A
    mTy-[] d ⋆ = refl
    mTy-[] d (arr A t u) = cong₂ _∨_ (mTy-[] d A) (cong₂ _∨_ (mTm-[] d t) (mTm-[] d u))

    mTm-[] : ∀ d t → mTm d (t [ σ ]tm) ≡ mTm d t
    mTm-[] d (var i) = mTm-lc d (lookupₛ σ i) (lcTm-mono d (lookupₛ σ i) (lc-lookup σ i l))
    mTm-[] d (bvar _ _) = refl
    mTm-[] d (coh _ _ τ) = mSub-[] d τ
    mTm-[] d (cst _) = refl
    mTm-[] d (bnd _ _ Δ τ) = cong₂ _∨_ (mTel-[] (suc d) Δ) (mSub-[] d τ)

    mTel-[] : ∀ d Δ → mTel d (Δ [ σ ]tel) ≡ mTel d Δ
    mTel-[] d ε = refl
    mTel-[] d (Δ ▸ A) = cong₂ _∨_ (mTel-[] d Δ) (mTy-[] d A)

    mSub-[] : ∀ d τ → mSub d (τ ∘ σ) ≡ mSub d τ
    mSub-[] d ⟨⟩ = refl
    mSub-[] d (τ ,ₛ t) = cong₂ _∨_ (mSub-[] d τ) (mTm-[] d t)

  srcOK-[] : ∀ S → srcOK (S [ σ ]tm) ≡ srcOK S
  srcOK-[] S = cong₂ _∨_ (isX-[] S) (cong not (mTm-[] 0 S))

  tgt-stable : ∀ T₀ → T (tgtOK T₀) → T (tgtOK (T₀ [ σ ]tm))
  tgt-stable (var _)       ()
  tgt-stable (bvar _ _)    p = p
  tgt-stable (coh _ _ _)   ()
  tgt-stable (cst _)       p = p
  tgt-stable (bnd _ _ _ _) ()

  mapP : Maybe (Tm × Tm) → Maybe (Tm × Tm)
  mapP nothing        = nothing
  mapP (just (S , T)) = just (S [ σ ]tm , T [ σ ]tm)

  mapT : Maybe Ty → Maybe Ty
  mapT nothing  = nothing
  mapT (just A) = just (A [ σ ]ty)

  base-[] : ∀ A → base (A [ σ ]ty) ≡ mapP (base A)
  base-[] ⋆                     = refl
  base-[] (arr ⋆ s t)           = refl
  base-[] (arr (arr A a c) _ _) = base-[] (arr A a c)

  okBase-stable : ∀ mb → T (okBase mb) → T (okBase (mapP mb))
  okBase-stable nothing        ()
  okBase-stable (just (S , T₀)) p =
    let (a , c) = T∧ {srcOK S} p in
    ∧T (subst T (sym (srcOK-[] S)) a) (tgt-stable T₀ c)

  entryOK-stable : ∀ A → T (entryOK A) → T (entryOK (A [ σ ]ty))
  entryOK-stable A p = subst (λ z → T (okBase z)) (sym (base-[] A)) (okBase-stable (base A) p)

  positive-stable : ∀ Δ → T (positive Δ) → T (positive (Δ [ σ ]tel))
  positive-stable ε                 ()
  positive-stable (ε ▸ ⋆)           _ = tt
  positive-stable (ε ▸ arr _ _ _)   ()
  positive-stable (Δ ▸ B₀ ▸ A)      p =
    let (a , c) = T∧ {positive (Δ ▸ B₀)} p in
    ∧T (positive-stable (Δ ▸ B₀) a) (entryOK-stable A c)

  mapsOnly-[] : ∀ Δ → mapsOnly (Δ [ σ ]tel) ≡ mapsOnly Δ
  mapsOnly-[] ε             = refl
  mapsOnly-[] (ε ▸ _)       = refl
  mapsOnly-[] (Δ ▸ B₀ ▸ A)  = cong₂ _∧_ (mapsOnly-[] (Δ ▸ B₀)) (cong (_==ℕ 1) (dim-[] A σ))

  lookup-[] : ∀ Δ y → lookup (Δ [ σ ]tel) y ≡ mapT (lookup Δ y)
  lookup-[] ε       y = refl
  lookup-[] (Δ ▸ A) y rewrite len-tel[] Δ σ with y ==ℕ len Δ
  ... | true  = refl
  ... | false = lookup-[] Δ y

  isMap-[] : ∀ Δ y → isMap? (lookup (Δ [ σ ]tel) y) ≡ isMap? (lookup Δ y)
  isMap-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = cong (_==ℕ 1) (dim-[] A σ)

  inner-[] : ∀ y Δ → inner y (Δ [ σ ]tel) ≡ inner y Δ
  inner-[] y Δ rewrite len-tel[] Δ σ = refl

  sel-[] : ∀ b y Δ → sel b y (Δ [ σ ]tel) ≡ sel b y Δ
  sel-[] μ    y Δ = refl
  sel-[] η    y Δ = inner-[] y Δ
  sel-[] rec  y Δ = refl
  sel-[] recY y Δ = cong₂ _∧_ (inner-[] y Δ) (isMap-[] Δ y)
  sel-[] uni  y Δ = cong ((y ==ℕ 0) ∧_) (mapsOnly-[] Δ)
  sel-[] uniY y Δ = cong₂ _∧_ (inner-[] y Δ) (mapsOnly-[] Δ)

  ----------------------------------------------------------------------
  -- The pieces of the argument telescopes and result types.

  ηAt-[] : ∀ Δ j → (ηAt Δ j) [ σ ]tm ≡ ηAt (Δ [ σ ]tel) j
  ηAt-[] Δ zero    = refl
  ηAt-[] Δ (suc j) = refl

  ηPre-∘ : ∀ Δ k → ηPre Δ k ∘ σ ≡ ηPre (Δ [ σ ]tel) k
  ηPre-∘ Δ zero    = refl
  ηPre-∘ Δ (suc k) = cong₂ _,ₛ_ (ηPre-∘ Δ k) (ηAt-[] Δ k)

  bvPre-∘ : ∀ k → bvPre k ∘ σ ≡ bvPre k
  bvPre-∘ zero    = refl
  bvPre-∘ (suc k) = cong (_,ₛ bvar 0 k) (bvPre-∘ k)

  act-[] : ∀ S M h → (act S M h) [ σ ]tm ≡ act (S [ σ ]tm) (M ∘ σ) (h [ σ ]tm)
  act-[] S M h rewrite if-[]tm (isX? S) h (idm (opTm 0 M S)) σ | isX-[] S with isX? S
  ... | true  = refl
  ... | false = cong idm (op-[]tm 0 M S σ l)

  cellTy-[] : ∀ S T₀ M₁ M₂ s₁ s₂ h →
              (cellTy S T₀ M₁ M₂ s₁ s₂ h) [ σ ]ty ≡
              cellTy (S [ σ ]tm) (T₀ [ σ ]tm) (M₁ ∘ σ) (M₂ ∘ σ) (s₁ [ σ ]tm) (s₂ [ σ ]tm) (h [ σ ]tm)
  cellTy-[] S T₀ M₁ M₂ s₁ s₂ h
    rewrite act-[] T₀ M₁ h | act-[] S M₁ h
          | op-[]tm 0 M₁ S σ l | op-[]tm 0 M₁ T₀ σ l | op-[]tm 0 M₂ S σ l | op-[]tm 0 M₂ T₀ σ l = refl

  withBase-[] : ∀ mb (k k′ : Tm → Tm → Ty) → (∀ S T₀ → (k S T₀) [ σ ]ty ≡ k′ (S [ σ ]tm) (T₀ [ σ ]tm)) →
                (withBase mb k) [ σ ]ty ≡ withBase (mapP mb) k′
  withBase-[] nothing         k k′ e = refl
  withBase-[] (just (S , T₀)) k k′ e = e S T₀

  entryBase-[] : ∀ Δ y → entryBase (Δ [ σ ]tel) y ≡ mapP (entryBase Δ y)
  entryBase-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = base-[] A

  θBody-[] : ∀ Δ y h S T₀ → (θBody Δ y h S T₀) [ σ ]ty ≡ θBody (Δ [ σ ]tel) y (h [ σ ]tm) (S [ σ ]tm) (T₀ [ σ ]tm)
  θBody-[] Δ y h S T₀
    rewrite cellTy-[] S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h
          | ηPre-∘ Δ (len Δ) | bvPre-∘ (len Δ) | ηAt-[] Δ y | len-tel[] Δ σ = refl

  θTy-[] : ∀ Δ y h → (θTy Δ y h) [ σ ]ty ≡ θTy (Δ [ σ ]tel) y (h [ σ ]tm)
  θTy-[] Δ y h =
    trans (withBase-[] (entryBase Δ y) (θBody Δ y h) (θBody (Δ [ σ ]tel) y (h [ σ ]tm)) (θBody-[] Δ y h))
          (cong (λ z → withBase z (θBody (Δ [ σ ]tel) y (h [ σ ]tm))) (sym (entryBase-[] Δ y)))

  θTel-[] : ∀ Δ o k → (θTel Δ o k) [ σ ]tel ≡ θTel (Δ [ σ ]tel) o k
  θTel-[] Δ o zero    = refl
  θTel-[] Δ o (suc k) = cong₂ _▸_ (θTel-[] Δ o k) (θTy-[] Δ (suc k) (bvar 0 o))

  morTel-[] : ∀ Δ o → (morTel Δ o) [ σ ]tel ≡ morTel (Δ [ σ ]tel) o
  morTel-[] Δ o =
    trans (⧺-[] (ε ▸ arr ⋆ (μT Δ) (bvar 0 0)) (θTel Δ o (len Δ ∸ 1)) σ)
          (cong ((ε ▸ arr ⋆ (μT (Δ [ σ ]tel)) (bvar 0 0)) ⧺_)
                (trans (θTel-[] Δ o (len Δ ∸ 1))
                       (cong (λ k → θTel (Δ [ σ ]tel) o (k ∸ 1)) (sym (len-tel[] Δ σ)))))

  uniYBody-[] : ∀ Δ y S T₀ → (uniYBody Δ y S T₀) [ σ ]ty ≡ uniYBody (Δ [ σ ]tel) y (S [ σ ]tm) (T₀ [ σ ]tm)
  uniYBody-[] Δ y S T₀
    rewrite if-[]tm (isX? T₀) (bnd uni 0 Δ (bvPre (len Δ + len Δ + len Δ)))
                   (id2 (opTm 0 (ηPre Δ (len Δ)) T₀) (opTm 0 (ηPre Δ (len Δ)) T₀) (idm (opTm 0 (ηPre Δ (len Δ)) T₀))) σ
          | if-[]tm (isX? S) (bnd uni 0 Δ (bvPre (len Δ + len Δ + len Δ)))
                   (id2 (opTm 0 (ηPre Δ (len Δ)) S) (opTm 0 (ηPre Δ (len Δ)) S) (idm (opTm 0 (ηPre Δ (len Δ)) S))) σ
          | act-[] T₀ (ηPre Δ (len Δ)) (bvar 0 (len Δ))
          | act-[] T₀ (ηPre Δ (len Δ)) (bvar 0 (len Δ + len Δ))
          | act-[] S (ηPre Δ (len Δ)) (bvar 0 (len Δ))
          | act-[] S (ηPre Δ (len Δ)) (bvar 0 (len Δ + len Δ))
          | op-[]tm 0 (ηPre Δ (len Δ)) S σ l | op-[]tm 0 (ηPre Δ (len Δ)) T₀ σ l
          | op-[]tm 0 (bvPre (len Δ)) S σ l | op-[]tm 0 (bvPre (len Δ)) T₀ σ l
          | isX-[] S | isX-[] T₀
          | ηPre-∘ Δ (len Δ) | bvPre-∘ (len Δ) | bvPre-∘ (len Δ + len Δ + len Δ)
          | ηAt-[] Δ y | len-tel[] Δ σ = refl

------------------------------------------------------------------------
-- Scoping of the result types.

module _ (n : Nat) where

  private
    sc∧ : ∀ {a b} → T a → T b → T (a ∧ b)
    sc∧ = ∧T

  sc-arr : ∀ A t u → T (scTy? n A) → T (scTm? n t) → T (scTm? n u) → T (scTy? n (arr A t u))
  sc-arr A t u pA pt pu = ∧T {scTy? n A} pA (∧T {scTm? n t} pt pu)

  sc-ηAt : ∀ Δ j → T (scTel? n Δ) → T (scTm? n (ηAt Δ j))
  sc-ηAt Δ zero    p = ∧T p tt
  sc-ηAt Δ (suc j) p = ∧T p tt

  sc-ηPre : ∀ Δ k → T (scTel? n Δ) → T (scSub? n (ηPre Δ k))
  sc-ηPre Δ zero    p = tt
  sc-ηPre Δ (suc k) p = ∧T (sc-ηPre Δ k p) (sc-ηAt Δ k p)

  sc-bvPre : ∀ k → T (scSub? n (bvPre k))
  sc-bvPre zero    = tt
  sc-bvPre (suc k) = ∧T (sc-bvPre k) tt

  sc-lookupTel : ∀ Δ y {A} → T (scTel? n Δ) → lookup Δ y ≡ just A → T (scTy? n A)
  sc-lookupTel (Δ ▸ A′) y p e with y ==ℕ len Δ
  ... | true  = subst (λ z → T (scTy? n z)) (just-inj e) (snd (T∧ {scTel? n Δ} p))
  ... | false = sc-lookupTel Δ y (fst (T∧ {scTel? n Δ} p)) e

  sc-base : ∀ A {S T₀} → T (scTy? n A) → base A ≡ just (S , T₀) → T (scTm? n S) × T (scTm? n T₀)
  sc-base (arr ⋆ s t) p refl = let (_ , q) = T∧ {true} p in T∧ {scTm? n s} q
  sc-base (arr (arr A a c) _ _) p e = sc-base (arr A a c) (fst (T∧ {scTy? n (arr A a c)} p)) e

  sc-entryBase : ∀ Δ y {S T₀} → T (scTel? n Δ) → entryBase Δ y ≡ just (S , T₀) →
                 T (scTm? n S) × T (scTm? n T₀)
  sc-entryBase Δ y p e with lookup Δ y in le
  ... | nothing = ⊥-elim (nj e)
    where
    nj : ∀ {x : Tm × Tm} → nothing ≡ just x → ⊥
    nj ()
  ... | just A  = sc-base A (sc-lookupTel Δ y p le) e

  sc-withBase : ∀ mb (k : Tm → Tm → Ty) →
                (∀ S T₀ → mb ≡ just (S , T₀) → T (scTy? n (k S T₀))) → T (scTy? n (withBase mb k))
  sc-withBase nothing         k h = tt
  sc-withBase (just (S , T₀)) k h = h S T₀ refl

  sc-idm : ∀ a → T (scTm? n a) → T (scTm? n (idm a))
  sc-idm a p = ∧T tt p

  sc-id2 : ∀ a b f → T (scTm? n a) → T (scTm? n b) → T (scTm? n f) → T (scTm? n (id2 a b f))
  sc-id2 a b f pa pb pf = ∧T (∧T (∧T tt pa) pb) pf

  sc-cmp : ∀ a b c f g → T (scTm? n a) → T (scTm? n b) → T (scTm? n c) → T (scTm? n f) → T (scTm? n g) →
           T (scTm? n (cmp a b c f g))
  sc-cmp a b c f g pa pb pc pf pg = ∧T (∧T (∧T (∧T (∧T tt pa) pb) pf) pc) pg

  sc-vcomp : ∀ a b f g α h β → T (scTm? n a) → T (scTm? n b) → T (scTm? n f) → T (scTm? n g) →
             T (scTm? n α) → T (scTm? n h) → T (scTm? n β) → T (scTm? n (vcomp a b f g α h β))
  sc-vcomp a b f g α h β pa pb pf pg pα ph pβ = ∧T (∧T (∧T (∧T (∧T (∧T (∧T tt pa) pb) pf) pg) pα) ph) pβ

  sc-lwh : ∀ a b c f g g′ α → T (scTm? n a) → T (scTm? n b) → T (scTm? n c) → T (scTm? n f) →
           T (scTm? n g) → T (scTm? n g′) → T (scTm? n α) → T (scTm? n (lwh a b c f g g′ α))
  sc-lwh a b c f g g′ α pa pb pc pf pg pg′ pα = ∧T (∧T (∧T (∧T (∧T (∧T (∧T tt pa) pb) pf) pc) pg) pg′) pα

  sc-rwh : ∀ a b c f f′ α g → T (scTm? n a) → T (scTm? n b) → T (scTm? n c) → T (scTm? n f) →
           T (scTm? n f′) → T (scTm? n α) → T (scTm? n g) → T (scTm? n (rwh a b c f f′ α g))
  sc-rwh a b c f f′ α g pa pb pc pf pf′ pα pg = ∧T (∧T (∧T (∧T (∧T (∧T (∧T tt pa) pb) pf) pf′) pα) pc) pg

  sc-if : ∀ c {x y : Tm} → T (scTm? n x) → T (scTm? n y) → T (scTm? n (if c then x else y))
  sc-if true  px _ = px
  sc-if false _ py = py

  sc-act : ∀ S M h → T (scTm? n S) → T (scSub? n M) → T (scTm? n h) → T (scTm? n (act S M h))
  sc-act S M h pS pM ph = sc-if (isX? S) ph (sc-idm (opTm 0 M S) (sc-opTm 0 M S pM pS))

  sc-cellTy : ∀ S T₀ M₁ M₂ s₁ s₂ h → T (scTm? n S) → T (scTm? n T₀) → T (scSub? n M₁) → T (scSub? n M₂) →
              T (scTm? n s₁) → T (scTm? n s₂) → T (scTm? n h) → T (scTy? n (cellTy S T₀ M₁ M₂ s₁ s₂ h))
  sc-cellTy S T₀ M₁ M₂ s₁ s₂ h pS pT p₁ p₂ ps₁ ps₂ ph =
    sc-arr (arr ⋆ a₁ d₂) (cmp a₁ c₁ d₂ s₁ th) (cmp a₁ a₂ d₂ sh s₂)
      (sc-arr ⋆ a₁ d₂ tt S₁ T₂)
      (sc-cmp a₁ c₁ d₂ s₁ th S₁ T₁ T₂ ps₁ (sc-act T₀ M₁ h pT p₁ ph))
      (sc-cmp a₁ a₂ d₂ sh s₂ S₁ S₂ T₂ (sc-act S M₁ h pS p₁ ph) ps₂)
    where
    a₁ = opTm 0 M₁ S
    a₂ = opTm 0 M₂ S
    c₁ = opTm 0 M₁ T₀
    d₂ = opTm 0 M₂ T₀
    th = act T₀ M₁ h
    sh = act S M₁ h
    S₁ = sc-opTm 0 M₁ S p₁ pS
    S₂ = sc-opTm 0 M₂ S p₂ pS
    T₁ = sc-opTm 0 M₁ T₀ p₁ pT
    T₂ = sc-opTm 0 M₂ T₀ p₂ pT

  sc-θTy : ∀ Δ y h → T (scTel? n Δ) → T (scTm? n h) → T (scTy? n (θTy Δ y h))
  sc-θTy Δ y h p ph =
    sc-withBase (entryBase Δ y) (θBody Δ y h) λ S T₀ e →
      let (pS , pT) = sc-entryBase Δ y p e in
      sc-cellTy S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h pS pT (sc-ηPre Δ (len Δ) p) (sc-bvPre (len Δ)) (sc-ηAt Δ y p) tt ph

  sc-uniYBody : ∀ Δ y S T₀ → T (scTel? n Δ) → T (scTm? n S) → T (scTm? n T₀) →
                T (scTy? n (uniYBody Δ y S T₀))
  sc-uniYBody Δ y S T₀ p pS pT =
    sc-arr (arr (arr ⋆ s₁ t₂) src tgt) l r
      (sc-arr (arr ⋆ s₁ t₂) src tgt (sc-arr ⋆ s₁ t₂ tt S₁ T₂) Src Tgt)
      (sc-vcomp s₁ t₂ src (cmp s₁ t₁ t₂ ηy th′) (lwh s₁ t₁ t₂ ηy th th′ tu) tgt (bvar 0 (m + m + y))
          S₁ T₂ Src (sc-cmp s₁ t₁ t₂ ηy th′ S₁ T₁ T₂ Ηy Th′)
          (sc-lwh s₁ t₁ t₂ ηy th th′ tu S₁ T₁ T₂ Ηy Th Th′ Tu) Tgt tt)
      (sc-vcomp s₁ t₂ src (cmp s₁ s₂ t₂ sh σy) (bvar 0 (m + y)) tgt (rwh s₁ s₂ t₂ sh sh′ su σy)
          S₁ T₂ Src (sc-cmp s₁ s₂ t₂ sh σy S₁ S₂ T₂ Sh tt) tt Tgt
          (sc-rwh s₁ s₂ t₂ sh sh′ su σy S₁ S₂ T₂ Sh Sh′ Su tt))
    where
    m   = len Δ
    M₁  = ηPre Δ m
    M₂  = bvPre m
    s₁  = opTm 0 M₁ S
    s₂  = opTm 0 M₂ S
    t₁  = opTm 0 M₁ T₀
    t₂  = opTm 0 M₂ T₀
    u   = bnd uni 0 Δ (bvPre (m + m + m))
    ηy  = ηAt Δ y
    σy  = bvar 0 y
    th  = act T₀ M₁ (bvar 0 m)
    th′ = act T₀ M₁ (bvar 0 (m + m))
    sh  = act S M₁ (bvar 0 m)
    sh′ = act S M₁ (bvar 0 (m + m))
    tu  = if isX? T₀ then u else id2 t₁ t₁ (idm t₁)
    su  = if isX? S then u else id2 s₁ s₁ (idm s₁)
    src = cmp s₁ t₁ t₂ ηy th
    tgt = cmp s₁ s₂ t₂ sh′ σy
    l   = vcomp s₁ t₂ src (cmp s₁ t₁ t₂ ηy th′) (lwh s₁ t₁ t₂ ηy th th′ tu) tgt (bvar 0 (m + m + y))
    r   = vcomp s₁ t₂ src (cmp s₁ s₂ t₂ sh σy) (bvar 0 (m + y)) tgt (rwh s₁ s₂ t₂ sh sh′ su σy)
    pM₁ = sc-ηPre Δ m p
    pM₂ = sc-bvPre m
    S₁  = sc-opTm 0 M₁ S pM₁ pS
    S₂  = sc-opTm 0 M₂ S pM₂ pS
    T₁  = sc-opTm 0 M₁ T₀ pM₁ pT
    T₂  = sc-opTm 0 M₂ T₀ pM₂ pT
    pu  : T (scTm? n u)
    pu  = ∧T {scTel? n Δ} p (sc-bvPre (m + m + m))
    Ηy  = sc-ηAt Δ y p
    Th  = sc-act T₀ M₁ (bvar 0 m) pT pM₁ tt
    Th′ = sc-act T₀ M₁ (bvar 0 (m + m)) pT pM₁ tt
    Sh  = sc-act S M₁ (bvar 0 m) pS pM₁ tt
    Sh′ = sc-act S M₁ (bvar 0 (m + m)) pS pM₁ tt
    Tu  = sc-if (isX? T₀) pu (sc-id2 t₁ t₁ (idm t₁) T₁ T₁ (sc-idm t₁ T₁))
    Su  = sc-if (isX? S) pu (sc-id2 s₁ s₁ (idm s₁) S₁ S₁ (sc-idm s₁ S₁))
    Src = sc-cmp s₁ t₁ t₂ ηy th S₁ T₁ T₂ Ηy Th
    Tgt = sc-cmp s₁ s₂ t₂ sh′ σy S₁ S₂ T₂ Sh′ tt

  sc-uniYTy : ∀ Δ y → T (scTel? n Δ) → T (scTy? n (uniYTy Δ y))
  sc-uniYTy Δ y p =
    sc-withBase (entryBase Δ y) (uniYBody Δ y) λ S T₀ e →
      let (pS , pT) = sc-entryBase Δ y p e in sc-uniYBody Δ y S T₀ p pS pT

  sc-res : ∀ b y Δ → T (scTel? n Δ) → T (scTy? n (res b y Δ))
  sc-res μ    y Δ p = tt
  sc-res η    y Δ p with lookup Δ y in e
  ... | nothing = tt
  ... | just A  = sc-opTy 0 (ηPre Δ y) A (sc-ηPre Δ y p) (sc-lookupTel Δ y p e)
  sc-res rec  y Δ p = ∧T tt (∧T (∧T p tt) tt)
  sc-res recY y Δ p = sc-θTy Δ y _ p (∧T p (sc-bvPre (len Δ)))
  sc-res uni  y Δ p = ∧T (∧T tt (∧T (∧T p tt) tt)) (∧T tt tt)
  sc-res uniY y Δ p = sc-uniYTy Δ y p

------------------------------------------------------------------------
-- The laws.

initLaws : BinderLaws
initLaws = record
  { side-stable = λ b y Δ σ l p →
      let (a , c) = T∧ {positive Δ} p in
      ∧T (positive-stable σ l Δ a) (subst T (sym (sel-[] σ l b y Δ)) c)
  ; args-stable = args-st
  ; res-stable  = res-st
  ; res-sc      = λ b y Δ n _ p → sc-res n b y Δ p
  }
  where
  args-st : ∀ b y Δ σ → LC σ → T (bside b y Δ) → bargs b y (Δ [ σ ]tel) ≡ (bargs b y Δ) [ σ ]tel
  args-st μ    y Δ σ l _ = refl
  args-st η    y Δ σ l _ = refl
  args-st rec  y Δ σ l _ = refl
  args-st recY y Δ σ l _ = refl
  args-st uni  y Δ σ l _
    rewrite ⧺-[] (Δ ⧺ morTel Δ (len Δ)) (morTel Δ (len Δ + len Δ)) σ | ⧺-[] Δ (morTel Δ (len Δ)) σ
          | morTel-[] σ l Δ (len Δ) | morTel-[] σ l Δ (len Δ + len Δ) | len-tel[] Δ σ = refl
  args-st uniY y Δ σ l _
    rewrite ⧺-[] (Δ ⧺ morTel Δ (len Δ)) (morTel Δ (len Δ + len Δ)) σ | ⧺-[] Δ (morTel Δ (len Δ)) σ
          | morTel-[] σ l Δ (len Δ) | morTel-[] σ l Δ (len Δ + len Δ) | len-tel[] Δ σ = refl

  res-st : ∀ b y Δ σ → LC σ → T (bside b y Δ) → bres b y (Δ [ σ ]tel) ≡ (bres b y Δ) [ σ ]ty
  res-st μ    y Δ σ l _ = refl
  res-st η    y Δ σ l _ rewrite lookup-[] σ l Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = sym (trans (op-[]ty 0 (ηPre Δ y) A σ l) (cong (λ z → opTy 0 z (A [ σ ]ty)) (ηPre-∘ σ l Δ y)))
  res-st rec  y Δ σ l _ = refl
  res-st recY y Δ σ l _ =
    sym (trans (θTy-[] σ l Δ y (bnd rec 0 Δ (bvPre (len Δ))))
               (cong (λ z → θTy (Δ [ σ ]tel) y (bnd rec 0 (Δ [ σ ]tel) z))
                     (trans (bvPre-∘ σ l (len Δ)) (cong bvPre (sym (len-tel[] Δ σ))))))
  res-st uni  y Δ σ l _ rewrite len-tel[] Δ σ = refl
  res-st uniY y Δ σ l _ =
    sym (trans (withBase-[] σ l (entryBase Δ y) (uniYBody Δ y) (uniYBody (Δ [ σ ]tel) y) (uniYBody-[] σ l Δ y))
               (cong (λ z → withBase z (uniYBody (Δ [ σ ]tel) y)) (sym (entryBase-[] σ l Δ y))))
