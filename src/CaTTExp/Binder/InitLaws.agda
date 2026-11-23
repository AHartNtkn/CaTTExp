------------------------------------------------------------------------
-- INIT's binder interface satisfies the stability laws
-- (CaTTExp.Binder.Laws.BinderLaws), so substitution, renaming and
-- weakening are admissible for CaTT + INIT (CaTTExp.Binder.Subst,
-- CaTTExp.Binder.Rename), for every coh side condition.
--
-- Under a substitution σ of the parameters by locally closed terms:
--  * positivity is preserved (a sort stays that sort, and a parameter-only object
--    stays parameter-only; a non-⊤ target may become ⊤, never the
--    reverse), and the selector conditions are unchanged;
--  * the argument telescopes and result types commute with σ, because
--    each is built from Δ by opening, the coherences of
--    CaTTExp.Binder.Init, and a case split on "which sort is this object?",
--    which σ cannot change; σ does not change the number of sorts.
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

-- Locally closed terms are not sorts and mention no bound variable.
srt-lc : ∀ m t → T (lcTm? 0 t) → srt m t ≡ nothing
srt-lc m (var _)       _ = refl
srt-lc m (bvar e j)    ()
srt-lc m (coh _ _ _)   _ = refl
srt-lc m (cst _)       _ = refl
srt-lc m (bnd _ _ _ _) _ = refl

∨-mono : ∀ a {b b′} → (T b → T b′) → T (a ∨ b) → T (a ∨ b′)
∨-mono true  f p = p
∨-mono false f p = f p

bv0?-lc : ∀ t → T (lcTm? 0 t) → bv0? t ≡ nothing
bv0?-lc (var _)       _ = refl
bv0?-lc (bvar e j)    ()
bv0?-lc (coh _ _ _)   _ = refl
bv0?-lc (cst _)       _ = refl
bv0?-lc (bnd _ _ _ _) _ = refl

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

  srt-[] : ∀ m t → srt m (t [ σ ]tm) ≡ srt m t
  srt-[] m (var i)       = srt-lc m (lookupₛ σ i) (lc-lookup σ i l)
  srt-[] m (bvar _ _)    = refl
  srt-[] m (coh _ _ _)   = refl
  srt-[] m (cst _)       = refl
  srt-[] m (bnd _ _ _ _) = refl

  isStar-[] : ∀ A → isStar (A [ σ ]ty) ≡ isStar A
  isStar-[] ⋆           = refl
  isStar-[] (arr _ _ _) = refl

  sorts-[] : ∀ Δ → sorts (Δ [ σ ]tel) ≡ sorts Δ
  sorts-[] ε       = refl
  sorts-[] (Δ ▸ A) rewrite sorts-[] Δ | len-tel[] Δ σ | isStar-[] A = refl

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

  srcOK-[] : ∀ m S → srcOK m (S [ σ ]tm) ≡ srcOK m S
  srcOK-[] m S = cong₂ _∨_ (cong is-just (srt-[] m S)) (cong not (mTm-[] 0 S))

  tgt-stable : ∀ m T₀ → T (tgtOK m T₀) → T (tgtOK m (T₀ [ σ ]tm))
  tgt-stable m (var _)       ()
  tgt-stable m (bvar _ _)    p = p
  tgt-stable m (coh _ _ _)   ()
  tgt-stable m (cst _)       p = p
  tgt-stable m (bnd _ _ _ _) ()

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

  okBase-stable : ∀ m mb → T (okBase m mb) → T (okBase m (mapP mb))
  okBase-stable m nothing        ()
  okBase-stable m (just (S , T₀)) p =
    let (a , c) = T∧ {srcOK m S} p in
    ∧T (subst T (sym (srcOK-[] m S)) a) (tgt-stable m T₀ c)

  entryOK-stable : ∀ m A → T (entryOK m A) → T (entryOK m (A [ σ ]ty))
  entryOK-stable m A p = subst (λ z → T (okBase m z)) (sym (base-[] A)) (okBase-stable m (base A) p)

  posFrom-stable : ∀ m Δ → T (posFrom m Δ) → T (posFrom m (Δ [ σ ]tel))
  posFrom-stable m ε       _ = tt
  posFrom-stable m (Δ ▸ A) p rewrite len-tel[] Δ σ =
    let (a , c) = T∧ {posFrom m Δ} p in
    ∧T (posFrom-stable m Δ a) (∨-mono (len Δ <ℕ m) (entryOK-stable m A) c)

  positive-stable : ∀ Δ → T (positive Δ) → T (positive (Δ [ σ ]tel))
  positive-stable Δ p rewrite sorts-[] Δ =
    let (a , c) = T∧ {0 <ℕ sorts Δ} p in ∧T a (posFrom-stable (sorts Δ) Δ c)

  bv0?-[] : ∀ t → bv0? (t [ σ ]tm) ≡ bv0? t
  bv0?-[] (var i)       = bv0?-lc (lookupₛ σ i) (lc-lookup σ i l)
  bv0?-[] (bvar zero _)    = refl
  bv0?-[] (bvar (suc _) _) = refl
  bv0?-[] (coh _ _ _)   = refl
  bv0?-[] (cst _)       = refl
  bv0?-[] (bnd _ _ _ _) = refl

  glob-[] : ∀ A → glob (A [ σ ]ty) ≡ glob A
  glob-[] ⋆                               = refl
  glob-[] (arr ⋆ _ _)                     = refl
  glob-[] (arr (arr ⋆ _ _) f g) rewrite bv0?-[] f | bv0?-[] g = refl
  glob-[] (arr (arr (arr _ _ _) _ _) _ _) = refl

  low-[] : ∀ A → low (A [ σ ]ty) ≡ low A
  low-[] A = cong₂ _∨_ (cong (_==ℕ 1) (dim-[] A σ)) (cong is-just (glob-[] A))

  lowFrom-[] : ∀ m Δ → lowFrom m (Δ [ σ ]tel) ≡ lowFrom m Δ
  lowFrom-[] m ε       = refl
  lowFrom-[] m (Δ ▸ A) rewrite len-tel[] Δ σ = cong₂ _∧_ (lowFrom-[] m Δ) (cong ((len Δ <ℕ m) ∨_) (low-[] A))

  lookup-[] : ∀ Δ y → lookup (Δ [ σ ]tel) y ≡ mapT (lookup Δ y)
  lookup-[] ε       y = refl
  lookup-[] (Δ ▸ A) y rewrite len-tel[] Δ σ with y ==ℕ len Δ
  ... | true  = refl
  ... | false = lookup-[] Δ y

  isMap-[] : ∀ Δ y → isMap? (lookup (Δ [ σ ]tel) y) ≡ isMap? (lookup Δ y)
  isMap-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = cong (_==ℕ 1) (dim-[] A σ)

  isLow-[] : ∀ Δ y → isLow? (lookup (Δ [ σ ]tel) y) ≡ isLow? (lookup Δ y)
  isLow-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = low-[] A

  globAt-[] : ∀ Δ y → globAt (Δ [ σ ]tel) y ≡ globAt Δ y
  globAt-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = glob-[] A

  inner-[] : ∀ y Δ → inner y (Δ [ σ ]tel) ≡ inner y Δ
  inner-[] y Δ rewrite len-tel[] Δ σ | sorts-[] Δ = refl

  isSortIx-[] : ∀ y Δ → isSortIx y (Δ [ σ ]tel) ≡ isSortIx y Δ
  isSortIx-[] y Δ rewrite sorts-[] Δ = refl

  sel-[] : ∀ b y Δ → sel b y (Δ [ σ ]tel) ≡ sel b y Δ
  sel-[] μ    y Δ = isSortIx-[] y Δ
  sel-[] η    y Δ = inner-[] y Δ
  sel-[] rec  y Δ = isSortIx-[] y Δ
  sel-[] recY y Δ = cong₂ _∧_ (inner-[] y Δ) (isLow-[] Δ y)
  sel-[] uni  y Δ = cong₂ _∧_ (isSortIx-[] y Δ) lf
    where lf = trans (cong (λ z → lowFrom z (Δ [ σ ]tel)) (sorts-[] Δ)) (lowFrom-[] (sorts Δ) Δ)
  sel-[] uniY y Δ = cong₂ _∧_ (cong₂ _∧_ (inner-[] y Δ) lf) (isMap-[] Δ y)
    where lf = trans (cong (λ z → lowFrom z (Δ [ σ ]tel)) (sorts-[] Δ)) (lowFrom-[] (sorts Δ) Δ)

  ----------------------------------------------------------------------
  -- The pieces of the argument telescopes and result types.

  ηAt-[] : ∀ Δ j → (ηAt Δ j) [ σ ]tm ≡ ηAt (Δ [ σ ]tel) j
  ηAt-[] Δ j rewrite if-[]tm (j <ℕ sorts Δ) (bnd μ j Δ ⟨⟩) (bnd η j Δ ⟨⟩) σ | sorts-[] Δ with j <ℕ sorts Δ
  ... | true  = refl
  ... | false = refl

  ηPre-∘ : ∀ Δ k → ηPre Δ k ∘ σ ≡ ηPre (Δ [ σ ]tel) k
  ηPre-∘ Δ zero    = refl
  ηPre-∘ Δ (suc k) = cong₂ _,ₛ_ (ηPre-∘ Δ k) (ηAt-[] Δ k)

  bvPre-∘ : ∀ k → bvPre k ∘ σ ≡ bvPre k
  bvPre-∘ zero    = refl
  bvPre-∘ (suc k) = cong (_,ₛ bvar 0 k) (bvPre-∘ k)

  actM-[] : ∀ mk S M h h′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) →
            (actM mk S M h) [ σ ]tm ≡ actM mk (S [ σ ]tm) (M ∘ σ) h′
  actM-[] (just k) S M h h′ e = e k
  actM-[] nothing  S M h h′ e = cong idm (op-[]tm 0 M S σ l)

  act-[] : ∀ m S M h h′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) →
           (act m S M h) [ σ ]tm ≡ act m (S [ σ ]tm) (M ∘ σ) h′
  act-[] m S M h h′ e rewrite srt-[] m S = actM-[] (srt m S) S M h h′ e

  cellTy-[] : ∀ m S T₀ M₁ M₂ s₁ s₂ h h′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) →
              (cellTy m S T₀ M₁ M₂ s₁ s₂ h) [ σ ]ty ≡
              cellTy m (S [ σ ]tm) (T₀ [ σ ]tm) (M₁ ∘ σ) (M₂ ∘ σ) (s₁ [ σ ]tm) (s₂ [ σ ]tm) h′
  cellTy-[] m S T₀ M₁ M₂ s₁ s₂ h h′ e
    rewrite act-[] m T₀ M₁ h h′ e | act-[] m S M₁ h h′ e
          | op-[]tm 0 M₁ S σ l | op-[]tm 0 M₁ T₀ σ l | op-[]tm 0 M₂ S σ l | op-[]tm 0 M₂ T₀ σ l = refl

  withBase-[] : ∀ mb (k k′ : Tm → Tm → Ty) → (∀ S T₀ → (k S T₀) [ σ ]ty ≡ k′ (S [ σ ]tm) (T₀ [ σ ]tm)) →
                (withBase mb k) [ σ ]ty ≡ withBase (mapP mb) k′
  withBase-[] nothing         k k′ e = refl
  withBase-[] (just (S , T₀)) k k′ e = e S T₀

  entryBase-[] : ∀ Δ y → entryBase (Δ [ σ ]tel) y ≡ mapP (entryBase Δ y)
  entryBase-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = base-[] A

  cell3Ty-[] : ∀ m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h h′ θf θg → (∀ k → (h k) [ σ ]tm ≡ h′ k) →
               (cell3Ty m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg) [ σ ]ty ≡
               cell3Ty m (S [ σ ]tm) (T₀ [ σ ]tm) (M₁ ∘ σ) (M₂ ∘ σ) (f₁ [ σ ]tm) (g₁ [ σ ]tm) (l₁ [ σ ]tm)
                       (f₂ [ σ ]tm) (g₂ [ σ ]tm) (l₂ [ σ ]tm) h′ (θf [ σ ]tm) (θg [ σ ]tm)
  cell3Ty-[] m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h h′ θf θg e
    rewrite act-[] m T₀ M₁ h h′ e | act-[] m S M₁ h h′ e
          | op-[]tm 0 M₁ S σ l | op-[]tm 0 M₁ T₀ σ l | op-[]tm 0 M₂ S σ l | op-[]tm 0 M₂ T₀ σ l = refl

  θSel-[] : ∀ Δ y h h′ th th′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) → (∀ i → (th i) [ σ ]tm ≡ th′ i) → ∀ S T₀ mg →
            (θSel Δ y h th S T₀ mg) [ σ ]ty ≡ θSel (Δ [ σ ]tel) y h′ th′ (S [ σ ]tm) (T₀ [ σ ]tm) mg
  θSel-[] Δ y h h′ th th′ eh e S T₀ nothing
    rewrite cellTy-[] (sorts Δ) S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h h′ eh
          | ηPre-∘ Δ (len Δ) | bvPre-∘ (len Δ) | ηAt-[] Δ y | len-tel[] Δ σ | sorts-[] Δ = refl
  θSel-[] Δ y h h′ th th′ eh e S T₀ (just (i , j))
    rewrite cell3Ty-[] (sorts Δ) S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ i) (ηAt Δ j) (ηAt Δ y)
                       (bvar 0 i) (bvar 0 j) (bvar 0 y) h h′ (th i) (th j) eh
          | ηPre-∘ Δ (len Δ) | bvPre-∘ (len Δ) | ηAt-[] Δ i | ηAt-[] Δ j | ηAt-[] Δ y
          | len-tel[] Δ σ | sorts-[] Δ | e i | e j = refl

  θBody-[] : ∀ Δ y h h′ th th′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) → (∀ i → (th i) [ σ ]tm ≡ th′ i) → ∀ S T₀ →
             (θBody Δ y h th S T₀) [ σ ]ty ≡ θBody (Δ [ σ ]tel) y h′ th′ (S [ σ ]tm) (T₀ [ σ ]tm)
  θBody-[] Δ y h h′ th th′ eh e S T₀ =
    trans (θSel-[] Δ y h h′ th th′ eh e S T₀ (globAt Δ y))
          (cong (θSel (Δ [ σ ]tel) y h′ th′ (S [ σ ]tm) (T₀ [ σ ]tm)) (sym (globAt-[] Δ y)))

  θTy-[] : ∀ Δ y h h′ th th′ → (∀ k → (h k) [ σ ]tm ≡ h′ k) → (∀ i → (th i) [ σ ]tm ≡ th′ i) →
           (θTy Δ y h th) [ σ ]ty ≡ θTy (Δ [ σ ]tel) y h′ th′
  θTy-[] Δ y h h′ th th′ eh e =
    trans (withBase-[] (entryBase Δ y) (θBody Δ y h th) (θBody (Δ [ σ ]tel) y h′ th′)
                       (θBody-[] Δ y h h′ th th′ eh e))
          (cong (λ z → withBase z (θBody (Δ [ σ ]tel) y h′ th′)) (sym (entryBase-[] Δ y)))

  morEntry-[] : ∀ Δ o k → (morEntry Δ o k) [ σ ]ty ≡ morEntry (Δ [ σ ]tel) o k
  morEntry-[] Δ o k rewrite sorts-[] Δ with k <ℕ sorts Δ
  ... | true  = refl
  ... | false = θTy-[] Δ k (λ i → bvar 0 (o + i)) (λ i → bvar 0 (o + i))
                       (λ i → bvar 0 (o + i)) (λ i → bvar 0 (o + i)) (λ _ → refl) (λ _ → refl)

  morPre-[] : ∀ Δ o k → (morPre Δ o k) [ σ ]tel ≡ morPre (Δ [ σ ]tel) o k
  morPre-[] Δ o zero    = refl
  morPre-[] Δ o (suc k) = cong₂ _▸_ (morPre-[] Δ o k) (morEntry-[] Δ o k)

  morTel-[] : ∀ Δ o → (morTel Δ o) [ σ ]tel ≡ morTel (Δ [ σ ]tel) o
  morTel-[] Δ o = trans (morPre-[] Δ o (len Δ)) (cong (morPre (Δ [ σ ]tel) o) (sym (len-tel[] Δ σ)))

  uActM-[] : ∀ mk S₁ u u′ → (∀ k → (u k) [ σ ]tm ≡ u′ k) →
             (uActM mk S₁ u) [ σ ]tm ≡ uActM mk (S₁ [ σ ]tm) u′
  uActM-[] (just k) S₁ u u′ e = e k
  uActM-[] nothing  S₁ u u′ e = refl

  uniYBody-[] : ∀ Δ y S T₀ → (uniYBody Δ y S T₀) [ σ ]ty ≡ uniYBody (Δ [ σ ]tel) y (S [ σ ]tm) (T₀ [ σ ]tm)
  uniYBody-[] Δ y S T₀
    rewrite uActM-[] (srt (sorts Δ) T₀) (opTm 0 (ηPre Δ (len Δ)) T₀)
                     (λ k → bnd uni k Δ (bvPre (len Δ + len Δ + len Δ)))
                     (λ k → bnd uni k (Δ [ σ ]tel) (bvPre (len Δ + len Δ + len Δ)))
                     (λ k → cong (bnd uni k (Δ [ σ ]tel)) (bvPre-∘ (len Δ + len Δ + len Δ)))
          | uActM-[] (srt (sorts Δ) S) (opTm 0 (ηPre Δ (len Δ)) S)
                     (λ k → bnd uni k Δ (bvPre (len Δ + len Δ + len Δ)))
                     (λ k → bnd uni k (Δ [ σ ]tel) (bvPre (len Δ + len Δ + len Δ)))
                     (λ k → cong (bnd uni k (Δ [ σ ]tel)) (bvPre-∘ (len Δ + len Δ + len Δ)))
          | act-[] (sorts Δ) T₀ (ηPre Δ (len Δ)) (λ k → bvar 0 (len Δ + k)) (λ k → bvar 0 (len Δ + k)) (λ _ → refl)
          | act-[] (sorts Δ) T₀ (ηPre Δ (len Δ)) (λ k → bvar 0 (len Δ + len Δ + k)) (λ k → bvar 0 (len Δ + len Δ + k)) (λ _ → refl)
          | act-[] (sorts Δ) S (ηPre Δ (len Δ)) (λ k → bvar 0 (len Δ + k)) (λ k → bvar 0 (len Δ + k)) (λ _ → refl)
          | act-[] (sorts Δ) S (ηPre Δ (len Δ)) (λ k → bvar 0 (len Δ + len Δ + k)) (λ k → bvar 0 (len Δ + len Δ + k)) (λ _ → refl)
          | op-[]tm 0 (ηPre Δ (len Δ)) S σ l | op-[]tm 0 (ηPre Δ (len Δ)) T₀ σ l
          | op-[]tm 0 (bvPre (len Δ)) S σ l | op-[]tm 0 (bvPre (len Δ)) T₀ σ l
          | ηPre-∘ Δ (len Δ) | bvPre-∘ (len Δ)
          | ηAt-[] Δ y | len-tel[] Δ σ | sorts-[] Δ
          | srt-[] (sorts Δ) S | srt-[] (sorts Δ) T₀ = refl

------------------------------------------------------------------------
-- Scoping of the result types.

module _ (n : Nat) where

  private
    sc∧ : ∀ {a b} → T a → T b → T (a ∧ b)
    sc∧ = ∧T

  sc-arr : ∀ A t u → T (scTy? n A) → T (scTm? n t) → T (scTm? n u) → T (scTy? n (arr A t u))
  sc-arr A t u pA pt pu = ∧T {scTy? n A} pA (∧T {scTm? n t} pt pu)

  sc-ηAt : ∀ Δ j → T (scTel? n Δ) → T (scTm? n (ηAt Δ j))
  sc-ηAt Δ j p with j <ℕ sorts Δ
  ... | true  = ∧T p tt
  ... | false = ∧T p tt

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

  sc-actM : ∀ mk S M h → T (scTm? n S) → T (scSub? n M) → (∀ k → T (scTm? n (h k))) →
            T (scTm? n (actM mk S M h))
  sc-actM (just k) S M h pS pM ph = ph k
  sc-actM nothing  S M h pS pM ph = sc-idm (opTm 0 M S) (sc-opTm 0 M S pM pS)

  sc-act : ∀ m S M h → T (scTm? n S) → T (scSub? n M) → (∀ k → T (scTm? n (h k))) →
           T (scTm? n (act m S M h))
  sc-act m S M h = sc-actM (srt m S) S M h

  sc-uActM : ∀ mk S₁ u → T (scTm? n S₁) → (∀ k → T (scTm? n (u k))) → T (scTm? n (uActM mk S₁ u))
  sc-uActM (just k) S₁ u pS pu = pu k
  sc-uActM nothing  S₁ u pS pu = sc-id2 S₁ S₁ (idm S₁) pS pS (sc-idm S₁ pS)

  sc-cellTy : ∀ m S T₀ M₁ M₂ s₁ s₂ h → T (scTm? n S) → T (scTm? n T₀) → T (scSub? n M₁) → T (scSub? n M₂) →
              T (scTm? n s₁) → T (scTm? n s₂) → (∀ k → T (scTm? n (h k))) → T (scTy? n (cellTy m S T₀ M₁ M₂ s₁ s₂ h))
  sc-cellTy m S T₀ M₁ M₂ s₁ s₂ h pS pT p₁ p₂ ps₁ ps₂ ph =
    sc-arr (arr ⋆ a₁ d₂) (cmp a₁ c₁ d₂ s₁ th) (cmp a₁ a₂ d₂ sh s₂)
      (sc-arr ⋆ a₁ d₂ tt S₁ T₂)
      (sc-cmp a₁ c₁ d₂ s₁ th S₁ T₁ T₂ ps₁ (sc-act m T₀ M₁ h pT p₁ ph))
      (sc-cmp a₁ a₂ d₂ sh s₂ S₁ S₂ T₂ (sc-act m S M₁ h pS p₁ ph) ps₂)
    where
    a₁ = opTm 0 M₁ S
    a₂ = opTm 0 M₂ S
    c₁ = opTm 0 M₁ T₀
    d₂ = opTm 0 M₂ T₀
    th = act m T₀ M₁ h
    sh = act m S M₁ h
    S₁ = sc-opTm 0 M₁ S p₁ pS
    S₂ = sc-opTm 0 M₂ S p₂ pS
    T₁ = sc-opTm 0 M₁ T₀ p₁ pT
    T₂ = sc-opTm 0 M₂ T₀ p₂ pT

  sc-cell3Ty : ∀ m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg → T (scTm? n S) → T (scTm? n T₀) →
               T (scSub? n M₁) → T (scSub? n M₂) → T (scTm? n f₁) → T (scTm? n g₁) → T (scTm? n l₁) →
               T (scTm? n f₂) → T (scTm? n g₂) → T (scTm? n l₂) → (∀ k → T (scTm? n (h k))) →
               T (scTm? n θf) → T (scTm? n θg) → T (scTy? n (cell3Ty m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg))
  sc-cell3Ty m S T₀ M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg pS pT p₁ p₂ pf₁ pg₁ pl₁ pf₂ pg₂ pl₂ ph pθf pθg =
    sc-arr (arr (arr ⋆ a₁ d₂) src tgt) lhs rhs
      (sc-arr (arr ⋆ a₁ d₂) src tgt (sc-arr ⋆ a₁ d₂ tt S₁ T₂) Src Tgt)
      (sc-vcomp a₁ d₂ src (cmp a₁ c₁ d₂ g₁ th) (rwh a₁ c₁ d₂ f₁ g₁ l₁ th) tgt θg
         S₁ T₂ Src (sc-cmp a₁ c₁ d₂ g₁ th S₁ T₁ T₂ pg₁ Th)
         (sc-rwh a₁ c₁ d₂ f₁ g₁ l₁ th S₁ T₁ T₂ pf₁ pg₁ pl₁ Th) Tgt pθg)
      (sc-vcomp a₁ d₂ src (cmp a₁ a₂ d₂ sh f₂) θf tgt (lwh a₁ a₂ d₂ sh f₂ g₂ l₂)
         S₁ T₂ Src (sc-cmp a₁ a₂ d₂ sh f₂ S₁ S₂ T₂ Sh pf₂) pθf Tgt
         (sc-lwh a₁ a₂ d₂ sh f₂ g₂ l₂ S₁ S₂ T₂ Sh pf₂ pg₂ pl₂))
    where
    a₁ = opTm 0 M₁ S
    a₂ = opTm 0 M₂ S
    c₁ = opTm 0 M₁ T₀
    d₂ = opTm 0 M₂ T₀
    th = act m T₀ M₁ h
    sh = act m S M₁ h
    src = cmp a₁ c₁ d₂ f₁ th
    tgt = cmp a₁ a₂ d₂ sh g₂
    lhs = vcomp a₁ d₂ src (cmp a₁ c₁ d₂ g₁ th) (rwh a₁ c₁ d₂ f₁ g₁ l₁ th) tgt θg
    rhs = vcomp a₁ d₂ src (cmp a₁ a₂ d₂ sh f₂) θf tgt (lwh a₁ a₂ d₂ sh f₂ g₂ l₂)
    S₁ = sc-opTm 0 M₁ S p₁ pS
    S₂ = sc-opTm 0 M₂ S p₂ pS
    T₁ = sc-opTm 0 M₁ T₀ p₁ pT
    T₂ = sc-opTm 0 M₂ T₀ p₂ pT
    Th = sc-act m T₀ M₁ h pT p₁ ph
    Sh = sc-act m S M₁ h pS p₁ ph
    Src = sc-cmp a₁ c₁ d₂ f₁ th S₁ T₁ T₂ pf₁ Th
    Tgt = sc-cmp a₁ a₂ d₂ sh g₂ S₁ S₂ T₂ Sh pg₂

  sc-θSel : ∀ Δ y h th S T₀ mg → T (scTel? n Δ) → (∀ k → T (scTm? n (h k))) → (∀ i → T (scTm? n (th i))) →
            T (scTm? n S) → T (scTm? n T₀) → T (scTy? n (θSel Δ y h th S T₀ mg))
  sc-θSel Δ y h th S T₀ nothing p ph pth pS pT =
    sc-cellTy (sorts Δ) S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h pS pT
      (sc-ηPre Δ (len Δ) p) (sc-bvPre (len Δ)) (sc-ηAt Δ y p) tt ph
  sc-θSel Δ y h th S T₀ (just (i , j)) p ph pth pS pT =
    sc-cell3Ty (sorts Δ) S T₀ (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ i) (ηAt Δ j) (ηAt Δ y)
      (bvar 0 i) (bvar 0 j) (bvar 0 y) h (th i) (th j) pS pT
      (sc-ηPre Δ (len Δ) p) (sc-bvPre (len Δ)) (sc-ηAt Δ i p) (sc-ηAt Δ j p) (sc-ηAt Δ y p)
      tt tt tt ph (pth i) (pth j)

  sc-θTy : ∀ Δ y h th → T (scTel? n Δ) → (∀ k → T (scTm? n (h k))) → (∀ i → T (scTm? n (th i))) →
           T (scTy? n (θTy Δ y h th))
  sc-θTy Δ y h th p ph pth =
    sc-withBase (entryBase Δ y) (θBody Δ y h th) λ S T₀ e →
      let (pS , pT) = sc-entryBase Δ y p e in
      sc-θSel Δ y h th S T₀ (globAt Δ y) p ph pth pS pT

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
    k₀  = sorts Δ
    M₁  = ηPre Δ m
    M₂  = bvPre m
    s₁  = opTm 0 M₁ S
    s₂  = opTm 0 M₂ S
    t₁  = opTm 0 M₁ T₀
    t₂  = opTm 0 M₂ T₀
    u   = λ k → bnd uni k Δ (bvPre (m + m + m))
    hh  = λ k → bvar 0 (m + k)
    hh′ = λ k → bvar 0 (m + m + k)
    ηy  = ηAt Δ y
    σy  = bvar 0 y
    th  = act k₀ T₀ M₁ hh
    th′ = act k₀ T₀ M₁ hh′
    sh  = act k₀ S M₁ hh
    sh′ = act k₀ S M₁ hh′
    tu  = uActM (srt k₀ T₀) t₁ u
    su  = uActM (srt k₀ S) s₁ u
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
    pu  : ∀ k → T (scTm? n (u k))
    pu  k = ∧T {scTel? n Δ} p (sc-bvPre (m + m + m))
    Ηy  = sc-ηAt Δ y p
    Th  = sc-act k₀ T₀ M₁ hh pT pM₁ (λ _ → tt)
    Th′ = sc-act k₀ T₀ M₁ hh′ pT pM₁ (λ _ → tt)
    Sh  = sc-act k₀ S M₁ hh pS pM₁ (λ _ → tt)
    Sh′ = sc-act k₀ S M₁ hh′ pS pM₁ (λ _ → tt)
    Tu  = sc-uActM (srt k₀ T₀) t₁ u T₁ pu
    Su  = sc-uActM (srt k₀ S) s₁ u S₁ pu
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
  sc-res recY y Δ p =
    sc-θTy Δ y _ _ p (λ k → ∧T {scTel? n Δ} p (sc-bvPre (len Δ))) (λ i → ∧T {scTel? n Δ} p (sc-bvPre (len Δ)))
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
    sym (trans (θTy-[] σ l Δ y (λ k → bnd rec k Δ (bvPre (len Δ))) (λ k → bnd rec k (Δ [ σ ]tel) (bvPre (len Δ)))
                       (λ i → bnd recY i Δ (bvPre (len Δ))) (λ i → bnd recY i (Δ [ σ ]tel) (bvPre (len Δ)))
                       (λ k → cong (bnd rec k (Δ [ σ ]tel)) (bvPre-∘ σ l (len Δ)))
                       (λ i → cong (bnd recY i (Δ [ σ ]tel)) (bvPre-∘ σ l (len Δ))))
               (cong (λ z → θTy (Δ [ σ ]tel) y (λ k → bnd rec k (Δ [ σ ]tel) (bvPre z)) (λ i → bnd recY i (Δ [ σ ]tel) (bvPre z)))
                     (sym (len-tel[] Δ σ))))
  res-st uni  y Δ σ l _ rewrite len-tel[] Δ σ = refl
  res-st uniY y Δ σ l _ =
    sym (trans (withBase-[] σ l (entryBase Δ y) (uniYBody Δ y) (uniYBody (Δ [ σ ]tel) y) (uniYBody-[] σ l Δ y))
               (cong (λ z → withBase z (uniYBody (Δ [ σ ]tel) y)) (sym (entryBase-[] σ l Δ y))))
