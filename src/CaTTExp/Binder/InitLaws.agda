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
--    each is built from Δ by opening and the naturality cylinders of
--    CaTTExp.Binder.Cyl, which commute with σ (CaTTExp.Binder.CylLaws:
--    σ acts on free variables only, and the cylinders' data commute
--    with it); σ does not change the number of sorts, nor which entries
--    the dimension-1 fillers cover (CaTTExp.Binder.CylOK.goodTy-[]).
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
open import CaTTExp.Naturality.DimOne using (K₁)
open import CaTTExp.Binder.CylOne 𝕊c using (K₁-scB)
open import CaTTExp.Binder.CylOK 𝕊c using (goodTy-[])
import CaTTExp.Binder.CylLaws 𝕊c K₁ as CL

------------------------------------------------------------------------
-- Generic helpers.

if-[]tm : ∀ c x y σ → (if c then x else y) [ σ ]tm ≡ (if c then (x [ σ ]tm) else (y [ σ ]tm))
if-[]tm true  x y σ = refl
if-[]tm false x y σ = refl

⧺-[] : ∀ Γ Ξ σ → (Γ ⧺ Ξ) [ σ ]tel ≡ (Γ [ σ ]tel) ⧺ (Ξ [ σ ]tel)
⧺-[] Γ ε       σ = refl
⧺-[] Γ (Ξ ▸[ ms ] A) σ = cong (_▸[ ms ] (A [ σ ]ty)) (⧺-[] Γ Ξ σ)

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
  mTel-lc d (Δ ▸[ _ ] A) p = let (a , b) = T∧ {lcTel? d Δ} p in ∨ff (mTel-lc d Δ a) (mTy-lc d A b)

  mSub-lc : ∀ d σ → T (lcSub? d σ) → mSub d σ ≡ false
  mSub-lc d ⟨⟩ _ = refl
  mSub-lc d (σ ,ₛ t) p = let (a , b) = T∧ {lcSub? d σ} p in ∨ff (mSub-lc d σ a) (mTm-lc d t b)

------------------------------------------------------------------------
-- Sorts over bases: `basedOK` only reads per-entry data (`Info`), and
-- is monotone in it.

record Rel (I I′ : Info) : Set where
  field
    hs≡ : ∀ j → Info.hs I j ≡ Info.hs I′ j
    ts≡ : ∀ j → Info.ts I j ≡ Info.ts I′ j
    tp→ : ∀ j → T (Info.tp I j) → T (Info.tp I′ j)
    dm≡ : ∀ j → Info.dm I j ≡ Info.dm I′ j
    cm→ : ∀ j x → Info.cm I j ≡ just x → Info.cm I′ j ≡ just x
    iv≡ : ∀ j → Info.iv I j ≡ Info.iv I′ j

hdrGo-ext : ∀ hs hs′ → (∀ j → hs j ≡ hs′ j) → ∀ f j lo → hdrGo hs f j lo ≡ hdrGo hs′ f j lo
hdrGo-ext hs hs′ e zero    j lo = refl
hdrGo-ext hs hs′ e (suc f) j lo rewrite e j with hs′ j
... | nothing = refl
... | just k  = cong (λ z → if k <ℕ lo then 0 else suc z) (hdrGo-ext hs hs′ e f (suc j) (suc k))

findHdr-ext : ∀ hs hs′ → (∀ j → hs j ≡ hs′ j) → ∀ k c j → findHdr hs k c j ≡ findHdr hs′ k c j
findHdr-ext hs hs′ e k zero    j = refl
findHdr-ext hs hs′ e k (suc c) j rewrite e j =
  cong (if eqMN (hs′ j) k then just j else_) (findHdr-ext hs hs′ e k c (suc j))

cmpIs-mono : ∀ m m′ k j p → (∀ x → m ≡ just x → m′ ≡ just x) → T (cmpIs m k j p) → T (cmpIs m′ k j p)
cmpIs-mono (just x) m′ k j p f q rewrite f x refl = q

okB-mono : ∀ {I I′} → Rel I I′ → ∀ n L j → T (okB n L I j) → T (okB n L I′ j)
okB-mono {I} {I′} R n L j p
  rewrite sym (hdrGo-ext (Info.hs I) (Info.hs I′) (Rel.hs≡ R) L n 0)
  with j <ℕ (n + hdrGo (Info.hs I) L n 0)
... | true  = tt
... | false = tgt (Info.ts I j) (Info.ts I′ j) (Rel.ts≡ R j) p
  where
  h = hdrGo (Info.hs I) L n 0
  fh : ∀ k → findHdr (Info.hs I) k h n ≡ findHdr (Info.hs I′) k h n
  fh k = findHdr-ext (Info.hs I) (Info.hs I′) (Rel.hs≡ R) k h n

  based : ∀ k mp → T (okBased I j k h mp) → T (okBased I′ j k h mp)
  based k nothing  q = tt
  based k (just q₀) q rewrite sym (Rel.dm≡ R j) | sym (Rel.iv≡ R (suc j)) =
    let (a , r) = T∧ {Info.dm I j ==ℕ 1} q
        (b , c) = T∧ {cmpIs (Info.cm I (suc j)) k j q₀} r
    in ∧T a (∧T (cmpIs-mono _ _ k j q₀ (Rel.cm→ R (suc j)) b) c)

  comp : ∀ m → (∀ x → m ≡ just x → Info.cm I′ j ≡ just x) → T (okComp I n h j m) → T (okComp I′ n h j (Info.cm I′ j))
  comp (just (k , j′ , q₀)) f q rewrite f (k , j′ , q₀) refl | sym (fh k) = q

  tgt : ∀ m m′ → m ≡ m′ → T (okTgt I n h j m) → T (okTgt I′ n h j m′)
  tgt (just k) .(just k) refl q rewrite sym (fh k) = based k (findHdr (Info.hs I) k h n) q
  tgt nothing  .nothing  refl q with Info.tp I j in e
  ... | true  = subst (λ z → T (z ∨ okComp I′ n h j (Info.cm I′ j))) (sym (T→≡ (Rel.tp→ R j (subst T (sym e) tt)))) tt
  ... | false = ∨-mono (Info.tp I′ j) (comp (Info.cm I j) (Rel.cm→ R j)) (T∨ʳ (Info.tp I′ j) q)
    where
    T∨ʳ : ∀ a {b} → T b → T (a ∨ b)
    T∨ʳ true  _ = tt
    T∨ʳ false q = q

allBelow-mono : ∀ L f g → (∀ j → T (f j) → T (g j)) → T (allBelow L f) → T (allBelow L g)
allBelow-mono zero    f g h p = tt
allBelow-mono (suc L) f g h p =
  let (a , b) = T∧ {allBelow L f} p in ∧T (allBelow-mono L f g h a) (h L b)

------------------------------------------------------------------------
-- Substitution by a locally closed σ.

module _ (σ : Sub) (l : LC σ) where

  module CS = CL.Subst σ l

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
  sorts-[] (Δ ▸[ _ ] A) rewrite sorts-[] Δ | len-tel[] Δ σ | isStar-[] A = refl

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
    mTel-[] d (Δ ▸[ _ ] A) = cong₂ _∨_ (mTel-[] d Δ) (mTy-[] d A)

    mSub-[] : ∀ d τ → mSub d (τ ∘ σ) ≡ mSub d τ
    mSub-[] d ⟨⟩ = refl
    mSub-[] d (τ ,ₛ t) = cong₂ _∨_ (mSub-[] d τ) (mTm-[] d t)

  srcOK-[] : ∀ m S → srcOK m (S [ σ ]tm) ≡ srcOK m S
  srcOK-[] m S = cong₂ _∨_ (cong is-just (srt-[] m S)) (cong not (mTm-[] 0 S))

  tgt-stable : ∀ m T₀ → T (tgtOK m T₀) → T (tgtOK m (T₀ [ σ ]tm))
  tgt-stable m T₀ p = subst T (sym (srcOK-[] m T₀)) p

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
  posFrom-stable m (Δ ▸[ ms ] A) p rewrite len-tel[] Δ σ =
    let (a , c) = T∧ {posFrom m Δ} p
        (b , d) = T∧ {marksOKAt m (len Δ) ms} c in
    ∧T (posFrom-stable m Δ a) (∧T b (∨-mono (len Δ <ℕ m) (entryOK-stable m A) d))

  bv0?-[] : ∀ t → bv0? (t [ σ ]tm) ≡ bv0? t
  bv0?-[] (var i)       = bv0?-lc (lookupₛ σ i) (lc-lookup σ i l)
  bv0?-[] (bvar zero _)    = refl
  bv0?-[] (bvar (suc _) _) = refl
  bv0?-[] (coh _ _ _)   = refl
  bv0?-[] (cst _)       = refl
  bv0?-[] (bnd _ _ _ _) = refl

  lookup-[] : ∀ Δ y → lookup (Δ [ σ ]tel) y ≡ mapT (lookup Δ y)
  lookup-[] ε       y = refl
  lookup-[] (Δ ▸[ _ ] A) y rewrite len-tel[] Δ σ with y ==ℕ len Δ
  ... | true  = refl
  ... | false = lookup-[] Δ y

  inner-[] : ∀ y Δ → inner y (Δ [ σ ]tel) ≡ inner y Δ
  inner-[] y Δ rewrite len-tel[] Δ σ | sorts-[] Δ = refl

  isSortIx-[] : ∀ y Δ → isSortIx y (Δ [ σ ]tel) ≡ isSortIx y Δ
  isSortIx-[] y Δ rewrite sorts-[] Δ = refl

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

  entryBase-[] : ∀ Δ y → entryBase (Δ [ σ ]tel) y ≡ mapP (entryBase Δ y)
  entryBase-[] Δ y rewrite lookup-[] Δ y with lookup Δ y
  ... | nothing = refl
  ... | just A  = base-[] A

  -- Sorts over bases: the per-entry data of `basedOK`.
  hdrShape-[] : ∀ n A → hdrShape n (A [ σ ]ty) ≡ hdrShape n A
  hdrShape-[] n ⋆                     = refl
  hdrShape-[] n (arr ⋆ S B)           rewrite mTm-[] 0 B | srt-[] n S = refl
  hdrShape-[] n (arr (arr _ _ _) _ _) = refl

  cmpSub-[] : ∀ τ → cmpSub (τ ∘ σ) ≡ cmpSub τ
  cmpSub-[] ⟨⟩ = refl
  cmpSub-[] (⟨⟩ ,ₛ _) = refl
  cmpSub-[] (⟨⟩ ,ₛ _ ,ₛ _) = refl
  cmpSub-[] (⟨⟩ ,ₛ _ ,ₛ _ ,ₛ _) = refl
  cmpSub-[] (⟨⟩ ,ₛ _ ,ₛ _ ,ₛ _ ,ₛ _) = refl
  cmpSub-[] (⟨⟩ ,ₛ _ ,ₛ x ,ₛ a ,ₛ _ ,ₛ q) rewrite bv0?-[] x | bv0?-[] a | bv0?-[] q = refl
  cmpSub-[] ((_ ,ₛ _) ,ₛ _ ,ₛ _ ,ₛ _ ,ₛ _ ,ₛ _) = refl

  cmpShape-[] : ∀ A x → cmpShape A ≡ just x → cmpShape (A [ σ ]ty) ≡ just x
  cmpShape-[] ⋆ x ()
  cmpShape-[] (arr ⋆ _ _) x ()
  cmpShape-[] (arr (arr ⋆ _ _) (coh Γ A τ) _) x e rewrite cmpSub-[] τ = e
  cmpShape-[] (arr (arr ⋆ _ _) (var _) _) x ()
  cmpShape-[] (arr (arr ⋆ _ _) (bvar _ _) _) x ()
  cmpShape-[] (arr (arr ⋆ _ _) (cst _) _) x ()
  cmpShape-[] (arr (arr ⋆ _ _) (bnd _ _ _ _) _) x ()
  cmpShape-[] (arr (arr (arr _ _ _) _ _) _ _) x ()

  isTop-[] : ∀ t → T (isTop? t) → T (isTop? (t [ σ ]tm))
  isTop-[] (cst _) p = p

  marksAt-[] : ∀ Δ j → marksAt (Δ [ σ ]tel) j ≡ marksAt Δ j
  marksAt-[] ε j = refl
  marksAt-[] (Δ ▸[ _ ] A) j rewrite len-tel[] Δ σ with j ==ℕ len Δ
  ... | true  = refl
  ... | false = marksAt-[] Δ j

  info-[] : ∀ Δ → Rel (infoOf Δ) (infoOf (Δ [ σ ]tel))
  info-[] Δ = record
    { hs≡ = λ j → sym (hs-eq j)
    ; ts≡ = λ j → sym (ts-eq j)
    ; tp→ = tp-imp
    ; dm≡ = λ j → sym (dm-eq j)
    ; cm→ = cm-imp
    ; iv≡ = λ j → cong (minv ∈M_) (sym (marksAt-[] Δ j))
    }
    where
    hs-eq : ∀ j → mapMT (hdrShape (sorts (Δ [ σ ]tel))) nothing (lookup (Δ [ σ ]tel) j)
                ≡ mapMT (hdrShape (sorts Δ)) nothing (lookup Δ j)
    hs-eq j rewrite sorts-[] Δ | lookup-[] Δ j with lookup Δ j
    ... | nothing = refl
    ... | just A  = hdrShape-[] (sorts Δ) A

    ts-eq : ∀ j → tgtSrtB (sorts (Δ [ σ ]tel)) (entryBase (Δ [ σ ]tel) j) ≡ tgtSrtB (sorts Δ) (entryBase Δ j)
    ts-eq j rewrite sorts-[] Δ | entryBase-[] Δ j with entryBase Δ j
    ... | nothing       = refl
    ... | just (_ , T₀) = srt-[] (sorts Δ) T₀

    tp-imp : ∀ j → T (tgtTopB (entryBase Δ j)) → T (tgtTopB (entryBase (Δ [ σ ]tel) j))
    tp-imp j p rewrite entryBase-[] Δ j with entryBase Δ j
    ... | just (_ , T₀) = isTop-[] T₀ p

    dm-eq : ∀ j → mapMT dim 0 (lookup (Δ [ σ ]tel) j) ≡ mapMT dim 0 (lookup Δ j)
    dm-eq j rewrite lookup-[] Δ j with lookup Δ j
    ... | nothing = refl
    ... | just A  = dim-[] A σ

    cm-imp : ∀ j x → mapMT cmpShape nothing (lookup Δ j) ≡ just x →
             mapMT cmpShape nothing (lookup (Δ [ σ ]tel) j) ≡ just x
    cm-imp j x e rewrite lookup-[] Δ j with lookup Δ j
    ... | just A = cmpShape-[] A x e

  basedOK-stable : ∀ Δ → T (basedOK Δ) → T (basedOK (Δ [ σ ]tel))
  basedOK-stable Δ p =
    tr (sorts-[] Δ) (len-tel[] Δ σ)
      (allBelow-mono (len Δ) (okB (sorts Δ) (len Δ) (infoOf Δ))
         (okB (sorts Δ) (len Δ) (infoOf (Δ [ σ ]tel)))
         (okB-mono (info-[] Δ) (sorts Δ) (len Δ)) p)
    where
    tr : ∀ {n n′ L L′} → n′ ≡ n → L′ ≡ L
       → T (allBelow L (okB n L (infoOf (Δ [ σ ]tel))))
       → T (allBelow L′ (okB n′ L′ (infoOf (Δ [ σ ]tel))))
    tr refl refl q = q

  positive-stable : ∀ Δ → T (positive Δ) → T (positive (Δ [ σ ]tel))
  positive-stable Δ p =
    let (ab , c) = T∧ {(0 <ℕ sorts Δ) ∧ posFrom (sorts Δ) Δ} p
        (a , b)  = T∧ {0 <ℕ sorts Δ} ab
    in ∧T (∧T (subst (λ n → T (0 <ℕ n)) (sym (sorts-[] Δ)) a)
              (subst (λ n → T (posFrom n (Δ [ σ ]tel))) (sym (sorts-[] Δ)) (posFrom-stable (sorts Δ) Δ b)))
          (basedOK-stable Δ c)

  ----------------------------------------------------------------------
  -- The arrow context and the results, as cylinders (CaTTExp.Binder.
  -- CylLaws: cylinders commute with σ when the datum does).

  okBelow-[] : ∀ m Δ → okBelow m (Δ [ σ ]tel) ≡ okBelow m Δ
  okBelow-[] m ε             = refl
  okBelow-[] m (Δ ▸[ _ ] A) rewrite len-tel[] Δ σ | okBelow-[] m Δ | goodTy-[] σ l allSel A = refl

  entryTy-[] : ∀ Δ j → entryTy (Δ [ σ ]tel) j ≡ entryTy Δ j [ σ ]ty
  entryTy-[] Δ j rewrite lookup-[] Δ j with lookup Δ j
  ... | nothing = refl
  ... | just A  = refl

  len≡ : ∀ Δ → len (Δ [ σ ]tel) ≡ len Δ
  len≡ Δ = len-tel[] Δ σ

  θTy-[] : ∀ Δ k th th′ → (∀ i → th i [ σ ]tm ≡ th′ i) → θTy Δ k th [ σ ]ty ≡ θTy (Δ [ σ ]tel) k th′
  θTy-[] Δ k th th′ e =
    trans (CS.cylTy-[] K₁-scB R (bvar 0 k) (entryTy Δ k))
          (cong (cylTy (morD (Δ [ σ ]tel) th′) (bvar 0 k)) (sym (entryTy-[] Δ k)))
    where
    R : CS.Rel (morD Δ th) (morD (Δ [ σ ]tel) th′)
    R = record { mmR  = trans (ηPre-∘ Δ (len Δ)) (cong (ηPre (Δ [ σ ]tel)) (sym (len≡ Δ)))
               ; mpR  = trans (bvPre-∘ (len Δ)) (cong bvPre (sym (len≡ Δ)))
               ; selR = λ _ → refl
               ; thR  = e }

  morEntry-[] : ∀ Δ o k → (morEntry Δ o k) [ σ ]ty ≡ morEntry (Δ [ σ ]tel) o k
  morEntry-[] Δ o k = θTy-[] Δ k _ _ (λ _ → refl)

  morPre-[] : ∀ Δ o k → (morPre Δ o k) [ σ ]tel ≡ morPre (Δ [ σ ]tel) o k
  morPre-[] Δ o zero    = refl
  morPre-[] Δ o (suc k) = cong₂ _▸_ (morPre-[] Δ o k) (morEntry-[] Δ o k)

  morTel-[] : ∀ Δ o → (morTel Δ o) [ σ ]tel ≡ morTel (Δ [ σ ]tel) o
  morTel-[] Δ o = trans (morPre-[] Δ o (len Δ)) (cong (morPre (Δ [ σ ]tel) o) (sym (len-tel[] Δ σ)))

  recTh-[] : ∀ Δ i → recTh Δ i [ σ ]tm ≡ recTh (Δ [ σ ]tel) i
  recTh-[] Δ i
    rewrite if-[]tm (i <ℕ sorts Δ) (bnd rec i Δ (bvPre (len Δ))) (bnd recY i Δ (bvPre (len Δ))) σ
          | sorts-[] Δ | len≡ Δ | bvPre-∘ (len Δ) with i <ℕ sorts Δ
  ... | true  = refl
  ... | false = refl

  uniTh-[] : ∀ Δ i → uniTh Δ i [ σ ]tm ≡ uniTh (Δ [ σ ]tel) i
  uniTh-[] Δ i
    rewrite if-[]tm (i <ℕ sorts Δ) (bnd uni i Δ (bvPre (len Δ + len Δ + len Δ)))
                    (bnd uniY i Δ (bvPre (len Δ + len Δ + len Δ))) σ
          | sorts-[] Δ | len≡ Δ | bvPre-∘ (len Δ + len Δ + len Δ) with i <ℕ sorts Δ
  ... | true  = refl
  ... | false = refl

  bvFrom-∘ : ∀ o k → bvFrom o k ∘ σ ≡ bvFrom o k
  bvFrom-∘ o zero    = refl
  bvFrom-∘ o (suc k) = cong (_,ₛ bvar 0 (o + k)) (bvFrom-∘ o k)

  ++-∘ : ∀ ρ τ → (ρ ++ₛ τ) ∘ σ ≡ (ρ ∘ σ) ++ₛ (τ ∘ σ)
  ++-∘ ρ ⟨⟩       = refl
  ++-∘ ρ (τ ,ₛ t) = cong (_,ₛ (t [ σ ]tm)) (++-∘ ρ τ)

  modR : ∀ Δ → CS.Rel (modD Δ) (modD (Δ [ σ ]tel))
  modR Δ = record
    { mmR  = trans (bvPre-∘ (len Δ + len Δ)) (cong (λ m → bvPre (m + m)) (sym (len≡ Δ)))
    ; mpR  = trans (++-∘ (bvPre (len Δ)) (bvFrom (len Δ + len Δ) (len Δ)))
                   (trans (cong₂ _++ₛ_ (bvPre-∘ (len Δ)) (bvFrom-∘ (len Δ + len Δ) (len Δ)))
                          (cong (λ m → bvPre m ++ₛ bvFrom (m + m) m) (sym (len≡ Δ))))
    ; selR = λ j → cong (λ m → modSel m j) (sym (len≡ Δ))
    ; thR  = λ j → trans (uniTh-[] Δ (j ∸ len Δ)) (cong (λ m → uniTh (Δ [ σ ]tel) (j ∸ m)) (sym (len≡ Δ)))
    }

  uniYTy-[] : ∀ Δ y → (uniYTy Δ y) [ σ ]ty ≡ uniYTy (Δ [ σ ]tel) y
  uniYTy-[] Δ y =
    trans (CS.cylTy-[] K₁-scB (modR Δ) (bvar 0 (len Δ + y)) (morEntry Δ (len Δ) y))
          (trans (cong (cylTy (modD (Δ [ σ ]tel)) (bvar 0 (len Δ + y))) (morEntry-[] Δ (len Δ) y))
                 (cong (λ m → cylTy (modD (Δ [ σ ]tel)) (bvar 0 (m + y)) (morEntry (Δ [ σ ]tel) m y)) (sym (len≡ Δ))))

  good2-[] : ∀ Δ y → good2 (Δ [ σ ]tel) y ≡ good2 Δ y
  good2-[] Δ y =
    trans (cong₂ (λ m A → goodTy (modSel m) A) (len≡ Δ)
                 (trans (cong (λ m → morEntry (Δ [ σ ]tel) m y) (len≡ Δ)) (sym (morEntry-[] Δ (len Δ) y))))
          (goodTy-[] σ l (modSel (len Δ)) (morEntry Δ (len Δ) y))

  sel-[] : ∀ b y Δ → sel b y (Δ [ σ ]tel) ≡ sel b y Δ
  sel-[] μ    y Δ = isSortIx-[] y Δ
  sel-[] η    y Δ = inner-[] y Δ
  sel-[] rec  y Δ = isSortIx-[] y Δ
  sel-[] recY y Δ = cong₂ _∧_ (inner-[] y Δ) (okBelow-[] (suc y) Δ)
  sel-[] uni  y Δ = cong₂ _∧_ (isSortIx-[] y Δ) lf
    where lf = trans (cong (λ z → okBelow z (Δ [ σ ]tel)) (len≡ Δ)) (okBelow-[] (len Δ) Δ)
  sel-[] uniY y Δ = cong₂ _∧_ (cong₂ _∧_ (inner-[] y Δ) lf) (good2-[] Δ y)
    where lf = trans (cong (λ z → okBelow z (Δ [ σ ]tel)) (len≡ Δ)) (okBelow-[] (len Δ) Δ)


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
  sc-lookupTel (Δ ▸[ _ ] A′) y p e with y ==ℕ len Δ
  ... | true  = subst (λ z → T (scTy? n z)) (just-inj e) (snd (T∧ {scTel? n Δ} p))
  ... | false = sc-lookupTel Δ y (fst (T∧ {scTel? n Δ} p)) e

  sc-if : ∀ c {x y : Tm} → T (scTm? n x) → T (scTm? n y) → T (scTm? n (if c then x else y))
  sc-if true  px _ = px
  sc-if false _ py = py

  sc-entryTy : ∀ Δ k → T (scTel? n Δ) → T (scTy? n (entryTy Δ k))
  sc-entryTy Δ k p with lookup Δ k in e
  ... | nothing = tt
  ... | just A  = sc-lookupTel Δ k p e

  sc-θTy : ∀ Δ k th → T (scTel? n Δ) → (∀ i → T (scTm? n (th i))) → T (scTy? n (θTy Δ k th))
  sc-θTy Δ k th p pth =
    CL.Scope.cylTy-sc n K₁-scB (morD Δ th) (sc-ηPre Δ (len Δ) p) (sc-bvPre (len Δ)) pth
      (bvar 0 k) (entryTy Δ k) tt (sc-entryTy Δ k p)

  sc-bvFrom : ∀ o k → T (scSub? n (bvFrom o k))
  sc-bvFrom o zero    = tt
  sc-bvFrom o (suc k) = ∧T (sc-bvFrom o k) tt

  sc-++ : ∀ ρ τ → T (scSub? n ρ) → T (scSub? n τ) → T (scSub? n (ρ ++ₛ τ))
  sc-++ ρ ⟨⟩       p _ = p
  sc-++ ρ (τ ,ₛ t) p q = let (a , b) = T∧ {scSub? n τ} q in ∧T (sc-++ ρ τ p a) b

  sc-uniYTy : ∀ Δ y → T (scTel? n Δ) → T (scTy? n (uniYTy Δ y))
  sc-uniYTy Δ y p =
    CL.Scope.cylTy-sc n K₁-scB (modD Δ) (sc-bvPre (len Δ + len Δ))
      (sc-++ (bvPre (len Δ)) (bvFrom (len Δ + len Δ) (len Δ)) (sc-bvPre (len Δ)) (sc-bvFrom (len Δ + len Δ) (len Δ)))
      (λ j → sc-if (j ∸ len Δ <ℕ sorts Δ) (∧T p (sc-bvPre (len Δ + len Δ + len Δ))) (∧T p (sc-bvPre (len Δ + len Δ + len Δ))))
      (bvar 0 (len Δ + y)) (morEntry Δ (len Δ) y) tt (sc-θTy Δ y _ p (λ _ → tt))

  sc-res : ∀ b y Δ → T (scTel? n Δ) → T (scTy? n (res b y Δ))
  sc-res μ    y Δ p = tt
  sc-res η    y Δ p with lookup Δ y in e
  ... | nothing = tt
  ... | just A  = sc-opTy 0 (ηPre Δ y) A (sc-ηPre Δ y p) (sc-lookupTel Δ y p e)
  sc-res rec  y Δ p = ∧T tt (∧T (∧T p tt) tt)
  sc-res recY y Δ p =
    sc-θTy Δ y (recTh Δ) p (λ i → sc-if (i <ℕ sorts Δ) (∧T {scTel? n Δ} p (sc-bvPre (len Δ))) (∧T {scTel? n Δ} p (sc-bvPre (len Δ))))
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
  res-st recY y Δ σ l _ = sym (θTy-[] σ l Δ y (recTh Δ) (recTh (Δ [ σ ]tel)) (recTh-[] σ l Δ))
  res-st uni  y Δ σ l _ rewrite len-tel[] Δ σ = refl
  res-st uniY y Δ σ l _ = sym (uniYTy-[] σ l Δ y)
