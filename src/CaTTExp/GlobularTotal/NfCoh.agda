------------------------------------------------------------------------
-- F2c, lemma (1′) in full: normal forms of well-typed terms of a
-- globular context.
--
--   res : Glob Γ → Γ ⊢ t : A → ResF Γ t A
--
-- For every fuel above the coh depth of t, nf t is a well-formed
-- diagram of Γ of dimension dim A, whose boundaries are the normal
-- forms of A's endpoints, labelled exactly by Var(t : A).
--
-- By induction on the typing derivation, together with
--   all-res : the same for every component of a substitution, and
--   hyp-res : NfSub's `Hyp` for a term of a globular Δ, given that the
--             images Ĵ of Δ's variables are typed (ExGood.TypedImg).
-- The coh case (`res-coh`) for coh Θ (u →_B v) σ, with Θ = ctxOf τ:
--   * nf of the coh is flatG Ĵ 0 (idTree τ), defined since idTree τ is
--     a diagram of Θ (LabEx) and the images are typed (ImgTyped, ExGood);
--   * nf u = bd false (dim B) (idTree τ) and likewise v (EndsNf, from
--     the side condition), so 1b (NfSub.nf-sub) and FlatBd give the
--     boundaries of the composite as the normal forms of u[σ], v[σ];
--   * its dimension is at most dim B + 1 (EndsNf bounds dim Θ, and
--     DimCheck.tree-dim), it is a diagram of Γ (ExMerge.ex-flat), and
--     its labels are the variables of σ (Labels.flat⊆/flat⊇, which
--     contain those of the type since the type lives in Θ).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.NfCoh where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; nf; bd; idTree; depthTm; depthSub)
open import CaTTExp.GlobularTotal.Surj ∅ using (treeOf-ps)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn; ps-glob)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.Labels using (anyL; anyLab; memI; flat⊆; flat⊇; bool-ext)
open import CaTTExp.GlobularTotal.FvSub using (fv-ty; memL-++)
open import CaTTExp.GlobularTotal.FlatBd using (flatG; Good; flat-bd; flat-is-flatG)
open import CaTTExp.GlobularTotal.NfSub using (Hyp; Ĵ; Iτ; nf-sub)
open import CaTTExp.GlobularTotal.ExGood using (TypedImg; ex-good)
open import CaTTExp.GlobularTotal.ExMerge using (ex-flat)
open import CaTTExp.GlobularTotal.DimCheck using (tree-dim)
open import CaTTExp.GlobularTotal.NfTyped using (Glob; Ends; res-var)
open import CaTTExp.GlobularTotal.EndsNf using (ends-nf; ParB)
open import CaTTExp.GlobularTotal.NfFuel using (nf-det; nf-≥; depth-look; dim-sub; sub-len; ctx-scope; ty-scope)
open import CaTTExp.GlobularTotal.ImgTyped using (ResF; VarTy; Shape; AllRes; img-res; J; typed-img)
open import CaTTExp.GlobularTotal.CohParts
  using (flat-total; lab-of-mem; anyL-elim; anyL-intro; anyLab-elim; anyLab-intro;
         fvSub-comp; comp-fvSub; look-out; lt-lookup)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  -- arithmetic
  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc zero    b c = refl
  +-assoc (suc a) b c = cong suc (+-assoc a b c)

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  ≤-+ : ∀ a m → T (a <ℕ suc (a + m))
  ≤-+ zero    m = tt
  ≤-+ (suc a) m = ≤-+ a m

  ≤-+r : ∀ a b → T (b <ℕ suc (a + b))
  ≤-+r zero    b = ≤-refl b
    where
    ≤-refl : ∀ a → T (a <ℕ suc a)
    ≤-refl zero    = tt
    ≤-refl (suc a) = ≤-refl a
  ≤-+r (suc a) b = ≤-weak b (a + b) (≤-+r a b)
    where
    ≤-weak : ∀ a b → T (a <ℕ suc b) → T (a <ℕ suc (suc b))
    ≤-weak zero    b       p = tt
    ≤-weak (suc a) zero    ()
    ≤-weak (suc a) (suc b) p = ≤-weak a b p

  -- a < b gives b = suc a + i
  lt-split : ∀ a b → T (a <ℕ b) → Σ Nat λ i → b ≡ suc a + i
  lt-split a       zero    ()
  lt-split zero    (suc b) p = b , refl
  lt-split (suc a) (suc b) p with lt-split a b p
  ... | i , e = i , cong suc e

  -- a ≤ b gives b = a + i
  le-split : ∀ a b → T (a <ℕ suc b) → Σ Nat λ i → b ≡ a + i
  le-split zero    b       p = b , refl
  le-split (suc a) zero    ()
  le-split (suc a) (suc b) p with le-split a b p
  ... | i , e = i , cong suc e

  le-lt : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
  le-lt zero    b       (suc c) p q = tt
  le-lt a       b       zero    p ()
  le-lt (suc a) zero    (suc c) () q
  le-lt (suc a) (suc b) (suc c) p q = le-lt a b c p q

  lt-ne : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne zero    zero    p ()
  lt-ne zero    (suc n) p e = tt
  lt-ne (suc y) zero    () e
  lt-ne (suc y) (suc n) p e = lt-ne y n p e

  memI-just : ∀ J y z a → J z ≡ just a → memI J y z ≡ mem y a
  memI-just J y z a e with J z
  memI-just J y z a refl | .(just a) = refl

  Top : LT → Set
  Top _ = ⊤

------------------------------------------------------------------------
-- Globular contexts have var-endpoint types.

glob-shape : ∀ Δ → Glob Δ → Shape Δ
glob-shape Δ g y B e = go B (g y B e)
  where
  go : ∀ B → TyIn Δ B → VarTy B
  go ⋆ _ = tt
  go (arr B (var a) (var b)) (_ , _ , _ , _ , t) = go B t
  go (arr B (var a) (coh _ _ _)) ()
  go (arr B (var a) (cst ()))    _
  go (arr B (coh _ _ _) _)       ()
  go (arr B (cst ()) _)          _

------------------------------------------------------------------------
-- Every normal form of a component of a typed substitution is a
-- diagram (in range by img-res, out of range it is a variable).

img-ex : ∀ Γ {σ Θ} → Glob Γ → (dσ : Γ ⊢sub σ ∶ Θ) → AllRes dσ → Θ ⊢ctx → Shape Θ →
         ∀ n y x → nf n Γ (lookupₛ σ y) ≡ just x → Ex Γ 0 nothing x
img-ex Γ {σ} {Θ} g dσ ar dΘ sh n y x h with y <ℕ lenₛ σ in eq
... | true with lt-lookup Θ y (subst (λ k → T (y <ℕ k)) (sub-len dσ) (≡-T eq))
...   | A , e with img-res Γ dσ ar dΘ sh y A e
...     | x' , fx , _ , _ , xx , _ =
  subst (Ex Γ 0 nothing) (sym (nf-det n (suc (depthTm (lookupₛ σ y)) + 0) Γ (lookupₛ σ y) x x' h (fx 0))) xx
img-ex Γ {σ} {Θ} g dσ ar dΘ sh n y x h | false = go n (trans (cong (nf n Γ) (sym (look-out σ y eq))) h)
  where
  go : ∀ n → nf n Γ (var y) ≡ just x → Ex Γ 0 nothing x
  go zero    ()
  go (suc n) h' with bind-inv (lookup Γ y) _ h'
  ... | A , eA , _ with res-var Γ y A g eA
  ...   | k , w , ew , _ , _ , xw , _ =
    subst (Ex Γ 0 nothing) (sym (nf-det (suc n) k Γ (var y) x w h' ew)) xw

------------------------------------------------------------------------
-- Hyp of 1b at a coherence, from its pasting context, the typed
-- images of its arguments, and Hyp for the arguments.

module _ (Γ : Ctx) (σ : Sub) (M : Nat) where

  hyp-coh : ∀ {Δ Θ A τ} → Glob Δ → TypedImg Δ (Ĵ Γ σ M) → Θ ⊢ps → Θ ⊢ctx →
            (dτ : Δ ⊢sub τ ∶ Θ) → AllRes dτ →
            (∀ y → T (y <ℕ lenₛ τ) → ∀ n → T (depthTm (lookupₛ τ y) <ℕ n) → Hyp Γ σ M n Δ (lookupₛ τ y)) →
            ∀ n → T (depthTm (coh Θ A τ) <ℕ n) → Hyp Γ σ M n Δ (coh Θ A τ)
  hyp-coh gΔ ti pΘ dΘ dτ art rec zero ()
  hyp-coh {Δ} {Θ} {A} {τ} gΔ ti pΘ dΘ dτ art rec (suc n) p tr etr with treeOf-ps pΘ
  ... | tr' , etr' , refl with trans (sym etr) etr'
  ...   | refl with lt-split (depthSub τ) n p
  ...     | i , refl = lab , good , goodJ , rec'
    where
    gΘ = ps-glob pΘ
    sh = glob-shape (ctxOf tr) gΘ

    lab = lab-of-mem (λ y → T (y <ℕ lenₛ τ)) (idTree tr)
            (λ y m → subst (λ k → T (y <ℕ k)) (sym (sub-len dτ)) (≡-T (trans (sym (lab-all tr y)) m)))

    good : Good (Iτ Γ σ M (suc (depthSub τ) + i) Δ τ) 0 Top (idTree tr)
    good = ex-good (ctxOf tr) (J Δ τ (ctxOf tr) i)
             (typed-img Δ τ (ctxOf tr) i gΘ (img-res Δ dτ art dΘ sh)) 0 (idTree tr) (lab-ex tr)

    goodJ : ∀ y b → Iτ Γ σ M (suc (depthSub τ) + i) Δ τ y ≡ just b → Good (Ĵ Γ σ M) 0 Top b
    goodJ y b e = ex-good Δ (Ĵ Γ σ M) ti 0 b (img-ex Δ gΔ dτ art dΘ sh (suc (depthSub τ) + i) y b e)

    rec' : ∀ y → T (y <ℕ lenₛ τ) → Hyp Γ σ M (suc (depthSub τ) + i) Δ (lookupₛ τ y)
    rec' y q = rec y q (suc (depthSub τ) + i)
                 (le-lt (depthTm (lookupₛ τ y)) (depthSub τ) (suc (depthSub τ) + i)
                        (depth-look τ y) (≤-+ (depthSub τ) i))

------------------------------------------------------------------------
-- The coh case of (1′).

private
  parB : ∀ {Θ} B au av → Ends Θ B au → Ends Θ B av → ParB B au av
  parB ⋆ _ _ _ _ = tt
  parB {Θ} (arr B' s t) au av (n , es , _) (n' , es' , _) = nf-det n n' Θ s _ _ es es'

res-coh : ∀ {Γ Θ B u v σ} → Glob Γ → Θ ⊢ps → Θ ⊢ctx → Θ ⊢tm u ∶ B → Θ ⊢tm v ∶ B →
          T (cattSide Θ B u v) → (dσ : Γ ⊢sub σ ∶ Θ) → AllRes dσ →
          ResF Θ u B → ResF Θ v B →
          (∀ n → T (depthTm u <ℕ n) → Hyp Γ σ (suc (depthSub σ) + 0) n Θ u) →
          (∀ n → T (depthTm v <ℕ n) → Hyp Γ σ (suc (depthSub σ) + 0) n Θ v) →
          ResF Γ (coh Θ (arr B u v) σ) ((arr B u v) [ σ ]ty)
res-coh {Γ} {Θ} {B} {u} {v} {σ} g pΘ dΘ du dv sd dσ ar
        (au , fu , wu , dmu , xu , enu , lu) (av , fv , wv , dmv , xv , env , lv) hu hv
  with treeOf-ps pΘ
... | tr , etr , refl = c₀ , fuel , wc , dimc , exc , endsc , labc
  where
  Tr = idTree tr
  gΘ = ps-glob pΘ
  sh = glob-shape (ctxOf tr) gΘ
  ir = img-res Γ dσ ar dΘ sh
  d = depthSub σ
  M = suc d + 0
  A = arr B u v

  J₀ : Nat → Maybe LT
  J₀ = J Γ σ (ctxOf tr) 0

  ti : TypedImg (ctxOf tr) J₀
  ti = typed-img Γ σ (ctxOf tr) 0 gΘ ir

  good : Good J₀ 0 Top Tr
  good = ex-good (ctxOf tr) J₀ ti 0 Tr (lab-ex tr)

  c₀ : LT
  c₀ = fst (flat-total J₀ 0 Top Tr good)

  e₀ : flatG J₀ 0 Tr ≡ just c₀
  e₀ = snd (flat-total J₀ 0 Top Tr good)

  -- fuel
  nf₀ : nf (suc (suc d) + 0) Γ (coh (ctxOf tr) A σ) ≡ just c₀
  nf₀ rewrite etr = trans (flat-is-flatG (suc d + 0) Γ σ 0 Tr) e₀

  fuel : ∀ m → nf (suc (suc d) + m) Γ (coh (ctxOf tr) A σ) ≡ just c₀
  fuel m = nf-≥ (suc (suc d) + 0) (suc (suc d) + m) Γ (coh (ctxOf tr) A σ) c₀ nf₀
             (subst (λ k → T (k <ℕ suc (suc (suc d) + m))) (sym (+0 (suc (suc d)))) (≤-+ (suc (suc d)) m))

  -- well formed, boundaries of the composite
  wc : WF c₀
  wc = fst (flat-bd J₀ 0 Top Tr c₀ good e₀)

  bdc : ∀ β i → flatG J₀ 0 (bd β i Tr) ≡ just (bd β i c₀)
  bdc = snd (flat-bd J₀ 0 Top Tr c₀ good e₀)

  -- a diagram of Γ
  exc : Ex Γ 0 nothing c₀
  exc = ex-flat Γ J₀ (λ y x e → img-ex Γ g dσ ar dΘ sh M y x e) 0 Top Tr c₀ good e₀

  -- the endpoints
  en = ends-nf tr B u v au av xu xv dmu dmv lu lv (parB B au av enu env) sd

  N : Nat
  N = suc (depthTm u + depthTm v)

  nu : nf N (ctxOf tr) u ≡ just au
  nu = fu (depthTm v)

  nv : nf N (ctxOf tr) v ≡ just av
  nv = nf-≥ (suc (depthTm v) + 0) N (ctxOf tr) v av (fv 0)
         (subst (λ k → T (k <ℕ suc N)) (sym (+0 (suc (depthTm v)))) (≤-+r (depthTm u) (depthTm v)))

  su : nf (N + M) Γ (u [ σ ]tm) ≡ just (bd false (dim B) c₀)
  su = trans (nf-sub Γ σ M N (ctxOf tr) u au (hu N (≤-+ (depthTm u) (depthTm v))) nu)
             (trans (cong (flatG J₀ 0) (fst en)) (bdc false (dim B)))

  sv : nf (N + M) Γ (v [ σ ]tm) ≡ just (bd true (dim B) c₀)
  sv = trans (nf-sub Γ σ M N (ctxOf tr) v av (hv N (≤-+r (depthTm u) (depthTm v))) nv)
             (trans (cong (flatG J₀ 0) (fst (snd en))) (bdc true (dim B)))

  endsc : Ends Γ (A [ σ ]ty) c₀
  endsc = N + M ,
          subst (λ k → nf (N + M) Γ (u [ σ ]tm) ≡ just (bd false k c₀)) (sym (dim-sub B σ)) su ,
          subst (λ k → nf (N + M) Γ (v [ σ ]tm) ≡ just (bd true k c₀)) (sym (dim-sub B σ)) sv

  -- dimension
  dimB : ∀ β i → bd β (suc (dim B) + i) c₀ ≡ c₀
  dimB β i with le-split (dimCtx (ctxOf tr)) (suc (dim B)) (snd (snd en))
  ... | j , ej =
    just-inj (trans (sym (bdc β (suc (dim B) + i)))
      (trans (cong (λ k → flatG J₀ 0 (bd β k Tr)) (trans (cong (_+ i) ej) (+-assoc (dimCtx (ctxOf tr)) j i)))
        (trans (cong (flatG J₀ 0) (tree-dim tr β (j + i))) e₀)))

  dimc : ∀ β i → bd β (suc (dim (B [ σ ]ty)) + i) c₀ ≡ c₀
  dimc β i rewrite dim-sub B σ = dimB β i

  -- labels
  inΘ : ∀ w → mem w Tr ≡ true → T (w <ℕ len (ctxOf tr))
  inΘ w m = ≡-T (trans (sym (lab-all tr w)) m)

  toσ : ∀ w → T (w <ℕ len (ctxOf tr)) → T (w <ℕ lenₛ σ)
  toσ w p = subst (λ k → T (w <ℕ k)) (sym (sub-len dσ)) p

  img : ∀ w A' → lookup (ctxOf tr) w ≡ just A' →
        Σ LT λ x → (J₀ w ≡ just x) × (∀ z → mem z x ≡ (memL z (fvTm (lookupₛ σ w)) ∨
                                         anyL (λ w' → memL z (fvTm (lookupₛ σ w'))) (fvTy A')))
  img w A' e with ti w A' e | ir w A' e
  ... | x' , jw , _ | x , fx , _ , _ , _ , _ , lx =
    x , trans jw (cong just (nf-det M (suc (depthTm (lookupₛ σ w)) + 0) Γ (lookupₛ σ w) x' x jw (fx 0))) , lx

  inS : ∀ z → mem z c₀ ≡ true → memL z (fvSub σ) ≡ true
  inS z m with anyLab-elim (memI J₀ z) Tr (flat⊆ J₀ 0 Tr c₀ z e₀ m)
  ... | w , mw , iw with lt-lookup (ctxOf tr) w (inΘ w mw)
  ...   | A' , eA with img w A' eA
  ...     | x , jw , lx with ∨-split _ _ (trans (sym (lx z)) (trans (sym (memI-just J₀ z w x jw)) iw))
  ...       | inl h = comp-fvSub σ z w (toσ w (inΘ w mw)) h
  ...       | inr h with anyL-elim _ (fvTy A') h
  ...         | w' , mw' , h' = comp-fvSub σ z w' (toσ w' (ctx-scope dΘ w A' eA w' mw')) h'

  fromS : ∀ z → memL z (fvSub σ) ≡ true → mem z c₀ ≡ true
  fromS z ms with fvSub-comp σ z ms
  ... | w , pw , h with subst (λ k → T (w <ℕ k)) (sub-len dσ) pw
  ...   | pΘw with lt-lookup (ctxOf tr) w pΘw
  ...     | A' , eA with img w A' eA
  ...       | x , jw , lx =
    flat⊇ J₀ 0 Top Tr c₀ z good e₀
      (anyLab-intro (memI J₀ z) Tr w (trans (lab-all tr w) (T-≡ pΘw))
         (trans (memI-just J₀ z w x jw) (trans (lx z) (∨-inl _ _ h))))

  tyS : ∀ z → memL z (fvTy (A [ σ ]ty)) ≡ true → memL z (fvSub σ) ≡ true
  tyS z mt with anyL-elim _ (fvTy A) (trans (sym (fv-ty z σ A)) mt)
  ... | w , mw , h = comp-fvSub σ z w (toσ w (ty-scope (arr-wf du dv) w mw)) h

  labc : ∀ z → mem z c₀ ≡ memL z (fvTmTy (coh (ctxOf tr) A σ) (A [ σ ]ty))
  labc z = bool-ext _ _
    (λ m → trans (memL-++ z (fvSub σ) (fvTy (A [ σ ]ty))) (∨-inl _ _ (inS z m)))
    (λ m → fro (∨-split _ _ (trans (sym (memL-++ z (fvSub σ) (fvTy (A [ σ ]ty)))) m)))
    where
    fro : (memL z (fvSub σ) ≡ true) ⊎ (memL z (fvTy (A [ σ ]ty)) ≡ true) → mem z c₀ ≡ true
    fro (inl ms) = fromS z ms
    fro (inr mt) = fromS z (tyS z mt)

------------------------------------------------------------------------
-- The induction.

mutual
  res : ∀ {Γ t A} → Glob Γ → Γ ⊢tm t ∶ A → ResF Γ t A
  res {Γ} g (var-wf {i} {A} _ e) = w , (λ m → nf-eq) , rest
    where
    r = res-var Γ i A g e
    w = fst (snd r)
    nf-eq : nf 1 Γ (var i) ≡ just w
    nf-eq = fst (snd (snd r))
    rest = snd (snd (snd r))
  res {Γ} g (coh-wf {Θ} {B} {u} {v} {σ} pΘ dΘ (arr-wf du dv) sd dσ) =
    res-coh g pΘ dΘ du dv sd dσ ar (res gΘ du) (res gΘ dv)
            (hyp-res Γ σ (suc (depthSub σ) + 0) gΘ ti du)
            (hyp-res Γ σ (suc (depthSub σ) + 0) gΘ ti dv)
    where
    gΘ = ps-glob pΘ
    ar = all-res g dσ
    ti = typed-img Γ σ Θ 0 gΘ (img-res Γ dσ ar dΘ (glob-shape Θ gΘ))
  res g (cst-wf {k = ()} _ _)

  all-res : ∀ {Γ σ Δ} → Glob Γ → (dσ : Γ ⊢sub σ ∶ Δ) → AllRes dσ
  all-res g (⟨⟩-wf _)    = tt
  all-res g (,-wf dσ dt) = all-res g dσ , res g dt

  hyp-res : ∀ Γ σ M {Δ t A} → Glob Δ → TypedImg Δ (Ĵ Γ σ M) → Δ ⊢tm t ∶ A →
            ∀ n → T (depthTm t <ℕ n) → Hyp Γ σ M n Δ t
  hyp-res Γ σ M gΔ ti (var-wf _ e) zero ()
  hyp-res Γ σ M gΔ ti (var-wf {i} {A} _ e) (suc n) p with ti i A e
  ... | x , ex , _ = x , ex
  hyp-res Γ σ M gΔ ti (coh-wf pΘ dΘ _ _ dτ) n p =
    hyp-coh Γ σ M gΔ ti pΘ dΘ dτ (all-res gΔ dτ) (hyp-sub Γ σ M gΔ ti dτ) n p
  hyp-res Γ σ M gΔ ti (cst-wf {k = ()} _ _) n p

  hyp-sub : ∀ Γ σ M {Δ τ Θ} → Glob Δ → TypedImg Δ (Ĵ Γ σ M) → Δ ⊢sub τ ∶ Θ →
            ∀ y → T (y <ℕ lenₛ τ) → ∀ n → T (depthTm (lookupₛ τ y) <ℕ n) → Hyp Γ σ M n Δ (lookupₛ τ y)
  hyp-sub Γ σ M gΔ ti (⟨⟩-wf _) y ()
  hyp-sub Γ σ M gΔ ti (,-wf {τ} dτ dt) y p with y ==ℕ lenₛ τ in eq
  ... | true  = hyp-res Γ σ M gΔ ti dt
  ... | false = hyp-sub Γ σ M gΔ ti dτ y (lt-ne y (lenₛ τ) p eq)

------------------------------------------------------------------------
-- (1′) in the form of NfTyped.Res.

res-nf : ∀ {Γ t A} → Glob Γ → Γ ⊢tm t ∶ A →
         Σ LT λ a → (nf (suc (depthTm t)) Γ t ≡ just a) × WF a × (∀ β i → bd β (dim A + i) a ≡ a)
       × Ex Γ 0 nothing a × Ends Γ A a × (∀ y → mem y a ≡ memL y (fvTmTy t A))
res-nf {Γ} {t} g dt with res g dt
... | a , fa , rest = a , subst (λ k → nf k Γ t ≡ just a) (+0 (suc (depthTm t))) (fa 0) , rest
