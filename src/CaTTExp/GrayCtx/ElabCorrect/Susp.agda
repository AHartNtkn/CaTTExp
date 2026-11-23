------------------------------------------------------------------------
-- Elab.vcomp is correct in every dimension and for every length
-- (ledger S20 (ii)).
--
-- The tree of a composite of n cells of dimension k + 1 is
-- vT k n = wrap k (chain of n leaves). Wrapping a tree once suspends
-- its context (ctx-susp) and shifts its locally maximal variables by
-- two (tops-susp); the composite's builder commutes with suspension
-- (vcompB-Σ), and so do typing (PureMetatheory.Σtm-wf), the side
-- condition (Suspension.sideΣ) and coverage (cover-Σ). So the shape
-- facts of Chain.shape-chain lift to every k by induction, with no
-- computation per shape.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Susp where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
  using (tops; topsF; vT; vcompB; vFirst; vLast; srcTgtVar; stvTy; vcomp; length; dimOf; tyOf; cohT;
         _<$>_; replicate)
open import CaTTExp.GrayCtx.ElabCorrect.Fill
  using (covers; allBelow; allLtB; memN; bkeys; bvars; vn; lookupTy; lookup-lt; mapL; bind-just; tyOf-typed)
open import CaTTExp.GrayCtx.ElabCorrect.Coh
open import CaTTExp.GrayCtx.ElabCorrect.Chain using (shape-chain; ctx-chain; tops-chain; eF)
open import CaTTExp.Suspension ∅ using (S; mapS; lenΣ; lookupΣ; sideΣ; dimΣ; Σty; Σtm; Σctx)
open import CaTTExp.PureMetatheory using (Σtm-wf; closed)
open import CaTTExp.DerivedBoundary using (dim[])
open import CaTTExp.Derived using (ps-ctx)
open import CaTTExp.GraphFillerTotal.Chains
  using (_≤_; _<_; z≤n; s≤s; ≤-refl; ≤-step; ≤-pred; ≤-case; _⊎_; inj₁; inj₂; <→T; T→<;
         lookup-edge; dbl)
import CaTTExp.Subst ∅ cattSide as Sb

------------------------------------------------------------------------
-- Small facts.

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  ∨-inr : ∀ a {b} → T b → T (a ∨ b)
  ∨-inr true  _ = tt
  ∨-inr false q = q

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) {f : A → Maybe B} {y} →
             (m >>= f) ≡ just y → Σ A λ x → (m ≡ just x) × (f x ≡ just y)
  bind-inv (just x) e = x , refl , e

  mem-++l : ∀ k xs ys → T (memN k xs) → T (memN k (xs ++ ys))
  mem-++l k (x ∷ xs) ys h with k ==ℕ x
  ... | true  = tt
  ... | false = mem-++l k xs ys h

  mem-++r : ∀ k xs ys → T (memN k ys) → T (memN k (xs ++ ys))
  mem-++r k []       ys h = h
  mem-++r k (x ∷ xs) ys h = ∨-inr (k ==ℕ x) (mem-++r k xs ys h)

  mem-split : ∀ k xs ys → T (memN k (xs ++ ys)) → T (memN k xs) ⊎ T (memN k ys)
  mem-split k []       ys h = inj₂ h
  mem-split k (x ∷ xs) ys h with k ==ℕ x
  ... | true  = inj₁ tt
  ... | false = mem-split k xs ys h

  mem-mapS : ∀ k xs → T (memN k xs) → T (memN (S k) (mapS xs))
  mem-mapS k (x ∷ xs) h with k ==ℕ x
  ... | true  = tt
  ... | false = mem-mapS k xs h

  mapS-++ : ∀ xs ys → mapS (xs ++ ys) ≡ mapS xs ++ mapS ys
  mapS-++ []       ys = refl
  mapS-++ (x ∷ xs) ys = cong (S x ∷_) (mapS-++ xs ys)

  ++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  allBelow-intro : ∀ f n → (∀ k → k < n → T (f k)) → T (allBelow f n)
  allBelow-intro f zero    h = tt
  allBelow-intro f (suc n) h = ∧-intro (allBelow-intro f n (λ k p → h k (≤-step p))) (h n ≤-refl)

  allBelow-elim : ∀ f n → T (allBelow f n) → ∀ k → k < n → T (f k)
  allBelow-elim f (suc n) h k (s≤s p) with ≤-case p
  ... | inj₁ q    = allBelow-elim f n (∧-fst {allBelow f n} h) k q
  ... | inj₂ refl = ∧-snd {allBelow f n} h

  allLtB-mapS : ∀ ks n → allLtB (mapS ks) (S n) ≡ allLtB ks n
  allLtB-mapS []       n = refl
  allLtB-mapS (k ∷ ks) n = cong ((k <ℕ n) ∧_) (allLtB-mapS ks n)

  allLtB-head : ∀ k ks n → T (allLtB (k ∷ ks) n) → T (k <ℕ n)
  allLtB-head k ks n h = ∧-fst {k <ℕ n} h

  allLtB-tail : ∀ k ks n → T (allLtB (k ∷ ks) n) → T (allLtB ks n)
  allLtB-tail k ks n h = ∧-snd {k <ℕ n} h

  length-mapS : ∀ xs → length (mapS xs) ≡ length xs
  length-mapS []       = refl
  length-mapS (x ∷ xs) = cong suc (length-mapS xs)

  length-mapL : ∀ {A B : Set} (f : A → B) xs → length (mapL f xs) ≡ length xs
  length-mapL f []       = refl
  length-mapL f (x ∷ xs) = cong suc (length-mapL f xs)

  len-ps : ∀ {Γ x A} → Γ ⊢ps x ∶ A → 0 < len Γ
  len-ps pss     = s≤s z≤n
  len-ps (pse d) = s≤s z≤n
  len-ps (psd d) = len-ps d

------------------------------------------------------------------------
-- Wrapping a tree suspends its context.

mutual
  bΣ : ∀ t {Γ x A Γ' x' A'} (d : Γ ⊢ps x ∶ A) (d' : Γ' ⊢ps x' ∶ A') →
       Γ' ≡ Σctx Γ → x' ≡ S x → A' ≡ Σty A → fst (build t d') ≡ Σctx (fst (build t d))
  bΣ (node ts) d d' eΓ ex eA = blΣ ts d d' eΓ ex eA

  blΣ : ∀ ts {Γ x A Γ' x' A'} (d : Γ ⊢ps x ∶ A) (d' : Γ' ⊢ps x' ∶ A') →
        Γ' ≡ Σctx Γ → x' ≡ S x → A' ≡ Σty A → fst (buildList ts d') ≡ Σctx (fst (buildList ts d))
  blΣ []       d d' eΓ _ _ = eΓ
  blΣ (t ∷ ts) {Γ} {x} {A} d d' refl refl refl =
    blΣ ts (psd (snd (snd (build t (pse d))))) (psd (snd (snd (build t (pse d')))))
        (bΣ t (pse d) (pse d') e1 (cong suc (lenΣ Γ)) e3) (lenΣ Γ) refl
    where
    e1 : Σctx Γ ▸ Σty A ▸ arr (Σty A) (var (S x)) (var (len (Σctx Γ)))
         ≡ Σctx (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
    e1 = cong (λ n → Σctx Γ ▸ Σty A ▸ arr (Σty A) (var (S x)) (var n)) (lenΣ Γ)
    e3 : arr (Σty A) (var (S x)) (var (len (Σctx Γ))) ≡ Σty (arr A (var x) (var (len Γ)))
    e3 = cong (λ n → arr (Σty A) (var (S x)) (var n)) (lenΣ Γ)

ctx-susp : ∀ τ → ctxOf (node (τ ∷ [])) ≡ Σctx (ctxOf τ)
ctx-susp τ = bΣ τ pss (pse pss) refl refl refl

------------------------------------------------------------------------
-- … and shifts its locally maximal variables by two.

mutual
  topsF-S : ∀ L ts → (fst (topsF (S L) ts) ≡ mapS (fst (topsF L ts)))
                    × (snd (topsF (S L) ts) ≡ S (snd (topsF L ts)))
  topsF-S L []               = refl , refl
  topsF-S L (node [] ∷ ts)   =
    let (a , b) = topsF-S (suc (suc L)) ts in cong (suc (S L) ∷_) a , b
  topsF-S L (node (c ∷ cs) ∷ ts) =
    let r₁       = topsF (suc (suc L)) (c ∷ cs)
        (a₁ , b₁) = topsF-S (suc (suc L)) (c ∷ cs)
        (a₂ , b₂) = topsF-S (snd r₁) ts
    in trans (cong₂ _++_ a₁ (trans (cong (λ M → fst (topsF M ts)) b₁) a₂))
             (sym (mapS-++ (fst r₁) (fst (topsF (snd r₁) ts)))) ,
       trans (cong (λ M → snd (topsF M ts)) b₁) b₂

tops-susp : ∀ τ → tops (node (τ ∷ [])) ≡ mapS (tops τ)
tops-susp (node [])       = refl
tops-susp (node (c ∷ cs)) = trans (++-[] _) (fst (topsF-S 1 (c ∷ cs)))

------------------------------------------------------------------------
-- The composite's builder commutes with suspension.

private
  stv-inv : ∀ B {a b} → stvTy B ≡ just (a , b) → Σ Ty λ C → B ≡ arr C (var a) (var b)
  stv-inv (arr C (var a) (var b)) refl = C , refl

  stv-Σ : ∀ P f {a b} → srcTgtVar P f ≡ just (a , b) → srcTgtVar (Σctx P) (S f) ≡ just (S a , S b)
  stv-Σ P f h with bind-inv (lookup P f) h
  ... | B , e , h' with stv-inv B h'
  ...   | C , refl rewrite lookupΣ P f e = refl

  vFirst-Σ : ∀ ts {f} → vFirst ts ≡ just f → vFirst (mapS ts) ≡ just (S f)
  vFirst-Σ (x ∷ ts) refl = refl

  vLast-Σ : ∀ ts {f} → vLast ts ≡ just f → vLast (mapS ts) ≡ just (S f)
  vLast-Σ (x ∷ [])     refl = refl
  vLast-Σ (_ ∷ x ∷ xs) h    = vLast-Σ (x ∷ xs) h

vcompB-Σ : ∀ ts P {s t} → vcompB ts P ≡ just (s , t) → vcompB (mapS ts) (Σctx P) ≡ just (Σtm s , Σtm t)
vcompB-Σ ts P h with bind-inv (vFirst ts) h
... | f , ef , h₁ with bind-inv (vLast ts) h₁
... | l , el , h₂ with bind-inv (srcTgtVar P f) h₂
... | (a , b) , ea , h₃ with bind-inv (srcTgtVar P l) h₃
... | (c , d) , ec , refl =
  trans (bind-just {m = vFirst (mapS ts)} (vFirst-Σ ts ef))
  (trans (bind-just {m = vLast (mapS ts)} (vLast-Σ ts el))
  (trans (bind-just {m = srcTgtVar (Σctx P) (S f)} (stv-Σ P f ea))
         (bind-just {m = srcTgtVar (Σctx P) (S l)} (stv-Σ P l ec))))

------------------------------------------------------------------------
-- Coverage is preserved.

private
  vn-Σ : ∀ t → vn (Σtm t) ≡ mapS (vn t)
  vn-Σ (var i)     = refl
  vn-Σ (coh _ _ _) = refl
  vn-Σ (cst ())

  bvars-Σ : ∀ A k → T (memN k (bvars A)) → T (memN (S k) (bvars (Σty A)))
  bvars-Σ (arr A s t) k h with mem-split k (vn s) _ h
  ... | inj₁ h₁ = mem-++l (S k) (vn (Σtm s)) _ (subst (λ l → T (memN (S k) l)) (sym (vn-Σ s)) (mem-mapS k (vn s) h₁))
  ... | inj₂ h₂ with mem-split k (vn t) _ h₂
  ...   | inj₁ h₃ = mem-++r (S k) (vn (Σtm s)) _ (mem-++l (S k) (vn (Σtm t)) _
                      (subst (λ l → T (memN (S k) l)) (sym (vn-Σ t)) (mem-mapS k (vn t) h₃)))
  ...   | inj₂ h₄ = mem-++r (S k) (vn (Σtm s)) _ (mem-++r (S k) (vn (Σtm t)) _ (bvars-Σ A k h₄))

  bvars-N : ∀ A → T (memN 0 (bvars (Σty A)))
  bvars-N ⋆           = tt
  bvars-N (arr A s t) = mem-++r 0 (vn (Σtm s)) _ (mem-++r 0 (vn (Σtm t)) _ (bvars-N A))

  bvars-S : ∀ A → T (memN 1 (bvars (Σty A)))
  bvars-S ⋆           = tt
  bvars-S (arr A s t) = mem-++r 1 (vn (Σtm s)) _ (mem-++r 1 (vn (Σtm t)) _ (bvars-S A))

  lookupTy-Σ : ∀ P p → T (p <ℕ len P) → lookupTy (Σctx P) (S p) ≡ Σty (lookupTy P p)
  lookupTy-Σ P p h with lookup-lt P p h
  ... | B , e rewrite e | lookupΣ P p e = refl

  bkeys-Σ : ∀ P ks k → T (allLtB ks (len P)) → T (memN k (bkeys P ks)) →
            T (memN (S k) (bkeys (Σctx P) (mapS ks)))
  bkeys-Σ P (p ∷ qs) k lt h with mem-split k (bvars (lookupTy P p)) _ h
  ... | inj₁ h₁ = mem-++l (S k) (bvars (lookupTy (Σctx P) (S p))) _
                    (subst (λ B → T (memN (S k) (bvars B))) (sym (lookupTy-Σ P p (allLtB-head p qs _ lt)))
                           (bvars-Σ (lookupTy P p) k h₁))
  ... | inj₂ h₂ = mem-++r (S k) (bvars (lookupTy (Σctx P) (S p))) _
                    (bkeys-Σ P qs k (allLtB-tail p qs _ lt) h₂)

  -- N and S are boundaries of every suspended top.
  bkeys-N : ∀ P p qs → T (p <ℕ len P) → T (memN 0 (bkeys (Σctx P) (mapS (p ∷ qs))))
  bkeys-N P p qs lt = mem-++l 0 (bvars (lookupTy (Σctx P) (S p))) _
    (subst (λ B → T (memN 0 (bvars B))) (sym (lookupTy-Σ P p lt)) (bvars-N (lookupTy P p)))

  bkeys-S : ∀ P p qs → T (p <ℕ len P) → T (memN 1 (bkeys (Σctx P) (mapS (p ∷ qs))))
  bkeys-S P p qs lt = mem-++l 1 (bvars (lookupTy (Σctx P) (S p))) _
    (subst (λ B → T (memN 1 (bvars B))) (sym (lookupTy-Σ P p lt)) (bvars-S (lookupTy P p)))

cover-Σ : ∀ P ks → 0 < len P → T (covers P ks) → T (covers (Σctx P) (mapS ks))
cover-Σ P [] pos cv = ⊥-elim (allBelow-elim _ (len P) (∧-snd {allLtB [] (len P)} cv) 0 pos)
cover-Σ P (q ∷ qs) pos cv rewrite lenΣ P =
  ∧-intro (subst T (sym (allLtB-mapS ks (len P))) lt)
          (allBelow-intro _ (S (len P)) go)
  where
  ks  = q ∷ qs
  lt  = ∧-fst {allLtB ks (len P)} cv
  mem = allBelow-elim _ (len P) (∧-snd {allLtB ks (len P)} cv)
  go : ∀ k → k < S (len P) → T (memN k (mapS ks ++ bkeys (Σctx P) (mapS ks)))
  go zero          _ = mem-++r 0 (mapS ks) _ (bkeys-N P q qs (allLtB-head q qs _ lt))
  go (suc zero)    _ = mem-++r 1 (mapS ks) _ (bkeys-S P q qs (allLtB-head q qs _ lt))
  go (suc (suc k)) p with mem-split k ks _ (mem k (≤-pred (≤-pred p)))
  ... | inj₁ h = mem-++l (S k) (mapS ks) _ (mem-mapS k ks h)
  ... | inj₂ h = mem-++r (S k) (mapS ks) _ (bkeys-Σ P ks k lt h)

------------------------------------------------------------------------
-- The shape facts of vcomp lift through one wrap, hence to every k.

shapeΣ-vcomp : ∀ τ → ShapeOK τ (vcompB (tops τ)) → ShapeOK (node (τ ∷ [])) (vcompB (tops (node (τ ∷ []))))
shapeΣ-vcomp τ sh = shapeOK (Σtm (src sh)) (Σtm (tgt sh)) (Σty (ty sh))
  (trans (cong₂ vcompB (tops-susp τ) (ctx-susp τ)) (vcompB-Σ (tops τ) (ctxOf τ) (built sh)))
  (inP (λ P → P ⊢tm Σtm (src sh) ∶ Σty (ty sh)) (Σtm-wf (src-wf sh)))
  (inP (λ P → P ⊢tm Σtm (tgt sh) ∶ Σty (ty sh)) (Σtm-wf (tgt-wf sh)))
  (inP (λ P → T (cattSide P (Σty (ty sh)) (Σtm (src sh)) (Σtm (tgt sh)))) (sideΣ {A = ty sh} {t = src sh} {u = tgt sh} (snd (psOf τ)) (side-ok sh)))
  (inP (λ P → T (covers P (tops (node (τ ∷ [])))))
       (subst (λ ks → T (covers (Σctx (ctxOf τ)) ks)) (sym (tops-susp τ))
              (cover-Σ (ctxOf τ) (tops τ) (pos (snd (psOf τ))) (cover sh))))
  where
  inP : (F : Ctx → Set) → F (Σctx (ctxOf τ)) → F (ctxOf (node (τ ∷ [])))
  inP F x = subst F (sym (ctx-susp τ)) x
  pos : ∀ {Γ} → Γ ⊢ps → 0 < len Γ
  pos (ps d) = len-ps d

shape-vcomp : ∀ k m → ShapeOK (vT k (suc m)) (vcompB (tops (vT k (suc m))))
shape-vcomp zero    m = shape-chain m
shape-vcomp (suc k) m = shapeΣ-vcomp (vT k (suc m)) (shape-vcomp k m)

------------------------------------------------------------------------
-- The first top of vT k n is a (k+1)-cell, and vT k n has n tops.

private
  dim-Σ : ∀ A → dim (Σty A) ≡ suc (dim A)
  dim-Σ ⋆           = refl
  dim-Σ (arr A _ _) = cong suc (dim-Σ A)

first-top : ∀ k m → Σ Nat λ p → Σ (List Nat) λ rest → (tops (vT k (suc m)) ≡ p ∷ rest)
            × Σ Ty λ A → (lookup (ctxOf (vT k (suc m))) p ≡ just A) × (dim A ≡ suc k)
first-top zero m = 2 , _ , tops-chain m , arr ⋆ (var 0) (var 1) ,
  subst (λ P → lookup P 2 ≡ just (arr ⋆ (var 0) (var 1))) (sym (ctx-chain (suc m)))
        (lookup-edge (suc m) 0 (s≤s z≤n)) , refl
first-top (suc k) m with first-top k m
... | p , rest , et , A , el , ed =
  S p , mapS rest , trans (tops-susp (vT k (suc m))) (cong mapS et) , Σty A ,
  subst (λ P → lookup P (S p) ≡ just (Σty A)) (sym (ctx-susp (vT k (suc m)))) (lookupΣ (ctxOf (vT k (suc m))) p el) ,
  trans (dim-Σ A) (cong suc ed)

private
  length-eF : ∀ i n → length (eF i n) ≡ n
  length-eF i zero    = refl
  length-eF i (suc n) = cong suc (length-eF (suc i) n)

length-tops : ∀ k m → length (tops (vT k (suc m))) ≡ suc m
length-tops zero    m = trans (cong length (tops-chain m)) (length-eF 0 (suc m))
length-tops (suc k) m = trans (cong length (tops-susp (vT k (suc m))))
                              (trans (length-mapS (tops (vT k (suc m)))) (length-tops k m))

------------------------------------------------------------------------
-- vcomp unfolds to cohT on its tree.

private
  headT : List Tm → Tm
  headT []      = var 0
  headT (c ∷ _) = c

vcomp-unfold : ∀ Γ cells k → 2 ≤ length cells → dimOf Γ (headT cells) ≡ just (suc k) →
               vcomp Γ cells ≡ cohT Γ (vT k (length cells)) (vcompB (tops (vT k (length cells)))) cells
vcomp-unfold Γ (c ∷ d ∷ cs) k _ e = bind-just {m = dimOf Γ c} e
vcomp-unfold Γ (c ∷ []) k (s≤s ()) e

------------------------------------------------------------------------
-- The theorem: for every k, every m and every typed σ₀ : ctxOf (vT k
-- (m+2)), vcomp of the images of the m+2 top cells is the composite
-- coherence, and it is well typed. No check per use.

module _ {Γ σ₀} (k m : Nat) where
  private
    τ  = vT k (suc (suc m))
    P  = ctxOf τ
    L  = mapL (lookupₛ σ₀) (tops τ)
    sh = shape-vcomp k (suc m)
    Aτ = arr (ty sh) (src sh) (tgt sh)

  vcomp-ok : Γ ⊢sub σ₀ ∶ P → (vcomp Γ L ≡ just (coh P Aτ σ₀)) × (Γ ⊢tm coh P Aτ σ₀ ∶ Aτ [ σ₀ ]ty)
  vcomp-ok s =
    trans (vcomp-unfold Γ L k two dh)
          (trans (cong (λ n → cohT Γ (vT k n) (vcompB (tops (vT k n))) L) lenL) (fst ok)) ,
    snd ok
    where
    ok = cohT-ok τ _ sh s
    lenL : length L ≡ suc (suc m)
    lenL = trans (length-mapL (lookupₛ σ₀) (tops τ)) (length-tops k (suc m))
    two : 2 ≤ length L
    two = subst (2 ≤_) (sym lenL) (s≤s (s≤s z≤n))
    ft = first-top k (suc m)
    p    = fst ft
    et   = fst (snd (snd ft))
    A    = fst (snd (snd (snd ft)))
    el   = fst (snd (snd (snd (snd ft))))
    ed   = snd (snd (snd (snd (snd ft))))
    hd : headT L ≡ lookupₛ σ₀ p
    hd rewrite et = refl
    dh : dimOf Γ (headT L) ≡ just (suc k)
    dh rewrite hd =
      trans (cong (dim <$>_) (tyOf-typed (Sb.lookup-sub closed (ps-ctx (snd (psOf τ))) el s)))
            (cong just (trans (dim[] A σ₀) ed))
