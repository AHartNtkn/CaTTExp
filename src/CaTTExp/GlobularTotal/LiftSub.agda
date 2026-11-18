------------------------------------------------------------------------
-- F2c, step (P4) of lemmas 3–5: lifting commutes with substitution.
--
-- Fix a coherence's pasting context Θ₁, its arguments σ₁ (terms of Γ),
-- positions P for the variables of Θ₁ (TypedImg Θ₁ P), and lifted
-- arguments σ₁′ with
--
--   rel   : the image of σ₁ y is the relabelling (along f) of P y;
--   lifts : liftT (σ₁ y) (P y) ≡ just (σ₁′ y), at every fuel above
--           the depth of σ₁ y.
--
-- Then for every term u of Θ₁, the lift of u[σ₁] at the composite of
-- P over nf u is u[σ₁′]:
--
--   lift-sub : Θ₁ ⊢ u : A → nf u ≡ just x → flatG P 0 x ≡ just E′ →
--              liftT k Γ (u [ σ₁ ]) E′ ≡ just (u [ σ₁′ ])
--
-- By induction on the typing of u. A variable y has the globe of y as
-- normal form, whose composite is P y (wrap-flat). At a coherence
-- coh Θ₂ A σ₂, the composite is that of y ↦ flatG P 0 (nf (σ₂ y))
-- over Θ₂'s tree (flat-assoc); these positions are typed
-- (typedImg-comp), so `assign` returns exactly them (AssignUnique),
-- and the induction hypothesis for the arguments of σ₂ gives
-- liftS ≡ σ₂ ∘ σ₁′ (liftS-ext).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LiftSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed; tm[])
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.GlobularFiller
  using (LT; lt; bd; nf; liftTy; depthTy; flat; liftT; liftS; assign; idTree; depthTm; depthSub; module Lists)
open Lists using (find)
open import CaTTExp.GlobularTotal.Surj ∅ using (treeOf-ps)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; memCs; Ex)
open import CaTTExp.GlobularTotal.PsOrd using (ps-glob)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.FlatBd using (flatG; Good; flat-bd; flat-is-flatG)
open import CaTTExp.GlobularTotal.FlatAssoc using (flat-def; flat-assoc; I∘J)
open import CaTTExp.GlobularTotal.NfSub using (Lab; LabL; AllN; Ĵ; nf-sub; wrap-flat; lookup-∘)
open import CaTTExp.GlobularTotal.ExGood using (TypedImg; Bnd; ex-good)
open import CaTTExp.GlobularTotal.NfTyped using (Glob; Ends)
open import CaTTExp.GlobularTotal.ExBd using (ex-bd)
open import CaTTExp.GlobularTotal.NfFuel using (nf-det; depth-look; sub-len; dim-sub)
open import CaTTExp.Derived using (tm-ty)
open import CaTTExp.GlobularTotal.ImgTyped using (img-res; J; typed-img)
open import CaTTExp.GlobularTotal.CohParts using (flat-total; lab-of-mem; lt-lookup)
open import CaTTExp.GlobularTotal.NfCoh using (glob-shape; img-ex; res; all-res; hyp-res)
open import CaTTExp.GlobularTotal.LabDistinct using (nd-idTree)
open import CaTTExp.GlobularTotal.Relabel using (relab)
open import CaTTExp.GlobularTotal.AssignUnique using (Rel; relab-flatG; assign-flat)
  renaming (J to Jσ)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  lt-split : ∀ a b → T (a <ℕ b) → Σ Nat λ i → b ≡ suc a + i
  lt-split a       zero    ()
  lt-split zero    (suc b) p = b , refl
  lt-split (suc a) (suc b) p with lt-split a b p
  ... | i , e = i , cong suc e

  le-lt : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
  le-lt zero    b       (suc c) p q = tt
  le-lt a       b       zero    p ()
  le-lt (suc a) zero    (suc c) () q
  le-lt (suc a) (suc b) (suc c) p q = le-lt a b c p q

  max-ltl : ∀ a b k → T (max a b <ℕ k) → T (a <ℕ k)
  max-ltl zero    b       (suc k) p = tt
  max-ltl a       b       zero    ()
  max-ltl (suc a) zero    (suc k) p = p
  max-ltl (suc a) (suc b) (suc k) p = max-ltl a b k p

  max-ltr : ∀ a b k → T (max a b <ℕ k) → T (b <ℕ k)
  max-ltr zero    b       k       p = p
  max-ltr a       b       zero    ()
  max-ltr (suc a) zero    (suc k) p = tt
  max-ltr (suc a) (suc b) (suc k) p = max-ltr a b k p

  bind-just : ∀ {A B : Set} (m : Maybe A) (k : A → Maybe B) {x} → m ≡ just x → (m >>= k) ≡ k x
  bind-just m k refl = refl

  lt-suc : ∀ a → T (a <ℕ suc a)
  lt-suc zero    = tt
  lt-suc (suc a) = lt-suc a

  lt-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  lt-weak zero    b       p = tt
  lt-weak (suc a) zero    ()
  lt-weak (suc a) (suc b) p = lt-weak a b p

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

  lt-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  lt-ne zero    zero    ()
  lt-ne zero    (suc b) p = refl
  lt-ne (suc a) zero    ()
  lt-ne (suc a) (suc b) p = lt-ne a b p

  lt-ne' : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne' zero    zero    p ()
  lt-ne' zero    (suc n) p e = tt
  lt-ne' (suc y) zero    () e
  lt-ne' (suc y) (suc n) p e = lt-ne' y n p e

  lenₛ-∘ : ∀ τ σ → lenₛ (τ ∘ σ) ≡ lenₛ τ
  lenₛ-∘ ⟨⟩       σ = refl
  lenₛ-∘ (τ ,ₛ t) σ = cong suc (lenₛ-∘ τ σ)

  -- a ≤ depth bound with +0
  look-lt : ∀ σ y → T (depthTm (lookupₛ σ y) <ℕ suc (depthSub σ) + 0)
  look-lt σ y = subst (λ k → T (depthTm (lookupₛ σ y) <ℕ k)) (sym (+0 (suc (depthSub σ)))) (depth-look σ y)

  allN-at : ∀ {P : Nat → Set} y xs → AllN P xs → memL y xs ≡ true → P y
  allN-at y []       _        ()
  allN-at y (x ∷ xs) (p , ps') m with y ==ℕ x in e
  ... | true  = subst _ (sym (==ℕ-sound y x (≡-T e))) p
  ... | false = allN-at y xs ps' m

mutual
  lab-at : ∀ {P : Nat → Set} y a → Lab P a → mem y a ≡ true → P y
  lab-at y (lt os cs) (p , ps') m with memL y os in e
  ... | true  = allN-at y os p e
  ... | false = labL-at y cs ps' m

  labL-at : ∀ {P : Nat → Set} y cs → LabL P cs → memCs y cs ≡ true → P y
  labL-at y []       _         ()
  labL-at y (c ∷ cs) (p , ps') m with mem y c in e
  ... | true  = lab-at y c p e
  ... | false = labL-at y cs ps' m

------------------------------------------------------------------------
-- Typed positions compose with flat.

module _ (Δ : Ctx) (I P : Nat → Maybe LT)
         (HI : ∀ y a → I y ≡ just a → Good P 0 (λ _ → ⊤) a) where

  typedImg-comp : TypedImg Δ I → TypedImg Δ (I∘J I P HI)
  typedImg-comp ti y A e with ti y A e
  ... | x , ex , wx , dx , bx with flat-def P 0 (λ _ → ⊤) x (HI y x ex)
  ...   | z , ez with flat-bd P 0 (λ _ → ⊤) x z (HI y x ex) ez
  ...     | wz , com = z , q , wz , dz , bnd A bx
    where
    q : (I y >>= flatG P 0) ≡ just z
    q rewrite ex = ez

    dz : ∀ β i → bd β (dim A + i) z ≡ z
    dz β i = just-inj (trans (sym (com β (dim A + i))) (trans (cong (flatG P 0) (dx β i)) ez))

    bnd : ∀ A → Bnd I A x → Bnd (I∘J I P HI) A z
    bnd ⋆                        _         = tt
    bnd (arr B (var a) (var b))  (ea , eb) = ga , gb
      where
      ga : (I a >>= flatG P 0) ≡ just (bd false (dim B) z)
      ga rewrite ea = com false (dim B)
      gb : (I b >>= flatG P 0) ≡ just (bd true (dim B) z)
      gb rewrite eb = com true (dim B)
    bnd (arr B (var a) (coh _ _ _)) ()
    bnd (arr B (var a) (cst _))     ()
    bnd (arr B (coh _ _ _) _)       ()
    bnd (arr B (cst _) _)           ()

------------------------------------------------------------------------
-- liftS is determined by the lifts of its components.

private
  LiftAt : Nat → Ctx → Sub → List (Nat × LT) → Sub → Set
  LiftAt k Γ τ as ρ = ∀ z → T (z <ℕ lenₛ ρ) → Σ LT λ X → (find z as ≡ just X) × (liftT k Γ (lookupₛ τ z) X ≡ just (lookupₛ ρ z))

  liftAt-init : ∀ k Γ τ as ρ t → LiftAt k Γ τ as (ρ ,ₛ t) → LiftAt k Γ τ as ρ
  liftAt-init k Γ τ as ρ t h z p with h z (lt-weak z (lenₛ ρ) p)
  ... | X , fX , lX = X , fX , trans lX (cong just look-old)
    where
    look-old : lookupₛ (ρ ,ₛ t) z ≡ lookupₛ ρ z
    look-old rewrite lt-ne z (lenₛ ρ) p = refl

liftS-ext : ∀ k Γ τ as ρ → LiftAt k Γ τ as ρ → liftS k Γ τ as (lenₛ ρ) ≡ just ρ
liftS-ext k Γ τ as ⟨⟩       h = refl
liftS-ext k Γ τ as (ρ ,ₛ t) h with h (lenₛ ρ) (lt-suc (lenₛ ρ))
... | X , fX , lX
  rewrite liftS-ext k Γ τ as ρ (liftAt-init k Γ τ as ρ t h) | fX | lX | ==-self (lenₛ ρ) = refl

------------------------------------------------------------------------
-- The theorem.

module _ (Γ : Ctx) (gΓ : Glob Γ) (f : Nat → Nat)
         (Θ₁ : Ctx) (gΘ₁ : Glob Θ₁) (dΘ₁ : Θ₁ ⊢ctx)
         (σ₁ σ₁′ : Sub) (dσ₁ : Γ ⊢sub σ₁ ∶ Θ₁)
         (P : Nat → Maybe LT) (tiP : TypedImg Θ₁ P)
         (rel : ∀ y X → P y ≡ just X → ∀ m → T (depthTm (lookupₛ σ₁ y) <ℕ m) →
                nf m Γ (lookupₛ σ₁ y) ≡ just (relab f X))
         (lifts : ∀ y X → P y ≡ just X → ∀ k → T (depthTm (lookupₛ σ₁ y) <ℕ k) →
                  liftT k Γ (lookupₛ σ₁ y) X ≡ just (lookupₛ σ₁′ y))
  where

  private
    M = suc (depthSub σ₁) + 0
    Ĵ₁ = Ĵ Γ σ₁ M

    tiĴ : TypedImg Θ₁ Ĵ₁
    tiĴ = typed-img Γ σ₁ Θ₁ 0 gΘ₁ (img-res Γ dσ₁ (all-res gΓ dσ₁) dΘ₁ (glob-shape Θ₁ gΘ₁))

    -- the images of σ₁ relabel the positions
    labĴ : ∀ a → Lab (Rel P Ĵ₁ f) a
    labĴ a = lab-of-mem (Rel P Ĵ₁ f) a (λ w _ X e → rel w X e M (look-lt σ₁ w))

    -- the image of a term of Θ₁, substituted, relabels its composite
    sub-rel : ∀ {t A} → Θ₁ ⊢tm t ∶ A → ∀ N a X k → T (depthTm t <ℕ N) → nf N Θ₁ t ≡ just a →
              flatG P 0 a ≡ just X → T (depthTm (t [ σ₁ ]tm) <ℕ k) →
              nf k Γ (t [ σ₁ ]tm) ≡ just (relab f X)
    sub-rel {t} dt N a X k pN ea eX pk with res gΓ (tm[] dt dσ₁) | lt-split (depthTm (t [ σ₁ ]tm)) k pk
    ... | r , fr , _ | i , refl =
      trans (fr i) (cong just (nf-det (suc (depthTm (t [ σ₁ ]tm)) + 0) (N + M) Γ (t [ σ₁ ]tm) r (relab f X) (fr 0) s))
      where
      s : nf (N + M) Γ (t [ σ₁ ]tm) ≡ just (relab f X)
      s = trans (nf-sub Γ σ₁ M N Θ₁ t a (hyp-res Γ σ₁ M gΘ₁ tiĴ dt N pN) ea)
                (relab-flatG P Ĵ₁ f 0 a X (labĴ a) eX)

  -- The coherence case, given the claim for its arguments.
  module _ (tr : Tree) (A : Ty) (σ₂ : Sub) (etr : treeOf (ctxOf tr) ≡ just tr) (pΘ₂ : ctxOf tr ⊢ps)
           (dΘ₂ : ctxOf tr ⊢ctx) (dσ₂ : Θ₁ ⊢sub σ₂ ∶ ctxOf tr)
           (ih : ∀ z → T (z <ℕ lenₛ σ₂) → ∀ n x E′ k → nf n Θ₁ (lookupₛ σ₂ z) ≡ just x → flatG P 0 x ≡ just E′ →
                 T (depthTm ((lookupₛ σ₂ z) [ σ₁ ]tm) <ℕ k) →
                 liftT k Γ ((lookupₛ σ₂ z) [ σ₁ ]tm) E′ ≡ just ((lookupₛ σ₂ z) [ σ₁′ ]tm))
           (n : Nat) (x E′ : LT) (k : Nat)
           (ex : nf (suc n) Θ₁ (coh (ctxOf tr) A σ₂) ≡ just x) (eE : flatG P 0 x ≡ just E′)
           (p : T (depthSub (σ₂ ∘ σ₁) <ℕ k)) where

    private
      I₂ = idTree tr
      d₂ = depthSub σ₂
      ar₂ = all-res gΘ₁ dσ₂
      sh₂ = glob-shape (ctxOf tr) (ps-glob pΘ₂)
      J₀ = J Θ₁ σ₂ (ctxOf tr) 0

      ti₀ : TypedImg (ctxOf tr) J₀
      ti₀ = typed-img Θ₁ σ₂ (ctxOf tr) 0 (ps-glob pΘ₂) (img-res Θ₁ dσ₂ ar₂ dΘ₂ sh₂)

      good₀ = ex-good (ctxOf tr) J₀ ti₀ 0 I₂ (lab-ex tr)
      c₀ = fst (flat-total J₀ 0 (λ _ → ⊤) I₂ good₀)

      e₀ : flatG J₀ 0 I₂ ≡ just c₀
      e₀ = snd (flat-total J₀ 0 (λ _ → ⊤) I₂ good₀)

      nf₀ : nf (suc (suc d₂ + 0)) Θ₁ (coh (ctxOf tr) A σ₂) ≡ just c₀
      nf₀ rewrite etr = trans (flat-is-flatG (suc d₂ + 0) Θ₁ σ₂ 0 I₂) e₀

      xc : x ≡ c₀
      xc = nf-det (suc n) (suc (suc d₂ + 0)) Θ₁ (coh (ctxOf tr) A σ₂) x c₀ ex nf₀

      HI : ∀ y a → J₀ y ≡ just a → Good P 0 (λ _ → ⊤) a
      HI y a e = ex-good Θ₁ P tiP 0 a (img-ex Θ₁ gΘ₁ dσ₂ ar₂ dΘ₂ sh₂ (suc d₂ + 0) y a e)

      Q = I∘J J₀ P HI

      eQ : flatG Q 0 I₂ ≡ just E′
      eQ = trans (flat-assoc J₀ P HI 0 (λ _ → ⊤) I₂ c₀ good₀ e₀) (subst (λ z → flatG P 0 z ≡ just E′) xc eE)

      goodQ = ex-good (ctxOf tr) Q (typedImg-comp (ctxOf tr) J₀ P HI ti₀) 0 I₂ (lab-ex tr)

      in-range : ∀ z → mem z I₂ ≡ true → T (z <ℕ lenₛ σ₂)
      in-range z m = subst (λ l → T (z <ℕ l)) (sym (sub-len dσ₂)) (≡-T (trans (sym (lab-all tr z)) m))

      depth-z : ∀ z → T (z <ℕ lenₛ σ₂) → T (depthTm ((lookupₛ σ₂ z) [ σ₁ ]tm) <ℕ k)
      depth-z z zs = subst (λ t → T (depthTm t <ℕ k)) (lookup-∘ σ₂ σ₁ z zs)
                       (le-lt _ (depthSub (σ₂ ∘ σ₁)) k (depth-look (σ₂ ∘ σ₁) z) p)

      relz : ∀ z → mem z I₂ ≡ true → ∀ X → Q z ≡ just X → nf k Γ (lookupₛ (σ₂ ∘ σ₁) z) ≡ just (relab f X)
      relz z m X eX = trans (cong (nf k Γ) (lookup-∘ σ₂ σ₁ z zs))
                        (sub-rel (S.lookup-sub closed dΘ₂ (snd (lt-lookup (ctxOf tr) z zl)) dσ₂)
                           (suc d₂ + 0) a X k (look-lt σ₂ z) ea eXa (depth-z z zs))
        where
        zl = ≡-T (trans (sym (lab-all tr z)) m)
        zs = in-range z m
        b = bind-inv (J₀ z) _ eX
        a = fst b
        ea = fst (snd b)
        eXa = snd (snd b)

      labRel : Lab (Rel Q (Jσ Γ (σ₂ ∘ σ₁) k f Q) f) I₂
      labRel = lab-of-mem _ I₂ relz

      R = assign-flat Γ (σ₂ ∘ σ₁) k f Q 0 (λ _ → ⊤) I₂ E′ goodQ eQ (nd-idTree tr) labRel
      as = fst R

      e-as : assign k Γ (σ₂ ∘ σ₁) 0 I₂ E′ ≡ just as
      e-as = fst (snd R)

      f-as : Lab (λ y → find y as ≡ Q y) I₂
      f-as = snd (snd (snd R))

      comp : ∀ z → T (z <ℕ lenₛ (σ₂ ∘ σ₁′)) → Σ LT λ X → (find z as ≡ just X)
             × (liftT k Γ (lookupₛ (σ₂ ∘ σ₁) z) X ≡ just (lookupₛ (σ₂ ∘ σ₁′) z))
      comp z q = X , trans (lab-at z I₂ f-as m) qX ,
                 trans (cong (λ t → liftT k Γ t X) (lookup-∘ σ₂ σ₁ z zs))
                   (trans (ih z zs (suc d₂ + 0) a X k ea eX (depth-z z zs))
                          (cong just (sym (lookup-∘ σ₂ σ₁′ z zs))))
        where
        zs : T (z <ℕ lenₛ σ₂)
        zs = subst (λ l → T (z <ℕ l)) (lenₛ-∘ σ₂ σ₁′) q
        m : mem z I₂ ≡ true
        m = trans (lab-all tr z) (T-≡ (subst (λ l → T (z <ℕ l)) (sub-len dσ₂) zs))
        A′ = lt-lookup (ctxOf tr) z (subst (λ l → T (z <ℕ l)) (sub-len dσ₂) zs)
        tia = ti₀ z (fst A′) (snd A′)
        a = fst tia
        ea = fst (snd tia)
        fd = flat-def P 0 (λ _ → ⊤) a (HI z a ea)
        X = fst fd
        eX = snd fd
        qX : Q z ≡ just X
        qX = trans (cong (λ w → w >>= flatG P 0) ea) eX

      e-ls : liftS k Γ (σ₂ ∘ σ₁) as (len (ctxOf tr)) ≡ just (σ₂ ∘ σ₁′)
      e-ls = subst (λ l → liftS k Γ (σ₂ ∘ σ₁) as l ≡ just (σ₂ ∘ σ₁′))
                   (trans (lenₛ-∘ σ₂ σ₁′) (sub-len dσ₂))
                   (liftS-ext k Γ (σ₂ ∘ σ₁) as (σ₂ ∘ σ₁′) comp)

    lift-coh : liftT (suc k) Γ (coh (ctxOf tr) A (σ₂ ∘ σ₁)) E′ ≡ just (coh (ctxOf tr) A (σ₂ ∘ σ₁′))
    lift-coh = trans (bind-just (treeOf (ctxOf tr)) (λ τ → assign k Γ (σ₂ ∘ σ₁) 0 (idTree τ) E′ >>= λ as′ →
                                     liftS k Γ (σ₂ ∘ σ₁) as′ (len (ctxOf tr)) >>= λ σ′ → just (coh (ctxOf tr) A σ′)) etr)
               (trans (bind-just (assign k Γ (σ₂ ∘ σ₁) 0 I₂ E′) (λ as′ →
                                     liftS k Γ (σ₂ ∘ σ₁) as′ (len (ctxOf tr)) >>= λ σ′ → just (coh (ctxOf tr) A σ′)) e-as)
                      (bind-just (liftS k Γ (σ₂ ∘ σ₁) as (len (ctxOf tr))) (λ σ′ → just (coh (ctxOf tr) A σ′)) e-ls))

  mutual
    lift-sub : ∀ {u A} → Θ₁ ⊢tm u ∶ A → ∀ n x E′ k → nf n Θ₁ u ≡ just x → flatG P 0 x ≡ just E′ →
               T (depthTm (u [ σ₁ ]tm) <ℕ k) → liftT k Γ (u [ σ₁ ]tm) E′ ≡ just (u [ σ₁′ ]tm)
    lift-sub (var-wf _ _) zero x E′ k () eE p
    lift-sub (var-wf {i} _ _) (suc n) x E′ k ex eE p with bind-inv (lookup Θ₁ i) _ ex
    ... | A′ , _ , ew = lifts i E′ (trans (sym (wrap-flat P A′ (lt (i ∷ []) []) x 0 ew)) eE) k p
    lift-sub (coh-wf _ _ _ _ _) zero x E′ k () eE p
    lift-sub (coh-wf _ _ _ _ _) (suc n) x E′ zero ex eE ()
    lift-sub {coh Θ₂ A σ₂} (coh-wf pΘ₂ dΘ₂ _ _ dσ₂) (suc n) x E′ (suc k) ex eE p
      with treeOf-ps pΘ₂
    ... | tr , etr , refl = lift-coh tr A σ₂ etr pΘ₂ dΘ₂ dσ₂ (lift-subS dσ₂) n x E′ k ex eE p
    lift-sub (cst-wf {k = ()} _ _) n x E′ k ex eE p

    lift-subS : ∀ {σ₂ Δ} → Θ₁ ⊢sub σ₂ ∶ Δ → ∀ z → T (z <ℕ lenₛ σ₂) → ∀ n x E′ k →
                nf n Θ₁ (lookupₛ σ₂ z) ≡ just x → flatG P 0 x ≡ just E′ →
                T (depthTm ((lookupₛ σ₂ z) [ σ₁ ]tm) <ℕ k) →
                liftT k Γ ((lookupₛ σ₂ z) [ σ₁ ]tm) E′ ≡ just ((lookupₛ σ₂ z) [ σ₁′ ]tm)
    lift-subS (⟨⟩-wf _) z ()
    lift-subS (,-wf {τ} dτ dt) z q with z ==ℕ lenₛ τ in eq
    ... | true  = lift-sub dt
    ... | false = lift-subS dτ z (lt-ne' z (lenₛ τ) q eq)

  ----------------------------------------------------------------------
  -- The same for types.

  -- The endpoints of B, at every dimension, sit at the boundaries of E.
  TyPos : Ty → LT → Set
  TyPos ⋆           E = ⊤
  TyPos (arr B a b) E =
      (Σ Nat λ n → Σ LT λ x → (nf n Θ₁ a ≡ just x) × (flatG P 0 x ≡ just (bd false (dim B) E)))
    × (Σ Nat λ n → Σ LT λ x → (nf n Θ₁ b ≡ just x) × (flatG P 0 x ≡ just (bd true (dim B) E)))
    × TyPos B (bd false (dim B) E)

  private
    arr-step : ∀ k B a b E B′ a′ b′ → liftTy k Γ B (bd false (dim B) E) ≡ just B′ →
               liftT k Γ a (bd false (dim B) E) ≡ just a′ → liftT k Γ b (bd true (dim B) E) ≡ just b′ →
               liftTy k Γ (arr B a b) E ≡ just (arr B′ a′ b′)
    arr-step k B a b E B′ a′ b′ e₁ e₂ e₃ rewrite e₁ | e₂ | e₃ = refl

  lift-sub-ty : ∀ B → Θ₁ ⊢ty B → ∀ E k → TyPos B E → T (depthTy (B [ σ₁ ]ty) <ℕ k) →
                liftTy k Γ (B [ σ₁ ]ty) E ≡ just (B [ σ₁′ ]ty)
  lift-sub-ty ⋆           _            E k _ _ = refl
  lift-sub-ty (arr B a b) (arr-wf da db) E k ((na , xa , ea , fa) , (nb , xb , eb , fb) , tb) p =
    arr-step k (B [ σ₁ ]ty) (a [ σ₁ ]tm) (b [ σ₁ ]tm) E (B [ σ₁′ ]ty) (a [ σ₁′ ]tm) (b [ σ₁′ ]tm)
      (subst (λ j → liftTy k Γ (B [ σ₁ ]ty) (bd false j E) ≡ just (B [ σ₁′ ]ty)) (sym (dim-sub B σ₁))
        (lift-sub-ty B (tm-ty da) (bd false (dim B) E) k tb (max-ltl (depthTy (B [ σ₁ ]ty)) _ k p)))
      (subst (λ j → liftT k Γ (a [ σ₁ ]tm) (bd false j E) ≡ just (a [ σ₁′ ]tm)) (sym (dim-sub B σ₁))
        (lift-sub da na xa (bd false (dim B) E) k ea fa (max-ltl (depthTm (a [ σ₁ ]tm)) (depthTm (b [ σ₁ ]tm)) k (max-ltr (depthTy (B [ σ₁ ]ty)) _ k p))))
      (subst (λ j → liftT k Γ (b [ σ₁ ]tm) (bd true j E) ≡ just (b [ σ₁′ ]tm)) (sym (dim-sub B σ₁))
        (lift-sub db nb xb (bd true (dim B) E) k eb fb (max-ltr (depthTm (a [ σ₁ ]tm)) (depthTm (b [ σ₁ ]tm)) k (max-ltr (depthTy (B [ σ₁ ]ty)) _ k p))))

  -- TyPos from the normal forms of B's endpoints (by (1′) in Θ₁).
  typos : ∀ B → Θ₁ ⊢ty B → ∀ a₀ E → Ex Θ₁ 0 nothing a₀ → Ends Θ₁ B a₀ → flatG P 0 a₀ ≡ just E → TyPos B E
  typos ⋆           _              a₀ E xa en eA = tt
  typos (arr B s u) (arr-wf ds du) a₀ E xa (n , es , eu) eA =
    (n , bd false (dim B) a₀ , es , com false (dim B)) ,
    (n , bd true  (dim B) a₀ , eu , com true  (dim B)) ,
    typos B (tm-ty ds) (bd false (dim B) a₀) (bd false (dim B) E)
          (ex-bd Θ₁ false (dim B) 0 nothing a₀ xa) endsB (com false (dim B))
    where
    com = snd (flat-bd P 0 (λ _ → ⊤) a₀ E (ex-good Θ₁ P tiP 0 a₀ xa) eA)
    r = res gΘ₁ ds
    endsB : Ends Θ₁ B (bd false (dim B) a₀)
    endsB = subst (Ends Θ₁ B)
                  (nf-det (suc (depthTm s) + 0) n Θ₁ s _ _ (fst (snd r) 0) es)
                  (fst (snd (snd (snd (snd (snd r))))))
