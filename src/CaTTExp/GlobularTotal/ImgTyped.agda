------------------------------------------------------------------------
-- F2c, for the coh case of (1′): the images of a typed substitution.
--
-- `ResF Γ t A` is Res of NfTyped with the fuel made explicit: nf
-- succeeds at every fuel above the coh-nesting depth of t (so all the
-- arguments of a coherence share a fuel).
--
-- For Γ ⊢ σ : Δ with ResF for each component (`AllRes`), every
-- variable y : A of Δ has an image nf (σ y) that is a well-formed
-- diagram of Γ of dimension dim A, whose boundaries are the images of
-- A's endpoints, labelled by the variables of σ y and of A[σ]
-- (`img-res`). These are what ExGood's `TypedImg` asks of the images.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.ImgTyped where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; nf; bd; depthTm; depthSub)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex)
open import CaTTExp.GlobularTotal.Labels using (anyL)
open import CaTTExp.GlobularTotal.FvSub using (fv-ty; memL-++)
open import CaTTExp.GlobularTotal.NfTyped using (Dim; Ends)
open import CaTTExp.GlobularTotal.NfFuel using (dim-sub; sub-len; Bnd; ty-scope; ctx-scope)

ResF : Ctx → Tm → Ty → Set
ResF Γ t A = Σ LT λ a →
    (∀ m → nf (suc (depthTm t) + m) Γ t ≡ just a) × WF a × Dim (dim A) a × Ex Γ 0 nothing a
  × Ends Γ A a × (∀ z → mem z a ≡ memL z (fvTmTy t A))

-- Types whose endpoints are variables.
VarTy : Ty → Set
VarTy ⋆                       = ⊤
VarTy (arr B (var a) (var b)) = VarTy B
VarTy (arr B _ _)             = ⊥

Shape : Ctx → Set
Shape Δ = ∀ y B → lookup Δ y ≡ just B → VarTy B

-- ResF for every component of a substitution derivation.
AllRes : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Set
AllRes (⟨⟩-wf _) = ⊤
AllRes {Γ} (,-wf {σ} {Δ} {t} {A} dσ dt) = AllRes dσ × ResF Γ t (A [ σ ]ty)

module _ (Γ : Ctx) where

  BndV : Sub → Ty → LT → Set
  BndV σ ⋆                       x = ⊤
  BndV σ (arr B (var a) (var b)) x =
      (Σ Nat λ n → nf n Γ (lookupₛ σ a) ≡ just (bd false (dim B) x))
    × (Σ Nat λ n → nf n Γ (lookupₛ σ b) ≡ just (bd true (dim B) x))
  BndV σ (arr B _ _)             x = ⊥

  -- The variables of A[σ], read through σ.
  fvImg : Sub → Ty → Nat → Bool
  fvImg σ A z = anyL (λ w → memL z (fvTm (lookupₛ σ w))) (fvTy A)

  ImgRes : Sub → Nat → Ty → Set
  ImgRes σ y A = Σ LT λ x →
      (∀ m → nf (suc (depthTm (lookupₛ σ y)) + m) Γ (lookupₛ σ y) ≡ just x)
    × WF x × Dim (dim A) x × Ex Γ 0 nothing x × BndV σ A x
    × (∀ z → mem z x ≡ (memL z (fvTm (lookupₛ σ y)) ∨ fvImg σ A z))

private
  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = <-suc (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

  lookup-weak : ∀ Γ C y A → lookup Γ y ≡ just A → lookup (Γ ▸ C) y ≡ just A
  lookup-weak Γ C y A e rewrite <-ne y (len Γ) (lookup-lt Γ y A e) = e

  look-old : ∀ σ s y → T (y <ℕ lenₛ σ) → lookupₛ (σ ,ₛ s) y ≡ lookupₛ σ y
  look-old σ s y p rewrite <-ne y (lenₛ σ) p = refl

  look-top : ∀ σ s → lookupₛ (σ ,ₛ s) (lenₛ σ) ≡ s
  look-top σ s rewrite T-≡ (==ℕ-refl (lenₛ σ)) = refl

  ∨-inl : ∀ {a b} → a ≡ true → (a ∨ b) ≡ true
  ∨-inl refl = refl

  ∨-inr : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  e = refl
  ∨-inr false e = e

  ==-self : ∀ x xs → memL x (x ∷ xs) ≡ true
  ==-self x xs rewrite T-≡ (==ℕ-refl x) = refl

  anyL-cong : ∀ f g xs → (∀ w → memL w xs ≡ true → f w ≡ g w) → anyL f xs ≡ anyL g xs
  anyL-cong f g []       h = refl
  anyL-cong f g (x ∷ xs) h =
    cong₂ _∨_ (h x (==-self x xs)) (anyL-cong f g xs (λ w m → h w (∨-inr (w ==ℕ x) m)))

shape-prefix : ∀ Δ A → Shape (Δ ▸ A) → Shape Δ × VarTy A
shape-prefix Δ A sh =
  (λ y B e → sh y B (lookup-weak Δ A y B e)) ,
  sh (len Δ) A (trans (cong (λ b → if b then just A else lookup Δ (len Δ)) (T-≡ (==ℕ-refl (len Δ)))) refl)

module _ (Γ : Ctx) where

  private
    fvImg-weak : ∀ σ s A z → Bnd (lenₛ σ) (fvTy A) → fvImg Γ (σ ,ₛ s) A z ≡ fvImg Γ σ A z
    fvImg-weak σ s A z b =
      anyL-cong _ _ (fvTy A) (λ w m → cong (λ t → memL z (fvTm t)) (look-old σ s w (b w m)))

    bndV-weak : ∀ σ s A x → VarTy A → Bnd (lenₛ σ) (fvTy A) → BndV Γ σ A x → BndV Γ (σ ,ₛ s) A x
    bndV-weak σ s ⋆ x _ _ _ = tt
    bndV-weak σ s (arr B (var a) (var b)) x _ bnd ((n , ea) , (n' , eb)) =
      (n , trans (cong (nf n Γ) (look-old σ s a pa)) ea) ,
      (n' , trans (cong (nf n' Γ) (look-old σ s b pb)) eb)
      where
      pa : T (a <ℕ lenₛ σ)
      pa = bnd a (trans (memL-++ a (fvTy B) (a ∷ b ∷ [])) (∨-inr (memL a (fvTy B)) (==-self a (b ∷ []))))
      pb : T (b <ℕ lenₛ σ)
      pb = bnd b (trans (memL-++ b (fvTy B) (a ∷ b ∷ []))
                   (∨-inr (memL b (fvTy B)) (∨-inr (b ==ℕ a) (==-self b []))))
    bndV-weak σ s (arr B (var a) (coh _ _ _)) x () _ _
    bndV-weak σ s (arr B (var a) (cst ()))    x _ _ _
    bndV-weak σ s (arr B (coh _ _ _) _)       x () _ _
    bndV-weak σ s (arr B (cst ()) _)          x _ _ _

    -- Ends for A[σ] read as BndV for A.
    ends-bndV : ∀ σ A x → VarTy A → Ends Γ (A [ σ ]ty) x → BndV Γ σ A x
    ends-bndV σ ⋆ x _ _ = tt
    ends-bndV σ (arr B (var a) (var b)) x _ (n , ea , eb) =
      (n , trans ea (cong (λ k → just (bd false k x)) (dim-sub B σ))) ,
      (n , trans eb (cong (λ k → just (bd true k x)) (dim-sub B σ)))
    ends-bndV σ (arr B (var a) (coh _ _ _)) x () _
    ends-bndV σ (arr B (var a) (cst ()))    x _ _
    ends-bndV σ (arr B (coh _ _ _) _)       x () _
    ends-bndV σ (arr B (cst ()) _)          x _ _

    dim-cast : ∀ A σ x → Dim (dim (A [ σ ]ty)) x → Dim (dim A) x
    dim-cast A σ x d = subst (λ k → Dim k x) (dim-sub A σ) d

  img-res : ∀ {σ Δ} (dσ : Γ ⊢sub σ ∶ Δ) → AllRes dσ → Δ ⊢ctx → Shape Δ →
            ∀ y A → lookup Δ y ≡ just A → ImgRes Γ σ y A
  img-res (⟨⟩-wf _) _ _ _ y A ()
  img-res (,-wf {σ} {Δ} {t} {C} dσ dt) (ar , rt) (▸-wf dΔ dC) sh y A e
    with shape-prefix Δ C sh | y ==ℕ len Δ in eq
  ... | shΔ , vC | true rewrite ==ℕ-sound y (len Δ) (≡-T eq) | just-inj (sym e)
    with rt
  ...   | x , fx , wx , dx , xx , ex , lx =
    x , fuel , wx , dim-cast C σ x dx , xx ,
    bndV-weak σ t C x vC bC (ends-bndV σ C x vC ex) , labs
    where
    l : lenₛ σ ≡ len Δ
    l = sub-len dσ

    bC : Bnd (lenₛ σ) (fvTy C)
    bC w m = subst (λ n → T (w <ℕ n)) (sym l) (ty-scope dC w m)

    top : lookupₛ (σ ,ₛ t) (len Δ) ≡ t
    top = subst (λ n → lookupₛ (σ ,ₛ t) n ≡ t) l (look-top σ t)

    fuel : ∀ m → nf (suc (depthTm (lookupₛ (σ ,ₛ t) (len Δ))) + m) Γ (lookupₛ (σ ,ₛ t) (len Δ)) ≡ just x
    fuel m rewrite top = fx m

    labs : ∀ z → mem z x ≡ (memL z (fvTm (lookupₛ (σ ,ₛ t) (len Δ))) ∨ fvImg Γ (σ ,ₛ t) C z)
    labs z rewrite top =
      trans (lx z)
      (trans (memL-++ z (fvTm t) (fvTy (C [ σ ]ty)))
             (cong (memL z (fvTm t) ∨_) (trans (fv-ty z σ C) (sym (fvImg-weak σ t C z bC)))))
  img-res (,-wf {σ} {Δ} {t} {C} dσ dt) (ar , rt) (▸-wf dΔ dC) sh y A e
      | shΔ , vC | false with img-res dσ ar dΔ shΔ y A e
  ... | x , fx , wx , dx , xx , bx , lx =
    x , fuel , wx , dx , xx , bndV-weak σ t A x (shΔ y A e) bA bx , labs
    where
    l : lenₛ σ ≡ len Δ
    l = sub-len dσ

    py : T (y <ℕ lenₛ σ)
    py = subst (λ n → T (y <ℕ n)) (sym l) (lookup-lt Δ y A e)

    bA : Bnd (lenₛ σ) (fvTy A)
    bA w m = subst (λ n → T (w <ℕ n)) (sym l) (ctx-scope dΔ y A e w m)

    fuel : ∀ m → nf (suc (depthTm (lookupₛ (σ ,ₛ t) y)) + m) Γ (lookupₛ (σ ,ₛ t) y) ≡ just x
    fuel m rewrite look-old σ t y py = fx m

    labs : ∀ z → mem z x ≡ (memL z (fvTm (lookupₛ (σ ,ₛ t) y)) ∨ fvImg Γ (σ ,ₛ t) A z)
    labs z rewrite look-old σ t y py | fvImg-weak σ t A z bA = lx z

------------------------------------------------------------------------
-- The images at a common fuel are typed in the sense of ExGood.

open import CaTTExp.GlobularTotal.ExGood using (TypedImg) renaming (Bnd to BndJ)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn)
open import CaTTExp.GlobularTotal.NfFuel using (nf-det; nf-≥; depth-look)

private
  ≤-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
  ≤-trans zero    b       c       p q = tt
  ≤-trans (suc a) zero    c       () q
  ≤-trans (suc a) (suc b) zero    p ()
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

  ≤-+ : ∀ a m → T (a <ℕ suc (a + m))
  ≤-+ zero    m = tt
  ≤-+ (suc a) m = ≤-+ a m

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  fuel-le : ∀ d D m → T (d <ℕ suc D) → T ((suc d + 0) <ℕ suc (suc D + m))
  fuel-le d D m p rewrite +0 d = ≤-trans d D (D + m) p (≤-+ D m)

module _ (Γ : Ctx) (σ : Sub) (Δ : Ctx) (m : Nat) where

  J : Nat → Maybe LT
  J y = nf (suc (depthSub σ) + m) Γ (lookupₛ σ y)

  private
    J-of : ∀ y x → (∀ m → nf (suc (depthTm (lookupₛ σ y)) + m) Γ (lookupₛ σ y) ≡ just x) → J y ≡ just x
    J-of y x fx = nf-≥ (suc (depthTm (lookupₛ σ y)) + 0) (suc (depthSub σ) + m) Γ (lookupₛ σ y) x (fx 0)
                    (fuel-le (depthTm (lookupₛ σ y)) (depthSub σ) m (depth-look σ y))

  typed-img : Glob Δ → (∀ y A → lookup Δ y ≡ just A → ImgRes Γ σ y A) → TypedImg Δ J
  typed-img g ir y A e with ir y A e
  ... | x , fx , wx , dx , _ , bx , _ = x , J-of y x fx , wx , dx , bnd A (g y A e) bx
    where
    bnd : ∀ A → TyIn Δ A → BndV Γ σ A x → BndJ J A x
    bnd ⋆ _ _ = tt
    bnd (arr B (var a) (var b)) (_ , _ , ea , eb , _) ((n , na) , (n' , nb)) with ir a B ea | ir b B eb
    ... | xa , fa , _ | xb , fb , _ =
      trans (J-of a xa fa) (cong just (nf-det (suc (depthTm (lookupₛ σ a)) + 0) n Γ (lookupₛ σ a) xa _ (fa 0) na)) ,
      trans (J-of b xb fb) (cong just (nf-det (suc (depthTm (lookupₛ σ b)) + 0) n' Γ (lookupₛ σ b) xb _ (fb 0) nb))
    bnd (arr B (var a) (coh _ _ _)) () _
    bnd (arr B (var a) (cst ()))    _ _
    bnd (arr B (coh _ _ _) _)       () _
    bnd (arr B (cst ()) _)          _ _
