------------------------------------------------------------------------
-- F2c, step (P3), conclusion: the positions `assign` returns for a
-- coherence's pasting context Θ₁ are typed in the sense of ExGood.
--
--   assign-typed : Inv 0 (idTree τ₁) E as → TypedImg Θ₁ J → TypedImg Θ₁ (λ y → find y as)
--
-- Boundaries come from BdOK (an object y of a branch between o and o′
-- is a cell y : o → o′ of Θ₁, by Uniq.Ex); dimensions transfer from
-- the images through relabelling (`dim-relab`: bd β j only reads the
-- shape).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.AssignTyped where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; bdL; idTree; module Lists)
open Lists using (find)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL; Ex; ExCs; Cell; AllN; dimOf)
open import CaTTExp.GlobularTotal.ExGood using (TypedImg) renaming (Bnd to BndJ)
open import CaTTExp.GlobularTotal.DimCheck using (ex-wf)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn)
open import CaTTExp.GlobularTotal.Relabel using (relab; relabs; mapN)
open import CaTTExp.GlobularTotal.Assign using (ObjB; BdOK; BdCs; Inv)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  arr-inj : ∀ {B B' : Ty} {s s' u u'} → arr B s u ≡ arr B' s' u' → (B ≡ B') × (s ≡ s') × (u ≡ u')
  arr-inj refl = refl , refl , refl

  var-inj : ∀ {a b} → Tm.var a ≡ var b → a ≡ b
  var-inj refl = refl

  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

------------------------------------------------------------------------
-- Boundary-preservation (bd β j X ≡ X) only reads the shape.

mutual
  dim-relab : ∀ f β j X → bd β j (relab f X) ≡ relab f X → bd β j X ≡ X
  dim-relab f false zero (lt (o ∷ []) []) e = refl
  dim-relab f true  zero (lt (o ∷ []) []) e = refl
  dim-relab f false zero (lt []            cs)       e with lt-injₒ e
  ... | ()
  dim-relab f false zero (lt (o ∷ o' ∷ os) cs)       e with ∷-injₜ (lt-injₒ e)
  ... | ()
  dim-relab f false zero (lt (o ∷ [])      (c ∷ cs)) e with lt-injₛ e
  ... | ()
  dim-relab f true zero (lt []            cs)       e with lt-injₒ e
  ... | ()
  dim-relab f true zero (lt (o ∷ o' ∷ os) cs)       e with ∷-injₜ (lt-injₒ e)
  ... | ()
  dim-relab f true zero (lt (o ∷ [])      (c ∷ cs)) e with lt-injₛ e
  ... | ()
  dim-relab f false (suc j) (lt os cs) e = cong (lt os) (dims-relab f false j cs (lt-injₛ e))
  dim-relab f true  (suc j) (lt os cs) e = cong (lt os) (dims-relab f true j cs (lt-injₛ e))

  dims-relab : ∀ f β j cs → bdL β j (relabs f cs) ≡ relabs f cs → bdL β j cs ≡ cs
  dims-relab f β j []       e = refl
  dims-relab f β j (c ∷ cs) e = cong₂ _∷_ (dim-relab f β j c (∷-injₕ e)) (dims-relab f β j cs (∷-injₜ e))

------------------------------------------------------------------------
-- Boundaries of positions from BdOK.

module _ (Θ₁ : Ctx) (P : Nat → Maybe LT) where

  BndAt : Nat → Set
  BndAt y = ∀ C a b → lookup Θ₁ y ≡ just (arr C (var a) (var b)) →
            Σ LT λ X → (P y ≡ just X) × (P a ≡ just (bd false (dim C) X)) × (P b ≡ just (bd true (dim C) X))

  private
    objs-bnd : ∀ e o o' os cs → AllN (Cell Θ₁ (suc e) (just (o , o'))) os → ObjB P e o o' (lt os cs) →
               ∀ y → memL y os ≡ true → BndAt y
    objs-bnd e o o' []       cs _ _ y ()
    objs-bnd e o o' (x ∷ xs) cs (((B , eB) , dB) , cells) ((X , ex , po , po') , rest) y m with y ==ℕ x in eq
    ... | false = objs-bnd e o o' xs cs cells rest y m
    ... | true rewrite ==ℕ-sound y x (≡-T eq) = λ C a b e' → go C a b e'
      where
      go : ∀ C a b → lookup Θ₁ x ≡ just (arr C (var a) (var b)) → _
      go C a b e' with arr-inj (just-inj (trans (sym eB) e'))
      ... | refl , pa , pb rewrite sym (var-inj pa) | sym (var-inj pb) =
        X , ex ,
        subst (λ k → P o ≡ just (bd false k X)) (sym dBe) po ,
        subst (λ k → P o' ≡ just (bd true k X)) (sym dBe) po'
        where
        dBe : dim B ≡ e
        dBe = suc-inj (trans (sym (dimOf-just Θ₁ x _ eB)) dB)

  kids : LT → List LT
  kids (lt _ cs) = cs

  mutual
    bnd-ex : ∀ e par R → Ex Θ₁ e par R → BdOK P e R → ∀ y → memCs y (kids R) ≡ true → BndAt y
    bnd-ex e par (lt os cs) (_ , xs) b y m = bnd-cs e os cs xs b y m

    bnd-cs : ∀ e os cs → ExCs Θ₁ e os cs → BdCs P e os cs → ∀ y → memCs y cs ≡ true → BndAt y
    bnd-cs e (o ∷ [])      []       _          _ y ()
    bnd-cs e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (ob , bc , bs) y m with ∨-split (mem y c) (memCs y cs) m
    ... | inr h = bnd-cs e (o' ∷ os) cs xs bs y h
    ... | inl h with c | xc | ob | bc
    ...   | lt os' cs' | (cells , xcs) | ob' | bc' with ∨-split (memL y os') (memCs y cs') h
    ...     | inl h' = objs-bnd e o o' os' cs' cells ob' y h'
    ...     | inr h' = bnd-cs (suc e) os' cs' xcs bc' y h'
    bnd-cs e []            _        () _ y m
    bnd-cs e (o ∷ [])      (c ∷ cs) () _ y m
    bnd-cs e (o ∷ o' ∷ os) []       () _ y m

  bnd-root : ∀ R → Ex Θ₁ 0 nothing R → BdOK P 0 R → ∀ y B a b → mem y R ≡ true →
             lookup Θ₁ y ≡ just (arr B (var a) (var b)) →
             Σ LT λ X → (P y ≡ just X) × (P a ≡ just (bd false (dim B) X)) × (P b ≡ just (bd true (dim B) X))
  bnd-root (lt os cs) (cells , xcs) b3 y B a b m e' with ∨-split (memL y os) (memCs y cs) m
  ... | inl h = ⊥-elim (zero≢suc (trans (sym (root-dim' os cells h)) (dimOf-just Θ₁ y _ e')))
    where
    zero≢suc : ∀ {k} → 0 ≡ suc k → ⊥
    zero≢suc ()
    root-dim' : ∀ os → AllN (Cell Θ₁ 0 nothing) os → memL y os ≡ true → dimOf Θ₁ y ≡ 0
    root-dim' []       _              ()
    root-dim' (o ∷ os) ((_ , d) , cs) m with y ==ℕ o in eq
    ... | true rewrite ==ℕ-sound y o (≡-T eq) = d
    ... | false = root-dim' os cs m
  ... | inr h = bnd-cs 0 os cs xcs b3 y h B a b e'

------------------------------------------------------------------------
-- The theorem.

private
  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = lt-suc (len Γ)
    where
    lt-suc : ∀ a → T (a <ℕ suc a)
    lt-suc zero    = tt
    lt-suc (suc a) = lt-suc a
  ... | false = weak y (len Γ) (lookup-lt Γ y A e)
    where
    weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
    weak zero    b       p = tt
    weak (suc a) zero    ()
    weak (suc a) (suc b) p = weak a b p

  root-dim : ∀ Θ os y → AllN (Cell Θ 0 nothing) os → memL y os ≡ true → dimOf Θ y ≡ 0
  root-dim Θ []       y _              ()
  root-dim Θ (o ∷ os) y ((_ , d) , cs) m with y ==ℕ o in eq
  ... | true rewrite ==ℕ-sound y o (≡-T eq) = d
  ... | false = root-dim Θ os y cs m

module _ (Γ : Ctx) (σ : Sub) (n : Nat) (Θ : Ctx) (f : Nat → Nat) (τ₁ : Tree) where

  open import CaTTExp.GlobularTotal.Assign using (J)

  private
    Θ₁ = ctxOf τ₁
    I₁ = idTree τ₁

  assign-typed : ∀ E as → Inv Γ σ n Θ f 0 I₁ E as → Glob Θ₁ → TypedImg Θ₁ (J Γ σ n Θ f) →
                 TypedImg Θ₁ (λ y → find y as)
  assign-typed E as (i1 , _ , i3 , _) gΘ tiJ y A e
    with i1 y (trans (lab-all τ₁ y) (T-≡ (lookup-lt Θ₁ y A e))) | tiJ y A e
  ... | X , fX , xX , jX , _ | x' , ej , _ , dx' , _ =
    X , fX , ex-wf Θ 0 nothing X xX ,
    (λ β i → dim-relab f β (dim A + i) X (trans (cong (bd β (dim A + i)) rx) (trans (dx' β i) (sym rx)))) ,
    bnd A (gΘ y A e) e
    where
    rx : relab f X ≡ x'
    rx = just-inj (trans (sym jX) ej)

    P = λ y → find y as

    bnd : ∀ A → TyIn Θ₁ A → lookup Θ₁ y ≡ just A → BndJ P A X
    bnd ⋆ _ _ = tt
    bnd (arr B (var a) (var b)) _ e' with bnd-root Θ₁ P I₁ (lab-ex τ₁) i3 y B a b
                                           (trans (lab-all τ₁ y) (T-≡ (lookup-lt Θ₁ y _ e'))) e'
    ... | X' , fX' , pa , pb with just-inj (trans (sym fX) fX')
    ...   | refl = pa , pb
    bnd (arr B (var a) (coh _ _ _)) () _
    bnd (arr B (var a) (cst ()))    _ _
    bnd (arr B (coh _ _ _) _)       () _
    bnd (arr B (cst ()) _)          _ _
