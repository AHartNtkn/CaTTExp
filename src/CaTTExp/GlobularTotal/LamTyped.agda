------------------------------------------------------------------------
-- F2c, step (P1) of lemmas 3–5, second part: the filler's
-- substitution λ : Θ_τ → Γ is well typed.
--
-- Let N be a diagram of a globular Γ with τ = shape N, Θ = ctxOf τ, and
-- f = lamF (zipLab (idTree τ) N) the label of N at each variable's
-- position. Then
--
--   labSub-ρ : labSub (zipLab (idTree τ) N) (len Θ) ≡ just (ρ f (len Θ))
--   ρ-typed  : Γ ⊢ ρ f (len Θ) ∶ Θ
--
-- where ρ f n = ⟨var (f 0), …, var (f (n−1))⟩. The type of f y is the
-- type of y with f applied: N and idTree τ are diagrams of the same
-- shape (Relabel.relab-id), so a cell of Θ from p to q sits where N
-- has a cell from f p to f q (`corr`), and the types below agree by
-- induction on dimension (`look-f`).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LamTyped where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; idTree; shape; zipLab; labSub; module Lists)
open Lists using (find)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL; Ex; ExCs; Cell; AllN; dimOf)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn; ps-glob)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.FvSub using (memL-++)
open import CaTTExp.GlobularTotal.NfFuel using (ctx-scope; ty-scope)
open import CaTTExp.GlobularTotal.Relabel
  using (relab; relabs; mapN; lamF; memK; memK-zipLab; relab-id; shape-id; wf-id)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  lt-ne : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne zero    zero    p ()
  lt-ne zero    (suc n) p e = tt
  lt-ne (suc y) zero    () e
  lt-ne (suc y) (suc n) p e = lt-ne y n p e

  lt-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  lt-trans zero    (suc b) (suc c) p q = tt
  lt-trans (suc a) (suc b) (suc c) p q = lt-trans a b c p q
  lt-trans a       zero    c       () q
  lt-trans a       (suc b) zero    p ()

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = <-suc (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

  lookup-top : ∀ Γ C → lookup (Γ ▸ C) (len Γ) ≡ just C
  lookup-top Γ C rewrite T-≡ (==ℕ-refl (len Γ)) = refl

  lookup-weak : ∀ Γ C y A → lookup Γ y ≡ just A → lookup (Γ ▸ C) y ≡ just A
  lookup-weak Γ C y A e rewrite <-ne y (len Γ) (lookup-lt Γ y A e) = e

  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

  dim0 : ∀ A → dim A ≡ 0 → A ≡ ⋆
  dim0 ⋆           _ = refl
  dim0 (arr _ _ _) ()

------------------------------------------------------------------------
-- The renaming substitution.

ρ : (Nat → Nat) → Nat → Sub
ρ f zero    = ⟨⟩
ρ f (suc n) = ρ f n ,ₛ var (f n)

lenρ : ∀ f n → lenₛ (ρ f n) ≡ n
lenρ f zero    = refl
lenρ f (suc n) = cong suc (lenρ f n)

look-ρ : ∀ f n y → T (y <ℕ n) → lookupₛ (ρ f n) y ≡ var (f y)
look-ρ f zero    y ()
look-ρ f (suc n) y p rewrite lenρ f n with y ==ℕ n in eq
... | true  rewrite ==ℕ-sound y n (≡-T eq) = refl
... | false = look-ρ f n y (lt-ne y n p eq)

-- labSub reads ρ when every key below n is present.
private
  find-just : ∀ y L → memK y L ≡ true → find y L ≡ just (lamF L y)
  find-just y []             ()
  find-just y ((k , v) ∷ L) m with y ==ℕ k
  ... | true  = refl
  ... | false = find-just y L m

labSub-ρ : ∀ L n → (∀ y → T (y <ℕ n) → memK y L ≡ true) → labSub L n ≡ just (ρ (lamF L) n)
labSub-ρ L zero    h = refl
labSub-ρ L (suc n) h
  rewrite labSub-ρ L n (λ y p → h y (<-weak y n p))
        | find-just n L (h n (<-suc n)) = refl

------------------------------------------------------------------------
-- Substitution only reads the free variables.

mutual
  ty-cong : ∀ A σ σ' → (∀ w → memL w (fvTy A) ≡ true → lookupₛ σ w ≡ lookupₛ σ' w) → A [ σ ]ty ≡ A [ σ' ]ty
  ty-cong ⋆           σ σ' h = refl
  ty-cong (arr A t u) σ σ' h =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (ty-cong A σ σ' (λ w m → h w (trans (memL-++ w (fvTy A) _) (∨-inl _ _ m))))
      (cong₂ _,_
        (tm-cong t σ σ' (λ w m → h w (trans (memL-++ w (fvTy A) _) (∨-inr (memL w (fvTy A)) _
                          (trans (memL-++ w (fvTm t) (fvTm u)) (∨-inl _ _ m))))))
        (tm-cong u σ σ' (λ w m → h w (trans (memL-++ w (fvTy A) _) (∨-inr (memL w (fvTy A)) _
                          (trans (memL-++ w (fvTm t) (fvTm u)) (∨-inr (memL w (fvTm t)) _ m)))))))

  tm-cong : ∀ t σ σ' → (∀ w → memL w (fvTm t) ≡ true → lookupₛ σ w ≡ lookupₛ σ' w) → t [ σ ]tm ≡ t [ σ' ]tm
  tm-cong (var i)     σ σ' h = h i (∨-inl _ _ (T-≡ (==ℕ-refl i)))
  tm-cong (coh Γ A τ) σ σ' h = cong (coh Γ A) (sub-cong τ σ σ' h)
  tm-cong (cst ())    σ σ' h

  sub-cong : ∀ τ σ σ' → (∀ w → memL w (fvSub τ) ≡ true → lookupₛ σ w ≡ lookupₛ σ' w) → (τ ∘ σ) ≡ (τ ∘ σ')
  sub-cong ⟨⟩       σ σ' h = refl
  sub-cong (τ ,ₛ t) σ σ' h =
    cong₂ _,ₛ_ (sub-cong τ σ σ' (λ w m → h w (trans (memL-++ w (fvSub τ) (fvTm t)) (∨-inl _ _ m))))
               (tm-cong t σ σ' (λ w m → h w (trans (memL-++ w (fvSub τ) (fvTm t)) (∨-inr (memL w (fvSub τ)) _ m))))

------------------------------------------------------------------------
-- Cells of the same position correspond.

module _ (Θ Γ : Ctx) (f : Nat → Nat) where

  -- y : ⋆ ↦ f y : ⋆, and y : p → q ↦ f y : f p → f q.
  Corr : Nat → Set
  Corr y = ((lookup Θ y ≡ just ⋆) × (lookup Γ (f y) ≡ just ⋆))
         ⊎ (Σ Ty λ B → Σ Ty λ B' → Σ Nat λ p → Σ Nat λ q →
              (lookup Θ y ≡ just (arr B (var p) (var q)))
            × (lookup Γ (f y) ≡ just (arr B' (var (f p)) (var (f q)))))

  mp : Maybe (Nat × Nat) → Maybe (Nat × Nat)
  mp nothing        = nothing
  mp (just (p , q)) = just (f p , f q)

  Root : Nat → Maybe (Nat × Nat) → Set
  Root e nothing  = e ≡ 0
  Root e (just _) = ⊤

  private
    cell-corr : ∀ e par o → Root e par → Cell Θ e par o → Cell Γ e (mp par) (f o) → Corr o
    cell-corr e nothing o r ((A , eA) , dA) ((A' , eA') , dA') with r
    ... | refl =
      inl (trans eA (cong just (dim0 A (trans (sym (dimOf-just Θ o A eA)) dA))) ,
           trans eA' (cong just (dim0 A' (trans (sym (dimOf-just Γ (f o) A' eA')) dA'))))
    cell-corr e (just (p , q)) o r ((B , eB) , _) ((B' , eB') , _) = inr (B , B' , p , q , eB , eB')

    all-corr : ∀ e par os → Root e par → AllN (Cell Θ e par) os → AllN (Cell Γ e (mp par)) (mapN f os) →
               ∀ y → memL y os ≡ true → Corr y
    all-corr e par []       r _        _          y ()
    all-corr e par (o ∷ os) r (c , cs) (c' , cs') y m with y ==ℕ o in eq
    ... | true rewrite ==ℕ-sound y o (≡-T eq) = cell-corr e par o r c c'
    ... | false = all-corr e par os r cs cs' y m

  mutual
    corr : ∀ e par X → Root e par → Ex Θ e par X → Ex Γ e (mp par) (relab f X) →
           ∀ y → mem y X ≡ true → Corr y
    corr e par (lt os cs) r (ao , xc) (ao' , xc') y m with y ∈? os
      where
      _∈?_ : ∀ y os → (memL y os ≡ true) ⊎ (memL y os ≡ false)
      y ∈? os with memL y os
      ... | true  = inl refl
      ... | false = inr refl
    ... | inl h = all-corr e par os r ao ao' y h
    ... | inr h = corrCs e os cs xc xc' y (subst (λ b → (b ∨ memCs y cs) ≡ true) h m)

    corrCs : ∀ e os cs → ExCs Θ e os cs → ExCs Γ e (mapN f os) (relabs f cs) →
             ∀ y → memCs y cs ≡ true → Corr y
    corrCs e (o ∷ [])      []       _          _            y ()
    corrCs e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (xc' , xs') y m with mem y c in eq
    ... | true  = corr (suc e) (just (o , o')) c tt xc xc' y eq
    ... | false = corrCs e (o' ∷ os) cs xs xs' y m
    corrCs e []            _        () _ y m
    corrCs e (o ∷ [])      (c ∷ cs) () _ y m
    corrCs e (o ∷ o' ∷ os) []       () _ y m

------------------------------------------------------------------------
-- The theorem.

module _ (Γ : Ctx) (gΓ : Glob Γ) (dΓ : Γ ⊢ctx) (N : LT) (xN : Ex Γ 0 nothing N) (wN : WF N) where

  private
    τ = shape N
    Θ = ctxOf τ
    I = idTree τ
    L = zipLab I N
    f = lamF L
    n = len Θ
    σλ = ρ f n

    rel : relab f I ≡ N
    rel = relab-id τ N refl wN

    corr-I : ∀ y → mem y I ≡ true → Corr Θ Γ f y
    corr-I = corr Θ Γ f 0 nothing I refl (lab-ex τ) (subst (Ex Γ 0 nothing) (sym rel) xN)

    inI : ∀ y → T (y <ℕ n) → mem y I ≡ true
    inI y p = trans (lab-all τ y) (T-≡ p)

    gΘ : Glob Θ
    gΘ = ps-glob (snd (psOf τ))

    -- by induction on (an upper bound of) dimension
    look-f' : ∀ k y A → T (dim A <ℕ k) → lookup Θ y ≡ just A → lookup Γ (f y) ≡ just (A [ σλ ]ty)
    look-f' zero    y A () e
    look-f' (suc k) y A d e with corr-I y (inI y (lookup-lt Θ y A e))
    ... | inl (eΘ , eΓ) rewrite just-inj (trans (sym e) eΘ) = eΓ
    ... | inr (B , B' , p , q , eΘ , eΓ) rewrite just-inj (trans (sym e) eΘ) with gΘ y _ eΘ
    ...   | p<n , q<n , ep , eq , _ with gΓ (f y) _ eΓ
    ...     | _ , _ , ep' , _ , _ =
      trans eΓ (cong just (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
        (just-inj (trans (sym ep') (look-f' k p B d ep)))
        (cong₂ _,_ (sym (look-ρ f n p p<n)) (sym (look-ρ f n q q<n)))))

  look-f : ∀ y A → lookup Θ y ≡ just A → lookup Γ (f y) ≡ just (A [ σλ ]ty)
  look-f y A = look-f' (suc (dim A)) y A (<-suc (dim A))

  labSub-λ : labSub L n ≡ just σλ
  labSub-λ = labSub-ρ L n (λ y p → trans (memK-zipLab y I N (shape-id τ) (wf-id τ) wN) (inI y p))

  private
    pre : ∀ {Δ} → Δ ⊢ctx → (∀ y A → lookup Δ y ≡ just A → lookup Θ y ≡ just A) → T (len Δ <ℕ suc n) →
          Γ ⊢sub ρ f (len Δ) ∶ Δ
    pre ε-wf _ _ = ⟨⟩-wf dΓ
    pre (▸-wf {Δ} {A} dΔ dA) h p =
      ,-wf (pre dΔ (λ y B e → h y B (lookup-weak Δ A y B e)) (<-weak (len Δ) n (lt-lenΔ p)))
           (var-wf dΓ (trans (look-f (len Δ) A (h (len Δ) A (lookup-top Δ A)))
                             (cong just (ty-cong A σλ (ρ f (len Δ))
                               (λ w m → trans (look-ρ f n w (lt-trans w (len Δ) n (ty-scope dA w m) (lt-lenΔ p)))
                                              (sym (look-ρ f (len Δ) w (ty-scope dA w m))))))))
      where
      lt-lenΔ : T (suc (len Δ) <ℕ suc n) → T (len Δ <ℕ n)
      lt-lenΔ q = q

  λ-typed : Θ ⊢ctx → Γ ⊢sub σλ ∶ Θ
  λ-typed dΘ = pre dΘ (λ y A e → e) (<-suc n)
