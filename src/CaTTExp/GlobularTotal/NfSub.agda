------------------------------------------------------------------------
-- F2c, lemma 1b: the strict normal form of a substitution instance.
--
-- With Ĵ y = nf m Δ' (σ y), the images of the variables under σ,
--
--   nf-sub : nf n Δ t ≡ just a  ⟹  nf (n + m) Δ' (t [ σ ]) ≡ flatG Ĵ 0 a
--
-- i.e. the normal form of t[σ] is the normal form of t with each
-- variable replaced by the normal form of its image. This is the strict
-- image being a functor. The hypothesis `Hyp n Δ t` asks, at every coh
-- inside t, that its argument substitution is long enough for the
-- labels of its pasting tree, that the images of its arguments are
-- compatible (FlatBd.Good), and that those images are compatible for Ĵ.
-- Lemma (1) is to supply Hyp from typing.
--
-- Also here: nf is monotone in fuel (nf-+), flat depends only on the
-- images of the labels it reads (flatG-cong), and the normal form of a
-- variable flattens to its image (wrap-flat).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.NfSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; nf; flat; flatL; wrap; idTree)
open import CaTTExp.GlobularTotal.FlatBd
open import CaTTExp.GlobularTotal.FlatAssoc

private
  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  Top : LT → Set
  Top _ = ⊤

------------------------------------------------------------------------
-- Predicates on the labels of a tree.

AllN : (Nat → Set) → List Nat → Set
AllN P []       = ⊤
AllN P (x ∷ xs) = P x × AllN P xs

mutual
  Lab : (Nat → Set) → LT → Set
  Lab P (lt os cs) = AllN P os × LabL P cs

  LabL : (Nat → Set) → List LT → Set
  LabL P []       = ⊤
  LabL P (c ∷ cs) = Lab P c × LabL P cs

private
  allN-zip : ∀ {P Q R : Nat → Set} → (∀ y → P y → Q y → R y) →
             ∀ xs → AllN P xs → AllN Q xs → AllN R xs
  allN-zip f []       _        _        = tt
  allN-zip f (x ∷ xs) (p , pp) (q , qq) = f x p q , allN-zip f xs pp qq

mutual
  lab-zip : ∀ {P Q R : Nat → Set} → (∀ y → P y → Q y → R y) →
            ∀ t → Lab P t → Lab Q t → Lab R t
  lab-zip f (lt os cs) (p , pp) (q , qq) = allN-zip f os p q , labL-zip f cs pp qq

  labL-zip : ∀ {P Q R : Nat → Set} → (∀ y → P y → Q y → R y) →
             ∀ cs → LabL P cs → LabL Q cs → LabL R cs
  labL-zip f []       _        _        = tt
  labL-zip f (c ∷ cs) (p , pp) (q , qq) = lab-zip f c p q , labL-zip f cs pp qq

-- Every label of a compatible tree has an image.
module _ (I : Nat → Maybe LT) where
  private
    Def : Nat → Set
    Def y = Σ LT λ b → I y ≡ just b

    all-def : ∀ {e P} os → AllL I (Ok I e P) os → AllN Def os
    all-def []       _                       = tt
    all-def (o ∷ os) ((b , eb , _) , oks)    = (b , eb) , all-def os oks

  mutual
    good-lab : ∀ e P t → Good I e P t → Lab (λ y → Σ LT λ b → I y ≡ just b) t
    good-lab e P (lt os cs) (oks , g) = all-def os oks , goodCs-lab e os cs g

    goodCs-lab : ∀ e os cs → GoodCs I e os cs → LabL (λ y → Σ LT λ b → I y ≡ just b) cs
    goodCs-lab e []            cs       ()
    goodCs-lab e (o ∷ [])      []       g = tt
    goodCs-lab e (o ∷ [])      (c ∷ cs) ()
    goodCs-lab e (o ∷ o' ∷ os) []       ()
    goodCs-lab e (o ∷ o' ∷ os) (c ∷ cs) (gc , g) =
      good-lab (suc e) _ c gc , goodCs-lab e (o' ∷ os) cs g

------------------------------------------------------------------------
-- flat reads only the images of the labels.

mutual
  flatG-cong : ∀ f g d t → Lab (λ y → f y ≡ g y) t → flatG f d t ≡ flatG g d t
  flatG-cong f g d (lt os (c ∷ cs))   (_ , l)       = flatGL-cong f g d c cs l
  flatG-cong f g d (lt [] [])         _             = refl
  flatG-cong f g d (lt (y ∷ []) [])   ((p , _) , _) = p
  flatG-cong f g d (lt (y ∷ y' ∷ ys) []) _          = refl

  flatGL-cong : ∀ f g d c cs → LabL (λ y → f y ≡ g y) (c ∷ cs) → flatGL f d c cs ≡ flatGL g d c cs
  flatGL-cong f g d c []        (lc , _)        = flatG-cong f g (suc d) c lc
  flatGL-cong f g d c (c' ∷ cs) (lc , ls)
    rewrite flatG-cong f g (suc d) c lc | flatGL-cong f g d c' cs ls = refl

-- ... and is monotone in them.
mutual
  flatG-mono : ∀ f g → (∀ y b → f y ≡ just b → g y ≡ just b) →
               ∀ d t a → flatG f d t ≡ just a → flatG g d t ≡ just a
  flatG-mono f g h d (lt os (c ∷ cs))      a e = flatGL-mono f g h d c cs a e
  flatG-mono f g h d (lt [] [])            a ()
  flatG-mono f g h d (lt (y ∷ []) [])      a e = h y a e
  flatG-mono f g h d (lt (y ∷ y' ∷ ys) []) a ()

  flatGL-mono : ∀ f g → (∀ y b → f y ≡ just b → g y ≡ just b) →
                ∀ d c cs a → flatGL f d c cs ≡ just a → flatGL g d c cs ≡ just a
  flatGL-mono f g h d c []        a e = flatG-mono f g h (suc d) c a e
  flatGL-mono f g h d c (c' ∷ cs) a e
    with bind-inv (flatG f (suc d) c) _ e
  ... | x , ex , e'
    with bind-inv (flatGL f d c' cs) _ e'
  ... | y , ey , e''
    rewrite flatG-mono f g h (suc d) c x ex | flatGL-mono f g h d c' cs y ey = e''

------------------------------------------------------------------------
-- nf is monotone in fuel.

nf-suc : ∀ m Γ t b → nf m Γ t ≡ just b → nf (suc m) Γ t ≡ just b
nf-suc zero    Γ t           b ()
nf-suc (suc m) Γ (var x)     b e = e
nf-suc (suc m) Γ (coh Θ A τ) b e
  with bind-inv (treeOf Θ) _ e
... | tr , etr , ef rewrite etr =
  trans (flat-is-flatG (suc m) Γ τ 0 (idTree tr))
        (flatG-mono (λ y → nf m Γ (lookupₛ τ y)) (λ y → nf (suc m) Γ (lookupₛ τ y))
                    (λ y b' → nf-suc m Γ (lookupₛ τ y) b')
                    0 (idTree tr) b
                    (trans (sym (flat-is-flatG m Γ τ 0 (idTree tr))) ef))
nf-suc (suc m) Γ (cst ()) b e

nf-+ : ∀ k m Γ t b → nf m Γ t ≡ just b → nf (k + m) Γ t ≡ just b
nf-+ zero    m Γ t b e = e
nf-+ (suc k) m Γ t b e = nf-suc (k + m) Γ t b (nf-+ k m Γ t b e)

------------------------------------------------------------------------
-- The normal form of a variable flattens to its image.

wrap-flat : ∀ J A t w d → wrap A t ≡ just w → flatG J d w ≡ flatG J (d + dim A) t
wrap-flat J ⋆ t w d refl = cong (λ k → flatG J k t) (sym (+-zero d))
wrap-flat J (arr B (var a) (var b)) t w d e =
  trans (wrap-flat J B (lt (a ∷ b ∷ []) (t ∷ [])) w d e)
        (cong (λ k → flatG J k t) (sym (+-suc d (dim B))))
wrap-flat J (arr B (var a) (coh _ _ _)) t w d ()
wrap-flat J (arr B (var a) (cst ())) t w d e
wrap-flat J (arr B (coh _ _ _) _) t w d ()
wrap-flat J (arr B (cst ()) _) t w d e

------------------------------------------------------------------------
-- Lookup in a composite substitution.

private
  lenₛ-∘ : ∀ τ σ → lenₛ (τ ∘ σ) ≡ lenₛ τ
  lenₛ-∘ ⟨⟩       σ = refl
  lenₛ-∘ (τ ,ₛ t) σ = cong suc (lenₛ-∘ τ σ)

  lt-ne : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne zero    zero    p ()
  lt-ne zero    (suc n) p e = tt
  lt-ne (suc y) zero    () e
  lt-ne (suc y) (suc n) p e = lt-ne y n p e

lookup-∘ : ∀ τ σ y → T (y <ℕ lenₛ τ) → lookupₛ (τ ∘ σ) y ≡ (lookupₛ τ y) [ σ ]tm
lookup-∘ ⟨⟩       σ y ()
lookup-∘ (τ ,ₛ t) σ y p rewrite lenₛ-∘ τ σ with y ==ℕ lenₛ τ in eq
... | true  = refl
... | false = lookup-∘ τ σ y (lt-ne y (lenₛ τ) p eq)

------------------------------------------------------------------------
-- The theorem.

module _ (Δ' : Ctx) (σ : Sub) (m : Nat) where

  Ĵ : Nat → Maybe LT
  Ĵ y = nf m Δ' (lookupₛ σ y)

  Iτ : Nat → Ctx → Sub → Nat → Maybe LT
  Iτ n Δ τ y = nf n Δ (lookupₛ τ y)

  Hyp : Nat → Ctx → Tm → Set
  Hyp zero    Δ t           = ⊤
  Hyp (suc n) Δ (var x)     = Σ LT λ b → Ĵ x ≡ just b
  Hyp (suc n) Δ (coh Θ A τ) =
    ∀ tr → treeOf Θ ≡ just tr →
      Lab (λ y → T (y <ℕ lenₛ τ)) (idTree tr)
    × Good (Iτ n Δ τ) 0 Top (idTree tr)
    × (∀ y b → Iτ n Δ τ y ≡ just b → Good Ĵ 0 Top b)
    × (∀ y → T (y <ℕ lenₛ τ) → Hyp n Δ (lookupₛ τ y))
  Hyp (suc n) Δ (cst k)     = ⊤

  nf-sub : ∀ n Δ t a → Hyp n Δ t → nf n Δ t ≡ just a →
           nf (n + m) Δ' (t [ σ ]tm) ≡ flatG Ĵ 0 a
  nf-sub zero    Δ t a h ()
  nf-sub (suc n) Δ (var x) a (b , eb) e
    with bind-inv (lookup Δ x) _ e
  ... | A , _ , ew =
    trans (nf-+ (suc n) m Δ' (lookupₛ σ x) b eb)
          (sym (trans (wrap-flat Ĵ A (lt (x ∷ []) []) a 0 ew) eb))
  nf-sub (suc n) Δ (coh Θ A τ) a h e
    with bind-inv (treeOf Θ) _ e
  ... | tr , etr , ef
    with h tr etr
  ... | labs , good , hi , hsub rewrite etr =
    trans (flat-is-flatG (n + m) Δ' (τ ∘ σ) 0 (idTree tr))
          (trans (flatG-cong _ (I∘J I Ĵ hi) 0 (idTree tr)
                   (lab-zip step (idTree tr) labs (good-lab I 0 Top (idTree tr) good)))
                 (flat-assoc I Ĵ hi 0 Top (idTree tr) a good ef'))
    where
    I : Nat → Maybe LT
    I = Iτ n Δ τ

    ef' : flatG I 0 (idTree tr) ≡ just a
    ef' = trans (sym (flat-is-flatG n Δ τ 0 (idTree tr))) ef

    step : ∀ y → T (y <ℕ lenₛ τ) → (Σ LT λ b → I y ≡ just b) →
           nf (n + m) Δ' (lookupₛ (τ ∘ σ) y) ≡ I∘J I Ĵ hi y
    step y p (b , eb) rewrite lookup-∘ τ σ y p | eb =
      nf-sub n Δ (lookupₛ τ y) b (hsub y p) eb
  nf-sub (suc n) Δ (cst ()) a h e
