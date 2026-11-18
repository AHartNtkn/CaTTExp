------------------------------------------------------------------------
-- F2c, lemma 1a (flat half): the composite of a labelled pasting
-- diagram commutes with boundaries.
--
-- CaTTExp.GlobularFiller.flat reads a labelled tree T of a pasting
-- context Θ at depth d, replaces each locally maximal variable y by an
-- image I y, and composes. `flatG` is that function with the image
-- abstracted (`flat-is-flatG` says it is the same function). If the
-- images are compatible (`Good`: the image of a cell of dimension e+1
-- between o and o' is a well-formed tree of dimension e+1 whose
-- e-boundaries are the images of o and o'), then
--
--   flat-bd : flatG d T ≡ just a  ⟹
--             WF a  and  flatG d (bd β i T) ≡ just (bd β (d + i) a)
--
-- i.e. the i-boundary of the diagram composes to the (d+i)-boundary
-- of the composite. `flat-ends` gives the d-boundaries of a branch.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FlatBd where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; merge; bd; bdL; nf; flat; flatL; module Lists)
open Lists using (headN; lastN)
open import CaTTExp.GlobularTotal.TreeAlg

------------------------------------------------------------------------
-- Small facts.

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

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

  <-suc+ : ∀ d i → T (d <ℕ suc (d + i))
  <-suc+ zero    i = tt
  <-suc+ (suc d) i = <-suc+ d i

  <-suc : ∀ d → T (d <ℕ suc d)
  <-suc zero    = tt
  <-suc (suc d) = <-suc d

------------------------------------------------------------------------
-- Lower boundaries of a boundary.

mutual
  bd-bd : ∀ β β' j k a → T (j <ℕ k) → bd β j (bd β' k a) ≡ bd β j a
  bd-bd false false zero    (suc k) (lt os cs) _ = refl
  bd-bd false true  zero    (suc k) (lt os cs) _ = refl
  bd-bd true  false zero    (suc k) (lt os cs) _ = refl
  bd-bd true  true  zero    (suc k) (lt os cs) _ = refl
  bd-bd false false (suc j) (suc k) (lt os cs) p = cong (lt os) (bdL-bdL false false j k cs p)
  bd-bd false true  (suc j) (suc k) (lt os cs) p = cong (lt os) (bdL-bdL false true  j k cs p)
  bd-bd true  false (suc j) (suc k) (lt os cs) p = cong (lt os) (bdL-bdL true  false j k cs p)
  bd-bd true  true  (suc j) (suc k) (lt os cs) p = cong (lt os) (bdL-bdL true  true  j k cs p)

  bdL-bdL : ∀ β β' j k cs → T (j <ℕ k) → bdL β j (bdL β' k cs) ≡ bdL β j cs
  bdL-bdL β β' j k []       p = refl
  bdL-bdL β β' j k (c ∷ cs) p = cong₂ _∷_ (bd-bd β β' j k c p) (bdL-bdL β β' j k cs p)

-- A one-label leaf is its own boundary.
private
  bd-leaf : ∀ β i y → bd β i (lt (y ∷ []) []) ≡ lt (y ∷ []) []
  bd-leaf false zero    y = refl
  bd-leaf true  zero    y = refl
  bd-leaf false (suc i) y = refl
  bd-leaf true  (suc i) y = refl

------------------------------------------------------------------------
-- The composite, with the image of the variables abstracted.

module _ (I : Nat → Maybe LT) where

  mutual
    flatG : Nat → LT → Maybe LT
    flatG d (lt _ (c ∷ cs))   = flatGL d c cs
    flatG d (lt (y ∷ []) [])  = I y
    flatG d (lt _ [])         = nothing

    flatGL : Nat → LT → List LT → Maybe LT
    flatGL d c []        = flatG (suc d) c
    flatGL d c (c' ∷ cs) =
      flatG (suc d) c >>= λ a →
      flatGL d c' cs  >>= λ b →
      just (merge d a b)

  -- a has dimension at most d.
  Dim : Nat → LT → Set
  Dim d a = ∀ β i → bd β (d + i) a ≡ a

  -- The image of an object o at depth d, constrained by P.
  Ok : Nat → (LT → Set) → Nat → Set
  Ok d P o = Σ LT λ x → (I o ≡ just x) × WF x × Dim d x × P x

  -- The constraint on the objects of a branch at depth d+1 lying
  -- between objects o and o' at depth d.
  Par : Nat → Nat → Nat → LT → Set
  Par d o o' x = (I o ≡ just (bd false d x)) × (I o' ≡ just (bd true d x))

  AllL : (Nat → Set) → List Nat → Set
  AllL P []       = ⊤
  AllL P (x ∷ xs) = P x × AllL P xs

  mutual
    Good : Nat → (LT → Set) → LT → Set
    Good d P (lt os cs) = AllL (Ok d P) os × GoodCs d os cs

    GoodCs : Nat → List Nat → List LT → Set
    GoodCs d (o ∷ [])      []       = ⊤
    GoodCs d (o ∷ o' ∷ os) (c ∷ cs) = Good (suc d) (Par d o o') c × GoodCs d (o' ∷ os) cs
    GoodCs d _             _        = ⊥

  private
    all-last : ∀ {P} o os → AllL P (o ∷ os) → P (lastN (o ∷ os))
    all-last o []        (p , _)  = p
    all-last o (o' ∷ os) (_ , rest) = all-last o' os rest

  ----------------------------------------------------------------------
  -- The theorem.

  mutual
    flat-bd : ∀ d P T a → Good d P T → flatG d T ≡ just a →
              WF a × (∀ β i → flatG d (bd β i T) ≡ just (bd β (d + i) a))
    -- a leaf: a locally maximal variable
    flat-bd d P (lt (y ∷ []) []) a ((ok , _) , _) e with ok
    ... | x , ex , wx , dx , _ with trans (sym ex) e
    ...   | refl = wx , λ β i →
                     trans (cong (flatG d) (bd-leaf β i y))
                           (trans ex (cong just (sym (dx β i))))
    flat-bd d P (lt [] [])               a (_ , ()) e
    flat-bd d P (lt (y ∷ y' ∷ ys) [])    a (_ , ()) e
    -- a node: compose the branches along dimension d
    flat-bd d P (lt [] (c ∷ cs))         a (_ , ()) e
    flat-bd d P (lt (o ∷ os) (c ∷ cs))   a (oks , g) e
      with flatL-bd d o os c cs a g e
    ... | wa , com , eo , el = wa , go
      where
      go : ∀ β i → flatG d (bd β i (lt (o ∷ os) (c ∷ cs))) ≡ just (bd β (d + i) a)
      go false zero    = trans eo (cong (λ n → just (bd false n a)) (sym (+-zero d)))
      go true  zero    = trans el (cong (λ n → just (bd true  n a)) (sym (+-zero d)))
      go false (suc i) = com false i
      go true  (suc i) = com true  i

    flatL-bd : ∀ d o os c cs a → GoodCs d (o ∷ os) (c ∷ cs) → flatGL d c cs ≡ just a →
               WF a
             × (∀ β i → flatGL d (bd β i c) (bdL β i cs) ≡ just (bd β (d + suc i) a))
             × (I o ≡ just (bd false d a))
             × (I (lastN (o ∷ os)) ≡ just (bd true d a))
    flatL-bd d o []               c cs        a () e
    flatL-bd d o (o' ∷ [])        c []        a (gc , _) e
      with flat-bd (suc d) (Par d o o') c a gc e | flat-ends d o o' c a gc e
    ... | wa , com | eo , eo' =
      wa , (λ β i → trans (com β i) (cong (λ n → just (bd β n a)) (sym (+-suc d i)))) , eo , eo'
    flatL-bd d o (o' ∷ o'' ∷ os)  c []        a (_ , ()) e
    flatL-bd d o (o' ∷ [])        c (c' ∷ cs) a (_ , ()) e
    flatL-bd d o (o' ∷ o'' ∷ os)  c (c' ∷ cs) a (gc , gs) e
      with bind-inv (flatG (suc d) c) _ e
    ... | a₁ , e₁ , e'
      with bind-inv (flatGL d c' cs) _ e'
    ... | b , e₂ , refl
      with flat-bd (suc d) (Par d o o') c a₁ gc e₁ | flat-ends d o o' c a₁ gc e₁
         | flatL-bd d o' (o'' ∷ os) c' cs b gs e₂
    ... | w₁ , com₁ | eo , eo' | wb , comb , ebo , ebl =
      wf-merge d a₁ b w₁ wb cp , com , src , tgt
      where
      cp : Compat d a₁ b
      cp = just-inj (trans (sym eo') ebo)

      src : I o ≡ just (bd false d (merge d a₁ b))
      src = trans eo (cong just (sym (bd-merge-src d a₁ b w₁ cp)))

      tgt : I (lastN (o'' ∷ os)) ≡ just (bd true d (merge d a₁ b))
      tgt = trans ebl (cong just (sym (bd-merge-tgt d a₁ b w₁ wb cp)))

      com : ∀ β i → flatGL d (bd β i c) (bdL β i (c' ∷ cs)) ≡ just (bd β (d + suc i) (merge d a₁ b))
      com β i
        rewrite com₁ β i | comb β i | +-suc d i
              = cong just (sym (bd-merge-high β (suc (d + i)) d a₁ b (<-suc+ d i)))

    -- The d-boundaries of a branch at depth d+1 between o and o'.
    flat-ends : ∀ d o o' c a → Good (suc d) (Par d o o') c → flatG (suc d) c ≡ just a →
                Par d o o' a
    flat-ends d o o' (lt [] cs)        a (_ , g) e = ⊥-elim (no-objs cs g)
      where
      no-objs : ∀ cs → GoodCs (suc d) [] cs → ⊥
      no-objs []       ()
      no-objs (_ ∷ _)  ()
    flat-ends d o o' (lt (h ∷ hs) cs)  a (oks@(okh , _) , g) e
      with flat-bd (suc d) (Par d o o') (lt (h ∷ hs) cs) a (oks , g) e
    ... | _ , com with okh | all-last h hs oks
    ... | x , ex , _ , _ , px₀ , _ | y , ey , _ , _ , _ , py₁ =
      trans px₀ (cong just (trans (cong (bd false d) xa) (bd-bd false false d (suc d + 0) a (<-suc+ d 0)))) ,
      trans py₁ (cong just (trans (cong (bd true d) ya) (bd-bd true true d (suc d + 0) a (<-suc+ d 0))))
      where
      xa : x ≡ bd false (suc d + 0) a
      xa = just-inj (trans (sym ex) (head-bd cs (com false 0)))
        where
        head-bd : ∀ cs → flatG (suc d) (bd false 0 (lt (h ∷ hs) cs)) ≡ just (bd false (suc d + 0) a) →
                  I h ≡ just (bd false (suc d + 0) a)
        head-bd _ p = p

      ya : y ≡ bd true (suc d + 0) a
      ya = just-inj (trans (sym ey) (com true 0))

------------------------------------------------------------------------
-- GlobularFiller.flat is flatG with I y = nf n Γ (σ y).

mutual
  flat-is-flatG : ∀ n Γ σ d T →
                  flat n Γ σ d T ≡ flatG (λ y → nf n Γ (lookupₛ σ y)) d T
  flat-is-flatG n Γ σ d (lt []            [])       = refl
  flat-is-flatG n Γ σ d (lt (y ∷ [])      [])       = refl
  flat-is-flatG n Γ σ d (lt (y ∷ y' ∷ ys) [])       = refl
  flat-is-flatG n Γ σ d (lt []            (c ∷ cs)) = flatL-is-flatGL n Γ σ d c cs
  flat-is-flatG n Γ σ d (lt (y ∷ [])      (c ∷ cs)) = flatL-is-flatGL n Γ σ d c cs
  flat-is-flatG n Γ σ d (lt (y ∷ y' ∷ ys) (c ∷ cs)) = flatL-is-flatGL n Γ σ d c cs

  flatL-is-flatGL : ∀ n Γ σ d c cs →
                    flatL n Γ σ d c cs ≡ flatGL (λ y → nf n Γ (lookupₛ σ y)) d c cs
  flatL-is-flatGL n Γ σ d c []        = flat-is-flatG n Γ σ (suc d) c
  flatL-is-flatGL n Γ σ d c (c' ∷ cs)
    rewrite flat-is-flatG n Γ σ (suc d) c | flatL-is-flatGL n Γ σ d c' cs = refl
