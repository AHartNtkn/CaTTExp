------------------------------------------------------------------------
-- Toward the k = 0 whisker heads of two-tier L (step 2(d) of the
-- two-tier L whiskering interface, notes/surface-conservativity.md §7).
--
-- Part 1: whiskering a single-hom context by a 1-cell. For a pasting
-- context Θ, let
--
--   W Θ = ΣΘ ▸ z : ⋆ ▸ h : a₁ → z
--
-- (BK 0 (j+1) is W (Dsk (j+1)) up to Σ(Dsk (j+1)) = Dsk (j+2)). Then
-- K(W Θ) = λΘ ⊗ λ{h}, h a 0-cell of its hom, and
--
--   homsW     : homs (W Θ) = hΣ Θ , (h)
--   bdryW     : bdryT sg (homs (W Θ)) = map (_++ (h)) (bdryT sg (homs ΣΘ))
--   sameDownW : sameDown ΣΘ S R → sameDown (W Θ) (S ++ (h)) (R ++ (h))
--
-- so the side condition on W Θ is carried over from ΣΘ along x ↦ x ++ (h).
-- Also: side-BK0 0 holds by evaluation.
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerZero where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Cover using (Any; here; there; any-++⁻; any-++l; any-++r; any-witness; any-at;
                                      any-map⁻; any-map⁺; _⊎_; inj₁; inj₂; T-All; All-T; ∧-in; ∨-inl; ∨-inr;
                                      _≤_; z≤n; s≤s)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; anyS⇒; anyS⇐; map≡)
open import CaTTExp.Gray.DownAgree ∅ using () renaming (module Faces to DF)
open import CaTTExp.Gray.Graded ∅ using (homOf; elsOf; mkEl≡)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; S; lenΣ; dimΣ)
open import CaTTExp.Gray.SingleHom ∅ using (fΣ; mkC; entriesΣ; objsΣ; cellsΣ; homsΣ; hΣ; endsTyΣ)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.Derived using (zK; BK)

------------------------------------------------------------------------
-- side-BK0 0: composition of two 1-cells, by evaluation.

gside-BK00 : T (graySide (BK 0 0) (aL 0) (var 0) (var (zK 0 0)))
gside-BK00 = tt

------------------------------------------------------------------------
-- List generalities.

private
  ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  map-++ : ∀ {A B : Set} (g : A → B) xs ys → map g (xs ++ ys) ≡ map g xs ++ map g ys
  map-++ g []       ys = refl
  map-++ g (x ∷ xs) ys = cong (g x ∷_) (map-++ g xs ys)

  filter-++ : ∀ {A : Set} (p : A → Bool) xs ys → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
  filter-++ p []       ys = refl
  filter-++ p (x ∷ xs) ys with p x
  ... | true  = cong (x ∷_) (filter-++ p xs ys)
  ... | false = filter-++ p xs ys

  cm-++ : ∀ {A B : Set} (g : A → List B) xs ys → concatMap g (xs ++ ys) ≡ concatMap g xs ++ concatMap g ys
  cm-++ g []       ys = refl
  cm-++ g (x ∷ xs) ys = trans (cong (g x ++_) (cm-++ g xs ys)) (sym (++-assoc (g x) (concatMap g xs) (concatMap g ys)))

  cm-cong : ∀ {A B : Set} {g g′ : A → List B} → (∀ x → g x ≡ g′ x) → ∀ xs → concatMap g xs ≡ concatMap g′ xs
  cm-cong e []       = refl
  cm-cong e (x ∷ xs) = cong₂ _++_ (e x) (cm-cong e xs)

  cm-map : ∀ {A B C : Set} (m : B → C) (g : A → List B) xs →
           concatMap (λ x → map m (g x)) xs ≡ map m (concatMap g xs)
  cm-map m g []       = refl
  cm-map m g (x ∷ xs) = trans (cong (map m (g x) ++_) (cm-map m g xs)) (sym (map-++ m (g x) (concatMap g xs)))

  cm-nil : ∀ {A B : Set} (g : A → List B) → (∀ x → g x ≡ []) → ∀ xs → concatMap g xs ≡ []
  cm-nil g e []       = refl
  cm-nil g e (x ∷ xs) rewrite e x = cm-nil g e xs

  ==ℕ-≡ : ∀ n → (n ==ℕ n) ≡ true
  ==ℕ-≡ zero    = refl
  ==ℕ-≡ (suc n) = ==ℕ-≡ n

------------------------------------------------------------------------
-- The whiskered context.

hT : Nat → Ty
hT L = arr ⋆ (var 1) (var L)

W : Ctx → Ctx
W Θ = Σctx Θ ▸ ⋆ ▸ hT (len (Σctx Θ))

-- The level of h, its cell, and its hom.
hl : Ctx → Nat
hl Θ = suc (len (Σctx Θ))

hc : Ctx → El
hc Θ = el (hl Θ) 2 0 0 0

hB : Ctx → Hom
hB Θ = mkHom 0 (hc Θ ∷ [])

app : Ctx → Tuple → Tuple
app Θ x = x ++ (hl Θ ∷ [])

private
  isStarΣ : ∀ A → isStar (Σty A) ≡ false
  isStarΣ ⋆           = refl
  isStarΣ (arr A t u) = refl

  filter-starΣ : ∀ es → filter (λ e → isStar (snd e)) (map fΣ es) ≡ []
  filter-starΣ []            = refl
  filter-starΣ ((v , A) ∷ es) rewrite isStarΣ A = filter-starΣ es

  mkEl-fΣ : ∀ os e → mkEl (0 ∷ 1 ∷ os) (fΣ e) ≡ mkC e ∷ []
  mkEl-fΣ os (v , A) = trans (mkEl≡ (0 ∷ 1 ∷ os) (S v) (Σty A)) (go A)
    where
    go : ∀ A → elsOf (0 ∷ 1 ∷ os) (S v) (Σty A) (homOf (0 ∷ 1 ∷ os) (Σty A)) ≡ mkC (v , A) ∷ []
    go A rewrite endsTyΣ A | dimΣ A = refl

  cm-mk : ∀ os es → concatMap (mkEl (0 ∷ 1 ∷ os)) (map fΣ es) ≡ map mkC es
  cm-mk os []       = refl
  cm-mk os (e ∷ es) rewrite mkEl-fΣ os e = cong (mkC e ∷_) (cm-mk os es)

  posOf-S : ∀ n → posOf (S n) (0 ∷ 1 ∷ S n ∷ []) ≡ just 2
  posOf-S n rewrite ==ℕ-≡ n = refl

  filter-mkC1 : ∀ es → filter (λ c → hom c ==ℕ 1) (map mkC es) ≡ map mkC es
  filter-mkC1 []       = refl
  filter-mkC1 (e ∷ es) = cong (mkC e ∷_) (filter-mkC1 es)

  filter-mkC2 : ∀ es → filter (λ c → hom c ==ℕ 2) (map mkC es) ≡ []
  filter-mkC2 []       = refl
  filter-mkC2 (e ∷ es) = filter-mkC2 es

module _ (Θ : Ctx) where

  private
    L  = len (Σctx Θ)
    es = entries Θ

  entriesW : entries (W Θ) ≡ (0 , ⋆) ∷ (1 , ⋆) ∷ (map fΣ es ++ ((L , ⋆) ∷ (suc L , hT L) ∷ []))
  entriesW =
    trans (++-assoc (entries (Σctx Θ)) ((L , ⋆) ∷ []) ((suc L , hT L) ∷ []))
          (cong (λ X → X ++ ((L , ⋆) ∷ (suc L , hT L) ∷ [])) (entriesΣ Θ))

  objsW : objs (W Θ) ≡ 0 ∷ 1 ∷ L ∷ []
  objsW =
    trans (cong (λ E → map fst (filter (λ e → isStar (snd e)) E)) entriesW)
          (cong (λ X → 0 ∷ 1 ∷ map fst X)
                (trans (filter-++ (λ e → isStar (snd e)) (map fΣ es) ((L , ⋆) ∷ (suc L , hT L) ∷ []))
                       (cong (_++ ((L , ⋆) ∷ [])) (filter-starΣ es))))

  private
    posL : posOf L (0 ∷ 1 ∷ L ∷ []) ≡ just 2
    posL = subst (λ n → posOf n (0 ∷ 1 ∷ n ∷ []) ≡ just 2) (sym (lenΣ Θ)) (posOf-S (len Θ))

    mkEl-h : mkEl (0 ∷ 1 ∷ L ∷ []) (suc L , hT L) ≡ hc Θ ∷ []
    mkEl-h = trans (mkEl≡ (0 ∷ 1 ∷ L ∷ []) (suc L) (hT L))
                   (cong (elsOf (0 ∷ 1 ∷ L ∷ []) (suc L) (hT L)) posL)

  cellsW : cells (W Θ) ≡ map mkC es ++ (hc Θ ∷ [])
  cellsW =
    trans (cong₂ (λ os E → concatMap (mkEl os) E) objsW entriesW)
      (trans (cm-++ (mkEl (0 ∷ 1 ∷ L ∷ [])) (map fΣ es) ((L , ⋆) ∷ (suc L , hT L) ∷ []))
             (cong₂ _++_ (cm-mk (L ∷ []) es) (cong (_++ []) mkEl-h)))

  private
    hm : List El → Hom
    hm cs = mkHom (maxL (map hdim cs)) cs

  homsW : homs (W Θ) ≡ hΣ Θ ∷ hB Θ ∷ []
  homsW =
    trans (cong (λ os → map (homAt (W Θ)) (drop1 (upto (lengthN os)))) objsW)
          (cong₂ (λ a b → a ∷ b ∷ []) h1 h2)
    where
    h1 : homAt (W Θ) 1 ≡ hΣ Θ
    h1 = trans (cong (λ cs → hm (filter (λ c → hom c ==ℕ 1) cs)) cellsW)
           (trans (cong hm (trans (filter-++ (λ c → hom c ==ℕ 1) (map mkC es) (hc Θ ∷ []))
                                  (trans (cong (_++ []) (filter-mkC1 es)) (++-[] (map mkC es)))))
             (sym (trans (cong (λ cs → hm (filter (λ c → hom c ==ℕ 1) cs)) (cellsΣ Θ))
                         (cong hm (filter-mkC1 es)))))
      where
      ++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
      ++-[] []       = refl
      ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)
    h2 : homAt (W Θ) 2 ≡ hB Θ
    h2 = trans (cong (λ cs → hm (filter (λ c → hom c ==ℕ 2) cs)) cellsW)
               (cong hm (trans (filter-++ (λ c → hom c ==ℕ 2) (map mkC es) (hc Θ ∷ []))
                               (cong (_++ (hc Θ ∷ [])) (filter-mkC2 es))))

------------------------------------------------------------------------
-- The tables of hΣ Θ ⊗ (h) are those of hΣ Θ, with h appended.

private
  prod1-app : ∀ ws C y → prod1 ws (map (_++ y) C) ≡ map (_++ y) (prod1 ws C)
  prod1-app ws C y = trans (cm-cong (λ x → mm x C) ws) (cm-map (_++ y) (λ x → map (x ∷_) C) ws)
    where
    mm : ∀ x C → map (x ∷_) (map (_++ y) C) ≡ map (_++ y) (map (x ∷_) C)
    mm x []      = refl
    mm x (c ∷ C) = cong ((x ∷ (c ++ y)) ∷_) (mm x C)

module _ (Θ : Ctx) where

  private
    flipS : Bool → Nat → Bool
    flipS s i = if odd i then not s else s

  chainB : ∀ s s′ m → chainT s m (hB Θ ∷ []) ≡ map (app Θ) (chainT s′ m [])
  chainB s s′ zero    = refl
  chainB s s′ (suc m) = cm-nil _ none (filter (λ i → i <ℕ suc (suc m)) (upto (suc m)))
    where
    none : ∀ i → prod1 (piece (hB Θ) i s) (chainT (flipS s i) (suc m ∸ i) []) ≡ []
    none zero    = refl
    none (suc i) = refl

  chainAB : ∀ hA s k → chainT s k (hA ∷ hB Θ ∷ []) ≡ map (app Θ) (chainT s k (hA ∷ []))
  chainAB hA s k =
    trans (cm-cong (λ i → trans (cong (prod1 (piece hA i s)) (chainB (flipS s i) (flipS s i) (k ∸ i)))
                                 (prod1-app (piece hA i s) (chainT (flipS s i) (k ∸ i) []) (hl Θ ∷ [])))
                   (filter (λ i → i <ℕ suc k) (upto k)))
          (cm-map (app Θ) (λ i → prod1 (piece hA i s) (chainT (flipS s i) (k ∸ i) []))
                  (filter (λ i → i <ℕ suc k) (upto k)))

  lowerAB : ∀ hA m → lowerT m (hA ∷ hB Θ ∷ []) ≡ map (app Θ) (lowerT m (hA ∷ []))
  lowerAB hA zero    = refl
  lowerAB hA (suc m) rewrite lowerAB hA m | chainAB hA false m | chainAB hA true m =
    sym (trans (map-++ (app Θ) (lowerT m (hA ∷ [])) (chainT false m (hA ∷ []) ++ chainT true m (hA ∷ [])))
               (cong (map (app Θ) (lowerT m (hA ∷ [])) ++_)
                     (map-++ (app Θ) (chainT false m (hA ∷ [])) (chainT true m (hA ∷ [])))))

  bdryW : ∀ sg → bdryT sg (homs (W Θ)) ≡ map (app Θ) (bdryT sg (homs (Σctx Θ)))
  bdryW sg rewrite homsW Θ | homsΣ Θ =
    trans (cong₂ _++_ (lowerAB (hΣ Θ) (hd (hΣ Θ) + 0 ∸ 1)) (chainAB (hΣ Θ) sg (hd (hΣ Θ) + 0 ∸ 1)))
          (sym (map-++ (app Θ) (lowerT (hd (hΣ Θ) + 0 ∸ 1) (hΣ Θ ∷ [])) (chainT sg (hd (hΣ Θ) + 0 ∸ 1) (hΣ Θ ∷ []))))

  topW : topT (homs (W Θ)) ≡ map (app Θ) (topT (homs (Σctx Θ)))
  topW rewrite homsW Θ | homsΣ Θ = chainAB (hΣ Θ) true (hd (hΣ Θ) + 0)

  dimKW : dimK (homs (W Θ)) ≡ dimK (homs (Σctx Θ))
  dimKW rewrite homsW Θ | homsΣ Θ = refl

------------------------------------------------------------------------
-- The face order is monotone in the list of cells.

private
  findEl-++ : ∀ w cs xs {c} → findEl w cs ≡ just c → findEl w (cs ++ xs) ≡ just c
  findEl-++ w (c′ ∷ cs) xs e with lvl c′ ==ℕ w
  ... | true  = e
  ... | false = findEl-++ w cs xs e

  bd-mono : ∀ cs xs w {b} → b ∈ᴺ bdEl cs w → b ∈ᴺ bdEl (cs ++ xs) w
  bd-mono cs xs w m with findEl w cs in e
  ... | just c rewrite findEl-++ w cs xs e = m

  lr-mono : ∀ cs xs {k b a} → DF.LR cs k b a → DF.LR (cs ++ xs) k b a
  lr-mono cs xs DF.lz          = DF.lz
  lr-mono cs xs (DF.ls {b = b} mc lr) = DF.ls (bd-mono cs xs b mc) (lr-mono cs xs lr)

  leqL-mono : ∀ cs xs n a b → T (leqL cs n a b) → T (leqL (cs ++ xs) n a b)
  leqL-mono cs xs n a b p with DF.leqL⇒ cs n a b p
  ... | k , l , lr = DF.leqL⇐ (cs ++ xs) n l (lr-mono cs xs lr)

  leqT-app : ∀ cs xs n y x r → T (leqT cs n x r) → T (leqT (cs ++ xs) n (x ++ y) (r ++ y))
  leqT-app cs xs n y []      []      _ = DF.leqT⇐ (cs ++ xs) (DF.pw-refl (cs ++ xs) n y)
  leqT-app cs xs n y (a ∷ x) (b ∷ r) p =
    ∧-in (leqL-mono cs xs n a b (∧-fst {leqL cs n a b} p)) (leqT-app cs xs n y x r (∧-snd {leqL cs n a b} p))
  leqT-app cs xs n y []      (_ ∷ _) ()
  leqT-app cs xs n y (_ ∷ _) []      ()

  covAll : List El → Nat → TSet → TSet → Bool
  covAll cs n S R = all (λ s → any (leqT cs n s) R) S

  cov-app : ∀ cs xs n y S R → T (covAll cs n S R) → T (covAll (cs ++ xs) n (map (_++ y) S) (map (_++ y) R))
  cov-app cs xs n y S R p =
    T-All (λ s → any (leqT (cs ++ xs) n s) (map (_++ y) R)) (map (_++ y) S) λ {s′} ms′ →
      go (any-witness (any-map⁻ (_++ y) S (subst (Any (s′ ≡_)) (map≡ (_++ y) S) ms′)))
    where
    go : ∀ {s′} → (Σ Tuple λ s → Any (s ≡_) S × (s′ ≡ s ++ y)) → T (any (leqT (cs ++ xs) n s′) (map (_++ y) R))
    go (s , ms , refl) with any-witness (anyS⇒ (leqT cs n s) R (All-T (λ s → any (leqT cs n s) R) S p ms))
    ... | r , mr , q =
      anyS⇐ (leqT (cs ++ xs) n (s ++ y)) (map (_++ y) R)
        (any-at (subst (Any ((r ++ y) ≡_)) (sym (map≡ (_++ y) R)) (any-map⁺ (_++ y) (any-at mr refl)))
                (leqT-app cs xs n y s r q))

------------------------------------------------------------------------
-- The transfer.

module _ (Θ : Ctx) where

  private
    N = dimK (homs (Σctx Θ))

  coversW : ∀ S R → T (covers (Σctx Θ) S R) → T (covers (W Θ) (map (app Θ) S) (map (app Θ) R))
  coversW S R p =
    subst (λ n → T (covAll (cells (W Θ)) n (map (app Θ) S) (map (app Θ) R))) (sym (dimKW Θ))
      (subst (λ cs → T (covAll cs N (map (app Θ) S) (map (app Θ) R))) (sym (cellsW Θ))
        (cov-app (map mkC (entries Θ)) (hc Θ ∷ []) N (hl Θ ∷ []) S R
          (subst (λ cs → T (covAll cs N S R)) (cellsΣ Θ) p)))

  sameDownW : ∀ S R → T (sameDown (Σctx Θ) S R) → T (sameDown (W Θ) (map (app Θ) S) (map (app Θ) R))
  sameDownW S R p =
    ∧-in (coversW S R (∧-fst {covers (Σctx Θ) S R} p)) (coversW R S (∧-snd {covers (Σctx Θ) S R} p))
