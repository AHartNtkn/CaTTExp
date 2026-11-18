------------------------------------------------------------------------
-- F2c, toward step (P3): `split` on a position tree.
--
-- Let E be a tree of the shape of a composite a ∗ₖ b (a, b well formed
-- and k-composable) and (Ea , Eb) = split k a E. Then
--
--   merge-split  : merge k Ea Eb ≡ E
--   compat-split : Compat k Ea Eb
--   relab-split  : split k a (relab f E) ≡ (relab f Ea , relab f Eb)
--   ex-split     : E a diagram of Θ ⟹ so are Ea and Eb
--   wf-split     : E well formed ⟹ so are Ea and Eb
--
-- So splitting a position along the image of a factor gives the
-- positions of the two factors, whose relabellings are the factors
-- when E's relabelling is the composite (with SplitMerge).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.SplitProps where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; merge; mergeL; bd; bdL; split; splitL; shape; shapes; module Lists)
open Lists using (headN; lastN; take; drop; length)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat) renaming (len to lenL)
open import CaTTExp.GlobularTotal.Uniq using (Ex; ExCs; Cell; AllN)
open import CaTTExp.GlobularTotal.Relabel using (relab; relabs; mapN)

private
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  node-inj : ∀ {ts ts'} → node ts ≡ node ts' → ts ≡ ts'
  node-inj refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  _≤_ : Nat → Nat → Set
  a ≤ b = T (a <ℕ suc b)

  len-length : ∀ {A : Set} (xs : List A) → lenL xs ≡ length xs
  len-length []       = refl
  len-length (x ∷ xs) = cong suc (len-length xs)

  length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  le-+ : ∀ a b → a ≤ (a + b)
  le-+ zero    b = tt
  le-+ (suc a) b = le-+ a b

  shapes-++ : ∀ xs ys → shapes (xs ++ ys) ≡ shapes xs ++ shapes ys
  shapes-++ []       ys = refl
  shapes-++ (x ∷ xs) ys = cong (shape x ∷_) (shapes-++ xs ys)

  len-shapes : ∀ cs cs' → shapes cs ≡ shapes cs' → length cs ≡ length cs'
  len-shapes []       []        e = refl
  len-shapes []       (c' ∷ cs') ()
  len-shapes (c ∷ cs) []        ()
  len-shapes (c ∷ cs) (c' ∷ cs') e = cong suc (len-shapes cs cs' (∷-injₜ e))

  length-shapes : ∀ cs → length (shapes cs) ≡ length cs
  length-shapes []       = refl
  length-shapes (c ∷ cs) = cong suc (length-shapes cs)

  take-drop : ∀ {A : Set} n (xs : List A) → take n xs ++ drop n xs ≡ xs
  take-drop zero    xs       = refl
  take-drop (suc n) []       = refl
  take-drop (suc n) (x ∷ xs) = cong (x ∷_) (take-drop n xs)

  drop-suc : ∀ {A : Set} m (xs : List A) → drop 1 (drop m xs) ≡ drop (suc m) xs
  drop-suc zero    []       = refl
  drop-suc zero    (x ∷ xs) = refl
  drop-suc (suc m) []       = refl
  drop-suc (suc m) (x ∷ xs) = drop-suc m xs

  take-suc-++ : ∀ {A : Set} m (xs : List A) → take (suc m) xs ++ drop 1 (drop m xs) ≡ xs
  take-suc-++ m xs rewrite drop-suc m xs = take-drop (suc m) xs

  last-head : ∀ m (xs : List Nat) → suc m ≤ length xs → lastN (take (suc m) xs) ≡ headN (drop m xs)
  last-head zero    (x ∷ xs)      p = refl
  last-head (suc m) (x ∷ [])      ()
  last-head (suc m) (x ∷ y ∷ xs)  p = last-head m (y ∷ xs) p

  map-take : ∀ f n xs → mapN f (take n xs) ≡ take n (mapN f xs)
  map-take f zero    xs       = refl
  map-take f (suc n) []       = refl
  map-take f (suc n) (x ∷ xs) = cong (f x ∷_) (map-take f n xs)

  map-drop : ∀ f n xs → mapN f (drop n xs) ≡ drop n (mapN f xs)
  map-drop f zero    xs       = refl
  map-drop f (suc n) []       = refl
  map-drop f (suc n) (x ∷ xs) = map-drop f n xs

  rels-take : ∀ f n cs → relabs f (take n cs) ≡ take n (relabs f cs)
  rels-take f zero    cs       = refl
  rels-take f (suc n) []       = refl
  rels-take f (suc n) (c ∷ cs) = cong (relab f c ∷_) (rels-take f n cs)

  rels-drop : ∀ f n cs → relabs f (drop n cs) ≡ drop n (relabs f cs)
  rels-drop f zero    cs       = refl
  rels-drop f (suc n) []       = refl
  rels-drop f (suc n) (c ∷ cs) = rels-drop f n cs

  len-take : ∀ {A : Set} n (xs : List A) → n ≤ length xs → length (take n xs) ≡ n
  len-take zero    xs       p = refl
  len-take (suc n) []       ()
  len-take (suc n) (x ∷ xs) p = cong suc (len-take n xs p)

  len-drop : ∀ {A : Set} n (xs : List A) → n ≤ length xs → length xs ≡ n + length (drop n xs)
  len-drop zero    xs       p = refl
  len-drop (suc n) []       ()
  len-drop (suc n) (x ∷ xs) p = cong suc (len-drop n xs p)

------------------------------------------------------------------------
-- The hypotheses: E has the shape of a ∗ₖ b.

Fits : Nat → LT → LT → LT → Set
Fits k a b E = WF a × WF b × Compat k a b × WF E × (shape E ≡ shape (merge k a b))

FitsL : Nat → List LT → List LT → List LT → Set
FitsL k as bs cs = WFs as × WFs bs × (bdL true k as ≡ bdL false k bs) × WFs cs × (shapes cs ≡ shapes (mergeL k as bs))

private
  -- zero case: lengths
  zero-lens : ∀ osa csa osb csb os cs → Fits zero (lt osa csa) (lt osb csb) (lt os cs) →
              (length csa ≤ length cs) × (suc (length csa) ≤ length os)
  zero-lens osa csa osb csb os cs (_ , _ , _ , (wE , _) , sh) = p₁ , p₂
    where
    lc : length cs ≡ length csa + length csb
    lc = trans (sym (length-shapes cs))
         (trans (cong length (node-inj sh))
         (trans (cong length (shapes-++ csa csb))
         (trans (length-++ (shapes csa) (shapes csb))
                (cong₂ _+_ (length-shapes csa) (length-shapes csb)))))
    p₁ : length csa ≤ length cs
    p₁ = subst (λ n → length csa ≤ n) (sym lc) (le-+ (length csa) (length csb))
    p₂ : suc (length csa) ≤ length os
    p₂ = subst (λ n → suc (length csa) ≤ n) (sym (trans (sym (len-length os)) (trans wE (cong suc (len-length cs))))) p₁

  -- the children of a fitting (suc k) composite fit pointwise
  suc-fits : ∀ k osa csa osb csb os cs → Fits (suc k) (lt osa csa) (lt osb csb) (lt os cs) → FitsL k csa csb cs
  suc-fits k osa csa osb csb os cs ((_ , wa) , (_ , wb) , cp , (_ , wE) , sh) = wa , wb , lt-injₛ cp , wE , node-inj sh

  fitsL-head : ∀ k a as b bs c cs → FitsL k (a ∷ as) (b ∷ bs) (c ∷ cs) → Fits k a b c × FitsL k as bs cs
  fitsL-head k a as b bs c cs ((wa , was) , (wb , wbs) , cp , (wc , wcs) , sh) =
    (wa , wb , ∷-injₕ cp , wc , ∷-injₕ sh) , (was , wbs , ∷-injₜ cp , wcs , ∷-injₜ sh)

------------------------------------------------------------------------

mutual
  merge-split : ∀ k a b E → Fits k a b E → merge k (fst (split k a E)) (snd (split k a E)) ≡ E
  merge-split zero (lt osa csa) (lt osb csb) (lt os cs) fz =
    cong₂ lt (take-suc-++ (length csa) os) (take-drop (length csa) cs)
  merge-split (suc k) (lt osa csa) (lt osb csb) (lt os cs) fz
    with splitL k csa cs | mergeSplitL k csa csb cs (suc-fits k osa csa osb csb os cs fz)
  ... | as , bs | e = cong (lt os) e

  mergeSplitL : ∀ k as bs cs → FitsL k as bs cs → mergeL k (fst (splitL k as cs)) (snd (splitL k as cs)) ≡ cs
  mergeSplitL k []       []       []       _ = refl
  mergeSplitL k []       []       (c ∷ cs) (_ , _ , _ , _ , ())
  mergeSplitL k []       (b ∷ bs) _        (_ , _ , () , _ , _)
  mergeSplitL k (a ∷ as) []       _        (_ , _ , () , _ , _)
  mergeSplitL k (a ∷ as) (b ∷ bs) []       (_ , _ , _ , _ , ())
  mergeSplitL k (a ∷ as) (b ∷ bs) (c ∷ cs) fl
    with split k a c | merge-split k a b c (fst (fitsL-head k a as b bs c cs fl))
       | splitL k as cs | mergeSplitL k as bs cs (snd (fitsL-head k a as b bs c cs fl))
  ... | x , y | e | xs , ys | es = cong₂ _∷_ e es

mutual
  compat-split : ∀ k a b E → Fits k a b E → Compat k (fst (split k a E)) (snd (split k a E))
  compat-split zero (lt osa csa) (lt osb csb) (lt os cs) fz =
    cong (λ z → lt (z ∷ []) []) (last-head (length csa) os (snd (zero-lens osa csa osb csb os cs fz)))
  compat-split (suc k) (lt osa csa) (lt osb csb) (lt os cs) fz
    with splitL k csa cs | compatSplitL k csa csb cs (suc-fits k osa csa osb csb os cs fz)
  ... | as , bs | e = cong (lt os) e

  compatSplitL : ∀ k as bs cs → FitsL k as bs cs →
                 bdL true k (fst (splitL k as cs)) ≡ bdL false k (snd (splitL k as cs))
  compatSplitL k []       []       []       _ = refl
  compatSplitL k []       []       (c ∷ cs) (_ , _ , _ , _ , ())
  compatSplitL k []       (b ∷ bs) _        (_ , _ , () , _ , _)
  compatSplitL k (a ∷ as) []       _        (_ , _ , () , _ , _)
  compatSplitL k (a ∷ as) (b ∷ bs) []       (_ , _ , _ , _ , ())
  compatSplitL k (a ∷ as) (b ∷ bs) (c ∷ cs) fl
    with split k a c | compat-split k a b c (fst (fitsL-head k a as b bs c cs fl))
       | splitL k as cs | compatSplitL k as bs cs (snd (fitsL-head k a as b bs c cs fl))
  ... | x , y | e | xs , ys | es = cong₂ _∷_ e es

-- split reads only the shape of a and the structure of E.
mutual
  relab-split : ∀ f k a E → split k a (relab f E) ≡ (relab f (fst (split k a E)) , relab f (snd (split k a E)))
  relab-split f zero (lt _ csA) (lt os cs) =
    cong₂ _,_ (cong₂ lt (sym (map-take f (suc (length csA)) os)) (sym (rels-take f (length csA) cs)))
              (cong₂ lt (sym (map-drop f (length csA) os)) (sym (rels-drop f (length csA) cs)))
  relab-split f (suc k) (lt _ csA) (lt os cs)
    with splitL k csA cs | splitL k csA (relabs f cs) | relabSplitL f k csA cs
  ... | as , bs | .(relabs f as , relabs f bs) | refl = refl

  relabSplitL : ∀ f k as cs → splitL k as (relabs f cs) ≡ (relabs f (fst (splitL k as cs)) , relabs f (snd (splitL k as cs)))
  relabSplitL f k []       cs       = refl
  relabSplitL f k (a ∷ as) []       = refl
  relabSplitL f k (a ∷ as) (c ∷ cs)
    with split k a c | split k a (relab f c) | relab-split f k a c
       | splitL k as cs | splitL k as (relabs f cs) | relabSplitL f k as cs
  ... | x , y | .(relab f x , relab f y) | refl | xs , ys | .(relabs f xs , relabs f ys) | refl = refl

------------------------------------------------------------------------
-- The parts of a well-formed diagram are well-formed diagrams.

private
  allN-take : ∀ {P : Nat → Set} n xs → AllN P xs → AllN P (take n xs)
  allN-take zero    xs       a        = tt
  allN-take (suc n) []       a        = tt
  allN-take (suc n) (x ∷ xs) (p , pp) = p , allN-take n xs pp

  allN-drop : ∀ {P : Nat → Set} n xs → AllN P xs → AllN P (drop n xs)
  allN-drop zero    xs       a        = a
  allN-drop (suc n) []       a        = tt
  allN-drop (suc n) (x ∷ xs) (p , pp) = allN-drop n xs pp

  wfs-take : ∀ n cs → WFs cs → WFs (take n cs)
  wfs-take zero    cs       w        = tt
  wfs-take (suc n) []       w        = tt
  wfs-take (suc n) (c ∷ cs) (w , ws) = w , wfs-take n cs ws

  wfs-drop : ∀ n cs → WFs cs → WFs (drop n cs)
  wfs-drop zero    cs       w        = w
  wfs-drop (suc n) []       w        = tt
  wfs-drop (suc n) (c ∷ cs) (w , ws) = wfs-drop n cs ws

  +-cancel : ∀ m a b → m + a ≡ m + b → a ≡ b
  +-cancel zero    a b e = e
  +-cancel (suc m) a b e = +-cancel m a b (suc-inj e)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

module _ (Θ : Ctx) where

  private
    exCs-take : ∀ e n os cs → ExCs Θ e os cs → n ≤ length cs → ExCs Θ e (take (suc n) os) (take n cs)
    exCs-take e zero    (o ∷ [])      []       x p = tt
    exCs-take e zero    (o ∷ o' ∷ os) (c ∷ cs) x p = tt
    exCs-take e (suc n) (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) p = xc , exCs-take e n (o' ∷ os) cs xs p
    exCs-take e (suc n) (o ∷ [])      []       x ()
    exCs-take e n       []            _        () p
    exCs-take e n       (o ∷ [])      (c ∷ cs) () p
    exCs-take e n       (o ∷ o' ∷ os) []       () p

    exCs-drop : ∀ e n os cs → ExCs Θ e os cs → n ≤ length cs → ExCs Θ e (drop n os) (drop n cs)
    exCs-drop e zero    os            cs       x p = x
    exCs-drop e (suc n) (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) p = exCs-drop e n (o' ∷ os) cs xs p
    exCs-drop e (suc n) (o ∷ [])      []       x ()
    exCs-drop e (suc n) []            _        () p
    exCs-drop e (suc n) (o ∷ [])      (c ∷ cs) () p
    exCs-drop e (suc n) (o ∷ o' ∷ os) []       () p

  mutual
    ex-split : ∀ k a b E e par → Fits k a b E → Ex Θ e par E →
               Ex Θ e par (fst (split k a E)) × Ex Θ e par (snd (split k a E))
    ex-split zero (lt osa csa) (lt osb csb) (lt os cs) e par fz (ao , xs) =
      (allN-take (suc m) os ao , exCs-take e m os cs xs p₁) ,
      (allN-drop m os ao , exCs-drop e m os cs xs p₁)
      where
      m = length csa
      p₁ = fst (zero-lens osa csa osb csb os cs fz)
    ex-split (suc k) (lt osa csa) (lt osb csb) (lt os cs) e par fz (ao , xs)
      with splitL k csa cs | exSplitL k csa csb os cs e (suc-fits k osa csa osb csb os cs fz) xs
    ... | as , bs | xa , xb = (ao , xa) , (ao , xb)

    exSplitL : ∀ k as bs os cs e → FitsL k as bs cs → ExCs Θ e os cs →
               ExCs Θ e os (fst (splitL k as cs)) × ExCs Θ e os (snd (splitL k as cs))
    exSplitL k []       []       os cs e (_ , _ , _ , _ , sh) x with cs | sh
    ... | [] | _ = x , x
    exSplitL k []       (b ∷ bs) os cs e (_ , _ , () , _ , _) x
    exSplitL k (a ∷ as) []       os cs e (_ , _ , () , _ , _) x
    exSplitL k (a ∷ as) (b ∷ bs) os []       e (_ , _ , _ , _ , ()) x
    exSplitL k (a ∷ as) (b ∷ bs) (o ∷ o' ∷ os) (c ∷ cs) e fl (xc , xs)
      with split k a c | ex-split k a b c (suc e) (just (o , o')) (fst (fitsL-head k a as b bs c cs fl)) xc
         | splitL k as cs | exSplitL k as bs (o' ∷ os) cs e (snd (fitsL-head k a as b bs c cs fl)) xs
    ... | x , y | xx , xy | xs' , ys' | xxs , xys = (xx , xxs) , (xy , xys)
    exSplitL k (a ∷ as) (b ∷ bs) []            (c ∷ cs) e fl ()
    exSplitL k (a ∷ as) (b ∷ bs) (o ∷ [])      (c ∷ cs) e fl ()
