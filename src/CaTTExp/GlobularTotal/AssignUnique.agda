------------------------------------------------------------------------
-- F2c, step (P3), uniqueness: `assign` on a composite returns its
-- factors.
--
-- Let Q give each label of a coherence's tree R a position (a tree),
-- compatible in the sense of FlatBd.Good, and suppose each image
-- J y = nf n Γ (σ y) is the relabelling of Q y along f. If E is the
-- composite of Q over R, then `assign` cuts E back into Q:
--
--   assign-flat : Good Q d P R → flatG Q d R ≡ just E → ND R →
--                 Lab (Rel Q) R →
--                 assign n Γ σ d R E ≡ just as  with  find y as ≡ Q y
--                 for every label y of R.
--
-- So the positions `assign` hands out are the only ones: lifting a
-- substituted coherence sees the arguments' own positions. On the
-- way: relabelling commutes with merge and with flatG (relab-flatG).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.AssignUnique where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; merge; mergeL; bd; split; flat; nf; assign; assignCs; shape; module Lists)
open Lists using (find; drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; Compat)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.FlatBd
  using (flatG; flatGL; Good; GoodCs; Ok; Par; AllL; flat-bd; flat-ends; flat-is-flatG)
open import CaTTExp.GlobularTotal.NfSub using (Lab; LabL; AllN)
open import CaTTExp.GlobularTotal.LabDistinct using (NodupL; ND; NDs)
open import CaTTExp.GlobularTotal.Relabel using (relab; relabs; mapN)
open import CaTTExp.GlobularTotal.Assign using (memKey; shape-relab)
open import CaTTExp.GlobularTotal.SplitMerge using (split-merge)

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

  ∨-false : ∀ a b → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false false false e = refl , refl
  ∨-false true  b     ()
  ∨-false false true  ()

  not-true : ∀ b → (b ≡ true → ⊥) → b ≡ false
  not-true true  f = ⊥-elim (f refl)
  not-true false f = refl

  t≢f : true ≡ false → ⊥
  t≢f ()

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

  ==-ne : ∀ y o → ((y ==ℕ o) ≡ true → ⊥) → (y ==ℕ o) ≡ false
  ==-ne y o f = not-true _ f

  ne-mem : ∀ y o (b : Nat → Bool) → b y ≡ true → b o ≡ false → (y ==ℕ o) ≡ false
  ne-mem y o b m n = ==-ne y o (λ h → t≢f (trans (sym m) (subst (λ z → b z ≡ false) (sym (==ℕ-sound y o (≡-T h))) n)))

  sh3 : ∀ a b c d → (a ∨ (b ∨ (c ∨ d))) ≡ ((a ∨ c) ∨ (b ∨ d))
  sh3 true  b     c     d = refl
  sh3 false true  true  d = refl
  sh3 false true  false d = refl
  sh3 false false c     d = refl

  sh2 : ∀ a b c → (a ∨ (b ∨ c)) ≡ ((a ∨ (b ∨ false)) ∨ (c ∨ false))
  sh2 true  b     c     = refl
  sh2 false true  c     = refl
  sh2 false false true  = refl
  sh2 false false false = refl

  sh1 : ∀ a → (a ∨ false) ≡ ((a ∨ false) ∨ false)
  sh1 true  = refl
  sh1 false = refl

  memKey-++ : ∀ y L₁ L₂ → memKey y (L₁ ++ L₂) ≡ (memKey y L₁ ∨ memKey y L₂)
  memKey-++ y []             L₂ = refl
  memKey-++ y ((k , _) ∷ L₁) L₂ with y ==ℕ k
  ... | true  = refl
  ... | false = memKey-++ y L₁ L₂

  find-in : ∀ y (L₁ L₂ : List (Nat × LT)) → memKey y L₁ ≡ true → find y (L₁ ++ L₂) ≡ find y L₁
  find-in y []             L₂ ()
  find-in y ((k , v) ∷ L₁) L₂ m with y ==ℕ k
  ... | true  = refl
  ... | false = find-in y L₁ L₂ m

  find-out : ∀ y (L₁ L₂ : List (Nat × LT)) → memKey y L₁ ≡ false → find y (L₁ ++ L₂) ≡ find y L₂
  find-out y []             L₂ m = refl
  find-out y ((k , v) ∷ L₁) L₂ m with y ==ℕ k
  find-out y ((k , v) ∷ L₁) L₂ () | true
  ... | false = find-out y L₁ L₂ m

  find-here : ∀ y (v : LT) L → find y ((y , v) ∷ L) ≡ just v
  find-here y v L rewrite ==-self y = refl

  find-skip : ∀ y k (v : LT) L → (y ==ℕ k) ≡ false → find y ((k , v) ∷ L) ≡ find y L
  find-skip y k v L e rewrite e = refl

------------------------------------------------------------------------
-- Lab under a membership-guarded implication.

private
  allN-mapM : ∀ {P P' : Nat → Set} xs → (∀ y → memL y xs ≡ true → P y → P' y) → AllN P xs → AllN P' xs
  allN-mapM []       h _        = tt
  allN-mapM (x ∷ xs) h (p , qs) =
    h x (∨-inl _ _ (==-self x)) p , allN-mapM xs (λ y m → h y (∨-inr (y ==ℕ x) _ m)) qs

mutual
  lab-mapM : ∀ {P P' : Nat → Set} a → (∀ y → mem y a ≡ true → P y → P' y) → Lab P a → Lab P' a
  lab-mapM (lt os cs) h (p , qs) =
    allN-mapM os (λ y m → h y (∨-inl _ _ m)) p , labL-mapM cs (λ y m → h y (∨-inr (memL y os) _ m)) qs

  labL-mapM : ∀ {P P' : Nat → Set} cs → (∀ y → memCs y cs ≡ true → P y → P' y) → LabL P cs → LabL P' cs
  labL-mapM []       h _        = tt
  labL-mapM (c ∷ cs) h (p , qs) =
    lab-mapM c (λ y m → h y (∨-inl _ _ m)) p , labL-mapM cs (λ y m → h y (∨-inr (mem y c) _ m)) qs

------------------------------------------------------------------------
-- Relabelling commutes with merge and flatG.

private
  map-++ : ∀ f xs ys → mapN f (xs ++ ys) ≡ mapN f xs ++ mapN f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  map-drop1 : ∀ f xs → mapN f (drop 1 xs) ≡ drop 1 (mapN f xs)
  map-drop1 f []       = refl
  map-drop1 f (x ∷ xs) = refl

  relabs-++ : ∀ f cs ds → relabs f (cs ++ ds) ≡ relabs f cs ++ relabs f ds
  relabs-++ f []       ds = refl
  relabs-++ f (c ∷ cs) ds = cong (relab f c ∷_) (relabs-++ f cs ds)

mutual
  relab-merge : ∀ f k a b → relab f (merge k a b) ≡ merge k (relab f a) (relab f b)
  relab-merge f zero    (lt os cs) (lt os' cs') =
    cong₂ lt (trans (map-++ f os (drop 1 os')) (cong (mapN f os ++_) (map-drop1 f os')))
             (relabs-++ f cs cs')
  relab-merge f (suc k) (lt os cs) (lt os' cs') = cong (lt (mapN f os)) (relabs-mergeL f k cs cs')

  relabs-mergeL : ∀ f k cs ds → relabs f (mergeL k cs ds) ≡ mergeL k (relabs f cs) (relabs f ds)
  relabs-mergeL f k []       ds       = refl
  relabs-mergeL f k (c ∷ cs) []       = refl
  relabs-mergeL f k (c ∷ cs) (d ∷ ds) = cong₂ _∷_ (relab-merge f k c d) (relabs-mergeL f k cs ds)

module _ (I J : Nat → Maybe LT) (f : Nat → Nat) where

  -- J y is the relabelling of I y.
  Rel : Nat → Set
  Rel y = ∀ X → I y ≡ just X → J y ≡ just (relab f X)

  mutual
    relab-flatG : ∀ d R a → Lab Rel R → flatG I d R ≡ just a → flatG J d R ≡ just (relab f a)
    relab-flatG d (lt os (c ∷ cs))       a (_ , lc) e = relab-flatGL d c cs a lc e
    relab-flatG d (lt (y ∷ []) [])       a ((r , _) , _) e = r a e
    relab-flatG d (lt []               []) a l ()
    relab-flatG d (lt (y ∷ y' ∷ ys)    []) a l ()

    relab-flatGL : ∀ d c cs a → LabL Rel (c ∷ cs) → flatGL I d c cs ≡ just a → flatGL J d c cs ≡ just (relab f a)
    relab-flatGL d c []        a (lc , _) e = relab-flatG (suc d) c a lc e
    relab-flatGL d c (c' ∷ cs) a (lc , lcs) e
      with bind-inv (flatG I (suc d) c) _ e
    ... | x , ex , e' with bind-inv (flatGL I d c' cs) _ e'
    ...   | y , ey , refl
      rewrite relab-flatG (suc d) c x lc ex | relab-flatGL d c' cs y lcs ey
      = cong just (sym (relab-merge f d x y))

------------------------------------------------------------------------
-- The theorem.

module _ (Γ : Ctx) (σ : Sub) (n : Nat) (f : Nat → Nat) (Q : Nat → Maybe LT) where

  J : Nat → Maybe LT
  J y = nf n Γ (lookupₛ σ y)

  private
    RelQ = Rel Q J f

    unfold : ∀ d o o' os c c' cs E a Ea Eb asc bs → flat n Γ σ (suc d) c ≡ just a →
             split d a E ≡ (Ea , Eb) →
             assign n Γ σ (suc d) c Ea ≡ just asc →
             assignCs n Γ σ d (o' ∷ os) c' cs Eb ≡ just bs →
             assignCs n Γ σ d (o ∷ o' ∷ os) c (c' ∷ cs) E ≡ just (((o , bd false d Ea) ∷ asc) ++ bs)
    unfold d o o' []      c c' cs E a Ea Eb asc bs fl sp e₁ e₂ rewrite fl | sp | e₁ | e₂ = refl
    unfold d o o' (_ ∷ _) c c' cs E a Ea Eb asc bs fl sp e₁ e₂ rewrite fl | sp | e₁ | e₂ = refl

  Out : Nat → LT → LT → List (Nat × LT) → Set
  Out d R E as = (∀ y → memKey y as ≡ mem y R) × Lab (λ y → find y as ≡ Q y) R

  mutual
    assign-flat : ∀ d P R E → Good Q d P R → flatG Q d R ≡ just E → ND R → Lab RelQ R →
                  Σ (List (Nat × LT)) λ as → (assign n Γ σ d R E ≡ just as) × Out d R E as
    assign-flat d P (lt (y ∷ []) []) E g e nd l =
      ((y , E) ∷ []) , refl , (λ y' → sh1 (y' ==ℕ y)) , ((trans (find-here y E []) (sym e) , tt) , tt)
    assign-flat d P (lt [] [])            E (_ , ()) e nd l
    assign-flat d P (lt (y ∷ y' ∷ ys) []) E (_ , ()) e nd l
    assign-flat d P (lt [] (c ∷ cs))      E (_ , ()) e nd l
    assign-flat d P (lt (o ∷ os) (c ∷ cs)) E (oks , g) e nd l with os
    ... | [] = ⊥-elim (no-objs g)
      where
      no-objs : GoodCs Q d (o ∷ []) (c ∷ cs) → ⊥
      no-objs ()
    ... | o' ∷ os' = assignCs-flat d P o (o' ∷ os') c cs E (oks , g) e nd l

    assignCs-flat : ∀ d P o os c cs E → Good Q d P (lt (o ∷ os) (c ∷ cs)) → flatGL Q d c cs ≡ just E →
                    ND (lt (o ∷ os) (c ∷ cs)) → Lab RelQ (lt (o ∷ os) (c ∷ cs)) →
                    Σ (List (Nat × LT)) λ as → (assignCs n Γ σ d (o ∷ os) c cs E ≡ just as)
                      × Out d (lt (o ∷ os) (c ∷ cs)) E as
    assignCs-flat d P o []        c cs E (_ , ()) e nd l
    assignCs-flat d P o (o' ∷ []) c [] E (oks , gc , tt) e ((o∉ , _) , dis , (ndc , _ , _)) ((ro , ro' , _) , (lc , _))
      with assign-flat (suc d) (Par Q d o o') c E gc e ndc lc
    ... | asc , ea , (kc , fc) rewrite ea = as , refl , keys , ((fo , fo' , tt) , (lab-mapM c (λ y m h → trans (tr y m) h) fc , tt))
      where
      as = (o , bd false d E) ∷ (o' , bd true d E) ∷ asc
      par = flat-ends Q d o o' c E gc e

      o≠o' : (o' ==ℕ o) ≡ false
      o≠o' = ne-mem o' o (λ z → memL z (o' ∷ [])) (∨-inl _ _ (==-self o')) o∉

      c-o : ∀ y → mem y c ≡ true → (y ==ℕ o) ≡ false
      c-o y m = ne-mem y o (λ z → mem z c) m (fst (∨-false _ _ (dis o (∨-inl _ _ (==-self o)))))

      c-o' : ∀ y → mem y c ≡ true → (y ==ℕ o') ≡ false
      c-o' y m = ne-mem y o' (λ z → mem z c) m
                   (fst (∨-false _ _ (dis o' (∨-inr (o' ==ℕ o) _ (∨-inl _ _ (==-self o'))))))

      tr : ∀ y → mem y c ≡ true → find y as ≡ find y asc
      tr y m rewrite c-o y m | c-o' y m = refl

      fo : find o as ≡ Q o
      fo = trans (find-here o (bd false d E) ((o' , bd true d E) ∷ asc)) (sym (fst par))

      fo' : find o' as ≡ Q o'
      fo' rewrite o≠o' = trans (find-here o' (bd true d E) asc) (sym (snd par))

      keys : ∀ y → memKey y as ≡ mem y (lt (o ∷ o' ∷ []) (c ∷ []))
      keys y rewrite kc y = sh2 (y ==ℕ o) (y ==ℕ o') (mem y c)
    assignCs-flat d P o (o' ∷ []) c (c' ∷ cs) E (_ , _ , ()) e nd l
    assignCs-flat d P o (o' ∷ o'' ∷ os) c [] E (_ , _ , ()) e nd l
    assignCs-flat d P o (o' ∷ os) c (c' ∷ cs) E ((oko , oks) , gc , gr) e
                  ((o∉ , ndos) , dis , (ndc , c∩ , ndcs)) ((ro , ros) , (lc , lcs))
      with bind-inv (flatG Q (suc d) c) _ e
    ... | qa , eqa , e' with bind-inv (flatGL Q d c' cs) _ e'
    ...   | qb , eqb , refl
      with assign-flat (suc d) (Par Q d o o') c qa gc eqa ndc lc
         | assignCs-flat d P o' os c' cs qb (oks , gr) eqb ndr (ros , lcs)
      where
      ndr : ND (lt (o' ∷ os) (c' ∷ cs))
      ndr = ndos , (λ y m → snd (∨-false (mem y c) (memCs y (c' ∷ cs)) (dis y (∨-inr (y ==ℕ o) _ m)))) , ndcs
    ... | asc , eac , (kc , fc) | bs , eab , (kr , fr) = as , eq , keys , ((fo , fst-fr) , (lc' , labL-mapM (c' ∷ cs) (λ y m h → trans (trr y (∨-inr (memL y (o' ∷ os)) _ m)) h) (snd fr)))
      where
      Rr = lt (o' ∷ os) (c' ∷ cs)
      gR : Good Q d P Rr
      gR = oks , gr
      wa = fst (flat-bd Q (suc d) (Par Q d o o') c qa gc eqa)
      wb = fst (flat-bd Q d P Rr qb gR eqb)
      cp : Compat d qa qb
      cp = trans (just-inj (trans (sym (snd (flat-ends Q d o o' c qa gc eqa))) (snd (flat-bd Q d P Rr qb gR eqb) false 0)))
                 (cong (λ k → bd false k qb) (+0 d))
      ja : flat n Γ σ (suc d) c ≡ just (relab f qa)
      ja = trans (flat-is-flatG n Γ σ (suc d) c) (relab-flatG Q J f (suc d) c qa lc eqa)
      sp : split d (relab f qa) (merge d qa qb) ≡ (qa , qb)
      sp = split-merge d (relab f qa) qa qb (shape-relab f qa) wa wb cp

      as = ((o , bd false d qa) ∷ asc) ++ bs

      eq : assignCs n Γ σ d (o ∷ o' ∷ os) c (c' ∷ cs) (merge d qa qb) ≡ just as
      eq = unfold d o o' os c c' cs (merge d qa qb) (relab f qa) qa qb asc bs ja sp eac eab

      o-head : memL o (o ∷ o' ∷ os) ≡ true
      o-head = ∨-inl _ _ (==-self o)

      c-o : ∀ y → mem y c ≡ true → (y ==ℕ o) ≡ false
      c-o y m = ne-mem y o (λ z → mem z c) m (fst (∨-false _ _ (dis o o-head)))

      r-o : ∀ y → mem y Rr ≡ true → (y ==ℕ o) ≡ false
      r-o y m with ∨-split (memL y (o' ∷ os)) (memCs y (c' ∷ cs)) m
      ... | inl h = ne-mem y o (λ z → memL z (o' ∷ os)) h o∉
      ... | inr h = ne-mem y o (λ z → memCs z (c' ∷ cs)) h (snd (∨-false (mem o c) (memCs o (c' ∷ cs)) (dis o o-head)))

      r-c : ∀ y → mem y Rr ≡ true → mem y c ≡ false
      r-c y m with ∨-split (memL y (o' ∷ os)) (memCs y (c' ∷ cs)) m
      ... | inl h = fst (∨-false _ _ (dis y (∨-inr (y ==ℕ o) _ h)))
      ... | inr h = not-true _ (λ mc → t≢f (trans (sym h) (c∩ y mc)))

      tc : ∀ y → mem y c ≡ true → find y as ≡ find y asc
      tc y m rewrite c-o y m = find-in y asc bs (trans (kc y) m)

      trr : ∀ y → mem y Rr ≡ true → find y as ≡ find y bs
      trr y m rewrite r-o y m = find-out y asc bs (trans (kc y) (r-c y m))

      fo : find o as ≡ Q o
      fo = trans (find-here o (bd false d qa) (asc ++ bs)) (sym (fst (flat-ends Q d o o' c qa gc eqa)))

      lc' : Lab (λ y → find y as ≡ Q y) c
      lc' = lab-mapM c (λ y m h → trans (tc y m) h) fc

      fst-fr : AllN (λ y → find y as ≡ Q y) (o' ∷ os)
      fst-fr = allN-mapM (o' ∷ os) (λ y m h → trans (trr y (∨-inl _ _ m)) h) (fst fr)

      keys : ∀ y → memKey y as ≡ mem y (lt (o ∷ o' ∷ os) (c ∷ c' ∷ cs))
      keys y rewrite memKey-++ y asc bs | kc y | kr y =
        sh3 (y ==ℕ o) (mem y c) (memL y (o' ∷ os)) (memCs y (c' ∷ cs))
