------------------------------------------------------------------------
-- F2c, step (P3) of lemmas 3–5: `assign` hands each variable of a
-- coherence's pasting context the cells it occupies.
--
-- Fix the images J y = nf n Γ (σ y) of the arguments of a coherence
-- and a relabelling f. For T (a part of the coherence's labelled tree
-- at depth d, compatible for J) whose composite is aT, and a position
-- E (a diagram of Θ) with relab f E ≡ aT, `assign` succeeds with a
-- list `as` such that, with P y = find y as:
--
--   (I1) every label y of T has a position X = P y, a diagram of Θ,
--        with relab f X its image J y, and X agrees with E below d;
--   (I2) the positions compose back to E: flatG P d T ≡ just E;
--   (I3) positions respect boundaries (`BdOK`): an object y of a branch
--        between o and o′ at depth d+1 has P o = bd false d (P y) and
--        P o′ = bd true d (P y);
--   (I4) the keys of `as` are the labels of T;
--   (I5) (T not a leaf) T's first and last objects sit at E's
--        d-boundaries.
--
-- By induction along assign's recursion, using SplitMerge and
-- SplitProps to cut E along the image of the first branch.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Assign where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; merge; bd; bdL; split; flat; nf; assign; assignCs; shape; shapes; module Lists)
open Lists using (find; headN; lastN)
open import CaTTExp.GlobularTotal.TreeAlg
  using (WF; WFs; Compat; bd-merge-src; bd-merge-tgt; bd-merge-low)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL; Ex; AllN)
open import CaTTExp.GlobularTotal.FlatBd
  using (flatG; flatGL; Good; GoodCs; Ok; Par; AllL; flat-bd; flat-ends; flat-is-flatG; bd-bd)
open import CaTTExp.GlobularTotal.NfSub using (flatG-cong)
open import CaTTExp.GlobularTotal.CohParts using (lab-of-mem)
open import CaTTExp.GlobularTotal.DimCheck using (ex-wf)
open import CaTTExp.GlobularTotal.ExBd using (ex-bd)
open import CaTTExp.GlobularTotal.LabDistinct using (NodupL; ND; NDs)
open import CaTTExp.GlobularTotal.Relabel using (relab; relabs; mapN)
open import CaTTExp.GlobularTotal.SplitMerge using (split-merge)
open import CaTTExp.GlobularTotal.SplitProps
  using (Fits; merge-split; compat-split; relab-split; ex-split)

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

  lt-suc : ∀ a → T (a <ℕ suc a)
  lt-suc zero    = tt
  lt-suc (suc a) = lt-suc a

  lt-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  lt-weak zero    b       p = tt
  lt-weak (suc a) zero    ()
  lt-weak (suc a) (suc b) p = lt-weak a b p

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

  ==-ne : ∀ y o → ((y ==ℕ o) ≡ true → ⊥) → (y ==ℕ o) ≡ false
  ==-ne y o f = not-true _ f

  memL-last : ∀ x xs → memL (lastN (x ∷ xs)) (x ∷ xs) ≡ true
  memL-last x []        = ∨-inl _ _ (==-self x)
  memL-last x (x' ∷ xs) = ∨-inr (lastN (x' ∷ xs) ==ℕ x) _ (memL-last x' xs)

  -- boolean shuffles
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

------------------------------------------------------------------------
-- Association lists of positions.

memKey : Nat → List (Nat × LT) → Bool
memKey y []             = false
memKey y ((k , _) ∷ L) = (y ==ℕ k) ∨ memKey y L

private
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

  find-skip : ∀ y k (v : LT) L → (y ==ℕ k) ≡ false → find y ((k , v) ∷ L) ≡ find y L
  find-skip y k v L e rewrite e = refl

  find-here : ∀ y (v : LT) L → find y ((y , v) ∷ L) ≡ just v
  find-here y v L rewrite ==-self y = refl

------------------------------------------------------------------------
-- Positions respect boundaries.

ObjB : (Nat → Maybe LT) → Nat → Nat → Nat → LT → Set
ObjB P d o o' (lt os _) =
  AllN (λ y → Σ LT λ X → (P y ≡ just X) × (P o ≡ just (bd false d X)) × (P o' ≡ just (bd true d X))) os

mutual
  BdOK : (Nat → Maybe LT) → Nat → LT → Set
  BdOK P d (lt os cs) = BdCs P d os cs

  BdCs : (Nat → Maybe LT) → Nat → List Nat → List LT → Set
  BdCs P d (o ∷ o' ∷ os) (c ∷ cs) = ObjB P d o o' c × BdOK P (suc d) c × BdCs P d (o' ∷ os) cs
  BdCs P d _             _        = ⊤

private
  memL-in : ∀ y os cs → memL y os ≡ true → mem y (lt os cs) ≡ true
  memL-in y os cs m = ∨-inl _ _ m

  objB-cong : ∀ P P' d o o' c → P o ≡ P' o → P o' ≡ P' o' → (∀ y → mem y c ≡ true → P y ≡ P' y) →
              ObjB P d o o' c → ObjB P' d o o' c
  objB-cong P P' d o o' (lt os cs) eo eo' h b = go os (λ y m → h y (memL-in y os cs m)) b
    where
    go : ∀ xs → (∀ y → memL y xs ≡ true → P y ≡ P' y) →
         AllN (λ y → Σ LT λ X → (P y ≡ just X) × (P o ≡ just (bd false d X)) × (P o' ≡ just (bd true d X))) xs →
         AllN (λ y → Σ LT λ X → (P' y ≡ just X) × (P' o ≡ just (bd false d X)) × (P' o' ≡ just (bd true d X))) xs
    go []       h' _ = tt
    go (x ∷ xs) h' ((X , ex , a , b') , rest) =
      (X , trans (sym (h' x (∨-inl _ _ (==-self x)))) ex , trans (sym eo) a , trans (sym eo') b') ,
      go xs (λ y m → h' y (∨-inr (y ==ℕ x) _ m)) rest

mutual
  bdOK-cong : ∀ P P' d T → (∀ y → mem y T ≡ true → P y ≡ P' y) → BdOK P d T → BdOK P' d T
  bdOK-cong P P' d (lt os cs) h b = bdCs-cong P P' d os cs h b

  bdCs-cong : ∀ P P' d os cs → (∀ y → mem y (lt os cs) ≡ true → P y ≡ P' y) → BdCs P d os cs → BdCs P' d os cs
  bdCs-cong P P' d (o ∷ o' ∷ os) (c ∷ cs) h (ob , bc , bs) =
    objB-cong P P' d o o' c (h o (∨-inl _ _ (∨-inl _ _ (==-self o))))
              (h o' (∨-inl _ _ (∨-inr (o' ==ℕ o) _ (∨-inl _ _ (==-self o')))))
              (λ y m → h y (∨-inr (memL y (o ∷ o' ∷ os)) _ (∨-inl _ _ m))) ob ,
    bdOK-cong P P' (suc d) c (λ y m → h y (∨-inr (memL y (o ∷ o' ∷ os)) _ (∨-inl _ _ m))) bc ,
    bdCs-cong P P' d (o' ∷ os) cs
      (λ y m → h y (rest y m)) bs
    where
    rest : ∀ y → mem y (lt (o' ∷ os) cs) ≡ true → mem y (lt (o ∷ o' ∷ os) (c ∷ cs)) ≡ true
    rest y m with ∨-split (memL y (o' ∷ os)) (memCs y cs) m
    ... | inl h₁ = ∨-inl _ _ (∨-inr (y ==ℕ o) _ h₁)
    ... | inr h₂ = ∨-inr (memL y (o ∷ o' ∷ os)) _ (∨-inr (mem y c) _ h₂)
  bdCs-cong P P' d []            cs       h b = tt
  bdCs-cong P P' d (o ∷ [])      cs       h b = tt
  bdCs-cong P P' d (o ∷ o' ∷ os) []       h b = tt

------------------------------------------------------------------------
-- Relabelling commutes with boundaries and keeps the shape.

private
  head-map : ∀ f o os → headN (mapN f (o ∷ os)) ≡ f (headN (o ∷ os))
  head-map f o os = refl

  last-map : ∀ f o os → lastN (mapN f (o ∷ os)) ≡ f (lastN (o ∷ os))
  last-map f o []        = refl
  last-map f o (o' ∷ os) = last-map f o' os

mutual
  relab-bd : ∀ f β k X → WF X → relab f (bd β k X) ≡ bd β k (relab f X)
  relab-bd f false zero    (lt []       cs) (() , _)
  relab-bd f false zero    (lt (o ∷ os) cs) _ = refl
  relab-bd f true  zero    (lt []       cs) (() , _)
  relab-bd f true  zero    (lt (o ∷ os) cs) _ = cong (λ z → lt (z ∷ []) []) (sym (last-map f o os))
  relab-bd f false (suc k) (lt os cs)       (_ , ws) = cong (lt (mapN f os)) (relabs-bd f false k cs ws)
  relab-bd f true  (suc k) (lt os cs)       (_ , ws) = cong (lt (mapN f os)) (relabs-bd f true k cs ws)

  relabs-bd : ∀ f β k cs → WFs cs → relabs f (bdL β k cs) ≡ bdL β k (relabs f cs)
  relabs-bd f β k []       _        = refl
  relabs-bd f β k (c ∷ cs) (w , ws) = cong₂ _∷_ (relab-bd f β k c w) (relabs-bd f β k cs ws)

mutual
  shape-relab : ∀ f X → shape (relab f X) ≡ shape X
  shape-relab f (lt os cs) = cong node (shapes-relab f cs)

  shapes-relab : ∀ f cs → shapes (relabs f cs) ≡ shapes cs
  shapes-relab f []       = refl
  shapes-relab f (c ∷ cs) = cong₂ _∷_ (shape-relab f c) (shapes-relab f cs)

------------------------------------------------------------------------
-- The theorem.

private
  bind-just : ∀ {A B : Set} {m : Maybe A} {x} (k : A → Maybe B) → m ≡ just x → (m >>= k) ≡ k x
  bind-just k refl = refl

  -- y = o contradicts o ∉ X when y ∈ X
  ne-mem : ∀ y o (b : Nat → Bool) → b y ≡ true → b o ≡ false → (y ==ℕ o) ≡ false
  ne-mem y o b m n = ==-ne y o (λ h → t≢f (trans (sym m) (subst (λ z → b z ≡ false) (sym (==ℕ-sound y o (≡-T h))) n)))

module _ (Γ : Ctx) (σ : Sub) (n : Nat) (Θ : Ctx) (f : Nat → Nat) where

  J : Nat → Maybe LT
  J y = nf n Γ (lookupₛ σ y)

  Inv : Nat → LT → LT → List (Nat × LT) → Set
  Inv d R E as =
      (∀ y → mem y R ≡ true →
         Σ LT λ X → (find y as ≡ just X) × Ex Θ 0 nothing X × (J y ≡ just (relab f X))
                  × (∀ β j → T (j <ℕ d) → bd β j X ≡ bd β j E))
    × (flatG (λ y → find y as) d R ≡ just E)
    × BdOK (λ y → find y as) d R
    × (∀ y → memKey y as ≡ mem y R)

  Ends5 : Nat → List Nat → LT → List (Nat × LT) → Set
  Ends5 d os E as = (find (headN os) as ≡ just (bd false d E)) × (find (lastN os) as ≡ just (bd true d E))

  private
    wfx : ∀ X → Ex Θ 0 nothing X → WF X
    wfx X x = ex-wf Θ 0 nothing X x

    relab-b : ∀ β d X aX → Ex Θ 0 nothing X → relab f X ≡ aX → relab f (bd β d X) ≡ bd β d aX
    relab-b β d X aX x r = trans (relab-bd f β d X (wfx X x)) (cong (bd β d) r)

  private
    unfold-C : ∀ d o o' os c c' cs E a asc bs → flat n Γ σ (suc d) c ≡ just a →
               assign n Γ σ (suc d) c (fst (split d a E)) ≡ just asc →
               assignCs n Γ σ d (o' ∷ os) c' cs (snd (split d a E)) ≡ just bs →
               assignCs n Γ σ d (o ∷ o' ∷ os) c (c' ∷ cs) E ≡ just (((o , bd false d (fst (split d a E))) ∷ asc) ++ bs)
    unfold-C d o o' []        c c' cs E a asc bs fl e₁ e₂ rewrite fl | e₁ | e₂ = refl
    unfold-C d o o' (_ ∷ _)   c c' cs E a asc bs fl e₁ e₂ rewrite fl | e₁ | e₂ = refl

  mutual
    assign-ok : ∀ d P R E aT → Good J d P R → flatG J d R ≡ just aT → relab f E ≡ aT →
                Ex Θ 0 nothing E → ND R →
                Σ (List (Nat × LT)) λ as → (assign n Γ σ d R E ≡ just as) × Inv d R E as
    assign-ok d P (lt (y ∷ []) []) E aT g e r x nd = ((y , E) ∷ []) , refl , i1 , find-here y E [] , tt , i4
      where
      i1 : ∀ y' → mem y' (lt (y ∷ []) []) ≡ true → _
      i1 y' m with y' ==ℕ y in eq
      ... | true rewrite ==ℕ-sound y' y (≡-T eq) =
        E , find-here y E [] , x , trans e (cong just (sym r)) , (λ β j p → refl)
      i1 y' () | false

      i4 : ∀ y' → memKey y' ((y , E) ∷ []) ≡ mem y' (lt (y ∷ []) [])
      i4 y' = sh1 (y' ==ℕ y)
    assign-ok d P (lt [] [])               E aT (_ , ()) e r x nd
    assign-ok d P (lt (y ∷ y' ∷ ys) [])    E aT (_ , ()) e r x nd
    assign-ok d P (lt [] (c ∷ cs))         E aT (_ , ()) e r x nd
    assign-ok d P (lt (o ∷ []) (c ∷ cs))   E aT (_ , ()) e r x nd
    assign-ok d P (lt (o ∷ o' ∷ os) (c ∷ cs)) E aT g e r x nd
      with assignCs-ok d P o (o' ∷ os) c cs E aT g e r x nd
    ... | as , ea , inv , _ = as , ea , inv

    assignCs-ok : ∀ d P o os c cs E aT → Good J d P (lt (o ∷ os) (c ∷ cs)) → flatGL J d c cs ≡ just aT →
                  relab f E ≡ aT → Ex Θ 0 nothing E → ND (lt (o ∷ os) (c ∷ cs)) →
                  Σ (List (Nat × LT)) λ as → (assignCs n Γ σ d (o ∷ os) c cs E ≡ just as)
                    × Inv d (lt (o ∷ os) (c ∷ cs)) E as × Ends5 d (o ∷ os) E as
    assignCs-ok d P o []        c cs E aT (_ , ()) e r x nd
    assignCs-ok d P o (o' ∷ []) c [] E aT (oks , gc , tt) e r x ((o∉ , _) , dis , (ndc , _ , _))
      with assign-ok (suc d) (Par J d o o') c E aT gc e r x ndc
    ... | asc , ea , (i1c , i2c , i3c , i4c) rewrite ea = as , refl , (i1 , i2 , i3 , i4) , (first , last)
      where
      as = (o , bd false d E) ∷ (o' , bd true d E) ∷ asc
      Pf = λ y → find y as
      par = flat-ends J d o o' c aT gc e

      o≠o' : (o' ==ℕ o) ≡ false
      o≠o' = ne-mem o' o (λ z → memL z (o' ∷ [])) (∨-inl _ _ (==-self o')) o∉

      c-o : ∀ y → mem y c ≡ true → (y ==ℕ o) ≡ false
      c-o y m = ne-mem y o (λ z → mem z c) m (fst (∨-false _ _ (dis o (∨-inl _ _ (==-self o)))))

      c-o' : ∀ y → mem y c ≡ true → (y ==ℕ o') ≡ false
      c-o' y m = ne-mem y o' (λ z → mem z c) m
                   (fst (∨-false _ _ (dis o' (∨-inr (o' ==ℕ o) _ (∨-inl _ _ (==-self o'))))))

      tr : ∀ y → mem y c ≡ true → find y as ≡ find y asc
      tr y m rewrite c-o y m | c-o' y m = refl

      first : find o as ≡ just (bd false d E)
      first = find-here o (bd false d E) ((o' , bd true d E) ∷ asc)

      last : find o' as ≡ just (bd true d E)
      last rewrite o≠o' = find-here o' (bd true d E) asc

      i1 : ∀ y → mem y (lt (o ∷ o' ∷ []) (c ∷ [])) ≡ true → _
      i1 y m with y ==ℕ o in eo
      ... | true rewrite ==ℕ-sound y o (≡-T eo) =
        bd false d E , first , ex-bd Θ false d 0 nothing E x ,
        trans (fst par) (cong just (sym (relab-b false d E aT x r))) , (λ β j p → bd-bd β false j d E p)
      ... | false with y ==ℕ o' in eo'
      ...   | true rewrite ==ℕ-sound y o' (≡-T eo') =
        bd true d E , last , ex-bd Θ true d 0 nothing E x ,
        trans (snd par) (cong just (sym (relab-b true d E aT x r))) , (λ β j p → bd-bd β true j d E p)
      ...   | false with ∨-split (mem y c) false m
      ...     | inr ()
      ...     | inl mc with i1c y mc
      ...       | X , fX , xX , jX , bX =
        X , trans (tr y mc) fX , xX , jX , (λ β j p → bX β j (lt-weak j d p))

      i2 : flatG Pf d (lt (o ∷ o' ∷ []) (c ∷ [])) ≡ just E
      i2 = trans (flatG-cong Pf (λ y → find y asc) (suc d) c (lab-of-mem _ c tr)) i2c

      i3 : BdOK Pf d (lt (o ∷ o' ∷ []) (c ∷ []))
      i3 = objs c (λ y m → m) , bdOK-cong (λ y → find y asc) Pf (suc d) c (λ y m → sym (tr y m)) i3c , tt
        where
        objs : ∀ c' → (∀ y → mem y c' ≡ true → mem y c ≡ true) → ObjB Pf d o o' c'
        objs (lt os' cs') h = go os' (λ y m → h y (∨-inl _ _ m))
          where
          go : ∀ xs → (∀ y → memL y xs ≡ true → mem y c ≡ true) →
               AllN (λ y → Σ LT λ X → (Pf y ≡ just X) × (Pf o ≡ just (bd false d X)) × (Pf o' ≡ just (bd true d X))) xs
          go []        h' = tt
          go (y ∷ xs) h' with i1c y (h' y (∨-inl _ _ (==-self y)))
          ... | X , fX , _ , _ , bX =
            (X , trans (tr y (h' y (∨-inl _ _ (==-self y)))) fX ,
                 trans first (cong just (sym (bX false d (lt-suc d)))) ,
                 trans last (cong just (sym (bX true d (lt-suc d))))) ,
            go xs (λ z m → h' z (∨-inr (z ==ℕ y) _ m))

      i4 : ∀ y → memKey y as ≡ mem y (lt (o ∷ o' ∷ []) (c ∷ []))
      i4 y rewrite i4c y = sh2 (y ==ℕ o) (y ==ℕ o') (mem y c)
    assignCs-ok d P o (o' ∷ []) c (c' ∷ cs) E aT (_ , _ , ()) e r x nd
    assignCs-ok d P o (o' ∷ o'' ∷ os) c [] E aT (_ , _ , ()) e r x nd
    assignCs-ok d P o (o' ∷ os) c (c' ∷ cs) E aT ((oko , oks) , gc , gr)
                e r x ((o∉ , ndos) , dis , (ndc , c∩ , ndcs))
      with bind-inv (flatG J (suc d) c) _ e
    ... | a , ea , e' with bind-inv (flatGL J d c' cs) _ e'
    ...   | b , eb , em
      with assign-ok (suc d) (Par J d o o') c (fst (split d a E)) a gc ea (cong fst rs) (fst xs) ndc
         | assignCs-ok d P o' os c' cs (snd (split d a E)) b (oks , gr) eb (cong snd rs) (snd xs) ndr
      where
      Rr = lt (o' ∷ os) (c' ∷ cs)
      gR : Good J d P Rr
      gR = oks , gr
      wa = fst (flat-bd J (suc d) (Par J d o o') c a gc ea)
      wb = fst (flat-bd J d P Rr b gR eb)
      cp : Compat d a b
      cp = trans (just-inj (trans (sym (snd (flat-ends J d o o' c a gc ea))) (snd (flat-bd J d P Rr b gR eb) false 0)))
                 (cong (λ k → bd false k b) (+0 d))
      mab : merge d a b ≡ aT
      mab = just-inj em
      fits : Fits d a b E
      fits = wa , wb , cp , wfx E x , trans (sym (shape-relab f E)) (cong shape (trans r (sym mab)))
      rs : (relab f (fst (split d a E)) , relab f (snd (split d a E))) ≡ (a , b)
      rs = trans (sym (relab-split f d a E)) (trans (cong (split d a) (trans r (sym mab))) (split-merge d a a b refl wa wb cp))
      xs = ex-split Θ d a b E 0 nothing fits x
      ndr : ND Rr
      ndr = ndos , (λ y m → snd (∨-false (mem y c) (memCs y (c' ∷ cs)) (dis y (∨-inr (y ==ℕ o) _ m)))) , ndcs
    ... | asc , eac , (i1c , i2c , i3c , i4c) | bs , eab , (i1r , i2r , i3r , i4r) , (hr , lr) =
      as , eq , (i1 , i2 , i3 , i4) , (first , last)
      where
      Rr = lt (o' ∷ os) (c' ∷ cs)
      R  = lt (o ∷ o' ∷ os) (c ∷ c' ∷ cs)
      gR : Good J d P Rr
      gR = oks , gr
      wa = fst (flat-bd J (suc d) (Par J d o o') c a gc ea)
      wb = fst (flat-bd J d P Rr b gR eb)
      cp : Compat d a b
      cp = trans (just-inj (trans (sym (snd (flat-ends J d o o' c a gc ea))) (snd (flat-bd J d P Rr b gR eb) false 0)))
                 (cong (λ k → bd false k b) (+0 d))
      mab : merge d a b ≡ aT
      mab = just-inj em
      fits : Fits d a b E
      fits = wa , wb , cp , wfx E x , trans (sym (shape-relab f E)) (cong shape (trans r (sym mab)))
      rs : (relab f (fst (split d a E)) , relab f (snd (split d a E))) ≡ (a , b)
      rs = trans (sym (relab-split f d a E)) (trans (cong (split d a) (trans r (sym mab))) (split-merge d a a b refl wa wb cp))
      Ea = fst (split d a E)
      Eb = snd (split d a E)
      xs = ex-split Θ d a b E 0 nothing fits x
      xa = fst xs
      xb = snd xs
      wEa = wfx Ea xa
      wEb = wfx Eb xb
      mE : merge d Ea Eb ≡ E
      mE = merge-split d a b E fits
      cpE : Compat d Ea Eb
      cpE = compat-split d a b E fits
      par = flat-ends J d o o' c a gc ea

      as = ((o , bd false d Ea) ∷ asc) ++ bs
      Pf = λ y → find y as

      eq : assignCs n Γ σ d (o ∷ o' ∷ os) c (c' ∷ cs) E ≡ just as
      eq = unfold-C d o o' os c c' cs E a asc bs (trans (flat-is-flatG n Γ σ (suc d) c) ea) eac eab

      -- boundaries below d
      low-a : ∀ β j → T (j <ℕ d) → bd β j Ea ≡ bd β j E
      low-a β j p = trans (sym (bd-merge-low β j d Ea Eb wEa wEb cpE p)) (cong (bd β j) mE)

      low-b : ∀ β j → T (j <ℕ d) → bd β j Eb ≡ bd β j E
      low-b β j p = trans (sym (bd-bd β false j d Eb p))
                    (trans (cong (bd β j) (sym cpE)) (trans (bd-bd β true j d Ea p) (low-a β j p)))

      -- where each label is found
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
      tc y m rewrite c-o y m = find-in y asc bs (trans (i4c y) m)

      trr : ∀ y → mem y Rr ≡ true → find y as ≡ find y bs
      trr y m rewrite r-o y m = find-out y asc bs (trans (i4c y) (r-c y m))

      first : find o as ≡ just (bd false d E)
      first = trans (find-here o (bd false d Ea) (asc ++ bs))
                    (cong just (trans (sym (bd-merge-src d Ea Eb wEa cpE)) (cong (bd false d) mE)))

      head-r : find o' as ≡ just (bd false d Eb)
      head-r = trans (trr o' (∨-inl _ _ (∨-inl _ _ (==-self o')))) hr

      last : find (lastN (o' ∷ os)) as ≡ just (bd true d E)
      last = trans (trr (lastN (o' ∷ os)) (∨-inl _ _ (memL-last o' os)))
               (trans lr (cong just (trans (sym (bd-merge-tgt d Ea Eb wEa wEb cpE)) (cong (bd true d) mE))))

      i1 : ∀ y → mem y R ≡ true →
           Σ LT λ X → (find y as ≡ just X) × Ex Θ 0 nothing X × (J y ≡ just (relab f X))
                    × (∀ β j → T (j <ℕ d) → bd β j X ≡ bd β j E)
      i1 y m with y ==ℕ o in eo
      ... | true rewrite ==ℕ-sound y o (≡-T eo) =
        bd false d Ea , refl , ex-bd Θ false d 0 nothing Ea xa ,
        trans (fst par) (cong just (sym (relab-b false d Ea a xa (cong fst rs)))) ,
        (λ β j p → trans (bd-bd β false j d Ea p) (low-a β j p))
      ... | false with mem y c in ec
      ...   | true with i1c y ec
      ...     | X , fX , xX , jX , bX =
        X , trans (find-in y asc bs (trans (i4c y) ec)) fX , xX , jX , (λ β j p → trans (bX β j (lt-weak j d p)) (low-a β j p))
      i1 y m | false | false with i1r y m
      ...     | X , fX , xX , jX , bX =
        X , trans (find-out y asc bs (trans (i4c y) (r-c y m))) fX , xX , jX , (λ β j p → trans (bX β j p) (low-b β j p))

      i2 : flatG Pf d R ≡ just E
      i2 = trans (bind-just _ (trans (flatG-cong Pf (λ y → find y asc) (suc d) c (lab-of-mem _ c tc)) i2c))
           (trans (bind-just _ (trans (flatG-cong Pf (λ y → find y bs) d Rr (lab-of-mem _ Rr trr)) i2r))
                  (cong just mE))

      i3 : BdOK Pf d R
      i3 = objs c (λ y m → m) ,
           bdOK-cong (λ y → find y asc) Pf (suc d) c (λ y m → sym (tc y m)) i3c ,
           bdOK-cong (λ y → find y bs) Pf d Rr (λ y m → sym (trr y m)) i3r
        where
        objs : ∀ c'' → (∀ y → mem y c'' ≡ true → mem y c ≡ true) → ObjB Pf d o o' c''
        objs (lt os' cs') h = go os' (λ y m → h y (∨-inl _ _ m))
          where
          go : ∀ zs → (∀ y → memL y zs ≡ true → mem y c ≡ true) →
               AllN (λ y → Σ LT λ X → (Pf y ≡ just X) × (Pf o ≡ just (bd false d X)) × (Pf o' ≡ just (bd true d X))) zs
          go []        h' = tt
          go (y ∷ zs) h' with i1c y (h' y (∨-inl _ _ (==-self y)))
          ... | X , fX , _ , _ , bX =
            (X , trans (tc y (h' y (∨-inl _ _ (==-self y)))) fX ,
                 trans (find-here o (bd false d Ea) (asc ++ bs)) (cong just (sym (bX false d (lt-suc d)))) ,
                 trans head-r (cong just (trans (sym cpE) (sym (bX true d (lt-suc d)))))) ,
            go zs (λ z m → h' z (∨-inr (z ==ℕ y) _ m))

      i4 : ∀ y → memKey y as ≡ mem y R
      i4 y rewrite memKey-++ y asc bs | i4c y | i4r y =
        sh3 (y ==ℕ o) (mem y c) (memL y (o' ∷ os)) (memCs y (c' ∷ cs))
