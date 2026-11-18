------------------------------------------------------------------------
-- Top-degree facts about the hom K(Γ)(first, last) of a pasting
-- context, used for the coherence case of strict-model soundness.
--
--   * A composable tuple from the first to the last object takes one
--     cell from each hom in order, so its degree is at most
--     d = dimK (homs Γ) (`deg-bound`), and a tuple of degree d takes a
--     top-dimensional cell from every hom (`top-shape`).
------------------------------------------------------------------------
module CaTTExp.Strict.TopCell where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Tensor
open import CaTTExp.Strict.Pasting
open import CaTTExp.Strict.Bridge
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Arithmetic.

suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
suc-inj refl = refl

subst₂ : ∀ {A B : Set} (P : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → P a b → P a' b'
subst₂ P refl refl p = p

le-+l : ∀ A B → T (B <ℕ suc (A + B))
le-+l zero    B = n<suc B
le-+l (suc A) B = <-suc B (suc (A + B)) (le-+l A B)

lt-le-absurd : ∀ x y → T (x <ℕ y) → T (y <ℕ suc x) → ⊥
lt-le-absurd zero    zero    () _
lt-le-absurd zero    (suc y) _ ()
lt-le-absurd (suc x) zero    () _
lt-le-absurd (suc x) (suc y) p q = lt-le-absurd x y p q

le-add : ∀ a A b B → T (a <ℕ suc A) → T (b <ℕ suc B) → T ((a + b) <ℕ suc (A + B))
le-add zero    A       b B p q = le-trans b B (A + B) q (le-+l A B)
le-add (suc a) zero    b B () q
le-add (suc a) (suc A) b B p q = le-add a A b B p q

eq-split : ∀ a A b B → T (a <ℕ suc A) → T (b <ℕ suc B) → a + b ≡ A + B → (a ≡ A) × (b ≡ B)
eq-split zero    zero    b B p q e = refl , e
eq-split zero    (suc A) b B p q e =
  ⊥-elim (lt-le-absurd (A + B) B (subst (λ z → T (z <ℕ suc B)) e q) (le-+l A B))
eq-split (suc a) zero    b B () q e
eq-split (suc a) (suc A) b B p q e with eq-split a A b B p q (suc-inj e)
... | refl , e' = refl , e'

------------------------------------------------------------------------
-- Pairs of consecutive objects.

∈-pairs-fst : ∀ {e} xs → e ∈ pairs xs → fst e ∈ xs
∈-pairs-fst (x ∷ y ∷ zs) hd∈     = hd∈
∈-pairs-fst (x ∷ y ∷ zs) (tl∈ m) = tl∈ (∈-pairs-fst (y ∷ zs) m)

-- In a strictly increasing list, a pair is determined by its source.
pairs-unique-src : ∀ xs {a c c'} → Inc xs → (a , c) ∈ pairs xs → (a , c') ∈ pairs xs → c ≡ c'
pairs-unique-src (x ∷ y ∷ zs) _         hd∈     hd∈      = refl
pairs-unique-src (x ∷ y ∷ zs) (ax , _)  hd∈     (tl∈ m)  = ⊥-elim (lt-irr x (AllL-∈ (y ∷ zs) ax (∈-pairs-fst (y ∷ zs) m)))
pairs-unique-src (x ∷ y ∷ zs) (ax , _)  (tl∈ m) hd∈      = ⊥-elim (lt-irr x (AllL-∈ (y ∷ zs) ax (∈-pairs-fst (y ∷ zs) m)))
pairs-unique-src (x ∷ y ∷ zs) (_ , iy)  (tl∈ m) (tl∈ m') = pairs-unique-src (y ∷ zs) iy m m'

pairs-last : ∀ {e} pre a → e ∈ pairs (pre ++ a ∷ []) → fst e ∈ pre
pairs-last (x ∷ [])    a hd∈     = hd∈
pairs-last (x ∷ y ∷ p) a hd∈     = hd∈
pairs-last (x ∷ y ∷ p) a (tl∈ m) = tl∈ (pairs-last (y ∷ p) a m)
pairs-last []          a ()
pairs-last (x ∷ [])    a (tl∈ ())

lastL-∈ : ∀ x xs → lastL (x ∷ xs) ∈ (x ∷ xs)
lastL-∈ x []       = hd∈
lastL-∈ x (y ∷ ys) = tl∈ (lastL-∈ y ys)

Inc-drop : ∀ pre xs → Inc (pre ++ xs) → Inc xs
Inc-drop []        xs i        = i
Inc-drop (x ∷ pre) xs (_ , i) = Inc-drop pre xs i

------------------------------------------------------------------------
-- A composable tuple walks through the homs in order.

-- Entry j lies in hom k + j and is bounded by its dimension.
Walk : Ctx → Nat → Tuple → Set
Walk Γ k []      = ⊤
Walk Γ k (v ∷ w) = T (hdimV Γ v <ℕ suc (hd (homAt Γ k))) × Walk Γ (suc k) w

walk : ∀ {Γ} (P : Γ ⊢ps) pre o rest → objL Γ ≡ pre ++ o ∷ rest → ∀ w →
       WFT Γ o (lastL (o ∷ rest)) w → (lengthN w ≡ lengthN rest) × Walk Γ (suc (lengthN pre)) w
walk P pre o []         eq []      _ = refl , tt
walk {Γ} P pre o (o' ∷ r) eq []    e =
  ⊥-elim (lt-irr o (AllL-∈ (o' ∷ r) (fst (Inc-drop pre (o ∷ o' ∷ r) (subst Inc eq (Inc-objL Γ))))
                     (subst (λ z → z ∈ (o' ∷ r)) (sym e) (lastL-∈ o' r))))
walk {Γ} P pre o []       eq (v ∷ w) (z , ev , p) =
  ⊥-elim (lt-irr o (AllL-∈ pre (Inc-before pre o [] inc) (pairs-last pre o mem)))
  where
  inc = subst Inc eq (Inc-objL Γ)
  mem = subst (λ xs → (o , z) ∈ pairs xs) eq (hom-ends P v ev)
walk {Γ} P pre o (o' ∷ r) eq (v ∷ w) (z , ev , p)
  with pairs-unique-src _ (subst Inc eq (Inc-objL Γ)) (subst (λ xs → (o , z) ∈ pairs xs) eq (hom-ends P v ev))
                        (pairs-mid pre o o' r)
... | refl with endsL-inv (lookup Γ v) ev
...   | (A , lv , evA) =
  cong suc (fst rec) ,
  subst T (cong (λ m → m <ℕ suc (hd (homAt Γ (suc (lengthN pre))))) (cong hdimTy (sym lv)))
        (OneHom.v-bound P pre o o' r eq v A lv evA) ,
  subst (λ j → Walk Γ (suc j) w) (lengthN-snoc pre o) (snd rec)
  where
  rec = walk P (pre ++ o ∷ []) o' r (trans eq (sym (++-assocL pre (o ∷ []) (o' ∷ r)))) w p

------------------------------------------------------------------------
-- Degrees.

sumHd : Ctx → Nat → Nat → Nat
sumHd Γ k zero    = 0
sumHd Γ k (suc m) = hd (homAt Γ k) + sumHd Γ (suc k) m

deg-le : ∀ Γ k w → Walk Γ k w → T (deg Γ w <ℕ suc (sumHd Γ k (lengthN w)))
deg-le Γ k []      _        = tt
deg-le Γ k (v ∷ w) (b , ws) = le-add (hdimV Γ v) _ (deg Γ w) _ b (deg-le Γ (suc k) w ws)

AllTop : Ctx → Nat → Tuple → Set
AllTop Γ k []      = ⊤
AllTop Γ k (v ∷ w) = (hdimV Γ v ≡ hd (homAt Γ k)) × AllTop Γ (suc k) w

deg-top : ∀ Γ k w → Walk Γ k w → deg Γ w ≡ sumHd Γ k (lengthN w) → AllTop Γ k w
deg-top Γ k []      _        _ = tt
deg-top Γ k (v ∷ w) (b , ws) e with eq-split (hdimV Γ v) _ (deg Γ w) _ b (deg-le Γ (suc k) w ws) e
... | e1 , e2 = e1 , deg-top Γ (suc k) w ws e2

dimK-seq : ∀ Γ k m → dimK (map (homAt Γ) (seq k m)) ≡ sumHd Γ k m
dimK-seq Γ k zero    = refl
dimK-seq Γ k (suc m) = cong (hd (homAt Γ k) +_) (dimK-seq Γ (suc k) m)

-- The objects and the dimension of a pasting context.
record Shape (Γ : Ctx) : Set where
  field
    o    : Nat
    rest : List Nat
    eqo  : objL Γ ≡ o ∷ rest
    eqd  : dimK (homs Γ) ≡ sumHd Γ 1 (lengthN rest)
    efst : firstL (objs Γ) ≡ o
    elst : lastL (objs Γ) ≡ lastL (o ∷ rest)

shape : ∀ {Γ} → Γ ⊢ps → Shape Γ
shape {Γ} P with objL Γ in eq
... | []       = ⊥-elim (subst NonEmpty eq (hom-ne P))
... | o ∷ rest = record
  { o = o ; rest = rest ; eqo = eq
  ; eqd = trans (cong (λ os → dimK (map (homAt Γ) (drop1 (upto (lengthN os))))) (trans (objs-objL Γ) eq))
                (trans (cong (λ js → dimK (map (homAt Γ) js)) (drop1-upto (lengthN rest))) (dimK-seq Γ 1 (lengthN rest)))
  ; efst = cong firstL (trans (objs-objL Γ) eq)
  ; elst = cong lastL (trans (objs-objL Γ) eq) }

-- Every basis element from the first to the last object has degree ≤ d.
deg-bound : ∀ {Γ} → Γ ⊢ps → ∀ w k → Basis Γ (firstL (objs Γ)) (lastL (objs Γ)) k w →
            T (k <ℕ suc (dimK (homs Γ)))
deg-bound {Γ} P w k (wf , dk) =
  subst (λ z → T (z <ℕ suc (dimK (homs Γ)))) dk
    (subst (λ z → T (deg Γ w <ℕ suc z)) (sym eqd)
      (subst (λ m → T (deg Γ w <ℕ suc (sumHd Γ 1 m))) (fst W) (deg-le Γ 1 w (snd W))))
  where
  open Shape (shape P)
  W = walk P [] o rest eqo w (subst₂ (λ a b → WFT Γ a b w) efst elst wf)

-- A basis element of degree d takes a top cell from every hom.
top-shape : ∀ {Γ} → Γ ⊢ps → ∀ w → Basis Γ (firstL (objs Γ)) (lastL (objs Γ)) (dimK (homs Γ)) w →
            AllTop Γ 1 w
top-shape {Γ} P w (wf , dk) =
  deg-top Γ 1 w (snd W) (trans dk (trans eqd (cong (sumHd Γ 1) (sym (fst W)))))
  where
  open Shape (shape P)
  W = walk P [] o rest eqo w (subst₂ (λ a b → WFT Γ a b w) efst elst wf)

------------------------------------------------------------------------
-- Order facts about faces in a pasting context.
--
--   fl : a cell's source comes before its target;
--   sl : a cell whose source is the target of α comes after α;
--   tu : two cells with the same target that are sources of nothing
--        are equal.

record Facts (Γ : Ctx) : Set where
  field
    fl : ∀ v {s t} → facesTy (lookup Γ v) ≡ just (s , t) → T (s <ℕ t)
    sl : ∀ α β {s t u} → facesTy (lookup Γ α) ≡ just (s , t) → facesTy (lookup Γ β) ≡ just (t , u) → T (α <ℕ β)
    tu : ∀ α α' {s s' t} → facesTy (lookup Γ α) ≡ just (s , t) → facesTy (lookup Γ α') ≡ just (s' , t) →
         NotSrc Γ α → NotSrc Γ α' → α ≡ α'

private
  data View (Γ : Ctx) (A F : Ty) (v : Nat) : Maybe Ty → Set where
    old : View Γ A F v (lookup Γ v)
    isy : v ≡ len Γ → View Γ A F v (just A)
    isf : v ≡ suc (len Γ) → View Γ A F v (just F)

  view : ∀ Γ A F v → View Γ A F v (lookup (Γ ▸ A ▸ F) v)
  view Γ A F v with v ==ℕ suc (len Γ) in e1
  ... | true  = isf (==→≡ v _ e1)
  ... | false with v ==ℕ len Γ in e2
  ...   | true  = isy (==→≡ v _ e2)
  ...   | false = old

  lt-trans' : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  lt-trans' zero    (suc b) (suc c) _ _ = tt
  lt-trans' (suc a) (suc b) (suc c) p q = lt-trans' a b c p q
  lt-trans' zero    zero    c       () _
  lt-trans' (suc a) zero    c       () _
  lt-trans' a       (suc b) zero    _ ()

  lt-neq : ∀ a b → T (a <ℕ b) → a ≡ b → ⊥
  lt-neq a .a p refl = lt-irr a p

  true≢false' : true ≡ false → ⊥
  true≢false' ()

  just-pair : ∀ {a b c d : Nat} → just (a , b) ≡ just (c , d) → (a ≡ c) × (b ≡ d)
  just-pair refl = refl , refl

  hit-self : ∀ Γ v {s t} → facesTy (lookup Γ v) ≡ just (s , t) → hitB Γ true s v ≡ true
  hit-self Γ v {s} e rewrite e = ==-true s

  notsrc-old : ∀ Γ A F v → NotSrc (Γ ▸ A ▸ F) v → NotSrc Γ v
  notsrc-old Γ A F v ns w lt =
    trans (cong (λ m → hitM true v (facesTy m)) (sym (trans (lookup-old (Γ ▸ A) F w (<-suc w (len Γ) lt)) (lookup-old Γ A w lt))))
          (ns w (<-suc w (suc (len Γ)) (<-suc w (len Γ) lt)))

  fF : ∀ A x y {s t} → facesTy (just A) ≡ just (s , t) → facesTy (just (arr A (var x) (var y))) ≡ just (x , y)
  fF ⋆           x y ()
  fF (arr _ _ _) x y e = refl

  ffA : ∀ A x y {s t} → facesTy (just (arr A (var x) (var y))) ≡ just (s , t) → (s ≡ x) × (t ≡ y)
  ffA ⋆           x y ()
  ffA (arr _ _ _) x y e = sym (fst (just-pair e)) , sym (snd (just-pair e))

module PseFacts {Γ : Ctx} {x : Nat} {A : Ty} (d : Γ ⊢ps x ∶ A) (I : Facts Γ) where
  open Facts I
  y = len Γ
  F = arr A (var x) (var y)
  Γ' = Γ ▸ A ▸ F
  invΓ = fst (ps-inv d)
  lx : lookup Γ x ≡ just A
  lx = snd (ps-inv d)
  x<y : T (x <ℕ y)
  x<y = lookup-lt Γ x lx
  IΓ = inv-ps d

  old-lt : ∀ v {s t} → facesTy (lookup Γ v) ≡ just (s , t) → T (v <ℕ len Γ)
  old-lt v e with lookup Γ v in lv
  old-lt v () | nothing
  old-lt v e  | just C = lookup-lt Γ v lv

  -- the faces of y are those of x
  fy : ∀ {s t} → facesTy (just A) ≡ just (s , t) → facesTy (lookup Γ x) ≡ just (s , t)
  fy e = trans (cong facesTy lx) e

  -- the faces of f are x and y
  ff : ∀ {s t} → facesTy (just F) ≡ just (s , t) → (s ≡ x) × (t ≡ y)
  ff = ffA A x y

  fl' : ∀ v {s t} → facesTy (lookup Γ' v) ≡ just (s , t) → T (s <ℕ t)
  fl' v e = go (lookup Γ' v) (view Γ A F v) e
    where
    go : ∀ m → View Γ A F v m → ∀ {s t} → facesTy m ≡ just (s , t) → T (s <ℕ t)
    go _ old       e = fl v e
    go _ (isy _)   e = fl x (fy e)
    go _ (isf _)   e with ff e
    ... | refl , refl = x<y

  -- the target of y is not the source of an old cell
  tgt-y : ∀ {s t} → facesTy (just A) ≡ just (s , t) → NotSrc Γ t
  tgt-y {s} {t} e = go A (Inv.tch IΓ) e
    where
    go : ∀ B → TgtChain Γ B → facesTy (just B) ≡ just (s , t) → NotSrc Γ t
    go ⋆ _ ()
    go (arr ⋆ _ _) _ ()
    go (arr (arr B a b) (var s₀) (var c)) (ns , _) refl = ns
    go (arr (arr B a b) (var s₀) (coh _ _ _)) () _
    go (arr (arr B a b) (var s₀) (cst ())) _ _
    go (arr (arr B a b) (coh _ _ _) _) _ ()
    go (arr (arr B a b) (cst ()) _) _ _

  sl' : ∀ α β {s t u} → facesTy (lookup Γ' α) ≡ just (s , t) → facesTy (lookup Γ' β) ≡ just (t , u) → T (α <ℕ β)
  sl' α β eα eβ = go (lookup Γ' α) (view Γ A F α) (lookup Γ' β) (view Γ A F β) eα eβ
    where
    go : ∀ mα → View Γ A F α mα → ∀ mβ → View Γ A F β mβ → ∀ {s t u} →
         facesTy mα ≡ just (s , t) → facesTy mβ ≡ just (t , u) → T (α <ℕ β)
    go _ old _ old eα eβ = sl α β eα eβ
    go _ old _ (isy refl) eα eβ = old-lt α eα
    go _ old _ (isf refl) eα eβ = <-suc α (len Γ) (old-lt α eα)
    go _ (isy refl) _ old {s} {t} eα eβ =
      ⊥-elim (true≢false' (trans (sym (hit-self Γ β eβ)) (tgt-y eα β (old-lt β eβ))))
    go _ (isy refl) _ (isy refl) eα eβ =
      ⊥-elim (lt-neq _ _ (fl x (fy eα)) (fst (just-pair (trans (sym eα) eβ))))
    go _ (isy refl) _ (isf refl) eα eβ = n<suc (len Γ)
    go _ (isf refl) _ old eα eβ with ff eα
    ... | refl , refl = ⊥-elim (lt-irr (len Γ) (fst (faces-lt Γ invΓ β eβ)))
    go _ (isf refl) _ (isy refl) eα eβ with ff eα
    ... | refl , refl = ⊥-elim (lt-irr (len Γ) (fst (faces-lt Γ invΓ x (fy eβ))))
    go _ (isf refl) _ (isf refl) eα eβ with ff eα | ff eβ
    ... | refl , refl | e , _ = ⊥-elim (lt-neq _ _ x<y (sym e))

  -- once A has faces, x is the source of f
  x-src : ∀ {s t} → facesTy (just A) ≡ just (s , t) → NotSrc Γ' x → ⊥
  x-src e ns =
    true≢false' (trans (sym (==-true x))
                (trans (sym (cong (hitM true x) (fF A x y e)))
                (trans (sym (cong (λ m → hitM true x (facesTy m)) (lookup-new (Γ ▸ A) F)))
                       (ns (suc (len Γ)) (n<suc (suc (len Γ)))))))

  tu' : ∀ α α' {s s' t} → facesTy (lookup Γ' α) ≡ just (s , t) → facesTy (lookup Γ' α') ≡ just (s' , t) →
        NotSrc Γ' α → NotSrc Γ' α' → α ≡ α'
  tu' α α' eα eα' nα nα' = go (lookup Γ' α) (view Γ A F α) (lookup Γ' α') (view Γ A F α') eα eα'
    where
    go : ∀ m → View Γ A F α m → ∀ m' → View Γ A F α' m' → ∀ {s s' t} →
         facesTy m ≡ just (s , t) → facesTy m' ≡ just (s' , t) → α ≡ α'
    go _ old _ old e e' = tu α α' e e' (notsrc-old Γ A F α nα) (notsrc-old Γ A F α' nα')
    go _ old _ (isy refl) e e' with tu α x e (fy e') (notsrc-old Γ A F α nα) (Inv.nsx IΓ)
    ... | refl = ⊥-elim (x-src e' nα)
    go _ old _ (isf refl) e e' with ff e'
    ... | _ , refl = ⊥-elim (lt-irr (len Γ) (snd (faces-lt Γ invΓ α e)))
    go _ (isy refl) _ old e e' with tu α' x e' (fy e) (notsrc-old Γ A F α' nα') (Inv.nsx IΓ)
    ... | refl = ⊥-elim (x-src e nα')
    go _ (isy refl) _ (isy refl) e e' = refl
    go _ (isy refl) _ (isf refl) e e' with ff e'
    ... | _ , refl = ⊥-elim (lt-irr (len Γ) (snd (faces-lt Γ invΓ x (fy e))))
    go _ (isf refl) _ old e e' with ff e
    ... | _ , refl = ⊥-elim (lt-irr (len Γ) (snd (faces-lt Γ invΓ α' e')))
    go _ (isf refl) _ (isy refl) e e' with ff e
    ... | _ , refl = ⊥-elim (lt-irr (len Γ) (snd (faces-lt Γ invΓ x (fy e'))))
    go _ (isf refl) _ (isf refl) e e' = refl

facts : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Facts Γ
facts pss = record { fl = fl0 ; sl = sl0 ; tu = tu0 }
  where
  fl0 : ∀ v {s t} → facesTy (lookup (ε ▸ ⋆) v) ≡ just (s , t) → T (s <ℕ t)
  fl0 zero ()
  fl0 (suc v) ()
  sl0 : ∀ α β {s t u} → facesTy (lookup (ε ▸ ⋆) α) ≡ just (s , t) → facesTy (lookup (ε ▸ ⋆) β) ≡ just (t , u) → T (α <ℕ β)
  sl0 zero    _ ()
  sl0 (suc α) _ ()
  tu0 : ∀ α α' {s s' t} → facesTy (lookup (ε ▸ ⋆) α) ≡ just (s , t) → facesTy (lookup (ε ▸ ⋆) α') ≡ just (s' , t) →
        NotSrc (ε ▸ ⋆) α → NotSrc (ε ▸ ⋆) α' → α ≡ α'
  tu0 zero    _ ()
  tu0 (suc α) _ ()
facts (pse d) = record { fl = fl' ; sl = sl' ; tu = tu' }
  where open PseFacts d (facts d)
facts (psd d) = facts d

facts-ps : ∀ {Γ} → Γ ⊢ps → Facts Γ
facts-ps (ps d) = facts d
