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
