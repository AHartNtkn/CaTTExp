------------------------------------------------------------------------
-- Gray tables: the reading of P's terms in the free Gray-enriched
-- category on a pasting diagram, at the level of supports (ledger S3a,
-- notes/uniform-checker.md §1.8 Route step 1).
--
-- An n-cell is read as a table: its 0-source and 0-target (`lo`, `hi`),
-- the supports of its i-source and i-target for 1 ≤ i < n (`s i`,
-- `t i`), and its top support. Supports are sets of tuples
-- (SuppAlg), as in Gray/Support.agda: composition along an object is
-- the concatenation product, composition along a higher cell is union.
-- On P's operations:
--
--   comp_n         top = top x · top y  (n = 1),  top x ∪ top y (n ≥ 2)
--   left/right_k   k = 1: every level and the top are products with
--                  the 1-cell's top; k ≥ 2: the k-level gains the
--                  k-cell's top, the rest is the n-cell's
--   id_n           top = the unit tuple (n = 0), empty (n ≥ 1)
--   χ, r, t        top = top x · top y   (the Gray tensor of the two)
--   h              top = top x · (2-target of y)
--   ι              top = empty            (strict in the Gray image)
--
-- and the lower levels of a comparison are those of its two boundary
-- terms (SigP.compBounds), evaluated in the same reading.
--
-- Every operation is given as a `Shape`: a recipe for each level from
-- the levels of its inputs, with ∪, ·, unit and empty. A table is
-- *clean*: levels outside 1 ≤ i < n, and the top of a 0-cell, are
-- empty, and a 0-cell has hi = lo. Tables are generic in the objects O
-- and the tuple letters K, so the same code reads terms concretely
-- (letters are generator names) and symbolically (letters are faces of
-- schema variables). The lemmas say that the reading is a congruence
-- (`ev-cong`) and commutes with interpreting the letters (`ev-hom`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.SuppAlg
open import CaTTExp.Uniform.SigP
open import Agda.Builtin.String using (String; primStringEquality)

module CaTTExp.Uniform.GrayTab where

record Tab (O K : Set) : Set where
  constructor tab
  field
    dm     : Nat
    lo hi  : O
    s t    : Nat → SExp K
    top    : SExp K
open Tab public

-- Equality of tables: same dimension and objects, same supports.
module _ {O K : Set} where
  infix 4 _≈T_
  _≈T_ : Tab O K → Tab O K → Set
  X ≈T Y = (dm X ≡ dm Y) × (lo X ≡ lo Y) × (hi X ≡ hi Y) ×
           (∀ l → s X l ≈S s Y l) × (∀ l → t X l ≈S t Y l) × (top X ≈S top Y)

  ≈T-refl : ∀ {X} → X ≈T X
  ≈T-refl = refl , refl , refl , (λ _ → ≈S-refl) , (λ _ → ≈S-refl) , ≈S-refl

  ≈T-sym : ∀ {X Y} → X ≈T Y → Y ≈T X
  ≈T-sym (a , b , c , d , e , f) = sym a , sym b , sym c , (λ l → ≈S-sym (d l)) , (λ l → ≈S-sym (e l)) , ≈S-sym f

  ≈T-trans : ∀ {X Y Z} → X ≈T Y → Y ≈T Z → X ≈T Z
  ≈T-trans (a , b , c , d , e , f) (a′ , b′ , c′ , d′ , e′ , f′) =
    trans a a′ , trans b b′ , trans c c′ , (λ l → ≈S-trans (d l) (d′ l)) ,
    (λ l → ≈S-trans (e l) (e′ l)) , ≈S-trans f f′

------------------------------------------------------------------------
-- Shapes.

infixr 25 _∪E_
infixr 26 _·E_

data LE : Set where
  sA tA      : Nat → Nat → LE      -- input, level
  topA       : Nat → LE
  _∪E_ _·E_  : LE → LE → LE
  εE ∅E      : LE

record Shape : Set where
  constructor shape
  field
    dmS       : Nat
    loR hiR   : Bool × Nat          -- (from hi?, input)
    sL tL     : Nat → LE
    topL      : LE
open Shape public

inR : Nat → Nat → Bool
inR l n = (0 <ℕ l) ∧ (l <ℕ n)

module _ {O K : Set} where
  evalLE : (Nat → Tab O K) → LE → SExp K
  evalLE ins (sA i l)  = s (ins i) l
  evalLE ins (tA i l)  = t (ins i) l
  evalLE ins (topA i)  = top (ins i)
  evalLE ins (a ∪E b)  = evalLE ins a ++ evalLE ins b
  evalLE ins (a ·E b)  = prodE (evalLE ins a) (evalLE ins b)
  evalLE ins εE        = [] ∷ []
  evalLE ins ∅E        = []

  obj : (Nat → Tab O K) → Bool × Nat → O
  obj ins (b , i) = if b then hi (ins i) else lo (ins i)

  apply : Shape → (Nat → Tab O K) → Tab O K
  apply sh ins = record
    { dm  = dmS sh
    ; lo  = obj ins (loR sh)
    ; hi  = if dmS sh ==ℕ 0 then obj ins (loR sh) else obj ins (hiR sh)
    ; s   = λ l → if inR l (dmS sh) then evalLE ins (sL sh l) else []
    ; t   = λ l → if inR l (dmS sh) then evalLE ins (tL sh l) else []
    ; top = if dmS sh ==ℕ 0 then [] else evalLE ins (topL sh)
    }

  in1 : Tab O K → Nat → Tab O K
  in1 X _ = X

  in2 : Tab O K → Tab O K → Nat → Tab O K
  in2 X Y i = if i ==ℕ 0 then X else Y

  in4 : Tab O K → Tab O K → Tab O K → Tab O K → Nat → Tab O K
  in4 S T X Y i = if i ==ℕ 0 then S else if i ==ℕ 1 then T else if i ==ℕ 2 then X else Y

------------------------------------------------------------------------
-- The shapes of P's operations.

faceSh : Bool → Nat → Shape
faceSh b n = shape (n ∸ 1) ((b ∧ ((n ∸ 1) ==ℕ 0)) , 0) (true , 0) (sA 0) (tA 0)
                   (if b then tA 0 (n ∸ 1) else sA 0 (n ∸ 1))

idSh : Nat → Shape
idSh n = shape (suc n) (false , 0) (true , 0)
               (λ l → if l ==ℕ n then topA 0 else sA 0 l)
               (λ l → if l ==ℕ n then topA 0 else tA 0 l)
               (if n ==ℕ 0 then εE else ∅E)

compSh : Nat → Shape
compSh n = shape n (false , 0) (true , 1) (sA 0) (tA 1)
                 (if n ==ℕ 1 then topA 0 ·E topA 1 else topA 0 ∪E topA 1)

private
  side : Bool → Nat → Nat → LE
  side b i l = if b then sA i l else tA i l

-- A k-cell (input 0) acting on the left of an n-cell (input 1).
lftSh : Nat → Nat → Shape
lftSh k n = shape n (false , 0) (true , 1) (lv true) (lv false)
                  (if k ==ℕ 1 then topA 0 ·E topA 1 else topA 1)
  where
  lv : Bool → Nat → LE
  lv b l = if l <ℕ k then (if b then sA 0 l else tA 1 l)
           else if k ==ℕ 1 then topA 0 ·E side b 1 l
           else if l ==ℕ k then topA 0 ∪E side b 1 l
           else side b 1 l

-- An n-cell (input 0) acted on the right by a k-cell (input 1).
rgtSh : Nat → Nat → Shape
rgtSh k n = shape n (false , 0) (true , 1) (lv true) (lv false)
                  (if k ==ℕ 1 then topA 0 ·E topA 1 else topA 0)
  where
  lv : Bool → Nat → LE
  lv b l = if l <ℕ k then (if b then sA 0 l else tA 1 l)
           else if k ==ℕ 1 then side b 0 l ·E topA 1
           else if l ==ℕ k then side b 0 l ∪E topA 1
           else side b 0 l

cmpTop : CmpOp → LE
cmpTop iotaO = ∅E
cmpTop hO    = topA 2 ·E tA 3 2
cmpTop _     = topA 2 ·E topA 3

-- Inputs: the boundary tables S, T, then the arguments x, y.
cmpSh : CmpOp → Shape
cmpSh o = shape d (false , 0) (true , 1)
                (λ l → if l ==ℕ (d ∸ 1) then topA 0 else sA 0 l)
                (λ l → if l ==ℕ (d ∸ 1) then topA 1 else tA 1 l)
                (cmpTop o)
  where d = cmpDim o

------------------------------------------------------------------------
-- Evaluation of terms, given the generators' tables and a reading of
-- the comparisons.

module Eval {O K : Set} (gen : Nat → String → Tab O K)
            (cm : CmpOp → Tab O K → Tab O K → Tab O K) where
  ev : Tm → Tab O K
  ev (v d x)       = gen d x
  ev (sF n x)      = apply (faceSh false n) (in1 (ev x))
  ev (tF n x)      = apply (faceSh true n) (in1 (ev x))
  ev (idT n x)     = apply (idSh n) (in1 (ev x))
  ev (comp n x y)  = apply (compSh n) (in2 (ev x) (ev y))
  ev (lft k n x y) = apply (lftSh k n) (in2 (ev x) (ev y))
  ev (rgt k n x y) = apply (rgtSh k n) (in2 (ev x) (ev y))
  ev (cmp o x y)   = cm o (ev x) (ev y)

-- The argument dimensions of each comparison.
argDims : CmpOp → Nat × Nat
argDims chiO  = 2 , 2
argDims rO    = 3 , 2
argDims tO    = 2 , 3
argDims iotaO = 3 , 3
argDims hO    = 3 , 3

bounds : CmpOp → Tm × Tm
bounds o = compBounds o (v (fst (argDims o)) "x0") (v (snd (argDims o)) "x1")

module _ {O K : Set} where
  env : Tab O K → Tab O K → Nat → String → Tab O K
  env X Y _ nm = if primStringEquality nm "x0" then X else Y

  mkCmp : CmpOp → (CmpOp → Tab O K → Tab O K → Tab O K) → Tab O K → Tab O K → Tab O K
  mkCmp o inner X Y =
    apply (cmpSh o) (in4 (Eval.ev (env X Y) inner (fst (bounds o)))
                         (Eval.ev (env X Y) inner (snd (bounds o))) X Y)

  -- χ's boundaries contain no comparison; those of r, t and h contain
  -- only χ; ι's contain none.
  cmNone : CmpOp → Tab O K → Tab O K → Tab O K
  cmNone _ X _ = X

  cmChi : Tab O K → Tab O K → Tab O K
  cmChi = mkCmp chiO cmNone

  cmOnlyChi : CmpOp → Tab O K → Tab O K → Tab O K
  cmOnlyChi chiO = cmChi
  cmOnlyChi _    = cmNone chiO

  cmAll : CmpOp → Tab O K → Tab O K → Tab O K
  cmAll chiO = cmChi
  cmAll o    = mkCmp o cmOnlyChi

-- The leaves of a term.
leaves : Tm → List (Nat × String)
leaves (v d x)       = (d , x) ∷ []
leaves (sF _ x)      = leaves x
leaves (tF _ x)      = leaves x
leaves (idT _ x)     = leaves x
leaves (comp _ x y)  = leaves x ++ leaves y
leaves (lft _ _ x y) = leaves x ++ leaves y
leaves (rgt _ _ x y) = leaves x ++ leaves y
leaves (cmp _ x y)   = leaves x ++ leaves y

------------------------------------------------------------------------
-- Congruence.

private
  if-cong : ∀ {A : Set} (R : A → A → Set) b {x x′ y y′} → R x x′ → R y y′ →
            R (if b then x else y) (if b then x′ else y′)
  if-cong R true  p q = p
  if-cong R false p q = q

  if-map : ∀ {A B : Set} (f : A → B) b {x y} → f (if b then x else y) ≡ (if b then f x else f y)
  if-map f true  = refl
  if-map f false = refl

module _ {O K : Set} where
  evalLE-cong : ∀ {ins ins′ : Nat → Tab O K} → (∀ i → ins i ≈T ins′ i) →
                ∀ e → evalLE ins e ≈S evalLE ins′ e
  evalLE-cong h (sA i l)  = fst (snd (snd (snd (h i)))) l
  evalLE-cong h (tA i l)  = fst (snd (snd (snd (snd (h i))))) l
  evalLE-cong h (topA i)  = snd (snd (snd (snd (snd (h i)))))
  evalLE-cong h (a ∪E b)  = ∪-cong (evalLE-cong h a) (evalLE-cong h b)
  evalLE-cong {ins} {ins′} h (a ·E b) =
    prod-cong (evalLE ins a) (evalLE ins′ a) (evalLE ins b) (evalLE ins′ b) (evalLE-cong h a) (evalLE-cong h b)
  evalLE-cong h εE = ≈S-refl
  evalLE-cong h ∅E = ≈S-refl

  obj-cong : ∀ {ins ins′ : Nat → Tab O K} → (∀ i → ins i ≈T ins′ i) → ∀ r → obj ins r ≡ obj ins′ r
  obj-cong h (true , i)  = fst (snd (snd (h i)))
  obj-cong h (false , i) = fst (snd (h i))

  apply-cong : ∀ sh {ins ins′ : Nat → Tab O K} → (∀ i → ins i ≈T ins′ i) → apply sh ins ≈T apply sh ins′
  apply-cong sh h =
    refl , obj-cong h (loR sh) ,
    if-cong _≡_ (dmS sh ==ℕ 0) (obj-cong h (loR sh)) (obj-cong h (hiR sh)) ,
    (λ l → if-cong _≈S_ (inR l (dmS sh)) (evalLE-cong h (sL sh l)) ≈S-refl) ,
    (λ l → if-cong _≈S_ (inR l (dmS sh)) (evalLE-cong h (tL sh l)) ≈S-refl) ,
    if-cong _≈S_ (dmS sh ==ℕ 0) ≈S-refl (evalLE-cong h (topL sh))

  in1-cong : ∀ {X X′ : Tab O K} → X ≈T X′ → ∀ i → in1 X i ≈T in1 X′ i
  in1-cong h _ = h

  in2-cong : ∀ {X X′ Y Y′ : Tab O K} → X ≈T X′ → Y ≈T Y′ → ∀ i → in2 X Y i ≈T in2 X′ Y′ i
  in2-cong h k i = if-cong _≈T_ (i ==ℕ 0) h k

  in4-cong : ∀ {S S′ T′ T″ X X′ Y Y′ : Tab O K} → S ≈T S′ → T′ ≈T T″ → X ≈T X′ → Y ≈T Y′ →
             ∀ i → in4 S T′ X Y i ≈T in4 S′ T″ X′ Y′ i
  in4-cong a b c d i =
    if-cong _≈T_ (i ==ℕ 0) a (if-cong _≈T_ (i ==ℕ 1) b (if-cong _≈T_ (i ==ℕ 2) c d))

  CmCong : (CmpOp → Tab O K → Tab O K → Tab O K) → Set
  CmCong cm = ∀ o {X X′ Y Y′} → X ≈T X′ → Y ≈T Y′ → cm o X Y ≈T cm o X′ Y′

  ev-cong : ∀ {gen gen′ : Nat → String → Tab O K} {cm} → CmCong cm → ∀ t →
            (∀ {d x} → (d , x) ∈L leaves t → gen d x ≈T gen′ d x) →
            Eval.ev gen cm t ≈T Eval.ev gen′ cm t
  ev-cong c (v d x)       h = h here
  ev-cong c (sF n x)      h = apply-cong (faceSh false n) (in1-cong (ev-cong c x h))
  ev-cong c (tF n x)      h = apply-cong (faceSh true n) (in1-cong (ev-cong c x h))
  ev-cong c (idT n x)     h = apply-cong (idSh n) (in1-cong (ev-cong c x h))
  ev-cong c (comp n x y)  h = apply-cong (compSh n)
    (in2-cong (ev-cong c x (λ m → h (∈-++ˡ (leaves y) m))) (ev-cong c y (λ m → h (∈-++ʳ (leaves x) m))))
  ev-cong c (lft k n x y) h = apply-cong (lftSh k n)
    (in2-cong (ev-cong c x (λ m → h (∈-++ˡ (leaves y) m))) (ev-cong c y (λ m → h (∈-++ʳ (leaves x) m))))
  ev-cong c (rgt k n x y) h = apply-cong (rgtSh k n)
    (in2-cong (ev-cong c x (λ m → h (∈-++ˡ (leaves y) m))) (ev-cong c y (λ m → h (∈-++ʳ (leaves x) m))))
  ev-cong c (cmp o x y)   h =
    c o (ev-cong c x (λ m → h (∈-++ˡ (leaves y) m))) (ev-cong c y (λ m → h (∈-++ʳ (leaves x) m)))

  env-cong : ∀ {X X′ Y Y′ : Tab O K} → X ≈T X′ → Y ≈T Y′ → ∀ d nm → env X Y d nm ≈T env X′ Y′ d nm
  env-cong a b d nm = if-cong _≈T_ (primStringEquality nm "x0") a b

  mkCmp-cong : ∀ o inner → CmCong inner → ∀ {X X′ Y Y′} → X ≈T X′ → Y ≈T Y′ →
               mkCmp o inner X Y ≈T mkCmp o inner X′ Y′
  mkCmp-cong o inner c {X} {X′} {Y} {Y′} a b = apply-cong (cmpSh o)
    (in4-cong (ev-cong {env X Y} {env X′ Y′} {inner} c (fst (bounds o)) (λ {d} {x} _ → env-cong a b d x))
              (ev-cong {env X Y} {env X′ Y′} {inner} c (snd (bounds o)) (λ {d} {x} _ → env-cong a b d x)) a b)

  cmNone-cong : CmCong cmNone
  cmNone-cong o a b = a

  cmChi-cong : CmCong (λ _ → cmChi)
  cmChi-cong o = mkCmp-cong chiO cmNone cmNone-cong

  cmOnlyChi-cong : CmCong cmOnlyChi
  cmOnlyChi-cong chiO  = mkCmp-cong chiO cmNone cmNone-cong
  cmOnlyChi-cong rO    a b = a
  cmOnlyChi-cong tO    a b = a
  cmOnlyChi-cong iotaO a b = a
  cmOnlyChi-cong hO    a b = a

  cmAll-cong : CmCong cmAll
  cmAll-cong chiO  = mkCmp-cong chiO cmNone cmNone-cong
  cmAll-cong rO    = mkCmp-cong rO cmOnlyChi cmOnlyChi-cong
  cmAll-cong tO    = mkCmp-cong tO cmOnlyChi cmOnlyChi-cong
  cmAll-cong iotaO = mkCmp-cong iotaO cmOnlyChi cmOnlyChi-cong
  cmAll-cong hO    = mkCmp-cong hO cmOnlyChi cmOnlyChi-cong

------------------------------------------------------------------------
-- Interpreting the letters and objects of a table.

module Hom {O O′ K L : Set} (ρo : O → O′) (ρ : K → SExp L) where
  open Interp ρ

  mapT : Tab O K → Tab O′ L
  mapT X = tab (dm X) (ρo (lo X)) (ρo (hi X)) (λ l → iE (s X l)) (λ l → iE (t X l)) (iE (top X))

  evalLE-hom : ∀ (ins : Nat → Tab O K) e → iE (evalLE ins e) ≈S evalLE (λ i → mapT (ins i)) e
  evalLE-hom ins (sA i l) = ≈S-refl
  evalLE-hom ins (tA i l) = ≈S-refl
  evalLE-hom ins (topA i) = ≈S-refl
  evalLE-hom ins (a ∪E b) =
    ≈S-trans (≡⇒≈S (iE-++ (evalLE ins a) (evalLE ins b))) (∪-cong (evalLE-hom ins a) (evalLE-hom ins b))
  evalLE-hom ins (a ·E b) =
    ≈S-trans (iE-prod (evalLE ins a) (evalLE ins b))
      (prod-cong (iE (evalLE ins a)) (evalLE (λ i → mapT (ins i)) a)
                 (iE (evalLE ins b)) (evalLE (λ i → mapT (ins i)) b)
                 (evalLE-hom ins a) (evalLE-hom ins b))
  evalLE-hom ins εE = iE-unit
  evalLE-hom ins ∅E = ≈S-refl

  obj-hom : ∀ (ins : Nat → Tab O K) r → ρo (obj ins r) ≡ obj (λ i → mapT (ins i)) r
  obj-hom ins (true , i)  = refl
  obj-hom ins (false , i) = refl

  apply-hom : ∀ sh (ins : Nat → Tab O K) → mapT (apply sh ins) ≈T apply sh (λ i → mapT (ins i))
  apply-hom sh ins =
    refl , obj-hom ins (loR sh) ,
    trans (if-map ρo (dmS sh ==ℕ 0))
          (if-cong _≡_ (dmS sh ==ℕ 0) (obj-hom ins (loR sh)) (obj-hom ins (hiR sh))) ,
    (λ l → ≈S-trans (≡⇒≈S (if-map iE (inR l (dmS sh))))
                    (if-cong _≈S_ (inR l (dmS sh)) (evalLE-hom ins (sL sh l)) ≈S-refl)) ,
    (λ l → ≈S-trans (≡⇒≈S (if-map iE (inR l (dmS sh))))
                    (if-cong _≈S_ (inR l (dmS sh)) (evalLE-hom ins (tL sh l)) ≈S-refl)) ,
    ≈S-trans (≡⇒≈S (if-map iE (dmS sh ==ℕ 0)))
             (if-cong _≈S_ (dmS sh ==ℕ 0) ≈S-refl (evalLE-hom ins (topL sh)))

  -- apply followed by the inputs' images, for the input builders.
  in1-hom : ∀ (X : Tab O K) i → mapT (in1 X i) ≈T in1 (mapT X) i
  in1-hom X i = ≈T-refl

  in2-hom : ∀ (X Y : Tab O K) i → mapT (in2 X Y i) ≈T in2 (mapT X) (mapT Y) i
  in2-hom X Y i = ≡⇒≈T (if-map mapT (i ==ℕ 0))
    where ≡⇒≈T : ∀ {A B : Tab O′ L} → A ≡ B → A ≈T B
          ≡⇒≈T refl = ≈T-refl

  in4-hom : ∀ (S T X Y : Tab O K) i → mapT (in4 S T X Y i) ≈T in4 (mapT S) (mapT T) (mapT X) (mapT Y) i
  in4-hom S T X Y i =
    ≡⇒≈T (trans (if-map mapT (i ==ℕ 0))
           (cong (if i ==ℕ 0 then mapT S else_)
             (trans (if-map mapT (i ==ℕ 1))
               (cong (if i ==ℕ 1 then mapT T else_) (if-map mapT (i ==ℕ 2))))))
    where ≡⇒≈T : ∀ {A B : Tab O′ L} → A ≡ B → A ≈T B
          ≡⇒≈T refl = ≈T-refl

  -- apply, then rebuild the inputs.
  apply-hom′ : ∀ sh (ins : Nat → Tab O K) (ins′ : Nat → Tab O′ L) →
               (∀ i → mapT (ins i) ≈T ins′ i) → mapT (apply sh ins) ≈T apply sh ins′
  apply-hom′ sh ins ins′ h = ≈T-trans (apply-hom sh ins) (apply-cong sh h)

  CmHom : (CmpOp → Tab O K → Tab O K → Tab O K) → (CmpOp → Tab O′ L → Tab O′ L → Tab O′ L) → Set
  CmHom cm cm′ = ∀ o X Y → mapT (cm o X Y) ≈T cm′ o (mapT X) (mapT Y)

  ev-hom : ∀ {gen : Nat → String → Tab O K} {gen′ : Nat → String → Tab O′ L} {cm cm′} →
           CmHom cm cm′ → CmCong cm′ → ∀ t →
           (∀ {d x} → (d , x) ∈L leaves t → mapT (gen d x) ≈T gen′ d x) →
           mapT (Eval.ev gen cm t) ≈T Eval.ev gen′ cm′ t
  -- (the two-input case, shared)
  two : ∀ {gen : Nat → String → Tab O K} {gen′ : Nat → String → Tab O′ L} {cm cm′} →
        CmHom cm cm′ → CmCong cm′ → ∀ x y →
        (∀ {d z} → (d , z) ∈L (leaves x ++ leaves y) → mapT (gen d z) ≈T gen′ d z) →
        ∀ i → mapT (in2 (Eval.ev gen cm x) (Eval.ev gen cm y) i) ≈T in2 (Eval.ev gen′ cm′ x) (Eval.ev gen′ cm′ y) i
  ev-hom hc cc (v d x) h = h here
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (sF n x) h =
    apply-hom′ (faceSh false n) (in1 (Eval.ev gen cm x)) (in1 (Eval.ev gen′ cm′ x)) (λ _ → ev-hom hc cc x h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (tF n x) h =
    apply-hom′ (faceSh true n) (in1 (Eval.ev gen cm x)) (in1 (Eval.ev gen′ cm′ x)) (λ _ → ev-hom hc cc x h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (idT n x) h =
    apply-hom′ (idSh n) (in1 (Eval.ev gen cm x)) (in1 (Eval.ev gen′ cm′ x)) (λ _ → ev-hom hc cc x h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (comp n x y) h =
    apply-hom′ (compSh n) (in2 (Eval.ev gen cm x) (Eval.ev gen cm y)) (in2 (Eval.ev gen′ cm′ x) (Eval.ev gen′ cm′ y))
      (two hc cc x y h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (lft k n x y) h =
    apply-hom′ (lftSh k n) (in2 (Eval.ev gen cm x) (Eval.ev gen cm y)) (in2 (Eval.ev gen′ cm′ x) (Eval.ev gen′ cm′ y))
      (two hc cc x y h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (rgt k n x y) h =
    apply-hom′ (rgtSh k n) (in2 (Eval.ev gen cm x) (Eval.ev gen cm y)) (in2 (Eval.ev gen′ cm′ x) (Eval.ev gen′ cm′ y))
      (two hc cc x y h)
  ev-hom {gen} {gen′} {cm} {cm′} hc cc (cmp o x y) h =
    ≈T-trans (hc o (Eval.ev gen cm x) (Eval.ev gen cm y))
      (cc o (ev-hom hc cc x (λ m → h (∈-++ˡ (leaves y) m))) (ev-hom hc cc y (λ m → h (∈-++ʳ (leaves x) m))))

  two {gen} {gen′} {cm} {cm′} hc cc x y h i =
    ≈T-trans (in2-hom (Eval.ev gen cm x) (Eval.ev gen cm y) i)
      (in2-cong (ev-hom hc cc x (λ m → h (∈-++ˡ (leaves y) m))) (ev-hom hc cc y (λ m → h (∈-++ʳ (leaves x) m))) i)

  env-hom : ∀ (X Y : Tab O K) d nm → mapT (env X Y d nm) ≈T env (mapT X) (mapT Y) d nm
  env-hom X Y d nm = ≡⇒≈T (if-map mapT (primStringEquality nm "x0"))
    where ≡⇒≈T : ∀ {A B : Tab O′ L} → A ≡ B → A ≈T B
          ≡⇒≈T refl = ≈T-refl

  mkCmp-hom : ∀ o inner inner′ → CmHom inner inner′ → CmCong inner′ → ∀ X Y →
              mapT (mkCmp o inner X Y) ≈T mkCmp o inner′ (mapT X) (mapT Y)
  mkCmp-hom o inner inner′ hc cc X Y =
    apply-hom′ (cmpSh o) _ _ λ i →
      ≈T-trans (in4-hom (Eval.ev (env X Y) inner (fst (bounds o))) (Eval.ev (env X Y) inner (snd (bounds o))) X Y i)
        (in4-cong (ev-hom {env X Y} {env (mapT X) (mapT Y)} {inner} {inner′} hc cc (fst (bounds o)) (λ {d} {x} _ → env-hom X Y d x))
                  (ev-hom {env X Y} {env (mapT X) (mapT Y)} {inner} {inner′} hc cc (snd (bounds o)) (λ {d} {x} _ → env-hom X Y d x)) ≈T-refl ≈T-refl i)

  cmNone-hom : CmHom cmNone cmNone
  cmNone-hom o X Y = ≈T-refl

  cmOnlyChi-hom : CmHom cmOnlyChi cmOnlyChi
  cmOnlyChi-hom chiO  = mkCmp-hom chiO cmNone cmNone cmNone-hom cmNone-cong
  cmOnlyChi-hom rO    X Y = ≈T-refl
  cmOnlyChi-hom tO    X Y = ≈T-refl
  cmOnlyChi-hom iotaO X Y = ≈T-refl
  cmOnlyChi-hom hO    X Y = ≈T-refl

  cmAll-hom : CmHom cmAll cmAll
  cmAll-hom chiO  = mkCmp-hom chiO cmNone cmNone cmNone-hom cmNone-cong
  cmAll-hom rO    = mkCmp-hom rO cmOnlyChi cmOnlyChi cmOnlyChi-hom cmOnlyChi-cong
  cmAll-hom tO    = mkCmp-hom tO cmOnlyChi cmOnlyChi cmOnlyChi-hom cmOnlyChi-cong
  cmAll-hom iotaO = mkCmp-hom iotaO cmOnlyChi cmOnlyChi cmOnlyChi-hom cmOnlyChi-cong
  cmAll-hom hO    = mkCmp-hom hO cmOnlyChi cmOnlyChi cmOnlyChi-hom cmOnlyChi-cong
