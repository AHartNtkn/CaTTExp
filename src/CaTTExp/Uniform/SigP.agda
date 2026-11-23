------------------------------------------------------------------------
-- The raw signature of the support-free presentation P, as data
-- (ledger S3a: raw syntax; r10 (K45), original construction (4)–(29),
-- round 5 Response 3).
--
-- This is a transcription of `scripts/e6/reachability_theory.py`, the
-- presentation that `scripts/e6/interchange_free.py` grounds on finite
-- pasting trees. Sorts are cell dimensions. A term is a variable or an
-- operation applied to terms; dimensions are computed (`dim`), and the
-- typing conditions are guards, i.e. equations between faces, because
-- the theory is essentially algebraic.
--
--   sesqui n      the sesquicategory structure in dimension n, for
--                 EVERY n ≥ 1: faces, units, composition, the left and
--                 right actions of k-cells (k < n) with their laws, and
--                 globularity. The Python stops at n = 4; nothing in the
--                 schemas depends on that bound.
--   compOps,      the comparison operations χ, r, t, ι, h with their
--   comparisons   boundaries, degeneracies and whiskering laws;
--   outer         equations (7a)–(21) and the binary join factorization;
--   rules         the directed 5-cell schemas W, δ, N_L, N_R, U_r, U_t.
--
-- Names follow the Python, so that the transcription can be compared
-- term by term with its output (notes/uniform-checker.md §1.8). Nothing
-- here is proved yet: this module only fixes the raw syntax. The free
-- algebra on a pasting tree, its normal forms and their agreement with
-- (K45) are the next steps of S3a.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

module CaTTExp.Uniform.SigP where

------------------------------------------------------------------------
-- Terms.

data CmpOp : Set where
  chiO rO tO iotaO hO : CmpOp

data Tm : Set where
  v    : Nat → String → Tm             -- a variable of the given dimension
  sF   : Nat → Tm → Tm                 -- s_n of an n-cell
  tF   : Nat → Tm → Tm                 -- t_n of an n-cell
  idT  : Nat → Tm → Tm                 -- id_n of an n-cell (an (n+1)-cell)
  comp : Nat → Tm → Tm → Tm            -- comp_n of two n-cells
  lft  : Nat → Nat → Tm → Tm → Tm      -- left_{k,n}: a k-cell acting on an n-cell
  rgt  : Nat → Nat → Tm → Tm → Tm      -- right_{k,n}: an n-cell acted on by a k-cell
  cmp  : CmpOp → Tm → Tm → Tm

cmpDim : CmpOp → Nat
cmpDim chiO = 3
cmpDim _    = 4

dim : Tm → Nat
dim (v d _)       = d
dim (sF n _)      = n ∸ 1
dim (tF n _)      = n ∸ 1
dim (idT n _)     = suc n
dim (comp n _ _)  = n
dim (lft _ n _ _) = n
dim (rgt _ n _ _) = n
dim (cmp o _ _)   = cmpDim o

-- Top composition or a single primitive whisker, arguments in order.
paste : Tm → Tm → Tm
paste x y with dim x | dim y
... | p | q = if p ==ℕ q then comp p x y
              else if p <ℕ q then lft p q x y
              else rgt q p x y

private
  iter : Nat → (Tm → Tm) → Tm → Tm
  iter zero    f x = x
  iter (suc k) f x = iter k f (f x)

-- The d-dimensional source or target face.
face : Nat → Bool → Tm → Tm
face d tgt x = iter (dim x ∸ d) step x
  where step : Tm → Tm
        step y = (if tgt then tF else sF) (dim y) y

src tgt : Tm → Tm
src x = face (dim x ∸ 1) false x
tgt x = face (dim x ∸ 1) true x

unit : Tm → Tm
unit x = idT (dim x) x

-- A guard: two terms that must be equal.
Guard : Set
Guard = Tm × Tm

adjacent : Tm → Tm → Nat → Guard
adjacent x y d = face d true x , face d false y

ctx : Maybe Tm → Tm → Maybe Tm → Tm
ctx p x q = after q (before p x)
  where before : Maybe Tm → Tm → Tm
        before nothing  x = x
        before (just p) x = paste p x
        after : Maybe Tm → Tm → Tm
        after nothing  x = x
        after (just q) x = paste x q

vertical : Tm → List Tm → Tm
vertical x []       = x
vertical x (y ∷ ys) = vertical (paste x y) ys

------------------------------------------------------------------------
-- Schemas.

record Schema : Set where
  constructor schema
  field
    name   : String
    vars   : List Tm
    guards : List Guard
    lhs    : Tm
    rhs    : Tm

-- An operation with its guards and boundary (as the faces of its
-- result on generic arguments).
record OpSpec : Set where
  constructor opSpec
  field
    opName  : String
    args    : List Tm
    guardsO : List Guard
    applied : Tm
    srcO    : Tm
    tgtO    : Tm

------------------------------------------------------------------------
-- Blocks: cells on outer spans with their stationary 1-whiskers
-- (Python's `Block`).

record Block : Set where
  constructor blk
  field
    cell    : Tm
    start   : Nat
    initial : List Tm
    final   : List Tm
open Block

private
  len : ∀ {A : Set} → List A → Nat
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

  nth : List Tm → Nat → Tm
  nth []       _       = v 0 "?"
  nth (x ∷ _)  zero    = x
  nth (_ ∷ xs) (suc i) = nth xs i

  range : Nat → Nat → List Nat
  range a b = go (b ∸ a) a
    where go : Nat → Nat → List Nat
          go zero    i = []
          go (suc k) i = i ∷ go k (suc i)

  rev : ∀ {A : Set} → List A → List A
  rev = go []
    where go : ∀ {A : Set} → List A → List A → List A
          go acc []       = acc
          go acc (x ∷ xs) = go (x ∷ acc) xs

  mapL : ∀ {A B : Set} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
  foldl f z []       = z
  foldl f z (x ∷ xs) = foldl f (f z x) xs

  minN : Nat → Nat → Nat
  minN a b = if a <ℕ b then a else b

stop : Block → Nat
stop b = start b + len (initial b)

bvar : Tm → Nat → Block
bvar c s = blk c s (face 1 false c ∷ []) (face 1 true c ∷ [])

bface : Bool → Block → Block
bface t b = blk ((if t then tgt else src) (cell b)) (start b) (initial b) (final b)

private
  extend : Block → Block → List Tm → Tm
  extend x y faces =
    foldl (λ c i → paste c (nth faces (i ∸ start y)))
      (foldl (λ c i → paste (nth faces (i ∸ start y)) c) (cell x) (rev (range (start y) (start x))))
      (range (stop x) (stop y))

  inRange : Block → Nat → Bool
  inRange b i = (start b <ℕ suc i) ∧ (i <ℕ stop b)

merge : Block → Block → (Tm → Tm → Tm) → Block
merge x y combine =
  blk (combine first second) lo
      (mapL (λ i → if inRange x i then nth (initial x) (i ∸ start x) else nth (initial y) (i ∸ start y)) (range lo hi))
      (mapL (λ i → if inRange y i then nth (final y) (i ∸ start y) else nth (final x) (i ∸ start x)) (range lo hi))
  where
  lo hi : Nat
  lo = minN (start x) (start y)
  hi = max (stop x) (stop y)
  first second : Tm
  first  = extend x y (initial y)
  second = extend y x (final x)

word inner : Block → Block → Block
word x y  = merge x y paste
inner x y = merge x y (cmp iotaO)

outer : CmpOp → Block → Block → Block
outer o x y = blk (cmp o (cell x) (cell y)) (start x) (initial x ++ initial y) (final x ++ final y)

chiB rB tB hB : Block → Block → Block
chiB = outer chiO
rB   = outer rO
tB   = outer tO
hB   = outer hO

c : Maybe Block → Block → Maybe Block → Tm
c p x q = ctx (mcell p) (cell x) (mcell q)
  where mcell : Maybe Block → Maybe Tm
        mcell nothing  = nothing
        mcell (just b) = just (cell b)

record Join : Set where
  field
    S U0 plus minus t0 t1 r0 r1 : Tm

binaryJoin : Block → Block → Join
binaryJoin A B = record
  { S     = vertical (cell (word B a)) (cell (chiB a bb) ∷ cell (word A bb) ∷ [])
  ; U0    = vertical (cell (word b A)) (cell (word B aa) ∷ cell (chiB aa bb) ∷ [])
  ; plus  = c (just (chiB a b)) (inner A B) nothing
  ; minus = c nothing (inner B A) (just (chiB aa bb))
  ; t0    = c nothing (tB a B) (just (word A bb))
  ; t1    = c (just (word b A)) (tB aa B) nothing
  ; r0    = c nothing (rB A b) (just (word aa B))
  ; r1    = c (just (word B a)) (rB A bb) nothing
  }
  where
  a aa b bb : Block
  a = bface false A ; aa = bface true A
  b = bface false B ; bb = bface true B

------------------------------------------------------------------------
-- The sesquicategory structure in dimension n ≥ 1.

private
  showN : Nat → String
  showN = primShowNat

  _&_ : String → String → String
  _&_ = primStringAppend
  infixr 5 _&_

  concatMapL : ∀ {A B : Set} → (A → List B) → List A → List B
  concatMapL f []       = []
  concatMapL f (x ∷ xs) = f x ++ concatMapL f xs

sesquiOps : Nat → List OpSpec
sesquiOps n =
  opSpec ("s" & showN n) (x ∷ []) [] (sF n x) (v 0 "?") (v 0 "?") ∷
  opSpec ("t" & showN n) (x ∷ []) [] (tF n x) (v 0 "?") (v 0 "?") ∷
  opSpec ("id" & showN (n ∸ 1)) (base ∷ []) [] (idT (n ∸ 1) base) base base ∷
  opSpec ("comp" & showN n) (x ∷ y ∷ []) (adjacent x y (n ∸ 1) ∷ []) (comp n x y) (src x) (tgt y) ∷
  concatMapL actOps (range 1 n)
  where
  x y base : Tm
  x = v n "x0" ; y = v n "x1" ; base = v (n ∸ 1) "x0"
  actOps : Nat → List OpSpec
  actOps k =
    opSpec ("left" & showN k & "_" & showN n) (u ∷ f ∷ [])
      (adjacent u f (k ∸ 1) ∷ []) (lft k n u f) (paste u (src f)) (paste u (tgt f)) ∷
    opSpec ("right" & showN k & "_" & showN n) (f′ ∷ u′ ∷ [])
      (adjacent f′ u′ (k ∸ 1) ∷ []) (rgt k n f′ u′) (paste (src f′) u′) (paste (tgt f′) u′) ∷ []
    where
    u f u′ f′ : Tm
    u = v k "x0" ; f = v n "x1" ; u′ = v k "x1" ; f′ = v n "x0"

sesqui : Nat → List Schema
sesqui n =
  schema ("associativity " & showN n) (x ∷ y ∷ z ∷ [])
    (adjacent x y (n ∸ 1) ∷ adjacent y z (n ∸ 1) ∷ [])
    (paste (paste x y) z) (paste x (paste y z)) ∷
  schema ("left unit " & showN n) (x ∷ []) [] (paste (unit (src x)) x) x ∷
  schema ("right unit " & showN n) (x ∷ []) [] (paste x (unit (tgt x))) x ∷
  globular ++ concatMapL perK (range 1 n)
  where
  x y z : Tm
  x = v n "x0" ; y = v n "x1" ; z = v n "x2"
  globular : List Schema
  globular = if n <ℕ 2 then [] else
    (schema ("globular source " & showN n) (x ∷ []) [] (src (src x)) (src (tgt x)) ∷
     schema ("globular target " & showN n) (x ∷ []) [] (tgt (src x)) (tgt (tgt x)) ∷ [])

  perK : Nat → List Schema
  perK k = side true ++ side false ++
    schema ("commuting left and right actions " & showN k & "," & showN n) (l ∷ f ∷ rr ∷ [])
      (adjacent l f (k ∸ 1) ∷ adjacent f rr (k ∸ 1) ∷ [])
      (paste (paste l f) rr) (paste l (paste f rr)) ∷ []
    where
    l ll f g F rr : Tm
    l = v k "l" ; ll = v k "m" ; f = v n "f" ; g = v n "g" ; F = v (n ∸ 1) "F" ; rr = v k "r"
    side : Bool → List Schema
    side left =
      schema (nm & " preserves identities " & showN k & "," & showN n) (l ∷ F ∷ [])
        (glue l F ∷ []) (act l (unit F)) (unit (act l F)) ∷
      schema (nm & " preserves composition " & showN k & "," & showN n) (l ∷ f ∷ g ∷ [])
        (glue l f ∷ adjacent f g (n ∸ 1) ∷ []) (act l (paste f g)) (paste (act l f) (act l g)) ∷
      schema (nm & " identity acts trivially " & showN k & "," & showN n) (f ∷ [])
        [] (act (unit (face (k ∸ 1) (not left) f)) f) f ∷
      schema (nm & " action " & showN k & "," & showN n) (l ∷ ll ∷ f ∷ [])
        (glue l ll ∷ glue ll f ∷ []) (act pair f) (act l (act ll f)) ∷
      concatMapL inside (range (suc k) n)
      where
      nm : String
      nm = if left then "left" else "right"
      act : Tm → Tm → Tm
      act low high = if left then paste low high else paste high low
      glue : Tm → Tm → Guard
      glue low high = if left then adjacent low high (k ∸ 1) else adjacent high low (k ∸ 1)
      pair : Tm
      pair = if left then paste l ll else paste ll l
      inside : Nat → List Schema
      inside j = one false ∷ one true ∷ []
        where
        m : Tm
        m = v j "m"
        one : Bool → Schema
        one il = schema (nm & " preserves " & (if il then "left" else "right") & " "
                            & showN k & "," & showN j & "," & showN n)
                   (l ∷ m ∷ f ∷ []) (glue l f ∷ adjacent a b (j ∸ 1) ∷ [])
                   (act l (paste a b)) (paste (act l a) (act l b))
          where a b : Tm
                a = if il then m else f
                b = if il then f else m

------------------------------------------------------------------------
-- The comparison operations χ, r, t, ι, h.

private
  cmpName : CmpOp → String
  cmpName chiO  = "chi"
  cmpName rO    = "r"
  cmpName tO    = "t"
  cmpName iotaO = "iota"
  cmpName hO    = "h"

  -- (op, p, q, cut)
  cmpTable : List (CmpOp × (Nat × (Nat × Nat)))
  cmpTable = (chiO , 2 , 2 , 0) ∷ (rO , 3 , 2 , 0) ∷ (tO , 2 , 3 , 0) ∷
             (iotaO , 3 , 3 , 1) ∷ (hO , 3 , 3 , 0) ∷ []

compBounds : CmpOp → Tm → Tm → Tm × Tm
compBounds o x y = go o
  where
  X Y : Block
  X = bvar x 0 ; Y = bvar y 1
  go : CmpOp → Tm × Tm
  go chiO  = cell (word Y X) , cell (word X Y)
  go rO    = vertical (cell (chiB (bface false X) Y)) (cell (word X Y) ∷ []) ,
             vertical (cell (word Y X)) (cell (chiB (bface true X) Y) ∷ [])
  go tO    = vertical (cell (word Y X)) (cell (chiB X (bface true Y)) ∷ []) ,
             vertical (cell (chiB X (bface false Y))) (cell (word X Y) ∷ [])
  go iotaO = vertical (paste (src x) y) (paste x (tgt y) ∷ []) ,
             vertical (paste x (src y)) (paste (tgt x) y ∷ [])
  go hO    = Join.S (binaryJoin X Y) , Join.U0 (binaryJoin X Y)

compOps : List OpSpec
compOps = mapL one cmpTable
  where
  one : CmpOp × (Nat × (Nat × Nat)) → OpSpec
  one (o , p , q , cut) =
    opSpec (cmpName o) (x ∷ y ∷ []) (adjacent x y cut ∷ []) (cmp o x y)
      (fst (compBounds o x y)) (snd (compBounds o x y))
    where x y : Tm
          x = v p "x0" ; y = v q "x1"

comparisons : List Schema
comparisons = concatMapL degen cmpTable ++ concatMapL whisk whiskTable
  where
  degen : CmpOp × (Nat × (Nat × Nat)) → List Schema
  degen (o , p , q , cut) = one true ∷ one false ∷ []
    where
    x y : Tm
    x = v p "x0" ; y = v q "x1"
    one : Bool → Schema
    one left = schema (cmpName o & (if left then " left" else " right") & " degeneracy")
                 (u ∷ w ∷ []) (adjacent u w cut ∷ []) whole degenerate
      where
      u w : Tm
      u = if left then v (p ∸ 1) "u" else x
      w = if left then y else v (q ∸ 1) "v"
      whole degenerate : Tm
      whole = cmp o (if left then unit u else u) (if left then w else unit w)
      degenerate = if (isH o) ∧ not left then cmp rO u w else unit (src whole)
        where isH : CmpOp → Bool
              isH hO = true
              isH _  = false

  whiskTable : List (CmpOp × (Nat × Nat))
  whiskTable = (chiO , 2 , 2) ∷ (rO , 3 , 2) ∷ (tO , 2 , 3) ∷ (iotaO , 3 , 3) ∷ []

  whisk : CmpOp × (Nat × Nat) → List Schema
  whisk (o , p , q) =
    schema (nm & " left whisker") (l ∷ x ∷ y ∷ []) (adjacent l x k ∷ adjacent x y k ∷ [])
      (J (paste l x) y) (paste l (J x y)) ∷
    schema (nm & " balanced whisker") (x ∷ l ∷ y ∷ []) (adjacent x l k ∷ adjacent l y k ∷ [])
      (J (paste x l) y) (J x (paste l y)) ∷
    schema (nm & " right whisker") (x ∷ y ∷ l ∷ []) (adjacent x y k ∷ adjacent y l k ∷ [])
      (J x (paste y l)) (paste (J x y) l) ∷
    extra o
    where
    nm : String
    nm = cmpName o
    ld : Nat
    ld = isIota o
      where isIota : CmpOp → Nat
            isIota iotaO = 2
            isIota _     = 1
    k : Nat
    k = ld ∸ 1
    l x y f : Tm
    l = v ld "l" ; x = v p "x" ; y = v q "y" ; f = v 1 "f"
    J : Tm → Tm → Tm
    J = cmp o
    extra : CmpOp → List Schema
    extra iotaO =
      schema "iota preserves left 1-whiskering" (f ∷ x ∷ y ∷ [])
        (adjacent f x 0 ∷ adjacent x y 1 ∷ []) (J (paste f x) (paste f y)) (paste f (J x y)) ∷
      schema "iota preserves right 1-whiskering" (x ∷ y ∷ f ∷ [])
        (adjacent x y 1 ∷ adjacent y f 0 ∷ []) (J (paste x f) (paste y f)) (paste (J x y) f) ∷ []
    extra _ = []

------------------------------------------------------------------------
-- Equations (7a)–(21), the binary join factorization, and W.

private
  eqB : String → List Block → List (Block × (Block × Nat)) → Tm → Tm → Schema
  eqB nm vs joins l r =
    schema nm (mapL cell vs) (mapL (λ { (u , w , d) → adjacent (cell u) (cell w) d }) joins) l r

outerEqs : List Schema
outerEqs =
  eqB "7a" (a1 ∷ a2 ∷ bv ∷ []) ((a1 , a2 , 1) ∷ (a1 , bv , 0) ∷ [])
    (cell (chiB (word a1 a2) bv))
    (vertical (cell (word (chiB a1 bv) a2)) (cell (word a1 (chiB a2 bv)) ∷ [])) ∷
  eqB "7b" (av ∷ b1 ∷ b2 ∷ []) ((b1 , b2 , 1) ∷ (av , b1 , 0) ∷ [])
    (cell (chiB av (word b1 b2)))
    (vertical (cell (word b1 (chiB av b2))) (cell (word (chiB av b1) b2) ∷ [])) ∷
  eqB "10" (A ∷ A2 ∷ bv ∷ []) ((A , A2 , 2) ∷ (A , bv , 0) ∷ [])
    (cell (rB (chain A A2) bv))
    (vertical (c nothing (rB A bv) (just (word A2 bv))) (c (just (word bv A)) (rB A2 bv) nothing ∷ [])) ∷
  eqB "11" (av ∷ B ∷ B2 ∷ []) ((B , B2 , 2) ∷ (av , B , 0) ∷ [])
    (cell (tB av (chain B B2)))
    (vertical (c (just (word B av)) (tB av B2) nothing) (c nothing (tB av B) (just (word av B2)) ∷ [])) ∷
  eqB "12" (A ∷ b1 ∷ b2 ∷ []) ((A , b1 , 0) ∷ (b1 , b2 , 1) ∷ [])
    (cell (rB A (word b1 b2)))
    (vertical (c (just (word b1 (chiB a b2))) (word (rB A b1) b2) nothing)
              (c nothing (word b1 (rB A b2)) (just (word (chiB aa b1) b2)) ∷ [])) ∷
  eqB "13" (a1 ∷ a2 ∷ B ∷ []) ((a1 , a2 , 1) ∷ (a1 , B , 0) ∷ [])
    (cell (tB (word a1 a2) B))
    (vertical (c nothing (word (tB a1 B) a2) (just (word a1 (chiB a2 bb))))
              (c (just (word (chiB a1 b) a2)) (word a1 (tB a2 B)) nothing ∷ [])) ∷
  eqB "14" (A ∷ a2 ∷ bv ∷ []) ((A , a2 , 1) ∷ (A , bv , 0) ∷ [])
    (cell (rB (word A a2) bv))
    (vertical (c (just (word (chiB a bv) a2)) (inner A (chiB a2 bv)) nothing)
              (c nothing (word (rB A bv) a2) (just (word aa (chiB a2 bv))) ∷ [])) ∷
  eqB "15" (a1 ∷ A ∷ bv ∷ []) ((a1 , A , 1) ∷ (A , bv , 0) ∷ [])
    (vertical (cell (rB (word a1 A) bv)) (c nothing (inner (chiB a1 bv) A) (just (word a1 (chiB aa bv))) ∷ []))
    (c (just (word (chiB a1 bv) a)) (word a1 (rB A bv)) nothing) ∷
  eqB "16" (av ∷ B ∷ b2 ∷ []) ((av , B , 0) ∷ (B , b2 , 1) ∷ [])
    (vertical (c nothing (inner B (chiB av b2)) (just (word (chiB av bb) b2))) (cell (tB av (word B b2)) ∷ []))
    (c (just (word b (chiB av b2))) (word (tB av B) b2) nothing) ∷
  eqB "17" (av ∷ b1 ∷ B ∷ []) ((av , b1 , 0) ∷ (b1 , B , 1) ∷ [])
    (cell (tB av (word b1 B)))
    (vertical (c nothing (word b1 (tB av B)) (just (word (chiB av b1) bb)))
              (c (just (word b1 (chiB av b))) (inner (chiB av b1) B) nothing ∷ [])) ∷
  eqB "18" (av ∷ bv ∷ d ∷ []) ((av , bv , 0) ∷ (bv , d , 0) ∷ [])
    (cell (rB (chiB av bv) d)) (cell (tB av (chiB bv d))) ∷
  schema "20" (F ∷ F2 ∷ cell av ∷ cell bv ∷ [])
    (crossGuard ∷ adjacent F F2 2 ∷ adjacent F cross 1 ∷ [])
    (cmp iotaO (paste F F2) cross)
    (vertical (ctx nothing (cmp iotaO F cross) (just (paste F2 (tgt cross))))
              (ctx (just (paste F (src cross))) (cmp iotaO F2 cross) nothing ∷ [])) ∷
  schema "21" (cell av ∷ cell bv ∷ F ∷ F2 ∷ [])
    (crossGuard ∷ adjacent F F2 2 ∷ adjacent cross F 1 ∷ [])
    (cmp iotaO cross (paste F F2))
    (vertical (ctx (just (paste (src cross) F)) (cmp iotaO cross F2) nothing)
              (ctx nothing (cmp iotaO cross F) (just (paste (tgt cross) F2)) ∷ [])) ∷
  eqB "binary join factorization" (A ∷ B ∷ []) ((A , B , 0) ∷ [])
    (Join.r1 J) (vertical join (Join.minus J ∷ [])) ∷ []
  where
  A A2 B B2 a aa b bb a1 a2 b1 b2 av bv d : Block
  A = bvar (v 3 "A") 0 ; A2 = bvar (v 3 "A2") 0
  B = bvar (v 3 "B") 1 ; B2 = bvar (v 3 "B2") 1
  a = bface false A ; aa = bface true A ; b = bface false B ; bb = bface true B
  a1 = bvar (v 2 "a1") 0 ; a2 = bvar (v 2 "a2") 0
  b1 = bvar (v 2 "b1") 1 ; b2 = bvar (v 2 "b2") 1
  av = bvar (v 2 "a") 0 ; bv = bvar (v 2 "b") 1
  d = bvar (v 2 "d") 2
  chain : Block → Block → Block
  chain u w = blk (paste (cell u) (cell w)) (start u) (initial u) (final u)
  F F2 cross : Tm
  F = v 3 "F" ; F2 = v 3 "F2"
  cross = cell (chiB av bv)
  crossGuard : Guard
  crossGuard = adjacent (cell av) (cell bv) 0
  J : Join
  J = binaryJoin A B
  join : Tm
  join = cell (hB A B)

------------------------------------------------------------------------
-- Directed 5-cell schemas (lhs ⇒ rhs).

rules : List Schema
rules =
  schema "W" (cell A ∷ cell B ∷ []) (adjacent (cell A) (cell B) 0 ∷ [])
    (vertical (Join.t0 J) (Join.plus J ∷ Join.r0 J ∷ []))
    (vertical (cell (hB A B)) (Join.t1 J ∷ [])) ∷
  schema "delta" (X ∷ Y ∷ []) (adjacent X Y 2 ∷ [])
    (vertical (paste (src X) Y) (paste X (tgt Y) ∷ []))
    (vertical (paste X (src Y)) (paste (tgt X) Y ∷ [])) ∷
  schema "N_L" (X ∷ G ∷ []) (adjacent X G 1 ∷ [])
    (vertical (cmp iotaO (src X) G) (ctx nothing (paste X (src G)) (just (paste (tgt (src X)) G)) ∷ []))
    (vertical (ctx (just (paste (src (src X)) G)) (paste X (tgt G)) nothing) (cmp iotaO (tgt X) G ∷ [])) ∷
  schema "N_R" (F ∷ Y ∷ []) (adjacent F Y 1 ∷ [])
    (vertical (ctx nothing (paste (src F) Y) (just (paste F (tgt (src Y))))) (cmp iotaO F (tgt Y) ∷ []))
    (vertical (cmp iotaO F (src Y)) (ctx (just (paste F (src (src Y)))) (paste (tgt F) Y) nothing ∷ [])) ∷
  schema "U_r" (X ∷ cell Bb ∷ []) (adjacent X (cell Bb) 0 ∷ [])
    (vertical (cell (rB LA Bb)) (c nothing (word Bb L) (just (chiB (bface true LA) Bb)) ∷ []))
    (vertical (c (just (chiB (bface false LA) Bb)) (word L Bb) nothing) (cell (rB LA2 Bb) ∷ [])) ∷
  schema "U_t" (cell av ∷ Y ∷ []) (adjacent (cell av) Y 0 ∷ [])
    (vertical (c nothing (word Q av) (just (chiB av (bface true QB)))) (cell (tB av QB2) ∷ []))
    (vertical (cell (tB av QB)) (c (just (chiB av (bface false QB))) (word av Q) nothing ∷ [])) ∷ []
  where
  A B : Block
  A = bvar (v 3 "A") 0 ; B = bvar (v 3 "B") 1
  J : Join
  J = binaryJoin A B
  X Y F G : Tm
  X = v 4 "X" ; Y = v 4 "Y" ; F = v 3 "F" ; G = v 3 "G"
  L Bb LA LA2 av Q QB QB2 : Block
  L = bvar X 0 ; Bb = bvar (v 2 "b") 1
  LA = bface false L ; LA2 = bface true L
  av = bvar (v 2 "a") 0 ; Q = bvar Y 1
  QB = bface false Q ; QB2 = bface true Q

------------------------------------------------------------------------
-- The presentation through dimension N (the Python takes N = 4).

operationsUpTo : Nat → List OpSpec
operationsUpTo N = concatMapL sesquiOps (range 1 (suc N)) ++ compOps

equationsUpTo : Nat → List Schema
equationsUpTo N = concatMapL sesqui (range 1 (suc N)) ++ comparisons ++ outerEqs
