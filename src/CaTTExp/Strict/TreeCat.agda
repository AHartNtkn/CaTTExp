------------------------------------------------------------------------
-- Labelled trees form a strict ω-category (ledger item A3a, general
-- case; notes/strict-omega-soundness.md).
--
-- For any label set A, the trees `LT A` of CaTTExp.Strict.Trees with
--   sₙ = truncation keeping the first cells at height n   (bdm n)
--   tₙ = truncation keeping the last cells at height n    (bdp n)
--   x #ₙ y = gluing along height n                         (glue n)
-- satisfy every axiom of CaTTExp.Strict.Omega. Trees labelled by the
-- variables of a pasting context are the cells of the free strict
-- ω-category on it; the soundness proof evaluates CaTT terms there.
-- Gluing is total on raw trees; the axioms that need it use the
-- composability proofs (for matching shapes).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Trees

module CaTTExp.Strict.TreeCat (A : Set) where

private
  Tr = LT A
  B  = Br A

------------------------------------------------------------------------
-- Lists of branches.

lastv-bdmB : ∀ d (x : A) r → lastv x (bdmB d r) ≡ lastv x r
lastv-bdmB d x nil          = refl
lastv-bdmB d x (cons T y r) = lastv-bdmB d y r

lastv-bdpB : ∀ d (x : A) r → lastv x (bdpB d r) ≡ lastv x r
lastv-bdpB d x nil          = refl
lastv-bdpB d x (cons T y r) = lastv-bdpB d y r

lastv-glueB : ∀ d (x : A) r₁ r₂ → lastv x (glueB d r₁ r₂) ≡ lastv x r₁
lastv-glueB d x nil            _              = refl
lastv-glueB d x (cons T y r)   nil            = refl
lastv-glueB d x (cons T₁ y r₁) (cons T₂ _ r₂) = lastv-glueB d y r₁ r₂

lastv-++ : ∀ (x : A) r₁ r₂ → lastv x (r₁ ++B r₂) ≡ lastv (lastv x r₁) r₂
lastv-++ x nil          r₂ = refl
lastv-++ x (cons T y r) r₂ = lastv-++ y r r₂

++B-nil : ∀ (r : B) → r ++B nil ≡ r
++B-nil nil          = refl
++B-nil (cons T y r) = cong (cons T y) (++B-nil r)

++B-assoc : ∀ (r₁ r₂ r₃ : B) → (r₁ ++B r₂) ++B r₃ ≡ r₁ ++B (r₂ ++B r₃)
++B-assoc nil          r₂ r₃ = refl
++B-assoc (cons T y r) r₂ r₃ = cong (cons T y) (++B-assoc r r₂ r₃)

bdmB-++ : ∀ d (r₁ r₂ : B) → bdmB d (r₁ ++B r₂) ≡ bdmB d r₁ ++B bdmB d r₂
bdmB-++ d nil          r₂ = refl
bdmB-++ d (cons T y r) r₂ = cong (cons (bdm d T) y) (bdmB-++ d r r₂)

bdpB-++ : ∀ d (r₁ r₂ : B) → bdpB d (r₁ ++B r₂) ≡ bdpB d r₁ ++B bdpB d r₂
bdpB-++ d nil          r₂ = refl
bdpB-++ d (cons T y r) r₂ = cong (cons (bdp d T) y) (bdpB-++ d r r₂)

-- Same length.
data SameL : B → B → Set where
  sl-nil  : SameL nil nil
  sl-cons : ∀ {T y r T′ y′ r′} → SameL r r′ → SameL (cons T y r) (cons T′ y′ r′)

sl-from : ∀ d (r₁ r₂ : B) → bdpB d r₁ ≡ bdmB d r₂ → SameL r₁ r₂
sl-from d nil            nil            _ = sl-nil
sl-from d nil            (cons _ _ _)   ()
sl-from d (cons _ _ _)   nil            ()
sl-from d (cons T₁ y₁ r₁) (cons T₂ y₂ r₂) e = sl-cons (sl-from d r₁ r₂ (cons-r e))

glueB-++ : ∀ d {r₁ r₂ : B} → SameL r₁ r₂ → ∀ r₃ r₄ →
           glueB d (r₁ ++B r₃) (r₂ ++B r₄) ≡ glueB d r₁ r₂ ++B glueB d r₃ r₄
glueB-++ d sl-nil r₃ r₄ = refl
glueB-++ d (sl-cons {T} {y} {r} {T′} {y′} {r′} s) r₃ r₄ = cong (cons (glue d T T′) y) (glueB-++ d s r₃ r₄)

------------------------------------------------------------------------
-- (i) Boundaries of boundaries.

mutual
  ss< : ∀ {m n} (x : Tr) → m < n → bdm m (bdm n x) ≡ bdm m x
  ss< {zero}  {suc n} (node x r) _       = refl
  ss< {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (ssB< r l)

  ssB< : ∀ {m n} (r : B) → m < n → bdmB m (bdmB n r) ≡ bdmB m r
  ssB< nil          l = refl
  ssB< (cons T y r) l = cong₂ (λ a b → cons a y b) (ss< T l) (ssB< r l)

mutual
  st< : ∀ {m n} (x : Tr) → m < n → bdm m (bdp n x) ≡ bdm m x
  st< {zero}  {suc n} (node x r) _       = refl
  st< {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (stB< r l)

  stB< : ∀ {m n} (r : B) → m < n → bdmB m (bdpB n r) ≡ bdmB m r
  stB< nil          l = refl
  stB< (cons T y r) l = cong₂ (λ a b → cons a y b) (st< T l) (stB< r l)

mutual
  ts< : ∀ {m n} (x : Tr) → m < n → bdp m (bdm n x) ≡ bdp m x
  ts< {zero}  {suc n} (node x r) _       = cong (λ v → node v nil) (lastv-bdmB n x r)
  ts< {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (tsB< r l)

  tsB< : ∀ {m n} (r : B) → m < n → bdpB m (bdmB n r) ≡ bdpB m r
  tsB< nil          l = refl
  tsB< (cons T y r) l = cong₂ (λ a b → cons a y b) (ts< T l) (tsB< r l)

mutual
  tt< : ∀ {m n} (x : Tr) → m < n → bdp m (bdp n x) ≡ bdp m x
  tt< {zero}  {suc n} (node x r) _       = cong (λ v → node v nil) (lastv-bdpB n x r)
  tt< {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (ttB< r l)

  ttB< : ∀ {m n} (r : B) → m < n → bdpB m (bdpB n r) ≡ bdpB m r
  ttB< nil          l = refl
  ttB< (cons T y r) l = cong₂ (λ a b → cons a y b) (tt< T l) (ttB< r l)

mutual
  ss≥ : ∀ {m n} (x : Tr) → n ≤ m → bdm m (bdm n x) ≡ bdm n x
  ss≥ {zero}  {zero}  (node x r) _       = refl
  ss≥ {suc m} {zero}  (node x r) _       = refl
  ss≥ {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (ssB≥ r l)

  ssB≥ : ∀ {m n} (r : B) → n ≤ m → bdmB m (bdmB n r) ≡ bdmB n r
  ssB≥ nil          l = refl
  ssB≥ (cons T y r) l = cong₂ (λ a b → cons a y b) (ss≥ T l) (ssB≥ r l)

mutual
  ts≥ : ∀ {m n} (x : Tr) → n ≤ m → bdp m (bdm n x) ≡ bdm n x
  ts≥ {zero}  {zero}  (node x r) _       = refl
  ts≥ {suc m} {zero}  (node x r) _       = refl
  ts≥ {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (tsB≥ r l)

  tsB≥ : ∀ {m n} (r : B) → n ≤ m → bdpB m (bdmB n r) ≡ bdmB n r
  tsB≥ nil          l = refl
  tsB≥ (cons T y r) l = cong₂ (λ a b → cons a y b) (ts≥ T l) (tsB≥ r l)

mutual
  st≥ : ∀ {m n} (x : Tr) → n ≤ m → bdm m (bdp n x) ≡ bdp n x
  st≥ {zero}  {zero}  (node x r) _       = refl
  st≥ {suc m} {zero}  (node x r) _       = refl
  st≥ {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (stB≥ r l)

  stB≥ : ∀ {m n} (r : B) → n ≤ m → bdmB m (bdpB n r) ≡ bdpB n r
  stB≥ nil          l = refl
  stB≥ (cons T y r) l = cong₂ (λ a b → cons a y b) (st≥ T l) (stB≥ r l)

mutual
  tt≥ : ∀ {m n} (x : Tr) → n ≤ m → bdp m (bdp n x) ≡ bdp n x
  tt≥ {zero}  {zero}  (node x r) _       = refl
  tt≥ {suc m} {zero}  (node x r) _       = refl
  tt≥ {suc m} {suc n} (node x r) (s≤s l) = cong (node x) (ttB≥ r l)

  ttB≥ : ∀ {m n} (r : B) → n ≤ m → bdpB m (bdpB n r) ≡ bdpB n r
  ttB≥ nil          l = refl
  ttB≥ (cons T y r) l = cong₂ (λ a b → cons a y b) (tt≥ T l) (ttB≥ r l)

------------------------------------------------------------------------
-- (iii) Boundaries of composites.

mutual
  s-glue : ∀ n (x y : Tr) → bdm n (glue n x y) ≡ bdm n x
  s-glue zero    (node x r₁) (node y r₂) = refl
  s-glue (suc n) (node x r₁) (node y r₂) = cong (node x) (sB-glue n r₁ r₂)

  sB-glue : ∀ n (r₁ r₂ : B) → bdmB n (glueB n r₁ r₂) ≡ bdmB n r₁
  sB-glue n nil            _              = refl
  sB-glue n (cons T y r)   nil            = refl
  sB-glue n (cons T₁ y r₁) (cons T₂ _ r₂) = cong₂ (λ a b → cons a y b) (s-glue n T₁ T₂) (sB-glue n r₁ r₂)

mutual
  t-glue : ∀ n (x y : Tr) → bdp n x ≡ bdm n y → bdp n (glue n x y) ≡ bdp n y
  t-glue zero (node x r₁) (node y r₂) p =
    cong (λ v → node v nil) (trans (lastv-++ x r₁ r₂) (cong (λ v → lastv v r₂) (node-x p)))
  t-glue (suc n) (node x r₁) (node y r₂) p with node-x p
  ... | refl = cong (node x) (tB-glue n r₁ r₂ (node-r p))

  tB-glue : ∀ n (r₁ r₂ : B) → bdpB n r₁ ≡ bdmB n r₂ → bdpB n (glueB n r₁ r₂) ≡ bdpB n r₂
  tB-glue n nil            nil            _ = refl
  tB-glue n nil            (cons _ _ _)   ()
  tB-glue n (cons _ _ _)   nil            ()
  tB-glue n (cons T₁ y r₁) (cons T₂ y₂ r₂) p with cons-y p
  ... | refl = cong₂ (λ a b → cons a y b) (t-glue n T₁ T₂ (cons-T p)) (tB-glue n r₁ r₂ (cons-r p))

mutual
  s-glue< : ∀ {m n} (x y : Tr) → m < n → bdm m (glue n x y) ≡ bdm m x
  s-glue< {zero}  {suc n} (node x r₁) (node y r₂) _       = refl
  s-glue< {suc m} {suc n} (node x r₁) (node y r₂) (s≤s l) = cong (node x) (sB-glue< r₁ r₂ l)

  sB-glue< : ∀ {m n} (r₁ r₂ : B) → m < n → bdmB m (glueB n r₁ r₂) ≡ bdmB m r₁
  sB-glue< nil            _              l = refl
  sB-glue< (cons T y r)   nil            l = refl
  sB-glue< (cons T₁ y r₁) (cons T₂ _ r₂) l = cong₂ (λ a b → cons a y b) (s-glue< T₁ T₂ l) (sB-glue< r₁ r₂ l)

mutual
  t-glue< : ∀ {m n} (x y : Tr) → m < n → bdp n x ≡ bdm n y → bdp m (glue n x y) ≡ bdp m y
  t-glue< {zero} {suc n} (node x r₁) (node y r₂) _ p =
    cong (λ v → node v nil)
      (trans (lastv-glueB n x r₁ r₂)
        (trans (sym (lastv-bdpB n x r₁))
          (trans (cong₂ lastv (node-x p) (node-r p)) (lastv-bdmB n y r₂))))
  t-glue< {suc m} {suc n} (node x r₁) (node y r₂) (s≤s l) p with node-x p
  ... | refl = cong (node x) (tB-glue< r₁ r₂ l (node-r p))

  tB-glue< : ∀ {m n} (r₁ r₂ : B) → m < n → bdpB n r₁ ≡ bdmB n r₂ → bdpB m (glueB n r₁ r₂) ≡ bdpB m r₂
  tB-glue< nil            nil            l _ = refl
  tB-glue< nil            (cons _ _ _)   l ()
  tB-glue< (cons _ _ _)   nil            l ()
  tB-glue< (cons T₁ y r₁) (cons T₂ y₂ r₂) l p with cons-y p
  ... | refl = cong₂ (λ a b → cons a y b) (t-glue< T₁ T₂ l (cons-T p)) (tB-glue< r₁ r₂ l (cons-r p))

mutual
  s-glue> : ∀ {m n} (x y : Tr) → n < m → bdm m (glue n x y) ≡ glue n (bdm m x) (bdm m y)
  s-glue> {suc m} {zero}  (node x r₁) (node y r₂) _       = cong (node x) (bdmB-++ m r₁ r₂)
  s-glue> {suc m} {suc n} (node x r₁) (node y r₂) (s≤s l) = cong (node x) (sB-glue> r₁ r₂ l)

  sB-glue> : ∀ {m n} (r₁ r₂ : B) → n < m → bdmB m (glueB n r₁ r₂) ≡ glueB n (bdmB m r₁) (bdmB m r₂)
  sB-glue> nil            _              l = refl
  sB-glue> (cons T y r)   nil            l = refl
  sB-glue> (cons T₁ y r₁) (cons T₂ _ r₂) l = cong₂ (λ a b → cons a y b) (s-glue> T₁ T₂ l) (sB-glue> r₁ r₂ l)

mutual
  t-glue> : ∀ {m n} (x y : Tr) → n < m → bdp m (glue n x y) ≡ glue n (bdp m x) (bdp m y)
  t-glue> {suc m} {zero}  (node x r₁) (node y r₂) _       = cong (node x) (bdpB-++ m r₁ r₂)
  t-glue> {suc m} {suc n} (node x r₁) (node y r₂) (s≤s l) = cong (node x) (tB-glue> r₁ r₂ l)

  tB-glue> : ∀ {m n} (r₁ r₂ : B) → n < m → bdpB m (glueB n r₁ r₂) ≡ glueB n (bdpB m r₁) (bdpB m r₂)
  tB-glue> nil            _              l = refl
  tB-glue> (cons T y r)   nil            l = refl
  tB-glue> (cons T₁ y r₁) (cons T₂ _ r₂) l = cong₂ (λ a b → cons a y b) (t-glue> T₁ T₂ l) (tB-glue> r₁ r₂ l)

------------------------------------------------------------------------
-- (iv) Units.

mutual
  unitl : ∀ n (x : Tr) → glue n (bdm n x) x ≡ x
  unitl zero    (node x r) = refl
  unitl (suc n) (node x r) = cong (node x) (unitlB n r)

  unitlB : ∀ n (r : B) → glueB n (bdmB n r) r ≡ r
  unitlB n nil          = refl
  unitlB n (cons T y r) = cong₂ (λ a b → cons a y b) (unitl n T) (unitlB n r)

mutual
  unitr : ∀ n (x : Tr) → glue n x (bdp n x) ≡ x
  unitr zero    (node x r) = cong (node x) (++B-nil r)
  unitr (suc n) (node x r) = cong (node x) (unitrB n r)

  unitrB : ∀ n (r : B) → glueB n r (bdpB n r) ≡ r
  unitrB n nil          = refl
  unitrB n (cons T y r) = cong₂ (λ a b → cons a y b) (unitr n T) (unitrB n r)

------------------------------------------------------------------------
-- (v) Associativity.

mutual
  assocT : ∀ n (x y z : Tr) → bdp n x ≡ bdm n y → bdp n y ≡ bdm n z →
           glue n (glue n x y) z ≡ glue n x (glue n y z)
  assocT zero    (node x r₁) (node y r₂) (node z r₃) _ _ = cong (node x) (++B-assoc r₁ r₂ r₃)
  assocT (suc n) (node x r₁) (node y r₂) (node z r₃) p q = cong (node x) (assocB n r₁ r₂ r₃ (node-r p) (node-r q))

  assocB : ∀ n (r₁ r₂ r₃ : B) → bdpB n r₁ ≡ bdmB n r₂ → bdpB n r₂ ≡ bdmB n r₃ →
           glueB n (glueB n r₁ r₂) r₃ ≡ glueB n r₁ (glueB n r₂ r₃)
  assocB n nil              _                _                _  _  = refl
  assocB n (cons _ _ _)     nil              _                () _
  assocB n (cons _ _ _)     (cons _ _ _)     nil              _  ()
  assocB n (cons T₁ y₁ r₁)  (cons T₂ y₂ r₂)  (cons T₃ y₃ r₃)  p  q  =
    cong₂ (λ a b → cons a y₁ b) (assocT n T₁ T₂ T₃ (cons-T p) (cons-T q)) (assocB n r₁ r₂ r₃ (cons-r p) (cons-r q))

------------------------------------------------------------------------
-- (vi) Interchange.

mutual
  interT : ∀ {m n} (x y z w : Tr) → m < n → bdp n x ≡ bdm n y → bdp n z ≡ bdm n w →
           bdp m (glue n x y) ≡ bdm m (glue n z w) →
           glue m (glue n x y) (glue n z w) ≡ glue n (glue m x z) (glue m y w)
  interT {zero} {suc n} (node a rx) (node b ry) (node c rz) (node e rw) _ p q r =
    cong (node a) (sym (glueB-++ n (sl-from n rx ry (node-r p)) rz rw))
  interT {suc m} {suc n} (node a rx) (node b ry) (node c rz) (node e rw) (s≤s l) p q r =
    cong (node a) (interB rx ry rz rw l (node-r p) (node-r q) (node-r r))

  interB : ∀ {m n} (rx ry rz rw : B) → m < n → bdpB n rx ≡ bdmB n ry → bdpB n rz ≡ bdmB n rw →
           bdpB m (glueB n rx ry) ≡ bdmB m (glueB n rz rw) →
           glueB m (glueB n rx ry) (glueB n rz rw) ≡ glueB n (glueB m rx rz) (glueB m ry rw)
  interB nil nil nil nil l _ _ _ = refl
  interB nil (cons _ _ _) _ _ l () _ _
  interB (cons _ _ _) nil _ _ l () _ _
  interB _ _ (cons _ _ _) nil l _ () _
  interB _ _ nil (cons _ _ _) l _ () _
  interB nil nil (cons _ _ _) (cons _ _ _) l _ _ ()
  interB (cons _ _ _) (cons _ _ _) nil nil l _ _ ()
  interB (cons Tx yx rx) (cons Ty yy ry) (cons Tz yz rz) (cons Tw yw rw) l p q r =
    cong₂ (λ a b → cons a yx b)
      (interT Tx Ty Tz Tw l (cons-T p) (cons-T q) (cons-T r))
      (interB rx ry rz rw l (cons-r p) (cons-r q) (cons-r r))

------------------------------------------------------------------------
-- The strict ω-category of A-labelled trees.

𝒯 : ωCat
𝒯 = record
  { C    = Tr
  ; src  = bdm
  ; tgt  = bdp
  ; comp = λ n x y _ → glue n x y
  ; src-src-< = ss<
  ; src-tgt-< = st<
  ; tgt-src-< = ts<
  ; tgt-tgt-< = tt<
  ; src-src-≥ = ss≥
  ; tgt-src-≥ = ts≥
  ; src-tgt-≥ = st≥
  ; tgt-tgt-≥ = tt≥
  ; src-comp = λ n x y _ → s-glue n x y
  ; tgt-comp = λ n x y p → t-glue n x y p
  ; src-comp-< = λ x y _ l → s-glue< x y l
  ; tgt-comp-< = λ x y p l → t-glue< x y l p
  ; src-comp-> = λ x y _ l _ → s-glue> x y l
  ; tgt-comp-> = λ x y _ l _ → t-glue> x y l
  ; unit-l = λ n x _ → unitl n x
  ; unit-r = λ n x _ → unitr n x
  ; assoc = λ n x y z p _ p′ _ → assocT n x y z p p′
  ; interchange = λ x y z w l p q r _ _ _ → interT x y z w l p q r
  }
