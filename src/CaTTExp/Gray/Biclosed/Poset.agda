------------------------------------------------------------------------
-- A universe of finite posets with decidable order, for the monotone
-- model of the biclosed kernel (PosetModel.agda).
--
-- Elements are untyped trees U (numbers, pairs, tables).  A code says
-- which trees belong to a poset and how they are ordered:
--   cnat b      the chain 0 < 1 < … < b
--   cpair a b   the product order
--   ctab a c    monotone maps from a to c, as tables indexed by the
--               enumeration els a, ordered pointwise
-- Every poset is finite (els enumerates it), inhabited (defC), and its
-- order is reflexive, transitive and antisymmetric on its elements.
-- Application app and tabulation tabF of tables satisfy β and η.
-- No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Poset where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.ListOps using (map; length)
open import CaTTExp.Gray.Biclosed.Rows using (leq)
open import CaTTExp.Gray.Biclosed.ListLemmas using (_⊎′_; inl; inr; length-map)

------------------------------------------------------------------------
-- Membership

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs} → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

∈-++ˡ : ∀ {A : Set} {x : A} {xs} ys → x ∈ xs → x ∈ (xs ++ ys)
∈-++ˡ ys hd     = hd
∈-++ˡ ys (tl p) = tl (∈-++ˡ ys p)

∈-++ʳ : ∀ {A : Set} {x : A} xs {ys} → x ∈ ys → x ∈ (xs ++ ys)
∈-++ʳ []       p = p
∈-++ʳ (_ ∷ xs) p = tl (∈-++ʳ xs p)

∈-++-inv : ∀ {A : Set} {x : A} xs {ys} → x ∈ (xs ++ ys) → (x ∈ xs) ⊎′ (x ∈ ys)
∈-++-inv []       p      = inr p
∈-++-inv (y ∷ xs) hd     = inl hd
∈-++-inv (y ∷ xs) (tl p) with ∈-++-inv xs p
... | inl q = inl (tl q)
... | inr q = inr q

∈-map : ∀ {A B : Set} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
∈-map f hd     = hd
∈-map f (tl p) = tl (∈-map f p)

∈-map-inv : ∀ {A B : Set} (f : A → B) {y} xs → y ∈ map f xs → Σ A (λ x → (x ∈ xs) × (y ≡ f x))
∈-map-inv f (x ∷ xs) hd     = x , hd , refl
∈-map-inv f (x ∷ xs) (tl p) with ∈-map-inv f xs p
... | z , q , e = z , tl q , e

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

∈-concatMap : ∀ {A B : Set} (f : A → List B) {x y xs} → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
∈-concatMap f {xs = x ∷ xs} hd     q = ∈-++ˡ (concatMap f xs) q
∈-concatMap f {xs = z ∷ xs} (tl p) q = ∈-++ʳ (f z) (∈-concatMap f p q)

∈-concatMap-inv : ∀ {A B : Set} (f : A → List B) {y} xs → y ∈ concatMap f xs →
                  Σ A (λ x → (x ∈ xs) × (y ∈ f x))
∈-concatMap-inv f (x ∷ xs) p with ∈-++-inv (f x) p
... | inl q = x , hd , q
... | inr q with ∈-concatMap-inv f xs q
...   | z , m , r = z , tl m , r

map-cong-∈ : ∀ {A B : Set} (f g : A → B) xs → (∀ {x} → x ∈ xs → f x ≡ g x) → map f xs ≡ map g xs
map-cong-∈ f g []       h = refl
map-cong-∈ f g (x ∷ xs) h = cong₂ _∷_ (h hd) (map-cong-∈ f g xs (λ m → h (tl m)))

------------------------------------------------------------------------
-- Booleans

∧I : ∀ {a b} → T a → T b → T (a ∧ b)
∧I {true} {true} _ _ = tt

∨-not-elim : ∀ a b → T (not a ∨ b) → T a → T b
∨-not-elim true  b p _ = p

∨-not-intro : ∀ a b → (T a → T b) → T (not a ∨ b)
∨-not-intro true  b f = f tt
∨-not-intro false b f = tt

T-≡ : ∀ {b} → T b → b ≡ true
T-≡ {true} _ = refl

all-∈ : ∀ {A : Set} (p : A → Bool) {x xs} → T (all p xs) → x ∈ xs → T (p x)
all-∈ p {xs = y ∷ xs} q hd     = ∧-fst q
all-∈ p {xs = y ∷ xs} q (tl m) = all-∈ p (∧-snd {p y} q) m

all-I : ∀ {A : Set} (p : A → Bool) xs → (∀ {x} → x ∈ xs → T (p x)) → T (all p xs)
all-I p []       f = tt
all-I p (x ∷ xs) f = ∧I (f hd) (all-I p xs (λ m → f (tl m)))

filter-∈ : ∀ {A : Set} (p : A → Bool) {x} xs → x ∈ xs → T (p x) → x ∈ filter p xs
filter-∈ p (y ∷ xs) hd q with p y
... | true  = hd
filter-∈ p (y ∷ xs) (tl m) q with p y
... | true  = tl (filter-∈ p xs m q)
... | false = filter-∈ p xs m q

filter-sound : ∀ {A : Set} (p : A → Bool) {x} xs → x ∈ filter p xs → T (p x)
filter-sound p (y ∷ xs) m with p y in e
filter-sound p (y ∷ xs) hd     | true  = subst T (sym e) tt
filter-sound p (y ∷ xs) (tl m) | true  = filter-sound p xs m
filter-sound p (y ∷ xs) m      | false = filter-sound p xs m

------------------------------------------------------------------------
-- leq

leq-refl : ∀ n → T (leq n n)
leq-refl zero    = tt
leq-refl (suc n) = leq-refl n

leq-trans : ∀ a b c → T (leq a b) → T (leq b c) → T (leq a c)
leq-trans zero    b       c       _ _ = tt
leq-trans (suc a) zero    c       () q
leq-trans (suc a) (suc b) zero    p ()
leq-trans (suc a) (suc b) (suc c) p q = leq-trans a b c p q

leq-antisym : ∀ a b → T (leq a b) → T (leq b a) → a ≡ b
leq-antisym zero    zero    _ _ = refl
leq-antisym zero    (suc b) _ ()
leq-antisym (suc a) zero    () _
leq-antisym (suc a) (suc b) p q = cong suc (leq-antisym a b p q)

leq-wk : ∀ a b → T (leq a b) → T (leq a (suc b))
leq-wk zero    b       _ = tt
leq-wk (suc a) zero    ()
leq-wk (suc a) (suc b) p = leq-wk a b p

leq-top : ∀ p b → T (leq p (suc b)) → leq p b ≡ false → p ≡ suc b
leq-top zero          b       _ ()
leq-top (suc zero)    zero    _ _ = refl
leq-top (suc (suc p)) zero    () _
leq-top (suc p)       (suc b) q e = cong suc (leq-top p b q e)

------------------------------------------------------------------------
-- Trees and codes

data U : Set where
  nat : Nat → U
  pr  : U → U → U
  tab : List U → U

data Code : Set where
  cnat  : Nat → Code
  cpair : Code → Code → Code
  ctab  : Code → Code → Code

nats : Nat → List U
nats zero    = nat zero ∷ []
nats (suc b) = nat (suc b) ∷ nats b

zipL : List U → List U → List (U × U)
zipL (a ∷ as) (b ∷ bs) = (a , b) ∷ zipL as bs
zipL _        _        = []

allZ : (U → U → Bool) → List U → List U → Bool
allZ r []       []       = true
allZ r (a ∷ as) (b ∷ bs) = r a b ∧ allZ r as bs
allZ r _        _        = false

vecs : Nat → List U → List (List U)
vecs zero    xs = [] ∷ []
vecs (suc n) xs = concatMap (λ x → map (x ∷_) (vecs n xs)) xs

monoP : (U → U → Bool) → (U → U → Bool) → List (U × U) → Bool
monoP la lc ps = all (λ p → all (λ q → not (la (fst p) (fst q)) ∨ lc (snd p) (snd q)) ps) ps

leC : Code → U → U → Bool
leC (cnat b)    (nat p)  (nat q)    = leq p q
leC (cpair a b) (pr x y) (pr x′ y′) = leC a x x′ ∧ leC b y y′
leC (ctab a c)  (tab ts) (tab ss)   = allZ (leC c) ts ss
leC _           _        _          = false

mutual
  inC : Code → U → Bool
  inC (cnat b)    (nat p)  = leq p b
  inC (cpair a b) (pr x y) = inC a x ∧ inC b y
  inC (ctab a c)  (tab ts) = (length ts ==ℕ length (els a)) ∧ tabOK a c ts
  inC _           _        = false

  -- entries in c, monotone along the enumeration of a
  tabOK : Code → Code → List U → Bool
  tabOK a c ts = all (inC c) ts ∧ monoP (leC a) (leC c) (zipL (els a) ts)

  els : Code → List U
  els (cnat b)    = nats b
  els (cpair a b) = concatMap (λ x → map (pr x) (els b)) (els a)
  els (ctab a c)  = map tab (filter (tabOK a c) (vecs (length (els a)) (els c)))

defC : Code → U
defC (cnat b)    = nat zero
defC (cpair a b) = pr (defC a) (defC b)
defC (ctab a c)  = tab (map (λ _ → defC c) (els a))

In : Code → U → Set
In c u = T (inC c u)

Le : Code → U → U → Set
Le c u v = T (leC c u v)

------------------------------------------------------------------------
-- Views of membership

inC-nat : ∀ b u → In (cnat b) u → Σ Nat (λ p → (u ≡ nat p) × T (leq p b))
inC-nat b (nat p)  q = p , refl , q
inC-nat b (pr _ _) ()
inC-nat b (tab _)  ()

inC-pair : ∀ a b u → In (cpair a b) u → Σ U (λ x → Σ U (λ y → (u ≡ pr x y) × In a x × In b y))
inC-pair a b (nat _)  ()
inC-pair a b (pr x y) q = x , y , refl , ∧-fst q , ∧-snd {inC a x} q
inC-pair a b (tab _)  ()

inC-tab : ∀ a c u → In (ctab a c) u →
          Σ (List U) (λ ts → (u ≡ tab ts) × (length ts ≡ length (els a)) × T (tabOK a c ts))
inC-tab a c (nat _)  ()
inC-tab a c (pr _ _) ()
inC-tab a c (tab ts) q = ts , refl , ==ℕ-sound _ _ (∧-fst q) , ∧-snd {length ts ==ℕ length (els a)} q

tabOK-all : ∀ a c ts → T (tabOK a c ts) → T (all (inC c) ts)
tabOK-all a c ts q = ∧-fst q

tabOK-mono : ∀ a c ts → T (tabOK a c ts) → T (monoP (leC a) (leC c) (zipL (els a) ts))
tabOK-mono a c ts q = ∧-snd {all (inC c) ts} q

------------------------------------------------------------------------
-- Zips

zip-fst : ∀ {p} es ts → p ∈ zipL es ts → fst p ∈ es
zip-fst (e ∷ es) (t ∷ ts) hd     = hd
zip-fst (e ∷ es) (t ∷ ts) (tl m) = tl (zip-fst es ts m)

zip-snd : ∀ {p} es ts → p ∈ zipL es ts → snd p ∈ ts
zip-snd (e ∷ es) (t ∷ ts) hd     = hd
zip-snd (e ∷ es) (t ∷ ts) (tl m) = tl (zip-snd es ts m)

zip-map : ∀ (f : U → U) {p} es → p ∈ zipL es (map f es) → snd p ≡ f (fst p)
zip-map f (e ∷ es) hd     = refl
zip-map f (e ∷ es) (tl m) = zip-map f es m

monoP-elim : ∀ la lc ps {p q} → T (monoP la lc ps) → p ∈ ps → q ∈ ps →
             T (la (fst p) (fst q)) → T (lc (snd p) (snd q))
monoP-elim la lc ps {p} {q} h mp mq l =
  ∨-not-elim (la (fst p) (fst q)) _
    (all-∈ (λ q → not (la (fst p) (fst q)) ∨ lc (snd p) (snd q))
       (all-∈ (λ p → all (λ q → not (la (fst p) (fst q)) ∨ lc (snd p) (snd q)) ps) h mp) mq) l

monoP-intro : ∀ la lc ps → (∀ {p q} → p ∈ ps → q ∈ ps → T (la (fst p) (fst q)) → T (lc (snd p) (snd q))) →
              T (monoP la lc ps)
monoP-intro la lc ps f =
  all-I _ ps (λ {p} mp → all-I _ ps (λ {q} mq → ∨-not-intro (la (fst p) (fst q)) _ (f mp mq)))

------------------------------------------------------------------------
-- The order: reflexive, transitive, antisymmetric

mutual
  leC-refl : ∀ c u → In c u → Le c u u
  leC-refl (cnat b)    u q with inC-nat b u q
  ... | p , refl , _ = leq-refl p
  leC-refl (cpair a b) u q with inC-pair a b u q
  ... | x , y , refl , qx , qy = ∧I (leC-refl a x qx) (leC-refl b y qy)
  leC-refl (ctab a c)  u q with inC-tab a c u q
  ... | ts , refl , _ , ok = allZ-refl c ts (tabOK-all a c ts ok)

  allZ-refl : ∀ c ts → T (all (inC c) ts) → T (allZ (leC c) ts ts)
  allZ-refl c []       _ = tt
  allZ-refl c (t ∷ ts) q = ∧I (leC-refl c t (∧-fst q)) (allZ-refl c ts (∧-snd {inC c t} q))

mutual
  leC-trans : ∀ c u v w → In c u → In c v → In c w → Le c u v → Le c v w → Le c u w
  leC-trans (cnat b) u v w qu qv qw l m with inC-nat b u qu | inC-nat b v qv | inC-nat b w qw
  ... | p , refl , _ | p′ , refl , _ | p″ , refl , _ = leq-trans p p′ p″ l m
  leC-trans (cpair a b) u v w qu qv qw l m
    with inC-pair a b u qu | inC-pair a b v qv | inC-pair a b w qw
  ... | x , y , refl , qx , qy | x′ , y′ , refl , qx′ , qy′ | x″ , y″ , refl , qx″ , qy″ =
    ∧I (leC-trans a x x′ x″ qx qx′ qx″ (∧-fst l) (∧-fst m))
       (leC-trans b y y′ y″ qy qy′ qy″ (∧-snd {leC a x x′} l) (∧-snd {leC a x′ x″} m))
  leC-trans (ctab a c) u v w qu qv qw l m
    with inC-tab a c u qu | inC-tab a c v qv | inC-tab a c w qw
  ... | ts , refl , _ , ok | ss , refl , _ , ok′ | rs , refl , _ , ok″ =
    allZ-trans c ts ss rs (tabOK-all a c ts ok) (tabOK-all a c ss ok′) (tabOK-all a c rs ok″) l m

  allZ-trans : ∀ c ts ss rs → T (all (inC c) ts) → T (all (inC c) ss) → T (all (inC c) rs) →
               T (allZ (leC c) ts ss) → T (allZ (leC c) ss rs) → T (allZ (leC c) ts rs)
  allZ-trans c []       []       []       _ _ _ _ _ = tt
  allZ-trans c []       []       (r ∷ rs) _ _ _ _ ()
  allZ-trans c []       (s ∷ ss) rs       _ _ _ () _
  allZ-trans c (t ∷ ts) []       rs       _ _ _ () _
  allZ-trans c (t ∷ ts) (s ∷ ss) []       _ _ _ _ ()
  allZ-trans c (t ∷ ts) (s ∷ ss) (r ∷ rs) qt qs qr l m =
    ∧I (leC-trans c t s r (∧-fst qt) (∧-fst qs) (∧-fst qr) (∧-fst l) (∧-fst m))
       (allZ-trans c ts ss rs (∧-snd {inC c t} qt) (∧-snd {inC c s} qs) (∧-snd {inC c r} qr)
          (∧-snd {leC c t s} l) (∧-snd {leC c s r} m))

mutual
  leC-antisym : ∀ c u v → In c u → In c v → Le c u v → Le c v u → u ≡ v
  leC-antisym (cnat b) u v qu qv l m with inC-nat b u qu | inC-nat b v qv
  ... | p , refl , _ | p′ , refl , _ = cong nat (leq-antisym p p′ l m)
  leC-antisym (cpair a b) u v qu qv l m with inC-pair a b u qu | inC-pair a b v qv
  ... | x , y , refl , qx , qy | x′ , y′ , refl , qx′ , qy′ =
    cong₂ pr (leC-antisym a x x′ qx qx′ (∧-fst l) (∧-fst m))
             (leC-antisym b y y′ qy qy′ (∧-snd {leC a x x′} l) (∧-snd {leC a x′ x} m))
  leC-antisym (ctab a c) u v qu qv l m with inC-tab a c u qu | inC-tab a c v qv
  ... | ts , refl , _ , ok | ss , refl , _ , ok′ =
    cong tab (allZ-antisym c ts ss (tabOK-all a c ts ok) (tabOK-all a c ss ok′) l m)

  allZ-antisym : ∀ c ts ss → T (all (inC c) ts) → T (all (inC c) ss) →
                 T (allZ (leC c) ts ss) → T (allZ (leC c) ss ts) → ts ≡ ss
  allZ-antisym c []       []       _ _ _ _ = refl
  allZ-antisym c []       (s ∷ ss) _ _ () _
  allZ-antisym c (t ∷ ts) []       _ _ () _
  allZ-antisym c (t ∷ ts) (s ∷ ss) qt qs l m =
    cong₂ _∷_ (leC-antisym c t s (∧-fst qt) (∧-fst qs) (∧-fst l) (∧-fst m))
              (allZ-antisym c ts ss (∧-snd {inC c t} qt) (∧-snd {inC c s} qs)
                 (∧-snd {leC c t s} l) (∧-snd {leC c s t} m))

------------------------------------------------------------------------
-- Enumerations are sound and complete

nats-sound : ∀ b {u} → u ∈ nats b → Σ Nat (λ p → (u ≡ nat p) × T (leq p b))
nats-sound zero    hd     = zero , refl , tt
nats-sound zero    (tl ())
nats-sound (suc b) hd     = suc b , refl , leq-refl b
nats-sound (suc b) (tl m) with nats-sound b m
... | p , e , q = p , e , leq-wk p b q

nats-complete : ∀ b p → T (leq p b) → nat p ∈ nats b
nats-complete zero    zero    _ = hd
nats-complete zero    (suc p) ()
nats-complete (suc b) p q with leq p b in e
... | true  = tl (nats-complete b p (subst T (sym e) tt))
... | false = subst (λ x → nat x ∈ nats (suc b)) (sym (leq-top p b q e)) hd

vecs-len : ∀ n xs {ts} → ts ∈ vecs n xs → length ts ≡ n
vecs-len zero    xs hd      = refl
vecs-len zero    xs (tl ())
vecs-len (suc n) xs m with ∈-concatMap-inv (λ x → map (x ∷_) (vecs n xs)) xs m
... | x , _ , m′ with ∈-map-inv (x ∷_) (vecs n xs) m′
...   | ts′ , m″ , refl = cong suc (vecs-len n xs m″)

vecs-complete : ∀ n xs ts → length ts ≡ n → (∀ {t} → t ∈ ts → t ∈ xs) → ts ∈ vecs n xs
vecs-complete zero    xs []       refl f = hd
vecs-complete (suc n) xs (t ∷ ts) e    f =
  ∈-concatMap (λ x → map (x ∷_) (vecs n xs)) (f hd)
    (∈-map (t ∷_) (vecs-complete n xs ts (suc-inj e) (λ m → f (tl m))))
  where
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

==ℕ-from : ∀ m n → m ≡ n → T (m ==ℕ n)
==ℕ-from m .m refl = ==ℕ-refl m

mutual
  els-sound : ∀ c {u} → u ∈ els c → In c u
  els-sound (cnat b) m with nats-sound b m
  ... | p , refl , q = q
  els-sound (cpair a b) m with ∈-concatMap-inv (λ x → map (pr x) (els b)) (els a) m
  ... | x , mx , m′ with ∈-map-inv (pr x) (els b) m′
  ...   | y , my , refl = ∧I (els-sound a mx) (els-sound b my)
  els-sound (ctab a c) m with ∈-map-inv tab (filter (tabOK a c) (vecs (length (els a)) (els c))) m
  ... | ts , mt , refl =
    ∧I (==ℕ-from _ _ (vecs-len (length (els a)) (els c)
                        (filter-in (tabOK a c) (vecs (length (els a)) (els c)) mt)))
       (filter-sound (tabOK a c) (vecs (length (els a)) (els c)) mt)

  -- an element of a filtered list is in the list
  filter-in : ∀ {A : Set} (p : A → Bool) xs {x} → x ∈ filter p xs → x ∈ xs
  filter-in p (y ∷ xs) m with p y
  filter-in p (y ∷ xs) hd     | true  = hd
  filter-in p (y ∷ xs) (tl m) | true  = tl (filter-in p xs m)
  filter-in p (y ∷ xs) m      | false = tl (filter-in p xs m)

els-complete : ∀ c u → In c u → u ∈ els c
els-complete (cnat b) u q with inC-nat b u q
... | p , refl , l = nats-complete b p l
els-complete (cpair a b) u q with inC-pair a b u q
... | x , y , refl , qx , qy =
  ∈-concatMap (λ x → map (pr x) (els b)) (els-complete a x qx) (∈-map (pr x) (els-complete b y qy))
els-complete (ctab a c) u q with inC-tab a c u q
... | ts , refl , len , ok =
  ∈-map tab (filter-∈ (tabOK a c) (vecs (length (els a)) (els c))
    (vecs-complete (length (els a)) (els c) ts len
       (λ m → els-complete c _ (all-∈ (inC c) (tabOK-all a c ts ok) m)))
    ok)

------------------------------------------------------------------------
-- Every poset is inhabited

inC-def : ∀ c → In c (defC c)
inC-def (cnat b)    = tt
inC-def (cpair a b) = ∧I (inC-def a) (inC-def b)
inC-def (ctab a c)  =
  ∧I (==ℕ-from _ _ (length-map (λ _ → defC c) (els a)))
     (∧I (all-I (inC c) (map (λ _ → defC c) (els a))
            (λ m → subst (In c) (sym (snd (snd (∈-map-inv (λ _ → defC c) (els a) m)))) (inC-def c)))
         (monoP-intro (leC a) (leC c) (zipL (els a) (map (λ _ → defC c) (els a)))
            (λ {p} {q} mp mq _ →
               subst₂′ (Le c) (sym (zip-map (λ _ → defC c) (els a) mp))
                              (sym (zip-map (λ _ → defC c) (els a) mq))
                       (leC-refl c (defC c) (inC-def c)))))
  where
  subst₂′ : ∀ {A : Set} (P : A → A → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
  subst₂′ P refl refl p = p

------------------------------------------------------------------------
-- Decidable equality of trees

mutual
  eqU : U → U → Bool
  eqU (nat p)  (nat q)  = p ==ℕ q
  eqU (pr a b) (pr c d) = eqU a c ∧ eqU b d
  eqU (tab ts) (tab ss) = eqUs ts ss
  eqU _        _        = false

  eqUs : List U → List U → Bool
  eqUs []       []       = true
  eqUs (a ∷ as) (b ∷ bs) = eqU a b ∧ eqUs as bs
  eqUs _        _        = false

mutual
  eqU-sound : ∀ u v → T (eqU u v) → u ≡ v
  eqU-sound (nat p)  (nat q)  e = cong nat (==ℕ-sound p q e)
  eqU-sound (pr a b) (pr c d) e = cong₂ pr (eqU-sound a c (∧-fst e)) (eqU-sound b d (∧-snd {eqU a c} e))
  eqU-sound (tab ts) (tab ss) e = cong tab (eqUs-sound ts ss e)
  eqU-sound (nat _)  (pr _ _) ()
  eqU-sound (nat _)  (tab _)  ()
  eqU-sound (pr _ _) (nat _)  ()
  eqU-sound (pr _ _) (tab _)  ()
  eqU-sound (tab _)  (nat _)  ()
  eqU-sound (tab _)  (pr _ _) ()

  eqUs-sound : ∀ ts ss → T (eqUs ts ss) → ts ≡ ss
  eqUs-sound []       []       _ = refl
  eqUs-sound (a ∷ as) (b ∷ bs) e = cong₂ _∷_ (eqU-sound a b (∧-fst e)) (eqUs-sound as bs (∧-snd {eqU a b} e))
  eqUs-sound []       (_ ∷ _)  ()
  eqUs-sound (_ ∷ _)  []       ()

mutual
  eqU-refl : ∀ u → T (eqU u u)
  eqU-refl (nat p)  = ==ℕ-refl p
  eqU-refl (pr a b) = ∧I (eqU-refl a) (eqU-refl b)
  eqU-refl (tab ts) = eqUs-refl ts

  eqUs-refl : ∀ ts → T (eqUs ts ts)
  eqUs-refl []       = tt
  eqUs-refl (t ∷ ts) = ∧I (eqU-refl t) (eqUs-refl ts)

------------------------------------------------------------------------
-- Lookup in a table

assocU : List U → List U → U → U
assocU (e ∷ es) (t ∷ ts) a = if eqU e a then t else assocU es ts a
assocU _        _        a = nat zero

assoc-map : ∀ (f : U → U) es a → a ∈ es → assocU es (map f es) a ≡ f a
assoc-map f (e ∷ es) a m with eqU e a in eq
assoc-map f (e ∷ es) a m       | true  = cong f (eqU-sound e a (subst T (sym eq) tt))
assoc-map f (e ∷ es) .e hd     | false = ⊥-elim (subst T eq (eqU-refl e))
assoc-map f (e ∷ es) a (tl m)  | false = assoc-map f es a m

assoc-zip : ∀ es ts a → a ∈ es → length es ≡ length ts → (a , assocU es ts a) ∈ zipL es ts
assoc-zip (e ∷ es) []       a m ()
assoc-zip (e ∷ es) (t ∷ ts) a m l with eqU e a in eq
assoc-zip (e ∷ es) (t ∷ ts) a m      l | true  =
  subst (λ z → (z , t) ∈ zipL (e ∷ es) (t ∷ ts)) (eqU-sound e a (subst T (sym eq) tt)) hd
assoc-zip (e ∷ es) (t ∷ ts) .e hd    l | false = ⊥-elim (subst T eq (eqU-refl e))
assoc-zip (e ∷ es) (t ∷ ts) a (tl m) l | false = tl (assoc-zip es ts a m (suc-inj l))
  where
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

assoc-le : ∀ (r : U → U → Bool) es ts ss a → a ∈ es → length es ≡ length ts →
           T (allZ r ts ss) → T (r (assocU es ts a) (assocU es ss a))
assoc-le r (e ∷ es) []       ss       a m () q
assoc-le r (e ∷ es) (t ∷ ts) []       a m l  ()
assoc-le r (e ∷ es) (t ∷ ts) (s ∷ ss) a m l  q with eqU e a in eq
assoc-le r (e ∷ es) (t ∷ ts) (s ∷ ss) a m      l q | true  = ∧-fst q
assoc-le r (e ∷ es) (t ∷ ts) (s ∷ ss) .e hd    l q | false = ⊥-elim (subst T eq (eqU-refl e))
assoc-le r (e ∷ es) (t ∷ ts) (s ∷ ss) a (tl m) l q | false =
  assoc-le r es ts ss a m (suc-inj l) (∧-snd {r t s} q)
  where
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

------------------------------------------------------------------------
-- Application and tabulation: β and η

app : Code → U → U → U
app a (tab ts) x = assocU (els a) ts x
app a _        x = nat zero

tabF : Code → (U → U) → U
tabF a f = tab (map f (els a))

app-tab : ∀ a f x → In a x → app a (tabF a f) x ≡ f x
app-tab a f x q = assoc-map f (els a) x (els-complete a x q)

-- a monotone table is a function of its index
tab-fun : ∀ a c ts → T (tabOK a c ts) → ∀ {p q} → p ∈ zipL (els a) ts → q ∈ zipL (els a) ts →
          fst p ≡ fst q → snd p ≡ snd q
tab-fun a c ts ok {p} {q} mp mq e =
  leC-antisym c (snd p) (snd q) ip iq
    (monoP-elim (leC a) (leC c) _ (tabOK-mono a c ts ok) mp mq
       (subst (λ z → Le a (fst p) z) e (leC-refl a (fst p) (els-sound a (zip-fst (els a) ts mp)))))
    (monoP-elim (leC a) (leC c) _ (tabOK-mono a c ts ok) mq mp
       (subst (λ z → Le a z (fst p)) e (leC-refl a (fst p) (els-sound a (zip-fst (els a) ts mp)))))
  where
  ip = all-∈ (inC c) (tabOK-all a c ts ok) (zip-snd (els a) ts mp)
  iq = all-∈ (inC c) (tabOK-all a c ts ok) (zip-snd (els a) ts mq)

map-fun : ∀ (f : U → U) es ts → length es ≡ length ts → (∀ {p} → p ∈ zipL es ts → f (fst p) ≡ snd p) →
          map f es ≡ ts
map-fun f []       []       _ _ = refl
map-fun f (e ∷ es) (t ∷ ts) l h = cong₂ _∷_ (h hd) (map-fun f es ts (suc-inj l) (λ m → h (tl m)))
  where
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl
map-fun f []       (_ ∷ _)  () _
map-fun f (_ ∷ _)  []       () _

tab-eta : ∀ a c u → In (ctab a c) u → tabF a (app a u) ≡ u
tab-eta a c u q with inC-tab a c u q
... | ts , refl , len , ok =
  cong tab (map-fun (assocU (els a) ts) (els a) ts (sym len)
    (λ {p} m → tab-fun a c ts ok (assoc-zip (els a) ts (fst p) (zip-fst (els a) ts m) (sym len)) m refl))

app-In : ∀ a c u x → In (ctab a c) u → In a x → In c (app a u x)
app-In a c u x q qx with inC-tab a c u q
... | ts , refl , len , ok =
  all-∈ (inC c) (tabOK-all a c ts ok)
    (zip-snd (els a) ts (assoc-zip (els a) ts x (els-complete a x qx) (sym len)))

app-mono : ∀ a c u u′ x x′ → In (ctab a c) u → In (ctab a c) u′ → In a x → In a x′ →
           Le a x x′ → Le (ctab a c) u u′ → Le c (app a u x) (app a u′ x′)
app-mono a c u u′ x x′ q q′ qx qx′ lx lu with inC-tab a c u q | inC-tab a c u′ q′
... | ts , refl , len , ok | ss , refl , len′ , ok′ =
  leC-trans c (app a (tab ts) x) (app a (tab ts) x′) (app a (tab ss) x′)
    (app-In a c (tab ts) x q qx) (app-In a c (tab ts) x′ q qx′) (app-In a c (tab ss) x′ q′ qx′)
    (monoP-elim (leC a) (leC c) _ (tabOK-mono a c ts ok)
       (assoc-zip (els a) ts x (els-complete a x qx) (sym len))
       (assoc-zip (els a) ts x′ (els-complete a x′ qx′) (sym len)) lx)
    (assoc-le (leC c) (els a) ts ss x′ (els-complete a x′ qx′) (sym len) lu)

tabF-In : ∀ a c f → (∀ x → In a x → In c (f x)) → (∀ x y → In a x → In a y → Le a x y → Le c (f x) (f y)) →
          In (ctab a c) (tabF a f)
tabF-In a c f hin hmono =
  ∧I (==ℕ-from _ _ (length-map f (els a)))
     (∧I (all-I (inC c) (map f (els a))
            (λ m → let (x , mx , e) = ∈-map-inv f (els a) m in subst (In c) (sym e) (hin x (els-sound a mx))))
         (monoP-intro (leC a) (leC c) (zipL (els a) (map f (els a)))
            (λ {p} {q} mp mq l →
               subst₂′ (Le c) (sym (zip-map f (els a) mp)) (sym (zip-map f (els a) mq))
                 (hmono (fst p) (fst q) (els-sound a (zip-fst (els a) _ mp)) (els-sound a (zip-fst (els a) _ mq)) l))))
  where
  subst₂′ : ∀ {A : Set} (P : A → A → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
  subst₂′ P refl refl p = p

tabF-le : ∀ a c f g → (∀ x → In a x → Le c (f x) (g x)) → Le (ctab a c) (tabF a f) (tabF a g)
tabF-le a c f g h = go (els a) (λ m → h _ (els-sound a m))
  where
  go : ∀ es → (∀ {x} → x ∈ es → Le c (f x) (g x)) → T (allZ (leC c) (map f es) (map g es))
  go []       k = tt
  go (e ∷ es) k = ∧I (k hd) (go es (λ m → k (tl m)))
