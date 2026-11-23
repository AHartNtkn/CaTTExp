------------------------------------------------------------------------
-- The repaired cone and the kernel's cone shape agree on every globular
-- diagram of dimension ≤ 2 (ledger S27 (h′)).
--
-- Two constructions of Mikhail's specified cone (Thm 3.3) exist:
--
--  * CaTTExp.Lim.Repaired.coneC, over named contexts, which the
--    recognition rules of CaTTExp.Lim.Rules accept (`SpecCone`), and
--  * CaTTExp.Cones.ConeOf.cone, over expression contexts, evaluated to
--    CaTT syntax; the kernel's limit heads take it as their cone shape
--    (`coneShape`, CaTTExp.Binder.LimHeadsExamples).
--
-- `cone-agrees` proves that for every globular diagram Γ of dimension
-- ≤ 2 (a well-formed context whose entries are objects, arrows between
-- objects, and 2-cells between parallel arrows), named canonically,
--
--   coneC Γ c >>= λ Π → lower (Γ, c, Π)   ≡   lower Γ >>= coneShape,
--
-- with c the next free name, and both sides are `just` the explicit
-- cone context `coneQ`. CaTTExp.Binder.LimRecognised checked this on
-- three diagrams; this is the general statement.
--
-- Diagrams are given as lists of entries (`Dg`, `Ent`) with a decidable
-- well-formedness test `wf`; `parse` reads a pure context as a diagram,
-- and `parse-sound` shows the context is the diagram's. The theorem is
-- stated for canonical naming (`named`: the variable at level i is
-- named i, the apex is named |Γ|), the naming used by Lim/Repaired's
-- examples; invariance of coneC under other injective namings is not
-- proved here.
------------------------------------------------------------------------
module CaTTExp.Lim.ConeAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅; build)
open import CaTTExp.Cones
  using (Ex; ExTy; ExCtx; v; ob; hom; bn; nth; length; evF; evTyF; evTy;
         tyE; tyF; cellF; binC; evCtx; evCtxGo; module ConeOf)
open import CaTTExp.Lim.Terms using (comp; vcomp; whL)
open import CaTTExp.Lim.Named
  using (NCtx; ∅; _▹_∶_; _⧺_; names; size; levelOf; lower; renTy; renTm; renSub)
open import CaTTExp.Lim.Rules using (coneCtx)
import CaTTExp.Lim.Repaired as R
open import CaTTExp.Binder.LimHeadsExamples using (coneShape; toExCtx; toExTy)

------------------------------------------------------------------------
-- Arithmetic and list lemmas.

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  _&_ : ∀ {a b} → T a → T b → T (a ∧ b)
  _&_ {true} _ q = q
  infixr 6 _&_

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  +-suc : ∀ n k → n + suc k ≡ suc (n + k)
  +-suc zero    k = refl
  +-suc (suc n) k = cong suc (+-suc n k)

  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  n<suc : ∀ n → T (n <ℕ suc n)
  n<suc zero    = tt
  n<suc (suc n) = n<suc n

  <-trans : ∀ i j k → T (i <ℕ j) → T (j <ℕ k) → T (i <ℕ k)
  <-trans zero    (suc j) (suc k) _ _ = tt
  <-trans (suc i) (suc j) (suc k) p q = <-trans i j k p q

  -- i < suc m splits into i < m or i = m.
  split : ∀ i m → T (i <ℕ suc m) → T (i <ℕ m) ⊎ (i ≡ m)
  split zero    zero    _ = inr refl
  split zero    (suc m) _ = inl tt
  split (suc i) zero    p = ⊥-elim (lt0 i p)
    where
    lt0 : ∀ i → T (i <ℕ 0) → ⊥
    lt0 _ ()
  split (suc i) (suc m) p with split i m p
  ... | inl q = inl q
  ... | inr e = inr (cong suc e)

  lt-irr : ∀ m → T (m <ℕ m) → ⊥
  lt-irr zero    ()
  lt-irr (suc m) p = lt-irr m p

  eq-refl : ∀ m → (m ==ℕ m) ≡ true
  eq-refl zero    = refl
  eq-refl (suc m) = eq-refl m

  lt-neq : ∀ i m → T (i <ℕ m) → (i ==ℕ m) ≡ false
  lt-neq zero    (suc m) _ = refl
  lt-neq (suc i) (suc m) p = lt-neq i m p

  lt-add : ∀ n {a k} → T (a <ℕ k) → T ((n + a) <ℕ (n + k))
  lt-add zero    p = p
  lt-add (suc n) p = lt-add n p

  le-add : ∀ n k → T (n <ℕ suc (n + k))
  le-add zero    k = tt
  le-add (suc n) k = le-add n k

  lt-addr : ∀ a n k → T (a <ℕ n) → T (a <ℕ suc (n + k))
  lt-addr a n k p = <-trans a n (suc (n + k)) p (le-add n k)

  -- Lists.
  map : ∀ {A B : Set} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  length-map : ∀ {A B : Set} (f : A → B) xs → length (map f xs) ≡ length xs
  length-map f []       = refl
  length-map f (x ∷ xs) = cong suc (length-map f xs)

  nth-map : ∀ {A B : Set} (f : A → B) (d : A) xs i → nth (f d) (map f xs) i ≡ f (nth d xs i)
  nth-map f d []       i       = refl
  nth-map f d (x ∷ xs) zero    = refl
  nth-map f d (x ∷ xs) (suc i) = nth-map f d xs i

  nth-app-l : ∀ {A : Set} (d : A) xs ys i → T (i <ℕ length xs) → nth d (xs ++ ys) i ≡ nth d xs i
  nth-app-l d (x ∷ xs) ys zero    _ = refl
  nth-app-l d (x ∷ xs) ys (suc i) p = nth-app-l d xs ys i p

  nth-app-r : ∀ {A : Set} (d : A) xs ys j → nth d (xs ++ ys) (length xs + j) ≡ nth d ys j
  nth-app-r d []       ys j = refl
  nth-app-r d (x ∷ xs) ys j = nth-app-r d xs ys j

  nth-last : ∀ {A : Set} (d : A) xs (x : A) i → length xs ≡ i → nth d (xs ++ (x ∷ [])) i ≡ x
  nth-last d xs x i refl = trans (cong (nth d (xs ++ (x ∷ []))) (sym (+-zero (length xs))))
                                 (nth-app-r d xs (x ∷ []) 0)

------------------------------------------------------------------------
-- Diagrams of dimension ≤ 2.

data Ent : Set where
  obj : Ent                            -- an object
  ar  : Nat → Nat → Ent                -- an arrow a → b
  tw  : Nat → Nat → Nat → Nat → Ent    -- a 2-cell f ⇒ g, f g : a → b

infixl 5 _,,_
data Dg : Set where
  dε   : Dg
  _,,_ : Dg → Ent → Dg

toP : Ent → Ty
toP obj          = ⋆
toP (ar a b)     = arr ⋆ (var a) (var b)
toP (tw a b f g) = arr (arr ⋆ (var a) (var b)) (var f) (var g)

toX : Ent → ExTy
toX obj          = ob
toX (ar a b)     = hom ob (v a) (v b)
toX (tw a b f g) = hom (hom ob (v a) (v b)) (v f) (v g)

pureOf : Dg → Ctx
pureOf dε       = ε
pureOf (d ,, e) = pureOf d ▸ toP e

lenD : Dg → Nat
lenD d = len (pureOf d)

at : Dg → Nat → Ent
at dε       i = obj
at (d ,, e) i = if i ==ℕ lenD d then e else at d i

ents : Dg → List Ent
ents dε       = []
ents (d ,, e) = ents d ++ (e ∷ [])

exOf : Dg → ExCtx
exOf dε       = []
exOf (d ,, e) = exOf d ++ (toX e ∷ [])

isObj : Ent → Bool
isObj obj = true
isObj _   = false

isAr : Nat → Nat → Ent → Bool
isAr a b (ar a' b') = (a ==ℕ a') ∧ (b ==ℕ b')
isAr _ _ _          = false

wfE : Dg → Ent → Bool
wfE d obj          = true
wfE d (ar a b)     = (a <ℕ lenD d) ∧ (b <ℕ lenD d) ∧ isObj (at d a) ∧ isObj (at d b)
wfE d (tw a b f g) = (a <ℕ lenD d) ∧ (b <ℕ lenD d) ∧ (f <ℕ lenD d) ∧ (g <ℕ lenD d) ∧
                     isObj (at d a) ∧ isObj (at d b) ∧ isAr a b (at d f) ∧ isAr a b (at d g)

wf : Dg → Bool
wf dε       = true
wf (d ,, e) = wf d ∧ wfE d e

-- Reading a pure context as a diagram.
private
  varOf : Tm → Maybe Nat
  varOf (var i) = just i
  varOf _       = nothing

  varOf-sound : ∀ t i → varOf t ≡ just i → t ≡ var i
  varOf-sound (var j)     i refl = refl
  varOf-sound (coh _ _ _) i ()

parseTy : Ty → Maybe Ent
parseTy ⋆ = just obj
parseTy (arr ⋆ s t) = varOf s >>= λ a → varOf t >>= λ b → just (ar a b)
parseTy (arr (arr ⋆ s t) u w) =
  varOf s >>= λ a → varOf t >>= λ b → varOf u >>= λ f → varOf w >>= λ g → just (tw a b f g)
parseTy (arr (arr (arr _ _ _) _ _) _ _) = nothing

parse : Ctx → Maybe Dg
parse ε       = just dε
parse (Γ ▸ A) = parse Γ >>= λ d → parseTy A >>= λ e → just (d ,, e)

private
  bind-just : ∀ {A B : Set} (m : Maybe A) (k : A → Maybe B) {y} →
              (m >>= k) ≡ just y → Σ A (λ x → (m ≡ just x) × (k x ≡ just y))
  bind-just (just x) k p = x , (refl , p)

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

parseTy-sound : ∀ A e → parseTy A ≡ just e → toP e ≡ A
parseTy-sound ⋆ .obj refl = refl
parseTy-sound (arr ⋆ s t) e p
  with bind-just (varOf s) _ p
... | a , (es , p1) with bind-just (varOf t) _ p1
...   | b , (pt , refl)
  rewrite varOf-sound s a es | varOf-sound t b pt = refl
parseTy-sound (arr (arr ⋆ s t) u w) e p
  with bind-just (varOf s) _ p
... | a , (es , p1) with bind-just (varOf t) _ p1
...   | b , (pt , p2) with bind-just (varOf u) _ p2
...     | f , (pu , p3) with bind-just (varOf w) _ p3
...       | g , (pw , refl)
  rewrite varOf-sound s a es | varOf-sound t b pt | varOf-sound u f pu | varOf-sound w g pw = refl
parseTy-sound (arr (arr (arr _ _ _) _ _) _ _) e ()

parse-sound : ∀ Γ d → parse Γ ≡ just d → pureOf d ≡ Γ
parse-sound ε .dε refl = refl
parse-sound (Γ ▸ A) d p with bind-just (parse Γ) _ p
... | d′ , (pd , p1) with bind-just (parseTy A) _ p1
...   | e , (pe , refl) = cong₂ _▸_ (parse-sound Γ d′ pd) (parseTy-sound A e pe)

------------------------------------------------------------------------
-- Lookups in a diagram.

at-new : ∀ d e → at (d ,, e) (lenD d) ≡ e
at-new d e rewrite eq-refl (lenD d) = refl

at-old : ∀ d e i → T (i <ℕ lenD d) → at (d ,, e) i ≡ at d i
at-old d e i p rewrite lt-neq i (lenD d) p = refl

isObj-sound : ∀ e → T (isObj e) → e ≡ obj
isObj-sound obj _ = refl

isAr-sound : ∀ a b e → T (isAr a b e) → e ≡ ar a b
isAr-sound a b (ar a′ b′) p
  rewrite ==ℕ-sound a a′ (∧-fst p) | ==ℕ-sound b b′ (∧-snd p) = refl

private
  facts4 : ∀ x y z w → T (x ∧ y ∧ z ∧ w) → T x × T y × T z × T w
  facts4 true true true true _ = tt , tt , tt , tt
  facts4 false _ _ _ ()
  facts4 true false _ _ ()
  facts4 true true false _ ()
  facts4 true true true false ()

  facts8 : ∀ x y z w x′ y′ z′ w′ → T (x ∧ y ∧ z ∧ w ∧ x′ ∧ y′ ∧ z′ ∧ w′) →
           T x × T y × T z × T w × T x′ × T y′ × T z′ × T w′
  facts8 true true true true x′ y′ z′ w′ q with facts4 x′ y′ z′ w′ q
  ... | a , b , c , d = tt , tt , tt , tt , a , b , c , d
  facts8 false _ _ _ _ _ _ _ ()
  facts8 true false _ _ _ _ _ _ ()
  facts8 true true false _ _ _ _ _ ()
  facts8 true true true false _ _ _ _ ()

-- What well-formedness says about the entry at level k of D.
WfEnt : Dg → Nat → Ent → Set
WfEnt D k obj          = ⊤
WfEnt D k (ar a b)     = T (a <ℕ k) × T (b <ℕ k) × (at D a ≡ obj) × (at D b ≡ obj)
WfEnt D k (tw a b f g) =
  T (a <ℕ k) × T (b <ℕ k) × T (f <ℕ k) × T (g <ℕ k) ×
  (at D a ≡ obj) × (at D b ≡ obj) × (at D f ≡ ar a b) × (at D g ≡ ar a b)

-- A prefix of D.
data Pfx (D : Dg) : Dg → Set where
  top  : Pfx D D
  drop : ∀ {d e} → Pfx D (d ,, e) → Pfx D d

pfx-le : ∀ {D d} → Pfx D d → T (lenD d <ℕ suc (lenD D))
pfx-le {D} top = n<suc (lenD D)
pfx-le {D} (drop {d} p) = <-trans (lenD d) (suc (lenD d)) (suc (lenD D)) (n<suc (lenD d)) (pfx-le p)

pfx-lt : ∀ {D d e} → Pfx D (d ,, e) → T (lenD d <ℕ lenD D)
pfx-lt p = pfx-le p

pfx-at : ∀ {D d} → Pfx D d → ∀ j → T (j <ℕ lenD d) → at D j ≡ at d j
pfx-at top j _ = refl
pfx-at (drop {d} {e} p) j q =
  trans (pfx-at p j (<-suc j (lenD d) q)) (at-old d e j q)

pfx-ent : ∀ {D d e} → Pfx D (d ,, e) → at D (lenD d) ≡ e
pfx-ent {D} {d} {e} p = trans (pfx-at p (lenD d) (n<suc (lenD d))) (at-new d e)

pfx-wf : ∀ {D d} → Pfx D d → T (wf D) → T (wf d)
pfx-wf top w = w
pfx-wf (drop p) w = ∧-fst (pfx-wf p w)

-- Well-formedness at each level.
wf-at : ∀ D → T (wf D) → ∀ {d e} → Pfx D (d ,, e) → WfEnt D (lenD d) e
wf-at D w {d} {e} p = go e (∧-snd (pfx-wf p w))
  where
  k = lenD d
  up : ∀ j → T (j <ℕ k) → at D j ≡ at d j
  up j q = trans (pfx-at p j (<-suc j k q)) (at-old d e j q)
  go : ∀ e′ → T (wfE d e′) → WfEnt D k e′
  go obj _ = tt
  go (ar a b) q with facts4 (a <ℕ k) (b <ℕ k) (isObj (at d a)) (isObj (at d b)) q
  ... | qa , qb , oa , ob′ =
    qa , qb , trans (up a qa) (isObj-sound _ oa) , trans (up b qb) (isObj-sound _ ob′)
  go (tw a b f g) q
    with facts8 (a <ℕ k) (b <ℕ k) (f <ℕ k) (g <ℕ k)
                (isObj (at d a)) (isObj (at d b)) (isAr a b (at d f)) (isAr a b (at d g)) q
  ... | qa , qb , qf , qg , oa , ob′ , af , ag =
    qa , qb , qf , qg ,
    trans (up a qa) (isObj-sound _ oa) , trans (up b qb) (isObj-sound _ ob′) ,
    trans (up f qf) (isAr-sound a b _ af) , trans (up g qg) (isAr-sound a b _ ag)

-- Every level below |D| is the last level of a prefix.
pfx-of : ∀ D j → T (j <ℕ lenD D) → Σ Dg (λ d → Σ Ent (λ e → Pfx D (d ,, e) × (lenD d ≡ j)))
pfx-of D j q = go D top j q
  where
  go : ∀ d → Pfx D d → ∀ j → T (j <ℕ lenD d) → Σ Dg (λ d′ → Σ Ent (λ e → Pfx D (d′ ,, e) × (lenD d′ ≡ j)))
  go (d ,, e) p j q with split j (lenD d) q
  ... | inl r = go d (drop p) j r
  ... | inr r = d , e , p , sym r

wf-lvl : ∀ D → T (wf D) → ∀ j → T (j <ℕ lenD D) → WfEnt D j (at D j)
wf-lvl D w j q with pfx-of D j q
... | d , e , p , refl rewrite pfx-ent p = wf-at D w p

-- Lists of entries and expression contexts.
len-ents : ∀ d → length (ents d) ≡ lenD d
len-ents dε = refl
len-ents (d ,, e) = trans (length-++ (ents d) (e ∷ [])) (trans (+-suc (length (ents d)) 0)
                      (cong suc (trans (+-zero _) (len-ents d))))

exOf-map : ∀ d → exOf d ≡ map toX (ents d)
exOf-map dε = refl
exOf-map (d ,, e) = trans (cong (_++ (toX e ∷ [])) (exOf-map d)) (sym (map-++ toX (ents d) (e ∷ [])))

len-exOf : ∀ d → length (exOf d) ≡ lenD d
len-exOf d = trans (cong length (exOf-map d)) (trans (length-map toX (ents d)) (len-ents d))

nth-ents : ∀ d i → T (i <ℕ lenD d) → nth obj (ents d) i ≡ at d i
nth-ents (d ,, e) i q with split i (lenD d) q
... | inl r = trans (nth-app-l obj (ents d) (e ∷ []) i (subst (λ m → T (i <ℕ m)) (sym (len-ents d)) r))
                (trans (nth-ents d i r) (sym (at-old d e i r)))
... | inr refl = trans (nth-last obj (ents d) e (lenD d) (len-ents d)) (sym (at-new d e))

nth-exOf : ∀ d i → T (i <ℕ lenD d) → nth ob (exOf d) i ≡ toX (at d i)
nth-exOf d i q = trans (cong (λ E → nth ob E i) (exOf-map d))
                   (trans (nth-map toX obj (ents d) i) (cong toX (nth-ents d i q)))

------------------------------------------------------------------------
-- Evaluation of the cone cells (CaTTExp.Cones) for symbolic indices.
-- The fuel is kept symbolic so that only the needed layers unfold.

evF-wh : ∀ n (K : ExCtx) c a b f g x pa →
  nth ob K pa ≡ hom ob (v c) (v a) →
  nth ob K x ≡ hom (hom ob (v a) (v b)) (v f) (v g) →
  evF (6 + n) K (bn 0 (v pa) (v x)) ≡ whL (var c) (var a) (var pa) (var b) (var f) (var g) (var x)
evF-wh n K c a b f g x pa e1 e5 rewrite e1 | e5 = refl

tyE-wh : ∀ n (K : ExCtx) c a b f g x pa →
  nth ob K pa ≡ hom ob (v c) (v a) →
  nth ob K f ≡ hom ob (v a) (v b) →
  nth ob K x ≡ hom (hom ob (v a) (v b)) (v f) (v g) →
  tyF (3 + n) K (bn 0 (v pa) (v x)) ≡ hom (hom ob (v c) (v b)) (bn 0 (v pa) (v f)) (bn 0 (v pa) (v g))
tyE-wh n K c a b f g x pa e1 e3 e5 rewrite e5 | e1 | e3 | e1 = refl

evF-comp : ∀ n (K : ExCtx) c a p b x →
  nth ob K p ≡ hom ob (v c) (v a) → nth ob K x ≡ hom ob (v a) (v b) →
  evF (6 + n) K (bn 0 (v p) (v x)) ≡ comp (var c) (var a) (var p) (var b) (var x)
evF-comp n K c a p b x ep ex rewrite ep | ex = refl

evF-vc : ∀ n (K : ExCtx) c a b f g x pa pb pf →
  nth ob K pa ≡ hom ob (v c) (v a) →
  nth ob K f ≡ hom ob (v a) (v b) → nth ob K g ≡ hom ob (v a) (v b) →
  nth ob K x ≡ hom (hom ob (v a) (v b)) (v f) (v g) →
  nth ob K pf ≡ hom (hom ob (v c) (v b)) (v pb) (bn 0 (v pa) (v f)) →
  evF (10 + n) K (bn 1 (v pf) (bn 0 (v pa) (v x)))
  ≡ vcomp (var c) (var b) (var pb) (comp (var c) (var a) (var pa) (var b) (var f)) (var pf)
          (comp (var c) (var a) (var pa) (var b) (var g))
          (whL (var c) (var a) (var pa) (var b) (var f) (var g) (var x))
evF-vc n K c a b f g x pa pb pf e1 e3 e4 e5 e6 =
  cong₂ (λ U W → fst (binC 1 U W)) cPf cWh
  where
  tyAB : ∀ m → evTyF (8 + m) K (hom (hom ob (v c) (v b)) (bn 0 (v pa) (v f)) (bn 0 (v pa) (v g)))
             ≡ arr (arr ⋆ (var c) (var b)) (comp (var c) (var a) (var pa) (var b) (var f))
                   (comp (var c) (var a) (var pa) (var b) (var g))
  tyAB m = cong₂ (arr (arr ⋆ (var c) (var b))) (evF-comp (1 + m) K c a pa b f e1 e3) (evF-comp (1 + m) K c a pa b g e1 e4)
  cWh : cellF (9 + n) K (bn 0 (v pa) (v x)) ≡ (whL (var c) (var a) (var pa) (var b) (var f) (var g) (var x) , _)
  cWh = cong₂ _,_ (evF-wh (2 + n) K c a b f g x pa e1 e5) (trans (cong (evTyF (8 + n) K) (tyE-wh 61 K c a b f g x pa e1 e3 e5)) (tyAB n))
  cPf : cellF (9 + n) K (v pf) ≡ (var pf , _)
  cPf = cong (var pf ,_) (trans (cong (evTyF (8 + n) K) e6)
          (cong (λ t → arr (arr ⋆ (var c) (var b)) (var pb) t) (evF-comp (1 + n) K c a pa b f e1 e3)))

------------------------------------------------------------------------
-- The explicit cone over a diagram (apex n, projection of level j at
-- level P j = n + 1 + j), as expressions and as CaTT types.

module Proj (n : Nat) where
  P : Nat → Nat
  P j = suc (n + j)

  pr : Nat → Ex
  pr j = v (P j)

  projX : Nat → Ent → ExTy
  projX k obj          = hom ob (v n) (v k)
  projX k (ar a b)     = hom (hom ob (v n) (v b)) (pr b) (bn 0 (pr a) (v k))
  projX k (tw a b f g) =
    hom (hom (hom ob (v n) (v b)) (pr b) (bn 0 (pr a) (v g))) (pr g)
        (bn 1 (pr f) (bn 0 (pr a) (v k)))

  cmp : Nat → Nat → Nat → Tm
  cmp a b x = comp (var n) (var a) (var (P a)) (var b) (var x)

  projP : Nat → Ent → Ty
  projP k obj          = arr ⋆ (var n) (var k)
  projP k (ar a b)     = arr (arr ⋆ (var n) (var b)) (var (P b)) (cmp a b k)
  projP k (tw a b f g) =
    arr (arr (arr ⋆ (var n) (var b)) (var (P b)) (cmp a b g)) (var (P g))
        (vcomp (var n) (var b) (var (P b)) (cmp a b f) (var (P f)) (cmp a b g)
               (whL (var n) (var a) (var (P a)) (var b) (var f) (var g) (var k)))

  projL : Nat → List Ent → ExCtx
  projL k []       = []
  projL k (e ∷ es) = projX k e ∷ projL (suc k) es

  -- The cone context: the diagram, the apex, the projections of the
  -- levels of d.
  Qpre : Dg → Dg → Ctx
  Qpre D dε       = pureOf D ▸ ⋆
  Qpre D (d ,, e) = Qpre D d ▸ projP (lenD d) e

coneQ : Dg → Ctx
coneQ D = Proj.Qpre (lenD D) D D

------------------------------------------------------------------------
-- The kernel's side: CaTTExp.Cones' cone over the diagram evaluates to
-- the explicit cone.

private
  ++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  lt-self : ∀ k m → T (k <ℕ k + suc m)
  lt-self zero    m = tt
  lt-self (suc k) m = lt-self k m

  go-app : ∀ K xs ys acc → evCtxGo K (xs ++ ys) acc ≡ evCtxGo K ys (evCtxGo K xs acc)
  go-app K []       ys acc = refl
  go-app K (x ∷ xs) ys acc = go-app K xs ys (acc ▸ evTy K x)

  evTy-toX : ∀ K e → evTy K (toX e) ≡ toP e
  evTy-toX K obj          = refl
  evTy-toX K (ar a b)     = refl
  evTy-toX K (tw a b f g) = refl

  go-E : ∀ K d → evCtxGo K (exOf d) ε ≡ pureOf d
  go-E K dε       = refl
  go-E K (d ,, e) =
    trans (go-app K (exOf d) (toX e ∷ []) ε)
          (cong₂ _▸_ (go-E K d) (evTy-toX K e))

  toExCtx-ok : ∀ d → toExCtx (pureOf d) ≡ just (exOf d)
  toExCtx-ok dε = refl
  toExCtx-ok (d ,, obj)        rewrite toExCtx-ok d = refl
  toExCtx-ok (d ,, ar a b)     rewrite toExCtx-ok d = refl
  toExCtx-ok (d ,, tw a b f g) rewrite toExCtx-ok d = refl

module ConeSide (D : Dg) (w : T (wf D)) where
  E : ExCtx
  E = exOf D

  N : Nat
  N = length E

  module C = ConeOf E
  open Proj N

  private
    -- n = |D|, as the bound for levels.
    toN : ∀ {i} → T (i <ℕ lenD D) → T (i <ℕ N)
    toN {i} q = subst (λ m → T (i <ℕ m)) (sym (len-exOf D)) q

  -- One step of ConeOf.build: the projection type of a level, given
  -- the lookups it uses.
  pt-ar : ∀ K k a b → nth ob E k ≡ hom ob (v a) (v b) →
          nth ob K (P b) ≡ hom ob (v N) (v b) →
          C.projTy K k (hom ob (v a) (v b)) ≡ projX k (ar a b)
  pt-ar K k a b ek eb rewrite ek | eb = refl

  pt-tw : ∀ K k a b f g → nth ob E k ≡ hom (hom ob (v a) (v b)) (v f) (v g) →
          nth ob E f ≡ hom ob (v a) (v b) →
          nth ob K (P g) ≡ projX g (ar a b) →
          C.projTy K k (hom (hom ob (v a) (v b)) (v f) (v g)) ≡ projX k (tw a b f g)
  pt-tw K k a b f g ek ef eg rewrite ek | ef | eg = refl

  pt : ∀ K k e → T (k <ℕ lenD D) → at D k ≡ e → WfEnt D k e →
       (∀ j → T (j <ℕ k) → nth ob K (P j) ≡ projX j (at D j)) →
       C.projTy K k (toX e) ≡ projX k e
  pt K k obj q ek _ hp = refl
  pt K k (ar a b) q ek (qa , qb , oa , ob′) hp =
    pt-ar K k a b (trans (nth-exOf D k q) (cong toX ek))
                  (trans (hp b qb) (cong (projX b) ob′))
  pt K k (tw a b f g) q ek (qa , qb , qf , qg , oa , ob′ , af , ag) hp =
    pt-tw K k a b f g (trans (nth-exOf D k q) (cong toX ek))
                      (trans (nth-exOf D f (<-trans f k (lenD D) qf q)) (cong toX af))
                      (trans (hp g qg) (cong (projX g) ag))

  build-ok : ∀ k K es →
    (∀ j → T (j <ℕ length es) → nth obj es j ≡ at D (k + j)) →
    k + length es ≡ lenD D →
    length K ≡ suc (N + k) →
    (∀ j → T (j <ℕ k) → nth ob K (P j) ≡ projX j (at D j)) →
    C.build k K (map toX es) ≡ K ++ projL k es
  build-ok k K [] he hl hK hp = sym (++-[] K)
  build-ok k K (e ∷ es) he hl hK hp =
    trans (cong (λ X → C.build (suc k) (K ++ (X ∷ [])) (map toX es)) step)
          (trans (build-ok (suc k) K′ es he′ hl′ hK′ hp′) (++-assoc K (projX k e ∷ []) (projL (suc k) es)))
    where
    q : T (k <ℕ lenD D)
    q = subst (λ m → T (k <ℕ m)) hl (lt-self k (length es))
    ek : at D k ≡ e
    ek = sym (trans (he 0 tt) (cong (at D) (+-zero k)))
    step : C.projTy K k (toX e) ≡ projX k e
    step = pt K k e q ek (subst (WfEnt D k) ek (wf-lvl D w k q)) hp
    K′ = K ++ (projX k e ∷ [])
    he′ : ∀ j → T (j <ℕ length es) → nth obj es j ≡ at D (suc k + j)
    he′ j r = trans (he (suc j) r) (cong (at D) (+-suc k j))
    hl′ : suc k + length es ≡ lenD D
    hl′ = trans (sym (+-suc k (length es))) hl
    hK′ : length K′ ≡ suc (N + suc k)
    hK′ = trans (length-++ K (projX k e ∷ []))
            (trans (+-suc (length K) 0)
              (trans (cong suc (trans (+-zero (length K)) hK)) (cong suc (sym (+-suc N k)))))
    hp′ : ∀ j → T (j <ℕ suc k) → nth ob K′ (P j) ≡ projX j (at D j)
    hp′ j r with split j k r
    ... | inl s = trans (nth-app-l ob K (projX k e ∷ []) (P j)
                          (subst (λ m → T (P j <ℕ m)) (sym hK) (lt-add N s)))
                        (hp j s)
    ... | inr refl = trans (nth-last ob K (projX k e) (P k) hK) (cong (projX k) (sym ek))

  -- The cone context of ConeOf, as a list.
  Kc : ExCtx
  Kc = (E ++ (ob ∷ [])) ++ projL 0 (ents D)

  cone-list : C.cone ≡ Kc
  cone-list =
    trans (cong (C.build 0 (E ++ (ob ∷ []))) (exOf-map D))
          (build-ok 0 (E ++ (ob ∷ [])) (ents D)
             (λ j r → nth-ents D j (subst (λ m → T (j <ℕ m)) (len-ents D) r))
             (len-ents D)
             (trans (length-++ E (ob ∷ [])) (+-suc N 0))
             (λ j ()))

  nth-projL : ∀ k es j → T (j <ℕ length es) → nth ob (projL k es) j ≡ projX (k + j) (nth obj es j)
  nth-projL k (e ∷ es) zero    _ = cong (λ m → projX m e) (sym (+-zero k))
  nth-projL k (e ∷ es) (suc j) r = trans (nth-projL (suc k) es j r) (cong (λ m → projX m (nth obj es j)) (sym (+-suc k j)))

  kc-diag : ∀ i → T (i <ℕ lenD D) → nth ob Kc i ≡ toX (at D i)
  kc-diag i q =
    trans (nth-app-l ob (E ++ (ob ∷ [])) (projL 0 (ents D)) i
             (subst (λ m → T (i <ℕ m)) (sym (trans (length-++ E (ob ∷ [])) (+-suc N 0)))
                    (<-suc i (N + 0) (subst (λ m → T (i <ℕ m)) (sym (+-zero N)) (toN q)))))
          (trans (nth-app-l ob E (ob ∷ []) i (toN q)) (nth-exOf D i q))

  kc-proj : ∀ j → T (j <ℕ lenD D) → nth ob Kc (P j) ≡ projX j (at D j)
  kc-proj j q =
    trans (cong (nth ob Kc) (sym idx))
          (trans (nth-app-r ob (E ++ (ob ∷ [])) (projL 0 (ents D)) j)
                 (trans (nth-projL 0 (ents D) j (subst (λ m → T (j <ℕ m)) (sym (len-ents D)) q))
                        (cong (projX j) (nth-ents D j q))))
    where
    idx : length (E ++ (ob ∷ [])) + j ≡ P j
    idx = cong (_+ j) (trans (length-++ E (ob ∷ [])) (trans (+-suc N 0) (cong suc (+-zero N))))

  -- Each projection type evaluates to the explicit one.
  evP : ∀ k e → T (k <ℕ lenD D) → at D k ≡ e → WfEnt D k e → evTy Kc (projX k e) ≡ projP k e
  evP k obj q ek _ = refl
  evP k (ar a b) q ek (qa , qb , oa , ob′) =
    cong (arr (arr ⋆ (var N) (var b)) (var (P b)))
         (evF-comp 57 Kc N a (P a) b k
            (trans (kc-proj a qa′) (cong (projX a) oa))
            (trans (kc-diag k q) (cong toX ek)))
    where qa′ = <-trans a k (lenD D) qa q
  evP k (tw a b f g) q ek (qa , qb , qf , qg , oa , ob′ , af , ag) =
    cong₂ (λ s t → arr (arr (arr ⋆ (var N) (var b)) (var (P b)) s) (var (P g)) t)
          (evF-comp 56 Kc N a (P a) b g epa eg)
          (evF-vc 53 Kc N a b f g k (P a) (P b) (P f) epa ef eg ek′ epf)
    where
    lt : ∀ x → T (x <ℕ k) → T (x <ℕ lenD D)
    lt x r = <-trans x k (lenD D) r q
    epa = trans (kc-proj a (lt a qa)) (cong (projX a) oa)
    ef  = trans (kc-diag f (lt f qf)) (cong toX af)
    eg  = trans (kc-diag g (lt g qg)) (cong toX ag)
    ek′ = trans (kc-diag k q) (cong toX ek)
    epf = trans (kc-proj f (lt f qf)) (cong (projX f) af)

  projL-snoc : ∀ k xs x → projL k (xs ++ (x ∷ [])) ≡ projL k xs ++ (projX (k + length xs) x ∷ [])
  projL-snoc k []       x = cong (λ m → projX m x ∷ []) (sym (+-zero k))
  projL-snoc k (y ∷ xs) x =
    cong (projX k y ∷_) (trans (projL-snoc (suc k) xs x)
      (cong (λ m → projL (suc k) xs ++ (projX m x ∷ [])) (sym (+-suc k (length xs)))))

  go-P : ∀ d → Pfx D d → evCtxGo Kc (projL 0 (ents d)) (pureOf D ▸ ⋆) ≡ Qpre D d
  go-P dε p = refl
  go-P (d ,, e) p =
    trans (cong (λ L → evCtxGo Kc L (pureOf D ▸ ⋆)) (projL-snoc 0 (ents d) e))
      (trans (go-app Kc (projL 0 (ents d)) (projX (length (ents d)) e ∷ []) (pureOf D ▸ ⋆))
        (cong₂ _▸_ (go-P d (drop p))
          (trans (cong (λ m → evTy Kc (projX m e)) (len-ents d))
                 (evP (lenD d) e (pfx-lt p) (pfx-ent p)
                      (subst (WfEnt D (lenD d)) (pfx-ent p) (wf-lvl D w (lenD d) (pfx-lt p)))))))

  cone-ev : evCtx C.cone ≡ Qpre D D
  cone-ev =
    trans (cong (λ K → evCtxGo K K ε) cone-list)
      (trans (go-app Kc (E ++ (ob ∷ [])) (projL 0 (ents D)) ε)
        (trans (cong (evCtxGo Kc (projL 0 (ents D)))
                     (trans (go-app Kc E (ob ∷ []) ε) (cong (_▸ ⋆) (go-E Kc D))))
               (go-P D top)))

  -- The kernel's cone shape of the diagram.
  shape-ok : coneShape (pureOf D) ≡ just (Qpre D D)
  shape-ok rewrite toExCtx-ok D = cong just cone-ev

------------------------------------------------------------------------
-- Canonical naming, and lowering it.

named : Ctx → NCtx
named ε       = ∅
named (Γ ▸ A) = named Γ ▹ len Γ ∶ A

size-named : ∀ Γ → size (named Γ) ≡ len Γ
size-named ε       = refl
size-named (Γ ▸ A) = cong suc (size-named Γ)

private
  elem-++ : ∀ x xs ys → T (elem x (xs ++ ys)) → T (elem x xs) ⊎ T (elem x ys)
  elem-++ x []       ys p = inr p
  elem-++ x (y ∷ xs) ys p with x ==ℕ y
  ... | true  = inl tt
  ... | false = elem-++ x xs ys p

  elem-one : ∀ x y → T (elem x (y ∷ [])) → x ≡ y
  elem-one x y p with x ==ℕ y | ==ℕ-sound x y
  ... | true  | s = s tt
  ... | false | _ = ⊥-elim p

names-lt : ∀ Γ x → T (elem x (names (named Γ))) → T (x <ℕ len Γ)
names-lt (Γ ▸ A) x p with elem-++ x (names (named Γ)) (len Γ ∷ []) p
... | inl q = <-suc x (len Γ) (names-lt Γ x q)
... | inr q rewrite elem-one x (len Γ) q = n<suc (len Γ)

fresh-named : ∀ Γ → elem (len Γ) (names (named Γ)) ≡ false
fresh-named Γ with elem (len Γ) (names (named Γ)) | names-lt Γ (len Γ)
... | true  | h = ⊥-elim (lt-irr (len Γ) (h tt))
... | false | _ = refl

levelOf-named : ∀ Γ x → T (x <ℕ len Γ) → levelOf (named Γ) x ≡ just x
levelOf-named (Γ ▸ A) x q with split x (len Γ) q
... | inl r rewrite lt-neq x (len Γ) r = levelOf-named Γ x r
... | inr refl rewrite eq-refl (len Γ) = cong just (size-named Γ)

-- Scoping: every variable is below m.
mutual
  WsTy : Nat → Ty → Set
  WsTy m ⋆           = ⊤
  WsTy m (arr A t u) = WsTy m A × WsTm m t × WsTm m u

  WsTm : Nat → Tm → Set
  WsTm m (var x)     = T (x <ℕ m)
  WsTm m (coh Δ A γ) = WsSub m γ
  WsTm m (cst ())

  WsSub : Nat → Sub → Set
  WsSub m ⟨⟩       = ⊤
  WsSub m (γ ,ₛ t) = WsSub m γ × WsTm m t

ScC : Ctx → Set
ScC ε       = ⊤
ScC (Γ ▸ A) = ScC Γ × WsTy (len Γ) A

module _ (ρ : Nat → Maybe Nat) (m : Nat) (hρ : ∀ x → T (x <ℕ m) → ρ x ≡ just x) where
  mutual
    renTy-id : ∀ A → WsTy m A → renTy ρ A ≡ just A
    renTy-id ⋆ _ = refl
    renTy-id (arr A t u) (wA , wt , wu)
      rewrite renTy-id A wA | renTm-id t wt | renTm-id u wu = refl

    renTm-id : ∀ t → WsTm m t → renTm ρ t ≡ just t
    renTm-id (var x) wx rewrite hρ x wx = refl
    renTm-id (coh Δ A γ) wγ rewrite renSub-id γ wγ = refl
    renTm-id (cst ())

    renSub-id : ∀ γ → WsSub m γ → renSub ρ γ ≡ just γ
    renSub-id ⟨⟩ _ = refl
    renSub-id (γ ,ₛ t) (wγ , wt) rewrite renSub-id γ wγ | renTm-id t wt = refl

lower-named : ∀ Γ → ScC Γ → lower (named Γ) ≡ just Γ
lower-named ε _ = refl
lower-named (Γ ▸ A) (sΓ , sA)
  rewrite fresh-named Γ | lower-named Γ sΓ
        | renTy-id (levelOf (named Γ)) (len Γ) (levelOf-named Γ) A sA = refl

------------------------------------------------------------------------
-- The repaired side: Lim/Repaired's coneC on the canonically named
-- diagram, lowered, is the explicit cone.

module NamedSide (D : Dg) (w : T (wf D)) where
  n : Nat
  n = lenD D

  open Proj n

  Γn : NCtx
  Γn = named (pureOf D)

  pn : Nat → Nat
  pn = R.pName Γn n

  pn-ok : ∀ a → T (a <ℕ n) → pn a ≡ P a
  pn-ok a q rewrite levelOf-named (pureOf D) a q = refl

  projTy-ok : ∀ k e → T (k <ℕ n) → WfEnt D k e → R.projTy n pn k (toP e) ≡ just (projP k e)
  projTy-ok k obj q _ = refl
  projTy-ok k (ar a b) q (qa , qb , _)
    rewrite pn-ok a (<-trans a k n qa q) | pn-ok b (<-trans b k n qb q) = refl
  projTy-ok k (tw a b f g) q (qa , qb , qf , qg , _)
    rewrite pn-ok a (<-trans a k n qa q) | pn-ok b (<-trans b k n qb q)
          | pn-ok f (<-trans f k n qf q) | pn-ok g (<-trans g k n qg q) = refl

  Πn : Dg → NCtx
  Πn dε       = ∅
  Πn (d ,, e) = Πn d ▹ P (lenD d) ∶ projP (lenD d) e

  coneWith-ok : ∀ d → Pfx D d → R.coneWith n pn (named (pureOf d)) ≡ just (Πn d)
  coneWith-ok dε p = refl
  coneWith-ok (d ,, e) p
    rewrite coneWith-ok d (drop p)
          | projTy-ok (lenD d) e (pfx-lt p) (wf-at D w p)
          | pn-ok (lenD d) (pfx-lt p) = refl

  len-Qpre : ∀ d → len (Qpre D d) ≡ P (lenD d)
  len-Qpre dε       = cong suc (sym (+-zero n))
  len-Qpre (d ,, e) = trans (cong suc (len-Qpre d)) (cong suc (sym (+-suc n (lenD d))))

  ⧺-ok : ∀ d → (Γn ▹ n ∶ ⋆) ⧺ Πn d ≡ named (Qpre D d)
  ⧺-ok dε       = refl
  ⧺-ok (d ,, e) = cong₂ (λ K x → K ▹ x ∶ projP (lenD d) e) (⧺-ok d) (sym (len-Qpre d))

  -- Scoping of the explicit cone.
  private
    module W (k : Nat) (q : T (k <ℕ n)) where
      m = suc (n + k)
      wn : T (n <ℕ m)
      wn = le-add n k
      wd : ∀ x → T (x <ℕ k) → T (x <ℕ m)
      wd x r = lt-addr x n k (<-trans x k n r q)
      wk : T (k <ℕ m)
      wk = lt-addr k n k q
      wP : ∀ x → T (x <ℕ k) → T (P x <ℕ m)
      wP x r = lt-add n r
      wcmp : ∀ a b x → T (a <ℕ k) → T (b <ℕ k) → T (x <ℕ m) → WsTm m (cmp a b x)
      wcmp a b x qa qb qx = ((((tt , wn) , wd a qa) , wP a qa) , wd b qb) , qx

    ws-projP : ∀ k e → T (k <ℕ n) → WfEnt D k e → WsTy (suc (n + k)) (projP k e)
    ws-projP k obj q _ = tt , W.wn k q , W.wk k q
    ws-projP k (ar a b) q (qa , qb , _) =
      (tt , wn , wd b qb) , wP b qb , wcmp a b k qa qb wk
      where open W k q
    ws-projP k (tw a b f g) q (qa , qb , qf , qg , _) =
      ((tt , wn , wd b qb) , wP b qb , wcmp a b g qa qb (wd g qg)) , wP g qg ,
      (((((((tt , wn) , wd b qb) , wP b qb) , wcmp a b f qa qb (wd f qf)) , wP f qf) ,
        wcmp a b g qa qb (wd g qg)) ,
       ((((((tt , wn) , wd a qa) , wP a qa) , wd b qb) , wd f qf) , wd g qg) , wk)
      where open W k q

    ws-toP : ∀ k e → WfEnt D k e → WsTy k (toP e)
    ws-toP k obj _ = tt
    ws-toP k (ar a b) (qa , qb , _) = tt , qa , qb
    ws-toP k (tw a b f g) (qa , qb , qf , qg , _) = (tt , qa , qb) , qf , qg

    sc-pure : ∀ d → Pfx D d → ScC (pureOf d)
    sc-pure dε p = tt
    sc-pure (d ,, e) p = sc-pure d (drop p) , ws-toP (lenD d) e (wf-at D w p)

    sc-Q : ∀ d → Pfx D d → ScC (Qpre D d)
    sc-Q dε p = sc-pure D top , tt
    sc-Q (d ,, e) p =
      sc-Q d (drop p) ,
      subst (λ m → WsTy m (projP (lenD d) e)) (sym (len-Qpre d))
            (ws-projP (lenD d) e (pfx-lt p) (wf-at D w p))

  sc-D : ScC (pureOf D)
  sc-D = sc-pure D top

  specified-ok : (R.coneC Γn n >>= λ Π → lower (coneCtx Γn n Π)) ≡ just (Qpre D D)
  specified-ok rewrite coneWith-ok D top | ⧺-ok D = lower-named (Qpre D D) (sc-Q D top)

------------------------------------------------------------------------
-- The theorem.

cone-agrees-dg : ∀ D → T (wf D) →
  (R.coneC (named (pureOf D)) (lenD D) >>= λ Π → lower (coneCtx (named (pureOf D)) (lenD D) Π))
  ≡ (lower (named (pureOf D)) >>= coneShape)
cone-agrees-dg D w
  rewrite NamedSide.specified-ok D w | lower-named (pureOf D) (NamedSide.sc-D D w)
        | ConeSide.shape-ok D w | len-exOf D = refl

-- For every pure context that reads as a well-formed diagram of
-- dimension ≤ 2, the repaired cone (named canonically, apex the next
-- name, lowered) is the kernel's cone shape.
cone-agrees : ∀ Γ D → parse Γ ≡ just D → T (wf D) →
  (R.coneC (named Γ) (len Γ) >>= λ Π → lower (coneCtx (named Γ) (len Γ) Π))
  ≡ (lower (named Γ) >>= coneShape)
cone-agrees Γ D p w with parse-sound Γ D p
... | refl = cone-agrees-dg D w

------------------------------------------------------------------------
-- Instances: Mikhail's Example 4.1 (x, y, f g : x → y, α : f ⇒ g) and
-- the loop are covered (they parse as well-formed diagrams); a
-- 3-dimensional cell and an ill-typed 2-cell are not.

private
  Γ41 : Ctx
  Γ41 = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
          ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)

  _ = cone-agrees Γ41 _ refl tt

  Γloop : Ctx
  Γloop = ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0) ▸ arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)

  _ = cone-agrees Γloop _ refl tt

  _ : parse (ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0) ▸ arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)
               ▸ arr (arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)) (var 2) (var 2)) ≡ nothing
  _ = refl

  -- α : f ⇒ g with f : x → y but g : y → x.
  _ : (parse (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 1) (var 0)
                ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)) >>= λ D → just (wf D)) ≡ just false
  _ = refl
