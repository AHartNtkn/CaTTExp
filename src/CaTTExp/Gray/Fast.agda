------------------------------------------------------------------------
-- The side condition of two-tier L, computed on symbolic supports
-- (CaTTExp.Gray.Cover), and the proof that it agrees with the
-- list-based definition of CaTTExp.Gray.Support:
--
--     fastSide Θ A t u ≡ graySide Θ A t u            (`fastSide-correct`)
--
-- for every Θ, A, t, u (no well-formedness assumptions).
--
-- Supports are built without enumeration: the support of a variable
-- is one literal; the top support of an operation-case coh is the top
-- chain of K(Θ) with every cell w replaced by the (symbolic) support
-- of ρ(w); the tables of T are the same chains with literal cells.
-- Their sizes are linear in the size of the term (as a tree) and in
-- the number of homs. The comparison ↓S = ↓R is the cover check of
-- Gray.Cover in both directions.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Fast (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)

------------------------------------------------------------------------
-- Symbolic supports.

plainE : Nat → Exp
plainE w = (lit (w ∷ []) ∷ []) ∷ []

shomOf : (Nat → Exp) → Hom → SHom
shomOf f h = mapL (λ i → i , concatMapL f (piece h i false) , concatMapL f (piece h i true)) (upto (hd h))

chainE : (Nat → Exp) → List Hom → Bool → Nat → Seq
chainE f hs sg k = sch (mapL (shomOf f) hs) sg k ∷ []

lowerE : Nat → List Hom → Exp
lowerE zero    hs = []
lowerE (suc m) hs = lowerE m hs ++ (chainE plainE hs false m ∷ chainE plainE hs true m ∷ [])

fullE : List Hom → Exp
fullE hs = lowerE (dimK hs) hs ++ (chainE plainE hs true (dimK hs) ∷ [])

bdryE : Bool → List Hom → Exp
bdryE sg hs = lowerE (dimK hs ∸ 1) hs ++ (chainE plainE hs sg (dimK hs ∸ 1) ∷ [])

nthE : Nat → List Exp → Exp
nthE _       []       = []
nthE zero    (x ∷ _)  = x
nthE (suc n) (_ ∷ xs) = nthE n xs

fastSame : Ctx → Exp → Exp → Bool
fastSame Γ S R = cover S R ∧ cover R S
  where open Algo (leqL (cells Γ) (dimK (homs Γ)))

mutual
  topSE : Tm → Exp
  topSE (var v)               = plainE v
  topSE (cst _)               = []
  topSE (coh Θ ⋆ ρ)           = []
  topSE (coh Θ (arr A t u) ρ) =
    if fastCoh Θ A t u then []
    else (chainE (λ w → nthE w (topsSubE ρ)) (homs Θ) true (dimK (homs Θ)) ∷ [])

  topsSubE : Sub → List Exp
  topsSubE ⟨⟩       = []
  topsSubE (ρ ,ₛ t) = topsSubE ρ ++ (topSE t ∷ [])

  suppTyE : Ty → Exp
  suppTyE ⋆                      = []
  suppTyE (arr ⋆ _ _)            = []
  suppTyE (arr (arr B s s') t u) = suppTyE (arr B s s') ++ topSE t ++ topSE u

  suppE : Tm → Ty → Exp
  suppE t A = topSE t ++ suppTyE A

  fastCoh : Ctx → Ty → Tm → Tm → Bool
  fastCoh Θ ⋆ t u = false
  fastCoh Θ A@(arr _ _ _) t u =
    endsOK Θ A ∧ fastSame Θ (suppE t A) (fullE (homs Θ))
               ∧ fastSame Θ (suppE u A) (fullE (homs Θ))

fastOp : Ctx → Ty → Tm → Tm → Bool
fastOp Θ ⋆ t u = opCase Θ ⋆ t u
fastOp Θ A@(arr _ _ _) t u =
  endsOK Θ A ∧ (dim A ==ℕ dimK (homs Θ))
  ∧ fastSame Θ (suppE t A) (bdryE false (homs Θ))
  ∧ fastSame Θ (suppE u A) (bdryE true (homs Θ))

fastSide : Ctx → Ty → Tm → Tm → Bool
fastSide Θ A t u = fastCoh Θ A t u ∨ fastOp Θ A t u

------------------------------------------------------------------------
-- Lists of Support versus those of Cover.

private
  map≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs → map f xs ≡ mapL f xs
  map≡ f []       = refl
  map≡ f (x ∷ xs) = cong (f x ∷_) (map≡ f xs)

  cm≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → List B) xs → concatMap f xs ≡ concatMapL f xs
  cm≡ f []       = refl
  cm≡ f (x ∷ xs) = cong (f x ++_) (cm≡ f xs)

  cm-cong : ∀ {a b} {A : Set a} {B : Set b} {f g : A → List B} → (∀ x → f x ≡ g x) → ∀ xs →
            concatMapL f xs ≡ concatMapL g xs
  cm-cong e []       = refl
  cm-cong e (x ∷ xs) = cong₂ _++_ (e x) (cm-cong e xs)

  anyS⇒ : ∀ {a} {A : Set a} (p : A → Bool) xs → T (any p xs) → Any (λ x → T (p x)) xs
  anyS⇒ p (x ∷ xs) t with ∨-out {p x} t
  ... | inj₁ r = here r
  ... | inj₂ r = there (anyS⇒ p xs r)

  anyS⇐ : ∀ {a} {A : Set a} (p : A → Bool) xs → Any (λ x → T (p x)) xs → T (any p xs)
  anyS⇐ p (x ∷ xs) (here r)  = ∨-inl r
  anyS⇐ p (x ∷ xs) (there r) = ∨-inr {p x} (anyS⇐ p xs r)

  iff≡ : ∀ {a b} → (T a → T b) → (T b → T a) → a ≡ b
  iff≡ {true}  {true}  f g = refl
  iff≡ {true}  {false} f g = ⊥-elim (f tt)
  iff≡ {false} {true}  f g = ⊥-elim (g tt)
  iff≡ {false} {false} f g = refl

------------------------------------------------------------------------
-- Sets versus symbolic sets.

infix 4 _∈L_ _∈ᴺ_
_∈L_ : Tuple → TSet → Set
x ∈L S = Any (x ≡_) S

_∈ᴺ_ : Nat → List Nat → Set
x ∈ᴺ S = Any (x ≡_) S

Rel : TSet → Exp → Set
Rel S E = ∀ x → (x ∈L S → x ∈E E) × (x ∈E E → x ∈L S)

rel-[] : Rel [] []
rel-[] x = (λ ()) , (λ ())

rel-++ : ∀ {S S' E E'} → Rel S E → Rel S' E' → Rel (S ++ S') (E ++ E')
rel-++ {S} {S'} {E} {E'} r r' x = to , from
  where
  to : x ∈L (S ++ S') → x ∈E (E ++ E')
  to m with any-++⁻ S m
  ... | inj₁ a = any-++l (fst (r x) a)
  ... | inj₂ b = any-++r E (fst (r' x) b)
  from : x ∈E (E ++ E') → x ∈L (S ++ S')
  from m with any-++⁻ E m
  ... | inj₁ a = any-++l (snd (r x) a)
  ... | inj₂ b = any-++r S (snd (r' x) b)

one⇒ : ∀ x {s} → x ∈E (s ∷ []) → x ∈S s
one⇒ x (here q) = q

-- Comparing generators.
module _ (Γ : Ctx) where
  private
    cs = cells Γ
    n  = dimK (homs Γ)
  open Algo (leqL cs n)

  leq≡ : ∀ x y → leqT cs n x y ≡ leqTg x y
  leq≡ []      []      = refl
  leq≡ []      (_ ∷ _) = refl
  leq≡ (_ ∷ _) []      = refl
  leq≡ (a ∷ x) (b ∷ y) = cong (leqL cs n a b ∧_) (leq≡ x y)

  covers≡ : ∀ {S R SE RE} → Rel S SE → Rel R RE → covers Γ S R ≡ cover SE RE
  covers≡ {S} {R} {SE} {RE} rS rR = iff≡ to from
    where
    to : T (covers Γ S R) → T (cover SE RE)
    to t = cover-complete SE RE λ x xE →
      let m = snd (rS x) xE
          w = anyS⇒ (leqT cs n x) R (All-T (λ s → any (leqT cs n s) R) S t m)
          y , my , l = any-witness w
      in y , subst T (leq≡ x y) l , fst (rR y) (any-at my refl)
    from : T (cover SE RE) → T (covers Γ S R)
    from t = T-All (λ s → any (leqT cs n s) R) S λ {x} m →
      let y , l , yE = cover-sound SE RE t x (fst (rS x) m)
      in anyS⇐ (leqT cs n x) R (any-mono (λ { refl → subst T (sym (leq≡ x y)) l }) (snd (rR y) yE))

  same≡ : ∀ {S R SE RE} → Rel S SE → Rel R RE → sameDown Γ S R ≡ fastSame Γ SE RE
  same≡ rS rR rewrite covers≡ rS rR | covers≡ rR rS = refl

------------------------------------------------------------------------
-- Numbers.

private
  lt-step : ∀ i n → T (i <ℕ suc n) → T (i <ℕ suc (suc n))
  lt-step zero    n       _ = tt
  lt-step (suc i) zero    ()
  lt-step (suc i) (suc n) p = lt-step i n p

  lt-refl : ∀ n → T (n <ℕ suc n)
  lt-refl zero    = tt
  lt-refl (suc n) = lt-refl n

  lt-split : ∀ i n → T (i <ℕ suc (suc n)) → T (i <ℕ suc n) ⊎ (i ≡ suc n)
  lt-split zero    n       _ = inj₁ tt
  lt-split (suc i) zero    p with i
  ... | zero = inj₂ refl
  lt-split (suc i) (suc n) p with lt-split i n p
  ... | inj₁ q = inj₁ q
  ... | inj₂ q = inj₂ (cong suc q)

  upto⇒ : ∀ i n → i ∈ᴺ upto n → T (i <ℕ suc n)
  upto⇒ i zero    (here refl) = tt
  upto⇒ i (suc n) m with any-++⁻ (upto n) m
  ... | inj₁ a = lt-step i n (upto⇒ i n a)
  ... | inj₂ (here refl) = lt-refl (suc n)

  upto⇐ : ∀ i n → T (i <ℕ suc n) → i ∈ᴺ upto n
  upto⇐ zero    zero    _ = here refl
  upto⇐ (suc i) zero    ()
  upto⇐ i       (suc n) p with lt-split i n p
  ... | inj₁ q    = any-++l (upto⇐ i n q)
  ... | inj₂ refl = any-++r (upto n) (here refl)

  filter⇒ : ∀ {a} {A : Set a} (p : A → Bool) xs {x} → Any (x ≡_) (filter p xs) → Any (x ≡_) xs × T (p x)
  filter⇒ p (y ∷ ys) m with p y in e
  filter⇒ p (y ∷ ys) (here refl) | true = here refl , subst T (sym e) tt
  filter⇒ p (y ∷ ys) (there m)   | true = let a , b = filter⇒ p ys m in there a , b
  ... | false = let a , b = filter⇒ p ys m in there a , b

  filter⇐ : ∀ {a} {A : Set a} (p : A → Bool) xs {x} → Any (x ≡_) xs → T (p x) → Any (x ≡_) (filter p xs)
  filter⇐ p (y ∷ ys) (here refl) t with p y
  ... | true  = here refl
  filter⇐ p (y ∷ ys) (there m) t with p y
  ... | true  = there (filter⇐ p ys m t)
  ... | false = filter⇐ p ys m t

  odd≡ : ∀ i → oddN i ≡ odd i
  odd≡ zero    = refl
  odd≡ (suc i) = cong not (odd≡ i)

  -- A cell in ⟨Θ⟩_i has i ≤ dim Θ.
  piece-bound : ∀ h i sg {w} → w ∈ᴺ piece h i sg → T (i <ℕ suc (hd h))
  piece-bound h i sg m with i ==ℕ hd h in e
  ... | true  = subst (λ j → T (j <ℕ suc (hd h))) (sym (==ℕ-sound i (hd h) (subst T (sym e) tt))) (lt-refl (hd h))
  ... | false with i <ℕ hd h in e'
  ...   | true  = lt-weak i (hd h) (subst T (sym e') tt)
    where
    lt-weak : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
    lt-weak zero    n       _ = tt
    lt-weak (suc i) (suc n) p = lt-weak i n p
  piece-bound h i sg () | false | false

  pick-shom : ∀ f h i sg →
              pick sg (i , concatMapL f (piece h i false) , concatMapL f (piece h i true)) ≡ concatMapL f (piece h i sg)
  pick-shom f h i true  = refl
  pick-shom f h i false = refl

------------------------------------------------------------------------
-- Products of sets.

private
  prodT⇒ : ∀ A B {x} → x ∈L prodT A B → Σ Tuple λ y → Σ Tuple λ z → (x ≡ y ++ z) × y ∈L A × z ∈L B
  prodT⇒ A B m rewrite cm≡ (λ x → map (x ++_) B) A with any-witness (any-cm⁻ _ A m)
  ... | y , my , m' rewrite map≡ (y ++_) B with any-witness (any-map⁻ (y ++_) B m')
  ...   | z , mz , refl = y , z , refl , my , mz

  prodT⇐ : ∀ A B {y z} → y ∈L A → z ∈L B → (y ++ z) ∈L prodT A B
  prodT⇐ A B {y} {z} my mz rewrite cm≡ (λ x → map (x ++_) B) A =
    any-cm⁺ _ (any-mono (λ { {y'} refl → subst (Any ((y ++ z) ≡_)) (sym (map≡ (y ++_) B)) (any-map⁺ (y ++_) (any-mono (λ { refl → refl }) mz)) }) my)

  prod1⇒ : ∀ ws C {c} → c ∈L prod1 ws C → Σ Nat λ w → Σ Tuple λ c' → (c ≡ w ∷ c') × w ∈ᴺ ws × c' ∈L C
  prod1⇒ ws C m rewrite cm≡ (λ x → map (x ∷_) C) ws with any-witness (any-cm⁻ _ ws m)
  ... | w , mw , m' rewrite map≡ (w ∷_) C with any-witness (any-map⁻ (w ∷_) C m')
  ...   | c' , mc , refl = w , c' , refl , mw , mc

  prod1⇐ : ∀ ws C {w c'} → w ∈ᴺ ws → c' ∈L C → (w ∷ c') ∈L prod1 ws C
  prod1⇐ ws C {w} {c'} mw mc rewrite cm≡ (λ x → map (x ∷_) C) ws =
    any-cm⁺ _ (any-mono (λ { refl → subst (Any ((w ∷ c') ≡_)) (sym (map≡ (w ∷_) C)) (any-map⁺ (w ∷_) (any-mono (λ { refl → refl }) mc)) }) mw)

FtupleG : (Nat → TSet) → Tuple → TSet
FtupleG g []       = [] ∷ []
FtupleG g (w ∷ ws) = prodT (g w) (FtupleG g ws)

------------------------------------------------------------------------
-- Chains: concatMap F_g (T^sg_k) versus chainE f.

module Chain (g : Nat → TSet) (f : Nat → Exp) (gf : ∀ w → Rel (g w) (f w)) where

  Fg = FtupleG g

  chain-rel : ∀ hs sg k → Rel (concatMapL Fg (chainT sg k hs)) (chainE f hs sg k ∷ [])
  chain-rel [] sg k x with k ==ℕ 0 in e
  ... | true  = (λ { (here refl) → here (schNil⇐ sg k (subst T (sym e) tt)) })
              , (λ m → let eqx , _ = schNil⇒ x sg k (one⇒ x m) in here eqx)
  ... | false = (λ ()) , (λ m → ⊥-elim (subst T e (snd (schNil⇒ x sg k (one⇒ x m)))))
  chain-rel (h ∷ hs) sg k x = to , from
    where
    L : TSet
    L = concatMap (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs))
                  (filter (λ i → i <ℕ suc k) (upto k))
    to : x ∈L concatMapL Fg L → x ∈E (chainE f (h ∷ hs) sg k ∷ [])
    to m with any-witness (any-cm⁻ Fg L m)
    ... | c , mc , mx
      rewrite cm≡ (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs))
                  (filter (λ i → i <ℕ suc k) (upto k))
      with any-witness (any-cm⁻ _ (filter (λ i → i <ℕ suc k) (upto k)) mc)
    ... | i , mi , mc' with prod1⇒ (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs) mc'
    ... | w , c' , refl , mw , mc'' with prodT⇒ (g w) (Fg c') mx
    ... | y , z , refl , my , mz with any-witness (fst (gf w y) my)
    ... | q , mq , yq =
      here (schCons⇐ (y ++ z) (shomOf f h) (mapL (shomOf f) hs) sg k
        (any-map⁺ _ (any-mono (λ { refl → snd (filter⇒ _ (upto k) mi) , ent }) (upto⇐ i (hd h) (piece-bound h i sg mw)))))
      where
      zr : z ∈S chainE f hs (flipS sg i) (k ∸ i)
      zr = subst (λ b → z ∈S chainE f hs (if b then not sg else sg) (k ∸ i)) (sym (odd≡ i))
             (one⇒ z (fst (chain-rel hs (if odd i then not sg else sg) (k ∸ i) z) (any-cm⁺ Fg (any-at mc'' mz))))
      ent : Any (λ q' → Split (y ++ z) q' (sch (mapL (shomOf f) hs) (flipS sg i) (k ∸ i) ∷ []))
                (pick sg (i , concatMapL f (piece h i false) , concatMapL f (piece h i true)))
      ent rewrite pick-shom f h i sg =
        any-cm⁺ f (any-mono (λ { refl → any-mono (λ { refl → split y z refl yq zr }) mq }) mw)
    from : x ∈E (chainE f (h ∷ hs) sg k ∷ []) → x ∈L concatMapL Fg L
    from m with any-witness (any-map⁻ _ (upto (hd h)) (schCons⇒ x (shomOf f h) (mapL (shomOf f) hs) sg k (one⇒ x m)))
    ... | i , mi , (lt , mq) rewrite pick-shom f h i sg with any-witness (any-cm⁻ f (piece h i sg) mq)
    ... | w , mw , mq' with any-witness mq'
    ... | q , mqq , split y z refl yq zr =
      any-cm⁺ Fg (any-at cL (prodT⇐ (g w) (Fg c') (snd (gf w y) (any-at mqq yq)) mz))
      where
      sg' = if odd i then not sg else sg
      zr' : z ∈S chainE f hs sg' (k ∸ i)
      zr' = subst (λ b → z ∈S chainE f hs (if b then not sg else sg) (k ∸ i)) (odd≡ i) zr
      inner : z ∈L concatMapL Fg (chainT sg' (k ∸ i) hs)
      inner = snd (chain-rel hs sg' (k ∸ i) z) (here zr')
      cz = any-witness (any-cm⁻ Fg (chainT sg' (k ∸ i) hs) inner)
      c' = fst cz
      mz : z ∈L Fg c'
      mz = snd (snd cz)
      cL : (w ∷ c') ∈L L
      cL rewrite cm≡ (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs))
                     (filter (λ i → i <ℕ suc k) (upto k)) =
        any-cm⁺ _ (any-at (filter⇐ (λ i → i <ℕ suc k) (upto k) (upto⇐ i k lt) lt)
                          (prod1⇐ (piece h i sg) (chainT sg' (k ∸ i) hs) mw (fst (snd cz))))

------------------------------------------------------------------------
-- Literal chains: the tables of T.

private
  nil-only : ∀ x → x ∈S [] → x ≡ []
  nil-only []      _  = refl
  nil-only (a ∷ x) ()

  plain-rel : ∀ w → Rel ((w ∷ []) ∷ []) (plainE w)
  plain-rel w x = to , from
    where
    to : x ∈L ((w ∷ []) ∷ []) → x ∈E plainE w
    to (here refl) = here (lit⇐ w [] (w ∷ []) [] (here refl) tt)
    from : x ∈E plainE w → x ∈L ((w ∷ []) ∷ [])
    from (here q) with lit⇒ x (w ∷ []) [] q
    ... | a , x' , refl , here refl , xr rewrite nil-only x' xr = here refl

  fg-id⇒ : ∀ c {x} → x ∈L FtupleG (λ w → (w ∷ []) ∷ []) c → x ≡ c
  fg-id⇒ []      (here refl) = refl
  fg-id⇒ (w ∷ c) m with prodT⇒ ((w ∷ []) ∷ []) (FtupleG (λ w → (w ∷ []) ∷ []) c) m
  ... | .(w ∷ []) , z , refl , here refl , mz = cong (w ∷_) (fg-id⇒ c mz)

  fg-id⇐ : ∀ c → c ∈L FtupleG (λ w → (w ∷ []) ∷ []) c
  fg-id⇐ []      = here refl
  fg-id⇐ (w ∷ c) = prodT⇐ ((w ∷ []) ∷ []) (FtupleG (λ w → (w ∷ []) ∷ []) c) (here refl) (fg-id⇐ c)

  open module PC = Chain (λ w → (w ∷ []) ∷ []) plainE plain-rel using () renaming (chain-rel to pchain)

chainT-rel : ∀ hs sg k → Rel (chainT sg k hs) (chainE plainE hs sg k ∷ [])
chainT-rel hs sg k x = to , from
  where
  to : x ∈L chainT sg k hs → x ∈E (chainE plainE hs sg k ∷ [])
  to m = fst (pchain hs sg k x) (any-cm⁺ _ (any-at m (fg-id⇐ x)))
  from : x ∈E (chainE plainE hs sg k ∷ []) → x ∈L chainT sg k hs
  from m with any-witness (any-cm⁻ _ (chainT sg k hs) (snd (pchain hs sg k x) m))
  ... | c , mc , mx rewrite fg-id⇒ c mx = mc

lower-rel : ∀ m hs → Rel (lowerT m hs) (lowerE m hs)
lower-rel zero    hs = rel-[]
lower-rel (suc m) hs =
  rel-++ (lower-rel m hs) (rel-++ (chainT-rel hs false m) (chainT-rel hs true m))

full-rel : ∀ hs → Rel (fullT hs) (fullE hs)
full-rel hs = rel-++ (lower-rel (dimK hs) hs) (chainT-rel hs true (dimK hs))

bdry-rel : ∀ sg hs → Rel (bdryT sg hs) (bdryE sg hs)
bdry-rel sg hs = rel-++ (lower-rel (dimK hs ∸ 1) hs) (chainT-rel hs sg (dimK hs ∸ 1))

------------------------------------------------------------------------
-- Supports of terms.

data PwR : List TSet → List Exp → Set where
  []  : PwR [] []
  _∷_ : ∀ {S E Ss Es} → Rel S E → PwR Ss Es → PwR (S ∷ Ss) (E ∷ Es)

private
  pw-snoc : ∀ {Ss Es S E} → PwR Ss Es → Rel S E → PwR (Ss ++ (S ∷ [])) (Es ++ (E ∷ []))
  pw-snoc []       r = r ∷ []
  pw-snoc (q ∷ qs) r = q ∷ pw-snoc qs r

  nth-rel : ∀ w {Ss Es} → PwR Ss Es → Rel (nth w Ss) (nthE w Es)
  nth-rel w       []       = rel-[]
  nth-rel zero    (r ∷ _)  = r
  nth-rel (suc w) (_ ∷ rs) = nth-rel w rs

  Ftuple≡ : ∀ tops c → Ftuple tops c ≡ FtupleG (λ w → nth w tops) c
  Ftuple≡ tops []      = refl
  Ftuple≡ tops (w ∷ c) = cong (prodT (nth w tops)) (Ftuple≡ tops c)

cohRel : ∀ Θ A t u ρ → fastCoh Θ A t u ≡ cohCase Θ A t u → PwR (topsSub ρ) (topsSubE ρ) →
         Rel (topS (coh Θ (arr A t u) ρ)) (topSE (coh Θ (arr A t u) ρ))
cohRel Θ A t u ρ eq pw rewrite eq with cohCase Θ A t u
... | true  = rel-[]
... | false
  rewrite cm≡ (Ftuple (topsSub ρ)) (chainT true (dimK (homs Θ)) (homs Θ))
        | cm-cong (Ftuple≡ (topsSub ρ)) (chainT true (dimK (homs Θ)) (homs Θ))
  = Chain.chain-rel (λ w → nth w (topsSub ρ)) (λ w → nthE w (topsSubE ρ))
                    (λ w → nth-rel w pw) (homs Θ) true (dimK (homs Θ))

mutual
  topS-rel : ∀ t → Rel (topS t) (topSE t)
  topS-rel (var v)               = plain-rel v
  topS-rel (cst _)               = rel-[]
  topS-rel (coh Θ ⋆ ρ)           = rel-[]
  topS-rel (coh Θ (arr A t u) ρ) = cohRel Θ A t u ρ (coh≡ Θ A t u) (topsSub-rel ρ)

  topsSub-rel : ∀ ρ → PwR (topsSub ρ) (topsSubE ρ)
  topsSub-rel ⟨⟩       = []
  topsSub-rel (ρ ,ₛ t) = pw-snoc (topsSub-rel ρ) (topS-rel t)

  suppTy-rel : ∀ A → Rel (suppTy A) (suppTyE A)
  suppTy-rel ⋆                      = rel-[]
  suppTy-rel (arr ⋆ _ _)            = rel-[]
  suppTy-rel (arr (arr B s s') t u) =
    rel-++ (suppTy-rel (arr B s s')) (rel-++ (topS-rel t) (topS-rel u))

  coh≡ : ∀ Θ A t u → fastCoh Θ A t u ≡ cohCase Θ A t u
  coh≡ Θ ⋆ t u = refl
  coh≡ Θ (arr B s s') t u =
    cong₂ (λ a b → endsOK Θ (arr B s s') ∧ a ∧ b)
      (sym (same≡ Θ (rel-++ (topS-rel t) (suppTy-rel (arr B s s'))) (full-rel (homs Θ))))
      (sym (same≡ Θ (rel-++ (topS-rel u) (suppTy-rel (arr B s s'))) (full-rel (homs Θ))))

supp-rel : ∀ t A → Rel (supp t A) (suppE t A)
supp-rel t A = rel-++ (topS-rel t) (suppTy-rel A)

op≡ : ∀ Θ A t u → fastOp Θ A t u ≡ opCase Θ A t u
op≡ Θ ⋆ t u = refl
op≡ Θ (arr B s s') t u
  rewrite same≡ Θ (supp-rel t (arr B s s')) (bdry-rel false (homs Θ))
        | same≡ Θ (supp-rel u (arr B s s')) (bdry-rel true (homs Θ)) = refl

-- The main result: the symbolic side condition is the side condition.
fastSide-correct : ∀ Θ A t u → fastSide Θ A t u ≡ graySide Θ A t u
fastSide-correct Θ A t u rewrite coh≡ Θ A t u | op≡ Θ A t u = refl
