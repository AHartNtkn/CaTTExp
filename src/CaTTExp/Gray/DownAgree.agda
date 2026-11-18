------------------------------------------------------------------------
-- The closure-free comparison of downsets agrees with the closure-based
-- one (notes/agda-gray-findings.md, "Fast side condition").
--
-- The side condition decides ↓S = ↓R by `sameDown`: every generator of
-- S is below one of R in the entrywise face order `leqT` (at most
-- N = dim K(Γ) source/target steps per entry), and vice versa. The
-- earlier definition, `sameDownClosure`, builds both closures with
-- `closeN N` (at most N face steps in total) and compares them.
--
-- Results, for every context Γ and all finite S, R:
--
--   closure⇒same : sameDownClosure Γ S R → sameDown Γ S R
--       with no hypotheses;
--
--   same⇒closure : Graded Γ → RankOK Γ S → RankOK Γ R →
--                  sameDown Γ S R → sameDownClosure Γ S R
--   sameDown≡Closure : (same hypotheses) → sameDown Γ S R ≡ sameDownClosure Γ S R
--
-- Graded: every source/target of a cell is one hom-dimension lower
-- (`suc (hgt b) ≡ hgt w`). RankOK: every tuple has total hom-dimension
-- at most N, as every cell of K(Γ) does. Both are decidable
-- (`gradedB`, `rankB`, with soundness), and both are needed:
-- `closeN N` counts steps over the whole tuple, `leqT N` per entry,
-- and the two counts agree only when every step lowers the rank by
-- one and the rank starts at most N. Gray.Graded proves that they
-- hold for every comparison the side condition makes in a pasting
-- context.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.DownAgree (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊

------------------------------------------------------------------------
-- Equality tests, sets.

private
  ==T-sound : ∀ x y → T (x ==T y) → x ≡ y
  ==T-sound []       []       _ = refl
  ==T-sound (a ∷ x)  (b ∷ y)  p =
    cong₂ _∷_ (==ℕ-sound a b (∧-fst {a ==ℕ b} p)) (==T-sound x y (∧-snd {a ==ℕ b} p))
  ==T-sound []       (_ ∷ _)  ()
  ==T-sound (_ ∷ _)  []       ()

  ==T-refl : ∀ x → T (x ==T x)
  ==T-refl []      = tt
  ==T-refl (a ∷ x) = ∧-in (==ℕ-refl a) (==T-refl x)

  memT⇒ : ∀ x S → T (memT x S) → x ∈L S
  memT⇒ x S p = any-mono (λ {y} q → ==T-sound x y q) (anyS⇒ (x ==T_) S p)

  memT⇐ : ∀ x S → x ∈L S → T (memT x S)
  memT⇐ x S m = anyS⇐ (x ==T_) S (any-mono (λ { refl → ==T-refl x }) m)

  nub⇒ : ∀ S {x} → x ∈L nubT S → x ∈L S
  nub⇒ (y ∷ ys) m with memT y ys
  ... | true  = there (nub⇒ ys m)
  nub⇒ (y ∷ ys) (here q)  | false = here q
  nub⇒ (y ∷ ys) (there m) | false = there (nub⇒ ys m)

  nub⇐ : ∀ S {x} → x ∈L S → x ∈L nubT S
  nub⇐ (y ∷ ys) m with memT y ys in e
  nub⇐ (y ∷ ys) (here refl) | true  = nub⇐ ys (memT⇒ y ys (subst T (sym e) tt))
  nub⇐ (y ∷ ys) (there m)   | true  = nub⇐ ys m
  nub⇐ (y ∷ ys) (here q)    | false = here q
  nub⇐ (y ∷ ys) (there m)   | false = there (nub⇐ ys m)

  ⊆T⇒ : ∀ A B → T (⊆T A B) → ∀ {x} → x ∈L A → x ∈L B
  ⊆T⇒ A B p {x} m = memT⇒ x B (All-T (λ y → memT y B) A p m)

  ⊆T⇐ : ∀ A B → (∀ {x} → x ∈L A → x ∈L B) → T (⊆T A B)
  ⊆T⇐ A B f = T-All (λ y → memT y B) A (λ {x} m → memT⇐ x B (f m))

  lt⇒≤ : ∀ i n → T (i <ℕ suc n) → i ≤ n
  lt⇒≤ zero    n       _ = z≤n
  lt⇒≤ (suc i) (suc n) p = s≤s (lt⇒≤ i n p)

  ≤⇒lt : ∀ i n → i ≤ n → T (i <ℕ suc n)
  ≤⇒lt zero    n       _       = tt
  ≤⇒lt (suc i) (suc n) (s≤s p) = ≤⇒lt i n p

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  ≤0 : ∀ {k} → k ≤ 0 → k ≡ 0
  ≤0 z≤n = refl

-- Exported, for the strict model.
memT-sound : ∀ x S → T (memT x S) → x ∈L S
memT-sound = memT⇒

memT-complete : ∀ x S → x ∈L S → T (memT x S)
memT-complete = memT⇐

nub-sound : ∀ S {x} → x ∈L nubT S → x ∈L S
nub-sound = nub⇒

nub-complete : ∀ S {x} → x ∈L S → x ∈L nubT S
nub-complete = nub⇐

------------------------------------------------------------------------
-- Face steps and reachability, for a fixed list of cells.

module Faces (cs : List El) where

  -- One source/target step on one entry.
  data Step : Tuple → Tuple → Set where
    sh : ∀ {w b ws}   → b ∈ᴺ bdEl cs w → Step (w ∷ ws) (b ∷ ws)
    st : ∀ {w ws ws'} → Step ws ws'    → Step (w ∷ ws) (w ∷ ws')

  -- Exactly k steps.
  data Reach : Nat → Tuple → Tuple → Set where
    done : ∀ {x} → Reach 0 x x
    step : ∀ {k x y z} → Step x y → Reach k y z → Reach (suc k) x z

  -- Exactly k steps on one entry.
  data LR : Nat → Nat → Nat → Set where
    lz : ∀ {a} → LR 0 a a
    ls : ∀ {k b c a} → c ∈ᴺ bdEl cs b → LR k c a → LR (suc k) b a

  -- Entrywise, at most n steps per entry.
  data Pw (n : Nat) : Tuple → Tuple → Set where
    pnil  : Pw n [] []
    pcons : ∀ {a b x r} k → k ≤ n → LR k b a → Pw n x r → Pw n (a ∷ x) (b ∷ r)

  -- x is reached from some s ∈ S in at most n steps.
  InClo : Nat → TSet → Tuple → Set
  InClo n S x = Σ Tuple λ s → s ∈L S × Σ Nat λ k → (k ≤ n) × Reach k s x

  reach-++ : ∀ {j k x y z} → Reach j x y → Reach k y z → Reach (j + k) x z
  reach-++ done       q = q
  reach-++ (step s p) q = step s (reach-++ p q)

  lift-tail : ∀ {k w r x} → Reach k r x → Reach k (w ∷ r) (w ∷ x)
  lift-tail done       = done
  lift-tail (step s p) = step (st s) (lift-tail p)

  lift-head : ∀ {k b a x} → LR k b a → Reach k (b ∷ x) (a ∷ x)
  lift-head lz       = done
  lift-head (ls c p) = step (sh c) (lift-head p)

  pw-mono : ∀ {n m x r} → n ≤ m → Pw n x r → Pw m x r
  pw-mono le pnil             = pnil
  pw-mono le (pcons k l lr p) = pcons k (≤-trans l le) lr (pw-mono le p)

  pw-refl : ∀ n x → Pw n x x
  pw-refl n []      = pnil
  pw-refl n (a ∷ x) = pcons 0 z≤n lz (pw-refl n x)

  pw-step : ∀ {k r y x} → Step r y → Pw k x y → Pw (suc k) x r
  pw-step (sh c) (pcons j l lr p) = pcons (suc j) (s≤s l) (ls c lr) (pw-mono (≤-step (≤-refl _)) p)
  pw-step (st s) (pcons j l lr p) = pcons j (≤-step l) lr (pw-step s p)

  -- Reaching x from r in k steps puts x below r entrywise, with ≤ k
  -- steps per entry.
  reach⇒pw : ∀ {k r x} → Reach k r x → Pw k x r
  reach⇒pw {x = x} done = pw-refl 0 x
  reach⇒pw (step s p)   = pw-step s (reach⇒pw p)

  -- Conversely, entrywise paths compose to a path of the tuple.
  pw⇒reach : ∀ {n x r} → Pw n x r → Σ Nat λ k → Reach k r x
  pw⇒reach pnil = 0 , done
  pw⇒reach (pcons {a} {b} {x} {r} j l lr p) with pw⇒reach p
  ... | k , q = k + j , reach-++ (lift-tail q) (lift-head lr)

  ----------------------------------------------------------------------
  -- leqL and leqT are the bounded path relations.

  mutual
    leqL⇒ : ∀ n a b → T (leqL cs n a b) → Σ Nat λ k → (k ≤ n) × LR k b a
    leqL⇒ zero    a b p = 0 , z≤n , subst (λ c → LR 0 c a) (==ℕ-sound a b p) lz
    leqL⇒ (suc n) a b p with ∨-out {a ==ℕ b} p
    ... | inj₁ q = 0 , z≤n , subst (λ c → LR 0 c a) (==ℕ-sound a b q) lz
    ... | inj₂ q with leqAny⇒ n a (bdEl cs b) q
    ...   | c , mc , q' with leqL⇒ n a c q'
    ...     | k , l , lr = suc k , s≤s l , ls mc lr

    leqAny⇒ : ∀ n a bs → T (leqAny cs n a bs) → Σ Nat λ c → (c ∈ᴺ bs) × T (leqL cs n a c)
    leqAny⇒ n a (c ∷ bs) p with ∨-out {leqL cs n a c} p
    ... | inj₁ q = c , here refl , q
    ... | inj₂ q with leqAny⇒ n a bs q
    ...   | c' , m , q' = c' , there m , q'

  leqL-refl : ∀ n a → T (leqL cs n a a)
  leqL-refl zero    a = ==ℕ-refl a
  leqL-refl (suc n) a = ∨-inl (==ℕ-refl a)

  leqAny⇐ : ∀ n a bs {c} → c ∈ᴺ bs → T (leqL cs n a c) → T (leqAny cs n a bs)
  leqAny⇐ n a (c ∷ bs) (here refl) q = ∨-inl q
  leqAny⇐ n a (c ∷ bs) (there m)   q = ∨-inr {leqL cs n a c} (leqAny⇐ n a bs m q)

  leqL⇐ : ∀ n {k a b} → k ≤ n → LR k b a → T (leqL cs n a b)
  leqL⇐ n {a = a} _ lz = leqL-refl n a
  leqL⇐ (suc n) {a = a} {b} (s≤s l) (ls mc lr) = ∨-inr {a ==ℕ b} (leqAny⇐ n a (bdEl cs b) mc (leqL⇐ n l lr))

  leqT⇒ : ∀ n x r → T (leqT cs n x r) → Pw n x r
  leqT⇒ n []      []      _ = pnil
  leqT⇒ n (a ∷ x) (b ∷ r) p with leqL⇒ n a b (∧-fst {leqL cs n a b} p)
  ... | k , l , lr = pcons k l lr (leqT⇒ n x r (∧-snd {leqL cs n a b} p))
  leqT⇒ n []      (_ ∷ _) ()
  leqT⇒ n (_ ∷ _) []      ()

  leqT⇐ : ∀ {n x r} → Pw n x r → T (leqT cs n x r)
  leqT⇐ pnil                  = tt
  leqT⇐ {n} (pcons k l lr p)  = ∧-in (leqL⇐ n l lr) (leqT⇐ p)

  ----------------------------------------------------------------------
  -- closeN is the bounded reachability closure.

  faces⇒ : ∀ x {y} → y ∈L facesT cs x → Step x y
  faces⇒ (w ∷ ws) m with any-++⁻ (map (_∷ ws) (bdEl cs w)) m
  ... | inj₁ a with any-witness (any-map⁻ (_∷ ws) (bdEl cs w) (subst (Any _) (map≡ (_∷ ws) (bdEl cs w)) a))
  ...   | b , mb , refl = sh mb
  faces⇒ (w ∷ ws) m | inj₂ a
    with any-witness (any-map⁻ (w ∷_) (facesT cs ws) (subst (Any _) (map≡ (w ∷_) (facesT cs ws)) a))
  ... | y' , my , refl = st (faces⇒ ws my)

  faces⇐ : ∀ {x y} → Step x y → y ∈L facesT cs x
  faces⇐ {w ∷ ws} (sh {b = b} mb) =
    any-++l (subst (Any _) (sym (map≡ (_∷ ws) (bdEl cs w))) (any-map⁺ (_∷ ws) (any-mono (λ { refl → refl }) mb)))
  faces⇐ {w ∷ ws} (st s) =
    any-++r (map (_∷ ws) (bdEl cs w))
      (subst (Any _) (sym (map≡ (w ∷_) (facesT cs ws))) (any-map⁺ (w ∷_) (any-mono (λ { refl → refl }) (faces⇐ s))))

  private
    nextS : TSet → TSet
    nextS S = nubT (S ++ concatMap (facesT cs) S)

    next⇒ : ∀ S {y} → y ∈L nextS S → y ∈L S ⊎ (Σ Tuple λ s → s ∈L S × Step s y)
    next⇒ S m with any-++⁻ S (nub⇒ (S ++ concatMap (facesT cs) S) m)
    ... | inj₁ a = inj₁ a
    ... | inj₂ b with any-witness (any-cm⁻ (facesT cs) S (subst (Any _) (cm≡ (facesT cs) S) b))
    ...   | s , ms , my = inj₂ (s , ms , faces⇒ s my)

    next-S : ∀ S {y} → y ∈L S → y ∈L nextS S
    next-S S m = nub⇐ (S ++ concatMap (facesT cs) S) (any-++l m)

    next-F : ∀ S {s y} → s ∈L S → Step s y → y ∈L nextS S
    next-F S ms st' =
      nub⇐ (S ++ concatMap (facesT cs) S)
        (any-++r S (subst (Any _) (sym (cm≡ (facesT cs) S)) (any-cm⁺ (facesT cs) (any-at ms (faces⇐ st')))))

  close⇒ : ∀ n S {x} → x ∈L closeN n cs S → InClo n S x
  close⇒ zero    S {x} m = x , m , 0 , z≤n , done
  close⇒ (suc n) S m with close⇒ n (nextS S) m
  ... | s' , ms' , k , l , r with next⇒ S ms'
  ...   | inj₁ a              = s' , a , k , ≤-step l , r
  ...   | inj₂ (s , ms , st') = s , ms , suc k , s≤s l , step st' r

  close⇐ : ∀ n S {x} → InClo n S x → x ∈L closeN n cs S
  close⇐ zero    S (s , ms , k , l , r) with ≤0 l
  close⇐ zero    S (s , ms , .0 , l , done) | refl = ms
  close⇐ (suc n) S (s , ms , 0 , l , done) = close⇐ n (nextS S) (s , next-S S ms , 0 , z≤n , done)
  close⇐ (suc n) S (s , ms , suc k , s≤s l , step st' r) =
    close⇐ n (nextS S) (_ , next-F S ms st' , k , l , r)

  ----------------------------------------------------------------------
  -- Ranks.

  hgtM : Maybe El → Nat
  hgtM nothing  = 0
  hgtM (just c) = hdim c

  -- The hom-dimension of an entry (0 if it is not a cell).
  hgt : Nat → Nat
  hgt w = hgtM (findEl w cs)

  rank : Tuple → Nat
  rank x = sumL (map hgt x)

  Graded : Set
  Graded = ∀ w {b} → b ∈ᴺ bdEl cs w → suc (hgt b) ≡ hgt w

  module _ (G : Graded) where
    lr-rank : ∀ {k b a} → LR k b a → hgt a + k ≡ hgt b
    lr-rank {a = a} lz = +-zero (hgt a)
    lr-rank {suc k} {b} {a} (ls {c = c} mc lr) =
      trans (+-suc (hgt a) k) (trans (cong suc (lr-rank lr)) (G b mc))

    step-rank : ∀ {r y} → Step r y → suc (rank y) ≡ rank r
    step-rank {w ∷ ws} (sh {b = b} mb) = cong (_+ rank ws) (G w mb)
    step-rank {w ∷ ws} (st {ws' = ws'} s) = trans (sym (+-suc (hgt w) (rank ws'))) (cong (hgt w +_) (step-rank s))

    reach-rank : ∀ {k r x} → Reach k r x → rank x + k ≡ rank r
    reach-rank {x = x} done = +-zero (rank x)
    reach-rank {suc k} {x = x} (step s p) = trans (+-suc (rank x) k) (trans (cong suc (reach-rank p)) (step-rank s))

    reach-bound : ∀ {k r x N} → Reach k r x → rank r ≤ N → k ≤ N
    reach-bound {k} {x = x} p l = ≤-trans (subst (k ≤_) (reach-rank p) (n≤m+n (rank x) k)) l

------------------------------------------------------------------------
-- Decidable versions of the hypotheses.

module _ (cs : List El) where
  open Faces cs

  gradedB : Bool
  gradedB = all (λ c → all (λ b → suc (hgt b) ==ℕ hgt (lvl c)) (bdEl cs (lvl c))) cs

  private
    findEl-in : ∀ w cs' {c} → findEl w cs' ≡ just c → Any (c ≡_) cs' × (lvl c ≡ w)
    findEl-in w (c ∷ cs') e with lvl c ==ℕ w in q
    findEl-in w (c ∷ cs') refl | true  = here refl , ==ℕ-sound (lvl c) w (subst T (sym q) tt)
    ... | false with findEl-in w cs' e
    ...   | m , l = there m , l

    -- bdEl only depends on the cell findEl returns.
    bd-nothing : ∀ w → findEl w cs ≡ nothing → bdEl cs w ≡ []
    bd-nothing w e with findEl w cs
    bd-nothing w refl | nothing = refl

  graded-sound : T gradedB → Graded
  graded-sound p w mb = go w (findEl w cs) refl mb
    where
    go : ∀ w m {b} → findEl w cs ≡ m → b ∈ᴺ bdEl cs w → suc (hgt b) ≡ hgt w
    go w nothing e mb = ⊥-elim (absurd (subst (λ l → _ ∈ᴺ l) (bd-nothing w e) mb))
      where absurd : ∀ {b} → b ∈ᴺ [] → ⊥
            absurd ()
    go w (just c) e mb with findEl-in w cs e
    ... | mc , refl =
      ==ℕ-sound _ _ (All-T (λ b → suc (hgt b) ==ℕ hgt (lvl c)) (bdEl cs (lvl c))
                       (All-T (λ c → all (λ b → suc (hgt b) ==ℕ hgt (lvl c)) (bdEl cs (lvl c))) cs p mc) mb)

  rankB : Nat → TSet → Bool
  rankB N S = all (λ x → rank x <ℕ suc N) S

  RankOK : Nat → TSet → Set
  RankOK N S = ∀ {x} → x ∈L S → rank x ≤ N

  rank-sound : ∀ N S → T (rankB N S) → RankOK N S
  rank-sound N S p {x} m = lt⇒≤ (rank x) N (All-T (λ x → rank x <ℕ suc N) S p m)

------------------------------------------------------------------------
-- The theorems.

module _ (Γ : Ctx) where
  private
    cs = cells Γ
    N  = dimK (homs Γ)
  open Faces cs

  private
    covers⇒ : ∀ S R → T (covers Γ S R) → ∀ {s} → s ∈L S → Σ Tuple λ r → r ∈L R × Pw N s r
    covers⇒ S R p {s} ms with any-witness (anyS⇒ (leqT cs N s) R (All-T (λ s → any (leqT cs N s) R) S p ms))
    ... | r , mr , q = r , mr , leqT⇒ N s r q

    covers⇐ : ∀ S R → (∀ {s} → s ∈L S → Σ Tuple λ r → r ∈L R × Pw N s r) → T (covers Γ S R)
    covers⇐ S R f = T-All (λ s → any (leqT cs N s) R) S λ {s} ms →
      let r , mr , pw = f ms in anyS⇐ (leqT cs N s) R (any-at mr (leqT⇐ pw))

    down⇒ : ∀ S {x} → x ∈L down Γ S → InClo N S x
    down⇒ S m with close⇒ N (nubT S) m
    ... | s , ms , k = s , nub⇒ S ms , k

    down⇐ : ∀ S {x} → InClo N S x → x ∈L down Γ S
    down⇐ S (s , ms , k) = close⇐ N (nubT S) (s , nub⇐ S ms , k)

    -- ↓S ⊆ ↓R by closures gives S ⊆ ↓R on generators.
    clo⇒cov : ∀ S R → T (⊆T (down Γ S) (down Γ R)) → T (covers Γ S R)
    clo⇒cov S R p = covers⇐ S R λ {s} ms →
      let r , mr , k , l , q = down⇒ R (⊆T⇒ (down Γ S) (down Γ R) p (down⇐ S (s , ms , 0 , z≤n , done)))
      in r , mr , pw-mono l (reach⇒pw q)

    -- S ⊆ ↓R on generators gives ↓S ⊆ ↓R, when paths lower the rank.
    cov⇒clo : Graded → ∀ S R → RankOK cs N R → T (covers Γ S R) → T (⊆T (down Γ S) (down Γ R))
    cov⇒clo G S R ok p = ⊆T⇐ (down Γ S) (down Γ R) λ {x} m →
      let s , ms , k , l , q = down⇒ S m
          r , mr , pw = covers⇒ S R p ms
          j , q' = pw⇒reach pw
          q'' = reach-++ q' q
      in down⇐ R (r , mr , j + k , reach-bound G q'' (ok mr) , q'')

  closure⇒same : ∀ S R → T (sameDownClosure Γ S R) → T (sameDown Γ S R)
  closure⇒same S R p =
    ∧-in (clo⇒cov S R (∧-fst {⊆T (down Γ S) (down Γ R)} p)) (clo⇒cov R S (∧-snd {⊆T (down Γ S) (down Γ R)} p))

  same⇒closure : Graded → ∀ S R → RankOK cs N S → RankOK cs N R →
                 T (sameDown Γ S R) → T (sameDownClosure Γ S R)
  same⇒closure G S R okS okR p =
    ∧-in (cov⇒clo G S R okR (∧-fst {covers Γ S R} p)) (cov⇒clo G R S okS (∧-snd {covers Γ S R} p))

  sameDown≡Closure : Graded → ∀ S R → RankOK cs N S → RankOK cs N R →
                     sameDown Γ S R ≡ sameDownClosure Γ S R
  sameDown≡Closure G S R okS okR = iff≡ (same⇒closure G S R okS okR) (closure⇒same S R)

  -- With the hypotheses checked by evaluation.
  sameDown≡Closureᴮ : ∀ S R → T (gradedB cs) → T (rankB cs N S) → T (rankB cs N R) →
                      sameDown Γ S R ≡ sameDownClosure Γ S R
  sameDown≡Closureᴮ S R g rS rR =
    sameDown≡Closure (graded-sound cs g) S R (rank-sound cs N S rS) (rank-sound cs N R rR)

-- The hypotheses for every comparison the side condition makes on
-- (Θ, A, t, u): Θ graded, and all of supp t A, supp u A, Supp T,
-- Supp ∂^±T of rank ≤ dim K(Θ).
hypSide : Ctx → Ty → Tm → Tm → Bool
hypSide Θ ⋆ t u = true
hypSide Θ A@(arr _ _ _) t u =
  gradedB (cells Θ) ∧
  all (rankB (cells Θ) (dimK (homs Θ)))
      (supp t A ∷ supp u A ∷ fullT (homs Θ) ∷ bdryT false (homs Θ) ∷ bdryT true (homs Θ) ∷ [])

-- Under hypSide, each of the four comparisons of the side condition
-- may be read as closure equality.
module HypSide (Θ : Ctx) (B : Ty) (s s' t u : Tm) (h : T (hypSide Θ (arr B s s') t u)) where
  private
    A  = arr B s s'
    hs = homs Θ
    cs = cells Θ
    N  = dimK hs
    Ls = supp t A ∷ supp u A ∷ fullT hs ∷ bdryT false hs ∷ bdryT true hs ∷ []

    clo : ∀ {S F} → Any (S ≡_) Ls → Any (F ≡_) Ls → T (sameDown Θ S F) → T (sameDownClosure Θ S F)
    clo {S} {F} mS mF p =
      subst T (sameDown≡Closureᴮ Θ S F (∧-fst h)
                 (All-T (rankB cs N) Ls (∧-snd {gradedB cs} h) mS)
                 (All-T (rankB cs N) Ls (∧-snd {gradedB cs} h) mF)) p

  coh-t : T (sameDown Θ (supp t A) (fullT hs)) → T (sameDownClosure Θ (supp t A) (fullT hs))
  coh-t = clo (here refl) (there (there (here refl)))

  coh-u : T (sameDown Θ (supp u A) (fullT hs)) → T (sameDownClosure Θ (supp u A) (fullT hs))
  coh-u = clo (there (here refl)) (there (there (here refl)))

  op-t : T (sameDown Θ (supp t A) (bdryT false hs)) → T (sameDownClosure Θ (supp t A) (bdryT false hs))
  op-t = clo (here refl) (there (there (there (here refl))))

  op-u : T (sameDown Θ (supp u A) (bdryT true hs)) → T (sameDownClosure Θ (supp u A) (bdryT true hs))
  op-u = clo (there (here refl)) (there (there (there (there (here refl)))))
