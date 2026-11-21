------------------------------------------------------------------------
-- Reachability in a finite graph is decidable
-- (spec/02-lax-core.md §2.3, "Side condition and decision procedure";
-- ledger S3).
--
-- A graph is a step function `next : A → List A` on a type with
-- decidable equality. A universe U is a list closed under `next`.
-- From any vertex of U, reachability is decidable:
--
--   shorten   every path can be cut to one with pairwise distinct
--             vertices (loop removal);
--   pigeon    such a path visits at most |U| vertices
--             (CaTTExp.Join.Finite.pigeon);
--   reach?    so a search to depth |U| decides reachability;
--   reachSet  the set of vertices reachable from p, computed by
--             breadth-first saturation with early stop, and proved to
--             be exactly that set (reachSet-sound, reachSet-complete).
--             This is the form used to compute: `reach?` searches
--             depth-first without memory.
--
-- Unlike CaTTExp.Join.BoundedReach, no length bound is assumed: the
-- bound is derived from the finite universe. The kernel uses this for
-- equality of cells (connectivity in the graph of one-step equation
-- applications, r10 Response 3 "Building the normal forms"), where the
-- universe is the finite list of raw words of a given weight.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite
  using (_∈L_; here; there; NoDup; []; _∷_; pigeon; _≤_; z≤n; s≤s; lengthL)
open import CaTTExp.Uniform.ListKit

module CaTTExp.Uniform.FiniteGraph
  {A : Set} (_≟_ : (x y : A) → Dec (x ≡ y)) (next : A → List A) where

------------------------------------------------------------------------
-- Paths.

infixr 5 _◅_
data Star : A → A → Set where
  ε   : ∀ {x} → Star x x
  _◅_ : ∀ {x y z} → y ∈L next x → Star y z → Star x z

_◅◅_ : ∀ {x y z} → Star x y → Star y z → Star x z
ε       ◅◅ t = t
(m ◅ s) ◅◅ t = m ◅ (s ◅◅ t)

-- The vertices a path leaves from (its source and every intermediate
-- vertex, not its target).
verts : ∀ {x z} → Star x z → List A
verts {x} ε       = []
verts {x} (_ ◅ s) = x ∷ verts s

------------------------------------------------------------------------
-- Membership is decidable.

mem? : (x : A) (xs : List A) → Dec (x ∈L xs)
mem? x [] = no λ ()
mem? x (y ∷ ys) with x ≟ y
... | yes refl = yes here
... | no x≠y with mem? x ys
...   | yes m = yes (there m)
...   | no ¬m = no λ { here → x≠y refl ; (there m) → ¬m m }

------------------------------------------------------------------------
-- Loop removal.

data Suffix : List A → List A → Set where
  stop : ∀ {xs} → Suffix xs xs
  skip : ∀ {xs y ys} → Suffix xs ys → Suffix xs (y ∷ ys)

nodup-suffix : ∀ {xs ys} → Suffix xs ys → NoDup ys → NoDup xs
nodup-suffix stop     nd       = nd
nodup-suffix (skip s) (_ ∷ nd) = nodup-suffix s nd

-- The part of a path from one of its vertices on.
drop-to : ∀ {y z w} (s : Star y z) → w ∈L verts s →
          Σ (Star w z) λ s′ → Suffix (verts s′) (verts s)
drop-to (m ◅ s) here      = (m ◅ s) , stop
drop-to (m ◅ s) (there k) with drop-to s k
... | s′ , sf = s′ , skip sf

shorten : ∀ {x z} → Star x z → Σ (Star x z) λ s → NoDup (verts s)
shorten ε = ε , []
shorten {x} (m ◅ s) with shorten s
... | s′ , nd with mem? x (verts s′)
...   | yes k = let r = drop-to s′ k in fst r , nodup-suffix (snd r) nd
...   | no ¬k = (m ◅ s′) , (¬k ∷ nd)

------------------------------------------------------------------------
-- Bounded search.

data Within : Nat → A → A → Set where
  now   : ∀ {k x} → Within k x x
  later : ∀ {k x y z} → y ∈L next x → Within k y z → Within (suc k) x z

within→star : ∀ {k x z} → Within k x z → Star x z
within→star now         = ε
within→star (later m w) = m ◅ within→star w

within-mono : ∀ {k k′ x z} → k ≤ k′ → Within k x z → Within k′ x z
within-mono _       now         = now
within-mono (s≤s p) (later m w) = later m (within-mono p w)

star→within : ∀ {x z} (s : Star x z) → Within (lengthL (verts s)) x z
star→within ε       = now
star→within (m ◅ s) = later m (star→within s)

mutual
  within? : ∀ k x z → Dec (Within k x z)
  within? zero x z with x ≟ z
  ... | yes refl = yes now
  ... | no x≠z   = no λ { now → x≠z refl }
  within? (suc k) x z with x ≟ z
  ... | yes refl = yes now
  ... | no x≠z with any? k z (next x)
  ...   | yes (y , m , w) = yes (later m w)
  ...   | no ¬r = no λ { now → x≠z refl ; (later m w) → ¬r (_ , m , w) }

  any? : ∀ k z (ys : List A) → Dec (Σ A λ y → (y ∈L ys) × Within k y z)
  any? k z [] = no λ { (_ , () , _) }
  any? k z (y ∷ ys) with within? k y z
  ... | yes w = yes (y , here , w)
  ... | no ¬w with any? k z ys
  ...   | yes (y′ , m , w) = yes (y′ , there m , w)
  ...   | no ¬r = no λ { (_ , here , w) → ¬w w
                       ; (y′ , there m , w) → ¬r (y′ , m , w) }

------------------------------------------------------------------------
-- A finite universe closed under steps.

module Universe (U : List A)
                (closed : ∀ {x y} → x ∈L U → y ∈L next x → y ∈L U) where

  verts-in : ∀ {x z} → x ∈L U → (s : Star x z) → ∀ {w} → w ∈L verts s → w ∈L U
  verts-in xu (m ◅ s) here      = xu
  verts-in xu (m ◅ s) (there k) = verts-in (closed xu m) s k

  -- Every path from U can be replaced by one of length at most |U|.
  bounded : ∀ {x z} → x ∈L U → Star x z → Within (lengthL U) x z
  bounded xu s with shorten s
  ... | s′ , nd = within-mono (pigeon nd (verts-in xu s′)) (star→within s′)

  reach? : ∀ {x} → x ∈L U → ∀ z → Dec (Star x z)
  reach? {x} xu z with within? (lengthL U) x z
  ... | yes w = yes (within→star w)
  ... | no ¬w = no λ s → ¬w (bounded xu s)

------------------------------------------------------------------------
-- Breadth-first saturation.

-- (Written through `ins` so that the recursive call is evaluated once.)
ins : A → List A → List A
ins x ys with mem? x ys
... | yes _ = ys
... | no _  = x ∷ ys

ins⁺ : ∀ {z} x ys → (z ≡ x) ⊎ (z ∈L ys) → z ∈L ins x ys
ins⁺ x ys h with mem? x ys
ins⁺ x ys (inj₁ refl) | yes m = m
ins⁺ x ys (inj₂ k)    | yes _ = k
ins⁺ x ys (inj₁ refl) | no _  = here
ins⁺ x ys (inj₂ k)    | no _  = there k

ins⁻ : ∀ {z} x ys → z ∈L ins x ys → (z ≡ x) ⊎ (z ∈L ys)
ins⁻ x ys k with mem? x ys
ins⁻ x ys k         | yes _ = inj₂ k
ins⁻ x ys here      | no _  = inj₁ refl
ins⁻ x ys (there k) | no _  = inj₂ k

dedup : List A → List A
dedup []       = []
dedup (x ∷ xs) = ins x (dedup xs)

dedup⁺ : ∀ {z} xs → z ∈L xs → z ∈L dedup xs
dedup⁺ (x ∷ xs) here      = ins⁺ x (dedup xs) (inj₁ refl)
dedup⁺ (x ∷ xs) (there k) = ins⁺ x (dedup xs) (inj₂ (dedup⁺ xs k))

dedup⁻ : ∀ {z} xs → z ∈L dedup xs → z ∈L xs
dedup⁻ (x ∷ xs) k with ins⁻ x (dedup xs) k
... | inj₁ refl = here
... | inj₂ k′   = there (dedup⁻ xs k′)

-- Snoc-form bounded paths: WithinR p k x when x is reachable from p in
-- at most k steps.
data WithinR (p : A) : Nat → A → Set where
  base : ∀ {k} → WithinR p k p
  snoc : ∀ {k y z} → WithinR p k y → z ∈L next y → WithinR p (suc k) z

prependR : ∀ {k x′ x z} → x ∈L next x′ → WithinR x k z → WithinR x′ (suc k) z
prependR m base        = snoc base m
prependR m (snoc w m′) = snoc (prependR m w) m′

within→R : ∀ {k x z} → Within k x z → WithinR x k z
within→R now         = base
within→R (later m w) = prependR m (within→R w)

R→star : ∀ {k x z} → WithinR x k z → Star x z
R→star base       = ε
R→star (snoc w m) = R→star w ◅◅ (m ◅ ε)

step-all : List A → List A
step-all S = concatK (mapK next S)

grow : List A → List A
grow S = dedup (S ++ step-all S)

grow-keep : ∀ {z} S → z ∈L S → z ∈L grow S
grow-keep S m = dedup⁺ (S ++ step-all S) (∈-++ˡ (step-all S) m)

grow-step : ∀ {y z} S → y ∈L S → z ∈L next y → z ∈L grow S
grow-step S my mz =
  dedup⁺ (S ++ step-all S) (∈-++ʳ S (∈-concat⁺ (mapK next S) mz (∈-map⁺ next my)))

grow⁻ : ∀ {z} S → z ∈L grow S → (z ∈L S) ⊎ (Σ A λ y → (y ∈L S) × (z ∈L next y))
grow⁻ S k with ∈-++⁻ S (dedup⁻ (S ++ step-all S) k)
... | inj₁ m = inj₁ m
... | inj₂ m with ∈-concat⁻ (mapK next S) m
...   | ys , mz , mys with ∈-map⁻ next S mys
...     | y , my , refl = inj₂ (y , my , mz)

closedB : List A → Bool
closedB S = all (λ x → all (λ y → isYes (mem? y S)) (next x)) S

private
  all-elim : ∀ {B : Set} (f : B → Bool) xs {x} → T (all f xs) → x ∈L xs → T (f x)
  all-elim f (x ∷ xs) t here      = ∧-fst t
  all-elim f (x ∷ xs) t (there m) = all-elim f xs (∧-snd {f x} t) m

closedB-sound : ∀ S → T (closedB S) → ∀ {x y} → x ∈L S → y ∈L next x → y ∈L S
closedB-sound S t mx my =
  isYes-sound (mem? _ S)
    (all-elim (λ y → isYes (mem? y S)) _ (all-elim _ S t mx) my)

close : Nat → List A → List A
close zero    S = S
close (suc f) S = if closedB S then S else close f (grow S)

reachSet : Nat → A → List A
reachSet fuel p = close fuel (p ∷ [])

-- Soundness: everything collected is reachable.
close-sound : ∀ {p} f S → (∀ {x} → x ∈L S → Star p x) → ∀ {x} → x ∈L close f S → Star p x
close-sound zero    S h m = h m
close-sound (suc f) S h m with closedB S
... | true  = h m
... | false = close-sound f (grow S) h′ m
  where
  h′ : ∀ {x} → x ∈L grow S → Star _ x
  h′ k with grow⁻ S k
  ... | inj₁ m′ = h m′
  ... | inj₂ (y , my , mz) = h my ◅◅ (mz ◅ ε)

reachSet-sound : ∀ fuel p {x} → x ∈L reachSet fuel p → Star p x
reachSet-sound fuel p = close-sound fuel (p ∷ []) λ { here → ε ; (there ()) }

-- Completeness, invariant form: either the result is closed and holds
-- p, or it holds every vertex within k + f steps.
private
  closed-holds : ∀ {S p} → (∀ {x y} → x ∈L S → y ∈L next x → y ∈L S) →
                 p ∈L S → ∀ {x} → Star p x → x ∈L S
  closed-holds c mp ε       = mp
  closed-holds c mp (m ◅ s) = closed-holds c (c mp m) s

  plus-suc : ∀ k f → k + suc f ≡ suc (k + f)
  plus-suc zero    f = refl
  plus-suc (suc k) f = cong suc (plus-suc k f)

  plus-zero : ∀ k → k + zero ≡ k
  plus-zero zero    = refl
  plus-zero (suc k) = cong suc (plus-zero k)

  close-complete : ∀ {p} f k S → p ∈L S → (∀ {x} → WithinR p k x → x ∈L S) →
                   ∀ {x} → Star p x → (WithinR p (k + f) x) → x ∈L close f S
  close-complete {p} zero k S mp inv {x} s w = inv (subst (λ n → WithinR p n x) (plus-zero k) w)
  close-complete {p} (suc f) k S mp inv {x} s w with closedB S | closedB-sound S
  ... | true  | c = closed-holds (c tt) mp s
  ... | false | _ =
        close-complete f (suc k) (grow S) (grow-keep S mp) inv′ s
          (subst (λ n → WithinR p n x) (plus-suc k f) w)
    where
    inv′ : ∀ {x} → WithinR _ (suc k) x → x ∈L grow S
    inv′ base       = grow-keep S mp
    inv′ (snoc w m) = grow-step S (inv w) m

module Saturate (U : List A)
                (closed : ∀ {x y} → x ∈L U → y ∈L next x → y ∈L U) where
  open Universe U closed

  reachSet-complete : ∀ {p x} → p ∈L U → Star p x → x ∈L reachSet (lengthL U) p
  reachSet-complete {p} mp s =
    close-complete (lengthL U) 0 (p ∷ []) here
      (λ { base → here }) s (within→R (bounded mp s))
