------------------------------------------------------------------------
-- Finiteness and the generator count (2) of the source-only joining
-- completion (r7 §1, "Termination and order independence").
--
-- If V and every E a b are finite (enumerated without repetition), V
-- has decidable equality and E is acyclic, then every type of inner
-- paths Path E u t is finite (enumPath). So the joining generators
--
--   JAll = Σ (seed α : s → t) . Σ u . Path E u t
--
-- (exactly the indices of Completion.jn) are finite once the seeds
-- are, and their number is
--
--   (2)  |J| = Σ_α #(inner paths ending at t α)          (count-J)
--
-- The number does not depend on how the generators are listed:
-- any two repetition-free enumerations of a type have the same length
-- (count-unique). In type theory the completion is a definition, not
-- the result of a saturation run, which is the order independence of
-- r7 in its strongest form.
--
-- The acyclicity bound uses a pigeonhole argument (pigeon): a path
-- visits pairwise distinct vertices, so it has fewer arrows than V has
-- vertices.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver

module CaTTExp.Join.Finite where

------------------------------------------------------------------------
-- Lists, membership, repetition-free enumerations.

infix 4 _∈L_
data _∈L_ {A : Set} (a : A) : List A → Set where
  here  : ∀ {xs} → a ∈L (a ∷ xs)
  there : ∀ {x xs} → a ∈L xs → a ∈L (x ∷ xs)

data NoDup {A : Set} : List A → Set where
  []  : NoDup []
  _∷_ : ∀ {x xs} → ¬ (x ∈L xs) → NoDup xs → NoDup (x ∷ xs)

record Enum (A : Set) : Set where
  constructor enum
  field
    elems : List A
    has   : ∀ a → a ∈L elems
    nodup : NoDup elems
open Enum public

lengthL : ∀ {A : Set} → List A → Nat
lengthL []       = 0
lengthL (_ ∷ xs) = suc (lengthL xs)

sumL : List Nat → Nat
sumL []       = 0
sumL (n ∷ ns) = n + sumL ns

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n     z≤n     = refl
≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

≤-step : ∀ {m n} → suc m ≤ n → m ≤ n
≤-step (s≤s z≤n)     = z≤n
≤-step (s≤s (s≤s p)) = s≤s (≤-step (s≤s p))

private
  ∈-++ˡ : ∀ {A : Set} {z : A} {xs} ys → z ∈L xs → z ∈L (xs ++ ys)
  ∈-++ˡ ys here      = here
  ∈-++ˡ ys (there m) = there (∈-++ˡ ys m)

  ∈-++ʳ : ∀ {A : Set} {z : A} xs {ys} → z ∈L ys → z ∈L (xs ++ ys)
  ∈-++ʳ []       m = m
  ∈-++ʳ (x ∷ xs) m = there (∈-++ʳ xs m)

  ∈-++⁻ : ∀ {A : Set} {z : A} xs {ys} → z ∈L (xs ++ ys) → (z ∈L xs) ⊎ (z ∈L ys)
  ∈-++⁻ []       m         = inj₂ m
  ∈-++⁻ (x ∷ xs) here      = inj₁ here
  ∈-++⁻ (x ∷ xs) (there m) with ∈-++⁻ xs m
  ... | inj₁ m′ = inj₁ (there m′)
  ... | inj₂ m′ = inj₂ m′

  ∈-map⁺ : ∀ {A B : Set} (f : A → B) {x xs} → x ∈L xs → f x ∈L mapL f xs
  ∈-map⁺ f here      = here
  ∈-map⁺ f (there m) = there (∈-map⁺ f m)

  ∈-map⁻ : ∀ {A B : Set} (f : A → B) {y} xs → y ∈L mapL f xs →
           Σ A λ x → (x ∈L xs) × (f x ≡ y)
  ∈-map⁻ f (x ∷ xs) here      = x , here , refl
  ∈-map⁻ f (x ∷ xs) (there m) with ∈-map⁻ f xs m
  ... | x′ , m′ , eq = x′ , there m′ , eq

  nodup-++ : ∀ {A : Set} {xs ys : List A} → NoDup xs → NoDup ys →
             (∀ {z} → z ∈L xs → z ∈L ys → ⊥) → NoDup (xs ++ ys)
  nodup-++ []         ny d = ny
  nodup-++ {xs = x ∷ xs} (nx ∷ nd) ny d = out ∷ nodup-++ nd ny (λ m → d (there m))
    where
    out : ¬ (x ∈L (xs ++ _))
    out m with ∈-++⁻ xs m
    ... | inj₁ m′ = nx m′
    ... | inj₂ m′ = d here m′

  nodup-map : ∀ {A B : Set} (f : A → B) → (∀ {x y} → f x ≡ f y → x ≡ y) →
              ∀ {xs} → NoDup xs → NoDup (mapL f xs)
  nodup-map f inj []                    = []
  nodup-map f inj {x ∷ xs} (nx ∷ nd) = out ∷ nodup-map f inj nd
    where
    out : ¬ (f x ∈L mapL f xs)
    out m with ∈-map⁻ f xs m
    ... | x′ , m′ , eq = nx (subst (_∈L xs) (inj eq) m′)

  length-++ : ∀ {A : Set} (xs ys : List A) → lengthL (xs ++ ys) ≡ lengthL xs + lengthL ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  length-map : ∀ {A B : Set} (f : A → B) xs → lengthL (mapL f xs) ≡ lengthL xs
  length-map f []       = refl
  length-map f (x ∷ xs) = cong suc (length-map f xs)

------------------------------------------------------------------------
-- Pigeonhole: a repetition-free list inside L is no longer than L.

private
  removeAt : ∀ {A : Set} {x : A} {L} → x ∈L L → List A
  removeAt {L = _ ∷ L} here      = L
  removeAt {L = y ∷ L} (there m) = y ∷ removeAt m

  remove-len : ∀ {A : Set} {x : A} {L} (m : x ∈L L) → lengthL L ≡ suc (lengthL (removeAt m))
  remove-len here      = refl
  remove-len (there m) = cong suc (remove-len m)

  remove-keep : ∀ {A : Set} {x y : A} {L} (m : x ∈L L) → y ∈L L → ¬ (y ≡ x) →
                y ∈L removeAt m
  remove-keep here      here       ne = ⊥-elim (ne refl)
  remove-keep here      (there my) ne = my
  remove-keep (there m) here       ne = here
  remove-keep (there m) (there my) ne = there (remove-keep m my ne)

pigeon : ∀ {A : Set} {xs L : List A} → NoDup xs → (∀ {z} → z ∈L xs → z ∈L L) →
         lengthL xs ≤ lengthL L
pigeon [] sub = z≤n
pigeon {xs = x ∷ xs} {L} (nx ∷ nd) sub =
  subst (suc (lengthL xs) ≤_) (sym (remove-len m))
    (s≤s (pigeon nd (λ {z} mz → remove-keep m (sub (there mz))
                                  (λ eq → nx (subst (_∈L xs) eq mz)))))
  where m = sub here

-- The size of a finite type does not depend on its enumeration.
count-unique : ∀ {A : Set} (e₁ e₂ : Enum A) → lengthL (elems e₁) ≡ lengthL (elems e₂)
count-unique e₁ e₂ =
  ≤-antisym (pigeon (nodup e₁) (λ {z} _ → has e₂ z))
            (pigeon (nodup e₂) (λ {z} _ → has e₁ z))

------------------------------------------------------------------------
-- Enumerations of the type formers we need.

Enum-⊥ : Enum ⊥
Enum-⊥ = enum [] (λ ()) []

Enum-≡ : ∀ {A : Set} {a b : A} → Dec (a ≡ b) → Enum (a ≡ b)
Enum-≡ (yes refl) = enum (refl ∷ []) (λ { refl → here }) ((λ ()) ∷ [])
Enum-≡ (no ne)    = enum [] (λ eq → ⊥-elim (ne eq)) []

Enum-⊎ : ∀ {A B : Set} → Enum A → Enum B → Enum (A ⊎ B)
Enum-⊎ (enum xs hx nx) (enum ys hy ny) =
  enum (mapL inj₁ xs ++ mapL inj₂ ys) has′
       (nodup-++ (nodup-map inj₁ i₁ nx) (nodup-map inj₂ i₂ ny) disj)
  where
  has′ : ∀ z → z ∈L (mapL inj₁ xs ++ mapL inj₂ ys)
  has′ (inj₁ a) = ∈-++ˡ _ (∈-map⁺ inj₁ (hx a))
  has′ (inj₂ b) = ∈-++ʳ (mapL inj₁ xs) (∈-map⁺ inj₂ (hy b))
  i₁ : ∀ {x y} → _≡_ {A = _ ⊎ _} (inj₁ x) (inj₁ y) → x ≡ y
  i₁ refl = refl
  i₂ : ∀ {x y} → _≡_ {A = _ ⊎ _} (inj₂ x) (inj₂ y) → x ≡ y
  i₂ refl = refl
  disj : ∀ {z} → z ∈L mapL inj₁ xs → z ∈L mapL inj₂ ys → ⊥
  disj m m′ with ∈-map⁻ inj₁ xs m | ∈-map⁻ inj₂ ys m′
  ... | _ , _ , refl | _ , _ , ()

module _ {A : Set} {B : A → Set} where

  private
    cm : List A → (∀ a → Enum (B a)) → List (Σ A B)
    cm []       eB = []
    cm (a ∷ as) eB = mapL (a ,_) (elems (eB a)) ++ cm as eB

    cm-fst : ∀ {z} as eB → z ∈L cm as eB → fst z ∈L as
    cm-fst (a ∷ as) eB m with ∈-++⁻ (mapL (a ,_) (elems (eB a))) m
    ... | inj₁ m′ with ∈-map⁻ (a ,_) _ m′
    ...   | _ , _ , refl = here
    cm-fst (a ∷ as) eB m | inj₂ m′ = there (cm-fst as eB m′)

    cm-has : ∀ {a} {b : B a} {as} eB → a ∈L as → (a , b) ∈L cm as eB
    cm-has {b = b} eB (here {xs = as}) =
      ∈-++ˡ (cm as eB) (∈-map⁺ (_ ,_) (has (eB _) b))
    cm-has eB (there {x = x} m) = ∈-++ʳ (mapL (x ,_) (elems (eB x))) (cm-has eB m)

    pair-inj : ∀ {a} {b b′ : B a} → _≡_ {A = Σ A B} (a , b) (a , b′) → b ≡ b′
    pair-inj refl = refl

    cm-nodup : ∀ {as} eB → NoDup as → NoDup (cm as eB)
    cm-nodup eB []                     = []
    cm-nodup {a ∷ as} eB (na ∷ nd) =
      nodup-++ (nodup-map (a ,_) pair-inj (nodup (eB a))) (cm-nodup eB nd) disj
      where
      disj : ∀ {z} → z ∈L mapL (a ,_) (elems (eB a)) → z ∈L cm as eB → ⊥
      disj m m′ with ∈-map⁻ (a ,_) _ m
      ... | _ , _ , refl = na (cm-fst as eB m′)

    cm-len : ∀ as eB → lengthL (cm as eB) ≡ sumL (mapL (λ a → lengthL (elems (eB a))) as)
    cm-len []       eB = refl
    cm-len (a ∷ as) eB =
      trans (length-++ (mapL (a ,_) (elems (eB a))) (cm as eB))
            (cong₂ _+_ (length-map (a ,_) (elems (eB a))) (cm-len as eB))

  Enum-Σ : Enum A → (∀ a → Enum (B a)) → Enum (Σ A B)
  Enum-Σ eA eB = enum (cm (elems eA) eB)
                      (λ { (a , b) → cm-has eB (has eA a) })
                      (cm-nodup eB (nodup eA))

  -- The size of a Σ is the sum of the sizes of its fibres.
  Enum-Σ-count : ∀ (eA : Enum A) (eB : ∀ a → Enum (B a)) →
                 lengthL (elems (Enum-Σ eA eB)) ≡
                 sumL (mapL (λ a → lengthL (elems (eB a))) (elems eA))
  Enum-Σ-count eA eB = cm-len (elems eA) eB

-- Transport along an isomorphism.
Enum-iso : ∀ {A B : Set} (to : A → B) (from : B → A) →
           (∀ a → from (to a) ≡ a) → (∀ b → to (from b) ≡ b) → Enum A → Enum B
Enum-iso to from ft tf (enum xs hx nx) =
  enum (mapL to xs)
       (λ b → subst (_∈L mapL to xs) (tf b) (∈-map⁺ to (hx (from b))))
       (nodup-map to (λ {x} {y} eq → trans (sym (ft x)) (trans (cong from eq) (ft y))) nx)

------------------------------------------------------------------------
-- Inner paths in a finite acyclic quiver are finite.

module Paths {V : Set} (E : V → V → Set)
             (decV : (a b : V) → Dec (a ≡ b))
             (eV : Enum V)
             (eE : ∀ a b → Enum (E a b))
             (acyc : ∀ {a} (p : Path E a a) → p ≡ []) where

  open Acyclic E acyc using (back-V)

  N : Nat
  N = lengthL (elems eV)

  verts : ∀ {u t} → Path E u t → List V
  verts {u} []      = u ∷ []
  verts {u} (e ∷ p) = u ∷ verts p

  private
    verts-len : ∀ {u t} (p : Path E u t) → lengthL (verts p) ≡ suc (len p)
    verts-len []      = refl
    verts-len (e ∷ p) = cong suc (verts-len p)

    verts-∈V : ∀ {x u t} (p : Path E u t) → x ∈L verts p → x ∈V p
    verts-∈V []      here      = src
    verts-∈V []      (there ())
    verts-∈V (e ∷ p) here      = src
    verts-∈V (e ∷ p) (there m) = next (verts-∈V p m)

    verts-nodup : ∀ {u t} (p : Path E u t) → NoDup (verts p)
    verts-nodup []      = (λ ()) ∷ []
    verts-nodup (e ∷ p) = (λ m → back-V e (verts-∈V p m)) ∷ verts-nodup p

  -- Pigeonhole: a path has fewer arrows than there are vertices.
  bound : ∀ {u t} (p : Path E u t) → len p ≤ N
  bound p = ≤-step (subst (_≤ N) (verts-len p)
                      (pigeon (verts-nodup p) (λ {z} _ → has eV z)))

  -- Paths of length at most n, as a finite type.
  IPL : Nat → V → V → Set
  IPL zero    u t = u ≡ t
  IPL (suc n) u t = (u ≡ t) ⊎ Σ V λ c → Σ (E u c) λ _ → IPL n c t

  enumIPL : ∀ n u t → Enum (IPL n u t)
  enumIPL zero    u t = Enum-≡ (decV u t)
  enumIPL (suc n) u t =
    Enum-⊎ (Enum-≡ (decV u t))
           (Enum-Σ eV (λ c → Enum-Σ (eE u c) (λ _ → enumIPL n c t)))

  private
    to : ∀ n {u t} (p : Path E u t) → len p ≤ n → IPL n u t
    to zero    []      _       = refl
    to (suc n) []      _       = inj₁ refl
    to (suc n) (e ∷ p) (s≤s h) = inj₂ (_ , e , to n p h)

    from : ∀ n {u t} → IPL n u t → Path E u t
    from zero    refl                = []
    from (suc n) (inj₁ refl)         = []
    from (suc n) (inj₂ (c , e , r))  = e ∷ from n r

    from-to : ∀ n {u t} (p : Path E u t) (h : len p ≤ n) → from n (to n p h) ≡ p
    from-to zero    []      _       = refl
    from-to (suc n) []      _       = refl
    from-to (suc n) (e ∷ p) (s≤s h) = cong (e ∷_) (from-to n p h)

    to-from : ∀ n {u t} (c : IPL n u t) (h : len (from n c) ≤ n) → to n (from n c) h ≡ c
    to-from zero    refl               _       = refl
    to-from (suc n) (inj₁ refl)        _       = refl
    to-from (suc n) (inj₂ (c , e , r)) (s≤s h) =
      cong (λ z → inj₂ (c , e , z)) (to-from n r h)

  enumPath : ∀ u t → Enum (Path E u t)
  enumPath u t =
    Enum-iso (from N) (λ p → to N p (bound p))
             (λ c → to-from N c (bound (from N c)))
             (λ p → from-to N p (bound p))
             (enumIPL N u t)

  -- Inner paths ending at t, from any vertex.
  PathsTo : V → Set
  PathsTo t = Σ V λ u → Path E u t

  enumPathsTo : ∀ t → Enum (PathsTo t)
  enumPathsTo t = Enum-Σ eV (λ u → enumPath u t)

  ----------------------------------------------------------------------
  -- The joining generators and the count (2).

  module Count (P : V → V → Set)
               (eP : Enum (Σ V λ s → Σ V λ t → P s t)) where

    Seed : Set
    Seed = Σ V λ s → Σ V λ t → P s t

    tgt : Seed → V
    tgt (_ , t , _) = t

    -- The index set of Completion.jn: a seed α and a path R into t α.
    JAll : Set
    JAll = Σ Seed λ α → PathsTo (tgt α)

    enumJ : Enum JAll
    enumJ = Enum-Σ eP (λ α → enumPathsTo (tgt α))

    count-J : lengthL (elems enumJ) ≡
              sumL (mapL (λ α → lengthL (elems (enumPathsTo (tgt α)))) (elems eP))
    count-J = Enum-Σ-count eP (λ α → enumPathsTo (tgt α))

    -- Every enumeration of the generators has this size.
    count-J-any : (e : Enum JAll) → lengthL (elems e) ≡
                  sumL (mapL (λ α → lengthL (elems (enumPathsTo (tgt α)))) (elems eP))
    count-J-any e = trans (count-unique e enumJ) count-J
