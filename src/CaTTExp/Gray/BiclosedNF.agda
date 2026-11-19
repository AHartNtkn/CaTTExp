------------------------------------------------------------------------
-- D11: the N / β / η rewriting system for 1-cells of the free
-- Gray-monoidal biclosed 2-category 𝒢 (reading I), after
-- notes/conjectures/answered/gray-biclosed-coherence-2026-11-19.md,
-- Followup 2 §1.  Executable encoding: syntax, the one-step reducts
-- of a word (all three rules, at every position and inside curry
-- bodies), and a bounded exhaustive search for normal forms.
--
-- What is checked here (by evaluation, `tt`):
--   * each row of the critical-pair table of §1.4 on a concrete
--     instance, with genuinely overlapping redexes, including mixed
--     left/right tags: every reduction order reaches one normal form;
--   * terms exported from scripts/d11/nbe_rewrite.py (BiclosedNFData).
-- The general confluence and termination proofs are on paper (§1.3,
-- §1.4); this module does not formalise them.
------------------------------------------------------------------------
module CaTTExp.Gray.BiclosedNF where

open import CaTTExp.Prelude

data Dir : Set where
  Ld Rd : Dir

mutual
  -- A formula is a nonempty-in-practice word of factors.
  data Factor : Set where
    atom : Nat → Factor
    lres : List Factor → List Factor → Factor   -- lres A Z = A \ Z
    rres : List Factor → List Factor → Factor   -- rres Z A = Z / A

Formula : Set
Formula = List Factor

mutual
  data Prim : Set where
    gen : Nat → Formula → Formula → Prim                    -- name, src, tgt
    ev  : Dir → Formula → Formula → Prim                    -- e_{(d,A),Z}
    cur : Dir → Formula → Formula → Formula → List Triple → Prim
                                                            -- κ_{(d,A)} with Z, X, body
  data Triple : Set where
    tri : Formula → Prim → Formula → Triple                 -- (L, q, R)

Word : Set
Word = List Triple

------------------------------------------------------------------------
-- Decidable equality

eqDir : Dir → Dir → Bool
eqDir Ld Ld = true
eqDir Rd Rd = true
eqDir _  _  = false

mutual
  eqFa : Factor → Factor → Bool
  eqFa (atom m)   (atom n)   = m ==ℕ n
  eqFa (lres A Z) (lres B W) = eqFo A B ∧ eqFo Z W
  eqFa (rres Z A) (rres W B) = eqFo Z W ∧ eqFo A B
  eqFa _ _ = false

  eqFo : Formula → Formula → Bool
  eqFo []       []       = true
  eqFo (x ∷ xs) (y ∷ ys) = eqFa x y ∧ eqFo xs ys
  eqFo _ _ = false

mutual
  eqP : Prim → Prim → Bool
  eqP (gen m s t) (gen n s' t') = (m ==ℕ n) ∧ eqFo s s' ∧ eqFo t t'
  eqP (ev d A Z) (ev d' A' Z') = eqDir d d' ∧ eqFo A A' ∧ eqFo Z Z'
  eqP (cur d A Z X b) (cur d' A' Z' X' b') =
    eqDir d d' ∧ eqFo A A' ∧ eqFo Z Z' ∧ eqFo X X' ∧ eqW b b'
  eqP _ _ = false

  eqT : Triple → Triple → Bool
  eqT (tri l q r) (tri l' q' r') = eqFo l l' ∧ eqP q q' ∧ eqFo r r'

  eqW : Word → Word → Bool
  eqW []       []       = true
  eqW (x ∷ xs) (y ∷ ys) = eqT x y ∧ eqW xs ys
  eqW _ _ = false

------------------------------------------------------------------------
-- List helpers

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

rev : ∀ {A : Set} → List A → List A
rev = go []
  where
    go : ∀ {A : Set} → List A → List A → List A
    go acc []       = acc
    go acc (x ∷ xs) = go (x ∷ acc) xs

dropPrefix : Formula → Formula → Maybe Formula
dropPrefix []       ys       = just ys
dropPrefix (x ∷ xs) []       = nothing
dropPrefix (x ∷ xs) (y ∷ ys) = if eqFa x y then dropPrefix xs ys else nothing

dropSuffix : Formula → Formula → Maybe Formula
dropSuffix xs ys = dropPrefix (rev xs) (rev ys) >>= λ r → just (rev r)

nonempty : ∀ {A : Set} → List A → Bool
nonempty []      = false
nonempty (_ ∷ _) = true

------------------------------------------------------------------------
-- Tags, contexts, sources

Tf : Dir → Formula → Formula → Formula        -- T_a X
Tf Ld A X = A ++ X
Tf Rd A X = X ++ A

Hf : Dir → Formula → Formula → Formula        -- H_a Z
Hf Ld A Z = lres A Z ∷ []
Hf Rd A Z = rres Z A ∷ []

srcP : Prim → Formula
srcP (gen _ s _)       = s
srcP (ev d A Z)        = Tf d A (Hf d A Z)
srcP (cur _ _ _ X _)   = X

wrap : Dir → Formula → Triple → Triple        -- T_a[t]
wrap Ld A (tri l q r) = tri (A ++ l) q r
wrap Rd A (tri l q r) = tri l q (r ++ A)

strip : Dir → Formula → Triple → Maybe Triple
strip Ld A (tri l q r) = dropPrefix A l >>= λ l' → just (tri l' q r)
strip Rd A (tri l q r) = dropSuffix A r >>= λ r' → just (tri l q r')

stripAll : Dir → Formula → Word → Maybe Word
stripAll d A []       = just []
stripAll d A (t ∷ ts) = strip d A t >>= λ t' → stripAll d A ts >>= λ ts' → just (t' ∷ ts')

inCtx : Formula → Formula → Triple → Triple   -- C[t]
inCtx CL CR (tri l q r) = tri (CL ++ l) q (r ++ CR)

------------------------------------------------------------------------
-- The three rules at the head of a word

-- η at a single curry triple: κ_a(T_a[g] ; e_a) ⟶ g
etaAt : Triple → Maybe Word
etaAt (tri CL (cur d A Z X body) CR) = go (rev body)
  where
    go : Word → Maybe Word
    go (tri [] (ev d' A' Z') [] ∷ rest) =
      guard (eqDir d d' ∧ eqFo A A' ∧ eqFo Z Z') λ _ →
        stripAll d A (rev rest) >>= λ g → just (mapL (inCtx CL CR) g)
    go _ = nothing
etaAt _ = nothing

-- N on two adjacent triples: D[g] ; C[κ_a(f)] ⟶ C[κ_a(T_a[D₀[g]] ; f)]
nAt : Triple → Triple → Maybe Triple
nAt (tri DL q DR) (tri CL (cur d A Z X body) CR) =
  dropPrefix CL DL >>= λ D0L →
  dropSuffix CR DR >>= λ D0R →
  let g = tri D0L q D0R
      Xn = D0L ++ srcP q ++ D0R
  in guard (nonempty Xn) λ _ → just (tri CL (cur d A Z Xn (wrap d A g ∷ body)) CR)
nAt _ _ = nothing

-- β on two adjacent triples: C[T_a[κ_a(f)]] ; C[e_a] ⟶ C[f]
betaAt : Triple → Triple → Maybe Word
betaAt (tri l (cur d A Z X body) r) (tri CL (ev d' A' Z') CR) =
  guard (eqDir d d' ∧ eqFo A A' ∧ eqFo Z Z' ∧ ctxOK d) λ _ →
    just (mapL (inCtx CL CR) body)
  where
    ctxOK : Dir → Bool
    ctxOK Ld = eqFo l (CL ++ A) ∧ eqFo r CR
    ctxOK Rd = eqFo l CL ∧ eqFo r (A ++ CR)
betaAt _ _ = nothing

maybeL : ∀ {A : Set} → Maybe A → List A
maybeL nothing  = []
maybeL (just x) = x ∷ []

------------------------------------------------------------------------
-- All one-step reducts

mutual
  reducts : Word → List Word
  reducts []       = []
  reducts (t ∷ ws) =
       mapL (λ w → w ++ ws) (maybeL (etaAt t))
    ++ pairs t ws
    ++ inside t ws
    ++ mapL (λ w → t ∷ w) (reducts ws)

  pairs : Triple → Word → List Word
  pairs t []        = []
  pairs t (u ∷ ws)  =
       mapL (λ v → v ∷ ws) (maybeL (nAt t u))
    ++ mapL (λ w → w ++ ws) (maybeL (betaAt t u))

  inside : Triple → Word → List Word
  inside (tri l (cur d A Z X body) r) ws =
    mapL (λ b → tri l (cur d A Z X b) r ∷ ws) (reducts body)
  inside _ ws = []

------------------------------------------------------------------------
-- Bounded exhaustive search: every normal form reachable within the
-- fuel.  `stuck` reports whether the fuel ran out.

mutual
  nfs : Nat → Word → List Word × Bool
  nfs zero    w = (w ∷ []) , not (nonempty (reducts w))
  nfs (suc n) w = go (reducts w)
    where
      go : List Word → List Word × Bool
      go []       = (w ∷ []) , true
      go (r ∷ rs) = nfsAll n (r ∷ rs)

  nfsAll : Nat → List Word → List Word × Bool
  nfsAll n []       = [] , true
  nfsAll n (r ∷ rs) with nfs n r | nfsAll n rs
  ... | a , ok | b , ok' = (a ++ b) , (ok ∧ ok')

allSame : List Word → Bool
allSame []       = true
allSame (w ∷ ws) = all (eqW w) ws

-- Confluent on w within the fuel: the search finished and found one
-- normal form.
confluentOn : Nat → Word → Bool
confluentOn n w with nfs n w
... | ws , finished = finished ∧ allSame ws

-- At least two redex occurrences: the term contains an overlap.  (In
-- some rows of the table the two reducts coincide syntactically, as in
-- the β/η shared-curry row.)
overlapping : Word → Bool
overlapping w = go (reducts w)
  where
    go : List Word → Bool
    go (_ ∷ _ ∷ _) = true
    go _           = false
