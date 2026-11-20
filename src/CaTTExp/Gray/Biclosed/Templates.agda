------------------------------------------------------------------------
-- D7d: the rows, the generic contexts of (GB-cut) and (GB-dcut), and
-- the admissibility judgement of notes/closed-structure.md F.7.4.
--
-- Main results (no postulates):
--   * admit? decides Admissible (admit?-sound, admit?-complete);
--   * no-reverse: a directed goal and its reverse are never both
--     admissible (the judgement is not endpoint-symmetric, r3 item 29);
--   * dir-needs-dir: an admissible directed goal has a directed
--     hypothesis in its context, so a context with no directed
--     hypothesis admits no directed cell.
--
-- Layout of the generic context of a template (row ρ, gap g, mode m,
-- dimension n).  Level j < n is a block of six entries at 6j … 6j+5:
--   u⁻_j, u⁺_j  : the (n−1)-sphere u of operations of type H
--   β⁻_j, β⁺_j  : the boundary sphere of the ball b in B
--   a⁻_j, a⁺_j  : the collar r(u±_j) ≅ (β±_j with lower collars adjoined)
-- followed by the ball b itself at position 6n.  With m = inv this is
-- Ctx(ρ, n) of (GB-cut); with m = dir and n = k ≥ 1 it is the context
-- of (GB-dcut) (u⁻, u⁺ are u±_{k−1}, the lower u's are their common
-- boundary, and the lower collars are the comparisons on it).
-- Goals: c = the n-cell of type H with boundary u (cgoal), and
-- ε = the invertible cell r(c) ≅ b with the collar adjoined (egoal).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Templates where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import Agda.Builtin.Nat using (_*_)

------------------------------------------------------------------------
-- Rows (F.7.4 §2 table)

data Row : Set where
  pairR  : List Fm → Fm → Fm → List Fm → Fm → Row        -- L U V R Z
  probeR : List Fm → Shape → Shape → List Fm → Fm → Row  -- L Δ Θ R Z
  unitR  : List Fm → List Fm → Fm → Row                  -- L R Z
  evLR   : List Fm → Fm → Fm → Row                       -- Φ A C
  evRR   : List Fm → Fm → Fm → Row                       -- Φ A C

-- H: type of the missing vertex
H : Row → MTy
H (pairR L U V R Z)  = (L ++ (U ⊗ V) ∷ R) ▸ Z
H (probeR L Δ Θ R Z) = (L ++ rep (Δ ⊠ Θ) ∷ R) ▸ Z
H (unitR L R Z)      = (L ++ rep (disk 0) ∷ R) ▸ Z
H (evLR Φ A C)       = Φ ▸ (A \\ C)
H (evRR Φ A C)       = Φ ▸ (C // A)

-- B: type of the outer operation
B : Row → MTy
B (pairR L U V R Z)  = (L ++ U ∷ V ∷ R) ▸ Z
B (probeR L Δ Θ R Z) = (L ++ rep Δ ∷ rep Θ ∷ R) ▸ Z
B (unitR L R Z)      = (L ++ R) ▸ Z
B (evLR Φ A C)       = (A ∷ Φ) ▸ C
B (evRR Φ A C)       = (Φ ++ A ∷ []) ▸ C

ids : List Fm → List Tm
ids = map idt

idTys : List Fm → List MTy
idTys = map (λ A → (A ∷ []) ▸ A)

-- r : H → B, pasting the distinguished vertex
rmap : Row → Tm → Tm
rmap (pairR L U V R Z)  x = comp x (ids L ++ mP U V ∷ ids R)
rmap (probeR L Δ Θ R Z) x = comp x (ids L ++ pP Δ Θ ∷ ids R)
rmap (unitR L R Z)      x = comp x (ids L ++ pt ∷ ids R)
rmap (evLR Φ A C)       x = comp (eL A C) (idt A ∷ x ∷ [])
rmap (evRR Φ A C)       x = comp (eR A C) (x ∷ idt A ∷ [])

-- the image of a time-slot gap under r (as computed by whiskering)
rgap : Row → Nat → Nat
rgap (pairR L U V R Z)  g = sumIns (take g (idTys L ++ ((U ∷ V ∷ []) ▸ (U ⊗ V)) ∷ idTys R))
rgap (probeR L Δ Θ R Z) g = sumIns (take g (idTys L ++ ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) ∷ idTys R))
rgap (unitR L R Z)      g = sumIns (take g (idTys L ++ ([] ▸ rep (disk 0)) ∷ idTys R))
rgap (evLR Φ A C)       g = 1 + g
rgap (evRR Φ A C)       g = g

-- generic templates use fresh object variables, numbered in order of
-- appearance in the outer profile B; the output is an object variable
fmsOf : Row → List Fm
fmsOf (pairR L U V R Z)  = L ++ U ∷ V ∷ R ++ Z ∷ []
fmsOf (probeR L _ _ R Z) = L ++ R ++ Z ∷ []
fmsOf (unitR L R Z)      = L ++ R ++ Z ∷ []
fmsOf (evLR Φ A C)       = A ∷ Φ ++ C ∷ []
fmsOf (evRR Φ A C)       = Φ ++ A ∷ C ∷ []

outOf : Row → Fm
outOf (pairR _ _ _ _ Z)  = Z
outOf (probeR _ _ _ _ Z) = Z
outOf (unitR _ _ Z)      = Z
outOf (evLR _ _ C)       = C
outOf (evRR _ _ C)       = C

canonFrom : Nat → List Fm → Bool
canonFrom k []             = true
canonFrom k (obj i ∷ fs)   = (i ==ℕ k) ∧ canonFrom (suc k) fs
canonFrom k (rep _ ∷ fs)   = canonFrom k fs
canonFrom k (_ ∷ _)        = false

isObj : Fm → Bool
isObj (obj _) = true
isObj _       = false

canon : Row → Bool
canon ρ = canonFrom 0 (fmsOf ρ) ∧ isObj (outOf ρ)

------------------------------------------------------------------------
-- Templates

record Tmpl : Set where
  constructor tmpl
  field
    row  : Row
    gap  : Nat
    mode : Mode
    dimn : Nat
open Tmpl public

pos : Nat → Nat → Nat
pos j o = o + j * 6

uM uP bM bP aM aP : Nat → Nat
uM j = pos j 0
uP j = pos j 1
bM j = pos j 2
bP j = pos j 3
aM j = pos j 4
aP j = pos j 5

module _ (t : Tmpl) where
  private
    ρ  = row t
    g  = gap t
    m  = mode t
    g′ = rgap (row t) (gap t)

  tyU : Nat → CTy
  tyU zero    = op (H ρ)
  tyU (suc j) = hom m g (tyU j) (var (uM j)) (var (uP j))

  tyB : Nat → CTy
  tyB zero    = op (B ρ)
  tyB (suc j) = hom m g′ (tyB j) (var (bM j)) (var (bP j))

  tyRU : Nat → CTy
  tyRU zero    = op (B ρ)
  tyRU (suc j) = hom m g′ (tyRU j) (rmap ρ (var (uM j))) (rmap ρ (var (uP j)))

  chain : Nat → Tm → Tm
  chain zero    y = y
  chain (suc j) y = glue (var (aM j)) (chain j y) (var (aP j))

  block : Nat → Ctx
  block j = tyU j ∷ tyU j ∷ tyB j ∷ tyB j
          ∷ hom inv g′ (tyRU j) (rmap ρ (var (uM j))) (chain j (var (bM j)))
          ∷ hom inv g′ (tyRU j) (rmap ρ (var (uP j))) (chain j (var (bP j)))
          ∷ []

  levels : Nat → Ctx
  levels zero    = []
  levels (suc j) = levels j ++ block j

  ctx : Ctx
  ctx = levels (dimn t) ++ (tyB (dimn t) ∷ [])

  cgoal : CTy
  cgoal = tyU (dimn t)

  egoal : CTy
  egoal = hom inv g′ (tyRU (dimn t)) (rmap ρ (here cgoal)) (chain (dimn t) (var (pos (dimn t) 0)))

leq : Nat → Nat → Bool
leq zero    _       = true
leq (suc m) zero    = false
leq (suc m) (suc n) = leq m n

-- side conditions: canonical generic formulas; at n = 0 the template is
-- the invertible one at the rightmost gap; otherwise any gap of H
okT : Tmpl → Bool
okT (tmpl ρ g m zero)    = canon ρ ∧ eqMode m inv ∧ (g ==ℕ length (ins (H ρ)))
okT (tmpl ρ g m (suc n)) = canon ρ ∧ leq g (length (ins (H ρ)))

------------------------------------------------------------------------
-- The admissibility judgement

data Admissible (Γ : Ctx) (A : CTy) : Set where
  adm-c : (t : Tmpl) → T (okT t) → Γ ≡ ctx t → A ≡ cgoal t → Admissible Γ A
  adm-ε : (t : Tmpl) → T (okT t) → Γ ≡ ctx t → A ≡ egoal t → Admissible Γ A

------------------------------------------------------------------------
-- Candidate templates read off a goal

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

outRows : List Fm → Fm → List Row
outRows xs (a \\ c) = evLR xs a c ∷ []
outRows xs (c // a) = evRR xs a c ∷ []
outRows xs _        = []

slotRow : List Fm → Fm → List Fm → Fm → List Row
slotRow pre (u ⊗ v)            post z = pairR pre u v post z ∷ []
slotRow pre (rep (d ⊠ θ))      post z = probeR pre d θ post z ∷ []
slotRow pre (rep (disk zero))  post z = unitR pre post z ∷ []
slotRow pre _                  post z = []

slotRows : List Fm → List Fm → Fm → List Row
slotRows pre []       z = []
slotRows pre (x ∷ xs) z = slotRow pre x xs z ++ slotRows (pre ++ x ∷ []) xs z

rowsOf : MTy → List Row
rowsOf (xs ▸ z) = outRows xs z ++ slotRows [] xs z

gapC : CTy → Nat
gapC (op M)          = length (ins M)
gapC (hom _ g _ _ _) = g

modeC : CTy → Mode
modeC (op _)          = inv
modeC (hom m _ _ _ _) = m

candsC : CTy → List Tmpl
candsC A = map (λ ρ → tmpl ρ (gapC A) (modeC A) (dim A)) (rowsOf (baseM A))

hereOf : Tm → List CTy
hereOf (here A) = A ∷ []
hereOf _        = []

heres : Tm → List CTy
heres (comp f gs) = hereOf f ++ concatMap hereOf gs
heres _           = []

candsE : CTy → List Tmpl
candsE (hom _ _ _ s _) = concatMap candsC (heres s)
candsE (op _)          = []

------------------------------------------------------------------------
-- The decision procedure

anyB : ∀ {A : Set} → (A → Bool) → List A → Bool
anyB p []       = false
anyB p (x ∷ xs) = p x ∨ anyB p xs

testC testE : Ctx → CTy → Tmpl → Bool
testC Γ A t = okT t ∧ eqCtx Γ (ctx t) ∧ eqTy A (cgoal t)
testE Γ A t = okT t ∧ eqCtx Γ (ctx t) ∧ eqTy A (egoal t)

admit? : Ctx → CTy → Bool
admit? Γ A = anyB (testC Γ A) (candsC A) ∨ anyB (testE Γ A) (candsE A)

------------------------------------------------------------------------
-- Membership and list lemmas

data _∈_ {A : Set} (x : A) : List A → Set where
  here!  : ∀ {xs} → x ∈ (x ∷ xs)
  there! : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

∈-++ˡ : ∀ {A : Set} {x : A} {xs} ys → x ∈ xs → x ∈ (xs ++ ys)
∈-++ˡ ys here!      = here!
∈-++ˡ ys (there! p) = there! (∈-++ˡ ys p)

∈-++ʳ : ∀ {A : Set} {x : A} xs {ys} → x ∈ ys → x ∈ (xs ++ ys)
∈-++ʳ []       p = p
∈-++ʳ (_ ∷ xs) p = there! (∈-++ʳ xs p)

∈-map : ∀ {A B : Set} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
∈-map f here!      = here!
∈-map f (there! p) = there! (∈-map f p)

∈-concatMap : ∀ {A B : Set} (f : A → List B) {x y xs} → x ∈ xs → y ∈ f x →
              y ∈ concatMap f xs
∈-concatMap f {xs = x ∷ xs} here!      q = ∈-++ˡ (concatMap f xs) q
∈-concatMap f {xs = z ∷ xs} (there! p) q = ∈-++ʳ (f z) (∈-concatMap f p q)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

∨-introˡ : ∀ {a} b → T a → T (a ∨ b)
∨-introˡ {true} b _ = tt

∨-introʳ : ∀ a {b} → T b → T (a ∨ b)
∨-introʳ true  _ = tt
∨-introʳ false p = p

anyB-complete : ∀ {A : Set} (p : A → Bool) {x xs} → x ∈ xs → T (p x) → T (anyB p xs)
anyB-complete p {x} {_ ∷ xs} here! q = ∨-introˡ (anyB p xs) q
anyB-complete p {xs = y ∷ xs} (there! m) q = ∨-introʳ (p y) (anyB-complete p m q)

anyB-sound : ∀ {A : Set} (p : A → Bool) xs → T (anyB p xs) → Σ A (λ x → T (p x))
anyB-sound p []       ()
anyB-sound p (x ∷ xs) q = go (p x) refl q
  where
  go : (b : Bool) → p x ≡ b → T (b ∨ anyB p xs) → Σ _ (λ y → T (p y))
  go true  e _ = x , subst T (sym e) tt
  go false e r = anyB-sound p xs r

∨-split : ∀ {X : Set} a b → T (a ∨ b) → (T a → X) → (T b → X) → X
∨-split true  _ p f _ = f tt
∨-split false b p _ g = g p

++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

------------------------------------------------------------------------
-- Completeness of the candidate lists

dim-tyU : ∀ t j → dim (tyU t j) ≡ j
dim-tyU t zero    = refl
dim-tyU t (suc j) = cong suc (dim-tyU t j)

baseM-tyU : ∀ t j → baseM (tyU t j) ≡ H (row t)
baseM-tyU t zero    = refl
baseM-tyU t (suc j) = baseM-tyU t j

slot-lemma : ∀ pre L x R z ρ → ρ ∈ slotRow (pre ++ L) x R z → ρ ∈ slotRows pre (L ++ x ∷ R) z
slot-lemma pre [] x R z ρ m =
  ∈-++ˡ (slotRows (pre ++ x ∷ []) R z) (subst (λ q → ρ ∈ slotRow q x R z) (++-[] pre) m)
slot-lemma pre (y ∷ L) x R z ρ m =
  ∈-++ʳ (slotRow pre y (L ++ x ∷ R) z)
    (slot-lemma (pre ++ y ∷ []) L x R z ρ
      (subst (λ q → ρ ∈ slotRow q x R z) (sym (++-assoc pre (y ∷ []) L)) m))

rowsOf-complete : ∀ ρ → ρ ∈ rowsOf (H ρ)
rowsOf-complete (pairR L U V R Z) =
  ∈-++ʳ (outRows (L ++ (U ⊗ V) ∷ R) Z) (slot-lemma [] L (U ⊗ V) R Z _ here!)
rowsOf-complete (probeR L Δ Θ R Z) =
  ∈-++ʳ (outRows (L ++ rep (Δ ⊠ Θ) ∷ R) Z) (slot-lemma [] L (rep (Δ ⊠ Θ)) R Z _ here!)
rowsOf-complete (unitR L R Z) =
  ∈-++ʳ (outRows (L ++ rep (disk 0) ∷ R) Z) (slot-lemma [] L (rep (disk 0)) R Z _ here!)
rowsOf-complete (evLR Φ A C) = here!
rowsOf-complete (evRR Φ A C) = here!

private
  tmpl-eq : ∀ t → T (okT t) →
            tmpl (row t) (gapC (cgoal t)) (modeC (cgoal t)) (dim (cgoal t)) ≡ t
  tmpl-eq (tmpl ρ g m zero) ok
    rewrite eqMode-sound m inv (∧-fst (∧-snd {canon ρ} ok))
          | ==ℕ-sound g (length (ins (H ρ))) (∧-snd {eqMode m inv} (∧-snd {canon ρ} ok))
    = refl
  tmpl-eq t@(tmpl ρ g m (suc k)) ok rewrite dim-tyU t k = refl

candsC-complete : ∀ t → T (okT t) → t ∈ candsC (cgoal t)
candsC-complete t ok =
  subst (λ u → u ∈ candsC (cgoal t)) (tmpl-eq t ok)
    (∈-map (λ ρ → tmpl ρ (gapC (cgoal t)) (modeC (cgoal t)) (dim (cgoal t)))
      (subst (λ M → row t ∈ rowsOf M) (sym (baseM-tyU t (dimn t))) (rowsOf-complete (row t))))

heres-rmap : ∀ ρ c → c ∈ heres (rmap ρ (here c))
heres-rmap (pairR _ _ _ _ _)  c = here!
heres-rmap (probeR _ _ _ _ _) c = here!
heres-rmap (unitR _ _ _)      c = here!
heres-rmap (evLR _ _ _)       c = here!
heres-rmap (evRR _ _ _)       c = here!

candsE-complete : ∀ t → T (okT t) → t ∈ candsE (egoal t)
candsE-complete t ok =
  ∈-concatMap candsC (heres-rmap (row t) (cgoal t)) (candsC-complete t ok)

------------------------------------------------------------------------
-- admit? decides Admissible

admit?-complete : ∀ {Γ A} → Admissible Γ A → T (admit? Γ A)
admit?-complete {Γ} {A} (adm-c t ok refl refl) =
  ∨-introˡ (anyB (testE Γ A) (candsE A))
    (anyB-complete (testC Γ A) (candsC-complete t ok)
      (∧-intro ok (∧-intro (eqCtx-refl (ctx t)) (eqTy-refl (cgoal t)))))
admit?-complete {Γ} {A} (adm-ε t ok refl refl) =
  ∨-introʳ (anyB (testC Γ A) (candsC A))
    (anyB-complete (testE Γ A) (candsE-complete t ok)
      (∧-intro ok (∧-intro (eqCtx-refl (ctx t)) (eqTy-refl (egoal t)))))

admit?-sound : ∀ Γ A → T (admit? Γ A) → Admissible Γ A
admit?-sound Γ A p =
  ∨-split (anyB (testC Γ A) (candsC A)) _ p
    (λ q → let (t , r) = anyB-sound (testC Γ A) (candsC A) q
               r′ = ∧-snd {okT t} r
           in adm-c t (∧-fst r) (eqCtx-sound Γ (ctx t) (∧-fst r′))
                    (eqTy-sound A (cgoal t) (∧-snd {eqCtx Γ (ctx t)} r′)))
    (λ q → let (t , r) = anyB-sound (testE Γ A) (candsE A) q
               r′ = ∧-snd {okT t} r
           in adm-ε t (∧-fst r) (eqCtx-sound Γ (ctx t) (∧-fst r′))
                    (eqTy-sound A (egoal t) (∧-snd {eqCtx Γ (ctx t)} r′)))

------------------------------------------------------------------------
-- Orientation

-- an admissible directed goal is a c-goal whose endpoints are u±_k
dir-shape : ∀ {Γ g X s t} → Admissible Γ (hom dir g X s t) →
            Σ Nat (λ k → (s ≡ var (uM k)) × (t ≡ var (uP k)))
dir-shape (adm-c (tmpl ρ g m zero)    ok eΓ ())
dir-shape (adm-c (tmpl ρ g m (suc k)) ok eΓ refl) = k , (refl , refl)
dir-shape (adm-ε t ok eΓ ())

private
  unvar : Tm → Nat
  unvar (var n) = n
  unvar _       = 0

  no-cycle : ∀ n → n ≡ suc (suc n) → ⊥
  no-cycle zero    ()
  no-cycle (suc n) e = no-cycle n (cong pred e)
    where pred : Nat → Nat
          pred zero    = zero
          pred (suc k) = k

-- the judgement is not endpoint-symmetric on directed goals
no-reverse : ∀ {Γ g X s t} → Admissible Γ (hom dir g X s t) →
             Admissible Γ (hom dir g X t s) → ⊥
no-reverse p q with dir-shape p | dir-shape q
... | k₁ , (refl , refl) | k₂ , (e₁ , e₂) =
  no-cycle (uM k₂)
    (trans (sym (cong unvar e₁)) (cong suc (cong unvar e₂)))

isDirTop : CTy → Bool
isDirTop (hom dir _ _ _ _) = true
isDirTop _                 = false

-- a directed goal needs a directed hypothesis
dir-needs-dir : ∀ {Γ g X s t} → Admissible Γ (hom dir g X s t) → T (anyB isDirTop Γ)
dir-needs-dir (adm-c (tmpl ρ g m zero)    ok eΓ ())
dir-needs-dir (adm-c t@(tmpl ρ g m (suc k)) ok refl refl) =
  anyB-complete isDirTop (∈-++ʳ (levels t (suc k)) here!) tt
dir-needs-dir (adm-ε t ok eΓ ())
