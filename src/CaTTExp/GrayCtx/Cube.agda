------------------------------------------------------------------------
-- The Gray cube D¹ ⊗ D¹ ⊗ D¹ in both bracketings, and G4 for it.
--
-- Factors a, b, c (each a copy of D¹ = x —f→ y). A generator is a
-- triple (α, β, γ) with entries 0, 1 (the two vertices) or e (the edge).
--
--   CubeR = (a ⊗ b) ⊗ c = cyl right 1 (a ⊗ b),  with a ⊗ b = cyl right 1 D¹
--   CubeL = a ⊗ (b ⊗ c) = cyl left  1 (b ⊗ c),  with b ⊗ c = cyl right 1 D¹
--
-- CubeR uses the "Γ ⊗ D¹" cylinder (new factor on the right) and CubeL
-- the "D¹ ⊗ Γ" cylinder (new factor on the left), so the two
-- orientations of the cylinder construction are both exercised.
--
-- Results (checked in CaTTExp.GrayCtx.Checks):
--   * both contexts are well formed;
--   * under the evident renaming of generators, all 26 generators other
--     than the cube cell (e,e,e) have syntactically equal types;
--   * the cube cells' types differ (bracketing of the boundary 3-paths
--     and placement of associators), so G4 fails on the nose;
--   * G4 holds up to coherence: `toL` is a well-typed substitution
--     CubeR ⊢ toL : CubeL, which is the renaming on the 26 lower
--     generators and sends the cube cell of CubeL to the cube cell of
--     CubeR conjugated by substituted pasting-scheme coherences.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Cube where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import Agda.Builtin.Nat using (_*_)

D¹ : Ctx
D¹ = ctxOf (chain 1)

Square : Ctx
Square = fromJust (cyl right 1 D¹)

CubeR CubeL : Maybe Ctx
CubeR = cyl right 1 Square
CubeL = cyl left  1 Square

-- Generator triples, in the variable order of CubeR.
Triple : Set
Triple = Nat × Nat × Nat     -- each entry 0, 1, or 2 (= e)

private
  three : List Nat
  three = 0 ∷ 1 ∷ 2 ∷ []

  mapL : ∀ {A B : Set} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
  concatMap f []       = []
  concatMap f (x ∷ xs) = f x ++ concatMap f xs

triples triplesL : List Triple
triples  = concatMap (λ c → concatMap (λ b → mapL (λ a → a , b , c) three) three) three
-- in the variable order of CubeL
triplesL = concatMap (λ a → concatMap (λ c → mapL (λ b → a , b , c) three) three) three

-- Levels. In a ⊗ D¹ (= Square) the vertex/edge v ∈ {x,y,f} = {0,1,2}
-- of the D¹ factor sits at v, and copy/edge w ∈ {0,1,e} adds 3w.
levelR levelL : Triple → Nat
levelR (a , b , c) = a + 3 * b + 9 * c      -- ((a ⊗ b) ⊗ c)
levelL (a , b , c) = b + 3 * c + 9 * a      -- (a ⊗ (b ⊗ c))

-- The renaming of generators, CubeL's variables in CubeR's order.
renRL : Sub
renRL = go ⟨⟩ triples
  where
  go : Sub → List Triple → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ var (levelL t)) ts

-- The generators whose types do NOT agree under the renaming.
mismatches : List Triple
mismatches = filter bad triples
  where
  -- A plain helper, not `with`: Agda 2.8 runs out of memory on the
  -- `with` version.
  cmp : Maybe Ty → Maybe Ty → Bool
  cmp (just A) (just B) = not ((A [ renRL ]ty) ==Ty B)
  cmp _        _        = true
  bad : Triple → Bool
  bad t = cmp (CubeR >>= (λ Γ → lookup Γ (levelR t))) (CubeL >>= (λ Γ → lookup Γ (levelL t)))

------------------------------------------------------------------------
-- G4 up to coherence: CubeR ⊢ toL : CubeL and CubeL ⊢ toR : CubeR.
--
-- The construction is split into small top-level pieces (a record of
-- the 2-cells and associators, then one definition per rewriting step)
-- to keep elaboration cheap.

-- The 2-cells of the two hexagons and the associators between them,
-- in a context Γ whose generators sit at levels lev(a, b, c).
-- P = 0ee, Q = e1e, R = ee0 (source squares); P′ = 1ee, Q′ = e0e, R′ = ee1.
record Hex : Set where
  field
    P▹ ◃Q R▹ ◃R′ Q′▹ ◃P′ : Tm
    a A1 A2 A3 b B1 B2 B3 : Tm

module HexOf (lev : Triple → Nat) (Γ : Ctx) where
  g : Nat → Nat → Nat → Tm
  g x y z = var (lev (x , y , z))

  e = 2

  whR whL : Tm → Tm → Maybe Tm
  whR c z = (Γ ▹ c) z
  whL z c = (Γ ◃ z) c

  hex : Maybe Hex
  hex =
    whR (g 0 e e) (g e 1 1) >>= λ p → whL (g 0 e 0) (g e 1 e) >>= λ q →
    whR (g e e 0) (g 1 1 e) >>= λ r → whL (g 0 0 e) (g e e 1) >>= λ r′ →
    whR (g e 0 e) (g 1 e 1) >>= λ q′ → whL (g e 0 0) (g 1 e e) >>= λ p′ →
    assoc  Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ a  →
    assoc⁻ Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ A1 →
    assoc  Γ (g 0 e 0) (g 0 1 e) (g e 1 1) >>= λ A2 →
    assoc⁻ Γ (g 0 e 0) (g e 1 0) (g 1 1 e) >>= λ A3 →
    assoc  Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ b  →
    assoc⁻ Γ (g 0 0 e) (g e 0 1) (g 1 e 1) >>= λ B1 →
    assoc  Γ (g e 0 0) (g 1 0 e) (g 1 e 1) >>= λ B2 →
    assoc⁻ Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ B3 →
    just (record { P▹ = p ; ◃Q = q ; R▹ = r ; ◃R′ = r′ ; Q′▹ = q′ ; ◃P′ = p′
                 ; a = a ; A1 = A1 ; A2 = A2 ; A3 = A3 ; b = b ; B1 = B1 ; B2 = B2 ; B3 = B3 })

  -- Hexagons as chains:
  --   S_R = [[A1, P▹, A2, ◃Q, A3], R▹]     T_R = [◃R′, [B1, Q′▹, B2, ◃P′, B3]]
  --   S_L = [P▹, [A2, ◃Q, A3, R▹, b]]      T_L = [[a, ◃R′, B1, Q′▹, B2], ◃P′]
  module _ (h : Hex) where
    open Hex h
    M N M′ N′ : List Tm
    M  = A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []
    N  = B1 ∷ Q′▹ ∷ B2 ∷ ◃P′ ∷ B3 ∷ []
    M′ = A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []
    N′ = a ∷ ◃R′ ∷ B1 ∷ Q′▹ ∷ B2 ∷ []

    snd′ : Maybe (List Tm × Tm) → Maybe Tm
    snd′ m = snd <$> m

    -- toL: the image of CubeL's cube cell, from CubeR's cube cell X.
    stepsL : Tm → List (Maybe Tm)
    stepsL X =
      -- S_L ⇒ flat
      regroup false Γ (P▹ ∷ []) M′ [] ∷
      -- P▹ ⇒ id ; P▹
      (unitor true false Γ P▹ >>= λ Φ → srcOf Γ P▹ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ [] (P▹ ∷ []) M′ Φ (i ∷ P▹ ∷ []))) ∷
      -- id ⇒ a ; A1
      (cancel false false Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ Φ →
       srcOf Γ P▹ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ [] (i ∷ []) (P▹ ∷ M′) Φ (a ∷ A1 ∷ []))) ∷
      -- flat ⇒ [a, S_R, b]
      regroup true Γ (a ∷ []) M (R▹ ∷ b ∷ []) ∷
      (vcomp Γ M >>= λ m → regroup true Γ (a ∷ []) (m ∷ R▹ ∷ []) (b ∷ [])) ∷
      whiskIn Γ (a ∷ []) X (b ∷ []) ∷
      -- [a, T_R, b] ⇒ flat
      (vcomp Γ N >>= λ n → regroup false Γ (a ∷ []) (◃R′ ∷ n ∷ []) (b ∷ [])) ∷
      regroup false Γ (a ∷ ◃R′ ∷ []) N (b ∷ []) ∷
      -- B3 ; b ⇒ id
      (cancel true true Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ Φ →
       tgtOf Γ ◃P′ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ (a ∷ ◃R′ ∷ B1 ∷ Q′▹ ∷ B2 ∷ ◃P′ ∷ []) (B3 ∷ b ∷ []) [] Φ (i ∷ []))) ∷
      -- ◃P′ ; id ⇒ ◃P′
      (unitor false true Γ ◃P′ >>= λ Φ → tgtOf Γ ◃P′ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ N′ (◃P′ ∷ i ∷ []) [] Φ (◃P′ ∷ []))) ∷
      -- flat ⇒ T_L
      regroup true Γ [] N′ (◃P′ ∷ []) ∷ []

    -- toR: the image of CubeR's cube cell, from CubeL's cube cell X.
    stepsR : Tm → List (Maybe Tm)
    stepsR X =
      regroup false Γ [] M (R▹ ∷ []) ∷
      (unitor false false Γ R▹ >>= λ Φ → tgtOf Γ R▹ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ M (R▹ ∷ []) [] Φ (R▹ ∷ i ∷ []))) ∷
      (cancel false false Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ Φ →
       tgtOf Γ R▹ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ (M ++ R▹ ∷ []) (i ∷ []) [] Φ (b ∷ B3 ∷ []))) ∷
      regroup true Γ (A1 ∷ P▹ ∷ []) M′ (B3 ∷ []) ∷
      (vcomp Γ M′ >>= λ m → regroup true Γ (A1 ∷ []) (P▹ ∷ m ∷ []) (B3 ∷ [])) ∷
      whiskIn Γ (A1 ∷ []) X (B3 ∷ []) ∷
      (vcomp Γ N′ >>= λ n → regroup false Γ (A1 ∷ []) (n ∷ ◃P′ ∷ []) (B3 ∷ [])) ∷
      regroup false Γ (A1 ∷ []) N′ (◃P′ ∷ B3 ∷ []) ∷
      (cancel true true Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ Φ →
       srcOf Γ ◃R′ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ [] (A1 ∷ a ∷ []) (◃R′ ∷ N) Φ (i ∷ []))) ∷
      (unitor true true Γ ◃R′ >>= λ Φ → srcOf Γ ◃R′ >>= idc Γ >>= λ i →
       snd′ (stepAt Γ [] (i ∷ ◃R′ ∷ []) N Φ (◃R′ ∷ []))) ∷
      regroup true Γ (◃R′ ∷ []) N [] ∷ []

  run : (Hex → Tm → List (Maybe Tm)) → Maybe Tm
  run steps = hex >>= λ h → mapM (λ m → m) (steps h (g e e e)) >>= vcomp Γ

-- the renaming on the first 26 generators of a cube (the cube cell is
-- last in both contexts), listed along `order`, sent to levels `lev`
private
  initRen : List Triple → (Triple → Nat) → Sub
  initRen order lev = go ⟨⟩ order
    where
    go : Sub → List Triple → Sub
    go σ []           = σ
    go σ (_ ∷ [])     = σ
    go σ (t ∷ u ∷ ts) = go (σ ,ₛ var (lev t)) (u ∷ ts)

toL : Maybe (Ctx × Sub)
toL = CubeR >>= λ Γ → HexOf.run levelR Γ (HexOf.stepsL levelR Γ) >>= λ c →
      just (Γ , (initRen triplesL levelR ,ₛ c))

toR : Maybe (Ctx × Sub)
toR = CubeL >>= λ Γ → HexOf.run levelL Γ (HexOf.stepsR levelL Γ) >>= λ c →
      just (Γ , (initRen triples levelL ,ₛ c))

------------------------------------------------------------------------
-- Consistency of the two orientations on the square: `cyl right 1 D¹`
-- (factors D¹ ⊗ e) and `cyl left 1 D¹` (factors e ⊗ D¹) are the same
-- context A ⊗ B up to the renaming of generators (A, B) ↦ (A, B).

SquareL : Ctx
SquareL = fromJust (cyl left 1 D¹)

private
  pairs : List (Nat × Nat)          -- (A, B) in the variable order of Square
  pairs = concatMap (λ B → mapL (λ A → A , B) three) three

renSq : Sub
renSq = go ⟨⟩ pairs
  where
  go : Sub → List (Nat × Nat) → Sub
  go σ []             = σ
  go σ ((A , B) ∷ qs) = go (σ ,ₛ var (B + 3 * A)) qs

squareMismatches : List (Nat × Nat)
squareMismatches = filter bad pairs
  where
  cmp : Maybe Ty → Maybe Ty → Bool
  cmp (just S) (just T) = not ((S [ renSq ]ty) ==Ty T)
  cmp _        _        = true
  bad : Nat × Nat → Bool
  bad (A , B) = cmp (lookup Square (A + 3 * B)) (lookup SquareL (B + 3 * A))
