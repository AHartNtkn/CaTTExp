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

fromJust : Maybe Ctx → Ctx
fromJust (just Γ) = Γ
fromJust nothing  = ε

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
  bad : Triple → Bool
  bad t with CubeR >>= (λ Γ → lookup Γ (levelR t)) | CubeL >>= (λ Γ → lookup Γ (levelL t))
  ... | just A | just B = not ((A [ renRL ]ty) ==Ty B)
  ... | _      | _      = true

------------------------------------------------------------------------
-- G4 up to coherence: CubeR ⊢ toL : CubeL.

module ToL (Γ : Ctx) where
  -- Γ is meant to be CubeR. Generators by triple, with e = 2.
  g : Nat → Nat → Nat → Tm
  g a b c = var (levelR (a , b , c))

  e = 2

  _▹'_ _◃'_ : Tm → Tm → Maybe Tm
  c ▹' z = (Γ ▹ c) z
  z ◃' c = (Γ ◃ z) c

  -- The image of CubeL's cube cell: a 3-cell  S_L ⇒ T_L  in CubeR, built
  -- from the cube cell  g e e e : S_R ⇒ T_R  of CubeR.
  cubeL : Maybe Tm
  cubeL =
    -- 2-cells of the source and target hexagons (squares whiskered by edges)
    (g 0 e e ▹' g e 1 1) >>= λ P▹ → (g 0 e 0 ◃' g e 1 e) >>= λ ◃Q → (g e e 0 ▹' g 1 1 e) >>= λ R▹ →
    (g 0 0 e ◃' g e e 1) >>= λ ◃R' → (g e 0 e ▹' g 1 e 1) >>= λ Q'▹ → (g e 0 0 ◃' g 1 e e) >>= λ ◃P' →
    -- associators
    assoc  Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ a  →
    assoc⁻ Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ A1 →
    assoc  Γ (g 0 e 0) (g 0 1 e) (g e 1 1) >>= λ A2 →
    assoc⁻ Γ (g 0 e 0) (g e 1 0) (g 1 1 e) >>= λ A3 →
    assoc  Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ b  →
    assoc⁻ Γ (g 0 0 e) (g e 0 1) (g 1 e 1) >>= λ B1 →
    assoc  Γ (g e 0 0) (g 1 0 e) (g 1 e 1) >>= λ B2 →
    assoc⁻ Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ B3 →
    -- CubeR's hexagons:  S_R = [[A1, P▹, A2, ◃Q, A3], R▹],  T_R = [◃R', [B1, Q'▹, B2, ◃P', B3]]
    vcomp Γ (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []) >>= λ M →
    vcomp Γ (B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ []) >>= λ N →
    vcomp Γ (M ∷ R▹ ∷ []) >>= λ S_R → vcomp Γ (◃R' ∷ N ∷ []) >>= λ T_R →
    -- CubeL's hexagons (renamed):  S_L = [P▹, [A2, ◃Q, A3, R▹, b]],  T_L = [[a, ◃R', B1, Q'▹, B2], ◃P']
    vcomp Γ (A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) >>= λ M' →
    vcomp Γ (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ []) >>= λ N' →
    -- S_L ⇒ flat
    regroup false Γ (P▹ ∷ []) (A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) [] >>= λ r₀ →
    let ch₀ = P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ [] in
    -- P▹ ⇒ id ; P▹ ⇒ (a ; A1) ; P▹
    srcOf Γ P▹ >>= λ u → idc Γ u >>= λ idu →
    unitor true false Γ P▹ >>= λ Φ₁ →
    stepAt Γ [] (P▹ ∷ []) (A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) Φ₁ (idu ∷ P▹ ∷ []) >>= λ s₁ →
    cancel false false Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ Φ₂ →
    stepAt Γ [] (idu ∷ []) (P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) Φ₂ (a ∷ A1 ∷ []) >>= λ s₂ →
    -- flat ⇒ [a, S_R, b]
    regroup true Γ (a ∷ []) (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []) (R▹ ∷ b ∷ []) >>= λ r₃ →
    regroup true Γ (a ∷ []) (M ∷ R▹ ∷ []) (b ∷ []) >>= λ r₄ →
    -- the cube cell of CubeR, whiskered
    whiskIn Γ (a ∷ []) (g e e e) (b ∷ []) >>= λ w₅ →
    -- [a, T_R, b] ⇒ flat
    regroup false Γ (a ∷ []) (◃R' ∷ N ∷ []) (b ∷ []) >>= λ r₆ →
    regroup false Γ (a ∷ ◃R' ∷ []) (B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ []) (b ∷ []) >>= λ r₇ →
    let ch₇ = a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ b ∷ [] in
    -- B3 ; b ⇒ id ; ◃P' ; id ⇒ ◃P'
    tgtOf Γ ◃P' >>= λ w → idc Γ w >>= λ idw →
    cancel true true Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ Φ₈ →
    stepAt Γ (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ []) (B3 ∷ b ∷ []) [] Φ₈ (idw ∷ []) >>= λ s₈ →
    unitor false true Γ ◃P' >>= λ Φ₉ →
    stepAt Γ (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ []) (◃P' ∷ idw ∷ []) [] Φ₉ (◃P' ∷ []) >>= λ s₉ →
    -- flat ⇒ T_L
    regroup true Γ [] (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ []) (◃P' ∷ []) >>= λ r₁₀ →
    vcomp Γ (r₀ ∷ snd s₁ ∷ snd s₂ ∷ r₃ ∷ r₄ ∷ w₅ ∷ r₆ ∷ r₇ ∷ snd s₈ ∷ snd s₉ ∷ r₁₀ ∷ [])

toL : Maybe (Ctx × Sub)
toL = CubeR >>= λ Γ → ToL.cubeL Γ >>= λ c → just (Γ , (init ,ₛ c))
  where
  -- the renaming on the first 26 generators of CubeL (the cube cell is
  -- last in both contexts)
  init : Sub
  init = go ⟨⟩ triplesL
    where
    go : Sub → List Triple → Sub
    go σ []            = σ
    go σ (_ ∷ [])      = σ
    go σ (t ∷ u ∷ ts)  = go (σ ,ₛ var (levelR t)) (u ∷ ts)

-- The converse: CubeL ⊢ toR : CubeR.
module ToR (Γ : Ctx) where
  -- Γ is meant to be CubeL.
  g : Nat → Nat → Nat → Tm
  g a b c = var (levelL (a , b , c))

  e = 2

  _▹'_ _◃'_ : Tm → Tm → Maybe Tm
  c ▹' z = (Γ ▹ c) z
  z ◃' c = (Γ ◃ z) c

  cubeR : Maybe Tm
  cubeR =
    (g 0 e e ▹' g e 1 1) >>= λ P▹ → (g 0 e 0 ◃' g e 1 e) >>= λ ◃Q → (g e e 0 ▹' g 1 1 e) >>= λ R▹ →
    (g 0 0 e ◃' g e e 1) >>= λ ◃R' → (g e 0 e ▹' g 1 e 1) >>= λ Q'▹ → (g e 0 0 ◃' g 1 e e) >>= λ ◃P' →
    assoc  Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ a  →
    assoc⁻ Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ A1 →
    assoc  Γ (g 0 e 0) (g 0 1 e) (g e 1 1) >>= λ A2 →
    assoc⁻ Γ (g 0 e 0) (g e 1 0) (g 1 1 e) >>= λ A3 →
    assoc  Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ b  →
    assoc⁻ Γ (g 0 0 e) (g e 0 1) (g 1 e 1) >>= λ B1 →
    assoc  Γ (g e 0 0) (g 1 0 e) (g 1 e 1) >>= λ B2 →
    assoc⁻ Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ B3 →
    vcomp Γ (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []) >>= λ M →
    vcomp Γ (A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) >>= λ M' →
    vcomp Γ (P▹ ∷ M' ∷ []) >>= λ S_L →
    vcomp Γ (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ []) >>= λ N' →
    -- S_R ⇒ flat
    regroup false Γ [] (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []) (R▹ ∷ []) >>= λ r₀ →
    -- R▹ ⇒ R▹ ; id ⇒ R▹ ; (b ; B3)
    tgtOf Γ R▹ >>= λ w → idc Γ w >>= λ idw →
    unitor false false Γ R▹ >>= λ Φ₁ →
    stepAt Γ (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ []) (R▹ ∷ []) [] Φ₁ (R▹ ∷ idw ∷ []) >>= λ s₁ →
    cancel false false Γ (g e 0 0) (g 1 e 0) (g 1 1 e) >>= λ Φ₂ →
    stepAt Γ (A1 ∷ P▹ ∷ A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ []) (idw ∷ []) [] Φ₂ (b ∷ B3 ∷ []) >>= λ s₂ →
    -- flat ⇒ [A1, S_L, B3]
    regroup true Γ (A1 ∷ P▹ ∷ []) (A2 ∷ ◃Q ∷ A3 ∷ R▹ ∷ b ∷ []) (B3 ∷ []) >>= λ r₃ →
    regroup true Γ (A1 ∷ []) (P▹ ∷ M' ∷ []) (B3 ∷ []) >>= λ r₄ →
    whiskIn Γ (A1 ∷ []) (g e e e) (B3 ∷ []) >>= λ w₅ →
    -- [A1, T_L, B3] ⇒ flat
    regroup false Γ (A1 ∷ []) (N' ∷ ◃P' ∷ []) (B3 ∷ []) >>= λ r₆ →
    regroup false Γ (A1 ∷ []) (a ∷ ◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ []) (◃P' ∷ B3 ∷ []) >>= λ r₇ →
    -- A1 ; a ⇒ id ; id ; ◃R' ⇒ ◃R'
    srcOf Γ ◃R' >>= λ u → idc Γ u >>= λ idu →
    cancel true true Γ (g 0 0 e) (g 0 e 1) (g e 1 1) >>= λ Φ₈ →
    stepAt Γ [] (A1 ∷ a ∷ []) (◃R' ∷ B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ []) Φ₈ (idu ∷ []) >>= λ s₈ →
    unitor true true Γ ◃R' >>= λ Φ₉ →
    stepAt Γ [] (idu ∷ ◃R' ∷ []) (B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ []) Φ₉ (◃R' ∷ []) >>= λ s₉ →
    -- flat ⇒ T_R
    regroup true Γ (◃R' ∷ []) (B1 ∷ Q'▹ ∷ B2 ∷ ◃P' ∷ B3 ∷ []) [] >>= λ r₁₀ →
    vcomp Γ (r₀ ∷ snd s₁ ∷ snd s₂ ∷ r₃ ∷ r₄ ∷ w₅ ∷ r₆ ∷ r₇ ∷ snd s₈ ∷ snd s₉ ∷ r₁₀ ∷ [])

toR : Maybe (Ctx × Sub)
toR = CubeL >>= λ Γ → ToR.cubeR Γ >>= λ c → just (Γ , (init ,ₛ c))
  where
  init : Sub
  init = go ⟨⟩ triples
    where
    go : Sub → List Triple → Sub
    go σ []            = σ
    go σ (_ ∷ [])      = σ
    go σ (t ∷ u ∷ ts)  = go (σ ,ₛ var (levelL t)) (u ∷ ts)

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
  go σ ((A , B) ∷ ps) = go (σ ,ₛ var (B + 3 * A)) ps

squareMismatches : List (Nat × Nat)
squareMismatches = filter bad pairs
  where
  bad : Nat × Nat → Bool
  bad (A , B) with lookup Square (A + 3 * B) | lookup SquareL (B + 3 * A)
  ... | just S | just T = not ((S [ renSq ]ty) ==Ty T)
  ... | _      | _      = true
