------------------------------------------------------------------------
-- D7d: the rows of F.7.4 §2 and the generic contexts and goals of the
-- templates (moved out of Templates so that the checker can type the
-- coherence term `here t e φs ts` against its template).
--
-- Layout of the generic context of a template (row ρ, gap g, mode m,
-- dimension n).  Level j < n is a block of six entries at 6j … 6j+5:
--   u⁻_j, u⁺_j  : the (n−1)-sphere u of operations of type H
--   β⁻_j, β⁺_j  : the boundary sphere of the ball b in B
--   a⁻_j, a⁺_j  : the collar r(u±_j) ≅ (β±_j with lower collars adjoined)
-- followed by the ball b itself at position 6n.  Goals: c = the n-cell
-- of type H with boundary u (cgoal), and ε = the invertible cell
-- r(c) ≅ b with the collar adjoined (egoal), whose source contains c as
-- the term `cterm` = here t gc (identity instance).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Rows where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import Agda.Builtin.Nat using (_*_)

------------------------------------------------------------------------
-- Rows (F.7.4 §2 table)

-- H: type of the missing vertex
H : Row → MTy
H (pairR L U V R Z)  = (L ++ (U ⊗ V) ∷ R) ▸ Z
H (probeR L Δ Θ R Z) = (L ++ rep (Δ ⊠ Θ) ∷ R) ▸ Z
H (unitR L R Z)      = (L ++ rep (disk 0) ∷ R) ▸ Z
H (evLR Φ A C)       = Φ ▸ (A \\ C)
H (evRR Φ A C)       = Φ ▸ (C // A)
H (shapeR L Θ R Z)   = (L ++ shp Θ ∷ R) ▸ Z

-- B: type of the outer operation
B : Row → MTy
B (pairR L U V R Z)  = (L ++ U ∷ V ∷ R) ▸ Z
B (probeR L Δ Θ R Z) = (L ++ rep Δ ∷ rep Θ ∷ R) ▸ Z
B (unitR L R Z)      = (L ++ R) ▸ Z
B (evLR Φ A C)       = (A ∷ Φ) ▸ C
B (evRR Φ A C)       = (Φ ++ A ∷ []) ▸ C
B (shapeR L Θ R Z)   = (L ++ rep Θ ∷ R) ▸ Z

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
rmap (shapeR L Θ R Z)    x = comp x (ids L ++ iP Θ ∷ ids R)

-- the image of a time-slot gap under r (as computed by whiskering)
rgap : Row → Nat → Nat
rgap (pairR L U V R Z)  g = sumIns (take g (idTys L ++ ((U ∷ V ∷ []) ▸ (U ⊗ V)) ∷ idTys R))
rgap (probeR L Δ Θ R Z) g = sumIns (take g (idTys L ++ ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) ∷ idTys R))
rgap (unitR L R Z)      g = sumIns (take g (idTys L ++ ([] ▸ rep (disk 0)) ∷ idTys R))
rgap (evLR Φ A C)       g = 1 + g
rgap (evRR Φ A C)       g = g
rgap (shapeR L Θ R Z)    g = sumIns (take g (idTys L ++ ((rep Θ ∷ []) ▸ shp Θ) ∷ idTys R))

-- generic templates use fresh object variables, numbered in order of
-- appearance in the outer profile B; the output is an object variable
fmsOf : Row → List Fm
fmsOf (pairR L U V R Z)  = L ++ U ∷ V ∷ R ++ Z ∷ []
fmsOf (probeR L _ _ R Z) = L ++ R ++ Z ∷ []
fmsOf (unitR L R Z)      = L ++ R ++ Z ∷ []
fmsOf (evLR Φ A C)       = A ∷ Φ ++ C ∷ []
fmsOf (evRR Φ A C)       = Φ ++ A ∷ C ∷ []
fmsOf (shapeR L _ R Z)    = L ++ R ++ Z ∷ []

outOf : Row → Fm
outOf (pairR _ _ _ _ Z)  = Z
outOf (probeR _ _ _ _ Z) = Z
outOf (unitR _ _ Z)      = Z
outOf (evLR _ _ C)       = C
outOf (evRR _ _ C)       = C
outOf (shapeR _ _ _ Z)   = Z

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

-- object variables of a template: one per formula of its row (an upper
-- bound for canonical rows, which skip representables)
nObj : Tmpl → Nat
nObj t = length (fmsOf (row t))

objsFrom : Nat → Nat → List Fm
objsFrom k zero    = []
objsFrom k (suc n) = obj k ∷ objsFrom (suc k) n

varsFrom : Nat → Nat → List Tm
varsFrom k zero    = []
varsFrom k (suc n) = var k ∷ varsFrom (suc k) n

idφ : Tmpl → List Fm
idφ t = objsFrom 0 (nObj t)

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

  -- the identity instance: object variable i ↦ obj i, context variable
  -- i ↦ var i, over the whole template
  nCtx : Nat
  nCtx = length ctx

  idts : List Tm
  idts = varsFrom 0 nCtx

  -- the c of this very instance, as a term
  cterm : Tm
  cterm = here t gc (idφ t) idts

  egoal : CTy
  egoal = hom inv g′ (tyRU (dimn t)) (rmap ρ cterm) (chain (dimn t) (var (pos (dimn t) 0)))

  goal : Goal → CTy
  goal gc = cgoal
  goal gε = egoal

leq : Nat → Nat → Bool
leq zero    _       = true
leq (suc m) zero    = false
leq (suc m) (suc n) = leq m n

-- side conditions: canonical generic formulas; at n = 0 the template is
-- the invertible one at the rightmost gap; otherwise any gap of H
okT : Tmpl → Bool
okT (tmpl ρ g m zero)    = canon ρ ∧ eqMode m inv ∧ (g ==ℕ length (ins (H ρ)))
okT (tmpl ρ g m (suc n)) = canon ρ ∧ leq g (length (ins (H ρ)))

