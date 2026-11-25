------------------------------------------------------------------------
-- The single-piece step of the descent (ledger S20 (i), stage 4e;
-- notes/rc-generator.md §1, stage 4 plan; tools/rc_descent.py `_piece`).
--
-- Given parallel typed n-cells t, u of Γ and a *plan* (untrusted data:
-- the pasting arity W = ctxOf tree, which nodes are expanded, J's
-- entries, R's images of the generators, and the generators in
-- dependency order), the step
--
--   1. types J : W → Γ (buildSub) and maps t, u into W by R (MapGen);
--   2. compares R t with R u in W by the recursion oracle, w : R t ⇛ R u,
--      and pulls it back: w* = J w : JR t ⇛ JR u;
--   3. walks the generators: x moves when JR x ≠ x (decided by ==Tm);
--      then x⁺ = JR x, its bridge x↑ : a_x ⇛ b_x is a recursive call on
--      the ends of Square.endsG, and for a top-dimensional x also the
--      reversed bridge b_x ⇛ a_x;
--   4. builds the lax square t↑ : a_t ⇛ b_t, the oplax square
--      u↑ᵒᵖ : b_u ⇛ a_u, and mid : b_t ⇛ b_u (the whiskers of b_t around
--      w*), and X = (t↑ ;ₙ mid) ;ₙ u↑ᵒᵖ : a_t ⇛ a_u;
--   5. strips the whiskers of a_t = (…(t ;₀ A₀) …) ;ₙ₋₁ Aₙ₋₁ from the
--      top (Strip.stripR at cut n − 1, Strip.stripL at cut n − 2).
--
-- `pieceA` decides that the result has type t ⇛ u (a syntactic
-- equality), so every answer is typed by proof; the plan, the fillers
-- and the oracle only decide whether there is one.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.Piece where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (tm[])
open import CaTTExp.RCProc using (Ans)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.GlueP using (treeCtx)
open import CaTTExp.RCProc.Strip using (dimT; comp2?; srcT; tgtT; stripR; stripL)
open import CaTTExp.RCProc.Descent.Lift using (FillO)
open import CaTTExp.RCProc.Descent.LiftOp using (FillOpO)
open import CaTTExp.RCProc.Descent.Fill using (RecAll)
open import CaTTExp.RCProc.Descent.MapGen using (mapT)
open import CaTTExp.RCProc.Descent.Square

-- The plan of a piece (untrusted).
record Plan (Γ : Ctx) : Set where
  field
    tree : Tree
    exp  : Tm → Bool
    Jimg : List (TTm Γ)
    Rimg : TTm Γ → Maybe (TTm (ctxOf tree))
    gens : List (TTm Γ)
open Plan public

-- A typed term of Δ pulled back along a typed σ : Γ → Δ.
pullT : ∀ {Γ Δ} → TSub Γ Δ → TTm Δ → TTm Γ
pullT σ x = tt[ tm x [ fst σ ]tm ∶ ty x [ fst σ ]ty , tm[] (der x) (snd σ) ]

Tab : Ctx → Set
Tab Γ = List (Tm × TTm Γ)

find : ∀ {Γ} → Tab Γ → Tm → Maybe (TTm Γ)
find []             t = nothing
find ((g , x) ∷ gs) t = if g ==Tm t then just x else find gs t

-- x ↦ x⁺, x ↦ x↑, x ↦ x↑ᵒᵖ, for the moved generators so far.
record Tabs (Γ : Ctx) : Set where
  constructor tabs
  field
    tPl tUp tDn : Tab Γ
open Tabs public

mkD : ∀ {Γ} → Γ ⊢ctx → (Tm → Bool) → Tabs Γ → GDatum Γ
mkD w e tb = record { wΓ = w ; exp = e ; moved = λ t → is-just (find (tPl tb) t)
                    ; plusG = λ y → find (tPl tb) (tm y)
                    ; upG = find (tUp tb) ; dnG = find (tDn tb) }

private
  iterM : ∀ {X : Set} → Nat → (X → Maybe X) → X → Maybe X
  iterM zero    f x = just x
  iterM (suc n) f x = f x >>= iterM n f

module _ {Γ : Ctx} (wΓ : Γ ⊢ctx) (rec : RecAll) (F : FillO) (G : FillOpO) (P : Plan Γ) where
  private
    W : Ctx
    W = ctxOf (tree P)
    wW : W ⊢ctx
    wW = treeCtx (tree P)

    R : TTm Γ → Maybe (TTm W)
    R = mapT wW (exp P) (Rimg P)

  -- Step 3: the tables, generator by generator.
  tables : TSub Γ W → Nat → List (TTm Γ) → Tabs Γ → Maybe (Tabs Γ)
  tables J n []       tb = just tb
  tables J n (x ∷ xs) tb = R x >>= λ rx → step (pullT J rx) >>= tables J n xs
    where
    step : TTm Γ → Maybe (Tabs Γ)
    step jx =
      if tm jx ==Tm tm x then just tb
      else (endsG F G (mkD wΓ (exp P) tb₁) x >>= λ ab →
            rec wΓ (fst ab) (snd ab) >>= λ br →
            back ab >>= λ dn →
            just (tabs (tPl tb₁) ((tm x , br) ∷ tUp tb) dn))
      where
      tb₁ = tabs ((tm x , jx) ∷ tPl tb) (tUp tb) (tDn tb)
      back : TTm Γ × TTm Γ → Maybe (Tab Γ)
      back ab = if dimT x ==ℕ n
                then (rec wΓ (snd ab) (fst ab) >>= λ bk → just ((tm x , bk) ∷ tDn tb))
                else just (tDn tb)

  -- Steps 4 and 5.
  module _ (D : GDatum Γ) (t u wst : TTm Γ) where
    private
      n : Nat
      n = dimT t

      lifted : TTm Γ → Maybe (Maybe (TTm Γ))
      lifted w = if touchedG F G D (tm w) then (liftG F G D w >>= λ l → just (just l)) else just nothing

      whisk : Nat → TTm Γ → Maybe (TTm Γ) → Maybe (TTm Γ)
      whisk j x nothing  = just x
      whisk j x (just a) = comp2? j x a

      -- mid after the cuts j < k: (σⁿ⁻ʲ t)↑ ;ⱼ mid
      midK : Nat → Maybe (TTm Γ)
      midK zero    = just wst
      midK (suc j) = midK j >>= λ m → iterM (n ∸ j) srcT t >>= lifted >>= λ where
        nothing  → just m
        (just l) → comp2? j l m

      -- the factor Aⱼ = (τⁿ⁻ʲ t)↑ of a_t, if any
      As : Nat → Maybe (Maybe (TTm Γ))
      As j = iterM (n ∸ j) tgtT t >>= lifted

      -- x with the factors of the cuts j < k
      lo : TTm Γ → Nat → Maybe (TTm Γ)
      lo x zero    = just x
      lo x (suc j) = lo x j >>= λ l → As j >>= whisk j l

      cut : Nat → TTm Γ → TTm Γ → TTm Γ → TTm Γ → Maybe (TTm Γ)
      cut j a b K V =
        if suc j ==ℕ n then stripR wΓ (rec wΓ) a b K V
        else if suc (suc j) ==ℕ n then stripL wΓ (rec wΓ) n a b K V
        else nothing

      strips : Nat → TTm Γ → Maybe (TTm Γ)
      strips zero    V = just V
      strips (suc j) V = As j >>= λ where
        nothing  → strips j V
        (just K) → lo t j >>= λ a → lo u j >>= λ b → cut j a b K V >>= strips j

    transfer : Maybe (TTm Γ)
    transfer =
      liftG F G D t >>= λ wt →
      liftOpG F G D u >>= λ wu →
      midK n >>= λ m →
      comp2? n wt m >>= λ wm →
      comp2? n wm wu >>= strips n

  piece : TTm Γ → TTm Γ → Maybe (TTm Γ)
  piece t u =
    buildSub wΓ W (Jimg P) >>= λ J →
    R t >>= λ Rt → R u >>= λ Ru →
    rec wW Rt Ru >>= λ w →
    tables J (dimT t) (gens P) (tabs [] [] []) >>= λ tb →
    transfer (mkD wΓ (exp P) tb) t u (pullT J w)

  -- The answer, typed t ⇛ u by a decided equality of types.
  pieceA : ∀ {A t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
  pieceA {A} {t} {u} dt du =
    piece tt[ t ∶ A , dt ] tt[ u ∶ A , du ] >>= λ w →
    decTy (ty w) (arr A t u) >>= λ p →
    just (tm w , subst (Γ ⊢tm tm w ∶_) p (der w))
