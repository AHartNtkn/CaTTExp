------------------------------------------------------------------------
-- A filler for localised graphs (open-issues F4a), on 1-cells.
--
-- Setting. Γ is a pure CaTT context containing a graph (objects, and
-- edges between object variables), together with *inverse data* for a
-- set M of its edges: for m : x → y,
--
--     m̄ : y → x,
--     ρ : m ; m̄ ⇒ 1_x     ρ̄ : 1_x ⇒ m ; m̄
--     λ : m̄ ; m ⇒ 1_y     λ̄ : 1_y ⇒ m̄ ; m
--
-- (composition in diagrammatic order, with the `comp` and `id` of
-- CaTTExp.GraphFiller's examples). This is the 2-dimensional part of a
-- walking equivalence on each m ∈ M, as in the localisation
-- ⟦L⟧[s⁻¹] of notes/ordinary-math.md §5.1. With the invertibility
-- marking of notes/invertibility-markings.md §1.2 the same data are the
-- destructors m⁻ˡ, m⁻ʳ, λ_m, ρ_m and their inverses; here they are
-- plain variables, so everything stays in plain CaTT.
--
-- The path of a 1-cell is now a word in the edges and the m̄. Its
-- *reduced word* cancels adjacent m m̄ and m̄ m. The tactic connects two
-- parallel 1-cells u, v with the same reduced word by a 2-cell
--
--   u ⇒ canon(path u) ⇒ … ⇒ canon(r) ⇒ … ⇒ canon(path v) ⇒ v
--
-- where canon(w) is the right-nested composite of the word w, the outer
-- steps are graph fillers (CaTTExp.GraphFiller, same path), each
-- forward step cancels one pair with a whiskered ρ or λ, and each
-- backward step inserts one with a whiskered ρ̄ or λ̄. A cancellation
-- step is itself graph filler ; whiskering ; graph filler. The 2-cells
-- are composed vertically.
--
-- As in the other fillers the output is raw syntax and the certified
-- checker decides it, so every returned cell is a CaTT derivation.
-- Cells between parallel 2-cells (needed for "the localisation is a
-- 1-category") are not constructed here; semantically they exist by
-- T-loc, and syntactically they need the higher walking-equivalence
-- data (ledger F4a, remaining part).
------------------------------------------------------------------------
module CaTTExp.LocalisedFiller where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.GraphFiller as GF

private
  v : Nat → Tm
  v = var

  reverse : List Nat → List Nat
  reverse = go []
    where
    go : List Nat → List Nat → List Nat
    go acc []       = acc
    go acc (x ∷ xs) = go (x ∷ acc) xs

  listEq : List Nat → List Nat → Bool
  listEq []       []       = true
  listEq (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ listEq xs ys
  listEq _        _        = false

  length : List Nat → Nat
  length []       = 0
  length (_ ∷ xs) = suc (length xs)

------------------------------------------------------------------------
-- The operations used (the same terms as CaTTExp.GraphFillerExamples).

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh (GF.chain 2) (arr ⋆ (v 0) (v 3)) ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

id : Tm → Tm
id x = coh (GF.chain 0) (arr ⋆ (v 0) (v 0)) ⟪ x ∷ [] ⟫

-- Vertical composite of α : f ⇒ g and β : g ⇒ h between a and b.
vcomp : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
vcomp a b f g α h β =
  coh (ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ [])))
      (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) ⟪ a ∷ b ∷ f ∷ g ∷ α ∷ h ∷ β ∷ [] ⟫

-- The identity 2-cell on f : a → b.
id₂ : Tm → Tm → Tm → Tm
id₂ a b f = coh (GF.chain 1) (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) ⟪ a ∷ b ∷ f ∷ [] ⟫

-- α ∗₀ g, for α : f ⇒ f' : a → b and g : b → c.
whR : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
whR a b f f' α c g =
  coh (ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ [])))
      (arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                               (comp (v 0) (v 1) (v 3) (v 5) (v 6)))
      ⟪ a ∷ b ∷ f ∷ f' ∷ α ∷ c ∷ g ∷ [] ⟫

-- f ∗₀ β, for f : a → b and β : g ⇒ g' : b → c.
whL : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
whL a b f c g g' β =
  coh (ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ [])))
      (arr (arr ⋆ (v 0) (v 3)) (comp (v 0) (v 1) (v 2) (v 3) (v 4))
                               (comp (v 0) (v 1) (v 2) (v 3) (v 5)))
      ⟪ a ∷ b ∷ f ∷ c ∷ g ∷ g' ∷ β ∷ [] ⟫

------------------------------------------------------------------------
-- Inverse data.

record InvData : Set where
  constructor invd
  field
    m mb rho rhob lam lamb : Nat     -- levels of m, m̄, ρ, ρ̄, λ, λ̄ in Γ

open InvData

-- If e e' is a cancellable pair, the cell that cancels it and the one
-- that inserts it.
cancels : List InvData → Nat → Nat → Maybe (Nat × Nat)
cancels []       e e' = nothing
cancels (d ∷ ds) e e' =
  if (e ==ℕ m d) ∧ (e' ==ℕ mb d) then just (rho d , rhob d)
  else if (e ==ℕ mb d) ∧ (e' ==ℕ m d) then just (lam d , lamb d)
  else cancels ds e e'

-- The first cancellable pair: prefix, the pair, suffix, and its cells.
record Redex : Set where
  constructor redex
  field
    pre : List Nat
    e₁ e₂ : Nat
    post : List Nat
    kill fill′ : Nat

findRedex : List InvData → List Nat → Maybe Redex
findRedex ds []      = nothing
findRedex ds (e ∷ w) = go [] e w
  where
  go : List Nat → Nat → List Nat → Maybe Redex
  go acc e []        = nothing
  go acc e (e' ∷ w) with cancels ds e e'
  ... | just (c , cb) = just (redex (reverse acc) e e' w c cb)
  ... | nothing       = go (e ∷ acc) e' w

-- All the cancellation steps, and the reduced word.
reduce : List InvData → Nat → List Nat → List Redex × List Nat
reduce ds zero    w = [] , w
reduce ds (suc n) w with findRedex ds w
... | nothing = [] , w
... | just r  with reduce ds n (Redex.pre r ++ Redex.post r)
...   | (rs , red) = r ∷ rs , red

------------------------------------------------------------------------
-- Words and their canonical composites.

tgtE : Ctx → Nat → Maybe Nat
tgtE Γ e with lookup Γ e
... | just (arr ⋆ _ (var b)) = just b
... | _ = nothing

endW : Ctx → Nat → List Nat → Maybe Nat
endW Γ a []      = just a
endW Γ a (e ∷ w) = tgtE Γ e >>= λ b → endW Γ b w

canon : Ctx → Nat → List Nat → Maybe Tm
canon Γ a []          = just (id (v a))
canon Γ a (e ∷ [])    = just (v e)
canon Γ a (e ∷ e' ∷ w) =
  tgtE Γ e >>= λ b →
  canon Γ b (e' ∷ w) >>= λ t →
  endW Γ b (e' ∷ w) >>= λ c →
  just (comp (v a) (v b) (v e) (v c) t)

------------------------------------------------------------------------
-- One step, as a list of 2-cells (source, target, cell), all between
-- a and the end of the word.

record Cell : Set where
  constructor cell
  field
    from to it : Tm

-- canon(P ++ e e' ++ S) ⇒ canon(P ++ S), or the reverse when `back`.
step : Ctx → Nat → Redex → Bool → Maybe (List Cell)
step Γ a (redex P e e' S c cb) back =
  endW Γ a P >>= λ ai →
  tgtE Γ e >>= λ b →
  endW Γ ai S >>= λ d →
  canon Γ a P >>= λ tP →
  canon Γ ai S >>= λ tS →
  canon Γ a (P ++ e ∷ e' ∷ S) >>= λ long →
  canon Γ a (P ++ S) >>= λ short →
  let f   = comp (v ai) (v b) (v e) (v ai) (v e')
      g   = id (v ai)
      X   = comp (v a) (v ai) tP (v d) (comp (v ai) (v ai) f (v d) tS)
      Y   = comp (v a) (v ai) tP (v d) (comp (v ai) (v ai) g (v d) tS)
      AB  = arr ⋆ (v a) (v d)
      wh  = λ (α s t : Tm) → whL (v a) (v ai) tP (v d) (comp (v ai) (v ai) s (v d) tS)
                               (comp (v ai) (v ai) t (v d) tS)
                               (whR (v ai) (v ai) s t α (v d) tS)
  in go back long short X Y AB (wh (v c) f g) (wh (v cb) g f)
  where
  go : Bool → Tm → Tm → Tm → Tm → Ty → Tm → Tm → Maybe (List Cell)
  go false long short X Y AB kill _ =
    GF.fillRaw Γ long X AB >>= λ c₁ →
    GF.fillRaw Γ Y short AB >>= λ c₂ →
    just (cell long X c₁ ∷ cell X Y kill ∷ cell Y short c₂ ∷ [])
  go true long short X Y AB _ ins =
    GF.fillRaw Γ short Y AB >>= λ c₁ →
    GF.fillRaw Γ X long AB >>= λ c₂ →
    just (cell short Y c₁ ∷ cell Y X ins ∷ cell X long c₂ ∷ [])

-- The steps of a reduction sequence, forward or backward.
steps : Ctx → Nat → List Redex → Bool → Maybe (List Cell)
steps Γ a []       back = just []
steps Γ a (r ∷ rs) back =
  step Γ a r back >>= λ cs →
  steps Γ a rs back >>= λ ds →
  just (if back then ds ++ cs else cs ++ ds)

-- Vertical composite of a chain of 2-cells from t₀, between a and b.
vchain : Tm → Tm → Tm → List Cell → Tm
vchain a b t₀ [] = id₂ a b t₀
vchain a b t₀ (cell s t c ∷ cs) = go t c cs
  where
  go : Tm → Tm → List Cell → Tm
  go cur acc []                  = acc
  go cur acc (cell _ t′ c′ ∷ cs) = go t′ (vcomp a b t₀ cur acc t′ c′) cs

------------------------------------------------------------------------
-- The tactic.

fuel : Nat
fuel = 64

fillRaw : Ctx → List InvData → Tm → Tm → Ty → Maybe Tm
fillRaw Γ ds u v′ (arr ⋆ (var a) (var b)) =
  GF.pathTm fuel Γ u  >>= λ p →
  GF.pathTm fuel Γ v′ >>= λ q →
  let (ru , r)  = reduce ds (length p) p
      (rv , r′) = reduce ds (length q) q
  in guard (listEq r r′) λ _ →
  canon Γ a p >>= λ cp →
  canon Γ a q >>= λ cq →
  GF.fillRaw Γ u cp (arr ⋆ (v a) (v b)) >>= λ c₀ →
  GF.fillRaw Γ cq v′ (arr ⋆ (v a) (v b)) >>= λ c₃ →
  steps Γ a ru false >>= λ fw →
  steps Γ a rv true  >>= λ bw →
  just (vchain (v a) (v b) u (cell u cp c₀ ∷ fw ++ bw ++ cell cq v′ c₃ ∷ []))
fillRaw Γ ds u v′ _ = nothing

-- Certified filler: if it returns, the result is a derivation of
-- Γ ⊢ fill ∶ u →_A v in plain CaTT.
fill : (Γ : Ctx) → List InvData → (u v : Tm) (A : Ty) →
       Maybe (Σ Tm (λ c → Γ ⊢tm c ∶ arr A u v))
fill Γ ds u v′ A =
  fillRaw Γ ds u v′ A >>= λ c →
  infer Γ c >>= λ { (B , d) → cast B c d (B ==Ty arr A u v′) (==Ty-sound B (arr A u v′)) }
  where
  cast : ∀ B c → Γ ⊢tm c ∶ B → (b : Bool) → (T b → B ≡ arr A u v′) →
         Maybe (Σ Tm (λ c → Γ ⊢tm c ∶ arr A u v′))
  cast B c d true  eq = just (c , subst (Γ ⊢tm c ∶_) (eq tt) d)
  cast B c d false _  = nothing
