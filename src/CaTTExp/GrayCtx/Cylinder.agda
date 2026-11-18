------------------------------------------------------------------------
-- Gray cylinders as a function on syntax.
--
-- For a CaTT context Γ and a path Pₚ = (0 → 1 → … → p) with p edges,
-- `cyl right p Γ` is the context Γ ⊗ Pₚ and `cyl left p Γ` is Pₚ ⊗ Γ,
-- in the Steiner / Ara–Maltsiniotis orientation. Generators are
--
--   x⊗c  (one copy of Γ for each vertex c of Pₚ)  and
--   x⊗eₑ (one cylinder generator for each x and each edge e),
--
-- with dim(x⊗eₑ) = dim x + 1. The type of a cylinder generator is the
-- composite of the boundary molecule given by Steiner's Leibniz rule
--   ∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y),
-- written as a whiskered binary composite (see notes/gray-cylinders.md
-- for the derivation of the recursive whiskerings L, R, L′, R′ below).
--
-- Scope. A boundary of a generator of Γ may be
--   * a variable (Γ globular, e.g. any pasting scheme), or
--   * a binary composite of 1-cells, recursively of such
--     (enough for Γ = D¹ ⊗ D¹, hence for the Gray cube).
-- For the latter, t ⊗ e is the layering of the two naturality squares
-- with associators (the G(2) construction of
-- notes/conjectures/gray-contexts-in-catt.md §3.2). Any other boundary
-- term makes `cyl` return nothing.
--
-- Nothing here is trusted: well-formedness of the output is established
-- by the certified checker (CaTTExp.GrayCtx.Checks).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Cylinder where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import Agda.Builtin.Nat using (_*_)

data Side : Set where
  right : Side   -- Γ ⊗ Pₚ   (generators x⊗e)
  left  : Side   -- Pₚ ⊗ Γ   (generators e⊗x)

------------------------------------------------------------------------
-- Layout. N = len Γ. Copy c of x sits at level c·N + x; the generator
-- of x over edge e (from vertex e to vertex e+1) at (p+1)·N + e·N + x.

cp : Nat → Nat → Nat → Nat
cp N c x = c * N + x

ed : Nat → Nat → Nat → Nat → Nat
ed N p e x = suc p * N + e * N + x

-- The renaming Γ → copy c.
ren : Nat → (Nat → Nat) → Sub
ren zero    f = ⟨⟩
ren (suc n) f = ren n f ,ₛ var (f n)

upto : Nat → List Nat
upto n = go n []
  where
  go : Nat → List Nat → List Nat
  go zero    acc = acc
  go (suc n) acc = go n (n ∷ acc)

foldM : ∀ {a} {A : Set a} → (Ctx → A → Maybe Ctx) → Ctx → List A → Maybe Ctx
foldM f Γ []       = just Γ
foldM f Γ (x ∷ xs) = f Γ x >>= λ Γ' → foldM f Γ' xs

odd : Nat → Bool
odd zero          = false
odd (suc zero)    = true
odd (suc (suc n)) = odd n

Comp₂T : Tree
Comp₂T = node (leaf ∷ leaf ∷ [])

------------------------------------------------------------------------
-- The generator types, over a fixed Γ, N, p, edge e, and the output
-- context Γ' built so far.

module Gen (sd : Side) (Γ : Ctx) (p e : Nat) (Γ' : Ctx) where
  N = len Γ
  a b : Nat → Nat
  a = cp N e
  b = cp N (suc e)

  copyA copyB : Tm → Tm
  copyA t = t [ ren N a ]tm
  copyB t = t [ ren N b ]tm

  -- t ⊗ e for a boundary term t of Γ.
  cylB : Nat → Tm → Maybe Tm
  cylB zero       _         = nothing
  cylB (suc fuel) (var x)   = just (var (ed N p e x))
  cylB (suc fuel) (coh Δ A (((((⟨⟩ ,ₛ x) ,ₛ y) ,ₛ u) ,ₛ z) ,ₛ v)) =
    guard (Δ ==Ctx ctxOf Comp₂T) λ _ →
    cylB fuel u >>= λ ue → cylB fuel v >>= λ ve →
    cylB fuel x >>= λ xe → cylB fuel y >>= λ ye → cylB fuel z >>= λ ze →
    let ua = copyA u ; va = copyA v ; ub = copyB u ; vb = copyB v in
    layers sd ue ve xe ye ze ua va ub vb >>= vcomp Γ'
    where
    layers : Side → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Maybe (List Tm)
    -- (u;v)⊗e : xₑ;(u;v)_b ⇒ (u;v)_a;zₑ
    layers right ue ve xe ye ze ua va ub vb =
      assoc⁻ Γ' xe ub vb >>= λ c₁ → (Γ' ▹ ue) vb >>= λ c₂ →
      assoc Γ' ua ye vb >>= λ c₃ → (Γ' ◃ ua) ve >>= λ c₄ →
      assoc⁻ Γ' ua va ze >>= λ c₅ → just (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ c₅ ∷ [])
    -- e⊗(u;v) : (u;v)_a;zₑ ⇒ xₑ;(u;v)_b
    layers left ue ve xe ye ze ua va ub vb =
      assoc Γ' ua va ze >>= λ c₁ → (Γ' ◃ ua) ve >>= λ c₂ →
      assoc⁻ Γ' ua ye vb >>= λ c₃ → (Γ' ▹ ue) vb >>= λ c₄ →
      assoc Γ' xe ub vb >>= λ c₅ → just (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ c₅ ∷ [])
  cylB (suc fuel) _ = nothing

  B : Tm → Maybe Tm
  B = cylB F

  -- The whiskerings. For y a cell of Γ of dimension m and c an m-cell
  -- parallel to a copy of y:
  --   right:  L_m^y c = R_{m−1}^{sy} c ▹ (t s y)⊗e,   R_m^y c = (s s y)⊗e ◃ L_{m−1}^{sy} c
  --   left:   L′_m^y c = L′_{m−1}^{sy} c ▹ (t s y)⊗e, R′_m^y c = (s s y)⊗e ◃ R′_{m−1}^{sy} c
  -- with L_1 = R_1 = L′_1 = R′_1 = identity.
  data Which : Set where L R : Which

  whisk : Nat → Which → Tm → Tm → Maybe Tm
  whisk zero _ _ _ = nothing
  whisk (suc fuel) w y c = dimOf Γ y >>= step
    where
    go : Side → Which → Tm → Tm → Tm → Maybe Tm
    go right L sy ssy tsy = whisk fuel R sy c >>= λ r → B tsy >>= λ z → (Γ' ▹ r) z
    go right R sy ssy tsy = whisk fuel L sy c >>= λ l → B ssy >>= λ z → (Γ' ◃ z) l
    go left  L sy ssy tsy = whisk fuel L sy c >>= λ l → B tsy >>= λ z → (Γ' ▹ l) z
    go left  R sy ssy tsy = whisk fuel R sy c >>= λ r → B ssy >>= λ z → (Γ' ◃ z) r
    step : Nat → Maybe Tm
    step zero          = nothing
    step (suc zero)    = just c
    step (suc (suc _)) =
      srcOf Γ y >>= λ sy → srcOf Γ sy >>= λ ssy → tgtOf Γ sy >>= λ tsy →
      go sd w sy ssy tsy

  -- The type of x⊗e (right) or e⊗x (left).
  genTy : Nat → Maybe Ty
  genTy x = lookup Γ x >>= gt
    where
    y = var x
    sides : Side → Nat → Tm → Tm → Maybe (List Tm × List Tm)
    -- ∂⁻(x⊗e) = (s x)⊗e ; L(x_ε),  ∂⁺(x⊗e) = R(x_ε′) ; (t x)⊗e,
    -- with ε = b, ε′ = a for m odd and ε = a, ε′ = b for m even.
    sides right m s t =
      let εS = if odd m then b x else a x
          εT = if odd m then a x else b x in
      B s >>= λ se → whisk F L y (var εS) >>= λ l →
      whisk F R y (var εT) >>= λ r → B t >>= λ te →
      just ((se ∷ l ∷ []) , (r ∷ te ∷ []))
    -- ∂⁻(e⊗x) = L′(x_a) ; (t x)⊗e,  ∂⁺(e⊗x) = (s x)⊗e ; R′(x_b).
    sides left m s t =
      whisk F L y (var (a x)) >>= λ l → B t >>= λ te →
      B s >>= λ se → whisk F R y (var (b x)) >>= λ r →
      just ((l ∷ te ∷ []) , (se ∷ r ∷ []))

    gt : Ty → Maybe Ty
    gt ⋆           = just (arr ⋆ (var (a x)) (var (b x)))
    gt (arr A s t) =
      sides sd (suc (dim A)) s t >>= λ st →
      vcomp Γ' (fst st) >>= λ S → vcomp Γ' (snd st) >>= λ T →
      tyOf Γ' S >>= λ C → just (arr C S T)

------------------------------------------------------------------------
-- The context.

cyl : Side → Nat → Ctx → Maybe Ctx
cyl sd p Γ =
  foldM copy ε (upto (suc p)) >>= λ Γc →
  foldM edge Γc (upto p)
  where
  N = len Γ
  copy : Ctx → Nat → Maybe Ctx
  copy Γ' c = foldM (λ Δ x → lookup Γ x >>= λ A → just (Δ ▸ (A [ ren N (cp N c) ]ty)))
                    Γ' (upto N)
  edge : Ctx → Nat → Maybe Ctx
  edge Γ' e = foldM (λ Δ x → Gen.genTy sd Γ p e Δ x >>= λ A → just (Δ ▸ A)) Γ' (upto N)

-- Γ ⊗ D¹ and D¹ ⊗ Γ.
_⊗D¹ D¹⊗_ : Ctx → Maybe Ctx
Γ ⊗D¹ = cyl right 1 Γ
D¹⊗ Γ = cyl left 1 Γ
