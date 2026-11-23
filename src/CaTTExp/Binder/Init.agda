------------------------------------------------------------------------
-- INIT (spec §9.3, syntax §1.1) as an instance of the binder
-- interface: six binding formers over a telescope X. Δ, a decidable
-- positivity check, and the stability laws (CaTTExp.Binder.Laws).
--
-- The telescope Δ of every former opens with its sort variables
-- X₀, …, X_{n-1} : ⋆ (n ≥ 1; spec §9.3 "several sorts", here all over
-- ⊤), followed by maps and cells A_n, …, A_{m-1}; entry j is bvar 0 j.
-- Writing μ_k for bnd μ k Δ ⟨⟩ and ηT y for bnd η y Δ ⟨⟩, the generic
-- model is η = ⟨μ_0, …, μ_{n-1}, ηT n, …, ηT (m-1)⟩, and a model is a
-- list of arguments for the telescope Δ itself (carriers, then the
-- rest). μ, rec and uni are indexed by a sort k < n; η, rec_y and uni_y
-- by an entry y ≥ n. With one sort this is the single-sorted rule.
--
--   former  arguments (bargs)          type (bres), bvar 0 j = argument j
--   μ_k     none                       ⋆
--   η_y     none                       A_y opened at η
--   rec_k   a model (A, σ) : Δ         μ_k → A_k
--   rec_y   a model (A, σ) : Δ         the cell of rec at y (below)
--   uni_k   a model, and two model     h_k ⇒ h′_k, the 2-cell between
--           morphisms (h, θ), (h′, θ′)  the carrier maps at sort k
--           from η to it
--   uni_y   the same                   the compatibility 3-cell at y
--
-- The cell of a model morphism h : A₁ → A₂ at a map variable
-- y : S → T is
--
--   s¹_y ; T(h)  ⇒  S(h) ; s²_y      (an arrow S¹ → T² in the ambient)
--
-- where T(h) = h_k if T is the sort X_k and the identity of T otherwise (likewise
-- S(h)). For uni_y, with u : h ⇒ h′ the cell uni and T(u) = u or an
-- identity 2-cell, the two sides are
--
--   (η_y ◁ T(u)) · θ′_y     and     θ_y · (S(u) ▷ σ_y).
--
-- Composites, whiskerings and identities are coherences over the usual
-- pasting contexts. INIT's model-morphism cells are meant invertible;
-- the types here carry no `inv`: that INIT's cells are inv belongs to
-- the kernel's mark judgment (spec chapter 3; ledger S26e).
--
-- Positivity (`positive`). This instance's fragment of §9.3's check,
-- for the object terms the Agda kernel has (variables, constants,
-- binders; it has no limit or colimit formers yet):
--   * the leading entries are the sorts X_k : ⋆ (at least one), and no
--     later entry is an object;
--   * every other entry is a map or a cell (of any dimension) whose
--     underlying arrow type is S → T with
--       S a sort, or S mentions no variable bound by the telescope;
--       T a sort, or T mentions no variable bound by the telescope;
--   * sorts over bases (`basedOK`): the X-free targets allowed are ⊤
--     (a constant the base marks as ⊤), the base B_k of a structure
--     map p : X_k → B_k in the header right after the sorts, and the
--     target of a companion cell c : a ; p_k ⇒ s (marked inv), which
--     must follow every operation a into a based sort X_k (see the
--     block before `positive`);
--   * marks (spec §9.3): a sort may be marked grpd_k or ⋆^{≤n}
--     (S¹ = μ(X : grpd, b, l : b ⇒ b), ‖A‖_n = μ(X : ⋆^{≤n}, g : A → X)),
--     and an operation or cell may be marked inv (ℤ = μ(X, z, s inv)).
--     A model is an argument list for Δ itself, so the kernel's mark
--     premise makes it certify every mark. That μ_k and the generic
--     model η carry the marks of Δ is the mark judgment's business
--     (ledger S26d/S26e).
-- The arrow context Δ^→ (model morphisms) is stated at maps and at
-- globular 2-cells l : f ⇒ g between map entries f, g, where its
-- component is a 3-cell between the two pastings of the naturality
-- square (`cell3Ty`). So rec_y needs entry y to be a map or a globular
-- 2-cell; uni needs every entry after X to be one; uni_y needs that and
-- entry y one too. At a map y, uni_y's type is a 3-cell; at a 2-cell
-- l : f ⇒ g it is a 4-cell between two pastings of 3-cells (`mod4`,
-- the modification condition built from θ_l, θ′_l, uni_f and uni_g).
-- Cells of higher dimension, or with composite boundaries, are accepted
-- by μ, η_y and rec only (ledger S26b).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.Init where

data Former : Set where
  μ η rec recY uni uniY : Former

private
  code : Former → Nat
  code μ    = 0
  code η    = 1
  code rec  = 2
  code recY = 3
  code uni  = 4
  code uniY = 5

  decode : Nat → Former
  decode 0 = μ
  decode 1 = η
  decode 2 = rec
  decode 3 = recY
  decode 4 = uni
  decode _ = uniY

  decode-code : ∀ b → decode (code b) ≡ b
  decode-code μ    = refl
  decode-code η    = refl
  decode-code rec  = refl
  decode-code recY = refl
  decode-code uni  = refl
  decode-code uniY = refl

_==F_ : Former → Former → Bool
b ==F c = code b ==ℕ code c

==F-sound : ∀ b c → T (b ==F c) → b ≡ c
==F-sound b c p = trans (sym (decode-code b)) (trans (cong decode (==ℕ-sound _ _ p)) (decode-code c))

==F-refl : ∀ b → T (b ==F b)
==F-refl b = ==ℕ-refl (code b)

------------------------------------------------------------------------
-- The construction, over constants K, with a test for ⊤.

module Construction (K : Set) (top? : K → Bool) where

  open Syntax K Former

  -- Lists of terms, left to right.
  ⟪_⟫ : List Tm → Sub
  ⟪ ts ⟫ = go ⟨⟩ ts
    where
    go : Sub → List Tm → Sub
    go σ []       = σ
    go σ (t ∷ ts) = go (σ ,ₛ t) ts

  ----------------------------------------------------------------------
  -- Pasting contexts and coherences used by the types.

  private
    v : Nat → Tm
    v = var

  PC0 PC1 PC2 PCv PClw PCrw : Ctx
  PC0  = ε ▸ ⋆
  PC1  = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)
  PC2  = PC1 ▸ ⋆ ▸ arr ⋆ (v 1) (v 3)
  PCv  = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5)
  PClw = PC2 ▸ arr ⋆ (v 1) (v 3) ▸ arr (arr ⋆ (v 1) (v 3)) (v 4) (v 5)
  PCrw = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ ⋆ ▸ arr ⋆ (v 1) (v 5)

  -- f ; g for f : a → b, g : b → c.
  cmp : Tm → Tm → Tm → Tm → Tm → Tm
  cmp a b c f g = coh PC2 (arr ⋆ (v 0) (v 3)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g)

  -- The identity of an object, and the identity 2-cell of a map.
  idm : Tm → Tm
  idm a = coh PC0 (arr ⋆ (v 0) (v 0)) (⟨⟩ ,ₛ a)

  id2 : Tm → Tm → Tm → Tm
  id2 a b f = coh PC1 (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f)

  -- α · β for α : f ⇒ g, β : g ⇒ h between maps a → b.
  vcomp : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  vcomp a b f g α h β =
    coh PCv (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ g ,ₛ α ,ₛ h ,ₛ β)

  -- f ◁ α for f : a → b, α : g ⇒ g′ between maps b → c.
  lwh : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  lwh a b c f g g′ α =
    coh PClw (arr (arr ⋆ (v 0) (v 3)) (cmp (v 0) (v 1) (v 3) (v 2) (v 4)) (cmp (v 0) (v 1) (v 3) (v 2) (v 5)))
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ c ,ₛ g ,ₛ g′ ,ₛ α)

  -- α ▷ g for α : f ⇒ f′ between maps a → b, g : b → c.
  rwh : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  rwh a b c f f′ α g =
    coh PCrw (arr (arr ⋆ (v 0) (v 5)) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 6)))
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ f ,ₛ f′ ,ₛ α ,ₛ c ,ₛ g)

  ----------------------------------------------------------------------
  -- Cells of dimension 3 between 2-cells of maps x → y, for uni_y at a
  -- 2-cell (below). Each is a coherence over a pasting context.

  PCwl PCwr PCas PCic PCv3 : Ctx
  -- x, y, z, a, α : z ⇒ a, b, P Q : a ⇒ b, Θ : P ⇛ Q
  PCwl = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5)
             ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5)
             ▸ arr (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5)) (v 6) (v 7)
  -- x, y, a, b, P Q : a ⇒ b, Θ : P ⇛ Q, c, β : b ⇒ c
  PCwr = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 4) (v 5)
             ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 7)
  -- x, y, a, b, α, c, β, d, γ : c ⇒ d
  PCas = PCv ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 5) (v 7)
  -- a, b, p, q, α : p ⇒ q, c, r, s, β : r ⇒ s
  PCic = PCrw ▸ arr ⋆ (v 1) (v 5) ▸ arr (arr ⋆ (v 1) (v 5)) (v 6) (v 7)
  -- x, y, a, b, P, Q, Θ : P ⇛ Q, R, Θ′ : Q ⇛ R
  PCv3 = PC1 ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 4) (v 5)
             ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
             ▸ arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 5) (v 7)

  -- α · Θ : α · P ⇛ α · Q.
  wL3 : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  wL3 x y z a α b P Q Θ =
    coh PCwl (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5))
                  (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
                  (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7)))
        (⟨⟩ ,ₛ x ,ₛ y ,ₛ z ,ₛ a ,ₛ α ,ₛ b ,ₛ P ,ₛ Q ,ₛ Θ)

  -- Θ · β : P · β ⇛ Q · β.
  wR3 : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  wR3 x y a b P Q Θ c β =
    coh PCwr (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7))
                  (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8))
                  (vcomp (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8)))
        (⟨⟩ ,ₛ x ,ₛ y ,ₛ a ,ₛ b ,ₛ P ,ₛ Q ,ₛ Θ ,ₛ c ,ₛ β)

  -- (α · β) · γ ⇛ α · (β · γ), and back.
  asc ascI : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  asc x y a b α c β d γ =
    coh PCas (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7)) ascL ascR)
        (⟨⟩ ,ₛ x ,ₛ y ,ₛ a ,ₛ b ,ₛ α ,ₛ c ,ₛ β ,ₛ d ,ₛ γ)
    where
    ascL = vcomp (v 0) (v 1) (v 2) (v 5) (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) (v 7) (v 8)
    ascR = vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (vcomp (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8))
  ascI x y a b α c β d γ =
    coh PCas (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7)) ascR ascL)
        (⟨⟩ ,ₛ x ,ₛ y ,ₛ a ,ₛ b ,ₛ α ,ₛ c ,ₛ β ,ₛ d ,ₛ γ)
    where
    ascL = vcomp (v 0) (v 1) (v 2) (v 5) (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) (v 7) (v 8)
    ascR = vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (vcomp (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8))

  -- Interchange, for α : p ⇒ q (maps a → b) and β : r ⇒ s (maps b → c):
  --   ich1 : (α ▷ r) · (q ◁ β) ⇛ (p ◁ β) · (α ▷ s),   ich2 the converse.
  ich1 ich2 : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  ich1 a b c p q α r s β =
    coh PCic (arr (arr (arr ⋆ (v 0) (v 5)) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7)))
                  ichL ichR)
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ p ,ₛ q ,ₛ α ,ₛ c ,ₛ r ,ₛ s ,ₛ β)
    where
    ichL = vcomp (v 0) (v 5) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 6))
                 (rwh (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7))
                 (lwh (v 0) (v 1) (v 5) (v 3) (v 6) (v 7) (v 8))
    ichR = vcomp (v 0) (v 5) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 2) (v 7))
                 (lwh (v 0) (v 1) (v 5) (v 2) (v 6) (v 7) (v 8)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7))
                 (rwh (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) (v 7))
  ich2 a b c p q α r s β =
    coh PCic (arr (arr (arr ⋆ (v 0) (v 5)) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7)))
                  ichR ichL)
        (⟨⟩ ,ₛ a ,ₛ b ,ₛ p ,ₛ q ,ₛ α ,ₛ c ,ₛ r ,ₛ s ,ₛ β)
    where
    ichL = vcomp (v 0) (v 5) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 6))
                 (rwh (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) (v 6)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7))
                 (lwh (v 0) (v 1) (v 5) (v 3) (v 6) (v 7) (v 8))
    ichR = vcomp (v 0) (v 5) (cmp (v 0) (v 1) (v 5) (v 2) (v 6)) (cmp (v 0) (v 1) (v 5) (v 2) (v 7))
                 (lwh (v 0) (v 1) (v 5) (v 2) (v 6) (v 7) (v 8)) (cmp (v 0) (v 1) (v 5) (v 3) (v 7))
                 (rwh (v 0) (v 1) (v 5) (v 2) (v 3) (v 4) (v 7))

  -- Θ ; Θ′ : P ⇛ R for Θ : P ⇛ Q, Θ′ : Q ⇛ R.
  v3 : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
  v3 x y a b P Q Θ R Θ′ =
    coh PCv3 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 4) (v 7))
        (⟨⟩ ,ₛ x ,ₛ y ,ₛ a ,ₛ b ,ₛ P ,ₛ Q ,ₛ Θ ,ₛ R ,ₛ Θ′)

  -- The modification condition at a 2-cell l : f ⇒ g between maps
  -- S → T (uni_y at l), from its data in the ambient: the boundaries
  -- s₁ s₂ t₁ t₂ (S and T in the two models), f, g, l in both models,
  -- the actions th, th′ (of h, h′ on T), sh, sh′ (on S), tu, su (of
  -- u : h ⇒ h′), the cells θ_f, θ_g, θ′_f, θ′_g, the 3-cells θ_l, θ′_l,
  -- and the 3-cells uni_f, uni_g. A 4-cell between two pastings of
  --   (l₁ ▷ Th) · ((g₁ ◁ Tu) · θ′_g)   ⇛   θ_f · ((Su ▷ f₂) · (Sh′ ◁ l₂)):
  --   P₁ = interchange at (l₁, Tu), then θ′_l, then uni_f;
  --   P₂ = uni_g, then θ_l, then interchange at (Su, l₂);
  -- with the associators between them.
  mod4 : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm →
         Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Ty
  mod4 s₁ s₂ t₁ t₂ f₁ g₁ l₁ f₂ g₂ l₂ th th′ sh sh′ tu su θf θg θf′ θg′ θl θl′ uf ug =
    arr (arr (arr (arr ⋆ s₁ t₂) F Sh′g) Q0 Q7) P1 P2
    where
    vc : Tm → Tm → Tm → Tm → Tm → Tm
    vc X Y Z α β = vcomp s₁ t₂ X Y α Z β
    F    = cmp s₁ t₁ t₂ f₁ th
    G    = cmp s₁ t₁ t₂ g₁ th
    G′   = cmp s₁ t₁ t₂ g₁ th′
    F′   = cmp s₁ t₁ t₂ f₁ th′
    Shf  = cmp s₁ s₂ t₂ sh f₂
    Shg  = cmp s₁ s₂ t₂ sh g₂
    Sh′f = cmp s₁ s₂ t₂ sh′ f₂
    Sh′g = cmp s₁ s₂ t₂ sh′ g₂
    A1   = rwh s₁ t₁ t₂ f₁ g₁ l₁ th
    B1   = lwh s₁ t₁ t₂ g₁ th th′ tu
    C1   = lwh s₁ t₁ t₂ f₁ th th′ tu
    D1   = rwh s₁ t₁ t₂ f₁ g₁ l₁ th′
    E2   = lwh s₁ s₂ t₂ sh f₂ g₂ l₂
    F2   = rwh s₁ s₂ t₂ sh sh′ su g₂
    G2   = rwh s₁ s₂ t₂ sh sh′ su f₂
    H2   = lwh s₁ s₂ t₂ sh′ f₂ g₂ l₂
    Bθ′g = vc G G′ Sh′g B1 θg′
    θgF2 = vc G Shg Sh′g θg F2
    A1θg = vc F G Shg A1 θg
    θfE2 = vc F Shf Shg θf E2
    E2F2 = vc Shf Shg Sh′g E2 F2
    G2H2 = vc Shf Sh′f Sh′g G2 H2
    A1B1 = vc F G G′ A1 B1
    C1D1 = vc F F′ G′ C1 D1
    D1θ′g = vc F′ G′ Sh′g D1 θg′
    θ′fH2 = vc F′ Sh′f Sh′g θf′ H2
    C1θ′f = vc F F′ Sh′f C1 θf′
    θfG2 = vc F Shf Sh′f θf G2
    Q0 = vc F G Sh′g A1 Bθ′g
    Q1 = vc F G′ Sh′g A1B1 θg′
    Q2 = vc F G′ Sh′g C1D1 θg′
    Q3 = vc F F′ Sh′g C1 D1θ′g
    Q4 = vc F F′ Sh′g C1 θ′fH2
    Q5 = vc F Sh′f Sh′g C1θ′f H2
    Q6 = vc F Sh′f Sh′g θfG2 H2
    Q7 = vc F Shf Sh′g θf G2H2
    R1 = vc F G Sh′g A1 θgF2
    R2 = vc F Shg Sh′g A1θg F2
    R3 = vc F Shg Sh′g θfE2 F2
    R4 = vc F Shf Sh′g θf E2F2
    vv : Tm → Tm → Tm → Tm → Tm
    vv P Q Θ Θ′ = v3 s₁ t₂ F Sh′g P Q Θ Q7 Θ′
    t1 = ascI s₁ t₂ F G A1 G′ B1 Sh′g θg′
    t2 = wR3 s₁ t₂ F G′ A1B1 C1D1 (ich1 s₁ t₁ t₂ f₁ g₁ l₁ th th′ tu) Sh′g θg′
    t3 = asc s₁ t₂ F F′ C1 G′ D1 Sh′g θg′
    t4 = wL3 s₁ t₂ F F′ C1 Sh′g D1θ′g θ′fH2 θl′
    t5 = ascI s₁ t₂ F F′ C1 Sh′f θf′ Sh′g H2
    t6 = wR3 s₁ t₂ F Sh′f C1θ′f θfG2 uf Sh′g H2
    t7 = asc s₁ t₂ F Shf θf Sh′f G2 Sh′g H2
    s1 = wL3 s₁ t₂ F G A1 Sh′g Bθ′g θgF2 ug
    s2 = ascI s₁ t₂ F G A1 Shg θg Sh′g F2
    s3 = wR3 s₁ t₂ F Shg A1θg θfE2 θl Sh′g F2
    s4 = asc s₁ t₂ F Shf θf Shg E2 Sh′g F2
    s5 = wL3 s₁ t₂ F Shf θf Sh′g E2F2 G2H2 (ich2 s₁ s₂ t₂ sh sh′ su f₂ g₂ l₂)
    P1 = vv Q0 Q1 t1 (vv Q1 Q2 t2 (vv Q2 Q3 t3 (vv Q3 Q4 t4 (vv Q4 Q5 t5 (vv Q5 Q6 t6 t7)))))
    P2 = vv Q0 R1 s1 (vv R1 R2 s2 (vv R2 R3 s3 (vv R3 R4 s4 s5)))

  ----------------------------------------------------------------------
  -- Sorts. The telescope opens with its sort variables X₀, …, X_{m-1},
  -- the leading entries of type ⋆; `sorts Δ` is m.

  isStar : Ty → Bool
  isStar ⋆           = true
  isStar (arr _ _ _) = false

  sorts : Ctx → Nat
  sorts ε       = 0
  sorts (Δ ▸[ _ ] A) = if (sorts Δ ==ℕ len Δ) ∧ isStar A then suc (len Δ) else sorts Δ

  -- Which sort a term is, if it is one.
  srt : Nat → Tm → Maybe Nat
  srt m (bvar zero j) = if j <ℕ m then just j else nothing
  srt m _             = nothing

  isSort : Nat → Tm → Bool
  isSort m t = is-just (srt m t)

  ----------------------------------------------------------------------
  -- Positivity.

  isTop? : Tm → Bool
  isTop? (cst k) = top? k
  isTop? _       = false

  -- Does the syntax mention a variable of the binder at depth d?
  mutual
    mTy : Nat → Ty → Bool
    mTy d ⋆           = false
    mTy d (arr A t u) = mTy d A ∨ mTm d t ∨ mTm d u

    mTm : Nat → Tm → Bool
    mTm d (var _)       = false
    mTm d (bvar e _)    = e ==ℕ d
    mTm d (coh _ _ σ)   = mSub d σ
    mTm d (cst _)       = false
    mTm d (bnd _ _ Δ σ) = mTel (suc d) Δ ∨ mSub d σ

    mTel : Nat → Ctx → Bool
    mTel d ε       = false
    mTel d (Δ ▸[ _ ] A) = mTel d Δ ∨ mTy d A

    mSub : Nat → Sub → Bool
    mSub d ⟨⟩       = false
    mSub d (σ ,ₛ t) = mSub d σ ∨ mTm d t

  srcOK tgtOK : Nat → Tm → Bool
  srcOK m S = isSort m S ∨ not (mTm 0 S)
  tgtOK m T = isSort m T ∨ not (mTm 0 T)

  -- The underlying arrow S → T of a map or cell type.
  base : Ty → Maybe (Tm × Tm)
  base ⋆                       = nothing
  base (arr ⋆ s t)             = just (s , t)
  base (arr (arr A a b) _ _)   = base (arr A a b)

  okBase : Nat → Maybe (Tm × Tm) → Bool
  okBase m nothing        = false
  okBase m (just (S , T)) = srcOK m S ∧ tgtOK m T

  entryOK : Nat → Ty → Bool
  entryOK m A = okBase m (base A)

  -- Marks (spec §9.3): a sort may be restricted to a reflective class
  -- closed under limits and filtered colimits, `grpd_k` or ⋆^{≤n}; an
  -- operation or cell may be marked inv.
  isInvMark isSortMark : Mark → Bool
  isInvMark minv = true
  isInvMark _    = false
  isSortMark (mgrpd _)  = true
  isSortMark (mtrunc _) = true
  isSortMark _          = false

  marksOKAt : Nat → Nat → List Mark → Bool
  marksOKAt m j ms = if j <ℕ m then all isSortMark ms else all isInvMark ms

  -- Every entry after the sorts is a map or cell with a good base, and
  -- marks are as above.
  posFrom : Nat → Ctx → Bool
  posFrom m ε             = true
  posFrom m (Δ ▸[ ms ] A) = posFrom m Δ ∧ marksOKAt m (len Δ) ms ∧ ((len Δ <ℕ m) ∨ entryOK m A)

  -- A variable of the binder at depth 0, other than through a parameter.
  bv0? : Tm → Maybe Nat
  bv0? (bvar zero j) = just j
  bv0? _             = nothing

  both : Maybe Nat → Maybe Nat → Maybe (Nat × Nat)
  both (just i) (just j) = just (i , j)
  both _        _        = nothing

  -- A globular 2-cell between two earlier entries: f ⇒ g for f, g : S → T
  -- variables of the telescope. Returns the entries of f and g.
  glob : Ty → Maybe (Nat × Nat)
  glob ⋆                               = nothing
  glob (arr ⋆ _ _)                     = nothing
  glob (arr (arr ⋆ _ _) f g)           = both (bv0? f) (bv0? g)
  glob (arr (arr (arr _ _ _) _ _) _ _) = nothing

  -- Entries whose model-morphism component the kernel states: maps, and
  -- globular 2-cells (ledger S26b for the rest).
  low : Ty → Bool
  low A = (dim A ==ℕ 1) ∨ is-just (glob A)

  -- Every entry after the sorts is low.
  lowFrom : Nat → Ctx → Bool
  lowFrom m ε       = true
  lowFrom m (Δ ▸[ _ ] A) = lowFrom m Δ ∧ ((len Δ <ℕ m) ∨ low A)

  isLow? : Maybe Ty → Bool
  isLow? nothing  = false
  isLow? (just A) = low A

  isMap? : Maybe Ty → Bool
  isMap? nothing  = false
  isMap? (just A) = dim A ==ℕ 1

  ----------------------------------------------------------------------
  -- Targets, and sorts over bases (spec §9.3 "several sorts, over
  -- bases"; the syntax of notes/higher-inductive.md §8 as fixed by the
  -- HIT thread). `posFrom` checks sources, and that targets are sorts or
  -- X-free. `basedOK` checks which X-free targets are allowed:
  --
  --   * the header: right after the sorts, structure maps p : X_k → B_k
  --     (B_k X-free; at most one per sort, in increasing order of k).
  --     X_k is then a sort over the base B_k;
  --   * in the body, an X-free target must be ⊤, unless the entry is
  --     the companion cell of an operation (below);
  --   * an operation a : S → X_k into a based sort must be a map (not a
  --     cell), followed by its companion c : a ; p_k ⇒ s marked inv,
  --     where s : S → B_k is a term (not a new variable: a definition,
  --     so that a is a map S → s*X_k into a pullback of X_k).
  --
  -- The companion's source is recognised as the binary composite of
  -- a and p_k (a coherence over PC2 with arguments S, X_k, a, B_k, p_k);
  -- that its types fit is the telescope's typing premise. Cells of
  -- dimension ≥ 2 into a based sort are not accepted yet (ledger S26c).

  baseOf : Maybe Ty → Maybe (Tm × Tm)
  baseOf nothing  = nothing
  baseOf (just A) = base A

  entryBase : Ctx → Nat → Maybe (Tm × Tm)
  entryBase Δ y = baseOf (lookup Δ y)

  -- A header entry X_k → B (B X-free): k.
  hdrShape : Nat → Ty → Maybe Nat
  hdrShape n ⋆                     = nothing
  hdrShape n (arr ⋆ S B)           = if mTm 0 B then nothing else srt n S
  hdrShape n (arr (arr _ _ _) _ _) = nothing

  isPC2 : Ctx → Bool
  isPC2 (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)) = true
  isPC2 _ = false

  isCmpTy : Ty → Bool
  isCmpTy (arr ⋆ (var 0) (var 3)) = true
  isCmpTy _                       = false

  tri : Maybe Nat → Maybe Nat → Maybe Nat → Maybe (Nat × Nat × Nat)
  tri (just x) (just y) (just z) = just (x , y , z)
  tri _        _        _        = nothing

  -- The arguments X_k, a, p of a binary composite S → X_k → B.
  cmpSub : Sub → Maybe (Nat × Nat × Nat)
  cmpSub (⟨⟩ ,ₛ _ ,ₛ x ,ₛ a ,ₛ _ ,ₛ q) = tri (bv0? x) (bv0? a) (bv0? q)
  cmpSub _                             = nothing

  cmpTm : Tm → Maybe (Nat × Nat × Nat)
  cmpTm (coh Γ A τ) = if isPC2 Γ ∧ isCmpTy A then cmpSub τ else nothing
  cmpTm _           = nothing

  -- A companion cell (a ; p) ⇒ s between maps: (k, a, p).
  cmpShape : Ty → Maybe (Nat × Nat × Nat)
  cmpShape (arr (arr ⋆ _ _) u _) = cmpTm u
  cmpShape _                     = nothing

  -- Per-entry data, as functions of the index.
  mapMT : ∀ {X : Set} → (Ty → X) → X → Maybe Ty → X
  mapMT f d nothing  = d
  mapMT f d (just A) = f A

  tgtSrtB : Nat → Maybe (Tm × Tm) → Maybe Nat
  tgtSrtB n nothing        = nothing
  tgtSrtB n (just (_ , T)) = srt n T

  tgtTopB : Maybe (Tm × Tm) → Bool
  tgtTopB nothing        = false
  tgtTopB (just (_ , T)) = isTop? T

  record Info : Set where
    field
      hs : Nat → Maybe Nat                -- header shape
      ts : Nat → Maybe Nat                -- target sort
      tp : Nat → Bool                     -- target ⊤
      dm : Nat → Nat                      -- dimension
      cm : Nat → Maybe (Nat × Nat × Nat)  -- companion shape
      iv : Nat → Bool                     -- marked inv

  infoOf : Ctx → Info
  infoOf Δ = record
    { hs = λ j → mapMT (hdrShape (sorts Δ)) nothing (lookup Δ j)
    ; ts = λ j → tgtSrtB (sorts Δ) (entryBase Δ j)
    ; tp = λ j → tgtTopB (entryBase Δ j)
    ; dm = λ j → mapMT dim 0 (lookup Δ j)
    ; cm = λ j → mapMT cmpShape nothing (lookup Δ j)
    ; iv = λ j → minv ∈M marksAt Δ j
    }

  eqMN : Maybe Nat → Nat → Bool
  eqMN nothing  _ = false
  eqMN (just x) y = x ==ℕ y

  -- Length of the header starting at j, sorts at least lo.
  hdrGo : (Nat → Maybe Nat) → Nat → Nat → Nat → Nat
  hdrGo hs zero    j lo = 0
  hdrGo hs (suc f) j lo = step (hs j)
    where
    step : Maybe Nat → Nat
    step nothing  = 0
    step (just k) = if k <ℕ lo then 0 else suc (hdrGo hs f (suc j) (suc k))

  -- The header entry of sort k among c entries from j.
  findHdr : (Nat → Maybe Nat) → Nat → Nat → Nat → Maybe Nat
  findHdr hs k zero    j = nothing
  findHdr hs k (suc c) j = if eqMN (hs j) k then just j else findHdr hs k c (suc j)

  cmpIs : Maybe (Nat × Nat × Nat) → Nat → Nat → Nat → Bool
  cmpIs nothing              k j p = false
  cmpIs (just (k′ , j′ , p′)) k j p = (k′ ==ℕ k) ∧ (j′ ==ℕ j) ∧ (p′ ==ℕ p)

  -- Entry j of the body, given the header length h.
  okBased : Info → Nat → Nat → Nat → Maybe Nat → Bool
  okBased I j k h nothing  = true
  okBased I j k h (just p) =
    (Info.dm I j ==ℕ 1) ∧ cmpIs (Info.cm I (suc j)) k j p ∧ Info.iv I (suc j)

  okComp : Info → Nat → Nat → Nat → Maybe (Nat × Nat × Nat) → Bool
  okComp I n h j nothing              = false
  okComp I n h j (just (k , j′ , p)) = (suc j′ ==ℕ j) ∧ eqMN (findHdr (Info.hs I) k h n) p

  okTgt : Info → Nat → Nat → Nat → Maybe Nat → Bool
  okTgt I n h j (just k) = okBased I j k h (findHdr (Info.hs I) k h n)
  okTgt I n h j nothing  = Info.tp I j ∨ okComp I n h j (Info.cm I j)

  okB : Nat → Nat → Info → Nat → Bool
  okB n L I j =
    if j <ℕ (n + hdrGo (Info.hs I) L n 0) then true
    else okTgt I n (hdrGo (Info.hs I) L n 0) j (Info.ts I j)

  allBelow : Nat → (Nat → Bool) → Bool
  allBelow zero    f = true
  allBelow (suc L) f = allBelow L f ∧ f L

  basedOK : Ctx → Bool
  basedOK Δ = allBelow (len Δ) (okB (sorts Δ) (len Δ) (infoOf Δ))

  positive : Ctx → Bool
  positive Δ = ((0 <ℕ sorts Δ) ∧ posFrom (sorts Δ) Δ) ∧ basedOK Δ

  -- y is a sort, or an entry after the sorts.
  isSortIx inner : Nat → Ctx → Bool
  isSortIx y Δ = y <ℕ sorts Δ
  inner    y Δ = not (y <ℕ sorts Δ) ∧ (y <ℕ len Δ)

  sel : Former → Nat → Ctx → Bool
  sel μ    y Δ = isSortIx y Δ
  sel η    y Δ = inner y Δ
  sel rec  y Δ = isSortIx y Δ
  sel recY y Δ = inner y Δ ∧ isLow? (lookup Δ y)
  sel uni  y Δ = isSortIx y Δ ∧ lowFrom (sorts Δ) Δ
  sel uniY y Δ = (inner y Δ ∧ lowFrom (sorts Δ) Δ) ∧ isLow? (lookup Δ y)

  side : Former → Nat → Ctx → Bool
  side b y Δ = positive Δ ∧ sel b y Δ

  ----------------------------------------------------------------------
  -- Models and model morphisms.

  -- The carrier of sort k.
  μAt : Ctx → Nat → Tm
  μAt Δ k = bnd μ k Δ ⟨⟩

  -- Component j of the generic model.
  ηAt : Ctx → Nat → Tm
  ηAt Δ j = if j <ℕ sorts Δ then bnd μ j Δ ⟨⟩ else bnd η j Δ ⟨⟩

  -- The first k components of the generic model.
  ηPre : Ctx → Nat → Sub
  ηPre Δ zero    = ⟨⟩
  ηPre Δ (suc k) = ηPre Δ k ,ₛ ηAt Δ k

  -- The first k arguments, bvar 0 0, …, bvar 0 (k - 1).
  bvPre : Nat → Sub
  bvPre zero    = ⟨⟩
  bvPre (suc k) = bvPre k ,ₛ bvar 0 k

  withBase : Maybe (Tm × Tm) → (Tm → Tm → Ty) → Ty
  withBase nothing        k = ⋆
  withBase (just (S , T)) k = k S T

  -- The action on carrier maps h (one per sort) of an object S of the
  -- telescope, at a model M₁: h k if S is the sort k, else an identity.
  actM : Maybe Nat → Tm → Sub → (Nat → Tm) → Tm
  actM (just k) S M₁ h = h k
  actM nothing  S M₁ h = idm (opTm 0 M₁ S)

  act : Nat → Tm → Sub → (Nat → Tm) → Tm
  act m S M₁ h = actM (srt m S) S M₁ h

  -- The cell of a model morphism h : M₁ → M₂ at a map y : S → T, whose
  -- components in the two models are s₁ and s₂.
  cellTy : Nat → Tm → Tm → Sub → Sub → Tm → Tm → (Nat → Tm) → Ty
  cellTy m S T M₁ M₂ s₁ s₂ h =
    arr (arr ⋆ (opTm 0 M₁ S) (opTm 0 M₂ T))
        (cmp (opTm 0 M₁ S) (opTm 0 M₁ T) (opTm 0 M₂ T) s₁ (act m T M₁ h))
        (cmp (opTm 0 M₁ S) (opTm 0 M₂ S) (opTm 0 M₂ T) (act m S M₁ h) s₂)

  -- The 3-cell of a model morphism h : M₁ → M₂ at a 2-cell l : f ⇒ g
  -- between maps S → T, given its cells θf, θg at f and g: the two
  -- pastings of the naturality square
  --   (l₁ ▷ T(h)) · θg   ⇛   θf · (S(h) ◁ l₂).
  cell3Ty : Nat → Tm → Tm → Sub → Sub → Tm → Tm → Tm → Tm → Tm → Tm → (Nat → Tm) → Tm → Tm → Ty
  cell3Ty m S T M₁ M₂ f₁ g₁ l₁ f₂ g₂ l₂ h θf θg =
    let S₁  = opTm 0 M₁ S
        S₂  = opTm 0 M₂ S
        T₁  = opTm 0 M₁ T
        T₂  = opTm 0 M₂ T
        Th  = act m T M₁ h
        Sh  = act m S M₁ h
        src = cmp S₁ T₁ T₂ f₁ Th
        tgt = cmp S₁ S₂ T₂ Sh g₂
    in arr (arr (arr ⋆ S₁ T₂) src tgt)
           (vcomp S₁ T₂ src (cmp S₁ T₁ T₂ g₁ Th) (rwh S₁ T₁ T₂ f₁ g₁ l₁ Th) tgt θg)
           (vcomp S₁ T₂ src (cmp S₁ S₂ T₂ Sh f₂) θf tgt (lwh S₁ S₂ T₂ Sh f₂ g₂ l₂))

  globM : Maybe Ty → Maybe (Nat × Nat)
  globM nothing  = nothing
  globM (just A) = glob A

  globAt : Ctx → Nat → Maybe (Nat × Nat)
  globAt Δ y = globM (lookup Δ y)

  -- The component at y of a morphism from η to the model given by the
  -- first len Δ arguments, with carrier maps h and components th i at
  -- the earlier entries: a cell at a map, a 3-cell at a globular 2-cell.
  θSel : Ctx → Nat → (Nat → Tm) → (Nat → Tm) → Tm → Tm → Maybe (Nat × Nat) → Ty
  θSel Δ y h th S T nothing        =
    cellTy (sorts Δ) S T (ηPre Δ (len Δ)) (bvPre (len Δ)) (ηAt Δ y) (bvar 0 y) h
  θSel Δ y h th S T (just (i , j)) =
    cell3Ty (sorts Δ) S T (ηPre Δ (len Δ)) (bvPre (len Δ))
            (ηAt Δ i) (ηAt Δ j) (ηAt Δ y) (bvar 0 i) (bvar 0 j) (bvar 0 y) h (th i) (th j)

  θBody : Ctx → Nat → (Nat → Tm) → (Nat → Tm) → Tm → Tm → Ty
  θBody Δ y h th S T = θSel Δ y h th S T (globAt Δ y)

  θTy : Ctx → Nat → (Nat → Tm) → (Nat → Tm) → Ty
  θTy Δ y h th = withBase (entryBase Δ y) (θBody Δ y h th)

  -- The type of component k of a morphism from η to the model given by
  -- the first len Δ arguments, whose components are bvar 0 (o + i):
  -- the carrier map at a sort, the cell θ_k otherwise.
  morEntry : Ctx → Nat → Nat → Ty
  morEntry Δ o k =
    if k <ℕ sorts Δ then arr ⋆ (μAt Δ k) (bvar 0 k)
    else θTy Δ k (λ i → bvar 0 (o + i)) (λ i → bvar 0 (o + i))

  morPre : Ctx → Nat → Nat → Ctx
  morPre Δ o zero    = ε
  morPre Δ o (suc k) = morPre Δ o k ▸ morEntry Δ o k

  -- A model morphism from η to the model given by the first len Δ
  -- arguments, starting at argument o.
  morTel : Ctx → Nat → Ctx
  morTel Δ o = morPre Δ o (len Δ)

  -- The action of the cells u (one per sort) on an object S at M₁.
  uActM : Maybe Nat → Tm → (Nat → Tm) → Tm
  uActM (just k) S₁ u = u k
  uActM nothing  S₁ u = id2 S₁ S₁ (idm S₁)

  -- The compatibility cell of uni at y.
  uniYBody : Ctx → Nat → Tm → Tm → Ty
  uniYBody Δ y S T =
    let m   = len Δ
        n   = sorts Δ
        M₁  = ηPre Δ m
        M₂  = bvPre m
        S₁  = opTm 0 M₁ S
        S₂  = opTm 0 M₂ S
        T₁  = opTm 0 M₁ T
        T₂  = opTm 0 M₂ T
        h   = λ k → bvar 0 (m + k)
        h′  = λ k → bvar 0 (m + m + k)
        u   = λ k → bnd uni k Δ (bvPre (m + m + m))
        ηy  = ηAt Δ y
        σy  = bvar 0 y
        Th  = act n T M₁ h
        Th′ = act n T M₁ h′
        Sh  = act n S M₁ h
        Sh′ = act n S M₁ h′
        Tu  = uActM (srt n T) T₁ u
        Su  = uActM (srt n S) S₁ u
        src = cmp S₁ T₁ T₂ ηy Th
        tgt = cmp S₁ S₂ T₂ Sh′ σy
    in arr (arr (arr ⋆ S₁ T₂) src tgt)
           (vcomp S₁ T₂ src (cmp S₁ T₁ T₂ ηy Th′) (lwh S₁ T₁ T₂ ηy Th Th′ Tu) tgt
                  (bvar 0 (m + m + y)))
           (vcomp S₁ T₂ src (cmp S₁ S₂ T₂ Sh σy) (bvar 0 (m + y)) tgt
                  (rwh S₁ S₂ T₂ Sh Sh′ Su σy))

  -- The compatibility 4-cell of uni at a 2-cell y : f ⇒ g (f = i, g = j).
  uniY2Body : Ctx → Nat → Nat → Nat → Tm → Tm → Ty
  uniY2Body Δ y i j S T =
    let m   = len Δ
        n   = sorts Δ
        M₁  = ηPre Δ m
        M₂  = bvPre m
        S₁  = opTm 0 M₁ S
        T₁  = opTm 0 M₁ T
        h   = λ k → bvar 0 (m + k)
        h′  = λ k → bvar 0 (m + m + k)
        u   = λ k → bnd uni k Δ (bvPre (m + m + m))
    in mod4 S₁ (opTm 0 M₂ S) T₁ (opTm 0 M₂ T)
            (ηAt Δ i) (ηAt Δ j) (ηAt Δ y) (bvar 0 i) (bvar 0 j) (bvar 0 y)
            (act n T M₁ h) (act n T M₁ h′) (act n S M₁ h) (act n S M₁ h′)
            (uActM (srt n T) T₁ u) (uActM (srt n S) S₁ u)
            (bvar 0 (m + i)) (bvar 0 (m + j)) (bvar 0 (m + m + i)) (bvar 0 (m + m + j))
            (bvar 0 (m + y)) (bvar 0 (m + m + y))
            (bnd uniY i Δ (bvPre (m + m + m))) (bnd uniY j Δ (bvPre (m + m + m)))

  uniYSel : Ctx → Nat → Maybe (Nat × Nat) → Tm → Tm → Ty
  uniYSel Δ y nothing        = uniYBody Δ y
  uniYSel Δ y (just (i , j)) = uniY2Body Δ y i j

  uniYTy : Ctx → Nat → Ty
  uniYTy Δ y = withBase (entryBase Δ y) (uniYSel Δ y (globAt Δ y))

  ηRes : Ctx → Nat → Maybe Ty → Ty
  ηRes Δ y nothing  = ⋆
  ηRes Δ y (just A) = opTy 0 (ηPre Δ y) A

  args : Former → Nat → Ctx → Ctx
  args μ    y Δ = ε
  args η    y Δ = ε
  args rec  y Δ = Δ
  args recY y Δ = Δ
  args uni  y Δ = Δ ⧺ morTel Δ (len Δ) ⧺ morTel Δ (len Δ + len Δ)
  args uniY y Δ = Δ ⧺ morTel Δ (len Δ) ⧺ morTel Δ (len Δ + len Δ)

  res : Former → Nat → Ctx → Ty
  res μ    y Δ = ⋆
  res η    y Δ = ηRes Δ y (lookup Δ y)
  res rec  y Δ = arr ⋆ (μAt Δ y) (bvar 0 y)
  res recY y Δ = θTy Δ y (λ k → bnd rec k Δ (bvPre (len Δ))) (λ i → bnd recY i Δ (bvPre (len Δ)))
  res uni  y Δ = arr (arr ⋆ (μAt Δ y) (bvar 0 y)) (bvar 0 (len Δ + y)) (bvar 0 (len Δ + len Δ + y))
  res uniY y Δ = uniYTy Δ y

------------------------------------------------------------------------
-- The signature: constants from a base, binding formers INIT's.

record Base : Set₁ where
  field
    K         : Set
    _==K_     : K → K → Bool
    ==K-sound : ∀ k l → T (k ==K l) → k ≡ l
    ty        : K → Syntax.Ty K Former
    Valid     : K → Set
    valid?    : (k : K) → Maybe (Valid k)
    -- Which constants are the terminal object ⊤ (allowed as targets).
    top?      : K → Bool

initSig : Base → Signature
initSig b = record
  { K         = K
  ; _==K_     = _==K_
  ; ==K-sound = ==K-sound
  ; B         = Former
  ; _==B_     = _==F_
  ; ==B-sound = ==F-sound
  ; ty        = ty
  ; Valid     = Valid
  ; valid?    = valid?
  ; bside     = Construction.side K top?
  ; bargs     = Construction.args K top?
  ; bres      = Construction.res K top?
  }
  where open Base b
