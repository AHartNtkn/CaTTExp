------------------------------------------------------------------------
-- Cones over coherence terms of every dimension, from a relative-
-- coherence oracle (ledger B19, N^cone; layer 1 of the executable
-- construction).
--
-- This is the reduction of notes/conjectures/answered/
-- cone-over-coherences-2026-11-18.md §2–3 ("RC(1..n) on the join
-- contexts gives N^cone through dimension n"), written as a function.
-- It is parametric in
--
--   rc : Ctx → Ty → Tm → Tm → Maybe Tm,
--
-- which, given Δ, A and parallel t, u : A with equal strict images,
-- should return w : t → u. Nothing trusts rc: its answers enter the
-- cone context as `raw` terms, and every cone context is run through
-- the certified checker in CaTTExp.ConeRCExamples. A wrong answer can
-- only make a check fail.
--
-- The construction of P(u), for a term u of Γ of dimension m, in the
-- cone context K built so far:
--
--   * u a variable: its projection p_u.
--   * u with identity strict image (empty top chain; e.g. an identity,
--     or a composite of identities): one rc call P(τu) → T(u).
--   * u = a ∗_k b otherwise: the strict lift
--       W₀ = P b ∗_{k+1} (P a ∗_k R_k(t_{k+1} b)),
--     where R_k(w) = P(s_{k−1} w) ∗_{k−1} (… (P(s₀ w) ∗₀ w)), so that
--     T(u) = R_m(u). Each gluing ∗_j first corrects the lower faces of
--     its right factor and then inserts one rc cell (§3, (23)). Then
--     W₀ is transported face by face to P(τu) → T(u) (§2, (18)–(21)).
--
-- Every rc call is between terms whose lower faces already agree
-- literally, so it is an instance of RC(r) in the join context. Cells
-- whose two ends agree literally are skipped, not filled.
------------------------------------------------------------------------
module CaTTExp.ConeRC where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.GraphFillerTotal using (path; fill₁)

RC : Set
RC = Ctx → Ty → Tm → Tm → Maybe Tm

-- An oracle query: Δ, A, t, u, asking for a term of type t →_A u in Δ.
Query : Set
Query = Ctx × (Ty × (Tm × Tm))

-- Results: a value, the first oracle query left unanswered, or a
-- failure not caused by the oracle.
data Out (A : Set) : Set where
  ret   : A → Out A
  miss : Query → Out A
  fail : Out A

infixl 1 _⟫=_
_⟫=_ : ∀ {A B : Set} → Out A → (A → Out B) → Out B
ret a   ⟫= k = k a
miss q ⟫= k = miss q
fail   ⟫= k = fail

fromMaybe : ∀ {A : Set} → Maybe A → Out A
fromMaybe (just a) = ret a
fromMaybe nothing  = fail

toMaybe : ∀ {A : Set} → Out A → Maybe A
toMaybe (ret a) = just a
toMaybe _      = nothing

missed : ∀ {A : Set} → Out A → Maybe Query
missed (miss q) = just q
missed _        = nothing

-- Try the first oracle, then the second.
_orRC_ : RC → RC → RC
(r₁ orRC r₂) Δ A t u with r₁ Δ A t u
... | just w  = just w
... | nothing = r₂ Δ A t u

------------------------------------------------------------------------
-- RC(1) in every context: the filler of CaTTExp.GraphFillerTotal,
-- for 1-cells with the same path.

eqList : List Nat → List Nat → Bool
eqList []       []       = true
eqList (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ eqList xs ys
eqList _        _        = false

rc1 : RC
rc1 Δ (arr ⋆ (var a) b) t u =
  if eqList (path t) (path u) then just (fill₁ Δ t u (arr ⋆ (var a) b)) else nothing
rc1 Δ _ t u = nothing

-- The oracle that only fills literally equal ends (with an identity);
-- with it, the construction succeeds only where no correction is needed.
rcNone : RC
rcNone Δ A t u = nothing

------------------------------------------------------------------------

-- The construction is parametric in how a filler a → b is obtained in
-- the context K built so far, and in how literal equality is decided.
-- ConeRC (below) uses the oracle directly; CoconeRC runs the cone
-- construction on the dual diagram and asks the oracle in the dual
-- (cocone) world.
Fill : Set
Fill = ExCtx → Ex → Ex → Out Ex

Eq : Set
Eq = ExCtx → Ex → Ex → Bool

fillCore : RC → Fill
fillCore rc K a b with rc (evCtx K) (evTy K (tyE K a)) (ev K a) (ev K b)
... | just w  = ret (raw w a b)
... | nothing = miss (evCtx K , evTy K (tyE K a) , ev K a , ev K b)

eqCore : Eq
eqCore K a b = ev K a ==Tm ev K b

module ConeGen (fillH : Fill) (eqH : Eq) (Γ : ExCtx) where
  private
    n = length Γ
    c = v n
    pr : Nat → Ex
    pr i = v (suc (n + i))

  module At (K : ExCtx) where
    dimK : Ex → Nat
    dimK e = dimE (tyE K e)

    sE tE : Ex → Ex
    sE e = srcE (tyE K e)
    tE e = tgtE (tyE K e)

    iter : Nat → (Ex → Ex) → Ex → Ex
    iter zero    f e = e
    iter (suc k) f e = iter k f (f e)

    -- The r-dimensional source (true) or target (false); e itself if
    -- r ≥ dim e.
    face : Bool → Nat → Ex → Ex
    face b r e =
      if r <ℕ dimK e
      then (if b then iter (dimK e ∸ r) sE e else tE (iter (dimK e ∸ suc r) sE e))
      else e

    eq : Ex → Ex → Bool
    eq = eqH K

    -- A cell a → b.
    fillE : Ex → Ex → Out Ex
    fillE = fillH K

    -- Precompose W along r with a cell L → s_r W, unless they agree.
    fixS : Nat → Ex → Ex → Out Ex
    fixS r L W = if eq L (face true r W) then ret W
                 else (fillE L (face true r W) ⟫= λ l → ret (bn r l W))

    -- Postcompose W along r with a cell t_r W → R, unless they agree.
    fixT : Nat → Ex → Ex → Out Ex
    fixT r W R = if eq (face false r W) R then ret W
                 else (fillE (face false r W) R ⟫= λ ρ → ret (bn r W ρ))

    -- Face-by-face transport (§2): make the r-faces of W equal to
    -- L r and R r, for r = 1, …, m in turn.
    transport : Nat → (Nat → Ex) → (Nat → Ex) → Ex → Out Ex
    transport m L R W = go m 1 W
      where
      go : Nat → Nat → Ex → Out Ex
      go zero    r W = ret W
      go (suc f) r W =
        if m <ℕ r then ret W
        else (fixS r (L r) W ⟫= λ W₁ → fixT r W₁ (R r) ⟫= λ W₂ → go f (suc r) W₂)

    -- X ∗_j Y after correcting Y (§3, (23)).
    compose : Nat → Ex → Ex → Out Ex
    compose zero    X Y = ret (bn 0 X Y)
    compose (suc j) X Y =
      transport j (λ r → face true r X) (λ r → face false r X) Y ⟫= λ Y₁ →
      fixS (suc j) (face false (suc j) X) Y₁ ⟫= λ Y₂ →
      ret (bn (suc j) X Y₂)

    -- Does u have a nonempty top chain (a non-identity strict image)?
    -- Variables do; identities and the named coherences do not.
    nz : Ex → Bool
    nz (v _)      = true
    nz (bn k a b) = ((dimK a ==ℕ d) ∧ nz a) ∨ ((dimK b ==ℕ d) ∧ nz b)
      where d = dimK (bn k a b)
    nz _          = false

    mutual
      P : Nat → Ex → Out Ex
      P zero    _     = fail
      P (suc f) (v i) = ret (pr i)
      P (suc f) u     =
        if nz u then lift f u
        else (P f (tE u) ⟫= λ Pt → Tc f u ⟫= λ Tu → fillE Pt Tu)

      lift : Nat → Ex → Out Ex
      lift f (bn k a b) =
        P f a ⟫= λ Pa → P f b ⟫= λ Pb →
        R f k (face false (suc k) b) ⟫= λ Rb →
        compose k Pa Rb ⟫= λ X → compose (suc k) Pb X ⟫= λ W₀ →
        P f (tE u) ⟫= λ Pt → Tc f u ⟫= λ Tu →
        transport m (λ r → if r ==ℕ m then Pt else face true r Pt)
                    (λ r → if r ==ℕ m then Tu else face false r Pt) W₀
        where
        u = bn k a b
        m = dimK u
      lift f _ = fail

      -- R_j(w) = P(s_{j−1} w) ∗_{j−1} (… (P(s₀ w) ∗₀ w)).
      R : Nat → Nat → Ex → Out Ex
      R f zero    w = ret w
      R f (suc j) w = P f (face true j w) ⟫= λ p → R f j w ⟫= λ r → ret (bn j p r)

      -- T(u) = R_m(u), m = dim u.
      Tc : Nat → Ex → Out Ex
      Tc f u = R f (dimK u) u

    PK : Ex → Out Ex
    PK = P fuel

    TK : Ex → Out Ex
    TK = Tc fuel

  projTy : ExCtx → Nat → ExTy → Out ExTy
  projTy K x ob          = ret (hom ob c (v x))
  projTy K x (hom A s t) = At.PK K t ⟫= λ pt → At.TK K (v x) ⟫= λ l →
                           ret (hom (tyE K pt) pt l)

  build : Nat → ExCtx → ExCtx → Out ExCtx
  build x K []       = ret K
  build x K (A ∷ As) = projTy K x A ⟫= λ B → build (suc x) (K ++ (B ∷ [])) As

  coneO : Out ExCtx
  coneO = build 0 (Γ ++ (ob ∷ [])) Γ

  cone : Maybe ExCtx
  cone = toMaybe coneO

  -- The first query the oracle could not answer, if any (for building
  -- oracle tables query by query).
  firstMiss : Maybe Query
  firstMiss = missed coneO

module ConeRC (rc : RC) (Γ : ExCtx) = ConeGen (fillCore rc) eqCore Γ

------------------------------------------------------------------------
-- Cocones by O_odd duality. The cone construction runs on the dual
-- diagram Γ*; each filler a → b it needs (an (r+1)-cell in the cone
-- context K of Γ*) is asked of the oracle in the dual context K*, which
-- is a prefix of the cocone of Γ: there it is a* → b*, or b* → a* when
-- r + 1 is odd. The answer w enters K as rawD w a b, whose dual is the
-- term w itself. Literal equality is also decided in K*.

oddB : Nat → Bool
oddB zero          = false
oddB (suc zero)    = true
oddB (suc (suc k)) = oddB k

fillDual : RC → Fill
fillDual rc K a b with rc (evCtx K*) (evTy K* (tyE K* t)) (ev K* t) (ev K* u)
  where
  K* = dualCtx K
  rev = oddB (suc (dimE (tyE K a)))
  t = if rev then dualE b else dualE a
  u = if rev then dualE a else dualE b
... | just w  = ret (rawD w a b)
... | nothing = miss (evCtx K* , evTy K* (tyE K* t) , ev K* t , ev K* u)
  where
  K* = dualCtx K
  rev = oddB (suc (dimE (tyE K a)))
  t = if rev then dualE b else dualE a
  u = if rev then dualE a else dualE b

eqDual : Eq
eqDual K a b = ev (dualCtx K) (dualE a) ==Tm ev (dualCtx K) (dualE b)

module CoconeRC (rc : RC) (Γ : ExCtx) where
  private
    module G = ConeGen (fillDual rc) eqDual (dualCtx Γ)

  cocone : Maybe ExCtx
  cocone = G.cone >>= λ K → if all dualOKTy K then just (dualCtx K) else nothing

  firstMiss : Maybe Query
  firstMiss = G.firstMiss
