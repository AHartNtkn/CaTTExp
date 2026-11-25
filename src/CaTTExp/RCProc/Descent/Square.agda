------------------------------------------------------------------------
-- Naturality squares over generators (ledger S20 (i), stage 4e;
-- notes/rc-generator.md §1, stage 4 plan; tools/rc_descent.py, the
-- squares of `_piece`).
--
-- The descent lifts terms whose leaves are *generators* (subterms it
-- does not expand), not variables.  Python abstracts the generators to
-- the variables of a context H, lifts there, and substitutes back.
-- Here the lifts are built in Γ directly, with the datum given at the
-- generators:
--
--   moved x      x is a moved generator (x ∈ Y);
--   x⁻ = x,      x⁺ = plusG x (J R x when x moves; x otherwise),
--   x↑ = upG x   (the bridge a_x ⇛ b_x), x↑ᵒᵖ = dnG x (b_x ⇛ a_x).
--
-- An expanded node coh Q B γ is lifted by a filler of the oracle, as in
-- Lift.liftD and LiftOp.liftOpD; its copies t⁻, t⁺ are t and its
-- structural image under ⁺ (MapGen.mapT).  So `liftG`, `liftOpG`,
-- `endsG` agree with the Python's H-level squares after substitution,
-- and every `just` is a typed term of Γ, whatever the datum holds.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.Square where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (tm[])
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; lcomp?)
open import CaTTExp.RCProc.GlueP using (bdT)
open import CaTTExp.RCProc.Descent.Lift using (Head; head; hQ; FillO; cylCtx)
open import CaTTExp.RCProc.Descent.LiftOp using (FillOpO; cylCtxOp)
open import CaTTExp.RCProc.Descent.MapGen using (mapT)

-- A datum given at the generators.
record GDatum (Γ : Ctx) : Set where
  field
    wΓ    : Γ ⊢ctx
    exp   : Tm → Bool
    moved : Tm → Bool
    plusG : TTm Γ → Maybe (TTm Γ)
    upG   : Tm → Maybe (TTm Γ)
    dnG   : Tm → Maybe (TTm Γ)
open GDatum public

module _ {Γ : Ctx} (F : FillO) (G : FillOpO) (D : GDatum Γ) where
  mutual
    -- does t meet a moved generator?
    touchedG : Tm → Bool
    touchedG (var x)       = moved D (var x)
    touchedG (coh Q B γ)   = if exp D (coh Q B γ) then touchedS γ else moved D (coh Q B γ)
    touchedG (cst ())

    touchedS : Sub → Bool
    touchedS ⟨⟩       = false
    touchedS (γ ,ₛ t) = touchedS γ ∨ touchedG t

  copyP : TTm Γ → Maybe (TTm Γ)
  copyP = mapT (wΓ D) (exp D) (λ y → if moved D (tm y) then plusG D y else just y)

  private
    maskG : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Sel
    maskG (⟨⟩-wf _)          = ◇
    maskG (,-wf {t = t} s _) = maskG s ◂ touchedG t

    applyK : ∀ {Δ} → TTm Δ → List (TTm Γ) → Maybe (TTm Γ)
    applyK {Δ} K es = buildSub (wΓ D) Δ es >>= λ σ →
      just tt[ tm K [ fst σ ]tm ∶ ty K [ fst σ ]ty , tm[] (der K) (snd σ) ]

    three : TTm Γ → TTm Γ → Maybe (List (TTm Γ))
    three e up = copyP e >>= λ p → just (e ∷ p ∷ up ∷ [])

  mutual
    -- the lax square t↑ : a_t ⇛ b_t
    liftGD : ∀ {t A} → Γ ⊢tm t ∶ A → Maybe (TTm Γ)
    liftGD {t} (var-wf _ _) = upG D t
    liftGD {t} (coh-wf {Δ = Q} {A} {s} {u} pQ wQ wB sd dγ) =
      if exp D t
      then (F (head Q A s u pQ wQ wB sd) (maskG dγ) >>= λ K → liftGE dγ >>= applyK K)
      else upG D t
    liftGD (cst-wf {k} _ _) = ⊥-elim k

    liftGE : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Maybe (List (TTm Γ))
    liftGE (⟨⟩-wf _) = just []
    liftGE (,-wf {t = t} s d) =
      liftGE s >>= λ es →
      if touchedG t
      then (liftGD d >>= three e >>= λ xs → just (es ++ xs))
      else just (es ++ (e ∷ []))
      where
      e = tt[ t ∶ _ , d ]

  mutual
    -- the oplax square t↑ᵒᵖ : b_t ⇛ a_t
    liftOpGD : ∀ {t A} → Γ ⊢tm t ∶ A → Maybe (TTm Γ)
    liftOpGD {t} (var-wf _ _) = dnG D t
    liftOpGD {t} (coh-wf {Δ = Q} {A} {s} {u} pQ wQ wB sd dγ) =
      if exp D t
      then (G (head Q A s u pQ wQ wB sd) (maskG dγ) >>= λ ZK → liftOpGE (fst ZK) dγ >>= applyK (snd ZK))
      else dnG D t
    liftOpGD (cst-wf {k} _ _) = ⊥-elim k

    liftOpGE : ∀ {γ Q} → Sel → Γ ⊢sub γ ∶ Q → Maybe (List (TTm Γ))
    liftOpGE ◇ (⟨⟩-wf _) = just []
    liftOpGE (Z ◂ z) (,-wf {t = t} s d) =
      liftOpGE Z s >>= λ es →
      if touchedG t
      then (up z >>= three e >>= λ xs → just (es ++ xs))
      else just (es ++ (e ∷ []))
      where
      e = tt[ t ∶ _ , d ]
      up : Bool → Maybe (TTm Γ)
      up true  = liftOpGD d
      up false = liftGD d
    liftOpGE _ _ = nothing

  liftG liftOpG : TTm Γ → Maybe (TTm Γ)
  liftG x   = liftGD (der x)
  liftOpG x = liftOpGD (der x)

  -- The k-dimensional source and target of a typed cell (k < its dim).
  bdAtG : Nat → TTm Γ → Maybe (TTm Γ × TTm Γ)
  bdAtG k x = go (dim (ty x)) x
    where
    go : Nat → TTm Γ → Maybe (TTm Γ × TTm Γ)
    go zero    _ = nothing
    go (suc n) y = bdT y >>= λ su → if k ==ℕ n then just su else go n (fst su)

  -- The boundary cells a_t, b_t (Raw's P and L at the generators).
  endsG : TTm Γ → Maybe (TTm Γ × TTm Γ)
  endsG x = Pk n >>= λ a → Lk n >>= λ b → just (a , b)
    where
    n = dim (ty x)
    Pk Lk : Nat → Maybe (TTm Γ)
    Pk zero    = just x
    Pk (suc k) = Pk k >>= λ p → bdAtG k x >>= λ su →
      if touchedG (tm (snd su)) then (liftG (snd su) >>= λ h → rcomp? k (n ∸ suc k) p h) else just p
    Lk zero    = copyP x
    Lk (suc k) = Lk k >>= λ l → bdAtG k x >>= λ su →
      if touchedG (tm (fst su)) then (liftG (fst su) >>= λ h → lcomp? k (n ∸ suc k) h l) else just l
