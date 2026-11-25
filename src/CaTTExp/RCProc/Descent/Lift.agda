------------------------------------------------------------------------
-- Naturality cylinders of typed terms, with fillers from an abstract
-- typed filler oracle (ledger S20 (i), stage 4d; notes/rc-generator.md
-- §1, stage 4 plan; tools/rc_nat.py nat_in).
--
-- A typed datum on Γ into Δ gives typed copies mm, mp : Δ → Γ, a
-- selection, and typed cylinders th x of the selected variables.  For a
-- typed term t of Γ, `liftT` builds t↑ by the recursion of
-- Naturality.Raw's `cyl`:
--
--   var x        ↦ th x
--   coh Q B γ    ↦ K [ γ↑ ]   with K = F Q B (mask γ), a typed filler
--                             in the cylinder context Q↑Y, and γ↑ the
--                             substitution x ↦ γx⁻, γx⁺, γx↑ (touched)
--                             or γx⁻ (untouched), typed by buildSub.
--
-- The result is a typed term of Δ (by tm[]), whatever F returns: F is
-- any function giving typed terms of the cylinder context.
--
-- `endsT` builds the boundary cells a_t, b_t of the cylinder by the
-- recursion of Raw's P and L (nested whiskers by the cylinders of the
-- touched iterated targets, resp. sources; untouched factors omitted),
-- with the decided whiskers of RCProc.TypedOps.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.Lift where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (tm[])
open import CaTTExp.Naturality.Raw
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; lcomp?)
open import CaTTExp.RCProc.GlueP using (bdT)

-- The cylinder contexts do not depend on the filler family when the
-- boundaries of Q's types are variables (as in every pasting context).
K0 : Filler
K0 _ _ _ = junk

module C0 = Cyl K0

cylCtx : Ctx → Sel → Ctx
cylCtx = C0.cylCtx

-- A coherence head with the typing facts of its coh-wf rule (read off
-- the derivation of a term using it).
record Head : Set where
  constructor head
  field
    hQ  : Ctx
    hA  : Ty
    hs  : Tm
    hu  : Tm
    hps : hQ ⊢ps
    hwQ : hQ ⊢ctx
    hwB : hQ ⊢ty arr hA hs hu
    hsd : T (cattSide hQ hA hs hu)
open Head public

-- A typed filler oracle: a typed term of Q↑Y, or nothing.
FillO : Set
FillO = (h : Head) → (Y : Sel) → Maybe (TTm (cylCtx (hQ h) Y))

-- A typed cylinder datum on Γ into Δ.
record TDatum (Γ Δ : Ctx) : Set where
  field
    wΔ  : Δ ⊢ctx
    mmT : TSub Δ Γ
    mpT : TSub Δ Γ
    sel : Nat → Bool
    thT : Nat → Maybe (TTm Δ)
open TDatum public

module _ {Γ Δ : Ctx} (F : FillO) (D : TDatum Γ Δ) where
  touched : Tm → Bool
  touched t = anyL (sel D) (fvTm t)

  private
    mmS mpS : Sub
    mmS = fst (mmT D)
    mpS = fst (mpT D)

    copyM copyP : TTm Γ → TTm Δ
    copyM x = tt[ tm x [ mmS ]tm ∶ ty x [ mmS ]ty , tm[] (der x) (snd (mmT D)) ]
    copyP x = tt[ tm x [ mpS ]tm ∶ ty x [ mpS ]ty , tm[] (der x) (snd (mpT D)) ]

  mutual
    -- t↑ for a typed t of Γ (by recursion on its derivation)
    liftD : ∀ {t A} → Γ ⊢tm t ∶ A → Maybe (TTm Δ)
    liftD (var-wf {i = x} _ _) = thT D x
    liftD (coh-wf {Δ = Q} {A} {s} {u} {γ} pQ wQ wB sd dγ) =
      F (head Q A s u pQ wQ wB sd) (maskD dγ) >>= λ K →
      liftE dγ >>= λ es →
      buildSub (wΔ D) (cylCtx Q (maskD dγ)) es >>= λ σ →
      just tt[ tm K [ fst σ ]tm ∶ ty K [ fst σ ]ty , tm[] (der K) (snd σ) ]
    liftD (cst-wf {k} _ _) = ⊥-elim k

    -- the selection of the touched entries of γ
    maskD : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Sel
    maskD (⟨⟩-wf _)          = ◇
    maskD (,-wf {t = t} s _) = maskD s ◂ touched t

    -- the entries of γ↑, in left-to-right order
    liftE : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Maybe (List (TTm Δ))
    liftE (⟨⟩-wf _) = just []
    liftE (,-wf {t = t} s d) =
      liftE s >>= λ es →
      if touched t
      then (liftD d >>= λ up → just (es ++ (copyM e ∷ copyP e ∷ up ∷ [])))
      else just (es ++ (copyM e ∷ []))
      where
      e = tt[ t ∶ _ , d ]

  liftT : TTm Γ → Maybe (TTm Δ)
  liftT x = liftD (der x)

  -- The k-dimensional source and target of a typed cell (k < its
  -- dimension), read down its type as Raw's srcAt/tgtAt do.
  bdAt : Nat → TTm Γ → Maybe (TTm Γ × TTm Γ)
  bdAt k x = go (dim (ty x)) x
    where
    go : Nat → TTm Γ → Maybe (TTm Γ × TTm Γ)
    go zero    _ = nothing
    go (suc n) y = bdT y >>= λ su → if k ==ℕ n then just su else go n (fst su)

  endsT : TTm Γ → Maybe (TTm Δ × TTm Δ)
  endsT x = Pk n >>= λ a → Lk n >>= λ b → just (a , b)
    where
    n = dim (ty x)
    Pk Lk : Nat → Maybe (TTm Δ)
    Pk zero    = just (copyM x)
    Pk (suc k) = Pk k >>= λ p → bdAt k x >>= λ su →
      if touched (tm (snd su)) then (liftT (snd su) >>= λ h → rcomp? k (n ∸ suc k) p h) else just p
    Lk zero    = just (copyP x)
    Lk (suc k) = Lk k >>= λ l → bdAt k x >>= λ su →
      if touched (tm (fst su)) then (liftT (fst su) >>= λ h → lcomp? k (n ∸ suc k) h l) else just l
