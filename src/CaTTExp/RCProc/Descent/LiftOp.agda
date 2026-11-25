------------------------------------------------------------------------
-- Oplax naturality squares of typed terms (ledger S20 (i), stage 4e;
-- notes/rc-generator.md §1, stage 4 plan; tools/rc_nat.py nat_op).
--
-- The descent closes a piece with the lax square t↑ : a_t → b_t of the
-- source and the *oplax* square u↑ᵒᵖ : b_u → a_u of the target.  It is
-- built by the recursion of Lift.liftD, with three changes:
--
--   var x        ↦ dn x, a reversed bridge b_x → a_x (given only for
--                  the moved top generators; none for the others);
--   coh Q B γ    ↦ K [ γ↑ ]   with (Z, K) = G Q B (mask γ): Z marks the
--                  touched arguments that take their op-lift, K is a
--                  typed term of the op cylinder context Q↑Y,Z, whose
--                  up-variables at Z are reversed;
--   γ↑           sends q ↦ γq⁻, γq⁺, and γq↑ᵒᵖ for q ∈ Z, the lax
--                  γq↑ for the other touched q.
--
-- G is an untrusted oracle (it chooses Z and the filler); the result is
-- a typed term of Δ whatever it returns.  Which type it has is not
-- proved: the piece step decides its final type syntactically.
--
-- `fillDirectOp` is the op filler of a coherence with Z empty: the one
-- query (b_c, a_c) on Q↑Y (RC is symmetric).  Compositions with a
-- selected top cell need layered op fillers (stage 4d).
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.LiftOp where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (idS; id-wf)
open import CaTTExp.PureMetatheory using (tm[])
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.Descent.Lift
open import CaTTExp.RCProc.Descent.Fill using (RecAll; genD; decCtx)

revTy : Ty → Ty
revTy ⋆           = ⋆
revTy (arr B a b) = arr B b a

-- The op cylinder context Q↑Y,Z: as Q↑Y, with the up-variables of the
-- positions in Z reversed (Z has the length of Y; else junk).
cylCtxOp : Ctx → Sel → Sel → Ctx
cylCtxOp ε       _           _       = ε
cylCtxOp (Q ▸ A) ◇           _       = ε
cylCtxOp (Q ▸ A) (Y ◂ b)     ◇       = ε
cylCtxOp (Q ▸ A) (Y ◂ true)  (Z ◂ z) =
  cylCtxOp Q Y Z ▸ A [ C0.genMm Y ]ty ▸ A [ C0.genMp Y ]ty ▸ (if z then revTy cT else cT)
  where
  cT = C0.cylTy (C0.gen (Y ◂ true)) (var (len Q)) A
cylCtxOp (Q ▸ A) (Y ◂ false) (Z ◂ _) = cylCtxOp Q Y Z ▸ A [ C0.genMm Y ]ty

noneSel : Sel → Sel
noneSel ◇       = ◇
noneSel (Y ◂ _) = noneSel Y ◂ false

-- An op filler oracle: the reversed positions and a typed term there.
FillOpO : Set
FillOpO = (h : Head) → (Y : Sel) → Maybe (Σ Sel λ Z → TTm (cylCtxOp (hQ h) Y Z))

module _ {Γ Δ : Ctx} (F : FillO) (G : FillOpO) (D : TDatum Γ Δ) (dn : Nat → Maybe (TTm Δ)) where
  mutual
    liftOpD : ∀ {t A} → Γ ⊢tm t ∶ A → Maybe (TTm Δ)
    liftOpD (var-wf {i = x} _ _) = dn x
    liftOpD (coh-wf {Δ = Q} {A} {s} {u} {γ} pQ wQ wB sd dγ) =
      G (head Q A s u pQ wQ wB sd) Y >>= λ ZK →
      liftOpE (fst ZK) dγ >>= λ es →
      buildSub (wΔ D) (cylCtxOp Q Y (fst ZK)) es >>= λ σ →
      just tt[ tm (snd ZK) [ fst σ ]tm ∶ ty (snd ZK) [ fst σ ]ty , tm[] (der (snd ZK)) (snd σ) ]
      where
      Y = maskD F D dγ
    liftOpD (cst-wf {k} _ _) = ⊥-elim k

    liftOpE : ∀ {γ Q} → Sel → Γ ⊢sub γ ∶ Q → Maybe (List (TTm Δ))
    liftOpE ◇ (⟨⟩-wf _) = just []
    liftOpE (Z ◂ z) (,-wf {t = t} s d) =
      liftOpE Z s >>= λ es →
      if touched F D t
      then (up z >>= λ w → just (es ++ (copyM F D e ∷ copyP F D e ∷ w ∷ [])))
      else just (es ++ (copyM F D e ∷ []))
      where
      e = tt[ t ∶ _ , d ]
      up : Bool → Maybe (TTm Δ)
      up true  = liftOpD d
      up false = liftD F D d
    liftOpE _ _ = nothing

  liftOpT : TTm Γ → Maybe (TTm Δ)
  liftOpT x = liftOpD (der x)

-- The direct op filler: one query (b_c, a_c) on Q↑Y, nothing reversed.
fillDirectOp : FillO → RecAll → FillOpO
fillDirectOp inner rec h Y =
  genD Q Y (hwQ h) >>= λ D →
  endsT inner D c >>= λ ab →
  rec (wΔ D) (snd ab) (fst ab) >>= λ w →
  decCtx (cylCtx Q Y) (cylCtxOp Q Y (noneSel Y)) >>= λ e →
  just (noneSel Y , subst TTm e w)
  where
  Q = hQ h
  B = arr (hA h) (hs h) (hu h)
  c : TTm Q
  c = tt[ C0.cohId Q B ∶ B [ idS (len Q) ]ty , coh-wf (hps h) (hwQ h) (hwB h) (hsd h) (id-wf (hwQ h)) ]
