------------------------------------------------------------------------
-- Typed composition with decided junctions (ledger S20 (i), stage 4c;
-- notes/rc-generator.md §1, stage 4 plan).
--
-- The descent assembles answers by composing cells whose boundaries
-- should agree syntactically: the Python implementation asserts it.
-- Here each junction is decided (==Ty, ==Tm, ==ℕ, sound), and the
-- composite is typed by the general whiskering lemmas of
-- DerivedBoundary.  So every `just` is typed by proof, whatever code
-- chose the pieces; a mismatch gives `nothing`.
--
--   decTm      : decided equality of terms
--   trans?     : Ans Γ A t s → Ans Γ A′ s′ u → Maybe (Ans Γ A t u)
--   rcomp?     : c ;ₖ h, c ▹ₖ h  (c : C of dimension j+k+1, h a (k+1)-cell
--                from the k-target of c)                    (rwT k j)
--   lcomp?     : h ◃ₖ c  (h a (k+1)-cell into the k-source of c)  (lwT k j)
--   ansT       : an answer as a typed term
------------------------------------------------------------------------
module CaTTExp.RCProc.TypedOps where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (nB; wK; lK)
open import CaTTExp.DerivedBoundary using (rwT; rwT-wf; tyK; tgtK; srcK; σR; lwT; lwT-wf; hL; σL)
open import CaTTExp.RCProc.Glue using (Ans; transA)
open import CaTTExp.RCProc.TypedSub using (TTm; tt[_∶_,_]; tm; ty; der; decTy)

decTm : (t u : Tm) → Maybe (t ≡ u)
decTm t u = go (t ==Tm u) (==Tm-sound t u)
  where
  go : (b : Bool) → (T b → t ≡ u) → Maybe (t ≡ u)
  go true  f = just (f tt)
  go false _ = nothing

decℕ : (m n : Nat) → Maybe (m ≡ n)
decℕ m n = go (m ==ℕ n) (==ℕ-sound m n)
  where
  go : (b : Bool) → (T b → m ≡ n) → Maybe (m ≡ n)
  go true  f = just (f tt)
  go false _ = nothing

trans? : ∀ {Γ A A′ t s s′ u} → Ans Γ A t s → Ans Γ A′ s′ u → Maybe (Ans Γ A t u)
trans? {Γ} {A} {A′} {t} {s} {s′} {u} a (w , dw) =
  decTy A′ A >>= λ p → decTm s′ s >>= λ q →
  just (transA a (w , subst (λ X → Γ ⊢tm w ∶ X)
                    (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) p (cong₂ _,_ q refl)) dw))

ansT : ∀ {Γ A t u} → Ans Γ A t u → TTm Γ
ansT {A = A} {t} {u} (w , dw) = tt[ w ∶ arr A t u , dw ]

private
  tgtOf : Ty → Tm
  tgtOf ⋆           = var 0
  tgtOf (arr _ _ z) = z
  srcOf : Ty → Tm
  srcOf ⋆           = var 0
  srcOf (arr _ s _) = s

-- c ▹ₖ h  (j = 0: the composite c ;ₖ h).
rcomp? : ∀ {Γ} (k j : Nat) → TTm Γ → TTm Γ → Maybe (TTm Γ)
rcomp? {Γ} k j c h =
  decℕ (dim (ty c)) (nB k j) >>= λ e →
  decTy (ty h) (arr (tyK k (ty c)) (tgtK k (ty c)) (tgtOf (ty h))) >>= λ p →
  just tt[ rwT k j (tm c) (ty c) (tgtOf (ty h)) (tm h) ∶ _ ,
           rwT-wf k j (der c) e (subst (Γ ⊢tm tm h ∶_) p (der h)) ]

-- h ◃ₖ c  (j = 0: the composite h ;ₖ c).
lcomp? : ∀ {Γ} (k j : Nat) → TTm Γ → TTm Γ → Maybe (TTm Γ)
lcomp? {Γ} k j h c =
  decℕ (dim (ty c)) (nB k j) >>= λ e →
  decTy (ty h) (hL k (srcOf (ty h)) (ty c)) >>= λ p →
  just tt[ lwT k j (tm h) (srcOf (ty h)) (tm c) (ty c) ∶ _ ,
           lwT-wf k j (der c) e (subst (Γ ⊢tm tm h ∶_) p (der h)) ]
