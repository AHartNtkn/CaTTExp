------------------------------------------------------------------------
-- Typed substitutions from typed entries (ledger S20 (i), stage 4a;
-- notes/rc-generator.md §1, stage 4 plan).
--
-- The descent (tools/rc_descent.py) builds substitutions whose entries
-- are chosen by untrusted code: J : W → Γ, R : U_θ → W, and the abstract
-- context's substitution H → Γ.  Every entry is a term that already
-- carries a typing derivation (a generator of a typed input, read off by
-- inversion, or a recursive answer).  What remains is that each entry's
-- type is the target context's type under the substitution built so
-- far, a syntactic equality, decided here by ==Ty (sound by ==Ty-sound).
-- So a substitution returned by `buildSub` is typed by proof, whatever code
-- chose its entries; nothing is run through the checker.
--
--   buildSub    : Γ ⊢ctx → (Δ : Ctx) → List (TTm Γ) → Maybe (TSub Γ Δ)
--   entries  : Γ ⊢sub σ ∶ Δ → the entries of σ, each typed
--   argsOf   : Γ ⊢tm coh Δ B σ ∶ C → Γ ⊢sub σ ∶ Δ   (inversion)
------------------------------------------------------------------------
module CaTTExp.RCProc.TypedSub where

open import CaTTExp.Prelude
open import CaTTExp.Pure

-- A term of Γ with its type and a typing derivation.
record TTm (Γ : Ctx) : Set where
  constructor tt[_∶_,_]
  field
    tm  : Tm
    ty  : Ty
    der : Γ ⊢tm tm ∶ ty
open TTm public

-- A typed substitution into Δ.
TSub : Ctx → Ctx → Set
TSub Γ Δ = Σ Sub λ σ → Γ ⊢sub σ ∶ Δ

decTy : (A B : Ty) → Maybe (A ≡ B)
decTy A B = go (A ==Ty B) (==Ty-sound A B)
  where
  go : (b : Bool) → (T b → A ≡ B) → Maybe (A ≡ B)
  go true  f = just (f tt)
  go false _ = nothing

-- Entries are listed last variable first (the snoc order of Δ, reversed),
-- so the head entry is the image of Δ's last variable.
buildRev : ∀ {Γ} → Γ ⊢ctx → (Δ : Ctx) → List (TTm Γ) → Maybe (TSub Γ Δ)
buildRev w ε       []       = just (⟨⟩ , ⟨⟩-wf w)
buildRev w ε       (_ ∷ _)  = nothing
buildRev w (Δ ▸ A) []       = nothing
buildRev {Γ} w (Δ ▸ A) (e ∷ es) =
  buildRev w Δ es >>= λ s →
  decTy (ty e) (A [ fst s ]ty) >>= λ q →
  just (fst s ,ₛ tm e , ,-wf (snd s) (subst (Γ ⊢tm tm e ∶_) q (der e)))

-- Entries in the left-to-right order of Δ.
buildSub : ∀ {Γ} → Γ ⊢ctx → (Δ : Ctx) → List (TTm Γ) → Maybe (TSub Γ Δ)
buildSub w Δ es = buildRev w Δ (rev es [])
  where
  rev : ∀ {a} {X : Set a} → List X → List X → List X
  rev []       acc = acc
  rev (x ∷ xs) acc = rev xs (x ∷ acc)

-- The entries of a typed substitution, each typed (last variable first).
entries : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → List (TTm Γ)
entries (⟨⟩-wf _) = []
entries (,-wf {t = t} s d) = tt[ t ∶ _ , d ] ∷ entries s

-- Inversion: the substitution of a typed coherence is typed.
argsOf : ∀ {Γ Δ B σ C} → Γ ⊢tm coh Δ B σ ∶ C → Γ ⊢sub σ ∶ Δ
argsOf (coh-wf _ _ _ _ s) = s
