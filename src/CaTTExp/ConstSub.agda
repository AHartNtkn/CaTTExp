------------------------------------------------------------------------
-- Constant substitutions (ledger item C8.2, `limits-representables.md`
-- §8 target 2): for every well-formed context Γ there is a substitution
--
--   (c : ⋆) ⊢ !_Γ ∶ Γ
--
-- sending every variable to an iterated coherence on c. This is the
-- contractibility of the one-point context D₀: every well-formed type
-- in D₀ is inhabited, by a full coherence over D₀ itself.
--
-- Hypotheses. The signature's constants have closed types (needed for
-- substitution, CaTTExp.Subst). Γ must be *constant free* outside coh
-- bodies (`NcCtx`): a constant c₀ : ⋆ in Γ's types would force a term
-- of type c₀ → c₀ that mentions the variable c, which the full-coherence
-- side condition cannot produce over D₀. Pure CaTT contexts are
-- constant free, so for pure CaTT the theorem holds for every Γ.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.ConstSub (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Subst 𝕊 cattSide

D₀ : Ctx
D₀ = ε ▸ ⋆

-- The identity substitution of D₀.
id₀ : Sub
id₀ = ⟨⟩ ,ₛ var 0

------------------------------------------------------------------------
-- Constant-free syntax (constants inside coh bodies are allowed; they
-- are closed and never substituted).

mutual
  NcTy : Ty → Set
  NcTy ⋆           = ⊤
  NcTy (arr A t u) = NcTy A × NcTm t × NcTm u

  NcTm : Tm → Set
  NcTm (var _)     = ⊤
  NcTm (coh _ _ σ) = NcSub σ
  NcTm (cst _)     = ⊥

  NcSub : Sub → Set
  NcSub ⟨⟩       = ⊤
  NcSub (σ ,ₛ t) = NcSub σ × NcTm t

NcCtx : Ctx → Set
NcCtx ε       = ⊤
NcCtx (Γ ▸ A) = NcCtx Γ × NcTy A

private
  nc-lookup : ∀ σ i → NcSub σ → NcTm (lookupₛ σ i)
  nc-lookup ⟨⟩       i _       = tt
  nc-lookup (σ ,ₛ t) i (p , q) with i ==ℕ lenₛ σ
  ... | true  = q
  ... | false = nc-lookup σ i p

mutual
  nc-ty[] : ∀ A σ → NcTy A → NcSub σ → NcTy (A [ σ ]ty)
  nc-ty[] ⋆           σ _           _ = tt
  nc-ty[] (arr A t u) σ (a , p , q) s = nc-ty[] A σ a s , nc-tm[] t σ p s , nc-tm[] u σ q s

  nc-tm[] : ∀ t σ → NcTm t → NcSub σ → NcTm (t [ σ ]tm)
  nc-tm[] (var i)     σ _ s = nc-lookup σ i s
  nc-tm[] (coh _ _ τ) σ p s = nc-∘ τ σ p s
  nc-tm[] (cst _)     σ () s

  nc-∘ : ∀ τ σ → NcSub τ → NcSub σ → NcSub (τ ∘ σ)
  nc-∘ ⟨⟩       σ _       _ = tt
  nc-∘ (τ ,ₛ t) σ (p , q) s = nc-∘ τ σ p s , nc-tm[] t σ q s

------------------------------------------------------------------------
-- id₀ acts as the identity on all syntax.

mutual
  id₀-ty : ∀ A → A [ id₀ ]ty ≡ A
  id₀-ty ⋆           = refl
  id₀-ty (arr A t u) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (id₀-ty A) (cong₂ _,_ (id₀-tm t) (id₀-tm u))

  id₀-tm : ∀ t → t [ id₀ ]tm ≡ t
  id₀-tm (var zero)    = refl
  id₀-tm (var (suc i)) = refl
  id₀-tm (coh Δ A τ)   = cong (coh Δ A) (id₀-sub τ)
  id₀-tm (cst k)       = refl

  id₀-sub : ∀ τ → τ ∘ id₀ ≡ τ
  id₀-sub ⟨⟩       = refl
  id₀-sub (τ ,ₛ t) = cong₂ _,ₛ_ (id₀-sub τ) (id₀-tm t)

------------------------------------------------------------------------
-- Variables of terms in D₀.

private
  all-++ : ∀ (p : Nat → Bool) xs ys → T (all p xs) → T (all p ys) → T (all p (xs ++ ys))
  all-++ p []       ys _ q = q
  all-++ p (x ∷ xs) ys h q with p x
  ... | true = all-++ p xs ys h q

  elem-++ʳ : ∀ n xs ys → T (elem n ys) → T (elem n (xs ++ ys))
  elem-++ʳ n []       ys p = p
  elem-++ʳ n (x ∷ xs) ys p with n ==ℕ x
  ... | true  = tt
  ... | false = elem-++ʳ n xs ys p

  elem-++ˡ : ∀ n xs ys → T (elem n xs) → T (elem n (xs ++ ys))
  elem-++ˡ n (x ∷ xs) ys p with n ==ℕ x
  ... | true  = tt
  ... | false = elem-++ˡ n xs ys p

  is0 : Nat → Bool
  is0 x = elem x (0 ∷ [])

-- Scoped in D₀ means every free variable is 0.
mutual
  sc1-ty : ∀ A → ScTy 1 A → T (all is0 (fvTy A))
  sc1-ty ⋆           _           = tt
  sc1-ty (arr A t u) (a , p , q) =
    all-++ is0 (fvTy A) _ (sc1-ty A a) (all-++ is0 (fvTm t) _ (sc1-tm t p) (sc1-tm u q))

  sc1-tm : ∀ t → ScTm 1 t → T (all is0 (fvTm t))
  sc1-tm (var zero)    _ = tt
  sc1-tm (var (suc i)) ()
  sc1-tm (coh _ _ σ)   p = sc1-sub σ p
  sc1-tm (cst _)       _ = tt

  sc1-sub : ∀ σ → ScSub 1 σ → T (all is0 (fvSub σ))
  sc1-sub ⟨⟩       _       = tt
  sc1-sub (σ ,ₛ t) (p , q) = all-++ is0 (fvSub σ) _ (sc1-sub σ p) (sc1-tm t q)

-- A constant-free term in D₀ mentions the variable 0.
private
  ps-nonempty : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Γ ≡ ε → ⊥
  ps-nonempty pss     ()
  ps-nonempty (pse _) ()
  ps-nonempty (psd d) e = ps-nonempty d e

has0 : ∀ {t A} → D₀ ⊢tm t ∶ A → NcTm t → T (elem 0 (fvTm t))
has0 (var-wf {zero} _ _) _ = tt
has0 (var-wf {suc i} _ ()) _
has0 (coh-wf (ps p) _ _ _ (⟨⟩-wf _)) _ = ⊥-elim (ps-nonempty p refl)
has0 (coh-wf {σ = σ ,ₛ t} _ _ _ _ (,-wf _ d)) (_ , q) = elem-++ʳ 0 (fvSub σ) (fvTm t) (has0 d q)
has0 (cst-wf _ _) ()

------------------------------------------------------------------------
-- Filling a type of D₀.

fill : Ty → Tm
fill ⋆           = var 0
fill (arr A t u) = coh D₀ (arr A t u) id₀

module _ (closed : Closed) where

  private
    w₀ : D₀ ⊢ctx
    w₀ = ▸-wf ε-wf (⋆-wf ε-wf)

    id₀-wf : D₀ ⊢sub id₀ ∶ D₀
    id₀-wf = ,-wf (⟨⟩-wf w₀) (var-wf w₀ refl)

    side₀ : ∀ {A t u} → D₀ ⊢ty arr A t u → NcTm t → NcTm u → T (cattSide D₀ A t u)
    side₀ {A} {t} {u} a@(arr-wf dt du) nt nu = ∨-inl (and2 (half t dt nt sA st) (half u du nu sA su))
      where
      sc = ty-sc closed a
      sA = fst sc
      st = fst (snd sc)
      su = snd (snd sc)

      and2 : ∀ {a b} → T a → T b → T (a ∧ b)
      and2 {true} _ q = q

      ∨-inl : ∀ {a b} → T a → T (a ∨ b)
      ∨-inl {true} _ = tt

      half : ∀ s → D₀ ⊢tm s ∶ A → NcTm s → ScTy 1 A → ScTm 1 s →
             T (≈? (fvTmTy s A) (varsCtx D₀))
      half s ds ns sa ss =
        and2 (all-++ is0 (fvTm s) (fvTy A) (sc1-tm s ss) (sc1-ty A sa))
             (and2 (elem-++ˡ 0 (fvTm s) (fvTy A) (has0 ds ns)) tt)

  fill-wf : ∀ {A} → D₀ ⊢ty A → NcTy A → D₀ ⊢tm fill A ∶ A
  fill-wf (⋆-wf _) _ = var-wf w₀ refl
  fill-wf {arr A t u} a@(arr-wf _ _) (_ , nt , nu) =
    subst (D₀ ⊢tm coh D₀ (arr A t u) id₀ ∶_) (id₀-ty (arr A t u))
      (coh-wf (ps pss) w₀ a (side₀ a nt nu) id₀-wf)

  private
    nc-fill : ∀ A → NcSub id₀ → NcTm (fill A)
    nc-fill ⋆           _ = tt
    nc-fill (arr A t u) p = p

  ----------------------------------------------------------------------
  -- The constant substitution.

  ! : Ctx → Sub
  ! ε       = ⟨⟩
  ! (Γ ▸ A) = ! Γ ,ₛ fill (A [ ! Γ ]ty)

  !-wf : ∀ {Γ} → Γ ⊢ctx → NcCtx Γ → (D₀ ⊢sub ! Γ ∶ Γ) × NcSub (! Γ)
  !-wf ε-wf _ = ⟨⟩-wf w₀ , tt
  !-wf {Γ ▸ A} (▸-wf w a) (nΓ , nA) =
    let (s , ns) = !-wf w nΓ in
    ,-wf s (fill-wf (ty[] closed a s) (nc-ty[] A (! Γ) nA ns)) , ns , nc-fill (A [ ! Γ ]ty) (tt , tt)
