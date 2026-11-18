------------------------------------------------------------------------
-- Purity: over a pasting context, the source and target of a coh
-- contain no constants (ledger item A3a).
--
-- In a context whose types are constant-free, every derivable t : A is
-- either
--   * constant-free with a free variable (and A constant-free), or
--   * closed (no free variables in t or A) and not constant-free.
-- The coh case uses that pasting contexts are connected: every
-- variable other than 0 is joined by an arrow to an earlier one, and
-- an arrow's image and its endpoints' images lie on the same side.
-- Since the side condition gives the source and target of a coh over
-- a pasting context a free variable, they are constant-free.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst

module CaTTExp.Strict.Purity (𝕊 : Signature) (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊)) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.ConstFree 𝕊
open import CaTTExp.Strict.PsFacts 𝕊
open import CaTTExp.Strict.Dim 𝕊 closed
import CaTTExp.Subst 𝕊 cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)

------------------------------------------------------------------------
-- The two sides.

VarSide : Tm → Ty → Set
VarSide t A = CFTm t × CFTy A × Σ Nat λ v → elem v (fvTm t) ≡ true

ClSide : Tm → Ty → Set
ClSide t A = (fvTmTy t A ≡ []) × (CFTm t → ⊥)

Pure : Tm → Ty → Set
Pure t A = VarSide t A ⊎′ ClSide t A

CtxCF : Ctx → Set
CtxCF Γ = ∀ v A → lookup Γ v ≡ just A → CFTy A

------------------------------------------------------------------------
-- Lists.

private
  t≢f : true ≡ false → ⊥
  t≢f ()

  ++-nil : ∀ (xs ys : List Nat) → xs ++ ys ≡ [] → (xs ≡ []) × (ys ≡ [])
  ++-nil []      ys p = refl , p
  ++-nil (x ∷ _) ys ()

  elem-nil : ∀ v {xs} → xs ≡ [] → elem v xs ≡ true → ⊥
  elem-nil v refl ()

  nil-from-elem : ∀ xs → (∀ v → elem v xs ≡ true → ⊥) → xs ≡ []
  nil-from-elem []      _ = refl
  nil-from-elem (x ∷ xs) f = ⊥-elim (f x (cong (_∨ elem x xs) (==-refl x)))

------------------------------------------------------------------------
-- Constant-free substitution.

mutual
  cf-ty[] : ∀ A σ → CFTy A → CFSub σ → CFTy (A [ σ ]ty)
  cf-ty[] ⋆           σ _           _ = tt
  cf-ty[] (arr A t u) σ (a , p , q) s = cf-ty[] A σ a s , cf-tm[] t σ p s , cf-tm[] u σ q s

  cf-tm[] : ∀ t σ → CFTm t → CFSub σ → CFTm (t [ σ ]tm)
  cf-tm[] (var i)     σ _       s = cf-lookup σ i s
  cf-tm[] (coh Δ A τ) σ (a , p) s = a , cf-∘ τ σ p s
  cf-tm[] (cst k)     σ ()      s

  cf-∘ : ∀ τ σ → CFSub τ → CFSub σ → CFSub (τ ∘ σ)
  cf-∘ ⟨⟩       σ _       _ = tt
  cf-∘ (τ ,ₛ t) σ (p , q) s = cf-∘ τ σ p s , cf-tm[] t σ q s

  cf-lookup : ∀ σ i → CFSub σ → CFTm (lookupₛ σ i)
  cf-lookup ⟨⟩       i _       = tt
  cf-lookup (σ ,ₛ t) i (p , q) with i ==ℕ lenₛ σ
  ... | true  = q
  ... | false = cf-lookup σ i p

private
  lookupₛ-skip : ∀ σ t w → T (w <ℕ lenₛ σ) → lookupₛ (σ ,ₛ t) w ≡ lookupₛ σ w
  lookupₛ-skip σ t w lw rewrite <→≢ w (lenₛ σ) lw = refl

  lookupₛ-top : ∀ σ t → lookupₛ (σ ,ₛ t) (lenₛ σ) ≡ t
  lookupₛ-top σ t rewrite ==-refl (lenₛ σ) = refl

cf-from-lookups : ∀ σ → (∀ w → T (w <ℕ lenₛ σ) → CFTm (lookupₛ σ w)) → CFSub σ
cf-from-lookups ⟨⟩       f = tt
cf-from-lookups (σ ,ₛ t) f =
  cf-from-lookups σ (λ w lw → subst CFTm (lookupₛ-skip σ t w lw) (f w (<-suc w (lenₛ σ) lw))) ,
  subst CFTm (lookupₛ-top σ t) (f (lenₛ σ) (n<suc (lenₛ σ)))

fv-from-lookups : ∀ σ → (∀ w → T (w <ℕ lenₛ σ) → fvTm (lookupₛ σ w) ≡ []) → fvSub σ ≡ []
fv-from-lookups ⟨⟩       f = refl
fv-from-lookups (σ ,ₛ t) f =
  trans (cong (_++ fvTm t)
          (fv-from-lookups σ (λ w lw → trans (cong fvTm (sym (lookupₛ-skip σ t w lw))) (f w (<-suc w (lenₛ σ) lw)))))
        (trans (cong fvTm (sym (lookupₛ-top σ t))) (f (lenₛ σ) (n<suc (lenₛ σ))))

------------------------------------------------------------------------
-- Pasting contexts: constant-free, ∂⁺ non-empty, connected.

PsTy→CF : ∀ {A} → PsTy A → CFTy A
PsTy→CF ⋆ₚ       = tt
PsTy→CF (arrₚ p) = PsTy→CF p , tt , tt

ps-ctxCF : ∀ {Γ z C} → Γ ⊢ps z ∶ C → CtxCF Γ
ps-ctxCF d v A eq = PsTy→CF (shape (ps-facts d) v A eq)

tgt-has : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i → Σ Nat λ v → elem v (tgtVars i Γ) ≡ true
tgt-has pss i = 0 , refl
tgt-has (psd d) i = tgt-has d i
tgt-has (pse {Γ} {x} {A} d) i with i <ℕ dim A
... | true  = tgt-has d i
... | false with dim A ==ℕ i
...   | true  = len Γ , last-in (dropLastᴸ (tgtVars i Γ)) (len Γ)
  where
  last-in : ∀ xs y → elem y (snoc xs y) ≡ true
  last-in []       y = cong (_∨ false) (==-refl y)
  last-in (x ∷ xs) y = ∨-r′ (y ==ℕ x) (last-in xs y)
    where
    ∨-r′ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
    ∨-r′ true  _ = refl
    ∨-r′ false p = p
...   | false = suc (len Γ) , last-in (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))
  where
  last-in : ∀ xs y → elem y (snoc xs y) ≡ true
  last-in []       y = cong (_∨ false) (==-refl y)
  last-in (x ∷ xs) y = ∨-r′ (y ==ℕ x) (last-in xs y)
    where
    ∨-r′ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
    ∨-r′ true  _ = refl
    ∨-r′ false p = p

-- Every variable other than 0 is an arrow, or the target of an arrow,
-- whose source is earlier.
Link : Ctx → Nat → Set
Link Γ w = Σ Nat λ f → Σ Ty λ B → Σ Nat λ x → Σ Nat λ y →
           (lookup Γ f ≡ just (arr B (var x) (var y))) × T (x <ℕ w) × ((f ≡ w) ⊎′ (y ≡ w))

ps-link : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ w → T (w <ℕ len Γ) → (w ≡ 0 → ⊥) → Link Γ w
ps-link pss zero _ nz = ⊥-elim (nz refl)
ps-link pss (suc w) () nz
ps-link (psd d) w lw nz = ps-link d w lw nz
ps-link (pse {Γ} {x} {A} d) w lw nz with w ==ℕ suc (len Γ) in e₁
... | true rewrite ==→≡ w (suc (len Γ)) e₁ =
  suc (len Γ) , A , x , len Γ , lookup-top (Γ ▸ A) _ , <-suc x (len Γ) lx , inl′ refl
  where
  lx = lookup-< Γ x (dang (ps-facts d))
... | false with w ==ℕ len Γ in e₂
...   | true rewrite ==→≡ w (len Γ) e₂ =
  suc (len Γ) , A , x , len Γ , lookup-top (Γ ▸ A) _ , lookup-< Γ x (dang (ps-facts d)) , inr′ refl
...   | false =
  let lw′ = <suc-≢ w (len Γ) (<suc-≢ w (suc (len Γ)) lw e₁) e₂
      (f , B , x′ , y′ , eq , lt , o) = ps-link d w lw′ nz
  in f , B , x′ , y′ , trans (lookup-wk₂ Γ A _ f (lookup-< Γ f eq)) eq , lt , o

------------------------------------------------------------------------
-- The purity theorem.

private
  pure-cf : ∀ {t A} → Pure t A → CFTm t → VarSide t A
  pure-cf (inl′ v)       _ = v
  pure-cf (inr′ (_ , n)) c = ⊥-elim (n c)

  pure-ncf : ∀ {t A} → Pure t A → (CFTm t → ⊥) → ClSide t A
  pure-ncf (inl′ (c , _)) n = ⊥-elim (n c)
  pure-ncf (inr′ s)       _ = s

  fvTy-arr-mid : ∀ B a b → fvTy (arr B a b) ≡ [] → fvTm a ≡ []
  fvTy-arr-mid B a b p = fst (++-nil (fvTm a) (fvTm b) (snd (++-nil (fvTy B) (fvTm a ++ fvTm b) p)))

  fvTy-arr-last : ∀ B a b → fvTy (arr B a b) ≡ [] → fvTm b ≡ []
  fvTy-arr-last B a b p = snd (++-nil (fvTm a) (fvTm b) (snd (++-nil (fvTy B) (fvTm a ++ fvTm b) p)))

  Iff : Set → Set → Set
  Iff X Y = (X → Y) × (Y → X)

  edge-a : ∀ {c B′ a b A₁} → Pure c (arr B′ a b) → Pure a A₁ → Iff (CFTm c) (CFTm a)
  edge-a (inl′ (cc , (_ , ca , _) , _)) _ = (λ _ → ca) , (λ _ → cc)
  edge-a {c} {B′} {a} {b} (inr′ (fv , nc)) pa =
    (λ x → ⊥-elim (nc x)) ,
    (λ ca → let (_ , _ , v , m) = pure-cf pa ca in
            ⊥-elim (elem-nil v (fvTy-arr-mid B′ a b (snd (++-nil (fvTm c) _ fv))) m))

  edge-b : ∀ {c B′ a b A₂} → Pure c (arr B′ a b) → Pure b A₂ → Iff (CFTm c) (CFTm b)
  edge-b (inl′ (cc , (_ , _ , cb) , _)) _ = (λ _ → cb) , (λ _ → cc)
  edge-b {c} {B′} {a} {b} (inr′ (fv , nc)) pb =
    (λ x → ⊥-elim (nc x)) ,
    (λ cb → let (_ , _ , v , m) = pure-cf pb cb in
            ⊥-elim (elem-nil v (fvTy-arr-last B′ a b (snd (++-nil (fvTm c) _ fv))) m))

  pure-var : ∀ {t A} → Pure t A → (Σ Nat λ v → elem v (fvTmTy t A) ≡ true) → VarSide t A
  pure-var (inl′ p)       _       = p
  pure-var (inr′ (e , _)) (v , m) = ⊥-elim (elem-nil v e m)

  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  side-s : ∀ {Θ z B s u} → Θ ⊢ps z ∶ ⋆ → T (cattSide Θ B s u) → Σ Nat λ v → elem v (fvTmTy s B) ≡ true
  side-s {Θ} {B = B} {s} {u} d side with isCoh Θ B s u in ec
  ... | true =
    let (w , m , _) = ps-top d in
    w , trans (≈?-elem (fvTmTy s B) (varsCtx Θ) (∧-l (≈? (fvTmTy s B) (varsCtx Θ)) _ (≡→T ec)) w) m
  ... | false =
    let (w , m , _) = src-has d (dimCtx Θ ∸ 1) (∸1-< (dimCtx Θ)) in
    w , trans (≈?-elem (fvTmTy s B) (∂⁻ Θ) (∧-l (≈? (fvTmTy s B) (∂⁻ Θ)) _ side) w) m

  side-u : ∀ {Θ z B s u} → Θ ⊢ps z ∶ ⋆ → T (cattSide Θ B s u) → Σ Nat λ v → elem v (fvTmTy u B) ≡ true
  side-u {Θ} {B = B} {s} {u} d side with isCoh Θ B s u in ec
  ... | true =
    let (w , m , _) = ps-top d in
    w , trans (≈?-elem (fvTmTy u B) (varsCtx Θ) (∧-r (≈? (fvTmTy s B) (varsCtx Θ)) _ (≡→T ec)) w) m
  ... | false =
    let (w , m) = tgt-has d (dimCtx Θ ∸ 1) in
    w , trans (≈?-elem (fvTmTy u B) (∂⁺ Θ) (∧-r (≈? (fvTmTy s B) (∂⁻ Θ)) _ side) w) m

  lt-step : ∀ x w n → T (x <ℕ w) → T (w <ℕ suc n) → T (x <ℕ n)
  lt-step x       zero    n       () _
  lt-step zero    (suc w) zero    _  ()
  lt-step zero    (suc w) (suc n) _  _ = tt
  lt-step (suc x) (suc w) zero    _  ()
  lt-step (suc x) (suc w) (suc n) a  b = lt-step x w n a b

  lt-trans : ∀ x w n → T (x <ℕ w) → T (w <ℕ n) → T (x <ℕ n)
  lt-trans x w n a b = lt-step x w n a (<-suc w n b)

  strong : (P : Nat → Set) → (∀ w → (∀ x → T (x <ℕ w) → P x) → P w) → ∀ w → P w
  strong P h w = go (suc w) w (n<suc w)
    where
    go : ∀ n w → T (w <ℕ n) → P w
    go zero    w ()
    go (suc n) w lw = h w (λ x lx → go n x (lt-step x w n lx lw))

  zero< : ∀ w n → T (w <ℕ n) → T (0 <ℕ n)
  zero< w (suc n) _ = tt

-- The coh case: over a pasting context, the images of all variables
-- lie on the same side as the image of variable 0.
module CohPure {Θ z} (d : Θ ⊢ps z ∶ ⋆) (σ : Sub)
  (P : ∀ w A → lookup Θ w ≡ just A → Pure (lookupₛ σ w) (A [ σ ]ty)) where

  private
    CFσ : Nat → Set
    CFσ w = CFTm (lookupₛ σ w)

    pure-at : ∀ w → T (w <ℕ len Θ) → Σ Ty λ A → Pure (lookupₛ σ w) A
    pure-at w lw with lookup-just Θ w lw
    ... | (A , e) = A [ σ ]ty , P w A e

    step : ∀ w f B′ x y → lookup Θ f ≡ just (arr B′ (var x) (var y)) → T (x <ℕ len Θ) → T (w <ℕ len Θ) →
           (f ≡ w) ⊎′ (y ≡ w) → Iff (CFσ x) (CFσ 0) → Iff (CFσ w) (CFσ 0)
    step w f B′ x y eqf lx lw (inl′ refl) (h₁ , h₂) =
      let (a₁ , a₂) = edge-a (P f _ eqf) (snd (pure-at x lx)) in
      (λ c → h₁ (a₁ c)) , (λ c → a₂ (h₂ c))
    step w f B′ x y eqf lx lw (inr′ refl) (h₁ , h₂) =
      let (a₁ , a₂) = edge-a (P f _ eqf) (snd (pure-at x lx))
          (b₁ , b₂) = edge-b (P f _ eqf) (snd (pure-at y lw))
      in (λ c → h₁ (a₁ (b₂ c))) , (λ c → b₁ (a₂ (h₂ c)))

    go : ∀ w → (∀ x → T (x <ℕ w) → T (x <ℕ len Θ) → Iff (CFσ x) (CFσ 0)) →
         T (w <ℕ len Θ) → Iff (CFσ w) (CFσ 0)
    go zero    _  _  = (λ c → c) , (λ c → c)
    go (suc w) ih lw with ps-link d (suc w) lw (λ ())
    ... | (f , B′ , x , y , eqf , lxw , o) =
      let lx = lt-trans x (suc w) (len Θ) lxw lw in
      step (suc w) f B′ x y eqf lx lw o (ih x lxw lx)

    conn : ∀ w → T (w <ℕ len Θ) → Iff (CFσ w) (CFσ 0)
    conn = strong (λ w → T (w <ℕ len Θ) → Iff (CFσ w) (CFσ 0)) go

    0<len : T (0 <ℕ len Θ)
    0<len with ps-top d
    ... | (w , m , _) = zero< w (len Θ) (elem-Below (len Θ) w (varsCtx Θ) (Below-downFrom (len Θ)) m)

  result : ∀ {B s u} → Θ ⊢ty arr B s u → T (cattSide Θ B s u) → lenₛ σ ≡ len Θ →
           Pure s B → Pure u B → Pure (coh Θ (arr B s u) σ) ((arr B s u) [ σ ]ty)
  result {B} {s} {u} wA side lσ qs qu with lookup-just Θ 0 0<len
  ... | (A₀ , e₀) = fin (P 0 A₀ e₀)
    where
    vs = pure-var qs (side-s {B = B} {s} {u} d side)
    vu = pure-var qu (side-u {B = B} {s} {u} d side)

    cfA : CFTy (arr B s u)
    cfA = fst (snd vs) , fst vs , fst vu

    lw′ : ∀ w → T (w <ℕ lenₛ σ) → T (w <ℕ len Θ)
    lw′ w = subst (λ n → T (w <ℕ n)) lσ

    l0 : T (0 <ℕ lenₛ σ)
    l0 = subst (λ n → T (0 <ℕ n)) (sym lσ) 0<len

    scA : ScTy (lenₛ σ) (arr B s u)
    scA = subst (λ n → ScTy n (arr B s u)) (sym lσ) (Sb.ty-sc closed wA)

    fin : ∀ {A′} → Pure (lookupₛ σ 0) A′ → Pure (coh Θ (arr B s u) σ) ((arr B s u) [ σ ]ty)
    fin (inl′ (c₀ , _ , v , m)) =
      let cfσ = cf-from-lookups σ (λ w lw → snd (conn w (lw′ w lw)) c₀) in
      inl′ ((cfA , cfσ) , cf-ty[] (arr B s u) σ cfA cfσ , v , fvSub-at σ 0 v l0 m)
    fin (inr′ (_ , n₀)) = inr′ (trans (cong (_++ fvTy ((arr B s u) [ σ ]ty)) fvσ) fvA , λ c → n₀ (cf-lookup σ 0 (snd c)))
      where
      fvw : ∀ w → T (w <ℕ lenₛ σ) → fvTm (lookupₛ σ w) ≡ []
      fvw w lw with pure-at w (lw′ w lw)
      ... | (A , q) = fst (++-nil (fvTm (lookupₛ σ w)) (fvTy A)
                        (fst (pure-ncf q (λ c → n₀ (fst (conn w (lw′ w lw)) c)))))

      fvσ : fvSub σ ≡ []
      fvσ = fv-from-lookups σ fvw

      fvA : fvTy ((arr B s u) [ σ ]ty) ≡ []
      fvA = nil-from-elem _ (λ v m → let (x , _ , lx , r) = fv-[]ty (arr B s u) σ v scA m in
                                       elem-nil v (fvw x lx) r)

mutual
  pure-tm : ∀ {Γ t A} → CtxCF Γ → Γ ⊢tm t ∶ A → Pure t A
  pure-tm cfΓ (var-wf {i} {A} w eq) = inl′ (tt , cfΓ i A eq , i , cong (_∨ false) (==-refl i))
  pure-tm cfΓ (cst-wf {k} _ _) = inr′ (sc0-ty (ty k) (closed k) , λ ())
  pure-tm cfΓ (coh-wf {σ = σ} (ps d) wΘ wA@(arr-wf ds du) side sσ) =
    CohPure.result d σ (pure-sub cfΓ sσ wΘ) wA side (snd (Sb.sub-sc closed sσ))
      (pure-tm (ps-ctxCF d) ds) (pure-tm (ps-ctxCF d) du)

  pure-sub : ∀ {Γ σ Δ} → CtxCF Γ → Γ ⊢sub σ ∶ Δ → Δ ⊢ctx → ∀ w A → lookup Δ w ≡ just A → Pure (lookupₛ σ w) (A [ σ ]ty)
  pure-sub cfΓ (⟨⟩-wf _) _ w A ()
  pure-sub cfΓ (,-wf {σ = σ} {Δ = Δ} {t = t} {A = A′} sσ dt) (▸-wf wΔ a′) w A eq with w ==ℕ len Δ in e
  ... | true with just-inj′ eq
  ...   | refl rewrite snd (Sb.sub-sc closed sσ) | e
                     | Sb.ext-ty A′ σ t (subst (λ n → ScTy n A′) (sym (snd (Sb.sub-sc closed sσ))) (Sb.ty-sc closed a′)) =
    pure-tm cfΓ dt
  pure-sub cfΓ (,-wf {σ = σ} {Δ = Δ} {t = t} {A = A′} sσ dt) (▸-wf wΔ a′) w A eq | false
    rewrite snd (Sb.sub-sc closed sσ) | e
          | Sb.ext-ty A σ t (subst (λ n → ScTy n A) (sym (snd (Sb.sub-sc closed sσ))) (snd (Sb.ctx-lookup closed wΔ eq))) =
    pure-sub cfΓ sσ wΔ w A eq

------------------------------------------------------------------------
-- The sides of a coh are constant-free.

pure-side : ∀ {Θ z B s u} → Θ ⊢ps z ∶ ⋆ → Θ ⊢tm s ∶ B → Θ ⊢tm u ∶ B → T (cattSide Θ B s u) →
            CFTy B × CFTm s × CFTm u
pure-side {B = B} {s} {u} d ds du side =
  let vs = pure-var (pure-tm (ps-ctxCF d) ds) (side-s {B = B} {s} {u} d side)
      vu = pure-var (pure-tm (ps-ctxCF d) du) (side-u {B = B} {s} {u} d side)
  in fst (snd vs) , fst vs , fst vu
