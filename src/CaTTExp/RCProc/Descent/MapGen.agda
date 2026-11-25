------------------------------------------------------------------------
-- Structural maps of typed terms, and the abstract context of a set of
-- generators (ledger S20 (i), stage 4e; notes/rc-generator.md §1,
-- stage 4 plan; tools/rc_descent.py `Rof`, `ab`, `Hctx`).
--
-- The descent reads a term as a tree of *expanded* coherence nodes over
-- *generators* (the subterms it does not expand).  `mapD` rebuilds a
-- typed term with each generator replaced by a typed image and each
-- expanded node kept (its head facts read off the derivation, its
-- substitution typed by buildSub): R : U_θ → W and the abstraction into
-- H are such maps.  Which nodes are expanded, and the images, are
-- untrusted data; every `just` is typed.
--
-- `absCtx` builds the abstract context H of a list of generators (in
-- dependency order): one variable per generator, its type the
-- generator's type with the earlier generators abstracted, typed by
-- mapD; and the substitution H → Γ sending each variable back to its
-- generator, typed by buildSub.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.MapGen where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ty)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (decTm)

module _ {Γ Δ : Ctx} (wΔ : Δ ⊢ctx) (exp : Tm → Bool) (img : TTm Γ → Maybe (TTm Δ)) where
  mutual
    mapD : ∀ {t A} → Γ ⊢tm t ∶ A → Maybe (TTm Δ)
    mapD {t} d@(coh-wf {Δ = Q} {A} {s} {u} {γ} pQ wQ wB sd dγ) =
      if exp t
      then (mapE dγ >>= λ es → buildSub wΔ Q es >>= λ σ →
            just tt[ coh Q (arr A s u) (fst σ) ∶ arr A s u [ fst σ ]ty , coh-wf pQ wQ wB sd (snd σ) ])
      else img tt[ t ∶ _ , d ]
    mapD {t} d = img tt[ t ∶ _ , d ]

    mapE : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Maybe (List (TTm Δ))
    mapE (⟨⟩-wf _) = just []
    mapE (,-wf s d) = mapE s >>= λ es → mapD d >>= λ e → just (es ++ (e ∷ []))

  mapT : TTm Γ → Maybe (TTm Δ)
  mapT x = mapD (der x)

  -- a type, mapped: its base type and boundary terms
  mapTy : ∀ {A} → Γ ⊢ty A → Maybe (Σ Ty (Δ ⊢ty_))
  mapTy (⋆-wf _) = just (⋆ , ⋆-wf wΔ)
  mapTy {arr B s u} (arr-wf ds du) =
    mapD ds >>= λ s′ → mapD du >>= λ u′ →
    decTy (ty u′) (ty s′) >>= λ p →
    just (arr (ty s′) (tm s′) (tm u′) , arr-wf (der s′) (subst (Δ ⊢tm tm u′ ∶_) p (der u′)))

------------------------------------------------------------------------
-- The abstract context.

record Abs (Γ : Ctx) : Set where
  field
    H    : Ctx
    wH   : H ⊢ctx
    gens : List (Tm × TTm H)       -- generator ↦ its variable
    sH   : List (TTm Γ)            -- the variables' images, in order
open Abs public

private
  find : ∀ {Δ} → List (Tm × TTm Δ) → Tm → Maybe (TTm Δ)
  find []             t = nothing
  find ((g , x) ∷ gs) t = if g ==Tm t then just x else find gs t

  -- weaken the typed variables of H into H ▸ B (by re-reading them)
  reread : ∀ {H} → H ⊢ctx → List (Tm × TTm H) → List (Tm × Nat)
  reread w []                 = []
  reread w ((g , x) ∷ gs) = (g , lvl (tm x)) ∷ reread w gs
    where
    lvl : Tm → Nat
    lvl (var i) = i
    lvl _       = 0

  varT′ : ∀ {Γ} → Γ ⊢ctx → Nat → Maybe (TTm Γ)
  varT′ {Γ} w i = go (lookup Γ i) refl
    where
    go : (m : Maybe Ty) → lookup Γ i ≡ m → Maybe (TTm Γ)
    go nothing  _ = nothing
    go (just A) e = just tt[ var i ∶ A , var-wf w e ]

  mapM : ∀ {a b} {X : Set a} {Y : Set b} → (X → Maybe Y) → List X → Maybe (List Y)
  mapM f []       = just []
  mapM f (x ∷ xs) = f x >>= λ y → mapM f xs >>= λ ys → just (y ∷ ys)

-- Extend an abstract context by one generator x (whose type's
-- generators are already in it), all subterms of its type expanded
-- except the generators.
extend : ∀ {Γ} → (exp : Tm → Bool) → Abs Γ → TTm Γ → Maybe (Abs Γ)
extend {Γ} exp a x =
  mapTy (wH a) exp (λ y → find (gens a) (tm y)) (tm-ty (der x)) >>= λ B →
  go (fst B) (▸-wf (wH a) (snd B))
  where
  go : (B : Ty) → (H a ▸ B) ⊢ctx → Maybe (Abs Γ)
  go B w′ =
    mapM (λ gi → varT′ w′ (snd gi) >>= λ v → just (fst gi , v)) (reread (wH a) (gens a)) >>= λ gs →
    just record { H = H a ▸ B ; wH = w′
                ; gens = (tm x , tt[ var (len (H a)) ∶ B , var-wf w′ (lookup-top (H a) B) ]) ∷ gs
                ; sH = sH a ++ (x ∷ []) }

absCtx : ∀ {Γ} → Γ ⊢ctx → (exp : Tm → Bool) → List (TTm Γ) → Maybe (Abs Γ)
absCtx {Γ} w exp xs = go xs (record { H = ε ; wH = ε-wf ; gens = [] ; sH = [] })
  where
  go : List (TTm Γ) → Abs Γ → Maybe (Abs Γ)
  go []       a = just a
  go (x ∷ xs) a = extend exp a x >>= go xs

-- The substitution H → Γ, typed.
subH : ∀ {Γ} → Γ ⊢ctx → (a : Abs Γ) → Maybe (TSub Γ (H a))
subH w a = buildSub w (H a) (sH a)

-- A term over the generators, abstracted into H.
absT : ∀ {Γ} → (exp : Tm → Bool) → (a : Abs Γ) → TTm Γ → Maybe (TTm (H a))
absT exp a = mapT (wH a) exp (λ y → find (gens a) (tm y))
