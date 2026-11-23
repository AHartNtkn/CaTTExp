------------------------------------------------------------------------
-- Renaming and weakening for CaTT with binders, for every side
-- condition and every binder interface satisfying BinderLaws.
--
-- With binders, weakening is still the identity on syntax (bound
-- variables are locally nameless), but not on derivations: the
-- telescope premise of a binder opens the telescope at the length of
-- the context, which grows. So weakening is proved as an instance of
-- renaming, where a renaming ρ : Γ′ ⇒ Γ sends each variable of Γ to a
-- variable of Γ′ of the renamed type. Renamings extend under a binder
-- (the telescope's opened variables go to the fresh variables after
-- Γ′) without any typing derivation of terms, which is what makes the
-- induction go through.
--
--   tm-ren : Γ ⊢ t ∶ A  and  Γ′ ⊢ren ρ ∶ Γ  give  Γ′ ⊢ t[ρ] ∶ A[ρ]
--   wk-tm  : Γ ⊢ t ∶ A  and  Γ ▸ B ⊢        give  Γ ▸ B ⊢ t ∶ A
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.Rename
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side
open import CaTTExp.Binder.Scoping 𝕊 side
open Laws 𝕊

infix 4 _⊢ren_∶_

record _⊢ren_∶_ (Γ′ : Ctx) (ρ : Sub) (Γ : Ctx) : Set where
  constructor mkRen
  field
    ctx  : Γ′ ⊢ctx
    leq  : lenₛ ρ ≡ len Γ
    lc   : LC ρ
    sc   : T (scSub? (len Γ′) ρ)
    look : ∀ i {A} → lookup Γ i ≡ just A →
           Σ Nat λ j → (lookupₛ ρ i ≡ var j) × (lookup Γ′ j ≡ just (A [ ρ ]ty))

open _⊢ren_∶_

------------------------------------------------------------------------
-- Lookup lemmas.

lookupₛ-top : ∀ σ t i → (i ==ℕ lenₛ σ) ≡ true → lookupₛ (σ ,ₛ t) i ≡ t
lookupₛ-top σ t i e rewrite e = refl

lookupₛ-pop : ∀ σ t i → (i ==ℕ lenₛ σ) ≡ false → lookupₛ (σ ,ₛ t) i ≡ lookupₛ σ i
lookupₛ-pop σ t i e rewrite e = refl

lookup-pop : ∀ Γ A i → (i ==ℕ len Γ) ≡ false → lookup (Γ ▸ A) i ≡ lookup Γ i
lookup-pop Γ A i e rewrite e = refl

lookup-top : ∀ Γ A i → (i ==ℕ len Γ) ≡ true → lookup (Γ ▸ A) i ≡ just A
lookup-top Γ A i e rewrite e = refl

==-transport : ∀ i {m n} → m ≡ n → (i ==ℕ m) ≡ (i ==ℕ n)
==-transport i refl = refl

==-self : ∀ {m n} → m ≡ n → (m ==ℕ n) ≡ true
==-self {m} refl = ==-refl m

------------------------------------------------------------------------
-- Identity substitutions are `fresh 0 n`.

⟨⟩++ : ∀ τ → ⟨⟩ ++ₛ τ ≡ τ
⟨⟩++ ⟨⟩ = refl
⟨⟩++ (τ ,ₛ t) = cong (_,ₛ t) (⟨⟩++ τ)

lookup-id : ∀ n i → T (i <ℕ n) → lookupₛ (fresh 0 n) i ≡ var i
lookup-id n i p = subst (λ τ → lookupₛ τ i ≡ var i) (⟨⟩++ (fresh 0 n)) (lookup-fresh ⟨⟩ 0 n i p)

mutual
  id-ty : ∀ n A → T (scTy? n A) → A [ fresh 0 n ]ty ≡ A
  id-ty n ⋆ _ = refl
  id-ty n (arr A t u) p =
    let (a , q) = T∧ {scTy? n A} p ; (b , c) = T∧ {scTm? n t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (id-ty n A a) (cong₂ _,_ (id-tm n t b) (id-tm n u c))

  id-tm : ∀ n t → T (scTm? n t) → t [ fresh 0 n ]tm ≡ t
  id-tm n (var i) p = lookup-id n i p
  id-tm n (bvar d j) _ = refl
  id-tm n (coh Δ A τ) p = cong (coh Δ A) (id-sub n τ p)
  id-tm n (cst k) _ = refl
  id-tm n (bnd b y Δ τ) p =
    let (a , c) = T∧ {scTel? n Δ} p in cong₂ (bnd b y) (id-tel n Δ a) (id-sub n τ c)

  id-tel : ∀ n Δ → T (scTel? n Δ) → Δ [ fresh 0 n ]tel ≡ Δ
  id-tel n ε _ = refl
  id-tel n (Δ ▸ A) p = let (a , b) = T∧ {scTel? n Δ} p in cong₂ _▸_ (id-tel n Δ a) (id-ty n A b)

  id-sub : ∀ n τ → T (scSub? n τ) → τ ∘ fresh 0 n ≡ τ
  id-sub n ⟨⟩ _ = refl
  id-sub n (τ ,ₛ t) p = let (a , b) = T∧ {scSub? n τ} p in cong₂ _,ₛ_ (id-sub n τ a) (id-tm n t b)

------------------------------------------------------------------------
-- The renaming lemma.

module _ (closed : Closed) (laws : BinderLaws) where

  open BinderLaws laws

  private
    scTyAt : ∀ {m n} A → m ≡ n → T (scTy? m A) → T (scTy? n A)
    scTyAt A refl p = p

  mutual
    tm-ren : ∀ {Γ Γ′ t A ρ} → Γ ⊢tm t ∶ A → Γ′ ⊢ren ρ ∶ Γ → Γ′ ⊢tm t [ ρ ]tm ∶ A [ ρ ]ty
    tm-ren (var-wf {i} w eq) r with look r i eq
    ... | j , e , l rewrite e = var-wf (ctx r) l
    tm-ren {Γ′ = Γ′} {ρ = ρ} (coh-wf {Δ = Θ} {A} {t} {u} {τ} p w a ok sτ) r =
      subst (Γ′ ⊢tm coh Θ (arr A t u) (τ ∘ ρ) ∶_)
        (sym (assoc-ty (arr A t u) τ ρ
               (scTyAt (arr A t u) (sym (snd (sub-sc closed laws sτ))) (ty-sc closed laws a))))
        (coh-wf p w a ok (sub-ren w sτ r))
    tm-ren {Γ′ = Γ′} {ρ = ρ} (cst-wf {k} _ v) r =
      subst (Γ′ ⊢tm cst k ∶_) (sym (closed-ty (ty k) ρ (closed k))) (cst-wf (ctx r) v)
    tm-ren {Γ} {Γ′} {ρ = ρ} (bnd-wf {b} {y} {Δ} {ts} scΔ l wt ok as) r =
      subst (Γ′ ⊢tm bnd b y (Δ [ ρ ]tel) (ts ∘ ρ) ∶_)
        (trans (cong (opTy 0 (ts ∘ ρ)) (res-stable b y Δ ρ (lc r) ok))
               (sym (op-[]ty 0 ts (bres b y Δ) ρ (lc r))))
        (bnd-wf (sc-tel[] Δ ρ (subst (λ n → T (scTel? n Δ)) (sym (leq r)) scΔ) (sc r))
                (lc-tel[] 1 Δ ρ l (lc r))
                (ctx (tel-ren Δ wt r scΔ))
                (side-stable b y Δ ρ (lc r) ok)
                (subst (Γ′ ⊢args ts ∘ ρ ∶_) (sym (args-stable b y Δ ρ (lc r) ok)) (args-ren as r)))

    ty-ren : ∀ {Γ Γ′ A ρ} → Γ ⊢ty A → Γ′ ⊢ren ρ ∶ Γ → Γ′ ⊢ty A [ ρ ]ty
    ty-ren (⋆-wf _)     r = ⋆-wf (ctx r)
    ty-ren (arr-wf d e) r = arr-wf (tm-ren d r) (tm-ren e r)

    sub-ren : ∀ {Θ Γ Γ′ τ ρ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Γ′ ⊢ren ρ ∶ Γ → Γ′ ⊢sub τ ∘ ρ ∶ Θ
    sub-ren _ (⟨⟩-wf _) r = ⟨⟩-wf (ctx r)
    sub-ren {Θ ▸ A} {Γ′ = Γ′} {τ ,ₛ t} {ρ} (▸-wf w a) (,-wf sτ d) r =
      ,-wf (sub-ren w sτ r)
        (subst (Γ′ ⊢tm t [ ρ ]tm ∶_)
          (assoc-ty A τ ρ (scTyAt A (sym (snd (sub-sc closed laws sτ))) (ty-sc closed laws a)))
          (tm-ren d r))

    args-ren : ∀ {Γ Γ′ ts Θ ρ} → Γ ⊢args ts ∶ Θ → Γ′ ⊢ren ρ ∶ Γ → Γ′ ⊢args ts ∘ ρ ∶ Θ [ ρ ]tel
    args-ren (⟨⟩-a _) r = ⟨⟩-a (ctx r)
    args-ren {Γ′ = Γ′} {ρ = ρ} (,-a {ts} {Θ} {t} {A} s d) r =
      ,-a (args-ren s r) (subst (Γ′ ⊢tm t [ ρ ]tm ∶_) (op-[]ty 0 ts A ρ (lc r)) (tm-ren d r))

    -- A renaming extends under an opened telescope.
    tel-ren : ∀ {Γ Γ′ ρ} Δ → (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → Γ′ ⊢ren ρ ∶ Γ → T (scTel? (len Γ) Δ) →
              (Γ′ ⧺ openTel (len Γ′) (Δ [ ρ ]tel)) ⊢ren (ρ ++ₛ fresh (len Γ′) (len Δ)) ∶ (Γ ⧺ openTel (len Γ) Δ)
    tel-ren ε _ r _ = r
    tel-ren {Γ} {Γ′} {ρ} (Δ ▸ A) (▸-wf wΞ a) r p =
      subst (λ Z → ((Γ′ ⧺ openTel n′ (Δ [ ρ ]tel)) ▸ Z) ⊢ren ρ′ ,ₛ var (n′ + k) ∶ ((Γ ⧺ Ξ) ▸ X))
            E r″
      where
      n  = len Γ
      n′ = len Γ′
      k  = len Δ
      Ξ  = openTel n Δ
      Ξ′ = openTel n′ (Δ [ ρ ]tel)
      X  = opTy 0 (fresh n k) A
      pΔ = fst (T∧ {scTel? n Δ} p)
      pA = snd (T∧ {scTel? n Δ} p)
      ρ′ = ρ ++ₛ fresh n′ k
      r′ : (Γ′ ⧺ Ξ′) ⊢ren ρ′ ∶ (Γ ⧺ Ξ)
      r′ = tel-ren Δ wΞ r pΔ
      X′ = X [ ρ′ ]ty
      a′ : (Γ′ ⧺ Ξ′) ⊢ty X′
      a′ = ty-ren a r′

      lenρ : lenₛ ρ ≡ n
      lenρ = leq r
      lenΞ′ : len (Γ′ ⧺ Ξ′) ≡ n′ + k
      lenΞ′ = trans (len-⧺ Γ′ Ξ′) (cong (n′ +_) (trans (len-openTel n′ (Δ [ ρ ]tel)) (len-tel[] Δ ρ)))

      E : X′ ≡ opTy 0 (fresh n′ (len (Δ [ ρ ]tel))) (A [ ρ ]ty)
      E = trans (op-[]ty 0 (fresh n k) A ρ′ (lc r′))
                (cong₂ (opTy 0)
                  (trans (cong (λ m → fresh m k ∘ ρ′) (sym lenρ))
                         (trans (fresh-∘ ρ n′ k) (cong (fresh n′) (sym (len-tel[] Δ ρ)))))
                  (ext-ty-++ A ρ (fresh n′ k) (subst (λ m → T (scTy? m A)) (sym lenρ) pA)))

      w″ : ((Γ′ ⧺ Ξ′) ▸ X′) ⊢ctx
      w″ = ▸-wf (ctx r′) a′

      scX : T (scTy? (lenₛ ρ′) X)
      scX = scTyAt X (sym (leq r′)) (ty-sc closed laws a)

      lk : ∀ i {T₀} → lookup ((Γ ⧺ Ξ) ▸ X) i ≡ just T₀ →
           Σ Nat λ j → (lookupₛ (ρ′ ,ₛ var (n′ + k)) i ≡ var j) × (lookup ((Γ′ ⧺ Ξ′) ▸ X′) j ≡ just (T₀ [ ρ′ ,ₛ var (n′ + k) ]ty))
      lk i {T₀} eq with i ==ℕ len (Γ ⧺ Ξ) in e
      ... | true  =
        n′ + k
        , lookupₛ-top ρ′ _ i (trans (==-transport i (leq r′)) e)
        , trans (lookup-top (Γ′ ⧺ Ξ′) X′ (n′ + k) (==-self (sym lenΞ′)))
                (cong just (trans (sym (ext-ty X ρ′ (var (n′ + k)) scX))
                                  (cong (_[ ρ′ ,ₛ var (n′ + k) ]ty) (just-inj eq))))
      ... | false with look r′ i eq
      ...   | j , ej , lj =
        j
        , trans (lookupₛ-pop ρ′ _ i (trans (==-transport i (leq r′)) e)) ej
        , trans (lookup-pop (Γ′ ⧺ Ξ′) X′ j
                   (<→≢ j (len (Γ′ ⧺ Ξ′)) (lookup-< (Γ′ ⧺ Ξ′) j lj)))
                (trans lj (cong just (sym (ext-ty T₀ ρ′ (var (n′ + k))
                   (scTyAt T₀ (sym (leq r′)) (snd (ctx-lookup closed laws wΞ eq)))))))

      r″ : ((Γ′ ⧺ Ξ′) ▸ X′) ⊢ren ρ′ ,ₛ var (n′ + k) ∶ ((Γ ⧺ Ξ) ▸ X)
      r″ = mkRen w″ (cong suc (leq r′)) (∧T (lc r′) tt)
             (∧T (scSub-suc ρ′ (sc r′))
                 (subst (λ m → T ((n′ + k) <ℕ suc m)) (sym lenΞ′) (<-self (n′ + k))))
             lk

  ----------------------------------------------------------------------
  -- Weakening.

  wk-ren : ∀ {Γ B} → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢ren fresh 0 (len Γ) ∶ Γ
  wk-ren {Γ} {B} w@(▸-wf wΓ _) =
    mkRen w (lenₛ-fresh 0 (len Γ)) (lc-fresh 0 (len Γ))
      (scSub-suc (fresh 0 (len Γ)) (sc-fresh 0 (len Γ)))
      λ i {A} eq →
        let (p , a) = ctx-lookup closed laws wΓ eq in
        i , lookup-id (len Γ) i p
          , trans (lookup-pop Γ B i (<→≢ i (len Γ) p)) (trans eq (cong just (sym (id-ty (len Γ) A a))))

  wk-tm : ∀ {Γ B t A} → Γ ⊢tm t ∶ A → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢tm t ∶ A
  wk-tm {Γ} {B} {t} {A} d w =
    subst₂ (λ u X → (Γ ▸ B) ⊢tm u ∶ X)
      (id-tm (len Γ) t (tm-sc closed laws d)) (id-ty (len Γ) A (tm-ty-sc closed laws d))
      (tm-ren d (wk-ren w))
    where
    subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) {x y u v} →
             x ≡ y → u ≡ v → P x u → P y v
    subst₂ P refl refl q = q

  wk-ty : ∀ {Γ B A} → Γ ⊢ty A → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢ty A
  wk-ty {Γ} {B} {A} a w =
    subst ((Γ ▸ B) ⊢ty_) (id-ty (len Γ) A (ty-sc closed laws a)) (ty-ren a (wk-ren w))

  wk-sub : ∀ {Θ Γ B τ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢sub τ ∶ Θ
  wk-sub {Θ} {Γ} {B} {τ} wΘ s w =
    subst (λ σ → (Γ ▸ B) ⊢sub σ ∶ Θ) (id-sub (len Γ) τ (fst (sub-sc closed laws s)))
      (sub-ren wΘ s (wk-ren w))

  wk-args : ∀ {Θ Γ B ts} → Γ ⊢args ts ∶ Θ → (Γ ▸ B) ⊢ctx → T (scTel? 0 Θ) → (Γ ▸ B) ⊢args ts ∶ Θ
  wk-args {Θ} {Γ} {B} {ts} s w p =
    subst₂ (λ σ Θ′ → (Γ ▸ B) ⊢args σ ∶ Θ′) (id-sub (len Γ) ts (args-sc closed laws s))
      (id-tel (len Γ) Θ (scTel-mono Θ p)) (args-ren s (wk-ren w))
    where
    subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) {x y u v} →
             x ≡ y → u ≡ v → P x u → P y v
    subst₂ P refl refl q = q
    scTel-mono : ∀ Θ → T (scTel? 0 Θ) → T (scTel? (len Γ) Θ)
    scTel-mono Θ q = go (len Γ)
      where
      go : ∀ n → T (scTel? n Θ)
      go zero    = q
      go (suc n) = scTel-suc Θ (go n)
