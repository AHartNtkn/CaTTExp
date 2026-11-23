------------------------------------------------------------------------
-- Laws of the binder cylinders (CaTTExp.Binder.Cyl).
--
--  * Substitution: for a locally closed σ (acting on free variables),
--    if D′ is D with σ applied (mm ∘ σ, mp ∘ σ, th i [σ], the same
--    selection), then
--      cyl D t [σ]       ≡ cyl D′ (t [σ])           (t touched),
--      cylTy D t A [σ]   ≡ cylTy D′ (t [σ]) (A [σ]).
--    σ does not change which terms are touched (`touched-[]`).
--  * Scoping: if t, A and the datum are scoped in n, so are the
--    cylinder and its type.
-- Both need the filler family scoped (Ksc: K Q B Y in the cylinder
-- context Q↑Y, of length cnt Y).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; Filler; anyL; cnt)

module CaTTExp.Binder.CylLaws (𝕊 : Signature) (KF : Filler) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Pasting 𝕊 using (embTm; toPure; toPureTy)
open import CaTTExp.Binder.Cyl 𝕊 KF

------------------------------------------------------------------------
-- Generic helpers.

dim-[]′ : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[]′ ⋆           σ = refl
dim-[]′ (arr A _ _) σ = cong suc (dim-[]′ A σ)

++-[] : ∀ {X : Set} (xs : List X) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

anyL-++ : ∀ f xs ys → anyL f (xs ++ ys) ≡ (anyL f xs ∨ anyL f ys)
anyL-++ f []       ys = refl
anyL-++ f (x ∷ xs) ys rewrite anyL-++ f xs ys with f x
... | true  = refl
... | false = refl

private
  ==-lt : ∀ e k d → T (e <ℕ k) → (e ==ℕ (k + d)) ≡ false
  ==-lt zero    (suc k) d _ = refl
  ==-lt (suc e) (suc k) d p = ==-lt e k d p

------------------------------------------------------------------------
-- Locally closed terms mention no outer bound variable.

mutual
  occ-lcTy : ∀ k d A → T (lcTy? k A) → occTy (k + d) A ≡ []
  occ-lcTy k d ⋆           _ = refl
  occ-lcTy k d (arr A t u) p
    rewrite occ-lcTy k d A (fst (T∧ {lcTy? k A} p))
          | occ-lcTm k d t (fst (T∧ {lcTm? k t} (snd (T∧ {lcTy? k A} p))))
          | occ-lcTm k d u (snd (T∧ {lcTm? k t} (snd (T∧ {lcTy? k A} p)))) = refl

  occ-lcTm : ∀ k d t → T (lcTm? k t) → occTm (k + d) t ≡ []
  occ-lcTm k d (var _)       _ = refl
  occ-lcTm k d (bvar e j)    p rewrite ==-lt e k d p = refl
  occ-lcTm k d (coh _ _ σ)   p = occ-lcSub k d σ p
  occ-lcTm k d (cst _)       _ = refl
  occ-lcTm k d (bnd _ _ Δ σ) p
    rewrite occ-lcTel (suc k) d Δ (fst (T∧ {lcTel? (suc k) Δ} p))
          | occ-lcSub k d σ (snd (T∧ {lcTel? (suc k) Δ} p)) = refl

  occ-lcTel : ∀ k d Δ → T (lcTel? k Δ) → occTel (k + d) Δ ≡ []
  occ-lcTel k d ε             _ = refl
  occ-lcTel k d (Δ ▸[ _ ] A) p
    rewrite occ-lcTel k d Δ (fst (T∧ {lcTel? k Δ} p))
          | occ-lcTy k d A (snd (T∧ {lcTel? k Δ} p)) = refl

  occ-lcSub : ∀ k d σ → T (lcSub? k σ) → occSub (k + d) σ ≡ []
  occ-lcSub k d ⟨⟩       _ = refl
  occ-lcSub k d (σ ,ₛ t) p
    rewrite occ-lcSub k d σ (fst (T∧ {lcSub? k σ} p))
          | occ-lcTm k d t (snd (T∧ {lcSub? k σ} p)) = refl

------------------------------------------------------------------------
-- The filler, scoped in the cylinder context.

KScoped : Set
KScoped = ∀ Q B Y → T (scTm? (cnt Y) (embTm (KF Q B Y)))

fillK-sc : KScoped → ∀ Q B Y → T (scTm? (cnt Y) (fillK Q B Y))
fillK-sc Ksc Q B Y with toPure Q | toPureTy B
... | just Q₀  | just B₀  = Ksc Q₀ B₀ Y
... | just _   | nothing  = tt
... | nothing  | _        = tt

lenₛ-liftS : ∀ D γ → lenₛ (liftS D γ) ≡ cnt (mask D γ)
lenₛ-liftS D ⟨⟩       = refl
lenₛ-liftS D (γ ,ₛ t) with touched D t
... | true  = cong (λ m → suc (suc (suc m))) (lenₛ-liftS D γ)
... | false = cong suc (lenₛ-liftS D γ)

------------------------------------------------------------------------
-- Substitution.

module Subst (σ : Sub) (l : LC σ) where

  mutual
    occ-[]ty : ∀ d A → occTy d (A [ σ ]ty) ≡ occTy d A
    occ-[]ty d ⋆           = refl
    occ-[]ty d (arr A t u) rewrite occ-[]ty d A | occ-[]tm d t | occ-[]tm d u = refl

    occ-[]tm : ∀ d t → occTm d (t [ σ ]tm) ≡ occTm d t
    occ-[]tm d (var i)       = occ-lcTm 0 d (lookupₛ σ i) (lc-lookup σ i l)
    occ-[]tm d (bvar e j)    = refl
    occ-[]tm d (coh _ _ τ)   = occ-[]sub d τ
    occ-[]tm d (cst _)       = refl
    occ-[]tm d (bnd _ _ Δ τ) rewrite occ-[]tel (suc d) Δ | occ-[]sub d τ = refl

    occ-[]tel : ∀ d Δ → occTel d (Δ [ σ ]tel) ≡ occTel d Δ
    occ-[]tel d ε             = refl
    occ-[]tel d (Δ ▸[ _ ] A) rewrite occ-[]tel d Δ | occ-[]ty d A = refl

    occ-[]sub : ∀ d τ → occSub d (τ ∘ σ) ≡ occSub d τ
    occ-[]sub d ⟨⟩       = refl
    occ-[]sub d (τ ,ₛ t) rewrite occ-[]sub d τ | occ-[]tm d t = refl

  -- D′ is D with σ applied.
  record Rel (D D′ : Datum) : Set where
    field
      mmR  : mm D ∘ σ ≡ mm D′
      mpR  : mp D ∘ σ ≡ mp D′
      selR : ∀ i → sel D i ≡ sel D′ i
      thR  : ∀ i → th D i [ σ ]tm ≡ th D′ i

  module _ {D D′ : Datum} (R : Rel D D′) where
    open Rel R

    anyL-sel : ∀ xs → anyL (sel D′) xs ≡ anyL (sel D) xs
    anyL-sel []       = refl
    anyL-sel (x ∷ xs) rewrite selR x | anyL-sel xs = refl

    touched-[] : ∀ t → touched D′ (t [ σ ]tm) ≡ touched D t
    touched-[] t rewrite occ-[]tm 0 t = anyL-sel (occTm 0 t)

    mask-[] : ∀ γ → mask D′ (γ ∘ σ) ≡ mask D γ
    mask-[] ⟨⟩       = refl
    mask-[] (γ ,ₛ t) = cong₂ _◂_ (mask-[] γ) (touched-[] t)

  ----------------------------------------------------------------------
  -- The whiskers.

  sph-∘ : ∀ C → sphSub C ∘ σ ≡ sphSub (C [ σ ]ty)
  sph-∘ ⋆           = refl
  sph-∘ (arr C s t) rewrite sph-∘ C = refl

  baseAt-[] : ∀ k A → baseAt k A [ σ ]ty ≡ baseAt k (A [ σ ]ty)
  baseAt-[] k ⋆           = refl
  baseAt-[] k (arr A s u) rewrite dim-[]′ A σ with k ==ℕ suc (dim A)
  ... | true  = refl
  ... | false = baseAt-[] k A

  tgtAt-[] : ∀ k A → tgtAt k A [ σ ]tm ≡ tgtAt k (A [ σ ]ty)
  tgtAt-[] k ⋆           = refl
  tgtAt-[] k (arr A s u) rewrite dim-[]′ A σ with k ==ℕ dim A
  ... | true  = refl
  ... | false = tgtAt-[] k A

  srcAt-[] : ∀ k A → srcAt k A [ σ ]tm ≡ srcAt k (A [ σ ]ty)
  srcAt-[] k ⋆           = refl
  srcAt-[] k (arr A s u) rewrite dim-[]′ A σ with k ==ℕ dim A
  ... | true  = refl
  ... | false = srcAt-[] k A

  σR-∘ : ∀ c C z h → σR c C z h ∘ σ ≡ σR (c [ σ ]tm) (C [ σ ]ty) (z [ σ ]tm) (h [ σ ]tm)
  σR-∘ c C z h rewrite sph-∘ C = refl

  hL-[] : ∀ k x C → hL k x C [ σ ]ty ≡ hL k (x [ σ ]tm) (C [ σ ]ty)
  hL-[] k x C rewrite baseAt-[] k C | srcAt-[] k C = refl

  σLp-∘ : ∀ k j h x C → σLp k j h x C ∘ σ ≡ σLp k j (h [ σ ]tm) (x [ σ ]tm) (C [ σ ]ty)
  σLp-∘ k zero    h x C            rewrite sph-∘ (hL k x C) | baseAt-[] k C | srcAt-[] k C | tgtAt-[] k C = refl
  σLp-∘ k (suc j) h x ⋆            = refl
  σLp-∘ k (suc j) h x (arr C' s t) rewrite σLp-∘ k j h x C' = refl

  rwI-[] : ∀ k n c C z h h′ b → (b ≡ true → h [ σ ]tm ≡ h′) →
           rwI k n c C z h b [ σ ]tm ≡ rwI k n (c [ σ ]tm) (C [ σ ]ty) (z [ σ ]tm) h′ b
  rwI-[] k n c C z h h′ true  e rewrite σR-∘ c C z h | e refl = refl
  rwI-[] k n c C z h h′ false e = refl

  lwI-[] : ∀ k n h h′ x c C b → (b ≡ true → h [ σ ]tm ≡ h′) →
           lwI k n h x c C b [ σ ]tm ≡ lwI k n h′ (x [ σ ]tm) (c [ σ ]tm) (C [ σ ]ty) b
  lwI-[] k n h h′ x c C true  e rewrite σLp-∘ k (n ∸ suc k) h x C | e refl = refl
  lwI-[] k n h h′ x c C false e = refl

  ----------------------------------------------------------------------
  -- The cylinders.

  module _ (Ksc : KScoped) where

    module _ {D D′ : Datum} (R : Rel D D′) where
      open Rel R

      mutual
        cyl-[] : ∀ t → touched D t ≡ true → cyl D t [ σ ]tm ≡ cyl D′ (t [ σ ]tm)
        cyl-[] (var i)       ()
        cyl-[] (bvar e i)    _ with e ==ℕ 0
        ... | true  = thR i
        ... | false = refl
        cyl-[] (coh Q B γ)   _ =
          trans (assoc-tm (fillK Q B (mask D γ)) (liftS D γ) σ
                  (subst (λ m → T (scTm? m (fillK Q B (mask D γ)))) (sym (lenₛ-liftS D γ))
                         (fillK-sc Ksc Q B (mask D γ))))
                (cong₂ (λ Y τ → fillK Q B Y [ τ ]tm) (sym (mask-[] R γ)) (liftS-[] γ))
        cyl-[] (cst _)       ()
        cyl-[] (bnd _ _ _ _) _ = refl

        liftS-[] : ∀ γ → liftS D γ ∘ σ ≡ liftS D′ (γ ∘ σ)
        liftS-[] ⟨⟩       = refl
        liftS-[] (γ ,ₛ t) rewrite touched-[] R t with touched D t in e
        ... | true  rewrite liftS-[] γ | op-[]tm 0 (mm D) t σ l | op-[]tm 0 (mp D) t σ l | mmR | mpR
                          | cyl-[] t e = refl
        ... | false rewrite liftS-[] γ | op-[]tm 0 (mm D) t σ l | mmR = refl

      Pq Lq : Nat → Set
      Pq k = ∀ t A → P D k t A [ σ ]tm ≡ P D′ k (t [ σ ]tm) (A [ σ ]ty)
      Lq k = ∀ t A → L D k t A [ σ ]tm ≡ L D′ k (t [ σ ]tm) (A [ σ ]ty)
      TPq TLq : Nat → Set
      TPq k = ∀ A → TP D k A [ σ ]ty ≡ TP D′ k (A [ σ ]ty)
      TLq k = ∀ A → TL D k A [ σ ]ty ≡ TL D′ k (A [ σ ]ty)

      record At (k : Nat) : Set where
        field
          pq  : Pq k
          tpq : TPq k
          lq  : Lq k
          tlq : TLq k

      at : ∀ k → At k
      at zero = record
        { pq  = λ t A → trans (op-[]tm 0 (mm D) t σ l) (cong (λ M → opTm 0 M (t [ σ ]tm)) mmR)
        ; tpq = λ A → trans (op-[]ty 0 (mm D) A σ l) (cong (λ M → opTy 0 M (A [ σ ]ty)) mmR)
        ; lq  = λ t A → trans (op-[]tm 0 (mp D) t σ l) (cong (λ M → opTm 0 M (t [ σ ]tm)) mpR)
        ; tlq = λ A → trans (op-[]ty 0 (mp D) A σ l) (cong (λ M → opTy 0 M (A [ σ ]ty)) mpR)
        }
      at (suc k) = record { pq = pS ; tpq = tpS ; lq = lS ; tlq = tlS }
        where
        open At (at k)

        pS : Pq (suc k)
        pS t A =
          trans (rwI-[] k (dim A) (P D k t A) (TP D k A) (L D k (tgtAt k A) (baseAt k A))
                        (cyl D (tgtAt k A)) (cyl D′ (tgtAt k A [ σ ]tm)) (touched D (tgtAt k A))
                        (cyl-[] (tgtAt k A)))
                e2
          where
          tch : touched D (tgtAt k A) ≡ touched D′ (tgtAt k (A [ σ ]ty))
          tch = sym (trans (cong (touched D′) (sym (tgtAt-[] k A))) (touched-[] R (tgtAt k A)))
          e2 : rwI k (dim A) (P D k t A [ σ ]tm) (TP D k A [ σ ]ty) (L D k (tgtAt k A) (baseAt k A) [ σ ]tm)
                   (cyl D′ (tgtAt k A [ σ ]tm)) (touched D (tgtAt k A))
               ≡ rwI k (dim (A [ σ ]ty)) (P D′ k (t [ σ ]tm) (A [ σ ]ty)) (TP D′ k (A [ σ ]ty))
                     (L D′ k (tgtAt k (A [ σ ]ty)) (baseAt k (A [ σ ]ty)))
                     (cyl D′ (tgtAt k (A [ σ ]ty))) (touched D′ (tgtAt k (A [ σ ]ty)))
          e2 rewrite pq t A | tpq A | lq (tgtAt k A) (baseAt k A)
                   | tgtAt-[] k A | baseAt-[] k A | tch | dim-[]′ A σ = refl

        lS : Lq (suc k)
        lS t A =
          trans (lwI-[] k (dim A) (cyl D (srcAt k A)) (cyl D′ (srcAt k A [ σ ]tm))
                        (P D k (srcAt k A) (baseAt k A)) (L D k t A) (TL D k A) (touched D (srcAt k A))
                        (cyl-[] (srcAt k A)))
                e2
          where
          tch : touched D (srcAt k A) ≡ touched D′ (srcAt k (A [ σ ]ty))
          tch = sym (trans (cong (touched D′) (sym (srcAt-[] k A))) (touched-[] R (srcAt k A)))
          e2 : lwI k (dim A) (cyl D′ (srcAt k A [ σ ]tm)) (P D k (srcAt k A) (baseAt k A) [ σ ]tm)
                   (L D k t A [ σ ]tm) (TL D k A [ σ ]ty) (touched D (srcAt k A))
               ≡ lwI k (dim (A [ σ ]ty)) (cyl D′ (srcAt k (A [ σ ]ty)))
                     (P D′ k (srcAt k (A [ σ ]ty)) (baseAt k (A [ σ ]ty)))
                     (L D′ k (t [ σ ]tm) (A [ σ ]ty)) (TL D′ k (A [ σ ]ty)) (touched D′ (srcAt k (A [ σ ]ty)))
          e2 rewrite pq (srcAt k A) (baseAt k A) | lq t A | tlq A
                   | srcAt-[] k A | baseAt-[] k A | tch | dim-[]′ A σ = refl

        tpS : TPq (suc k)
        tpS ⋆ = refl
        tpS (arr A s u) rewrite dim-[]′ A σ with k ==ℕ dim A
        ... | true  rewrite tpq A | pq s A | lq u A | dim-[]′ A σ = refl
        ... | false rewrite tpS A | pS s A | pS u A | dim-[]′ A σ = refl

        tlS : TLq (suc k)
        tlS ⋆ = refl
        tlS (arr A s u) rewrite dim-[]′ A σ with k ==ℕ dim A
        ... | true  rewrite tpq A | pq s A | lq u A | dim-[]′ A σ = refl
        ... | false rewrite tlS A | lS s A | lS u A | dim-[]′ A σ = refl

      cylTy-[] : ∀ t A → cylTy D t A [ σ ]ty ≡ cylTy D′ (t [ σ ]tm) (A [ σ ]ty)
      cylTy-[] t A rewrite dim-[]′ A σ | At.tpq (at (dim A)) A | At.pq (at (dim A)) t A
                         | At.lq (at (dim A)) t A = refl

------------------------------------------------------------------------
-- Scoping.

module Scope (n : Nat) (Ksc : KScoped) where

  sph-sc : ∀ C → T (scTy? n C) → T (scSub? n (sphSub C))
  sph-sc ⋆           _ = tt
  sph-sc (arr C s t) p =
    let (pC , q) = T∧ {scTy? n C} p ; (ps , pt) = T∧ {scTm? n s} q
    in ∧T (∧T (sph-sc C pC) ps) pt

  baseAt-sc : ∀ k A → T (scTy? n A) → T (scTy? n (baseAt k A))
  baseAt-sc k ⋆           _ = tt
  baseAt-sc k (arr A s u) p with k ==ℕ suc (dim A)
  ... | true  = p
  ... | false = baseAt-sc k A (fst (T∧ {scTy? n A} p))

  tgtAt-sc : ∀ k A → T (scTy? n A) → T (scTm? n (tgtAt k A))
  tgtAt-sc k ⋆           _ = tt
  tgtAt-sc k (arr A s u) p with k ==ℕ dim A
  ... | true  = snd (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
  ... | false = tgtAt-sc k A (fst (T∧ {scTy? n A} p))

  srcAt-sc′ : ∀ k A → T (scTy? n A) → T (scTm? n (srcAt k A))
  srcAt-sc′ k ⋆           _ = tt
  srcAt-sc′ k (arr A s u) p with k ==ℕ dim A
  ... | true  = fst (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
  ... | false = srcAt-sc′ k A (fst (T∧ {scTy? n A} p))

  rwI-sc : ∀ k m c C z h b → T (scTm? n c) → T (scTy? n C) → T (scTm? n z) → (b ≡ true → T (scTm? n h)) →
           T (scTm? n (rwI k m c C z h b))
  rwI-sc k m c C z h true  pc pC pz ph = ∧T (∧T (∧T (sph-sc C pC) pc) pz) (ph refl)
  rwI-sc k m c C z h false pc pC pz ph = pc

  lwI-sc : ∀ k m h x c C b → (b ≡ true → T (scTm? n h)) → T (scTm? n x) → T (scTm? n c) → T (scTy? n C) →
           T (scTm? n (lwI k m h x c C b))
  lwI-sc k m h x c C true  ph px pc pC = ∧T (σLp-sc k (m ∸ suc k) C pC) pc
    where
    σLp-sc : ∀ k j C → T (scTy? n C) → T (scSub? n (σLp k j h x C))
    σLp-sc k zero    C p =
      ∧T (∧T (sph-sc (hL k x C) (∧T (baseAt-sc k C p) (∧T px (srcAt-sc′ k C p)))) (ph refl)) (tgtAt-sc k C p)
    σLp-sc k (suc j) ⋆            p = tt
    σLp-sc k (suc j) (arr C′ s t) p =
      let (pC , q) = T∧ {scTy? n C′} p ; (ps , pt) = T∧ {scTm? n s} q
      in ∧T (∧T (σLp-sc k j C′ pC) ps) pt
  lwI-sc k m h x c C false ph px pc pC = pc

  module _ (D : Datum) (pmm : T (scSub? n (mm D))) (pmp : T (scSub? n (mp D)))
           (pth : ∀ i → T (scTm? n (th D i))) where

    mutual
      cyl-sc : ∀ t → T (scTm? n t) → T (scTm? n (cyl D t))
      cyl-sc (var _)       _ = tt
      cyl-sc (bvar e i)    _ with e ==ℕ 0
      ... | true  = pth i
      ... | false = tt
      cyl-sc (coh Q B γ)   p =
        sc-tm[] (fillK Q B (mask D γ)) (liftS D γ)
          (subst (λ m → T (scTm? m (fillK Q B (mask D γ)))) (sym (lenₛ-liftS D γ)) (fillK-sc Ksc Q B (mask D γ)))
          (liftS-sc γ p)
      cyl-sc (cst _)       _ = tt
      cyl-sc (bnd _ _ _ _) _ = tt

      liftS-sc : ∀ γ → T (scSub? n γ) → T (scSub? n (liftS D γ))
      liftS-sc ⟨⟩       _ = tt
      liftS-sc (γ ,ₛ t) p with touched D t
      ... | true  = ∧T (∧T (∧T (liftS-sc γ pγ) (sc-opTm 0 (mm D) t pmm pt)) (sc-opTm 0 (mp D) t pmp pt)) (cyl-sc t pt)
        where pγ = fst (T∧ {scSub? n γ} p) ; pt = snd (T∧ {scSub? n γ} p)
      ... | false = ∧T (liftS-sc γ pγ) (sc-opTm 0 (mm D) t pmm pt)
        where pγ = fst (T∧ {scSub? n γ} p) ; pt = snd (T∧ {scSub? n γ} p)

    record ScAt (k : Nat) : Set where
      field
        psc  : ∀ t A → T (scTm? n t) → T (scTy? n A) → T (scTm? n (P D k t A))
        tpsc : ∀ A → T (scTy? n A) → T (scTy? n (TP D k A))
        lsc  : ∀ t A → T (scTm? n t) → T (scTy? n A) → T (scTm? n (L D k t A))
        tlsc : ∀ A → T (scTy? n A) → T (scTy? n (TL D k A))

    scAt : ∀ k → ScAt k
    scAt zero = record
      { psc  = λ t A pt _ → sc-opTm 0 (mm D) t pmm pt
      ; tpsc = λ A pA → sc-opTy 0 (mm D) A pmm pA
      ; lsc  = λ t A pt _ → sc-opTm 0 (mp D) t pmp pt
      ; tlsc = λ A pA → sc-opTy 0 (mp D) A pmp pA
      }
    scAt (suc k) = record { psc = pS ; tpsc = tpS ; lsc = lS ; tlsc = tlS }
      where
      open ScAt (scAt k)

      pS : ∀ t A → T (scTm? n t) → T (scTy? n A) → T (scTm? n (P D (suc k) t A))
      pS t A pt pA =
        rwI-sc k (dim A) _ _ _ _ (touched D (tgtAt k A)) (psc t A pt pA) (tpsc A pA)
          (lsc (tgtAt k A) (baseAt k A) (tgtAt-sc k A pA) (baseAt-sc k A pA))
          (λ _ → cyl-sc (tgtAt k A) (tgtAt-sc k A pA))

      lS : ∀ t A → T (scTm? n t) → T (scTy? n A) → T (scTm? n (L D (suc k) t A))
      lS t A pt pA =
        lwI-sc k (dim A) _ _ _ _ (touched D (srcAt k A))
          (λ _ → cyl-sc (srcAt k A) (srcAt-sc′ k A pA))
          (psc (srcAt k A) (baseAt k A) (srcAt-sc′ k A pA) (baseAt-sc k A pA))
          (lsc t A pt pA) (tlsc A pA)

      tpS : ∀ A → T (scTy? n A) → T (scTy? n (TP D (suc k) A))
      tpS ⋆           _ = tt
      tpS (arr A s u) p with k ==ℕ dim A
      ... | true  = ∧T (tpsc A pA) (∧T (psc s A ps pA) (lsc u A pu pA))
        where pA = fst (T∧ {scTy? n A} p) ; ps = fst (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
              pu = snd (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
      ... | false = ∧T (tpS A pA) (∧T (pS s A ps pA) (pS u A pu pA))
        where pA = fst (T∧ {scTy? n A} p) ; ps = fst (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
              pu = snd (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))

      tlS : ∀ A → T (scTy? n A) → T (scTy? n (TL D (suc k) A))
      tlS ⋆           _ = tt
      tlS (arr A s u) p with k ==ℕ dim A
      ... | true  = ∧T (tpsc A pA) (∧T (psc s A ps pA) (lsc u A pu pA))
        where pA = fst (T∧ {scTy? n A} p) ; ps = fst (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
              pu = snd (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
      ... | false = ∧T (tlS A pA) (∧T (lS s A ps pA) (lS u A pu pA))
        where pA = fst (T∧ {scTy? n A} p) ; ps = fst (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))
              pu = snd (T∧ {scTm? n s} (snd (T∧ {scTy? n A} p)))

    cylTy-sc : ∀ t A → T (scTm? n t) → T (scTy? n A) → T (scTy? n (cylTy D t A))
    cylTy-sc t A pt pA =
      ∧T (ScAt.tpsc (scAt (dim A)) A pA) (∧T (ScAt.psc (scAt (dim A)) t A pt pA) (ScAt.lsc (scAt (dim A)) t A pt pA))
