------------------------------------------------------------------------
-- Unfolding a table (CaTTExp.Dag.Table) into ordinary CaTT syntax.
--
-- The unfolding functions take fuel. When the table is decreasing
-- (every reference points to a smaller id), the fuel does not matter
-- once it exceeds the ids involved (tm-irr, ctx-irr), so each id has a
-- canonical denotation ⟦ n ⟧ = tmU (suc n) n, and the denotations obey
-- the expected unfolding equations (⟦⟧-V, ⟦⟧-C, ⟦⟧c-E, ⟦⟧c-S). Nothing
-- downstream looks at fuel again.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Dag.Table

module CaTTExp.Dag.Unfold (R : Nat → Maybe Item) where

mutual
  tmU : Nat → Nat → Tm
  tmU zero    n = var 0
  tmU (suc f) n = tmI f (R n)

  tmI : Nat → Maybe Item → Tm
  tmI f (just (V i))    = var i
  tmI f (just (C h as)) = cohI f (R h) as
  tmI f _               = var 0

  cohI : Nat → Maybe Item → List Nat → Tm
  cohI f (just (H c A)) as = coh (ctxU f c) (tyU f A) (subU f as)
  cohI f _              as = var 0

  ctxU : Nat → Nat → Ctx
  ctxU zero    c = ε
  ctxU (suc f) c = ctxI f (R c)

  ctxI : Nat → Maybe Item → Ctx
  ctxI f (just (S c A)) = ctxU f c ▸ tyU f A
  ctxI f _              = ε

  tyU : Nat → RTy → Ty
  tyU f ⋆ᵣ           = ⋆
  tyU f (arrᵣ A s t) = arr (tyU f A) (tmU f s) (tmU f t)

  subU : Nat → List Nat → Sub
  subU f []       = ⟨⟩
  subU f (a ∷ as) = subU f as ,ₛ tmU f a

------------------------------------------------------------------------
-- Denotations, each id with its own fuel

⟦_⟧ : Nat → Tm
⟦ n ⟧ = tmU (suc n) n

⟦_⟧c : Nat → Ctx
⟦ c ⟧c = ctxU (suc c) c

⟦_⟧ty : RTy → Ty
⟦ ⋆ᵣ ⟧ty         = ⋆
⟦ arrᵣ A s t ⟧ty = arr ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧

⟦_⟧s : List Nat → Sub
⟦ [] ⟧s     = ⟨⟩
⟦ a ∷ as ⟧s = ⟦ as ⟧s ,ₛ ⟦ a ⟧

Decreasing : Set
Decreasing = ∀ k it → R k ≡ just it → T (decItem k it)

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

module Irr (dec : Decreasing) where

  mutual
    tm-irr : ∀ f g n → T (n <ℕ f) → T (n <ℕ g) → tmU f n ≡ tmU g n
    tm-irr (suc f) (suc g) n lf lg with R n in eq
    ... | just (V i)    = refl
    ... | just (C h as) =
      let d = dec n (C h as) eq in
      coh-irr f g h as (<-pred h n f (∧-fst d) lf) (<-pred h n g (∧-fst d) lg)
        (belowL-mono n f as lf (∧-snd {h <ℕ n} d))
        (belowL-mono n g as lg (∧-snd {h <ℕ n} d))
    ... | just E        = refl
    ... | just (S _ _)  = refl
    ... | just (H _ _)  = refl
    ... | nothing       = refl

    coh-irr : ∀ f g h as → T (h <ℕ f) → T (h <ℕ g) →
              T (belowL f as) → T (belowL g as) → cohI f (R h) as ≡ cohI g (R h) as
    coh-irr f g h as hf hg af ag with R h in eq
    ... | just (H c A) =
      let d = dec h (H c A) eq in
      cong₃ coh
        (ctx-irr f g c (<-trans c h f (∧-fst d) hf) (<-trans c h g (∧-fst d) hg))
        (ty-irr f g A (belowR-mono h f A (<-suc h f hf) (∧-snd {c <ℕ h} d))
                      (belowR-mono h g A (<-suc h g hg) (∧-snd {c <ℕ h} d)))
        (sub-irr f g as af ag)
    ... | just (V _)    = refl
    ... | just (C _ _)  = refl
    ... | just E        = refl
    ... | just (S _ _)  = refl
    ... | nothing       = refl

    ctx-irr : ∀ f g c → T (c <ℕ f) → T (c <ℕ g) → ctxU f c ≡ ctxU g c
    ctx-irr (suc f) (suc g) c lf lg with R c in eq
    ... | just (S c' A) =
      let d = dec c (S c' A) eq in
      cong₂ _▸_ (ctx-irr f g c' (<-pred c' c f (∧-fst d) lf) (<-pred c' c g (∧-fst d) lg))
        (ty-irr f g A (belowR-mono c f A lf (∧-snd {c' <ℕ c} d))
                      (belowR-mono c g A lg (∧-snd {c' <ℕ c} d)))
    ... | just (V _)    = refl
    ... | just (C _ _)  = refl
    ... | just E        = refl
    ... | just (H _ _)  = refl
    ... | nothing       = refl

    ty-irr : ∀ f g A → T (belowR f A) → T (belowR g A) → tyU f A ≡ tyU g A
    ty-irr f g ⋆ᵣ _ _ = refl
    ty-irr f g (arrᵣ A s t) pf pg =
      let qf = ∧-snd {belowR f A} pf ; qg = ∧-snd {belowR g A} pg in
      cong₃ arr (ty-irr f g A (∧-fst pf) (∧-fst pg))
        (tm-irr f g s (∧-fst qf) (∧-fst qg))
        (tm-irr f g t (∧-snd {s <ℕ f} qf) (∧-snd {s <ℕ g} qg))

    sub-irr : ∀ f g as → T (belowL f as) → T (belowL g as) → subU f as ≡ subU g as
    sub-irr f g []       _  _  = refl
    sub-irr f g (a ∷ as) pf pg =
      cong₂ _,ₛ_ (sub-irr f g as (∧-snd {a <ℕ f} pf) (∧-snd {a <ℕ g} pg))
        (tm-irr f g a (∧-fst pf) (∧-fst pg))

  -- With enough fuel, the fuelled unfoldings are the denotations.
  tmU-⟦⟧ : ∀ f n → T (n <ℕ f) → tmU f n ≡ ⟦ n ⟧
  tmU-⟦⟧ f n p = tm-irr f (suc n) n p (<-suc-self n)

  ctxU-⟦⟧ : ∀ f c → T (c <ℕ f) → ctxU f c ≡ ⟦ c ⟧c
  ctxU-⟦⟧ f c p = ctx-irr f (suc c) c p (<-suc-self c)

  tyU-⟦⟧ : ∀ f A → T (belowR f A) → tyU f A ≡ ⟦ A ⟧ty
  tyU-⟦⟧ f ⋆ᵣ _ = refl
  tyU-⟦⟧ f (arrᵣ A s t) p =
    let q = ∧-snd {belowR f A} p in
    cong₃ arr (tyU-⟦⟧ f A (∧-fst p)) (tmU-⟦⟧ f s (∧-fst q)) (tmU-⟦⟧ f t (∧-snd {s <ℕ f} q))

  subU-⟦⟧ : ∀ f as → T (belowL f as) → subU f as ≡ ⟦ as ⟧s
  subU-⟦⟧ f []       _ = refl
  subU-⟦⟧ f (a ∷ as) p = cong₂ _,ₛ_ (subU-⟦⟧ f as (∧-snd {a <ℕ f} p)) (tmU-⟦⟧ f a (∧-fst p))

  ----------------------------------------------------------------------
  -- Unfolding equations

  ⟦⟧-V : ∀ {n i} → R n ≡ just (V i) → ⟦ n ⟧ ≡ var i
  ⟦⟧-V {n} e rewrite e = refl

  ⟦⟧-C : ∀ {n h as c A} → R n ≡ just (C h as) → R h ≡ just (H c A) →
         ⟦ n ⟧ ≡ coh ⟦ c ⟧c ⟦ A ⟧ty ⟦ as ⟧s
  ⟦⟧-C {n} {h} {as} {c} {A} en eh =
    let dn = dec n (C h as) en ; dh = dec h (H c A) eh
        hn = ∧-fst dn
    in trans (cong (tmI n) en)
      (trans (cong (λ m → cohI n m as) eh)
        (cong₃ coh (ctxU-⟦⟧ n c (<-trans c h n (∧-fst dh) hn))
                   (tyU-⟦⟧ n A (belowR-mono h n A (<-suc h n hn) (∧-snd {c <ℕ h} dh)))
                   (subU-⟦⟧ n as (belowL-mono n n as (<-suc-self n) (∧-snd {h <ℕ n} dn)))))

  ⟦⟧c-E : ∀ {c} → R c ≡ just E → ⟦ c ⟧c ≡ ε
  ⟦⟧c-E {c} e rewrite e = refl

  ⟦⟧c-S : ∀ {c c' A} → R c ≡ just (S c' A) → ⟦ c ⟧c ≡ ⟦ c' ⟧c ▸ ⟦ A ⟧ty
  ⟦⟧c-S {c} {c'} {A} e =
    let d = dec c (S c' A) e in
    trans (cong (ctxI c) e)
      (cong₂ _▸_ (ctxU-⟦⟧ c c' (∧-fst d))
                 (tyU-⟦⟧ c A (belowR-mono c c A (<-suc-self c) (∧-snd {c' <ℕ c} d))))
