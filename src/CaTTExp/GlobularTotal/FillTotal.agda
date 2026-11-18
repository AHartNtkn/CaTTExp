------------------------------------------------------------------------
-- F2c: totality of the globular filler (lemmas 3–5 assembled).
--
-- For a globular Γ and Γ ⊢ u, v : A with the same strict normal form
-- N, `fillRaw` returns a coherence c with Γ ⊢ c : u →_A v:
--
--   fill-total : Glob Γ → Γ ⊢ u : A → Γ ⊢ v : A →
--                nf u ≡ just N → nf v ≡ just N →
--                Σ c. fillRaw Γ u v A ≡ just c × Γ ⊢ c : arr A u v
--
-- The image of u and v is N (at fillRaw's fuel, by (1′)). With
-- τ = shape N, Θ = ctxOf τ and λ the substitution read off N:
--   * λ is well typed and relabels Θ's tree I to N (P1, LamTyped);
--   * the lift lemma (P5, Lift) at E = I gives u′, v′ : A′ in Θ with
--     u′[λ] = u, v′[λ] = v, A′[λ] = A, and nf u′ = nf v′ = I;
--   * so by (1′) in Θ both u′ and v′ use every variable of Θ, which is
--     the side condition in its coherence form.
-- This is the form `totalN` has for graphs. By completeness of the
-- checker, the certified `fill` returns the same cell (`fill-of-raw`),
-- so `fill-ok`: fill Γ u v A ≡ just (c , d).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FillTotal where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Completeness
open import CaTTExp.Derived using (tm-ctx; ps-ctx)
open import CaTTExp.GlobularFiller
  using (LT; lt; nf; fillRaw; fill; image; fuelFor; ltEq; ltEqs; shape; idTree; zipLab; labSub;
         liftT; liftTy; depthTm; depthTy; module Lists)
open Lists using (listEq)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.PsOrd using (ps-glob)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.NfFuel using (nf-det)
open import CaTTExp.GlobularTotal.NfCoh using (res)
open import CaTTExp.GlobularTotal.Relabel using (relab; lamF; relab-id)
open import CaTTExp.GlobularTotal.LamTyped using (ρ; look-f; labSub-λ; λ-typed)
open import CaTTExp.GlobularTotal.Lift using (lift)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-just : ∀ {A B : Set} (m : Maybe A) (k : A → Maybe B) {x} → m ≡ just x → (m >>= k) ≡ k x
  bind-just m k refl = refl

  and : ∀ {a b} → T a → T b → T (a ∧ b)
  and {true} {true} _ _ = tt

  or-l : ∀ {a b} → T a → T (a ∨ b)
  or-l {true} _ = tt

  lt-split : ∀ a b → T (a <ℕ b) → Σ Nat λ i → b ≡ suc a + i
  lt-split a       zero    ()
  lt-split zero    (suc b) p = b , refl
  lt-split (suc a) (suc b) p with lt-split a b p
  ... | i , e = i , cong suc e

  -- a ≤ b written a < suc b
  ≤-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
  ≤-trans zero    b       c       p q = tt
  ≤-trans (suc a) zero    c       () q
  ≤-trans (suc a) (suc b) zero    p ()
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

  ≤-max-l : ∀ a b → T (a <ℕ suc (max a b))
  ≤-max-l zero    b       = tt
  ≤-max-l (suc a) zero    = ≤-refl a
    where
    ≤-refl : ∀ a → T (a <ℕ suc a)
    ≤-refl zero    = tt
    ≤-refl (suc a) = ≤-refl a
  ≤-max-l (suc a) (suc b) = ≤-max-l a b

  ≤-max-r : ∀ a b → T (b <ℕ suc (max a b))
  ≤-max-r zero    b       = ≤-refl b
    where
    ≤-refl : ∀ a → T (a <ℕ suc a)
    ≤-refl zero    = tt
    ≤-refl (suc a) = ≤-refl a
  ≤-max-r (suc a) zero    = tt
  ≤-max-r (suc a) (suc b) = ≤-max-r a b

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

  listEq-refl : ∀ xs → listEq xs xs ≡ true
  listEq-refl []       = refl
  listEq-refl (x ∷ xs) rewrite ==-self x = listEq-refl xs

  mutual
    ltEq-refl : ∀ a → ltEq a a ≡ true
    ltEq-refl (lt os cs) rewrite listEq-refl os = ltEqs-refl cs

    ltEqs-refl : ∀ cs → ltEqs cs cs ≡ true
    ltEqs-refl []       = refl
    ltEqs-refl (c ∷ cs) rewrite ltEq-refl c = ltEqs-refl cs

  -- membership in the variables of a context
  memL-down : ∀ y n → memL y (downFrom n) ≡ (y <ℕ n)
  memL-down y zero    = refl
  memL-down y (suc n) with y ==ℕ n in e
  ... | true rewrite ==ℕ-sound y n (≡-T e) = sym (T-≡ (lt-suc n))
    where
    lt-suc : ∀ a → T (a <ℕ suc a)
    lt-suc zero    = tt
    lt-suc (suc a) = lt-suc a
  ... | false = trans (memL-down y n) (lt-suc-ne y n e)
    where
    lt-suc-ne : ∀ y n → (y ==ℕ n) ≡ false → (y <ℕ n) ≡ (y <ℕ suc n)
    lt-suc-ne zero    zero    ()
    lt-suc-ne zero    (suc n) e = refl
    lt-suc-ne (suc y) zero    e = refl
    lt-suc-ne (suc y) (suc n) e = lt-suc-ne y n e

  -- ≈? decides equality of the sets of labels
  elem-memL : ∀ y xs → elem y xs ≡ memL y xs
  elem-memL y []       = refl
  elem-memL y (x ∷ xs) = cong ((y ==ℕ x) ∨_) (elem-memL y xs)

  ⊆?-complete : ∀ xs ys → (∀ y → memL y xs ≡ true → memL y ys ≡ true) → T (⊆? xs ys)
  ⊆?-complete []       ys h = tt
  ⊆?-complete (x ∷ xs) ys h =
    and {elem x ys} {⊆? xs ys} (≡-T (trans (elem-memL x ys) (h x (cong (_∨ memL x xs) (==-self x)))))
        (⊆?-complete xs ys (λ y m → h y (∨r (y ==ℕ x) m)))
    where
    ∨r : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
    ∨r true  e = refl
    ∨r false e = e

  ≈?-complete : ∀ xs ys → (∀ y → memL y xs ≡ memL y ys) → T (≈? xs ys)
  ≈?-complete xs ys h = and {⊆? xs ys} {⊆? ys xs} (⊆?-complete xs ys (λ y m → trans (sym (h y)) m))
                            (⊆?-complete ys xs (λ y m → trans (h y) m))

------------------------------------------------------------------------
-- The theorem.

fill-total : ∀ {Γ u v A} → Glob Γ → Γ ⊢tm u ∶ A → Γ ⊢tm v ∶ A →
             ∀ N n n′ → nf n Γ u ≡ just N → nf n′ Γ v ≡ just N →
             Σ Tm λ c → (fillRaw Γ u v A ≡ just c) × (Γ ⊢tm c ∶ arr A u v)
fill-total {Γ} {u} {v} {A} gΓ du dv N n n′ eu ev =
  coh Θ (arr A′ u′ v′) λσ , eq , subst (Γ ⊢tm coh Θ (arr A′ u′ v′) λσ ∶_) tyeq dc
  where
  dΓ = tm-ctx du
  ru = res gΓ du
  rv = res gΓ dv
  Nu≡ : fst ru ≡ N
  Nu≡ = nf-det (suc (depthTm u) + 0) n Γ u (fst ru) N (fst (snd ru) 0) eu
  Nv≡ : fst rv ≡ N
  Nv≡ = nf-det (suc (depthTm v) + 0) n′ Γ v (fst rv) N (fst (snd rv) 0) ev
  wN = subst WF Nu≡ (fst (snd (snd ru)))
  xN : Ex Γ 0 nothing N
  xN = subst (Ex Γ 0 nothing) Nu≡ (fst (snd (snd (snd (snd ru)))))

  fuel = fuelFor u v A
  dA = depthTy A
  du₀ = depthTm u
  dv₀ = depthTm v

  pu : T (du₀ <ℕ fuel)
  pu = ≤-trans du₀ (max du₀ dv₀) (max dA (max du₀ dv₀)) (≤-max-l du₀ dv₀) (≤-max-r dA (max du₀ dv₀))
  pv : T (dv₀ <ℕ fuel)
  pv = ≤-trans dv₀ (max du₀ dv₀) (max dA (max du₀ dv₀)) (≤-max-r du₀ dv₀) (≤-max-r dA (max du₀ dv₀))
  pA : T (dA <ℕ fuel)
  pA = ≤-max-l dA (max du₀ dv₀)

  at : ∀ t a → (∀ m → nf (suc (depthTm t) + m) Γ t ≡ just a) → a ≡ N →
       T (depthTm t <ℕ fuel) → nf fuel Γ t ≡ just N
  at t a fa e p with lt-split (depthTm t) fuel p
  ... | i , q = trans (cong (λ k → nf k Γ t) q) (trans (fa i) (cong just e))

  img : image fuel Γ u v ≡ just N
  img = trans (bind-just (nf fuel Γ u) (λ Nu → nf fuel Γ v >>= λ Nv → guard (ltEq Nu Nv) (λ _ → just Nu)) (at u (fst ru) (fst (snd ru)) Nu≡ pu))
          (trans (bind-just (nf fuel Γ v) (λ Nv → guard (ltEq N Nv) (λ _ → just N)) (at v (fst rv) (fst (snd rv)) Nv≡ pv)) g)
    where
    g : guard (ltEq N N) (λ _ → just N) ≡ just N
    g rewrite ltEq-refl N = refl

  τ = shape N
  I = idTree τ
  Θ = ctxOf τ
  f = lamF (zipLab I N)
  λσ = ρ f (len Θ)
  pΘ = snd (psOf τ)
  dΘ = ps-ctx pΘ
  gΘ = ps-glob pΘ
  lf = look-f Γ gΓ dΓ N xN wN
  rel : relab f I ≡ N
  rel = relab-id τ N refl wN

  Lu = lift Γ gΓ τ dΘ f lf du I (lab-ex τ) (n , trans eu (cong just (sym rel)))
  Lv = lift Γ gΓ τ dΘ f lf dv I (lab-ex τ) (n′ , trans ev (cong just (sym rel)))

  u′ = fst Lu
  A′ = fst (snd Lu)
  v′ = fst Lv
  A′v = fst (snd Lv)

  lTy-u : liftTy fuel Γ A I ≡ just A′
  lTy-u = fst (snd (snd (snd Lu))) fuel pA
  lTy-v : liftTy fuel Γ A I ≡ just A′v
  lTy-v = fst (snd (snd (snd Lv))) fuel pA
  A′≡ : A′v ≡ A′
  A′≡ = just-inj (trans (sym lTy-v) lTy-u)

  lT-u : liftT fuel Γ u I ≡ just u′
  lT-u = fst (snd (snd Lu)) fuel pu
  lT-v : liftT fuel Γ v I ≡ just v′
  lT-v = fst (snd (snd Lv)) fuel pv

  eq : fillRaw Γ u v A ≡ just (coh Θ (arr A′ u′ v′) λσ)
  eq rewrite img | lTy-u | lT-u | lT-v | labSub-λ Γ gΓ dΓ N xN wN = refl

  du′ : Θ ⊢tm u′ ∶ A′
  du′ = fst (snd (snd (snd (snd Lu))))
  dv′ : Θ ⊢tm v′ ∶ A′
  dv′ = subst (Θ ⊢tm v′ ∶_) A′≡ (fst (snd (snd (snd (snd Lv)))))

  -- the side condition: u′ and v′ use every variable of Θ
  full : ∀ {t} → Θ ⊢tm t ∶ A′ → (Σ Nat λ k → nf k Θ t ≡ just I) →
         ∀ y → memL y (fvTmTy t A′) ≡ memL y (varsCtx Θ)
  full {t} dt (k , ek) y with res gΘ dt
  ... | a , fa , _ , _ , _ , _ , la =
    trans (sym (la y))
      (trans (cong (mem y) (nf-det (suc (depthTm t) + 0) k Θ t a I (fa 0) ek))
        (trans (lab-all τ y) (sym (memL-down y (len Θ)))))

  nfu : Σ Nat λ k → nf k Θ u′ ≡ just I
  nfu = (snd (snd (snd (snd (snd (snd (snd Lu)))))))
  nfv : Σ Nat λ k → nf k Θ v′ ≡ just I
  nfv = (snd (snd (snd (snd (snd (snd (snd Lv)))))))

  side : T (cattSide Θ A′ u′ v′)
  side = or-l {isCoh Θ A′ u′ v′} {isOp Θ A′ u′ v′}
           (and {≈? (fvTmTy u′ A′) (varsCtx Θ)} {≈? (fvTmTy v′ A′) (varsCtx Θ)}
                (≈?-complete (fvTmTy u′ A′) (varsCtx Θ) (full du′ nfu))
                (≈?-complete (fvTmTy v′ A′) (varsCtx Θ) (full dv′ nfv)))

  dc : Γ ⊢tm coh Θ (arr A′ u′ v′) λσ ∶ (arr A′ u′ v′) [ λσ ]ty
  dc = coh-wf pΘ dΘ (arr-wf du′ dv′) side (λ-typed Γ gΓ dΓ N xN wN dΘ)

  tyeq : (arr A′ u′ v′) [ λσ ]ty ≡ arr A u v
  tyeq = cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
           (fst (snd (snd (snd (snd (snd (snd Lu)))))))
           (cong₂ _,_ (fst (snd (snd (snd (snd (snd Lu))))))
                      (fst (snd (snd (snd (snd (snd Lv)))))))

------------------------------------------------------------------------
-- The certified filler succeeds: whenever `fillRaw` returns a
-- well-typed cell, `fill` re-checks it and returns that same cell.

private
  module Cp = CaTTExp.Completeness ∅ cattSide (λ ()) (λ ())

fill-of-raw : ∀ {Γ u v A c} → fillRaw Γ u v A ≡ just c → Γ ⊢tm c ∶ arr A u v →
              Σ (Γ ⊢tm c ∶ arr A u v) λ d → fill Γ u v A ≡ just (c , d)
fill-of-raw {Γ} {u} {v} {A} {c} e dc rewrite e
  with checkCtx Γ | Cp.checkCtx-complete (tm-ctx dc)
... | just w | _ with inferTm Γ w c | Cp.inferTm-complete dc w
... | just (B , d) | _ with Cp.tm-unique d dc
... | refl with arr A u v ==Ty arr A u v | ==Ty-sound (arr A u v) (arr A u v) | Cp.==Ty-refl (arr A u v)
... | true | s | _ = subst (Γ ⊢tm c ∶_) (s tt) d , refl

-- Totality of the certified filler: on a globular context, two terms of
-- the same type with the same normal form get a certified filler.
fill-ok : ∀ {Γ u v A} → Glob Γ → Γ ⊢tm u ∶ A → Γ ⊢tm v ∶ A →
          ∀ N n n′ → nf n Γ u ≡ just N → nf n′ Γ v ≡ just N →
          Σ (Σ Tm λ c → Γ ⊢tm c ∶ arr A u v) λ r → fill Γ u v A ≡ just r
fill-ok gΓ du dv N n n′ eu ev with fill-total gΓ du dv N n n′ eu ev
... | c , e , dc with fill-of-raw e dc
... | d , e′ = (c , d) , e′
