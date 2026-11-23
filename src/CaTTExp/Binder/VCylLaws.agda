------------------------------------------------------------------------
-- Substitution commutation for the free-variable binder cylinders
-- (CaTTExp.Binder.VCyl), ported from CaTTExp.Naturality.Commute:
--
--   pre σ D   = (σ ∘ mm, σ ∘ mp, q ↦ touched (σ q), q ↦ cyl D (σ q))
--   D [ S ]D  = (mm ∘ S, mp ∘ S, sel, th[S])
--
--   cyl-pre  : cyl D (t [ σ ]) ≡ cyl (pre σ D) t
--   cyl-sub  : cyl D t [ S ]   ≡ cyl (D [ S ]D) t
--   cylTy-pre, cylTy-sub, and extensionality (`Ext`).
--
-- Binder syntax adds bound variables, constants and binder terms, whose
-- cylinder is junk on both sides; and its iterated boundaries are
-- Binder.Cyl's, which commute with every substitution (CylLaws.Whisk),
-- so some hypotheses of Commute's lemmas are not needed. Purely
-- syntactic: no typing is assumed. Premises: cyl-pre and cylTy-pre
-- need t (and A) scoped in σ (scTm? (lenₛ σ)); cyl-sub and cylTy-sub
-- (module Post) need a scoped filler family (KScoped), equal lengths
-- of mm and mp, and t, A scoped in them; Ext needs agreement below the
-- scope n.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; Filler; anyL; cnt)
open import CaTTExp.GrayCtx.NaturalWF using (n<sn; ≡-T)
open import CaTTExp.Derived using (nB)

module CaTTExp.Binder.VCylLaws (𝕊 : Signature) (KF : Filler) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.VCyl 𝕊 KF
open import CaTTExp.Binder.CylLaws 𝕊 KF
  using (dim-[]′; anyL-++; KScoped; fillK-sc; module Whisk)

------------------------------------------------------------------------
-- Small facts.

lt-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
lt-ne zero    zero    _ ()
lt-ne zero    (suc n) _ _ = tt
lt-ne (suc i) zero    p _ = ⊥-elim (no i p)
  where no : ∀ i → T (i <ℕ 0) → ⊥
        no zero    ()
        no (suc i) ()
lt-ne (suc i) (suc n) p q = lt-ne i n p q

eq-sound : ∀ {i n} → (i ==ℕ n) ≡ true → i ≡ n
eq-sound {i} {n} e = ==ℕ-sound i n (≡-T e)

le-zero : ∀ k → T (k <ℕ suc 0) → k ≡ 0
le-zero zero _ = refl
le-zero (suc k) ()

ifCase : ∀ {a} {X : Set a} {x y x' y' : X} (b : Bool) → (b ≡ true → x ≡ x') → (b ≡ false → y ≡ y') →
         (if b then x else y) ≡ (if b then x' else y')
ifCase true  f g = f refl
ifCase false f g = g refl

arr≡ : ∀ {A A' s s' u u'} → A ≡ A' → s ≡ s' → u ≡ u' → arr A s u ≡ arr A' s' u'
arr≡ refl refl refl = refl

∨-false : ∀ a → (a ∨ false) ≡ a
∨-false true  = refl
∨-false false = refl

scArr : ∀ {n A t u} → T (scTy? n (arr A t u)) → T (scTy? n A) × T (scTm? n t) × T (scTm? n u)
scArr {n} {A} {t} {u} p =
  let (a , q) = T∧ {scTy? n A} p
      (b , c) = T∧ {scTm? n t} q
  in a , b , c

dim-baseAt : ∀ k A → T (k <ℕ suc (dim A)) → dim (baseAt k A) ≡ k
dim-baseAt k ⋆           p = sym (le-zero k p)
dim-baseAt k (arr A s u) p with k ==ℕ suc (dim A) in e
... | true  = sym (eq-sound e)
... | false = dim-baseAt k A (lt-ne k (suc (dim A)) p e)

sc-baseAt : ∀ {n} k A → T (scTy? n A) → T (scTy? n (baseAt k A))
sc-baseAt k ⋆           s = tt
sc-baseAt k (arr A s u) a with k ==ℕ suc (dim A)
... | true  = a
... | false = sc-baseAt k A (fst (scArr {_} {A} {s} {u} a))

sc-tgtAt : ∀ {n} k A → T (k <ℕ dim A) → T (scTy? n A) → T (scTm? n (tgtAt k A))
sc-tgtAt k (arr A s u) p a with k ==ℕ dim A in e
... | true  = snd (snd (scArr {_} {A} {s} {u} a))
... | false = sc-tgtAt k A (lt-ne k (dim A) p e) (fst (scArr {_} {A} {s} {u} a))

sc-srcAt : ∀ {n} k A → T (k <ℕ dim A) → T (scTy? n A) → T (scTm? n (srcAt k A))
sc-srcAt k (arr A s u) p a with k ==ℕ dim A in e
... | true  = fst (snd (scArr {_} {A} {s} {u} a))
... | false = sc-srcAt k A (lt-ne k (dim A) p e) (fst (scArr {_} {A} {s} {u} a))

k≤W : ∀ k A → T (k <ℕ dim A) → T (k <ℕ suc (dim (baseAt k A)))
k≤W k A p = subst (λ m → T (k <ℕ suc m)) (sym (dim-baseAt k A (<-suc k (dim A) p))) (n<sn k)

------------------------------------------------------------------------
-- Free variables under substitution, through anyL.

module _ (f : Nat → Bool) (σ : Sub) where
  img : Nat → Bool
  img y = anyL f (fvTm (lookupₛ σ y))

  private
    ++3 : ∀ g xs ys zs → anyL g (xs ++ ys ++ zs) ≡ (anyL g xs ∨ anyL g ys ∨ anyL g zs)
    ++3 g xs ys zs rewrite anyL-++ g xs (ys ++ zs) | anyL-++ g ys zs = refl

  mutual
    anyL-ty : ∀ A → anyL f (fvTy (A [ σ ]ty)) ≡ anyL img (fvTy A)
    anyL-ty ⋆           = refl
    anyL-ty (arr A t u) rewrite ++3 f (fvTy (A [ σ ]ty)) (fvTm (t [ σ ]tm)) (fvTm (u [ σ ]tm))
                              | ++3 img (fvTy A) (fvTm t) (fvTm u)
                              | anyL-ty A | anyL-tm t | anyL-tm u = refl

    anyL-tm : ∀ t → anyL f (fvTm (t [ σ ]tm)) ≡ anyL img (fvTm t)
    anyL-tm (var i)       = sym (∨-false (img i))
    anyL-tm (bvar _ _)    = refl
    anyL-tm (coh Q A τ)   = anyL-sub τ
    anyL-tm (cst _)       = refl
    anyL-tm (bnd _ _ Δ τ) rewrite anyL-++ f (fvTel (Δ [ σ ]tel)) (fvSub (τ ∘ σ))
                                | anyL-++ img (fvTel Δ) (fvSub τ)
                                | anyL-tel Δ | anyL-sub τ = refl

    anyL-tel : ∀ Δ → anyL f (fvTel (Δ [ σ ]tel)) ≡ anyL img (fvTel Δ)
    anyL-tel ε             = refl
    anyL-tel (Δ ▸[ _ ] A) rewrite anyL-++ f (fvTel (Δ [ σ ]tel)) (fvTy (A [ σ ]ty))
                                | anyL-++ img (fvTel Δ) (fvTy A)
                                | anyL-tel Δ | anyL-ty A = refl

    anyL-sub : ∀ τ → anyL f (fvSub (τ ∘ σ)) ≡ anyL img (fvSub τ)
    anyL-sub ⟨⟩       = refl
    anyL-sub (τ ,ₛ t) rewrite anyL-++ f (fvSub (τ ∘ σ)) (fvTm (t [ σ ]tm))
                            | anyL-++ img (fvSub τ) (fvTm t)
                            | anyL-sub τ | anyL-tm t = refl

-- anyL depends only on the values of f on the variables in scope.
module _ {n : Nat} (f g : Nat → Bool) (e : ∀ i → T (i <ℕ n) → f i ≡ g i) where
  mutual
    aext-ty : ∀ A → T (scTy? n A) → anyL f (fvTy A) ≡ anyL g (fvTy A)
    aext-ty ⋆           _ = refl
    aext-ty (arr A t u) p
      rewrite anyL-++ f (fvTy A) (fvTm t ++ fvTm u) | anyL-++ g (fvTy A) (fvTm t ++ fvTm u)
            | anyL-++ f (fvTm t) (fvTm u) | anyL-++ g (fvTm t) (fvTm u)
            | aext-ty A (fst (scArr {_} {A} {t} {u} p)) | aext-tm t (fst (snd (scArr {_} {A} {t} {u} p))) | aext-tm u (snd (snd (scArr {_} {A} {t} {u} p))) = refl

    aext-tm : ∀ t → T (scTm? n t) → anyL f (fvTm t) ≡ anyL g (fvTm t)
    aext-tm (var i)       p = cong (_∨ false) (e i p)
    aext-tm (bvar _ _)    p = refl
    aext-tm (coh Q B γ)   p = aext-sub γ p
    aext-tm (cst _)       p = refl
    aext-tm (bnd _ _ Δ γ) p
      rewrite anyL-++ f (fvTel Δ) (fvSub γ) | anyL-++ g (fvTel Δ) (fvSub γ)
            | aext-tel Δ (fst (T∧ {scTel? n Δ} p)) | aext-sub γ (snd (T∧ {scTel? n Δ} p)) = refl

    aext-tel : ∀ Δ → T (scTel? n Δ) → anyL f (fvTel Δ) ≡ anyL g (fvTel Δ)
    aext-tel ε             _ = refl
    aext-tel (Δ ▸[ _ ] A) p
      rewrite anyL-++ f (fvTel Δ) (fvTy A) | anyL-++ g (fvTel Δ) (fvTy A)
            | aext-tel Δ (fst (T∧ {scTel? n Δ} p)) | aext-ty A (snd (T∧ {scTel? n Δ} p)) = refl

    aext-sub : ∀ γ → T (scSub? n γ) → anyL f (fvSub γ) ≡ anyL g (fvSub γ)
    aext-sub ⟨⟩       _ = refl
    aext-sub (γ ,ₛ t) p
      rewrite anyL-++ f (fvSub γ) (fvTm t) | anyL-++ g (fvSub γ) (fvTm t)
            | aext-sub γ (fst (T∧ {scSub? n γ} p)) | aext-tm t (snd (T∧ {scSub? n γ} p)) = refl

------------------------------------------------------------------------
-- Congruences.

liftOne-cong : ∀ {ρ ρ' a a' b b' c c'} v → ρ ≡ ρ' → a ≡ a' → b ≡ b' → c ≡ c' →
               liftOne ρ a b c v ≡ liftOne ρ' a' b' c' v
liftOne-cong v refl refl refl refl = refl

liftOne-sub : ∀ ρ a b c v S → (liftOne ρ a b c v) ∘ S ≡ liftOne (ρ ∘ S) (a [ S ]tm) (b [ S ]tm) (c [ S ]tm) v
liftOne-sub ρ a b c true  S = refl
liftOne-sub ρ a b c false S = refl

rwI-cong : ∀ k n {c c' C C' z z' h h'} v → c ≡ c' → C ≡ C' → z ≡ z' → h ≡ h' →
           rwI k n c C z h v ≡ rwI k n c' C' z' h' v
rwI-cong k n v refl refl refl refl = refl

lwI-cong : ∀ k n {h h' x x' c c' C C'} v → h ≡ h' → x ≡ x' → c ≡ c' → C ≡ C' →
           lwI k n h x c C v ≡ lwI k n h' x' c' C' v
lwI-cong k n v refl refl refl refl = refl

liftOne-cong' : ∀ {ρ ρ' a a' b b' c c' v v'} → v ≡ v' → ρ ≡ ρ' → a ≡ a' → b ≡ b' → (T v → c ≡ c') →
                liftOne ρ a b c v ≡ liftOne ρ' a' b' c' v'
liftOne-cong' {v = true}  refl refl refl refl h = cong (λ X → _ ,ₛ _ ,ₛ _ ,ₛ X) (h tt)
liftOne-cong' {v = false} refl refl refl refl h = refl

rwI-cong' : ∀ k m {c c' C C' z z' h h' v v'} → v ≡ v' → c ≡ c' → C ≡ C' → z ≡ z' → (T v → h ≡ h') →
            rwI k m c C z h v ≡ rwI k m c' C' z' h' v'
rwI-cong' k m {v = true}  refl refl refl refl e = cong (rwT k (m ∸ suc k) _ _ _) (e tt)
rwI-cong' k m {v = false} refl refl refl refl e = refl

lwI-cong' : ∀ k m {h h' x x' c c' C C' v v'} → v ≡ v' → (T v → h ≡ h') → x ≡ x' → c ≡ c' → C ≡ C' →
            lwI k m h x c C v ≡ lwI k m h' x' c' C' v'
lwI-cong' k m {v = true}  refl e refl refl refl = cong (λ X → lwT k (m ∸ suc k) X _ _ _) (e tt)
lwI-cong' k m {v = false} refl e refl refl refl = refl

------------------------------------------------------------------------
-- Precomposition: cyl D (t [ σ ]) ≡ cyl (pre σ D) t.

pre : Sub → Datum → Datum
pre σ D = datum (σ ∘ mm D) (σ ∘ mp D) (λ q → touched D (lookupₛ σ q)) (λ q → cyl D (lookupₛ σ q))

touched-pre : ∀ D σ t → touched D (t [ σ ]tm) ≡ touched (pre σ D) t
touched-pre D σ t = anyL-tm (sel D) σ t

mask-pre : ∀ D σ δ → mask D (δ ∘ σ) ≡ mask (pre σ D) δ
mask-pre D σ ⟨⟩       = refl
mask-pre D σ (δ ,ₛ t) = cong₂ _◂_ (mask-pre D σ δ) (touched-pre D σ t)

mutual
  cyl-pre : ∀ D σ t → T (scTm? (lenₛ σ) t) → cyl D (t [ σ ]tm) ≡ cyl (pre σ D) t
  cyl-pre D σ (var i)       p = refl
  cyl-pre D σ (bvar _ _)    p = refl
  cyl-pre D σ (coh Q B δ)   p =
    cong₂ (λ Y ρ → fillK Q B Y [ ρ ]tm) (mask-pre D σ δ) (liftS-pre D σ δ p)
  cyl-pre D σ (cst _)       p = refl
  cyl-pre D σ (bnd _ _ _ _) p = refl

  liftS-pre : ∀ D σ δ → T (scSub? (lenₛ σ) δ) → liftS D (δ ∘ σ) ≡ liftS (pre σ D) δ
  liftS-pre D σ ⟨⟩       p = refl
  liftS-pre D σ (δ ,ₛ t) pq =
    let (p , q) = T∧ {scSub? (lenₛ σ) δ} pq in
    trans (liftOne-cong (touched D (t [ σ ]tm)) (liftS-pre D σ δ p)
             (assoc-tm t σ (mm D) q) (assoc-tm t σ (mp D) q) (cyl-pre D σ t q))
          (cong (liftOne (liftS (pre σ D) δ) (t [ σ ∘ mm D ]tm) (t [ σ ∘ mp D ]tm) (cyl (pre σ D) t))
                (touched-pre D σ t))

module _ (D : Datum) (σ : Sub) where
  private
    D' = pre σ D
    n  = lenₛ σ
    open Whisk σ using (baseAt-[]; tgtAt-[]; srcAt-[])

  mutual
    P-pre : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTm? n t) → T (scTy? n A) →
            P D k (t [ σ ]tm) (A [ σ ]ty) ≡ P D' k t A
    P-pre zero    t A p st sA = assoc-tm t σ (mm D) st
    P-pre (suc k) t A p st sA = step (dim-[]′ A σ) (sym (tgtAt-[] k A)) (sym (baseAt-[] k A))
      where
      w = tgtAt k A
      W = baseAt k A
      step : ∀ {m w' W'} → m ≡ dim A → w' ≡ w [ σ ]tm → W' ≡ W [ σ ]ty →
             rwI k m (P D k (t [ σ ]tm) (A [ σ ]ty)) (TP D k (A [ σ ]ty)) (L D k w' W') (cyl D w') (touched D w')
               ≡ P D' (suc k) t A
      step refl refl refl =
        trans (rwI-cong k (dim A) (touched D (w [ σ ]tm))
                 (P-pre k t A (<-suc k (dim A) p) st sA)
                 (TP-pre k A (<-suc k (dim A) p) sA)
                 (L-pre k w W (k≤W k A p) (sc-tgtAt k A p sA) (sc-baseAt k A sA))
                 (cyl-pre D σ w (sc-tgtAt k A p sA)))
              (cong (rwI k (dim A) (P D' k t A) (TP D' k A) (L D' k w W) (cyl D' w)) (touched-pre D σ w))

    TP-pre : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TP D k (A [ σ ]ty) ≡ TP D' k A
    TP-pre zero    A           p sA = assoc-ty A σ (mm D) sA
    TP-pre (suc k) ⋆           () sA
    TP-pre (suc k) (arr A s u) p sc =
      let (sA , ss , su) = scArr {n} {A} {s} {u} sc in
      trans (cong (λ m → if k ==ℕ m then X else Y) (dim-[]′ A σ))
            (ifCase (k ==ℕ dim A)
               (λ e → arr≡ (TP-pre k A p sA) (P-pre k s A p ss sA) (L-pre k u A p su sA))
               (λ e → arr≡ (TP-pre (suc k) A (lt-ne k (dim A) p e) sA) (P-pre (suc k) s A (lt-ne k (dim A) p e) ss sA)
                           (P-pre (suc k) u A (lt-ne k (dim A) p e) su sA)))
      where
      X = arr (TP D k (A [ σ ]ty)) (P D k (s [ σ ]tm) (A [ σ ]ty)) (L D k (u [ σ ]tm) (A [ σ ]ty))
      Y = arr (TP D (suc k) (A [ σ ]ty)) (P D (suc k) (s [ σ ]tm) (A [ σ ]ty)) (P D (suc k) (u [ σ ]tm) (A [ σ ]ty))

    L-pre : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTm? n t) → T (scTy? n A) →
            L D k (t [ σ ]tm) (A [ σ ]ty) ≡ L D' k t A
    L-pre zero    t A p st sA = assoc-tm t σ (mp D) st
    L-pre (suc k) t A p st sA = step (dim-[]′ A σ) (sym (srcAt-[] k A)) (sym (baseAt-[] k A))
      where
      w = srcAt k A
      W = baseAt k A
      step : ∀ {m w' W'} → m ≡ dim A → w' ≡ w [ σ ]tm → W' ≡ W [ σ ]ty →
             lwI k m (cyl D w') (P D k w' W') (L D k (t [ σ ]tm) (A [ σ ]ty)) (TL D k (A [ σ ]ty)) (touched D w')
               ≡ L D' (suc k) t A
      step refl refl refl =
        trans (lwI-cong k (dim A) (touched D (w [ σ ]tm))
                 (cyl-pre D σ w (sc-srcAt k A p sA))
                 (P-pre k w W (k≤W k A p) (sc-srcAt k A p sA) (sc-baseAt k A sA))
                 (L-pre k t A (<-suc k (dim A) p) st sA)
                 (TL-pre k A (<-suc k (dim A) p) sA))
              (cong (lwI k (dim A) (cyl D' w) (P D' k w W) (L D' k t A) (TL D' k A)) (touched-pre D σ w))

    TL-pre : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TL D k (A [ σ ]ty) ≡ TL D' k A
    TL-pre zero    A           p sA = assoc-ty A σ (mp D) sA
    TL-pre (suc k) ⋆           () sA
    TL-pre (suc k) (arr A s u) p sc =
      let (sA , ss , su) = scArr {n} {A} {s} {u} sc in
      trans (cong (λ m → if k ==ℕ m then X else Y) (dim-[]′ A σ))
            (ifCase (k ==ℕ dim A)
               (λ e → arr≡ (TP-pre k A p sA) (P-pre k s A p ss sA) (L-pre k u A p su sA))
               (λ e → arr≡ (TL-pre (suc k) A (lt-ne k (dim A) p e) sA) (L-pre (suc k) s A (lt-ne k (dim A) p e) ss sA)
                           (L-pre (suc k) u A (lt-ne k (dim A) p e) su sA)))
      where
      X = arr (TP D k (A [ σ ]ty)) (P D k (s [ σ ]tm) (A [ σ ]ty)) (L D k (u [ σ ]tm) (A [ σ ]ty))
      Y = arr (TL D (suc k) (A [ σ ]ty)) (L D (suc k) (s [ σ ]tm) (A [ σ ]ty)) (L D (suc k) (u [ σ ]tm) (A [ σ ]ty))

  cylTy-pre : ∀ t A → T (scTm? n t) → T (scTy? n A) → cylTy D (t [ σ ]tm) (A [ σ ]ty) ≡ cylTy D' t A
  cylTy-pre t A st sA rewrite dim-[]′ A σ =
    arr≡ (TP-pre (dim A) A (n<sn (dim A)) sA) (P-pre (dim A) t A (n<sn (dim A)) st sA)
         (L-pre (dim A) t A (n<sn (dim A)) st sA)

------------------------------------------------------------------------
-- Postcomposition: cyl D t [ S ] ≡ cyl (D [ S ]D) t.

_[_]D : Datum → Sub → Datum
D [ S ]D = datum (mm D ∘ S) (mp D ∘ S) (sel D) (λ x → th D x [ S ]tm)

mask-post : ∀ D S δ → mask (D [ S ]D) δ ≡ mask D δ
mask-post D S ⟨⟩       = refl
mask-post D S (δ ,ₛ t) = cong (_◂ touched D t) (mask-post D S δ)

lenₛ-liftS : ∀ D γ → lenₛ (liftS D γ) ≡ cnt (mask D γ)
lenₛ-liftS D ⟨⟩       = refl
lenₛ-liftS D (γ ,ₛ t) with touched D t
... | true  = cong (λ m → suc (suc (suc m))) (lenₛ-liftS D γ)
... | false = cong suc (lenₛ-liftS D γ)

module Post (Ksc : KScoped) (D : Datum) (S : Sub) (lm : lenₛ (mp D) ≡ lenₛ (mm D)) where
  private
    n = lenₛ (mm D)
    tm' : ∀ t → T (scTm? n t) → T (scTm? (lenₛ (mp D)) t)
    tm' t s = subst (λ m → T (scTm? m t)) (sym lm) s
    ty' : ∀ A → T (scTy? n A) → T (scTy? (lenₛ (mp D)) A)
    ty' A s = subst (λ m → T (scTy? m A)) (sym lm) s
    open Whisk S using (rwI-[]; lwI-[])

  mutual
    cyl-sub : ∀ t → T (scTm? n t) → cyl D t [ S ]tm ≡ cyl (D [ S ]D) t
    cyl-sub (var x)       p = refl
    cyl-sub (bvar _ _)    p = refl
    cyl-sub (coh Q B γ)   p =
      trans (assoc-tm (fillK Q B (mask D γ)) (liftS D γ) S
               (subst (λ m → T (scTm? m (fillK Q B (mask D γ)))) (sym (lenₛ-liftS D γ)) (fillK-sc Ksc Q B (mask D γ))))
            (cong₂ (λ Y ρ → fillK Q B Y [ ρ ]tm) (sym (mask-post D S γ)) (liftS-sub γ p))
    cyl-sub (cst _)       p = refl
    cyl-sub (bnd _ _ _ _) p = refl

    liftS-sub : ∀ γ → T (scSub? n γ) → liftS D γ ∘ S ≡ liftS (D [ S ]D) γ
    liftS-sub ⟨⟩       _  = refl
    liftS-sub (γ ,ₛ t) pp =
      let (p , p') = T∧ {scSub? n γ} pp in
      trans (liftOne-sub (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) (touched D t) S)
            (liftOne-cong (touched D t) (liftS-sub γ p)
               (assoc-tm t (mm D) S p') (assoc-tm t (mp D) S (tm' t p')) (cyl-sub t p'))

  if-ty : ∀ b {X Y} → (if b then X else Y) [ S ]ty ≡ (if b then (X [ S ]ty) else (Y [ S ]ty))
  if-ty true  = refl
  if-ty false = refl

  mutual
    P-sub : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTm? n t) → T (scTy? n A) → P D k t A [ S ]tm ≡ P (D [ S ]D) k t A
    P-sub zero    t A p st sA = assoc-tm t (mm D) S st
    P-sub (suc k) t A p st sA =
      trans (rwI-[] k (dim A) (P D k t A) (TP D k A) (L D k w W) (cyl D w) (cyl D w [ S ]tm) (touched D w) (λ _ → refl))
            (rwI-cong k (dim A) (touched D w)
               (P-sub k t A (<-suc k (dim A) p) st sA)
               (TP-sub k A (<-suc k (dim A) p) sA)
               (L-sub k w W (k≤W k A p) (sc-tgtAt k A p sA) (sc-baseAt k A sA))
               (cyl-sub w (sc-tgtAt k A p sA)))
      where w = tgtAt k A
            W = baseAt k A

    TP-sub : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TP D k A [ S ]ty ≡ TP (D [ S ]D) k A
    TP-sub zero    A           p sA = assoc-ty A (mm D) S sA
    TP-sub (suc k) ⋆           () sA
    TP-sub (suc k) (arr A s u) p sc =
      let (sA , ss , su) = scArr {n} {A} {s} {u} sc in
      trans (if-ty (k ==ℕ dim A)) (ifCase (k ==ℕ dim A)
        (λ e → arr≡ (TP-sub k A p sA) (P-sub k s A p ss sA) (L-sub k u A p su sA))
        (λ e → arr≡ (TP-sub (suc k) A (lt-ne k (dim A) p e) sA) (P-sub (suc k) s A (lt-ne k (dim A) p e) ss sA)
                    (P-sub (suc k) u A (lt-ne k (dim A) p e) su sA)))

    L-sub : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTm? n t) → T (scTy? n A) → L D k t A [ S ]tm ≡ L (D [ S ]D) k t A
    L-sub zero    t A p st sA = assoc-tm t (mp D) S (tm' t st)
    L-sub (suc k) t A p st sA =
      trans (lwI-[] k (dim A) (cyl D w) (cyl D w [ S ]tm) (P D k w W) (L D k t A) (TL D k A) (touched D w) (λ _ → refl))
            (lwI-cong k (dim A) (touched D w)
               (cyl-sub w (sc-srcAt k A p sA))
               (P-sub k w W (k≤W k A p) (sc-srcAt k A p sA) (sc-baseAt k A sA))
               (L-sub k t A (<-suc k (dim A) p) st sA)
               (TL-sub k A (<-suc k (dim A) p) sA))
      where w = srcAt k A
            W = baseAt k A

    TL-sub : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TL D k A [ S ]ty ≡ TL (D [ S ]D) k A
    TL-sub zero    A           p sA = assoc-ty A (mp D) S (ty' A sA)
    TL-sub (suc k) ⋆           () sA
    TL-sub (suc k) (arr A s u) p sc =
      let (sA , ss , su) = scArr {n} {A} {s} {u} sc in
      trans (if-ty (k ==ℕ dim A)) (ifCase (k ==ℕ dim A)
        (λ e → arr≡ (TP-sub k A p sA) (P-sub k s A p ss sA) (L-sub k u A p su sA))
        (λ e → arr≡ (TL-sub (suc k) A (lt-ne k (dim A) p e) sA) (L-sub (suc k) s A (lt-ne k (dim A) p e) ss sA)
                    (L-sub (suc k) u A (lt-ne k (dim A) p e) su sA)))

  cylTy-sub : ∀ t A → T (scTm? n t) → T (scTy? n A) → cylTy D t A [ S ]ty ≡ cylTy (D [ S ]D) t A
  cylTy-sub t A st sA =
    arr≡ (TP-sub (dim A) A (n<sn (dim A)) sA) (P-sub (dim A) t A (n<sn (dim A)) st sA)
         (L-sub (dim A) t A (n<sn (dim A)) st sA)

------------------------------------------------------------------------
-- Extensionality: data that agree on the variables < n give the same
-- boundary cells for every type scoped in n, and the same cylinders for
-- touched terms scoped in n.

module Ext (D D' : Datum) (n : Nat) (emm : mm D ≡ mm D') (emp : mp D ≡ mp D')
           (esel : ∀ i → T (i <ℕ n) → sel D i ≡ sel D' i)
           (eth : ∀ i → T (i <ℕ n) → T (sel D i) → th D i ≡ th D' i) where

  touched-ext : ∀ t → T (scTm? n t) → touched D t ≡ touched D' t
  touched-ext = aext-tm (sel D) (sel D') esel

  mask-ext : ∀ γ → T (scSub? n γ) → mask D γ ≡ mask D' γ
  mask-ext ⟨⟩       _  = refl
  mask-ext (γ ,ₛ t) pq = let (p , q) = T∧ {scSub? n γ} pq in cong₂ _◂_ (mask-ext γ p) (touched-ext t q)

  sel-of : ∀ i → T (sel D i ∨ false) → T (sel D i)
  sel-of i q with sel D i
  ... | true = tt

  mutual
    cyl-ext : ∀ t → T (scTm? n t) → T (touched D t) → cyl D t ≡ cyl D' t
    cyl-ext (var i)       p q = eth i p (sel-of i q)
    cyl-ext (bvar _ _)    p q = refl
    cyl-ext (coh Q B γ)   p q = cong₂ (λ Y ρ → fillK Q B Y [ ρ ]tm) (mask-ext γ p) (liftS-ext γ p)
    cyl-ext (cst _)       p q = refl
    cyl-ext (bnd _ _ _ _) p q = refl

    liftS-ext : ∀ γ → T (scSub? n γ) → liftS D γ ≡ liftS D' γ
    liftS-ext ⟨⟩       _  = refl
    liftS-ext (γ ,ₛ t) pq =
      let (p , q) = T∧ {scSub? n γ} pq in
      liftOne-cong' (touched-ext t q) (liftS-ext γ p) (cong (t [_]tm) emm) (cong (t [_]tm) emp)
        (cyl-ext t q)

  mutual
    P-ext : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTy? n A) → P D k t A ≡ P D' k t A
    P-ext zero    t A p sA = cong (t [_]tm) emm
    P-ext (suc k) t A p sA =
      rwI-cong' k (dim A) (touched-ext w sw) (P-ext k t A (<-suc k (dim A) p) sA)
        (TP-ext k A (<-suc k (dim A) p) sA) (L-ext k w W (k≤W k A p) (sc-baseAt k A sA))
        (cyl-ext w sw)
      where w = tgtAt k A
            W = baseAt k A
            sw = sc-tgtAt k A p sA

    TP-ext : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TP D k A ≡ TP D' k A
    TP-ext zero    A           p sA = cong (A [_]ty) emm
    TP-ext (suc k) ⋆           () sA
    TP-ext (suc k) (arr A s u) p sc =
      let (sA , _ , _) = scArr {n} {A} {s} {u} sc in
      ifCase (k ==ℕ dim A)
        (λ e → arr≡ (TP-ext k A p sA) (P-ext k s A p sA) (L-ext k u A p sA))
        (λ e → arr≡ (TP-ext (suc k) A (lt-ne k (dim A) p e) sA) (P-ext (suc k) s A (lt-ne k (dim A) p e) sA)
                    (P-ext (suc k) u A (lt-ne k (dim A) p e) sA))

    L-ext : ∀ k t A → T (k <ℕ suc (dim A)) → T (scTy? n A) → L D k t A ≡ L D' k t A
    L-ext zero    t A p sA = cong (t [_]tm) emp
    L-ext (suc k) t A p sA =
      lwI-cong' k (dim A) (touched-ext w sw) (cyl-ext w sw) (P-ext k w W (k≤W k A p) (sc-baseAt k A sA))
        (L-ext k t A (<-suc k (dim A) p) sA) (TL-ext k A (<-suc k (dim A) p) sA)
      where w = srcAt k A
            W = baseAt k A
            sw = sc-srcAt k A p sA

    TL-ext : ∀ k A → T (k <ℕ suc (dim A)) → T (scTy? n A) → TL D k A ≡ TL D' k A
    TL-ext zero    A           p sA = cong (A [_]ty) emp
    TL-ext (suc k) ⋆           () sA
    TL-ext (suc k) (arr A s u) p sc =
      let (sA , _ , _) = scArr {n} {A} {s} {u} sc in
      ifCase (k ==ℕ dim A)
        (λ e → arr≡ (TP-ext k A p sA) (P-ext k s A p sA) (L-ext k u A p sA))
        (λ e → arr≡ (TL-ext (suc k) A (lt-ne k (dim A) p e) sA) (L-ext (suc k) s A (lt-ne k (dim A) p e) sA)
                    (L-ext (suc k) u A (lt-ne k (dim A) p e) sA))

  cylTy-ext : ∀ t A → T (scTy? n A) → cylTy D t A ≡ cylTy D' t A
  cylTy-ext t A sA =
    arr≡ (TP-ext (dim A) A (n<sn (dim A)) sA) (P-ext (dim A) t A (n<sn (dim A)) sA)
         (L-ext (dim A) t A (n<sn (dim A)) sA)
