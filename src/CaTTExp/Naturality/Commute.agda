------------------------------------------------------------------------
-- Substitution commutation for naturality cylinders
-- (CaTTExp.Naturality.Raw). Two operations on data:
--
--   D [ S ]D  = (mm ∘ S, mp ∘ S, sel, th[S])          postcompose
--   pre σ D   = (σ ∘ mm, σ ∘ mp, q ↦ touched (σ q),
--                q ↦ cyl D (σ q))                     precompose
--
-- and the two laws, for cylinders and for both boundary cells:
--
--   cyl-sub : cyl D t [ S ]  ≡ cyl (D [ S ]D) t
--   cyl-pre : cyl D (t [ σ ]) ≡ cyl (pre σ D) t
--
-- (and P-sub, L-sub, TP-sub, TL-sub, P-pre, …). The first needs t
-- scoped in the domain of mm and mp, and every filler scoped in its
-- cylinder context (`Scoped`); the second needs t scoped in σ. Both
-- are purely syntactic: no typing is assumed.
------------------------------------------------------------------------
module CaTTExp.Naturality.Commute where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (sc-aL; sc-mono; <-suc; n<sn; ≡-T)
open import CaTTExp.Derived using (sphSub; dskSub; lenₛ-sph; nB; lt-dbl; dbl-mono; LK; lK; BK; wK)
open import CaTTExp.DerivedBoundary using (rwT; lwT; σLp; hL; tyK; srcK; tgtK; dim[])
open import CaTTExp.Naturality.Raw

------------------------------------------------------------------------
-- Arithmetic.

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

-- n = nB k (n ∸ suc k) when k < n.
nB-sub : ∀ k n → T (k <ℕ n) → n ≡ nB k (n ∸ suc k)
nB-sub zero    (suc n) _ = cong suc (sym (+0 n))
  where +0 : ∀ n → n + 0 ≡ n
        +0 zero    = refl
        +0 (suc n) = cong suc (+0 n)
nB-sub (suc k) (suc n) p = trans (cong suc (nB-sub k n p)) (cong suc (sym (+s (n ∸ suc k) k)))
  where +s : ∀ m n → m + suc n ≡ suc (m + n)
        +s zero    n = refl
        +s (suc m) n = cong suc (+s m n)

lt-le : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
lt-le = <-suc

if-t : ∀ {a} {X : Set a} {b} {x y : X} → b ≡ true → (if b then x else y) ≡ x
if-t refl = refl

if-f : ∀ {a} {X : Set a} {b} {x y : X} → b ≡ false → (if b then x else y) ≡ y
if-f refl = refl

ifCase : ∀ {a} {X : Set a} {x y x' y' : X} (b : Bool) → (b ≡ true → x ≡ x') → (b ≡ false → y ≡ y') →
         (if b then x else y) ≡ (if b then x' else y')
ifCase true  f g = f refl
ifCase false f g = g refl

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
f $ x = f x

le-zero : ∀ k → T (k <ℕ suc 0) → k ≡ 0
le-zero zero _ = refl
le-zero (suc k) ()

------------------------------------------------------------------------
-- Whiskers commute with substitution.

sph-sub : ∀ C S → sphSub C ∘ S ≡ sphSub (C [ S ]ty)
sph-sub ⋆           S = refl
sph-sub (arr C s t) S = cong (λ X → X ,ₛ s [ S ]tm ,ₛ t [ S ]tm) (sph-sub C S)

rwT-sub : ∀ k j c C z h S →
          rwT k j c C z h [ S ]tm ≡ rwT k j (c [ S ]tm) (C [ S ]ty) (z [ S ]tm) (h [ S ]tm)
rwT-sub k j c C z h S =
  cong (λ X → coh (BK k j) (wK k j) (X ,ₛ c [ S ]tm ,ₛ z [ S ]tm ,ₛ h [ S ]tm)) (sph-sub C S)

module _ (k : Nat) (C : Ty) (S : Sub) (p : T (k <ℕ dim C)) where
  private
    lS : lenₛ (sphSub C) ≡ dbl (dim C)
    lS = lenₛ-sph C
    sc : ScTy (lenₛ (sphSub C)) (aL k)
    sc = subst (λ m → ScTy m (aL k)) (sym lS)
           (sc-mono (dbl k) (dbl (dim C)) (aL k) (dbl-mono k (dim C) (<-suc k (dim C) p)) (sc-aL k))
    q₀ : T (dbl k <ℕ lenₛ (sphSub C))
    q₀ = subst (λ m → T (dbl k <ℕ m)) (sym lS)
           (lt-dbl (dbl k) (suc k) (dim C) (<-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))) p)
    q₁ : T (suc (dbl k) <ℕ lenₛ (sphSub C))
    q₁ = subst (λ m → T (suc (dbl k) <ℕ m)) (sym lS)
           (lt-dbl (suc (dbl k)) (suc k) (dim C) (n<sn (suc (dbl k))) p)

  tyK-sub : tyK k C [ S ]ty ≡ tyK k (C [ S ]ty)
  tyK-sub = trans (Sb.assoc-ty (aL k) (sphSub C) S sc) (cong (aL k [_]ty) (sph-sub C S))

  srcK-sub : srcK k C [ S ]tm ≡ srcK k (C [ S ]ty)
  srcK-sub = trans (sym (Sb.lookupₛ-∘ (sphSub C) S (dbl k) q₀)) (cong (λ X → lookupₛ X (dbl k)) (sph-sub C S))

  tgtK-sub : tgtK k C [ S ]tm ≡ tgtK k (C [ S ]ty)
  tgtK-sub = trans (sym (Sb.lookupₛ-∘ (sphSub C) S (suc (dbl k)) q₁)) (cong (λ X → lookupₛ X (suc (dbl k))) (sph-sub C S))

  hL-sub : ∀ x → hL k x C [ S ]ty ≡ hL k (x [ S ]tm) (C [ S ]ty)
  hL-sub x = cong₂ (λ X Y → arr X (x [ S ]tm) Y) tyK-sub srcK-sub

σLp-sub : ∀ k j h x C S → dim C ≡ nB k j →
          σLp k j h x C ∘ S ≡ σLp k j (h [ S ]tm) (x [ S ]tm) (C [ S ]ty)
σLp-sub k zero h x C S e =
  cong₂ (λ X Y → (X ,ₛ h [ S ]tm) ,ₛ Y)
    (trans (sph-sub (hL k x C) S) (cong sphSub (hL-sub k C S p x)))
    (tgtK-sub k C S p)
  where p : T (k <ℕ dim C)
        p = subst (λ m → T (k <ℕ m)) (sym e) (n<sn k)
σLp-sub k (suc j) h x ⋆ S ()
σLp-sub k (suc j) h x (arr C s t) S e =
  cong (λ X → X ,ₛ s [ S ]tm ,ₛ t [ S ]tm) (σLp-sub k j h x C S (cong (λ m → m ∸ 1) e))

lwT-sub : ∀ k j h x c C S → dim C ≡ nB k j →
          lwT k j h x c C [ S ]tm ≡ lwT k j (h [ S ]tm) (x [ S ]tm) (c [ S ]tm) (C [ S ]ty)
lwT-sub k j h x c C S e =
  cong (λ X → coh (LK k j) (lK k j) (X ,ₛ c [ S ]tm)) (σLp-sub k j h x C S e)

------------------------------------------------------------------------
-- Iterated boundaries.

dim-baseAt : ∀ k A → T (k <ℕ suc (dim A)) → dim (baseAt k A) ≡ k
dim-baseAt k ⋆           p = sym (le-zero k p)
dim-baseAt k (arr A s u) p with k ==ℕ suc (dim A) in e
... | true  = sym (eq-sound e)
... | false = dim-baseAt k A (lt-ne k (suc (dim A)) p e)

sc-baseAt : ∀ {n} k A → ScTy n A → ScTy n (baseAt k A)
sc-baseAt k ⋆           s = tt
sc-baseAt k (arr A s u) a with k ==ℕ suc (dim A)
... | true  = a
... | false = sc-baseAt k A (fst a)

sc-tgtAt : ∀ {n} k A → T (k <ℕ dim A) → ScTy n A → ScTm n (tgtAt k A)
sc-tgtAt k (arr A s u) p a with k ==ℕ dim A in e
... | true  = snd (snd a)
... | false = sc-tgtAt k A (lt-ne k (dim A) p e) (fst a)

sc-srcAt : ∀ {n} k A → T (k <ℕ dim A) → ScTy n A → ScTm n (srcAt k A)
sc-srcAt k (arr A s u) p a with k ==ℕ dim A in e
... | true  = fst (snd a)
... | false = sc-srcAt k A (lt-ne k (dim A) p e) (fst a)

baseAt-sub : ∀ k A σ → baseAt k (A [ σ ]ty) ≡ baseAt k A [ σ ]ty
baseAt-sub k ⋆           σ = refl
baseAt-sub k (arr A s u) σ rewrite dim[] A σ with k ==ℕ suc (dim A)
... | true  = refl
... | false = baseAt-sub k A σ

tgtAt-sub : ∀ k A σ → T (k <ℕ dim A) → tgtAt k (A [ σ ]ty) ≡ tgtAt k A [ σ ]tm
tgtAt-sub k (arr A s u) σ p rewrite dim[] A σ with k ==ℕ dim A in e
... | true  = refl
... | false = tgtAt-sub k A σ (lt-ne k (dim A) p e)

srcAt-sub : ∀ k A σ → T (k <ℕ dim A) → srcAt k (A [ σ ]ty) ≡ srcAt k A [ σ ]tm
srcAt-sub k (arr A s u) σ p rewrite dim[] A σ with k ==ℕ dim A in e
... | true  = refl
... | false = srcAt-sub k A σ (lt-ne k (dim A) p e)

------------------------------------------------------------------------
-- Free variables under substitution, through anyL.

∨-false : ∀ a → (a ∨ false) ≡ a
∨-false true  = refl
∨-false false = refl

anyL-++ : ∀ f xs ys → anyL f (xs ++ ys) ≡ (anyL f xs ∨ anyL f ys)
anyL-++ f []       ys = refl
anyL-++ f (x ∷ xs) ys with f x
... | true  = refl
... | false = anyL-++ f xs ys

module _ (f : Nat → Bool) (σ : Sub) where
  img : Nat → Bool
  img y = anyL f (fvTm (lookupₛ σ y))

  mutual
    anyL-tm : ∀ t → anyL f (fvTm (t [ σ ]tm)) ≡ anyL img (fvTm t)
    anyL-tm (var i)     = sym (∨-false (img i))
    anyL-tm (coh Q A τ) = anyL-sub τ
    anyL-tm (cst ())

    anyL-sub : ∀ τ → anyL f (fvSub (τ ∘ σ)) ≡ anyL img (fvSub τ)
    anyL-sub ⟨⟩       = refl
    anyL-sub (τ ,ₛ t) =
      trans (anyL-++ f (fvSub (τ ∘ σ)) (fvTm (t [ σ ]tm)))
      (trans (cong₂ _∨_ (anyL-sub τ) (anyL-tm t))
             (sym (anyL-++ img (fvSub τ) (fvTm t))))

  anyL-ty : ∀ A → anyL f (fvTy (A [ σ ]ty)) ≡ anyL img (fvTy A)
  anyL-ty ⋆           = refl
  anyL-ty (arr A t u) =
    trans (anyL-++ f (fvTy (A [ σ ]ty)) (fvTm (t [ σ ]tm) ++ fvTm (u [ σ ]tm)))
    (trans (cong₂ _∨_ (anyL-ty A)
             (trans (anyL-++ f (fvTm (t [ σ ]tm)) (fvTm (u [ σ ]tm))) (cong₂ _∨_ (anyL-tm t) (anyL-tm u))))
    (trans (cong (anyL img (fvTy A) ∨_) (sym (anyL-++ img (fvTm t) (fvTm u))))
           (sym (anyL-++ img (fvTy A) (fvTm t ++ fvTm u)))))

-- anyL depends only on the values of f on the variables in scope.
anyL-ext : ∀ {n} (f g : Nat → Bool) → (∀ i → T (i <ℕ n) → f i ≡ g i) →
           (∀ t → ScTm n t → anyL f (fvTm t) ≡ anyL g (fvTm t)) ×
           (∀ γ → ScSub n γ → anyL f (fvSub γ) ≡ anyL g (fvSub γ))
anyL-ext {n} f g e = tm , sb
  where
  mutual
    tm : ∀ t → ScTm n t → anyL f (fvTm t) ≡ anyL g (fvTm t)
    tm (var i)     p = cong (_∨ false) (e i p)
    tm (coh Q B γ) p = sb γ p
    tm (cst ())    p
    sb : ∀ γ → ScSub n γ → anyL f (fvSub γ) ≡ anyL g (fvSub γ)
    sb ⟨⟩       p       = refl
    sb (γ ,ₛ t) (p , q) =
      trans (anyL-++ f (fvSub γ) (fvTm t))
      (trans (cong₂ _∨_ (sb γ p) (tm t q)) (sym (anyL-++ g (fvSub γ) (fvTm t))))

anyL-ext-ty : ∀ {n} (f g : Nat → Bool) → (∀ i → T (i <ℕ n) → f i ≡ g i) →
              ∀ A → ScTy n A → anyL f (fvTy A) ≡ anyL g (fvTy A)
anyL-ext-ty f g e ⋆           _           = refl
anyL-ext-ty f g e (arr A t u) (a , p , q) =
  trans (anyL-++ f (fvTy A) (fvTm t ++ fvTm u))
  (trans (cong₂ _∨_ (anyL-ext-ty f g e A a)
           (trans (anyL-++ f (fvTm t) (fvTm u))
           (trans (cong₂ _∨_ (fst (anyL-ext f g e) t p) (fst (anyL-ext f g e) u q))
                  (sym (anyL-++ g (fvTm t) (fvTm u))))))
         (sym (anyL-++ g (fvTy A) (fvTm t ++ fvTm u))))

------------------------------------------------------------------------
-- The two operations on data.

_[_]D : Datum → Sub → Datum
D [ S ]D = datum (mm D ∘ S) (mp D ∘ S) (sel D) (λ x → th D x [ S ]tm)

liftOne-sub : ∀ ρ a b c v S → (liftOne ρ a b c v) ∘ S ≡ liftOne (ρ ∘ S) (a [ S ]tm) (b [ S ]tm) (c [ S ]tm) v
liftOne-sub ρ a b c true  S = refl
liftOne-sub ρ a b c false S = refl

liftOne-cong : ∀ {ρ ρ' a a' b b' c c'} v → ρ ≡ ρ' → a ≡ a' → b ≡ b' → c ≡ c' →
               liftOne ρ a b c v ≡ liftOne ρ' a' b' c' v
liftOne-cong v refl refl refl refl = refl

-- Every filler is scoped in its cylinder context.
Scoped : Filler → Set
Scoped K = ∀ Q B Y → ScTm (cnt Y) (K Q B Y)

module Laws (K : Filler) where
  open Cyl K

  pre : Sub → Datum → Datum
  pre σ D = datum (σ ∘ mm D) (σ ∘ mp D) (λ q → touched D (lookupₛ σ q)) (λ q → cyl D (lookupₛ σ q))

  len-liftS : ∀ D γ → lenₛ (liftS D γ) ≡ cnt (mask D γ)
  len-liftS D ⟨⟩ = refl
  len-liftS D (γ ,ₛ t) with touched D t
  ... | true  = cong (λ n → suc (suc (suc n))) (len-liftS D γ)
  ... | false = cong suc (len-liftS D γ)

  --------------------------------------------------------------------
  -- Precomposition: cyl D (t [ σ ]) ≡ cyl (pre σ D) t.

  touched-pre : ∀ D σ t → touched D (t [ σ ]tm) ≡ touched (pre σ D) t
  touched-pre D σ t = anyL-tm (sel D) σ t

  mask-pre : ∀ D σ δ → mask D (δ ∘ σ) ≡ mask (pre σ D) δ
  mask-pre D σ ⟨⟩       = refl
  mask-pre D σ (δ ,ₛ t) = cong₂ _◂_ (mask-pre D σ δ) (touched-pre D σ t)

  mutual
    cyl-pre : ∀ D σ t → ScTm (lenₛ σ) t → cyl D (t [ σ ]tm) ≡ cyl (pre σ D) t
    cyl-pre D σ (var i)     p = refl
    cyl-pre D σ (coh Q B δ) p =
      cong₂ (λ Y ρ → K Q B Y [ ρ ]tm) (mask-pre D σ δ) (liftS-pre D σ δ p)
    cyl-pre D σ (cst ())    p

    liftS-pre : ∀ D σ δ → ScSub (lenₛ σ) δ → liftS D (δ ∘ σ) ≡ liftS (pre σ D) δ
    liftS-pre D σ ⟨⟩       p       = refl
    liftS-pre D σ (δ ,ₛ t) (p , q) =
      trans (liftOne-cong (touched D (t [ σ ]tm)) (liftS-pre D σ δ p)
               (Sb.assoc-tm t σ (mm D) q) (Sb.assoc-tm t σ (mp D) q) (cyl-pre D σ t q))
            (cong (liftOne (liftS (pre σ D) δ) (t [ σ ∘ mm D ]tm) (t [ σ ∘ mp D ]tm) (cyl (pre σ D) t))
                  (touched-pre D σ t))

  rwI-cong : ∀ k n {c c' C C' z z' h h'} v → c ≡ c' → C ≡ C' → z ≡ z' → h ≡ h' →
             rwI k n c C z h v ≡ rwI k n c' C' z' h' v
  rwI-cong k n v refl refl refl refl = refl

  lwI-cong : ∀ k n {h h' x x' c c' C C'} v → h ≡ h' → x ≡ x' → c ≡ c' → C ≡ C' →
             lwI k n h x c C v ≡ lwI k n h' x' c' C' v
  lwI-cong k n v refl refl refl refl = refl

  arr≡ : ∀ {A A' s s' u u'} → A ≡ A' → s ≡ s' → u ≡ u' → arr A s u ≡ arr A' s' u'
  arr≡ refl refl refl = refl

  module _ (D : Datum) (σ : Sub) where
    private
      D' = pre σ D
      n  = lenₛ σ

    mutual
      P-pre : ∀ k t A → T (k <ℕ suc (dim A)) → ScTm n t → ScTy n A →
              P D k (t [ σ ]tm) (A [ σ ]ty) ≡ P D' k t A
      P-pre zero    t A p st sA = Sb.assoc-tm t σ (mm D) st
      P-pre (suc k) t A p st sA = step (dim[] A σ) (tgtAt-sub k A σ p) (baseAt-sub k A σ)
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
                   (L-pre k w W (subst (λ m → T (k <ℕ suc m)) (sym (dim-baseAt k A (<-suc k (dim A) p))) (n<sn k))
                      (sc-tgtAt k A p sA) (sc-baseAt k A sA))
                   (cyl-pre D σ w (sc-tgtAt k A p sA)))
                (cong (rwI k (dim A) (P D' k t A) (TP D' k A) (L D' k w W) (cyl D' w)) (touched-pre D σ w))

      TP-pre : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TP D k (A [ σ ]ty) ≡ TP D' k A
      TP-pre zero    A           p sA = Sb.assoc-ty A σ (mm D) sA
      TP-pre (suc k) ⋆           () sA
      TP-pre (suc k) (arr A s u) p (sA , ss , su) =
        trans (cong (λ m → if k ==ℕ m then X else Y) (dim[] A σ))
              (ifCase (k ==ℕ dim A)
                 (λ e → arr≡ (TP-pre k A p sA) (P-pre k s A p ss sA) (L-pre k u A p su sA))
                 (λ e → arr≡ (TP-pre (suc k) A (lt-ne k (dim A) p e) sA) (P-pre (suc k) s A (lt-ne k (dim A) p e) ss sA)
                             (P-pre (suc k) u A (lt-ne k (dim A) p e) su sA)))
        where
        X = arr (TP D k (A [ σ ]ty)) (P D k (s [ σ ]tm) (A [ σ ]ty)) (L D k (u [ σ ]tm) (A [ σ ]ty))
        Y = arr (TP D (suc k) (A [ σ ]ty)) (P D (suc k) (s [ σ ]tm) (A [ σ ]ty)) (P D (suc k) (u [ σ ]tm) (A [ σ ]ty))

      L-pre : ∀ k t A → T (k <ℕ suc (dim A)) → ScTm n t → ScTy n A →
              L D k (t [ σ ]tm) (A [ σ ]ty) ≡ L D' k t A
      L-pre zero    t A p st sA = Sb.assoc-tm t σ (mp D) st
      L-pre (suc k) t A p st sA = step (dim[] A σ) (srcAt-sub k A σ p) (baseAt-sub k A σ)
        where
        w = srcAt k A
        W = baseAt k A
        step : ∀ {m w' W'} → m ≡ dim A → w' ≡ w [ σ ]tm → W' ≡ W [ σ ]ty →
               lwI k m (cyl D w') (P D k w' W') (L D k (t [ σ ]tm) (A [ σ ]ty)) (TL D k (A [ σ ]ty)) (touched D w')
                 ≡ L D' (suc k) t A
        step refl refl refl =
          trans (lwI-cong k (dim A) (touched D (w [ σ ]tm))
                   (cyl-pre D σ w (sc-srcAt k A p sA))
                   (P-pre k w W (subst (λ m → T (k <ℕ suc m)) (sym (dim-baseAt k A (<-suc k (dim A) p))) (n<sn k))
                      (sc-srcAt k A p sA) (sc-baseAt k A sA))
                   (L-pre k t A (<-suc k (dim A) p) st sA)
                   (TL-pre k A (<-suc k (dim A) p) sA))
                (cong (lwI k (dim A) (cyl D' w) (P D' k w W) (L D' k t A) (TL D' k A)) (touched-pre D σ w))

      TL-pre : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TL D k (A [ σ ]ty) ≡ TL D' k A
      TL-pre zero    A           p sA = Sb.assoc-ty A σ (mp D) sA
      TL-pre (suc k) ⋆           () sA
      TL-pre (suc k) (arr A s u) p (sA , ss , su) =
        trans (cong (λ m → if k ==ℕ m then X else Y) (dim[] A σ))
              (ifCase (k ==ℕ dim A)
                 (λ e → arr≡ (TP-pre k A p sA) (P-pre k s A p ss sA) (L-pre k u A p su sA))
                 (λ e → arr≡ (TL-pre (suc k) A (lt-ne k (dim A) p e) sA) (L-pre (suc k) s A (lt-ne k (dim A) p e) ss sA)
                             (L-pre (suc k) u A (lt-ne k (dim A) p e) su sA)))
        where
        X = arr (TP D k (A [ σ ]ty)) (P D k (s [ σ ]tm) (A [ σ ]ty)) (L D k (u [ σ ]tm) (A [ σ ]ty))
        Y = arr (TL D (suc k) (A [ σ ]ty)) (L D (suc k) (s [ σ ]tm) (A [ σ ]ty)) (L D (suc k) (u [ σ ]tm) (A [ σ ]ty))

    cylTy-pre : ∀ t A → ScTm n t → ScTy n A → cylTy D (t [ σ ]tm) (A [ σ ]ty) ≡ cylTy D' t A
    cylTy-pre t A st sA rewrite dim[] A σ =
      arr≡ (TP-pre (dim A) A (n<sn (dim A)) sA) (P-pre (dim A) t A (n<sn (dim A)) st sA)
           (L-pre (dim A) t A (n<sn (dim A)) st sA)

  --------------------------------------------------------------------
  -- Postcomposition: cyl D t [ S ] ≡ cyl (D [ S ]D) t.

  module Post (Ksc : Scoped K) where

    mask-post : ∀ D S δ → mask (D [ S ]D) δ ≡ mask D δ
    mask-post D S ⟨⟩       = refl
    mask-post D S (δ ,ₛ t) = cong (_◂ touched D t) (mask-post D S δ)

    module _ (D : Datum) (S : Sub) (lm : lenₛ (mp D) ≡ lenₛ (mm D)) where
      private
        n = lenₛ (mm D)
        tm' : ∀ t → ScTm n t → ScTm (lenₛ (mp D)) t
        tm' t s = subst (λ m → ScTm m t) (sym lm) s
        ty' : ∀ A → ScTy n A → ScTy (lenₛ (mp D)) A
        ty' A s = subst (λ m → ScTy m A) (sym lm) s

      mutual
        cyl-sub : ∀ t → ScTm n t → cyl D t [ S ]tm ≡ cyl (D [ S ]D) t
        cyl-sub (var x)     p = refl
        cyl-sub (coh Q B γ) p =
          trans (Sb.assoc-tm (K Q B (mask D γ)) (liftS D γ) S
                   (subst (λ m → ScTm m (K Q B (mask D γ))) (sym (len-liftS D γ)) (Ksc Q B (mask D γ))))
                (cong₂ (λ Y ρ → K Q B Y [ ρ ]tm) (sym (mask-post D S γ)) (liftS-sub γ p))
        cyl-sub (cst ())    p

        liftS-sub : ∀ γ → ScSub n γ → liftS D γ ∘ S ≡ liftS (D [ S ]D) γ
        liftS-sub ⟨⟩       p        = refl
        liftS-sub (γ ,ₛ t) (p , p') =
          trans (liftOne-sub (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) (touched D t) S)
                (liftOne-cong (touched D t) (liftS-sub γ p)
                   (Sb.assoc-tm t (mm D) S p') (Sb.assoc-tm t (mp D) S (tm' t p')) (cyl-sub t p'))

      dim-TP : ∀ k A → T (k <ℕ suc (dim A)) → dim (TP D k A) ≡ dim A
      dim-TP zero    A           p = dim[] A (mm D)
      dim-TP (suc k) ⋆           ()
      dim-TP (suc k) (arr A s u) p with k ==ℕ dim A in e
      ... | true  = cong suc (dim-TP k A p)
      ... | false = cong suc (dim-TP (suc k) A (lt-ne k (dim A) p e))

      dim-TL : ∀ k A → T (k <ℕ suc (dim A)) → dim (TL D k A) ≡ dim A
      dim-TL zero    A           p = dim[] A (mp D)
      dim-TL (suc k) ⋆           ()
      dim-TL (suc k) (arr A s u) p with k ==ℕ dim A in e
      ... | true  = cong suc (dim-TP k A p)
      ... | false = cong suc (dim-TL (suc k) A (lt-ne k (dim A) p e))

      private
        k≤W : ∀ k A → T (k <ℕ dim A) → T (k <ℕ suc (dim (baseAt k A)))
        k≤W k A p = subst (λ m → T (k <ℕ suc m)) (sym (dim-baseAt k A (<-suc k (dim A) p))) (n<sn k)

      if-ty : ∀ b {X Y} → (if b then X else Y) [ S ]ty ≡ (if b then (X [ S ]ty) else (Y [ S ]ty))
      if-ty true  = refl
      if-ty false = refl

      rwI-sub : ∀ k m c C z h v → rwI k m c C z h v [ S ]tm ≡ rwI k m (c [ S ]tm) (C [ S ]ty) (z [ S ]tm) (h [ S ]tm) v
      rwI-sub k m c C z h true  = rwT-sub k (m ∸ suc k) c C z h S
      rwI-sub k m c C z h false = refl

      lwI-sub : ∀ k m h x c C v → dim C ≡ nB k (m ∸ suc k) →
                lwI k m h x c C v [ S ]tm ≡ lwI k m (h [ S ]tm) (x [ S ]tm) (c [ S ]tm) (C [ S ]ty) v
      lwI-sub k m h x c C true  e = lwT-sub k (m ∸ suc k) h x c C S e
      lwI-sub k m h x c C false e = refl

      mutual
        P-sub : ∀ k t A → T (k <ℕ suc (dim A)) → ScTm n t → ScTy n A → P D k t A [ S ]tm ≡ P (D [ S ]D) k t A
        P-sub zero    t A p st sA = Sb.assoc-tm t (mm D) S st
        P-sub (suc k) t A p st sA =
          trans (rwI-sub k (dim A) (P D k t A) (TP D k A) (L D k w W) (cyl D w) (touched D w))
                (rwI-cong k (dim A) (touched D w)
                   (P-sub k t A (<-suc k (dim A) p) st sA)
                   (TP-sub k A (<-suc k (dim A) p) sA)
                   (L-sub k w W (k≤W k A p) (sc-tgtAt k A p sA) (sc-baseAt k A sA))
                   (cyl-sub w (sc-tgtAt k A p sA)))
          where w = tgtAt k A
                W = baseAt k A

        TP-sub : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TP D k A [ S ]ty ≡ TP (D [ S ]D) k A
        TP-sub zero    A           p sA = Sb.assoc-ty A (mm D) S sA
        TP-sub (suc k) ⋆           () sA
        TP-sub (suc k) (arr A s u) p (sA , ss , su) =
          trans (if-ty (k ==ℕ dim A)) $ ifCase (k ==ℕ dim A)
            (λ e → arr≡ (TP-sub k A p sA) (P-sub k s A p ss sA) (L-sub k u A p su sA))
            (λ e → arr≡ (TP-sub (suc k) A (lt-ne k (dim A) p e) sA) (P-sub (suc k) s A (lt-ne k (dim A) p e) ss sA)
                        (P-sub (suc k) u A (lt-ne k (dim A) p e) su sA))

        L-sub : ∀ k t A → T (k <ℕ suc (dim A)) → ScTm n t → ScTy n A → L D k t A [ S ]tm ≡ L (D [ S ]D) k t A
        L-sub zero    t A p st sA = Sb.assoc-tm t (mp D) S (tm' t st)
        L-sub (suc k) t A p st sA =
          trans (lwI-sub k (dim A) (cyl D w) (P D k w W) (L D k t A) (TL D k A) (touched D w)
                   (trans (dim-TL k A (<-suc k (dim A) p)) (nB-sub k (dim A) p)))
                (lwI-cong k (dim A) (touched D w)
                   (cyl-sub w (sc-srcAt k A p sA))
                   (P-sub k w W (k≤W k A p) (sc-srcAt k A p sA) (sc-baseAt k A sA))
                   (L-sub k t A (<-suc k (dim A) p) st sA)
                   (TL-sub k A (<-suc k (dim A) p) sA))
          where w = srcAt k A
                W = baseAt k A

        TL-sub : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TL D k A [ S ]ty ≡ TL (D [ S ]D) k A
        TL-sub zero    A           p sA = Sb.assoc-ty A (mp D) S (ty' A sA)
        TL-sub (suc k) ⋆           () sA
        TL-sub (suc k) (arr A s u) p (sA , ss , su) =
          trans (if-ty (k ==ℕ dim A)) $ ifCase (k ==ℕ dim A)
            (λ e → arr≡ (TP-sub k A p sA) (P-sub k s A p ss sA) (L-sub k u A p su sA))
            (λ e → arr≡ (TL-sub (suc k) A (lt-ne k (dim A) p e) sA) (L-sub (suc k) s A (lt-ne k (dim A) p e) ss sA)
                        (L-sub (suc k) u A (lt-ne k (dim A) p e) su sA))

      cylTy-sub : ∀ t A → ScTm n t → ScTy n A → cylTy D t A [ S ]ty ≡ cylTy (D [ S ]D) t A
      cylTy-sub t A st sA =
        arr≡ (TP-sub (dim A) A (n<sn (dim A)) sA) (P-sub (dim A) t A (n<sn (dim A)) st sA)
             (L-sub (dim A) t A (n<sn (dim A)) st sA)

  ----------------------------------------------------------------------
  -- Extensionality: data that agree on the variables < n give the same
  -- boundary cells for every type scoped in n, and the same cylinders
  -- for touched terms scoped in n. The term t of P k t A is only ever
  -- substituted, so it need not be scoped.

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

  module Ext (D D' : Datum) (n : Nat) (emm : mm D ≡ mm D') (emp : mp D ≡ mp D')
             (esel : ∀ i → T (i <ℕ n) → sel D i ≡ sel D' i)
             (eth : ∀ i → T (i <ℕ n) → T (sel D i) → th D i ≡ th D' i) where

    touched-ext : ∀ t → ScTm n t → touched D t ≡ touched D' t
    touched-ext = fst (anyL-ext (sel D) (sel D') esel)

    mask-ext : ∀ γ → ScSub n γ → mask D γ ≡ mask D' γ
    mask-ext ⟨⟩       p       = refl
    mask-ext (γ ,ₛ t) (p , q) = cong₂ _◂_ (mask-ext γ p) (touched-ext t q)

    sel-of : ∀ i → T (i <ℕ n) → T (sel D i ∨ false) → T (sel D i)
    sel-of i p q with sel D i
    ... | true = tt

    mutual
      cyl-ext : ∀ t → ScTm n t → T (touched D t) → cyl D t ≡ cyl D' t
      cyl-ext (var i)     p q = eth i p (sel-of i p q)
      cyl-ext (coh Q B γ) p q = cong₂ (λ Y ρ → K Q B Y [ ρ ]tm) (mask-ext γ p) (liftS-ext γ p)
      cyl-ext (cst ())    p q

      liftS-ext : ∀ γ → ScSub n γ → liftS D γ ≡ liftS D' γ
      liftS-ext ⟨⟩       p       = refl
      liftS-ext (γ ,ₛ t) (p , q) =
        liftOne-cong' (touched-ext t q) (liftS-ext γ p) (cong (t [_]tm) emm) (cong (t [_]tm) emp)
          (cyl-ext t q)

    private
      k≤W : ∀ k A → T (k <ℕ dim A) → T (k <ℕ suc (dim (baseAt k A)))
      k≤W k A p = subst (λ m → T (k <ℕ suc m)) (sym (dim-baseAt k A (<-suc k (dim A) p))) (n<sn k)

    mutual
      P-ext : ∀ k t A → T (k <ℕ suc (dim A)) → ScTy n A → P D k t A ≡ P D' k t A
      P-ext zero    t A p sA = cong (t [_]tm) emm
      P-ext (suc k) t A p sA =
        rwI-cong' k (dim A) (touched-ext w sw) (P-ext k t A (<-suc k (dim A) p) sA)
          (TP-ext k A (<-suc k (dim A) p) sA) (L-ext k w W (k≤W k A p) (sc-baseAt k A sA))
          (cyl-ext w sw)
        where w = tgtAt k A
              W = baseAt k A
              sw = sc-tgtAt k A p sA

      TP-ext : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TP D k A ≡ TP D' k A
      TP-ext zero    A           p sA = cong (A [_]ty) emm
      TP-ext (suc k) ⋆           () sA
      TP-ext (suc k) (arr A s u) p (sA , ss , su) =
        ifCase (k ==ℕ dim A)
          (λ e → arr≡ (TP-ext k A p sA) (P-ext k s A p sA) (L-ext k u A p sA))
          (λ e → arr≡ (TP-ext (suc k) A (lt-ne k (dim A) p e) sA) (P-ext (suc k) s A (lt-ne k (dim A) p e) sA)
                      (P-ext (suc k) u A (lt-ne k (dim A) p e) sA))

      L-ext : ∀ k t A → T (k <ℕ suc (dim A)) → ScTy n A → L D k t A ≡ L D' k t A
      L-ext zero    t A p sA = cong (t [_]tm) emp
      L-ext (suc k) t A p sA =
        lwI-cong' k (dim A) (touched-ext w sw) (cyl-ext w sw) (P-ext k w W (k≤W k A p) (sc-baseAt k A sA))
          (L-ext k t A (<-suc k (dim A) p) sA) (TL-ext k A (<-suc k (dim A) p) sA)
        where w = srcAt k A
              W = baseAt k A
              sw = sc-srcAt k A p sA

      TL-ext : ∀ k A → T (k <ℕ suc (dim A)) → ScTy n A → TL D k A ≡ TL D' k A
      TL-ext zero    A           p sA = cong (A [_]ty) emp
      TL-ext (suc k) ⋆           () sA
      TL-ext (suc k) (arr A s u) p (sA , ss , su) =
        ifCase (k ==ℕ dim A)
          (λ e → arr≡ (TP-ext k A p sA) (P-ext k s A p sA) (L-ext k u A p sA))
          (λ e → arr≡ (TL-ext (suc k) A (lt-ne k (dim A) p e) sA) (L-ext (suc k) s A (lt-ne k (dim A) p e) sA)
                      (L-ext (suc k) u A (lt-ne k (dim A) p e) sA))

    cylTy-ext : ∀ t A → ScTy n A → cylTy D t A ≡ cylTy D' t A
    cylTy-ext t A sA =
      arr≡ (TP-ext (dim A) A (n<sn (dim A)) sA) (P-ext (dim A) t A (n<sn (dim A)) sA)
           (L-ext (dim A) t A (n<sn (dim A)) sA)
