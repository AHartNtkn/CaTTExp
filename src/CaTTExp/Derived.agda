------------------------------------------------------------------------
-- Derived typing rules for pure CaTT, in every dimension.
--
-- Main results (all k, j; no postulates, checks with --safe):
--
--   rwhisk k j : Γ ⊢sub σ ∶ BK k j → Γ ⊢tm coh (BK k j) (wK k j) σ ∶ wK k j [ σ ]ty
--   lwhisk k j : Γ ⊢sub σ ∶ LK k j → Γ ⊢tm coh (LK k j) (lK k j) σ ∶ lK k j [ σ ]ty
--   comp k     = rwhisk k 0
--
-- i.e. the right whisker c ▹ₖ h and the left whisker h ◃ₖ c of an
-- n-cell c (n = j+k+1) by a (k+1)-cell h along dimension k, and the
-- composite of two (k+1)-cells along k, are well-typed operations.
-- BK, LK, wK, lK are explicit (no fuel); they coincide with what the
-- elaborator GrayCtx.Elab (rw, lw) builds, checked for k + j ≤ 5 in
-- GrayCtx.Checks.WhiskerAgree.
--
-- The proof is by induction on j. The interesting obligations are the
-- side condition (the whisker is an operation: its source uses exactly
-- ∂⁻ and its target exactly ∂⁺ of the pasting context, computed here
-- for all k, j) and that the two faces of the top cell give the same
-- type (the whisker type never mentions the top cell).
--
-- CaTTExp.DerivedBoundary states these rules for given cells (typing
-- of c ▹ₖ h and h ◃ₖ c from that of c and h) and computes their types
-- from the boundary of c.
--
-- Along the way: pasting contexts are well formed (ps-ctx), disks and
-- the classifying substitution of a cell (dsk-wf), and lemmas on free
-- variables under substitution.
------------------------------------------------------------------------
module CaTTExp.Derived where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.Weakening ∅ cattSide using (wk-tm; wk-ty; wk-sub)

closed : Sb.Closed
closed ()

------------------------------------------------------------------------
-- A well-typed term has a well-formed type.

lookup-wf : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
lookup-wf {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
... | true  = subst (λ X → (Γ ▸ B) ⊢ty X) (just-inj eq) (wk-ty b (▸-wf w b))
  where
  just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
  just-inj refl = refl
... | false = wk-ty (lookup-wf w eq) (▸-wf w b)

tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
tm-ty (var-wf w eq)            = lookup-wf w eq
tm-ty (coh-wf _ _ a _ s)       = Sb.ty[] closed a s
tm-ty (cst-wf {k} _ _)         = ⊥-elim k

tm-ctx : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx
tm-ctx (var-wf w _)       = w
tm-ctx (coh-wf _ _ _ _ s) = Sb.sub-ctx closed s
tm-ctx (cst-wf w _)       = w

------------------------------------------------------------------------
-- Pasting contexts are well formed.

T-≡ : ∀ {b} → T b → b ≡ true
T-≡ {true} _ = refl

last-lookup : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
last-lookup Γ A rewrite T-≡ (==ℕ-refl (len Γ)) = refl

ps-wf : ∀ {Γ x A} → Γ ⊢ps x ∶ A → (Γ ⊢ctx) × (Γ ⊢tm var x ∶ A)
ps-wf pss = let w = ▸-wf ε-wf (⋆-wf ε-wf) in w , var-wf w refl
ps-wf (pse {Γ} {x} {A} d) =
  let (w , dx) = ps-wf d
      a  = tm-ty dx
      w₁ = ▸-wf w a
      B  = arr A (var x) (var (len Γ))
      b  = arr-wf (wk-tm dx w₁) (var-wf w₁ (last-lookup Γ A))
      w₂ = ▸-wf w₁ b
  in w₂ , var-wf w₂ (last-lookup (Γ ▸ A) B)
ps-wf (psd d) with ps-wf d
... | w , df with tm-ty df
...   | arr-wf _ dy = w , dy

ps-ctx : ∀ {Γ} → Γ ⊢ps → Γ ⊢ctx
ps-ctx (ps d) = fst (ps-wf d)

------------------------------------------------------------------------
-- Spheres and disks, and the substitution classifying a cell.
--
-- Sph k has the levels 0 … 2k−1, the pair (2i, 2i+1) being the source
-- and target of dimension i; Dsk k adds the generic k-cell at 2k.

open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (sc-aL; dim-aL; <-suc; <-trans; <-≤-trans; n<sn; <→≢; >→≢; ≡-T)

Sph : Nat → Ctx
Sph zero    = ε
Sph (suc k) = Sph k ▸ aL k ▸ aL k

Dsk : Nat → Ctx
Dsk k = Sph k ▸ aL k

len-Sph : ∀ k → len (Sph k) ≡ dbl k
len-Sph zero    = refl
len-Sph (suc k) = cong (λ n → suc (suc n)) (len-Sph k)

-- The boundary of a type, as a substitution into a sphere.
sphSub : Ty → Sub
sphSub ⋆           = ⟨⟩
sphSub (arr A s t) = sphSub A ,ₛ s ,ₛ t

-- The substitution classifying a cell c : C.
dskSub : Tm → Ty → Sub
dskSub c C = sphSub C ,ₛ c

lenₛ-sph : ∀ A → lenₛ (sphSub A) ≡ dbl (dim A)
lenₛ-sph ⋆           = refl
lenₛ-sph (arr A _ _) = cong (λ n → suc (suc n)) (lenₛ-sph A)

sc-aL' : ∀ A → ScTy (lenₛ (sphSub A)) (aL (dim A))
sc-aL' A = subst (λ n → ScTy n (aL (dim A))) (sym (lenₛ-sph A)) (sc-aL (dim A))

<→ff : ∀ n → (n ==ℕ suc n) ≡ false
<→ff zero    = refl
<→ff (suc n) = <→ff n

-- aL (dim A) is the generic type of dimension dim A.
aL-sph : ∀ A → aL (dim A) [ sphSub A ]ty ≡ A
aL-sph ⋆ = refl
aL-sph (arr A s t) rewrite lenₛ-sph A
                         | Sb.ext-ty (aL (dim A)) (sphSub A ,ₛ s) t
                             (Sb.scTy-suc (aL (dim A)) (sc-aL' A))
                         | Sb.ext-ty (aL (dim A)) (sphSub A) s (sc-aL' A)
                         | aL-sph A
                         | <→ff (dbl (dim A))
                         | T-≡ (==ℕ-refl (dbl (dim A))) = refl

sph-wf : ∀ {Γ A} → Γ ⊢ty A → Γ ⊢sub sphSub A ∶ Sph (dim A)
sph-wf (⋆-wf w) = ⟨⟩-wf w
sph-wf {Γ} {arr A s t} (arr-wf ds dt) =
  ,-wf (,-wf (sph-wf (tm-ty ds)) (subst (Γ ⊢tm s ∶_) (sym (aL-sph A)) ds))
       (subst (Γ ⊢tm t ∶_)
         (sym (trans (Sb.ext-ty (aL (dim A)) (sphSub A) s (sc-aL' A)) (aL-sph A))) dt)

dsk-wf : ∀ {Γ c C} → Γ ⊢tm c ∶ C → Γ ⊢sub dskSub c C ∶ Dsk (dim C)
dsk-wf {Γ} {c} {C} d = ,-wf (sph-wf (tm-ty d)) (subst (Γ ⊢tm c ∶_) (sym (aL-sph C)) d)

------------------------------------------------------------------------
-- Disks are pasting contexts.

dsk-ps : ∀ m → Dsk m ⊢ps dbl m ∶ aL m
dsk-ps zero    = pss
dsk-ps (suc m) =
  subst (λ n → (Dsk m ▸ aL m ▸ arr (aL m) (var (dbl m)) (var n)) ⊢ps suc n ∶ arr (aL m) (var (dbl m)) (var n))
        (cong suc (len-Sph m)) (pse (dsk-ps m))

------------------------------------------------------------------------
-- Renamings as substitutions.

renS : Nat → (Nat → Nat) → Sub
renS zero    f = ⟨⟩
renS (suc n) f = renS n f ,ₛ var (f n)

lenₛ-renS : ∀ n f → lenₛ (renS n f) ≡ n
lenₛ-renS zero    f = refl
lenₛ-renS (suc n) f = cong suc (lenₛ-renS n f)

lookup-renS : ∀ n f i → T (i <ℕ n) → lookupₛ (renS n f) i ≡ var (f i)
lookup-renS (suc n) f i p rewrite lenₛ-renS n f with i ==ℕ n in e
... | true  = cong (λ k → var (f k)) (sym (==ℕ-sound i n (≡T e)))
  where ≡T : ∀ {b} → b ≡ true → T b
        ≡T refl = tt
... | false = lookup-renS n f i (<suc-≢' i n p e)
  where
  <suc-≢' : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  <suc-≢' zero    zero    _ ()
  <suc-≢' zero    (suc n) _ _ = tt
  <suc-≢' (suc i) (suc n) p q = <suc-≢' i n p q

------------------------------------------------------------------------
-- Finite sets of levels.

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

Mem : Nat → List Nat → Set
Mem n xs = T (elem n xs)

_⊆_ : List Nat → List Nat → Set
xs ⊆ ys = ∀ n → Mem n xs → Mem n ys

∨-l : ∀ {a b} → T a → T (a ∨ b)
∨-l {true} _ = tt

∨-r : ∀ {a b} → T b → T (a ∨ b)
∨-r {true}  _ = tt
∨-r {false} p = p

∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
∧-in {true} _ q = q

mem++ : ∀ n xs ys → Mem n (xs ++ ys) → Mem n xs ⊎ Mem n ys
mem++ n []       ys p = inj₂ p
mem++ n (x ∷ xs) ys p with n ==ℕ x
... | true  = inj₁ tt
... | false = mem++ n xs ys p

mem++l : ∀ n xs ys → Mem n xs → Mem n (xs ++ ys)
mem++l n (x ∷ xs) ys p with n ==ℕ x
... | true  = tt
... | false = mem++l n xs ys p

mem++r : ∀ n xs ys → Mem n ys → Mem n (xs ++ ys)
mem++r n []       ys p = p
mem++r n (x ∷ xs) ys p with n ==ℕ x
... | true  = tt
... | false = mem++r n xs ys p

mem-one : ∀ n x → Mem n (x ∷ []) → n ≡ x
mem-one n x p with n ==ℕ x in e
... | true = ==ℕ-sound n x (≡-T e)

mem-snoc : ∀ n xs x → Mem n (snoc xs x) → Mem n xs ⊎ (n ≡ x)
mem-snoc n xs x p with mem++ n xs (x ∷ []) p
... | inj₁ q = inj₁ q
... | inj₂ q = inj₂ (mem-one n x q)

⊆?-complete : ∀ xs ys → xs ⊆ ys → T (⊆? xs ys)
⊆?-complete []       ys h = tt
⊆?-complete (x ∷ xs) ys h =
  ∧-in (h x (∨-l (==ℕ-refl x))) (⊆?-complete xs ys (λ n q → h n (∨-r q)))

-- xs ++ ys ≈ xs once ys ⊆ xs.
≈-absorb : ∀ xs ys → ys ⊆ xs → T (≈? (xs ++ ys) xs)
≈-absorb xs ys h =
  ∧-in (⊆?-complete (xs ++ ys) xs (λ n p → back n (mem++ n xs ys p)))
       (⊆?-complete xs (xs ++ ys) (λ n p → mem++l n xs ys p))
  where
  back : ∀ n → Mem n xs ⊎ Mem n ys → Mem n xs
  back n (inj₁ p) = p
  back n (inj₂ q) = h n q

------------------------------------------------------------------------
-- The levels 0 … m−1, and the boundaries of disks and of Bctx.

upTo : Nat → List Nat
upTo zero    = []
upTo (suc n) = snoc (upTo n) n

mem-upTo : ∀ n m → Mem n (upTo m) → T (n <ℕ m)
mem-upTo n (suc m) p with mem-snoc n (upTo m) m p
... | inj₁ q    = <-suc n m (mem-upTo n m q)
... | inj₂ refl = n<sn n

dropLast-snoc : ∀ xs x → dropLastᴸ (snoc xs x) ≡ xs
dropLast-snoc []           x = refl
dropLast-snoc (y ∷ [])     x = refl
dropLast-snoc (y ∷ z ∷ xs) x = cong (y ∷_) (dropLast-snoc (z ∷ xs) x)

len-Dsk : ∀ m → len (Dsk m) ≡ suc (dbl m)
len-Dsk m = cong suc (len-Sph m)

≤→≮ : ∀ m i → T (m <ℕ i) → (i <ℕ suc m) ≡ false
≤→≮ zero    (suc i) _ = refl
≤→≮ (suc m) (suc i) p = ≤→≮ m i p

<→≮ : ∀ m i → T (m <ℕ i) → (i <ℕ m) ≡ false
<→≮ zero    (suc i) _ = refl
<→≮ (suc m) (suc i) p = <→≮ m i p

src-Dsk : ∀ i m → T (m <ℕ suc i) → srcVars i (Dsk m) ≡ upTo (suc (dbl m))
src-Dsk i zero    _ = refl
src-Dsk i (suc m) p rewrite dim-aL m | ≤→≮ m i p | src-Dsk i m (<-suc m i p) | len-Sph m = refl

tgt-Dsk : ∀ i m → T (m <ℕ suc i) → tgtVars i (Dsk m) ≡ upTo (suc (dbl m))
tgt-Dsk i zero    _ = refl
tgt-Dsk i (suc m) p rewrite dim-aL m | <→≮ m i p | <→≢ m i p | tgt-Dsk i m (<-suc m i p) | len-Sph m = refl

n≮n : ∀ n → (n <ℕ n) ≡ false

src-Dsk-top : ∀ i → srcVars i (Dsk (suc i)) ≡ upTo (suc (dbl i))
src-Dsk-top i rewrite dim-aL i | T-≡ (n<sn i) = src-Dsk i i (n<sn i)

tgt-Dsk-top : ∀ i → tgtVars i (Dsk (suc i)) ≡ snoc (upTo (dbl i)) (suc (dbl i))
tgt-Dsk-top i rewrite dim-aL i | n≮n i | T-≡ (==ℕ-refl i) | tgt-Dsk i i (n<sn i)
                    | dropLast-snoc (upTo (dbl i)) (dbl i) | len-Sph i = refl

n≮n zero    = refl
n≮n (suc n) = n≮n n

max-le : ∀ a b → T (b <ℕ suc a) → max a b ≡ a
max-le zero    zero    _ = refl
max-le (suc a) zero    _ = refl
max-le (suc a) (suc b) p = cong suc (max-le a b p)

dimCtx-Sph : ∀ k → T (dimCtx (Sph k) <ℕ suc k)
dimCtx-Sph zero    = tt
dimCtx-Sph (suc k) rewrite dim-aL k | max-le k (dimCtx (Sph k)) (dimCtx-Sph k) | max-le k k (n<sn k) = <-suc k (suc k) (n<sn k)

fv-sph : ∀ k → fvSub (sphSub (aL k)) ≡ upTo (dbl k)
fv-sph zero    = refl
fv-sph (suc k) rewrite fv-sph k = refl

dimCtx-Dsk : ∀ m → dimCtx (Dsk m) ≡ m
dimCtx-Dsk m rewrite dim-aL m = max-le m (dimCtx (Sph m)) (dimCtx-Sph m)

------------------------------------------------------------------------
-- Free variables under substitution.

lk-fv : ∀ σ i → T (i <ℕ lenₛ σ) → fvTm (lookupₛ σ i) ⊆ fvSub σ
lk-fv (σ ,ₛ t) i p n q with i ==ℕ lenₛ σ in e
... | true  = mem++r n (fvSub σ) (fvTm t) q
... | false = mem++l n (fvSub σ) (fvTm t) (lk-fv σ i (<suc-ne i (lenₛ σ) p e) n q)
  where
  <suc-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  <suc-ne zero    zero    _ ()
  <suc-ne zero    (suc n) _ _ = tt
  <suc-ne (suc i) (suc n) p q = <suc-ne i n p q

mutual
  fv-ty[] : ∀ A σ → ScTy (lenₛ σ) A → fvTy (A [ σ ]ty) ⊆ fvSub σ
  fv-ty[] ⋆           σ _           n ()
  fv-ty[] (arr A t u) σ (a , p , q) n m with mem++ n (fvTy (A [ σ ]ty)) _ m
  ... | inj₁ r = fv-ty[] A σ a n r
  ... | inj₂ r with mem++ n (fvTm (t [ σ ]tm)) _ r
  ...   | inj₁ s = fv-tm[] t σ p n s
  ...   | inj₂ s = fv-tm[] u σ q n s

  fv-tm[] : ∀ t σ → ScTm (lenₛ σ) t → fvTm (t [ σ ]tm) ⊆ fvSub σ
  fv-tm[] (var i)     σ p = lk-fv σ i p
  fv-tm[] (coh Δ A τ) σ p = fv-sub[] τ σ p
  fv-tm[] (cst ())    σ p

  fv-sub[] : ∀ τ σ → ScSub (lenₛ σ) τ → fvSub (τ ∘ σ) ⊆ fvSub σ
  fv-sub[] ⟨⟩       σ _       n ()
  fv-sub[] (τ ,ₛ t) σ (p , q) n m with mem++ n (fvSub (τ ∘ σ)) _ m
  ... | inj₁ r = fv-sub[] τ σ p n r
  ... | inj₂ r = fv-tm[] t σ q n r

-- Substitutions agreeing on the free variables act alike.
mutual
  agree-ty : ∀ A σ τ → (∀ w → Mem w (fvTy A) → lookupₛ σ w ≡ lookupₛ τ w) → A [ σ ]ty ≡ A [ τ ]ty
  agree-ty ⋆           σ τ h = refl
  agree-ty (arr A t u) σ τ h =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (agree-ty A σ τ (λ w m → h w (mem++l w (fvTy A) _ m)))
      (cong₂ _,_ (agree-tm t σ τ (λ w m → h w (mem++r w (fvTy A) _ (mem++l w (fvTm t) _ m))))
                 (agree-tm u σ τ (λ w m → h w (mem++r w (fvTy A) _ (mem++r w (fvTm t) _ m)))))

  agree-tm : ∀ t σ τ → (∀ w → Mem w (fvTm t) → lookupₛ σ w ≡ lookupₛ τ w) → t [ σ ]tm ≡ t [ τ ]tm
  agree-tm (var i)     σ τ h = h i (∨-l (==ℕ-refl i))
  agree-tm (coh Δ A ρ) σ τ h = cong (coh Δ A) (agree-sub ρ σ τ h)
  agree-tm (cst ())    σ τ h

  agree-sub : ∀ ρ σ τ → (∀ w → Mem w (fvSub ρ) → lookupₛ σ w ≡ lookupₛ τ w) → ρ ∘ σ ≡ ρ ∘ τ
  agree-sub ⟨⟩       σ τ h = refl
  agree-sub (ρ ,ₛ t) σ τ h =
    cong₂ _,ₛ_ (agree-sub ρ σ τ (λ w m → h w (mem++l w (fvSub ρ) _ m)))
               (agree-tm t σ τ (λ w m → h w (mem++r w (fvSub ρ) _ m)))

------------------------------------------------------------------------
-- Small lemmas.

lk-face : ∀ S v v' z h w → (w ==ℕ lenₛ S) ≡ false →
          lookupₛ (S ,ₛ var v ,ₛ z ,ₛ h) w ≡ lookupₛ (S ,ₛ var v' ,ₛ z ,ₛ h) w
lk-face S v v' z h w ne with w ==ℕ suc (suc (lenₛ S))
... | true  = refl
... | false with w ==ℕ suc (lenₛ S)
...   | true  = refl
...   | false rewrite ne = refl

lenₛ-sphL : ∀ k → lenₛ (sphSub (aL k)) ≡ dbl k
lenₛ-sphL k = trans (lenₛ-sph (aL k)) (cong dbl (dim-aL k))

<-irr' : ∀ n → T (n <ℕ n) → ⊥
<-irr' (suc n) p = <-irr' n p

lt-absurd : ∀ a b → T (a <ℕ b) → T (b <ℕ suc a) → ⊥
lt-absurd zero    (suc b) _ ()
lt-absurd (suc a) (suc b) p q = lt-absurd a b p q

ss≮ : ∀ d → T (suc (suc d) <ℕ d) → ⊥
ss≮ d p = lt-absurd (suc (suc d)) d p (<-suc d (suc (suc d)) (<-suc d (suc d) (n<sn d)))

n≢ssn : ∀ n → n ≡ suc (suc n) → ⊥
n≢ssn n e = <-irr' n (subst (λ x → T (n <ℕ x)) (sym e) (<-suc n (suc n) (n<sn n)))

n≢sn : ∀ n → n ≡ suc n → ⊥
n≢sn n e = <-irr' n (subst (λ x → T (n <ℕ x)) (sym e) (n<sn n))

lk-skip : ∀ Γ A i → T (i <ℕ len Γ) → lookup (Γ ▸ A) i ≡ lookup Γ i
lk-skip Γ A i p rewrite <→≢ i (len Γ) p = refl

idS : Nat → Sub
idS n = renS n (λ i → i)

fv-idS : ∀ n → fvSub (idS n) ≡ upTo n
fv-idS zero    = refl
fv-idS (suc n) rewrite fv-idS n = refl

-- The identity substitution.

mutual
  id-ty : ∀ n A → ScTy n A → A [ idS n ]ty ≡ A
  id-ty n ⋆           _           = refl
  id-ty n (arr A t u) (a , p , q) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (id-ty n A a)
      (cong₂ _,_ (id-tm n t p) (id-tm n u q))

  id-tm : ∀ n t → ScTm n t → t [ idS n ]tm ≡ t
  id-tm n (var i)     p = lookup-renS n (λ i → i) i p
  id-tm n (coh Δ A σ) p = cong (coh Δ A) (id-sub n σ p)
  id-tm n (cst ())    _

  id-sub : ∀ n σ → ScSub n σ → σ ∘ idS n ≡ σ
  id-sub n ⟨⟩       _       = refl
  id-sub n (σ ,ₛ t) (p , q) = cong₂ _,ₛ_ (id-sub n σ p) (id-tm n t q)

id-wf : ∀ {Γ} → Γ ⊢ctx → Γ ⊢sub idS (len Γ) ∶ Γ
id-wf ε-wf = ⟨⟩-wf ε-wf
id-wf (▸-wf {Γ} {A} w a) =
  ,-wf (wk-sub (id-wf w) w')
       (subst ((Γ ▸ A) ⊢tm var (len Γ) ∶_) (sym (id-ty (len Γ) A (Sb.ty-sc closed a)))
              (var-wf w' (last-lookup Γ A)))
  where w' = ▸-wf w a

ctx-init : ∀ {Γ A} → (Γ ▸ A) ⊢ctx → Γ ⊢ctx
ctx-init (▸-wf w _) = w

ctx-last : ∀ {Γ A} → (Γ ▸ A) ⊢ctx → Γ ⊢ty A
ctx-last (▸-wf _ a) = a

------------------------------------------------------------------------
-- More arithmetic and list facts.

++-assoc : ∀ (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

fvTy-aL : ∀ k → fvTy (aL k) ≡ upTo (dbl k)
fvTy-aL zero    = refl
fvTy-aL (suc k) rewrite fvTy-aL k = sym (++-assoc (upTo (dbl k)) (dbl k ∷ []) (suc (dbl k) ∷ []))

≈-cons-snoc : ∀ x L → T (≈? (x ∷ L) (snoc L x))
≈-cons-snoc x L =
  ∧-in (⊆?-complete (x ∷ L) (snoc L x) to) (⊆?-complete (snoc L x) (x ∷ L) from)
  where
  to : (x ∷ L) ⊆ snoc L x
  to n m with n ==ℕ x in e
  ... | true  = mem++r n L (x ∷ []) (subst (λ b → T (b ∨ false)) (sym e) tt)
  ... | false = mem++l n L (x ∷ []) m
  from : snoc L x ⊆ (x ∷ L)
  from n m with mem-snoc n L x m
  ... | inj₁ q    = ∨-r q
  ... | inj₂ refl = ∨-l (==ℕ-refl n)

max-ge : ∀ a b → T (a <ℕ suc b) → max a b ≡ b
max-ge zero    b       _ = refl
max-ge (suc a) (suc b) p = cong suc (max-ge a b p)

k<n : ∀ j k → T (k <ℕ suc (j + k))
k<n zero    k = n<sn k
k<n (suc j) k = <-suc k (suc (j + k)) (k<n j k)

≤-≮ : ∀ a b → T (a <ℕ suc b) → (b <ℕ a) ≡ false
≤-≮ zero    b       _ = refl
≤-≮ (suc a) zero    ()
≤-≮ (suc a) (suc b) p = ≤-≮ a b p

<suc-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
<suc-ne zero    zero    _ ()
<suc-ne zero    (suc n) _ _ = tt
<suc-ne (suc i) (suc n) p q = <suc-ne i n p q

------------------------------------------------------------------------
-- Lookups in spheres, disks and their classifying substitutions.

lk-ext : ∀ σ t i → T (i <ℕ lenₛ σ) → lookupₛ (σ ,ₛ t) i ≡ lookupₛ σ i
lk-ext σ t i p rewrite <→≢ i (lenₛ σ) p = refl

lk-sph : ∀ n i → T (i <ℕ dbl n) → lookupₛ (sphSub (aL n)) i ≡ var i
lk-sph (suc n) i p rewrite lenₛ-sphL n with i ==ℕ suc (dbl n) in e₁
... | true  = cong var (sym (==ℕ-sound i _ (≡-T e₁)))
... | false with i ==ℕ dbl n in e₂
...   | true  = cong var (sym (==ℕ-sound i _ (≡-T e₂)))
...   | false = lk-sph n i (<suc-ne i (dbl n) (<suc-ne i (suc (dbl n)) p e₁) e₂)

-- A substitution fixing the variables below n fixes what is scoped in n.
mutual
  fix-ty : ∀ n A σ → ScTy n A → (∀ i → T (i <ℕ n) → lookupₛ σ i ≡ var i) → A [ σ ]ty ≡ A
  fix-ty n ⋆           σ _           h = refl
  fix-ty n (arr A t u) σ (a , p , q) h =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (fix-ty n A σ a h)
      (cong₂ _,_ (fix-tm n t σ p h) (fix-tm n u σ q h))

  fix-tm : ∀ n t σ → ScTm n t → (∀ i → T (i <ℕ n) → lookupₛ σ i ≡ var i) → t [ σ ]tm ≡ t
  fix-tm n (var i)     σ p h = h i p
  fix-tm n (coh Δ A τ) σ p h = cong (coh Δ A) (fix-sub n τ σ p h)
  fix-tm n (cst ())    σ p h

  fix-sub : ∀ n τ σ → ScSub n τ → (∀ i → T (i <ℕ n) → lookupₛ σ i ≡ var i) → τ ∘ σ ≡ τ
  fix-sub n ⟨⟩       σ _       h = refl
  fix-sub n (τ ,ₛ t) σ (p , q) h = cong₂ _,ₛ_ (fix-sub n τ σ p h) (fix-tm n t σ q h)

lk-Sph-s : ∀ k → lookup (Sph (suc k)) (dbl k) ≡ just (aL k)
lk-Sph-s k = subst (λ i → lookup (Sph (suc k)) i ≡ just (aL k)) (len-Sph k)
               (trans (lk-skip (Sph k ▸ aL k) (aL k) (len (Sph k)) (n<sn (len (Sph k))))
                      (last-lookup (Sph k) (aL k)))

lk-Sph-t : ∀ k → lookup (Sph (suc k)) (suc (dbl k)) ≡ just (aL k)
lk-Sph-t k = subst (λ i → lookup (Sph (suc k)) (suc i) ≡ just (aL k)) (len-Sph k)
               (last-lookup (Sph k ▸ aL k) (aL k))

------------------------------------------------------------------------
-- Descending a pasting derivation along iterated targets.

downK : ∀ {Γ} j k x → Γ ⊢ps x ∶ aL (suc (j + k)) → Γ ⊢ps suc (dbl k) ∶ aL k
downK zero    k x d = psd d
downK (suc j) k x d = downK j k (suc (dbl (suc (j + k)))) (psd d)

toStar : ∀ {Γ} k x → Γ ⊢ps x ∶ aL k → Σ Nat (λ y → Γ ⊢ps y ∶ ⋆)
toStar zero    x d = x , d
toStar (suc k) x d = toStar k (suc (dbl k)) (psd d)

------------------------------------------------------------------------
-- Right whiskering along k of an n-cell c by a (k+1)-cell h, where
-- n = j+k+1, over the pasting context
--
--   BK k j = Dⁿ             (c at level 2n; its i-source and i-target,
--                            i < n, at 2i and 2i+1),
--            z : aL k       (level zK k j = 2n+1),
--            h : t_k c → z  (level 2n+2).
--
-- The whisker c ▹ₖ h is coh (BK k j) (wK k j); for j = 0 it is the
-- composite c ;ₖ h of two (k+1)-cells along k. wK is the type the
-- elaborator `rw` (GrayCtx.Elab) builds: for j ≥ 1 it is
-- (s c ▹ₖ h) → (t c ▹ₖ h), the whiskers of the faces of c.

nB : Nat → Nat → Nat
nB k j = suc (j + k)

zK : Nat → Nat → Nat
zK k j = suc (dbl (nB k j))

hTy : Nat → Nat → Ty
hTy k j = arr (aL k) (var (suc (dbl k))) (var (zK k j))

BK : Nat → Nat → Ctx
BK k j = Dsk (nB k j) ▸ aL k ▸ hTy k j

-- BK k j into BK k (j+1), onto a face (level v) of the top cell.
ρK : Nat → Nat → Nat → Sub
ρK k j v = dskSub (var v) (aL (nB k j)) ,ₛ var (zK k (suc j)) ,ₛ var (suc (zK k (suc j)))

ρsK ρtK : Nat → Nat → Sub
ρsK k j = ρK k j (dbl (nB k j))
ρtK k j = ρK k j (suc (dbl (nB k j)))

wK : Nat → Nat → Ty
wK k zero    = arr (aL k) (var (dbl k)) (var (zK k zero))
wK k (suc j) = arr (wK k j [ ρsK k j ]ty) (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j))

BK-ps : ∀ k j → BK k j ⊢ps
BK-ps k j =
  let d = downK j k (dbl (nB k j)) (dsk-ps (nB k j))
      e = subst (λ m → (Dsk (nB k j) ▸ aL k ▸ arr (aL k) (var (suc (dbl k))) (var m))
                         ⊢ps suc m ∶ arr (aL k) (var (suc (dbl k))) (var m))
                (len-Dsk (nB k j)) (pse d)
  in ps (snd (toStar k (zK k j) (psd e)))

wBK : ∀ k j → BK k j ⊢ctx
wBK k j = ps-ctx (BK-ps k j)

-- Boundaries.
dimCtx-BK : ∀ k j → dimCtx (BK k j) ≡ nB k j
dimCtx-BK k j =
  trans (cong₂ max (cong suc (dim-aL k)) (cong₂ max (dim-aL k) (dimCtx-Dsk (nB k j))))
        (trans (cong (max (suc k)) (max-ge k (nB k j) (<-suc k (nB k j) (k<n j k))))
               (max-ge (suc k) (nB k j) (k<n j k)))

fv-ρK : ∀ k j v → fvSub (ρK k j v) ≡ snoc (snoc (snoc (upTo (dbl (nB k j))) v) (zK k (suc j))) (suc (zK k (suc j)))
fv-ρK k j v rewrite fv-sph (nB k j) = refl

src-BK : ∀ k j → ∂⁻ (BK k (suc j)) ≡ fvSub (ρsK k j)
src-BK k j rewrite dimCtx-BK k (suc j) | dim-aL k | ≤-≮ k (j + k) (k<n j k) | src-Dsk-top (nB k j)
                 | fv-ρK k j (dbl (nB k j)) | len-Sph (j + k) = refl

tgt-BK : ∀ k j → ∂⁺ (BK k (suc j)) ≡ fvSub (ρtK k j)
tgt-BK k j rewrite dimCtx-BK k (suc j) | dim-aL k | ≤-≮ k (suc (j + k)) (<-suc k (suc (j + k)) (k<n j k))
                 | <→≢ k (suc (j + k)) (k<n j k) | tgt-Dsk-top (nB k j)
                 | fv-ρK k j (suc (dbl (nB k j))) | len-Sph (j + k) = refl

-- The base case j = 0: composition of two (k+1)-cells along k.
src-BK0 : ∀ k → ∂⁻ (BK k 0) ≡ snoc (upTo (dbl k)) (dbl k)
src-BK0 k rewrite dimCtx-BK k 0 | dim-aL k | T-≡ (n<sn k) | src-Dsk k k (n<sn k) = refl

tgt-BK0 : ∀ k → ∂⁺ (BK k 0) ≡ snoc (upTo (dbl k)) (zK k 0)
tgt-BK0 k rewrite dimCtx-BK k 0 | dim-aL k | n≮n k | T-≡ (==ℕ-refl k) | tgt-Dsk k k (n<sn k)
                | dropLast-snoc (upTo (dbl k)) (dbl k) | len-Sph k | dropLast-snoc (upTo (dbl k)) (suc (dbl k)) = refl

subst₂ : ∀ {A B : Set} (P : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → P a b → P a' b'
subst₂ P refl refl p = p

side-BK0 : ∀ k → T (cattSide (BK k 0) (aL k) (var (dbl k)) (var (zK k 0)))
side-BK0 k =
  ∨-r (∧-in (subst₂ (λ X L → T (≈? (dbl k ∷ X) L)) (sym (fvTy-aL k)) (sym (src-BK0 k))
               (≈-cons-snoc (dbl k) (upTo (dbl k))))
            (subst₂ (λ X L → T (≈? (zK k 0 ∷ X) L)) (sym (fvTy-aL k)) (sym (tgt-BK0 k))
               (≈-cons-snoc (zK k 0) (upTo (dbl k)))))

-- The two faces differ only at the top cell 2n of BK k j.
lk-ρK : ∀ k j v v' w → (w ==ℕ dbl (nB k j)) ≡ false → lookupₛ (ρK k j v) w ≡ lookupₛ (ρK k j v') w
lk-ρK k j v v' w ne =
  lk-face (sphSub (aL (nB k j))) v v' (var (zK k (suc j))) (var (suc (zK k (suc j)))) w
          (trans (cong (w ==ℕ_) (lenₛ-sphL (nB k j))) ne)

faces-BK : ∀ k j A → ¬ Mem (dbl (nB k j)) (fvTy A) → A [ ρsK k j ]ty ≡ A [ ρtK k j ]ty
faces-BK k j A av = agree-ty A (ρsK k j) (ρtK k j) (λ w m → lk-ρK k j _ _ w (ne w m))
  where
  ne : ∀ w → Mem w (fvTy A) → (w ==ℕ dbl (nB k j)) ≡ false
  ne w m with w ==ℕ dbl (nB k j) in e
  ... | true  = ⊥-elim (av (subst (λ x → Mem x (fvTy A)) (==ℕ-sound w _ (≡-T e)) m))
  ... | false = refl

lenρK : ∀ k j v → lenₛ (ρK k j v) ≡ len (BK k j)
lenρK k j v rewrite lenₛ-sphL (nB k j) | len-Sph (nB k j) = refl

sc-ρK : ∀ k j v → ScTy (len (BK k j)) (wK k j) → ScTy (lenₛ (ρK k j v)) (wK k j)
sc-ρK k j v sc = subst (λ n → ScTy n (wK k j)) (sym (lenρK k j v)) sc

-- The top cell 2(n+1) of BK k (j+1) is free in no face.
notIn-ρK : ∀ k j v → T (v <ℕ dbl (suc (nB k j))) → ¬ Mem (dbl (suc (nB k j))) (fvSub (ρK k j v))
notIn-ρK k j v lt m rewrite fv-ρK k j v = go (mem-snoc D L3 (suc z') m)
  where
  D  = dbl (suc (nB k j))
  z' = zK k (suc j)
  L2 = snoc (upTo (dbl (nB k j))) v
  L3 = snoc L2 z'
  go₃ : Mem D (upTo (dbl (nB k j))) ⊎ (D ≡ v) → ⊥
  go₃ (inj₁ m₃) = ss≮ (dbl (nB k j)) (mem-upTo D (dbl (nB k j)) m₃)
  go₃ (inj₂ e)  = <-irr' v (subst (λ x → T (v <ℕ x)) e lt)
  go₂ : Mem D L2 ⊎ (D ≡ z') → ⊥
  go₂ (inj₁ m₂) = go₃ (mem-snoc D (upTo (dbl (nB k j))) v m₂)
  go₂ (inj₂ e)  = n≢sn D e
  go : Mem D L3 ⊎ (D ≡ suc z') → ⊥
  go (inj₁ m₁) = go₂ (mem-snoc D L2 z' m₁)
  go (inj₂ e)  = n≢ssn D e

lt-sK : ∀ k j → T (dbl (nB k j) <ℕ dbl (suc (nB k j)))
lt-sK k j = <-suc (dbl (nB k j)) (suc (dbl (nB k j))) (n<sn (dbl (nB k j)))

lt-tK : ∀ k j → T (suc (dbl (nB k j)) <ℕ dbl (suc (nB k j)))
lt-tK k j = n<sn (suc (dbl (nB k j)))

avoid-BK0 : ∀ k → ¬ Mem (dbl (nB k 0)) (fvTy (wK k 0))
avoid-BK0 k m rewrite fvTy-aL k with mem++ D (upTo (dbl k)) (dbl k ∷ zK k 0 ∷ []) m
  where D = dbl (suc k)
... | inj₁ q = ss≮ (dbl k) (mem-upTo (dbl (suc k)) (dbl k) q)
... | inj₂ q with mem++ (dbl (suc k)) (dbl k ∷ []) (zK k 0 ∷ []) q
...   | inj₁ r = n≢ssn (dbl k) (sym (mem-one (dbl (suc k)) (dbl k) r))
...   | inj₂ r = n≢sn (dbl (suc k)) (mem-one (dbl (suc k)) (zK k 0) r)

avoid-BK : ∀ k j → ScTy (len (BK k j)) (wK k j) → ¬ Mem (dbl (nB k (suc j))) (fvTy (wK k (suc j)))
avoid-BK k j sc m with mem++ D (fvTy (wK k j [ ρsK k j ]ty)) (fvSub (ρsK k j) ++ fvSub (ρtK k j)) m
  where D = dbl (nB k (suc j))
... | inj₁ r = notIn-ρK k j _ (lt-sK k j) (fv-ty[] (wK k j) (ρsK k j) (sc-ρK k j (dbl (nB k j)) sc) _ r)
... | inj₂ r with mem++ (dbl (nB k (suc j))) (fvSub (ρsK k j)) (fvSub (ρtK k j)) r
...   | inj₁ s = notIn-ρK k j _ (lt-sK k j) s
...   | inj₂ s = notIn-ρK k j _ (lt-tK k j) s

side-BK : ∀ k j → ScTy (len (BK k j)) (wK k j) → ¬ Mem (dbl (nB k j)) (fvTy (wK k j)) →
          T (cattSide (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                      (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j)))
side-BK k j sc av = ∨-r
  (∧-in (subst (λ L → T (≈? (fvSub (ρsK k j) ++ fvTy A) L)) (sym (src-BK k j))
          (≈-absorb (fvSub (ρsK k j)) (fvTy A) (fv-ty[] (wK k j) (ρsK k j) (sc-ρK k j (dbl (nB k j)) sc))))
        (subst (λ L → T (≈? (fvSub (ρtK k j) ++ fvTy A) L)) (sym (tgt-BK k j))
          (≈-absorb (fvSub (ρtK k j)) (fvTy A)
            (subst (λ X → fvTy X ⊆ fvSub (ρtK k j)) (sym (faces-BK k j (wK k j) av))
              (fv-ty[] (wK k j) (ρtK k j) (sc-ρK k j (suc (dbl (nB k j))) sc))))))
  where A = wK k j [ ρsK k j ]ty

-- Lookups in BK k j.
lk-BK-Sph : ∀ k j i → T (i <ℕ dbl (nB k j)) → lookup (BK k j) i ≡ lookup (Sph (nB k j)) i
lk-BK-Sph k j i p =
  trans (lk-skip (S ▸ aL n ▸ aL k) (hTy k j) i (<-suc i (suc (len S)) (<-suc i (len S) q)))
  (trans (lk-skip (S ▸ aL n) (aL k) i (<-suc i (len S) q))
         (lk-skip S (aL n) i q))
  where
  n = nB k j
  S = Sph n
  q = subst (λ m → T (i <ℕ m)) (sym (len-Sph n)) p

lk-zK : ∀ k j → lookup (BK k j) (zK k j) ≡ just (aL k)
lk-zK k j = subst (λ i → lookup (BK k j) i ≡ just (aL k)) (len-Dsk (nB k j))
              (trans (lk-skip (Dsk (nB k j) ▸ aL k) (hTy k j) (len (Dsk (nB k j))) (n<sn (len (Dsk (nB k j)))))
                     (last-lookup (Dsk (nB k j)) (aL k)))

lk-hK : ∀ k j → lookup (BK k j) (suc (zK k j)) ≡ just (hTy k j)
lk-hK k j = subst (λ i → lookup (BK k j) (suc i) ≡ just (hTy k j)) (len-Dsk (nB k j))
              (last-lookup (Dsk (nB k j) ▸ aL k) (hTy k j))

dbl-mono : ∀ k n → T (k <ℕ suc n) → T (dbl k <ℕ suc (dbl n))
dbl-mono zero    n       _ = tt
dbl-mono (suc k) (suc n) p = dbl-mono k n p

lt-dbl : ∀ i k n → T (i <ℕ dbl k) → T (k <ℕ suc n) → T (i <ℕ dbl n)
lt-dbl i k n p q = <-≤-trans i (dbl k) (dbl n) p (dbl-mono k n q)

-- The classifying substitution of a face fixes the levels below it.
lkσ : ∀ n v z i → T (i <ℕ dbl n) → lookupₛ (sphSub (aL n) ,ₛ var v ,ₛ z) i ≡ var i
lkσ n v z i p =
  trans (lk-ext (sphSub (aL n) ,ₛ var v) z i (<-suc i (lenₛ (sphSub (aL n))) q))
  (trans (lk-ext (sphSub (aL n)) (var v) i q) (lk-sph n i p))
  where q = subst (λ m → T (i <ℕ m)) (sym (lenₛ-sphL n)) p

fix-aL : ∀ k n v z → T (k <ℕ suc n) → aL k [ sphSub (aL n) ,ₛ var v ,ₛ z ]ty ≡ aL k
fix-aL k n v z q = fix-ty (dbl k) (aL k) _ (sc-aL k) (λ i p → lkσ n v z i (lt-dbl i k n p q))

fix-aL1 : ∀ k n v → T (k <ℕ suc n) → aL k [ sphSub (aL n) ,ₛ var v ]ty ≡ aL k
fix-aL1 k n v q = fix-ty (dbl k) (aL k) _ (sc-aL k)
  (λ i p → trans (lk-ext (sphSub (aL n)) (var v) i
                    (subst (λ m → T (i <ℕ m)) (sym (lenₛ-sphL n)) (lt-dbl i k n p q)))
                 (lk-sph n i (lt-dbl i k n p q)))

lk-top : ∀ σ t → lookupₛ (σ ,ₛ t) (lenₛ σ) ≡ t
lk-top σ t rewrite T-≡ (==ℕ-refl (lenₛ σ)) = refl

lkz : ∀ n v z → lookupₛ (sphSub (aL n) ,ₛ var v ,ₛ z) (suc (dbl n)) ≡ z
lkz n v z = subst (λ m → lookupₛ (sphSub (aL n) ,ₛ var v ,ₛ z) (suc m) ≡ z) (lenₛ-sphL n)
              (lk-top (sphSub (aL n) ,ₛ var v) z)

ty-hK : ∀ k j v → hTy k j [ dskSub (var v) (aL (nB k j)) ,ₛ var (zK k (suc j)) ]ty ≡ hTy k (suc j)
ty-hK k j v =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (fix-aL k (nB k j) v (var (zK k (suc j))) (<-suc k (nB k j) (k<n j k)))
    (cong₂ _,_ (lkσ (nB k j) v (var (zK k (suc j))) (suc (dbl k))
                  (lt-dbl (suc (dbl k)) (suc k) (nB k j) (n<sn (suc (dbl k))) (k<n j k)))
               (lkz (nB k j) v (var (zK k (suc j)))))

ρK-wf : ∀ k j v → lookup (BK k (suc j)) v ≡ just (aL (nB k j)) → BK k (suc j) ⊢sub ρK k j v ∶ BK k j
ρK-wf k j v lv =
  ,-wf (,-wf D (subst (BK k (suc j) ⊢tm var (zK k (suc j)) ∶_)
                      (sym (fix-aL1 k (nB k j) v (<-suc k (nB k j) (k<n j k))))
                      (var-wf w (lk-zK k (suc j)))))
       (subst (BK k (suc j) ⊢tm var (suc (zK k (suc j))) ∶_) (sym (ty-hK k j v)) (var-wf w (lk-hK k (suc j))))
  where
  w = wBK k (suc j)
  D : BK k (suc j) ⊢sub dskSub (var v) (aL (nB k j)) ∶ Dsk (nB k j)
  D = subst (λ m → BK k (suc j) ⊢sub dskSub (var v) (aL (nB k j)) ∶ Dsk m) (dim-aL (nB k j))
            (dsk-wf (var-wf w lv))

-- The whisker coherences are well typed, for every k and j.
SideK : Nat → Nat → Set
SideK k zero    = T (cattSide (BK k 0) (aL k) (var (dbl k)) (var (zK k 0)))
SideK k (suc j) = T (cattSide (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                       (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j)))

rwhisk' : ∀ k j {Γ σ} → BK k j ⊢ty wK k j → SideK k j → Γ ⊢sub σ ∶ BK k j →
          Γ ⊢tm coh (BK k j) (wK k j) σ ∶ wK k j [ σ ]ty
rwhisk' k zero    a s d = coh-wf (BK-ps k zero)    (wBK k zero)    a s d
rwhisk' k (suc j) a s d = coh-wf (BK-ps k (suc j)) (wBK k (suc j)) a s d

lk-face-s : ∀ k j → lookup (BK k (suc j)) (dbl (nB k j)) ≡ just (aL (nB k j))
lk-face-s k j = trans (lk-BK-Sph k (suc j) (dbl (nB k j)) (lt-sK k j)) (lk-Sph-s (nB k j))

lk-face-t : ∀ k j → lookup (BK k (suc j)) (suc (dbl (nB k j))) ≡ just (aL (nB k j))
lk-face-t k j = trans (lk-BK-Sph k (suc j) (suc (dbl (nB k j))) (lt-tK k j)) (lk-Sph-t (nB k j))

mutual
  wK-wf : ∀ k j → BK k j ⊢ty wK k j
  wK-wf k zero =
    arr-wf (var-wf (wBK k 0) (trans (lk-BK-Sph k 0 (dbl k) (<-suc (dbl k) (suc (dbl k)) (n<sn (dbl k))))
                                    (lk-Sph-s k)))
           (var-wf (wBK k 0) (lk-zK k 0))
  wK-wf k (suc j) =
    arr-wf (rwhisk' k j (wK-wf k j) (sideK k j) (ρK-wf k j _ (lk-face-s k j)))
           (subst (BK k (suc j) ⊢tm coh (BK k j) (wK k j) (ρtK k j) ∶_)
                  (sym (faces-BK k j (wK k j) (avoidK k j)))
                  (rwhisk' k j (wK-wf k j) (sideK k j) (ρK-wf k j _ (lk-face-t k j))))

  sideK : ∀ k j → SideK k j
  sideK k zero    = side-BK0 k
  sideK k (suc j) = side-BK k j (Sb.ty-sc closed (wK-wf k j)) (avoidK k j)

  avoidK : ∀ k j → ¬ Mem (dbl (nB k j)) (fvTy (wK k j))
  avoidK k zero    = avoid-BK0 k
  avoidK k (suc j) = avoid-BK k j (Sb.ty-sc closed (wK-wf k j))

-- RIGHT WHISKERING, every k and j: c ▹ₖ h = coh (BK k j) (wK k j) σ is
-- well typed whenever σ is a well-typed substitution into BK k j.
rwhisk : ∀ k j {Γ σ} → Γ ⊢sub σ ∶ BK k j → Γ ⊢tm coh (BK k j) (wK k j) σ ∶ wK k j [ σ ]ty
rwhisk k j = rwhisk' k j (wK-wf k j) (sideK k j)

------------------------------------------------------------------------
-- Left whiskering along k of an n-cell c by a (k+1)-cell h, n = j+k+1,
-- over the pasting context
--
--   LK k j = D^{k+1}          (h at level 2k+2, from x (2k) to y (2k+1)),
--            z : aL k         (level 2k+3),
--            then the cells of c over (y, z): its i-source and
--            i-target at 2i+2, 2i+3 for k < i < n, c at tL k j = 2n+2.
--
-- The whisker h ◃ₖ c is coh (LK k j) (lK k j); for j = 0 the context
-- and the type are those of BK k 0 (composition along k).

tL : Nat → Nat → Nat
tL k j = dbl (suc (nB k j))

bLK : Nat → Nat → Ty
bLK k zero          = aL k
bLK k (suc zero)    = arr (aL k) (var (suc (dbl k))) (var (suc (suc (suc (dbl k)))))
bLK k (suc (suc m)) = arr (bLK k (suc m)) (var (tL k m)) (var (suc (tL k m)))

mutual
  LPK : Nat → Nat → Ctx
  LPK k zero    = Dsk (suc k) ▸ aL k
  LPK k (suc j) = LK k j ▸ bLK k (suc j)

  LK : Nat → Nat → Ctx
  LK k j = LPK k j ▸ bLK k (suc j)

λsK λtK : Nat → Nat → Sub
λsK k j = idS (suc (tL k j))
λtK k j = idS (tL k j) ,ₛ var (suc (tL k j))

lK : Nat → Nat → Ty
lK k zero    = wK k zero
lK k (suc j) = arr (lK k j [ λsK k j ]ty) (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j))

dim-bLK : ∀ k m → dim (bLK k m) ≡ m + k
dim-bLK k zero          = dim-aL k
dim-bLK k (suc zero)    = cong suc (dim-aL k)
dim-bLK k (suc (suc m)) = cong suc (dim-bLK k (suc m))

len-LK : ∀ k j → len (LK k j) ≡ suc (tL k j)
len-LK k zero    = cong (λ n → suc (suc n)) (len-Dsk (suc k))
len-LK k (suc j) = cong (λ n → suc (suc n)) (len-LK k j)

len-LPK : ∀ k j → len (LPK k j) ≡ tL k j
len-LPK k j = cong (λ n → n ∸ 1) (len-LK k j)

-- LK k j is a pasting context.
LK-ps' : ∀ k j → LK k j ⊢ps tL k j ∶ bLK k (suc j)
LK-ps' k zero =
  subst (λ n → (Dsk (suc k) ▸ aL k ▸ arr (aL k) (var (suc (dbl k))) (var n))
                 ⊢ps suc n ∶ arr (aL k) (var (suc (dbl k))) (var n))
        (len-Dsk (suc k)) (pse (psd (dsk-ps (suc k))))
LK-ps' k (suc j) =
  subst (λ n → (LK k j ▸ bLK k (suc j) ▸ arr (bLK k (suc j)) (var (tL k j)) (var n))
                 ⊢ps suc n ∶ arr (bLK k (suc j)) (var (tL k j)) (var n))
        (len-LK k j) (pse (LK-ps' k j))

downLK : ∀ {Γ} k m x → Γ ⊢ps x ∶ bLK k (suc m) → Γ ⊢ps suc (suc (suc (dbl k))) ∶ aL k
downLK k zero    x d = psd d
downLK k (suc m) x d = downLK k m (suc (tL k m)) (psd d)

LK-ps : ∀ k j → LK k j ⊢ps
LK-ps k j = ps (snd (toStar k _ (downLK k j (tL k j) (LK-ps' k j))))

wLK : ∀ k j → LK k j ⊢ctx
wLK k j = ps-ctx (LK-ps k j)

-- Boundaries.
dimCtx-LK : ∀ k m → dimCtx (LK k m) ≡ nB k m
dimCtx-LK k zero    = dimCtx-BK k zero
dimCtx-LK k (suc m) =
  trans (cong₂ max (dim-bLK k (suc (suc m))) (cong₂ max (dim-bLK k (suc m)) (dimCtx-LK k m)))
        (trans (cong (max (suc (suc (m + k)))) (max-le (suc (m + k)) (suc (m + k)) (n<sn (suc (m + k)))))
               (max-le (suc (suc (m + k))) (suc (m + k)) (<-suc (suc (m + k)) (suc (suc (m + k))) (n<sn (suc (m + k))))))

srcLK : ∀ k i m → T (m + k <ℕ i) → srcVars i (LK k m) ≡ upTo (len (LK k m))
srcLK k i zero    p rewrite dim-aL k | ≤→≮ k i p | src-Dsk i k (<-suc k i p) | len-Sph k = refl
srcLK k i (suc m) p rewrite dim-bLK k (suc m) | ≤→≮ (suc (m + k)) i p
                          | srcLK k i m (<-trans (m + k) (suc (m + k)) i (n<sn (m + k)) p) = refl

tgtLK : ∀ k i m → T (m + k <ℕ i) → tgtVars i (LK k m) ≡ upTo (len (LK k m))
tgtLK k i zero    p rewrite dim-aL k | <→≮ k i p | <→≢ k i p | tgt-Dsk i k (<-suc k i p) | len-Sph k = refl
tgtLK k i (suc m) p rewrite dim-bLK k (suc m) | <→≮ (suc (m + k)) i p | <→≢ (suc (m + k)) i p
                          | tgtLK k i m (<-trans (m + k) (suc (m + k)) i (n<sn (m + k)) p) = refl

src-LK : ∀ k j → ∂⁻ (LK k (suc j)) ≡ fvSub (λsK k j)
src-LK k j rewrite dimCtx-LK k (suc j) | dim-bLK k (suc j) | T-≡ (n<sn (j + k))
                 | srcLK k (suc (j + k)) j (n<sn (j + k)) | fv-idS (suc (tL k j)) | len-LPK k j = refl

tgt-LK : ∀ k j → ∂⁺ (LK k (suc j)) ≡ fvSub (λtK k j)
tgt-LK k j rewrite dimCtx-LK k (suc j) | dim-bLK k (suc j) | n≮n (j + k) | T-≡ (==ℕ-refl (j + k))
                 | tgtLK k (suc (j + k)) j (n<sn (j + k)) | len-LPK k j
                 | dropLast-snoc (upTo (tL k j)) (tL k j) | fv-idS (tL k j) = refl

-- The faces differ only at the top cell of LK k j.
lk-λK : ∀ k j w → (w ==ℕ tL k j) ≡ false → lookupₛ (λsK k j) w ≡ lookupₛ (λtK k j) w
lk-λK k j w ne rewrite lenₛ-renS (tL k j) (λ i → i) | ne = refl

faces-LK : ∀ k j A → ¬ Mem (tL k j) (fvTy A) → A [ λsK k j ]ty ≡ A [ λtK k j ]ty
faces-LK k j A av = agree-ty A (λsK k j) (λtK k j) (λ w m → lk-λK k j w (ne w m))
  where
  ne : ∀ w → Mem w (fvTy A) → (w ==ℕ tL k j) ≡ false
  ne w m with w ==ℕ tL k j in e
  ... | true  = ⊥-elim (av (subst (λ x → Mem x (fvTy A)) (==ℕ-sound w _ (≡-T e)) m))
  ... | false = refl

lenλs : ∀ k j → lenₛ (λsK k j) ≡ len (LK k j)
lenλs k j = trans (lenₛ-renS _ (λ i → i)) (sym (len-LK k j))

lenλt : ∀ k j → lenₛ (λtK k j) ≡ len (LK k j)
lenλt k j = trans (cong suc (lenₛ-renS _ (λ i → i))) (sym (len-LK k j))

notIn-λs : ∀ k j → ¬ Mem (tL k (suc j)) (fvSub (λsK k j))
notIn-λs k j m rewrite fv-idS (suc (tL k j)) =
  lt-absurd (tL k (suc j)) (suc (tL k j))
    (mem-upTo (tL k (suc j)) (suc (tL k j)) m)
    (<-suc (suc (tL k j)) (suc (suc (tL k j))) (n<sn (suc (tL k j))))

notIn-λt : ∀ k j → ¬ Mem (tL k (suc j)) (fvSub (λtK k j))
notIn-λt k j m rewrite fv-idS (tL k j) with mem-snoc (tL k (suc j)) (upTo (tL k j)) (suc (tL k j)) m
... | inj₁ q = ss≮ (tL k j) (mem-upTo (tL k (suc j)) (tL k j) q)
... | inj₂ e = n≢sn (suc (tL k j)) (sym e)

lt4 : ∀ d → T (d <ℕ suc (suc (suc (suc d))))
lt4 zero    = tt
lt4 (suc d) = lt4 d

lt5 : ∀ d → T (d <ℕ suc (suc (suc (suc (suc d)))))
lt5 zero    = tt
lt5 (suc d) = lt5 d

avoid-LK0 : ∀ k → ¬ Mem (tL k 0) (fvTy (lK k 0))
avoid-LK0 k m rewrite fvTy-aL k with mem++ D (upTo (dbl k)) (dbl k ∷ zK k 0 ∷ []) m
  where D = tL k 0
... | inj₁ q = lt-absurd (tL k 0) (dbl k) (mem-upTo (tL k 0) (dbl k) q) (lt5 (dbl k))
... | inj₂ q with mem++ (tL k 0) (dbl k ∷ []) (zK k 0 ∷ []) q
...   | inj₁ r = <-irr' (dbl k) (subst (λ x → T (dbl k <ℕ x)) (mem-one (tL k 0) (dbl k) r) (lt4 (dbl k)))
...   | inj₂ r = n≢sn (zK k 0) (sym (mem-one (tL k 0) (zK k 0) r))

avoid-LK : ∀ k j → ScTy (len (LK k j)) (lK k j) → ¬ Mem (tL k (suc j)) (fvTy (lK k (suc j)))
avoid-LK k j sc m with mem++ D (fvTy (lK k j [ λsK k j ]ty)) (fvSub (λsK k j) ++ fvSub (λtK k j)) m
  where D = tL k (suc j)
... | inj₁ r = notIn-λs k j (fv-ty[] (lK k j) (λsK k j) (subst (λ n → ScTy n (lK k j)) (sym (lenλs k j)) sc) _ r)
... | inj₂ r with mem++ (tL k (suc j)) (fvSub (λsK k j)) (fvSub (λtK k j)) r
...   | inj₁ s = notIn-λs k j s
...   | inj₂ s = notIn-λt k j s

side-LK : ∀ k j → ScTy (len (LK k j)) (lK k j) → ¬ Mem (tL k j) (fvTy (lK k j)) →
          T (cattSide (LK k (suc j)) (lK k j [ λsK k j ]ty)
                      (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j)))
side-LK k j sc av = ∨-r
  (∧-in (subst (λ L → T (≈? (fvSub (λsK k j) ++ fvTy A) L)) (sym (src-LK k j))
          (≈-absorb (fvSub (λsK k j)) (fvTy A)
            (fv-ty[] (lK k j) (λsK k j) (subst (λ n → ScTy n (lK k j)) (sym (lenλs k j)) sc))))
        (subst (λ L → T (≈? (fvSub (λtK k j) ++ fvTy A) L)) (sym (tgt-LK k j))
          (≈-absorb (fvSub (λtK k j)) (fvTy A)
            (subst (λ X → fvTy X ⊆ fvSub (λtK k j)) (sym (faces-LK k j (lK k j) av))
              (fv-ty[] (lK k j) (λtK k j) (subst (λ n → ScTy n (lK k j)) (sym (lenλt k j)) sc))))))
  where A = lK k j [ λsK k j ]ty

-- The faces are well typed.
λsK-wf : ∀ k j → LK k (suc j) ⊢sub λsK k j ∶ LK k j
λsK-wf k j =
  subst (λ n → LK k (suc j) ⊢sub idS n ∶ LK k j) (len-LK k j)
        (wk-sub (wk-sub (id-wf (wLK k j)) (ctx-init w)) w)
  where w = wLK k (suc j)

lk-λt : ∀ k j → lookup (LK k (suc j)) (suc (tL k j)) ≡ just (bLK k (suc j))
lk-λt k j = subst (λ i → lookup (LK k (suc j)) i ≡ just (bLK k (suc j))) (len-LK k j)
              (trans (lk-skip (LK k j ▸ bLK k (suc j)) (bLK k (suc (suc j))) (len (LK k j)) (n<sn (len (LK k j))))
                     (last-lookup (LK k j) (bLK k (suc j))))

λtK-wf : ∀ k j → LK k (suc j) ⊢sub λtK k j ∶ LK k j
λtK-wf k j =
  ,-wf (subst (λ n → LK k (suc j) ⊢sub idS n ∶ LPK k j) (len-LPK k j)
              (wk-sub (wk-sub (wk-sub (id-wf (ctx-init (wLK k j))) (ctx-init (ctx-init w))) (ctx-init w)) w))
       (subst (LK k (suc j) ⊢tm var (suc (tL k j)) ∶_)
              (sym (id-ty (tL k j) (bLK k (suc j))
                     (subst (λ n → ScTy n (bLK k (suc j))) (len-LPK k j) (Sb.ty-sc closed (ctx-last (wLK k j))))))
              (var-wf w (lk-λt k j)))
  where w = wLK k (suc j)

-- The left whisker coherences are well typed, for every k and j.
SideLK : Nat → Nat → Set
SideLK k zero    = SideK k zero
SideLK k (suc j) = T (cattSide (LK k (suc j)) (lK k j [ λsK k j ]ty)
                        (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j)))

lwhisk' : ∀ k j {Γ σ} → LK k j ⊢ty lK k j → SideLK k j → Γ ⊢sub σ ∶ LK k j →
          Γ ⊢tm coh (LK k j) (lK k j) σ ∶ lK k j [ σ ]ty
lwhisk' k zero    a s d = coh-wf (LK-ps k zero)    (wLK k zero)    a s d
lwhisk' k (suc j) a s d = coh-wf (LK-ps k (suc j)) (wLK k (suc j)) a s d

mutual
  lK-wf : ∀ k j → LK k j ⊢ty lK k j
  lK-wf k zero    = wK-wf k zero
  lK-wf k (suc j) =
    arr-wf (lwhisk' k j (lK-wf k j) (sideLK k j) (λsK-wf k j))
           (subst (LK k (suc j) ⊢tm coh (LK k j) (lK k j) (λtK k j) ∶_)
                  (sym (faces-LK k j (lK k j) (avoidLK k j)))
                  (lwhisk' k j (lK-wf k j) (sideLK k j) (λtK-wf k j)))

  sideLK : ∀ k j → SideLK k j
  sideLK k zero    = side-BK0 k
  sideLK k (suc j) = side-LK k j (Sb.ty-sc closed (lK-wf k j)) (avoidLK k j)

  avoidLK : ∀ k j → ¬ Mem (tL k j) (fvTy (lK k j))
  avoidLK k zero    = avoid-LK0 k
  avoidLK k (suc j) = avoid-LK k j (Sb.ty-sc closed (lK-wf k j))

-- LEFT WHISKERING, every k and j: h ◃ₖ c = coh (LK k j) (lK k j) σ is
-- well typed whenever σ is a well-typed substitution into LK k j.
lwhisk : ∀ k j {Γ σ} → Γ ⊢sub σ ∶ LK k j → Γ ⊢tm coh (LK k j) (lK k j) σ ∶ lK k j [ σ ]ty
lwhisk k j = lwhisk' k j (lK-wf k j) (sideLK k j)

-- COMPOSITION of two (k+1)-cells along k, every k: the case j = 0.
comp : ∀ k {Γ σ} → Γ ⊢sub σ ∶ BK k 0 → Γ ⊢tm coh (BK k 0) (wK k 0) σ ∶ wK k 0 [ σ ]ty
comp k = rwhisk k 0
