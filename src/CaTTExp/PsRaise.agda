------------------------------------------------------------------------
-- Raised pasting trees (ledger S20 (i) stage 3b and S20 (ii) step 4).
--
-- GrayCtx.Lift.raiseT bs τ raises the leaves of τ flagged by bs (in
-- leaf order) by one dimension: a flagged leaf f : x → y becomes
-- f, f′ : x → y and α : f → f′. Over T^ = raiseT bs τ there are two
-- inclusions of τ:
--
--   incl⁻ sends every variable of τ to its copy (f ↦ f),
--   incl⁺ is the same except that a raised leaf goes to f′,
--
-- This module proves, for every tree τ = node (t ∷ ts) and every flag
-- list bs, that both are typed substitutions
--
--   ctxOf (raiseT bs τ) ⊢sub incl∓ ∶ ctxOf τ          (`incl-wf`)
--
-- by simulating the two runs of the pasting-context builder side by
-- side (`simL`). ⊢ps of the raised tree is `psOf` itself.
--
-- When τ has dimension ≤ k, every flagged leaf has dimension k
-- (`TopOK k 0`) and some leaf is flagged (`anyR`), the raised context
-- has dimension k + 1 (`dim-raise`) and its boundaries are the images
-- of all of τ:
--
--   ∂⁻ (ctxOf (raiseT bs τ)) ≡ img incl⁻ (upTo (len (ctxOf τ)))   (`src-raise`)
--   ∂⁺ (ctxOf (raiseT bs τ)) ≡ img incl⁺ (upTo (len (ctxOf τ)))   (`tgt-raise`)
--
-- The hypotheses are needed: a flagged leaf below the top dimension
-- leaves the raised context's boundary at a dimension where τ's own
-- cells are not all kept.
------------------------------------------------------------------------
module CaTTExp.PsRaise where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Weakening ∅ cattSide using (wk-sub; lookup-top; lookup-wk)
open import CaTTExp.Derived using (ps-wf; ctx-init; lk-ext; lk-top; dropLast-snoc; upTo)
open import CaTTExp.GrayCtx.Lift using (raiseL; raiseT)

private
  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  <-self : ∀ n → T (n <ℕ suc n)
  <-self zero    = tt
  <-self (suc n) = <-self n

  arr-inj : ∀ {A A′ s s′ t t′} → arr A s t ≡ arr A′ s′ t′ → (A ≡ A′) × (s ≡ s′) × (t ≡ t′)
  arr-inj refl = refl , refl , refl

  arr≡ : ∀ {A A′ s s′ t t′} → A ≡ A′ → s ≡ s′ → t ≡ t′ → arr A s t ≡ arr A′ s′ t′
  arr≡ refl refl refl = refl

------------------------------------------------------------------------
-- One half of the simulation: a substitution σ sending the current
-- state (Γ, x : A) of the original run to the state (Δ, x^ : A^) of the
-- raised run.

record Half (σ : Sub) (Γ : Ctx) (x : Nat) (A : Ty) (Δ : Ctx) (x^ : Nat) (A^ : Ty) : Set where
  constructor half
  field
    wσ : Δ ⊢sub σ ∶ Γ
    pt : lookupₛ σ x ≡ var x^
    ty : A [ σ ]ty ≡ A^
open Half

-- Weakening the raised side.
halfW : ∀ {σ Γ x A Δ x^ A^ C} → Half σ Γ x A Δ x^ A^ → (Δ ▸ C) ⊢ctx → Half σ Γ x A (Δ ▸ C) x^ A^
halfW h w = half (wk-sub (wσ h) w) (pt h) (ty h)

-- A pse step of the original run, matched by the cells yv : A^ and
-- fv : x^ → yv of Δ.
halfE : ∀ {σ Γ x A Δ x^ A^} → Γ ⊢ps x ∶ A → Half σ Γ x A Δ x^ A^ → Δ ⊢ctx →
        ∀ yv fv → lookup Δ yv ≡ just A^ → lookup Δ fv ≡ just (arr A^ (var x^) (var yv)) →
        Half (σ ,ₛ var yv ,ₛ var fv) (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (suc (len Γ))
             (arr A (var x) (var (len Γ))) Δ fv (arr A^ (var x^) (var yv))
halfE {σ} {Γ} {x} {A} {Δ} {x^} {A^} d h wΔ yv fv ly lf =
  half (,-wf (,-wf (wσ h) (var-wf wΔ (trans ly (cong just (sym (ty h))))))
             (var-wf wΔ (trans lf (cong just (sym eF)))))
       (subst (λ n → lookupₛ (σ ,ₛ var yv ,ₛ var fv) n ≡ var fv) (cong suc l) (lk-top (σ ,ₛ var yv) (var fv)))
       (trans (Sb.ext-ty (arr A (var x) (var (len Γ))) (σ ,ₛ var yv) (var fv)
                 (subst (λ n → Sb.ScTy n (arr A (var x) (var (len Γ)))) (sym (cong suc l)) scF))
              eF)
  where
  l : lenₛ σ ≡ len Γ
  l = snd (Sb.sub-sc closed (wσ h))
  dx = snd (ps-wf d)
  scA : Sb.ScTy (len Γ) A
  scA = Sb.tm-ty-sc closed dx
  x< : T (x <ℕ len Γ)
  x< = Sb.tm-sc closed dx
  scF : Sb.ScTy (suc (len Γ)) (arr A (var x) (var (len Γ)))
  scF = Sb.scTy-suc A scA , <-suc x (len Γ) x< , <-self (len Γ)
  e1 : A [ σ ,ₛ var yv ]ty ≡ A^
  e1 = trans (Sb.ext-ty A σ (var yv) (subst (λ n → Sb.ScTy n A) (sym l) scA)) (ty h)
  eF : arr A (var x) (var (len Γ)) [ σ ,ₛ var yv ]ty ≡ arr A^ (var x^) (var yv)
  eF = arr≡ e1
         (trans (lk-ext σ (var yv) x (subst (λ n → T (x <ℕ n)) (sym l) x<)) (pt h))
         (subst (λ n → lookupₛ (σ ,ₛ var yv) n ≡ var yv) l (lk-top σ (var yv)))

-- A psd step: from f : x → y to y.
halfD : ∀ {σ Γ f A x y Δ f^ A^ x^ y^} →
        Half σ Γ f (arr A (var x) (var y)) Δ f^ (arr A^ (var x^) (var y^)) → Half σ Γ y A Δ y^ A^
halfD h = let e = arr-inj (ty h) in half (wσ h) (snd (snd e)) (fst e)

------------------------------------------------------------------------
-- The simulation: both inclusions.

Sim : Ctx → Nat → Ty → Ctx → Nat → Ty → Set
Sim Γ x A Δ x^ A^ = Σ Sub λ rm → Σ Sub λ rp → Half rm Γ x A Δ x^ A^ × Half rp Γ x A Δ x^ A^

private
  -- The two contexts after a pse.
  ctx1 : ∀ {Γ x A} → Γ ⊢ps x ∶ A → (Γ ▸ A ▸ arr A (var x) (var (len Γ))) ⊢ctx
  ctx1 d = fst (ps-wf (pse d))

  lk-y : ∀ Γ A B → lookup (Γ ▸ A ▸ B) (len Γ) ≡ just A
  lk-y Γ A B = lookup-wk (Γ ▸ A) (len Γ) B (lookup-top Γ A)

pseS : ∀ {Γ x A Δ x^ A^} → Γ ⊢ps x ∶ A → Δ ⊢ps x^ ∶ A^ → Sim Γ x A Δ x^ A^ →
       Sim (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (suc (len Γ)) (arr A (var x) (var (len Γ)))
           (Δ ▸ A^ ▸ arr A^ (var x^) (var (len Δ))) (suc (len Δ)) (arr A^ (var x^) (var (len Δ)))
pseS {Γ} {x} {A} {Δ} {x^} {A^} d d^ (rm , rp , hm , hp) =
  _ , _ , go hm , go hp
  where
  w₂ = ctx1 d^
  w₁ = ctx-init w₂
  go : ∀ {σ} → Half σ Γ x A Δ x^ A^ → _
  go h = halfE d (halfW (halfW h w₁) w₂) w₂ (len Δ) (suc (len Δ))
           (lk-y Δ A^ (arr A^ (var x^) (var (len Δ)))) (lookup-top (Δ ▸ A^) (arr A^ (var x^) (var (len Δ))))

psdS : ∀ {Γ f A x y Δ f^ A^ x^ y^} →
       Sim Γ f (arr A (var x) (var y)) Δ f^ (arr A^ (var x^) (var y^)) → Sim Γ y A Δ y^ A^
psdS (rm , rp , hm , hp) = rm , rp , halfD hm , halfD hp

-- A flagged leaf: the original run does pse; psd, the raised run does
-- pse; pse; psd; psd, and incl⁺ sends the leaf f to the new copy f′.
Raised : Ctx → Nat → Ty → Ctx
Raised Δ x^ A^ = Δ ▸ A^ ▸ F ▸ F ▸ arr F (var (suc (len Δ))) (var (suc (suc (len Δ))))
  where F = arr A^ (var x^) (var (len Δ))

leafR : ∀ {Γ x A Δ x^ A^} → (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) → Sim Γ x A Δ x^ A^ →
        Sim (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (len Γ) A (Raised Δ x^ A^) (len Δ) A^
leafR {Γ} {x} {A} {Δ} {x^} {A^} d d^ (rm , rp , hm , hp) =
  _ , _ , halfD (halfE d (wk4 hm) w₄ (len Δ) (suc (len Δ)) ly lf₁)
        , halfD (halfE d (wk4 hp) w₄ (len Δ) (suc (suc (len Δ))) ly lf₂)
  where
  F  = arr A^ (var x^) (var (len Δ))
  Δ₁ = Δ ▸ A^ ▸ F
  G  = arr F (var (suc (len Δ))) (var (len Δ₁))
  Δ₂ = Δ₁ ▸ F ▸ G
  w₄ : Δ₂ ⊢ctx
  w₄ = fst (ps-wf (pse (pse d^)))
  w₃ = ctx-init w₄
  w₂ = ctx-init w₃
  w₁ = ctx-init w₂
  wk4 : ∀ {σ} → Half σ Γ x A Δ x^ A^ → Half σ Γ x A Δ₂ x^ A^
  wk4 h = halfW (halfW (halfW (halfW h w₁) w₂) w₃) w₄
  ly : lookup Δ₂ (len Δ) ≡ just A^
  ly = lookup-wk (Δ₁ ▸ F) (len Δ) G (lookup-wk Δ₁ (len Δ) F (lk-y Δ A^ F))
  lf₁ : lookup Δ₂ (suc (len Δ)) ≡ just F
  lf₁ = lookup-wk (Δ₁ ▸ F) (suc (len Δ)) G (lookup-wk Δ₁ (suc (len Δ)) F (lookup-top (Δ ▸ A^) F))
  lf₂ : lookup Δ₂ (suc (suc (len Δ))) ≡ just F
  lf₂ = lk-y Δ₁ F G

------------------------------------------------------------------------
-- The two runs of the builder, side by side.

BRes : Ty → Set
BRes A = Σ Ctx (λ Γ′ → Σ Nat (λ x′ → Γ′ ⊢ps x′ ∶ A))

SimR : ∀ {A A^} → BRes A → BRes A^ → Set
SimR {A} {A^} r r^ = Sim (fst r) (fst (snd r)) A (fst r^) (fst (snd r^)) A^

private
  leafP : ∀ {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) → Sim Γ x A Δ x^ A^ →
          Sim (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (len Γ) A (Δ ▸ A^ ▸ arr A^ (var x^) (var (len Δ))) (len Δ) A^
  leafP d d^ S = psdS (pseS d d^ S)

mutual
  simL : ∀ ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) → Sim Γ x A Δ x^ A^ →
         SimR (buildList ts d) (buildList (fst (raiseL bs ts)) d^)
  simL []                  bs        d d^ S = S
  simL (node [] ∷ ts)      []        d d^ S = simL ts [] (psd (pse d)) (psd (pse d^)) (leafP d d^ S)
  simL (node [] ∷ ts)      (true ∷ bs)  d d^ S = simL ts bs (psd (pse d)) (psd (psd (pse (pse d^)))) (leafR d d^ S)
  simL (node [] ∷ ts)      (false ∷ bs) d d^ S = simL ts bs (psd (pse d)) (psd (pse d^)) (leafP d d^ S)
  simL (node (c ∷ cs) ∷ ts) []        d d^ S = simN (c ∷ cs) ts [] d d^ S
  simL (node (c ∷ cs) ∷ ts) (b ∷ bs) d d^ S = simN (c ∷ cs) ts (b ∷ bs) d d^ S

  -- A child with children of its own.
  simN : ∀ cs ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) → Sim Γ x A Δ x^ A^ →
         SimR (buildList ts (psd (snd (snd (buildList cs (pse d))))))
              (buildList (fst (raiseL (snd (raiseL bs cs)) ts)) (psd (snd (snd (buildList (fst (raiseL bs cs)) (pse d^))))))
  simN cs ts bs d d^ S =
    simL ts (snd (raiseL bs cs)) _ _ (psdS (simL cs bs (pse d) (pse d^) (pseS d d^ S)))

------------------------------------------------------------------------
-- The inclusions.

private
  base : Sim (ε ▸ ⋆) 0 ⋆ (ε ▸ ⋆) 0 ⋆
  base = s , s , h , h
    where
    s = ⟨⟩ ,ₛ var 0
    w = fst (ps-wf pss)
    h = half (,-wf (⟨⟩-wf w) (var-wf w refl)) refl refl

-- For a tree with at least one child: both inclusions, typed.
InclT : List Bool → Tree → List Tree → Set
InclT bs t ts = Σ Nat λ x → Σ Nat λ x^ → Sim (ctxOf (node (t ∷ ts))) x ⋆ (ctxOf (raiseT bs (node (t ∷ ts)))) x^ ⋆

incl : ∀ bs t ts → InclT bs t ts
incl []       t ts = _ , _ , simL (t ∷ ts) [] pss pss base
incl (b ∷ bs) t ts = _ , _ , simL (t ∷ ts) (b ∷ bs) pss pss base

inclM inclP : ∀ bs t ts → Sub
inclM bs t ts = fst (snd (snd (incl bs t ts)))
inclP bs t ts = fst (snd (snd (snd (incl bs t ts))))

inclM-wf : ∀ bs t ts → ctxOf (raiseT bs (node (t ∷ ts))) ⊢sub inclM bs t ts ∶ ctxOf (node (t ∷ ts))
inclM-wf bs t ts = wσ (fst (snd (snd (snd (snd (incl bs t ts))))))

inclP-wf : ∀ bs t ts → ctxOf (raiseT bs (node (t ∷ ts))) ⊢sub inclP bs t ts ∶ ctxOf (node (t ∷ ts))
inclP-wf bs t ts = wσ (snd (snd (snd (snd (snd (incl bs t ts))))))

------------------------------------------------------------------------
-- Boundaries. Fix k. If every flagged leaf has dimension k (its
-- parent's type has dimension k − 1; `TopOK`), then along the two runs
--
--   srcVars k (raised) ≡ incl⁻ applied to srcVars k (original),
--   tgtVars k (raised) ≡ incl⁺ applied to tgtVars k (original),
--
-- as lists of levels (`srcL`, `tgtL`). With k the dimension of τ these
-- are ∂⁻ and ∂⁺ of the raised tree.

lev : Tm → Nat
lev (var i) = i
lev _       = 0

img : Sub → List Nat → List Nat
img σ []       = []
img σ (i ∷ is) = lev (lookupₛ σ i) ∷ img σ is

AllLt : Nat → List Nat → Set
AllLt n []       = ⊤
AllLt n (i ∷ is) = T (i <ℕ n) × AllLt n is

private
  img-++ : ∀ σ xs ys → img σ (xs ++ ys) ≡ img σ xs ++ img σ ys
  img-++ σ []       ys = refl
  img-++ σ (x ∷ xs) ys = cong (_ ∷_) (img-++ σ xs ys)

  img-snoc : ∀ σ xs y → img σ (snoc xs y) ≡ snoc (img σ xs) (lev (lookupₛ σ y))
  img-snoc σ xs y = img-++ σ xs (y ∷ [])

  img-dropLast : ∀ σ xs → img σ (dropLastᴸ xs) ≡ dropLastᴸ (img σ xs)
  img-dropLast σ []           = refl
  img-dropLast σ (x ∷ [])     = refl
  img-dropLast σ (x ∷ y ∷ xs) = cong (_ ∷_) (img-dropLast σ (y ∷ xs))

  allLt-suc : ∀ n xs → AllLt n xs → AllLt (suc n) xs
  allLt-suc n []       _       = tt
  allLt-suc n (x ∷ xs) (p , a) = <-suc x n p , allLt-suc n xs a

  allLt-++ : ∀ n xs ys → AllLt n xs → AllLt n ys → AllLt n (xs ++ ys)
  allLt-++ n []       ys _       b = b
  allLt-++ n (x ∷ xs) ys (p , a) b = p , allLt-++ n xs ys a b

  allLt-dropLast : ∀ n xs → AllLt n xs → AllLt n (dropLastᴸ xs)
  allLt-dropLast n []           _       = tt
  allLt-dropLast n (x ∷ [])     _       = tt
  allLt-dropLast n (x ∷ y ∷ xs) (p , a) = p , allLt-dropLast n (y ∷ xs) a

  allLt-ss : ∀ n xs → AllLt n xs → AllLt (suc (suc n)) (snoc (snoc xs n) (suc n))
  allLt-ss n xs a = allLt-++ _ (snoc xs n) _ (allLt-++ _ xs _ (allLt-suc _ xs (allLt-suc _ xs a)) (<-suc n (suc n) (<-self n) , tt))
                      (<-self (suc n) , tt)

  allLt-ds : ∀ n xs → AllLt n xs → AllLt (suc (suc n)) (snoc (dropLastᴸ xs) n)
  allLt-ds n xs a = allLt-++ _ (dropLastᴸ xs) _ (allLt-suc _ _ (allLt-suc _ _ (allLt-dropLast n xs a))) (<-suc n (suc n) (<-self n) , tt)

  img-ext2 : ∀ σ a b xs → AllLt (lenₛ σ) xs → img (σ ,ₛ a ,ₛ b) xs ≡ img σ xs
  img-ext2 σ a b []       _       = refl
  img-ext2 σ a b (x ∷ xs) (p , q) =
    cong₂ _∷_ (cong lev (trans (lk-ext (σ ,ₛ a) b x (<-suc x (lenₛ σ) p)) (lk-ext σ a x p))) (img-ext2 σ a b xs q)

-- Levels in a boundary are in range.
src-lt : ∀ k Γ → AllLt (len Γ) (srcVars k Γ)
src-lt k ε               = tt
src-lt k (ε ▸ _)         = tt , tt
src-lt k (Γ ▸ A ▸ B) with k <ℕ suc (dim A)
... | true  = allLt-suc _ _ (allLt-suc _ _ (src-lt k Γ))
... | false = allLt-ss (len Γ) (srcVars k Γ) (src-lt k Γ)

tgt-lt : ∀ k Γ → AllLt (len Γ) (tgtVars k Γ)
tgt-lt k ε               = tt
tgt-lt k (ε ▸ _)         = tt , tt
tgt-lt k (Γ ▸ A ▸ B) with k <ℕ dim A
... | true  = allLt-suc _ _ (allLt-suc _ _ (tgt-lt k Γ))
... | false with dim A ==ℕ k
...   | true  = allLt-ds (len Γ) (tgtVars k Γ) (tgt-lt k Γ)
...   | false = allLt-ss (len Γ) (tgtVars k Γ) (tgt-lt k Γ)

private
  lk2-y : ∀ σ a b → lookupₛ (σ ,ₛ a ,ₛ b) (lenₛ σ) ≡ a
  lk2-y σ a b = trans (lk-ext (σ ,ₛ a) b (lenₛ σ) (<-self (lenₛ σ))) (lk-top σ a)

  lk2-f : ∀ σ a b → lookupₛ (σ ,ₛ a ,ₛ b) (suc (lenₛ σ)) ≡ b
  lk2-f σ a b = lk-top (σ ,ₛ a) b

  -- img through a pse-extended substitution, at the two new levels.
  img-ss : ∀ σ L n yv fv → lenₛ σ ≡ n → AllLt n L →
           img (σ ,ₛ var yv ,ₛ var fv) (snoc (snoc L n) (suc n)) ≡ snoc (snoc (img σ L) yv) fv
  img-ss σ L n yv fv refl a
    rewrite img-snoc (σ ,ₛ var yv ,ₛ var fv) (snoc L (lenₛ σ)) (suc (lenₛ σ))
          | img-snoc (σ ,ₛ var yv ,ₛ var fv) L (lenₛ σ)
          | lk2-y σ (var yv) (var fv) | lk2-f σ (var yv) (var fv)
          | img-ext2 σ (var yv) (var fv) L a = refl

  img-ds : ∀ σ L n yv fv → lenₛ σ ≡ n → AllLt n L →
           img (σ ,ₛ var yv ,ₛ var fv) (snoc (dropLastᴸ L) n) ≡ snoc (dropLastᴸ (img σ L)) yv
  img-ds σ L n yv fv refl a
    rewrite img-snoc (σ ,ₛ var yv ,ₛ var fv) (dropLastᴸ L) (lenₛ σ)
          | lk2-y σ (var yv) (var fv)
          | img-ext2 σ (var yv) (var fv) (dropLastᴸ L) (allLt-dropLast _ L a)
          | img-dropLast σ L = refl

-- A plain pse step preserves both equations.
srcE : ∀ k Γ A B Δ A^ B^ σ → dim A^ ≡ dim A → lenₛ σ ≡ len Γ → srcVars k Δ ≡ img σ (srcVars k Γ) →
       srcVars k (Δ ▸ A^ ▸ B^) ≡ img (σ ,ₛ var (len Δ) ,ₛ var (suc (len Δ))) (srcVars k (Γ ▸ A ▸ B))
srcE k Γ A B Δ A^ B^ σ dA l e =
  trans (cong (λ m → if k <ℕ suc m then SΔ else snoc (snoc SΔ (len Δ)) (suc (len Δ))) dA) (go (k <ℕ suc (dim A)))
  where
  SΔ = srcVars k Δ
  SΓ = srcVars k Γ
  σ′ = σ ,ₛ var (len Δ) ,ₛ var (suc (len Δ))
  go : ∀ b → (if b then SΔ else snoc (snoc SΔ (len Δ)) (suc (len Δ)))
             ≡ img σ′ (if b then SΓ else snoc (snoc SΓ (len Γ)) (suc (len Γ)))
  go true  = trans e (sym (img-ext2 σ _ _ SΓ (subst (λ n → AllLt n SΓ) (sym l) (src-lt k Γ))))
  go false = trans (cong (λ L → snoc (snoc L (len Δ)) (suc (len Δ))) e) (sym (img-ss σ SΓ (len Γ) _ _ l (src-lt k Γ)))

tgtE : ∀ k Γ A B Δ A^ B^ σ → dim A^ ≡ dim A → lenₛ σ ≡ len Γ → tgtVars k Δ ≡ img σ (tgtVars k Γ) →
       tgtVars k (Δ ▸ A^ ▸ B^) ≡ img (σ ,ₛ var (len Δ) ,ₛ var (suc (len Δ))) (tgtVars k (Γ ▸ A ▸ B))
tgtE k Γ A B Δ A^ B^ σ dA l e =
  trans (cong (λ m → if k <ℕ m then TΔ else if m ==ℕ k then snoc (dropLastᴸ TΔ) (len Δ) else snoc (snoc TΔ (len Δ)) (suc (len Δ))) dA)
        (go (k <ℕ dim A) (dim A ==ℕ k))
  where
  TΔ = tgtVars k Δ
  TΓ = tgtVars k Γ
  σ′ = σ ,ₛ var (len Δ) ,ₛ var (suc (len Δ))
  aΓ = tgt-lt k Γ
  go : ∀ b c → (if b then TΔ else if c then snoc (dropLastᴸ TΔ) (len Δ) else snoc (snoc TΔ (len Δ)) (suc (len Δ)))
               ≡ img σ′ (if b then TΓ else if c then snoc (dropLastᴸ TΓ) (len Γ) else snoc (snoc TΓ (len Γ)) (suc (len Γ)))
  go true  c     = trans e (sym (img-ext2 σ _ _ TΓ (subst (λ n → AllLt n TΓ) (sym l) aΓ)))
  go false true  = trans (cong (λ L → snoc (dropLastᴸ L) (len Δ)) e) (sym (img-ds σ TΓ (len Γ) _ _ l aΓ))
  go false false = trans (cong (λ L → snoc (snoc L (len Δ)) (suc (len Δ))) e) (sym (img-ss σ TΓ (len Γ) _ _ l aΓ))

private
  sa<a : ∀ a → (suc a <ℕ a) ≡ false
  sa<a zero    = refl
  sa<a (suc a) = sa<a a

  a=sa : ∀ a → (a ==ℕ suc a) ≡ false
  a=sa zero    = refl
  a=sa (suc a) = a=sa a

  n<sn : ∀ n → (n <ℕ suc n) ≡ true
  n<sn zero    = refl
  n<sn (suc n) = n<sn n

  n<n : ∀ n → (n <ℕ n) ≡ false
  n<n zero    = refl
  n<n (suc n) = n<n n

  n=n : ∀ n → (n ==ℕ n) ≡ true
  n=n zero    = refl
  n=n (suc n) = n=n n

-- A raised leaf (its parent's type A has dimension k − 1).
srcR : ∀ Γ A B Δ x^ A^ σ → dim A^ ≡ dim A → lenₛ σ ≡ len Γ → srcVars (suc (dim A)) Δ ≡ img σ (srcVars (suc (dim A)) Γ) →
       srcVars (suc (dim A)) (Raised Δ x^ A^) ≡ img (σ ,ₛ var (len Δ) ,ₛ var (suc (len Δ))) (srcVars (suc (dim A)) (Γ ▸ A ▸ B))
srcR Γ A B Δ x^ A^ σ dA l e =
  trans (cong (λ m → if k <ℕ suc (suc m) then S₁ else snoc (snoc S₁ (len Δ₁)) (suc (len Δ₁))) dA)
    (trans (cong (λ b → if b then S₁ else snoc (snoc S₁ (len Δ₁)) (suc (len Δ₁))) (n<sn k))
      (srcE k Γ A B Δ A^ F σ dA l e))
  where
  k  = suc (dim A)
  F  = arr A^ (var x^) (var (len Δ))
  Δ₁ = Δ ▸ A^ ▸ F
  S₁ = srcVars k Δ₁

tgtR : ∀ Γ A B Δ x^ A^ σ → dim A^ ≡ dim A → lenₛ σ ≡ len Γ → tgtVars (suc (dim A)) Δ ≡ img σ (tgtVars (suc (dim A)) Γ) →
       tgtVars (suc (dim A)) (Raised Δ x^ A^) ≡ img (σ ,ₛ var (len Δ) ,ₛ var (suc (suc (len Δ)))) (tgtVars (suc (dim A)) (Γ ▸ A ▸ B))
tgtR Γ A B Δ x^ A^ σ dA l e
  rewrite dA | sa<a (dim A) | n<n (suc (dim A)) | n=n (suc (dim A)) | a=sa (dim A)
        | dropLast-snoc (snoc (tgtVars (suc (dim A)) Δ) (len Δ)) (suc (len Δ)) | e =
  sym (img-ss σ (tgtVars (suc (dim A)) Γ) (len Γ) (len Δ) (suc (suc (len Δ))) l (tgt-lt _ Γ))

-- Every flagged leaf has dimension k: its parent's type has dimension
-- k − 1. m is the dimension of the current parent's type.
TopOK : Nat → Nat → List Tree → List Bool → Set
TopOK k m []                   bs           = ⊤
TopOK k m (node [] ∷ ts)       []           = TopOK k m ts []
TopOK k m (node [] ∷ ts)       (true ∷ bs)  = (suc m ≡ k) × TopOK k m ts bs
TopOK k m (node [] ∷ ts)       (false ∷ bs) = TopOK k m ts bs
TopOK k m (node (c ∷ cs) ∷ ts) []           = TopOK k (suc m) (c ∷ cs) [] × TopOK k m ts (snd (raiseL [] (c ∷ cs)))
TopOK k m (node (c ∷ cs) ∷ ts) (b ∷ bs)     = TopOK k (suc m) (c ∷ cs) (b ∷ bs) × TopOK k m ts (snd (raiseL (b ∷ bs) (c ∷ cs)))

private
  dimS : ∀ {Γ x A Δ x^ A^} (S : Sim Γ x A Δ x^ A^) → dim A^ ≡ dim A
  dimS {A = A} (rm , _ , hm , _) = trans (cong dim (sym (ty hm))) (dim[] A rm)
    where open import CaTTExp.DerivedBoundary using (dim[])

  lenM : ∀ {Γ x A Δ x^ A^} (S : Sim Γ x A Δ x^ A^) → lenₛ (fst S) ≡ len Γ
  lenM (_ , _ , hm , _) = snd (Sb.sub-sc closed (wσ hm))

  lenP : ∀ {Γ x A Δ x^ A^} (S : Sim Γ x A Δ x^ A^) → lenₛ (fst (snd S)) ≡ len Γ
  lenP (_ , _ , _ , hp) = snd (Sb.sub-sc closed (wσ hp))

mutual
  srcL : ∀ k ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (dim A) ts bs → srcVars k Δ ≡ img (fst S) (srcVars k Γ) →
         srcVars k (fst (buildList (fst (raiseL bs ts)) d^)) ≡ img (fst (simL ts bs d d^ S)) (srcVars k (fst (buildList ts d)))
  srcL k []                  bs           d d^ S _ e = e
  srcL k (node [] ∷ ts)      []           {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top e =
    srcL k ts [] (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (srcE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst S) (dimS S) (lenM S) e)
  srcL k (node [] ∷ ts)      (false ∷ bs) {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top e =
    srcL k ts bs (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (srcE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst S) (dimS S) (lenM S) e)
  srcL .(suc (dim A)) (node [] ∷ ts) (true ∷ bs) {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (refl , top) e =
    srcL _ ts bs (psd (pse d)) (psd (psd (pse (pse d^)))) (leafR d d^ S) top (srcR Γ A (arr A (var x) (var (len Γ))) Δ x^ A^ (fst S) (dimS S) (lenM S) e)
  srcL k (node (c ∷ cs) ∷ ts) []       d d^ S top e = srcN k (c ∷ cs) ts [] d d^ S top e
  srcL k (node (c ∷ cs) ∷ ts) (b ∷ bs) d d^ S top e = srcN k (c ∷ cs) ts (b ∷ bs) d d^ S top e

  srcN : ∀ k cs ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (suc (dim A)) cs bs × TopOK k (dim A) ts (snd (raiseL bs cs)) →
         srcVars k Δ ≡ img (fst S) (srcVars k Γ) →
         srcVars k (fst (buildList (fst (raiseL (snd (raiseL bs cs)) ts)) (psd (snd (snd (buildList (fst (raiseL bs cs)) (pse d^)))))))
           ≡ img (fst (simN cs ts bs d d^ S)) (srcVars k (fst (buildList ts (psd (snd (snd (buildList cs (pse d))))))))
  srcN k cs ts bs {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (top₁ , top₂) e =
    srcL k ts (snd (raiseL bs cs)) _ _ _ top₂
      (srcL k cs bs (pse d) (pse d^) (pseS d d^ S) top₁ (srcE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst S) (dimS S) (lenM S) e))

mutual
  tgtL : ∀ k ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (dim A) ts bs → tgtVars k Δ ≡ img (fst (snd S)) (tgtVars k Γ) →
         tgtVars k (fst (buildList (fst (raiseL bs ts)) d^)) ≡ img (fst (snd (simL ts bs d d^ S))) (tgtVars k (fst (buildList ts d)))
  tgtL k []                  bs           d d^ S _ e = e
  tgtL k (node [] ∷ ts)      []           {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top e =
    tgtL k ts [] (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (tgtE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst (snd S)) (dimS S) (lenP S) e)
  tgtL k (node [] ∷ ts)      (false ∷ bs) {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top e =
    tgtL k ts bs (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (tgtE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst (snd S)) (dimS S) (lenP S) e)
  tgtL .(suc (dim A)) (node [] ∷ ts) (true ∷ bs) {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (refl , top) e =
    tgtL _ ts bs (psd (pse d)) (psd (psd (pse (pse d^)))) (leafR d d^ S) top (tgtR Γ A (arr A (var x) (var (len Γ))) Δ x^ A^ (fst (snd S)) (dimS S) (lenP S) e)
  tgtL k (node (c ∷ cs) ∷ ts) []       d d^ S top e = tgtN k (c ∷ cs) ts [] d d^ S top e
  tgtL k (node (c ∷ cs) ∷ ts) (b ∷ bs) d d^ S top e = tgtN k (c ∷ cs) ts (b ∷ bs) d d^ S top e

  tgtN : ∀ k cs ts bs {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (suc (dim A)) cs bs × TopOK k (dim A) ts (snd (raiseL bs cs)) →
         tgtVars k Δ ≡ img (fst (snd S)) (tgtVars k Γ) →
         tgtVars k (fst (buildList (fst (raiseL (snd (raiseL bs cs)) ts)) (psd (snd (snd (buildList (fst (raiseL bs cs)) (pse d^)))))))
           ≡ img (fst (snd (simN cs ts bs d d^ S))) (tgtVars k (fst (buildList ts (psd (snd (snd (buildList cs (pse d))))))))
  tgtN k cs ts bs {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (top₁ , top₂) e =
    tgtL k ts (snd (raiseL bs cs)) _ _ _ top₂
      (tgtL k cs bs (pse d) (pse d^) (pseS d d^ S) top₁ (tgtE k Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (fst (snd S)) (dimS S) (lenP S) e))

------------------------------------------------------------------------
-- The boundary equations for trees.

src-incl : ∀ k bs t ts → TopOK k 0 (t ∷ ts) bs →
           srcVars k (ctxOf (raiseT bs (node (t ∷ ts)))) ≡ img (inclM bs t ts) (srcVars k (ctxOf (node (t ∷ ts))))
src-incl k []       t ts top = srcL k (t ∷ ts) [] pss pss base top refl
src-incl k (b ∷ bs) t ts top = srcL k (t ∷ ts) (b ∷ bs) pss pss base top refl

tgt-incl : ∀ k bs t ts → TopOK k 0 (t ∷ ts) bs →
           tgtVars k (ctxOf (raiseT bs (node (t ∷ ts)))) ≡ img (inclP bs t ts) (tgtVars k (ctxOf (node (t ∷ ts))))
tgt-incl k []       t ts top = tgtL k (t ∷ ts) [] pss pss base top refl
tgt-incl k (b ∷ bs) t ts top = tgtL k (t ∷ ts) (b ∷ bs) pss pss base top refl

------------------------------------------------------------------------
-- At or above the dimension of a pasting context, srcVars and tgtVars
-- are all its levels.

private
  max-lt-l : ∀ a b k → T (max a b <ℕ k) → T (a <ℕ k)
  max-lt-l zero    b       (suc k) _ = tt
  max-lt-l (suc a) zero    k       p = p
  max-lt-l (suc a) (suc b) (suc k) p = max-lt-l a b k p

  max-lt-r : ∀ a b k → T (max a b <ℕ k) → T (b <ℕ k)
  max-lt-r zero    b       k       p = p
  max-lt-r (suc a) zero    (suc k) _ = tt
  max-lt-r (suc a) (suc b) (suc k) p = max-lt-r a b k p

  lt-not : ∀ a k → T (suc a <ℕ suc k) → (k <ℕ suc a) ≡ false
  lt-not a       zero    ()
  lt-not zero    (suc k) _ = refl
  lt-not (suc a) (suc k) p = lt-not a k p

  lt-not′ : ∀ a k → T (suc a <ℕ suc k) → (k <ℕ a) ≡ false
  lt-not′ a       zero    ()
  lt-not′ zero    (suc k) _ = refl
  lt-not′ (suc a) (suc k) p = lt-not′ a k p

  lt-neq : ∀ a k → T (suc a <ℕ suc k) → (a ==ℕ k) ≡ false
  lt-neq a       zero    ()
  lt-neq zero    (suc k) _ = refl
  lt-neq (suc a) (suc k) p = lt-neq a k p

full-src : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ k → T (dimCtx Γ <ℕ suc k) → srcVars k Γ ≡ upTo (len Γ)
full-src pss k _ = refl
full-src (pse {Γ} {x} {A} d) k p
  rewrite lt-not (dim A) k (max-lt-l (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc k) p)
        | full-src d k (max-lt-r (dim A) (dimCtx Γ) (suc k) (max-lt-r (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc k) p)) = refl
full-src (psd d) k p = full-src d k p

full-tgt : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ k → T (dimCtx Γ <ℕ suc k) → tgtVars k Γ ≡ upTo (len Γ)
full-tgt pss k _ = refl
full-tgt (pse {Γ} {x} {A} d) k p
  rewrite lt-not′ (dim A) k (max-lt-l (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc k) p)
        | lt-neq (dim A) k (max-lt-l (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc k) p)
        | full-tgt d k (max-lt-r (dim A) (dimCtx Γ) (suc k) (max-lt-r (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc k) p)) = refl
full-tgt (psd d) k p = full-tgt d k p

------------------------------------------------------------------------
-- The dimension of the raised context: if τ has dimension ≤ k and some
-- flagged leaf (all of dimension k) is raised, the raised context has
-- dimension k + 1.

Le : Nat → Nat → Set
Le a b = T (a <ℕ suc b)

private
  le-refl : ∀ a → Le a a
  le-refl a = <-self a

  le-trans : ∀ a b c → Le a b → Le b c → Le a c
  le-trans zero    b       c       _ _ = tt
  le-trans (suc a) zero    c       () _
  le-trans (suc a) (suc b) zero    _ ()
  le-trans (suc a) (suc b) (suc c) p q = le-trans a b c p q

  le-suc : ∀ a → Le a (suc a)
  le-suc zero    = tt
  le-suc (suc a) = le-suc a

  le-max-l : ∀ a b → Le a (max a b)
  le-max-l zero    b       = tt
  le-max-l (suc a) zero    = le-refl (suc a)
  le-max-l (suc a) (suc b) = le-max-l a b

  le-max-r : ∀ a b → Le b (max a b)
  le-max-r zero    b       = le-refl b
  le-max-r (suc a) zero    = tt
  le-max-r (suc a) (suc b) = le-max-r a b

  max-lub : ∀ a b c → Le a c → Le b c → Le (max a b) c
  max-lub zero    b       c       _ q = q
  max-lub (suc a) zero    c       p _ = p
  max-lub (suc a) (suc b) zero    () _
  max-lub (suc a) (suc b) (suc c) p q = max-lub a b c p q

  le-antisym : ∀ a b → Le a b → Le b a → a ≡ b
  le-antisym zero    zero    _ _ = refl
  le-antisym zero    (suc b) _ ()
  le-antisym (suc a) zero    () _
  le-antisym (suc a) (suc b) p q = cong suc (le-antisym a b p q)

  -- x ≤ max y z, from x ≤ y.
  up-l : ∀ x y z → Le x y → Le x (max y z)
  up-l x y z p = le-trans x y (max y z) p (le-max-l y z)

  up-r : ∀ x y z → Le x z → Le x (max y z)
  up-r x y z p = le-trans x z (max y z) p (le-max-r y z)

anyR : List Bool → List Tree → Bool
anyR bs                   []             = false
anyR []                   (node [] ∷ ts) = anyR [] ts
anyR (b ∷ bs)             (node [] ∷ ts) = b ∨ anyR bs ts
anyR []       (node (c ∷ cs) ∷ ts) = anyR [] (c ∷ cs) ∨ anyR (snd (raiseL [] (c ∷ cs))) ts
anyR (b ∷ bs) (node (c ∷ cs) ∷ ts) = anyR (b ∷ bs) (c ∷ cs) ∨ anyR (snd (raiseL (b ∷ bs) (c ∷ cs))) ts

-- The dimension invariant along the two runs.
record DimInv (k : Nat) (r : Bool) (Γ Δ : Ctx) : Set where
  constructor _,ᵈ_
  field
    upper : Le (dimCtx Δ) (max (dimCtx Γ) (suc k))
    lower : T r → Le (suc k) (dimCtx Δ)

private
  ∨-r′ : ∀ a b → T b → T (a ∨ b)
  ∨-r′ true  b _ = tt
  ∨-r′ false b p = p

  dimE-n : ∀ k G D a b a′ b′ → a′ ≡ a → b′ ≡ b → Le D (max G (suc k)) →
           Le (max b′ (max a′ D)) (max (max b (max a G)) (suc k))
  dimE-n k G D a b .a .b refl refl up =
    max-lub b _ M (up-l b _ (suc k) (le-max-l b _))
      (max-lub a D M (up-l a _ (suc k) (up-r a b _ (le-max-l a _)))
        (le-trans D _ M up (max-mono G _ (suc k)
          (up-r G b _ (le-max-r a G)))))
    where
    M = max (max b (max a G)) (suc k)
    max-mono : ∀ x x′ y → Le x x′ → Le (max x y) (max x′ y)
    max-mono x x′ y p = max-lub x y (max x′ y) (up-l x x′ y p) (le-max-r x′ y)

  -- A pse step on both sides (the new cells have the same dimensions).
  dimE : ∀ k r Γ A B Δ A^ B^ → dim A^ ≡ dim A → dim B^ ≡ dim B → DimInv k r Γ Δ →
         DimInv k r (Γ ▸ A ▸ B) (Δ ▸ A^ ▸ B^)
  dimE k r Γ A B Δ A^ B^ dA dB (up ,ᵈ lo) =
    dimE-n k (dimCtx Γ) (dimCtx Δ) (dim A) (dim B) (dim A^) (dim B^) dA dB up ,ᵈ
    λ t → up-r (suc k) (dim B^) _ (up-r (suc k) (dim A^) (dimCtx Δ) (lo t))

  dimR-n : ∀ G D a a′ → a′ ≡ a → Le D (max G (suc (suc a))) →
           Le (max (suc (suc a′)) (max (suc a′) (max (suc a′) (max a′ D))))
              (max (max (suc a) (max a G)) (suc (suc a)))
  dimR-n G D a .a refl up =
    max-lub ssa (max sa (max sa (max a D))) M (up-r ssa G₁ ssa (le-refl ssa))
      (max-lub sa (max sa (max a D)) M sa≤
        (max-lub sa (max a D) M sa≤
          (max-lub a D M (up-l a G₁ ssa (up-r a sa (max a G) (le-max-l a G)))
            (le-trans D (max G ssa) M up
              (max-lub G ssa M (up-l G G₁ ssa (up-r G sa (max a G) (le-max-r a G)))
                (le-max-r G₁ ssa))))))
    where
    sa  = suc a
    ssa = suc sa
    G₁  = max sa (max a G)
    M   = max G₁ ssa
    sa≤ : Le sa M
    sa≤ = le-trans sa ssa M (le-suc sa) (le-max-r G₁ ssa)

  lowR : ∀ a a′ n → a′ ≡ a → Le (suc (suc a′)) n → Le (suc (suc a)) n
  lowR a .a n refl p = p

  -- A raised leaf of dimension k = suc (dim A).
  dimR : ∀ r Γ A x Δ x^ A^ → dim A^ ≡ dim A → DimInv (suc (dim A)) r Γ Δ →
         DimInv (suc (dim A)) true (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (Raised Δ x^ A^)
  dimR r Γ A x Δ x^ A^ dA (up ,ᵈ lo) =
    dimR-n (dimCtx Γ) (dimCtx Δ) (dim A) (dim A^) dA up ,ᵈ
    λ _ → lowR (dim A) (dim A^) (dimCtx (Raised Δ x^ A^)) dA
             (le-max-l (suc (suc (dim A^))) (max (suc (dim A^)) (max (suc (dim A^)) (max (dim A^) (dimCtx Δ)))))

  dimW : ∀ {k a b Γ Δ} → (T b → T a) → DimInv k a Γ Δ → DimInv k b Γ Δ
  dimW f (up ,ᵈ lo) = up ,ᵈ λ t → lo (f t)

  ∨-false-T : ∀ r → T (r ∨ false) → T r
  ∨-false-T true  _ = tt

  ∨-assoc-T : ∀ r a b → T (r ∨ (a ∨ b)) → T ((r ∨ a) ∨ b)
  ∨-assoc-T true  a b _ = tt
  ∨-assoc-T false true  b _ = tt
  ∨-assoc-T false false b p = p

mutual
  dimL : ∀ k ts bs r {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (dim A) ts bs → DimInv k r Γ Δ →
         DimInv k (r ∨ anyR bs ts) (fst (buildList ts d)) (fst (buildList (fst (raiseL bs ts)) d^))
  dimL k []                  bs           r d d^ S _ i = dimW (∨-false-T r) i
  dimL k (node [] ∷ ts)      []           r {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top i =
    dimL k ts [] r (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (dimE k r Γ A _ Δ A^ _ (dimS S) (cong suc (dimS S)) i)
  dimL k (node [] ∷ ts)      (false ∷ bs) r {Γ} {x} {A} {Δ} {x^} {A^} d d^ S top i =
    dimL k ts bs r (psd (pse d)) (psd (pse d^)) (leafP d d^ S) top (dimE k r Γ A _ Δ A^ _ (dimS S) (cong suc (dimS S)) i)
  dimL .(suc (dim A)) (node [] ∷ ts) (true ∷ bs) r {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (refl , top) i =
    dimW (λ _ → tt) (dimL _ ts bs true (psd (pse d)) (psd (psd (pse (pse d^)))) (leafR d d^ S) top
                      (dimR r Γ A x Δ x^ A^ (dimS S) i))
  dimL k (node (c ∷ cs) ∷ ts) []       r d d^ S top i = dimN k (c ∷ cs) ts [] r d d^ S top i
  dimL k (node (c ∷ cs) ∷ ts) (b ∷ bs) r d d^ S top i = dimN k (c ∷ cs) ts (b ∷ bs) r d d^ S top i

  dimN : ∀ k cs ts bs r {Γ x A Δ x^ A^} (d : Γ ⊢ps x ∶ A) (d^ : Δ ⊢ps x^ ∶ A^) (S : Sim Γ x A Δ x^ A^) →
         TopOK k (suc (dim A)) cs bs × TopOK k (dim A) ts (snd (raiseL bs cs)) → DimInv k r Γ Δ →
         DimInv k (r ∨ (anyR bs cs ∨ anyR (snd (raiseL bs cs)) ts))
           (fst (buildList ts (psd (snd (snd (buildList cs (pse d)))))))
           (fst (buildList (fst (raiseL (snd (raiseL bs cs)) ts)) (psd (snd (snd (buildList (fst (raiseL bs cs)) (pse d^)))))))
  dimN k cs ts bs r {Γ} {x} {A} {Δ} {x^} {A^} d d^ S (top₁ , top₂) i =
    dimW (∨-assoc-T r (anyR bs cs) (anyR (snd (raiseL bs cs)) ts))
      (dimL k ts (snd (raiseL bs cs)) (r ∨ anyR bs cs) _ _ (psdS (simL cs bs (pse d) (pse d^) (pseS d d^ S))) top₂
        (dimL k cs bs r (pse d) (pse d^) (pseS d d^ S) top₁
          (dimE k r Γ A (arr A (var x) (var (len Γ))) Δ A^ (arr A^ (var x^) (var (len Δ))) (dimS S) (cong suc (dimS S)) i)))

private
  le-max-suc : ∀ G k → Le G k → Le (max G (suc k)) (suc k)
  le-max-suc G k p = max-lub G (suc k) (suc k) (le-trans G k (suc k) p (le-suc k)) (le-refl (suc k))

  dimInv-eq : ∀ {k r Γ Δ} → DimInv k r Γ Δ → Le (dimCtx Γ) k → T r → dimCtx Δ ≡ suc k
  dimInv-eq {k} {r} {Γ} {Δ} (up ,ᵈ lo) le t =
    le-antisym (dimCtx Δ) (suc k)
      (le-trans (dimCtx Δ) (max (dimCtx Γ) (suc k)) (suc k) up (le-max-suc (dimCtx Γ) k le)) (lo t)

  dim0 : ∀ k → DimInv k false (ε ▸ ⋆) (ε ▸ ⋆)
  dim0 k = tt ,ᵈ λ ()

-- If τ has dimension ≤ k, every flagged leaf has dimension k and some
-- leaf is flagged, then the raised context has dimension k + 1.
dim-raise : ∀ k bs t ts → Le (dimCtx (ctxOf (node (t ∷ ts)))) k → TopOK k 0 (t ∷ ts) bs →
            T (anyR bs (t ∷ ts)) → dimCtx (ctxOf (raiseT bs (node (t ∷ ts)))) ≡ suc k
dim-raise k []       t ts le top a = dimInv-eq (dimL k (t ∷ ts) [] false pss pss base top (dim0 k)) le a
dim-raise k (b ∷ bs) t ts le top a = dimInv-eq (dimL k (t ∷ ts) (b ∷ bs) false pss pss base top (dim0 k)) le a

------------------------------------------------------------------------
-- The boundaries of the raised context are the images of τ under the
-- two inclusions:
--
--   ∂⁻ (ctxOf (raiseT bs τ)) ≡ img incl⁻ (all levels of τ)
--   ∂⁺ (ctxOf (raiseT bs τ)) ≡ img incl⁺ (all levels of τ)

private
  dTree : ∀ t ts → ctxOf (node (t ∷ ts)) ⊢ps fst (snd (build (node (t ∷ ts)) pss)) ∶ ⋆
  dTree t ts = snd (snd (build (node (t ∷ ts)) pss))

src-raise : ∀ k bs t ts → Le (dimCtx (ctxOf (node (t ∷ ts)))) k → TopOK k 0 (t ∷ ts) bs →
            T (anyR bs (t ∷ ts)) →
            ∂⁻ (ctxOf (raiseT bs (node (t ∷ ts)))) ≡ img (inclM bs t ts) (upTo (len (ctxOf (node (t ∷ ts)))))
src-raise k bs t ts le top a =
  trans (cong (λ n → srcVars (n ∸ 1) (ctxOf (raiseT bs (node (t ∷ ts))))) (dim-raise k bs t ts le top a))
    (trans (src-incl k bs t ts top) (cong (img (inclM bs t ts)) (full-src (dTree t ts) k le)))

tgt-raise : ∀ k bs t ts → Le (dimCtx (ctxOf (node (t ∷ ts)))) k → TopOK k 0 (t ∷ ts) bs →
            T (anyR bs (t ∷ ts)) →
            ∂⁺ (ctxOf (raiseT bs (node (t ∷ ts)))) ≡ img (inclP bs t ts) (upTo (len (ctxOf (node (t ∷ ts)))))
tgt-raise k bs t ts le top a =
  trans (cong (λ n → tgtVars (n ∸ 1) (ctxOf (raiseT bs (node (t ∷ ts))))) (dim-raise k bs t ts le top a))
    (trans (tgt-incl k bs t ts top) (cong (img (inclP bs t ts)) (full-tgt (dTree t ts) k le)))
