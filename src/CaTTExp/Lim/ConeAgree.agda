------------------------------------------------------------------------
-- The repaired cone and the kernel's cone shape agree on every globular
-- diagram, in every dimension (ledger S27 (h′)).
--
-- Two constructions of Mikhail's specified cone (Thm 3.3) exist:
--
--  * CaTTExp.Lim.Repaired.coneC, over named contexts, which the
--    recognition rules of CaTTExp.Lim.Rules accept (`SpecCone`), and
--  * CaTTExp.Cones.ConeOf.cone, over expression contexts, evaluated to
--    CaTT syntax; the kernel's limit heads take it as their cone shape
--    (`coneShape`, CaTTExp.Binder.LimHeadsExamples).
--
-- `cone-agrees` proves that for every well-formed globular diagram Γ
-- (every boundary of every variable is a variable, of the right type;
-- the decidable test `gwf`), named canonically,
--
--   coneC Γ c >>= λ Π → lower (Γ, c, Π)   ≡   lower Γ >>= coneShape,
--
-- with c the next free name, and both sides are `just` the explicit
-- cone context `QM.Qc` (spec §6.1):
--
--   p_x : c → x                                          (dim x = 0)
--   p_t : p_{τt} → p_{σt} ∗_{m−1} (… (p_{σᵐt} ∗₀ t))      (dim t = m ≥ 1)
--
-- typed by CaTTExp.Lim.ConeCells (`Proj.projN`). The kernel side uses
-- the soundness of the kernel's evaluator (CaTTExp.Lim.ConesEval): the
-- kernel's long side is a composable chain whose cell is ConeCells'
-- T_t (spec Lemma 2.2 gives composability), so it evaluates to it.
-- The theorem is stated for canonical naming (`named`: the variable at
-- level i is named i, the apex is named |Γ|), the naming used by
-- Lim/Repaired's examples; invariance of coneC under other injective
-- namings is not proved here.
------------------------------------------------------------------------
module CaTTExp.Lim.ConeAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅; build)
open import CaTTExp.Cones
  using (Ex; ExTy; ExCtx; v; ob; hom; bn; nth; length; map; Cell; dimC; srcC; tgtC; dimE;
         srcE; evCtx; evCtxGo; tyE; srcIter; module ConeOf)
open import CaTTExp.Lim.ConeCells
  using (pred; srcN; chainF; lenL; ChainOK; chain-dim; dim-srcN; module Proj)
open import CaTTExp.Lim.ConesEval
  using (Le; lt0; le-refl; le-trans; le-suc; le-step; lt-le; le-lt; +-zero; +-suc; subst₂;
         length-++; nth-app-l; nth-last; nth-out; ScE; sv; sb; ScTy; Comp; module Main)
open import CaTTExp.Lim.Named
  using (NCtx; ∅; _▹_∶_; _⧺_; names; size; levelOf; lower; renTy; renTm; renSub)
open import CaTTExp.Lim.Rules using (coneCtx)
import CaTTExp.Lim.Repaired as R
open import CaTTExp.Binder.LimHeadsExamples using (coneShape; toExCtx; toExTy)

------------------------------------------------------------------------
-- Arithmetic and lists.

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

private
  lt-irr : ∀ m → (m <ℕ m) ≡ false
  lt-irr zero    = refl
  lt-irr (suc m) = lt-irr m

  eq-refl : ∀ m → (m ==ℕ m) ≡ true
  eq-refl zero    = refl
  eq-refl (suc m) = eq-refl m

  lt-neq : ∀ i m → T (i <ℕ m) → (i ==ℕ m) ≡ false
  lt-neq zero    (suc m) _ = refl
  lt-neq (suc i) (suc m) p = lt-neq i m p
  lt-neq i       zero    p = lt0 i p

  <-trans : ∀ i j k → T (i <ℕ j) → T (j <ℕ k) → T (i <ℕ k)
  <-trans i j k p q = le-lt i k (le-trans (suc i) j k (lt-le i j p) (le-trans j (suc j) k (le-suc j) (lt-le j k q)))

  n<suc : ∀ n → T (n <ℕ suc n)
  n<suc zero    = tt
  n<suc (suc n) = n<suc n

  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc i n p = <-trans i n (suc n) p (n<suc n)

  lt-add : ∀ n {a k} → T (a <ℕ k) → T ((n + a) <ℕ (n + k))
  lt-add zero    p = p
  lt-add (suc n) p = lt-add n p

  le-add : ∀ n k → T (n <ℕ suc (n + k))
  le-add zero    k = tt
  le-add (suc n) k = le-add n k

  -- i < suc m splits into i < m or i = m.
  split : ∀ i m → T (i <ℕ suc m) → T (i <ℕ m) ⊎ (i ≡ m)
  split zero    zero    _ = inr refl
  split zero    (suc m) _ = inl tt
  split (suc i) zero    p = lt0 i p
  split (suc i) (suc m) p with split i m p
  ... | inl q = inl q
  ... | inr e = inr (cong suc e)

  ∸0 : ∀ a → a ∸ 0 ≡ a
  ∸0 zero    = refl
  ∸0 (suc a) = refl

  ∸-self : ∀ m → m ∸ m ≡ 0
  ∸-self zero    = refl
  ∸-self (suc m) = ∸-self m

  -- m ∸ j = suc (m ∸ suc j) when j < m.
  ∸-step : ∀ m j → T (j <ℕ m) → m ∸ j ≡ suc (m ∸ suc j)
  ∸-step (suc m) zero    _ = cong suc (sym (∸0 m))
  ∸-step (suc m) (suc j) p = ∸-step m j p
  ∸-step zero    j       p = lt0 j p

  ∸-le′ : ∀ m j → Le (m ∸ j) m
  ∸-le′ zero    zero    = tt
  ∸-le′ zero    (suc j) = tt
  ∸-le′ (suc m) zero    = le-refl m
  ∸-le′ (suc m) (suc j) = le-step (m ∸ j) m (∸-le′ m j)

  ∸-suc : ∀ m k → Le k m → suc m ∸ k ≡ suc (m ∸ k)
  ∸-suc m       zero    _ = cong suc (sym (∸0 m))
  ∸-suc (suc m) (suc k) p = ∸-suc m k p
  ∸-suc zero    (suc k) p = lt0 k p

  -- m ∸ (m ∸ j) = j when j ≤ m.
  ∸-∸ : ∀ m j → Le j m → m ∸ (m ∸ j) ≡ j
  ∸-∸ m       zero    _ = trans (cong (m ∸_) (∸0 m)) (∸-self m)
  ∸-∸ (suc m) (suc j) p = trans (∸-suc m (m ∸ j) (∸-le′ m j)) (cong suc (∸-∸ m j p))
  ∸-∸ zero    (suc j) p = lt0 j p

nth-app-r : ∀ {A : Set} (d : A) xs ys j → nth d (xs ++ ys) (length xs + j) ≡ nth d ys j
nth-app-r d []       ys j = refl
nth-app-r d (x ∷ xs) ys j = nth-app-r d xs ys j

nth-map : ∀ {A B : Set} (f : A → B) (d : A) xs i → nth (f d) (map f xs) i ≡ f (nth d xs i)
nth-map f d []       i       = refl
nth-map f d (x ∷ xs) zero    = refl
nth-map f d (x ∷ xs) (suc i) = nth-map f d xs i

length-map : ∀ {A B : Set} (f : A → B) xs → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

snoc-len : ∀ {A : Set} (xs : List A) x → length (xs ++ (x ∷ [])) ≡ suc (length xs)
snoc-len []       x = refl
snoc-len (y ∷ xs) x = cong suc (snoc-len xs x)

lt-snoc : ∀ {A : Set} (xs : List A) x i → T (i <ℕ length (xs ++ (x ∷ []))) → T (i <ℕ length xs) ⊎ (i ≡ length xs)
lt-snoc xs x i p = split i (length xs) (subst (λ n → T (i <ℕ n)) (snoc-len xs x) p)

------------------------------------------------------------------------
-- Diagrams: pure contexts read left to right.

tyList : Ctx → List Ty
tyList ε       = []
tyList (Γ ▸ A) = tyList Γ ++ (A ∷ [])

len-tyList : ∀ Γ → length (tyList Γ) ≡ len Γ
len-tyList ε       = refl
len-tyList (Γ ▸ A) = trans (snoc-len (tyList Γ) A) (cong suc (len-tyList Γ))

-- A list of types as a context.
ctxGo : Ctx → List Ty → Ctx
ctxGo acc []       = acc
ctxGo acc (A ∷ As) = ctxGo (acc ▸ A) As

ctxGo-snoc : ∀ acc As A → ctxGo acc (As ++ (A ∷ [])) ≡ ctxGo acc As ▸ A
ctxGo-snoc acc []       A = refl
ctxGo-snoc acc (B ∷ As) A = ctxGo-snoc (acc ▸ B) As A

ctx-tyList : ∀ Γ → ctxGo ε (tyList Γ) ≡ Γ
ctx-tyList ε       = refl
ctx-tyList (Γ ▸ A) = trans (ctxGo-snoc ε (tyList Γ) A) (cong (_▸ A) (ctx-tyList Γ))

-- A globular type as an expression type.
exTy : Ty → ExTy
exTy ⋆                       = ob
exTy (arr A (var s) (var t)) = hom (exTy A) (v s) (v t)
exTy _                       = ob

-- Well-formed globular types over G, below level i: every boundary is
-- a variable below i of the right type.
data OkT (G : List Ty) (i : Nat) : Ty → Set where
  ok⋆ : OkT G i ⋆
  okA : ∀ {A s t} → T (s <ℕ i) → T (t <ℕ i) → nth ⋆ G s ≡ A → nth ⋆ G t ≡ A → OkT G i A →
        OkT G i (arr A (var s) (var t))

WF : List Ty → Set
WF G = ∀ i → T (i <ℕ length G) → OkT G i (nth ⋆ G i)

-- The decidable test: each entry is well formed over the entries before it.
okTy : List Ty → Ty → Bool
okTy Ts ⋆ = true
okTy Ts (arr A (var s) (var t)) =
  (s <ℕ length Ts) ∧ (t <ℕ length Ts) ∧ (nth ⋆ Ts s ==Ty A) ∧ (nth ⋆ Ts t ==Ty A) ∧ okTy Ts A
okTy Ts (arr A _ _) = false

gwf : Ctx → Bool
gwf ε       = true
gwf (Γ ▸ A) = gwf Γ ∧ okTy (tyList Γ) A

private
  okTy-sound : ∀ Ts A → T (okTy Ts A) → OkT Ts (length Ts) A
  okTy-sound Ts ⋆ _ = ok⋆
  okTy-sound Ts (arr A (var s) (var t)) p =
    okA (∧-fst p) (∧-fst p2) (==Ty-sound _ A (∧-fst p3)) (==Ty-sound _ A (∧-fst p4))
        (∧-snd {nth ⋆ Ts t ==Ty A} p4 ▷ okTy-sound Ts A)
    where
    _▷_ : ∀ {X Y : Set} → X → (X → Y) → Y
    x ▷ f = f x
    p2 = ∧-snd {s <ℕ length Ts} p
    p3 = ∧-snd {t <ℕ length Ts} p2
    p4 = ∧-snd {nth ⋆ Ts s ==Ty A} p3
  okTy-sound Ts (arr A (var s) (coh _ _ _)) ()
  okTy-sound Ts (arr A (var s) (cst ()))
  okTy-sound Ts (arr A (coh _ _ _) u) ()
  okTy-sound Ts (arr A (cst ()) u)

  -- OkT only looks below its level.
  okT-ext : ∀ G G′ i → (∀ j → T (j <ℕ i) → nth ⋆ G′ j ≡ nth ⋆ G j) → ∀ {A} → OkT G i A → OkT G′ i A
  okT-ext G G′ i h ok⋆ = ok⋆
  okT-ext G G′ i h (okA qs qt es et ok) =
    okA qs qt (trans (h _ qs) es) (trans (h _ qt) et) (okT-ext G G′ i h ok)

gwf-sound : ∀ Γ → T (gwf Γ) → WF (tyList Γ)
gwf-sound ε       _ i p = lt0 i p
gwf-sound (Γ ▸ A) w i p with lt-snoc (tyList Γ) A i p
... | inl q =
  subst (OkT G′ i) (sym (nth-app-l ⋆ G (A ∷ []) i q))
        (okT-ext G G′ i (λ j r → nth-app-l ⋆ G (A ∷ []) j (<-trans j i (length G) r q))
                 (gwf-sound Γ (∧-fst w) i q))
  where
  G = tyList Γ
  G′ = G ++ (A ∷ [])
... | inr refl =
  subst (OkT G′ (length G)) (sym (nth-last ⋆ G A))
        (okT-ext G G′ (length G) (λ j r → nth-app-l ⋆ G (A ∷ []) j r)
                 (okTy-sound G A (∧-snd {gwf Γ} w)))
  where
  G = tyList Γ
  G′ = G ++ (A ∷ [])

------------------------------------------------------------------------
-- The explicit cone over a diagram G, apex n, p_x at level n + 1 + x.

module QM (G : List Ty) (n : Nat) where
  P : Nat → Nat
  P x = suc (n + x)

  open Proj n P public using (projN; pcs; pc; Tc; pv; dim-projN; len-pcs; pcs-ok; tgt-pc; chain-comp)

  cellOf : Nat → Cell
  cellOf x = var x , nth ⋆ G x

  projEnt : Nat → Ty
  projEnt x = projN (var x) (nth ⋆ G x)

  pl : Nat → Nat → List Ty
  pl k zero    = []
  pl k (suc m) = projEnt k ∷ pl (suc k) m

  QL : List Ty
  QL = G ++ (⋆ ∷ pl 0 n)

  Qc : Ctx
  Qc = ctxGo ε QL

  private
    nth-pl : ∀ k m x → T (x <ℕ m) → nth ⋆ (pl k m) x ≡ projEnt (k + x)
    nth-pl k (suc m) zero    _ = cong projEnt (sym (+-zero k))
    nth-pl k (suc m) (suc x) p = trans (nth-pl (suc k) m x p) (cong projEnt (sym (+-suc k x)))
    nth-pl k zero    x       p = lt0 x p

    len-pl : ∀ k m → length (pl k m) ≡ m
    len-pl k zero    = refl
    len-pl k (suc m) = cong suc (len-pl (suc k) m)

  module _ (hn : length G ≡ n) where
    QL-G : ∀ i → T (i <ℕ n) → nth ⋆ QL i ≡ nth ⋆ G i
    QL-G i p = nth-app-l ⋆ G _ i (subst (λ m → T (i <ℕ m)) (sym hn) p)

    QL-c : nth ⋆ QL n ≡ ⋆
    QL-c = trans (cong (nth ⋆ QL) (sym (trans (+-zero (length G)) hn))) (nth-app-r ⋆ G _ 0)

    QL-P : ∀ x → T (x <ℕ n) → nth ⋆ QL (P x) ≡ projEnt x
    QL-P x p =
      trans (cong (nth ⋆ QL) (sym (trans (+-suc (length G) x) (cong (λ m → suc (m + x)) hn))))
            (trans (nth-app-r ⋆ G _ (suc x)) (nth-pl 0 n x p))

    len-QL : length QL ≡ suc (n + n)
    len-QL = trans (length-++ G _) (trans (cong₂ _+_ hn (cong suc (len-pl 0 n))) (+-suc n n))

------------------------------------------------------------------------
-- Cells and their iterated sources.

private
  srcN-srcC : ∀ k c → srcN k (srcC c) ≡ srcC (srcN k c)
  srcN-srcC zero    c = refl
  srcN-srcC (suc k) c = srcN-srcC k (srcC c)

module PcsLemmas (n : Nat) (P : Nat → Nat) where
  open Proj n P

  pcs-pos : ∀ d → T (0 <ℕ dimC d) → pcs (snd d) ≡ pc (srcC d) ∷ pcs (snd (srcC d))
  pcs-pos (y , arr B s t) _ = refl
  pcs-pos (y , ⋆) ()

  pcs-zero : ∀ d → dimC d ≡ 0 → pcs (snd d) ≡ []
  pcs-zero (y , ⋆) _ = refl
  pcs-zero (y , arr B s t) ()

  -- The projections of the iterated sources: pcs of the k-fold source.
  pcs-step : ∀ k c → T (0 <ℕ dimC (srcN k c)) →
             pcs (snd (srcN k c)) ≡ pc (srcN (suc k) c) ∷ pcs (snd (srcN (suc k) c))
  pcs-step k c p =
    trans (pcs-pos (srcN k c) p)
          (cong (λ d → pc d ∷ pcs (snd d)) (sym (srcN-srcC k c)))

------------------------------------------------------------------------
-- Scoping is monotone.

private
  scE-mono : ∀ {a b} → Le a b → ∀ {e} → ScE a e → ScE b e
  scE-mono {a} {b} q (sv {j} p) = sv (le-lt j b (le-trans (suc j) a b (lt-le j a p) q))
  scE-mono q (sb su sw) = sb (scE-mono q su) (scE-mono q sw)

  scTy-mono : ∀ {a b} → Le a b → ∀ X → ScTy a X → ScTy b X
  scTy-mono q ob          _              = tt
  scTy-mono q (hom X s t) (sX , ss , st) = scTy-mono q X sX , scE-mono q ss , scE-mono q st

------------------------------------------------------------------------
-- The kernel side: ConeOf's cone over a well-formed globular diagram
-- evaluates to the explicit cone.

module KS (G : List Ty) (wf : WF G) where
  E : ExCtx
  E = map exTy G

  module C = ConeOf E

  n : Nat
  n = length E

  hn : length G ≡ n
  hn = sym (length-map exTy G)

  open QM G n
  open PcsLemmas n P

  nth-E : ∀ i → nth ob E i ≡ exTy (nth ⋆ G i)
  nth-E i = nth-map exTy ⋆ G i

  wf′ : ∀ i → T (i <ℕ n) → OkT G i (nth ⋆ G i)
  wf′ i p = wf i (subst (λ m → T (i <ℕ m)) (sym hn) p)

  ------------------------------------------------------------------
  -- The layout of ConeOf.build.

  private
    lt-snoc′ : ∀ (K : ExCtx) a j → T (j <ℕ length K) → T (j <ℕ length (K ++ (a ∷ [])))
    lt-snoc′ K a j p = subst (λ m → T (j <ℕ m)) (sym (snoc-len K a)) (<-suc j (length K) p)

  len-build : ∀ x K As → length (C.build x K As) ≡ length K + length As
  len-build x K []       = sym (+-zero (length K))
  len-build x K (A ∷ As) =
    trans (len-build (suc x) (K ++ (C.projTy K x A ∷ [])) As)
          (trans (cong (_+ length As) (snoc-len K _)) (sym (+-suc (length K) (length As))))

  build-pre : ∀ x K As j → T (j <ℕ length K) → nth ob (C.build x K As) j ≡ nth ob K j
  build-pre x K []       j p = refl
  build-pre x K (A ∷ As) j p =
    trans (build-pre (suc x) (K ++ (a ∷ [])) As j (lt-snoc′ K a j p)) (nth-app-l ob K (a ∷ []) j p)
    where a = C.projTy K x A

  build-new : ∀ x K As m → T (m <ℕ length As) →
    Σ ExCtx (λ K′ → (length K′ ≡ length K + m) ×
                    (∀ j → T (j <ℕ length K′) → nth ob K′ j ≡ nth ob (C.build x K As) j) ×
                    (nth ob (C.build x K As) (length K + m) ≡ C.projTy K′ (x + m) (nth ob As m)))
  build-new x K (A ∷ As) zero _ =
    K , sym (+-zero (length K)) ,
    (λ j p → sym (build-pre x K (A ∷ As) j p)) ,
    trans (cong (nth ob (C.build (suc x) K₁ As)) (+-zero (length K)))
      (trans (build-pre (suc x) K₁ As (length K) (subst (λ m → T (length K <ℕ m)) (sym (snoc-len K a)) (n<suc (length K))))
        (trans (nth-last ob K a) (cong (λ y → C.projTy K y A) (sym (+-zero x)))))
    where
    a = C.projTy K x A
    K₁ = K ++ (a ∷ [])
  build-new x K (A ∷ As) (suc m) p with build-new (suc x) (K ++ (C.projTy K x A ∷ [])) As m p
  ... | K′ , lK , pre , ent =
    K′ , trans lK (trans (cong (_+ m) (snoc-len K _)) (sym (+-suc (length K) m))) , pre ,
    trans (cong (nth ob (C.build (suc x) (K ++ (C.projTy K x A ∷ [])) As))
                (trans (+-suc (length K) m) (cong (_+ m) (sym (snoc-len K (C.projTy K x A))))))
          (trans ent (cong (λ y → C.projTy K′ y (nth ob As m)) (sym (+-suc x m))))
  build-new x K [] m p = lt0 m p

  K₀ : ExCtx
  K₀ = E ++ (ob ∷ [])

  Kc : ExCtx
  Kc = C.cone

  len-Kc : length Kc ≡ suc (n + n)
  len-Kc = trans (len-build 0 K₀ E) (cong (_+ n) (snoc-len E ob))

  kc-E : ∀ i → T (i <ℕ n) → nth ob Kc i ≡ exTy (nth ⋆ G i)
  kc-E i p = trans (build-pre 0 K₀ E i (lt-snoc′ E ob i p)) (trans (nth-app-l ob E (ob ∷ []) i p) (nth-E i))

  kc-c : nth ob Kc n ≡ ob
  kc-c = trans (build-pre 0 K₀ E n (subst (λ m → T (n <ℕ m)) (sym (snoc-len E ob)) (n<suc n)))
               (nth-last ob E ob)

  kc-P : ∀ x → T (x <ℕ n) →
    Σ ExCtx (λ K′ → (length K′ ≡ P x) × (∀ j → T (j <ℕ length K′) → nth ob K′ j ≡ nth ob Kc j) ×
                    (nth ob Kc (P x) ≡ C.projTy K′ x (exTy (nth ⋆ G x))))
  kc-P x p with build-new 0 K₀ E x p
  ... | K′ , lK , pre , ent =
    K′ , trans lK (cong (_+ x) (snoc-len E ob)) , pre ,
    trans (cong (nth ob Kc) (cong (_+ x) (sym (snoc-len E ob)))) (trans ent (cong (C.projTy K′ x) (nth-E x)))

  ------------------------------------------------------------------
  -- The intended cells: variable i is the cell (var i, QL_i).

  semV : Nat → Cell
  semV i = var i , nth ⋆ QL i

  open Main Kc semV

  x<P : ∀ x → T (x <ℕ P x)
  x<P x = CaTTExp.Lim.ConesEval.le-+l n x

  ------------------------------------------------------------------
  -- Diagram entries.

  repD : ∀ i y {A} → OkT G i A → Le i n → Rep (exTy A) (var y , A)
  repD i y ok⋆ _ = refl
  repD i y (okA {A} {s} {t} qs qt es et ok) le =
    (gv s , gv t) ,
    (cong (var s ,_) (trans (QL-G hn s (lt s qs)) es) , cong (var t ,_) (trans (QL-G hn t (lt t qt)) et)) ,
    tt , repD i s ok le
    where
    lt : ∀ j → T (j <ℕ i) → T (j <ℕ n)
    lt j q = le-lt j n (le-trans (suc j) i n (lt-le j i q) le)

  scD : ∀ i {A} → OkT G i A → ScTy i (exTy A)
  scD i ok⋆                  = tt
  scD i (okA qs qt _ _ ok)   = scD i ok , sv qs , sv qt

  dim-exTy : ∀ i {A} → OkT G i A → dimE (exTy A) ≡ dim A
  dim-exTy i ok⋆                = refl
  dim-exTy i (okA _ _ _ _ ok)   = cong suc (dim-exTy i ok)

  ------------------------------------------------------------------
  -- Iterated sources in the diagram are variables.

  σ-lem : ∀ k x → T (x <ℕ n) → Le k (dim (nth ⋆ G x)) →
    Σ Nat (λ y → (srcIter E k (v x) ≡ v y) × (srcN k (cellOf x) ≡ cellOf y) × Le (k + y) x × T (y <ℕ n))
  σ-lem zero    x p q = x , refl , refl , le-refl x , p
  σ-lem (suc k) x p q = σ-step (nth ⋆ G x) refl (wf′ x p) q
    where
    σ-step : ∀ A → nth ⋆ G x ≡ A → OkT G x A → Le (suc k) (dim A) →
      Σ Nat (λ y → (srcIter E (suc k) (v x) ≡ v y) × (srcN (suc k) (cellOf x) ≡ cellOf y) ×
                   Le (suc k + y) x × T (y <ℕ n))
    σ-step ⋆ ex ok q′ = lt0 k q′
    σ-step (arr B (var s) (var t)) ex (okA qs qt es et ok) q′
      with σ-lem k s (<-trans s x n qs p) (subst (λ D → Le k (dim D)) (sym es) q′)
    ... | y , e1 , e2 , e3 , e4 =
      y ,
      trans (cong (λ X → srcIter E k (srcE X)) (trans (nth-E x) (cong exTy ex))) e1 ,
      trans (cong (λ D → srcN k (srcC (var x , D))) ex) (trans (cong (λ D → srcN k (var s , D)) (sym es)) e2) ,
      le-trans (suc (k + y)) (suc s) x e3 (lt-le s x qs) ,
      e4

  ------------------------------------------------------------------
  -- The long side over x is a composable chain with cell T_x.

  module Long (x : Nat) (px : T (x <ℕ n)) where
    c : Cell
    c = cellOf x

    m : Nat
    m = dim (nth ⋆ G x)

    Inv : Nat → Ex → Set
    Inv j acc = Good acc × (sem acc ≡ chainF (pcs (snd (srcN (m ∸ j) c))) c) × ScE (P x) acc

    private
      dsN : ∀ k → dimC (srcN k c) ≡ m ∸ k
      dsN k = dim-srcN k c

    step : ∀ j acc → T (j <ℕ m) → Inv j acc → Inv (suc j) (bn j (C.pE (srcIter E (m ∸ j) (v x))) acc)
    step j acc jm (gacc , eacc , sacc) with σ-lem (m ∸ j) x px (∸-le′ m j)
    ... | y , e1 , e2 , e3 , e4 =
      subst (λ e → Inv (suc j) (bn j (C.pE e) acc)) (sym e1)
        (good , esem , sb (sv (lt-add n {y} {x} yx)) sacc)
      where
      d = srcN (m ∸ j) c
      V = chainF (pcs (snd d)) c
      k = m ∸ suc j
      ek : m ∸ j ≡ suc k
      ek = ∸-step m j jm
      yx : T (y <ℕ x)
      yx = le-lt y x (le-trans (suc y) (suc (k + y)) x (CaTTExp.Lim.ConesEval.le-+l k y)
                               (subst (λ a → Le (a + y) x) ek e3))
      dd : dimC d ≡ j
      dd = trans (dsN (m ∸ j)) (∸-∸ m j (lt-le j m jm ▹ λ q → le-trans j (suc j) m (le-suc j) q))
        where
        _▹_ : ∀ {A B : Set} → A → (A → B) → B
        a ▹ f = f a
      spy : sem (v (P y)) ≡ pc d
      spy = trans (cong (var (P y) ,_) (QL-P hn y e4)) (cong pc (sym e2))
      okV : ChainOK (pcs (snd d)) m
      okV = pcs-ok (snd d) m (subst (λ a → T (a <ℕ m)) (sym dd) jm)
      dV : dimC V ≡ m
      dV = chain-dim (pcs (snd d)) c okV
      lenV : lenL (pcs (snd d)) ≡ j
      lenV = trans (len-pcs (snd d)) dd
      esem : sem (bn j (v (P y)) acc) ≡ chainF (pcs (snd (srcN (m ∸ suc j) c))) c
      esem =
        trans (cong₂ (CaTTExp.Lim.ConeCells.bcell j) spy eacc)
          (trans (cong (λ l → CaTTExp.Lim.ConeCells.bcell l (pc d) V) (sym lenV))
            (sym (trans (cong (λ ps → chainF ps c)
                              (pcs-step k c (subst (λ a → T (0 <ℕ a)) (sym (dsN k)) (∸-pos-lt))))
                        (cong (λ d′ → chainF (pc d′ ∷ pcs (snd d′)) c) (cong (λ a → srcN a c) (sym ek))))))
        where
        ∸-pos-lt : T (0 <ℕ m ∸ k)
        ∸-pos-lt = subst (λ a → T (0 <ℕ a)) (sym (∸-∸ m (suc j) (lt-le j m jm))) tt
      cmp : Comp j (pc d) V
      cmp = trans (cong (λ a → CaTTExp.Lim.ConeCells.tgtN (a ∸ j) (pc d))
                        (trans (dim-projN (fst d) (snd d)) (cong suc dd)))
              (trans (cong (λ a → CaTTExp.Lim.ConeCells.tgtN a (pc d)) (sk∸k j))
                (trans (chain-comp (m ∸ j) c (le-lt′))
                       (cong (λ a → srcN (a ∸ j) V) (sym dV))))
        where
        y′ = fst d
        sk∸k : ∀ k → suc k ∸ k ≡ 1
        sk∸k zero    = refl
        sk∸k (suc k) = sk∸k k
        le-lt′ : T ((m ∸ j) <ℕ suc (dimC c))
        le-lt′ = ∸-le′ m j
      good : Good (bn j (v (P y)) acc)
      good = gb (gv (P y)) gacc
               (subst (λ e → T (j <ℕ dimC e)) (sym spy)
                      (subst (λ a → T (j <ℕ a)) (sym (trans (dim-projN (fst d) (snd d)) (cong suc dd))) (n<suc j)))
               (subst (λ e → T (j <ℕ dimC e)) (sym eacc) (subst (λ a → T (j <ℕ a)) (sym dV) jm))
               (subst₂ (Comp j) (sym spy) (sym eacc) cmp)

    private
      antisym : ∀ a b → Le a b → Le b a → a ≡ b
      antisym zero    zero    _ _ = refl
      antisym (suc a) (suc b) p q = cong suc (antisym a b p q)
      antisym zero    (suc b) _ q = lt0 b q
      antisym (suc a) zero    p _ = lt0 a p

      nle-lt : ∀ a b → (a <ℕ suc b) ≡ false → T (b <ℕ a)
      nle-lt zero    b       ()
      nle-lt (suc a) zero    _ = tt
      nle-lt (suc a) (suc b) e = nle-lt a b e

    loop : ∀ f j acc → Le j m → Le m (j + f) → Inv j acc → Inv m (C.longGo x m f j acc)
    loop zero    j acc p q inv =
      subst (λ a → Inv a acc) (antisym j m p (subst (λ a → Le m a) (+-zero j) q)) inv
    loop (suc f) j acc p q inv with m <ℕ suc j in e
    ... | true  = subst (λ a → Inv a acc) (antisym j m p (subst T (sym e) tt)) inv
    ... | false =
      loop f (suc j) _ (lt-le j m (nle-lt m j e)) (subst (λ a → Le m a) (+-suc j f) q)
           (step j acc (nle-lt m j e) inv)

    init : Inv 0 (v x)
    init = gv x ,
           trans (cong (var x ,_) (QL-G hn x px))
                 (sym (cong (λ ps → chainF ps c) (pcs-zero (srcN m c) (trans (dsN m) (∸-self m))))) ,
           sv (x<P x)

    -- The kernel's long side.
    LS : Ex
    LS = C.longSide x (exTy (nth ⋆ G x))

    ls-ok : T (0 <ℕ m) → Inv m LS
    ls-ok pm =
      subst (λ M → Inv m (C.longGo x M M 1 (bn 0 (C.pE (srcIter E M (v x))) (v x))))
            (sym (dim-exTy x (wf′ x px)))
            (loop m 1 _ (lt-le 0 m pm) (le-suc m) (step 0 (v x) pm init))

    ls-sem : (pm : T (0 <ℕ m)) → sem LS ≡ Tc c
    ls-sem pm = trans (fst (snd (ls-ok pm))) (cong (λ a → chainF (pcs (snd (srcN a c))) c) (∸-self m))

  ------------------------------------------------------------------
  -- Projection entries, by strong induction.

  RP : Nat → Set
  RP x = Rep (nth ob Kc (P x)) (semV (P x)) × ScTy (P x) (nth ob Kc (P x))

  private
    n<P : ∀ x → T (n <ℕ P x)
    n<P x = le-add n x

    P-mono : ∀ t x → T (t <ℕ x) → T (P t <ℕ P x)
    P-mono t x q = lt-add n {t} {x} q

  repP : ∀ N x → T (x <ℕ N) → T (x <ℕ n) → RP x
  repP zero    x q _  = lt0 x q
  repP (suc N) x q px with kc-P x px
  ... | K′ , lK , pre , ent =
    subst (λ X → Rep X (semV (P x)) × ScTy (P x) X) (sym ent)
      (subst (λ D → Rep (C.projTy K′ x (exTy (nth ⋆ G x))) (var (P x) , D) × ScTy (P x) (C.projTy K′ x (exTy (nth ⋆ G x))))
             (sym (QL-P hn x px))
             (helper refl (wf′ x px)))
    where
    helper : ∀ {A} → nth ⋆ G x ≡ A → OkT G x A →
      Rep (C.projTy K′ x (exTy A)) (var (P x) , projN (var x) A) × ScTy (P x) (C.projTy K′ x (exTy A))
    helper ex ok⋆ =
      ((gv n , gv x) , (cong (var n ,_) (QL-c hn) , cong (var x ,_) (trans (QL-G hn x px) ex)) , tt , refl) ,
      (tt , sv (n<P x) , sv (x<P x))
    helper {arr B (var s) (var t)} ex (okA qs qt es et ok) =
      ((gv (P t) , gLS) , (es1 , els) , tt , repT) , (scT , sv (P-mono t x qt) , sLS)
      where
      A = arr B (var s) (var t)
      pt : T (t <ℕ n)
      pt = <-trans t x n qt px
      pm : T (0 <ℕ Long.m x px)
      pm = subst (λ D → T (0 <ℕ dim D)) (sym ex) tt
      module L = Long x px
      inv : L.Inv L.m (C.longSide x (exTy A))
      inv = subst (λ D → L.Inv L.m (C.longSide x (exTy D))) ex (L.ls-ok pm)
      gLS = fst inv
      sLS = snd (snd inv)
      es1 : sem (v (P t)) ≡ (var (P t) , projN (var t) B)
      es1 = cong (var (P t) ,_) (trans (QL-P hn t pt) (cong (projN (var t)) et))
      els : sem (C.longSide x (exTy A)) ≡ tgtC (var (P x) , projN (var x) A)
      els = trans (subst (λ D → sem (C.longSide x (exTy D)) ≡ Tc (var x , D)) ex (L.ls-sem pm))
                  (sym (tgt-pc (var x , A)))
      IH : RP t
      IH = repP N t (le-lt t N (le-trans (suc t) x N (lt-le t x qt) q)) pt
      pre-eq : nth ob K′ (P t) ≡ nth ob Kc (P t)
      pre-eq = pre (P t) (subst (λ a → T (P t <ℕ a)) (sym lK) (P-mono t x qt))
      repT : Rep (nth ob K′ (P t)) (var (P t) , projN (var t) B)
      repT = subst₂ Rep (sym pre-eq) (trans (cong (var (P t) ,_) refl) es1) (fst IH)
      scT : ScTy (P x) (nth ob K′ (P t))
      scT = scTy-mono {P t} {P x} (lt-le (P t) (P x) (P-mono t x qt) ▹ le-pred′) (nth ob K′ (P t))
                      (subst (ScTy (P t)) (sym pre-eq) (snd IH))
        where
        _▹_ : ∀ {X Y : Set} → X → (X → Y) → Y
        a ▹ f = f a
        le-pred′ : Le (suc (P t)) (P x) → Le (P t) (P x)
        le-pred′ r = le-trans (P t) (suc (P t)) (P x) (le-suc (P t)) r

  ------------------------------------------------------------------
  -- The hypotheses of ConesEval, and the evaluated cone.

  private
    split-n : ∀ i → (i <ℕ n) ≡ false → i ≡ n + (i ∸ n)
    split-n i e = go n i e
      where
      go : ∀ n i → (i <ℕ n) ≡ false → i ≡ n + (i ∸ n)
      go zero    i       _ = refl
      go (suc n) zero    ()
      go (suc n) (suc i) e = cong suc (go n i e)

  data Where (i : Nat) : Set where
    atD : T (i <ℕ n) → Where i
    atC : i ≡ n → Where i
    atP : ∀ x → i ≡ P x → T (x <ℕ n) → Where i

  classify : ∀ i → T (i <ℕ length Kc) → Where i
  classify i p with i <ℕ n in e
  ... | true  = atD (subst T (sym e) tt)
  ... | false with i ∸ n | split-n i e
  ...   | zero  | ei = atC (trans ei (+-zero n))
  ...   | suc x | ei =
    atP x (trans ei (+-suc n x))
          (lt-add-inv n x n (subst (λ a → T (a <ℕ suc (n + n))) (trans ei (+-suc n x)) (subst (λ a → T (i <ℕ a)) len-Kc p)))
    where
    lt-add-inv : ∀ n a b → T ((n + a) <ℕ (n + b)) → T (a <ℕ b)
    lt-add-inv zero    a b q = q
    lt-add-inv (suc n) a b q = lt-add-inv n a b q

  rep : ∀ i → T (i <ℕ length Kc) → Rep (nth ob Kc i) (semV i)
  rep i p with classify i p
  ... | atD q =
    subst (λ X → Rep X (semV i)) (sym (kc-E i q))
      (subst (λ D → Rep (exTy (nth ⋆ G i)) (var i , D)) (sym (QL-G hn i q))
             (repD i i (wf′ i q) (lt-le′ i n q)))
    where
    lt-le′ : ∀ i n → T (i <ℕ n) → Le i n
    lt-le′ i n q = le-trans i (suc i) n (le-suc i) (lt-le i n q)
  ... | atC refl = subst (λ X → Rep X (semV n)) (sym kc-c) (QL-c hn)
  ... | atP x refl px = fst (repP (suc x) x (n<suc x) px)

  sc : ∀ i → T (i <ℕ length Kc) → ScTy i (nth ob Kc i)
  sc i p with classify i p
  ... | atD q = subst (ScTy i) (sym (kc-E i q)) (scD i (wf′ i q))
  ... | atC refl = subst (ScTy n) (sym kc-c) tt
  ... | atP x refl px = snd (repP (suc x) x (n<suc x) px)

  len-KQ : length Kc ≡ length QL
  len-KQ = trans len-Kc (sym (len-QL hn))

  repOut : ∀ i → (i <ℕ length Kc) ≡ false → snd (semV i) ≡ ⋆
  repOut i e = nth-out ⋆ QL i (trans (cong (i <ℕ_) (sym len-KQ)) e)

  module H = Hyp rep repOut (λ i → refl) sc

  private
    semGo-ok : ∀ As j acc → (∀ m → T (m <ℕ length As) → nth ⋆ QL (j + m) ≡ nth ⋆ As m) →
               semGo j (length As) acc ≡ ctxGo acc As
    semGo-ok []       j acc h = refl
    semGo-ok (A ∷ As) j acc h =
      trans (cong (λ B → semGo (suc j) (length As) (acc ▸ B)) (trans (cong (nth ⋆ QL) (sym (+-zero j))) (h 0 tt)))
            (semGo-ok As (suc j) (acc ▸ A) (λ m q → trans (cong (nth ⋆ QL) (sym (+-suc j m))) (h (suc m) q)))

  -- The kernel's evaluated cone is the explicit cone.
  cone-ev : evCtx Kc ≡ Qc
  cone-ev = trans H.evCtx-ok (trans (cong (λ l → semGo 0 l ε) len-KQ) (semGo-ok QL 0 ε (λ m _ → refl)))

------------------------------------------------------------------------
-- Canonical naming, and lowering it.

named : Ctx → NCtx
named ε       = ∅
named (Γ ▸ A) = named Γ ▹ len Γ ∶ A

size-named : ∀ Γ → size (named Γ) ≡ len Γ
size-named ε       = refl
size-named (Γ ▸ A) = cong suc (size-named Γ)

private
  elem-++ : ∀ x xs ys → T (elem x (xs ++ ys)) → T (elem x xs) ⊎ T (elem x ys)
  elem-++ x []       ys p = inr p
  elem-++ x (y ∷ xs) ys p with x ==ℕ y
  ... | true  = inl tt
  ... | false = elem-++ x xs ys p

  elem-one : ∀ x y → T (elem x (y ∷ [])) → x ≡ y
  elem-one x y p with x ==ℕ y | ==ℕ-sound x y
  ... | true  | s = s tt
  ... | false | _ = ⊥-elim p

names-lt : ∀ Γ x → T (elem x (names (named Γ))) → T (x <ℕ len Γ)
names-lt (Γ ▸ A) x p with elem-++ x (names (named Γ)) (len Γ ∷ []) p
... | inl q = <-suc x (len Γ) (names-lt Γ x q)
... | inr q rewrite elem-one x (len Γ) q = n<suc (len Γ)

fresh-named : ∀ Γ → elem (len Γ) (names (named Γ)) ≡ false
fresh-named Γ with elem (len Γ) (names (named Γ)) | names-lt Γ (len Γ)
... | true  | h = ⊥-elim (subst T (lt-irr (len Γ)) (h tt))
... | false | _ = refl

levelOf-named : ∀ Γ x → T (x <ℕ len Γ) → levelOf (named Γ) x ≡ just x
levelOf-named (Γ ▸ A) x q with split x (len Γ) q
... | inl r rewrite lt-neq x (len Γ) r = levelOf-named Γ x r
... | inr refl rewrite eq-refl (len Γ) = cong just (size-named Γ)

-- Scoping: every variable is below m.
mutual
  WsTy : Nat → Ty → Set
  WsTy m ⋆           = ⊤
  WsTy m (arr A t u) = WsTy m A × WsTm m t × WsTm m u

  WsTm : Nat → Tm → Set
  WsTm m (var x)     = T (x <ℕ m)
  WsTm m (coh Δ A γ) = WsSub m γ
  WsTm m (cst ())

  WsSub : Nat → Sub → Set
  WsSub m ⟨⟩       = ⊤
  WsSub m (γ ,ₛ t) = WsSub m γ × WsTm m t

ScC : Ctx → Set
ScC ε       = ⊤
ScC (Γ ▸ A) = ScC Γ × WsTy (len Γ) A

module _ (ρ : Nat → Maybe Nat) (m : Nat) (hρ : ∀ x → T (x <ℕ m) → ρ x ≡ just x) where
  mutual
    renTy-id : ∀ A → WsTy m A → renTy ρ A ≡ just A
    renTy-id ⋆ _ = refl
    renTy-id (arr A t u) (wA , wt , wu)
      rewrite renTy-id A wA | renTm-id t wt | renTm-id u wu = refl

    renTm-id : ∀ t → WsTm m t → renTm ρ t ≡ just t
    renTm-id (var x) wx rewrite hρ x wx = refl
    renTm-id (coh Δ A γ) wγ rewrite renSub-id γ wγ = refl
    renTm-id (cst ())

    renSub-id : ∀ γ → WsSub m γ → renSub ρ γ ≡ just γ
    renSub-id ⟨⟩ _ = refl
    renSub-id (γ ,ₛ t) (wγ , wt) rewrite renSub-id γ wγ | renTm-id t wt = refl

lower-named : ∀ Γ → ScC Γ → lower (named Γ) ≡ just Γ
lower-named ε _ = refl
lower-named (Γ ▸ A) (sΓ , sA)
  rewrite fresh-named Γ | lower-named Γ sΓ
        | renTy-id (levelOf (named Γ)) (len Γ) (levelOf-named Γ) A sA = refl

------------------------------------------------------------------------
-- The kernel's cone shape of a well-formed globular diagram.

private
  map-snoc : ∀ {A B : Set} (f : A → B) xs x → map f (xs ++ (x ∷ [])) ≡ map f xs ++ (f x ∷ [])
  map-snoc f []       x = refl
  map-snoc f (y ∷ xs) x = cong (f y ∷_) (map-snoc f xs x)

  toExTy-ok : ∀ Ts A → T (okTy Ts A) → toExTy A ≡ just (exTy A)
  toExTy-ok Ts ⋆ _ = refl
  toExTy-ok Ts (arr A (var s) (var t)) p
    rewrite toExTy-ok Ts A (∧-snd {nth ⋆ Ts t ==Ty A} (∧-snd {nth ⋆ Ts s ==Ty A}
                             (∧-snd {t <ℕ length Ts} (∧-snd {s <ℕ length Ts} p)))) = refl
  toExTy-ok Ts (arr A (var s) (coh _ _ _)) ()
  toExTy-ok Ts (arr A (var s) (cst ()))
  toExTy-ok Ts (arr A (coh _ _ _) u) ()
  toExTy-ok Ts (arr A (cst ()) u)

toExCtx-ok : ∀ Γ → T (gwf Γ) → toExCtx Γ ≡ just (map exTy (tyList Γ))
toExCtx-ok ε       _ = refl
toExCtx-ok (Γ ▸ A) w
  rewrite toExCtx-ok Γ (∧-fst w) | toExTy-ok (tyList Γ) A (∧-snd {gwf Γ} w) =
  cong just (sym (map-snoc exTy (tyList Γ) A))

len-exList : ∀ Γ → length (map exTy (tyList Γ)) ≡ len Γ
len-exList Γ = trans (length-map exTy (tyList Γ)) (len-tyList Γ)

-- The kernel's cone shape is the explicit cone.
shape-ok : ∀ Γ (w : T (gwf Γ)) → coneShape Γ ≡ just (QM.Qc (tyList Γ) (len Γ))
shape-ok Γ w rewrite toExCtx-ok Γ w =
  cong just (trans (KS.cone-ev (tyList Γ) (gwf-sound Γ w))
                   (cong (QM.Qc (tyList Γ)) (len-exList Γ)))

------------------------------------------------------------------------
-- Scoping of cells, composites and projection types.

WsCell : Nat → Cell → Set
WsCell m c = WsTm m (fst c) × WsTy m (snd c)

WsL : Nat → List Tm → Set
WsL m []       = ⊤
WsL m (t ∷ ts) = WsTm m t × WsL m ts

private
  ws-++ : ∀ m xs ys → WsL m xs → WsL m ys → WsL m (xs ++ ys)
  ws-++ m []       ys _        q = q
  ws-++ m (x ∷ xs) ys (px , p) q = px , ws-++ m xs ys p q

  ws-subGo : ∀ m σ ts → WsSub m σ → WsL m ts → WsSub m (subGo σ ts)
  ws-subGo m σ []       p _        = p
  ws-subGo m σ (t ∷ ts) p (pt , q) = ws-subGo m (σ ,ₛ t) ts (p , pt) q

  ws-src : ∀ m c → WsCell m c → WsCell m (srcC c)
  ws-src m (x , ⋆)       w                   = w
  ws-src m (x , arr A s t) (_ , (wA , ws , _)) = ws , wA

  ws-tgt : ∀ m c → WsCell m c → WsCell m (tgtC c)
  ws-tgt m (x , ⋆)       w                   = w
  ws-tgt m (x , arr A s t) (_ , (wA , _ , wt)) = wt , wA

  ws-disk : ∀ m n c → WsCell m c → WsL m (CaTTExp.Cones.diskGo n c)
  ws-disk m zero    c w = fst w , tt
  ws-disk m (suc n) c w =
    ws-++ m _ _ (ws-disk m n (srcC c) (ws-src m c w)) (fst (ws-tgt m c w) , fst w , tt)

  ws-rest : ∀ m k n c → WsCell m c → WsL m (CaTTExp.Cones.restGo k n c)
  ws-rest m k zero    c w = tt
  ws-rest m k (suc n) c w with dimC c ==ℕ k
  ... | true  = tt
  ... | false = ws-++ m _ _ (ws-rest m k n (srcC c) (ws-src m c w)) (fst (ws-tgt m c w) , fst w , tt)

  ws-binC : ∀ m k u w → WsCell m u → WsCell m w → WsTm m (fst (CaTTExp.Cones.binC k u w))
  ws-binC m k u w wu ww =
    ws-subGo m ⟨⟩ _ tt (ws-++ m _ _ (ws-disk m (dimC u) u wu) (ws-rest m k (dimC w) w ww))

  ws-lo : ∀ m r c → WsCell m c → WsCell m (CaTTExp.Lim.ConeCells.loC r c)
  ws-lo m r c w with dimC c <ℕ r
  ... | true  = w
  ... | false = ws-src m c w

  ws-hi : ∀ m r c → WsCell m c → WsCell m (CaTTExp.Lim.ConeCells.hiC r c)
  ws-hi m r c w with dimC c <ℕ r
  ... | true  = w
  ... | false = ws-tgt m c w

  ws-bty : ∀ m r k u w → WsCell m u → WsCell m w → WsTy m (CaTTExp.Lim.ConeCells.btyR r k u w)
  ws-bty m zero     k u w wu ww = tt
  ws-bty m (suc r′) k u w wu ww with r′ ==ℕ k
  ... | true  = snd (ws-src m u wu) , fst (ws-src m u wu) , fst (ws-tgt m w ww)
  ... | false =
    ws-bty m r′ k lu lw wlu wlw , ws-binC m k lu lw wlu wlw ,
    ws-binC m k (CaTTExp.Lim.ConeCells.hiC (suc r′) u) (CaTTExp.Lim.ConeCells.hiC (suc r′) w)
            (ws-hi m (suc r′) u wu) (ws-hi m (suc r′) w ww)
    where
    lu = CaTTExp.Lim.ConeCells.loC (suc r′) u
    lw = CaTTExp.Lim.ConeCells.loC (suc r′) w
    wlu = ws-lo m (suc r′) u wu
    wlw = ws-lo m (suc r′) w ww

ws-bcell : ∀ m k u w → WsCell m u → WsCell m w → WsCell m (CaTTExp.Lim.ConeCells.bcell k u w)
ws-bcell m k u w wu ww = ws-binC m k u w wu ww , ws-bty m (max (dimC u) (dimC w)) k u w wu ww

AllWs : Nat → List Cell → Set
AllWs m []       = ⊤
AllWs m (c ∷ cs) = WsCell m c × AllWs m cs

ws-chain : ∀ m Ps c → AllWs m Ps → WsCell m c → WsCell m (chainF Ps c)
ws-chain m []       c _        wc = wc
ws-chain m (P ∷ Ps) c (wP , w) wc = ws-bcell m (lenL Ps) P (chainF Ps c) wP (ws-chain m Ps c w wc)

module WsProj (n : Nat) (pn : Nat → Nat) (m : Nat) (nm : T (n <ℕ m)) where
  open Proj n pn

  -- The projections of the boundaries are in scope.
  PvOK : Ty → Set
  PvOK ⋆           = ⊤
  PvOK (arr B s t) = (WsTm m (pv s) × WsTm m (pv t)) × PvOK B

  mutual
    ws-projN : ∀ x A → WsTm m x → WsTy m A → PvOK A → WsTy m (projN x A)
    ws-projN x ⋆           wx _                pA = tt , nm , wx
    ws-projN x (arr B s t) wx (wB , ws , wt) ((wps , wpt) , pB) =
      ws-projN t B wt wB pB , wpt ,
      fst (ws-chain m (pcs (arr B s t)) (x , arr B s t) (ws-pcs (arr B s t) (wB , ws , wt) ((wps , wpt) , pB))
                    (wx , wB , ws , wt))

    ws-pcs : ∀ A → WsTy m A → PvOK A → AllWs m (pcs A)
    ws-pcs ⋆           _              _               = tt
    ws-pcs (arr B s t) (wB , ws , wt) ((wps , wpt) , pB) = (wps , ws-projN s B ws wB pB) , ws-pcs B wB pB

------------------------------------------------------------------------
-- The repaired side: Lim/Repaired's coneC on the canonically named
-- diagram, lowered, is the explicit cone.

-- Prefixes of a context.
data Pfx (Γ : Ctx) : Ctx → Set where
  top  : Pfx Γ Γ
  drop : ∀ {Δ A} → Pfx Γ (Δ ▸ A) → Pfx Γ Δ

pfx-le : ∀ {Γ Δ} → Pfx Γ Δ → Le (len Δ) (len Γ)
pfx-le {Γ} top = le-refl (len Γ)
pfx-le {Γ} (drop {Δ} {A} p) = le-trans (len Δ) (suc (len Δ)) (len Γ) (le-suc (len Δ)) (pfx-le p)

pfx-nth : ∀ {Γ Δ} → Pfx Γ Δ → ∀ j → T (j <ℕ len Δ) → nth ⋆ (tyList Γ) j ≡ nth ⋆ (tyList Δ) j
pfx-nth top      j q = refl
pfx-nth {Γ} (drop {Δ} {A} p) j q =
  trans (pfx-nth p j (<-suc j (len Δ) q))
        (nth-app-l ⋆ (tyList Δ) (A ∷ []) j (subst (λ a → T (j <ℕ a)) (sym (len-tyList Δ)) q))

pfx-at : ∀ {Γ Δ A} → Pfx Γ (Δ ▸ A) → nth ⋆ (tyList Γ) (len Δ) ≡ A
pfx-at {Γ} {Δ} {A} p =
  trans (pfx-nth p (len Δ) (n<suc (len Δ)))
        (trans (cong (nth ⋆ (tyList Δ ++ (A ∷ []))) (sym (len-tyList Δ))) (nth-last ⋆ (tyList Δ) A))

module NS (Γ : Ctx) (w : T (gwf Γ)) where
  G : List Ty
  G = tyList Γ

  n : Nat
  n = len Γ

  hn : length G ≡ n
  hn = len-tyList Γ

  wfG : WF G
  wfG = gwf-sound Γ w

  open QM G n

  okAt : ∀ {Δ A} → Pfx Γ (Δ ▸ A) → OkT G (len Δ) A
  okAt {Δ} {A} p =
    subst (OkT G (len Δ)) (pfx-at p)
          (wfG (len Δ) (subst (λ a → T (len Δ <ℕ a)) (sym hn) (pfx-le p)))

  ltAt : ∀ {Δ A} → Pfx Γ (Δ ▸ A) → T (len Δ <ℕ n)
  ltAt p = pfx-le p

  Γn : NCtx
  Γn = named Γ

  pn : Nat → Nat
  pn = R.pName Γn n

  pn-ok : ∀ a → T (a <ℕ n) → pn a ≡ P a
  pn-ok a q rewrite levelOf-named Γ a q = refl

  -- projN only uses the projection names of the boundaries.
  module _ (pn′ : Nat → Nat) (i : Nat) (h : ∀ a → T (a <ℕ i) → pn′ a ≡ P a) where
    mutual
      pN-cong : ∀ {A} → OkT G i A → ∀ x → Proj.projN n pn′ x A ≡ projN x A
      pN-cong ok⋆ x = refl
      pN-cong (okA {A} {s} {t} qs qt es et ok) x =
        cong₂ (λ a bc → arr a (fst bc) (fst (chainF (snd bc) (x , arr A (var s) (var t)))))
              (pN-cong ok (var t))
              (cong₂ _,_ (cong var (h t qt)) (pcs-cong (okA qs qt es et ok)))

      pcs-cong : ∀ {A} → OkT G i A → Proj.pcs n pn′ A ≡ pcs A
      pcs-cong ok⋆ = refl
      pcs-cong (okA {A} {s} {t} qs qt es et ok) =
        cong₂ _∷_ (cong₂ _,_ (cong var (h s qs)) (pN-cong ok (var s))) (pcs-cong ok)

  globTy-ok : ∀ {i A} → OkT G i A → R.globTy A ≡ true
  globTy-ok ok⋆              = refl
  globTy-ok (okA _ _ _ _ ok) = globTy-ok ok

  Πn : Ctx → NCtx
  Πn ε       = ∅
  Πn (Δ ▸ A) = Πn Δ ▹ P (len Δ) ∶ projEnt (len Δ)

  coneWith-ok : ∀ Δ → Pfx Γ Δ → R.coneWith n pn (named Δ) ≡ just (Πn Δ)
  coneWith-ok ε       p = refl
  coneWith-ok (Δ ▸ A) p
    rewrite coneWith-ok Δ (drop p) | globTy-ok (okAt p)
          | pN-cong pn (len Δ) (λ a q → pn-ok a (<-trans a (len Δ) n q (ltAt p))) (okAt p) (var (len Δ))
          | pn-ok (len Δ) (ltAt p) =
    cong (λ X → just (Πn Δ ▹ P (len Δ) ∶ projN (var (len Δ)) X)) (sym (pfx-at p))

  -- The explicit cone with its first m projections.
  Qm : Nat → Ctx
  Qm m = ctxGo (Γ ▸ ⋆) (pl 0 m)

  private
    pl-snoc : ∀ k m → pl k (suc m) ≡ pl k m ++ (projEnt (k + m) ∷ [])
    pl-snoc k zero    = cong (λ a → projEnt a ∷ []) (sym (+-zero k))
    pl-snoc k (suc m) = cong (projEnt k ∷_) (trans (pl-snoc (suc k) m) (cong (λ a → pl (suc k) m ++ (projEnt a ∷ [])) (sym (+-suc k m))))

    len-ctxGo : ∀ acc As → len (ctxGo acc As) ≡ len acc + length As
    len-ctxGo acc []       = sym (+-zero (len acc))
    len-ctxGo acc (A ∷ As) = trans (len-ctxGo (acc ▸ A) As) (sym (+-suc (len acc) (length As)))

    len-pl′ : ∀ k m → length (pl k m) ≡ m
    len-pl′ k zero    = refl
    len-pl′ k (suc m) = cong suc (len-pl′ (suc k) m)

    ctxGo-++ : ∀ acc As Bs → ctxGo acc (As ++ Bs) ≡ ctxGo (ctxGo acc As) Bs
    ctxGo-++ acc []       Bs = refl
    ctxGo-++ acc (A ∷ As) Bs = ctxGo-++ (acc ▸ A) As Bs

  Qm-suc : ∀ m → Qm (suc m) ≡ Qm m ▸ projEnt m
  Qm-suc m = trans (cong (ctxGo (Γ ▸ ⋆)) (pl-snoc 0 m)) (ctxGo-snoc (Γ ▸ ⋆) (pl 0 m) (projEnt m))

  len-Qm : ∀ m → len (Qm m) ≡ P m
  len-Qm m = trans (len-ctxGo (Γ ▸ ⋆) (pl 0 m)) (cong (λ a → suc (n + a)) (len-pl′ 0 m))

  Qc-Qm : Qc ≡ Qm n
  Qc-Qm = trans (ctxGo-++ ε G (⋆ ∷ pl 0 n)) (cong (λ D → ctxGo (D ▸ ⋆) (pl 0 n)) (ctx-tyList Γ))

  ⧺-ok : ∀ Δ → (Γn ▹ n ∶ ⋆) ⧺ Πn Δ ≡ named (Qm (len Δ))
  ⧺-ok ε       = refl
  ⧺-ok (Δ ▸ A) =
    trans (cong₂ (λ K a → K ▹ a ∶ projEnt (len Δ)) (⧺-ok Δ) (sym (len-Qm (len Δ))))
          (cong named (sym (Qm-suc (len Δ))))

  -- Scoping of the explicit cone.
  private
    ws-okT : ∀ i m {A} → OkT G i A → Le i m → WsTy m A
    ws-okT i m ok⋆ _ = tt
    ws-okT i m (okA {A} {s} {t} qs qt _ _ ok) le =
      ws-okT i m ok le , lt s qs , lt t qt
      where
      lt : ∀ j → T (j <ℕ i) → T (j <ℕ m)
      lt j q = le-lt j m (le-trans (suc j) i m (lt-le j i q) le)

    pv-okT : ∀ i {A} → OkT G i A → WsProj.PvOK n P (P i) (le-add n i) A
    pv-okT i ok⋆ = tt
    pv-okT i (okA qs qt _ _ ok) = (lt-add n qs , lt-add n qt) , pv-okT i ok

  sc-Γ : ∀ Δ → Pfx Γ Δ → ScC Δ
  sc-Γ ε       p = tt
  sc-Γ (Δ ▸ A) p = sc-Γ Δ (drop p) , ws-okT (len Δ) (len Δ) (okAt p) (le-refl (len Δ))

  sc-Qm : ∀ m → Le m n → ScC (Qm m)
  sc-Qm zero    _ = sc-Γ Γ top , tt
  sc-Qm (suc m) q =
    subst ScC (sym (Qm-suc m))
      (sc-Qm m (le-trans m (suc m) n (le-suc m) q) ,
       subst (λ a → WsTy a (projEnt m)) (sym (len-Qm m))
             (WsProj.ws-projN n P (P m) nm (var m) (nth ⋆ G m) (le-+l′ n m)
                              (ws-okT m (P m) okm (le-trans m (suc m) (P m) (le-suc m) (lt-le m (P m) (le-+l′ n m))))
                              (pv-okT m okm)))
    where
    nm : T (n <ℕ P m)
    nm = le-add n m
    le-+l′ : ∀ n m → T (m <ℕ suc (n + m))
    le-+l′ n m = CaTTExp.Lim.ConesEval.le-+l n m
    okm : OkT G m (nth ⋆ G m)
    okm = wfG m (subst (λ a → T (m <ℕ a)) (sym hn) q)

  -- The specified cone, lowered, is the explicit cone.
  specified-ok : (R.coneC Γn n >>= λ Π → lower (coneCtx Γn n Π)) ≡ just Qc
  specified-ok rewrite coneWith-ok Γ top | ⧺-ok Γ =
    trans (lower-named (Qm n) (sc-Qm n (le-refl n))) (cong just (sym Qc-Qm))

------------------------------------------------------------------------
-- The theorem.

-- For every well-formed globular diagram Γ, in every dimension, the
-- repaired cone (named canonically, apex the next name, lowered) is
-- the kernel's cone shape; both are the explicit cone.
cone-is-explicit : ∀ Γ (w : T (gwf Γ)) →
  (R.coneC (named Γ) (len Γ) >>= λ Π → lower (coneCtx (named Γ) (len Γ) Π))
  ≡ just (QM.Qc (tyList Γ) (len Γ))
cone-is-explicit Γ w = NS.specified-ok Γ w

shape-is-explicit : ∀ Γ (w : T (gwf Γ)) →
  (lower (named Γ) >>= coneShape) ≡ just (QM.Qc (tyList Γ) (len Γ))
shape-is-explicit Γ w rewrite lower-named Γ (NS.sc-Γ Γ w Γ top) = shape-ok Γ w

cone-agrees : ∀ Γ → T (gwf Γ) →
  (R.coneC (named Γ) (len Γ) >>= λ Π → lower (coneCtx (named Γ) (len Γ) Π))
  ≡ (lower (named Γ) >>= coneShape)
cone-agrees Γ w = trans (cone-is-explicit Γ w) (sym (shape-is-explicit Γ w))

------------------------------------------------------------------------
-- Instances: Mikhail's Example 4.1 (x, y, f g : x → y, α : f ⇒ g), the
-- loop, and a 3-dimensional cell between parallel 2-cells are covered;
-- an ill-typed 2-cell and a non-globular boundary are not.

private
  Γ41 : Ctx
  Γ41 = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
          ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)

  _ = cone-agrees Γ41 tt

  Γloop : Ctx
  Γloop = ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0) ▸ arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)

  _ = cone-agrees Γloop tt

  -- x, y, f g : x → y, α β : f ⇒ g, Θ : α ⇛ β.
  Γ3 : Ctx
  Γ3 = Γ41 ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)
           ▸ arr (arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)) (var 4) (var 5)

  _ = cone-agrees Γ3 tt

  -- α : f ⇒ g with f : x → y but g : y → x.
  _ : gwf (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 1) (var 0)
             ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3)) ≡ false
  _ = refl
