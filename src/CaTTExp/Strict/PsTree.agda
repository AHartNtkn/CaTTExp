------------------------------------------------------------------------
-- The labelled tree of a pasting context (ledger item A3a, general
-- case).
--
-- `tr Θ` is the Batanin tree of Θ with each position labelled by its
-- variable. It is computed from the raw context by reading the (y, f)
-- pairs in order: the pair y : A, f : x → y adds the branch (f, y) at
-- the end of the rightmost node at height dim A. In a pasting context
-- that node ends with x (`tr-rm`), so this is the tree the pse/psd
-- rules describe.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega using (_≤_; _<_; z≤n; s≤s)
open import CaTTExp.Strict.Trees

module CaTTExp.Strict.PsTree (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊

------------------------------------------------------------------------
-- Insertion at the end of the rightmost node at height n.

mutual
  insert : Nat → Nat → Nat → LT Nat → LT Nat
  insert zero    y f (node s br) = node s (br ++B cons (node f nil) y nil)
  insert (suc n) y f (node s br) = node s (insLast n y f br)

  insLast : Nat → Nat → Nat → Br Nat → Br Nat
  insLast n y f nil                         = nil
  insLast n y f (cons T z nil)              = cons (insert n y f T) z nil
  insLast n y f (cons T z (cons T′ z′ r))   = cons T z (insLast n y f (cons T′ z′ r))

tr : Ctx → LT Nat
tr ε             = node 0 nil
tr (ε ▸ _)       = node 0 nil
tr (Γ ▸ A ▸ B)   = insert (dim A) (len Γ) (suc (len Γ)) (tr Γ)

------------------------------------------------------------------------
-- The rightmost node at height k ends with x.

mutual
  RM : Nat → LT Nat → Nat → Set
  RM zero    (node s br) x = lastv s br ≡ x
  RM (suc k) (node s br) x = RMB k br x

  RMB : Nat → Br Nat → Nat → Set
  RMB k nil                       x = ⊥
  RMB k (cons T z nil)            x = RM k T x
  RMB k (cons T z (cons T′ z′ r)) x = RMB k (cons T′ z′ r) x

private
  lastv-++1 : ∀ s (br : Br Nat) T y → lastv s (br ++B cons T y nil) ≡ y
  lastv-++1 s nil          T y = refl
  lastv-++1 s (cons U z r) T y = lastv-++1 z r T y

  rmb-snoc : ∀ k (br : Br Nat) T y x → RM k T x → RMB k (br ++B cons T y nil) x
  rmb-snoc k nil                       T y x p = p
  rmb-snoc k (cons U z nil)            T y x p = p
  rmb-snoc k (cons U z (cons U′ z′ r)) T y x p = rmb-snoc k (cons U′ z′ r) T y x p

  lastv-insLast : ∀ n y f s (br : Br Nat) → lastv s (insLast n y f br) ≡ lastv s br
  lastv-insLast n y f s nil                       = refl
  lastv-insLast n y f s (cons T z nil)            = refl
  lastv-insLast n y f s (cons T z (cons T′ z′ r)) = lastv-insLast n y f z (cons T′ z′ r)

mutual
  rm-ins-top : ∀ n T x y f → RM n T x → RM (suc n) (insert n y f T) f
  rm-ins-top zero    (node s br) x y f p = rmb-snoc 0 br (node f nil) y f refl
  rm-ins-top (suc n) (node s br) x y f p = rmB-ins-top n br x y f p

  rmB-ins-top : ∀ n br x y f → RMB n br x → RMB (suc n) (insLast n y f br) f
  rmB-ins-top n nil                       x y f ()
  rmB-ins-top n (cons T z nil)            x y f p = rm-ins-top n T x y f p
  rmB-ins-top n (cons T z (cons T′ z′ nil)) x y f p = rmB-ins-top n (cons T′ z′ nil) x y f p
  rmB-ins-top n (cons T z (cons T′ z′ (cons T″ z″ r))) x y f p = rmB-ins-top n (cons T′ z′ (cons T″ z″ r)) x y f p

mutual
  rm-ins-same : ∀ n T x y f → RM n T x → RM n (insert n y f T) y
  rm-ins-same zero    (node s br) x y f p = lastv-++1 s br (node f nil) y
  rm-ins-same (suc n) (node s br) x y f p = rmB-ins-same n br x y f p

  rmB-ins-same : ∀ n br x y f → RMB n br x → RMB n (insLast n y f br) y
  rmB-ins-same n nil                       x y f ()
  rmB-ins-same n (cons T z nil)            x y f p = rm-ins-same n T x y f p
  rmB-ins-same n (cons T z (cons T′ z′ nil)) x y f p = rmB-ins-same n (cons T′ z′ nil) x y f p
  rmB-ins-same n (cons T z (cons T′ z′ (cons T″ z″ r))) x y f p = rmB-ins-same n (cons T′ z′ (cons T″ z″ r)) x y f p

mutual
  rm-ins-low : ∀ {j n} T z y f → j < n → RM j T z → RM j (insert n y f T) z
  rm-ins-low {zero}  {suc n} (node s br) z y f _ p = trans (lastv-insLast n y f s br) p
  rm-ins-low {suc j} {suc n} (node s br) z y f (s≤s l) p = rmB-ins-low br z y f l p

  rmB-ins-low : ∀ {j n} br z y f → j < n → RMB j br z → RMB j (insLast n y f br) z
  rmB-ins-low nil                       z y f l ()
  rmB-ins-low (cons T w nil)            z y f l p = rm-ins-low T z y f l p
  rmB-ins-low (cons T w (cons T′ w′ nil)) z y f l p = rmB-ins-low (cons T′ w′ nil) z y f l p
  rmB-ins-low (cons T w (cons T′ w′ (cons T″ w″ r))) z y f l p = rmB-ins-low (cons T′ w′ (cons T″ w″ r)) z y f l p

------------------------------------------------------------------------
-- The whole rightmost path of the tree of a context under construction
-- follows the dangling variable and its iterated targets.

RMT : LT Nat → Nat → Ty → Set
RMT T x ⋆                         = RM 0 T x
RMT T x (arr B (var a) (var b))   = RM (suc (dim B)) T x × RMT T b B
RMT T x (arr B (var a) (coh _ _ _)) = ⊥
RMT T x (arr B (var a) (cst _))   = ⊥
RMT T x (arr B (coh _ _ _) _)     = ⊥
RMT T x (arr B (cst _) _)         = ⊥

rmt-top : ∀ T x A → RMT T x A → RM (dim A) T x
rmt-top T x ⋆                       p = p
rmt-top T x (arr B (var a) (var b)) p = fst p

private
  ≤-refl′ : ∀ n → n ≤ n
  ≤-refl′ zero    = z≤n
  ≤-refl′ (suc n) = s≤s (≤-refl′ n)

  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step z≤n     = z≤n
  ≤-step (s≤s p) = s≤s (≤-step p)

rmt-low : ∀ T z y f B n → dim B < n → RMT T z B → RMT (insert n y f T) z B
rmt-low T z y f ⋆                       n l p = rm-ins-low T z y f l p
rmt-low T z y f (arr B (var a) (var b)) n l (p , q) =
  rm-ins-low T z y f l p , rmt-low T b y f B n (≤-step′ l) q
  where
  ≤-step′ : ∀ {m n} → suc m < n → m < n
  ≤-step′ (s≤s p) = ≤-step p

rmt-ins : ∀ T x y f A → RMT T x A → RMT (insert (dim A) y f T) y A
rmt-ins T x y f ⋆                       p = rm-ins-same 0 T x y f p
rmt-ins T x y f (arr B (var a) (var b)) (p , q) =
  rm-ins-same (suc (dim B)) T x y f p , rmt-low T b y f B (suc (dim B)) (≤-refl′ (suc (dim B))) q

tr-rm : ∀ {Γ x A} → Γ ⊢ps x ∶ A → RMT (tr Γ) x A
tr-rm pss = refl
tr-rm (pse {Γ} {x} {A} d) =
  rm-ins-top (dim A) (tr Γ) x (len Γ) (suc (len Γ)) (rmt-top (tr Γ) x A (tr-rm d)) ,
  rmt-ins (tr Γ) x (len Γ) (suc (len Γ)) A (tr-rm d)
tr-rm (psd d) = snd (tr-rm d)
