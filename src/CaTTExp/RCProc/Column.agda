------------------------------------------------------------------------
-- Chains and columns as pasting trees (ledger S20 (i), stage 3c).
--
-- The chain tree `chainT N` (N leaves) builds the context
-- `chainFrom (ε ▸ ⋆) 0 N`, a chain of N edges; raising its leaf m
-- (flags `falses m ++ true ∷ []`) gives the column tree
-- `leaves m ++ col ∷ leaves n`, whose context is the chain of m edges,
-- then a 2-disc α : f ⇒ f′ (`PsRaise.Raised`), then a chain of n edges
-- (`col-ctx`). These are the contexts P_g of a whiskered generator
-- (notes/relative-coherence.md §2 Step 3).
------------------------------------------------------------------------
module CaTTExp.RCProc.Column where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Lift using (raiseL; raiseT)
open import CaTTExp.PsRaise using (Raised)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx; len-chain; +-suc; +-zero)

leaves : Nat → List Tree
leaves zero    = []
leaves (suc n) = node [] ∷ leaves n

col : Tree
col = node (node [] ∷ [])

falses : Nat → List Bool
falses zero    = []
falses (suc m) = false ∷ falses m

-- The flags raising leaf m.
flagAt : Nat → List Bool
flagAt m = falses m ++ (true ∷ [])

-- The context and point reached by n more chain steps from (Γ, x).
chainFrom : Ctx → Nat → Nat → Ctx
chainFrom Γ x zero    = Γ
chainFrom Γ x (suc n) = chainFrom (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n

endFrom : Ctx → Nat → Nat → Nat
endFrom Γ x zero    = x
endFrom Γ x (suc n) = endFrom (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n

------------------------------------------------------------------------
-- What the builder does.

private
  -- buildList on a concatenation.
  build-++ : ∀ xs ys {Γ x A} (d : Γ ⊢ps x ∶ A) →
             buildList (xs ++ ys) d ≡ buildList ys (snd (snd (buildList xs d)))
  build-++ []       ys d = refl
  build-++ (t ∷ xs) ys d = build-++ xs ys (psd (snd (snd (build t (pse d)))))

build-leaves : ∀ n {Γ x} (d : Γ ⊢ps x ∶ ⋆) →
               (fst (buildList (leaves n) d) ≡ chainFrom Γ x n) × (fst (snd (buildList (leaves n) d)) ≡ endFrom Γ x n)
build-leaves zero    d = refl , refl
build-leaves (suc n) d = build-leaves n (psd (pse d))

------------------------------------------------------------------------
-- The chain tree and its raised column.

chainT : Nat → Tree
chainT N = node (leaves N)

C₀ : Nat → Ctx
C₀ m = chainFrom (ε ▸ ⋆) 0 m

e₀ : Nat → Nat
e₀ m = endFrom (ε ▸ ⋆) 0 m

chain-ctx : ∀ N → ctxOf (chainT N) ≡ C₀ N
chain-ctx N = fst (build-leaves N pss)

-- The column context: m chain edges, a 2-disc, n chain edges.
colCtx : Nat → Nat → Ctx
colCtx m n = chainFrom (Raised (C₀ m) (e₀ m) ⋆) (len (C₀ m)) n

private
  raiseL-[] : ∀ n → fst (raiseL [] (leaves n)) ≡ leaves n
  raiseL-[] zero    = refl
  raiseL-[] (suc n) = cong (node [] ∷_) (raiseL-[] n)

  raiseT-node : ∀ m ts → raiseT (flagAt m) (node (node [] ∷ ts)) ≡ node (fst (raiseL (flagAt m) (node [] ∷ ts)))
  raiseT-node zero    ts = refl
  raiseT-node (suc m) ts = refl

raise-leaves : ∀ m n → fst (raiseL (flagAt m) (leaves (suc (m + n)))) ≡ leaves m ++ col ∷ leaves n
raise-leaves zero    n = cong (col ∷_) (raiseL-[] n)
raise-leaves (suc m) n = cong (node [] ∷_) (raise-leaves m n)

raised-ctx : ∀ m n → ctxOf (raiseT (flagAt m) (chainT (suc (m + n)))) ≡ colCtx m n
raised-ctx m n =
  trans (cong ctxOf (trans (raiseT-node m (leaves (m + n))) (cong node (raise-leaves m n))))
    (trans (cong fst (build-++ (leaves m) (col ∷ leaves n) pss))
      (trans (fst (build-leaves n (psd (psd (pse (pse dm))))))
        (cong₂ (λ Γ x → chainFrom (Raised Γ x ⋆) (len Γ) n) (fst bm) (snd bm))))
  where
  dm = snd (snd (buildList (leaves m) pss))
  bm = build-leaves m pss

-- The chain built by the builder is GraphFillerTotal's chainC.
chain-eq : ∀ n k → (chainFrom (chainC k) (vtx k) n ≡ chainC (n + k)) × (endFrom (chainC k) (vtx k) n ≡ vtx (n + k))
chain-eq zero    k = refl , refl
chain-eq (suc n) k rewrite len-chain k =
  trans (fst (chain-eq n (suc k))) (cong chainC (+-suc n k)) ,
  trans (snd (chain-eq n (suc k))) (cong vtx (+-suc n k))

C₀-chainC : ∀ N → C₀ N ≡ chainC N
C₀-chainC N = trans (fst (chain-eq N 0)) (cong chainC (+-zero N))

e₀-vtx : ∀ N → e₀ N ≡ vtx N
e₀-vtx N = trans (snd (chain-eq N 0)) (cong vtx (+-zero N))
