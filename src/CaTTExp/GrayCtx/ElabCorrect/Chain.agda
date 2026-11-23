------------------------------------------------------------------------
-- Elab.vcomp on 1-cells is correct for every length (ledger S20 (ii)).
--
-- The tree of an n-fold composite of 1-cells is the chain
-- node (replicate n leaf); its context is the chain context chainC n,
-- its locally maximal variables are the n edges, and the composite's
-- source and target are the first and last objects. The ShapeOK facts
-- are proved here by induction on n, not by computation per length.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Chain where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
  using (replicate; tops; topsF; vT; vcompB; vFirst; vLast; srcTgtVar; vcomp; length; dimOf; tyOf; cohT; _<$>_)
open import CaTTExp.GraphFillerTotal.Chains
  using (chainC; vtx; dbl; edge; len-chain; chainC-ps; chainC-wf; src-chain; tgt-chain;
         _≤_; _<_; z≤n; s≤s; ≤-refl; ≤-step; ≤-trans; ≤-pred; +-zero; +-suc;
         <→T; T→<; lookup-vtx; lookup-edge; edge-<; Parity; isVtx; isEdge; parity)
open import CaTTExp.GrayCtx.ElabCorrect.Fill
  using (covers; allBelow; allLtB; memN; bkeys; bvars; lookupTy; mapL; bind-just; tyOf-typed)
open import CaTTExp.GrayCtx.ElabCorrect.Coh
open import CaTTExp.Derived using (ps-ctx)
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S

-- Building n leaves onto a chain extends the chain.
build-chain : ∀ n m {Γ x} (d : Γ ⊢ps x ∶ ⋆) → Γ ≡ chainC m → x ≡ vtx m →
              fst (buildList (replicate n leaf) d) ≡ chainC (n + m)
build-chain zero    m d e _ = e
build-chain (suc n) m d refl refl =
  trans (build-chain n (suc m) (psd (pse d))
           (cong (λ k → chainC m ▸ ⋆ ▸ arr ⋆ (var (vtx m)) (var k)) (len-chain m))
           (len-chain m))
        (cong chainC (+-suc n m))

ctx-chain : ∀ n → ctxOf (node (replicate n leaf)) ≡ chainC n
ctx-chain n = trans (build-chain n 0 pss refl refl) (cong chainC (+-zero n))

------------------------------------------------------------------------
-- The locally maximal variables: the edges e_{i+1}, …, e_{i+n}.

eF : Nat → Nat → List Nat
eF i zero    = []
eF i (suc n) = dbl (suc i) ∷ eF (suc i) n

topsF-chain : ∀ i n → fst (topsF (suc (dbl i)) (replicate n leaf)) ≡ eF i n
topsF-chain i zero    = refl
topsF-chain i (suc n) = cong (dbl (suc i) ∷_) (topsF-chain (suc i) n)

tops-chain : ∀ m → tops (node (replicate (suc m) leaf)) ≡ eF 0 (suc m)
tops-chain m = topsF-chain 0 (suc m)

vLast-eF : ∀ i n → vLast (eF i (suc n)) ≡ just (dbl (suc (n + i)))
vLast-eF i zero    = refl
vLast-eF i (suc n) = trans (vLast-eF (suc i) n) (cong (λ k → just (dbl (suc k))) (+-suc n i))

------------------------------------------------------------------------
-- Booleans.

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  ∨-inr : ∀ a {b} → T b → T (a ∨ b)
  ∨-inr true  _ = tt
  ∨-inr false q = q

  mem-here : ∀ k ks → T (memN k (k ∷ ks))
  mem-here k ks with k ==ℕ k | ==ℕ-refl k
  ... | true | _ = tt

  mem-there : ∀ k m ks → T (memN k ks) → T (memN k (m ∷ ks))
  mem-there k m ks h = ∨-inr (k ==ℕ m) h

  mem-++l : ∀ k xs ys → T (memN k xs) → T (memN k (xs ++ ys))
  mem-++l k (x ∷ xs) ys h with k ==ℕ x
  ... | true  = tt
  ... | false = mem-++l k xs ys h

  mem-++r : ∀ k xs ys → T (memN k ys) → T (memN k (xs ++ ys))
  mem-++r k []       ys h = h
  mem-++r k (x ∷ xs) ys h = mem-there k x (xs ++ ys) (mem-++r k xs ys h)

  allBelow-intro : ∀ f n → (∀ k → k < n → T (f k)) → T (allBelow f n)
  allBelow-intro f zero    h = tt
  allBelow-intro f (suc n) h = ∧-intro (allBelow-intro f n (λ k p → h k (≤-step p))) (h n ≤-refl)

  single-≈ : ∀ x → T (≈? (x ∷ []) (x ∷ []))
  single-≈ x with x ==ℕ x | ==ℕ-refl x
  ... | true | _ = tt

------------------------------------------------------------------------
-- Order facts on vertex and edge positions.

private
  dbl-r : ∀ j K → suc (dbl j) ≤ dbl K → j < K
  dbl-r j       zero    ()
  dbl-r zero    (suc K) _ = s≤s z≤n
  dbl-r (suc j) (suc K) (s≤s (s≤s p)) = s≤s (dbl-r j K p)

  vtx-r : ∀ j K → vtx (suc j) < vtx (suc K) → j < K
  vtx-r j K (s≤s p) = dbl-r j K p

  edge-r : ∀ j K → edge (suc j) < vtx (suc K) → j < K
  edge-r j K (s≤s p) = dbl-r j K (≤-trans (≤-step ≤-refl) p)

  +≤ : ∀ i n K → i + suc n ≤ K → i < K
  +≤ zero    n (suc K) _       = s≤s z≤n
  +≤ (suc i) n (suc K) (s≤s p) = s≤s (+≤ i n K p)

lookupTy-edge : ∀ K i → i < K →
  lookupTy (chainC K) (edge (suc i)) ≡ arr ⋆ (var (vtx i)) (var (vtx (suc i)))
lookupTy-edge K i h rewrite lookup-edge K i h = refl

------------------------------------------------------------------------
-- Coverage.

memEF : ∀ i n d → d < n → T (memN (dbl (suc (d + i))) (eF i n))
memEF i (suc n) zero    _       = mem-here (dbl (suc i)) (eF (suc i) n)
memEF i (suc n) (suc d) (s≤s p) =
  mem-there (dbl (suc (suc d + i))) (dbl (suc i)) (eF (suc i) n)
    (subst (λ k → T (memN (dbl (suc k)) (eF (suc i) n))) (+-suc d i) (memEF (suc i) n d p))

bkT : ∀ K i n d → d < n → i + n ≤ K → T (memN (vtx (suc (d + i))) (bkeys (chainC K) (eF i n)))
bkT K i (suc n) zero _ q rewrite lookupTy-edge K i (+≤ i n K q) =
  mem-++l (vtx (suc i)) (vtx i ∷ vtx (suc i) ∷ []) (bkeys (chainC K) (eF (suc i) n))
    (mem-there (vtx (suc i)) (vtx i) (vtx (suc i) ∷ []) (mem-here (vtx (suc i)) []))
bkT K i (suc n) (suc d) (s≤s p) q =
  mem-++r _ (bvars (lookupTy (chainC K) (dbl (suc i)))) _
    (subst (λ k → T (memN (vtx (suc k)) (bkeys (chainC K) (eF (suc i) n)))) (+-suc d i)
      (bkT K (suc i) n d p (subst (_≤ K) (+-suc i n) q)))

bk0 : ∀ K n → 0 < n → n ≤ K → T (memN 0 (bkeys (chainC K) (eF 0 n)))
bk0 K (suc n) _ q rewrite lookupTy-edge K 0 (+≤ 0 n K q) = mem-here 0 (1 ∷ bkeys (chainC K) (eF 1 n))

allLt-eF : ∀ K i n → i + n ≤ K → T (allLtB (eF i n) (vtx (suc K)))
allLt-eF K i zero    _ = tt
allLt-eF K i (suc n) q =
  ∧-intro (<→T (edge-< (+≤ i n K q))) (allLt-eF K (suc i) n (subst (_≤ K) (+-suc i n) q))

cover-chain : ∀ K → 0 < K → T (covers (chainC K) (eF 0 K))
cover-chain K pos rewrite len-chain K =
  ∧-intro (allLt-eF K 0 K ≤-refl)
          (allBelow-intro _ (vtx (suc K)) λ k p → go k (parity k) p)
  where
  ks = eF 0 K
  go : ∀ k → Parity k → k < vtx (suc K) → T (memN k (ks ++ bkeys (chainC K) ks))
  go _ (isVtx zero)    _ = mem-++r 0 ks _ (bk0 K K pos ≤-refl)
  go _ (isVtx (suc j)) p =
    mem-++r _ ks _ (subst (λ x → T (memN (vtx (suc x)) (bkeys (chainC K) ks))) (+-zero j)
                     (bkT K 0 K j (vtx-r j K p) ≤-refl))
  go _ (isEdge j)      p =
    mem-++l _ ks _ (subst (λ x → T (memN (dbl (suc x)) ks)) (+-zero j) (memEF 0 K j (edge-r j K p)))

------------------------------------------------------------------------
-- The builder, the typing and the side condition.

srcTgt-edge : ∀ K i → i < K → srcTgtVar (chainC K) (edge (suc i)) ≡ just (vtx i , vtx (suc i))
srcTgt-edge K i h rewrite lookup-edge K i h = refl

built-chain : ∀ m → vcompB (eF 0 (suc m)) (chainC (suc m)) ≡ just (var 0 , var (vtx (suc m)))
built-chain m =
  trans (bind-just {m = vLast (eF 0 (suc m))} (vLast-eF 0 m))
  (trans (bind-just {m = srcTgtVar (chainC (suc m)) (dbl 1)} (srcTgt-edge (suc m) 0 (s≤s z≤n)))
  (trans (bind-just {m = srcTgtVar (chainC (suc m)) (dbl (suc (m + 0)))}
                    (subst (λ x → srcTgtVar (chainC (suc m)) (edge (suc x)) ≡ just (vtx x , vtx (suc x)))
                           (sym (+-zero m)) (srcTgt-edge (suc m) m ≤-refl)))
         (cong (λ x → just (var 0 , var (vtx (suc x)))) (+-zero m))))

dimCtx-chain : ∀ m → dimCtx (chainC (suc m)) ≡ 1
dimCtx-chain zero    = refl
dimCtx-chain (suc m) rewrite dimCtx-chain m = refl

side-chain : ∀ m → T (cattSide (chainC (suc m)) ⋆ (var 0) (var (vtx (suc m))))
side-chain m = ∨-inr (isCoh (chainC (suc m)) ⋆ (var 0) (var (vtx (suc m)))) op
  where
  op : T (isOp (chainC (suc m)) ⋆ (var 0) (var (vtx (suc m))))
  op rewrite dimCtx-chain m | src-chain (suc m) | tgt-chain (suc m) =
    ∧-intro (single-≈ 0) (single-≈ (vtx (suc m)))

-- The shape facts of the m+1-fold composite of 1-cells, for every m.
shape-chain : ∀ m → ShapeOK (node (replicate (suc m) leaf)) (vcompB (tops (node (replicate (suc m) leaf))))
shape-chain m = shapeOK (var 0) (var (vtx (suc m))) ⋆
  (trans (cong₂ vcompB (tops-chain m) (ctx-chain (suc m))) (built-chain m))
  (inP (λ P → P ⊢tm var 0 ∶ ⋆) (var-wf (chainC-wf (suc m)) (lookup-vtx (suc m) 0 z≤n)))
  (inP (λ P → P ⊢tm var (vtx (suc m)) ∶ ⋆) (var-wf (chainC-wf (suc m)) (lookup-vtx (suc m) (suc m) ≤-refl)))
  (inP (λ P → T (cattSide P ⋆ (var 0) (var (vtx (suc m))))) (side-chain m))
  (inP (λ P → T (covers P (tops τ)))
       (subst (λ ks → T (covers (chainC (suc m)) ks)) (sym (tops-chain m)) (cover-chain (suc m) (s≤s z≤n))))
  where
  τ = node (replicate (suc m) leaf)
  inP : (F : Ctx → Set) → F (chainC (suc m)) → F (ctxOf τ)
  inP F x = subst F (sym (ctx-chain (suc m))) x

------------------------------------------------------------------------
-- vcomp on 1-cells: for every m and every typed σ₀ : chainC (m+2),
-- vcomp of the m+2 edges' images is the composite and is well typed.

private
  length-mapL : ∀ {A B : Set} (f : A → B) xs → length (mapL f xs) ≡ length xs
  length-mapL f []       = refl
  length-mapL f (x ∷ xs) = cong suc (length-mapL f xs)

  length-eF : ∀ i n → length (eF i n) ≡ n
  length-eF i zero    = refl
  length-eF i (suc n) = cong suc (length-eF (suc i) n)

module _ {Γ σ₀} (m : Nat) where
  private
    τ = node (replicate (suc (suc m)) leaf)
    P = ctxOf τ
    L = mapL (lookupₛ σ₀) (tops τ)
    Aτ = arr ⋆ (var 0) (var (vtx (suc (suc m))))

  vcomp1-ok : Γ ⊢sub σ₀ ∶ P →
              (vcomp Γ L ≡ just (coh P Aτ σ₀)) × (Γ ⊢tm coh P Aτ σ₀ ∶ Aτ [ σ₀ ]ty)
  vcomp1-ok s =
    trans (bind-just {m = dimOf Γ (lookupₛ σ₀ 2)} d1)
          (trans (cong (λ n → cohT Γ (vT 0 n) (vcompB (tops (vT 0 n))) L) lenL)
                 (fst ok)) ,
    snd ok
    where
    ok = cohT-ok τ _ (shape-chain (suc m)) s
    l2 : lookup P 2 ≡ just (arr ⋆ (var 0) (var 1))
    l2 = subst (λ Q → lookup Q 2 ≡ just (arr ⋆ (var 0) (var 1))) (sym (ctx-chain (suc (suc m))))
               (lookup-edge (suc (suc m)) 0 (s≤s z≤n))
    d1 : dimOf Γ (lookupₛ σ₀ 2) ≡ just 1
    d1 = cong (dim <$>_) (tyOf-typed (S.lookup-sub closed (ps-ctx (snd (psOf τ))) l2 s))
    lenL : length L ≡ suc (suc m)
    lenL = trans (length-mapL (lookupₛ σ₀) (tops τ))
                 (trans (cong length (tops-chain (suc m))) (length-eF 0 (suc (suc m))))
