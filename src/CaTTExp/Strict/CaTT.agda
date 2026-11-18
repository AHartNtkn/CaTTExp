------------------------------------------------------------------------
-- Soundness of CaTT in every strict ω-category ν(K) (ledger item A3a).
--
-- K is an arbitrary chain complex with a basis, given by ∂ and Bas as
-- in CaTTExp.Strict.Cell; nothing is assumed about it. A derivable
-- constant-free term t : A, interpreted (CaTTExp.Strict.Interp) in an
-- environment of cells of ν(K) with the boundaries their types
-- prescribe, is a cell of ν(K) with the boundary A prescribes:
--
--     sound-cf : Γ ⊢tm t ∶ A → CFTm t → ValidEnv ∂ Bas ρ Γ →
--                IsCell (dim A) ⟦t⟧ρ × Bd ⟦t⟧ρ A ρ
--
-- No hypothesis is taken on K, and nothing is postulated. The proof:
--
--  * A coh over Δ in environment ρ′ is the image, under the chain map
--    Fv ρ′ : λΔ → K, of the same coh in the generic environment η of
--    λΔ (CaTTExp.Strict.Interp.nat-tm), and chain maps preserve the
--    chain equation (CaTTExp.Strict.Cell.Transport.chain-transport).
--  * In λΔ, the top chain of a term t : B is the set of variables of
--    Var(t : B) of dimension dim B (key), so the side condition fixes
--    the tops of the source and target: the i-variables of ∂⁻Δ and
--    ∂⁺Δ. The chain equation is then the boundary formula
--    (CaTTExp.Strict.PsFacts.Bnd).
--  * key is proved by induction. Its coh case needs the top chain to
--    count every variable at most once, which holds for every cell of
--    λΓ with Γ ordered (CaTTExp.Strict.Lambda.MF), and the term is a
--    cell by the soundness proof itself, at a structurally smaller
--    derivation for each side condition: the two proofs are mutual.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst
open import CaTTExp.Strict.Cell using (Tower)

module CaTTExp.Strict.CaTT
  (𝕊 : Signature)
  (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊))
  (M : Signature.K 𝕊 → Tower)
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.PsFacts 𝕊
open import CaTTExp.Strict.Lambda 𝕊
open import CaTTExp.Strict.Interp 𝕊 M
open import CaTTExp.Strict.Dim 𝕊 closed
import CaTTExp.Subst 𝕊 cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)

------------------------------------------------------------------------
-- Small facts.

private
  t≢f : true ≡ false → ⊥
  t≢f ()

  z≢s : ∀ {m} → zero ≡ suc m → ⊥
  z≢s ()

  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  T<→≤ : ∀ a b → T (a <ℕ suc b) → a ≤ b
  T<→≤ zero    b       _ = z≤n
  T<→≤ (suc a) (suc b) p = s≤s (T<→≤ a b p)
  T<→≤ (suc a) zero    p = ⊥-elim (z a p)
    where
    z : ∀ a → T (suc a <ℕ 1) → ⊥
    z zero    ()
    z (suc a) ()

  ≤→T< : ∀ {a b} → a ≤ b → T (a <ℕ suc b)
  ≤→T< z≤n     = tt
  ≤→T< (s≤s p) = ≤→T< p

  ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym z≤n     z≤n     = refl
  ≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

  ≤-+ˡ : ∀ a b → b ≤ a + b
  ≤-+ˡ zero    b = ≤-refl b
  ≤-+ˡ (suc a) b = ≤-suc (≤-+ˡ a b)

  ≤-+-mono : ∀ {a b} c → a ≤ b → a ≤ c + b
  ≤-+-mono zero    p = p
  ≤-+-mono (suc c) p = ≤-suc (≤-+-mono c p)

  suc≰ : ∀ n → suc n ≤ n → ⊥
  suc≰ (suc n) (s≤s p) = suc≰ n p

  ==-false : ∀ {a b} → (a ≡ b → ⊥) → (a ==ℕ b) ≡ false
  ==-false {a} {b} f with a ==ℕ b in e
  ... | true  = ⊥-elim (f (==→≡ a b e))
  ... | false = refl

  ==-sym : ∀ a b → (a ==ℕ b) ≡ (b ==ℕ a)
  ==-sym zero    zero    = refl
  ==-sym zero    (suc b) = refl
  ==-sym (suc a) zero    = refl
  ==-sym (suc a) (suc b) = ==-sym a b

ind₀ : Bool → Nat
ind₀ b = if b then 1 else 0

-- A count of at most one, positive exactly when b holds, is ind₀ b.
count01 : ∀ n b → n ≤ 1 → (b ≡ true → 1 ≤ n) → (b ≡ false → n ≡ 0) → n ≡ ind₀ b
count01 n true  p q _ = ≤-antisym p (q refl)
count01 n false _ _ r = r refl

ind-∧ : ∀ a b → ind₀ (a ∧ b) ≡ (if a then ind₀ b else 0)
ind-∧ true  b = refl
ind-∧ false b = refl

------------------------------------------------------------------------
-- Counting through cm.

count-cm-zero : ∀ a g X → All (λ w → count a (g w) ≡ 0) X → count a (cm g X) ≡ 0
count-cm-zero a g []      _        = refl
count-cm-zero a g (w ∷ X) (p , qs) rewrite count-++ a (g w) (cm g X) | p = count-cm-zero a g X qs

count-cm-≥ : ∀ a g X x → 1 ≤ count x X → count a (g x) ≤ count a (cm g X)
count-cm-≥ a g (y ∷ X) x p rewrite count-++ a (g y) (cm g X) with eqT x y in e
... | true  rewrite eqT-sound x y (≡→T e) = ≤-+ʳ (count a (g y)) (count a (cm g X))
... | false = ≤-+-mono (count a (g y)) (count-cm-≥ a g X x p)

------------------------------------------------------------------------
-- Bags of singletons.

Single : Tuple → Set
Single t = Σ Nat λ v → t ≡ tup v

private
  count-nil-single : ∀ X → All Single X → count [] X ≡ 0
  count-nil-single []      _               = refl
  count-nil-single (_ ∷ X) ((v , refl) , s) = count-nil-single X s

  count-long-single : ∀ v w r X → All Single X → count (v ∷ w ∷ r) X ≡ 0
  count-long-single v w r []      _                = refl
  count-long-single v w r (_ ∷ X) ((x , refl) , s)
    rewrite ∧-false (v ==ℕ x) = count-long-single v w r X s

≈-singletons : ∀ X Y → All Single X → All Single Y →
               (∀ v → count (tup v) X ≡ count (tup v) Y) → X ≈ Y
≈-singletons X Y sX sY f = mk≈ go
  where
  go : ∀ a → count a X ≡ count a Y
  go []          = trans (count-nil-single X sX) (sym (count-nil-single Y sY))
  go (v ∷ [])    = f v
  go (v ∷ w ∷ r) = trans (count-long-single v w r X sX) (sym (count-long-single v w r Y sY))

All-sel : ∀ Γ k xs → All (λ t → Σ Nat λ w → (t ≡ tup w) × (elem w xs ≡ true) × (dimv Γ w ≡ k)) (sel Γ k xs)
All-sel Γ k []       = tt
All-sel Γ k (x ∷ xs) with dimv Γ x ==ℕ k in e
... | true  = (x , refl , cong (_∨ elem x xs) (==-refl x) , ==→≡ _ k e) ,
              All-map (sel Γ k xs) (λ t (w , p , m , d) → w , p , ∨-r′ (w ==ℕ x) m , d) (All-sel Γ k xs)
  where
  ∨-r′ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r′ true  _ = refl
  ∨-r′ false p = p
... | false = All-map (sel Γ k xs) (λ t (w , p , m , d) → w , p , ∨-r′ (w ==ℕ x) m , d) (All-sel Γ k xs)
  where
  ∨-r′ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r′ true  _ = refl
  ∨-r′ false p = p

All-sel-single : ∀ Γ k xs → All Single (sel Γ k xs)
All-sel-single Γ k xs = All-map (sel Γ k xs) (λ t (w , p , _) → w , p) (All-sel Γ k xs)

All-Basλ-single : ∀ Γ k X → All (Basλ Γ k) X → All Single X
All-Basλ-single Γ k X a = All-map X (λ t (v , p , _) → v , p) a

------------------------------------------------------------------------
-- Lists of variables.

------------------------------------------------------------------------
-- Valid environments in ν(K).

ValidEnv : (Bool → Tuple → Bag) → (Nat → Tuple → Set) → Env → Ctx → Set
ValidEnv ∂ Bas ρ Γ = ∀ v A → lookup Γ v ≡ just A →
                  Cells.IsCell ∂ Bas (dim A) (lookupₑ ρ v) × Bd (lookupₑ ρ v) A ρ

Par-Bd : ∀ X Y A ρ → Bd X A ρ → Bd Y A ρ → Par X Y
Par-Bd (base _)     (base _)       ⋆           ρ _         _         = tt
Par-Bd (step S U _) (step S′ U′ _) (arr A t u) ρ (p₁ , p₂) (q₁ , q₂) =
  ≈w-trans S _ S′ p₁ (≈w-sym S′ _ q₁) , ≈w-trans U _ U′ p₂ (≈w-sym U′ _ q₂)

------------------------------------------------------------------------
-- Cells of λΓ are cells of λ(Γ ▸ B).

mapTw-id : ∀ X → mapTw (cm (λ x → x ∷ [])) X ≡ X
mapTw-id (base c)     = cong base (cm-single c)
mapTw-id (step S U c) rewrite mapTw-id S | mapTw-id U | cm-single c = refl

module _ (Γ : Ctx) (B : Ty) where

  private
    F : Tuple → Bag
    F w = w ∷ []

    wk-basis : ∀ k w → Basλ Γ k w → All (Basλ (Γ ▸ B) k) (F w)
    wk-basis k w (v , p , A , eq , d) = (v , p , A , trans (lookup-wk Γ B v (lookup-< Γ v eq)) eq , d) , tt

    wk-aug : ∀ w → Basλ Γ zero w → Σ Tuple λ w′ → F w ≈ w′ ∷ []
    wk-aug w _ = w , ≈-refl

    ∂-same : ∀ k b w → Basλ Γ k w → ∂λ (Γ ▸ B) b w ≡ ∂λ Γ b w
    ∂-same k b .(v ∷ []) (v , refl , A , eq , _) = cong (∂T b) (lookup-wk Γ B v (lookup-< Γ v eq))

    wk-chain : ∀ k w b → Basλ Γ k w →
               cm (∂λ (Γ ▸ B) b) (F w) ++ cm F (∂λ Γ (not b) w) ≈ cm (∂λ (Γ ▸ B) (not b)) (F w) ++ cm F (∂λ Γ b w)
    wk-chain k w b bw
      rewrite ∂-same k b w bw | ∂-same k (not b) w bw
            | cm-single (∂λ Γ (not b) w) | cm-single (∂λ Γ b w)
            | ++-[]L (∂λ Γ b w) | ++-[]L (∂λ Γ (not b) w) =
      ++-comm (∂λ Γ b w) (∂λ Γ (not b) w)

  open Transport (∂λ Γ) (Basλ Γ) (∂λ (Γ ▸ B)) (Basλ (Γ ▸ B)) F wk-basis wk-aug wk-chain

  cell-wk : ∀ n X → Cells.IsCell (∂λ Γ) (Basλ Γ) n X → Cells.IsCell (∂λ (Γ ▸ B)) (Basλ (Γ ▸ B)) n X
  cell-wk n X c = subst (Cells.IsCell (∂λ (Γ ▸ B)) (Basλ (Γ ▸ B)) n) (mapTw-id X) (transport n X c)

------------------------------------------------------------------------
-- The generic environment is valid in λΓ for ordered Γ.

Ordered-init : ∀ {Γ B} → Γ ⊢ctx → Ordered (Γ ▸ B) → Ordered Γ
Ordered-init {Γ} {B} w (o , s) = o′ , s′
  where
  o′ : ArrOrd Γ
  o′ f A x y eq =
    let lf = lookup-< Γ f eq
        (lx , ly , xy) = o f A x y (trans (lookup-wk Γ B f lf) eq)
        (_ , (_ , sx , sy)) = Sb.ctx-lookup closed w eq
    in trans (sym (lookup-wk Γ B x sx)) lx , trans (sym (lookup-wk Γ B y sy)) ly , xy
  s′ : PsCtx Γ
  s′ f A eq = s f A (trans (lookup-wk Γ B f (lookup-< Γ f eq)) eq)

η-valid : ∀ {Γ} → Ordered Γ → Γ ⊢ctx → ValidEnv (∂λ Γ) (Basλ Γ) (η Γ) Γ
η-valid o ε-wf v A ()
η-valid {Γ ▸ A} o (▸-wf w a) v A′ eq = split (v ==ℕ lenₑ ρ) refl
  where
  IH = η-valid (Ordered-init w o) w
  n = len Γ
  ρ = η Γ
  ρ′ = η Γ ,ₑ gen n A ρ
  Γ′ = Γ ▸ A
  IsC = Cells.IsCell (∂λ Γ′) (Basλ Γ′)

  sA : ScTy (lenₑ ρ) A
  sA = subst (λ m → ScTy m A) (sym (lenₑ-η Γ)) (Sb.ty-sc closed a)

  Bd-gen : ∀ A → Bd (gen n A ρ) A ρ
  Bd-gen ⋆           = tt
  Bd-gen (arr B s u) = ≈w-refl _ , ≈w-refl _

  top-ηx : ∀ x → T (x <ℕ n) → top (lookupₑ ρ x) ≡ tup x ∷ []
  top-ηx x lx rewrite η-top Γ x | T→≡ lx = refl

  cell-gen : PsTy A → ScTy n A → IsC (dim A) (gen n A ρ)
  cell-gen ⋆ₚ _ = tup n , ≈-refl , (n , refl , ⋆ , lookup-top Γ ⋆ , refl)
  cell-gen (arrₚ {B} {x} {y} _) (_ , sx , sy) =
    let (lx , ly , xy) = fst o n B x y (lookup-top Γ _)
        lxΓ = trans (sym (lookup-wk Γ A x sx)) lx
        lyΓ = trans (sym (lookup-wk Γ A y sy)) ly
        (cx , bx) = IH x B lxΓ
        (cy , by) = IH y B lyΓ
    in cell-wk Γ A (dim B) _ cx , cell-wk Γ A (dim B) _ cy ,
       Par-Bd (lookupₑ ρ x) (lookupₑ ρ y) B ρ bx by ,
       chain ,
       ((n , refl , arr B (var x) (var y) , lookup-top Γ _ , refl) , tt)
    where
    chain : Cells.ChainEq (∂λ Γ′) (Basλ Γ′) (tup n ∷ []) (top (lookupₑ ρ x)) (top (lookupₑ ρ y))
    chain rewrite top-ηx x sx | top-ηx y sy | ==-refl (len Γ) = ++-comm (tup y ∷ []) (tup x ∷ [])

  new : ∀ A″ → lookup Γ′ n ≡ just A″ → IsC (dim A″) (lookupₑ ρ′ n) × Bd (lookupₑ ρ′ n) A″ ρ′
  new A″ e with just-inj′ (trans (sym e) (lookup-top Γ A))
  ... | refl rewrite lenₑ-η Γ | ==-refl n =
    cell-gen (snd o n A (lookup-top Γ A)) (Sb.ty-sc closed a) ,
    Bd-wk (gen n A ρ) A ρ (gen n A ρ) sA (Bd-gen A)

  split : (b : Bool) → (v ==ℕ lenₑ ρ) ≡ b → IsC (dim A′) (lookupₑ ρ′ v) × Bd (lookupₑ ρ′ v) A′ ρ′
  split true e =
    let vn = trans (==→≡ v (lenₑ ρ) e) (lenₑ-η Γ) in
    subst (λ u → IsC (dim A′) (lookupₑ ρ′ u) × Bd (lookupₑ ρ′ u) A′ ρ′) (sym vn)
      (new A′ (subst (λ u → lookup Γ′ u ≡ just A′) vn eq))
  split false e rewrite e =
    let e′ = trans (cong (v ==ℕ_) (sym (lenₑ-η Γ))) e
        eqΓ = trans (sym (cond-false e′)) eq
        (c , b) = IH v A′ eqΓ
        (_ , sc) = Sb.ctx-lookup closed w eqΓ
    in cell-wk Γ A (dim A′) _ c ,
       Bd-wk (lookupₑ ρ v) A′ ρ (gen n A ρ) (subst (λ m → ScTy m A′) (sym (lenₑ-η Γ)) sc) b
    where
    cond-false : (v ==ℕ len Γ) ≡ false → lookup Γ′ v ≡ lookup Γ v
    cond-false p rewrite p = refl

------------------------------------------------------------------------
-- Facts about the side condition, used by the chain equation.

private
  cohTop-yes : ∀ Θ B ρ → (suc (dim B) ==ℕ dimCtx Θ) ≡ true → cohTop Θ B ρ ≡ cm (Fv ρ) (Wb Θ (dimCtx Θ))
  cohTop-yes Θ B ρ e rewrite e = refl

  cohTop-no : ∀ Θ B ρ → (suc (dim B) ==ℕ dimCtx Θ) ≡ false → cohTop Θ B ρ ≡ []
  cohTop-no Θ B ρ e rewrite e = refl

  ∧-cong-false : ∀ a b → b ≡ false → (a ∧ b) ≡ false
  ∧-cong-false a b refl = ∧-false a

-- Variables of the type do not reach the top dimension.
fvTmTy-key : ∀ {Θ s B} → Θ ⊢tm s ∶ B → ∀ v →
             (elem v (fvTmTy s B) ∧ (dimv Θ v ==ℕ dim B)) ≡ (elem v (fvTm s) ∧ (dimv Θ v ==ℕ dim B))
fvTmTy-key {Θ} {s} {B} ds v rewrite elem-++ v (fvTm s) (fvTy B) with elem v (fvTy B) in e
... | false = cong (_∧ (dimv Θ v ==ℕ dim B)) (∨-false′ (elem v (fvTm s)))
  where
  ∨-false′ : ∀ a → (a ∨ false) ≡ a
  ∨-false′ true  = refl
  ∨-false′ false = refl
... | true  rewrite ==-false {dimv Θ v} {dim B} (λ eq → suc≰ (dim B) (subst (λ m → suc m ≤ dim B) eq (dim-tyof ds v e)))
  = trans (∧-false (elem v (fvTm s) ∨ true)) (sym (∧-false (elem v (fvTm s))))

-- A coherence (full source) is never a genuine operation.
coh-not-op : ∀ {Θ B s z} → Θ ⊢ps z ∶ ⋆ → Θ ⊢tm s ∶ B → T (≈? (fvTmTy s B) (varsCtx Θ)) →
             (suc (dim B) ==ℕ dimCtx Θ) ≡ false
coh-not-op {Θ} {B} {s} d ds p =
  let (w , m , dw) = ps-top d
      m′ = trans (≈?-elem (fvTmTy s B) (varsCtx Θ) p w) m
      le = dim-tmty ds w m′
  in ==-false (λ eq → suc≰ (dim B) (subst (_≤ dim B) (trans dw (sym eq)) le))

-- In a non-genuine operation, ∂⁻Δ and ∂⁺Δ agree in dimension dim B.
op-flat : ∀ {Θ B s z} → Θ ⊢ps z ∶ ⋆ → Θ ⊢tm s ∶ B → T (≈? (fvTmTy s B) (∂⁻ Θ)) →
          (suc (dim B) ==ℕ dimCtx Θ) ≡ false → ∀ v →
          (elem v (∂⁻ Θ) ∧ (dimv Θ v ==ℕ dim B)) ≡ (elem v (∂⁺ Θ) ∧ (dimv Θ v ==ℕ dim B))
op-flat {Θ} {B} {s} d ds p g v = split (dimCtx Θ) refl
  where
  split : ∀ m → dimCtx Θ ≡ m → (elem v (∂⁻ Θ) ∧ (dimv Θ v ==ℕ dim B)) ≡ (elem v (∂⁺ Θ) ∧ (dimv Θ v ==ℕ dim B))
  split zero e rewrite ps-dim0 d e = refl
  split (suc i) e = trans (side-false (srcVars i Θ) (src-dims d i v) ∂⁻-is) (sym (side-false (tgtVars i Θ) (tgt-dims d i v) ∂⁺-is))
    where
    ∂⁻-is : ∂⁻ Θ ≡ srcVars i Θ
    ∂⁻-is = cong (λ m → srcVars (m ∸ 1) Θ) e
    ∂⁺-is : ∂⁺ Θ ≡ tgtVars i Θ
    ∂⁺-is = cong (λ m → tgtVars (m ∸ 1) Θ) e
    -- i ≤ dim B, and dim B ≠ i
    i≤B : i ≤ dim B
    i≤B = let (w , mw , dw) = src-has d i (subst (λ m → T (i <ℕ suc m)) (sym e) (<-suc i (suc i) (n<suc i)))
              mw′ = trans (≈?-elem (fvTmTy s B) (∂⁻ Θ) p w) (trans (cong (elem w) ∂⁻-is) mw)
          in subst (_≤ dim B) dw (dim-tmty ds w mw′)
    B≢i : dim B ≡ i → ⊥
    B≢i eq = t≢f (trans (sym (trans (cong (λ m → suc m ==ℕ suc i) eq) (==-refl i))) (trans (cong (suc (dim B) ==ℕ_) (sym e)) g))
    side-false : ∀ xs → (elem v xs ≡ true → T (dimv Θ v <ℕ suc i)) → ∀ {ys} → ys ≡ xs →
                 (elem v ys ∧ (dimv Θ v ==ℕ dim B)) ≡ false
    side-false xs f refl with dimv Θ v ==ℕ dim B in eD
    ... | false = ∧-false (elem v xs)
    ... | true with elem v xs in em
    ...   | false = refl
    ...   | true = ⊥-elim (B≢i (≤-antisym (subst (_≤ i) (==→≡ (dimv Θ v) (dim B) eD) (T<→≤ (dimv Θ v) i (f refl))) i≤B))

-- From the count characterization, the top of t : B over a pasting
-- context is the bag of the dim-B variables of any list with the same
-- elements as Var(t : B) and no repeats.
top-is-sel : ∀ {Θ s B} X xs → Θ ⊢tm s ∶ B → All Single X →
             (∀ v → count (tup v) X ≡ ind₀ (elem v (fvTm s) ∧ (dimv Θ v ==ℕ dim B))) →
             T (≈? (fvTmTy s B) xs) → NoDup xs → X ≈ sel Θ (dim B) xs
top-is-sel {Θ} {s} {B} X xs ds sX kX p nd =
  ≈-singletons X (sel Θ (dim B) xs) sX (All-sel-single Θ (dim B) xs) λ v →
    trans (kX v)
   (trans (cong ind₀ (sym (fvTmTy-key ds v)))
   (trans (cong (λ b → ind₀ (b ∧ (dimv Θ v ==ℕ dim B))) (≈?-elem (fvTmTy s B) xs p v))
   (trans (ind-∧ (elem v xs) (dimv Θ v ==ℕ dim B))
   (trans (if-ind (elem v xs) (dimv Θ v ==ℕ dim B))
          (sym (count-sel Θ (dim B) v xs nd))))))
  where
  if-ind : ∀ a b → (if a then ind₀ b else 0) ≡ (if a then (if b then 1 else 0) else 0)
  if-ind true  b = refl
  if-ind false b = refl

------------------------------------------------------------------------
-- All of the top chain of a coh consists of basis elements.

all-top : ∀ ∂ Bas {Θ B ρ} → ValidEnv ∂ Bas ρ Θ → All (Bas (suc (dim B))) (cohTop Θ B ρ)
all-top ∂ Bas {Θ} {B} {ρ} vρ = split (suc (dim B) ==ℕ dimCtx Θ) refl
  where
  split : ∀ b → (suc (dim B) ==ℕ dimCtx Θ) ≡ b → All (Bas (suc (dim B))) (cohTop Θ B ρ)
  split false e rewrite cohTop-no Θ B ρ e = tt
  split true  e rewrite cohTop-yes Θ B ρ e =
    All-cm (Fv ρ) (Wb Θ (dimCtx Θ)) (All-sel Θ (dimCtx Θ) (varsCtx Θ)) each
    where
    each : ∀ t → (Σ Nat λ w → (t ≡ tup w) × (elem w (varsCtx Θ) ≡ true) × (dimv Θ w ≡ dimCtx Θ)) →
           All (Bas (suc (dim B))) (Fv ρ t)
    each .(w ∷ []) (w , refl , m , dw) =
      let lw = elem-Below (len Θ) w (varsCtx Θ) (Below-downFrom (len Θ)) m
          (Aw , eq) = lookup-just Θ w lw
          (c , _) = vρ w Aw eq
          d : dim Aw ≡ suc (dim B)
          d = trans (sym (cong dimM eq)) (trans dw (sym (==→≡ _ _ e)))
      in subst (λ k → All (Bas k) (top (lookupₑ ρ w))) d (Cells.IsCell-top ∂ Bas (dim Aw) _ c)

------------------------------------------------------------------------
-- Soundness and the support lemma, by mutual induction.

private
  VE : (Bool → Tuple → Bag) → (Nat → Tuple → Set) → Tower → Ty → Env → Set
  VE ∂ Bas X A ρ = Cells.IsCell ∂ Bas (dim A) X × Bd X A ρ

  lookupₑ-top : ∀ ρ X n → lenₑ ρ ≡ n → lookupₑ (ρ ,ₑ X) n ≡ X
  lookupₑ-top ρ X n refl rewrite ==-refl (lenₑ ρ) = refl

  lookupₑ-skip : ∀ ρ X v → (v ==ℕ lenₑ ρ) ≡ false → lookupₑ (ρ ,ₑ X) v ≡ lookupₑ ρ v
  lookupₑ-skip ρ X v e rewrite e = refl

  lookup-skip : ∀ Δ B v → (v ==ℕ len Δ) ≡ false → lookup (Δ ▸ B) v ≡ lookup Δ v
  lookup-skip Δ B v e rewrite e = refl

  ind-zero : ∀ a a′ c c′ → (a′ ≡ true → a ≡ true) → c′ ≡ c → (a ∧ c) ≡ false → ind₀ (a′ ∧ c′) ≡ 0
  ind-zero a true  c c′ f refl p rewrite f refl = cong ind₀ p
  ind-zero a false c c′ f _    _ = refl

mutual
  sound-tm : ∀ ∂ Bas {Γ t A ρ} → Γ ⊢tm t ∶ A → CFTm t → ValidEnv ∂ Bas ρ Γ → VE ∂ Bas (⟦ t ⟧ ρ) A ρ
  sound-tm ∂ Bas (var-wf {i} w eq) _ vρ = vρ i _ eq
  sound-tm ∂ Bas (cst-wf _ _) () vρ
  sound-tm ∂ Bas {Γ} {ρ = ρ} (coh-wf {Δ = Θ} {A = B} {t = s} {u = u} {σ = σ} pΘ wΘ (arr-wf ds du) side sσ)
           ((cfB , cfs , cfu) , cfσ) vρ =
    subst (λ m → Cells.IsCell ∂ Bas (suc m) X) (sym (dim-[] B σ)) cell ,
    Bd-[]← X (arr B s u) σ ρ scC (≈w-refl (⟦ s ⟧ ρ′) , ≈w-refl (⟦ u ⟧ ρ′))
    where
    ρ′ = ⟦ σ ⟧ₛ ρ
    X = ⟦ coh Θ (arr B s u) σ ⟧ ρ
    lσ : lenₛ σ ≡ len Θ
    lσ = snd (Sb.sub-sc closed sσ)
    scC : ScTy (lenₛ σ) (arr B s u)
    scC = subst (λ n → ScTy n (arr B s u)) (sym lσ) (Sb.ty-sc closed (arr-wf ds du))
    vρ′ = sound-sub ∂ Bas sσ cfσ vρ wΘ
    lρ′ : lenₑ ρ′ ≡ len Θ
    lρ′ = trans (lenₑ-⟦⟧ₛ σ ρ) lσ
    S = sound-tm ∂ Bas ds cfs vρ′
    U = sound-tm ∂ Bas du cfu vρ′
    cell : Cells.IsCell ∂ Bas (suc (dim B)) X
    cell = fst S , fst U , Par-Bd (⟦ s ⟧ ρ′) (⟦ u ⟧ ρ′) B ρ′ (snd S) (snd U) ,
           chain-eq ∂ Bas pΘ wΘ ds du cfs cfu side vρ′ lρ′ ,
           all-top ∂ Bas {Θ} {B} vρ′

  sound-sub : ∀ ∂ Bas {Γ σ Δ ρ} → Γ ⊢sub σ ∶ Δ → CFSub σ → ValidEnv ∂ Bas ρ Γ → Δ ⊢ctx →
              ValidEnv ∂ Bas (⟦ σ ⟧ₛ ρ) Δ
  sound-sub ∂ Bas (⟨⟩-wf _) _ vρ _ v A ()
  sound-sub ∂ Bas {ρ = ρ} (,-wf {σ = σ} {Δ = Δ} {t = t} {A = B} sσ dt) (cσ , ct) vρ (▸-wf wΔ bB) v A eq =
    split (v ==ℕ len Δ) refl
    where
    ρσ = ⟦ σ ⟧ₛ ρ
    lσ′ : lenₛ σ ≡ len Δ
    lσ′ = snd (Sb.sub-sc closed sσ)
    lσ : lenₑ ρσ ≡ len Δ
    lσ = trans (lenₑ-⟦⟧ₛ σ ρ) lσ′
    IH = sound-sub ∂ Bas sσ cσ vρ wΔ
    Tt = sound-tm ∂ Bas dt ct vρ
    split : ∀ b → (v ==ℕ len Δ) ≡ b → VE ∂ Bas (lookupₑ (ρσ ,ₑ ⟦ t ⟧ ρ) v) A (ρσ ,ₑ ⟦ t ⟧ ρ)
    split true e with ==→≡ v (len Δ) e
    ... | refl with just-inj′ (trans (sym eq) (lookup-top Δ B))
    ...   | refl =
      subst (λ Y → VE ∂ Bas Y B (ρσ ,ₑ ⟦ t ⟧ ρ)) (sym (lookupₑ-top ρσ (⟦ t ⟧ ρ) (len Δ) lσ))
        (subst (λ m → Cells.IsCell ∂ Bas m (⟦ t ⟧ ρ)) (dim-[] B σ) (fst Tt) ,
         Bd-wk (⟦ t ⟧ ρ) B ρσ (⟦ t ⟧ ρ)
           (subst (λ m → ScTy m B) (sym lσ) (Sb.ty-sc closed bB))
           (Bd-[]→ (⟦ t ⟧ ρ) B σ ρ (subst (λ m → ScTy m B) (sym lσ′) (Sb.ty-sc closed bB)) (snd Tt)))
    split false e =
      let eqΔ = trans (sym (lookup-skip Δ B v e)) eq
          (c , b) = IH v A eqΔ
          (_ , sc) = Sb.ctx-lookup closed wΔ eqΔ
      in subst (λ Y → VE ∂ Bas Y A (ρσ ,ₑ ⟦ t ⟧ ρ))
           (sym (lookupₑ-skip ρσ (⟦ t ⟧ ρ) v (trans (cong (v ==ℕ_) lσ) e)))
           (c , Bd-wk (lookupₑ ρσ v) A ρσ (⟦ t ⟧ ρ) (subst (λ m → ScTy m A) (sym lσ) sc) b)

  -- The chain equation of a coh.
  chain-eq : ∀ ∂ Bas {Θ B s u ρ′} → Θ ⊢ps → Θ ⊢ctx → Θ ⊢tm s ∶ B → Θ ⊢tm u ∶ B → CFTm s → CFTm u →
             T (cattSide Θ B s u) → ValidEnv ∂ Bas ρ′ Θ → lenₑ ρ′ ≡ len Θ →
             Cells.ChainEq ∂ Bas (cohTop Θ B ρ′) (top (⟦ s ⟧ ρ′)) (top (⟦ u ⟧ ρ′))
  chain-eq ∂ Bas {Θ} {B} {s} {u} {ρ′} (ps d) wΘ ds du cfs cfu side vρ′ l =
    Cells.ChainEq-≈ ∂ Bas (≡→≈ (cm-if g)) (≈-sym ns) (≈-sym nu) transported
    where
    F = Fv ρ′
    pf = ps-facts d
    oΘ : Ordered Θ
    oΘ = ord pf , shape pf
    Sη = top (⟦ s ⟧ (η Θ))
    Uη = top (⟦ u ⟧ (η Θ))
    ns : top (⟦ s ⟧ ρ′) ≈ cm F Sη
    ns = nat-tm F (η Θ) ρ′ s cfs (η-nat Θ ρ′ l)
    nu : top (⟦ u ⟧ ρ′) ≈ cm F Uη
    nu = nat-tm F (η Θ) ρ′ u cfu (η-nat Θ ρ′ l)
    g = suc (dim B) ==ℕ dimCtx Θ
    W = Wb Θ (dimCtx Θ)
    cλ : Bag
    cλ = if g then W else []
    cm-if : ∀ b → cm F (if b then W else []) ≡ (if b then cm F W else [])
    cm-if true  = refl
    cm-if false = refl

    BasP : Nat → Tuple → Set
    BasP zero    _ = ⊥
    BasP (suc k) t = Basλ Θ (suc k) t

    F-basis : ∀ k w → BasP k w → All (Bas k) (F w)
    F-basis (suc k) .(v ∷ []) (v , refl , A , eq , dA) =
      subst (λ m → All (Bas m) (top (lookupₑ ρ′ v))) dA (Cells.IsCell-top ∂ Bas (dim A) _ (fst (vρ′ v A eq)))

    F-aug : ∀ w → BasP zero w → Σ Tuple λ w′ → F w ≈ w′ ∷ []
    F-aug w ()

    F-chain : ∀ k w b → BasP k w → cm (∂ b) (F w) ++ cm F (∂λ Θ (not b) w) ≈ cm (∂ (not b)) (F w) ++ cm F (∂λ Θ b w)
    F-chain (suc k) .(v ∷ []) b (v , refl , A , eq , dA) with shape pf v A eq
    ... | arrₚ {C} {x} {y} _ = arrow (lookupₑ ρ′ v) (vρ′ v _ eq) b
      where
      arrow : ∀ Y → VE ∂ Bas Y (arr C (var x) (var y)) ρ′ → ∀ b →
              cm (∂ b) (top Y) ++ cm F (∂T (not b) (lookup Θ v)) ≈ cm (∂ (not b)) (top Y) ++ cm F (∂T b (lookup Θ v))
      arrow (step S U c) ((_ , _ , _ , ch , _) , (pS , pU)) b rewrite eq =
        let tS : top S ≈ F (tup x) ++ []
            tS = ≈-trans (≈w-top S _ pS) (≡→≈ (sym (++-[]L (top (lookupₑ ρ′ x)))))
            tU : top U ≈ F (tup y) ++ []
            tU = ≈-trans (≈w-top U _ pU) (≡→≈ (sym (++-[]L (top (lookupₑ ρ′ y)))))
        in which b tS tU
        where
        which : ∀ b → top S ≈ F (tup x) ++ [] → top U ≈ F (tup y) ++ [] →
                cm (∂ b) c ++ cm F (∂T (not b) (just (arr C (var x) (var y))))
                ≈ cm (∂ (not b)) c ++ cm F (∂T b (just (arr C (var x) (var y))))
        which true  tS tU = Cells.ChainEq-≈ ∂ Bas (≈-refl {c}) tS tU ch
        which false tS tU = ≈-sym (Cells.ChainEq-≈ ∂ Bas (≈-refl {c}) tS tU ch)
    ... | ⋆ₚ = ⊥-elim (z≢s dA)

    module Tr = Transport (∂λ Θ) BasP ∂ Bas F F-basis F-aug F-chain

    sS : All Single Sη
    sS = All-Basλ-single Θ (dim B) Sη
           (Cells.IsCell-top (∂λ Θ) (Basλ Θ) (dim B) _ (fst (sound-tm (∂λ Θ) (Basλ Θ) ds cfs (η-valid oΘ wΘ))))
    sU : All Single Uη
    sU = All-Basλ-single Θ (dim B) Uη
           (Cells.IsCell-top (∂λ Θ) (Basλ Θ) (dim B) _ (fst (sound-tm (∂λ Θ) (Basλ Θ) du cfu (η-valid oΘ wΘ))))
    kS = support oΘ wΘ ds cfs
    kU = support oΘ wΘ du cfu

    -- The chain equation in λΘ.
    chλ : ∀ b → g ≡ b → Cells.ChainEq (∂λ Θ) BasP (if b then W else []) Sη Uη × All (BasP (suc (dim B))) (if b then W else [])
    chλ true e = eqn , allW
      where
      eΘ : dimCtx Θ ≡ suc (dim B)
      eΘ = sym (==→≡ _ _ e)
      notcoh : isCoh Θ B s u ≡ false
      notcoh with isCoh Θ B s u in ec
      ... | false = refl
      ... | true  = ⊥-elim (t≢f (trans (sym e) (coh-not-op d ds (∧-l _ _ (≡→T ec)))))
      op : T (isOp Θ B s u)
      op = subst (λ b → T (b ∨ isOp Θ B s u)) notcoh side
      ∂⁻-is : ∂⁻ Θ ≡ srcVars (dim B) Θ
      ∂⁻-is = cong (λ m → srcVars (m ∸ 1) Θ) eΘ
      ∂⁺-is : ∂⁺ Θ ≡ tgtVars (dim B) Θ
      ∂⁺-is = cong (λ m → tgtVars (m ∸ 1) Θ) eΘ
      S≈ : Sη ≈ sel Θ (dim B) (srcVars (dim B) Θ)
      S≈ = top-is-sel Sη (srcVars (dim B) Θ) ds sS kS
             (subst (λ xs → T (≈? (fvTmTy s B) xs)) ∂⁻-is (∧-l _ _ op)) (src-nodup (dim B) Θ)
      U≈ : Uη ≈ sel Θ (dim B) (tgtVars (dim B) Θ)
      U≈ = top-is-sel Uη (tgtVars (dim B) Θ) du sU kU
             (subst (λ xs → T (≈? (fvTmTy u B) xs)) ∂⁺-is (∧-r (≈? (fvTmTy s B) (∂⁻ Θ)) _ op)) (tgt-nodup (dim B) Θ)
      W≡ : W ≡ Wb Θ (suc (dim B))
      W≡ = cong (Wb Θ) eΘ
      bnd = Bnd d (dim B) (subst (λ m → T (m <ℕ suc (suc (dim B)))) (sym eΘ) (n<suc (suc (dim B))))
      eqn : Cells.ChainEq (∂λ Θ) BasP W Sη Uη
      eqn rewrite W≡ = ≈-trans (++-cong ≈-refl S≈) (≈-trans bnd (++-cong ≈-refl (≈-sym U≈)))
      allW : All (BasP (suc (dim B))) W
      allW = All-map W each (All-sel Θ (dimCtx Θ) (varsCtx Θ))
        where
        each : ∀ t → (Σ Nat λ w → (t ≡ tup w) × (elem w (varsCtx Θ) ≡ true) × (dimv Θ w ≡ dimCtx Θ)) → BasP (suc (dim B)) t
        each .(w ∷ []) (w , refl , m , dw) =
          let lw = elem-Below (len Θ) w (varsCtx Θ) (Below-downFrom (len Θ)) m
              (Aw , eqw) = lookup-just Θ w lw
          in w , refl , Aw , eqw , trans (sym (cong dimM eqw)) (trans dw eΘ)
    chλ false e = flatSU , tt
      where
      flatSU : Sη ≈ Uη
      flatSU = ≈-singletons Sη Uη sS sU λ v →
        trans (kS v) (trans (cong ind₀ (sym (fvTmTy-key ds v)))
       (trans (cong ind₀ (same v)) (trans (cong ind₀ (fvTmTy-key du v)) (sym (kU v)))))
        where
        same : ∀ v → (elem v (fvTmTy s B) ∧ (dimv Θ v ==ℕ dim B)) ≡ (elem v (fvTmTy u B) ∧ (dimv Θ v ==ℕ dim B))
        same v with isCoh Θ B s u in ec
        ... | true =
          let p = ≡→T ec in
          cong (_∧ (dimv Θ v ==ℕ dim B))
            (trans (≈?-elem (fvTmTy s B) (varsCtx Θ) (∧-l _ _ p) v)
                   (sym (≈?-elem (fvTmTy u B) (varsCtx Θ) (∧-r (≈? (fvTmTy s B) (varsCtx Θ)) _ p) v)))
        ... | false =
          let op = side
              ps′ = ∧-l (≈? (fvTmTy s B) (∂⁻ Θ)) _ op
              pu′ = ∧-r (≈? (fvTmTy s B) (∂⁻ Θ)) _ op
          in trans (cong (_∧ (dimv Θ v ==ℕ dim B)) (≈?-elem (fvTmTy s B) (∂⁻ Θ) ps′ v))
            (trans (op-flat d ds ps′ e v)
                   (cong (_∧ (dimv Θ v ==ℕ dim B)) (sym (≈?-elem (fvTmTy u B) (∂⁺ Θ) pu′ v))))

    transported : Cells.ChainEq ∂ Bas (cm F cλ) (cm F Sη) (cm F Uη)
    transported = let (e , a) = chλ g refl in Tr.chain-transport (suc (dim B)) cλ Sη Uη a e

  -- The support lemma: in the generic environment of an ordered
  -- context, the top chain of t : A is the set of variables of t of
  -- dimension dim A.
  support : ∀ {Γ t A} → Ordered Γ → Γ ⊢ctx → Γ ⊢tm t ∶ A → CFTm t → ∀ v →
        count (tup v) (top (⟦ t ⟧ (η Γ))) ≡ ind₀ (elem v (fvTm t) ∧ (dimv Γ v ==ℕ dim A))
  support {Γ} oΓ wΓ (var-wf {i} {A} w eq) _ v
    rewrite η-top Γ i | T→≡ (lookup-< Γ i eq) with v ==ℕ i in e
  ... | true rewrite ==→≡ v i e | eq | ==-refl (dim A) = refl
  ... | false = refl
  support oΓ wΓ (cst-wf _ _) () v
  support {Γ} oΓ wΓ d@(coh-wf {Δ = Θ} {A = B} {t = s} {u = u} {σ = τ} pΘ wΘ (arr-wf ds du) side sτ) cf v =
    count01 (count (tup v) (cohTop Θ B ρ′)) b
      (MF.MF-cell Γ oΓ (suc (dim (B [ τ ]ty))) (⟦ coh Θ (arr B s u) τ ⟧ (η Γ)) (fst (sound-tm (∂λ Γ) (Basλ Γ) d cf (η-valid oΓ wΓ))) v)
      pos zero′
    where
    ρ′ = ⟦ τ ⟧ₛ (η Γ)
    W = Wb Θ (dimCtx Θ)
    D = dimv Γ v ==ℕ suc (dim (B [ τ ]ty))
    b = elem v (fvSub τ) ∧ D
    lτ : lenₛ τ ≡ len Θ
    lτ = snd (Sb.sub-sc closed sτ)
    cfτ = snd cf
    ks = key-sub oΓ wΓ sτ cfτ

    D′ : ∀ x → dimv Θ x ≡ dimCtx Θ → (suc (dim B) ==ℕ dimCtx Θ) ≡ true → (dimv Γ v ==ℕ dimv Θ x) ≡ D
    D′ x dx e = trans (cong (dimv Γ v ==ℕ_) (trans dx (sym (==→≡ (suc (dim B)) (dimCtx Θ) e))))
                      (cong (λ m → dimv Γ v ==ℕ suc m) (sym (dim-[] B τ)))

    zero′ : b ≡ false → count (tup v) (cohTop Θ B ρ′) ≡ 0
    zero′ bf with suc (dim B) ==ℕ dimCtx Θ in e
    ... | false = refl
    ... | true = count-cm-zero (tup v) (Fv ρ′) W (All-map W each (All-sel Θ (dimCtx Θ) (varsCtx Θ)))
      where
      each : ∀ t → (Σ Nat λ w → (t ≡ tup w) × (elem w (varsCtx Θ) ≡ true) × (dimv Θ w ≡ dimCtx Θ)) →
             count (tup v) (Fv ρ′ t) ≡ 0
      each .(w ∷ []) (w , refl , m , dw) =
        let lw = elem-Below (len Θ) w (varsCtx Θ) (Below-downFrom (len Θ)) m in
        trans (ks w lw v)
          (ind-zero (elem v (fvSub τ)) (elem v (fvTm (lookupₛ τ w))) D (dimv Γ v ==ℕ dimv Θ w)
            (fvSub-at τ w v (subst (λ n → T (w <ℕ n)) (sym lτ) lw)) (D′ w dw e) bf)

    pos : b ≡ true → 1 ≤ count (tup v) (cohTop Θ B ρ′)
    pos bt with suc (dim B) ==ℕ dimCtx Θ in e
    ... | false = ⊥-elim (suc≰ (dim B) (≤-trans (subst (_≤ dimv Γ v) refl dv≥) (≤-trans dv≤ cΘ)))
      where
      inv : elem v (fvSub τ) ≡ true
      inv = T→≡ (∧-l _ _ (≡→T bt))
      dv≡ : dimv Γ v ≡ suc (dim B)
      dv≡ = trans (==→≡ _ _ (T→≡ (∧-r (elem v (fvSub τ)) _ (≡→T bt)))) (cong suc (dim-[] B τ))
      dv≥ : suc (dim B) ≤ dimv Γ v
      dv≥ = subst (suc (dim B) ≤_) (sym dv≡) (≤-refl _)
      dv≤ : dimv Γ v ≤ dimCtx Θ
      dv≤ = dim-sub sτ v inv
      cΘ : dimCtx Θ ≤ dim B
      cΘ = le-ne (dimCtx Θ) (dim B) (side-dim {u = u} pΘ wΘ ds side) e
        where
        le-ne : ∀ a c → a ≤ suc c → (suc c ==ℕ a) ≡ false → a ≤ c
        le-ne zero    c       _       _ = z≤n
        le-ne (suc a) zero    (s≤s z≤n) ()
        le-ne (suc a) (suc c) (s≤s p) q = s≤s (le-ne a c p q)
    ... | true =
      let inv = T→≡ (∧-l _ _ (≡→T bt))
          dv≡ : dimv Γ v ≡ suc (dim B)
          dv≡ = trans (==→≡ _ _ (T→≡ (∧-r (elem v (fvSub τ)) _ (≡→T bt)))) (cong suc (dim-[] B τ))
          (x , lx , mx) = fvSub-split τ v inv
          lxΘ = subst (λ n → T (x <ℕ n)) lτ lx
          (Ax , eqx) = lookup-just Θ x lxΘ
          eΘ = sym (==→≡ _ _ e)
          dx≤ : dimv Θ x ≤ dimCtx Θ
          dx≤ = T<→≤ _ _ (subst (λ m → T (m <ℕ suc (dimCtx Θ))) (sym (cong dimM eqx)) (dim-≤-dimCtx Θ x eqx))
          dv≤ : dimv Γ v ≤ dimv Θ x
          dv≤ = dim-sub-at sτ x lxΘ v mx
          dx≡ : dimv Θ x ≡ dimCtx Θ
          dx≡ = ≤-antisym dx≤ (subst (_≤ dimv Θ x) (trans dv≡ (sym eΘ)) dv≤)
          inW : 1 ≤ count (tup x) W
          inW = subst (1 ≤_) (sym (trans (count-sel Θ (dimCtx Θ) x (varsCtx Θ) (nodup-downFrom (len Θ)))
                                     (one (elem-downFrom (len Θ) x lxΘ) dx≡))) (≤-refl 1)
          kx : count (tup v) (Fv ρ′ (tup x)) ≡ 1
          kx = trans (ks x lxΘ v) (cong ind₀ (trans (cong (_∧ (dimv Γ v ==ℕ dimv Θ x)) mx)
                                                    (≡→==true (trans dv≡ (trans (sym eΘ) (sym dx≡))))))
      in subst (_≤ count (tup v) (cm (Fv ρ′) W)) kx (count-cm-≥ (tup v) (Fv ρ′) W (tup x) inW)
      where
      one : ∀ {x m} → elem x (varsCtx Θ) ≡ true → dimv Θ x ≡ m →
            (if elem x (varsCtx Θ) then (if dimv Θ x ==ℕ m then 1 else 0) else 0) ≡ 1
      one {x} {m} p q rewrite p | q | ==-refl m = refl
      ≡→==true : ∀ {a c} → a ≡ c → (true ∧ (a ==ℕ c)) ≡ true
      ≡→==true {a} refl = ==-refl a

  key-sub : ∀ {Γ τ Θ} → Ordered Γ → Γ ⊢ctx → Γ ⊢sub τ ∶ Θ → CFSub τ → ∀ x → T (x <ℕ len Θ) → ∀ v →
            count (tup v) (top (lookupₑ (⟦ τ ⟧ₛ (η Γ)) x)) ≡ ind₀ (elem v (fvTm (lookupₛ τ x)) ∧ (dimv Γ v ==ℕ dimv Θ x))
  key-sub oΓ wΓ (⟨⟩-wf _) _ x () v
  key-sub {Γ} oΓ wΓ (,-wf {σ = σ} {Δ = Δ} {t = t} {A = A} sσ dt) (cσ , ct) x lx v
    rewrite lenₑ-⟦⟧ₛ σ (η Γ) | snd (Sb.sub-sc closed sσ) with x ==ℕ len Δ in e
  ... | true = trans (support oΓ wΓ dt ct v) (cong (λ m → ind₀ (elem v (fvTm t) ∧ (dimv Γ v ==ℕ m))) (dim-[] A σ))
  ... | false = key-sub oΓ wΓ sσ cσ x (<suc-≢ x (len Δ) lx e) v
