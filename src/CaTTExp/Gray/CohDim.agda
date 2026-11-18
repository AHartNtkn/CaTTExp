------------------------------------------------------------------------
-- A derivable coh of two-tier L is at least as high as its pasting
-- context (the hypothesis DimOK of Gray.MarksFuel):
--
--   dimOK : Θ ⊢ps → Θ ⊢ty arr A t u → T (graySide Θ A t u) →
--           dimCtx Θ ≤ suc (dim A)
--
-- for every signature whose constants are closed and well typed
-- (S.Closed, SigOK; both trivial for pure L). `StableL` is
-- Gray.MarksFuel.Stable with DimOK discharged.
--
-- Steps, for a pasting context Θ with N = dim K(Θ):
--   ctx-dim    : dimCtx Θ ≤ N + 1 (every cell lies in a hom);
--   top-tuple  : Supp T has a tuple of rank N (every hom is inhabited);
--   supp-rank  : in any context, the support tuples of a derivable
--                t : A have rank ≤ dim A − 1 (by induction on the
--                derivation: F_ρ never raises rank, since a non-coh-case
--                coh has dim A = dim K(Δ) by the op case);
-- then: in the op case dim A = N; in the coh case Supp T ⊆ ↓supp t A,
-- and ranks only go down along the face order (Gray.Graded).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.CohDim (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.DownAgree 𝕊
open import CaTTExp.Gray.Graded 𝕊
open import CaTTExp.Gray.PsFacts 𝕊
open import CaTTExp.Gray.Orient 𝕊 using (chainε; chainε-false; flipIf)
open import CaTTExp.Gray.OrientRev 𝕊 using (Path; nil; cons; path⇐; path⇒)
open import CaTTExp.Gray.Typing 𝕊
open import CaTTExp.Gray.MarksSubst 𝕊 using (dim-[])
open import CaTTExp.Gray.MarksFuel 𝕊 using (DimOK; SigOK; tm-ty)
import CaTTExp.Gray.MarksFuel 𝕊 as MF
import CaTTExp.Subst 𝕊 graySide as S

------------------------------------------------------------------------
-- Numbers and lists.

private
  max-lub : ∀ {a b n} → a ≤ n → b ≤ n → max a b ≤ n
  max-lub {zero}  {b}     _       q       = q
  max-lub {suc a} {zero}  p       _       = p
  max-lub {suc a} {suc b} (s≤s p) (s≤s q) = s≤s (max-lub p q)

  max-≤l : ∀ a b → a ≤ max a b
  max-≤l zero    b       = z≤n
  max-≤l (suc a) zero    = ≤-refl (suc a)
  max-≤l (suc a) (suc b) = s≤s (max-≤l a b)

  max-≤r : ∀ a b → b ≤ max a b
  max-≤r zero    b       = ≤-refl b
  max-≤r (suc a) zero    = z≤n
  max-≤r (suc a) (suc b) = s≤s (max-≤r a b)

  maxL-ge : ∀ xs {x} → x ∈ᴺ xs → x ≤ maxL xs
  maxL-ge (y ∷ ys) (here refl) = max-≤l y (maxL ys)
  maxL-ge (y ∷ ys) (there m)   = ≤-trans (maxL-ge ys m) (max-≤r y (maxL ys))

  -- max a b is one of a, b
  max-is : ∀ a b → (max a b ≡ a) ⊎ (max a b ≡ b)
  max-is zero    b       = inj₂ refl
  max-is (suc a) zero    = inj₁ refl
  max-is (suc a) (suc b) with max-is a b
  ... | inj₁ e = inj₁ (cong suc e)
  ... | inj₂ e = inj₂ (cong suc e)

  max0 : ∀ y → max y 0 ≡ y
  max0 zero    = refl
  max0 (suc y) = refl

  pickM : ∀ {y m l} → (max y m ≡ y) ⊎ (max y m ≡ m) → m ∈ᴺ l → max y m ∈ᴺ (y ∷ l)
  pickM (inj₁ e) _ = here e
  pickM (inj₂ e) m = there (subst (_∈ᴺ _) (sym e) m)

  maxL-mem' : ∀ y ys → maxL (y ∷ ys) ∈ᴺ (y ∷ ys)
  maxL-mem' y []       = here (max0 y)
  maxL-mem' y (z ∷ zs) = pickM (max-is y (maxL (z ∷ zs))) (maxL-mem' z zs)

  maxL-mem : ∀ xs → (Σ Nat λ x → x ∈ᴺ xs) → maxL xs ∈ᴺ xs
  maxL-mem (y ∷ ys) _ = maxL-mem' y ys

  sum-ge : ∀ xs {x} → x ∈ᴺ xs → x ≤ sumL xs
  sum-ge (y ∷ ys) (here refl) = m≤m+n y (sumL ys)
  sum-ge (y ∷ ys) (there m)   = ≤-trans (sum-ge ys m) (n≤m+n y (sumL ys))

  lookup-entries : ∀ Γ {v C} → lookup Γ v ≡ just C → Any ((v , C) ≡_) (entries Γ)
  lookup-entries (Γ ▸ A) {v} e with v ==ℕ len Γ in q
  lookup-entries (Γ ▸ A) {v} refl | true
    rewrite ==ℕ-sound v (len Γ) (subst T (sym q) tt) = any-++r (entries Γ) (here refl)
  ... | false = any-++l (lookup-entries Γ e)

  -- The tail of upto r: 1 … r.
  utail : Nat → List Nat
  utail zero    = []
  utail (suc r) = utail r ++ (suc r ∷ [])

  upto≡ : ∀ r → upto r ≡ 0 ∷ utail r
  upto≡ zero    = refl
  upto≡ (suc r) = cong (_++ (suc r ∷ [])) (upto≡ r)

  dropLast-snoc : ∀ xs x → dropLast (xs ++ x ∷ []) ≡ xs
  dropLast-snoc []           x = refl
  dropLast-snoc (y ∷ [])     x = refl
  dropLast-snoc (y ∷ z ∷ zs) x = cong (y ∷_) (dropLast-snoc (z ∷ zs) x)

  idx≡ : ∀ r → homIdx (suc r) ≡ utail r
  idx≡ r rewrite upto≡ r = dropLast-snoc (utail r) (suc r)

  utail⇒ : ∀ r {k} → k ∈ᴺ utail r → T (0 <ℕ k) × T (k <ℕ suc r)
  utail⇒ (suc r) {k} m with any-++⁻ (utail r) m
  ... | inj₁ a with utail⇒ r a
  ...   | p , q = p , lt-step k r q
  utail⇒ (suc r) m | inj₂ (here refl) = tt , lt-refl (suc r)

  utail⇐ : ∀ r k → T (0 <ℕ k) → T (k <ℕ suc r) → k ∈ᴺ utail r
  utail⇐ zero    zero    () _
  utail⇐ zero    (suc k) _ ()
  utail⇐ (suc r) k p q with lt-split k r q
  ... | inj₁ q' = any-++l (utail⇐ r k p q')
  ... | inj₂ refl = any-++r (utail r) (here refl)

  idx⇒ : ∀ L {k} → k ∈ᴺ homIdx L → T (0 <ℕ k) × T (k <ℕ L)
  idx⇒ zero    ()
  idx⇒ (suc r) m = utail⇒ r (subst (λ l → _ ∈ᴺ l) (idx≡ r) m)

  pos-in-idx : ∀ k L → T (0 <ℕ k) → T (k <ℕ L) → k ∈ᴺ homIdx L
  pos-in-idx k (suc r) p q = subst (λ l → k ∈ᴺ l) (sym (idx≡ r)) (utail⇐ r k p q)
  pos-in-idx zero    zero p q = ⊥-elim p
  pos-in-idx (suc k) zero p ()

------------------------------------------------------------------------
-- Cells of a pasting context.

module Cells (Θ : Ctx) (P : PsFacts Θ) where
  private
    os = objs Θ
    N  = dimK (homs Θ)

  -- The El of a variable of positive dimension, in its hom.
  elOfVar : ∀ v C → lookup Θ v ≡ just C → isStar C ≡ false →
            Σ Nat λ k → T (0 <ℕ k) × T (k <ℕ countL os) ×
            Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (hcs (homAt Θ k))
  elOfVar v C e st with cellP P v C e st
  ... | k , h , p , q = k , p , q , filter⇐ (λ c → hom c ==ℕ k) (cells Θ) inCells (==ℕ-refl k)
    where
    inMk : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (mkEl os (v , C))
    inMk rewrite mkEl≡ os v C | h = here refl
    inCells : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (cells Θ)
    inCells = subst (Any _) (sym (cm≡ (mkEl os) (entries Θ)))
                (any-cm⁺ (mkEl os) (any-at (lookup-entries Θ e) inMk))

  homAt-in : ∀ k → T (0 <ℕ k) → T (k <ℕ countL os) → Any (homAt Θ k ≡_) (homs Θ)
  homAt-in k p q =
    subst (Any _) (sym (map≡ (homAt Θ) (homIdx (countL os))))
      (any-map⁺ (homAt Θ) (any-mono (λ { refl → refl }) (pos-in-idx k (countL os) p q)))

  hd-le : ∀ {h} → Any (h ≡_) (homs Θ) → hd h ≤ N
  hd-le {h} m =
    sum-ge (map hd (homs Θ))
      (subst (Any _) (sym (map≡ hd (homs Θ))) (any-map⁺ hd (any-mono (λ { refl → refl }) m)))

  hdim-le-hd : ∀ k {e} → Any (e ≡_) (hcs (homAt Θ k)) → hdim e ≤ hd (homAt Θ k)
  hdim-le-hd k {e} m =
    maxL-ge (map hdim (hcs (homAt Θ k)))
      (subst (Any _) (sym (map≡ hdim (hcs (homAt Θ k)))) (any-map⁺ hdim (any-mono (λ { refl → refl }) m)))

  var-dim : ∀ v C → lookup Θ v ≡ just C → dim C ≤ suc N
  var-dim v ⋆ e = z≤n
  var-dim v (arr B s t) e with elOfVar v (arr B s t) e refl
  ... | k , p , q , m = s≤s (≤-trans (hdim-le-hd k m) (hd-le (homAt-in k p q)))

  private
    ctx-le : ∀ Γ M → (∀ v C → lookup Γ v ≡ just C → dim C ≤ M) → dimCtx Γ ≤ M
    ctx-le ε       M f = z≤n
    ctx-le (Γ ▸ A) M f =
      max-lub (f (len Γ) A (lk-new Γ A))
              (ctx-le Γ M (λ v C e → f v C (lk-ext Γ A v e)))
      where
      lk-new : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
      lk-new Γ A rewrite ==-refl≡ (len Γ) = refl
      lk-lt : ∀ Γ v {C} → lookup Γ v ≡ just C → T (v <ℕ len Γ)
      lk-lt (Γ ▸ A) v e with v ==ℕ len Γ in q
      ... | true  = subst (λ w → T (w <ℕ suc (len Γ))) (sym (==ℕ-sound v (len Γ) (subst T (sym q) tt))) (lt-refl (len Γ))
      ... | false = weak< v (len Γ) (lk-lt Γ v e)
      lk-ext : ∀ Γ A v {C} → lookup Γ v ≡ just C → lookup (Γ ▸ A) v ≡ just C
      lk-ext Γ A v e rewrite lt-ne v (len Γ) (lk-lt Γ v e) = e

  ctx-dim : dimCtx Θ ≤ suc N
  ctx-dim = ctx-le Θ (suc N) var-dim

  ----------------------------------------------------------------------
  -- Supp T has a tuple of rank N.

  elIn : ∀ v C k → lookup Θ v ≡ just C → homOf os C ≡ just k →
         Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (hcs (homAt Θ k))
  elIn v C k e h = filter⇐ (λ c → hom c ==ℕ k) (cells Θ) inCells (==ℕ-refl k)
    where
    inMk : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (mkEl os (v , C))
    inMk rewrite mkEl≡ os v C | h = here refl
    inCells : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (cells Θ)
    inCells = subst (Any _) (sym (cm≡ (mkEl os) (entries Θ)))
                (any-cm⁺ (mkEl os) (any-at (lookup-entries Θ e) inMk))

  piece-top : ∀ h sg → piece h (hd h) sg ≡ piece h (hd h) true
  piece-top h sg rewrite ==-refl≡ (hd h) = refl

  -- Each hom has a cell of its top dimension.
  top-cell : ∀ {h} → Any (h ≡_) (homs Θ) → Σ Nat λ c → c ∈ᴺ piece h (hd h) true
  top-cell {h} m with any-witness (any-map⁻ (homAt Θ) (homIdx (countL os))
                                   (subst (Any _) (map≡ (homAt Θ) (homIdx (countL os))) m))
  ... | k , mk , refl with idx⇒ (countL os) mk
  ...   | p0 , pq with nonE P k p0 pq
  ...     | v , C , e , d , hk = top
    where
    H = homAt Θ k
    m₀ = elIn v C k e hk
    ne : Σ Nat λ x → x ∈ᴺ map hdim (hcs H)
    ne = _ , subst (Any _) (sym (map≡ hdim (hcs H))) (any-map⁺ hdim (any-mono (λ { refl → refl }) m₀))
    top : Σ Nat λ c → c ∈ᴺ piece H (hd H) true
    top with any-witness (any-map⁻ hdim (hcs H) (subst (Any _) (map≡ hdim (hcs H)) (maxL-mem (map hdim (hcs H)) ne)))
    ... | e' , me' , q rewrite ==-refl≡ (hd H) =
      lvl e' , subst (Any _) (sym (map≡ lvl _))
                 (any-map⁺ lvl (any-mono (λ { refl → refl })
                   (filter⇐ (λ c → hdim c ==ℕ hd H) (hcs H) me' (subst (λ n → T (hdim e' ==ℕ n)) (sym q) (==ℕ-refl (hdim e'))))))

  private
    path-top : ∀ hs s → (∀ {h} → Any (h ≡_) hs → Σ Nat λ c → c ∈ᴺ piece h (hd h) true) →
               Σ Tuple λ x → Path (λ _ → false) s hs (map hd hs) x
    path-top []       s f = [] , nil
    path-top (h ∷ hs) s f with f (here refl) | path-top hs (flipIf (odd (hd h)) s) (λ m → f (there m))
    ... | c , mc | x , p = c ∷ x , cons (subst (λ l → c ∈ᴺ l) (sym (piece-top h s)) mc) p

  top-tuple : Σ Tuple λ x → (x ∈L topT (homs Θ)) × (Faces.rank (cells Θ) x ≡ N)
  top-tuple with path-top (homs Θ) true top-cell
  ... | x , p = x , mem , Ranks.chain-rank Θ true N mem
    where
    mem : x ∈L topT (homs Θ)
    mem = subst (λ L → x ∈L L) (chainε-false true N (homs Θ)) (path⇐ (λ _ → false) p)

------------------------------------------------------------------------
-- Support ranks of derivable terms, in any context.

private
  rk : Ctx → Tuple → Nat
  rk Γ = Faces.rank (cells Γ)

  ht : Ctx → Nat → Nat
  ht Γ = Faces.hgt (cells Γ)

  rank-++ : ∀ Γ a b → rk Γ (a ++ b) ≡ rk Γ a + rk Γ b
  rank-++ Γ []      b = refl
  rank-++ Γ (w ∷ a) b =
    trans (cong (ht Γ w +_) (rank-++ Γ a b)) (sym (+-assoc (ht Γ w) (rk Γ a) (rk Γ b)))

  -- A variable's height is its dimension minus one (or 0).
  hgt-le : ∀ Γ v {C} → lookup Γ v ≡ just C → ht Γ v ≤ dim C ∸ 1
  hgt-le Γ v {C} eL rewrite findEl-cells (objs Γ) Γ v | eL | mkEl≡ (objs Γ) v C
    with homOf (objs Γ) C
  ... | nothing = z≤n
  ... | just k  = ≤-refl _

  -- A cell of Δ is a variable whose height is its dimension minus one.
  cell-var : ∀ Δ {e} → Any (e ≡_) (cells Δ) →
             Σ Ty λ C → (lookup Δ (lvl e) ≡ just C) × (ht Δ (lvl e) ≡ dim C ∸ 1)
  cell-var Δ {e} m
    with elAt-just (objs Δ) Δ (lvl e) (trans (sym (findEl-cells (objs Δ) Δ (lvl e))) (findEl-mem Δ m))
  ... | C , eL , k , eH , ee =
    C , eL , trans (cong (Faces.hgtM (cells Δ)) (findEl-mem Δ m)) (cong hdim ee)

  -- The operation case fixes the height of the pasting context.
  opDim : ∀ Δ A t u → T (opCase Δ A t u) → dimK (homs Δ) ≤ dim A
  opDim Δ ⋆ t u p = subst (_≤ 0) (sym (==ℕ-sound (dimK (homs Δ)) 0 (∧-fst {dimK (homs Δ) ==ℕ 0} p))) z≤n
  opDim Δ (arr B s s') t u p =
    subst (_≤ dim (arr B s s')) (==ℕ-sound (dim (arr B s s')) (dimK (homs Δ))
            (∧-fst {dim (arr B s s') ==ℕ dimK (homs Δ)} (∧-snd {endsOK Δ (arr B s s')} p)))
          (≤-refl _)

  -- Lists of supports.
  length-snoc : ∀ (xs : List TSet) y → length (xs ++ y ∷ []) ≡ suc (length xs)
  length-snoc []       y = refl
  length-snoc (x ∷ xs) y = cong suc (length-snoc xs y)

  tops-len : ∀ σ → length (topsSub σ) ≡ lenₛ σ
  tops-len ⟨⟩       = refl
  tops-len (σ ,ₛ t) = trans (length-snoc (topsSub σ) (topS t)) (cong suc (tops-len σ))

  sub-len : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → lenₛ σ ≡ len Δ
  sub-len (⟨⟩-wf _)  = refl
  sub-len (,-wf s _) = cong suc (sub-len s)

  nth-snoc-eq : ∀ xs y → nth (length xs) (xs ++ y ∷ []) ≡ y
  nth-snoc-eq []       y = refl
  nth-snoc-eq (x ∷ xs) y = nth-snoc-eq xs y

  nth-snoc-ne : ∀ xs y w → (w ==ℕ length xs) ≡ false → nth w (xs ++ y ∷ []) ≡ nth w xs
  nth-snoc-ne []       y zero    ()
  nth-snoc-ne []       y (suc w) q = refl
  nth-snoc-ne (x ∷ xs) y zero    q = refl
  nth-snoc-ne (x ∷ xs) y (suc w) q = nth-snoc-ne xs y w q

  -- F_ρ of a table tuple c has rank at most the rank of c, when each
  -- variable's image has rank at most the variable's height.
  module FRank (Γ Δ : Ctx) (tops : List TSet)
    (bnd : ∀ {w C} → lookup Δ w ≡ just C → ∀ {y} → y ∈L nth w tops → rk Γ y ≤ dim C ∸ 1) where
    F-rank : ∀ {s hs is c x} → (∀ {h} → Any (h ≡_) hs → Ranks.HomOK Δ h) →
             Path (λ _ → false) s hs is c → x ∈L Ftuple tops c → rk Γ x ≤ rk Δ c
    F-rank ok nil (here refl) = z≤n
    F-rank ok nil (there ())
    F-rank ok (cons {s = s} {h = h} {i = i} {c = w} {x = c'} mc p) mx
      with piece-mem h i s mc | prodT⇒ (nth w tops) (Ftuple tops c') mx
    ... | e , me , refl , _ | y , z , refl , my , mz with cell-var Δ (ok (here refl) me)
    ...   | C , eL , hq =
      subst (_≤ rk Δ (lvl e ∷ c')) (sym (rank-++ Γ y z))
        (+-mono (subst (rk Γ y ≤_) (sym hq) (bnd eL my)) (F-rank (λ m → ok (there m)) p mz))

mutual
  -- The top support tuples of a derivable t : A have rank ≤ dim A − 1.
  supp-rank : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ∀ {x} → x ∈L topS t → rk Γ x ≤ dim A ∸ 1
  supp-rank {Γ} (var-wf {i} w eL) (here refl) =
    subst (_≤ _) (sym (+-zero (ht Γ i))) (hgt-le Γ i eL)
  supp-rank (var-wf w eL) (there ())
  supp-rank (cst-wf w v) ()
  supp-rank {Γ} (coh-wf {Δ} {A} {t} {u} {σ} _ _ _ side sσ) {x} mx
    rewrite dim-[] A σ with cohCase Δ A t u
  ... | true = ⊥-elim (none mx)
    where
    none : x ∈L [] → ⊥
    none ()
  ... | false
    with any-witness (any-cm⁻ (Ftuple (topsSub σ)) (topT (homs Δ))
                       (subst (Any _) (cm≡ (Ftuple (topsSub σ)) (topT (homs Δ))) mx))
  ...   | c , mc , mxc
    with path⇒ (λ _ → false) (homs Δ) true (dimK (homs Δ))
           (subst (λ L → c ∈L L) (sym (chainε-false true (dimK (homs Δ)) (homs Δ))) mc)
  ...   | is , _ , p =
    ≤-trans (FRank.F-rank Γ Δ (topsSub σ) (sub-bnd sσ) (Ranks.homs-ok Δ) p mxc)
      (subst (_≤ dim A) (sym (Ranks.chain-rank Δ true (dimK (homs Δ)) mc)) (opDim Δ A t u side))

  -- The same for the images of the variables of a substitution.
  sub-bnd : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ∀ {w C} → lookup Δ w ≡ just C →
            ∀ {y} → y ∈L nth w (topsSub σ) → rk Γ y ≤ dim C ∸ 1
  sub-bnd (⟨⟩-wf _) () _
  sub-bnd (,-wf {σ} {Δ} {t} {A} sd d) {w} eL my with w ==ℕ len Δ in q
  sub-bnd {Γ} (,-wf {σ} {Δ} {t} {A} sd d) {w} refl {y} my | true =
    subst (rk Γ y ≤_) (cong (_∸ 1) (dim-[] A σ)) (supp-rank d (subst (λ L → _ ∈L L) eq my))
    where
    eq : nth w (topsSub σ ++ topS t ∷ []) ≡ topS t
    eq rewrite ==ℕ-sound w (len Δ) (subst T (sym q) tt) | sym (sub-len sd) | sym (tops-len σ)
      = nth-snoc-eq (topsSub σ) (topS t)
  ... | false = sub-bnd sd eL (subst (λ L → _ ∈L L) eq my)
    where
    eq : nth w (topsSub σ ++ topS t ∷ []) ≡ nth w (topsSub σ)
    eq = nth-snoc-ne (topsSub σ) (topS t) w
           (trans (cong (w ==ℕ_) (trans (tops-len σ) (sub-len sd))) q)

------------------------------------------------------------------------
-- The supports in a type, and in supp t A.

private
  ⊎-case : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
  ⊎-case (inj₁ a) f g = f a
  ⊎-case (inj₂ b) f g = g b

module _ (closed : S.Closed) (sig : SigOK) where
  private
    suppTy-rank : ∀ {Γ} A → Γ ⊢ty A → ∀ {x} → x ∈L suppTy A → rk Γ x ≤ dim A ∸ 1
    suppTy-rank ⋆           _ ()
    suppTy-rank (arr ⋆ _ _) _ ()
    suppTy-rank (arr (arr B s s') t u) (arr-wf dt du) mx =
      ⊎-case (any-++⁻ (suppTy (arr B s s')) mx)
        (λ m → ≤-step (suppTy-rank (arr B s s') (tm-ty closed sig dt) m))
        (λ m → ⊎-case (any-++⁻ (topS t) m)
                 (λ m' → ≤-step (supp-rank dt m'))
                 (λ m' → ≤-step (supp-rank du m')))

    supp-all : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ∀ {x} → x ∈L supp t A → rk Γ x ≤ dim A ∸ 1
    supp-all {t = t} {A} dt mx with any-++⁻ (topS t) mx
    ... | inj₁ m = supp-rank dt m
    ... | inj₂ m = suppTy-rank A (tm-ty closed sig dt) m

    ∨-case : ∀ a b → T (a ∨ b) → T a ⊎ T b
    ∨-case true  b p = inj₁ tt
    ∨-case false b p = inj₂ p

    -- The coh case: Supp T ⊆ ↓supp t A, so the top tuple of T lies
    -- below a support tuple of t, of rank ≤ dim A − 1.
    cohB : ∀ Θ (P : PsFacts Θ) A t → Θ ⊢tm t ∶ A → ∀ u → T (cohCase Θ A t u) → dimK (homs Θ) ≤ dim A
    cohB Θ P ⋆ t dt u ()
    cohB Θ P (arr B s s') t dt u c with Cells.top-tuple Θ P
    ... | f , mf , rf
      with any-witness (anyS⇒ (leqT (cells Θ) N f) (supp t A)
             (All-T (λ s → any (leqT (cells Θ) N s) (supp t A)) (fullT hs) cov (any-++r (lowerT N hs) mf)))
      where
      A  = arr B s s'
      hs = homs Θ
      N  = dimK hs
      cov : T (covers Θ (fullT hs) (supp t A))
      cov = ∧-snd {covers Θ (supp t A) (fullT hs)}
              (∧-fst {sameDown Θ (supp t A) (fullT hs)} (∧-snd {endsOK Θ A} c))
    ... | r , mr , q =
      subst (_≤ dim (arr B s s')) rf
        (≤-trans (Ranks.rank-mono Θ (graded Θ (inv P)) (Faces.leqT⇒ (cells Θ) (dimK (homs Θ)) f r q))
                 (≤-step (supp-all dt mr)))

  -- DimOK for two-tier L.
  dimOK : DimOK
  dimOK {Θ} {A} {t} {u} (ps d) (arr-wf dt du) side =
    ≤-trans (Cells.ctx-dim Θ P) (s≤s (side-dim (∨-case (cohCase Θ A t u) (opCase Θ A t u) side)))
    where
    P = fst (ps-facts d)
    side-dim : T (cohCase Θ A t u) ⊎ T (opCase Θ A t u) → dimK (homs Θ) ≤ dim A
    side-dim (inj₁ c) = cohB Θ P A t dt u c
    side-dim (inj₂ o) = opDim Θ A t u o

  -- Fuel stability for L, with DimOK discharged.
  module StableL = MF.Stable closed sig dimOK
