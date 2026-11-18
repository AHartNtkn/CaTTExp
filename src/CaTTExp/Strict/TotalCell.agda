------------------------------------------------------------------------
-- The total cell T of a pasting context, from its homs.
--
-- CaTTExp.Gray.Support's chainT computes T's table as an iterated
-- tensor of the tables ⟨Θₖ⟩ of the homs (`piece`). Here:
--   * chainT (h ∷ hs) is the tensor of h's table with chainT hs
--     (`chainT-cons`), and chainT [] is the unit;
--   * so if each hom's table is a cell between consecutive objects,
--     T is a cell from the first to the last object (`total-cell`).
-- What remains of the hypothesis (T-cell) of Strict.Soundness is the
-- statement `HomCells`: each hom of a pasting context has a cell as
-- its table.
------------------------------------------------------------------------
module CaTTExp.Strict.TotalCell where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Subst using (concatMap-cm; map-cm)
open import CaTTExp.Strict.Soundness using (twT; TCell)
open import CaTTExp.Strict.Tensor
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Tables of homs and of T.

sing : Nat → Tuple
sing v = v ∷ []

Ph : Hom → Tab
Ph h b i = map sing (piece h i b)

Ch : List Hom → Tab
Ch hs b k = chainT b k hs

private
  odd-flip : ∀ i sg → (if odd i then not sg else sg) ≡ flipN i sg
  odd-flip zero    sg = refl
  odd-flip (suc i) sg with odd i | odd-flip i sg
  ... | true  | e = trans (sym (not-not sg)) (cong not e)
    where
    not-not : ∀ b → not (not b) ≡ b
    not-not true  = refl
    not-not false = refl
  ... | false | e = cong not e

  map-cons : ∀ v (Y : Bag) → map (v ∷_) Y ≡ cm (λ y → (v ∷ y) ∷ []) Y
  map-cons v []      = refl
  map-cons v (y ∷ Y) = cong ((v ∷ y) ∷_) (map-cons v Y)

  prod1-prod : ∀ xs Y → prod1 xs Y ≡ prod (map sing xs) Y
  prod1-prod []       Y = refl
  prod1-prod (v ∷ xs) Y = cong₂ _++_ (map-cons v Y) (prod1-prod xs Y)

  concatMap-++ : ∀ (g : Nat → Bag) xs ys → concatMap g (xs ++ ys) ≡ concatMap g xs ++ concatMap g ys
  concatMap-++ g []       ys = refl
  concatMap-++ g (x ∷ xs) ys = trans (cong (g x ++_) (concatMap-++ g xs ys)) (sym (++-assocL (g x) _ _))

  <-suc+ : ∀ i d → T (i <ℕ suc (i + d))
  <-suc+ zero    d = tt
  <-suc+ (suc i) d = <-suc+ i d

  -- upto k with each element's witness i + d = k.
  data AllU (P : Nat → Set) : List Nat → Set where
    []ᵘ  : AllU P []
    _∷ᵘ_ : ∀ {x xs} → P x → AllU P xs → AllU P (x ∷ xs)

  AllU-++ : ∀ {P} xs ys → AllU P xs → AllU P ys → AllU P (xs ++ ys)
  AllU-++ []       ys []ᵘ       q = q
  AllU-++ (x ∷ xs) ys (p ∷ᵘ rs) q = p ∷ᵘ AllU-++ xs ys rs q

  upto-le : ∀ k → AllU (λ i → Σ Nat λ d → i + d ≡ k) (upto k)
  upto-le zero    = (0 , refl) ∷ᵘ []ᵘ
  upto-le (suc k) =
    AllU-++ (upto k) (suc k ∷ []) (mapU (upto k) (upto-le k)) ((0 , cong suc (+-zero k)) ∷ᵘ []ᵘ)
    where
    mapU : ∀ xs → AllU (λ i → Σ Nat λ d → i + d ≡ k) xs → AllU (λ i → Σ Nat λ d → i + d ≡ suc k) xs
    mapU []       []ᵘ             = []ᵘ
    mapU (x ∷ xs) ((d , e) ∷ᵘ rs) = (suc d , trans (+-suc x d) (cong suc e)) ∷ᵘ mapU xs rs

  filter-all : ∀ (p : Nat → Bool) xs → AllU (λ i → T (p i)) xs → filter p xs ≡ xs
  filter-all p []       []ᵘ       = refl
  filter-all p (x ∷ xs) (q ∷ᵘ qs) with p x
  ... | true  = cong (x ∷_) (filter-all p xs qs)

  mapAllU : ∀ {P Q : Nat → Set} xs → (∀ x → P x → Q x) → AllU P xs → AllU Q xs
  mapAllU []       f []ᵘ       = []ᵘ
  mapAllU (x ∷ xs) f (p ∷ᵘ rs) = f x p ∷ᵘ mapAllU xs f rs

  concatMap-ext : ∀ {P} (g h : Nat → Bag) xs → AllU P xs → (∀ x → P x → g x ≈ h x) →
                  concatMap g xs ≈ concatMap h xs
  concatMap-ext g h []       []ᵘ       f = ≈-refl
  concatMap-ext g h (x ∷ xs) (p ∷ᵘ rs) f = ++-cong (f x p) (concatMap-ext g h xs rs f)

  ∸-suc : ∀ i d k → i + d ≡ k → suc k ∸ i ≡ suc (k ∸ i)
  ∸-suc zero    d k e = refl
  ∸-suc (suc i) d (suc k) e = ∸-suc i d k (suc-inj e)
    where
    suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
    suc-inj refl = refl

  ∸-self : ∀ k → k ∸ k ≡ 0
  ∸-self zero    = refl
  ∸-self (suc k) = ∸-self k

  upto-sum : ∀ k f → concatMap (λ i → f i (k ∸ i)) (upto k) ≈ sumB k f
  upto-sum zero    f = ≡→≈ (++-[]L (f 0 0))
  upto-sum (suc k) f =
    begin
      concatMap (λ i → f i (suc k ∸ i)) (upto k ++ (suc k ∷ []))
    ≈⟨ ≡→≈ (concatMap-++ (λ i → f i (suc k ∸ i)) (upto k) (suc k ∷ [])) ⟩
      concatMap (λ i → f i (suc k ∸ i)) (upto k) ++ (f (suc k) (k ∸ k) ++ [])
    ≈⟨ ++-cong (concatMap-ext _ _ (upto k) (upto-le k)
                  (λ i de → ≡→≈ (cong (f i) (∸-suc i (fst de) k (snd de)))))
               (≡→≈ (trans (++-[]L _) (cong (f (suc k)) (∸-self k)))) ⟩
      concatMap (λ i → f i (suc (k ∸ i))) (upto k) ++ f (suc k) 0
    ≈⟨ ++-cong (upto-sum k (λ i j → f i (suc j))) (≈-refl {f (suc k) 0}) ⟩
      sumB k (λ i j → f i (suc j)) ++ f (suc k) 0
    ≈⟨ ≈-sym (sumB-last k f) ⟩
      sumB (suc k) f
    ∎

chainT-cons : ∀ h hs sg k → chainT sg k (h ∷ hs) ≈ (Ph h ⊗t Ch hs) sg k
chainT-cons h hs sg k =
  begin
    concatMap (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs))
              (filter (λ i → i <ℕ suc k) (upto k))
  ≈⟨ ≡→≈ (cong (concatMap _) (filter-all _ (upto k)
        (mapAllU (upto k) (λ i de → subst (λ m → T (i <ℕ suc m)) (snd de) (<-suc+ i (fst de))) (upto-le k)))) ⟩
    concatMap (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs)) (upto k)
  ≈⟨ concatMap-ext _ _ (upto k) (upto-le k)
        (λ i _ → ≡→≈ (trans (prod1-prod (piece h i sg) _)
                            (cong (λ c → prod (Ph h sg i) (chainT c (k ∸ i) hs)) (odd-flip i sg)))) ⟩
    concatMap (λ i → prod (Ph h sg i) (Ch hs (flipN i sg) (k ∸ i))) (upto k)
  ≈⟨ upto-sum k (λ i j → prod (Ph h sg i) (Ch hs (flipN i sg) j)) ⟩
    (Ph h ⊗t Ch hs) sg k
  ∎

------------------------------------------------------------------------
-- Tables equal pointwise give the same cells.

TabCell-≈ : ∀ {Γ x y n X X'} → (∀ b k → X b k ≈ X' b k) → TabCell Γ x y n X → TabCell Γ x y n X'
TabCell-≈ {Γ} {x} {y} {n} {X} {X'} e c = record
  { basis = λ b k → All-≈ (X b k) (X' b k) (e b k) (basis c b k)
  ; above = λ b d → ≈-trans (≈-sym (e b (suc (n + d)))) (above c b d)
  ; aug   = λ b → fst (aug c b) , ≈-trans (≈-sym (e b 0)) (snd (aug c b))
  ; chain = λ b k →
      ~-trans {δ Γ (X' b (suc k))} {δ Γ (X b (suc k))}
        (≈d (cm-cong _ _ _ (≈-sym (e b (suc k)))) (cm-cong _ _ _ (≈-sym (e b (suc k)))))
        (~-trans {δ Γ (X b (suc k))} (chain c b k) (≈d (e true k) (e false k)))
  }

------------------------------------------------------------------------
-- Hom tables along the objects, and the total cell.

-- Each hom hₖ has a cell as its table, between objects oₖ₋₁ and oₖ.
HC : Ctx → List Nat → List Hom → Set
HC Γ (o ∷ [])      []       = ⊤
HC Γ (o ∷ o' ∷ os) (h ∷ hs) = TabCell Γ o o' (hd h) (Ph h) × HC Γ (o' ∷ os) hs
HC Γ _             _        = ⊥

firstO lastO : List Nat → Nat
firstO = firstL
lastO = lastL

private
  Ch-nil : ∀ b k → unitTab b k ≈ Ch [] b k
  Ch-nil b zero    = ≈-refl
  Ch-nil b (suc k) = ≈-refl

total-cell : ∀ {Γ} os hs → HC Γ os hs → TabCell Γ (firstO os) (lastO os) (dimK hs) (Ch hs)
total-cell {Γ} (o ∷ [])      []       tt        = TabCell-≈ Ch-nil (unit-cell Γ o)
total-cell {Γ} (o ∷ o' ∷ os) (h ∷ hs) (ch , cs) =
  TabCell-≈ (λ b k → ≈-sym (chainT-cons h hs b k)) (tensor-cell ch (total-cell (o' ∷ os) hs cs))
total-cell (_ ∷ []) (_ ∷ _) ()
total-cell (_ ∷ _ ∷ _) [] ()
total-cell [] _ ()

private
  twT-twTab : ∀ hs sg m → twT hs sg m ≡ twTab (Ch hs) sg m
  twT-twTab hs sg zero    = refl
  twT-twTab hs sg (suc m) = cong₂ (λ S U → step S U (chainT sg (suc m) hs)) (twT-twTab hs false m) (twT-twTab hs true m)

  ends-objs : ∀ Θ A x y → T (endsOK Θ A) → endsTy A ≡ just (var x , var y) →
              (x ≡ firstO (objs Θ)) × (y ≡ lastO (objs Θ))
  ends-objs Θ A x y ok e with endsTy A
  ends-objs Θ A x y ok refl | just (var x , var y) =
    ==ℕ-sound x _ (∧-fst ok) , ==ℕ-sound y _ (∧-snd {x ==ℕ firstL (objs Θ)} ok)

-- Every pasting context has cells as hom tables.
HomCells : Set
HomCells = ∀ {Θ} → Θ ⊢ps → HC Θ (objs Θ) (homs Θ)

-- The hypothesis (T-cell) of Strict.Soundness follows.
T-cell-from : HomCells → TCell
T-cell-from hc {Θ} p A x y ok e
  with ends-objs Θ A x y ok e
... | refl , refl
  rewrite twT-twTab (homs Θ) true (dimK (homs Θ)) =
  tab-cell (total-cell (objs Θ) (homs Θ) (hc p)) (dimK (homs Θ)) true
