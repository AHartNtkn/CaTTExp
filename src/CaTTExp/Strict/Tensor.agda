------------------------------------------------------------------------
-- Cells as chain tables, and the Gray tensor of cells.
--
-- A cell of ν(K(Γ)) is presented by its table X b k (b = true is +):
--   * X b k consists of basis elements of degree k of the hom x → y;
--   * X b k = 0 above the dimension n;
--   * X b 0 is a single basis element;
--   * ∂X b (k+1) = X⁺ k − X⁻ k for both signs b and every k (above n
--     this says X⁻ n = X⁺ n).
-- `tab-cell` turns a table into an IsCellL tower.
--
-- The tensor of tables (Steiner 2004 §§ 2–3; Ara–Maltsiniotis,
-- arXiv 1607.00668, §A, "le produit tensoriel de tableaux")
--     (X ⊗ Y) b k = Σ_{i+j=k} X b i ⊗ Y ((−1)^i b) j
-- of a cell X : x → y and a cell Y : y → z is a cell x → z of
-- dimension n + m (`tensor-cell`). Inside K(Γ) the tensor of basis
-- elements is concatenation of tuples, and its boundary follows the
-- Leibniz rule (Complex.∂B-prod).
--
-- Signed chains are handled as formal differences (P, N) ~ "P − N",
-- with (P, N) ~ (P', N') iff P + N' = P' + N.
------------------------------------------------------------------------
module CaTTExp.Strict.Tensor where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Formal differences.

D : Set
D = Bag × Bag

infix 4 _~_
record _~_ (d d' : D) : Set where
  constructor mk~
  field un~ : fst d ++ snd d' ≈ fst d' ++ snd d
open _~_ public

private
  swap23 : ∀ A B C → (A ++ B) ++ C ≈ (A ++ C) ++ B
  swap23 A B C =
    ≈-trans (++-assoc A B C) (≈-trans (++-cong (≈-refl {A}) (++-comm B C)) (≈-sym (++-assoc A C B)))

~-refl : ∀ d → d ~ d
~-refl d = mk~ ≈-refl

~-sym : ∀ {d d'} → d ~ d' → d' ~ d
~-sym p = mk~ (≈-sym (un~ p))

~-trans : ∀ {d d' d''} → d ~ d' → d' ~ d'' → d ~ d''
~-trans {P , N} {P' , N'} {P'' , N''} (mk~ p) (mk~ q) = mk~ (
  ++-cancelʳ (P ++ N'') (P'' ++ N) N'
    (begin
       (P ++ N'') ++ N'
     ≈⟨ swap23 P N'' N' ⟩
       (P ++ N') ++ N''
     ≈⟨ ++-cong p (≈-refl {N''}) ⟩
       (P' ++ N) ++ N''
     ≈⟨ swap23 P' N N'' ⟩
       (P' ++ N'') ++ N
     ≈⟨ ++-cong q (≈-refl {N}) ⟩
       (P'' ++ N') ++ N
     ≈⟨ swap23 P'' N' N ⟩
       (P'' ++ N) ++ N'
     ∎))

-- Componentwise equality gives ~.
≈d : ∀ {P N P' N'} → P ≈ P' → N ≈ N' → (P , N) ~ (P' , N')
≈d p n = mk~ (++-cong p (≈-sym n))

zeroD : D
zeroD = [] , []

infixl 6 _⊕_
_⊕_ : D → D → D
d ⊕ d' = (fst d ++ fst d') , (snd d ++ snd d')

⊕-cong : ∀ {a a' b b'} → a ~ a' → b ~ b' → a ⊕ b ~ a' ⊕ b'
⊕-cong {P , N} {P' , N'} {Q , M} {Q' , M'} (mk~ p) (mk~ q) = mk~ (
  begin
    (P ++ Q) ++ (N' ++ M')
  ≈⟨ ++-interchange P Q N' M' ⟩
    (P ++ N') ++ (Q ++ M')
  ≈⟨ ++-cong p q ⟩
    (P' ++ N) ++ (Q' ++ M)
  ≈⟨ ++-interchange P' N Q' M ⟩
    (P' ++ Q') ++ (N ++ M)
  ∎)

⊕-zeroʳ : ∀ d → d ⊕ zeroD ~ d
⊕-zeroʳ (P , N) = ≈d (≡→≈ (++-[]L P)) (≡→≈ (++-[]L N))

zero-⊕ : ∀ d → zeroD ⊕ d ~ d
zero-⊕ d = mk~ ≈-refl

neg : D → D
neg d = snd d , fst d

sgn : Bool → D → D
sgn true  d = d
sgn false d = neg d

sgn-cong : ∀ s {d d'} → d ~ d' → sgn s d ~ sgn s d'
sgn-cong true  p = p
sgn-cong false {P , N} {P' , N'} (mk~ p) = mk~ (
  ≈-trans (++-comm N P') (≈-trans (≈-sym p) (++-comm P N')))

-- Tensoring a difference with a bag, on either side.
pr : D → Bag → D
pr d Y = prod (fst d) Y , prod (snd d) Y

pl : Bag → D → D
pl X d = prod X (fst d) , prod X (snd d)

pr-cong : ∀ {d d'} Y → d ~ d' → pr d Y ~ pr d' Y
pr-cong {P , N} {P' , N'} Y (mk~ p) = mk~ (
  ≈-trans (≡→≈ (sym (prod-++ˡ P N' Y)))
 (≈-trans (prod-congˡ Y p) (≡→≈ (prod-++ˡ P' N Y))))

pl-cong : ∀ X {d d'} → d ~ d' → pl X d ~ pl X d'
pl-cong X {P , N} {P' , N'} (mk~ p) = mk~ (
  ≈-trans (≈-sym (prod-++ʳ X P N'))
 (≈-trans (prod-congʳ X p) (prod-++ʳ X P' N)))

pl-zero : ∀ X → pl X zeroD ~ zeroD
pl-zero X = ≈d (≡→≈ (prod-nilʳ X)) (≡→≈ (prod-nilʳ X))

------------------------------------------------------------------------
-- Sums over i + j = k.

sumB : Nat → (Nat → Nat → Bag) → Bag
sumB zero    f = f 0 0
sumB (suc k) f = f 0 (suc k) ++ sumB k (λ i j → f (suc i) j)

sumD : Nat → (Nat → Nat → D) → D
sumD k f = sumB k (λ i j → fst (f i j)) , sumB k (λ i j → snd (f i j))

sumB-ext : ∀ k f g → (∀ i j → i + j ≡ k → f i j ≈ g i j) → sumB k f ≈ sumB k g
sumB-ext zero    f g h = h 0 0 refl
sumB-ext (suc k) f g h =
  ++-cong (h 0 (suc k) refl)
          (sumB-ext k (λ i j → f (suc i) j) (λ i j → g (suc i) j) (λ i j e → h (suc i) j (cong suc e)))

sumB-All : ∀ {P} k f → (∀ i j → i + j ≡ k → All P (f i j)) → All P (sumB k f)
sumB-All zero    f h = h 0 0 refl
sumB-All (suc k) f h =
  All-++ (f 0 (suc k)) _ (h 0 (suc k) refl) (sumB-All k (λ i j → f (suc i) j) (λ i j e → h (suc i) j (cong suc e)))

sumB-nil : ∀ k → sumB k (λ _ _ → []) ≡ []
sumB-nil zero    = refl
sumB-nil (suc k) = sumB-nil k

sumB-sum : ∀ k f g → sumB k (λ i j → f i j ++ g i j) ≈ sumB k f ++ sumB k g
sumB-sum zero    f g = ≈-refl
sumB-sum (suc k) f g =
  ≈-trans (++-cong (≈-refl {f 0 (suc k) ++ g 0 (suc k)})
                   (sumB-sum k (λ i j → f (suc i) j) (λ i j → g (suc i) j)))
          (++-interchange (f 0 (suc k)) (g 0 (suc k)) _ _)

sumB-last : ∀ k f → sumB (suc k) f ≈ sumB k (λ i j → f i (suc j)) ++ f (suc k) 0
sumB-last zero    f = ≈-refl
sumB-last (suc k) f =
  ≈-trans (++-cong (≈-refl {f 0 (suc (suc k))}) (sumB-last k (λ i j → f (suc i) j)))
          (≈-sym (++-assoc (f 0 (suc (suc k))) _ (f (suc (suc k)) 0)))

sumD-ext : ∀ k f g → (∀ i j → f i j ~ g i j) → sumD k f ~ sumD k g
sumD-ext zero    f g h = h 0 0
sumD-ext (suc k) f g h =
  ⊕-cong {f 0 (suc k)} {g 0 (suc k)} (h 0 (suc k))
         (sumD-ext k (λ i j → f (suc i) j) (λ i j → g (suc i) j) (λ i j → h (suc i) j))

sumD-sum : ∀ k f g → sumD k (λ i j → f i j ⊕ g i j) ~ sumD k f ⊕ sumD k g
sumD-sum k f g = ≈d (sumB-sum k (λ i j → fst (f i j)) (λ i j → fst (g i j))) (sumB-sum k (λ i j → snd (f i j)) (λ i j → snd (g i j)))

sumD-last : ∀ k f → sumD (suc k) f ~ sumD k (λ i j → f i (suc j)) ⊕ f (suc k) 0
sumD-last k f = ≈d (sumB-last k (λ i j → fst (f i j))) (sumB-last k (λ i j → snd (f i j)))

------------------------------------------------------------------------
-- Boundaries as differences.

module _ (Γ : Ctx) where

  δ : Bag → D
  δ X = ∂B Γ true X , ∂B Γ false X

  ∂B-sumB : ∀ b k f → ∂B Γ b (sumB k f) ≡ sumB k (λ i j → ∂B Γ b (f i j))
  ∂B-sumB b zero    f = refl
  ∂B-sumB b (suc k) f =
    trans (cm-++ (∂T Γ b) (f 0 (suc k)) _)
          (cong (∂B Γ b (f 0 (suc k)) ++_) (∂B-sumB b k (λ i j → f (suc i) j)))

  δ-sumB : ∀ k f → δ (sumB k f) ~ sumD k (λ i j → δ (f i j))
  δ-sumB k f = ≈d (≡→≈ (∂B-sumB true k f)) (≡→≈ (∂B-sumB false k f))

  δ-deg0 : ∀ {x y} X → All (Basis Γ x y 0) X → δ X ~ zeroD
  δ-deg0 X a = ≈d (≡→≈ (cm-zero (∂T Γ true) X a (λ c bc → ∂-deg0 c bc true)))
                  (≡→≈ (cm-zero (∂T Γ false) X a (λ c bc → ∂-deg0 c bc false)))

  -- The Leibniz rule for a tensor of chains.
  δ-prod : ∀ p C E → All (Deg Γ p) C → δ (prod C E) ~ pr (δ C) E ⊕ pl C (sgn (flipN p true) (δ E))
  δ-prod p C E hom =
    ≈d (≈-trans (∂B-prod Γ p true C E hom) (++-cong (≈-refl {prod (∂B Γ true C) E}) (≡→≈ (lemma true))))
       (≈-trans (∂B-prod Γ p false C E hom) (++-cong (≈-refl {prod (∂B Γ false C) E}) (≡→≈ (lemma false))))
    where
    s = flipN p true
    pair : ∀ s → sgn s (δ E) ≡ (∂B Γ s E , ∂B Γ (not s) E)
    pair true  = refl
    pair false = refl
    lemma : ∀ b → prod C (∂B Γ (flipN p b) E) ≡ (if b then fst (pl C (sgn s (δ E))) else snd (pl C (sgn s (δ E))))
    lemma true  = cong (λ d → prod C (fst d)) (sym (pair s))
    lemma false = trans (cong (λ c → prod C (∂B Γ c E)) (flipN-not p true))
                        (cong (λ d → prod C (snd d)) (sym (pair s)))

------------------------------------------------------------------------
-- Tables.

Tab : Set
Tab = Bool → Nat → Bag

β : Tab → Nat → D
β X k = X true k , X false k

record TabCell (Γ : Ctx) (x y n : Nat) (X : Tab) : Set where
  field
    basis : ∀ b k → All (Basis Γ x y k) (X b k)
    above : ∀ b d → X b (suc (n + d)) ≈ []
    aug   : ∀ b → Σ Tuple λ w → X b 0 ≈ w ∷ []
    chain : ∀ b k → δ Γ (X b (suc k)) ~ β X k
open TabCell public

-- The tower of a table.
twTab : Tab → Bool → Nat → Tower
twTab X b zero    = base (X b zero)
twTab X b (suc m) = step (twTab X false m) (twTab X true m) (X b (suc m))

top-twTab : ∀ X b m → top (twTab X b m) ≡ X b m
top-twTab X b zero    = refl
top-twTab X b (suc m) = refl

tab-cell : ∀ {Γ x y n X} → TabCell Γ x y n X → ∀ m b → IsCellL Γ x y m (twTab X b m)
tab-cell {Γ} {x} {y} {n} {X} c zero b =
  let (w , p) = aug c b in
  w , p , fst (All-≈ (X b 0) (w ∷ []) p (basis c b 0))
tab-cell {Γ} {x} {y} {n} {X} c (suc m) b =
  tab-cell c m false , tab-cell c m true , par m ,
  ce , basis c b (suc m)
  where
  par : ∀ m → Par (twTab X false m) (twTab X true m)
  par zero    = tt
  par (suc m) = ≈w-refl _ , ≈w-refl _
  ce : ∂B Γ true (X b (suc m)) ++ top (twTab X false m) ≈ ∂B Γ false (X b (suc m)) ++ top (twTab X true m)
  ce rewrite top-twTab X false m | top-twTab X true m =
    ≈-trans (un~ (chain c b m)) (++-comm (X true m) (∂B Γ false (X b (suc m))))

------------------------------------------------------------------------
-- The unit: the identity of an object.

unitTab : Tab
unitTab b zero    = [] ∷ []
unitTab b (suc k) = []

unit-cell : ∀ Γ x → TabCell Γ x x 0 unitTab
unit-cell Γ x = record
  { basis = bas ; above = λ b d → ≈-refl ; aug = λ b → [] , ≈-refl ; chain = ch }
  where
  bas : ∀ b k → All (Basis Γ x x k) (unitTab b k)
  bas b zero    = (refl , refl) , tt
  bas b (suc k) = tt
  ch : ∀ b k → δ Γ (unitTab b (suc k)) ~ β unitTab k
  ch b zero    = mk~ ≈-refl
  ch b (suc k) = mk~ ≈-refl

------------------------------------------------------------------------
-- The tensor.

infixr 7 _⊗t_
_⊗t_ : Tab → Tab → Tab
(X ⊗t Y) b k = sumB k (λ i j → prod (X b i) (Y (flipN i b) j))

private
  data Either (A B : Set) : Set where
    inl : A → Either A B
    inr : B → Either A B

  -- i + j > n + m forces i > n or j > m.
  split : ∀ n m d i j → i + j ≡ suc ((n + m) + d) →
          Either (Σ Nat λ e → i ≡ suc (n + e)) (Σ Nat λ e → j ≡ suc (m + e))
  split zero    m d zero    j e = inr (d , e)
  split zero    m d (suc i) j e = inl (i , refl)
  split (suc n) m d zero    j e = inr (suc (n + d) , trans e (cong suc (lem n m d)))
    where
    lem : ∀ n m d → suc ((n + m) + d) ≡ m + suc (n + d)
    lem n m d = trans (cong suc (trans (cong (_+ d) (+-comm n m)) (+-assoc m n d))) (sym (+-suc m (n + d)))
  split (suc n) m d (suc i) j e with split n m d i j (suc-inj e)
    where
    suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
    suc-inj refl = refl
  ... | inl (e' , p) = inl (e' , cong suc p)
  ... | inr q        = inr q

  -- The four sign cases of the boundary of x_i ⊗ y_j.
  key : ∀ (Xf Yf : Bool → Bag) b s →
        pr (Xf true , Xf false) (Yf (not (if b then s else not s))) ⊕ pl (Xf b) (sgn s (Yf true , Yf false))
        ~ (prod (Xf true) (Yf s) , prod (Xf false) (Yf (not s)))
  key Xf Yf true true =
    let A = prod (Xf true) (Yf true) ; B = prod (Xf true) (Yf false) ; E = prod (Xf false) (Yf false) in
    mk~ (begin
      (B ++ A) ++ E
    ≈⟨ ++-cong (++-comm B A) (≈-refl {E}) ⟩
      (A ++ B) ++ E
    ≈⟨ ++-assoc A B E ⟩
      A ++ (B ++ E)
    ≈⟨ ++-cong (≈-refl {A}) (++-comm B E) ⟩
      A ++ (E ++ B)
    ∎)
  key Xf Yf true false =
    let A = prod (Xf true) (Yf true) ; B = prod (Xf true) (Yf false) ; C = prod (Xf false) (Yf true) in
    mk~ (begin
      (A ++ B) ++ C
    ≈⟨ ++-cong (++-comm A B) (≈-refl {C}) ⟩
      (B ++ A) ++ C
    ≈⟨ ++-assoc B A C ⟩
      B ++ (A ++ C)
    ≈⟨ ++-cong (≈-refl {B}) (++-comm A C) ⟩
      B ++ (C ++ A)
    ∎)
  key Xf Yf false true  =
    mk~ (++-assoc (prod (Xf true) (Yf true)) (prod (Xf false) (Yf true)) (prod (Xf false) (Yf false)))
  key Xf Yf false false =
    mk~ (++-assoc (prod (Xf true) (Yf false)) (prod (Xf false) (Yf false)) (prod (Xf false) (Yf true)))

  flip-b : ∀ i b → flipN i b ≡ (if b then flipN i true else not (flipN i true))
  flip-b i true  = refl
  flip-b i false = flipN-not i true

module _ {Γ : Ctx} {x y z n m : Nat} {X Y : Tab}
         (cX : TabCell Γ x y n X) (cY : TabCell Γ y z m Y) where

  private
    Z = X ⊗t Y

    degX : ∀ b i → All (Deg Γ i) (X b i)
    degX b i = All-map (X b i) (λ c bc → snd bc) (basis cX b i)

    -- The boundary of one term.
    term : ∀ b i j → δ Γ (prod (X b i) (Y (flipN i b) j)) ~
                     pr (δ Γ (X b i)) (Y (flipN i b) j) ⊕ pl (X b i) (sgn (flipN i true) (δ Γ (Y (flipN i b) j)))
    term b i j = δ-prod Γ i (X b i) (Y (flipN i b) j) (degX b i)

    F G : Bool → Nat → Nat → D
    F b i j = pr (δ Γ (X b i)) (Y (flipN i b) j)
    G b i j = pl (X b i) (sgn (flipN i true) (δ Γ (Y (flipN i b) j)))

    sumF : ∀ b k → sumD (suc k) (F b) ~ sumD k (λ i j → pr (β X i) (Y (flipN (suc i) b) j))
    sumF b k =
      ~-trans {sumD (suc k) (F b)} {zeroD ⊕ sumD k (λ i j → F b (suc i) j)}
        (⊕-cong {F b 0 (suc k)} {zeroD}
                (~-trans {F b 0 (suc k)} {pr zeroD (Y b (suc k))}
                   (pr-cong (Y b (suc k)) (δ-deg0 Γ (X b 0) (basis cX b 0))) (mk~ ≈-refl))
                (~-refl (sumD k (λ i j → F b (suc i) j))))
        (sumD-ext k (λ i j → F b (suc i) j) _ (λ i j → pr-cong (Y (flipN (suc i) b) j) (chain cX b i)))

    sumG : ∀ b k → sumD (suc k) (G b) ~ sumD k (λ i j → pl (X b i) (sgn (flipN i true) (β Y j)))
    sumG b k =
      ~-trans {sumD (suc k) (G b)} {sumD k (λ i j → G b i (suc j)) ⊕ zeroD}
        (~-trans {sumD (suc k) (G b)} {sumD k (λ i j → G b i (suc j)) ⊕ G b (suc k) 0}
           (sumD-last k (G b))
           (⊕-cong {sumD k (λ i j → G b i (suc j))} (~-refl (sumD k (λ i j → G b i (suc j)))) g0))
     (~-trans {sumD k (λ i j → G b i (suc j)) ⊕ zeroD} (⊕-zeroʳ (sumD k (λ i j → G b i (suc j))))
        (sumD-ext k (λ i j → G b i (suc j)) _
           (λ i j → pl-cong (X b i) (sgn-cong (flipN i true) (chain cY (flipN i b) j)))))
      where
      g0 : G b (suc k) 0 ~ zeroD
      g0 = ~-trans {G b (suc k) 0} {pl (X b (suc k)) (sgn (flipN (suc k) true) zeroD)}
             (pl-cong (X b (suc k)) (sgn-cong (flipN (suc k) true)
                (δ-deg0 Γ (Y (flipN (suc k) b) 0) (basis cY _ 0))))
             (~-trans {pl (X b (suc k)) (sgn (flipN (suc k) true) zeroD)} {pl (X b (suc k)) zeroD}
                (pl-cong (X b (suc k)) (sz (flipN (suc k) true))) (pl-zero (X b (suc k))))
        where
        sz : ∀ s → sgn s zeroD ~ zeroD
        sz true  = mk~ ≈-refl
        sz false = mk~ ≈-refl

    pointwise : ∀ b i j → pr (β X i) (Y (flipN (suc i) b) j) ⊕ pl (X b i) (sgn (flipN i true) (β Y j))
                        ~ (prod (X true i) (Y (flipN i true) j) , prod (X false i) (Y (flipN i false) j))
    pointwise b i j
      rewrite flip-b i b | flipN-not i true = key (λ c → X c i) (λ c → Y c j) b (flipN i true)

  tensor-chain : ∀ b k → δ Γ (Z b (suc k)) ~ β Z k
  tensor-chain b k =
    ~-trans {δ Γ (Z b (suc k))} {sumD (suc k) (λ i j → F b i j ⊕ G b i j)}
      (~-trans {δ Γ (Z b (suc k))} {sumD (suc k) (λ i j → δ Γ (prod (X b i) (Y (flipN i b) j)))}
         (δ-sumB Γ (suc k) (λ i j → prod (X b i) (Y (flipN i b) j))) (sumD-ext (suc k) _ _ (term b)))
   (~-trans {sumD (suc k) (λ i j → F b i j ⊕ G b i j)} {sumD (suc k) (F b) ⊕ sumD (suc k) (G b)}
      (sumD-sum (suc k) (F b) (G b))
   (~-trans {sumD (suc k) (F b) ⊕ sumD (suc k) (G b)}
            {sumD k (λ i j → pr (β X i) (Y (flipN (suc i) b) j)) ⊕ sumD k (λ i j → pl (X b i) (sgn (flipN i true) (β Y j)))}
      (⊕-cong {sumD (suc k) (F b)} (sumF b k) (sumG b k))
   (~-trans {_} {sumD k (λ i j → pr (β X i) (Y (flipN (suc i) b) j) ⊕ pl (X b i) (sgn (flipN i true) (β Y j)))}
      (~-sym {sumD k (λ i j → pr (β X i) (Y (flipN (suc i) b) j) ⊕ pl (X b i) (sgn (flipN i true) (β Y j)))}
             (sumD-sum k _ _))
      (sumD-ext k _ _ (pointwise b)))))

  tensor-cell : TabCell Γ x z (n + m) Z
  tensor-cell = record { basis = bas ; above = abv ; aug = ag ; chain = tensor-chain }
    where
    bas : ∀ b k → All (Basis Γ x z k) (Z b k)
    bas b k = sumB-All k _ (λ i j e →
      subst (λ l → All (Basis Γ x z l) (prod (X b i) (Y (flipN i b) j))) e
            (All-prod (X b i) (Y (flipN i b) j) (basis cX b i) (basis cY _ j)))
    abv : ∀ b d → Z b (suc ((n + m) + d)) ≈ []
    abv b d =
      ≈-trans (sumB-ext (suc ((n + m) + d)) _ (λ _ _ → []) pt) (≡→≈ (sumB-nil (suc ((n + m) + d))))
      where
      pt : ∀ i j → i + j ≡ suc ((n + m) + d) → prod (X b i) (Y (flipN i b) j) ≈ []
      pt i j e with split n m d i j e
      ... | inl (e' , refl) = prod-congˡ (Y (flipN i b) j) (above cX b e')
      ... | inr (e' , refl) = ≈-trans (prod-congʳ (X b i) (above cY (flipN i b) e')) (≡→≈ (prod-nilʳ (X b i)))
    ag : ∀ b → Σ Tuple λ w → Z b 0 ≈ w ∷ []
    ag b =
      let (w , p) = aug cX b ; (w' , q) = aug cY b in
      (w ++ w') ,
      ≈-trans (prod-congˡ (Y b 0) p)
     (≈-trans (prod-congʳ (w ∷ []) q) ≈-refl)
