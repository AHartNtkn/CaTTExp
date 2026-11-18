------------------------------------------------------------------------
-- The strict model of two-tier L: every term over a context Γ is read
-- as a tower of chains of K(Γ) (its top chain is CaTTExp.Gray.Support's
-- topS), and substitutions act on such towers by the chain map
-- applyF (topsSub σ). This module sets up that interpretation:
--
--  * towerOf t A, the table of t : A, and IsCellTm Γ t A, "it is a cell
--    of ν(K(Γ)) in the hom between the endpoints of A";
--  * variables of a pasting context are cells (var-cell);
--  * a substitution whose terms are cells maps cells of ν(K(Θ)) to
--    cells of ν(K(Γ)) (SubstMap.transport-σ), i.e. it is a morphism
--    of augmented directed complexes K(Θ) → K(Γ).
--
-- Soundness itself is in CaTTExp.Strict.Soundness.
------------------------------------------------------------------------
module CaTTExp.Strict.L where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Subst ∅ graySide as S

------------------------------------------------------------------------
-- Small facts.

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
var-inj refl = refl

,-inj₁ : ∀ {A B : Set} {a a' : A} {b b' : B} → (a , b) ≡ (a' , b') → a ≡ a'
,-inj₁ refl = refl

,-inj₂ : ∀ {A B : Set} {a a' : A} {b b' : B} → (a , b) ≡ (a' , b') → b ≡ b'
,-inj₂ refl = refl

==-true : ∀ n → (n ==ℕ n) ≡ true
==-true zero    = refl
==-true (suc n) = ==-true n

==→≡ : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
==→≡ i n p = ==ℕ-sound i n (subst T (sym p) tt)

<→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
<→≢ zero    (suc n) _ = refl
<→≢ (suc i) (suc n) p = <→≢ i n p

<-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
<-suc zero    (suc n) _ = tt
<-suc (suc i) (suc n) p = <-suc i n p

n<suc : ∀ n → T (n <ℕ suc n)
n<suc zero    = tt
n<suc (suc n) = n<suc n

dim-sub : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-sub ⋆           σ = refl
dim-sub (arr A _ _) σ = cong suc (dim-sub A σ)

------------------------------------------------------------------------
-- Cells of K(Γ)(x, y).

IsCellL : Ctx → Nat → Nat → Nat → Tower → Set
IsCellL Γ x y = Cells.IsCell (∂T Γ) (Basis Γ x y)

-- The table of t : A.
towerOf : Tm → Ty → Tower
towerOf t ⋆                     = base []
towerOf t (arr ⋆ _ _)           = base (topS t)
towerOf t (arr (arr B a b) s u) = step (towerOf s (arr B a b)) (towerOf u (arr B a b)) (topS t)

-- t : A is a cell of ν(K(Γ)) between objects of Γ.
IsCellTm : Ctx → Tm → Ty → Set
IsCellTm Γ t ⋆           = Σ Nat λ i → (t ≡ var i) × (lookup Γ i ≡ just ⋆)
IsCellTm Γ t (arr A s u) =
  Σ (Nat × Nat) λ e → (endsV (arr A s u) ≡ just e) ×
    (lookup Γ (fst e) ≡ just ⋆) × (lookup Γ (snd e) ≡ just ⋆) ×
    IsCellL Γ (fst e) (snd e) (dim A) (towerOf t (arr A s u))

top-towerOf : ∀ t A s u → top (towerOf t (arr A s u)) ≡ topS t
top-towerOf t ⋆           s u = refl
top-towerOf t (arr _ _ _) s u = refl

Par-same : ∀ a b A s u → Par (towerOf a (arr A s u)) (towerOf b (arr A s u))
Par-same a b ⋆               s u = tt
Par-same a b (arr B a' b')   s u = ≈w-refl _ , ≈w-refl _

------------------------------------------------------------------------
-- Pasting contexts: every type's boundary consists of variables whose
-- types are the type's lower part.

VarTower : Ctx → Ty → Set
VarTower Γ ⋆           = ⊤
VarTower Γ (arr B s t) =
  Σ Nat λ i → Σ Nat λ j → (s ≡ var i) × (t ≡ var j) × (lookup Γ i ≡ just B) × (lookup Γ j ≡ just B)

PsInv : Ctx → Set
PsInv Γ = ∀ i B → lookup Γ i ≡ just B → VarTower Γ B

lookup-lt : ∀ Γ i {B} → lookup Γ i ≡ just B → T (i <ℕ len Γ)
lookup-lt (Γ ▸ A) i eq with i ==ℕ len Γ in e
... | true  = subst (λ k → T (k <ℕ suc (len Γ))) (sym (==→≡ i (len Γ) e)) (n<suc (len Γ))
... | false = <-suc i (len Γ) (lookup-lt Γ i eq)

lookup-ext : ∀ Γ C i {B} → lookup Γ i ≡ just B → lookup (Γ ▸ C) i ≡ just B
lookup-ext Γ C i eq rewrite <→≢ i (len Γ) (lookup-lt Γ i eq) = eq

lookup-new : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
lookup-new Γ A rewrite ==-true (len Γ) = refl

VarTower-ext : ∀ Γ C B → VarTower Γ B → VarTower (Γ ▸ C) B
VarTower-ext Γ C ⋆           _                       = tt
VarTower-ext Γ C (arr B s t) (i , j , qs , qt , li , lj) =
  i , j , qs , qt , lookup-ext Γ C i li , lookup-ext Γ C j lj

ps-inv : ∀ {Γ x A} → Γ ⊢ps x ∶ A → PsInv Γ × (lookup Γ x ≡ just A)
ps-inv pss = inv , refl
  where
  inv : PsInv (ε ▸ ⋆)
  inv i B eq with i ==ℕ 0
  inv i B refl | true = tt
  inv i B ()   | false
ps-inv {Γ₂} (pse {Γ} {x} {A} d) = inv , lookup-new (Γ ▸ A) (arr A (var x) (var (len Γ)))
  where
  IH = ps-inv d
  invΓ = fst IH
  lx   = snd IH
  Γ₁ = Γ ▸ A
  F  = arr A (var x) (var (len Γ))
  lift2 : ∀ B → VarTower Γ B → VarTower Γ₂ B
  lift2 B v = VarTower-ext Γ₁ F B (VarTower-ext Γ A B v)
  inv : PsInv Γ₂
  inv i B eq with i ==ℕ suc (len Γ) | i ==ℕ len Γ
  inv i B refl | true  | _ =
    x , len Γ , refl , refl ,
    lookup-ext Γ₁ F x (lookup-ext Γ A x lx) ,
    lookup-ext Γ₁ F (len Γ) (lookup-new Γ A)
  inv i B refl | false | true  = lift2 A (invΓ x A lx)
  inv i B eq   | false | false = lift2 B (invΓ i B eq)
ps-inv (psd {Γ} {f} {A} {x} {y} d) with ps-inv d
... | invΓ , lf with invΓ f _ lf
...   | (i , j , refl , refl , li , lj) = invΓ , lj

psInv : ∀ {Γ} → Γ ⊢ps → PsInv Γ
psInv (ps d) = fst (ps-inv d)

------------------------------------------------------------------------
-- Variables of a pasting context are cells.

private
  deg-single : ∀ Γ i {B} → lookup Γ i ≡ just B → deg Γ (i ∷ []) ≡ dim B ∸ 1
  deg-single Γ i eq = trans (cong (λ m → hdimTy m + 0) eq) (+-zero _)

  WFT-single : ∀ Γ i {B x y} → lookup Γ i ≡ just B → endsV B ≡ just (x , y) → WFT Γ x y (i ∷ [])
  WFT-single Γ i eq e = _ , trans (cong endsL eq) e , refl

vc : ∀ {Γ} → PsInv Γ → ∀ A i → lookup Γ i ≡ just A → IsCellTm Γ (var i) A

var-cell-step : ∀ {Γ} → PsInv Γ → ∀ i B a b j k →
  lookup Γ i ≡ just (arr (arr B a b) (var j) (var k)) →
  lookup Γ j ≡ just (arr B a b) → lookup Γ k ≡ just (arr B a b) →
  IsCellTm Γ (var j) (arr B a b) → IsCellTm Γ (var k) (arr B a b) →
  IsCellTm Γ (var i) (arr (arr B a b) (var j) (var k))
vc inv ⋆ i eq = i , refl , eq
vc {Γ} inv (arr ⋆ s u) i eq with inv i _ eq
... | (j , k , refl , refl , lj , lk) =
  (j , k) , refl , lj , lk ,
  ((i ∷ []) , ≈-refl , WFT-single Γ i eq refl , deg-single Γ i eq)
vc {Γ} inv (arr (arr B a b) s u) i eq =
  let (j , k , qs , qu , lj , lk) = inv i _ eq in
  subst₂' (λ s' u' → IsCellTm Γ (var i) (arr (arr B a b) s' u')) (sym qs) (sym qu)
    (var-cell-step inv i B a b j k
       (subst₂' (λ s' u' → lookup Γ i ≡ just (arr (arr B a b) s' u')) qs qu eq) lj lk
       (vc inv (arr B a b) j lj) (vc inv (arr B a b) k lk))
  where
  subst₂' : ∀ {A : Set} (P : A → A → Set) {x y u v} → x ≡ y → u ≡ v → P x u → P y v
  subst₂' P refl refl p = p

var-cell : ∀ {Γ} → PsInv Γ → ∀ i A → lookup Γ i ≡ just A → IsCellTm Γ (var i) A
var-cell inv i A eq = vc inv A i eq

var-cell-step {Γ} inv i B a b j k eq lj lk (e , ee , l₁ , l₂ , cj) (e' , ee' , _ , _ , ck) =
  e , ee , l₁ , l₂ ,
  ( cj , subst (λ e'' → IsCellL Γ (fst e'') (snd e'') (dim B) (towerOf (var k) (arr B a b)))
               (just-inj (trans (sym ee') ee)) ck
  , Par-same (var j) (var k) B a b
  , chain
  , ((WFT-single Γ i eq ee , deg-single Γ i eq) , tt) )
  where
  faces : ∀ c → ∂T Γ c (i ∷ []) ≡ (((if c then k else j) ∷ []) ∷ [])
  faces c = cong (λ m → here c (facesTy m) [] ++ []) eq
  chain : Cells.ChainEq (∂T Γ) (Basis Γ (fst e) (snd e)) ((i ∷ []) ∷ [])
            (top (towerOf (var j) (arr B a b))) (top (towerOf (var k) (arr B a b)))
  chain rewrite top-towerOf (var j) B a b | top-towerOf (var k) B a b
              | faces true | faces false = ++-comm ((k ∷ []) ∷ []) ((j ∷ []) ∷ [])

------------------------------------------------------------------------
-- Endpoints under substitution.

endsV-arr⋆ : ∀ a b {p q} → endsV (arr ⋆ a b) ≡ just (p , q) → (a ≡ var p) × (b ≡ var q)
endsV-arr⋆ (var a) (var b) refl = refl , refl
endsV-arr⋆ (var a) (coh _ _ _) ()
endsV-arr⋆ (var a) (cst ())
endsV-arr⋆ (coh _ _ _) b ()
endsV-arr⋆ (cst ()) b

ends-sub : ∀ B σ {x z p q} → endsV B ≡ just (x , z) → endsV (B [ σ ]ty) ≡ just (p , q) →
           (lookupₛ σ x ≡ var p) × (lookupₛ σ z ≡ var q)
ends-sub ⋆ σ ()
ends-sub (arr ⋆ (var x) (var z)) σ refl e = endsV-arr⋆ (lookupₛ σ x) (lookupₛ σ z) e
ends-sub (arr ⋆ (var x) (coh _ _ _)) σ ()
ends-sub (arr ⋆ (var x) (cst ()))    σ
ends-sub (arr ⋆ (coh _ _ _) _)       σ ()
ends-sub (arr ⋆ (cst ()) _)          σ
ends-sub (arr (arr B s t) _ _) σ e e' = ends-sub (arr B s t) σ e e'

ends-sub→ : ∀ B σ {x z p q} → endsV B ≡ just (x , z) →
            lookupₛ σ x ≡ var p → lookupₛ σ z ≡ var q → endsV (B [ σ ]ty) ≡ just (p , q)
ends-sub→ ⋆ σ ()
ends-sub→ (arr ⋆ (var x) (var z)) σ refl ex ez rewrite ex | ez = refl
ends-sub→ (arr ⋆ (var x) (coh _ _ _)) σ ()
ends-sub→ (arr ⋆ (var x) (cst ()))    σ
ends-sub→ (arr ⋆ (coh _ _ _) _)       σ ()
ends-sub→ (arr ⋆ (cst ()) _)          σ
ends-sub→ (arr (arr B s t) _ _) σ e ex ez = ends-sub→ (arr B s t) σ e ex ez

endsL-inv : ∀ m {e} → endsL m ≡ just e → Σ Ty λ B → (m ≡ just B) × (endsV B ≡ just e)
endsL-inv (just B) p = B , refl , p

------------------------------------------------------------------------
-- Towers commute with substitution.

tower-sub : ∀ t A σ → S.ScTm (lenₛ σ) t → S.ScTy (lenₛ σ) A →
            towerOf (t [ σ ]tm) (A [ σ ]ty) ≈w mapTw (applyF (topsSub σ)) (towerOf t A)
tower-sub t ⋆                     σ p q = ≈-refl
tower-sub t (arr ⋆ a b)           σ p q = topS-sub t σ p
tower-sub t (arr (arr B a b) s u) σ p (qA , qs , qu) =
  tower-sub s (arr B a b) σ qs qA , tower-sub u (arr B a b) σ qu qA , topS-sub t σ p

mapTw-ext : ∀ (f g : Bag → Bag) → (∀ c → f c ≡ g c) → ∀ X → mapTw f X ≡ mapTw g X
mapTw-ext f g h (base c)     = cong base (h c)
mapTw-ext f g h (step S U c) =
  cong₂ (λ X Y → step X Y (f c)) (mapTw-ext f g h S) (mapTw-ext f g h U)
  ⟨≡⟩ cong (step (mapTw g S) (mapTw g U)) (h c)
  where
  infixr 2 _⟨≡⟩_
  _⟨≡⟩_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⟨≡⟩_ = trans

------------------------------------------------------------------------
-- Algebra for one step of the chain-map property.

private
  prod-++ˡ≈ : ∀ X X' Y → prod X Y ++ prod X' Y ≈ prod (X ++ X') Y
  prod-++ˡ≈ X X' Y = ≡→≈ (sym (prod-++ˡ X X' Y))

chain-step : ∀ (∂C ∂D G H K PD : Bool → Bag) (C D Cs Ct : Bag) p →
  (∀ b → PD b ≈ prod (∂C b) D ++ prod C (∂D (flipN p b))) →
  (∂C true ++ Cs ≈ ∂C false ++ Ct) →
  (∀ b → H b ≈ prod (if b then Ct else Cs) D) →
  (∀ b → K b ≈ prod C (G (flipN p b))) →
  (∀ b → ∂D b ++ G (not b) ≈ ∂D (not b) ++ G b) →
  ∀ b → PD b ++ (H (not b) ++ K (not b)) ≈ PD (not b) ++ (H b ++ K b)
chain-step ∂C ∂D G H K PD C D Cs Ct p hP E hH hK IH = main
  where
  X : Bool → Bag
  X b = if b then Ct else Cs
  half : ∀ b → PD b ++ (H (not b) ++ K (not b)) ≈
               prod (∂C b ++ X (not b)) D ++ prod C (∂D (flipN p b) ++ G (flipN p (not b)))
  half b =
    begin
      PD b ++ (H (not b) ++ K (not b))
    ≈⟨ ++-cong (hP b) (++-cong (hH (not b)) (hK (not b))) ⟩
      (prod (∂C b) D ++ prod C (∂D (flipN p b))) ++ (prod (X (not b)) D ++ prod C (G (flipN p (not b))))
    ≈⟨ ++-interchange (prod (∂C b) D) (prod C (∂D (flipN p b))) (prod (X (not b)) D) (prod C (G (flipN p (not b)))) ⟩
      (prod (∂C b) D ++ prod (X (not b)) D) ++ (prod C (∂D (flipN p b)) ++ prod C (G (flipN p (not b))))
    ≈⟨ ++-cong (prod-++ˡ≈ (∂C b) (X (not b)) D)
               (≈-sym (prod-++ʳ C (∂D (flipN p b)) (G (flipN p (not b))))) ⟩
      prod (∂C b ++ X (not b)) D ++ prod C (∂D (flipN p b) ++ G (flipN p (not b)))
    ∎
  b' = flipN p true
  fl : flipN p false ≡ not b'
  fl = flipN-not p true
  mid : ∂D b' ++ G (flipN p false) ≈ ∂D (flipN p false) ++ G b'
  mid = subst (λ c → ∂D b' ++ G c ≈ ∂D c ++ G b') (sym fl) (IH b')
  main-true : PD true ++ (H false ++ K false) ≈ PD false ++ (H true ++ K true)
  main-true =
    begin
      PD true ++ (H false ++ K false)
    ≈⟨ half true ⟩
      prod (∂C true ++ Cs) D ++ prod C (∂D b' ++ G (flipN p false))
    ≈⟨ ++-cong (prod-congˡ D E) (prod-congʳ C mid) ⟩
      prod (∂C false ++ Ct) D ++ prod C (∂D (flipN p false) ++ G b')
    ≈⟨ ≈-sym (half false) ⟩
      PD false ++ (H true ++ K true)
    ∎
  main : ∀ b → PD b ++ (H (not b) ++ K (not b)) ≈ PD (not b) ++ (H b ++ K b)
  main true  = main-true
  main false = ≈-sym main-true

cm-zero : ∀ {P : Tuple → Set} (g : Tuple → Bag) X → All P X → (∀ c → P c → g c ≡ []) → cm g X ≡ []
cm-zero g []      _        _ = refl
cm-zero g (x ∷ X) (p , qs) h = cong₂ _++_ (h x p) (cm-zero g X qs h)

All-prod : ∀ {Γ x z y k l} C D → All (Basis Γ x z k) C → All (Basis Γ z y l) D →
           All (Basis Γ x y (k + l)) (prod C D)
All-prod {Γ} {x} {z} {y} {k} {l} C D aC aD =
  All-cm _ C aC (λ c bc → All-cm _ D aD (λ d bd → Basis-++ Γ x z y k l c d bc bd , tt))

private
  +-zero-inv : ∀ m n → m + n ≡ 0 → (m ≡ 0) × (n ≡ 0)
  +-zero-inv zero zero _ = refl , refl

  dim-zero : ∀ B → dim B ≡ 0 → B ≡ ⋆
  dim-zero ⋆ _ = refl

-- Tuples of degree 0 have no boundary.
∂-deg0 : ∀ {Γ x y} c → Basis Γ x y 0 c → ∀ b → ∂T Γ b c ≡ []
∂-deg0 []      _ b = refl
∂-deg0 {Γ} (v ∷ c) ((z , ev , wft) , dg) b with endsL-inv (lookup Γ v) ev
... | (⋆ , lv , ())
... | (arr B₀ s₀ u₀ , lv , eB) =
  let (h0 , d0) = +-zero-inv (hdimV Γ v) (deg Γ c) dg
      B₀⋆ = dim-zero B₀ (trans (sym (cong hdimTy lv)) h0)
  in cong₂ (λ F Z → here b F c ++ consB v Z)
       (trans (cong facesTy lv) (cong (λ B → facesTy (just (arr B s₀ u₀))) B₀⋆))
       (∂-deg0 c (wft , d0) _)

------------------------------------------------------------------------
-- Substitutions whose terms are cells act on cells.

Cellular : Ctx → Sub → Ctx → Set
Cellular Γ σ Θ = ∀ v B → lookup Θ v ≡ just B → IsCellTm Γ (lookupₛ σ v) (B [ σ ]ty)

module SubstMap {Γ Θ : Ctx} {σ : Sub}
  (cellσ : Cellular Γ σ Θ) (lenσ : lenₛ σ ≡ len Θ) (invΘ : PsInv Θ) where

  Sσ : List Bag
  Sσ = topsSub σ

  Fσ : Tuple → Bag
  Fσ = Ftuple Sσ

  nthσ : ∀ v {B} → lookup Θ v ≡ just B → nth v Sσ ≡ topS (lookupₛ σ v)
  nthσ v eq = nth-topsSub σ v (subst (λ n → T (v <ℕ n)) (sym lenσ) (lookup-lt Θ v eq))

  -- The cell that σ assigns to a hom variable v of Θ.
  vcell : ∀ v x z x' → endsL (lookup Θ v) ≡ just (x , z) → lookupₛ σ x ≡ var x' →
    Σ Ty λ B₀ → Σ Tm λ s₀ → Σ Tm λ u₀ → (lookup Θ v ≡ just (arr B₀ s₀ u₀)) ×
    Σ Nat λ q → (lookupₛ σ z ≡ var q) ×
    IsCellL Γ x' q (dim B₀) (towerOf (lookupₛ σ v) (arr (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm)))
  vcell v x z x' ev σx with endsL-inv (lookup Θ v) ev
  ... | (⋆ , lv , ())
  ... | (arr B₀ s₀ u₀ , lv , eB) with cellσ v _ lv
  ...   | ((e₁ , e₂) , ee , _ , _ , c) =
    let (σx₁ , σz) = ends-sub (arr B₀ s₀ u₀) σ eB ee
        e₁≡x' = var-inj (trans (sym σx₁) σx)
    in B₀ , s₀ , u₀ , lv , e₂ , σz ,
       subst₂' (λ a n → IsCellL Γ a e₂ n (towerOf (lookupₛ σ v) (arr (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm))))
               e₁≡x' (dim-sub B₀ σ) c
    where
    subst₂' : ∀ {A B : Set} (P : A → B → Set) {x y u v} → x ≡ y → u ≡ v → P x u → P y v
    subst₂' P refl refl p = p

  vtop : ∀ v B₀ s₀ u₀ x' q → IsCellL Γ x' q (dim B₀) (towerOf (lookupₛ σ v) (arr (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm))) →
         All (Basis Γ x' q (dim B₀)) (topS (lookupₛ σ v))
  vtop v B₀ s₀ u₀ x' q c =
    subst (All (Basis Γ x' q (dim B₀))) (top-towerOf (lookupₛ σ v) (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm))
      (Cells.IsCell-top (∂T Γ) (Basis Γ x' q) (dim B₀) _ c)

  F-basis : ∀ k w x y x' y' → lookupₛ σ x ≡ var x' → lookupₛ σ y ≡ var y' →
            Basis Θ x y k w → All (Basis Γ x' y' k) (Fσ w)
  F-basis k [] x y x' y' σx σy (x≡y , d) =
    (var-inj (trans (sym σx) (trans (cong (lookupₛ σ) x≡y) σy)) , d) , tt
  F-basis k (v ∷ w) x y x' y' σx σy ((z , ev , wft) , dg) =
    let (B₀ , s₀ , u₀ , lv , q , σz , c) = vcell v x z x' ev σx
        aC = vtop v B₀ s₀ u₀ x' q c
        aD = F-basis (deg Θ w) w z y q y' σz σy (wft , refl)
        hv : hdimV Θ v ≡ dim B₀
        hv = cong hdimTy lv
    in subst (λ X → All (Basis Γ x' y' k) X) (sym (Ftuple-cons Sσ v w))
         (subst (λ X → All (Basis Γ x' y' k) (prod X (Fσ w))) (sym (nthσ v lv))
           (subst (λ n → All (Basis Γ x' y' n) (prod (topS (lookupₛ σ v)) (Fσ w)))
                  (trans (cong (_+ deg Θ w) (sym hv)) dg)
                  (All-prod (topS (lookupₛ σ v)) (Fσ w) aC aD)))

  F-aug : ∀ w x y → Basis Θ x y 0 w → Σ Tuple λ w' → Fσ w ≈ w' ∷ []
  F-aug [] x y _ = [] , ≈-refl
  F-aug (v ∷ w) x y ((z , ev , wft) , dg) with endsL-inv (lookup Θ v) ev
  ... | (⋆ , lv , ())
  ... | (arr B₀ s₀ u₀ , lv , eB) =
    let (h0 , d0) = +-zero-inv (hdimV Θ v) (deg Θ w) dg
        B₀⋆ = dim-zero B₀ (trans (sym (cong hdimTy lv)) h0)
        (w'' , pD) = F-aug w z y (wft , d0)
    in aux B₀ B₀⋆ lv w'' pD
    where
    aux : ∀ B₀ → B₀ ≡ ⋆ → lookup Θ v ≡ just (arr B₀ s₀ u₀) → ∀ w'' → Fσ w ≈ w'' ∷ [] →
          Σ Tuple λ w' → Fσ (v ∷ w) ≈ w' ∷ []
    aux .⋆ refl lv w'' pD with cellσ v _ lv
    ... | (_ , _ , _ , _ , (u , pu , _)) =
      (u ++ w'') ,
      ≈-trans (≡→≈ (trans (Ftuple-cons Sσ v w) (cong (λ X → prod X (Fσ w)) (nthσ v lv))))
     (≈-trans (prod-congˡ (Fσ w) pu)
              (prod-congʳ (u ∷ []) pD))

  -- σ on v ∷ u, through the tensor
  cons-F : ∀ v {B} → lookup Θ v ≡ just B → ∀ Z →
           cm Fσ (consB v Z) ≈ prod (topS (lookupₛ σ v)) (cm Fσ Z)
  cons-F v lv Z =
    begin
      cm Fσ (cm (λ u → (v ∷ u) ∷ []) Z)
    ≈⟨ ≡→≈ (cm-fuse Fσ (λ u → (v ∷ u) ∷ []) Z) ⟩
      cm (λ u → Fσ (v ∷ u) ++ []) Z
    ≈⟨ cm-ext' _ _ Z (λ u → ≡→≈ (trans (++-[]L (Fσ (v ∷ u)))
                                 (trans (Ftuple-cons Sσ v u) (cong (λ X → prod X (Fσ u)) (nthσ v lv))))) ⟩
      cm (λ u → prod (topS (lookupₛ σ v)) (Fσ u)) Z
    ≈⟨ ≈-sym (prod-cmʳ (topS (lookupₛ σ v)) Fσ Z) ⟩
      prod (topS (lookupₛ σ v)) (cm Fσ Z)
    ∎

  step-for : ∀ v w x' B₀ s₀ u₀ → lookup Θ v ≡ just (arr B₀ s₀ u₀) → ∀ q →
    IsCellL Γ x' q (dim B₀) (towerOf (lookupₛ σ v) (arr (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm))) →
    (∀ b → ∂B Γ b (Fσ w) ++ cm Fσ (∂T Θ (not b) w) ≈ ∂B Γ (not b) (Fσ w) ++ cm Fσ (∂T Θ b w)) →
    ∀ b → ∂B Γ b (Fσ (v ∷ w)) ++ cm Fσ (∂T Θ (not b) (v ∷ w)) ≈ ∂B Γ (not b) (Fσ (v ∷ w)) ++ cm Fσ (∂T Θ b (v ∷ w))
  step-for v w x' B₀ s₀ u₀ lv q c IH b =
    ≈-trans (≡→≈ (cong₂ _++_ (cong (∂B Γ b) eqF) (unfold (not b))))
   (≈-trans (chain-step (λ b → ∂B Γ b C) (λ b → ∂B Γ b D) G H Kc (λ b → ∂B Γ b (prod C D))
               C D Cs Ct p (λ b → ∂B-prod Γ p b C D homC) E hH (λ b → cons-F v lv (∂T Θ (flipN p b) w)) IH b)
            (≡→≈ (sym (cong₂ _++_ (cong (∂B Γ (not b)) eqF) (unfold b)))))
    where
    C = topS (lookupₛ σ v)
    D = Fσ w
    p = dim B₀
    G : Bool → Bag
    G b = cm Fσ (∂T Θ b w)
    H Kc : Bool → Bag
    H b = cm Fσ (here b (facesTy (lookup Θ v)) w)
    Kc b = cm Fσ (consB v (∂T Θ (flipN p b) w))
    aC : All (Basis Γ x' q p) C
    aC = vtop v B₀ s₀ u₀ x' q c
    homC : All (Deg Γ p) C
    homC = All-map C (λ _ bc → snd bc) aC
    eqF : Fσ (v ∷ w) ≡ prod C D
    eqF = trans (Ftuple-cons Sσ v w) (cong (λ X → prod X D) (nthσ v lv))
    unfold : ∀ b → cm Fσ (∂T Θ b (v ∷ w)) ≡ H b ++ Kc b
    unfold b = trans (cm-++ Fσ (here b (facesTy (lookup Θ v)) w) _)
                     (cong (λ n → H b ++ cm Fσ (consB v (∂T Θ (flipN n b) w))) (cong hdimTy lv))
    -- the boundary of v and its image
    bd : Σ Bag λ Cs → Σ Bag λ Ct → (∂B Γ true C ++ Cs ≈ ∂B Γ false C ++ Ct) ×
         (∀ b → H b ≈ prod (if b then Ct else Cs) D)
    bd = bd' B₀ s₀ u₀ lv c
      where
      bd' : ∀ B₀ s₀ u₀ → lookup Θ v ≡ just (arr B₀ s₀ u₀) →
            IsCellL Γ x' q (dim B₀) (towerOf (lookupₛ σ v) (arr (B₀ [ σ ]ty) (s₀ [ σ ]tm) (u₀ [ σ ]tm))) →
            Σ Bag λ Cs → Σ Bag λ Ct → (∂B Γ true C ++ Cs ≈ ∂B Γ false C ++ Ct) ×
            (∀ b → H b ≈ prod (if b then Ct else Cs) D)
      bd' ⋆ s₀ u₀ lv' c' =
        [] , [] , ≡→≈ (cong₂ _++_ (trans z0 (sym z1)) refl) , hH
        where
        aC' : All (Basis Γ x' q 0) C
        aC' = vtop v ⋆ s₀ u₀ x' q c'
        z0 : ∂B Γ true C ≡ []
        z0 = cm-zero (∂T Γ true) C aC' (λ c bc → ∂-deg0 c bc true)
        z1 : ∂B Γ false C ≡ []
        z1 = cm-zero (∂T Γ false) C aC' (λ c bc → ∂-deg0 c bc false)
        hH : ∀ b → H b ≈ prod (if b then [] else []) D
        hH true  = ≡→≈ (cong (λ F → cm Fσ (here true F w)) (cong facesTy lv'))
        hH false = ≡→≈ (cong (λ F → cm Fσ (here false F w)) (cong facesTy lv'))
      bd' (arr B₁ a₁ b₁) s₀ u₀ lv' c' with invΘ v _ lv'
      ... | (sv , uv , refl , refl , lsv , luv) =
        topS (lookupₛ σ sv) , topS (lookupₛ σ uv) , E' , hH
        where
        E' : ∂B Γ true C ++ topS (lookupₛ σ sv) ≈ ∂B Γ false C ++ topS (lookupₛ σ uv)
        E' = subst₂'' (λ X Y → ∂B Γ true C ++ X ≈ ∂B Γ false C ++ Y)
               (top-towerOf (lookupₛ σ sv) (B₁ [ σ ]ty) (a₁ [ σ ]tm) (b₁ [ σ ]tm))
               (top-towerOf (lookupₛ σ uv) (B₁ [ σ ]ty) (a₁ [ σ ]tm) (b₁ [ σ ]tm))
               (fst (snd (snd (snd c'))))
          where
          subst₂'' : ∀ {A : Set} (P : A → A → Set) {x y u v} → x ≡ y → u ≡ v → P x u → P y v
          subst₂'' P refl refl p = p
        hF : facesTy (lookup Θ v) ≡ just (sv , uv)
        hF = cong facesTy lv'
        hH : ∀ b → H b ≈ prod (if b then topS (lookupₛ σ uv) else topS (lookupₛ σ sv)) D
        hH true  = ≡→≈ (trans (cong (λ F → cm Fσ (here true F w)) hF)
                        (trans (++-[]L (Fσ (uv ∷ w)))
                        (trans (Ftuple-cons Sσ uv w) (cong (λ X → prod X D) (nthσ uv luv)))))
        hH false = ≡→≈ (trans (cong (λ F → cm Fσ (here false F w)) hF)
                        (trans (++-[]L (Fσ (sv ∷ w)))
                        (trans (Ftuple-cons Sσ sv w) (cong (λ X → prod X D) (nthσ sv lsv)))))
    Cs = fst bd
    Ct = fst (snd bd)
    E  = fst (snd (snd bd))
    hH = snd (snd (snd bd))

  F-chain : ∀ k w x y x' b → lookupₛ σ x ≡ var x' → Basis Θ x y k w →
            ∂B Γ b (Fσ w) ++ cm Fσ (∂T Θ (not b) w) ≈ ∂B Γ (not b) (Fσ w) ++ cm Fσ (∂T Θ b w)
  F-chain k [] x y x' b σx _ = ≈-refl
  F-chain k (v ∷ w) x y x' b σx ((z , ev , wft) , dg) =
    let (B₀ , s₀ , u₀ , lv , q , σz , c) = vcell v x z x' ev σx
    in step-for v w x' B₀ s₀ u₀ lv q c (λ b' → F-chain (deg Θ w) w z y q b' σz (wft , refl)) b

  -- σ is a morphism of complexes K(Θ)(x, y) → K(Γ)(x', y').
  transport-σ : ∀ x y x' y' n X → lookupₛ σ x ≡ var x' → lookupₛ σ y ≡ var y' →
                IsCellL Θ x y n X → IsCellL Γ x' y' n (mapTw (applyF Sσ) X)
  transport-σ x y x' y' n X σx σy c =
    subst (IsCellL Γ x' y' n) (sym (mapTw-ext (applyF Sσ) (cm Fσ) (applyF-cm Sσ) X))
      (Tr.transport n X c)
    where
    module Tr = Transport (∂T Θ) (Basis Θ x y) (∂T Γ) (Basis Γ x' y') Fσ
                  (λ k w bw → F-basis k w x y x' y' σx σy bw)
                  (λ w bw → F-aug w x y bw)
                  (λ k w b bw → F-chain k w x y x' b σx bw)
