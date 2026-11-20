------------------------------------------------------------------------
-- Theorem S, generic part: soundness of composition (planar
-- substitution and whiskering) and of collar gluing.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.SemComp (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.ListLemmas
open Model 𝔐
open import CaTTExp.Gray.Biclosed.ModelFacts 𝔐
open import CaTTExp.Gray.Biclosed.RowSem 𝔐
open import CaTTExp.Gray.Biclosed.Sem 𝔐

------------------------------------------------------------------------
-- Lists of types and of cells

data AllOp : List CTy → Set where
  []  : AllOp []
  _∷_ : ∀ M {As} → AllOp As → AllOp (op M ∷ As)

data All2 {A B : Set} (R : A → B → Set) : List A → List B → Set where
  []  : All2 R [] []
  _∷_ : ∀ {a b as bs} → R a b → All2 R as bs → All2 R (a ∷ as) (b ∷ bs)

All2-++ : ∀ {A B : Set} {R : A → B → Set} {as as′ bs bs′} →
          All2 R as bs → All2 R as′ bs′ → All2 R (as ++ as′) (bs ++ bs′)
All2-++ []       q = q
All2-++ (p ∷ ps) q = p ∷ All2-++ ps q

All2-length : ∀ {A B : Set} {R : A → B → Set} {as bs} → All2 R as bs → length as ≡ length bs
All2-length []       = refl
All2-length (_ ∷ ps) = cong suc (All2-length ps)

All2-take : ∀ {A B : Set} {R : A → B → Set} n {as bs} → All2 R as bs → All2 R (take n as) (take n bs)
All2-take zero    ps       = []
All2-take (suc n) []       = []
All2-take (suc n) (p ∷ ps) = p ∷ All2-take n ps

All2-drop : ∀ {A B : Set} {R : A → B → Set} n {as bs} → All2 R as bs → All2 R (drop n as) (drop n bs)
All2-drop zero    ps       = ps
All2-drop (suc n) []       = []
All2-drop (suc n) (p ∷ ps) = All2-drop n ps

All2-split : ∀ {A B : Set} {R : A → B → Set} xs₁ {x xs₂ cs} → All2 R (xs₁ ++ x ∷ xs₂) cs →
  Σ (List B) λ cs₁ → Σ B λ c → Σ (List B) λ cs₂ →
    (cs ≡ cs₁ ++ c ∷ cs₂) × All2 R xs₁ cs₁ × R x c × All2 R xs₂ cs₂
All2-split []        (p ∷ ps) = [] , _ , _ , refl , [] , p , ps
All2-split (x ∷ xs₁) (p ∷ ps) with All2-split xs₁ ps
... | cs₁ , c , cs₂ , refl , q₁ , q , q₂ = _ ∷ cs₁ , c , cs₂ , refl , p ∷ q₁ , q , q₂

------------------------------------------------------------------------
-- Facts about the checker's helpers

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

bind-just : ∀ {A B : Set} (m : Maybe A) (k : A → B) {y} → (m >>= λ x → just (k x)) ≡ just y →
            Σ A (λ x → (m ≡ just x) × (k x ≡ y))
bind-just (just x) k refl = x , refl , refl

if-just : ∀ {A : Set} b {x : A} {y} → (if b then just x else nothing) ≡ just y → T b × (x ≡ y)
if-just true refl = tt , refl

if-just′ : ∀ {A : Set} b {m : Maybe A} {y} → (if b then m else nothing) ≡ just y → T b × (m ≡ just y)
if-just′ true p = tt , p

compOp-just : ∀ M ms {A} → mapM op (compOp M ms) ≡ just A →
              (ins M ≡ map out ms) × (A ≡ op (concatIns ms ▸ out M))
compOp-just (ys ▸ z) ms p with eqFms ys (map out ms) in e
... | true with p
...   | refl = eqFms-sound ys (map out ms) (subst T (sym e) tt) , refl

countHom-0 : ∀ tgs → (countHom tgs ==ℕ 0) ≡ true → AllOp tgs
countHom-0 []                    e = []
countHom-0 (op M ∷ tgs)          e = M ∷ countHom-0 tgs e
countHom-0 (hom _ _ _ _ _ ∷ tgs) ()

firstHom-split : ∀ i tgs {j tj} → firstHom i tgs ≡ just (j , tj) →
  Σ (List CTy) λ tgs₁ → Σ (List CTy) λ tgs₂ →
    AllOp tgs₁ × (tgs ≡ tgs₁ ++ tj ∷ tgs₂) × (j ≡ i + length tgs₁) × (isHom tj ≡ true)
firstHom-split i [] ()
firstHom-split i (op M ∷ tgs) e with firstHom-split (suc i) tgs e
... | tgs₁ , tgs₂ , a , refl , refl , h = op M ∷ tgs₁ , tgs₂ , M ∷ a , refl , sym (+-suc i (length tgs₁)) , h
firstHom-split i (hom m g U s t ∷ tgs) refl = [] , tgs , [] , refl , sym (+-zero i) , refl

countHom-tail : ∀ {tgs₁} tj tgs₂ → AllOp tgs₁ → isHom tj ≡ true →
                (countHom (tgs₁ ++ tj ∷ tgs₂) ==ℕ 1) ≡ true → AllOp tgs₂
countHom-tail (hom _ _ _ _ _) tgs₂ []      refl e = countHom-0 tgs₂ e
countHom-tail tj              tgs₂ (M ∷ a) h    e = countHom-tail tj tgs₂ a h e

map-baseM-ops : ∀ {tgs} → AllOp tgs → Σ (List MTy) (λ ms → map baseM tgs ≡ ms)
map-baseM-ops {tgs} _ = map baseM tgs , refl

setAt-split : ∀ {A : Set} (xs : List A) y z zs → setAt (length xs) y (xs ++ z ∷ zs) ≡ xs ++ y ∷ zs
setAt-split []       y z zs = refl
setAt-split (x ∷ xs) y z zs = cong (x ∷_) (setAt-split xs y z zs)

take-split : ∀ {A : Set} (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
take-split []       ys = refl
take-split (x ∷ xs) ys = cong (x ∷_) (take-split xs ys)

sumAr-++ : ∀ cs ds → sumAr (cs ++ ds) ≡ sumAr cs + sumAr ds
sumAr-++ []       ds = refl
sumAr-++ (c ∷ cs) ds = trans (cong (ar c +_) (sumAr-++ cs ds)) (sym (+-assoc (ar c) (sumAr cs) (sumAr ds)))

compS-0 : ∀ c cs → dm c ≡ 0 → compS c cs ≡ sc (cmpFrom (val c) 0 (vals cs)) (sumAr cs) (hiD cs) (hiG cs)
compS-0 (sc F a zero g) cs refl = refl

compS-suc : ∀ c cs k → dm c ≡ suc k →
  compS c cs ≡ sc (whS (suc k) (val c) (vals (take (gp c) cs)) (vals (drop (gp c) cs)))
                  (sumAr cs) (suc k) (sumAr (take (gp c) cs))
compS-suc (sc F a (suc k) g) cs .k refl = refl

vals-take-drop : ∀ g cs → vals (take g cs) ++ vals (drop g cs) ≡ vals cs
vals-take-drop g cs = trans (sym (map-++ val (take g cs) (drop g cs))) (cong vals (take-drop g cs))

------------------------------------------------------------------------
-- Interpretation facts

module _ (ε : Nat → SC) where
  open Interp ε

  OpsMem : List MTy → List SC → Set
  OpsMem = All2 (λ M c → Mem (op M) c)

  toOps : ∀ {tgs cs} → AllOp tgs → All2 Mem tgs cs → OpsMem (map baseM tgs) cs
  toOps []      []       = []
  toOps (M ∷ a) (p ∷ ps) = p ∷ toOps a ps

  ops-args : ∀ {ms cs} → OpsMem ms cs → Args (vals cs) ms
  ops-args []             = []
  ops-args ((t , _) ∷ ps) = t ∷ ops-args ps

  ops-sumAr : ∀ {ms cs} → OpsMem ms cs → sumAr cs ≡ sumIns ms
  ops-sumAr {M ∷ ms} {c ∷ cs} ((_ , a , _) ∷ ps) =
    trans (cong₂ _+_ a (ops-sumAr ps)) (sym (length-++ (ins M) (concatIns ms)))
  ops-sumAr [] = refl

  ops-hiD : ∀ {ms cs} → OpsMem ms cs → hiD cs ≡ 0
  ops-hiD [] = refl
  ops-hiD {cs = sc v a zero g ∷ cs} ((_ , _ , refl) ∷ ps) = ops-hiD ps

  hiD-ops-++ : ∀ {ms cs} → OpsMem ms cs → ∀ y ds → hiD (cs ++ y ∷ ds) ≡ hiD (y ∷ ds)
  hiD-ops-++ [] y ds = refl
  hiD-ops-++ {cs = sc v a zero g ∷ cs} ((_ , _ , refl) ∷ ps) y ds = hiD-ops-++ ps y ds

  hiG-ops-++ : ∀ {ms cs} → OpsMem ms cs → ∀ y ds → hiG (cs ++ y ∷ ds) ≡ sumAr cs + hiG (y ∷ ds)
  hiG-ops-++ [] y ds = refl
  hiG-ops-++ {cs = sc v a zero g ∷ cs} ((_ , _ , refl) ∷ ps) y ds =
    trans (cong (a +_) (hiG-ops-++ ps y ds)) (sym (+-assoc a (sumAr cs) (hiG (y ∷ ds))))

  ⟦setAt⟧ : ∀ j s gs → ⟦ setAt j s gs ⟧s ≡ setAt j ⟦ s ⟧ ⟦ gs ⟧s
  ⟦setAt⟧ j       s []       = refl
  ⟦setAt⟧ zero    s (g ∷ gs) = refl
  ⟦setAt⟧ (suc j) s (g ∷ gs) = cong (⟦ g ⟧ ∷_) (⟦setAt⟧ j s gs)

  -- composite of an operation with operations
  compOps : ∀ {M ms c cs} → Mem (op M) c → OpsMem ms cs → ins M ≡ map out ms →
            Mem (op (concatIns ms ▸ out M)) (compS c cs)
  compOps {M} {ms} {c} {cs} (tc , _ , dc) ps e =
    Mem-≡ (op (concatIns ms ▸ out M)) (sym (compS-0 c cs dc))
      ( retype (T-cmpFrom {P = []} {R = []} (retype tc (cong (_▸ out M) (trans e (sym (++-[] _)))))
                  (ops-args ps) refl)
               (cong (_▸ out M) (++-[] (concatIns ms)))
      , ops-sumAr ps , ops-hiD ps )

  -- the value of a whiskered cell, as whiskering at the gap of its type
  compS-whS-val : ∀ U {x} g cs → Mem U x → gapIs g U →
                  val (compS x cs) ≡ whS (dim U) (val x) (vals (take g cs)) (vals (drop g cs))
  compS-whS-val (op M) {x} g cs (_ , _ , d) _ =
    trans (cong val (compS-0 x cs d))
          (trans (cong (cmpFrom (val x) 0) (sym (vals-take-drop g cs)))
                 (sym (whS-0 (val x) (vals (take g cs)) (vals (drop g cs)))))
  compS-whS-val (hom m g′ U s t) {x} g cs mx refl =
    trans (cong val (compS-suc x cs (dim U) (mDm mx)))
          (cong (λ h → whS (suc (dim U)) (val x) (vals (take h cs)) (vals (drop h cs))) (mGp mx))

  hiD-suc : ∀ y ds k → dm y ≡ suc k → hiD (y ∷ ds) ≡ suc k
  hiD-suc (sc v a (suc k) g) ds .k refl = refl

  hiG-suc : ∀ y ds k → dm y ≡ suc k → hiG (y ∷ ds) ≡ gp y
  hiG-suc (sc v a (suc k) g) ds .k refl = refl

------------------------------------------------------------------------
-- Shapes of whiskered types

subst₂′ : ∀ {A B : Set} (P : A → B → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
subst₂′ P refl refl p = p

leq-prefix : ∀ {A : Set} (pre post xs : List A) → pre ++ post ≡ xs → T (leq (length pre) (length xs))
leq-prefix pre post xs e =
  subst (λ n → T (leq (length pre) n)) (trans (sym (length-++ pre post)) (cong length e))
        (leq-+ (length pre) (length post))

liftF-shape : ∀ gs ms U {A} → liftF gs ms U ≡ just A →
  (dim A ≡ dim U) × (baseM A ≡ (concatIns ms ▸ out (baseM U))) × (ins (baseM U) ≡ map out ms) ×
  (∀ g → gapIs g U → gapIs (sumIns (take g ms)) A)
liftF-shape gs ms (op M) p with compOp-just M ms p
... | e , refl = refl , refl , e , λ _ _ → tt
liftF-shape gs ms (hom m g U s t) p
  with bind-just (liftF gs ms U) (λ U′ → hom m (sumIns (take g ms)) U′ (comp s gs) (comp t gs)) p
... | U′ , eU , refl with liftF-shape gs ms U eU
...   | dU , bU , iU , _ = cong suc dU , bU , iU , λ g′ e → cong (λ h → sumIns (take h ms)) e

liftG-shape : ∀ f gs Mf ms₁ Mx ms₂ U {A} → baseM U ≡ Mx →
  liftG f gs (length ms₁) Mf (ms₁ ++ Mx ∷ ms₂) U ≡ just A →
  (dim A ≡ dim U) × (baseM A ≡ (concatIns (ms₁ ++ Mx ∷ ms₂) ▸ out Mf)) ×
  (ins Mf ≡ map out (ms₁ ++ Mx ∷ ms₂)) × (∀ g → gapIs g U → gapIs (sumIns ms₁ + g) A)
liftG-shape f gs Mf ms₁ Mx ms₂ (op M) refl p
  with compOp-just Mf (ms₁ ++ M ∷ ms₂)
         (subst (λ l → mapM op (compOp Mf l) ≡ just _) (setAt-split ms₁ M M ms₂) p)
... | e , refl = refl , refl , e , λ _ _ → tt
liftG-shape f gs Mf ms₁ Mx ms₂ (hom m g U s t) bx p
  with bind-just (liftG f gs (length ms₁) Mf (ms₁ ++ Mx ∷ ms₂) U)
         (λ U′ → hom m (sumIns (take (length ms₁) (ms₁ ++ Mx ∷ ms₂)) + g) U′
                   (comp f (setAt (length ms₁) s gs)) (comp f (setAt (length ms₁) t gs))) p
... | U′ , eU , refl with liftG-shape f gs Mf ms₁ Mx ms₂ U bx eU
...   | dU , bU , iU , _ =
  cong suc dU , bU , iU ,
  λ g′ e → trans (cong (λ l → sumIns l + g) (take-split ms₁ (Mx ∷ ms₂))) (cong (sumIns ms₁ +_) e)

------------------------------------------------------------------------
-- Soundness of whiskering

module _ (ε : Nat → SC) where
  open Interp ε

  -- a higher cell whiskered by operations
  liftFS : ∀ gs ms → OpsMem ε ms ⟦ gs ⟧s → ∀ U {x A} → Mem U x → liftF gs ms U ≡ just A →
           Mem A (compS x ⟦ gs ⟧s)
  liftFS gs ms ops (op M) mx p with compOp-just M ms p
  ... | e , refl = compOps ε mx ops e
  liftFS gs ms ops (hom m g U s t) {x} mx p
    with bind-just (liftF gs ms U) (λ U′ → hom m (sumIns (take g ms)) U′ (comp s gs) (comp t gs)) p
  ... | U′ , eU , refl with liftF-shape gs ms U eU | cell mx
  ...   | dU , bU , iU , gU | cellAt pre post sp len ty =
    Mem-≡ (hom m (sumIns (take g ms)) U′ (comp s gs) (comp t gs)) (sym eqx) hm
    where
    cs = ⟦ gs ⟧s
    d  = dim U
    vs₁ = vals (take g cs)
    vs₂ = vals (drop g cs)
    W  = whS (suc d) (val x) vs₁ vs₂
    eqx : compS x cs ≡ sc W (sumAr cs) (suc d) (sumAr (take g cs))
    eqx = trans (compS-suc x cs d (mDm mx))
                (cong (λ h → sc (whS (suc d) (val x) (vals (take h cs)) (vals (drop h cs)))
                                (sumAr cs) (suc d) (sumAr (take h cs))) (mGp mx))
    su = split-unique pre post (map out ms) (trans sp iU)
    e-pre : pre ≡ map out (take g ms)
    e-pre = trans (fst su) (trans (cong (λ n → take n (map out ms)) len) (take-map out g ms))
    e-post : post ≡ map out (drop g ms)
    e-post = trans (snd su) (trans (cong (λ n → drop n (map out ms)) len) (drop-map out g ms))
    Fty : val x ∶ ((map out (take g ms) ++ dsrc (suc d) ++ map out (drop g ms)) ▸ out (baseM U))
    Fty = retype ty (cong₂ (λ a b → (a ++ dsrc (suc d) ++ b) ▸ out (baseM U)) e-pre e-post)
    a₁ = ops-args ε (All2-take g ops)
    a₂ = ops-args ε (All2-drop g ops)
    lv : length vs₁ ≡ g
    lv = trans (length-map val (take g cs))
         (length-take g cs (subst (λ n → T (leq g n))
                              (trans (length-map out ms) (All2-length ops))
                              (subst (λ n → T (leq n (length (map out ms)))) len
                                     (leq-prefix pre post (map out ms) (trans sp iU)))))
    cell₀ : CellAt (suc d) (sumIns (take g ms)) (concatIns ms ▸ out (baseM U)) W
    cell₀ = cellAt (concatIns (take g ms)) (concatIns (drop g ms))
              (trans (sym (concatIns-++ (take g ms) (drop g ms))) (cong concatIns (take-drop g ms)))
              refl (T-whS Fty a₁ a₂)
    face : ∀ α {y} → pc (val x) g (δ α d) ≈ val y → Mem U y →
           pc W (sumIns (take g ms)) (δ α d) ≈ val (compS y cs)
    face α {y} f my =
      ≈-trans (face-whS α Fty a₁ a₂)
      (≈-trans (whS-cong d vs₁ vs₂ (≈-trans (≡→≈ (cong (λ i → pc (val x) i (δ α d)) lv)) f))
               (≡→≈ (sym (compS-whS-val ε U g cs my (gapA mx)))))
    hm : HomMem m (sumIns (take g ms)) U′ (Mem U′) (compS ⟦ s ⟧ cs) (compS ⟦ t ⟧ cs)
           (sc W (sumAr cs) (suc d) (sumAr (take g cs)))
    hm = record
      { cell = subst₂′ (λ k M → CellAt (suc k) (sumIns (take g ms)) M W) (sym dU) (sym bU) cell₀
      ; mAr  = trans (ops-sumAr ε ops) (cong (λ M → length (ins M)) (sym bU))
      ; mDm  = cong suc (sym dU)
      ; mGp  = ops-sumAr ε (All2-take g ops)
      ; gapA = gU g (gapA mx)
      ; memS = liftFS gs ms ops U (memS mx) eU
      ; memT = liftFS gs ms ops U (memT mx) eU
      ; fS   = subst (λ k → pc W (sumIns (take g ms)) (δ false k) ≈ val (compS ⟦ s ⟧ cs)) (sym dU) (face false (fS mx) (memS mx))
      ; fT   = subst (λ k → pc W (sumIns (take g ms)) (δ true k) ≈ val (compS ⟦ t ⟧ cs)) (sym dU) (face true (fT mx) (memT mx))
      ; flat = λ e → ≈-trans (≡→≈ (compS-whS-val ε U g cs (memS mx) (gapA mx)))
                     (≈-trans (whS-cong d vs₁ vs₂ (flat mx e))
                              (≡→≈ (sym (compS-whS-val ε U g cs (memT mx) (gapA mx)))))
      }

  -- an operation composed with operations and one higher cell
  module LiftG (f : Tm) (gs : List Tm) (Mf : MTy) (mf : Mem (op Mf) ⟦ f ⟧)
               (ms₁ : List MTy) (Mx : MTy) (ms₂ : List MTy)
               (cs₁ : List SC) (c : SC) (cs₂ : List SC)
               (eqgs : ⟦ gs ⟧s ≡ cs₁ ++ c ∷ cs₂)
               (o₁ : OpsMem ε ms₁ cs₁) (o₂ : OpsMem ε ms₂ cs₂) where

    ms = ms₁ ++ Mx ∷ ms₂
    j  = length ms₁
    F  = val ⟦ f ⟧

    lj : j ≡ length cs₁
    lj = All2-length o₁

    eqS : ∀ s → ⟦ setAt j s gs ⟧s ≡ cs₁ ++ ⟦ s ⟧ ∷ cs₂
    eqS s = trans (⟦setAt⟧ ε j s gs)
            (trans (cong (setAt j ⟦ s ⟧) eqgs)
            (trans (cong (λ i → setAt i ⟦ s ⟧ (cs₁ ++ c ∷ cs₂)) lj) (setAt-split cs₁ ⟦ s ⟧ c cs₂)))

    val-at : ∀ y → val (compS ⟦ f ⟧ (cs₁ ++ y ∷ cs₂)) ≡ cmpFrom F 0 (vals cs₁ ++ val y ∷ vals cs₂)
    val-at y = trans (cong val (compS-0 ⟦ f ⟧ (cs₁ ++ y ∷ cs₂) (snd (snd mf))))
                     (cong (cmpFrom F 0) (map-++ val cs₁ (y ∷ cs₂)))

    liftGS : ∀ U {y A} → Mem U y → baseM U ≡ Mx → liftG f gs j Mf ms U ≡ just A →
             Mem A (compS ⟦ f ⟧ (cs₁ ++ y ∷ cs₂))
    liftGS (op M) my refl p
      with compOp-just Mf (ms₁ ++ M ∷ ms₂)
             (subst (λ l → mapM op (compOp Mf l) ≡ just _) (setAt-split ms₁ M M ms₂) p)
    ... | e , refl = compOps ε mf (All2-++ o₁ (my ∷ o₂)) e
    liftGS (hom m g U s t) {y} my bx p
      with bind-just (liftG f gs j Mf ms U)
             (λ U′ → hom m (sumIns (take j ms) + g) U′ (comp f (setAt j s gs)) (comp f (setAt j t gs))) p
    ... | U′ , eU , refl with liftG-shape f gs Mf ms₁ Mx ms₂ U bx eU | cell my
    ...   | dU , bU , iU , gU | cellAt pre post sp len ty =
      Mem-≡ (hom m (sumIns (take j ms) + g) U′ (comp f (setAt j s gs)) (comp f (setAt j t gs)))
            (sym eqy) hm
      where
      d   = dim U
      ys  = cs₁ ++ y ∷ cs₂
      G₀  = sumIns ms₁ + g
      eG : G₀ ≡ sumIns (take j ms) + g
      eG = cong (λ l → sumIns l + g) (sym (take-split ms₁ (Mx ∷ ms₂)))
      vs₁ = vals cs₁
      vs₂ = vals cs₂
      Wv  = cmpFrom F 0 (vs₁ ++ val y ∷ vs₂)
      eqy : compS ⟦ f ⟧ ys ≡ sc Wv (sumAr ys) (hiD ys) (hiG ys)
      eqy = trans (compS-0 ⟦ f ⟧ ys (snd (snd mf)))
                  (cong (λ l → sc (cmpFrom F 0 l) (sumAr ys) (hiD ys) (hiG ys)) (map-++ val cs₁ (y ∷ cs₂)))
      My = (pre ++ dsrc (suc d) ++ post) ▸ out Mx
      Fty : F ∶ (([] ++ map out ms₁ ++ out Mx ∷ map out ms₂ ++ []) ▸ out Mf)
      Fty = retype (fst mf) (cong (_▸ out Mf) (trans iU (trans (map-++ out ms₁ (Mx ∷ ms₂))
                                                   (cong (λ l → map out ms₁ ++ out Mx ∷ l) (sym (++-[] _))))))
      ty′ : val y ∶ ((pre ++ D (suc d) ∷ post) ▸ out Mx)
      ty′ = retype ty (cong (λ M → (pre ++ D (suc d) ∷ post) ▸ out M) bx)
      E : concatIns (ms₁ ++ My ∷ ms₂) ++ [] ≡ (concatIns ms₁ ++ pre) ++ dsrc (suc d) ++ post ++ concatIns ms₂
      E = trans (++-[] _) (trans (concatIns-++ ms₁ (My ∷ ms₂))
          (trans (cong (concatIns ms₁ ++_) (trans (++-assoc pre (dsrc (suc d) ++ post) (concatIns ms₂))
                                                  (cong (pre ++_) (++-assoc (dsrc (suc d)) post (concatIns ms₂)))))
                 (sym (++-assoc (concatIns ms₁) pre _))))
      sp′ : (concatIns ms₁ ++ pre) ++ post ++ concatIns ms₂ ≡ concatIns ms
      sp′ = trans (++-assoc (concatIns ms₁) pre (post ++ concatIns ms₂))
            (trans (cong (concatIns ms₁ ++_) (trans (sym (++-assoc pre post (concatIns ms₂)))
                                                    (cong (_++ concatIns ms₂) (trans sp (cong ins bx)))))
                   (sym (concatIns-++ ms₁ (Mx ∷ ms₂))))
      cell₀ : CellAt (suc d) (sumIns (take j ms) + g) (concatIns ms ▸ out Mf) Wv
      cell₀ = cellAt (concatIns ms₁ ++ pre) (post ++ concatIns ms₂) sp′
                (trans (length-++ (concatIns ms₁) pre) (trans (cong (sumIns ms₁ +_) len) eG))
                (retype (T-cmpFrom {P = []} {R = []} {Ms = ms₁ ++ My ∷ ms₂}
                           (retype Fty (cong (_▸ out Mf)
                              (trans (cong (λ l → map out ms₁ ++ out Mx ∷ l) (++-[] (map out ms₂)))
                              (trans (sym (map-++ out ms₁ (My ∷ ms₂))) (sym (++-[] _))))))
                           (Args-++ (ops-args ε o₁) (ty′ ∷ ops-args ε o₂)) refl)
                        (cong (_▸ out Mf) E))
      face : ∀ α {z} → pc (val y) g (δ α d) ≈ val z →
             pc Wv (sumIns (take j ms) + g) (δ α d) ≈ val (compS ⟦ f ⟧ (cs₁ ++ z ∷ cs₂))
      face α {z} fz =
        ≈-trans (≡→≈ (cong (λ i → pc Wv i (δ α d))
                       (trans (sym eG) (cong (sumIns ms₁ +_) (sym len)))))
        (≈-trans (face-arg {P = []} {Q = []} {Ms₁ = ms₁} {Pre = pre} {X = D (suc d)} {Post = post}
                    {Y = out Mx} {Ms₂ = ms₂} Fty (ops-args ε o₁) ty′ (ops-args ε o₂) (T-δ α d) refl)
        (≈-trans (cmpFrom-arg-cong F 0 vs₁ vs₂ (≈-trans (≡→≈ (cong (λ i → pc (val y) i (δ α d)) len)) fz))
                 (≡→≈ (sym (val-at z)))))
      ⟦s⟧-eq : ∀ s′ → compS ⟦ f ⟧ ⟦ setAt j s′ gs ⟧s ≡ compS ⟦ f ⟧ (cs₁ ++ ⟦ s′ ⟧ ∷ cs₂)
      ⟦s⟧-eq s′ = cong (compS ⟦ f ⟧) (eqS s′)
      hm : HomMem m (sumIns (take j ms) + g) U′ (Mem U′)
             (compS ⟦ f ⟧ ⟦ setAt j s gs ⟧s) (compS ⟦ f ⟧ ⟦ setAt j t gs ⟧s)
             (sc Wv (sumAr ys) (hiD ys) (hiG ys))
      hm = record
        { cell = subst₂′ (λ k M → CellAt (suc k) (sumIns (take j ms) + g) M Wv) (sym dU) (sym bU) cell₀
        ; mAr  = trans (sumAr-++ cs₁ (y ∷ cs₂))
                 (trans (cong₂ _+_ (ops-sumAr ε o₁)
                          (cong₂ _+_ (trans (mAr my) (cong (λ M → length (ins M)) bx)) (ops-sumAr ε o₂)))
                 (trans (cong (sumIns ms₁ +_) (sym (length-++ (ins Mx) (concatIns ms₂))))
                 (trans (sym (sumIns-++ ms₁ (Mx ∷ ms₂))) (cong (λ M → length (ins M)) (sym bU)))))
        ; mDm  = trans (hiD-ops-++ ε o₁ y cs₂) (trans (hiD-suc ε y cs₂ d (mDm my)) (cong suc (sym dU)))
        ; mGp  = trans (hiG-ops-++ ε o₁ y cs₂)
                 (trans (cong₂ _+_ (ops-sumAr ε o₁) (trans (hiG-suc ε y cs₂ d (mDm my)) (mGp my))) eG)
        ; gapA = subst (λ G → gapIs G U′) eG (gU g (gapA my))
        ; memS = Mem-≡ U′ (sym (⟦s⟧-eq s)) (liftGS U (memS my) bx eU)
        ; memT = Mem-≡ U′ (sym (⟦s⟧-eq t)) (liftGS U (memT my) bx eU)
        ; fS   = subst (λ k → pc Wv (sumIns (take j ms) + g) (δ false k) ≈ val (compS ⟦ f ⟧ ⟦ setAt j s gs ⟧s)) (sym dU)
                   (≈-trans (face false (fS my)) (≡→≈ (cong val (sym (⟦s⟧-eq s)))))
        ; fT   = subst (λ k → pc Wv (sumIns (take j ms) + g) (δ true k) ≈ val (compS ⟦ f ⟧ ⟦ setAt j t gs ⟧s)) (sym dU)
                   (≈-trans (face true (fT my)) (≡→≈ (cong val (sym (⟦s⟧-eq t)))))
        ; flat = λ e → ≈-trans (≡→≈ (trans (cong val (⟦s⟧-eq s)) (val-at ⟦ s ⟧)))
                       (≈-trans (cmpFrom-arg-cong F 0 vs₁ vs₂ (flat my e))
                                (≡→≈ (sym (trans (cong val (⟦s⟧-eq t)) (val-at ⟦ t ⟧)))))
        }

  -- composition
  compSound : ∀ f gs tf tgs {A} → Mem tf ⟦ f ⟧ → All2 Mem tgs ⟦ gs ⟧s →
              compTy f gs tf tgs ≡ just A → Mem A ⟦ comp f gs ⟧
  compSound f gs (op Mf) tgs mf mgs p
    with countHom tgs ==ℕ 0 in e0 | countHom tgs ==ℕ 1 in e1 | firstHom 0 tgs in e2
  ... | true | _ | _ with compOp-just Mf (map baseM tgs) p
  ...   | e , refl = compOps ε mf (toOps ε (countHom-0 tgs e0) mgs) e
  compSound f gs (op Mf) tgs mf mgs p | false | true | just (j , tj)
    with firstHom-split 0 tgs e2
  ... | tgs₁ , tgs₂ , a₁ , refl , refl , h with All2-split tgs₁ mgs
  ...   | cs₁ , c , cs₂ , eqgs , m₁ , mc , m₂ =
    Mem-≡ _ (cong (compS ⟦ f ⟧) (sym eqgs))
      (LiftG.liftGS f gs Mf mf ms₁ Mx ms₂ cs₁ c cs₂ eqgs
         (toOps ε a₁ m₁) (toOps ε (countHom-tail tj tgs₂ a₁ h e1) m₂)
         tj mc refl
         (subst₂′ (λ i l → liftG f gs i Mf l tj ≡ just _)
                  (sym (length-map baseM tgs₁)) (map-++ baseM tgs₁ (tj ∷ tgs₂)) p))
    where
    ms₁ = map baseM tgs₁
    Mx  = baseM tj
    ms₂ = map baseM tgs₂
  compSound f gs (op Mf) tgs mf mgs () | false | true | nothing
  compSound f gs (op Mf) tgs mf mgs () | false | false | _
  compSound f gs (hom m g U s t) tgs mf mgs p with countHom tgs ==ℕ 0 in e0
  ... | true  = liftFS gs (map baseM tgs) (toOps ε (countHom-0 tgs e0) mgs) (hom m g U s t) mf p
  ... | false = ⊥-elim (nothing≢just p)
    where
    nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nothing≢just ()

------------------------------------------------------------------------
-- Soundness of gluing collars

glueTy-shape : ∀ am ap Tc qm qp pm pp U {A} → glueTy am ap Tc qm qp pm pp U ≡ just A →
  (dim A ≡ dim U) × (baseM A ≡ baseM U) × (∀ g → gapIs g U → gapIs g A)
glueTy-shape am ap Tc qm qp pm pp (op M) ()
glueTy-shape am ap Tc qm qp pm pp (hom m g U s t) p
  with eqTy U Tc ∧ eqTm s qm ∧ eqTm t qp in e
... | true with p
...   | refl with eqTy-sound U Tc (∧-fst (subst T (sym e) tt))
...     | refl = refl , refl , λ _ q → q
glueTy-shape am ap Tc qm qp pm pp (hom m g U s t) p | false
  with bind-just (glueTy am ap Tc qm qp pm pp U) (λ U′ → hom m g U′ (glue am s ap) (glue am t ap)) p
... | U′ , eU , refl with glueTy-shape am ap Tc qm qp pm pp U eU
...   | dU , bU , _ = cong suc dU , bU , λ _ q → q

module _ (ε : Nat → SC) where
  open Interp ε

  module Glue (am ap : Tm) (Tc : CTy) (qm qp pm pp : Tm)
              (mPm : Mem Tc ⟦ pm ⟧) (mPp : Mem Tc ⟦ pp ⟧)
              (eqm : val ⟦ pm ⟧ ≈ val ⟦ qm ⟧) (eqp : val ⟦ pp ⟧ ≈ val ⟦ qp ⟧) where

    glueTyS : ∀ U {c A} → Mem U c → glueTy am ap Tc qm qp pm pp U ≡ just A → Mem A c
    glueTyS (op M) mc ()
    glueTyS (hom m g U s t) {c} mc p with eqTy U Tc ∧ eqTm s qm ∧ eqTm t qp in e
    ... | true with p
    ...   | refl with eqTy-sound U Tc (∧-fst (subst T (sym e) tt))
                    | eqTm-sound s qm (∧-fst (∧-snd {eqTy U Tc} (subst T (sym e) tt)))
                    | eqTm-sound t qp (∧-snd {eqTm s qm} (∧-snd {eqTy U Tc} (subst T (sym e) tt)))
    ...     | refl | refl | refl = record
      { cell = cell mc ; mAr = mAr mc ; mDm = mDm mc ; mGp = mGp mc ; gapA = gapA mc
      ; memS = mPm ; memT = mPp
      ; fS = ≈-trans (fS mc) (≈-sym eqm) ; fT = ≈-trans (fT mc) (≈-sym eqp)
      ; flat = λ e′ → ≈-trans eqm (≈-trans (flat mc e′) (≈-sym eqp)) }
    glueTyS (hom m g U s t) {c} mc p | false
      with bind-just (glueTy am ap Tc qm qp pm pp U) (λ U′ → hom m g U′ (glue am s ap) (glue am t ap)) p
    ... | U′ , eU , refl with glueTy-shape am ap Tc qm qp pm pp U eU
    ...   | dU , bU , gU = record
      { cell = subst₂′ (λ k M → CellAt (suc k) g M (val c)) (sym dU) (sym bU) (cell mc)
      ; mAr  = trans (mAr mc) (cong (λ M → length (ins M)) (sym bU))
      ; mDm  = trans (mDm mc) (cong suc (sym dU))
      ; mGp  = mGp mc
      ; gapA = gU g (gapA mc)
      ; memS = glueTyS U (memS mc) eU
      ; memT = glueTyS U (memT mc) eU
      ; fS   = subst (λ k → pc (val c) g (δ false k) ≈ val ⟦ s ⟧) (sym dU) (fS mc)
      ; fT   = subst (λ k → pc (val c) g (δ true k) ≈ val ⟦ t ⟧) (sym dU) (fT mc)
      ; flat = flat mc }

  glueSound : ∀ am ap x ta tb tx {A} → Mem ta ⟦ am ⟧ → Mem tb ⟦ ap ⟧ → Mem tx ⟦ x ⟧ →
              glueTop am ap ta tb tx ≡ just A → Mem A ⟦ glue am x ap ⟧
  glueSound am ap x (hom inv g Tc pm qm) (hom inv g′ Tc′ pp qp) tx ma mb mx p
    with if-just′ ((g ==ℕ g′) ∧ eqTy Tc Tc′) p
  ... | c , q with eqTy-sound Tc Tc′ (∧-snd {g ==ℕ g′} c)
  ...   | refl = Glue.glueTyS am ap Tc qm qp pm pp (memS ma) (memS mb) (flat ma refl) (flat mb refl) tx mx q
  glueSound am ap x (op _)                (hom _ _ _ _ _)          tx ma mb mx ()
  glueSound am ap x (hom dir _ _ _ _)     (hom _ _ _ _ _)          tx ma mb mx ()
  glueSound am ap x (hom inv _ _ _ _)     (op _)                   tx ma mb mx ()
  glueSound am ap x (hom inv _ _ _ _)     (hom dir _ _ _ _)        tx ma mb mx ()
  glueSound am ap x (op _)                (op _)                   tx ma mb mx ()
  glueSound am ap x (hom dir _ _ _ _)     (op _)                   tx ma mb mx ()
