------------------------------------------------------------------------
-- Facts about the cells and homs of a pasting context, by induction
-- on the pasting derivation.
--
--   ps-facts : Γ ⊢ps x ∶ A → PsFacts Γ
--
-- PsFacts Γ says:
--   * every type of Γ is a tower of variables (Gray.Graded.Inv);
--   * every variable of positive dimension is a cell of some hom
--     k with 1 ≤ k < #objects (`cellP`);
--   * every such hom contains a 1-cell (`nonE`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.PsFacts (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.Graded 𝕊

CellT : Ctx → List Nat → Set
CellT Γ os = ∀ v C → lookup Γ v ≡ just C → isStar C ≡ false →
             Σ Nat λ k → (homOf os C ≡ just k) × T (0 <ℕ k) × T (k <ℕ countL os)

NonT : Ctx → List Nat → Set
NonT Γ os = ∀ k → T (0 <ℕ k) → T (k <ℕ countL os) →
            Σ Nat λ v → Σ Ty λ C → (lookup Γ v ≡ just C) × (dim C ≡ 1) × (homOf os C ≡ just k)

record PsFacts (Γ : Ctx) : Set where
  field
    inv   : Inv Γ
    cellP : CellT Γ (objs Γ)
    nonE  : NonT Γ (objs Γ)
    objLt : ∀ {o} → o ∈ᴺ objs Γ → T (o <ℕ len Γ)
open PsFacts public

------------------------------------------------------------------------
-- Lists, lookups.

private
  lookup-new' : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
  lookup-new' Γ A rewrite ==-refl≡ (len Γ) = refl

  lookup-lt : ∀ Γ v {C} → lookup Γ v ≡ just C → T (v <ℕ len Γ)
  lookup-lt (Γ ▸ A) v e with v ==ℕ len Γ in q
  ... | true  = subst (λ w → T (w <ℕ suc (len Γ))) (sym (==ℕ-sound v (len Γ) (subst T (sym q) tt))) (lt-refl (len Γ))
  ... | false = weak< v (len Γ) (lookup-lt Γ v e)

  lookup-ext : ∀ Γ A v {C} → lookup Γ v ≡ just C → lookup (Γ ▸ A) v ≡ just C
  lookup-ext Γ A v e rewrite lt-ne v (len Γ) (lookup-lt Γ v e) = e

  lookup-split : ∀ Γ A v {C} → lookup (Γ ▸ A) v ≡ just C → ((v ≡ len Γ) × (C ≡ A)) ⊎ (lookup Γ v ≡ just C)
  lookup-split Γ A v e with v ==ℕ len Γ in q
  lookup-split Γ A v refl | true  = inj₁ (==ℕ-sound v (len Γ) (subst T (sym q) tt) , refl)
  ... | false = inj₂ e

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  filter-++ : ∀ {A : Set} (p : A → Bool) xs ys → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
  filter-++ p []       ys = refl
  filter-++ p (x ∷ xs) ys with p x
  ... | true  = cong (x ∷_) (filter-++ p xs ys)
  ... | false = filter-++ p xs ys

  map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  count-++ : ∀ xs y → countL (xs ++ (y ∷ [])) ≡ suc (countL xs)
  count-++ []       y = refl
  count-++ (x ∷ xs) y = cong suc (count-++ xs y)

objs-star : ∀ Γ → objs (Γ ▸ ⋆) ≡ objs Γ ++ (len Γ ∷ [])
objs-star Γ = trans (cong (map fst) (filter-++ (λ e → isStar (snd e)) (entries Γ) ((len Γ , ⋆) ∷ [])))
                    (map-++ fst (filter (λ e → isStar (snd e)) (entries Γ)) ((len Γ , ⋆) ∷ []))

objs-arr : ∀ Γ B s t → objs (Γ ▸ arr B s t) ≡ objs Γ
objs-arr Γ B s t = trans (cong (map fst) (filter-++ (λ e → isStar (snd e)) (entries Γ) ((len Γ , arr B s t) ∷ [])))
                         (trans (map-++ fst (filter (λ e → isStar (snd e)) (entries Γ)) [])
                                (++-[] (objs Γ)))

private
  posOf-++ : ∀ b os ys {k} → posOf b os ≡ just k → posOf b (os ++ ys) ≡ just k
  posOf-++ b (m ∷ ms) ys e with b ==ℕ m
  ... | true  = e
  ... | false with posOf b ms in q
  ... | just k' rewrite posOf-++ b ms ys q = e

  posOf-new : ∀ y os → (∀ {o} → o ∈ᴺ os → T (o <ℕ y)) → posOf y (os ++ (y ∷ [])) ≡ just (countL os)
  posOf-new y []       f rewrite ==-refl≡ y = refl
  posOf-new y (m ∷ ms) f rewrite trans (==-sym≡ y m) (lt-ne m y (f (here refl)))
                               | posOf-new y ms (λ o → f (there o)) = refl

  objs-mem : ∀ Γ {o} → lookup Γ o ≡ just ⋆ → o ∈ᴺ objs Γ
  objs-mem (Γ ▸ A) {o} e with lookup-split Γ A o e
  ... | inj₁ (refl , refl) rewrite objs-star Γ = any-++r (objs Γ) (here refl)
  ... | inj₂ e' with A
  ...   | ⋆ rewrite objs-star Γ = any-++l (objs-mem Γ e')
  ...   | arr B s t rewrite objs-arr Γ B s t = objs-mem Γ e'

  -- homOf only looks at the ends of the bottom arrow.
  homOf-arr : ∀ os B s t a b → homOf os (arr (arr B s t) a b) ≡ homOf os (arr B s t)
  homOf-arr os B s t a b = refl

  homOf-++ : ∀ os ys C {k} → homOf os C ≡ just k → homOf (os ++ ys) C ≡ just k
  homOf-++ os ys C e with endsTy C
  ... | just (_ , b) with varLvl b
  ...   | just b' = posOf-++ b' os ys e

  pos< : ∀ {k} → T (0 <ℕ suc k)
  pos< = tt

  lt-suc : ∀ k n → T (k <ℕ n) → T (k <ℕ suc n)
  lt-suc = weak<

  lt-splt : ∀ k n → T (k <ℕ suc n) → T (k <ℕ n) ⊎ (k ≡ n)
  lt-splt zero    zero    _ = inj₂ refl
  lt-splt zero    (suc n) _ = inj₁ tt
  lt-splt (suc k) (suc n) p with lt-splt k n p
  ... | inj₁ q = inj₁ q
  ... | inj₂ q = inj₂ (cong suc q)

------------------------------------------------------------------------
-- One pse step.

module _ (Γ : Ctx) (x : Nat) (A : Ty) (P : PsFacts Γ) (lx : lookup Γ x ≡ just A) where
  private
    F  = arr A (var x) (var (len Γ))
    Γ₁ = Γ ▸ A
    Γ₂ = Γ₁ ▸ F

    lk2 : ∀ v {C} → lookup Γ v ≡ just C → lookup Γ₂ v ≡ just C
    lk2 v e = lookup-ext Γ₁ F v (lookup-ext Γ A v e)

    vt2 : ∀ B → VT Γ B → VT Γ₂ B
    vt2 ⋆ _ = tt
    vt2 (arr B s t) (i , j , qs , qt , li , lj) = i , j , qs , qt , lk2 i li , lk2 j lj

  inv-step : Inv Γ₂
  inv-step v C e with lookup-split Γ₁ F v e
  ... | inj₁ (refl , refl) = x , len Γ , refl , refl , lk2 x lx , lookup-ext Γ₁ F (len Γ) (lookup-new' Γ A)
  ... | inj₂ e₁ with lookup-split Γ A v e₁
  ...   | inj₁ (refl , refl) = vt2 A (inv P x A lx)
  ...   | inj₂ e₀ = vt2 C (inv P v C e₀)

  -- the three cases of a variable of Γ₂
  data Which (v : Nat) (C : Ty) : Set where
    isF   : v ≡ suc (len Γ) → C ≡ F → Which v C
    isA   : v ≡ len Γ → C ≡ A → Which v C
    isOld : lookup Γ v ≡ just C → Which v C

  which : ∀ v {C} → lookup Γ₂ v ≡ just C → Which v C
  which v e with lookup-split Γ₁ F v e
  ... | inj₁ (p , q) = isF p q
  ... | inj₂ e₁ with lookup-split Γ A v e₁
  ...   | inj₁ (p , q) = isA p q
  ...   | inj₂ e₀ = isOld e₀

  objLt-step : (objs Γ₂ ≡ objs Γ ++ (len Γ ∷ [])) ⊎ (objs Γ₂ ≡ objs Γ) → ∀ {o} → o ∈ᴺ objs Γ₂ → T (o <ℕ len Γ₂)
  objLt-step (inj₁ e) {o} m rewrite e with any-++⁻ (objs Γ) m
  ... | inj₁ a = weak< o (suc (len Γ)) (weak< o (len Γ) (objLt P a))
  ... | inj₂ (here refl) = weak< (len Γ) (suc (len Γ)) (lt-refl (len Γ))
  objLt-step (inj₂ e) {o} m rewrite e = weak< o (suc (len Γ)) (weak< o (len Γ) (objLt P m))

step : ∀ Γ x A → PsFacts Γ → lookup Γ x ≡ just A → PsFacts (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
step Γ x ⋆ P lx = record
  { inv = inv-step Γ x ⋆ P lx ; cellP = subst (CellT _) (sym os≡) cellS ; nonE = subst (NonT _) (sym os≡) nonES
  ; objLt = objLt-step Γ x ⋆ P lx (inj₁ os≡) }
  where
  os = objs Γ
  os≡ : objs (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) ≡ os ++ (len Γ ∷ [])
  os≡ = trans (objs-arr (Γ ▸ ⋆) ⋆ (var x) (var (len Γ))) (objs-star Γ)
  newpos : posOf (len Γ) (os ++ (len Γ ∷ [])) ≡ just (countL os)
  newpos = posOf-new (len Γ) os (objLt P)
  cnt : countL (os ++ (len Γ ∷ [])) ≡ suc (countL os)
  cnt = count-++ os (len Γ)
  ne : T (0 <ℕ countL os)
  ne with objs-mem Γ lx
  ... | m = nz os m
    where
    nz : ∀ l {o} → o ∈ᴺ l → T (0 <ℕ countL l)
    nz (_ ∷ _) _ = tt
  cellS : CellT (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (os ++ (len Γ ∷ []))
  cellS v C e st rewrite cnt with which Γ x ⋆ P lx v e
  ... | isF refl refl = countL os , newpos , ne , lt-refl (countL os)
  ... | isA refl refl = ⊥-elim (true≢false st)
    where
    true≢false : true ≡ false → ⊥
    true≢false ()
  ... | isOld e₀ with cellP P v C e₀ st
  ...   | k , h , p , q = k , homOf-++ os (len Γ ∷ []) C h , p , lt-suc k (countL os) q
  nonES : NonT (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (os ++ (len Γ ∷ []))
  nonES k p q rewrite cnt with lt-splt k (countL os) q
  ... | inj₁ q' with nonE P k p q'
  ...   | v , C , e , d , h = v , C , lookup-ext (Γ ▸ ⋆) _ v (lookup-ext Γ ⋆ v e) , d , homOf-++ os (len Γ ∷ []) C h
  nonES k p q | inj₂ refl =
    suc (len Γ) , arr ⋆ (var x) (var (len Γ)) , lookup-new' (Γ ▸ ⋆) _ , refl , newpos
step Γ x (arr B s t) P lx = record
  { inv = inv-step Γ x A P lx ; cellP = subst (CellT _) (sym os≡) cellS ; nonE = subst (NonT _) (sym os≡) nonES
  ; objLt = objLt-step Γ x A P lx (inj₂ os≡) }
  where
  A = arr B s t
  os = objs Γ
  os≡ : objs (Γ ▸ A ▸ arr A (var x) (var (len Γ))) ≡ os
  os≡ = trans (objs-arr (Γ ▸ A) A (var x) (var (len Γ))) (objs-arr Γ B s t)
  cellS : CellT (Γ ▸ A ▸ arr A (var x) (var (len Γ))) os
  cellS v C e st with which Γ x A P lx v e
  ... | isF refl refl = cellP P x A lx refl
  ... | isA refl refl = cellP P x A lx refl
  ... | isOld e₀ = cellP P v C e₀ st
  nonES : NonT (Γ ▸ A ▸ arr A (var x) (var (len Γ))) os
  nonES k p q with nonE P k p q
  ... | v , C , e , d , h = v , C , lookup-ext (Γ ▸ A) _ v (lookup-ext Γ A v e) , d , h

------------------------------------------------------------------------
-- The induction.

ps-facts : ∀ {Γ x A} → Γ ⊢ps x ∶ A → PsFacts Γ × (lookup Γ x ≡ just A)
ps-facts pss = record { inv = inv0 ; cellP = cell0 ; nonE = nonE0 ; objLt = olt0 } , refl
  where
  inv0 : Inv (ε ▸ ⋆)
  inv0 i B e with i ==ℕ 0
  inv0 i B refl | true = tt
  inv0 i B ()   | false
  cell0 : CellT (ε ▸ ⋆) (0 ∷ [])
  cell0 v C e st with v ==ℕ 0
  cell0 v .⋆ refl () | true
  cell0 v C () st | false
  nonE0 : NonT (ε ▸ ⋆) (0 ∷ [])
  nonE0 zero    () _
  nonE0 (suc k) _  ()
  olt0 : ∀ {o} → o ∈ᴺ (0 ∷ []) → T (o <ℕ 1)
  olt0 (here refl) = tt
ps-facts (psd {Γ} {f} {A} {x} {y} d) with ps-facts d
... | P , lf with inv P f _ lf
...   | i , j , refl , refl , li , lj = P , lj
ps-facts (pse {Γ} {x} {A} d) with ps-facts d
... | P , lx = step Γ x A P lx , lookup-new' (Γ ▸ A) (arr A (var x) (var (len Γ)))
