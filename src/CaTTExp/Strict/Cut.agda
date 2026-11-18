------------------------------------------------------------------------
-- The cut lemma (notes/conjectures/answered/
-- steiner-support-formalizable-2026-11-18.md, §2).
--
-- In a pasting context Γ, with the basis order _<ₒ_ of Strict.Order
-- (negative faces before, positive faces after), take adjacent rows
-- u = x_q⁻, v = x_q⁺ and c = x_{q+1} of a cell, so ∂⁺c + u = ∂⁻c + v.
-- For a tuple a, the cut
--
--     cut a u v c = (v + ∂⁻(c≥a))|_{<a} + (u + ∂⁺(c<a))|_{≥a}
--
-- is u + ∂(c<a) (`cut-eq`), it has coefficient u[a] + (∂⁺c)[a] at a
-- (`cut-at`), and replacing the top row of the q-cell (rows < q of x,
-- top u) by it gives a q-cell (`cut-cell`).
------------------------------------------------------------------------
module CaTTExp.Strict.Cut where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.DD
open import CaTTExp.Strict.TopCell using (_⊎_; inj₁; inj₂; Pos; count-filter-in; count-filter-out)
open import CaTTExp.Strict.CohCase using (count-∈L; All-∈L; ∈L-++r)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any) renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; filter⇒)
open import CaTTExp.Strict.Order using (_<ₒ_; <ₒ-irrefl; <ₒ-trans; ord-neg; ord-pos; OInv; count-in)

------------------------------------------------------------------------
-- Membership.

∈L-++ : ∀ A {B x} → x ∈L (A ++ B) → (x ∈L A) ⊎ (x ∈L B)
∈L-++ []      m          = inj₂ m
∈L-++ (a ∷ A) (hereA e)  = inj₁ (hereA e)
∈L-++ (a ∷ A) (thereA m) with ∈L-++ A m
... | inj₁ p = inj₁ (thereA p)
... | inj₂ q = inj₂ q

∈L-consB : ∀ v Y {z} → z ∈L consB v Y → Σ Tuple λ z' → (z ≡ v ∷ z') × (z' ∈L Y)
∈L-consB v (y ∷ Y) (hereA refl) = y , refl , hereA refl
∈L-consB v (y ∷ Y) (thereA m) with ∈L-consB v Y m
... | z' , e , m' = z' , e , thereA m'

------------------------------------------------------------------------
-- Faces of basis elements are basis elements one degree lower.

private
  data VShape (Γ : Ctx) (v : Nat) : Set where
    flatS : facesTy (lookup Γ v) ≡ nothing → VShape Γ v
    deep  : ∀ B a b s t → lookup Γ v ≡ just (arr (arr B a b) (var s) (var t)) →
            lookup Γ s ≡ just (arr B a b) → lookup Γ t ≡ just (arr B a b) → VShape Γ v

  vshape : ∀ {Γ} → PsInv Γ → ∀ v → VShape Γ v
  vshape {Γ} inv v = go (lookup Γ v) refl
    where
    go : ∀ m → lookup Γ v ≡ m → VShape Γ v
    go nothing            e = flatS (cong facesTy e)
    go (just ⋆)           e = flatS (cong facesTy e)
    go (just (arr ⋆ _ _)) e = flatS (cong facesTy e)
    go (just (arr (arr B a b) s t)) e with inv v _ e
    ... | (i , j , refl , refl , li , lj) = deep B a b i j e li lj

face-wft : ∀ {Γ} → PsInv Γ → ∀ σ x y w {z} → WFT Γ x y w → z ∈L ∂T Γ σ w →
           WFT Γ x y z × (suc (deg Γ z) ≡ deg Γ w)
face-wft inv σ x y [] _ ()
face-wft {Γ} inv σ x y (v ∷ w) {z} (m , ev , p) mz
  with ∈L-++ (here σ (facesTy (lookup Γ v)) w) mz
... | inj₂ mc with ∈L-consB v (∂T Γ (flipN (hdimV Γ v) σ) w) mc
...   | z' , refl , m' with face-wft inv (flipN (hdimV Γ v) σ) m y w p m'
...     | wz , dz = (m , ev , wz) , trans (sym (+-suc (hdimV Γ v) (deg Γ z'))) (cong (hdimV Γ v +_) dz)
face-wft {Γ} inv σ x y (v ∷ w) {z} (m , ev , p) mz | inj₁ mh with vshape inv v
... | flatS e = ⊥-elim (none (subst (λ F → z ∈L here σ F w) e mh))
  where
  none : z ∈L [] → ⊥
  none ()
... | deep B a b s t lv ls lt = go σ (subst (λ F → z ∈L here σ F w) (cong facesTy lv) mh)
  where
  ev' : endsV (arr B a b) ≡ just (x , m)
  ev' = trans (cong endsL (sym lv)) ev
  hv : hdimV Γ v ≡ suc (hdimV Γ s)
  hv = trans (cong hdimTy lv) (cong (λ q → suc (hdimTy q)) (sym ls))
  go : ∀ σ' → z ∈L here σ' (just (s , t)) w → WFT Γ x y z × (suc (deg Γ z) ≡ deg Γ (v ∷ w))
  go true  (hereA refl) =
    (m , trans (cong endsL lt) ev' , p) ,
    cong (_+ deg Γ w) (trans (cong (λ q → suc (hdimTy q)) (trans lt (sym ls))) (sym hv))
  go false (hereA refl) =
    (m , trans (cong endsL ls) ev' , p) , cong (_+ deg Γ w) (sym hv)
  go true  (thereA ())
  go false (thereA ())

face-basis : ∀ {Γ} → PsInv Γ → ∀ σ x y k w {z} → Basis Γ x y (suc k) w → z ∈L ∂T Γ σ w → Basis Γ x y k z
face-basis inv σ x y k w (wf , dw) mz with face-wft inv σ x y w wf mz
... | wz , dz = wz , suc-inj (trans dz dw)
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

------------------------------------------------------------------------
-- Counting.

cnt0 : ∀ d X → (d ∈L X → ⊥) → count d X ≡ 0
cnt0 d X h with count d X in e
... | zero  = refl
... | suc n = ⊥-elim (h (count-in d X e))

cm-zero' : ∀ d g X → (∀ {b} → b ∈L X → d ∈L g b → ⊥) → count d (cm g X) ≡ 0
cm-zero' d g []      h = refl
cm-zero' d g (x ∷ X) h =
  trans (count-++ d (g x) (cm g X))
        (cong₂ _+_ (cnt0 d (g x) (h (hereA refl))) (cm-zero' d g X (λ m → h (thereA m))))

cm-split : ∀ d g Q X → count d (cm g X) ≡
           count d (cm g (filter Q X)) + count d (cm g (filter (λ b → not (Q b)) X))
cm-split d g Q []      = refl
cm-split d g Q (x ∷ X) with Q x
... | true  = trans (count-++ d (g x) (cm g X))
              (trans (cong (count d (g x) +_) (cm-split d g Q X))
              (trans (sym (+-assoc (count d (g x)) _ _))
                     (cong (_+ count d (cm g (filter (λ b → not (Q b)) X))) (sym (count-++ d (g x) (cm g (filter Q X)))))))
... | false = trans (count-++ d (g x) (cm g X))
              (trans (cong (count d (g x) +_) (cm-split d g Q X))
              (trans (sym (+-assoc (count d (g x)) _ _))
              (trans (cong (_+ count d (cm g (filter (λ b → not (Q b)) X))) (+-comm (count d (g x)) _))
              (trans (+-assoc (count d (cm g (filter Q X))) _ _)
                     (cong (count d (cm g (filter Q X)) +_) (sym (count-++ d (g x) (cm g (filter (λ b → not (Q b)) X)))))))))

------------------------------------------------------------------------
-- The cut.

module _ {Γ : Ctx} (I : OInv Γ) where

  private
    _<_ : Tuple → Tuple → Bool
    a < b = _<ₒ_ Γ a b

    ge : Tuple → Tuple → Bool
    ge a b = not (b < a)

  -- The part of c below a, and the part at or above a.
  below above : Tuple → Bag → Bag
  below a c = filter (λ b → b < a) c
  above a c = filter (λ b → not (b < a)) c

  cut : Tuple → Bag → Bag → Bag → Bag
  cut a u v c = filter (λ b → b < a) (v ++ ∂B Γ false (above a c))
             ++ filter (λ b → not (b < a)) (u ++ ∂B Γ true (below a c))

  private
    perm3 : ∀ a b c → (a + b) + c ≡ (c + b) + a
    perm3 a b c = trans (+-comm (a + b) c) (trans (cong (c +_) (+-comm a b)) (sym (+-assoc c b a)))

    ar1 : ∀ p u n h v → (p + 0) + u ≡ (n + h) + v → ((v + h) + 0) + n ≡ u + p
    ar1 p u n h v eq =
      trans (cong (_+ n) (+-zero (v + h)))
      (trans (perm3 v h n)
      (trans (sym eq)
      (trans (cong (_+ u) (+-zero p)) (+-comm p u))))

    not-T : ∀ b → T (not b) → b ≡ false
    not-T false _ = refl

    -- No element of `above a c` has a positive face below a (or at a).
    P-above : ∀ a c d → (∀ b → T (b < d) → T (b < a)) → count d (∂B Γ true (above a c)) ≡ 0
    P-above a c d le = cm-zero' d (∂T Γ true) (above a c) λ {b} mb md →
      let (_ , nb) = filter⇒ (λ b → not (b < a)) c mb
      in  T≠false (le b (ord-pos Γ I b md)) (not-T (b < a) nb)
      where
      T≠false : ∀ {x} → T x → x ≡ false → ⊥
      T≠false {true} _ ()

    -- No element of `below a c` has a negative face at or above a.
    N-below : ∀ a c d → (d < a) ≡ false → count d (∂B Γ false (below a c)) ≡ 0
    N-below a c d da = cm-zero' d (∂T Γ false) (below a c) λ {b} mb md →
      let (_ , ba) = filter⇒ (λ b → b < a) c mb
      in  T≠false (<ₒ-trans Γ d b a (ord-neg Γ I b md) ba) da
      where
      T≠false : ∀ {x} → T x → x ≡ false → ⊥
      T≠false {true} _ ()

  -- The cut is u + ∂(c below a).
  cut-eq : ∀ a u v c → ∂B Γ true c ++ u ≈ ∂B Γ false c ++ v →
           cut a u v c ++ ∂B Γ false (below a c) ≈ u ++ ∂B Γ true (below a c)
  cut-eq a u v c ch = mk≈ λ d → go d (d < a) refl
    where
    Lo Hi : Bag
    Lo = below a c
    Hi = above a c
    Q : Tuple → Bool
    Q b = b < a
    Q' : Tuple → Bool
    Q' b = not (b < a)
    chd : ∀ d → (count d (∂B Γ true Lo) + count d (∂B Γ true Hi)) + count d u
              ≡ (count d (∂B Γ false Lo) + count d (∂B Γ false Hi)) + count d v
    chd d = trans (cong (_+ count d u) (sym (cm-split d (∂T Γ true) Q c)))
            (trans (sym (count-++ d (∂B Γ true c) u))
            (trans (at ch d)
            (trans (count-++ d (∂B Γ false c) v)
                   (cong (_+ count d v) (cm-split d (∂T Γ false) Q c)))))
    go : ∀ d b → d < a ≡ b →
         count d (cut a u v c ++ ∂B Γ false Lo) ≡ count d (u ++ ∂B Γ true Lo)
    go d true e =
      trans (count-++ d (cut a u v c) (∂B Γ false Lo))
      (trans (cong (_+ count d (∂B Γ false Lo)) (count-++ d (filter Q (v ++ ∂B Γ false Hi)) (filter Q' (u ++ ∂B Γ true Lo))))
      (trans (cong₂ (λ x y → (x + y) + count d (∂B Γ false Lo))
                    (trans (count-filter-in Q d (v ++ ∂B Γ false Hi) (subst T (sym e) tt)) (count-++ d v (∂B Γ false Hi)))
                    (count-filter-out Q' d (u ++ ∂B Γ true Lo) (cong not e)))
      (trans (ar1 (count d (∂B Γ true Lo)) (count d u) (count d (∂B Γ false Lo)) (count d (∂B Γ false Hi)) (count d v)
                  (trans (cong (λ z → (count d (∂B Γ true Lo) + z) + count d u)
                               (sym (P-above a c d (λ b bd → <ₒ-trans Γ b d a bd (subst T (sym e) tt)))))
                         (chd d)))
             (sym (count-++ d u (∂B Γ true Lo))))))
    go d false e =
      trans (count-++ d (cut a u v c) (∂B Γ false Lo))
      (trans (cong₂ _+_
               (trans (count-++ d (filter Q (v ++ ∂B Γ false Hi)) (filter Q' (u ++ ∂B Γ true Lo)))
                      (cong₂ _+_ (count-filter-out Q d (v ++ ∂B Γ false Hi) e)
                                 (count-filter-in Q' d (u ++ ∂B Γ true Lo) (subst T (sym (cong not e)) tt))))
               (N-below a c d e))
             (+-zero _))

  -- The coefficient of the cut at a.
  cut-at : ∀ a u v c → count a (cut a u v c) ≡ count a u + count a (∂B Γ true c)
  cut-at a u v c =
    trans (count-++ a (filter (λ b → b < a) (v ++ ∂B Γ false (above a c))) (filter (λ b → not (b < a)) (u ++ ∂B Γ true (below a c))))
    (trans (cong₂ _+_ (count-filter-out (λ b → b < a) a (v ++ ∂B Γ false (above a c)) (<ₒ-irrefl Γ a))
                      (count-filter-in (λ b → not (b < a)) a (u ++ ∂B Γ true (below a c)) (subst T (sym (cong not (<ₒ-irrefl Γ a))) tt)))
    (trans (count-++ a u (∂B Γ true (below a c)))
           (cong (count a u +_)
             (sym (trans (cm-split a (∂T Γ true) (λ b → b < a) c)
                  (trans (cong (count a (∂B Γ true (below a c)) +_) (P-above a c a (λ b ba → ba)))
                         (+-zero _)))))))
