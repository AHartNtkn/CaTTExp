------------------------------------------------------------------------
-- Facts about a single-hom context Γ = ΣΘ, for the ⇐ half of
-- notes/conjectures/single-hom-conservativity.md (Strict.SuppFV).
--
--  * every variable of positive dimension of ΣΘ is S u, of type Σty A
--    for u : A in Θ (`lookupΣ⁻`), so its endpoints are the objects 0
--    and 1 (`ends01`) and a composable tuple has length ≤ 1 (`short`);
--  * a face in the strict complex is one Gray step (`face-step`), the
--    converse of Strict.Recon's step-face;
--  * an object has no Gray steps (`reach-obj`, for any context);
--  * a path ending in a singleton starts in a singleton (`reach-one`),
--    and its length is at most dim Θ (`hgt-le`).
------------------------------------------------------------------------
module CaTTExp.Strict.SigmaFacts where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Cut using (∈L-++)
open import CaTTExp.Strict.TopCell using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Rad using (cm-mem; ∈L-count)
open import CaTTExp.Strict.CohCase using (count-∈L)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; any-map⁻; any-map⁺; any-mono; any-witness; _≤_; z≤n; s≤s; ≤-trans; ≤-refl)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; map≡)
open import CaTTExp.Gray.DownAgree ∅ renaming (module Faces to DF)
import CaTTExp.Gray.Graded ∅ as Gr
open import CaTTExp.Suspension ∅ using (Σctx; Σty; Σtm; S; dimΣ)
open import CaTTExp.Gray.SingleHom ∅ using (fΣ; mkC; entriesΣ; lookup→entries; cell-in; hΣ; hcsΣ; hdΣ)

private
  no10 : 1 ≡ 0 → ⊥
  no10 ()

  noTF : true ≡ false → ⊥
  noTF ()

  cm-out : ∀ g X {z} → z ∈L cm g X → Σ Tuple λ b → (b ∈L X) × (z ∈L g b)
  cm-out g X {z} m with cm-mem g X z (∈L-count z (cm g X) m)
  ... | b , mb , p = b , mb , count-∈L z (g b) p

  max-≤l : ∀ a b → a ≤ max a b
  max-≤l zero    b       = z≤n
  max-≤l (suc a) zero    = ≤-refl (suc a)
  max-≤l (suc a) (suc b) = s≤s (max-≤l a b)

  max-≤r : ∀ a b → b ≤ max a b
  max-≤r zero    b       = ≤-refl b
  max-≤r (suc a) zero    = z≤n
  max-≤r (suc a) (suc b) = s≤s (max-≤r a b)

  maxL-ge : ∀ xs {x} → x ∈ᴺ xs → x ≤ maxL xs
  maxL-ge (y ∷ ys) (hereA refl) = max-≤l y (maxL ys)
  maxL-ge (y ∷ ys) (thereA m)   = ≤-trans (maxL-ge ys m) (max-≤r y (maxL ys))

  findEl-in : ∀ w cs {c} → findEl w cs ≡ just c → Any (c ≡_) cs
  findEl-in w (c ∷ cs) e with lvl c ==ℕ w
  ... | true  = hereA (just-inj (sym e))
  ... | false = thereA (findEl-in w cs e)

------------------------------------------------------------------------
-- Objects, in any context.

module _ (Γ : Ctx) where
  private
    module F = DF (cells Γ)

  bd-obj : ∀ i → lookup Γ i ≡ just ⋆ → bdEl (cells Γ) i ≡ []
  bd-obj i e rewrite Gr.findEl-cells (objs Γ) Γ i | e = refl

  reach-obj : ∀ i → lookup Γ i ≡ just ⋆ → ∀ {k y} → F.Reach k (i ∷ []) y → y ≡ i ∷ []
  reach-obj i e F.done = refl
  reach-obj i e (F.step (F.sh {b = b} mb) r) = ⊥-elim (none (subst (b ∈ᴺ_) (bd-obj i e) mb))
    where
    none : b ∈ᴺ [] → ⊥
    none ()
  reach-obj i e (F.step (F.st ()) r)

  -- Steps keep the length; a path to a singleton starts at one.
  step-one : ∀ {x b} → F.Step x (b ∷ []) → Σ Nat λ a → x ≡ a ∷ []
  step-one (F.sh {w} {ws = []} _) = w , refl
  step-one (F.st ())

  reach-one : ∀ {k x b} → F.Reach k x (b ∷ []) → Σ Nat λ a → x ≡ a ∷ []
  reach-one {b = b} F.done = b , refl
  reach-one (F.step s r) with reach-one r
  ... | a , refl = step-one s

------------------------------------------------------------------------
-- The single hom ΣΘ.

private
  lookupΣ-go : ∀ Θ {v C} → isStar C ≡ false → Any ((v , C) ≡_) ((0 , ⋆) ∷ (1 , ⋆) ∷ map fΣ (entries Θ)) →
               Σ Nat λ u → Σ Ty λ A → (v ≡ S u) × (C ≡ Σty A) × (lookup Θ u ≡ just A)
  lookupΣ-go Θ st (hereA refl) = ⊥-elim (noTF st)
  lookupΣ-go Θ st (thereA (hereA refl)) = ⊥-elim (noTF st)
  lookupΣ-go Θ st (thereA (thereA m))
    with any-witness (any-map⁻ fΣ (entries Θ) (subst (Any _) (map≡ fΣ (entries Θ)) m))
  ... | (u , A) , mu , refl = u , A , refl , refl , Gr.entries-lookup Θ mu

endsΣty : ∀ A → endsV (Σty A) ≡ just (0 , 1)
endsΣty ⋆                     = refl
endsΣty (arr ⋆ t u)           = refl
endsΣty (arr (arr B a b) t u) = endsΣty (arr B a b)

module _ (Θ : Ctx) where
  private
    Γ = Σctx Θ
    module F = DF (cells Γ)

  lookupΣ⁻ : ∀ v {C} → lookup Γ v ≡ just C → isStar C ≡ false →
             Σ Nat λ u → Σ Ty λ A → (v ≡ S u) × (C ≡ Σty A) × (lookup Θ u ≡ just A)
  lookupΣ⁻ v e st = lookupΣ-go Θ st (subst (Any _) (entriesΣ Θ) (lookup→entries Γ v e))

  ends01 : ∀ v {x z} → endsL (lookup Γ v) ≡ just (x , z) → (x ≡ 0) × (z ≡ 1)
  ends01 v {x} {z} ev with endsL-inv (lookup Γ v) ev
  ... | B , lB , eB = go B lB eB
    where
    go : ∀ B → lookup Γ v ≡ just B → endsV B ≡ just (x , z) → (x ≡ 0) × (z ≡ 1)
    go ⋆ _ ()
    go B@(arr _ _ _) lB eB with lookupΣ⁻ v lB refl
    ... | u , A , _ , eC , _ =
      let p = just-inj (trans (sym eB) (trans (cong endsV eC) (endsΣty A))) in cong fst p , cong snd p

  -- Composable tuples of ΣΘ have length at most 1.
  data Short : Tuple → Set where
    s0 : Short []
    s1 : ∀ a → Short (a ∷ [])

  short : ∀ {x y} w → WFT Γ x y w → Short w
  short []          _ = s0
  short (a ∷ [])    _ = s1 a
  short (a ∷ b ∷ w) (z , ea , (z' , eb , _)) with ends01 a ea | ends01 b eb
  ... | _ , z1 | z0 , _ = ⊥-elim (no10 (trans (sym z1) z0))

  short-mid : ∀ A u B → Short (A ++ u ∷ B) → (A ≡ []) × (B ≡ [])
  short-mid []            u []      _ = refl , refl
  short-mid []            u (_ ∷ _) ()
  short-mid (_ ∷ [])      u B       ()
  short-mid (_ ∷ _ ∷ _)   u B       ()

  -- The faces of a cell of ΣΘ are its Gray boundary entries.
  private
    faces-shape : ∀ C {s t} → facesTy (just C) ≡ just (s , t) →
                  Σ Ty λ B → Σ Tm λ a → Σ Tm λ a' → C ≡ arr (arr B a a') (var s) (var t)
    faces-shape (arr (arr B a a') (var s) (var t)) refl = B , a , a' , refl
    faces-shape ⋆ ()
    faces-shape (arr ⋆ _ _) ()
    faces-shape (arr (arr _ _ _) (coh _ _ _) _) ()
    faces-shape (arr (arr _ _ _) (cst ()) _)
    faces-shape (arr (arr _ _ _) (var _) (coh _ _ _)) ()
    faces-shape (arr (arr _ _ _) (var _) (cst ()))

    bd-list : ∀ A {B a a' s t} → Σty A ≡ arr (arr B a a') (var s) (var t) →
              (if dim A ==ℕ 0 then [] else (fst (elBdry (Σty A)) ∷ snd (elBdry (Σty A)) ∷ [])) ≡ s ∷ t ∷ []
    bd-list ⋆ ()
    bd-list (arr A₀ x y) e rewrite e = refl

  bd-faces : ∀ v C {s t} → lookup Γ v ≡ just C → facesTy (just C) ≡ just (s , t) →
             (s ∈ᴺ bdEl (cells Γ) v) × (t ∈ᴺ bdEl (cells Γ) v)
  bd-faces v C {s} {t} lv ef with faces-shape C ef
  ... | B , a , a' , refl with lookupΣ⁻ v lv refl
  ...   | u , A , refl , eC , lu =
    subst (s ∈ᴺ_) (sym bdE) (hereA refl) , subst (t ∈ᴺ_) (sym bdE) (thereA (hereA refl))
    where
    bdE : bdEl (cells Γ) (S u) ≡ s ∷ t ∷ []
    bdE = trans (Gr.bd-just (cells Γ) (S u) (Gr.findEl-mem Γ (cell-in Θ u lu))) (bd-list A (sym eC))

  face-step : ∀ b {z z'} → z' ∈L ∂T Γ b z → F.Step z z'
  face-step b {[]} ()
  face-step b {v ∷ w} {z'} m with ∈L-++ (here b (facesTy (lookup Γ v)) w) m
  ... | inj₂ m' with cm-out (λ u → (v ∷ u) ∷ []) (∂T Γ (flipN (hdimV Γ v) b) w) m'
  ...   | w' , mw' , hereA e = subst (F.Step (v ∷ w)) (sym e) (F.st (face-step _ mw'))
  ...   | w' , mw' , thereA ()
  face-step b {v ∷ w} {z'} m | inj₁ mh = hM (lookup Γ v) refl mh
    where
    hF : ∀ C → lookup Γ v ≡ just C → ∀ Fc → facesTy (just C) ≡ Fc → z' ∈L here b Fc w → F.Step (v ∷ w) z'
    hF C lv nothing       _  ()
    hF C lv (just (s , t)) ef (hereA e) = subst (F.Step (v ∷ w)) (sym e) (F.sh (pk b))
      where
      pk : ∀ b → (if b then t else s) ∈ᴺ bdEl (cells Γ) v
      pk true  = snd (bd-faces v C lv ef)
      pk false = fst (bd-faces v C lv ef)
    hF C lv (just _) _ (thereA ())
    hM : ∀ M → lookup Γ v ≡ M → z' ∈L here b (facesTy M) w → F.Step (v ∷ w) z'
    hM nothing  _  ()
    hM (just C) lv mh' = hF C lv (facesTy (just C)) refl mh'

  -- Entries of ΣΘ have hom dimension at most dim Θ.
  hgt-le : ∀ a → F.hgt a ≤ dimCtx Θ
  hgt-le a = go (findEl a (cells Γ)) refl
    where
    go : ∀ m → findEl a (cells Γ) ≡ m → F.hgtM m ≤ dimCtx Θ
    go nothing  _ = z≤n
    go (just c) e =
      subst (hdim c ≤_) (hdΣ Θ)
        (maxL-ge (map hdim (hcs (hΣ Θ)))
          (subst (Any _) (sym (map≡ hdim (hcs (hΣ Θ))))
            (any-map⁺ hdim (any-mono (λ { refl → refl })
              (subst (Any (c ≡_)) (sym (hcsΣ Θ)) (findEl-in a (cells Γ) e))))))
