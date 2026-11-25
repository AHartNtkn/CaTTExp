------------------------------------------------------------------------
-- Gray face steps in a pasting context (any number of homs).
--
--  * `face-step`: a face in the strict complex is one Gray step, in
--    every pasting context (Strict.SigmaFacts proves it for ΣΘ);
--  * `step-ent`: Gray steps keep every entry a cell (a non-object
--    variable);
--  * `lower`: every entry can be lowered, by Gray steps, to a 1-cell
--    variable (a 0-cell of its hom), so a tuple p ++ g ∷ q of cells
--    reaches a tuple pre ++ g ∷ post whose other entries are 1-cells;
--  * `objs-lookup`: the objects of Γ are the variables of type ⋆.
--
-- For the ⇐ half of Lemma 4.2 (notes/lax-sc-completeness.md §4) in
-- several homs (Strict.G.SuppFV).
------------------------------------------------------------------------
module CaTTExp.Strict.PsSteps where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.L using (endsL-inv)
open import CaTTExp.Strict.Cut using (∈L-++)
open import CaTTExp.Strict.TopCell using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Rad using (cm-mem; ∈L-count)
open import CaTTExp.Strict.CohCase using (count-∈L)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; any-map⁻; any-witness)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; filter⇒; map≡)
open import CaTTExp.Gray.DownAgree ∅ renaming (module Faces to DF)
import CaTTExp.Gray.Graded ∅ as Gr
open import CaTTExp.Gray.PsFacts ∅ using (PsFacts; inv; cellP)
open import CaTTExp.Gray.Through ∅ using (One; AllOne; []; _∷_)

private
  cm-out : ∀ g X {z} → z ∈L cm g X → Σ Tuple λ b → (b ∈L X) × (z ∈L g b)
  cm-out g X {z} m with cm-mem g X z (∈L-count z (cm g X) m)
  ... | b , mb , p = b , mb , count-∈L z (g b) p

  noTF : true ≡ false → ⊥
  noTF ()

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  star-true : ∀ C → isStar C ≡ true → C ≡ ⋆
  star-true ⋆           _ = refl
  star-true (arr _ _ _) ()

------------------------------------------------------------------------
-- Objects.

objs-lookup : ∀ Γ {o} → o ∈ᴺ objs Γ → lookup Γ o ≡ just ⋆
objs-lookup Γ {o} m with any-witness (any-map⁻ fst (filter (λ e → isStar (snd e)) (entries Γ))
                             (subst (Any _) (map≡ fst (filter (λ e → isStar (snd e)) (entries Γ))) m))
... | (v , C) , me , refl with filter⇒ (λ e → isStar (snd e)) (entries Γ) me
...   | me' , st = subst (λ D → lookup Γ v ≡ just D) (star-true C (T-true st)) (Gr.entries-lookup Γ me')
  where
  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

module _ (Γ : Ctx) (P : PsFacts Γ) where
  private
    module F = DF (cells Γ)
    os = objs Γ

  -- A cell: a variable whose type is not ⋆.
  Ent : Nat → Set
  Ent v = Σ Ty λ C → (lookup Γ v ≡ just C) × (isStar C ≡ false)

  data AllEnt : Tuple → Set where
    []  : AllEnt []
    _∷_ : ∀ {v w} → Ent v → AllEnt w → AllEnt (v ∷ w)

  AllEnt-++ : ∀ {x y} → AllEnt x → AllEnt y → AllEnt (x ++ y)
  AllEnt-++ []       q = q
  AllEnt-++ (e ∷ p)  q = e ∷ AllEnt-++ p q

  AllEnt-++⁻ : ∀ x {y} → AllEnt (x ++ y) → AllEnt x × AllEnt y
  AllEnt-++⁻ []      q       = [] , q
  AllEnt-++⁻ (v ∷ x) (e ∷ q) = let (a , b) = AllEnt-++⁻ x q in (e ∷ a) , b

  -- Entries of composable tuples are cells.
  wft-ent : ∀ {x y} w → WFT Γ x y w → AllEnt w
  wft-ent []      _            = []
  wft-ent (v ∷ w) (z , ev , p) with endsL-inv (lookup Γ v) ev
  ... | ⋆ , lv , ()
  ... | arr B s t , lv , _ = (arr B s t , lv , refl) ∷ wft-ent w p

  -- The cell of a variable.
  findEl-var : ∀ v C k → lookup Γ v ≡ just C → Gr.homOf os C ≡ just k →
               findEl v (cells Γ) ≡ just (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)))
  findEl-var v C k lv hk =
    trans (Gr.findEl-cells os Γ v) (go lv)
    where
    go : lookup Γ v ≡ just C → Gr.elAt os Γ v ≡ just (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)))
    go eL with lookup Γ v
    go refl | .(just C) rewrite Gr.mkEl≡ os v C | hk = refl

  -- The boundary entries of a cell of dimension ≥ 2 are its faces.
  bdEl-var : ∀ v B a a' i j → lookup Γ v ≡ just (arr (arr B a a') (var i) (var j)) →
             bdEl (cells Γ) v ≡ i ∷ j ∷ []
  bdEl-var v B a a' i j lv with cellP P v _ lv refl
  ... | k , hk , _ rewrite findEl-var v _ k lv hk = refl

  bd-faces : ∀ v C {s t} → lookup Γ v ≡ just C → facesTy (just C) ≡ just (s , t) →
             (s ∈ᴺ bdEl (cells Γ) v) × (t ∈ᴺ bdEl (cells Γ) v)
  bd-faces v (arr (arr B a a') (var i) (var j)) lv refl rewrite bdEl-var v B a a' i j lv =
    hereA refl , thereA (hereA refl)
  bd-faces v ⋆ lv ()
  bd-faces v (arr ⋆ _ _) lv ()
  bd-faces v (arr (arr _ _ _) (coh _ _ _) _) lv ()
  bd-faces v (arr (arr _ _ _) (cst ()) _) lv
  bd-faces v (arr (arr _ _ _) (var _) (coh _ _ _)) lv ()
  bd-faces v (arr (arr _ _ _) (var _) (cst ())) lv

  -- A face in the strict complex is one Gray step.
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

  ----------------------------------------------------------------------
  -- Steps keep entries cells.

  private
    bd-ent : ∀ {w b} → Ent w → b ∈ᴺ bdEl (cells Γ) w → Ent b
    bd-ent {w} (⋆ , lw , ()) mb
    bd-ent {w} (arr ⋆ s t , lw , _) mb with cellP P w _ lw refl
    ... | k , hk , _ rewrite findEl-var w _ k lw hk with mb
    ...   | ()
    bd-ent {w} (arr (arr B a a') s t , lw , _) mb with inv P w _ lw
    ... | i , j , refl , refl , li , lj rewrite bdEl-var w B a a' i j lw with mb
    ...   | hereA refl          = arr B a a' , li , refl
    ...   | thereA (hereA refl) = arr B a a' , lj , refl
    ...   | thereA (thereA ())

  step-ent : ∀ {x y} → F.Step x y → AllEnt x → AllEnt y
  step-ent (F.sh mb) (e ∷ es) = bd-ent e mb ∷ es
  step-ent (F.st s)  (e ∷ es) = e ∷ step-ent s es

  reach-ent : ∀ {k x y} → F.Reach k x y → AllEnt x → AllEnt y
  reach-ent F.done       a = a
  reach-ent (F.step s r) a = reach-ent r (step-ent s a)

  ----------------------------------------------------------------------
  -- Lowering entries to 1-cells.

  step-app : ∀ {x y} zs → F.Step x y → F.Step (x ++ zs) (y ++ zs)
  step-app zs (F.sh mb) = F.sh mb
  step-app zs (F.st s)  = F.st (step-app zs s)

  reach-app : ∀ {k x y} zs → F.Reach k x y → F.Reach k (x ++ zs) (y ++ zs)
  reach-app zs F.done       = F.done
  reach-app zs (F.step s r) = F.step (step-app zs s) (reach-app zs r)

  reach-pre : ∀ {k x y} qs → F.Reach k x y → F.Reach k (qs ++ x) (qs ++ y)
  reach-pre []       r = r
  reach-pre (p ∷ qs) r = cons (reach-pre qs r)
    where
    cons : ∀ {k x y} → F.Reach k x y → F.Reach k (p ∷ x) (p ∷ y)
    cons F.done       = F.done
    cons (F.step s r) = F.step (F.st s) (cons r)

  private
    dim-pos : ∀ C → isStar C ≡ false → Σ Nat λ n → dim C ≡ suc n
    dim-pos ⋆           ()
    dim-pos (arr B _ _) _ = dim B , refl

    desc : ∀ n v C → lookup Γ v ≡ just C → dim C ≡ suc n →
           Σ Nat λ o → One Γ P o × Σ Nat λ k → F.Reach k (v ∷ []) (o ∷ [])
    desc zero    v C lv d = v , (C , lv , d) , 0 , F.done
    desc (suc n) v ⋆ lv ()
    desc (suc n) v (arr ⋆ _ _) lv ()
    desc (suc n) v (arr (arr B a a') s t) lv d with inv P v _ lv
    ... | i , j , refl , refl , li , lj with desc n i (arr B a a') li (suc-inj d)
    ...   | o , oo , k , r = o , oo , suc k , F.step (F.sh (fst (bd-faces v _ lv refl))) r

  lower1 : ∀ {v} → Ent v → Σ Nat λ o → One Γ P o × Σ Nat λ k → ∀ ws → F.Reach k (v ∷ ws) (o ∷ ws)
  lower1 {v} (C , lv , st) with dim-pos C st
  ... | n , d with desc n v C lv d
  ...   | o , oo , k , r = o , oo , k , λ ws → reach-app ws r

  lower : ∀ {p} → AllEnt p → ∀ ws → Σ Tuple λ p' → AllOne Γ P p' × Σ Nat λ k → F.Reach k (p ++ ws) (p' ++ ws)
  lower []       ws = [] , [] , 0 , F.done
  lower {v ∷ p} (e ∷ es) ws with lower1 e | lower es ws
  ... | o , oo , k , r | p' , ap , j , q =
    o ∷ p' , oo ∷ ap , j + k , F.reach-++ (reach-pre (v ∷ []) q) (r (p' ++ ws))

  -- A tuple of cells through g reaches one whose other entries are 1-cells.
  through' : ∀ p g q → AllEnt (p ++ g ∷ q) →
             Σ Tuple λ pre → Σ Tuple λ post → AllOne Γ P pre × AllOne Γ P post ×
             Σ Nat λ k → F.Reach k (p ++ g ∷ q) (pre ++ g ∷ post)
  through' p g q a with AllEnt-++⁻ p a
  ... | ap , (_ ∷ aq) with lower aq []
  ...   | q' , oq , j , rq with lower ap (g ∷ q')
  ...     | p' , op , k , rp = p' , q' , op , oq , j + k , F.reach-++ r1 rp
    where
    subst₂' : ∀ {A : Set} (R : A → A → Set) {a a' b b'} → a ≡ a' → b ≡ b' → R a b → R a' b'
    subst₂' R refl refl r = r
    r1 : F.Reach j (p ++ g ∷ q) (p ++ g ∷ q')
    r1 = subst₂' (F.Reach j) (++-assocL p (g ∷ []) q) (++-assocL p (g ∷ []) q')
           (reach-pre (p ++ g ∷ []) (subst₂' (F.Reach j) (++-[]L q) (++-[]L q') rq))
