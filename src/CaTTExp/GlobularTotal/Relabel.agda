------------------------------------------------------------------------
-- F2c, step (P1) of lemmas 3–5: relabelling.
--
-- `relab f a` renames every label y of a to f y. The filler's
-- substitution λ : Θ_τ → Γ is read off the pairs `zipLab (idTree τ) N`
-- with `find`; write `lamF L y` for the label `find` returns. Then
--
--   relab-id : shape N ≡ τ → WF N → relab (lamF (zipLab (idTree τ) N)) (idTree τ) ≡ N
--
-- i.e. relabelling Θ_τ's own tree along λ gives back N. This needs the
-- labels of idTree τ to be distinct (LabDistinct), so that every
-- variable's pair is the one at its own position. Also here:
-- shape (idTree τ) ≡ τ.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Relabel where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
  using (LT; lt; labT; labCs; idTree; shape; shapes; zipLab; zipLabs; zipN; module Lists)
open Lists using (find)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs) renaming (len to lenL)
open import CaTTExp.GlobularTotal.LabDistinct using (NodupL; ND; NDs; nd-idTree)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  ∨-false : ∀ a b → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false false false e = refl , refl
  ∨-false true  b     ()
  ∨-false false true  ()

  not-true : ∀ b → (b ≡ true → ⊥) → b ≡ false
  not-true true  f = ⊥-elim (f refl)
  not-true false f = refl

  t≢f : true ≡ false → ⊥
  t≢f ()

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  node-inj : ∀ {ts ts'} → node ts ≡ node ts' → ts ≡ ts'
  node-inj refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

------------------------------------------------------------------------
-- Relabelling.

mapN : (Nat → Nat) → List Nat → List Nat
mapN f []       = []
mapN f (x ∷ xs) = f x ∷ mapN f xs

mutual
  relab : (Nat → Nat) → LT → LT
  relab f (lt os cs) = lt (mapN f os) (relabs f cs)

  relabs : (Nat → Nat) → List LT → List LT
  relabs f []       = []
  relabs f (c ∷ cs) = relab f c ∷ relabs f cs

val : Maybe Nat → Nat
val (just x) = x
val nothing  = 0

lamF : List (Nat × Nat) → Nat → Nat
lamF L y = val (find y L)

------------------------------------------------------------------------
-- find on appended association lists.

memK : Nat → List (Nat × Nat) → Bool
memK y []             = false
memK y ((k , _) ∷ L) = (y ==ℕ k) ∨ memK y L

private
  memK-++ : ∀ y L₁ L₂ → memK y (L₁ ++ L₂) ≡ (memK y L₁ ∨ memK y L₂)
  memK-++ y []             L₂ = refl
  memK-++ y ((k , _) ∷ L₁) L₂ with y ==ℕ k
  ... | true  = refl
  ... | false = memK-++ y L₁ L₂

  find-in : ∀ y L₁ L₂ → memK y L₁ ≡ true → find y (L₁ ++ L₂) ≡ find y L₁
  find-in y []             L₂ ()
  find-in y ((k , v) ∷ L₁) L₂ m with y ==ℕ k
  ... | true  = refl
  ... | false = find-in y L₁ L₂ m

  find-out : ∀ y L₁ L₂ → memK y L₁ ≡ false → find y (L₁ ++ L₂) ≡ find y L₂
  find-out y []             L₂ m = refl
  find-out y ((k , v) ∷ L₁) L₂ m with y ==ℕ k
  find-out y ((k , v) ∷ L₁) L₂ () | true
  ... | false = find-out y L₁ L₂ m

  memK-zipN : ∀ y os os' → lenL os ≡ lenL os' → memK y (zipN os os') ≡ memL y os
  memK-zipN y []       []         e = refl
  memK-zipN y []       (o' ∷ os') ()
  memK-zipN y (o ∷ os) []         ()
  memK-zipN y (o ∷ os) (o' ∷ os') e = cong ((y ==ℕ o) ∨_) (memK-zipN y os os' (suc-inj e))

  len-shapes : ∀ cs cs' → shapes cs ≡ shapes cs' → lenL cs ≡ lenL cs'
  len-shapes []       []        e = refl
  len-shapes []       (c' ∷ cs') ()
  len-shapes (c ∷ cs) []        ()
  len-shapes (c ∷ cs) (c' ∷ cs') e = cong suc (len-shapes cs cs' (∷-injₜ e))

  len-os : ∀ os cs os' cs' → shape (lt os cs) ≡ shape (lt os' cs') →
           WF (lt os cs) → WF (lt os' cs') → lenL os ≡ lenL os'
  len-os os cs os' cs' sh (w , _) (w' , _) =
    trans w (trans (cong suc (len-shapes cs cs' (node-inj sh))) (sym w'))

mutual
  memK-zipLab : ∀ y X N → shape X ≡ shape N → WF X → WF N → memK y (zipLab X N) ≡ mem y X
  memK-zipLab y (lt os cs) (lt os' cs') sh wX wN =
    trans (memK-++ y (zipN os os') (zipLabs cs cs'))
      (cong₂ _∨_ (memK-zipN y os os' (len-os os cs os' cs' sh wX wN))
                 (memK-zipLabs y cs cs' (node-inj sh) (snd wX) (snd wN)))

  memK-zipLabs : ∀ y cs cs' → shapes cs ≡ shapes cs' → WFs cs → WFs cs' → memK y (zipLabs cs cs') ≡ memCs y cs
  memK-zipLabs y []       []         sh _ _ = refl
  memK-zipLabs y []       (c' ∷ cs') ()
  memK-zipLabs y (c ∷ cs) []         ()
  memK-zipLabs y (c ∷ cs) (c' ∷ cs') sh (w , ws) (w' , ws') =
    trans (memK-++ y (zipLab c c') (zipLabs cs cs'))
      (cong₂ _∨_ (memK-zipLab y c c' (∷-injₕ sh) w w') (memK-zipLabs y cs cs' (∷-injₜ sh) ws ws'))

------------------------------------------------------------------------
-- Relabelling along the pairs gives the second tree.

private
  ne-of : ∀ y o os → memL y os ≡ true → memL o os ≡ false → (y ==ℕ o) ≡ false
  ne-of y o os m n = not-true _ (λ h → t≢f (trans (sym m) (subst (λ z → memL z os ≡ false) (sym (==ℕ-sound y o (≡-T h))) n)))

  zipN-map : ∀ L os os' R → NodupL os → lenL os ≡ lenL os' →
             (∀ y → memL y os ≡ true → find y L ≡ find y (zipN os os' ++ R)) →
             mapN (lamF L) os ≡ os'
  zipN-map L []       []         R _ _ h = refl
  zipN-map L []       (o' ∷ os') R _ () h
  zipN-map L (o ∷ os) []         R _ () h
  zipN-map L (o ∷ os) (o' ∷ os') R (o∉ , nd) e h =
    cong₂ _∷_ hd (zipN-map L os os' R nd (suc-inj e) tl)
    where
    hd : lamF L o ≡ o'
    hd rewrite h o (∨-inl _ _ (T-≡ (==ℕ-refl o))) | T-≡ (==ℕ-refl o) = refl

    tl : ∀ y → memL y os ≡ true → find y L ≡ find y (zipN os os' ++ R)
    tl y m rewrite h y (∨-inr (y ==ℕ o) _ m) | ne-of y o os m o∉ = refl

mutual
  relab-zip : ∀ L X N → shape X ≡ shape N → WF X → WF N → ND X →
              (∀ y → mem y X ≡ true → find y L ≡ find y (zipLab X N)) → relab (lamF L) X ≡ N
  relab-zip L (lt os cs) (lt os' cs') sh wX wN (ndo , dis , nds) h =
    cong₂ lt (zipN-map L os os' (zipLabs cs cs') ndo (len-os os cs os' cs' sh wX wN)
                (λ y m → h y (∨-inl _ _ m)))
             (relabs-zip L cs cs' (node-inj sh) (snd wX) (snd wN) nds hc)
    where
    hc : ∀ y → memCs y cs ≡ true → find y L ≡ find y (zipLabs cs cs')
    hc y m = trans (h y (∨-inr (memL y os) _ m))
                   (find-out y (zipN os os') (zipLabs cs cs')
                      (trans (memK-zipN y os os' (len-os os cs os' cs' sh wX wN))
                             (not-true _ (λ o → t≢f (trans (sym m) (dis y o))))))

  relabs-zip : ∀ L cs cs' → shapes cs ≡ shapes cs' → WFs cs → WFs cs' → NDs cs →
               (∀ y → memCs y cs ≡ true → find y L ≡ find y (zipLabs cs cs')) → relabs (lamF L) cs ≡ cs'
  relabs-zip L []       []         sh _ _ _ h = refl
  relabs-zip L []       (c' ∷ cs') ()
  relabs-zip L (c ∷ cs) []         ()
  relabs-zip L (c ∷ cs) (c' ∷ cs') sh (w , ws) (w' , ws') (ndc , dis , nds) h =
    cong₂ _∷_ (relab-zip L c c' (∷-injₕ sh) w w' ndc hd)
              (relabs-zip L cs cs' (∷-injₜ sh) ws ws' nds tl)
    where
    hd : ∀ y → mem y c ≡ true → find y L ≡ find y (zipLab c c')
    hd y m = trans (h y (∨-inl _ _ m))
                   (find-in y (zipLab c c') (zipLabs cs cs') (trans (memK-zipLab y c c' (∷-injₕ sh) w w') m))

    tl : ∀ y → memCs y cs ≡ true → find y L ≡ find y (zipLabs cs cs')
    tl y m = trans (h y (∨-inr (mem y c) _ m))
                   (find-out y (zipLab c c') (zipLabs cs cs')
                      (trans (memK-zipLab y c c' (∷-injₕ sh) w w')
                             (not-true _ (λ o → t≢f (trans (sym m) (dis y o))))))

------------------------------------------------------------------------
-- The tree of a pasting context has that shape.

mutual
  shape-labT : ∀ t x n → shape (fst (labT t x n)) ≡ t
  shape-labT (node cs) x n with labCs cs n | shape-labCs cs n
  ... | os , ls , n' | e = cong node e

  shape-labCs : ∀ cs n → shapes (fst (snd (labCs cs n))) ≡ cs
  shape-labCs []       n = refl
  shape-labCs (c ∷ cs) n with labT c (suc n) (suc (suc n)) | shape-labT c (suc n) (suc (suc n))
  ... | l , n₁ | el with labCs cs n₁ | shape-labCs cs n₁
  ...   | os , ls , n₂ | e = cong₂ _∷_ el e

shape-id : ∀ τ → shape (idTree τ) ≡ τ
shape-id τ = shape-labT τ 0 1

------------------------------------------------------------------------
-- Relabelling Θ_τ's tree along λ gives N back.

open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.DimCheck using (ex-wf)

wf-id : ∀ τ → WF (idTree τ)
wf-id τ = ex-wf (ctxOf τ) 0 nothing (idTree τ) (lab-ex τ)

relab-id : ∀ τ N → shape N ≡ τ → WF N → relab (lamF (zipLab (idTree τ) N)) (idTree τ) ≡ N
relab-id τ N sh wN =
  relab-zip (zipLab (idTree τ) N) (idTree τ) N (trans (shape-id τ) (sym sh)) (wf-id τ) wN (nd-idTree τ)
    (λ y _ → refl)
