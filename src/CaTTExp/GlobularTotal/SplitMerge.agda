------------------------------------------------------------------------
-- F2c, step (P2) of lemmas 3–5: `split` inverts `merge`.
--
--   split-merge : shape a ≡ shape a′ → WF a′ → WF b′ → Compat k a′ b′ →
--                 split k a (merge k a′ b′) ≡ (a′ , b′)
--
-- `split k a E` cuts a tree of shape a ∗ₖ b into its two parts, reading
-- only the shape of a. So when the first factor of a composite has a's
-- shape, split recovers both factors. This is what makes `assign` hand
-- each argument of a coherence the cells it occupies.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.SplitMerge where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; split; splitL; shape; shapes; module Lists)
open Lists using (headN; lastN; take; drop; length)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat) renaming (len to lenL)

private
  node-inj : ∀ {ts ts'} → node ts ≡ node ts' → ts ≡ ts'
  node-inj refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  -- lengths
  len-shapes : ∀ cs cs' → shapes cs ≡ shapes cs' → length cs ≡ length cs'
  len-shapes []       []        e = refl
  len-shapes []       (c' ∷ cs') ()
  len-shapes (c ∷ cs) []        ()
  len-shapes (c ∷ cs) (c' ∷ cs') e = cong suc (len-shapes cs cs' (∷-injₜ e))

  len-length : ∀ {A : Set} (xs : List A) → lenL xs ≡ length xs
  len-length []       = refl
  len-length (x ∷ xs) = cong suc (len-length xs)

  take-++ : ∀ {A : Set} n (xs ys : List A) → length xs ≡ n → take n (xs ++ ys) ≡ xs
  take-++ zero    []       ys e = refl
  take-++ (suc n) (x ∷ xs) ys e = cong (x ∷_) (take-++ n xs ys (suc-inj e))

  drop-++ : ∀ {A : Set} n (xs ys : List A) → length xs ≡ n → drop n (xs ++ ys) ≡ ys
  drop-++ zero    []       ys e = refl
  drop-++ (suc n) (x ∷ xs) ys e = drop-++ n xs ys (suc-inj e)

  -- dropping all but the last object
  drop-last : ∀ n (os ys : List Nat) → length os ≡ suc n → drop n (os ++ ys) ≡ lastN os ∷ ys
  drop-last zero    (o ∷ [])      ys e = refl
  drop-last zero    (o ∷ o' ∷ os) ys ()
  drop-last (suc n) (o ∷ [])      ys ()
  drop-last (suc n) (o ∷ o' ∷ os) ys e = drop-last n (o' ∷ os) ys (suc-inj e)

  head-drop : ∀ (os : List Nat) → length os ≡ suc (length (drop 1 os)) → headN os ∷ drop 1 os ≡ os
  head-drop []       ()
  head-drop (o ∷ os) e = refl

  len-drop1 : ∀ (os : List Nat) n → length os ≡ suc n → length os ≡ suc (length (drop 1 os))
  len-drop1 []       n ()
  len-drop1 (o ∷ os) n e = refl

mutual
  split-merge : ∀ k a a' b' → shape a ≡ shape a' → WF a' → WF b' → Compat k a' b' →
                split k a (merge k a' b') ≡ (a' , b')
  split-merge zero (lt _ csA) (lt os cs) (lt os' cs') sh (wo , _) (wo' , _) cp =
    cong₂ _,_
      (cong₂ lt (take-++ (suc m) os (drop 1 os') (trans (sym (len-length os)) (trans wo (cong suc (trans (len-length cs) (sym mA))))))
                (take-++ m cs cs' (sym mA)))
      (cong₂ lt (trans (drop-last m os (drop 1 os') (trans (sym (len-length os)) (trans wo (cong suc (trans (len-length cs) (sym mA))))))
                       (trans (cong (_∷ drop 1 os') (∷-injₕ (lt-injₒ cp)))
                              (head-drop os' (len-drop1 os' (lenL cs') (trans (sym (len-length os')) wo')))))
                (drop-++ m cs cs' (sym mA)))
    where
    m = length csA
    mA : m ≡ length cs
    mA = len-shapes csA cs (node-inj sh)
  split-merge (suc k) (lt _ csA) (lt os cs) (lt os' cs') sh (_ , ws) (_ , ws') cp with lt-injₒ cp
  ... | refl rewrite splitL-mergeL k csA cs cs' (node-inj sh) ws ws' (lt-injₛ cp) = refl

  splitL-mergeL : ∀ k csA cs cs' → shapes csA ≡ shapes cs → WFs cs → WFs cs' → bdL true k cs ≡ bdL false k cs' →
                  splitL k csA (mergeL k cs cs') ≡ (cs , cs')
  splitL-mergeL k []         []       []         sh _ _ _ = refl
  splitL-mergeL k []         []       (c' ∷ cs') sh _ _ ()
  splitL-mergeL k []         (c ∷ cs) _          () _ _ _
  splitL-mergeL k (a ∷ as)   []       _          () _ _ _
  splitL-mergeL k (a ∷ as)   (c ∷ cs) []         sh _ _ ()
  splitL-mergeL k (a ∷ as)   (c ∷ cs) (c' ∷ cs') sh (w , ws) (w' , ws') e
    rewrite split-merge k a c c' (∷-injₕ sh) w w' (∷-injₕ e)
          | splitL-mergeL k as cs cs' (∷-injₜ sh) ws ws' (∷-injₜ e) = refl
