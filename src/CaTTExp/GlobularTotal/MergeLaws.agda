------------------------------------------------------------------------
-- F2c, toward lemma 1b: the strict ω-category laws for composition of
-- labelled pasting trees (GlobularFiller.merge), on the nose.
--
--   merge-assoc : merge k (merge k a b) c ≡ merge k a (merge k b c)
--   merge-unitl : x thin at k (bd false k x ≡ x) ⟹ merge k x b ≡ b
--   merge-unitr : x thin at k (bd true  k x ≡ x) ⟹ merge k a x ≡ a
--   merge-xch   : j < k ⟹
--     merge k (merge j a b) (merge j c d) ≡ merge j (merge k a c) (merge k b d)
--
-- These are what make the strict image of a substitution a functor
-- (flat over a composite is the composite of the flats).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.MergeLaws where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat; len)

private
  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  ++-assoc : ∀ {a} {A : Set a} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  0≢suc : ∀ {n} → zero ≡ suc n → ⊥
  0≢suc ()

------------------------------------------------------------------------
-- Associativity.

mutual
  merge-assoc : ∀ k a b c → WF b →
                merge k (merge k a b) c ≡ merge k a (merge k b c)
  merge-assoc zero (lt osa csa) (lt [] csb) c (l , _) = ⊥-elim (0≢suc l)
  merge-assoc zero (lt osa csa) (lt (o ∷ osb) csb) (lt osc csc) _ =
    cong₂ lt (++-assoc osa osb (drop 1 osc)) (++-assoc csa csb csc)
  merge-assoc (suc k) (lt osa csa) (lt osb csb) (lt osc csc) (_ , w) =
    cong (lt osa) (mergeL-assoc k csa csb csc w)

  mergeL-assoc : ∀ k as bs cs → WFs bs →
                 mergeL k (mergeL k as bs) cs ≡ mergeL k as (mergeL k bs cs)
  mergeL-assoc k []       bs       cs       w = refl
  mergeL-assoc k (a ∷ as) []       cs       w = refl
  mergeL-assoc k (a ∷ as) (b ∷ bs) []       w = refl
  mergeL-assoc k (a ∷ as) (b ∷ bs) (c ∷ cs) (wb , w) =
    cong₂ _∷_ (merge-assoc k a b c wb) (mergeL-assoc k as bs cs w)

------------------------------------------------------------------------
-- Interchange.

private
  len-bdL : ∀ β j cs → len (bdL β j cs) ≡ len cs
  len-bdL β j []       = refl
  len-bdL β j (c ∷ cs) = cong suc (len-bdL β j cs)

  len-cong : ∀ {xs ys : List LT} → xs ≡ ys → len xs ≡ len ys
  len-cong refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  -- Zipping distributes over appending lists of equal length.
  mergeL-++ : ∀ k as bs cs ds → len as ≡ len cs →
              mergeL k (as ++ bs) (cs ++ ds) ≡ (mergeL k as cs ++ mergeL k bs ds)
  mergeL-++ k []       bs []       ds _ = refl
  mergeL-++ k []       bs (c ∷ cs) ds ()
  mergeL-++ k (a ∷ as) bs []       ds ()
  mergeL-++ k (a ∷ as) bs (c ∷ cs) ds l =
    cong (merge k a c ∷_) (mergeL-++ k as bs cs ds (suc-inj l))

mutual
  merge-xch : ∀ j k a b c d → T (j <ℕ k) → Compat k a c →
              merge k (merge j a b) (merge j c d) ≡ merge j (merge k a c) (merge k b d)
  merge-xch zero (suc k) (lt osa csa) (lt osb csb) (lt osc csc) (lt osd csd) _ cp =
    cong (lt _) (mergeL-++ k csa csb csc csd
      (trans (sym (len-bdL true k csa)) (trans (len-cong (lt-injₛ cp)) (len-bdL false k csc))))
  merge-xch (suc j) (suc k) (lt osa csa) (lt osb csb) (lt osc csc) (lt osd csd) p cp =
    cong (lt osa) (mergeL-xch j k csa csb csc csd p (lt-injₛ cp))

  mergeL-xch : ∀ j k as bs cs ds → T (j <ℕ k) → bdL true k as ≡ bdL false k cs →
               mergeL k (mergeL j as bs) (mergeL j cs ds)
               ≡ mergeL j (mergeL k as cs) (mergeL k bs ds)
  mergeL-xch j k []       bs       cs       ds       p e = refl
  mergeL-xch j k (a ∷ as) []       []       ds       p e = refl
  mergeL-xch j k (a ∷ as) []       (c ∷ cs) []       p e = refl
  mergeL-xch j k (a ∷ as) []       (c ∷ cs) (d ∷ ds) p e = refl
  mergeL-xch j k (a ∷ as) (b ∷ bs) []       ds       p e = refl
  mergeL-xch j k (a ∷ as) (b ∷ bs) (c ∷ cs) []       p e = refl
  mergeL-xch j k (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) p e =
    cong₂ _∷_ (merge-xch j k a b c d p (∷-injₕ e)) (mergeL-xch j k as bs cs ds p (∷-injₜ e))

------------------------------------------------------------------------
-- Units: a tree of dimension at most k is a unit for merge k.

private
  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  ++-[] : ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

mutual
  merge-unitl : ∀ k x b → bd false k x ≡ x → WF b → Compat k x b → merge k x b ≡ b
  merge-unitl zero (lt os cs) (lt [] csb) th (l , _) c = ⊥-elim (0≢suc l)
  merge-unitl zero (lt os cs) (lt (o' ∷ osb) csb) th _ c
    with lt-injₒ th | lt-injₛ th
  merge-unitl zero (lt (o ∷ []) []) (lt (o' ∷ osb) csb) th _ c | refl | refl
    with lt-injₒ c
  ... | refl = refl
  merge-unitl (suc k) (lt os cs) (lt osb csb) th (_ , w) c
    with lt-injₒ c
  ... | refl = cong (lt os) (mergeL-unitl k cs csb (lt-injₛ th) w (lt-injₛ c))

  mergeL-unitl : ∀ k xs bs → bdL false k xs ≡ xs → WFs bs → bdL true k xs ≡ bdL false k bs →
                 mergeL k xs bs ≡ bs
  mergeL-unitl k []       []       th w c = refl
  mergeL-unitl k []       (b ∷ bs) th w ()
  mergeL-unitl k (x ∷ xs) []       th w ()
  mergeL-unitl k (x ∷ xs) (b ∷ bs) th (wb , w) c =
    cong₂ _∷_ (merge-unitl k x b (∷-injₕ th) wb (∷-injₕ c))
              (mergeL-unitl k xs bs (∷-injₜ th) w (∷-injₜ c))

mutual
  merge-unitr : ∀ k a x → bd true k x ≡ x → Compat k a x → merge k a x ≡ a
  merge-unitr zero (lt osa csa) (lt os cs) th c
    with lt-injₒ th | lt-injₛ th
  merge-unitr zero (lt osa csa) (lt (o ∷ []) []) th c | refl | refl =
    cong₂ lt (++-[] osa) (++-[] csa)
  merge-unitr (suc k) (lt osa csa) (lt os cs) th c =
    cong (lt osa) (mergeL-unitr k csa cs (lt-injₛ th) (lt-injₛ c))

  mergeL-unitr : ∀ k as xs → bdL true k xs ≡ xs → bdL true k as ≡ bdL false k xs →
                 mergeL k as xs ≡ as
  mergeL-unitr k []       []       th c = refl
  mergeL-unitr k []       (x ∷ xs) th ()
  mergeL-unitr k (a ∷ as) []       th ()
  mergeL-unitr k (a ∷ as) (x ∷ xs) th c =
    cong₂ _∷_ (merge-unitr k a x (∷-injₕ th) (∷-injₕ c))
              (mergeL-unitr k as xs (∷-injₜ th) (∷-injₜ c))
