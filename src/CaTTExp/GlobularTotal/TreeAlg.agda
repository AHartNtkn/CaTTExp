------------------------------------------------------------------------
-- F2c, lemma 1a: boundary/merge algebra of labelled pasting trees
-- (CaTTExp.GlobularFiller's LT, merge, bd).
--
-- For well-formed trees a, b that are k-composable (bd true k a ≡
-- bd false k b):
--   bd-merge-src : bd false k (merge k a b) ≡ bd false k a
--   bd-merge-tgt : bd true  k (merge k a b) ≡ bd true  k b
--   bd-merge-low : j < k  ⟹  bd β j (merge k a b) ≡ bd β j a
--   bd-merge-high: j > k  ⟹  bd β j (merge k a b) ≡ merge k (bd β j a) (bd β j b)
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.TreeAlg where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (headN; lastN; drop)

------------------------------------------------------------------------
-- Well-formedness: m + 1 objects for m children, recursively.

len : ∀ {a} {A : Set a} → List A → Nat
len []       = 0
len (_ ∷ xs) = suc (len xs)

mutual
  WF : LT → Set
  WF (lt os cs) = (len os ≡ suc (len cs)) × WFs cs

  WFs : List LT → Set
  WFs []       = ⊤
  WFs (c ∷ cs) = WF c × WFs cs

Compat : Nat → LT → LT → Set
Compat k a b = bd true k a ≡ bd false k b

private
  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  ++-[] : ∀ (xs : List Nat) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  lastN-app : ∀ os r rs → lastN (os ++ (r ∷ rs)) ≡ lastN (r ∷ rs)
  lastN-app []           r rs = refl
  lastN-app (x ∷ [])     r rs = refl
  lastN-app (x ∷ y ∷ ys) r rs = lastN-app (y ∷ ys) r rs

  lastN-++ : ∀ os rest o' → lastN os ≡ o' → lastN (os ++ rest) ≡ lastN (o' ∷ rest)
  lastN-++ os []       o' e = trans (cong lastN (++-[] os)) e
  lastN-++ os (r ∷ rs) o' e = lastN-app os r rs

  0≢suc : ∀ {n} → zero ≡ suc n → ⊥
  0≢suc ()

------------------------------------------------------------------------
-- Source and target of a composite.

mutual
  bd-merge-src : ∀ k a b → WF a → Compat k a b → bd false k (merge k a b) ≡ bd false k a
  bd-merge-src zero    (lt [] cs)       b (l , _) c = ⊥-elim (0≢suc l)
  bd-merge-src zero    (lt (o ∷ os) cs) (lt os' cs') _ c = refl
  bd-merge-src (suc k) (lt os cs) (lt os' cs') (_ , w) c =
    cong (lt os) (bdL-mergeL-src k cs cs' w (lt-injₛ c))

  bdL-mergeL-src : ∀ k cs cs' → WFs cs → bdL true k cs ≡ bdL false k cs' →
                   bdL false k (mergeL k cs cs') ≡ bdL false k cs
  bdL-mergeL-src k []       []         _       _ = refl
  bdL-mergeL-src k []       (c' ∷ cs') _       ()
  bdL-mergeL-src k (c ∷ cs) []         _       ()
  bdL-mergeL-src k (c ∷ cs) (c' ∷ cs') (w , ws) e =
    cong₂ _∷_ (bd-merge-src k c c' w (∷-injₕ e)) (bdL-mergeL-src k cs cs' ws (∷-injₜ e))

mutual
  bd-merge-tgt : ∀ k a b → WF a → WF b → Compat k a b → bd true k (merge k a b) ≡ bd true k b
  bd-merge-tgt zero (lt os cs) (lt [] cs') _ (l , _) c = ⊥-elim (0≢suc l)
  bd-merge-tgt zero (lt os cs) (lt (o' ∷ rest) cs') _ _ c =
    cong (λ x → lt (x ∷ []) []) (lastN-++ os rest o' (∷-injₕ (lt-injₒ c)))
  bd-merge-tgt (suc k) (lt os cs) (lt os' cs') (_ , w) (_ , w') c =
    cong₂ lt (lt-injₒ c) (bdL-mergeL-tgt k cs cs' w w' (lt-injₛ c))

  bdL-mergeL-tgt : ∀ k cs cs' → WFs cs → WFs cs' → bdL true k cs ≡ bdL false k cs' →
                   bdL true k (mergeL k cs cs') ≡ bdL true k cs'
  bdL-mergeL-tgt k []       []         _        _         _ = refl
  bdL-mergeL-tgt k []       (c' ∷ cs') _        _         ()
  bdL-mergeL-tgt k (c ∷ cs) []         _        _         ()
  bdL-mergeL-tgt k (c ∷ cs) (c' ∷ cs') (w , ws) (w' , ws') e =
    cong₂ _∷_ (bd-merge-tgt k c c' w w' (∷-injₕ e)) (bdL-mergeL-tgt k cs cs' ws ws' (∷-injₜ e))

------------------------------------------------------------------------
-- Lower boundaries of a composite are those of either factor; higher
-- boundaries of a composite are composites of boundaries.

mutual
  bd-merge-low : ∀ β j k a b → WF a → WF b → Compat k a b → T (j <ℕ k) →
                 bd β j (merge k a b) ≡ bd β j a
  bd-merge-low false zero    (suc k) (lt os cs) (lt _ cs') _ _ _ _ = refl
  bd-merge-low true  zero    (suc k) (lt os cs) (lt _ cs') _ _ _ _ = refl
  bd-merge-low false (suc j) (suc k) (lt os cs) (lt _ cs') (_ , w) (_ , w') c p =
    cong (lt os) (bdL-mergeL-low false j k cs cs' w w' (lt-injₛ c) p)
  bd-merge-low true  (suc j) (suc k) (lt os cs) (lt _ cs') (_ , w) (_ , w') c p =
    cong (lt os) (bdL-mergeL-low true j k cs cs' w w' (lt-injₛ c) p)

  bdL-mergeL-low : ∀ β j k cs cs' → WFs cs → WFs cs' → bdL true k cs ≡ bdL false k cs' →
                   T (j <ℕ k) → bdL β j (mergeL k cs cs') ≡ bdL β j cs
  bdL-mergeL-low β j k []       []         _        _         _ p = refl
  bdL-mergeL-low β j k []       (c' ∷ cs') _        _         () p
  bdL-mergeL-low β j k (c ∷ cs) []         _        _         () p
  bdL-mergeL-low β j k (c ∷ cs) (c' ∷ cs') (w , ws) (w' , ws') e p =
    cong₂ _∷_ (bd-merge-low β j k c c' w w' (∷-injₕ e) p)
              (bdL-mergeL-low β j k cs cs' ws ws' (∷-injₜ e) p)

private
  bdL-++ : ∀ β j cs cs' → bdL β j (cs ++ cs') ≡ (bdL β j cs ++ bdL β j cs')
  bdL-++ β j []       cs' = refl
  bdL-++ β j (c ∷ cs) cs' = cong (bd β j c ∷_) (bdL-++ β j cs cs')

mutual
  bd-merge-high : ∀ β j k a b → T (k <ℕ j) → bd β j (merge k a b) ≡ merge k (bd β j a) (bd β j b)
  bd-merge-high false (suc j) zero    (lt os cs) (lt os' cs') _ = cong (lt _) (bdL-++ false j cs cs')
  bd-merge-high true  (suc j) zero    (lt os cs) (lt os' cs') _ = cong (lt _) (bdL-++ true j cs cs')
  bd-merge-high false (suc j) (suc k) (lt os cs) (lt _ cs') p =
    cong (lt os) (bdL-mergeL-high false j k cs cs' p)
  bd-merge-high true  (suc j) (suc k) (lt os cs) (lt _ cs') p =
    cong (lt os) (bdL-mergeL-high true j k cs cs' p)

  bdL-mergeL-high : ∀ β j k cs cs' → T (k <ℕ j) →
                    bdL β j (mergeL k cs cs') ≡ mergeL k (bdL β j cs) (bdL β j cs')
  bdL-mergeL-high β j k []       cs'        p = refl
  bdL-mergeL-high β j k (c ∷ cs) []         p = refl
  bdL-mergeL-high β j k (c ∷ cs) (c' ∷ cs') p =
    cong₂ _∷_ (bd-merge-high β j k c c' p) (bdL-mergeL-high β j k cs cs' p)

------------------------------------------------------------------------
-- Well-formedness is preserved by boundaries and composites.

private
  len-bdL : ∀ β j cs → len (bdL β j cs) ≡ len cs
  len-bdL β j []       = refl
  len-bdL β j (c ∷ cs) = cong suc (len-bdL β j cs)

  len-++ : ∀ {a} {A : Set a} (xs ys : List A) → len (xs ++ ys) ≡ len xs + len ys
  len-++ []       ys = refl
  len-++ (x ∷ xs) ys = cong suc (len-++ xs ys)

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  len-cong : ∀ {a} {A : Set a} {xs ys : List A} → xs ≡ ys → len xs ≡ len ys
  len-cong refl = refl

mutual
  wf-bd : ∀ β j a → WF a → WF (bd β j a)
  wf-bd false zero    (lt os cs) _       = refl , tt
  wf-bd true  zero    (lt os cs) _       = refl , tt
  wf-bd false (suc j) (lt os cs) (l , w) = trans l (cong suc (sym (len-bdL false j cs))) , wfs-bd false j cs w
  wf-bd true  (suc j) (lt os cs) (l , w) = trans l (cong suc (sym (len-bdL true j cs))) , wfs-bd true j cs w

  wfs-bd : ∀ β j cs → WFs cs → WFs (bdL β j cs)
  wfs-bd β j []       _        = tt
  wfs-bd β j (c ∷ cs) (w , ws) = wf-bd β j c w , wfs-bd β j cs ws

private
  wfs-++ : ∀ cs cs' → WFs cs → WFs cs' → WFs (cs ++ cs')
  wfs-++ []       cs' _        w' = w'
  wfs-++ (c ∷ cs) cs' (w , ws) w' = w , wfs-++ cs cs' ws w'

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

mutual
  wf-merge : ∀ k a b → WF a → WF b → Compat k a b → WF (merge k a b)
  wf-merge zero (lt os cs) (lt [] cs') _ (l' , _) _ = ⊥-elim (0≢suc l')
  wf-merge zero (lt os cs) (lt (o' ∷ rest) cs') (l , w) (l' , w') _ =
    trans (len-++ os rest)
      (trans (cong (_+ len rest) l)
        (cong suc (trans (cong (len cs +_) (suc-inj l')) (sym (len-++ cs cs'))))) ,
    wfs-++ cs cs' w w'
  wf-merge (suc k) (lt os cs) (lt os' cs') (l , w) (l' , w') c =
    trans l (cong suc (sym (len-mergeL k cs cs' (suc-inj (trans (sym l) (trans (len-cong (lt-injₒ c)) l')))))) ,
    wfs-mergeL k cs cs' w w' (lt-injₛ c)

  wfs-mergeL : ∀ k cs cs' → WFs cs → WFs cs' → bdL true k cs ≡ bdL false k cs' → WFs (mergeL k cs cs')
  wfs-mergeL k []       cs'        _        _         _ = tt
  wfs-mergeL k (c ∷ cs) []         _        _         _ = tt
  wfs-mergeL k (c ∷ cs) (c' ∷ cs') (w , ws) (w' , ws') e =
    wf-merge k c c' w w' (∷-injₕ e) , wfs-mergeL k cs cs' ws ws' (∷-injₜ e)

  len-mergeL : ∀ k cs cs' → len cs ≡ len cs' → len (mergeL k cs cs') ≡ len cs
  len-mergeL k []       []         _ = refl
  len-mergeL k []       (c' ∷ cs') ()
  len-mergeL k (c ∷ cs) []         ()
  len-mergeL k (c ∷ cs) (c' ∷ cs') e = cong suc (len-mergeL k cs cs' (suc-inj e))
