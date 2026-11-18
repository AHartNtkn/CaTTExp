------------------------------------------------------------------------
-- The checker's hom tables are the lookup-based ones, so T-cell holds.
--
-- CaTTExp.Gray.Support computes the homs of a pasting context Γ from
-- its list of entries: objs Γ, the El records of `cells`, `homAt`, and
-- the table `piece`. CaTTExp.Strict.Pasting proves the cell conditions
-- for the tables Tb Γ (o , o'), which are defined by lookups. Here we
-- show that the two agree:
--   * objs Γ is objL Γ (`objs-objL`), and the k-th hom collects the
--     cells between the (k−1)-th and k-th objects (`hk`);
--   * piece (homAt Γ k) i b is the list Tb Γ (oₖ₋₁ , oₖ) b i
--     (`piece-Tb`), using that a cell is hit only by cells of its own
--     hom (`eq-hit`) and that the hom dimension bounds every cell's;
--   * so every hom table is a TabCell (`hom-cell`), which is
--     TotalCell's `HomCells`, and the hypothesis T-cell of
--     Strict.Soundness holds (`T-cell`).
-- Nothing is postulated.
------------------------------------------------------------------------
module CaTTExp.Strict.Bridge where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Tensor
open import CaTTExp.Strict.Pasting
open import CaTTExp.Strict.TotalCell using (Ph; HC; HomCells; T-cell-from)
open import CaTTExp.Strict.Soundness using (TCell; BSupp; module Soundness)
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Booleans and arithmetic.

private
  infixr 2 _≡⟨_⟩_
  infix  3 _∎≡
  _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q
  _∎≡ : ∀ {A : Set} (x : A) → x ≡ x
  x ∎≡ = refl

lt-irr : ∀ n → T (n <ℕ n) → ⊥
lt-irr n p = subst T (len-not-lt n) p

le-trans : ∀ x m M → T (x <ℕ suc m) → T (m <ℕ suc M) → T (x <ℕ suc M)
le-trans zero    m       M       _ _ = tt
le-trans (suc x) zero    M       () _
le-trans (suc x) (suc m) zero    p ()
le-trans (suc x) (suc m) (suc M) p q = le-trans x m M p q

le-max-l : ∀ n m → T (n <ℕ suc (max n m))
le-max-l zero    m       = tt
le-max-l (suc n) zero    = n<suc n
le-max-l (suc n) (suc m) = le-max-l n m

le-max-r : ∀ n m → T (m <ℕ suc (max n m))
le-max-r zero    m       = n<suc m
le-max-r (suc n) zero    = tt
le-max-r (suc n) (suc m) = le-max-r n m

-- x ≤ h and h ≤ i give x ≠ i + 1.
le-neq-suc : ∀ x h i → T (x <ℕ suc h) → T (h <ℕ suc i) → (x ==ℕ suc i) ≡ false
le-neq-suc x h i p q = <→≢ x (suc i) (le-trans x h i p q)

-- x ≤ h < i gives x ≠ i.
le-lt-neq : ∀ x h i → T (x <ℕ suc h) → (i ==ℕ h) ≡ false → (i <ℕ h) ≡ false → (x ==ℕ i) ≡ false
le-lt-neq zero    zero    zero    _ () _
le-lt-neq zero    h       (suc i) _ _  _ = refl
le-lt-neq zero    (suc h) zero    _ _  ()
le-lt-neq (suc x) zero    i       () _ _
le-lt-neq (suc x) (suc h) zero    _ _  _ = refl
le-lt-neq (suc x) (suc h) (suc i) p e  l = le-lt-neq x h i p e l

suc+-neq : ∀ h d → (suc (h + d) ==ℕ h) ≡ false
suc+-neq zero    d = refl
suc+-neq (suc h) d = suc+-neq h d

suc+-nlt : ∀ h d → (suc (h + d) <ℕ h) ≡ false
suc+-nlt zero    d = refl
suc+-nlt (suc h) d = suc+-nlt h d

------------------------------------------------------------------------
-- Generic list lemmas.

filterG-++ : ∀ {A : Set} (p : A → Bool) xs ys → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
filterG-++ p []       ys = refl
filterG-++ p (x ∷ xs) ys with p x
... | true  = cong (x ∷_) (filterG-++ p xs ys)
... | false = filterG-++ p xs ys

anyG-++ : ∀ {A : Set} (p : A → Bool) xs ys → any p (xs ++ ys) ≡ any p xs ∨ any p ys
anyG-++ p []       ys = refl
anyG-++ p (x ∷ xs) ys with p x
... | true  = refl
... | false = anyG-++ p xs ys

concatMap-++ : ∀ {A B : Set} (g : A → List B) xs ys → concatMap g (xs ++ ys) ≡ concatMap g xs ++ concatMap g ys
concatMap-++ g []       ys = refl
concatMap-++ g (x ∷ xs) ys = trans (cong (g x ++_) (concatMap-++ g xs ys)) (sym (++-assocL (g x) _ _))

concatMap-ext : ∀ {A B : Set} (g h : A → List B) xs → (∀ x → g x ≡ h x) → concatMap g xs ≡ concatMap h xs
concatMap-ext g h []       e = refl
concatMap-ext g h (x ∷ xs) e = cong₂ _++_ (e x) (concatMap-ext g h xs e)

concatMap-rng-ext : ∀ {B : Set} n (g h : Nat → List B) → (∀ v → T (v <ℕ n) → g v ≡ h v) →
                    concatMap g (rng n) ≡ concatMap h (rng n)
concatMap-rng-ext zero    g h e = refl
concatMap-rng-ext (suc n) g h e =
  trans (concatMap-++ g (rng n) (n ∷ []))
    (trans (cong₂ _++_ (concatMap-rng-ext n g h (λ v lt → e v (<-suc v n lt)))
                       (cong (_++ []) (e n (n<suc n))))
      (sym (concatMap-++ h (rng n) (n ∷ []))))

filter-concatMap : ∀ {A B : Set} (q : B → Bool) (g : A → List B) xs →
                   filter q (concatMap g xs) ≡ concatMap (λ x → filter q (g x)) xs
filter-concatMap q g []       = refl
filter-concatMap q g (x ∷ xs) = trans (filterG-++ q (g x) (concatMap g xs)) (cong (filter q (g x) ++_) (filter-concatMap q g xs))

any-concatMap : ∀ {A B : Set} (p : B → Bool) (g : A → List B) xs →
                any p (concatMap g xs) ≡ any (λ x → any p (g x)) xs
any-concatMap p g []       = refl
any-concatMap p g (x ∷ xs) = trans (anyG-++ p (g x) (concatMap g xs)) (cong (any p (g x) ∨_) (any-concatMap p g xs))

any-filter : ∀ {A : Set} (p q : A → Bool) xs → any p (filter q xs) ≡ any (λ x → q x ∧ p x) xs
any-filter p q []       = refl
any-filter p q (x ∷ xs) with q x
... | true  = cong (p x ∨_) (any-filter p q xs)
... | false = any-filter p q xs

filter-ext : ∀ {A : Set} (p q : A → Bool) xs → (∀ x → p x ≡ q x) → filter p xs ≡ filter q xs
filter-ext p q []       e = refl
filter-ext p q (x ∷ xs) e rewrite e x with q x
... | true  = cong (x ∷_) (filter-ext p q xs e)
... | false = filter-ext p q xs e

filter-cm : ∀ {A : Set} (q : A → Bool) xs → filter q xs ≡ concatMap (λ x → if q x then x ∷ [] else []) xs
filter-cm q []       = refl
filter-cm q (x ∷ xs) with q x
... | true  = cong (x ∷_) (filter-cm q xs)
... | false = filter-cm q xs

map-filter-cm : ∀ {A B : Set} (f : A → B) (q : A → Bool) xs →
                map f (filter q xs) ≡ concatMap (λ x → if q x then f x ∷ [] else []) xs
map-filter-cm f q []       = refl
map-filter-cm f q (x ∷ xs) with q x
... | true  = cong (f x ∷_) (map-filter-cm f q xs)
... | false = map-filter-cm f q xs

any-AllL-false : ∀ {A : Set} (p : A → Bool) xs → AllL (λ x → p x ≡ false) xs → any p xs ≡ false
any-AllL-false p []       []ᴬ       = refl
any-AllL-false p (x ∷ xs) (e ∷ᴬ es) rewrite e = any-AllL-false p xs es

filter-AllL-false : ∀ {A : Set} (p : A → Bool) xs → AllL (λ x → p x ≡ false) xs → filter p xs ≡ []
filter-AllL-false p []       []ᴬ       = refl
filter-AllL-false p (x ∷ xs) (e ∷ᴬ es) rewrite e = filter-AllL-false p xs es

AllL-∈ : ∀ {A : Set} {P : A → Set} {a} xs → AllL P xs → a ∈ xs → P a
AllL-∈ (x ∷ xs) (p ∷ᴬ ps') hd∈     = p
AllL-∈ (x ∷ xs) (p ∷ᴬ ps') (tl∈ m) = AllL-∈ xs ps' m

AllL-mid : ∀ {A : Set} {P : A → Set} xs {c ys} → AllL P (xs ++ c ∷ ys) → P c
AllL-mid []       (p ∷ᴬ _)  = p
AllL-mid (x ∷ xs) (_ ∷ᴬ ps') = AllL-mid xs ps'

-- The bound of a list by its maximum.
maxL-bound : ∀ {A : Set} (f : A → Nat) xs → AllL (λ c → T (f c <ℕ suc (maxL (map f xs)))) xs
maxL-bound f []       = []ᴬ
maxL-bound f (x ∷ xs) =
  le-max-l (f x) (maxL (map f xs)) ∷ᴬ
  AllL-map xs (λ c lt → le-trans (f c) (maxL (map f xs)) _ lt (le-max-r (f x) (maxL (map f xs)))) (maxL-bound f xs)

lengthN-snoc : ∀ xs x → lengthN (xs ++ x ∷ []) ≡ suc (lengthN xs)
lengthN-snoc []       x = refl
lengthN-snoc (y ∷ xs) x = cong suc (lengthN-snoc xs x)

------------------------------------------------------------------------
-- Hom indices: drop1 (upto n) lists 1 … n − 1.

seq : Nat → Nat → List Nat
seq j zero    = []
seq j (suc m) = j ∷ seq (suc j) m

seq-snoc : ∀ j m → seq j (suc m) ≡ seq j m ++ ((j + m) ∷ [])
seq-snoc j zero    = cong (λ z → z ∷ []) (sym (+-zero j))
seq-snoc j (suc m) = cong (j ∷_) (trans (seq-snoc (suc j) m) (cong (λ z → seq (suc j) m ++ (z ∷ [])) (sym (+-suc j m))))

upto-seq : ∀ n → upto n ≡ seq 0 (suc n)
upto-seq zero    = refl
upto-seq (suc n) = trans (cong (_++ (suc n ∷ [])) (upto-seq n)) (sym (seq-snoc 0 (suc n)))

dropLast-snoc : ∀ xs x → dropLast (xs ++ x ∷ []) ≡ xs
dropLast-snoc []            x = refl
dropLast-snoc (y ∷ [])      x = refl
dropLast-snoc (y ∷ z ∷ zs)  x = cong (y ∷_) (dropLast-snoc (z ∷ zs) x)

drop1-upto : ∀ r → drop1 (upto (suc r)) ≡ seq 1 r
drop1-upto r =
  trans (cong drop1 (upto-seq (suc r)))
    (trans (cong dropLast (seq-snoc 1 r)) (dropLast-snoc (seq 1 r) _))

------------------------------------------------------------------------
-- Positions in a list of objects.

private
  nz : ∀ (mb : Maybe Nat) → (mb >>= λ k → just (suc k)) ≡ just 0 → ⊥
  nz nothing  ()
  nz (just _) ()

  peel : ∀ (mb : Maybe Nat) m → (mb >>= λ k → just (suc k)) ≡ just (suc m) → mb ≡ just m
  peel nothing  m ()
  peel (just k) m refl = refl

  inj-tail : ∀ b c xs m → posOf b xs ≡ just m → posOf c xs ≡ just m → b ≡ c
  inj-tail-suc : ∀ b c xs m → (posOf b xs >>= λ k → just (suc k)) ≡ just m →
                 (posOf c xs >>= λ k → just (suc k)) ≡ just m → b ≡ c

  inj-tail b c []       m () _
  inj-tail b c (x ∷ xs) m eb ec with b ==ℕ x in hb | c ==ℕ x in hc
  ... | true  | true  = trans (==→≡ b x hb) (sym (==→≡ c x hc))
  ... | true  | false = ⊥-elim (nz (posOf c xs) (trans ec (sym eb)))
  ... | false | true  = ⊥-elim (nz (posOf b xs) (trans eb (sym ec)))
  ... | false | false = inj-tail-suc b c xs m eb ec

  inj-tail-suc b c xs zero    eb ec = ⊥-elim (nz (posOf b xs) eb)
  inj-tail-suc b c xs (suc m) eb ec = inj-tail b c xs m (peel _ m eb) (peel _ m ec)

posOf-inj : ∀ b c xs {m} → posOf b xs ≡ just m → posOf c xs ≡ just m → b ≡ c
posOf-inj b c xs {m} = inj-tail b c xs m

posOf-complete : ∀ b xs → b ∈ xs → Σ Nat λ m → posOf b xs ≡ just m
posOf-complete b (.b ∷ xs) hd∈ rewrite ==-true b = 0 , refl
posOf-complete b (x ∷ xs) (tl∈ mem) with b ==ℕ x
... | true  = 0 , refl
... | false with posOf-complete b xs mem
...   | m , e rewrite e = suc m , refl

posOf-at : ∀ c pre rest → AllL (λ x → (c ==ℕ x) ≡ false) pre → posOf c (pre ++ c ∷ rest) ≡ just (lengthN pre)
posOf-at c []        rest []ᴬ       rewrite ==-true c = refl
posOf-at c (x ∷ pre) rest (h ∷ᴬ hs) rewrite h | posOf-at c pre rest hs = refl

------------------------------------------------------------------------
-- The objects of a pasting context are strictly increasing.

Inc : List Nat → Set
Inc []       = ⊤
Inc (x ∷ xs) = AllL (λ y → T (x <ℕ y)) xs × Inc xs

Inc-snoc : ∀ xs n → Inc xs → AllL (λ y → T (y <ℕ n)) xs → Inc (xs ++ n ∷ [])
Inc-snoc []       n _          _          = []ᴬ , tt
Inc-snoc (x ∷ xs) n (ax , ix) (lt ∷ᴬ ls) = AllL-++ xs (n ∷ []) ax (lt ∷ᴬ []ᴬ) , Inc-snoc xs n ix ls

Inc-rng : ∀ n → Inc (rng n)
Inc-rng zero    = tt
Inc-rng (suc n) = Inc-snoc (rng n) n (Inc-rng n) (rng-lt n)

Inc-filter : ∀ (q : Nat → Bool) xs → Inc xs → Inc (filter q xs)
Inc-filter q []       _          = tt
Inc-filter q (x ∷ xs) (ax , ix) with q x
... | true  = filter-AllL q xs ax , Inc-filter q xs ix
... | false = Inc-filter q xs ix

Inc-objL : ∀ Γ → Inc (objL Γ)
Inc-objL Γ = Inc-filter _ (rng (len Γ)) (Inc-rng (len Γ))

Inc-before : ∀ pre c rest → Inc (pre ++ c ∷ rest) → AllL (λ x → T (x <ℕ c)) pre
Inc-before []        c rest _          = []ᴬ
Inc-before (x ∷ pre) c rest (ax , ix) = AllL-mid pre ax ∷ᴬ Inc-before pre c rest ix

∈-pairs-snd : ∀ {e} y zs → e ∈ pairs (y ∷ zs) → snd e ∈ zs
∈-pairs-snd y []       ()
∈-pairs-snd y (z ∷ zs) hd∈     = hd∈
∈-pairs-snd y (z ∷ zs) (tl∈ m) = tl∈ (∈-pairs-snd z zs m)

∈-pairs-snd' : ∀ {e} xs → e ∈ pairs xs → snd e ∈ xs
∈-pairs-snd' []       ()
∈-pairs-snd' (x ∷ xs) m = tl∈ (∈-pairs-snd x xs m)

-- In a strictly increasing list, a pair is determined by its target.
pairs-unique : ∀ xs {a a' c} → Inc xs → (a , c) ∈ pairs xs → (a' , c) ∈ pairs xs → a ≡ a'
pairs-unique (x ∷ y ∷ zs) _                hd∈      hd∈      = refl
pairs-unique (x ∷ y ∷ zs) (_ , (ay , _))   hd∈      (tl∈ m)  = ⊥-elim (lt-irr y (AllL-∈ zs ay (∈-pairs-snd y zs m)))
pairs-unique (x ∷ y ∷ zs) (_ , (ay , _))   (tl∈ m)  hd∈      = ⊥-elim (lt-irr y (AllL-∈ zs ay (∈-pairs-snd y zs m)))
pairs-unique (x ∷ y ∷ zs) (_ , iy)         (tl∈ m)  (tl∈ m') = pairs-unique (y ∷ zs) iy m m'

pairs-mid : ∀ pre o o' rest → (o , o') ∈ pairs (pre ++ o ∷ o' ∷ rest)
pairs-mid []            o o' rest = hd∈
pairs-mid (x ∷ [])      o o' rest = tl∈ hd∈
pairs-mid (x ∷ y ∷ pre) o o' rest = tl∈ (pairs-mid (y ∷ pre) o o' rest)

-- o' sits at position |pre| + 1.
pos-o' : ∀ pre o o' rest → Inc (pre ++ o ∷ o' ∷ rest) → posOf o' (pre ++ o ∷ o' ∷ rest) ≡ just (suc (lengthN pre))
pos-o' pre o o' rest inc =
  trans (cong (posOf o') assoc)
    (trans (posOf-at o' (pre ++ o ∷ []) rest
              (AllL-map (pre ++ o ∷ []) (λ x lt → ≡-sym-false x o' (<→≢ x o' lt))
                (Inc-before (pre ++ o ∷ []) o' rest (subst Inc assoc inc))))
           (cong just (lengthN-snoc pre o)))
  where
  assoc : pre ++ o ∷ o' ∷ rest ≡ (pre ++ o ∷ []) ++ o' ∷ rest
  assoc = sym (++-assocL pre (o ∷ []) (o' ∷ rest))

private
  true≢false : true ≡ false → ⊥
  true≢false ()

-- The k-th hom (k = |pre| + 1) is the one between o and o'.
hk : ∀ pre o o' rest → Inc (pre ++ o ∷ o' ∷ rest) → ∀ a b m →
     (a , b) ∈ pairs (pre ++ o ∷ o' ∷ rest) → posOf b (pre ++ o ∷ o' ∷ rest) ≡ just m →
     (m ==ℕ suc (lengthN pre)) ≡ ((a ==ℕ o) ∧ (b ==ℕ o'))
hk pre o o' rest inc a b m mem pb with b ==ℕ o' in hb
... | true with ==→≡ b o' hb
...   | refl rewrite pairs-unique _ inc mem (pairs-mid pre o o' rest)
                   | just-inj (trans (sym pb) (pos-o' pre o o' rest inc)) | ==-true o | ==-true (lengthN pre) = refl
hk pre o o' rest inc a b m mem pb | false with m ==ℕ suc (lengthN pre) in hm
... | true  = ⊥-elim (true≢false (trans (sym (==-true b))
                (trans (cong (b ==ℕ_) (posOf-inj b o' (pre ++ o ∷ o' ∷ rest) pb
                          (trans (pos-o' pre o o' rest inc) (cong just (sym (==→≡ m _ hm)))))) hb)))
... | false = sym (∧-false (a ==ℕ o))

------------------------------------------------------------------------
-- Entries are lookups.

entries-rng : ∀ {B : Set} (G : Nat → Maybe Ty → List B) Γ →
              concatMap (λ e → G (fst e) (just (snd e))) (entries Γ) ≡ concatMap (λ v → G v (lookup Γ v)) (rng (len Γ))
entries-rng G ε       = refl
entries-rng G (Γ ▸ A) =
  trans (concatMap-++ (λ e → G (fst e) (just (snd e))) (entries Γ) ((len Γ , A) ∷ []))
    (trans (cong₂ _++_
              (trans (entries-rng G Γ)
                     (concatMap-rng-ext (len Γ) (λ v → G v (lookup Γ v)) (λ v → G v (lookup (Γ ▸ A) v))
                        (λ v lt → cong (G v) (sym (lookup-old Γ A v lt)))))
              (cong (λ m → G (len Γ) m ++ []) (sym (lookup-new Γ A))))
      (sym (concatMap-++ (λ v → G v (lookup (Γ ▸ A) v)) (rng (len Γ)) (len Γ ∷ []))))

isStar-M : ∀ A → isStar A ≡ isStarM (just A)
isStar-M ⋆           = refl
isStar-M (arr _ _ _) = refl

objs-objL : ∀ Γ → objs Γ ≡ objL Γ
objs-objL Γ =
  map fst (filter (λ e → isStar (snd e)) (entries Γ))
    ≡⟨ map-filter-cm fst (λ e → isStar (snd e)) (entries Γ) ⟩
  concatMap (λ e → if isStar (snd e) then fst e ∷ [] else []) (entries Γ)
    ≡⟨ concatMap-ext _ (λ e → G (fst e) (just (snd e))) (entries Γ)
         (λ e → cong (λ b → if b then fst e ∷ [] else []) (isStar-M (snd e))) ⟩
  concatMap (λ e → G (fst e) (just (snd e))) (entries Γ)
    ≡⟨ entries-rng G Γ ⟩
  concatMap (λ v → G v (lookup Γ v)) (rng (len Γ))
    ≡⟨ sym (filter-cm (λ v → isStarM (lookup Γ v)) (rng (len Γ))) ⟩
  objL Γ ∎≡
  where
  G : Nat → Maybe Ty → List Nat
  G v m = if isStarM m then v ∷ [] else []

------------------------------------------------------------------------
-- The El of a variable.

elsM : List Nat → Nat → Maybe Ty → List El
elsM os v nothing  = []
elsM os v (just A) = mkEl os (v , A)

cells-rng : ∀ Γ → cells Γ ≡ concatMap (λ v → elsM (objL Γ) v (lookup Γ v)) (rng (len Γ))
cells-rng Γ =
  trans (entries-rng (elsM (objs Γ)) Γ)
        (cong (λ os → concatMap (λ v → elsM os v (lookup Γ v)) (rng (len Γ))) (objs-objL Γ))

endsHom : List Nat → Maybe (Tm × Tm) → Maybe Nat
endsHom os (just (_ , var b)) = posOf b os
endsHom os _                  = nothing

homOf : List Nat → Ty → Maybe Nat
homOf os A = endsHom os (endsTy A)

elsOf : Nat → Ty → Maybe Nat → List El
elsOf v A nothing  = []
elsOf v A (just k) = el v k (dim A ∸ 1) (fst (elBdry A)) (snd (elBdry A)) ∷ []

mkEl-eq : ∀ os v A → mkEl os (v , A) ≡ elsOf v A (homOf os A)
mkEl-eq os v A with endsTy A
... | nothing = refl
... | just (_ , var b) with posOf b os
...   | nothing = refl
...   | just k  = refl
mkEl-eq os v A | just (_ , coh _ _ _) = refl
mkEl-eq os v A | just (_ , cst ())

homOf-ends : ∀ os A {a b} → endsV A ≡ just (a , b) → homOf os A ≡ posOf b os
homOf-ends os ⋆                    ()
homOf-ends os (arr ⋆ s t)          e with endsV-arr⋆ s t e
... | refl , refl = refl
homOf-ends os (arr (arr B s' t') s t) e = homOf-ends os (arr B s' t') e

-- In a pasting context every cell of positive dimension has object ends.
ends-just : ∀ {Γ} → PsInv Γ → ∀ v B s t → lookup Γ v ≡ just (arr B s t) →
            Σ (Nat × Nat) λ e → endsV (arr B s t) ≡ just e
ends-just inv v ⋆ s t lv with inv v _ lv
... | (i , j , refl , refl , _ , _) = (i , j) , refl
ends-just inv v (arr B s' t') s t lv with inv v _ lv
... | (i , j , refl , refl , li , _) = ends-just inv i B s' t' li

------------------------------------------------------------------------
-- One hom of a pasting context.

private
  filter-one : ∀ (e : El) (Q H' : El → Bool) →
               map lvl (filter Q (filter H' (e ∷ []))) ≡ (if H' e ∧ Q e then lvl e ∷ [] else [])
  filter-one e Q H' with H' e
  ... | false = refl
  ... | true with Q e
  ...   | true  = refl
  ...   | false = refl

  bool-sel : ∀ M D X Y P → P ≡ M → (T M → T D → X ≡ Y) → M ∧ (D ∧ not X) ≡ (P ∧ D) ∧ not Y
  bool-sel M D X Y P refl h with M | D
  ... | false | _     = refl
  ... | true  | false = refl
  ... | true  | true  = cong not (h tt tt)

  L1 : ∀ (Q : El → Bool) (q : Nat → Bool) (g : Nat → List El) n →
       (∀ v → T (v <ℕ n) → map lvl (filter Q (g v)) ≡ (if q v then v ∷ [] else [])) →
       map lvl (filter Q (concatMap g (rng n))) ≡ filter q (rng n)
  L1 Q q g zero    h = refl
  L1 Q q g (suc n) h =
    map lvl (filter Q (concatMap g (rng n ++ n ∷ [])))
      ≡⟨ cong (λ L → map lvl (filter Q L)) (concatMap-++ g (rng n) (n ∷ [])) ⟩
    map lvl (filter Q (concatMap g (rng n) ++ (g n ++ [])))
      ≡⟨ cong (map lvl) (filterG-++ Q (concatMap g (rng n)) (g n ++ [])) ⟩
    map lvl (filter Q (concatMap g (rng n)) ++ filter Q (g n ++ []))
      ≡⟨ map-++ lvl (filter Q (concatMap g (rng n))) (filter Q (g n ++ [])) ⟩
    map lvl (filter Q (concatMap g (rng n))) ++ map lvl (filter Q (g n ++ []))
      ≡⟨ cong₂ _++_ (L1 Q q g n (λ v lt → h v (<-suc v n lt)))
                    (trans (cong (λ L → map lvl (filter Q L)) (++-[]L (g n))) (trans (h n (n<suc n)) last)) ⟩
    filter q (rng n) ++ filter q (n ∷ [])
      ≡⟨ sym (filter-++ q (rng n) (n ∷ [])) ⟩
    filter q (rng n ++ n ∷ []) ∎≡
    where
    last : (if q n then n ∷ [] else []) ≡ filter q (n ∷ [])
    last with q n
    ... | true  = refl
    ... | false = refl

module OneHom {Γ : Ctx} (P : Γ ⊢ps) (pre : List Nat) (o o' : Nat) (rest : List Nat)
              (eqo : objL Γ ≡ pre ++ o ∷ o' ∷ rest) where

  invΓ : PsInv Γ
  invΓ = psInv P

  os : List Nat
  os = objL Γ

  n : Nat
  n = len Γ

  k : Nat
  k = suc (lengthN pre)

  g : Nat → List El
  g v = elsM os v (lookup Γ v)

  Hq : El → Bool
  Hq c = hom c ==ℕ k

  h : Hom
  h = homAt Γ k

  H : List El
  H = hcs h

  H-rng : H ≡ filter Hq (concatMap g (rng n))
  H-rng = cong (filter Hq) (cells-rng Γ)

  -- Every cell of positive dimension: its ends, its hom and its El.
  record CellInfo (v : Nat) (A : Ty) : Set where
    field
      a b m  : Nat
      ev     : endsV A ≡ just (a , b)
      mem    : (a , b) ∈ pairs os
      hom-eq : homOf os A ≡ just m

  cell-info : ∀ v B s t → lookup Γ v ≡ just (arr B s t) → CellInfo v (arr B s t)
  cell-info v B s t lv with ends-just invΓ v B s t lv
  ... | (a , b) , ev = record
    { a = a ; b = b ; m = fst pm ; ev = ev ; mem = mem
    ; hom-eq = trans (homOf-ends os (arr B s t) ev) (snd pm) }
    where
    mem = hom-ends P v (trans (cong endsL lv) ev)
    pm = posOf-complete b os (∈-pairs-snd' os mem)

  hom-sel : ∀ v A (ci : CellInfo v A) → (CellInfo.m ci ==ℕ k) ≡ homM (o , o') (endsV A)
  hom-sel v A ci rewrite CellInfo.ev ci =
    hk pre o o' rest (subst Inc eqo (Inc-objL Γ)) (CellInfo.a ci) (CellInfo.b ci) (CellInfo.m ci)
       (subst (λ xs → _ ∈ pairs xs) eqo (CellInfo.mem ci)) (subst (λ xs → posOf _ xs ≡ _) eqo (pos ci))
    where
    pos : ∀ ci → posOf (CellInfo.b ci) os ≡ just (CellInfo.m ci)
    pos ci = trans (sym (homOf-ends os A (CellInfo.ev ci))) (CellInfo.hom-eq ci)

  -- A cell v of hom k is hit (as a source, sg = true, or target) by a
  -- cell w of the context exactly when w's El hits v's in hom k.
  eq-hit : ∀ i sg v Av (k' d' s'' t'' : Nat) → lookup Γ v ≡ just Av → homOf os Av ≡ just k →
           i ≡ dim Av ∸ 1 →
           any (hitsP i sg (el v k' d' s'' t'')) H ≡ any (hitB Γ sg v) (rng n)
  eq-hit i sg v Av k' d' s'' t'' lv hv iv =
    any (hitsP i sg c) H
      ≡⟨ cong (any (hitsP i sg c)) H-rng ⟩
    any (hitsP i sg c) (filter Hq (concatMap g (rng n)))
      ≡⟨ any-filter (hitsP i sg c) Hq (concatMap g (rng n)) ⟩
    any (λ x → Hq x ∧ hitsP i sg c x) (concatMap g (rng n))
      ≡⟨ any-concatMap (λ x → Hq x ∧ hitsP i sg c x) g (rng n) ⟩
    any (λ w → any (λ x → Hq x ∧ hitsP i sg c x) (g w)) (rng n)
      ≡⟨ any-rng-ext n _ _ (λ w _ → pt w) ⟩
    any (hitB Γ sg v) (rng n) ∎≡
    where
    c = el v k' d' s'' t''

    -- the El of an arr-⋆ cell has hom dimension 0
    flatC : ∀ w s t → any (λ x → Hq x ∧ hitsP i sg c x) (mkEl os (w , arr ⋆ s t)) ≡ false
    flatC w s t rewrite mkEl-eq os w (arr ⋆ s t) with homOf os (arr ⋆ s t)
    ... | nothing = refl
    ... | just m' rewrite ∧-false (m' ==ℕ k) = refl

    -- face is the source (sg = true) or target of w, of type arr B s' t'.
    deepC : ∀ w B s' t' s0 t0 → lookup Γ s0 ≡ just (arr B s' t') → lookup Γ t0 ≡ just (arr B s' t') →
           any (λ x → Hq x ∧ hitsP i sg c x) (mkEl os (w , arr (arr B s' t') (var s0) (var t0)))
           ≡ ((if sg then s0 else t0) ==ℕ v)
    deepC w B s' t' s0 t0 ls lt rewrite mkEl-eq os w (arr (arr B s' t') (var s0) (var t0)) = go sg
      where
      Aw = arr (arr B s' t') (var s0) (var t0)
      hit-case : ∀ f → lookup Γ f ≡ just (arr B s' t') → (f ==ℕ v) ≡ true →
                 homOf os Aw ≡ just k × (i ≡ dim B)
      hit-case f lf e with ==→≡ f v e
      ... | refl with trans (sym lv) lf
      ...   | refl = hv , iv
      go : ∀ sg' → any (λ x → Hq x ∧ hitsP i sg' c x) (elsOf w Aw (homOf os Aw)) ≡ ((if sg' then s0 else t0) ==ℕ v)
      go true with s0 ==ℕ v in e
      ... | true with hit-case s0 ls e
      ...   | hw , refl rewrite hw | ==-true k | ==-true (dim B) | e = refl
      go true | false with homOf os Aw
      ... | nothing = refl
      ... | just m' rewrite e | ∧-false (suc (dim B) ==ℕ suc i) | ∧-false (m' ==ℕ k) = refl
      go false with t0 ==ℕ v in e
      ... | true with hit-case t0 lt e
      ...   | hw , refl rewrite hw | ==-true k | ==-true (dim B) | e = refl
      go false | false with homOf os Aw
      ... | nothing = refl
      ... | just m' rewrite e | ∧-false (suc (dim B) ==ℕ suc i) | ∧-false (m' ==ℕ k) = refl

    pt : ∀ w → any (λ x → Hq x ∧ hitsP i sg c x) (g w) ≡ hitB Γ sg v w
    pt w with lookup Γ w in lw
    ... | nothing = refl
    ... | just ⋆  = refl
    ... | just (arr ⋆ s t) = flatC w s t
    ... | just (arr (arr B s' t') s t) with invΓ w _ lw
    ...   | (s0 , t0 , refl , refl , ls , lt) = deepC w B s' t' s0 t0 ls lt

  -- Qc: the predicate of `piece` below the top dimension.
  Qc : Nat → Bool → El → Bool
  Qc i sg c = (hdim c ==ℕ i) ∧ not (any (hitsP i sg c) H)

  -- The table below the top dimension is the lookup-based one.
  core-eq : ∀ i sg → map lvl (filter (Qc i sg) H) ≡ filter (sel Γ (o , o') sg i) (rng n)
  core-eq i sg =
    trans (cong (λ L → map lvl (filter (Qc i sg) L)) (trans H-rng (filter-concatMap Hq g (rng n))))
          (L1 (Qc i sg) (sel Γ (o , o') sg i) (λ v → filter Hq (g v)) n pt)
    where
    pt : ∀ v → T (v <ℕ n) →
         map lvl (filter (Qc i sg) (filter Hq (g v))) ≡
         (if (homM (o , o') (endsL (lookup Γ v)) ∧ (hdimTy (lookup Γ v) ==ℕ i)) ∧ not (any (hitB Γ sg v) (rng n))
          then v ∷ [] else [])
    pt v _ with lookup Γ v in lv
    ... | nothing = refl
    ... | just ⋆  = refl
    ... | just (arr B s t) =
      let A  = arr B s t
          ci = cell-info v B s t lv
          m  = CellInfo.m ci
      in
      trans (cong (λ L → map lvl (filter (Qc i sg) (filter Hq L))) (trans (mkEl-eq os v A) (cong (elsOf v A) (CellInfo.hom-eq ci))))
        (trans (filter-one (el v m (dim A ∸ 1) (fst (elBdry A)) (snd (elBdry A))) (Qc i sg) Hq)
          (cong (λ x → if x then v ∷ [] else [])
            (bool-sel (m ==ℕ k) (dim A ∸ 1 ==ℕ i) _ _ (homM (o , o') (endsV A)) (sym (hom-sel v A ci))
              (λ mk di → eq-hit i sg v A m (dim A ∸ 1) (fst (elBdry A)) (snd (elBdry A)) lv
                 (trans (CellInfo.hom-eq ci) (cong just (==ℕ-sound m k mk)))
                 (sym (==ℕ-sound _ i di))))))

  -- The hom dimension bounds every cell of the hom.
  bound : AllL (λ c → T (hdim c <ℕ suc (hd h))) H
  bound = maxL-bound hdim H

  -- At or above the top dimension nothing is hit.
  no-hit : ∀ i sg c → T (hd h <ℕ suc i) → any (hitsP i sg c) H ≡ false
  no-hit i sg c le = any-AllL-false (hitsP i sg c) H
    (AllL-map H (λ w lt → cong (λ x → x ∧ (if sg then (src w ==ℕ lvl c) else (tgt w ==ℕ lvl c)))
                                (le-neq-suc (hdim w) (hd h) i lt le)) bound)

  piece-Tb : ∀ i sg → piece h i sg ≡ filter (sel Γ (o , o') sg i) (rng n)
  piece-Tb i sg with i ==ℕ hd h in e1
  ... | true  =
    trans (cong (map lvl) (filter-ext _ (Qc i sg) H
            (λ c → sym (trans (cong (λ x → (hdim c ==ℕ i) ∧ not x)
                                    (no-hit i sg c (subst (λ j → T (j <ℕ suc i)) (==→≡ i _ e1) (n<suc i))))
                              (∧-true _)))))
          (core-eq i sg)
  ... | false with i <ℕ hd h in e2
  ...   | true  = core-eq i sg
  ...   | false =
    trans (sym (cong (map lvl) (filter-AllL-false (Qc i sg) H
            (AllL-map H (λ c lt → cong (λ x → x ∧ not (any (hitsP i sg c) H)) (le-lt-neq (hdim c) (hd h) i lt e1 e2)) bound))))
          (core-eq i sg)

  Ph-Tb : ∀ b i → Ph h b i ≈ Tb Γ (o , o') b i
  Ph-Tb b i = ≡→≈ (cong (map sing) (piece-Tb i b))

  aboveH : ∀ b d → Ph h b (suc (hd h + d)) ≈ []
  aboveH b d = ≡→≈ (cong (map sing) (trans (cong (λ x → if x then X else Y) (suc+-neq (hd h) d))
                                          (cong (λ x → if x then Z else []) (suc+-nlt (hd h) d))))
    where
    i = suc (hd h + d)
    X = map lvl (filter (λ c → hdim c ==ℕ i) H)
    Z = map lvl (filter (λ c → (hdim c ==ℕ i) ∧ not (any (hitsP i b c) H)) H)
    Y = if i <ℕ hd h then Z else []

  hom-cell : TabCell Γ o o' (hd h) (Ph h)
  hom-cell = record
    { basis = λ b i → All-≈ (Tb Γ (o , o') b i) (Ph h b i) (≈-sym (Ph-Tb b i)) (Tb-basis Γ o o' b i)
    ; above = aboveH
    ; aug   = fst core'
    ; chain = snd core'
    }
    where
    core : Core Γ (o , o') (Tb Γ (o , o'))
    core = AllL-∈ (pairs os) (hom-cores P) (subst (λ xs → (o , o') ∈ pairs xs) (sym eqo) (pairs-mid pre o o' rest))
    core' : Core Γ (o , o') (Ph h)
    core' = Core-≈ Γ (o , o') (Tb Γ (o , o')) (Ph h) (λ b i → ≈-sym (Ph-Tb b i)) core

------------------------------------------------------------------------
-- All homs.

hc-go : ∀ {Γ} (P : Γ ⊢ps) pre o rest → objL Γ ≡ pre ++ o ∷ rest →
        HC Γ (o ∷ rest) (map (homAt Γ) (seq (suc (lengthN pre)) (lengthN rest)))
hc-go P pre o []          eq = tt
hc-go {Γ} P pre o (o' ∷ rest) eq =
  OneHom.hom-cell P pre o o' rest eq ,
  subst (λ j → HC Γ (o' ∷ rest) (map (homAt Γ) (seq j (lengthN rest))))
        (cong suc (lengthN-snoc pre o))
        (hc-go P (pre ++ o ∷ []) o' rest (trans eq (sym (++-assocL pre (o ∷ []) (o' ∷ rest)))))

hom-ne : ∀ {Γ} → Γ ⊢ps → NonEmpty (objL Γ)
hom-ne (ps d) = Inv.ne (inv-ps d)

private
  homs-objL : ∀ {Θ} (P : Θ ⊢ps) → HC Θ (objL Θ) (map (homAt Θ) (drop1 (upto (lengthN (objL Θ)))))
  homs-objL {Θ} P with objL Θ in eq
  ... | []       = ⊥-elim (subst NonEmpty eq (hom-ne P))
  ... | o ∷ rest =
    subst (λ js → HC Θ (o ∷ rest) (map (homAt Θ) js)) (sym (drop1-upto (lengthN rest)))
          (hc-go P [] o rest eq)

homCells : HomCells
homCells {Θ} P =
  subst (λ os → HC Θ os (homs Θ)) (sym (objs-objL Θ))
    (subst (λ L → HC Θ (objL Θ) (map (homAt Θ) (drop1 (upto (lengthN L))))) (sym (objs-objL Θ))
      (homs-objL P))

-- The first hypothesis of Strict.Soundness, now a theorem.
T-cell : TCell
T-cell = T-cell-from homCells

-- Strict-model soundness with its one remaining hypothesis.
module SoundnessB (B-supp : BSupp) = Soundness T-cell B-supp
