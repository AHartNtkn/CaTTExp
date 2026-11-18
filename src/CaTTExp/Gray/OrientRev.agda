------------------------------------------------------------------------
-- Alternating orientation gives the factor-reversed tensor
-- (notes/closed-structure.md D.3; notes/agda-gray-findings.md,
-- "The orientation family L_ε").
--
-- For ε = odd (reverse the odd hom-dimensions) and for ε = even, the
-- tables of L_ε are those of L for the tensor taken in the opposite
-- factor order, read back in the original coordinates:
--
--   x ∈ T_ε^sg_k(Θ₁,…,Θₙ)  ⟺  rev x ∈ T^sg_k(Θₙ,…,Θ₁)
--
-- (`alt-rev⇒`, `alt-rev⇐`, for every pasting diagram, every sign and
-- every k), so ⊗_ε = ⊗^rev on all tables.
--
-- Method: membership in a chain is a path (`Path`): a choice of a
-- dimension iⱼ and a cell cⱼ ∈ piece hⱼ iⱼ (sign) for each factor, with
-- Σ iⱼ = k and the sign of factor j equal to the start sign flipped by
-- the parity of i₁ + … + i_{j-1}. Reversing a path of ⊗_odd gives a
-- path of ⊗ whose signs are flipped by the parity of the suffix sums;
-- the two agree because i₁+…+i_{j-1} + (i_j + 1) + (k + 1) ≡
-- i_{j+1}+…+iₙ (mod 2).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.OrientRev (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Orient 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊

rev : ∀ {a} {A : Set a} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

evenO : Orient
evenO i = not (odd i)

------------------------------------------------------------------------
-- Lists and numbers.

private
  rev-snoc : ∀ {a} {A : Set a} (xs : List A) y → rev (xs ++ (y ∷ [])) ≡ y ∷ rev xs
  rev-snoc []       y = refl
  rev-snoc (x ∷ xs) y = cong (_++ (x ∷ [])) (rev-snoc xs y)

  rev-rev : ∀ {a} {A : Set a} (xs : List A) → rev (rev xs) ≡ xs
  rev-rev []       = refl
  rev-rev (x ∷ xs) = trans (rev-snoc (rev xs) x) (cong (x ∷_) (rev-rev xs))

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm zero    b = sym (+-zero b)
  +-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

  sum-snoc : ∀ is i → sumL (is ++ (i ∷ [])) ≡ sumL is + i
  sum-snoc []       i = +-zero i
  sum-snoc (j ∷ is) i = trans (cong (j +_) (sum-snoc is i)) (sym (+-assoc j (sumL is) i))

  sum-rev : ∀ is → sumL (rev is) ≡ sumL is
  sum-rev []       = refl
  sum-rev (i ∷ is) = trans (sum-snoc (rev is) i) (trans (cong (_+ i) (sum-rev is)) (+-comm (sumL is) i))

  odd-+ : ∀ m n → odd (m + n) ≡ flipIf (odd m) (odd n)
  odd-+ zero    n = refl
  odd-+ (suc m) n = trans (cong not (odd-+ m n)) (l (odd m) (odd n))
    where
    l : ∀ a b → not (flipIf a b) ≡ flipIf (not a) b
    l true  true  = refl
    l true  false = refl
    l false b     = refl

  -- i ≤ k as the chains test it.
  lt⇒ : ∀ i k → T (i <ℕ suc k) → i + (k ∸ i) ≡ k
  lt⇒ zero    k       _ = refl
  lt⇒ (suc i) (suc k) p = cong suc (lt⇒ i k p)

  lt⇐ : ∀ i n → T (i <ℕ suc (i + n))
  lt⇐ zero    n = tt
  lt⇐ (suc i) n = lt⇐ i n

  +∸ : ∀ i n → (i + n) ∸ i ≡ n
  +∸ zero    n = refl
  +∸ (suc i) n = +∸ i n

------------------------------------------------------------------------
-- Booleans: flipIf is exclusive or.

private
  ff : Bool → Bool → Bool
  ff = flipIf

  b1 : ∀ a b s → not (ff (ff a b) s) ≡ not (ff a (ff b s))
  b1 true  true  true  = refl
  b1 true  true  false = refl
  b1 true  false true  = refl
  b1 true  false false = refl
  b1 false true  s     = refl
  b1 false false s     = refl

  b2 : ∀ a b s → ff a (not (ff (ff a b) s)) ≡ ff (not b) s
  b2 true  true  true  = refl
  b2 true  true  false = refl
  b2 true  false true  = refl
  b2 true  false false = refl
  b2 false true  true  = refl
  b2 false true  false = refl
  b2 false false true  = refl
  b2 false false false = refl

  b3 : ∀ a b t → ff (ff a b) t ≡ ff b (ff a t)
  b3 true  true  true  = refl
  b3 true  true  false = refl
  b3 true  false t     = refl
  b3 false true  t     = refl
  b3 false false t     = refl

  b4 : ∀ a b s → ff a (not (ff (ff b a) s)) ≡ ff (not b) s
  b4 true  true  true  = refl
  b4 true  true  false = refl
  b4 true  false true  = refl
  b4 true  false false = refl
  b4 false true  true  = refl
  b4 false true  false = refl
  b4 false false true  = refl
  b4 false false false = refl

  b5 : ∀ a sg → not (ff a (ff (not a) sg)) ≡ sg
  b5 true  true  = refl
  b5 true  false = refl
  b5 false true  = refl
  b5 false false = refl

  flip-not : ∀ a sg → ff a (not sg) ≡ not (ff a sg)
  flip-not true  sg = refl
  flip-not false sg = refl

------------------------------------------------------------------------
-- Paths through a chain.

data Path (o : Orient) : Bool → List Hom → List Nat → Tuple → Set where
  nil  : ∀ {s} → Path o s [] [] []
  cons : ∀ {s h hs i is c x} → c ∈ᴺ pieceε o h i s → Path o (flipIf (odd i) s) hs is x →
         Path o s (h ∷ hs) (i ∷ is) (c ∷ x)

-- Paths of L itself.
Path₀ : Bool → List Hom → List Nat → Tuple → Set
Path₀ = Path (λ _ → false)

path⇒ : ∀ o hs s k {x} → x ∈L chainε o s k hs → Σ (List Nat) λ is → (sumL is ≡ k) × Path o s hs is x
path⇒ o []       s k m with any-if (k ==ℕ 0) m
... | p , here refl = [] , sym (==ℕ-sound k 0 p) , nil
path⇒ o (h ∷ hs) s k m
  rewrite cm≡ (λ i → prod1 (pieceε o h i s) (chainε o (flipIf (odd i) s) (k ∸ i) hs))
              (filter (λ i → i <ℕ suc k) (upto k))
  with any-witness (any-cm⁻ _ (filter (λ i → i <ℕ suc k) (upto k)) m)
... | i , mi , mx with filter⇒ (λ i → i <ℕ suc k) (upto k) mi
...   | _ , lt with prod1⇒ (pieceε o h i s) (chainε o (flipIf (odd i) s) (k ∸ i) hs) mx
...     | c , x , refl , mc , mx' with path⇒ o hs (flipIf (odd i) s) (k ∸ i) mx'
...       | is , e , p = i ∷ is , trans (cong (i +_) e) (lt⇒ i k lt) , cons mc p

path⇐ : ∀ o {s hs is x} → Path o s hs is x → x ∈L chainε o s (sumL is) hs
path⇐ o nil = here refl
path⇐ o {s} {h ∷ hs} {i ∷ is} {c ∷ x} (cons mc p)
  rewrite cm≡ (λ j → prod1 (pieceε o h j s) (chainε o (flipIf (odd j) s) ((i + sumL is) ∸ j) hs))
              (filter (λ j → j <ℕ suc (i + sumL is)) (upto (i + sumL is))) =
  any-cm⁺ _ (any-at (filter⇐ _ (upto (i + sumL is)) (upto⇐ i (i + sumL is) (lt⇐ i (sumL is))) (lt⇐ i (sumL is)))
                    (prod1⇐ (pieceε o h i s) _ mc
                       (subst (λ n → x ∈L chainε o (flipIf (odd i) s) n hs) (sym (+∸ i (sumL is))) (path⇐ o p))))

------------------------------------------------------------------------
-- Appending a factor at the end of a path of L.

private
  snoc⁺ : ∀ {t hs is x h i c} → Path₀ t hs is x → c ∈ᴺ piece h i (flipIf (odd (sumL is)) t) →
          Path₀ t (hs ++ (h ∷ [])) (is ++ (i ∷ [])) (x ++ (c ∷ []))
  snoc⁺ nil q = cons q nil
  snoc⁺ {t} {h = h} {i} (cons {i = i'} {is'} p f) q =
    cons p (snoc⁺ f (subst (λ b → _ ∈ᴺ piece h i b) (trans (cong (λ a → ff a t) (odd-+ i' (sumL is'))) (b3 (odd i') (odd (sumL is')) t)) q))

  snoc⁻ : ∀ hs {t h js y} → Path₀ t (hs ++ (h ∷ [])) js y →
          Σ (List Nat) λ is → Σ Nat λ i → Σ Tuple λ x → Σ Nat λ c →
          (js ≡ is ++ (i ∷ [])) × (y ≡ x ++ (c ∷ [])) × Path₀ t hs is x × c ∈ᴺ piece h i (flipIf (odd (sumL is)) t)
  snoc⁻ [] (cons {i = i} {c = c} q nil) = [] , i , [] , c , refl , refl , nil , q
  snoc⁻ (h' ∷ hs) {t} {h} (cons {i = i'} {c = c'} p f) with snoc⁻ hs f
  ... | is , i , x , c , refl , refl , f' , q =
    i' ∷ is , i , c' ∷ x , c , refl , refl , cons p f' ,
    subst (λ b → c ∈ᴺ piece h i b) (sym (trans (cong (λ a → ff a t) (odd-+ i' (sumL is))) (b3 (odd i') (odd (sumL is)) t))) q

------------------------------------------------------------------------
-- Reversing paths: ⊗_odd forwards is ⊗ backwards.

rev⇒ : ∀ {s hs is x} → Path odd s hs is x → Path₀ (not (flipIf (odd (sumL is)) s)) (rev hs) (rev is) (rev x)
rev⇒ nil = nil
rev⇒ {s} (cons {h = h} {i = i} {is} {c} p f) =
  snoc⁺ (subst (λ t → Path₀ t _ _ _) (sym (cong not (trans (cong (λ a → ff a s) (odd-+ i (sumL is))) (b3 (odd i) (odd (sumL is)) s)))) (rev⇒ f))
        (subst (λ b → c ∈ᴺ piece h i b) (sym e) p)
  where
  e : ff (odd (sumL (rev is))) (not (ff (odd (i + sumL is)) s)) ≡ ff (not (odd i)) s
  e rewrite sum-rev is | odd-+ i (sumL is) = b4 (odd (sumL is)) (odd i) s

rev⇐ : ∀ hs {s js y} → Path₀ (not (flipIf (odd (sumL js)) s)) (rev hs) js y → Path odd s hs (rev js) (rev y)
rev⇐ [] nil = nil
rev⇐ (h ∷ hs) {s} f with snoc⁻ (rev hs) f
... | is , i , x , c , refl , refl , f' , q
  rewrite rev-snoc is i | rev-snoc x c =
  cons (subst (λ b → c ∈ᴺ piece h i b) e₂ q)
       (rev⇐ hs (subst (λ t → Path₀ t (rev hs) is x) e₁ f'))
  where
  S = sumL is
  e₀ : odd (sumL (is ++ (i ∷ []))) ≡ ff (odd S) (odd i)
  e₀ = trans (cong odd (sum-snoc is i)) (odd-+ S i)
  e₁ : not (ff (odd (sumL (is ++ (i ∷ [])))) s) ≡ not (ff (odd S) (ff (odd i) s))
  e₁ rewrite e₀ = b1 (odd S) (odd i) s
  e₂ : ff (odd S) (not (ff (odd (sumL (is ++ (i ∷ [])))) s)) ≡ ff (not (odd i)) s
  e₂ rewrite e₀ = b2 (odd S) (odd i) s

------------------------------------------------------------------------
-- The theorem, for ε = odd.

alt-rev⇒ : ∀ sg k hs {x} → x ∈L chainTε odd sg k hs → rev x ∈L chainT sg k (rev hs)
alt-rev⇒ sg k hs m with path⇒ odd hs (flipIf (odd (suc k)) sg) k m
... | is , refl , p =
  subst (λ L → _ ∈L L) (chainε-false sg (sumL is) (rev hs))
    (subst (λ n → _ ∈L chainε (λ _ → false) sg n (rev hs)) (sum-rev is)
      (path⇐ (λ _ → false) (subst (λ t → Path₀ t _ _ _) (b5 (odd (sumL is)) sg) (rev⇒ p))))

alt-rev⇐ : ∀ sg k hs {x} → rev x ∈L chainT sg k (rev hs) → x ∈L chainTε odd sg k hs
alt-rev⇐ sg k hs {x} m
  with path⇒ (λ _ → false) (rev hs) sg k (subst (λ L → rev x ∈L L) (sym (chainε-false sg k (rev hs))) m)
... | js , refl , p =
  subst (λ y → y ∈L chainTε odd sg (sumL js) hs) (rev-rev x)
    (subst (λ n → rev (rev x) ∈L chainε odd (flipIf (odd (suc (sumL js))) sg) n hs) (sum-rev js)
      (path⇐ odd (rev⇐ hs (subst (λ t → Path₀ t (rev hs) js (rev x)) (sym (b5 (odd (sumL js)) sg)) p))))

------------------------------------------------------------------------
-- ε = even gives the same tables as ε = odd.

chainε-even : ∀ sg k hs → chainε evenO sg k hs ≡ chainε odd (not sg) k hs
chainε-even sg k []       = refl
chainε-even sg k (h ∷ hs) =
  cmc (λ i → cong₂ prod1 (cong (piece h i) (pe (odd i) sg))
                             (trans (chainε-even (flipIf (odd i) sg) (k ∸ i) hs)
                                    (cong (λ b → chainε odd b (k ∸ i) hs) (sym (flip-not (odd i) sg)))))
          (filter (λ i → i <ℕ suc k) (upto k))
  where
  pe : ∀ a sg → flipIf (not (not a)) sg ≡ flipIf (not a) (not sg)
  pe true  true  = refl
  pe true  false = refl
  pe false true  = refl
  pe false false = refl
  cmc : ∀ {A B : Set} {f g : A → List B} → (∀ x → f x ≡ g x) → ∀ xs → concatMap f xs ≡ concatMap g xs
  cmc e []       = refl
  cmc e (x ∷ xs) = cong₂ _++_ (e x) (cmc e xs)

chainTε-even : ∀ sg k hs → chainTε evenO sg k hs ≡ chainTε odd sg k hs
chainTε-even sg k hs =
  trans (chainε-even (flipIf (not (odd (suc k))) sg) k hs)
        (cong (λ b → chainε odd b k hs) (e (odd (suc k)) sg))
  where
  e : ∀ a sg → not (flipIf (not a) sg) ≡ flipIf a sg
  e true  sg = refl
  e false true  = refl
  e false false = refl

------------------------------------------------------------------------
-- Whole tables: L_odd's supports of T, ∂⁻T, ∂⁺T are L's supports for
-- the reversed factor order, read backwards.

RevSet : TSet → TSet → Set
RevSet S R = ∀ x → (x ∈L S → rev x ∈L R) × (rev x ∈L R → x ∈L S)

private
  map-rev : ∀ {A B : Set} (f : A → B) xs → map f (rev xs) ≡ rev (map f xs)
  map-rev f []       = refl
  map-rev f (x ∷ xs) = trans (map-++ (rev xs)) (cong (_++ (f x ∷ [])) (map-rev f xs))
    where
    map-++ : ∀ ys {zs} → map f (ys ++ zs) ≡ map f ys ++ map f zs
    map-++ []       = refl
    map-++ (y ∷ ys) = cong (f y ∷_) (map-++ ys)

  revset-++ : ∀ {S S' R R'} → RevSet S R → RevSet S' R' → RevSet (S ++ S') (R ++ R')
  revset-++ {S} {S'} {R} {R'} r r' x = to , from
    where
    to : x ∈L (S ++ S') → rev x ∈L (R ++ R')
    to m with any-++⁻ S m
    ... | inj₁ a = any-++l (fst (r x) a)
    ... | inj₂ b = any-++r R (fst (r' x) b)
    from : rev x ∈L (R ++ R') → x ∈L (S ++ S')
    from m with any-++⁻ R m
    ... | inj₁ a = any-++l (snd (r x) a)
    ... | inj₂ b = any-++r S (snd (r' x) b)

dimK-rev : ∀ hs → dimK (rev hs) ≡ dimK hs
dimK-rev hs = trans (cong sumL (map-rev hd hs)) (sum-rev (map hd hs))

chain-rev : ∀ sg k hs → RevSet (chainTε odd sg k hs) (chainT sg k (rev hs))
chain-rev sg k hs x = alt-rev⇒ sg k hs , alt-rev⇐ sg k hs

lower-rev : ∀ m hs → RevSet (lowerTε odd m hs) (lowerT m (rev hs))
lower-rev zero    hs x = (λ ()) , (λ ())
lower-rev (suc m) hs =
  revset-++ (lower-rev m hs) (revset-++ (chain-rev false m hs) (chain-rev true m hs))

full-rev : ∀ hs → RevSet (fullTε odd hs) (fullT (rev hs))
full-rev hs rewrite dimK-rev hs = revset-++ (lower-rev (dimK hs) hs) (chain-rev true (dimK hs) hs)

bdry-rev : ∀ sg hs → RevSet (bdryTε odd sg hs) (bdryT sg (rev hs))
bdry-rev sg hs rewrite dimK-rev hs = revset-++ (lower-rev (dimK hs ∸ 1) hs) (chain-rev sg (dimK hs ∸ 1) hs)

-- ε = even: the same, through chainTε-even.
chain-rev-even : ∀ sg k hs → RevSet (chainTε evenO sg k hs) (chainT sg k (rev hs))
chain-rev-even sg k hs rewrite chainTε-even sg k hs = chain-rev sg k hs
