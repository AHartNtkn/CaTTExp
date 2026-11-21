------------------------------------------------------------------------
-- The grid layer in the raw syntax of T (ledger S3c; E12 Link A–B).
--
-- CaTTExp.Uniform.Grid models the 4-cells of F_{V+S} on the suspended
-- grid Σ(Σ[m] ∨ Σ[n]) by raw paths of block crossings modulo the
-- enabled split laws. CaTTExp.Join.SepAlgebra has the raw syntax of the
-- theory T through dimension 4 (lax construction-or-impossibility
-- §7, (K30)), and CaTTExp.Join.SwitchLaws the switched laws as schemas
-- on that syntax. Until now nothing related the two. This module gives
-- the translation of grid paths into raw T-terms and proves that it
-- sends grid equality to T-equality.
--
-- The grid as a T-signature. The suspended grid has one hom. Its
-- 2-cells are u₀ … u_m (on the first span) and v₀ … v_n (on the
-- second), and its 3-cells are aᵢ : uᵢ ⇛ uᵢ₊₁ and bⱼ : vⱼ ⇛ vⱼ₊₁ (here
-- indexed from 0). There are no 1-cell whiskers and no 4-cells.
--   * A word of the grid at stage (i, j) is the chronological 3-path
--     whose a-letter is wr (aᵢ) vⱼ and whose b-letter is wl uᵢ (bⱼ)
--     (`lets`, `w3`).
--   * The block crossing ⟨k, p, q⟩ at word w is ctx P (ι F G) Q, with
--     P the first k letters, F the a-run and G the b-run as raw
--     composites of generators, and Q the rest (`trE`).
--   * A raw path is the composite of its edges' translations, ending in
--     an identity (`tr`). It is a pure-ι 4-term (`tr-inner`).
--
-- The relation on raw T-terms is ≈S: every equation of T except the
-- raw support equations (the theory P of (K45) and V drop them; they
-- would identify parallel paths with the same edge set), the switched
-- laws of SwitchLaws.Law in setting sw, closed under congruence.
--
-- Proved here:
--   flat-≈3      a normalizer for 3-terms built by ⨾, identities and
--                2-whiskering: two such terms with the same nonempty
--                list of whiskered letters are equal under ≈3;
--   cross-sound, cross-complete   the shape of a block crossing;
--   core-left, core-right   one left (right) split of a block crossing
--                is an instance of SwitchLaws.splitL (splitR), up to
--                T's structural equations;
--   link         sw ⊢ p ≈ q in Grid (both paths valid) implies
--                sw ⊢ tr start p ≈S tr start q.
--
-- The converse is CaTTExp.Uniform.GridSep (a model of T separating
-- grid paths), so on valid paths the two equalities agree. Raw ≈ is
-- untyped and has the identity normalisations (for example
-- ι (id3 u) G ≈ id4 F for every F), so ≈S identifies all identity
-- 4-terms; GridSep shows it still identifies no two grid paths that
-- Grid keeps apart.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; lengthL)
open import CaTTExp.Join.SwitchLaws using (Switches; IsTrue; tt′)
import CaTTExp.Join.SwitchLaws as SL
import CaTTExp.Join.SepAlgebra as Sep
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Arith
open import CaTTExp.Uniform.Grid

module CaTTExp.Uniform.GridLink where

open Switches

------------------------------------------------------------------------
-- The signature of a suspended grid.

data Empty : Set where

data G2 : Set where
  uu vv : Nat → G2

data G3 : Set where
  aa bb : Nat → G3

open Sep.Theory Empty G2 G3 Empty public
open SL.PartA Empty G2 G3 Empty public
  using (Law; splitL; splitR; Inner4; i-id; i-ι; i-·; i-ctx)

------------------------------------------------------------------------
-- List lemmas.

++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) → mapK f (xs ++ ys) ≡ mapK f xs ++ mapK f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

rep-+ : ∀ a b (x : Bool) → rep (a + b) x ≡ rep a x ++ rep b x
rep-+ zero    b x = refl
rep-+ (suc a) b x = cong (x ∷_) (rep-+ a b x)

take : Nat → Word → Word
take zero    w       = []
take (suc k) []      = []
take (suc k) (x ∷ w) = x ∷ take k w

drop : Nat → Word → Word
drop zero    w       = w
drop (suc k) []      = []
drop (suc k) (x ∷ w) = drop k w

take-len : ∀ (xs ys : Word) → take (lengthL xs) (xs ++ ys) ≡ xs
take-len []       ys = refl
take-len (x ∷ xs) ys = cong (x ∷_) (take-len xs ys)

drop-len : ∀ (xs ys : Word) → drop (lengthL xs) (xs ++ ys) ≡ ys
drop-len []       ys = refl
drop-len (x ∷ xs) ys = drop-len xs ys

len-++ : ∀ (xs ys : Word) → lengthL (xs ++ ys) ≡ lengthL xs + lengthL ys
len-++ []       ys = refl
len-++ (x ∷ xs) ys = cong suc (len-++ xs ys)

len-rep : ∀ n (x : Bool) → lengthL (rep n x) ≡ n
len-rep zero    x = refl
len-rep (suc n) x = cong suc (len-rep n x)

-- Occurrences of a's (true) and b's (false).
cntA cntB : Word → Nat
cntA []           = zero
cntA (true ∷ w)   = suc (cntA w)
cntA (false ∷ w)  = cntA w
cntB []           = zero
cntB (true ∷ w)   = cntB w
cntB (false ∷ w)  = suc (cntB w)

cntA-++ : ∀ xs ys → cntA (xs ++ ys) ≡ cntA xs + cntA ys
cntA-++ []           ys = refl
cntA-++ (true ∷ xs)  ys = cong suc (cntA-++ xs ys)
cntA-++ (false ∷ xs) ys = cntA-++ xs ys

cntB-++ : ∀ xs ys → cntB (xs ++ ys) ≡ cntB xs + cntB ys
cntB-++ []           ys = refl
cntB-++ (true ∷ xs)  ys = cntB-++ xs ys
cntB-++ (false ∷ xs) ys = cong suc (cntB-++ xs ys)

cntA-repA : ∀ n → cntA (rep n true) ≡ n
cntA-repA zero    = refl
cntA-repA (suc n) = cong suc (cntA-repA n)

cntB-repA : ∀ n → cntB (rep n true) ≡ zero
cntB-repA zero    = refl
cntB-repA (suc n) = cntB-repA n

cntA-repB : ∀ n → cntA (rep n false) ≡ zero
cntA-repB zero    = refl
cntA-repB (suc n) = cntA-repB n

cntB-repB : ∀ n → cntB (rep n false) ≡ n
cntB-repB zero    = refl
cntB-repB (suc n) = cong suc (cntB-repB n)

------------------------------------------------------------------------
-- The shape of a block crossing.

private
  strip-sound : ∀ k x w {w′} → strip k x w ≡ just w′ → w ≡ rep k x ++ w′
  strip-sound zero    x w       refl = refl
  strip-sound (suc k) x []      ()
  strip-sound (suc k) x (y ∷ w) e with x ≟B y
  ... | yes refl = cong (x ∷_) (strip-sound k x w e)
  ... | no _ with e
  ...   | ()

  strip-rep : ∀ k x w → strip k x (rep k x ++ w) ≡ just w
  strip-rep zero    x w = refl
  strip-rep (suc k) x w with x ≟B x
  ... | yes _ = strip-rep k x w
  ... | no ne = ⊥-elim (ne refl)

  just-inj : ∀ {A : Set} {a b : A} → _≡_ {A = Maybe A} (just a) (just b) → a ≡ b
  just-inj refl = refl

-- A block crossing ⟨k, p, q⟩ applies to w exactly when w is
-- pre ++ b^{p+1} ++ a^{q+1} ++ post with |pre| = k.
record Shape (k p q : Nat) (w w′ : Word) : Set where
  constructor shape
  field
    pre post : Word
    len   : lengthL pre ≡ k
    src   : w ≡ pre ++ (rep (suc p) false ++ (rep (suc q) true ++ post))
    dst   : w′ ≡ pre ++ (rep (suc q) true ++ (rep (suc p) false ++ post))

cross-sound : ∀ k p q w {w′} → cross ⟨ k , p , q ⟩ w ≡ just w′ → Shape k p q w w′
cross-sound (suc k) p q [] ()
cross-sound (suc k) p q (x ∷ w) e with cross ⟨ k , p , q ⟩ w in c
cross-sound (suc k) p q (x ∷ w) refl | just w₀ with cross-sound k p q w c
... | shape pre post l s d = shape (x ∷ pre) post (cong suc l) (cong (x ∷_) s) (cong (x ∷_) d)
cross-sound zero p q w e with strip (suc p) false w in e₁
... | just w₁ with strip (suc q) true w₁ in e₂
...   | just w₂ =
  shape [] w₂ refl
    (trans (strip-sound (suc p) false w e₁) (cong (rep (suc p) false ++_) (strip-sound (suc q) true w₁ e₂)))
    (sym (just-inj e))

cross-complete : ∀ pre p q post →
  cross ⟨ lengthL pre , p , q ⟩ (pre ++ (rep (suc p) false ++ (rep (suc q) true ++ post))) ≡
  just (pre ++ (rep (suc q) true ++ (rep (suc p) false ++ post)))
cross-complete (x ∷ pre) p q post rewrite cross-complete pre p q post = refl
cross-complete [] p q post
  rewrite strip-rep (suc p) false (rep (suc q) true ++ post)
        | strip-rep (suc q) true post = refl

------------------------------------------------------------------------
-- 3-terms: whiskered letters and a normalizer.

reify : T3 → List T3 → T3
reify x []       = x
reify x (y ∷ ys) = x ⨾ reify y ys

-- The list of whiskered letters of a 3-term.
flat : T3 → List T3
flat (F ⨾ G)   = flat F ++ flat G
flat (id3 _)   = []
flat (wr F z)  = mapK (λ x → wr x z) (flat F)
flat (wl z F)  = mapK (wl z) (flat F)
flat (gen3 g)  = gen3 g ∷ []
flat (χ a b)   = χ a b ∷ []
flat (w1L₃ f F) = w1L₃ f F ∷ []
flat (w1R₃ F g) = w1R₃ F g ∷ []

data Norm (F : T3) : Set where
  empty : (u : T2) → flat F ≡ [] → F ≈3 id3 u → Norm F
  cons  : ∀ x xs → flat F ≡ x ∷ xs → F ≈3 reify x xs → Norm F

private
  reify-++ : ∀ x xs y ys → (reify x xs ⨾ reify y ys) ≈3 reify x (xs ++ y ∷ ys)
  reify-++ x []        y ys = rfl3
  reify-++ x (x′ ∷ xs) y ys =
    trans3 (⨾-assoc x (reify x′ xs) (reify y ys)) (⨾-cong rfl3 (reify-++ x′ xs y ys))

  wr-reify : ∀ z x xs → wr (reify x xs) z ≈3 reify (wr x z) (mapK (λ y → wr y z) xs)
  wr-reify z x []       = rfl3
  wr-reify z x (y ∷ ys) = trans3 (wr-⨾ z x (reify y ys)) (⨾-cong rfl3 (wr-reify z y ys))

  wl-reify : ∀ z x xs → wl z (reify x xs) ≈3 reify (wl z x) (mapK (wl z) xs)
  wl-reify z x []       = rfl3
  wl-reify z x (y ∷ ys) = trans3 (wl-⨾ z x (reify y ys)) (⨾-cong rfl3 (wl-reify z y ys))

norm : ∀ F → Norm F
norm (gen3 g)   = cons (gen3 g) [] refl rfl3
norm (χ a b)    = cons (χ a b) [] refl rfl3
norm (w1L₃ f F) = cons (w1L₃ f F) [] refl rfl3
norm (w1R₃ F g) = cons (w1R₃ F g) [] refl rfl3
norm (id3 u)    = empty u refl rfl3
norm (wr F z) with norm F
... | empty u e d = empty (u ∘₂ z) (cong (mapK (λ x → wr x z)) e) (trans3 (wr-cong z d) (wr-id z u))
... | cons x xs e d =
  cons (wr x z) (mapK (λ y → wr y z) xs) (cong (mapK (λ x → wr x z)) e)
       (trans3 (wr-cong z d) (wr-reify z x xs))
norm (wl z F) with norm F
... | empty u e d = empty (z ∘₂ u) (cong (mapK (wl z)) e) (trans3 (wl-cong z d) (wl-id z u))
... | cons x xs e d =
  cons (wl z x) (mapK (wl z) xs) (cong (mapK (wl z)) e) (trans3 (wl-cong z d) (wl-reify z x xs))
norm (F ⨾ G) with norm F | norm G
... | empty u e d | empty u′ e′ d′ =
  empty u′ (cong₂ _++_ e e′) (trans3 (⨾-cong d d′) (⨾-idˡ u (id3 u′)))
... | empty u e d | cons y ys e′ d′ =
  cons y ys (cong₂ _++_ e e′) (trans3 (⨾-cong d d′) (⨾-idˡ u (reify y ys)))
... | cons x xs e d | empty u′ e′ d′ =
  cons x xs (trans (cong₂ _++_ e e′) (++-[] (x ∷ xs))) (trans3 (⨾-cong d d′) (⨾-idʳ u′ (reify x xs)))
... | cons x xs e d | cons y ys e′ d′ =
  cons x (xs ++ y ∷ ys) (cong₂ _++_ e e′) (trans3 (⨾-cong d d′) (reify-++ x xs y ys))

NonEmpty : List T3 → Set
NonEmpty xs = Σ T3 λ x → Σ (List T3) λ ys → xs ≡ x ∷ ys

-- Two 3-terms with the same nonempty list of letters are equal.
flat-≈3 : ∀ F G → flat F ≡ flat G → NonEmpty (flat G) → F ≈3 G
flat-≈3 F G e (x , xs , ne) with norm F | norm G
... | cons y ys eF dF | cons z zs eG dG =
  trans3 dF (trans3 (same (trans (sym eF) (trans e eG))) (sym3 dG))
  where
  same : ∀ {y ys z zs} → _≡_ {A = List T3} (y ∷ ys) (z ∷ zs) → reify y ys ≈3 reify z zs
  same refl = rfl3
... | empty _ eF _ | _ = ⊥-elim (nil≢cons (trans (sym eF) (trans e ne)))
  where nil≢cons : ∀ {x : T3} {xs} → [] ≡ x ∷ xs → ⊥
        nil≢cons ()
... | cons _ _ _ _ | empty _ eG _ = ⊥-elim (nil≢cons (trans (sym eG) ne))
  where nil≢cons : ∀ {x : T3} {xs} → [] ≡ x ∷ xs → ⊥
        nil≢cons ()

ne-++ʳ : ∀ xs {ys} → NonEmpty ys → NonEmpty (xs ++ ys)
ne-++ʳ []       n            = n
ne-++ʳ (x ∷ xs) _            = x , _ , refl

------------------------------------------------------------------------
-- Words and runs as 3-terms.

-- The letter at stage (i, j).
l3 : Nat → Nat → Bool → T3
l3 i j true  = wr (gen3 (aa i)) (gen2 (vv j))
l3 i j false = wl (gen2 (uu i)) (gen3 (bb j))

lets : Nat → Nat → Word → List T3
lets i j []          = []
lets i j (true ∷ w)  = l3 i j true  ∷ lets (suc i) j w
lets i j (false ∷ w) = l3 i j false ∷ lets i (suc j) w

reify₀ : T3 → List T3 → T3
reify₀ d []       = d
reify₀ d (x ∷ xs) = reify x xs

-- A word read from stage (i, j).
w3 : Nat → Nat → Word → T3
w3 i j w = reify₀ (id3 (gen2 (uu i) ∘₂ gen2 (vv j))) (lets i j w)

-- The generators aᵢ … aᵢ₊ₙ₋₁ and bⱼ … bⱼ₊ₙ₋₁.
asL bsL : Nat → Nat → List T3
asL i zero    = []
asL i (suc n) = gen3 (aa i) ∷ asL (suc i) n
bsL j zero    = []
bsL j (suc n) = gen3 (bb j) ∷ bsL (suc j) n

-- Runs of length k + 1, as raw composites.
aRun bRun : Nat → Nat → T3
aRun i k = reify (gen3 (aa i)) (asL (suc i) k)
bRun j k = reify (gen3 (bb j)) (bsL (suc j) k)

private
  flat-atoms : ∀ x xs → flat x ≡ x ∷ [] → (∀ {y} → y ∈L xs → flat y ≡ y ∷ []) →
               flat (reify x xs) ≡ x ∷ xs
  flat-atoms x []       fx h = fx
  flat-atoms x (y ∷ ys) fx h = cong₂ _++_ fx (flat-atoms y ys (h here) (λ m → h (there m)))

  gensA : ∀ i n {y} → y ∈L asL i n → flat y ≡ y ∷ []
  gensA i (suc n) here      = refl
  gensA i (suc n) (there m) = gensA (suc i) n m

  gensB : ∀ j n {y} → y ∈L bsL j n → flat y ≡ y ∷ []
  gensB j (suc n) here      = refl
  gensB j (suc n) (there m) = gensB (suc j) n m

  lets-atoms : ∀ i j w {y} → y ∈L lets i j w → flat y ≡ y ∷ []
  lets-atoms i j (true ∷ w)  here      = refl
  lets-atoms i j (false ∷ w) here      = refl
  lets-atoms i j (true ∷ w)  (there m) = lets-atoms (suc i) j w m
  lets-atoms i j (false ∷ w) (there m) = lets-atoms i (suc j) w m

flat-aRun : ∀ i k → flat (aRun i k) ≡ asL i (suc k)
flat-aRun i k = flat-atoms (gen3 (aa i)) (asL (suc i) k) refl (gensA (suc i) k)

flat-bRun : ∀ j k → flat (bRun j k) ≡ bsL j (suc k)
flat-bRun j k = flat-atoms (gen3 (bb j)) (bsL (suc j) k) refl (gensB (suc j) k)

flat-w3 : ∀ i j w → flat (w3 i j w) ≡ lets i j w
flat-w3 i j w with lets i j w in e
... | []     = refl
... | x ∷ xs = flat-atoms x xs (lets-atoms i j w (subst (x ∈L_) (sym e) here))
                 (λ m → lets-atoms i j w (subst (_ ∈L_) (sym e) (there m)))

asL-+ : ∀ i a b → asL i (a + b) ≡ asL i a ++ asL (i + a) b
asL-+ i zero    b = cong (λ n → asL n b) (sym (+-zero i))
asL-+ i (suc a) b = cong (gen3 (aa i) ∷_) (trans (asL-+ (suc i) a b) (cong (λ n → asL (suc i) a ++ asL n b) (sym (+-suc i a))))

bsL-+ : ∀ j a b → bsL j (a + b) ≡ bsL j a ++ bsL (j + a) b
bsL-+ j zero    b = cong (λ n → bsL n b) (sym (+-zero j))
bsL-+ j (suc a) b = cong (gen3 (bb j) ∷_) (trans (bsL-+ (suc j) a b) (cong (λ n → bsL (suc j) a ++ bsL n b) (sym (+-suc j a))))

lets-++ : ∀ i j xs ys → lets i j (xs ++ ys) ≡ lets i j xs ++ lets (i + cntA xs) (j + cntB xs) ys
lets-++ i j []           ys = cong₂ (λ a b → lets a b ys) (sym (+-zero i)) (sym (+-zero j))
lets-++ i j (true ∷ xs)  ys =
  cong (l3 i j true ∷_) (trans (lets-++ (suc i) j xs ys) (cong (λ a → lets (suc i) j xs ++ lets a (j + cntB xs) ys) (sym (+-suc i (cntA xs)))))
lets-++ i j (false ∷ xs) ys =
  cong (l3 i j false ∷_) (trans (lets-++ i (suc j) xs ys) (cong (λ b → lets i (suc j) xs ++ lets (i + cntA xs) b ys) (sym (+-suc j (cntB xs)))))

lets-repA : ∀ i j n → lets i j (rep n true) ≡ mapK (λ x → wr x (gen2 (vv j))) (asL i n)
lets-repA i j zero    = refl
lets-repA i j (suc n) = cong (l3 i j true ∷_) (lets-repA (suc i) j n)

lets-repB : ∀ i j n → lets i j (rep n false) ≡ mapK (wl (gen2 (uu i))) (bsL j n)
lets-repB i j zero    = refl
lets-repB i j (suc n) = cong (l3 i j false ∷_) (lets-repB i (suc j) n)

------------------------------------------------------------------------
-- The translation of edges and paths.

-- The crossing of b-run bRun j₀ p past a-run aRun i₀ q, whiskered by
-- the words before and after it.
trE′ : Word → Nat → Nat → Word → T4
trE′ pr p q po =
  ctx (w3 0 0 pr) (ι (aRun (cntA pr) q) (bRun (cntB pr) p))
      (w3 (cntA pr + suc q) (cntB pr + suc p) po)

trE : Edge → Word → T4
trE ⟨ k , p , q ⟩ w = trE′ (take k w) p q (drop (suc p + suc q) (drop k w))

private
  drop-rr : ∀ m n (x y : Bool) post → drop (m + n) (rep m x ++ (rep n y ++ post)) ≡ post
  drop-rr zero    zero    x y post = refl
  drop-rr zero    (suc n) x y post = drop-rr zero n x y post
  drop-rr (suc m) n       x y post = drop-rr m n x y post

-- trE on a word of the shape a crossing applies to.
trE-shape : ∀ pre p q post →
  trE ⟨ lengthL pre , p , q ⟩ (pre ++ (rep (suc p) false ++ (rep (suc q) true ++ post))) ≡
  trE′ pre p q post
trE-shape pre p q post =
  cong₂ (λ pr po → trE′ pr p q po) (take-len pre R)
        (trans (cong (drop (suc p + suc q)) (drop-len pre R)) (drop-rr (suc p) (suc q) false true post))
  where R = rep (suc p) false ++ (rep (suc q) true ++ post)

next : Edge → Word → Word
next e w with cross e w
... | just w′ = w′
... | nothing = w

next-≡ : ∀ e w {w′} → cross e w ≡ just w′ → next e w ≡ w′
next-≡ e w c rewrite c = refl

tr : Word → RawPath → T4
tr w []       = id4 (w3 0 0 w)
tr w (e ∷ es) = trE e w · tr (next e w) es

tr-inner : ∀ w es → Inner4 (tr w es)
tr-inner w []       = i-id _
tr-inner w (⟨ k , p , q ⟩ ∷ es) = i-· (i-ctx _ _ (i-ι _ _)) (tr-inner _ es)

------------------------------------------------------------------------
-- T's equations without the support equations, with the switched laws.

noSupp : ∀ {X Y} → X ≈ Y → Bool
noSupp (sym≈ d)          = noSupp d
noSupp (trans≈ d e)      = noSupp d ∧ noSupp e
noSupp (·-cong d e)      = noSupp d ∧ noSupp e
noSupp (ctx-cong _ d _)  = noSupp d
noSupp (wl4-cong _ d)    = noSupp d
noSupp (wr4-cong _ d)    = noSupp d
noSupp (w1L-cong _ d)    = noSupp d
noSupp (w1R-cong _ d)    = noSupp d
noSupp (supp _ _ _ _ _ _) = false
noSupp _                 = true

infix 3 _⊢_≈S_
data _⊢_≈S_ (sw : Switches) : T4 → T4 → Set where
  str    : ∀ {X Y} (d : X ≈ Y) → T (noSupp d) → sw ⊢ X ≈S Y
  law    : ∀ {X Y} → Law sw X Y → sw ⊢ X ≈S Y
  symS   : ∀ {X Y} → sw ⊢ X ≈S Y → sw ⊢ Y ≈S X
  transS : ∀ {X Y Z} → sw ⊢ X ≈S Y → sw ⊢ Y ≈S Z → sw ⊢ X ≈S Z
  ·-c    : ∀ {X X′ Y Y′} → sw ⊢ X ≈S X′ → sw ⊢ Y ≈S Y′ → sw ⊢ X · Y ≈S X′ · Y′
  ctx-c  : ∀ {p p′ X X′ q q′} → p ≈3 p′ → sw ⊢ X ≈S X′ → q ≈3 q′ →
           sw ⊢ ctx p X q ≈S ctx p′ X′ q′

rflS : ∀ {sw X} → sw ⊢ X ≈S X
rflS = str rfl tt

------------------------------------------------------------------------
-- One split of a block crossing is an instance of a switched law.

subst₂ : ∀ {A B : Set} (R : A → B → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → R x y → R x′ y′
subst₂ R refl refl z = z

private
  isTrue : ∀ {b} → T b → IsTrue b
  isTrue {true} _ = tt′

  -- 3-equations through the normalizer.
  by-flat : ∀ F G → flat F ≡ flat G → NonEmpty (flat G) → F ≈3 G
  by-flat = flat-≈3

  -- ctx p (X · Y) q splits, and nested contexts merge.
  ctx-split : ∀ {sw} P X q₁ Y p₂ Q →
              sw ⊢ ctx P (ctx (id3 id2) X q₁ · ctx p₂ Y (id3 id2)) Q ≈S
                   ctx (P ⨾ id3 id2) X (q₁ ⨾ Q) · ctx (P ⨾ p₂) Y (id3 id2 ⨾ Q)
  ctx-split P X q₁ Y p₂ Q =
    transS (str (ctx-· P _ _ Q) tt)
      (·-c (str (ctx-ctx P (id3 id2) X q₁ Q) tt) (str (ctx-ctx P p₂ Y (id3 id2) Q) tt))

  ctx-split′ : ∀ {sw} P p₁ X Y q₂ Q →
               sw ⊢ ctx P (ctx p₁ X (id3 id2) · ctx (id3 id2) Y q₂) Q ≈S
                    ctx (P ⨾ p₁) X (id3 id2 ⨾ Q) · ctx (P ⨾ id3 id2) Y (q₂ ⨾ Q)
  ctx-split′ P p₁ X Y q₂ Q =
    transS (str (ctx-· P _ _ Q) tt)
      (·-c (str (ctx-ctx P p₁ X (id3 id2) Q) tt) (str (ctx-ctx P (id3 id2) Y q₂ Q) tt))

-- The left split: w = pre ++ b^{p+1} ++ a^{a+1} ++ a^{b+1} ++ post.
core-left : ∀ {sw} → T (icc sw) → ∀ pre p a b post →
  let w  = pre ++ (rep (suc p) false ++ (rep (suc (a + suc b)) true ++ post))
      w₁ = pre ++ (rep (suc a) true ++ (rep (suc p) false ++ (rep (suc b) true ++ post)))
      k  = lengthL pre
  in sw ⊢ trE ⟨ k , p , a + suc b ⟩ w ≈S
          trE ⟨ k , p , a ⟩ w · trE ⟨ k + suc a , p , b ⟩ w₁
core-left {sw} on pre p a b post =
  subst₂ (λ X Y → sw ⊢ X ≈S Y) (sym lhs-≡) (sym rhs-≡) main
  where
  k  = lengthL pre
  i₀ = cntA pre
  j₀ = cntB pre
  A₁ = rep (suc a) true
  A₂ = rep (suc b) true
  Bs = rep (suc p) false
  P  = w3 0 0 pre
  G  = bRun j₀ p
  F  = aRun i₀ a
  F′ = aRun (i₀ + suc a) b
  FF = aRun i₀ (a + suc b)
  v  = gen2 (vv j₀)
  v′ = gen2 (vv (j₀ + suc p))
  Q  = w3 (i₀ + suc (a + suc b)) (j₀ + suc p) post
  Q₁ = w3 (i₀ + suc a) (j₀ + suc p) (A₂ ++ post)
  P₂ = w3 0 0 (pre ++ A₁)
  Q₂ = w3 ((i₀ + suc a) + suc b) (j₀ + suc p) post

  arith : i₀ + suc (a + suc b) ≡ (i₀ + suc a) + suc b
  arith = sym (+-assoc i₀ (suc a) (suc b))

  -- The translations, computed.
  lhs-≡ : trE ⟨ k , p , a + suc b ⟩ (pre ++ (Bs ++ (rep (suc (a + suc b)) true ++ post))) ≡
          ctx P (ι FF G) Q
  lhs-≡ = trE-shape pre p (a + suc b) post

  eqW : rep (suc (a + suc b)) true ++ post ≡ A₁ ++ (A₂ ++ post)
  eqW = trans (cong (_++ post) (rep-+ (suc a) (suc b) true)) (++-assoc A₁ A₂ post)

  pre₂ = pre ++ A₁
  lenpre₂ : lengthL pre₂ ≡ k + suc a
  lenpre₂ = trans (len-++ pre A₁) (cong (k +_) (len-rep (suc a) true))
  cA : cntA pre₂ ≡ i₀ + suc a
  cA = trans (cntA-++ pre A₁) (cong (i₀ +_) (cntA-repA (suc a)))
  cB : cntB pre₂ ≡ j₀
  cB = trans (cntB-++ pre A₁) (trans (cong (j₀ +_) (cntB-repA (suc a))) (+-zero j₀))

  rhs-≡ : trE ⟨ k , p , a ⟩ (pre ++ (Bs ++ (rep (suc (a + suc b)) true ++ post))) ·
          trE ⟨ k + suc a , p , b ⟩ (pre ++ (A₁ ++ (Bs ++ (A₂ ++ post)))) ≡
          ctx P (ι F G) Q₁ · ctx P₂ (ι F′ G) Q₂
  rhs-≡ = cong₂ _·_ e₁ e₂
    where
    e₁ = trans (cong (λ ws → trE ⟨ k , p , a ⟩ (pre ++ (Bs ++ ws))) eqW) (trE-shape pre p a (A₂ ++ post))
    e₂ = trans (cong₂ (λ n ws → trE ⟨ n , p , b ⟩ ws) (sym lenpre₂) (sym (++-assoc pre A₁ (Bs ++ (A₂ ++ post)))))
           (trans (trE-shape pre₂ p b post)
             (cong₂ (λ i j → ctx P₂ (ι (aRun i b) (bRun j p)) (w3 (i + suc b) (j + suc p) post)) cA cB))

  -- The 3-equations.
  eFF : FF ≈3 (F ⨾ F′)
  eFF = by-flat FF (F ⨾ F′)
          (trans (flat-aRun i₀ (a + suc b))
            (trans (asL-+ i₀ (suc a) (suc b))
              (sym (cong₂ _++_ (flat-aRun i₀ a) (flat-aRun (i₀ + suc a) b)))))
          (_ , _ , cong₂ _++_ (flat-aRun i₀ a) (flat-aRun (i₀ + suc a) b))

  eP : (P ⨾ id3 id2) ≈3 P
  eP = ⨾-idʳ id2 P

  eQ₁ : (wr F′ v′ ⨾ Q) ≈3 Q₁
  eQ₁ = by-flat (wr F′ v′ ⨾ Q) Q₁
          (trans (cong₂ _++_ (cong (mapK (λ x → wr x v′)) (flat-aRun (i₀ + suc a) b))
                             (trans (flat-w3 _ _ post) (cong (λ n → lets n (j₀ + suc p) post) arith)))
            (sym (trans (flat-w3 _ _ (A₂ ++ post))
                   (trans (lets-++ (i₀ + suc a) (j₀ + suc p) A₂ post)
                     (cong₂ _++_ (lets-repA (i₀ + suc a) (j₀ + suc p) (suc b))
                       (cong₂ (λ x y → lets x y post) (cong ((i₀ + suc a) +_) (cntA-repA (suc b)))
                                                      (trans (cong ((j₀ + suc p) +_) (cntB-repA (suc b))) (+-zero _))))))))
          (subst NonEmpty (sym (flat-w3 _ _ (A₂ ++ post))) (_ , _ , refl))

  eP₂ : (P ⨾ wr F v) ≈3 P₂
  eP₂ = by-flat (P ⨾ wr F v) P₂
          (trans (cong₂ _++_ (flat-w3 0 0 pre) (cong (mapK (λ x → wr x v)) (flat-aRun i₀ a)))
            (sym (trans (flat-w3 0 0 (pre ++ A₁))
                   (trans (lets-++ 0 0 pre A₁) (cong (lets 0 0 pre ++_) (lets-repA i₀ j₀ (suc a)))))))
          (subst NonEmpty (sym (trans (flat-w3 0 0 (pre ++ A₁))
                   (trans (lets-++ 0 0 pre A₁) (cong (lets 0 0 pre ++_) (lets-repA i₀ j₀ (suc a))))))
                 (ne-++ʳ (lets 0 0 pre) (_ , _ , refl)))

  eQ₂ : (id3 id2 ⨾ Q) ≈3 Q₂
  eQ₂ = trans3 (⨾-idˡ id2 Q) (subst (λ n → Q ≈3 w3 n (j₀ + suc p) post) arith rfl3)

  main : sw ⊢ ctx P (ι FF G) Q ≈S ctx P (ι F G) Q₁ · ctx P₂ (ι F′ G) Q₂
  main =
    transS (ctx-c rfl3 (str (ι-cong eFF rfl3) tt) rfl3)
      (transS (ctx-c rfl3 (law (splitL (isTrue on) F F′ G v v′ id2 id2)) rfl3)
        (transS (ctx-split P (ι F G) (wr F′ v′) (ι F′ G) (wr F v) Q)
          (·-c (ctx-c eP rflS eQ₁) (ctx-c eP₂ rflS eQ₂))))

-- The right split: w = pre ++ b^{a+1} ++ b^{b+1} ++ a^{q+1} ++ post.
-- The crossing of the second b-piece comes first.
core-right : ∀ {sw} → T (rsp sw) → ∀ pre a b q post →
  let w  = pre ++ (rep (suc (a + suc b)) false ++ (rep (suc q) true ++ post))
      w₁ = pre ++ (rep (suc a) false ++ (rep (suc q) true ++ (rep (suc b) false ++ post)))
      k  = lengthL pre
  in sw ⊢ trE ⟨ k , a + suc b , q ⟩ w ≈S
          trE ⟨ k + suc a , b , q ⟩ w · trE ⟨ k , a , q ⟩ w₁
core-right {sw} on pre a b q post =
  subst₂ (λ X Y → sw ⊢ X ≈S Y) (sym lhs-≡) (sym rhs-≡) main
  where
  k  = lengthL pre
  i₀ = cntA pre
  j₀ = cntB pre
  B₁ = rep (suc a) false
  B₂ = rep (suc b) false
  As = rep (suc q) true
  P  = w3 0 0 pre
  F  = aRun i₀ q
  G  = bRun j₀ a
  G′ = bRun (j₀ + suc a) b
  GG = bRun j₀ (a + suc b)
  u  = gen2 (uu i₀)
  u′ = gen2 (uu (i₀ + suc q))
  Q  = w3 (i₀ + suc q) (j₀ + suc (a + suc b)) post
  pre₂ = pre ++ B₁
  P₁ = w3 0 0 pre₂
  Q₁ = w3 (i₀ + suc q) ((j₀ + suc a) + suc b) post
  Q₂ = w3 (i₀ + suc q) (j₀ + suc a) (B₂ ++ post)

  arith : j₀ + suc (a + suc b) ≡ (j₀ + suc a) + suc b
  arith = sym (+-assoc j₀ (suc a) (suc b))

  eqW : ∀ tl → rep (suc (a + suc b)) false ++ tl ≡ B₁ ++ (B₂ ++ tl)
  eqW tl = trans (cong (_++ tl) (rep-+ (suc a) (suc b) false)) (++-assoc B₁ B₂ tl)

  lenpre₂ : lengthL pre₂ ≡ k + suc a
  lenpre₂ = trans (len-++ pre B₁) (cong (k +_) (len-rep (suc a) false))
  cA : cntA pre₂ ≡ i₀
  cA = trans (cntA-++ pre B₁) (trans (cong (i₀ +_) (cntA-repB (suc a))) (+-zero i₀))
  cB : cntB pre₂ ≡ j₀ + suc a
  cB = trans (cntB-++ pre B₁) (cong (j₀ +_) (cntB-repB (suc a)))

  lhs-≡ : trE ⟨ k , a + suc b , q ⟩ (pre ++ (rep (suc (a + suc b)) false ++ (As ++ post))) ≡
          ctx P (ι F GG) Q
  lhs-≡ = trE-shape pre (a + suc b) q post

  rhs-≡ : trE ⟨ k + suc a , b , q ⟩ (pre ++ (rep (suc (a + suc b)) false ++ (As ++ post))) ·
          trE ⟨ k , a , q ⟩ (pre ++ (B₁ ++ (As ++ (B₂ ++ post)))) ≡
          ctx P₁ (ι F G′) Q₁ · ctx P (ι F G) Q₂
  rhs-≡ = cong₂ _·_ e₁ e₂
    where
    e₁ = trans (cong₂ (λ n ws → trE ⟨ n , b , q ⟩ ws) (sym lenpre₂)
                 (trans (cong (pre ++_) (eqW (As ++ post))) (sym (++-assoc pre B₁ (B₂ ++ (As ++ post))))))
           (trans (trE-shape pre₂ b q post)
             (cong₂ (λ i j → ctx P₁ (ι (aRun i q) (bRun j b)) (w3 (i + suc q) (j + suc b) post)) cA cB))
    e₂ = trE-shape pre a q (B₂ ++ post)

  eGG : GG ≈3 (G ⨾ G′)
  eGG = by-flat GG (G ⨾ G′)
          (trans (flat-bRun j₀ (a + suc b))
            (trans (bsL-+ j₀ (suc a) (suc b))
              (sym (cong₂ _++_ (flat-bRun j₀ a) (flat-bRun (j₀ + suc a) b)))))
          (_ , _ , cong₂ _++_ (flat-bRun j₀ a) (flat-bRun (j₀ + suc a) b))

  lets-pre₂ : lets 0 0 pre₂ ≡ lets 0 0 pre ++ mapK (wl u) (bsL j₀ (suc a))
  lets-pre₂ = trans (lets-++ 0 0 pre B₁) (cong (lets 0 0 pre ++_) (lets-repB i₀ j₀ (suc a)))

  eP₁ : (P ⨾ wl u G) ≈3 P₁
  eP₁ = by-flat (P ⨾ wl u G) P₁
          (trans (cong₂ _++_ (flat-w3 0 0 pre) (cong (mapK (wl u)) (flat-bRun j₀ a)))
            (sym (trans (flat-w3 0 0 pre₂) lets-pre₂)))
          (subst NonEmpty (sym (trans (flat-w3 0 0 pre₂) lets-pre₂))
                 (ne-++ʳ (lets 0 0 pre) (_ , _ , refl)))

  eQ₁ : (id3 id2 ⨾ Q) ≈3 Q₁
  eQ₁ = trans3 (⨾-idˡ id2 Q) (subst (λ n → Q ≈3 w3 (i₀ + suc q) n post) arith rfl3)

  eP : (P ⨾ id3 id2) ≈3 P
  eP = ⨾-idʳ id2 P

  lets-Q₂ : lets (i₀ + suc q) (j₀ + suc a) (B₂ ++ post) ≡
            mapK (wl u′) (bsL (j₀ + suc a) (suc b)) ++ lets (i₀ + suc q) (j₀ + suc (a + suc b)) post
  lets-Q₂ = trans (lets-++ (i₀ + suc q) (j₀ + suc a) B₂ post)
              (cong₂ _++_ (lets-repB (i₀ + suc q) (j₀ + suc a) (suc b))
                (cong₂ (λ x y → lets x y post)
                  (trans (cong ((i₀ + suc q) +_) (cntA-repB (suc b))) (+-zero _))
                  (trans (cong ((j₀ + suc a) +_) (cntB-repB (suc b))) (sym arith))))

  eQ₂ : (wl u′ G′ ⨾ Q) ≈3 Q₂
  eQ₂ = by-flat (wl u′ G′ ⨾ Q) Q₂
          (trans (cong₂ _++_ (cong (mapK (wl u′)) (flat-bRun (j₀ + suc a) b)) (flat-w3 _ _ post))
            (sym (trans (flat-w3 _ _ (B₂ ++ post)) lets-Q₂)))
          (subst NonEmpty (sym (flat-w3 _ _ (B₂ ++ post))) (_ , _ , refl))

  main : sw ⊢ ctx P (ι F GG) Q ≈S ctx P₁ (ι F G′) Q₁ · ctx P (ι F G) Q₂
  main =
    transS (ctx-c rfl3 (str (ι-cong rfl3 eGG) tt) rfl3)
      (transS (ctx-c rfl3 (law (splitR (isTrue on) F G G′ u u′ id2 id2)) rfl3)
        (transS (ctx-split′ P (wl u G) (ι F G′) (ι F G) (wl u′ G′) Q)
          (·-c (ctx-c eP₁ rflS eQ₁) (ctx-c eP rflS eQ₂))))

------------------------------------------------------------------------
-- One split step inside a path.

private
  run-cons : ∀ x w L {t} → run w (x ∷ L) ≡ just t →
             Σ Word λ w′ → (cross x w ≡ just w′) × (run w′ L ≡ just t)
  run-cons x w L h with cross x w in c
  ... | just w′ = w′ , refl , h

  whenE : ∀ {A : Set} b (xs : List A) {x} → x ∈L when b xs → T b × (x ∈L xs)
  whenE true  xs m = tt , m

-- A left split at the head of the path.
base-left : ∀ {sw} → T (icc sw) → ∀ pre p a b post rest →
  let w = pre ++ (rep (suc p) false ++ (rep (suc (a + suc b)) true ++ post))
      k = lengthL pre
  in sw ⊢ tr w (⟨ k , p , a + suc b ⟩ ∷ rest) ≈S tr w (⟨ k , p , a ⟩ ∷ ⟨ k + suc a , p , b ⟩ ∷ rest)
base-left {sw} on pre p a b post rest =
  subst₂ (λ X Y → sw ⊢ X ≈S Y) (sym lhs) (sym rhs) chain
  where
  k  = lengthL pre
  Bs = rep (suc p) false
  A₁ = rep (suc a) true
  A₂ = rep (suc b) true
  w  = pre ++ (Bs ++ (rep (suc (a + suc b)) true ++ post))
  w₁ = pre ++ (A₁ ++ (Bs ++ (A₂ ++ post)))
  w′ = pre ++ (rep (suc (a + suc b)) true ++ (Bs ++ post))
  pre₂ = pre ++ A₁
  e  = ⟨ k , p , a + suc b ⟩
  e₁ = ⟨ k , p , a ⟩
  e₂ = ⟨ k + suc a , p , b ⟩

  eqW : ∀ tl → rep (suc (a + suc b)) true ++ tl ≡ A₁ ++ (A₂ ++ tl)
  eqW tl = trans (cong (_++ tl) (rep-+ (suc a) (suc b) true)) (++-assoc A₁ A₂ tl)
  lenpre₂ : lengthL pre₂ ≡ k + suc a
  lenpre₂ = trans (len-++ pre A₁) (cong (k +_) (len-rep (suc a) true))

  n0 : next e w ≡ w′
  n0 = next-≡ e w (cross-complete pre p (a + suc b) post)
  n1 : next e₁ w ≡ w₁
  n1 = next-≡ e₁ w (subst (λ ws → cross e₁ (pre ++ (Bs ++ ws)) ≡ just w₁) (sym (eqW post))
                          (cross-complete pre p a (A₂ ++ post)))
  c2 : cross e₂ w₁ ≡ just w′
  c2 = subst₂ (λ n ws → cross ⟨ n , p , b ⟩ ws ≡ just w′) lenpre₂ (++-assoc pre A₁ (Bs ++ (A₂ ++ post)))
         (trans (cross-complete pre₂ p b post)
           (cong just (trans (++-assoc pre A₁ (A₂ ++ (Bs ++ post))) (cong (pre ++_) (sym (eqW (Bs ++ post)))))))
  lhs : tr w (e ∷ rest) ≡ trE e w · tr w′ rest
  lhs = cong (λ v → trE e w · tr v rest) n0
  rhs : tr w (e₁ ∷ e₂ ∷ rest) ≡ trE e₁ w · (trE e₂ w₁ · tr w′ rest)
  rhs = cong₂ (λ v v′ → trE e₁ w · (trE e₂ v · tr v′ rest)) n1 (trans (cong (next e₂) n1) (next-≡ e₂ w₁ c2))
  chain : sw ⊢ trE e w · tr w′ rest ≈S trE e₁ w · (trE e₂ w₁ · tr w′ rest)
  chain = transS (·-c (core-left on pre p a b post) rflS) (str (·-assoc _ _ _) tt)

-- A right split at the head of the path.
base-right : ∀ {sw} → T (rsp sw) → ∀ pre a b q post rest →
  let w = pre ++ (rep (suc (a + suc b)) false ++ (rep (suc q) true ++ post))
      k = lengthL pre
  in sw ⊢ tr w (⟨ k , a + suc b , q ⟩ ∷ rest) ≈S tr w (⟨ k + suc a , b , q ⟩ ∷ ⟨ k , a , q ⟩ ∷ rest)
base-right {sw} on pre a b q post rest =
  subst₂ (λ X Y → sw ⊢ X ≈S Y) (sym lhs) (sym rhs) chain
  where
  k  = lengthL pre
  B₁ = rep (suc a) false
  B₂ = rep (suc b) false
  As = rep (suc q) true
  w  = pre ++ (rep (suc (a + suc b)) false ++ (As ++ post))
  w₁ = pre ++ (B₁ ++ (As ++ (B₂ ++ post)))
  w′ = pre ++ (As ++ (rep (suc (a + suc b)) false ++ post))
  pre₂ = pre ++ B₁
  e  = ⟨ k , a + suc b , q ⟩
  e₁ = ⟨ k + suc a , b , q ⟩
  e₂ = ⟨ k , a , q ⟩

  eqW : ∀ tl → rep (suc (a + suc b)) false ++ tl ≡ B₁ ++ (B₂ ++ tl)
  eqW tl = trans (cong (_++ tl) (rep-+ (suc a) (suc b) false)) (++-assoc B₁ B₂ tl)
  lenpre₂ : lengthL pre₂ ≡ k + suc a
  lenpre₂ = trans (len-++ pre B₁) (cong (k +_) (len-rep (suc a) false))

  n0 : next e w ≡ w′
  n0 = next-≡ e w (cross-complete pre (a + suc b) q post)
  c1 : cross e₁ w ≡ just w₁
  c1 = subst₂ (λ n ws → cross ⟨ n , b , q ⟩ ws ≡ just w₁) lenpre₂
         (trans (++-assoc pre B₁ (B₂ ++ (As ++ post))) (cong (pre ++_) (sym (eqW (As ++ post)))))
         (trans (cross-complete pre₂ b q post) (cong just (++-assoc pre B₁ (As ++ (B₂ ++ post)))))
  c2 : cross e₂ w₁ ≡ just w′
  c2 = trans (cross-complete pre a q (B₂ ++ post))
             (cong (λ ws → just (pre ++ (As ++ ws))) (sym (eqW post)))
  lhs : tr w (e ∷ rest) ≡ trE e w · tr w′ rest
  lhs = cong (λ v → trE e w · tr v rest) n0
  rhs : tr w (e₁ ∷ e₂ ∷ rest) ≡ trE e₁ w · (trE e₂ w₁ · tr w′ rest)
  rhs = cong₂ (λ v v′ → trE e₁ w · (trE e₂ v · tr v′ rest)) (next-≡ e₁ w c1)
          (trans (cong (next e₂) (next-≡ e₁ w c1)) (next-≡ e₂ w₁ c2))
  chain : sw ⊢ trE e w · tr w′ rest ≈S trE e₁ w · (trE e₂ w₁ · tr w′ rest)
  chain = transS (·-c (core-right on pre a b q post) rflS) (str (·-assoc _ _ _) tt)

-- Any split at the head of a path whose first edge applies.
base : ∀ {sw} pre p q post′ rest {r} → r ∈L splits sw ⟨ lengthL pre , p , q ⟩ →
  sw ⊢ tr (pre ++ (rep (suc p) false ++ (rep (suc q) true ++ post′))) (⟨ lengthL pre , p , q ⟩ ∷ rest) ≈S
       tr (pre ++ (rep (suc p) false ++ (rep (suc q) true ++ post′))) (r ++ rest)
base {sw} pre p q post′ rest m with ∈-++⁻ (when (icc sw) (leftS ⟨ lengthL pre , p , q ⟩)) m
... | inj₁ m′ with whenE (icc sw) _ m′
...   | on , m″ with ∈-map⁻ _ (cuts q) m″
...     | (a , b) , mc , refl =
  subst (λ q′ → sw ⊢ tr (pre ++ (rep (suc p) false ++ (rep (suc q′) true ++ post′))) (⟨ lengthL pre , p , q′ ⟩ ∷ rest) ≈S
                     tr (pre ++ (rep (suc p) false ++ (rep (suc q′) true ++ post′)))
                        (⟨ lengthL pre , p , a ⟩ ∷ ⟨ lengthL pre + suc a , p , b ⟩ ∷ rest))
        (cuts-sound q mc) (base-left on pre p a b post′ rest)
base {sw} pre p q post′ rest m | inj₂ m′ with whenE (rsp sw) _ m′
...   | on , m″ with ∈-map⁻ _ (cuts p) m″
...     | (a , b) , mc , refl =
  subst (λ p′ → sw ⊢ tr (pre ++ (rep (suc p′) false ++ (rep (suc q) true ++ post′))) (⟨ lengthL pre , p′ , q ⟩ ∷ rest) ≈S
                     tr (pre ++ (rep (suc p′) false ++ (rep (suc q) true ++ post′)))
                        (⟨ lengthL pre + suc a , b , q ⟩ ∷ ⟨ lengthL pre , a , q ⟩ ∷ rest))
        (cuts-sound p mc) (base-right on pre a b q post′ rest)

-- A split anywhere in a path that runs from w.
tr-step : ∀ {sw} w pre e post {r t} → r ∈L splits sw e → run w (pre ++ e ∷ post) ≡ just t →
          sw ⊢ tr w (pre ++ e ∷ post) ≈S tr w (pre ++ r ++ post)
tr-step {sw} w (x ∷ pre) e post {rr} m h with run-cons x w (pre ++ e ∷ post) h
... | w′ , c , h′ =
  subst (λ v → sw ⊢ trE x w · tr v (pre ++ e ∷ post) ≈S trE x w · tr v (pre ++ rr ++ post))
        (sym (next-≡ x w c)) (·-c rflS (tr-step w′ pre e post m h′))
tr-step w [] ⟨ k , p , q ⟩ post m h with run-cons ⟨ k , p , q ⟩ w post h
... | w′ , c , _ with cross-sound k p q w c
...   | shape pre′ post′ refl refl _ = base pre′ p q post′ post m

------------------------------------------------------------------------
-- The link: grid equality gives T-equality of the translations.

module Link (m n : Nat) where
  open OnGrid m n

  link : ∀ {sw p q} → sw ⊢ p ≈ q → sw ⊢ tr start p ≈S tr start q
  link ≈-refl                              = rflS
  link (≈-step vp _ (step pre e post mm))  = tr-step start pre e post mm vp
  link (≈-sym d)                           = symS (link d)
  link (≈-trans d d′)                      = transS (link d) (link d′)
