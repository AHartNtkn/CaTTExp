------------------------------------------------------------------------
-- The rule-level half of single-hom conservativity, for every
-- pasting diagram.
--
-- For a pasting context Θ of dimension N ≥ 1 and Γ = ΣΘ (one hom),
-- and every variable v of Θ:
--
--   rule-bdry : (S v) ∈ ↓Supp(∂^sg T)  ⟺  S v ∈ ∂^sg Γ
--   rule-full : (S v) ∈ ↓Supp(T)
--
-- where ∂⁻Γ, ∂⁺Γ are Finster–Mimram's boundaries (`∂⁻`, `∂⁺` of
-- Syntax), ↓ is the face order of Gray.Support, and S v is the level
-- of v in ΣΘ. Together with the fact that the tuples of K(ΣΘ) are the
-- singletons (S v), this is the statement Gray.Bounded checked by
-- evaluation for |Θ| ≤ 6 edges: on one hom, the tables of the
-- operation and coherence cases close up to exactly the boundaries
-- and variables Finster–Mimram use.
--
-- Proof. Both sides are compared with one pointwise description
-- (Gray.BdryChar): dim v < N − 1, or dim v = N − 1 and v is not the
-- target (∂⁻) / source (∂⁺) of an N-cell.
--  * ⊆: a table entry of ∂^sg T is such a cell (the tables at
--    dimension N − 1 are exactly the cells that are not hit), and a
--    proper face has lower dimension.
--  * ⊇: go up from v through cells of which it is the sg-face until
--    reaching a cell that is not hit (it is in a lower table) or the
--    dimension N − 1. There, slide along N-cells: if u is the target
--    of w : u′ → u, replace u by u′, which has the same type, hence
--    the same faces; levels decrease, so this stops at a cell of the
--    (N − 1)-table (dually for ∂⁺, with levels increasing).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.SingleHom (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.DownAgree 𝕊
open import CaTTExp.Gray.Graded 𝕊
open import CaTTExp.Suspension 𝕊 using (Σctx; Σty; S; lenΣ; dimΣ; Σps; srcΣ; tgtΣ; ps-odd; Lift; mapS)
open import CaTTExp.Gray.Orient 𝕊 using (chainε-false)
open import CaTTExp.Gray.OrientRev 𝕊 using (Path; nil; cons; path⇒; path⇐)
open import CaTTExp.Gray.FullSupp 𝕊 using (piece-low-in; lr-snoc; InK; knil; kcons; full-cover)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)
import CaTTExp.Strict.PsFacts 𝕊 as SP
import CaTTExp.Gray.PsFacts 𝕊 as GP
open import CaTTExp.Gray.BdryChar 𝕊

------------------------------------------------------------------------
-- Lists and numbers.

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  map-map : ∀ {A B C : Set} (f : A → B) (g : B → C) xs → map g (map f xs) ≡ map (λ x → g (f x)) xs
  map-map f g []       = refl
  map-map f g (x ∷ xs) = cong (g (f x) ∷_) (map-map f g xs)

  max-0 : ∀ n → max n 0 ≡ n
  max-0 zero    = refl
  max-0 (suc n) = refl

  max-comm : ∀ a b → max a b ≡ max b a
  max-comm zero    zero    = refl
  max-comm zero    (suc b) = refl
  max-comm (suc a) zero    = refl
  max-comm (suc a) (suc b) = cong suc (max-comm a b)

  max-swap : ∀ a b c → max a (max b c) ≡ max b (max a c)
  max-swap zero    b       c       = refl
  max-swap (suc a) zero    c       = refl
  max-swap (suc a) (suc b) zero    = cong suc (max-comm a b)
  max-swap (suc a) (suc b) (suc c) = cong suc (max-swap a b c)

  maxL-snoc : ∀ xs y → maxL (xs ++ y ∷ []) ≡ max y (maxL xs)
  maxL-snoc []       y = refl
  maxL-snoc (x ∷ xs) y = trans (cong (max x) (maxL-snoc xs y)) (max-swap x y (maxL xs))

------------------------------------------------------------------------
-- The cells of ΣΘ.

fΣ : Nat × Ty → Nat × Ty
fΣ e = S (fst e) , Σty (snd e)

-- The cell of ΣΘ at the level S v, for v : A in Θ (dimension dim A in
-- the hom).
mkC : Nat × Ty → El
mkC e = el (S (fst e)) 1 (dim (snd e)) (fst (elBdry (Σty (snd e)))) (snd (elBdry (Σty (snd e))))

entriesΣ : ∀ Θ → entries (Σctx Θ) ≡ (0 , ⋆) ∷ (1 , ⋆) ∷ map fΣ (entries Θ)
entriesΣ ε = refl
entriesΣ (Θ ▸ A) rewrite entriesΣ Θ | lenΣ Θ | map-++ fΣ (entries Θ) ((len Θ , A) ∷ []) = refl

private
  isStarΣ : ∀ A → isStar (Σty A) ≡ false
  isStarΣ ⋆           = refl
  isStarΣ (arr A t u) = refl

  filter-starΣ : ∀ es → filter (λ e → isStar (snd e)) (map fΣ es) ≡ []
  filter-starΣ []            = refl
  filter-starΣ ((v , A) ∷ es) rewrite isStarΣ A = filter-starΣ es

objsΣ : ∀ Θ → objs (Σctx Θ) ≡ 0 ∷ 1 ∷ []
objsΣ Θ = trans (cong (λ es → map fst (filter (λ e → isStar (snd e)) es)) (entriesΣ Θ))
                (cong (λ L → 0 ∷ 1 ∷ map fst L) (filter-starΣ (entries Θ)))

endsTyΣ : ∀ A → endsTy (Σty A) ≡ just (var 0 , var 1)
endsTyΣ ⋆                       = refl
endsTyΣ (arr ⋆ t u)             = refl
endsTyΣ (arr (arr B s s') t u) = endsTyΣ (arr B s s')

private
  os₂ : List Nat
  os₂ = 0 ∷ 1 ∷ []

  homOfΣ : ∀ A → homOf os₂ (Σty A) ≡ just 1
  homOfΣ A rewrite endsTyΣ A = refl

  elsOf1 : ∀ v A → elsOf os₂ (S v) (Σty A) (just 1) ≡ mkC (v , A) ∷ []
  elsOf1 v A rewrite dimΣ A = refl

  mkElΣ : ∀ e → mkEl os₂ (fΣ e) ≡ mkC e ∷ []
  mkElΣ (v , A) = trans (mkEl≡ os₂ (S v) (Σty A))
                        (trans (cong (elsOf os₂ (S v) (Σty A)) (homOfΣ A)) (elsOf1 v A))

  cm-mkΣ : ∀ es → concatMap (mkEl os₂) (map fΣ es) ≡ map mkC es
  cm-mkΣ []       = refl
  cm-mkΣ (e ∷ es) rewrite mkElΣ e = cong (mkC e ∷_) (cm-mkΣ es)

cellsΣ : ∀ Θ → cells (Σctx Θ) ≡ map mkC (entries Θ)
cellsΣ Θ = trans (cong₂ (λ os es → concatMap (mkEl os) es) (objsΣ Θ) (entriesΣ Θ)) (cm-mkΣ (entries Θ))

homsΣ : ∀ Θ → homs (Σctx Θ) ≡ homAt (Σctx Θ) 1 ∷ []
homsΣ Θ = cong (λ os → map (homAt (Σctx Θ)) (drop1 (upto (lengthN os)))) (objsΣ Θ)

private
  filter-mkC : ∀ es → filter (λ c → hom c ==ℕ 1) (map mkC es) ≡ map mkC es
  filter-mkC []       = refl
  filter-mkC (e ∷ es) = cong (mkC e ∷_) (filter-mkC es)

  maxEntries : ∀ Θ → maxL (map hdim (map mkC (entries Θ))) ≡ dimCtx Θ
  maxEntries ε       = refl
  maxEntries (Θ ▸ A) =
    trans (cong (λ L → maxL (map hdim L)) (map-++ mkC (entries Θ) ((len Θ , A) ∷ [])))
      (trans (cong maxL (map-++ hdim (map mkC (entries Θ)) (mkC (len Θ , A) ∷ [])))
        (trans (maxL-snoc (map hdim (map mkC (entries Θ))) (dim A))
               (cong (max (dim A)) (maxEntries Θ))))

-- The one hom of ΣΘ.
hΣ : Ctx → Hom
hΣ Θ = homAt (Σctx Θ) 1

hcsΣ : ∀ Θ → hcs (hΣ Θ) ≡ cells (Σctx Θ)
hcsΣ Θ = trans (cong (filter (λ c → hom c ==ℕ 1)) (cellsΣ Θ))
               (trans (filter-mkC (entries Θ)) (sym (cellsΣ Θ)))

hdΣ : ∀ Θ → hd (hΣ Θ) ≡ dimCtx Θ
hdΣ Θ = trans (cong (λ L → maxL (map hdim L)) (hcsΣ Θ))
              (trans (cong (λ L → maxL (map hdim L)) (cellsΣ Θ)) (maxEntries Θ))

dimKΣ : ∀ Θ → dimK (homs (Σctx Θ)) ≡ dimCtx Θ
dimKΣ Θ = trans (cong dimK (homsΣ Θ)) (trans (+-zero (hd (hΣ Θ))) (hdΣ Θ))

------------------------------------------------------------------------
-- Membership in the cells.

lookup→entries : ∀ Γ v {A} → lookup Γ v ≡ just A → Any ((v , A) ≡_) (entries Γ)
lookup→entries (Γ ▸ B) v e with v ==ℕ len Γ in q
... | true  rewrite ==ℕ-sound v (len Γ) (subst T (sym q) tt) | just-inj e = any-++r (entries Γ) (here refl)
... | false = any-++l (lookup→entries Γ v e)

cell-in : ∀ Θ v {A} → lookup Θ v ≡ just A → Any (mkC (v , A) ≡_) (cells (Σctx Θ))
cell-in Θ v e =
  subst (Any (mkC (v , _) ≡_)) (sym (cellsΣ Θ))
    (subst (Any _) (sym (map≡ mkC (entries Θ))) (any-map⁺ mkC (any-mono (λ { refl → refl }) (lookup→entries Θ v e))))

cell-shape : ∀ Θ {c} → Any (c ≡_) (cells (Σctx Θ)) →
             Σ Nat λ v → Σ Ty λ A → (lookup Θ v ≡ just A) × (c ≡ mkC (v , A))
cell-shape Θ m
  with any-witness (any-map⁻ mkC (entries Θ) (subst (Any _) (map≡ mkC (entries Θ)) (subst (Any _) (cellsΣ Θ) m)))
... | (v , A) , me , q = v , A , entries-lookup Θ me , q

------------------------------------------------------------------------
-- Tables of one hom.

module _ (h : Hom) where

  chain1⇒ : ∀ s k {τ} → τ ∈L chainT s k (h ∷ []) → Σ Nat λ b → (τ ≡ b ∷ []) × (b ∈ᴺ piece h k s)
  chain1⇒ s k {τ} m with path⇒ (λ _ → false) (h ∷ []) s k (subst (λ L → τ ∈L L) (sym (chainε-false s k (h ∷ []))) m)
  ... | i ∷ [] , e , cons {c = c} mc nil = c , refl , subst (λ j → c ∈ᴺ piece h j s) (trans (sym (+-zero i)) e) mc

  chain1⇐ : ∀ s k {b} → b ∈ᴺ piece h k s → (b ∷ []) ∈L chainT s k (h ∷ [])
  chain1⇐ s k {b} mb =
    subst (λ L → (b ∷ []) ∈L L) (chainε-false s k (h ∷ []))
      (subst (λ j → (b ∷ []) ∈L chainε (λ _ → false) s j (h ∷ [])) (+-zero k)
        (path⇐ (λ _ → false) (cons {s = s} {h = h} {hs = []} {i = k} {is = []} mb nil)))
    where open import CaTTExp.Gray.Orient 𝕊 using (chainε)

lower⇒ : ∀ m hs {τ} → τ ∈L lowerT m hs → Σ Nat λ k → Σ Bool λ s → T (k <ℕ m) × (τ ∈L chainT s k hs)
lower⇒ zero    hs ()
lower⇒ (suc m) hs mτ with any-++⁻ (lowerT m hs) mτ
... | inj₁ l with lower⇒ m hs l
...   | k , s , lt , mc = k , s , SP.<-suc k m lt , mc
lower⇒ (suc m) hs mτ | inj₂ r with any-++⁻ (chainT false m hs) r
...   | inj₁ c = m , false , SP.n<suc m , c
...   | inj₂ c = m , true , SP.n<suc m , c

lower⇐ : ∀ m hs k s {τ} → T (k <ℕ m) → τ ∈L chainT s k hs → τ ∈L lowerT m hs
lower⇐ (suc m) hs k s {τ} lt mc with k ==ℕ m in e
... | true rewrite ==ℕ-sound k m (subst T (sym e) tt) = any-++r (lowerT m hs) (pickC s mc)
  where
  pickC : ∀ s → τ ∈L chainT s m hs → τ ∈L (chainT false m hs ++ chainT true m hs)
  pickC false c = any-++l c
  pickC true  c = any-++r (chainT false m hs) c
... | false = any-++l (lower⇐ m hs k s (SP.<suc-≢ k m lt e) mc)

-- An entry of a table below the top dimension is a cell that is not
-- hit.
piece-mem-low : ∀ h i s {b} → b ∈ᴺ piece h i s → T (i <ℕ hd h) →
                Σ El λ e → Any (e ≡_) (hcs h) × (b ≡ lvl e) × (hdim e ≡ i) × (any (hitsP i s e) (hcs h) ≡ false)
piece-mem-low h i s {b} m lt = go m
  where
  P : El → Bool
  P c = (hdim c ==ℕ i) ∧ not (any (hitsP i s c) (hcs h))
  low : piece h i s ≡ map lvl (filter P (hcs h))
  low rewrite SP.<→≢ i (hd h) lt | SP.T→≡ lt = refl
  notT : ∀ b → T (not b) → b ≡ false
  notT false _ = refl
  go : b ∈ᴺ piece h i s → _
  go m with any-witness (any-map⁻ lvl _ (subst (Any _) (map≡ lvl (filter P (hcs h))) (subst (λ L → b ∈ᴺ L) low m)))
  ... | e , me , q with filter⇒ P (hcs h) me
  ...   | me′ , pe = e , me′ , q , ==ℕ-sound (hdim e) i (∧-fst {hdim e ==ℕ i} pe) ,
                     notT (any (hitsP i s e) (hcs h)) (∧-snd {hdim e ==ℕ i} pe)

------------------------------------------------------------------------
-- Arithmetic.

private
  S-inj : ∀ {a b} → S a ≡ S b → a ≡ b
  S-inj refl = refl

  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

  ≡→T : ∀ {b} → b ≡ true → T b
  ≡→T refl = tt

  ≡→== : ∀ {a b} → a ≡ b → (a ==ℕ b) ≡ true
  ≡→== {a} refl = SP.==-refl a

  lt-lt-pred : ∀ s u n → T (s <ℕ u) → T (u <ℕ suc n) → T (s <ℕ n)
  lt-lt-pred zero    (suc u) (suc n) _ _ = tt
  lt-lt-pred zero    (suc u) zero    _ ()
  lt-lt-pred (suc s) (suc u) (suc n) p q = lt-lt-pred s u n p q

  lt-le-⊥ : ∀ L u → T (L <ℕ suc u) → T (u <ℕ L) → ⊥
  lt-le-⊥ zero    u       _ ()
  lt-le-⊥ (suc L) zero    () _
  lt-le-⊥ (suc L) (suc u) p q = lt-le-⊥ L u p q

  +suc : ∀ a b → a + suc b ≡ suc (a + b)
  +suc zero    b = refl
  +suc (suc a) b = cong suc (+suc a b)

  -- len ≤ (n + 1) + u and u < t give len ≤ n + t.
  shiftB : ∀ L n u t → T (L <ℕ suc (suc (n + u))) → T (u <ℕ t) → T (L <ℕ suc (n + t))
  shiftB L n u t p q = go L (n + u) (n + t) p (mono n u t q)
    where
    mono : ∀ n u t → T (u <ℕ t) → T ((n + u) <ℕ (n + t))
    mono zero    u t q = q
    mono (suc n) u t q = mono n u t q
    go : ∀ L a b → T (L <ℕ suc (suc a)) → T (a <ℕ b) → T (L <ℕ suc b)
    go zero    a       b       _ _ = tt
    go (suc L) zero    (suc b) p _ = go′ L b p
      where
      go′ : ∀ L b → T (L <ℕ 1) → T (L <ℕ suc b)
      go′ zero b _ = tt
      go′ (suc L) b ()
    go (suc L) (suc a) (suc b) p q = go L a b p q

  le-refl-plus : ∀ M a → T (M <ℕ suc (M + a))
  le-refl-plus zero    a = tt
  le-refl-plus (suc M) a = le-refl-plus M a

  lt→≤ : ∀ i n → T (i <ℕ suc n) → i ≤ n
  lt→≤ zero    n       _ = z≤n
  lt→≤ (suc i) (suc n) p = s≤s (lt→≤ i n p)
  lt→≤ (suc i) zero    ()

  lt-of-plus : ∀ a k → T (a <ℕ a + suc k)
  lt-of-plus zero    k = tt
  lt-of-plus (suc a) k = lt-of-plus a k

  pred-lt : ∀ n → T (0 <ℕ n) → T ((n ∸ 1) <ℕ n)
  pred-lt (suc n) _ = SP.n<suc n

  lt-trans-le : ∀ a b c → T (a <ℕ b) → T (b <ℕ suc c) → T (a <ℕ c)
  lt-trans-le a b c p q = lt-lt-pred a b c p q

  le-lt : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
  le-lt zero    b       (suc c) _ _ = tt
  le-lt (suc a) (suc b) (suc c) p q = le-lt a b c p q
  le-lt (suc a) zero    _       () _

  elBdryΣ : ∀ B s t → elBdry (Σty (arr B (var s) (var t))) ≡ (S s , S t)
  elBdryΣ ⋆           s t = refl
  elBdryΣ (arr _ _ _) s t = refl

------------------------------------------------------------------------
-- The main argument.

module Main {Θ z C} (d : Θ ⊢ps z ∶ C) (pos : T (0 <ℕ dimCtx Θ)) where

  Γ : Ctx
  Γ = Σctx Θ

  cs : List El
  cs = cells Γ

  h : Hom
  h = hΣ Θ

  N M NK : Nat
  N  = dimCtx Θ
  M  = N ∸ 1
  NK = dimK (homs Γ)

  private
    F = SP.ps-facts d

    inv : Inv Γ
    inv = GP.inv (fst (GP.ps-facts (Σps d)))

    G : Faces.Graded cs
    G = graded Γ inv

  open Faces cs

  M<N : T (M <ℕ N)
  M<N = pred-lt N pos

  hd≡ : hd h ≡ N
  hd≡ = hdΣ Θ

  ----------------------------------------------------------------------
  -- Cells of variables.

  in-h : ∀ v {A} → lookup Θ v ≡ just A → Any (mkC (v , A) ≡_) (hcs h)
  in-h v e = subst (λ L → Any (mkC (v , _) ≡_) L) (sym (hcsΣ Θ)) (cell-in Θ v e)

  find : ∀ v {A} → lookup Θ v ≡ just A → findEl (S v) cs ≡ just (mkC (v , A))
  find v e = findEl-mem Γ (cell-in Θ v e)

  hgt-v : ∀ v {A} → lookup Θ v ≡ just A → hgt (S v) ≡ dim A
  hgt-v v e = cong hgtM (find v e)

  bd-v : ∀ v {A} → lookup Θ v ≡ just A →
         bdEl cs (S v) ≡ (if dim A ==ℕ 0 then [] else (src (mkC (v , A)) ∷ tgt (mkC (v , A)) ∷ []))
  bd-v v e = bd-just cs (S v) (find v e)

  any-hcs : ∀ (p : El → Bool) → any p (hcs h) ≡ any p cs
  any-hcs p = cong (any p) (hcsΣ Θ)

  ----------------------------------------------------------------------
  -- Hits, in Θ and in the tables.

  hit-wit : ∀ i sg {e} → any (hitsP i sg e) cs ≡ true →
            Σ Nat λ w → Σ Ty λ B → Σ Nat λ s → Σ Nat λ t →
            (lookup Θ w ≡ just (arr B (var s) (var t))) × (dim B ≡ i) × (S (pickB sg s t) ≡ lvl e)
  hit-wit i sg {e} q with any-witness (anyS⇒ (hitsP i sg e) cs (≡→T q))
  ... | c , mc , hp with cell-shape Θ mc
  ...   | w , A , lw , refl = go A lw (SP.shape F w A lw) hp
    where
    go : ∀ A → lookup Θ w ≡ just A → PsTy A → T (hitsP i sg e (mkC (w , A))) →
         Σ Nat λ w → Σ Ty λ B → Σ Nat λ s → Σ Nat λ t →
         (lookup Θ w ≡ just (arr B (var s) (var t))) × (dim B ≡ i) × (S (pickB sg s t) ≡ lvl e)
    go ⋆ lw ⋆ₚ ()
    go (arr B (var s) (var t)) lw (arrₚ _) hp =
      w , B , s , t , lw , ==ℕ-sound (dim B) i (∧-fst {dim B ==ℕ i} hp) ,
      end sg (subst (λ p → T (if sg then (fst p ==ℕ lvl e) else (snd p ==ℕ lvl e))) (elBdryΣ B s t)
                    (∧-snd {dim B ==ℕ i} hp))
      where
      end : ∀ sg → T (if sg then (S s ==ℕ lvl e) else (S t ==ℕ lvl e)) → S (pickB sg s t) ≡ lvl e
      end true  q = ==ℕ-sound (S s) (lvl e) q
      end false q = ==ℕ-sound (S t) (lvl e) q

  hit→any : ∀ i sg v {A} → lookup Θ v ≡ just A → Hit sg i Θ v → any (hitsP i sg (mkC (v , A))) cs ≡ true
  hit→any i sg v {A} lv (w , B , s , t , lw , dB , pk) =
    T→≡ (anyS⇐ (hitsP i sg (mkC (v , A))) cs (any-at (cell-in Θ w lw) tp))
    where
    sec : ∀ sg → pickB sg s t ≡ v → T (if sg then (S s ==ℕ S v) else (S t ==ℕ S v))
    sec true  refl = ==ℕ-refl (S s)
    sec false refl = ==ℕ-refl (S t)
    tp : T (hitsP i sg (mkC (v , A)) (mkC (w , arr B (var s) (var t))))
    tp = ∧-in (≡→T (≡→== {dim B} dB))
              (subst (λ p → T (if sg then (fst p ==ℕ S v) else (snd p ==ℕ S v))) (sym (elBdryΣ B s t)) (sec sg pk))

  nohit→false : ∀ i sg v {A} → lookup Θ v ≡ just A → ¬ Hit sg i Θ v → any (hitsP i sg (mkC (v , A))) cs ≡ false
  nohit→false i sg v {A} lv nh with any (hitsP i sg (mkC (v , A))) cs in q
  ... | false = refl
  ... | true with hit-wit i sg {mkC (v , A)} q
  ...   | w , B , s , t , lw , dB , pk = ⊥-elim (nh (w , B , s , t , lw , dB , S-inj pk))

  false→nohit : ∀ i sg v {A} → lookup Θ v ≡ just A → any (hitsP i sg (mkC (v , A))) cs ≡ false → ¬ Hit sg i Θ v
  false→nohit i sg v lv q hit = f≢t (trans (sym q) (hit→any i sg v lv hit))
    where
    f≢t : false ≡ true → ⊥
    f≢t ()

  ----------------------------------------------------------------------
  -- The boundary tables of ΣΘ.

  bdryEq : ∀ sg → bdryT sg (homs Γ) ≡ lowerT M (h ∷ []) ++ chainT sg M (h ∷ [])
  bdryEq sg = trans (cong (bdryT sg) (homsΣ Θ))
                    (cong (λ n → lowerT (n ∸ 1) (h ∷ []) ++ chainT sg (n ∸ 1) (h ∷ [])) (trans (+-zero (hd h)) hd≡))

  NK≡ : NK ≡ N
  NK≡ = dimKΣ Θ

  in-piece : ∀ s u {A} → lookup Θ u ≡ just A → T (dim A <ℕ N) →
             any (hitsP (dim A) s (mkC (u , A))) cs ≡ false → S u ∈ᴺ piece h (dim A) s
  in-piece s u {A} lu lt q =
    piece-low-in h s {mkC (u , A)} (in-h u lu)
      (SP.<→≢ (dim A) (hd h) lt′) lt′ (trans (any-hcs (hitsP (dim A) s (mkC (u , A)))) q)
    where
    lt′ : T (dim A <ℕ hd h)
    lt′ = subst (λ n → T (dim A <ℕ n)) (sym hd≡) lt

  tbl-top : ∀ sg u {A} → lookup Θ u ≡ just A → dim A ≡ M →
            any (hitsP M sg (mkC (u , A))) cs ≡ false → (S u ∷ []) ∈L bdryT sg (homs Γ)
  tbl-top sg u {A} lu dM q =
    subst (λ L → (S u ∷ []) ∈L L) (sym (bdryEq sg))
      (any-++r (lowerT M (h ∷ []))
        (subst (λ j → (S u ∷ []) ∈L chainT sg j (h ∷ [])) dM
          (chain1⇐ h sg (dim A) (in-piece sg u lu (subst (λ j → T (j <ℕ N)) (sym dM) M<N)
            (subst (λ j → any (hitsP j sg (mkC (u , A))) cs ≡ false) (sym dM) q)))))

  tbl-low : ∀ sg s u {A} → lookup Θ u ≡ just A → T (dim A <ℕ M) →
            any (hitsP (dim A) s (mkC (u , A))) cs ≡ false → (S u ∷ []) ∈L bdryT sg (homs Γ)
  tbl-low sg s u {A} lu lt q =
    subst (λ L → (S u ∷ []) ∈L L) (sym (bdryEq sg))
      (any-++l (lower⇐ M (h ∷ []) (dim A) s lt
        (chain1⇐ h s (dim A) (in-piece s u lu (SP.<-trans (dim A) M N lt M<N) q))))

  inTable : ∀ sg {b} → (b ∷ []) ∈L bdryT sg (homs Γ) →
            Σ Nat λ j → Σ Bool λ s → (b ∈ᴺ piece h j s) × (T (j <ℕ M) ⊎ ((j ≡ M) × (s ≡ sg)))
  inTable sg {b} m with any-++⁻ (lowerT M (h ∷ [])) (subst (λ L → (b ∷ []) ∈L L) (bdryEq sg) m)
  ... | inj₁ l with lower⇒ M (h ∷ []) l
  ...   | k , s , lt , mc with chain1⇒ h s k mc
  ...     | b′ , refl , pb = k , s , pb , inj₁ lt
  inTable sg {b} m | inj₂ c with chain1⇒ h sg M c
  ...   | b′ , refl , pb = M , sg , pb , inj₂ (refl , refl)

  ----------------------------------------------------------------------
  -- ⊆: what lies below a boundary table is in the boundary.

  rule⇒ : ∀ sg v {A} → lookup Θ v ≡ just A →
          T (any (leqT cs NK (S v ∷ [])) (bdryT sg (homs Γ))) → InBd sg M Θ v
  rule⇒ sg v {A} lv p with any-witness (anyS⇒ (leqT cs NK (S v ∷ [])) (bdryT sg (homs Γ)) p)
  ... | τ , mτ , q with leqT⇒ NK (S v ∷ []) τ q
  ...   | pcons {b = b} k _ lr pnil = fin b k lr mτ
    where
    jlt : ∀ {j s} → (T (j <ℕ M) ⊎ ((j ≡ M) × (s ≡ sg))) → T (j <ℕ hd h)
    jlt (inj₁ l) = subst (λ n → T (_ <ℕ n)) (sym hd≡) (SP.<-trans _ M N l M<N)
    jlt (inj₂ (refl , _)) = subst (λ n → T (M <ℕ n)) (sym hd≡) M<N

    dimv≡ : SP.dimv Θ v ≡ dim A
    dimv≡ = cong SP.dimM lv

    fin : ∀ b k → LR k b (S v) → (b ∷ []) ∈L bdryT sg (homs Γ) → InBd sg M Θ v
    fin b k lr mb with inTable sg mb
    ... | j , s , pj , jc with piece-mem-low h j s pj (jlt jc)
    ...   | e , me , refl , refl , nh with cell-shape Θ (subst (λ L → Any (e ≡_) L) (hcsΣ Θ) me)
    ...     | u , Au , lu , refl = case lr jc nh
      where
      case : LR k (S u) (S v) → (T (dim Au <ℕ M) ⊎ ((dim Au ≡ M) × (s ≡ sg))) →
             any (hitsP (dim Au) s (mkC (u , Au))) (hcs h) ≡ false → InBd sg M Θ v
      case lz jc nh with trans (sym lu) lv
      ... | refl = SP.lookup-< Θ v lv , top jc
        where
        top : (T (dim A <ℕ M) ⊎ ((dim A ≡ M) × (s ≡ sg))) → T (SP.dimv Θ v <ℕ M) ⊎ ((SP.dimv Θ v ≡ M) × ¬ Hit sg M Θ v)
        top (inj₁ l) = inj₁ (subst (λ n → T (n <ℕ M)) (sym dimv≡) l)
        top (inj₂ (dM , refl)) =
          inj₂ (trans dimv≡ dM , false→nohit M sg v lv
                  (trans (sym (any-hcs (hitsP M sg (mkC (v , A)))))
                         (subst (λ j → any (hitsP j sg (mkC (v , A))) (hcs h) ≡ false) dM nh)))
      case (ls {k = k′} mc lr′) jc nh = SP.lookup-< Θ v lv , inj₁ (subst (λ n → T (n <ℕ M)) (sym dimv≡) (below jc))
        where
        rk : dim A + suc k′ ≡ dim Au
        rk = trans (cong (_+ suc k′) (sym (hgt-v v lv)))
                   (trans (lr-rank G (ls mc lr′)) (hgt-v u lu))
        below : (T (dim Au <ℕ M) ⊎ ((dim Au ≡ M) × (s ≡ sg))) → T (dim A <ℕ M)
        below (inj₁ l) = SP.<-trans (dim A) (dim Au) M (subst (λ n → T (dim A <ℕ n)) rk (lt-of-plus (dim A) k′)) l
        below (inj₂ (dM , _)) = subst (λ n → T (dim A <ℕ n)) (trans rk dM) (lt-of-plus (dim A) k′)

  ----------------------------------------------------------------------
  -- Sliding at dimension N − 1 along N-cells.

  Found : Bool → Ty → Set
  Found sg A = Σ Nat λ u′ → (lookup Θ u′ ≡ just A) × ((S u′ ∷ []) ∈L bdryT sg (homs Γ))

  slideF : ∀ n u {A} → lookup Θ u ≡ just A → dim A ≡ M → T (u <ℕ n) → Found false A
  slideF zero    u lu dM ()
  slideF (suc n) u {A} lu dM bn with any (hitsP M false (mkC (u , A))) cs in q
  ... | false = u , lu , tbl-top false u lu dM q
  ... | true with hit-wit M false {mkC (u , A)} q
  ...   | w , B , s , t , lw , dB , pk with SP.ord F w B s t lw
  ...     | lsB , ltB , sot =
    slideF n s (subst (λ X → lookup Θ s ≡ just X) BA lsB) dM (lt-lt-pred s u n (subst (λ x → T (s <ℕ x)) tu sot) bn)
    where
    tu : t ≡ u
    tu = S-inj pk
    BA : B ≡ A
    BA = just-inj (trans (sym (subst (λ x → lookup Θ x ≡ just B) tu ltB)) lu)

  slideT : ∀ n u {A} → lookup Θ u ≡ just A → dim A ≡ M → T (len Θ <ℕ suc (n + u)) → Found true A
  slideT zero    u lu dM bn = ⊥-elim (lt-le-⊥ (len Θ) u bn (SP.lookup-< Θ u lu))
  slideT (suc n) u {A} lu dM bn with any (hitsP M true (mkC (u , A))) cs in q
  ... | false = u , lu , tbl-top true u lu dM q
  ... | true with hit-wit M true {mkC (u , A)} q
  ...   | w , B , s , t , lw , dB , pk with SP.ord F w B s t lw
  ...     | lsB , ltB , sot =
    slideT n t (subst (λ X → lookup Θ t ≡ just X) BA ltB) dM
      (shiftB (len Θ) n u t bn (subst (λ x → T (x <ℕ t)) su sot))
    where
    su : s ≡ u
    su = S-inj pk
    BA : B ≡ A
    BA = just-inj (trans (sym (subst (λ x → lookup Θ x ≡ just B) su lsB)) lu)

  slide : ∀ sg u {A} → lookup Θ u ≡ just A → dim A ≡ M → Found sg A
  slide false u lu dM = slideF (len Θ) u lu dM (SP.lookup-< Θ u lu)
  slide true  u lu dM = slideT (len Θ) u lu dM (le-plus (len Θ) u)
    where
    le-plus : ∀ L u → T (L <ℕ suc (L + u))
    le-plus = le-refl-plus

  ----------------------------------------------------------------------
  -- ⊇: going up from a low cell.

  Up : Bool → Nat → Set
  Up sg v = Σ Nat λ u′ → Σ Ty λ A′ → Σ Nat λ k →
            (lookup Θ u′ ≡ just A′) × ((S u′ ∷ []) ∈L bdryT sg (homs Γ)) × LR k (S u′) (S v)

  up : ∀ sg f u {A} → lookup Θ u ≡ just A → T (dim A <ℕ M) → T (M <ℕ suc (f + dim A)) → Up sg u
  up sg f u {A} lu lt bnd with any (hitsP (dim A) sg (mkC (u , A))) cs in q
  ... | false = u , A , 0 , lu , tbl-low sg sg u lu lt q , lz
  ... | true with hit-wit (dim A) sg {mkC (u , A)} q
  ...   | w , B , s , t , lw , dB , pk = next f bnd (lt-cases′ (dim A) M lt)
    where
    Aw = arr B (var s) (var t)

    face : S u ∈ᴺ bdEl cs (S w)
    face = subst (λ L → S u ∈ᴺ L) (sym (trans (bd-v w lw) (cong (λ p → fst p ∷ snd p ∷ []) (elBdryΣ B s t)))) (pk-in sg pk)
      where
      pk-in : ∀ sg → S (pickB sg s t) ≡ S u → S u ∈ᴺ (S s ∷ S t ∷ [])
      pk-in true  p = here (sym p)
      pk-in false p = there (here (sym p))

    lt-cases′ : ∀ a i → T (a <ℕ i) → T (suc a <ℕ i) ⊎ (suc a ≡ i)
    lt-cases′ zero    (suc zero)    _ = inj₂ refl
    lt-cases′ zero    (suc (suc i)) _ = inj₁ tt
    lt-cases′ (suc a) (suc i)       p with lt-cases′ a i p
    ... | inj₁ r = inj₁ r
    ... | inj₂ r = inj₂ (cong suc r)

    dAw : dim Aw ≡ suc (dim A)
    dAw = cong suc dB

    next : ∀ f → T (M <ℕ suc (f + dim A)) → T (suc (dim A) <ℕ M) ⊎ (suc (dim A) ≡ M) → Up sg u
    next zero    b _ = ⊥-elim (lt-le-⊥ M (dim A) b lt)
    next (suc f) b (inj₁ l) with up sg f w {Aw} lw (subst (λ n → T (n <ℕ M)) (sym dAw) l)
                                    (subst (λ n → T (M <ℕ suc n)) (trans (sym (+suc f (dim A))) (cong (f +_) (sym dAw))) b)
    ... | u′ , A′ , k , lu′ , mb , lr = u′ , A′ , suc k , lu′ , mb , lr-snoc Γ lr face
    next (suc f) b (inj₂ e) with slide sg w {Aw} lw (trans dAw e)
    ... | u′ , lu′ , mb = u′ , Aw , 1 , lu′ , mb , ls face′ lz
      where
      face′ : S u ∈ᴺ bdEl cs (S u′)
      face′ = subst (λ L → S u ∈ᴺ L) (trans (bd-v w lw) (sym (bd-v u′ lu′))) face

  rule⇐ : ∀ sg v {A} → lookup Θ v ≡ just A → InBd sg M Θ v →
          T (any (leqT cs NK (S v ∷ [])) (bdryT sg (homs Γ)))
  rule⇐ sg v {A} lv (_ , inj₂ (dM , nh)) =
    anyS⇐ (leqT cs NK (S v ∷ [])) (bdryT sg (homs Γ))
      (any-at (tbl-top sg v lv dA (nohit→false M sg v lv nh)) (leqT⇐ {NK} {S v ∷ []} {S v ∷ []} (pcons 0 z≤n lz pnil)))
    where
    dA : dim A ≡ M
    dA = trans (sym (cong SP.dimM lv)) dM
  rule⇐ sg v {A} lv (_ , inj₁ lt) with up sg M v lv lt′ (le-refl-plus M (dim A))
    where
    lt′ : T (dim A <ℕ M)
    lt′ = subst (λ n → T (n <ℕ M)) (cong SP.dimM lv) lt
  ... | u′ , A′ , k , lu′ , mb , lr =
    anyS⇐ (leqT cs NK (S v ∷ [])) (bdryT sg (homs Γ))
      (any-at mb (leqT⇐ (pcons k kb lr pnil)))
    where
    rk : dim A + k ≡ dim A′
    rk = trans (cong (_+ k) (sym (hgt-v v lv))) (trans (lr-rank G lr) (hgt-v u′ lu′))
    kb : k ≤ NK
    kb = subst (k ≤_) (sym NK≡)
           (≤-trans (subst (k ≤_) rk (n≤m+n (dim A) k)) (lt→≤ (dim A′) N (SP.dim-≤-dimCtx Θ u′ lu′)))

------------------------------------------------------------------------
-- The statements, with Finster–Mimram's boundaries of ΣΘ.

FM : Bool → Ctx → List Nat
FM false Γ = ∂⁻ Γ
FM true  Γ = ∂⁺ Γ

private
  dimCtxΣ : ∀ Θ A → dimCtx (Σctx (Θ ▸ A)) ≡ suc (dimCtx (Θ ▸ A))
  dimCtxΣ ε       A rewrite dimΣ A = cong suc (sym (max-0 (dim A)))
  dimCtxΣ (Θ ▸ B) A rewrite dimΣ A | dimCtxΣ Θ B = refl

  elem-mapS : ∀ v L → elem (S v) (mapS L) ≡ elem v L
  elem-mapS v []       = refl
  elem-mapS v (x ∷ L) = cong ((v ==ℕ x) ∨_) (elem-mapS v L)

  sucpred : ∀ n → T (0 <ℕ n) → n ≡ suc (n ∸ 1)
  sucpred (suc n) _ = refl

FM-Σ : ∀ {Θ z C} → Θ ⊢ps z ∶ C → T (0 <ℕ dimCtx Θ) →
       ∀ sg v → elem (S v) (FM sg (Σctx Θ)) ≡ elem v (bdV sg (dimCtx Θ ∸ 1) Θ)
FM-Σ {ε}     d () sg v
FM-Σ {Θ ▸ A} d pos false v =
  trans (cong (λ i → elem (S v) (srcVars i (Σctx (Θ ▸ A))))
              (trans (cong (_∸ 1) (dimCtxΣ Θ A)) (sucpred (dimCtx (Θ ▸ A)) pos)))
        (trans (cong (elem (S v)) (srcΣ (dimCtx (Θ ▸ A) ∸ 1) (Θ ▸ A))) (elem-mapS v (srcVars (dimCtx (Θ ▸ A) ∸ 1) (Θ ▸ A))))
FM-Σ {Θ ▸ A} d pos true v =
  trans (cong (λ i → elem (S v) (tgtVars i (Σctx (Θ ▸ A))))
              (trans (cong (_∸ 1) (dimCtxΣ Θ A)) (sucpred (dimCtx (Θ ▸ A)) pos)))
        (trans (cong (elem (S v)) (tgtΣ (dimCtx (Θ ▸ A) ∸ 1) (Θ ▸ A) (ps-odd d))) (elem-mapS v (tgtVars (dimCtx (Θ ▸ A) ∸ 1) (Θ ▸ A))))

-- The closure of Supp(∂^sg T) is ∂^sg(ΣΘ), on non-object variables.
rule-bdry⇒ : ∀ {Θ z C} → Θ ⊢ps z ∶ C → T (0 <ℕ dimCtx Θ) → ∀ sg v {A} → lookup Θ v ≡ just A →
             T (any (leqT (cells (Σctx Θ)) (dimK (homs (Σctx Θ))) (S v ∷ [])) (bdryT sg (homs (Σctx Θ)))) →
             elem (S v) (FM sg (Σctx Θ)) ≡ true
rule-bdry⇒ {Θ} d pos sg v lv p =
  trans (FM-Σ d pos sg v) (bd⇐ d sg (dimCtx Θ ∸ 1) v (Main.rule⇒ d pos sg v lv p))

rule-bdry⇐ : ∀ {Θ z C} → Θ ⊢ps z ∶ C → T (0 <ℕ dimCtx Θ) → ∀ sg v {A} → lookup Θ v ≡ just A →
             elem (S v) (FM sg (Σctx Θ)) ≡ true →
             T (any (leqT (cells (Σctx Θ)) (dimK (homs (Σctx Θ))) (S v ∷ [])) (bdryT sg (homs (Σctx Θ))))
rule-bdry⇐ {Θ} d pos sg v lv q =
  Main.rule⇐ d pos sg v lv (bd⇒ d sg (dimCtx Θ ∸ 1) v (trans (sym (FM-Σ d pos sg v)) q))

-- The closure of Supp(T) is every non-object variable.
rule-full : ∀ Θ v {A} → lookup Θ v ≡ just A →
            T (any (leqT (cells (Σctx Θ)) (dimK (homs (Σctx Θ))) (S v ∷ [])) (fullT (homs (Σctx Θ))))
rule-full Θ v {A} lv =
  full-cover (Σctx Θ)
    (subst (λ hs → InK (Σctx Θ) hs (S v ∷ [])) (sym (homsΣ Θ))
      (kcons (subst (λ L → Any (mkC (v , A) ≡_) L) (sym (hcsΣ Θ)) (cell-in Θ v lv)) knil))

-- The tuples of K(ΣΘ) are the singletons (S v), for v a variable of Θ.
tuples-K : ∀ Θ {x} → InK (Σctx Θ) (homs (Σctx Θ)) x →
           Σ Nat λ v → Σ Ty λ A → (lookup Θ v ≡ just A) × (x ≡ S v ∷ [])
tuples-K Θ {x} k = go (subst (λ hs → InK (Σctx Θ) hs x) (homsΣ Θ) k)
  where
  go : InK (Σctx Θ) (hΣ Θ ∷ []) x → Σ Nat λ v → Σ Ty λ A → (lookup Θ v ≡ just A) × (x ≡ S v ∷ [])
  go (kcons me knil) with cell-shape Θ (subst (λ L → Any (_ ≡_) L) (hcsΣ Θ) me)
  ... | v , A , lv , refl = v , A , lv , refl
