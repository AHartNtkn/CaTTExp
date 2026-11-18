------------------------------------------------------------------------
-- The hypotheses of Gray.DownAgree hold in every context whose types
-- are variable towers (every pasting context, Strict.L.ps-inv), for
-- every comparison the side condition makes.
--
--   graded      : Inv Γ → Graded (cells Γ)
--   chain-rank  : x ∈ chainT sg k (homs Γ) → rank x ≡ k
--   PsSide      : under Inv Θ, each of the four generator comparisons
--                 of graySide Θ A t u implies the closure equality.
--
-- The term side needs no hypothesis: in a graded context, a tuple
-- below a table tuple entrywise has rank at most that tuple's rank,
-- and the comparison itself puts every tuple of supp t A below a
-- table tuple.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Graded (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.DownAgree 𝕊
open import CaTTExp.Gray.Orient 𝕊 using (chainε; chainε-false)
open import CaTTExp.Gray.OrientRev 𝕊 using (Path; nil; cons; path⇒)

-- Every type in the context is a tower of variables.
VT : Ctx → Ty → Set
VT Γ ⋆           = ⊤
VT Γ (arr B s t) =
  Σ Nat λ i → Σ Nat λ j → (s ≡ var i) × (t ≡ var j) × (lookup Γ i ≡ just B) × (lookup Γ j ≡ just B)

Inv : Ctx → Set
Inv Γ = ∀ i B → lookup Γ i ≡ just B → VT Γ B

------------------------------------------------------------------------
-- The cells of a context.

headM : List El → Maybe El
headM []      = nothing
headM (c ∷ _) = just c

orElse : Maybe El → Maybe El → Maybe El
orElse (just c) _ = just c
orElse nothing  m = m

-- The hom index of a cell of type A (if A's ends are objects).
homOf : List Nat → Ty → Maybe Nat
homOf os A with endsTy A
... | nothing      = nothing
... | just (_ , b) with varLvl b
...   | nothing = nothing
...   | just b' = posOf b' os

elsOf : List Nat → Nat → Ty → Maybe Nat → List El
elsOf os v A nothing  = []
elsOf os v A (just k) = el v k (dim A ∸ 1) (fst (elBdry A)) (snd (elBdry A)) ∷ []

mkEl≡ : ∀ os v A → mkEl os (v , A) ≡ elsOf os v A (homOf os A)
mkEl≡ os v A with endsTy A
... | nothing      = refl
... | just (_ , b) with varLvl b
...   | nothing = refl
...   | just b' with posOf b' os
...     | nothing = refl
...     | just k  = refl

elsOf-lvl : ∀ os v A m {c} → Any (c ≡_) (elsOf os v A m) → lvl c ≡ v
elsOf-lvl os v A (just k) (here refl) = refl

elAt : List Nat → Ctx → Nat → Maybe El
elAt os Γ w with lookup Γ w
... | nothing = nothing
... | just A  = headM (mkEl os (w , A))

findEl-++ : ∀ w xs ys → findEl w (xs ++ ys) ≡ orElse (findEl w xs) (findEl w ys)
findEl-++ w []       ys = refl
findEl-++ w (c ∷ xs) ys with lvl c ==ℕ w
... | true  = refl
... | false = findEl-++ w xs ys

cm-++ : ∀ {A B : Set} (f : A → List B) xs ys → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
cm-++ f []       ys = refl
cm-++ f (x ∷ xs) ys = trans (cong (f x ++_) (cm-++ f xs ys)) (sym (++-assoc (f x) (concatMap f xs) (concatMap f ys)))

==-refl≡ : ∀ n → (n ==ℕ n) ≡ true
==-refl≡ zero    = refl
==-refl≡ (suc n) = ==-refl≡ n

==-sym≡ : ∀ m n → (m ==ℕ n) ≡ (n ==ℕ m)
==-sym≡ zero    zero    = refl
==-sym≡ zero    (suc n) = refl
==-sym≡ (suc m) zero    = refl
==-sym≡ (suc m) (suc n) = ==-sym≡ m n

lt-ne : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
lt-ne zero    (suc n) _ = refl
lt-ne (suc i) (suc n) p = lt-ne i n p

weak< : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
weak< zero    b       _ = tt
weak< (suc a) (suc b) q = weak< a b q

lookup-len : ∀ Γ i → T (len Γ <ℕ suc i) → lookup Γ i ≡ nothing
lookup-len ε       i _ = refl
lookup-len (Γ ▸ A) i p rewrite trans (==-sym≡ i (len Γ)) (lt-ne (len Γ) i p) = lookup-len Γ i (weak< (len Γ) i p)

-- A cell of mkEl for entry w is found first.
findEl-one : ∀ os w A → findEl w (mkEl os (w , A)) ≡ headM (mkEl os (w , A))
findEl-one os w A rewrite mkEl≡ os w A with homOf os A
... | nothing = refl
... | just k rewrite ==-refl≡ w = refl

findEl-other : ∀ os v w A → (v ==ℕ w) ≡ false → findEl w (mkEl os (v , A)) ≡ nothing
findEl-other os v w A ne rewrite mkEl≡ os v A with homOf os A
... | nothing = refl
... | just k rewrite ne = refl

orElse-nothing : ∀ m → orElse m nothing ≡ m
orElse-nothing nothing  = refl
orElse-nothing (just c) = refl

findEl-cells : ∀ os Γ w → findEl w (concatMap (mkEl os) (entries Γ)) ≡ elAt os Γ w
findEl-cells os ε       w = refl
findEl-cells os (Γ ▸ A) w
  rewrite cm-++ (mkEl os) (entries Γ) ((len Γ , A) ∷ [])
        | ++-[] (mkEl os (len Γ , A))
        | findEl-++ w (concatMap (mkEl os) (entries Γ)) (mkEl os (len Γ , A))
        | findEl-cells os Γ w
  with w ==ℕ len Γ in e
... | true  rewrite ==ℕ-sound w (len Γ) (subst T (sym e) tt)
                  | lookup-len Γ (len Γ) (lt-refl (len Γ)) = findEl-one os (len Γ) A
... | false rewrite findEl-other os (len Γ) w A (trans (==-sym≡ (len Γ) w) e) = orElse-nothing (elAt os Γ w)

entries-lt : ∀ Γ {v A} → Any ((v , A) ≡_) (entries Γ) → T (v <ℕ len Γ)
entries-lt (Γ ▸ B) m with any-++⁻ (entries Γ) m
... | inj₁ a = weak< _ (len Γ) (entries-lt Γ a)
... | inj₂ (here refl) = lt-refl (len Γ)

entries-lookup : ∀ Γ {v A} → Any ((v , A) ≡_) (entries Γ) → lookup Γ v ≡ just A
entries-lookup (Γ ▸ B) {v} m with any-++⁻ (entries Γ) m
... | inj₁ a rewrite lt-ne v (len Γ) (entries-lt Γ a) = entries-lookup Γ a
... | inj₂ (here refl) rewrite ==-refl≡ (len Γ) = refl

elsOf-head : ∀ os v A m {c} → Any (c ≡_) (elsOf os v A m) → headM (elsOf os v A m) ≡ just c
elsOf-head os v A (just k) (here refl) = refl

elsOf-mem-lvl : ∀ os v A {c} → Any (c ≡_) (mkEl os (v , A)) → lvl c ≡ v
elsOf-mem-lvl os v A m = elsOf-lvl os v A (homOf os A) (subst (Any _) (mkEl≡ os v A) m)

-- Every cell of Γ is the one findEl returns for its level.
findEl-mem : ∀ Γ {e} → Any (e ≡_) (cells Γ) → findEl (lvl e) (cells Γ) ≡ just e
findEl-mem Γ {e} m
  with any-witness (any-cm⁻ (mkEl (objs Γ)) (entries Γ) (subst (Any _) (cm≡ (mkEl (objs Γ)) (entries Γ)) m))
... | (v , A) , mv , me rewrite elsOf-mem-lvl (objs Γ) v A me
  = trans (findEl-cells (objs Γ) Γ v) (elAt≡ (entries-lookup Γ mv))
  where
  elAt≡ : lookup Γ v ≡ just A → elAt (objs Γ) Γ v ≡ just e
  elAt≡ eL with lookup Γ v
  elAt≡ refl | .(just A) =
    trans (cong headM (mkEl≡ (objs Γ) v A))
          (elsOf-head (objs Γ) v A (homOf (objs Γ) A) (subst (Any _) (mkEl≡ (objs Γ) v A) me))

------------------------------------------------------------------------
-- Gradedness.

elAt-just : ∀ os Γ w {c} → elAt os Γ w ≡ just c →
            Σ Ty λ A → (lookup Γ w ≡ just A) × Σ Nat λ k → (homOf os A ≡ just k) ×
            (c ≡ el w k (dim A ∸ 1) (fst (elBdry A)) (snd (elBdry A)))
elAt-just os Γ w e with lookup Γ w
... | just A rewrite mkEl≡ os w A with homOf os A in eH
elAt-just os Γ w refl | just A | just k = A , refl , k , eH , refl

hgt-of : ∀ Γ i {A' k} → lookup Γ i ≡ just A' → homOf (objs Γ) A' ≡ just k →
         Faces.hgt (cells Γ) i ≡ dim A' ∸ 1
hgt-of Γ i {A'} eL eH
  rewrite findEl-cells (objs Γ) Γ i | eL | mkEl≡ (objs Γ) i A' | eH = refl

bd-just : ∀ cs w {c} → findEl w cs ≡ just c → bdEl cs w ≡ (if hdim c ==ℕ 0 then [] else (src c ∷ tgt c ∷ []))
bd-just cs w e with findEl w cs
bd-just cs w refl | just c = refl

graded : ∀ Γ → Inv Γ → Faces.Graded (cells Γ)
graded Γ inv w {b} mb = go (findEl w (cells Γ)) refl
  where
  open Faces (cells Γ)
  go : ∀ m → findEl w (cells Γ) ≡ m → suc (hgt b) ≡ hgt w
  go nothing e = ⊥-elim (no (subst (λ l → b ∈ᴺ l) (bd-nothing e) mb))
    where
    no : b ∈ᴺ [] → ⊥
    no ()
    bd-nothing : findEl w (cells Γ) ≡ nothing → bdEl (cells Γ) w ≡ []
    bd-nothing e with findEl w (cells Γ)
    bd-nothing refl | nothing = refl
  go (just c) e with elAt-just (objs Γ) Γ w (trans (sym (findEl-cells (objs Γ) Γ w)) e)
  ... | A , eL , k , eH , refl = shape A eL eH (cong hgtM e) (subst (λ l → b ∈ᴺ l) (bd-just (cells Γ) w e) mb)
    where
    shape : ∀ A → lookup Γ w ≡ just A → homOf (objs Γ) A ≡ just k → hgt w ≡ dim A ∸ 1 →
            b ∈ᴺ (if (dim A ∸ 1) ==ℕ 0 then [] else (fst (elBdry A) ∷ snd (elBdry A) ∷ [])) →
            suc (hgt b) ≡ hgt w
    shape ⋆ _ _ _ ()
    shape (arr ⋆ _ _) _ _ _ ()
    shape (arr (arr A'' s0 t0) a a') eL eH hw' mb' with inv w _ eL
    ... | i , j , refl , refl , li , lj = trans (pk mb') (sym hw')
      where
      pk : b ∈ᴺ (i ∷ j ∷ []) → suc (hgt b) ≡ suc (dim A'')
      pk (here refl)         = cong suc (hgt-of Γ i li eH)
      pk (there (here refl)) = cong suc (hgt-of Γ j lj eH)

------------------------------------------------------------------------
-- Ranks of table tuples.

piece-mem : ∀ h i sg {w} → w ∈ᴺ piece h i sg →
            Σ El λ e → Any (e ≡_) (hcs h) × (w ≡ lvl e) × (hdim e ≡ i)
piece-mem h i sg m with i ==ℕ hd h
... | true with any-witness (any-map⁻ lvl _ (subst (Any _) (map≡ lvl (filter (λ c → hdim c ==ℕ i) (hcs h))) m))
...   | e , me , refl with filter⇒ (λ c → hdim c ==ℕ i) (hcs h) me
...     | me' , q = e , me' , refl , ==ℕ-sound (hdim e) i q
piece-mem h i sg m | false with i <ℕ hd h
piece-mem h i sg m | false | true
  with any-witness (any-map⁻ lvl _ (subst (Any _) (map≡ lvl _) m))
... | e , me , refl with filter⇒ _ (hcs h) me
...   | me' , q = e , me' , refl , ==ℕ-sound (hdim e) i (∧-fst {hdim e ==ℕ i} q)
piece-mem h i sg () | false | false

+-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
+-mono {b = b} {d = d} z≤n q = ≤-trans q (n≤m+n b d)
+-mono (s≤s p) q = s≤s (+-mono p q)

∸1≤ : ∀ n → n ∸ 1 ≤ n
∸1≤ zero    = z≤n
∸1≤ (suc n) = ≤-step (≤-refl n)

module Ranks (Γ : Ctx) where
  open Faces (cells Γ)

  private
    N  = dimK (homs Γ)
    cs = cells Γ

  HomOK : Hom → Set
  HomOK h = ∀ {e} → Any (e ≡_) (hcs h) → Any (e ≡_) (cells Γ)

  private
    map-ok : ∀ L {h} → Any (h ≡_) (map (homAt Γ) L) → HomOK h
    map-ok L m mh with any-witness (any-map⁻ (homAt Γ) L (subst (Any _) (map≡ (homAt Γ) L) m))
    ... | k , _ , refl = fst (filter⇒ (λ c → hom c ==ℕ k) (cells Γ) mh)

  homs-ok : ∀ {h} → Any (h ≡_) (homs Γ) → HomOK h
  homs-ok = map-ok _

  path-rank : ∀ {s hs is x} → (∀ {h} → Any (h ≡_) hs → HomOK h) →
              Path (λ _ → false) s hs is x → rank x ≡ sumL is
  path-rank ok nil = refl
  path-rank ok (cons {s = s} {h = h} {i = i} mc p) with piece-mem h i s mc
  ... | e , me , refl , hdi =
    cong₂ _+_ (trans (cong hgtM (findEl-mem Γ (ok (here refl) me))) hdi) (path-rank (λ m → ok (there m)) p)

  chain-rank : ∀ sg k {x} → x ∈L chainT sg k (homs Γ) → rank x ≡ k
  chain-rank sg k {x} m
    with path⇒ (λ _ → false) (homs Γ) sg k (subst (λ L → x ∈L L) (sym (chainε-false sg k (homs Γ))) m)
  ... | is , e , p = trans (path-rank homs-ok p) e

  lower-rank : ∀ m {x} → x ∈L lowerT m (homs Γ) → suc (rank x) ≤ m
  lower-rank (suc m) {x} q with any-++⁻ (lowerT m (homs Γ)) q
  ... | inj₁ a = ≤-step (lower-rank m a)
  ... | inj₂ b with any-++⁻ (chainT false m (homs Γ)) b
  ...   | inj₁ c = s≤s (subst (_≤ m) (sym (chain-rank false m c)) (≤-refl m))
  ...   | inj₂ c = s≤s (subst (_≤ m) (sym (chain-rank true m c)) (≤-refl m))

  full-rank : ∀ {x} → x ∈L fullT (homs Γ) → rank x ≤ N
  full-rank q with any-++⁻ (lowerT N (homs Γ)) q
  ... | inj₁ a = ≤-trans (≤-step (≤-refl _)) (lower-rank N a)
  ... | inj₂ b = subst (_≤ N) (sym (chain-rank true N b)) (≤-refl N)

  bdry-rank : ∀ sg {x} → x ∈L bdryT sg (homs Γ) → rank x ≤ N
  bdry-rank sg q with any-++⁻ (lowerT (N ∸ 1) (homs Γ)) q
  ... | inj₁ a = ≤-trans (≤-step (≤-refl _)) (≤-trans (lower-rank (N ∸ 1) a) (∸1≤ N))
  ... | inj₂ b = subst (_≤ N) (sym (chain-rank sg (N ∸ 1) b)) (∸1≤ N)

  -- Below entrywise means lower rank, in a graded context.
  rank-mono : Graded → ∀ {n s r} → Pw n s r → rank s ≤ rank r
  rank-mono G pnil = z≤n
  rank-mono G (pcons {a} k l lr p) =
    +-mono (subst (hgt a ≤_) (lr-rank G lr) (m≤m+n (hgt a) k)) (rank-mono G p)

  covers-rank : Graded → ∀ S F → T (covers Γ S F) → (∀ {x} → x ∈L F → rank x ≤ N) →
                ∀ {s} → s ∈L S → rank s ≤ N
  covers-rank G S F p okF {s} ms
    with any-witness (anyS⇒ (leqT cs N s) F (All-T (λ s → any (leqT cs N s) F) S p ms))
  ... | r , mr , q = ≤-trans (rank-mono G (leqT⇒ N s r q)) (okF mr)

------------------------------------------------------------------------
-- The four comparisons of the side condition, in a context whose
-- types are variable towers.

module PsSide (Θ : Ctx) (inv : Inv Θ) (B : Ty) (s s' t u : Tm) where
  open Ranks Θ
  private
    A  = arr B s s'
    hs = homs Θ
    G  = graded Θ inv

    clo : ∀ S F → (∀ {x} → x ∈L F → Faces.rank (cells Θ) x ≤ dimK hs) →
          T (sameDown Θ S F) → T (sameDownClosure Θ S F)
    clo S F okF p =
      subst T (sameDown≡Closure Θ G S F (covers-rank G S F (∧-fst {covers Θ S F} p) okF) okF) p

  coh-t : T (sameDown Θ (supp t A) (fullT hs)) → T (sameDownClosure Θ (supp t A) (fullT hs))
  coh-t = clo (supp t A) (fullT hs) full-rank

  coh-u : T (sameDown Θ (supp u A) (fullT hs)) → T (sameDownClosure Θ (supp u A) (fullT hs))
  coh-u = clo (supp u A) (fullT hs) full-rank

  op-t : T (sameDown Θ (supp t A) (bdryT false hs)) → T (sameDownClosure Θ (supp t A) (bdryT false hs))
  op-t = clo (supp t A) (bdryT false hs) (bdry-rank false)

  op-u : T (sameDown Θ (supp u A) (bdryT true hs)) → T (sameDownClosure Θ (supp u A) (bdryT true hs))
  op-u = clo (supp u A) (bdryT true hs) (bdry-rank true)
