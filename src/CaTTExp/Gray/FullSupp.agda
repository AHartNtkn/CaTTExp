------------------------------------------------------------------------
-- ↓Supp(T) is all of K(Γ), for every context Γ.
--
--   full-cover : InK (homs Γ) x → T (any (leqT (cells Γ) N x) (fullT (homs Γ)))
--
-- Every tuple x of cells, one from each hom, lies (entrywise, within
-- the face order of Gray.Support) below a tuple of Supp(T). This was
-- checked by evaluation for all pasting contexts with ≤ 5 edges
-- (Gray.Bounded); here it is proved for every context.
--
-- Proof: in one hom, every cell e is below a cell of ⟨Θ⟩^s_i for any
-- sign s (`up`): if e is the s-face of some (i+1)-cell w, go up to w,
-- otherwise e itself is in the table (at the top dimension every cell
-- is). Doing this entry by entry, with the signs the tensor formula
-- prescribes, gives a path through the tables, i.e. a tuple of
-- T^+_k for some k ≤ N, hence of Supp(T).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.FullSupp (𝕊 : Signature) where

open Signature 𝕊

open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.DownAgree 𝕊
open import CaTTExp.Gray.Graded 𝕊
open import CaTTExp.Gray.Orient 𝕊 using (chainε-false; flipIf)
open import CaTTExp.Gray.OrientRev 𝕊 using (Path; nil; cons; path⇐)

------------------------------------------------------------------------
-- Numbers.

private
  ≤-≠-< : ∀ a b → a ≤ b → (a ==ℕ b) ≡ false → T (a <ℕ b)
  ≤-≠-< zero    zero    _       ()
  ≤-≠-< zero    (suc b) _       _ = tt
  ≤-≠-< (suc a) (suc b) (s≤s l) q = ≤-≠-< a b l q

  <-≤-⊥ : ∀ a b → T (a <ℕ b) → b ≤ a → ⊥
  <-≤-⊥ zero    (suc b) _ ()
  <-≤-⊥ (suc a) (suc b) p (s≤s l) = <-≤-⊥ a b p l

  T≡ : ∀ {b} → T b → b ≡ true
  T≡ {true} _ = refl

  +≤-l : ∀ k a {n} → k + a ≤ n → k ≤ n
  +≤-l zero    a _       = z≤n
  +≤-l (suc k) a (s≤s l) = s≤s (+≤-l k a l)

  ≤-case : ∀ k m → k ≤ m → (k ≡ m) ⊎ (suc k ≤ m)
  ≤-case zero    zero    _       = inj₁ refl
  ≤-case zero    (suc m) _       = inj₂ (s≤s z≤n)
  ≤-case (suc k) (suc m) (s≤s l) with ≤-case k m l
  ... | inj₁ e = inj₁ (cong suc e)
  ... | inj₂ l' = inj₂ (s≤s l')

  max-≤l : ∀ a b → a ≤ max a b
  max-≤l zero    b       = z≤n
  max-≤l (suc a) zero    = ≤-refl (suc a)
  max-≤l (suc a) (suc b) = s≤s (max-≤l a b)

  max-≤r : ∀ a b → b ≤ max a b
  max-≤r zero    b       = ≤-refl b
  max-≤r (suc a) zero    = z≤n
  max-≤r (suc a) (suc b) = s≤s (max-≤r a b)

  maxL-ge : ∀ xs {x} → x ∈ᴺ xs → x ≤ maxL xs
  maxL-ge (y ∷ ys) (here refl) = max-≤l y (maxL ys)
  maxL-ge (y ∷ ys) (there m)   = ≤-trans (maxL-ge ys m) (max-≤r y (maxL ys))

  +-suc' : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc' zero    b = refl
  +-suc' (suc a) b = cong suc (+-suc' a b)

  +-mono' : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
  +-mono' {b = b} {d = d} z≤n q = ≤-trans q (n≤m+n b d)
  +-mono' (s≤s p) q = s≤s (+-mono' p q)

------------------------------------------------------------------------
-- Membership in one table piece.

-- The test of Support.piece: w has c as its s-face.
hitsF : Nat → Bool → El → El → Bool
hitsF i sg c w = (hdim w ==ℕ suc i) ∧ (if sg then (src w ==ℕ lvl c) else (tgt w ==ℕ lvl c))

private
  in-filter-map : ∀ (p : El → Bool) xs {e} → Any (e ≡_) xs → T (p e) → lvl e ∈ᴺ map lvl (filter p xs)
  in-filter-map p xs me pe =
    subst (Any _) (sym (map≡ lvl (filter p xs)))
      (any-map⁺ lvl (any-mono (λ { refl → refl }) (filter⇐ p xs me pe)))

piece-top-in : ∀ h s {e} → Any (e ≡_) (hcs h) → (hdim e ==ℕ hd h) ≡ true → lvl e ∈ᴺ piece h (hdim e) s
piece-top-in h s {e} me q rewrite q = in-filter-map (λ c → hdim c ==ℕ hdim e) (hcs h) me (==ℕ-refl (hdim e))

piece-low-in : ∀ h s {e} → Any (e ≡_) (hcs h) → (hdim e ==ℕ hd h) ≡ false → T (hdim e <ℕ hd h) →
               any (hitsF (hdim e) s e) (hcs h) ≡ false → lvl e ∈ᴺ piece h (hdim e) s
piece-low-in h s {e} me q lt qh rewrite q | T≡ lt =
  in-filter-map (λ c → (hdim c ==ℕ hdim e) ∧ not (any (hitsF (hdim e) s c) (hcs h))) (hcs h) me
    (∧-in (==ℕ-refl (hdim e)) (subst (λ b → T (not b)) (sym qh) tt))

------------------------------------------------------------------------
-- Going up inside one hom.

module _ (Γ : Ctx) where
  open Faces (cells Γ)

  private
    cs = cells Γ

  lr-snoc : ∀ {k b c a} → LR k b c → a ∈ᴺ bdEl cs c → LR (suc k) b a
  lr-snoc lz         m = ls m lz
  lr-snoc (ls mc lr) m = ls mc (lr-snoc lr m)

  module Up (h : Hom) (ok : Ranks.HomOK Γ h)
            (top : ∀ {e} → Any (e ≡_) (hcs h) → hdim e ≤ hd h) where

    private
      face-in : ∀ s {e w} → Any (w ≡_) (hcs h) → hdim w ≡ suc (hdim e) →
                T (if s then (src w ==ℕ lvl e) else (tgt w ==ℕ lvl e)) → lvl e ∈ᴺ bdEl cs (lvl w)
      face-in s {e} {w} mw hw p rewrite bd-just cs (lvl w) (findEl-mem Γ (ok mw)) | hw = pickS s p
        where
        pickS : ∀ s → T (if s then (src w ==ℕ lvl e) else (tgt w ==ℕ lvl e)) → lvl e ∈ᴺ (src w ∷ tgt w ∷ [])
        pickS true  p = here (sym (==ℕ-sound (src w) (lvl e) p))
        pickS false p = there (here (sym (==ℕ-sound (tgt w) (lvl e) p)))

    -- Every cell lies below a cell of the s-table at its own dimension.
    up : ∀ f s {e} → Any (e ≡_) (hcs h) → hd h ≤ f + hdim e →
         Σ El λ z → Any (z ≡_) (hcs h) × (lvl z ∈ᴺ piece h (hdim z) s) ×
         Σ Nat λ k → (k + hdim e ≤ hd h) × LR k (lvl z) (lvl e)
    up f s {e} me bnd with hdim e ==ℕ hd h in q1
    ... | true = e , me , piece-top-in h s me q1 , 0 , top me , lz
    ... | false with any (hitsF (hdim e) s e) (hcs h) in q2
    ...   | false = e , me , piece-low-in h s me q1 (≤-≠-< _ _ (top me) q1) q2 , 0 , top me , lz
    ...   | true with any-witness (anyS⇒ (hitsF (hdim e) s e) (hcs h) (subst T (sym q2) tt))
    ...     | w , mw , hw = go f bnd
      where
      hw' : hdim w ≡ suc (hdim e)
      hw' = ==ℕ-sound (hdim w) (suc (hdim e)) (∧-fst {hdim w ==ℕ suc (hdim e)} hw)
      fe : lvl e ∈ᴺ bdEl cs (lvl w)
      fe = face-in s {e} {w} mw hw' (∧-snd {hdim w ==ℕ suc (hdim e)} hw)
      go : ∀ f → hd h ≤ f + hdim e →
           Σ El λ z → Any (z ≡_) (hcs h) × (lvl z ∈ᴺ piece h (hdim z) s) ×
           Σ Nat λ k → (k + hdim e ≤ hd h) × LR k (lvl z) (lvl e)
      go zero    b = ⊥-elim (<-≤-⊥ (hdim e) (hd h) (≤-≠-< _ _ (top me) q1) b)
      go (suc f) b with up f s mw (subst (λ n → hd h ≤ f + n) (sym hw') (subst (hd h ≤_) (sym (+-suc' f (hdim e))) b))
      ... | z , mz , pz , k , kb , lr =
        z , mz , pz , suc k ,
        subst (_≤ hd h) (trans (cong (k +_) hw') (+-suc' k (hdim e))) kb ,
        lr-snoc lr fe

  ----------------------------------------------------------------------
  -- Tuples of K(Γ): one cell from each hom.

  data InK : List Hom → Tuple → Set where
    knil  : InK [] []
    kcons : ∀ {h hs e x} → Any (e ≡_) (hcs h) → InK hs x → InK (h ∷ hs) (lvl e ∷ x)

  private
    homs-top : ∀ {h} → Any (h ≡_) (homs Γ) → ∀ {e} → Any (e ≡_) (hcs h) → hdim e ≤ hd h
    homs-top m {e} me
      with any-witness (any-map⁻ (homAt Γ) _ (subst (Any _) (map≡ (homAt Γ) _) m))
    ... | k , _ , refl =
      maxL-ge (map hdim (hcs (homAt Γ k)))
        (subst (Any _) (sym (map≡ hdim (hcs (homAt Γ k)))) (any-map⁺ hdim (any-mono (λ { refl → refl }) me)))

    cover-path : ∀ hs n → (∀ {h} → Any (h ≡_) hs → Any (h ≡_) (homs Γ)) → sumL (map hd hs) ≤ n →
                 ∀ s {x} → InK hs x →
                 Σ Tuple λ τ → Σ (List Nat) λ is → Path (λ _ → false) s hs is τ ×
                 (sumL is ≤ sumL (map hd hs)) × Pw n x τ
    cover-path []       n sub sb s knil = [] , [] , nil , z≤n , pnil
    cover-path (h ∷ hs) n sub sb s (kcons me kx)
      with Up.up h (Ranks.homs-ok Γ (sub (here refl))) (homs-top (sub (here refl))) (hd h) s me
                 (≤-trans (m≤m+n (hd h) _) (≤-refl _))
    ... | z , mz , pz , k , kb , lr
      with cover-path hs n (λ m → sub (there m)) (≤-trans (n≤m+n (hd h) _) sb) (flipIf (odd (hdim z)) s) kx
    ...   | τ , is , p , ib , pw =
      lvl z ∷ τ , hdim z ∷ is , cons pz p , +-mono' (homs-top (sub (here refl)) mz) ib ,
      pcons k (≤-trans (+≤-l k _ kb) (≤-trans (m≤m+n (hd h) _) sb)) lr pw

    chain-lower : ∀ m k {hs x} → suc k ≤ m → x ∈L chainT true k hs → x ∈L lowerT m hs
    chain-lower (suc m) k {hs} (s≤s l) mx with ≤-case k m l
    ... | inj₁ refl = any-++r (lowerT k hs) (any-++r (chainT false k hs) mx)
    ... | inj₂ l'   = any-++l (chain-lower m k l' mx)

  -- ↓Supp(T) is all of K(Γ).
  full-cover : ∀ {x} → InK (homs Γ) x → T (any (leqT cs (dimK (homs Γ)) x) (fullT (homs Γ)))
  full-cover {x} kx with cover-path (homs Γ) (dimK (homs Γ)) (λ m → m) (≤-refl _) true kx
  ... | τ , is , p , ib , pw =
    anyS⇐ (leqT cs N x) (fullT (homs Γ)) (any-mono (λ { refl → leqT⇐ pw }) inFull)
    where
    N = dimK (homs Γ)
    inChain : τ ∈L chainT true (sumL is) (homs Γ)
    inChain = subst (λ L → τ ∈L L) (chainε-false true (sumL is) (homs Γ)) (path⇐ (λ _ → false) p)
    inFull : τ ∈L fullT (homs Γ)
    inFull with ≤-case (sumL is) N ib
    ... | inj₁ e = any-++r (lowerT N (homs Γ)) (subst (λ k → τ ∈L chainT true k (homs Γ)) e inChain)
    ... | inj₂ l = any-++l (chain-lower N (sumL is) l inChain)
