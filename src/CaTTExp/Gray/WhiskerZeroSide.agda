------------------------------------------------------------------------
-- Two-tier L accepts the right whisker heads of CaTTExp.Derived for
-- k = 0 (step 2(d) of the two-tier L whiskering interface,
-- notes/surface-conservativity.md §7; k ≥ 1 is Gray.WhiskerSide).
--
--   gside-BK0-0  : graySide accepts (BK 0 0,     wK 0 0)
--   gside-BK-0 j : graySide accepts (BK 0 (j+1), wK 0 (j+1))
--
-- BK 0 (j+1) is W(Dⁿ) = Dⁿ⁺¹ ▸ z ▸ h (Gray.WhiskerZero), n = j+1, and
-- the sides of its head are the whiskers by h of the source and target
-- s, t : aL n of the top cell of Dⁿ⁺¹ = ΣDⁿ. Proof, by induction on j,
-- together with the L-typing of the heads (g0wK-wf):
--  * supports (Ttop, U): the top support of a whisker side is (c, h)
--    for c the face of the top cell (the top of a disk is its one top
--    cell, topDsk⇒/⇐), and the type supports are those of aL n with h
--    appended; so supp(side) has the same tuples as supp(s : aL n)
--    with h appended;
--  * on the disk, s, t satisfy the operation condition
--    (Gray.SingleHomSide.op-side, Finster–Mimram's isOp for Dⁿ⁺¹);
--  * Gray.WhiskerZero carries sameDown and the boundary tables along
--    x ↦ x ++ (h), so the operation case holds on BK 0 (j+1);
--  * the coherence case is false (NoCoh): it would put the source
--    above dim K (Gray.CohDim.cohB<), and the support computation
--    needs this for the heads below.
-- The left whisker heads LK 0 (j+1) are Gray.WhiskerZeroLeftSide.
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerZeroSide where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Cover using (Any; here; there; any-witness; any-at; any-++⁻; any-++l; any-++r;
                                      any-map⁻; any-map⁺; any-cm⁻; any-cm⁺; _⊎_; inj₁; inj₂; T-All; All-T; ∧-in; ∨-inl; ∨-inr)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; anyS⇒; anyS⇐; map≡; cm≡; filter⇒; filter⇐)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; S; lenΣ)
open import CaTTExp.Gray.SingleHom ∅ using (mkC; hΣ; hcsΣ; hdΣ; homsΣ; cell-shape; cell-in; chain1⇒; chain1⇐)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (dim-aL; <-suc; n<sn)
import CaTTExp.Derived as D
open D using (nB; zK; BK; wK; ρK; ρsK; ρtK; Sph; Dsk; sphSub; lenₛ-sphL)
open import CaTTExp.Typing ∅ using (cattSide; isOp)
import CaTTExp.Subst as SubstM
open import CaTTExp.Gray.SingleHom ∅ using (objsΣ; dimKΣ)
open import CaTTExp.Gray.SingleHomSide using (op-side)
open import CaTTExp.Gray.PsFacts ∅ using (ps-facts; PsFacts)
open import CaTTExp.Gray.MarksFuel ∅ using (SigOK)
open import CaTTExp.Strict.Hyp using (closed)
import CaTTExp.Gray.CohDim ∅ as CD
open import CaTTExp.Gray.Cover using (_≤_; s≤s)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Gray.WhiskerSigma using (Σ-Dsk)
open import CaTTExp.Gray.WhiskerZero
open import CaTTExp.Strict.Subst using (nth-topsSub)

------------------------------------------------------------------------
-- Generalities.

private
  +-zero : ∀ a → a + 0 ≡ a
  +-zero zero    = refl
  +-zero (suc a) = cong suc (+-zero a)

  ==ℕ-≡ : ∀ n → (n ==ℕ n) ≡ true
  ==ℕ-≡ zero    = refl
  ==ℕ-≡ (suc n) = ==ℕ-≡ n

  lt-irr : ∀ n → T (n <ℕ n) → ⊥
  lt-irr (suc n) p = lt-irr n p

  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  map⇒ : ∀ {A B : Set} (f : A → B) xs {y} → Any (y ≡_) (map f xs) → Σ A λ x → Any (x ≡_) xs × (y ≡ f x)
  map⇒ f xs m = any-witness (any-map⁻ f xs (subst (Any _) (map≡ f xs) m))

  map⇐ : ∀ {A B : Set} (f : A → B) xs {x} → Any (x ≡_) xs → Any (f x ≡_) (map f xs)
  map⇐ f xs {x} m = subst (Any (f x ≡_)) (sym (map≡ f xs)) (any-map⁺ f (any-at m refl))

-- S ⊑ R: every tuple of S is a tuple of R.
_⊑_ : TSet → TSet → Set
S ⊑ R = ∀ {x} → x ∈L S → x ∈L R

covers-⊑ : ∀ Γ {S S′ R R′} → S′ ⊑ S → R ⊑ R′ → T (covers Γ S R) → T (covers Γ S′ R′)
covers-⊑ Γ {S} {S′} {R} {R′} sS rR c =
  T-All (λ s → any (leqT cs N s) R′) S′ λ {s} ms →
    go {s} (any-witness (anyS⇒ (leqT cs N s) R (All-T (λ s → any (leqT cs N s) R) S c (sS ms))))
  where
  cs = cells Γ
  N  = dimK (homs Γ)
  go : ∀ {s} → (Σ Tuple λ r → Any (r ≡_) R × T (leqT cs N s r)) → T (any (leqT cs N s) R′)
  go {s} (r , mr , q) = anyS⇐ (leqT cs N s) R′ (any-at (rR mr) q)

sameDown-⊑ : ∀ Γ {S S′ R R′} → S′ ⊑ S → S ⊑ S′ → R ⊑ R′ → R′ ⊑ R →
             T (sameDown Γ S R) → T (sameDown Γ S′ R′)
sameDown-⊑ Γ {S} {S′} {R} {R′} a b c d p =
  ∧-in (covers-⊑ Γ a c (∧-fst {covers Γ S R} p)) (covers-⊑ Γ d b (∧-snd {covers Γ S R} p))

------------------------------------------------------------------------
-- The top of a disk: one cell.

private
  sph-lt : ∀ m v {A} → lookup (Sph m) v ≡ just A → T (dim A <ℕ m)
  sph-lt zero    v ()
  sph-lt (suc k) v {A} e with v ==ℕ len (Sph k ▸ aL k)
  ... | true  rewrite sym (just-inj e) | dim-aL k = n<sn k
  ... | false with v ==ℕ len (Sph k)
  ...   | true  rewrite sym (just-inj e) | dim-aL k = n<sn k
  ...   | false = <-suc (dim A) k (sph-lt k v e)

  dsk-uniq : ∀ m v {A} → lookup (Dsk m) v ≡ just A → dim A ≡ m → v ≡ dbl m
  dsk-uniq m v {A} e d with v ==ℕ len (Sph m) in q
  ... | true  = trans (==ℕ-sound v _ (subst T (sym q) tt)) (D.len-Sph m)
  ... | false = ⊥-elim (lt-irr m (subst (λ n → T (n <ℕ m)) d (sph-lt m v e)))

  lk-dsk-top : ∀ m → lookup (Dsk m) (dbl m) ≡ just (aL m)
  lk-dsk-top m = subst (λ i → lookup (Dsk m) i ≡ just (aL m)) (D.len-Sph m) (D.last-lookup (Sph m) (aL m))

module _ (m : Nat) where

  private
    Θ = Dsk m
    h = hΣ Θ
    P : El → Bool
    P c = hdim c ==ℕ hd h

    hd≡ : hd h ≡ m
    hd≡ = trans (hdΣ Θ) (D.dimCtx-Dsk m)

    topH : topT (homs (Σctx Θ)) ≡ chainT true (hd h) (h ∷ [])
    topH rewrite homsΣ Θ = cong (λ k → chainT true k (h ∷ [])) (+-zero (hd h))

    pieceTop : piece h (hd h) true ≡ map lvl (filter P (hcs h))
    pieceTop rewrite ==ℕ-≡ (hd h) = refl

  topDsk⇒ : ∀ {x} → x ∈L topT (homs (Σctx Θ)) → x ≡ S (dbl m) ∷ []
  topDsk⇒ mx with chain1⇒ h true (hd h) (subst (λ L → _ ∈L L) topH mx)
  ... | b , refl , pb with map⇒ lvl (filter P (hcs h)) (subst (λ L → b ∈ᴺ L) pieceTop pb)
  ...   | e , me , refl with filter⇒ P (hcs h) me
  ...     | me′ , pe with cell-shape Θ (subst (λ L → Any (e ≡_) L) (hcsΣ Θ) me′)
  ...       | v , A , lv , refl =
    cong (λ v → S v ∷ []) (dsk-uniq m v lv (trans (==ℕ-sound (dim A) (hd h) pe) hd≡))

  topDsk⇐ : (S (dbl m) ∷ []) ∈L topT (homs (Σctx Θ))
  topDsk⇐ =
    subst (λ L → (S (dbl m) ∷ []) ∈L L) (sym topH)
      (chain1⇐ h true (hd h)
        (subst (λ L → S (dbl m) ∈ᴺ L) (sym pieceTop)
          (map⇐ lvl (filter P (hcs h))
            (filter⇐ P (hcs h) (subst (λ L → Any (mkC (dbl m , aL m) ≡_) L) (sym (hcsΣ Θ)) (cell-in Θ (dbl m) (lk-dsk-top m)))
                     (subst T (sym (trans (cong (dim (aL m) ==ℕ_) hd≡) (trans (cong (_==ℕ m) (dim-aL m)) (==ℕ-≡ m)))) tt)))))

------------------------------------------------------------------------
-- Same tuples.

_≋_ : TSet → TSet → Set
S ≋ R = (S ⊑ R) × (R ⊑ S)

≋-refl : ∀ {S} → S ≋ S
≋-refl = (λ m → m) , (λ m → m)

≡→≋ : ∀ {S R} → S ≡ R → S ≋ R
≡→≋ refl = ≋-refl

≋-sym : ∀ {S R} → S ≋ R → R ≋ S
≋-sym (a , b) = b , a

≋-trans : ∀ {S R Q} → S ≋ R → R ≋ Q → S ≋ Q
≋-trans (a , b) (c , d) = (λ m → c (a m)) , (λ m → b (d m))

private
  ⊑-++ : ∀ {S S′ R R′} → S ⊑ S′ → R ⊑ R′ → (S ++ R) ⊑ (S′ ++ R′)
  ⊑-++ {S} {S′} a b m with any-++⁻ S m
  ... | inj₁ l = any-++l (a l)
  ... | inj₂ r = any-++r S′ (b r)

≋-++ : ∀ {S S′ R R′} → S ≋ S′ → R ≋ R′ → (S ++ R) ≋ (S′ ++ R′)
≋-++ (a , b) (c , d) = ⊑-++ a c , ⊑-++ b d

------------------------------------------------------------------------
-- BK 0 j is W (Dsk j), and its top is (c, h) for c the top cell of the
-- disk and h the whisker.

cJ hJ : Nat → Nat
cJ j = dbl (nB 0 j)
hJ j = suc (zK 0 j)

eqW : ∀ j → W (Dsk (j + 0)) ≡ BK 0 j
eqW j = trans (cong (λ Γ → Γ ▸ ⋆ ▸ hT (len Γ)) (Σ-Dsk (j + 0)))
              (cong (λ L → Dsk (suc (j + 0)) ▸ ⋆ ▸ hT L) (D.len-Dsk (suc (j + 0))))

hl≡ : ∀ j → hl (Dsk (j + 0)) ≡ hJ j
hl≡ j = cong suc (trans (lenΣ (Dsk (j + 0))) (cong S (D.len-Dsk (j + 0))))

topBK⇒ : ∀ j {x} → x ∈L topT (homs (BK 0 j)) → x ≡ cJ j ∷ hJ j ∷ []
topBK⇒ j {x} mx
  with map⇒ (app (Dsk (j + 0))) _
         (subst (λ L → x ∈L L) (topW (Dsk (j + 0))) (subst (λ Γ → x ∈L topT (homs Γ)) (sym (eqW j)) mx))
... | y , my , refl rewrite topDsk⇒ (j + 0) my = cong (λ n → cJ j ∷ n ∷ []) (hl≡ j)

topBK⇐ : ∀ j → (cJ j ∷ hJ j ∷ []) ∈L topT (homs (BK 0 j))
topBK⇐ j =
  subst (λ Γ → (cJ j ∷ hJ j ∷ []) ∈L topT (homs Γ)) (eqW j)
    (subst (λ L → (cJ j ∷ hJ j ∷ []) ∈L L) (sym (topW (Dsk (j + 0))))
      (subst (λ n → (cJ j ∷ n ∷ []) ∈L map (app (Dsk (j + 0))) (topT (homs (Σctx (Dsk (j + 0))))))
             (hl≡ j) (map⇐ (app (Dsk (j + 0))) _ (topDsk⇐ (j + 0)))))

------------------------------------------------------------------------
-- The top support of coh (BK 0 j) (wK 0 j) σ, for σ sending the top
-- cell and the whisker to variables.

NoCoh : Nat → Set
NoCoh zero    = ⊤
NoCoh (suc j) = cohCase (BK 0 (suc j)) (wK 0 j [ ρsK 0 j ]ty)
                        (coh (BK 0 j) (wK 0 j) (ρsK 0 j)) (coh (BK 0 j) (wK 0 j) (ρtK 0 j)) ≡ false

NCs : Nat → Set
NCs zero    = ⊤
NCs (suc j) = NCs j × NoCoh j

private
  topS-coh : ∀ j σ → NoCoh j → topS (coh (BK 0 j) (wK 0 j) σ) ≡ applyF (topsSub σ) (topT (homs (BK 0 j)))
  topS-coh zero    σ _  = refl
  topS-coh (suc j) σ nc rewrite nc = refl

  Fpair : ∀ σ c h {c′ h′} → T (c <ℕ lenₛ σ) → T (h <ℕ lenₛ σ) → lookupₛ σ c ≡ var c′ → lookupₛ σ h ≡ var h′ →
          Ftuple (topsSub σ) (c ∷ h ∷ []) ≡ (c′ ∷ h′ ∷ []) ∷ []
  Fpair σ c h lc lh ec eh rewrite nth-topsSub σ c lc | nth-topsSub σ h lh | ec | eh = refl

  ltBK : ∀ j σ i → lenₛ σ ≡ len (BK 0 j) → T (i <ℕ suc (suc (suc (cJ j)))) → T (i <ℕ lenₛ σ)
  ltBK j σ i e p rewrite e | D.len-Dsk (nB 0 j) = p

  cJ<h : ∀ j → T (cJ j <ℕ suc (suc (suc (cJ j))))
  cJ<h j = <-suc (cJ j) (suc (suc (cJ j))) (<-suc (cJ j) (suc (cJ j)) (n<sn (cJ j)))

  hJ<h : ∀ j → T (hJ j <ℕ suc (suc (suc (cJ j))))
  hJ<h j = n<sn (hJ j)

Ttop : ∀ j σ {c′ h′} → NoCoh j → lenₛ σ ≡ len (BK 0 j) → lookupₛ σ (cJ j) ≡ var c′ → lookupₛ σ (hJ j) ≡ var h′ →
       topS (coh (BK 0 j) (wK 0 j) σ) ≋ ((c′ ∷ h′ ∷ []) ∷ [])
Ttop j σ {c′} {h′} nc e ec eh =
  (λ {x} mx → fwd x (subst (λ L → x ∈L L) (topS-coh j σ nc) mx)) ,
  (λ { (here refl) → subst (λ L → (c′ ∷ h′ ∷ []) ∈L L) (sym (topS-coh j σ nc)) bwd ; (there ()) })
  where
  R = topsSub σ
  C = topT (homs (BK 0 j))
  F≡ : Ftuple R (cJ j ∷ hJ j ∷ []) ≡ (c′ ∷ h′ ∷ []) ∷ []
  F≡ = Fpair σ (cJ j) (hJ j) (ltBK j σ (cJ j) e (cJ<h j)) (ltBK j σ (hJ j) e (hJ<h j)) ec eh
  fwd : ∀ x → x ∈L applyF R C → x ∈L ((c′ ∷ h′ ∷ []) ∷ [])
  fwd x mx with any-witness (any-cm⁻ (Ftuple R) C (subst (λ L → x ∈L L) (cm≡ (Ftuple R) C) mx))
  ... | y , my , mF rewrite topBK⇒ j my = subst (λ L → x ∈L L) F≡ mF
  bwd : (c′ ∷ h′ ∷ []) ∈L applyF R C
  bwd = subst (λ L → (c′ ∷ h′ ∷ []) ∈L L) (sym (cm≡ (Ftuple R) C))
          (any-cm⁺ (Ftuple R) (any-at (topBK⇐ j) (subst (λ L → (c′ ∷ h′ ∷ []) ∈L L) (sym F≡) (here refl))))

------------------------------------------------------------------------
-- The faces ρK 0 j v.

private
  lk3lt : ∀ X a b c i → T (i <ℕ lenₛ X) → lookupₛ (X ,ₛ a ,ₛ b ,ₛ c) i ≡ lookupₛ X i
  lk3lt X a b c i p =
    trans (D.lk-ext (X ,ₛ a ,ₛ b) c i (<-suc i (suc (lenₛ X)) (<-suc i (lenₛ X) p)))
      (trans (D.lk-ext (X ,ₛ a) b i (<-suc i (lenₛ X) p)) (D.lk-ext X a i p))

  lk3a : ∀ X a b c → lookupₛ (X ,ₛ a ,ₛ b ,ₛ c) (lenₛ X) ≡ a
  lk3a X a b c =
    trans (D.lk-ext (X ,ₛ a ,ₛ b) c (lenₛ X) (<-suc (lenₛ X) (suc (lenₛ X)) (n<sn (lenₛ X))))
      (trans (D.lk-ext (X ,ₛ a) b (lenₛ X) (n<sn (lenₛ X))) (D.lk-top X a))

  lk3b : ∀ X a b c → lookupₛ (X ,ₛ a ,ₛ b ,ₛ c) (suc (lenₛ X)) ≡ b
  lk3b X a b c =
    trans (D.lk-ext (X ,ₛ a ,ₛ b) c (suc (lenₛ X)) (n<sn (suc (lenₛ X)))) (D.lk-top (X ,ₛ a) b)

  lk3c : ∀ X a b c → lookupₛ (X ,ₛ a ,ₛ b ,ₛ c) (suc (suc (lenₛ X))) ≡ c
  lk3c X a b c = D.lk-top (X ,ₛ a ,ₛ b) c

lkρ-lt : ∀ j v i → T (i <ℕ cJ j) → lookupₛ (ρK 0 j v) i ≡ var i
lkρ-lt j v i p =
  trans (lk3lt (sphSub (aL (nB 0 j))) _ _ _ i (subst (λ L → T (i <ℕ L)) (sym (lenₛ-sphL (nB 0 j))) p))
        (D.lk-sph (nB 0 j) i p)

lkρ-c : ∀ j v → lookupₛ (ρK 0 j v) (cJ j) ≡ var v
lkρ-c j v = subst (λ L → lookupₛ (ρK 0 j v) L ≡ var v) (lenₛ-sphL (nB 0 j)) (lk3a (sphSub (aL (nB 0 j))) _ _ _)

lkρ-z : ∀ j v → lookupₛ (ρK 0 j v) (zK 0 j) ≡ var (zK 0 (suc j))
lkρ-z j v = subst (λ L → lookupₛ (ρK 0 j v) (suc L) ≡ var (zK 0 (suc j))) (lenₛ-sphL (nB 0 j))
              (lk3b (sphSub (aL (nB 0 j))) _ _ _)

lkρ-h : ∀ j v → lookupₛ (ρK 0 j v) (hJ j) ≡ var (hJ (suc j))
lkρ-h j v = subst (λ L → lookupₛ (ρK 0 j v) (suc (suc L)) ≡ var (hJ (suc j))) (lenₛ-sphL (nB 0 j))
              (lk3c (sphSub (aL (nB 0 j))) _ _ _)

ltρ : ∀ j v i → T (i <ℕ suc (suc (suc (cJ j)))) → T (i <ℕ lenₛ (ρK 0 j v))
ltρ j v i p = subst (λ L → T (i <ℕ suc (suc (suc L)))) (sym (lenₛ-sphL (nB 0 j))) p

∘lk : ∀ τ σ i {w t} → T (i <ℕ lenₛ τ) → lookupₛ τ i ≡ var w → lookupₛ σ w ≡ t → lookupₛ (τ ∘ σ) i ≡ t
∘lk τ σ i p e e′ = trans (Sb.lookupₛ-∘ τ σ i p) (trans (cong (_[ σ ]tm) e) e′)

------------------------------------------------------------------------
-- The type supports.

private
  map-++ : ∀ {A B : Set} (g : A → B) xs ys → map g (xs ++ ys) ≡ map g xs ++ map g ys
  map-++ g []       ys = refl
  map-++ g (x ∷ xs) ys = cong (g x ∷_) (map-++ g xs ys)

  sT : ∀ A t u → (A ≡ ⋆ → ⊥) → suppTy (arr A t u) ≡ suppTy A ++ (topS t ++ topS u)
  sT ⋆            t u ne = ⊥-elim (ne refl)
  sT (arr B s s′) t u ne = refl

  ty⋆ : ∀ A σ → A [ σ ]ty ≡ ⋆ → A ≡ ⋆
  ty⋆ ⋆           σ _ = refl
  ty⋆ (arr A t u) σ ()

  wK≢⋆ : ∀ j → wK 0 j ≡ ⋆ → ⊥
  wK≢⋆ zero    ()
  wK≢⋆ (suc j) ()

  lt2 : ∀ i n → T (i <ℕ n) → T (i <ℕ suc (suc n))
  lt2 i n p = <-suc i (suc n) (<-suc i n p)

  lt3 : ∀ i n → T (i <ℕ n) → T (i <ℕ suc (suc (suc n)))
  lt3 i n p = <-suc i (suc (suc n)) (lt2 i n p)

  scW : ∀ j v → Sb.ScTy (lenₛ (ρK 0 j v)) (wK 0 j)
  scW j v = D.sc-ρK 0 j v (Sb.ty-sc D.closed (D.wK-wf 0 j))

U : ∀ j σ {h′} → NCs j → lenₛ σ ≡ len (BK 0 j) → (∀ i → T (i <ℕ cJ j) → lookupₛ σ i ≡ var i) →
    lookupₛ σ (hJ j) ≡ var h′ → suppTy (wK 0 j [ σ ]ty) ≋ map (_++ (h′ ∷ [])) (suppTy (aL (nB 0 j)))
U zero    σ _ _ _ _ = ≋-refl
U (suc j) σ {h′} (ncs , nc) e lo lh =
  ≋-trans (≡→≋ (trans (sT (wK 0 j [ ρs ]ty [ σ ]ty) _ _ (λ q → wK≢⋆ j (ty⋆ (wK 0 j) ρs (ty⋆ _ σ q))))
                      (cong (λ A → suppTy A ++ (topS (coh (BK 0 j) (wK 0 j) τs) ++ topS (coh (BK 0 j) (wK 0 j) τt))) (Sb.assoc-ty (wK 0 j) ρs σ (scW j (cJ j))))))
  (≋-trans (≋-++ (U j τs ncs eτs loτ lhτs)
                 (≋-++ (Ttop j τs nc eτs ecs lhτs) (Ttop j τt nc eτt ect lhτt)))
           (≡→≋ (sym (map-++ (_++ (h′ ∷ [])) (suppTy (aL n)) _))))
  where
  n  = nB 0 j
  ρs = ρsK 0 j
  ρt = ρtK 0 j
  τs = ρs ∘ σ
  τt = ρt ∘ σ
  eτs : lenₛ τs ≡ len (BK 0 j)
  eτs = trans (Sb.lenₛ-∘ ρs σ) (D.lenρK 0 j (cJ j))
  eτt : lenₛ τt ≡ len (BK 0 j)
  eτt = trans (Sb.lenₛ-∘ ρt σ) (D.lenρK 0 j (suc (cJ j)))
  loτ : ∀ i → T (i <ℕ cJ j) → lookupₛ τs i ≡ var i
  loτ i p = ∘lk ρs σ i (ltρ j (cJ j) i (lt3 i (cJ j) p)) (lkρ-lt j (cJ j) i p) (lo i (lt2 i (cJ j) p))
  lhτs : lookupₛ τs (hJ j) ≡ var h′
  lhτs = ∘lk ρs σ (hJ j) (ltρ j (cJ j) (hJ j) (hJ<h j)) (lkρ-h j (cJ j)) lh
  lhτt : lookupₛ τt (hJ j) ≡ var h′
  lhτt = ∘lk ρt σ (hJ j) (ltρ j (suc (cJ j)) (hJ j) (hJ<h j)) (lkρ-h j (suc (cJ j))) lh
  ecs : lookupₛ τs (cJ j) ≡ var (cJ j)
  ecs = ∘lk ρs σ (cJ j) (ltρ j (cJ j) (cJ j) (cJ<h j)) (lkρ-c j (cJ j)) (lo (cJ j) (<-suc (cJ j) (suc (cJ j)) (n<sn (cJ j))))
  ect : lookupₛ τt (cJ j) ≡ var (suc (cJ j))
  ect = ∘lk ρt σ (cJ j) (ltρ j (suc (cJ j)) (cJ j) (cJ<h j)) (lkρ-c j (suc (cJ j))) (lo (suc (cJ j)) (n<sn (suc (cJ j))))

------------------------------------------------------------------------
-- Ends and dimension of the whisker types.

private
  endsTy-arr : ∀ A t u → (A ≡ ⋆ → ⊥) → endsTy (arr A t u) ≡ endsTy A
  endsTy-arr ⋆            t u ne = ⊥-elim (ne refl)
  endsTy-arr (arr B s s′) t u ne = refl

  dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
  dim-[] ⋆           σ = refl
  dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

dim-wK0 : ∀ j → dim (wK 0 j) ≡ nB 0 j
dim-wK0 zero    = refl
dim-wK0 (suc j) = cong suc (trans (dim-[] (wK 0 j) (ρsK 0 j)) (dim-wK0 j))

E : ∀ j σ → endsTy (wK 0 j [ σ ]ty) ≡ just (lookupₛ σ 0 , lookupₛ σ (zK 0 j))
E zero    σ = refl
E (suc j) σ =
  trans (endsTy-arr (wK 0 j [ ρs ]ty [ σ ]ty) _ _ (λ q → wK≢⋆ j (ty⋆ (wK 0 j) ρs (ty⋆ _ σ q))))
  (trans (cong endsTy (Sb.assoc-ty (wK 0 j) ρs σ (scW j (cJ j))))
  (trans (E j (ρs ∘ σ))
         (cong₂ (λ a b → just (a , b))
                (trans (Sb.lookupₛ-∘ ρs σ 0 (ltρ j (cJ j) 0 tt)) (cong (_[ σ ]tm) (lkρ-lt j (cJ j) 0 tt)))
                (trans (Sb.lookupₛ-∘ ρs σ (zK 0 j) (ltρ j (cJ j) (zK 0 j) (<-suc (zK 0 j) (suc (zK 0 j)) (n<sn (zK 0 j)))))
                       (cong (_[ σ ]tm) (lkρ-z j (cJ j)))))))
  where ρs = ρsK 0 j

------------------------------------------------------------------------
-- The operation condition on the disk Dⁿ⁺¹ = Σ Dⁿ, for its top cell
-- c : s → t: the two sides s, t : aL n.

private
  closedL : SubstM.Closed ∅ graySide
  closedL ()

open import CaTTExp.DerivedWithBase graySide closedL using (ps-wf; tm-ty; wBK; ρK-wf)

private
  dskPs : ∀ n → Dsk n ⊢ps
  dskPs n = ps (snd (D.toStar n (dbl n) (D.dsk-ps n)))

  srcD : ∀ n → ∂⁻ (Dsk (suc n)) ≡ snoc (D.upTo (dbl n)) (dbl n)
  srcD n rewrite D.dimCtx-Dsk (suc n) = D.src-Dsk-top n

  tgtD : ∀ n → ∂⁺ (Dsk (suc n)) ≡ snoc (D.upTo (dbl n)) (suc (dbl n))
  tgtD n rewrite D.dimCtx-Dsk (suc n) = D.tgt-Dsk-top n

  opDsk : ∀ n → T (isOp (Dsk (suc n)) (aL n) (var (dbl n)) (var (suc (dbl n))))
  opDsk n =
    ∧-in (D.subst₂ (λ X L → T (≈? (dbl n ∷ X) L)) (sym (D.fvTy-aL n)) (sym (srcD n))
                   (D.≈-cons-snoc (dbl n) (D.upTo (dbl n))))
         (D.subst₂ (λ X L → T (≈? (suc (dbl n) ∷ X) L)) (sym (D.fvTy-aL n)) (sym (tgtD n))
                   (D.≈-cons-snoc (suc (dbl n)) (D.upTo (dbl n))))

  dsrc : ∀ n → Dsk (suc n) ⊢tm var (dbl n) ∶ aL n
  dsrc n with tm-ty (snd (ps-wf (D.dsk-ps (suc n))))
  ... | arr-wf d _ = d

  dtgt : ∀ n → Dsk (suc n) ⊢tm var (suc (dbl n)) ∶ aL n
  dtgt n with tm-ty (snd (ps-wf (D.dsk-ps (suc n))))
  ... | arr-wf _ d = d

  endsTy-aL : ∀ m → endsTy (aL (suc m)) ≡ just (var 0 , var 1)
  endsTy-aL zero    = refl
  endsTy-aL (suc m) = endsTy-aL m

  endsOK-ty : ∀ Γ A {a b} → endsTy A ≡ just (a , b) →
              endsOK Γ A ≡ (isVarAt a (firstL (objs Γ)) ∧ isVarAt b (lastL (objs Γ)))
  endsOK-ty Γ A e rewrite e = refl

  opParts : ∀ Γ B p q t u → T (opCase Γ (arr B p q) t u) →
            T (sameDown Γ (supp t (arr B p q)) (bdryT false (homs Γ))) ×
            T (sameDown Γ (supp u (arr B p q)) (bdryT true (homs Γ)))
  opParts Γ B p q t u o =
    ∧-fst {sameDown Γ (supp t A) (bdryT false (homs Γ))} r , ∧-snd {sameDown Γ (supp t A) (bdryT false (homs Γ))} r
    where
    A = arr B p q
    r = ∧-snd {dim A ==ℕ dimK (homs Γ)} (∧-snd {endsOK Γ A} o)

module _ (m : Nat) where

  private
    n = suc m
    Γ = Σctx (Dsk n)

    tr : ∀ {t A} → Dsk (suc n) ⊢tm t ∶ A → Γ ⊢tm t ∶ A
    tr {t} {A} = subst (λ Δ → Δ ⊢tm t ∶ A) (sym (Σ-Dsk n))

    ok : T (endsOK Γ (aL n))
    ok = subst T (sym (trans (endsOK-ty Γ (aL n) (endsTy-aL m))
                             (cong (λ L → isVarAt (var 0) (firstL L) ∧ isVarAt (var 1) (lastL L)) (objsΣ (Dsk n)))))
               tt

    opD : T (opCase Γ (aL n) (var (dbl n)) (var (suc (dbl n))))
    opD = op-side (dskPs n) (subst (λ k → T (0 <ℕ k)) (sym (D.dimCtx-Dsk n)) tt) (tr (dsrc n)) (tr (dtgt n)) ok
                  (trans (dim-aL n) (sym (D.dimCtx-Dsk n)))
                  (subst (λ Δ → T (isOp Δ (aL n) (var (dbl n)) (var (suc (dbl n))))) (sym (Σ-Dsk n)) (opDsk n))

  sdDsk⁻ : T (sameDown Γ (supp (var (dbl n)) (aL n)) (bdryT false (homs Γ)))
  sdDsk⁻ = fst (opParts Γ (aL m) (var (dbl m)) (var (suc (dbl m))) (var (dbl n)) (var (suc (dbl n))) opD)

  sdDsk⁺ : T (sameDown Γ (supp (var (suc (dbl n))) (aL n)) (bdryT true (homs Γ)))
  sdDsk⁺ = snd (opParts Γ (aL m) (var (dbl m)) (var (suc (dbl m))) (var (dbl n)) (var (suc (dbl n))) opD)

------------------------------------------------------------------------
-- The side condition of the head (0, j+1): operation case.

private
  ≡⊑ : ∀ {S R} → S ≡ R → S ⊑ R
  ≡⊑ refl m = m

  opCase-intro : ∀ Γ A t u → (A ≡ ⋆ → ⊥) → T (endsOK Γ A) → dim A ≡ dimK (homs Γ) →
                 T (sameDown Γ (supp t A) (bdryT false (homs Γ))) → T (sameDown Γ (supp u A) (bdryT true (homs Γ))) →
                 T (opCase Γ A t u)
  opCase-intro Γ ⋆            t u ne _  _  _ _ = ⊥-elim (ne refl)
  opCase-intro Γ (arr B p q) t u ne ok dA s₁ s₂ =
    ∧-in ok (∧-in (subst (λ k → T (suc (dim B) ==ℕ k)) dA (==ℕ-refl (suc (dim B)))) (∧-in s₁ s₂))

module _ (j : Nat) (ncs : NCs j) (nc : NoCoh j) where

  private
    n  = nB 0 j
    Γw = W (Dsk n)
    ρs = ρsK 0 j
    ρt = ρtK 0 j
    A  = wK 0 j [ ρs ]ty
    ts = coh (BK 0 j) (wK 0 j) ρs
    tu = coh (BK 0 j) (wK 0 j) ρt
    hh = hJ (suc j)
    z  = zK 0 (suc j)

    app≡ : ∀ X → map (app (Dsk n)) X ≡ map (_++ (hh ∷ [])) X
    app≡ X = cong (λ h → map (_++ (h ∷ [])) X) (hl≡ (suc j))

    UA : suppTy A ≋ map (_++ (hh ∷ [])) (suppTy (aL n))
    UA = U j ρs ncs (D.lenρK 0 j (cJ j)) (lkρ-lt j (cJ j)) (lkρ-h j (cJ j))

    supp-s : supp ts A ≋ map (app (Dsk n)) (supp (var (dbl n)) (aL n))
    supp-s = subst (λ L → supp ts A ≋ L) (sym (app≡ (supp (var (dbl n)) (aL n))))
               (≋-++ (Ttop j ρs nc (D.lenρK 0 j (cJ j)) (lkρ-c j (cJ j)) (lkρ-h j (cJ j))) UA)

    supp-t : supp tu A ≋ map (app (Dsk n)) (supp (var (suc (dbl n))) (aL n))
    supp-t = subst (λ L → supp tu A ≋ L) (sym (app≡ (supp (var (suc (dbl n))) (aL n))))
               (≋-++ (Ttop j ρt nc (D.lenρK 0 j (suc (cJ j))) (lkρ-c j (suc (cJ j))) (lkρ-h j (suc (cJ j)))) UA)

    sd : ∀ sg {t X} → supp t A ≋ map (app (Dsk n)) X →
         T (sameDown (Σctx (Dsk n)) X (bdryT sg (homs (Σctx (Dsk n))))) →
         T (sameDown Γw (supp t A) (bdryT sg (homs Γw)))
    sd sg {t} {X} (a , b) p =
      sameDown-⊑ Γw a b (≡⊑ (sym (bdryW (Dsk n) sg))) (≡⊑ (bdryW (Dsk n) sg))
        (sameDownW (Dsk n) X (bdryT sg (homs (Σctx (Dsk n)))) p)

    ne : A ≡ ⋆ → ⊥
    ne q = wK≢⋆ j (ty⋆ (wK 0 j) ρs q)

    Lz : len (Σctx (Dsk n)) ≡ z
    Lz = trans (lenΣ (Dsk n)) (cong S (D.len-Dsk n))

    eA : endsTy A ≡ just (var 0 , var z)
    eA = trans (E j ρs) (cong₂ (λ a b → just (a , b)) (lkρ-lt j (cJ j) 0 tt) (lkρ-z j (cJ j)))

    okW : T (endsOK Γw A)
    okW = subst T (sym (trans (endsOK-ty Γw A eA)
                              (cong (λ L → isVarAt (var 0) (firstL L) ∧ isVarAt (var z) (lastL L))
                                    (trans (objsW (Dsk n)) (cong (λ L → 0 ∷ 1 ∷ L ∷ []) Lz)))))
                (==ℕ-refl z)

  dimA : dim A ≡ dimK (homs Γw)
  dimA = trans (dim-[] (wK 0 j) ρs)
           (trans (dim-wK0 j) (sym (trans (dimKW (Dsk n)) (trans (dimKΣ (Dsk n)) (D.dimCtx-Dsk n)))))

  opW : T (opCase Γw A ts tu)
  opW = opCase-intro Γw A ts tu ne okW dimA (sd false {ts} {supp (var (dbl n)) (aL n)} supp-s (sdDsk⁻ (j + 0)))
                                    (sd true {tu} {supp (var (suc (dbl n))) (aL n)} supp-t (sdDsk⁺ (j + 0)))

  op0 : T (opCase (BK 0 (suc j)) A ts tu)
  op0 = subst (λ Γ → T (opCase Γ A ts tu)) (eqW (suc j)) opW

  dim0 : dim A ≡ dimK (homs (BK 0 (suc j)))
  dim0 = subst (λ Γ → dim A ≡ dimK (homs Γ)) (eqW (suc j)) dimA

------------------------------------------------------------------------
-- The coherence case never applies: its source would have dimension
-- above dim K(Γ) (Gray.CohDim), while dim A = dim K(Γ).

private
  sig : SigOK
  sig {k = ()} _ _

  sle : ∀ n → suc n ≤ n → ⊥
  sle zero    ()
  sle (suc n) (s≤s p) = sle n p

  nocoh : ∀ Γ → PsFacts Γ → ∀ A t u → Γ ⊢tm t ∶ A → dim A ≡ dimK (homs Γ) → cohCase Γ A t u ≡ false
  nocoh Γ P ⋆            t u dt e = refl
  nocoh Γ P (arr B s s′) t u dt e with cohCase Γ (arr B s s′) t u in q
  ... | false = refl
  ... | true  = ⊥-elim (sle (dimK (homs Γ))
                  (subst (λ k → suc (dimK (homs Γ)) ≤ k) e
                         (CD.cohB< closed (λ {G} {k} → sig {G} {k}) Γ P B s s′ t dt u (subst T (sym q) tt))))

  P0 : ∀ j → PsFacts (BK 0 j)
  P0 j with D.BK-ps 0 j
  ... | ps d = fst (ps-facts d)

------------------------------------------------------------------------
-- The heads (0, j), by induction on j.

GSide0 : Nat → Set
GSide0 zero    = T (graySide (BK 0 0) (aL 0) (var 0) (var (zK 0 0)))
GSide0 (suc j) = T (graySide (BK 0 (suc j)) (wK 0 j [ ρsK 0 j ]ty)
                     (coh (BK 0 j) (wK 0 j) (ρsK 0 j)) (coh (BK 0 j) (wK 0 j) (ρtK 0 j)))

private
  rcoh0 : ∀ j {Γ σ} → BK 0 j ⊢ty wK 0 j → GSide0 j → Γ ⊢sub σ ∶ BK 0 j →
          Γ ⊢tm coh (BK 0 j) (wK 0 j) σ ∶ wK 0 j [ σ ]ty
  rcoh0 zero    a s d = coh-wf (D.BK-ps 0 zero)    (wBK 0 zero)    a s d
  rcoh0 (suc j) a s d = coh-wf (D.BK-ps 0 (suc j)) (wBK 0 (suc j)) a s d

  rsrc0 : ∀ j → BK 0 j ⊢ty wK 0 j → GSide0 j →
          BK 0 (suc j) ⊢tm coh (BK 0 j) (wK 0 j) (ρsK 0 j) ∶ wK 0 j [ ρsK 0 j ]ty
  rsrc0 j a s = rcoh0 j a s (ρK-wf 0 j _ (D.lk-face-s 0 j))

  rtgt0 : ∀ j → BK 0 j ⊢ty wK 0 j → GSide0 j →
          BK 0 (suc j) ⊢tm coh (BK 0 j) (wK 0 j) (ρtK 0 j) ∶ wK 0 j [ ρsK 0 j ]ty
  rtgt0 j a s =
    subst (BK 0 (suc j) ⊢tm coh (BK 0 j) (wK 0 j) (ρtK 0 j) ∶_)
          (sym (D.faces-BK 0 j (wK 0 j) (D.avoidK 0 j)))
          (rcoh0 j a s (ρK-wf 0 j _ (D.lk-face-t 0 j)))

mutual
  g0wK-wf : ∀ j → BK 0 j ⊢ty wK 0 j
  g0wK-wf zero =
    arr-wf (var-wf (wBK 0 0) (trans (D.lk-BK-Sph 0 0 0 tt) (D.lk-Sph-s 0)))
           (var-wf (wBK 0 0) (D.lk-zK 0 0))
  g0wK-wf (suc j) = arr-wf (rsrc0 j (g0wK-wf j) (g0side j)) (rtgt0 j (g0wK-wf j) (g0side j))

  g0side : ∀ j → GSide0 j
  g0side zero    = gside-BK00
  g0side (suc j) =
    ∨-inr {cohCase (BK 0 (suc j)) (wK 0 j [ ρsK 0 j ]ty) (coh (BK 0 j) (wK 0 j) (ρsK 0 j)) (coh (BK 0 j) (wK 0 j) (ρtK 0 j))}
          (op0 j (ncs0 j) (nc0 j))

  nc0 : ∀ j → NoCoh j
  nc0 zero    = tt
  nc0 (suc j) =
    nocoh (BK 0 (suc j)) (P0 (suc j)) (wK 0 j [ ρsK 0 j ]ty) _ _ (rsrc0 j (g0wK-wf j) (g0side j))
          (dim0 j (ncs0 j) (nc0 j))

  ncs0 : ∀ j → NCs j
  ncs0 zero    = tt
  ncs0 (suc j) = ncs0 j , nc0 j

------------------------------------------------------------------------
-- The hypotheses of CaTTExp.DerivedWith at graySide, for k = 0.

gside-BK0-0 : T (graySide (BK 0 0) (aL 0) (var (dbl 0)) (var (zK 0 0)))
gside-BK0-0 = g0side zero

gside-BK-0 : ∀ j → T (graySide (BK 0 (suc j)) (wK 0 j [ ρsK 0 j ]ty)
                        (coh (BK 0 j) (wK 0 j) (ρsK 0 j)) (coh (BK 0 j) (wK 0 j) (ρtK 0 j)))
gside-BK-0 j = g0side (suc j)
