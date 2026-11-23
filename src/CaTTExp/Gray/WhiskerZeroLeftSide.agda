------------------------------------------------------------------------
-- Two-tier L accepts the left whisker heads of CaTTExp.Derived for
-- k = 0 (step 2(d) of the two-tier L whiskering interface,
-- notes/surface-conservativity.md §7):
--
--   gside-LK-0 j : graySide accepts (LK 0 (j+1), lK 0 (j+1))
--
-- The mirror of Gray.WhiskerZeroSide, over LK 0 (j+1) = LW(Dⁿ),
-- n = j+1 (Gray.WhiskerZeroLeft): the sides of the head are the
-- whiskers by h of the source and target s, t : aL n of the top cell of
-- Dⁿ⁺¹, so supp(side) has the tuples of supp(s : aL n) relabelled and
-- with h prepended (TtopL, UL); the disk's operation case
-- (Gray.WhiskerZeroSide.sdDsk⁻/⁺) is carried over by sameDownLW and
-- bdryLW; the coherence case is false by Gray.CohDim.cohB<. By
-- induction on j, with the L-typing of the heads (gl0K-wf).
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerZeroLeftSide where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Cover using (Any; here; there; any-witness; any-at; any-map⁻; any-map⁺; any-cm⁻; any-cm⁺;
                                      T-All; All-T; ∧-in; ∨-inr; _≤_; s≤s)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; map≡; cm≡)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; S)
open import CaTTExp.Gray.SingleHom ∅ using (dimKΣ)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn)
import CaTTExp.Derived as D
open D using (nB; zK; BK; wK; Dsk; LK; lK; tL; λsK; λtK; idS; renS)
open import CaTTExp.Typing ∅ using (cattSide)
import CaTTExp.Subst as SubstM
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Strict.Subst using (nth-topsSub)
open import CaTTExp.Gray.PsFacts ∅ using (ps-facts; PsFacts)
open import CaTTExp.Gray.MarksFuel ∅ using (SigOK)
open import CaTTExp.Strict.Hyp using (closed)
import CaTTExp.Gray.CohDim ∅ as CD
open import CaTTExp.Gray.WhiskerZeroSide
  using (_⊑_; _≋_; ≋-refl; ≡→≋; ≋-trans; ≋-++; sameDown-⊑; topDsk⇒; topDsk⇐; sdDsk⁻; sdDsk⁺; gside-BK0-0; g0wK-wf)
open import CaTTExp.Gray.WhiskerZeroLeft

------------------------------------------------------------------------
-- Generalities.

private
  map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  map⇒ : ∀ {A B : Set} (f : A → B) xs {y} → Any (y ≡_) (map f xs) → Σ A λ x → Any (x ≡_) xs × (y ≡ f x)
  map⇒ f xs m = any-witness (any-map⁻ f xs (subst (Any _) (map≡ f xs) m))

  map⇐ : ∀ {A B : Set} (f : A → B) xs {x} → Any (x ≡_) xs → Any (f x ≡_) (map f xs)
  map⇐ f xs {x} m = subst (Any (f x ≡_)) (sym (map≡ f xs)) (any-map⁺ f (any-at m refl))

  ≡⊑ : ∀ {S R} → S ≡ R → S ⊑ R
  ≡⊑ refl m = m

  lt2 : ∀ i n → T (i <ℕ n) → T (i <ℕ suc (suc n))
  lt2 i n p = <-suc i (suc n) (<-suc i n p)

  -- tL 0 j ≥ 4.
  lt-tL : ∀ j i → T (i <ℕ 4) → T (i <ℕ tL 0 j)
  lt-tL j zero          _ = tt
  lt-tL j (suc zero)    _ = tt
  lt-tL j (suc (suc zero)) _ = tt
  lt-tL j (suc (suc (suc zero))) _ = tt

  sT : ∀ A t u → (A ≡ ⋆ → ⊥) → suppTy (arr A t u) ≡ suppTy A ++ (topS t ++ topS u)
  sT ⋆            t u ne = ⊥-elim (ne refl)
  sT (arr B s s′) t u ne = refl

  ty⋆ : ∀ A σ → A [ σ ]ty ≡ ⋆ → A ≡ ⋆
  ty⋆ ⋆           σ _ = refl
  ty⋆ (arr A t u) σ ()

  lK≢⋆ : ∀ j → lK 0 j ≡ ⋆ → ⊥
  lK≢⋆ zero    ()
  lK≢⋆ (suc j) ()

  endsTy-arr : ∀ A t u → (A ≡ ⋆ → ⊥) → endsTy (arr A t u) ≡ endsTy A
  endsTy-arr ⋆            t u ne = ⊥-elim (ne refl)
  endsTy-arr (arr B s s′) t u ne = refl

  dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
  dim-[] ⋆           σ = refl
  dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

  endsOK-ty : ∀ Γ A {a b} → endsTy A ≡ just (a , b) →
              endsOK Γ A ≡ (isVarAt a (firstL (objs Γ)) ∧ isVarAt b (lastL (objs Γ)))
  endsOK-ty Γ A e rewrite e = refl

  ∘lk : ∀ τ σ i {w t} → T (i <ℕ lenₛ τ) → lookupₛ τ i ≡ var w → lookupₛ σ w ≡ t → lookupₛ (τ ∘ σ) i ≡ t
  ∘lk τ σ i p e e′ = trans (Sb.lookupₛ-∘ τ σ i p) (trans (cong (_[ σ ]tm) e) e′)

------------------------------------------------------------------------
-- The faces λsK 0 j, λtK 0 j.

private
  lenλs : ∀ j → lenₛ (λsK 0 j) ≡ suc (tL 0 j)
  lenλs j = D.lenₛ-renS (suc (tL 0 j)) (λ i → i)

  lenλt : ∀ j → lenₛ (λtK 0 j) ≡ suc (tL 0 j)
  lenλt j = cong suc (D.lenₛ-renS (tL 0 j) (λ i → i))

  ltλs : ∀ j i → T (i <ℕ suc (tL 0 j)) → T (i <ℕ lenₛ (λsK 0 j))
  ltλs j i p = subst (λ n → T (i <ℕ n)) (sym (lenλs j)) p

  ltλt : ∀ j i → T (i <ℕ suc (tL 0 j)) → T (i <ℕ lenₛ (λtK 0 j))
  ltλt j i p = subst (λ n → T (i <ℕ n)) (sym (lenλt j)) p

  lkλs : ∀ j i → T (i <ℕ suc (tL 0 j)) → lookupₛ (λsK 0 j) i ≡ var i
  lkλs j i p = D.lookup-renS (suc (tL 0 j)) (λ i → i) i p

  lkλt : ∀ j i → T (i <ℕ tL 0 j) → lookupₛ (λtK 0 j) i ≡ var i
  lkλt j i p =
    trans (D.lk-ext (idS (tL 0 j)) _ i (subst (λ n → T (i <ℕ n)) (sym (D.lenₛ-renS (tL 0 j) (λ i → i))) p))
          (D.lookup-renS (tL 0 j) (λ i → i) i p)

  lkλt-top : ∀ j → lookupₛ (λtK 0 j) (tL 0 j) ≡ var (suc (tL 0 j))
  lkλt-top j = subst (λ n → lookupₛ (λtK 0 j) n ≡ var (suc (tL 0 j))) (D.lenₛ-renS (tL 0 j) (λ i → i))
                     (D.lk-top (idS (tL 0 j)) (var (suc (tL 0 j))))

  scL : ∀ j → Sb.ScTy (lenₛ (λsK 0 j)) (lK 0 j)
  scL j = subst (λ n → Sb.ScTy n (lK 0 j)) (sym (trans (lenλs j) (sym (D.len-LK 0 j))))
                (Sb.ty-sc D.closed (D.lK-wf 0 j))

------------------------------------------------------------------------
-- The top of LK 0 j is (h, c), c its top cell.

topLK⇒ : ∀ j {x} → x ∈L topT (homs (LK 0 j)) → x ≡ 2 ∷ tL 0 j ∷ []
topLK⇒ j {x} mx
  with map⇒ F _ (subst (λ L → x ∈L L) (topLW (Dsk (j + 0)) (goodD (j + 0)))
                  (subst (λ Γ → x ∈L topT (homs Γ)) (sym (eqLW j)) mx))
... | y , my , refl rewrite topDsk⇒ (j + 0) my = refl

topLK⇐ : ∀ j → (2 ∷ tL 0 j ∷ []) ∈L topT (homs (LK 0 j))
topLK⇐ j =
  subst (λ Γ → (2 ∷ tL 0 j ∷ []) ∈L topT (homs Γ)) (eqLW j)
    (subst (λ L → (2 ∷ tL 0 j ∷ []) ∈L L) (sym (topLW (Dsk (j + 0)) (goodD (j + 0))))
      (map⇐ F _ (topDsk⇐ (j + 0))))

NoCohL : Nat → Set
NoCohL zero    = ⊤
NoCohL (suc j) = cohCase (LK 0 (suc j)) (lK 0 j [ λsK 0 j ]ty)
                         (coh (LK 0 j) (lK 0 j) (λsK 0 j)) (coh (LK 0 j) (lK 0 j) (λtK 0 j)) ≡ false

NCsL : Nat → Set
NCsL zero    = ⊤
NCsL (suc j) = NCsL j × NoCohL j

private
  topS-cohL : ∀ j σ → NoCohL j → topS (coh (LK 0 j) (lK 0 j) σ) ≡ applyF (topsSub σ) (topT (homs (LK 0 j)))
  topS-cohL zero    σ _  = refl
  topS-cohL (suc j) σ nc rewrite nc = refl

  Fpair : ∀ σ c h {c′ h′} → T (c <ℕ lenₛ σ) → T (h <ℕ lenₛ σ) → lookupₛ σ c ≡ var c′ → lookupₛ σ h ≡ var h′ →
          Ftuple (topsSub σ) (c ∷ h ∷ []) ≡ (c′ ∷ h′ ∷ []) ∷ []
  Fpair σ c h lc lh ec eh rewrite nth-topsSub σ c lc | nth-topsSub σ h lh | ec | eh = refl

  ltLK : ∀ j σ i → lenₛ σ ≡ len (LK 0 j) → T (i <ℕ suc (tL 0 j)) → T (i <ℕ lenₛ σ)
  ltLK j σ i e p rewrite e | D.len-LK 0 j = p

TtopL : ∀ j σ {h′ c′} → NoCohL j → lenₛ σ ≡ len (LK 0 j) → lookupₛ σ 2 ≡ var h′ → lookupₛ σ (tL 0 j) ≡ var c′ →
        topS (coh (LK 0 j) (lK 0 j) σ) ≋ ((h′ ∷ c′ ∷ []) ∷ [])
TtopL j σ {h′} {c′} nc e eh ec =
  (λ {x} mx → fwd x (subst (λ L → x ∈L L) (topS-cohL j σ nc) mx)) ,
  (λ { (here refl) → subst (λ L → (h′ ∷ c′ ∷ []) ∈L L) (sym (topS-cohL j σ nc)) bwd ; (there ()) })
  where
  R = topsSub σ
  C = topT (homs (LK 0 j))
  F≡ : Ftuple R (2 ∷ tL 0 j ∷ []) ≡ (h′ ∷ c′ ∷ []) ∷ []
  F≡ = Fpair σ 2 (tL 0 j) (ltLK j σ 2 e (<-suc 2 (tL 0 j) (lt-tL j 2 tt))) (ltLK j σ (tL 0 j) e (n<sn (tL 0 j))) eh ec
  fwd : ∀ x → x ∈L applyF R C → x ∈L ((h′ ∷ c′ ∷ []) ∷ [])
  fwd x mx with any-witness (any-cm⁻ (Ftuple R) C (subst (λ L → x ∈L L) (cm≡ (Ftuple R) C) mx))
  ... | y , my , mF rewrite topLK⇒ j my = subst (λ L → x ∈L L) F≡ mF
  bwd : (h′ ∷ c′ ∷ []) ∈L applyF R C
  bwd = subst (λ L → (h′ ∷ c′ ∷ []) ∈L L) (sym (cm≡ (Ftuple R) C))
          (any-cm⁺ (Ftuple R) (any-at (topLK⇐ j) (subst (λ L → (h′ ∷ c′ ∷ []) ∈L L) (sym F≡) (here refl))))

------------------------------------------------------------------------
-- The type supports.

UL : ∀ j σ → NCsL j → lenₛ σ ≡ len (LK 0 j) → (∀ i → T (i <ℕ tL 0 j) → lookupₛ σ i ≡ var i) →
     suppTy (lK 0 j [ σ ]ty) ≋ map F (suppTy (aL (nB 0 j)))
UL zero    σ _ _ _ = ≋-refl
UL (suc j) σ (ncs , nc) e lo =
  ≋-trans (≡→≋ (trans (sT (lK 0 j [ λs ]ty [ σ ]ty) _ _ (λ q → lK≢⋆ j (ty⋆ (lK 0 j) λs (ty⋆ _ σ q))))
                      (cong (λ A → suppTy A ++ (topS (coh (LK 0 j) (lK 0 j) τs) ++ topS (coh (LK 0 j) (lK 0 j) τt)))
                            (Sb.assoc-ty (lK 0 j) λs σ (scL j)))))
  (≋-trans (≋-++ (UL j τs ncs eτs loτ)
                 (≋-++ (TtopL j τs nc eτs h2s cs) (TtopL j τt nc eτt h2t ct)))
           (≡→≋ (sym (map-++ F (suppTy (aL n)) _))))
  where
  n  = nB 0 j
  t  = tL 0 j
  λs = λsK 0 j
  λt = λtK 0 j
  τs = λs ∘ σ
  τt = λt ∘ σ
  eτs : lenₛ τs ≡ len (LK 0 j)
  eτs = trans (Sb.lenₛ-∘ λs σ) (trans (lenλs j) (sym (D.len-LK 0 j)))
  eτt : lenₛ τt ≡ len (LK 0 j)
  eτt = trans (Sb.lenₛ-∘ λt σ) (trans (lenλt j) (sym (D.len-LK 0 j)))
  loτ : ∀ i → T (i <ℕ t) → lookupₛ τs i ≡ var i
  loτ i p = ∘lk λs σ i (ltλs j i (<-suc i t p)) (lkλs j i (<-suc i t p)) (lo i (lt2 i t p))
  2<t : T (2 <ℕ t)
  2<t = lt-tL j 2 tt
  h2s : lookupₛ τs 2 ≡ var 2
  h2s = ∘lk λs σ 2 (ltλs j 2 (<-suc 2 t 2<t)) (lkλs j 2 (<-suc 2 t 2<t)) (lo 2 (lt2 2 t 2<t))
  h2t : lookupₛ τt 2 ≡ var 2
  h2t = ∘lk λt σ 2 (ltλt j 2 (<-suc 2 t 2<t)) (lkλt j 2 2<t) (lo 2 (lt2 2 t 2<t))
  cs : lookupₛ τs t ≡ var t
  cs = ∘lk λs σ t (ltλs j t (n<sn t)) (lkλs j t (n<sn t)) (lo t (<-suc t (suc t) (n<sn t)))
  ct : lookupₛ τt t ≡ var (suc t)
  ct = ∘lk λt σ t (ltλt j t (n<sn t)) (lkλt-top j) (lo (suc t) (n<sn (suc t)))

------------------------------------------------------------------------
-- Ends and dimension.

dim-lK0 : ∀ j → dim (lK 0 j) ≡ nB 0 j
dim-lK0 zero    = refl
dim-lK0 (suc j) = cong suc (trans (dim-[] (lK 0 j) (λsK 0 j)) (dim-lK0 j))

EL : ∀ j σ → endsTy (lK 0 j [ σ ]ty) ≡ just (lookupₛ σ 0 , lookupₛ σ 3)
EL zero    σ = refl
EL (suc j) σ =
  trans (endsTy-arr (lK 0 j [ λs ]ty [ σ ]ty) _ _ (λ q → lK≢⋆ j (ty⋆ (lK 0 j) λs (ty⋆ _ σ q))))
  (trans (cong endsTy (Sb.assoc-ty (lK 0 j) λs σ (scL j)))
  (trans (EL j (λs ∘ σ))
         (cong₂ (λ a b → just (a , b))
                (trans (Sb.lookupₛ-∘ λs σ 0 (ltλs j 0 tt)) (cong (_[ σ ]tm) (lkλs j 0 tt)))
                (trans (Sb.lookupₛ-∘ λs σ 3 (ltλs j 3 (<-suc 3 (tL 0 j) (lt-tL j 3 tt))))
                       (cong (_[ σ ]tm) (lkλs j 3 (<-suc 3 (tL 0 j) (lt-tL j 3 tt))))))))
  where λs = λsK 0 j

------------------------------------------------------------------------
-- The operation case of the head (0, j+1).

private
  opCase-intro : ∀ Γ A t u → (A ≡ ⋆ → ⊥) → T (endsOK Γ A) → dim A ≡ dimK (homs Γ) →
                 T (sameDown Γ (supp t A) (bdryT false (homs Γ))) → T (sameDown Γ (supp u A) (bdryT true (homs Γ))) →
                 T (opCase Γ A t u)
  opCase-intro Γ ⋆            t u ne _  _  _ _ = ⊥-elim (ne refl)
  opCase-intro Γ (arr B p q) t u ne ok dA s₁ s₂ =
    ∧-in ok (∧-in (subst (λ k → T (suc (dim B) ==ℕ k)) dA (==ℕ-refl (suc (dim B)))) (∧-in s₁ s₂))

module _ (j : Nat) (ncs : NCsL j) (nc : NoCohL j) where

  private
    n  = nB 0 j
    Γw = LW (Dsk n)
    λs = λsK 0 j
    λt = λtK 0 j
    A  = lK 0 j [ λs ]ty
    ts = coh (LK 0 j) (lK 0 j) λs
    tu = coh (LK 0 j) (lK 0 j) λt
    t  = tL 0 j
    2<t : T (2 <ℕ t)
    2<t = lt-tL j 2 tt
    lenL : lenₛ λs ≡ len (LK 0 j)
    lenL = trans (lenλs j) (sym (D.len-LK 0 j))
    lenT : lenₛ λt ≡ len (LK 0 j)
    lenT = trans (lenλt j) (sym (D.len-LK 0 j))

    UA : suppTy A ≋ map F (suppTy (aL n))
    UA = UL j λs ncs lenL (λ i p → lkλs j i (<-suc i t p))

    supp-s : supp ts A ≋ map F (supp (var (dbl n)) (aL n))
    supp-s = ≋-++ (TtopL j λs nc lenL (lkλs j 2 (<-suc 2 t 2<t)) (lkλs j t (n<sn t))) UA

    supp-t : supp tu A ≋ map F (supp (var (suc (dbl n))) (aL n))
    supp-t = ≋-++ (TtopL j λt nc lenT (lkλt j 2 2<t) (lkλt-top j)) UA

    sd : ∀ sg {u X} → supp u A ≋ map F X →
         T (sameDown (Σctx (Dsk n)) X (bdryT sg (homs (Σctx (Dsk n))))) →
         T (sameDown Γw (supp u A) (bdryT sg (homs Γw)))
    sd sg {u} {X} (a , b) p =
      sameDown-⊑ Γw a b (≡⊑ (sym (bdryLW (Dsk n) (goodD n) sg))) (≡⊑ (bdryLW (Dsk n) (goodD n) sg))
        (sameDownLW (Dsk n) (goodD n) X (bdryT sg (homs (Σctx (Dsk n)))) p)

    ne : A ≡ ⋆ → ⊥
    ne q = lK≢⋆ j (ty⋆ (lK 0 j) λs q)

    eA : endsTy A ≡ just (var 0 , var 3)
    eA = trans (EL j λs) (cong₂ (λ a b → just (a , b)) (lkλs j 0 tt) (lkλs j 3 (<-suc 3 t (lt-tL j 3 tt))))

    okW : T (endsOK Γw A)
    okW = subst T (sym (trans (endsOK-ty Γw A eA)
                              (cong (λ L → isVarAt (var 0) (firstL L) ∧ isVarAt (var 3) (lastL L)) (objsLW (Dsk n)))))
                tt

  dimAL : dim A ≡ dimK (homs Γw)
  dimAL = trans (dim-[] (lK 0 j) λs)
            (trans (dim-lK0 j) (sym (trans (dimKLW (Dsk n) (goodD n)) (trans (dimKΣ (Dsk n)) (D.dimCtx-Dsk n)))))

  opL : T (opCase (LK 0 (suc j)) A ts tu)
  opL = subst (λ Γ → T (opCase Γ A ts tu)) (eqLW (suc j))
          (opCase-intro Γw A ts tu ne okW dimAL
            (sd false {ts} {supp (var (dbl n)) (aL n)} supp-s (sdDsk⁻ (j + 0)))
            (sd true {tu} {supp (var (suc (dbl n))) (aL n)} supp-t (sdDsk⁺ (j + 0))))

  dimL : dim A ≡ dimK (homs (LK 0 (suc j)))
  dimL = subst (λ Γ → dim A ≡ dimK (homs Γ)) (eqLW (suc j)) dimAL

------------------------------------------------------------------------
-- The coherence case never applies (Gray.CohDim).

private
  closedL : SubstM.Closed ∅ graySide
  closedL ()

open import CaTTExp.DerivedWithBase graySide closedL using (wLK; λsK-wf; λtK-wf)

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

  PL0 : ∀ j → PsFacts (LK 0 j)
  PL0 j with D.LK-ps 0 j
  ... | ps d = fst (ps-facts d)

------------------------------------------------------------------------
-- The heads (0, j), by induction on j.

GLSide0 : Nat → Set
GLSide0 zero    = T (graySide (BK 0 0) (aL 0) (var 0) (var (zK 0 0)))
GLSide0 (suc j) = T (graySide (LK 0 (suc j)) (lK 0 j [ λsK 0 j ]ty)
                      (coh (LK 0 j) (lK 0 j) (λsK 0 j)) (coh (LK 0 j) (lK 0 j) (λtK 0 j)))

private
  lcoh0 : ∀ j {Γ σ} → LK 0 j ⊢ty lK 0 j → GLSide0 j → Γ ⊢sub σ ∶ LK 0 j →
          Γ ⊢tm coh (LK 0 j) (lK 0 j) σ ∶ lK 0 j [ σ ]ty
  lcoh0 zero    a s d = coh-wf (D.LK-ps 0 zero)    (wLK 0 zero)    a s d
  lcoh0 (suc j) a s d = coh-wf (D.LK-ps 0 (suc j)) (wLK 0 (suc j)) a s d

  lsrc0 : ∀ j → LK 0 j ⊢ty lK 0 j → GLSide0 j →
          LK 0 (suc j) ⊢tm coh (LK 0 j) (lK 0 j) (λsK 0 j) ∶ lK 0 j [ λsK 0 j ]ty
  lsrc0 j a s = lcoh0 j a s (λsK-wf 0 j)

  ltgt0 : ∀ j → LK 0 j ⊢ty lK 0 j → GLSide0 j →
          LK 0 (suc j) ⊢tm coh (LK 0 j) (lK 0 j) (λtK 0 j) ∶ lK 0 j [ λsK 0 j ]ty
  ltgt0 j a s =
    subst (LK 0 (suc j) ⊢tm coh (LK 0 j) (lK 0 j) (λtK 0 j) ∶_)
          (sym (D.faces-LK 0 j (lK 0 j) (D.avoidLK 0 j)))
          (lcoh0 j a s (λtK-wf 0 j))

mutual
  gl0K-wf : ∀ j → LK 0 j ⊢ty lK 0 j
  gl0K-wf zero    = g0wK-wf zero
  gl0K-wf (suc j) = arr-wf (lsrc0 j (gl0K-wf j) (gl0side j)) (ltgt0 j (gl0K-wf j) (gl0side j))

  gl0side : ∀ j → GLSide0 j
  gl0side zero    = gside-BK0-0
  gl0side (suc j) =
    ∨-inr {cohCase (LK 0 (suc j)) (lK 0 j [ λsK 0 j ]ty) (coh (LK 0 j) (lK 0 j) (λsK 0 j)) (coh (LK 0 j) (lK 0 j) (λtK 0 j))}
          (opL j (ncsL j) (ncL j))

  ncL : ∀ j → NoCohL j
  ncL zero    = tt
  ncL (suc j) =
    nocoh (LK 0 (suc j)) (PL0 (suc j)) (lK 0 j [ λsK 0 j ]ty) _ _ (lsrc0 j (gl0K-wf j) (gl0side j))
          (dimL j (ncsL j) (ncL j))

  ncsL : ∀ j → NCsL j
  ncsL zero    = tt
  ncsL (suc j) = ncsL j , ncL j

------------------------------------------------------------------------
-- The third hypothesis of CaTTExp.DerivedWith at graySide, for k = 0.

gside-LK-0 : ∀ j → T (graySide (LK 0 (suc j)) (lK 0 j [ λsK 0 j ]ty)
                        (coh (LK 0 j) (lK 0 j) (λsK 0 j)) (coh (LK 0 j) (lK 0 j) (λtK 0 j)))
gside-LK-0 j = gl0side (suc j)
