------------------------------------------------------------------------
-- On one hom, Finster–Mimram's operation condition gives two-tier L's.
--
--   op-side : Θ ⊢ps → dim Θ > 0 →
--             ΣΘ ⊢tm t ∶ A → ΣΘ ⊢tm u ∶ A   (in two-tier L) →
--             endsOK (ΣΘ) A → dim A = dim Θ →
--             isOp (ΣΘ) A t u → opCase (ΣΘ) A t u
--
-- This is step 2(b) of the two-tier L whiskering interface
-- (notes/surface-conservativity.md §7): every whisker head with k ≥ 1
-- lives on ΣΘ (Gray.WhiskerSigma) and is accepted by isOp (Derived), so
-- graySide accepts it once its two sides are L-derivable and endsOK,
-- dim A = dim Θ hold.
--
-- Proof. For sg = − (resp. +) and the source t (resp. target u):
--  * covers(supp(t:A), ∂^sg T): a tuple of supp(t:A) is a singleton
--    (S v) for v a variable of Θ (soundness, Strict.Soundness: it is a
--    basis element of K(ΣΘ)(a₀,a₁), and endsOK fixes a₀ ≠ a₁). S v is
--    a variable of t:A (Gray.SuppVars.supp-fv), hence in ∂^sg(ΣΘ) by
--    isOp, hence below ∂^sg T (Gray.SingleHom.rule-bdry⇐).
--  * covers(∂^sg T, supp(t:A)): a tuple of ∂^sg T is a singleton (S v)
--    for v a variable of Θ (the tables of one hom), and lies below
--    itself, so S v ∈ ∂^sg(ΣΘ) (rule-bdry⇒), hence S v is a variable of
--    t:A by isOp. It is not an object, so (S v) ∈ ↓supp(t:A)
--    (Strict.SuppFV.supp-fv⇐), which is a bounded path from a tuple of
--    supp(t:A), i.e. a leqT cover (Gray.DownAgree).
------------------------------------------------------------------------
module CaTTExp.Gray.SingleHomSide where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Complex using (endsV; endsL; WFT)
open import CaTTExp.Strict.L using (PsInv; psInv; IsCellTm; towerOf; endsL-inv)
open import CaTTExp.Strict.Cell using (flat)
open import CaTTExp.Strict.Soundness using (flat-supp; endsV→endsTy)
open import CaTTExp.Strict.Recon using (flat-sub; Sub-cell; topdeg)
open import CaTTExp.Strict.SigmaFacts using (Short; s1; short; lookupΣ⁻)
open import CaTTExp.Strict.SuppFV using (supp-fv⇐)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; here; there; any-witness; any-at; any-++⁻; any-++l; any-++r;
                                      any-map⁻; _⊎_; inj₁; inj₂; T-All; All-T; ∧-in; ∨-out; ∨-inl; ∨-inr)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; anyS⇐; map≡; filter⇒)
open import CaTTExp.Gray.DownAgree ∅ using (memT-sound; memT-complete; nub-sound) renaming (module Faces to DF)
open import CaTTExp.Gray.SuppVars ∅ using (supp-fv)
open import CaTTExp.Gray.SingleHom ∅
  using (module Main; mkC; hΣ; hcsΣ; cell-shape; objsΣ; dimKΣ; rule-bdry⇒; rule-bdry⇐; FM; chain1⇒; lower⇒)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; S; Σps′; lookupΣ)
open import CaTTExp.Typing ∅ using (isOp)

open import CaTTExp.Strict.Soundness using (module Soundness)
open Soundness using (sound-tm)

------------------------------------------------------------------------
-- Generalities.

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  ≡T : ∀ {b} → b ≡ true → T b
  ≡T refl = tt

  T≡ : ∀ {b} → T b → b ≡ true
  T≡ {true} _ = refl

  elem⇒ : ∀ x ys → T (elem x ys) → x ∈ᴺ ys
  elem⇒ x (y ∷ ys) p with ∨-out {x ==ℕ y} p
  ... | inj₁ q = here (==ℕ-sound x y q)
  ... | inj₂ q = there (elem⇒ x ys q)

  elem⇐ : ∀ x ys → x ∈ᴺ ys → T (elem x ys)
  elem⇐ x (y ∷ ys) (here refl) = ∨-inl {x ==ℕ x} (==ℕ-refl x)
  elem⇐ x (y ∷ ys) (there m)   = ∨-inr {x ==ℕ y} (elem⇐ x ys m)

  ⊆?⇒ : ∀ xs ys {x} → T (⊆? xs ys) → x ∈ᴺ xs → x ∈ᴺ ys
  ⊆?⇒ xs ys p m = elem⇒ _ ys (All-T (λ x → elem x ys) xs p m)

  Σ≢⋆ : ∀ A → Σty A ≡ ⋆ → ⊥
  Σ≢⋆ ⋆           ()
  Σ≢⋆ (arr _ _ _) ()

  -- Entries of a table of one hom are levels of its cells.
  mf : ∀ (P : El → Bool) xs {b} → b ∈ᴺ map lvl (filter P xs) → Σ El λ e → Any (e ≡_) xs × (b ≡ lvl e)
  mf P xs m with any-witness (any-map⁻ lvl (filter P xs) (subst (Any _) (map≡ lvl (filter P xs)) m))
  ... | e , me , q = e , fst (filter⇒ P xs me) , q

  piece-cell : ∀ h i sg {b} → b ∈ᴺ piece h i sg → Σ El λ e → Any (e ≡_) (hcs h) × (b ≡ lvl e)
  piece-cell h i sg m with i ==ℕ hd h
  ... | true  = mf _ (hcs h) m
  ... | false with i <ℕ hd h
  ...   | true  = mf _ (hcs h) m
  ...   | false = ⊥-elim (none m)
    where
    none : ∀ {b} → b ∈ᴺ [] → ⊥
    none ()

  short-tail : ∀ {Θ a w} → Short Θ (a ∷ w) → w ≡ []
  short-tail (s1 _) = refl

  endsOK-ty : ∀ Γ A {a b} → endsTy A ≡ just (a , b) →
              endsOK Γ A ≡ (isVarAt a (firstL (objs Γ)) ∧ isVarAt b (lastL (objs Γ)))
  endsOK-ty Γ A e rewrite e = refl

------------------------------------------------------------------------
-- The lemma, over Γ = ΣΘ.

module _ {Θ : Ctx} (PΘ : Θ ⊢ps) (pos : T (0 <ℕ dimCtx Θ)) where

  private
    Γ  = Σctx Θ
    PΓ : Γ ⊢ps
    PΓ = Σps′ PΘ
    invΓ = psInv PΓ
    cs = cells Γ
    N  = dimK (homs Γ)
    h  = hΣ Θ
    module F = DF cs

    inner : Θ ⊢ps → Σ Nat λ z → Θ ⊢ps z ∶ ⋆
    inner (ps d) = _ , d

    dΘ : Θ ⊢ps fst (inner PΘ) ∶ ⋆
    dΘ = snd (inner PΘ)

    rb⇒ : ∀ sg v {A} → lookup Θ v ≡ just A →
          T (any (leqT cs N (S v ∷ [])) (bdryT sg (homs Γ))) → elem (S v) (FM sg Γ) ≡ true
    rb⇒ sg v lv p = rule-bdry⇒ dΘ pos sg v lv p

    rb⇐ : ∀ sg v {A} → lookup Θ v ≡ just A →
          elem (S v) (FM sg Γ) ≡ true → T (any (leqT cs N (S v ∷ [])) (bdryT sg (homs Γ)))
    rb⇐ sg v lv p = rule-bdry⇐ dΘ pos sg v lv p

    -- The ⋆-endpoints fixed by endsOK are the objects 0 and 1.
    ends01 : ∀ A {x y} → endsV A ≡ just (x , y) → T (endsOK Γ A) → (x ≡ 0) × (y ≡ 1)
    ends01 A {x} {y} ev ok =
      let q = subst (λ L → T (isVarAt (var x) (firstL L) ∧ isVarAt (var y) (lastL L))) (objsΣ Θ)
                (subst T (endsOK-ty Γ A (endsV→endsTy A ev)) ok)
      in ==ℕ-sound x 0 (∧-fst q) , ==ℕ-sound y 1 (∧-snd {x ==ℕ 0} q)

    -- A tuple of supp(t : A) is a singleton (S v), v a variable of Θ.
    supp-sing : ∀ {t B p q} → Γ ⊢tm t ∶ arr B p q → T (endsOK Γ (arr B p q)) →
                ∀ {s} → s ∈L supp t (arr B p q) →
                Σ Nat λ v → Σ Ty λ A′ → (lookup Θ v ≡ just A′) × (s ≡ S v ∷ [])
    supp-sing {t} {B} {p} {q} d ok {s} ms with sound-tm invΓ d
    ... | (x , y) , ev , _ , _ , cX
      with flat-sub PΓ (dim B) (towerOf t (arr B p q)) cX
             (memT-sound s _ (subst T (sym (flat-supp t B p q s)) (memT-complete s _ ms)))
    ...   | m , V , sub , mv with topdeg PΓ m V (Sub-cell PΓ cX sub) mv | ends01 (arr B p q) ev ok
    ...     | wft , _ | refl , refl = fin s wft
      where
      fin : ∀ s → WFT Γ 0 1 s → Σ Nat λ v → Σ Ty λ A′ → (lookup Θ v ≡ just A′) × (s ≡ S v ∷ [])
      fin []      ()
      fin (a ∷ w) (z , ea , rest) with endsL-inv (lookup Γ a) ea
      ... | ⋆ , la , ()
      ... | arr C c c′ , la , _ with lookupΣ⁻ Θ a la refl
      ...   | v , A′ , refl , _ , lv =
        v , A′ , lv , cong (S v ∷_) (short-tail (short Θ (S v ∷ w) (z , ea , rest)))

    -- A tuple of ∂^sg T is a singleton (S v), v a variable of Θ.
    bdry-sing : ∀ sg {τ} → τ ∈L bdryT sg (homs Γ) →
                Σ Nat λ v → Σ Ty λ A′ → (lookup Θ v ≡ just A′) × (τ ≡ S v ∷ [])
    bdry-sing sg {τ} mτ = fromPiece (split (subst (λ L → τ ∈L L) (Main.bdryEq dΘ pos sg) mτ))
      where
      M = Main.M dΘ pos
      split : τ ∈L (lowerT M (h ∷ []) ++ chainT sg M (h ∷ [])) →
              Σ Nat λ k → Σ Bool λ s → τ ∈L chainT s k (h ∷ [])
      split m with any-++⁻ (lowerT M (h ∷ [])) m
      ... | inj₁ l with lower⇒ M (h ∷ []) l
      ...   | k , s , _ , mc = k , s , mc
      split m | inj₂ c = M , sg , c

      fromPiece : (Σ Nat λ k → Σ Bool λ s → τ ∈L chainT s k (h ∷ [])) →
                  Σ Nat λ v → Σ Ty λ A′ → (lookup Θ v ≡ just A′) × (τ ≡ S v ∷ [])
      fromPiece (k , s , mc) with chain1⇒ h s k mc
      ... | b , refl , pb with piece-cell h k s pb
      ...   | e , me , refl with cell-shape Θ (subst (λ L → Any (e ≡_) L) (hcsΣ Θ) me)
      ...     | v , A′ , lv , refl = v , A′ , lv , refl

    -- covers(supp(t : A), ∂^sg T).
    supp⊆bdry : ∀ sg {t B p q} → Γ ⊢tm t ∶ arr B p q → T (endsOK Γ (arr B p q)) →
                T (⊆? (fvTmTy t (arr B p q)) (FM sg Γ)) →
                T (covers Γ (supp t (arr B p q)) (bdryT sg (homs Γ)))
    supp⊆bdry sg {t} {B} {p} {q} d ok sub =
      T-All (λ s → any (leqT cs N s) (bdryT sg (homs Γ))) (supp t A) (λ {s} ms → go s ms)
      where
      A = arr B p q
      go : ∀ s → s ∈L supp t A → T (any (leqT cs N s) (bdryT sg (homs Γ)))
      go s ms with supp-sing d ok ms
      ... | v , A′ , lv , refl =
        rb⇐ sg v lv (T≡ (elem⇐ (S v) (FM sg Γ) (⊆?⇒ (fvTmTy t A) (FM sg Γ) sub (supp-fv t A ms (here refl)))))

    -- covers(∂^sg T, supp(t : A)).
    bdry⊆supp : ∀ sg {t B p q} → Γ ⊢tm t ∶ arr B p q →
                T (⊆? (FM sg Γ) (fvTmTy t (arr B p q))) →
                T (covers Γ (bdryT sg (homs Γ)) (supp t (arr B p q)))
    bdry⊆supp sg {t} {B} {p} {q} d sub =
      T-All (λ τ → any (leqT cs N τ) (supp t A)) (bdryT sg (homs Γ)) (λ {τ} mτ → go τ mτ)
      where
      A = arr B p q
      go : ∀ τ → τ ∈L bdryT sg (homs Γ) → T (any (leqT cs N τ) (supp t A))
      go τ mτ with bdry-sing sg mτ
      ... | v , A′ , lv , refl with F.close⇒ N (nubT (supp t A)) (memT-sound (S v ∷ []) (down Γ (supp t A)) (supp-fv⇐ PΘ d inFV no))
        where
        self : T (any (leqT cs N (S v ∷ [])) (bdryT sg (homs Γ)))
        self = anyS⇐ (leqT cs N (S v ∷ [])) (bdryT sg (homs Γ)) (any-at mτ (F.leqT⇐ (F.pw-refl N (S v ∷ []))))
        inFV : S v ∈ᴺ fvTmTy t A
        inFV = ⊆?⇒ (FM sg Γ) (fvTmTy t A) sub (elem⇒ (S v) (FM sg Γ) (≡T (rb⇒ sg v lv self)))
        no : lookup Γ (S v) ≡ just ⋆ → ⊥
        no e = Σ≢⋆ A′ (just-inj (trans (sym (lookupΣ Θ v lv)) e))
      ...   | s , ms , k , kle , r =
        anyS⇐ (leqT cs N (S v ∷ [])) (supp t A)
          (any-at (nub-sound (supp t A) ms) (F.leqT⇐ {N} {S v ∷ []} (F.pw-mono kle (F.reach⇒pw r))))

  ----------------------------------------------------------------------
  -- The theorem.

  op-side : ∀ {B p q t u} → Γ ⊢tm t ∶ arr B p q → Γ ⊢tm u ∶ arr B p q →
            T (endsOK Γ (arr B p q)) → dim (arr B p q) ≡ dimCtx Θ →
            T (isOp Γ (arr B p q) t u) → T (opCase Γ (arr B p q) t u)
  op-side {B} {p} {q} {t} {u} dt du ok dA iop =
    ∧-in ok (∧-in dimOK (∧-in (half false dt (∧-fst iop)) (half true du (∧-snd {≈? (fvTmTy t A) (∂⁻ Γ)} iop))))
    where
    A = arr B p q
    dimOK : T (dim A ==ℕ dimK (homs Γ))
    dimOK = subst (λ n → T (dim A ==ℕ n)) (trans dA (sym (dimKΣ Θ))) (==ℕ-refl (dim A))
    half : ∀ sg {w} → Γ ⊢tm w ∶ A → T (≈? (fvTmTy w A) (FM sg Γ)) →
           T (sameDown Γ (supp w A) (bdryT sg (homs Γ)))
    half sg {w} d e = ∧-in (supp⊆bdry sg d ok (∧-fst e)) (bdry⊆supp sg d (∧-snd {⊆? (fvTmTy w A) (FM sg Γ)} e))

  op-side-gray : ∀ {B p q t u} → Γ ⊢tm t ∶ arr B p q → Γ ⊢tm u ∶ arr B p q →
                 T (endsOK Γ (arr B p q)) → dim (arr B p q) ≡ dimCtx Θ →
                 T (isOp Γ (arr B p q) t u) → T (graySide Γ (arr B p q) t u)
  op-side-gray {B} {p} {q} {t} {u} dt du ok dA iop =
    ∨-inr {cohCase Γ (arr B p q) t u} (op-side dt du ok dA iop)
