------------------------------------------------------------------------
-- The context of a canonical head is well formed, with unary atom
-- types, and its atoms are bounded (ledger S26j, step 2b).
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsWf where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Gray.Biclosed.Subst using (_⊢_∶_; ⊢in; sub-wf)
open import CaTTExp.Binder.Multimap using (atomFm)
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen
  using (T-if; F-if; dec; inl; inr; ptTy; blankFrom; blank; lookup-blank; mapM-if; nthY-just; lookup-map; lookup-idx;
         agree-blank-on; ren-typed)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; Deps↓; lookup-some; elem-split)
open import CaTTExp.Binder.MultimapCellsRen
open import CaTTExp.Binder.MultimapCellsComp

------------------------------------------------------------------------
-- okTy and atomFm under a renaming of atoms into range.

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt
  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p
  ∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in {true} _ q = q

module OkRen (as vs : List Nat) where
  private ρ = renOf as vs

  atomFm-ren : ∀ k x → T (atomFm k x) → atF x ⊆ as → T (atomFm (length as) (sF (fo ρ) x))
  atomFm-ren k (obj i)  _ h = idx-lt as i (h i (∨-l (i ==ℕ i) _ (==ℕ-refl i)))
  atomFm-ren k (x ⊗ y)  p h = ∧-in (atomFm-ren k x (∧-l _ _ p) (⊆-l (atF x) (atF y) as h)) (atomFm-ren k y (∧-r _ _ p) (⊆-r (atF x) (atF y) as h))
  atomFm-ren k (x \\ y) p h = ∧-in (atomFm-ren k x (∧-l _ _ p) (⊆-l (atF x) (atF y) as h)) (atomFm-ren k y (∧-r _ _ p) (⊆-r (atF x) (atF y) as h))
  atomFm-ren k (x // y) p h = ∧-in (atomFm-ren k x (∧-l _ _ p) (⊆-l (atF x) (atF y) as h)) (atomFm-ren k y (∧-r _ _ p) (⊆-r (atF x) (atF y) as h))

  okTy-ren : ∀ k A → T (okTy k A) → atY A ⊆ as → T (okTy (length as) (sY ρ A))
  okTy-ren k (op ((x ∷ []) ▸ z)) p h =
    ∧-in (atomFm-ren k x (∧-l _ _ p) (λ i q → h i (elem-++l i (atF x ++ []) (atF z) (elem-++l i (atF x) [] q))))
         (atomFm-ren k z (∧-r _ _ p) (λ i q → h i (elem-++r i (atF x ++ []) (atF z) q)))
  okTy-ren k (op ([] ▸ _)) ()
  okTy-ren k (op ((_ ∷ _ ∷ _) ▸ _)) ()
  okTy-ren k (hom m g A s t) p h =
    ∧-in (∧-l _ _ p) (okTy-ren k A (∧-r (g ==ℕ 1) _ p) (⊆-l (atY A) (atT s ++ atT t) as h))

------------------------------------------------------------------------
-- wf reads a context only at the variables of the type.

wf-agree : ∀ Γ Δ A → Agree Γ Δ (varsY A) → wf Γ A ≡ wf Δ A
wf-agree Γ Δ (op _) a = refl
wf-agree Γ Δ (hom m g A s t) a =
  let a₁  = agree-l Γ Δ (varsY A) (varsT s ++ varsT t) a
      a₂₃ = agree-r Γ Δ (varsY A) (varsT s ++ varsT t) a
  in cong₃′ (λ x y z → x ∧ eqMaybeTy y A ∧ eqMaybeTy z A)
       (wf-agree Γ Δ A a₁)
       (infer-agree Γ Δ s (agree-l Γ Δ (varsT s) (varsT t) a₂₃))
       (infer-agree Γ Δ t (agree-r Γ Δ (varsT s) (varsT t) a₂₃))

------------------------------------------------------------------------
-- wfCtx entry by entry.

lookup-take : ∀ (Ψ : Ctx) p i → T (i <ℕ p) → lookup (take p Ψ) i ≡ lookup Ψ i
lookup-take []      (suc p) i       _ = refl
lookup-take (A ∷ Ψ) (suc p) zero    _ = refl
lookup-take (A ∷ Ψ) (suc p) (suc i) l = lookup-take Ψ p i l

lookup-take-out : ∀ (Ψ : Ctx) p i → (T (i <ℕ p) → ⊥) → lookup (take p Ψ) i ≡ nothing
lookup-take-out Ψ       zero    i       _ = refl
lookup-take-out []      (suc p) i       _ = refl
lookup-take-out (A ∷ Ψ) (suc p) zero    n = ⊥-elim (n tt)
lookup-take-out (A ∷ Ψ) (suc p) (suc i) n = lookup-take-out Ψ p i n

++-take : ∀ (acc : Ctx) (A : CTy) Ψ p → (acc ++ (A ∷ [])) ++ take p Ψ ≡ acc ++ take (suc p) (A ∷ Ψ)
++-take []        A Ψ p = refl
++-take (B ∷ acc) A Ψ p = cong (B ∷_) (++-take acc A Ψ p)

wfFrom-elim : ∀ acc Ψ p {A} → T (wfCtxFrom acc Ψ) → lookup Ψ p ≡ just A → T (wf (acc ++ take p Ψ) A)
wfFrom-elim acc (B ∷ Ψ) zero    w refl = subst (λ Γ → T (wf Γ B)) (sym (++-[] acc)) (∧-l _ _ w)
  where
  ++-[] : ∀ (xs : Ctx) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)
wfFrom-elim acc (B ∷ Ψ) (suc p) {A} w e =
  subst (λ Γ → T (wf Γ A)) (++-take acc B Ψ p) (wfFrom-elim (acc ++ (B ∷ [])) Ψ p (∧-r _ _ w) e)

wfFrom-intro : ∀ acc Ψ → (∀ p {A} → lookup Ψ p ≡ just A → T (wf (acc ++ take p Ψ) A)) → T (wfCtxFrom acc Ψ)
wfFrom-intro acc []      h = tt
wfFrom-intro acc (B ∷ Ψ) h =
  ∧-in (subst (λ Γ → T (wf Γ B)) (++-[] acc) (h 0 refl))
       (wfFrom-intro (acc ++ (B ∷ [])) Ψ (λ p {A} e → subst (λ Γ → T (wf Γ A)) (sym (++-take acc B Ψ p)) (h (suc p) e)))
  where
  ++-[] : ∀ (xs : Ctx) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

------------------------------------------------------------------------
-- The context of the canonical head of b is well formed.

open import CaTTExp.Binder.MultimapCellsCanon using (module Idem; atY-concatAt)

module SubWf (k : Nat) (Φ : Ctx) (w : T (wfCtx Φ)) (b : Tm) {B : CTy} (eB : infer Φ b ≡ just B)
             (wB : T (wf Φ B)) (ab : ∀ i → In (supAtomsOf Φ b) i → T (i <ℕ k)) where

  open Idem k Φ w b eB wB ab

  private
    just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
    just-inj refl = refl
    nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
    nj ()

  module AtPos (p : Nat) (l : T (p <ℕ m)) where
    j : Nat
    j = nth vs p
    jvs : In vs j
    jvs = nth-In vs p l
    rj : rr j ≡ p
    rj = idx-nth vs vs-nd p l

    typed : take p Φ′ ⊢ ρ ∶ blank vs (take j Φ)
    typed = ⊢in app′
      where
      app′ : ∀ i C → lookup (blank vs (take j Φ)) i ≡ just C → infer (take p Φ′) (Sub.tm ρ i) ≡ just (sY ρ C)
      app′ i C e with dec (i <ℕ j)
      ... | inr nl = ⊥-elim (nj (trans (sym (trans (lookup-blank 0 vs (take j Φ) i)
                       (cong (mapM (λ A → if elem i vs then A else ptTy)) (lookup-take-out Φ j i nl)))) e))
      ... | inl il with lookup Φ i in eΦ
      ...   | nothing = ⊥-elim (nj (trans (sym (trans (lookup-blank 0 vs (take j Φ) i)
                         (cong (mapM (λ A → if elem i vs then A else ptTy)) (trans (lookup-take Φ j i il) eΦ)))) e))
      ...   | just D with dec (elem i vs)
      ...     | inl ivs =
                let eC : D ≡ C
                    eC = just-inj (trans (sym (mapM-if (elem i vs) (just D) ivs))
                           (trans (cong (mapM (λ A → if elem i vs then A else ptTy)) (sym (trans (lookup-take Φ j i il) eΦ)))
                             (trans (sym (lookup-blank 0 vs (take j Φ) i)) e)))
                    ri<p : T (rr i <ℕ p)
                    ri<p = subst (λ z → T (rr i <ℕ z)) rj (idx-mono vs vs-inc i j ivs jvs il)
                in trans (cong (infer (take p Φ′)) (T-if (elem i vs) ivs))
                     (trans (lookup-take Φ′ p (rr i) ri<p)
                       (trans (lookup-Φ′-r i eΦ ivs) (cong (λ X → just (sY ρ X)) eC)))
      ...     | inr nvs =
                let eC : ptTy ≡ C
                    eC = just-inj (trans (cong just (sym (F-if (elem i vs) nvs)))
                           (trans (cong (mapM (λ A → if elem i vs then A else ptTy)) (sym (trans (lookup-take Φ j i il) eΦ)))
                             (trans (sym (lookup-blank 0 vs (take j Φ) i)) e)))
                in trans (cong (infer (take p Φ′)) (F-if (elem i vs) nvs)) (cong (λ X → just (sY ρ X)) eC)

    entry-wf : ∀ {A} → lookup Φ j ≡ just A → T (wf (take p Φ′) (sY ρ A))
    entry-wf {A} eA =
      let wfj = wfFrom-elim [] Φ j w eA
          ag : Agree (take j Φ) (blank vs (take j Φ)) (varsY A)
          ag i q = sym (trans (lookup-blank 0 vs (take j Φ) i)
                     (mapM-if (elem i vs) (lookup (take j Φ) i) (vs-closed j eA jvs i q)))
          wfb = subst T (wf-agree (take j Φ) (blank vs (take j Φ)) A ag) wfj
      in sub-wf typed A wfb

  wfCtx-Φ′ : T (wfCtx Φ′)
  wfCtx-Φ′ = wfFrom-intro [] Φ′ (λ p {A′} e →
    let l = lt-m e
        open AtPos p l
        (A , eA) = lookup-some Φ j (vs-lt j jvs)
        eA′ : A′ ≡ sY ρ A
        eA′ = just-inj (trans (sym e) (trans (lookup-Φ′ p l) (cong (λ X → just (sY ρ X)) (nthY-just Φ j eA))))
    in subst (λ X → T (wf (take p Φ′) X)) (sym eA′) (entry-wf eA))

  ----------------------------------------------------------------------
  -- The canonical head of b passes the side condition, with the
  -- renamed type of b.

  all-introL : ∀ (P : CTy → Bool) (xs : Ctx) → (∀ p {A} → lookup xs p ≡ just A → T (P A)) → T (all P xs)
  all-introL P []       h = tt
  all-introL P (x ∷ xs) h = ∧-in (h 0 refl) (all-introL P xs (λ p e → h (suc p) e))

  all-introN : ∀ (P : Nat → Bool) xs → (∀ i → In xs i → T (P i)) → T (all P xs)
  all-introN P []       h = tt
  all-introN P (x ∷ xs) h = ∧-in (h x (∨-l (x ==ℕ x) _ (==ℕ-refl x))) (all-introN P xs (λ i q → h i (∨-r (i ==ℕ x) _ q)))

  open OkRen asb vs using (okTy-ren)
  open AtRen asb vs using (atT-ren; atY-ren; concatAt-ren)

  S-asb : ∀ i → In S i → In asb i
  S-asb = S-in

  module _ (oks : ∀ j {A} → lookup Φ j ≡ just A → T (okTy k A)) (okB : T (okTy k B)) where

    entries-ok : T (all (okTy (length asb)) Φ′)
    entries-ok = all-introL _ Φ′ (λ p {A′} eA′ →
      let l′ = lt-m eA′
          open AtPos p l′
          (A , eA) = lookup-some Φ j (vs-lt j jvs)
          e′ : A′ ≡ sY ρ A
          e′ = just-inj (trans (sym eA′) (trans (lookup-Φ′ p l′) (cong (λ X → just (sY ρ X)) (nthY-just Φ j eA))))
          sub : atY A ⊆ asb
          sub i r = S-in i (elem-++l i (concatAt (map (nthY Φ) vs)) _
                      (atY-concatAt (nthY Φ) vs j jvs i (subst (λ X → In (atY X) i) (sym (nthY-just Φ j eA)) r)))
      in subst (λ X → T (okTy (length asb) X)) (sym e′) (okTy-ren k A (oks j eA) sub))

    toS : ∀ x → In (concatAt (map (nthY Φ) vs) ++ atT b) x → In S x
    toS x xin with elem-split x (concatAt (map (nthY Φ) vs)) (atT b) xin
    ... | inl r = elem-++l x (concatAt (map (nthY Φ) vs)) (atT b ++ atYM (infer Φ b)) r
    ... | inr r = elem-++r x (concatAt (map (nthY Φ) vs)) _ (elem-++l x (atT b) _ r)

    atoms-ok : T (atomsBelow (length asb) Φ′ b′)
    atoms-ok = all-introN _ (concatAt Φ′ ++ atT b′) (λ i q →
      let q′ = subst (λ X → In X i) (cong₂ _++_ (concatAt-ren (map (nthY Φ) vs)) (atT-ren b)) q
          q″ = subst (λ X → In X i) (sym (map-++ ra (concatAt (map (nthY Φ) vs)) (atT b))) q′
          (x , xin , e) = In-map-inv ra (concatAt (map (nthY Φ) vs) ++ atT b) i q″
      in subst (λ z → T (z <ℕ length asb)) (sym e) (idx-lt asb x (S-in x (toS x xin))))

    B-ok : T (okTy (length asb) (sY ρ B))
    B-ok = okTy-ren k B okB (λ i r → S-in i (elem-++r i (concatAt (map (nthY Φ) vs)) _
                                (elem-++r i (atT b) _ (subst (λ X → In (atYM X) i) (sym eB) r))))

    B-wf : T (wf Φ′ (sY ρ B))
    B-wf = sub-wf (ren-typed asb vs Φ) B
             (subst T (wf-agree Φ (blank vs Φ) B (agree-blank-on Φ vs (varsY B) (λ i q _ → bvsY i q))) wB)

    B-at : T (all (λ i → i <ℕ length asb) (atY (sY ρ B)))
    B-at = all-introN _ (atY (sY ρ B)) (λ i q →
      let (x , xin , e) = In-map-inv ra (atY B) i (subst (λ X → In X i) (atY-ren B) q)
      in subst (λ z → T (z <ℕ length asb)) (sym e)
           (idx-lt asb x (S-in x (elem-++r x (concatAt (map (nthY Φ) vs)) _
                                   (elem-++r x (atT b) _ (subst (λ X → In (atYM X) x) (sym eB) xin))))))

    sub-mmcTy : mmcTy (cidx (canon k Φ b)) ≡ just (sY ρ B)
    sub-mmcTy =
      trans (T-if (isCanon (cidx (canon k Φ b)) ∧ all (okTy (length asb)) Φ′ ∧ wfCtx Φ′ ∧ atomsBelow (length asb) Φ′ b′)
                  (∧-in isCanon-sub (∧-in entries-ok (∧-in wfCtx-Φ′ atoms-ok))))
        (trans (cong (λ X → X >>= λ A → if okTy (length asb) A ∧ wf Φ′ A ∧ all (λ i → i <ℕ length asb) (atY A)
                                         then just A else nothing) infer-b′)
               (T-if (okTy (length asb) (sY ρ B) ∧ wf Φ′ (sY ρ B) ∧ all (λ i → i <ℕ length asb) (atY (sY ρ B)))
                     (∧-in B-ok (∧-in B-wf B-at))))
