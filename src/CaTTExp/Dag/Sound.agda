------------------------------------------------------------------------
-- Soundness of the DAG checker.
--
-- `Generic.Hyp` assumes that every local check of CaTTExp.Dag.Check
-- passes (on every item, every claim block, every free-variable claim)
-- and proves, by induction on ids, that every claim holds of the
-- unfolded terms (CaTTExp.Dag.Unfold): a claim J c n = just A gives a
-- genuine derivation ⟦ c ⟧c ⊢tm ⟦ n ⟧ ∶ ⟦ A ⟧ty of plain CaTT
-- (CaTTExp.Typing), and every context item gives ⟦ c ⟧c ⊢ctx.
--
-- `certified` is the end-to-end statement for the string certificates
-- of CaTTExp.Dag.Run: if `runCert ... Γ B ≡ true` (proved by refl in a
-- generated module) then Σ Tm (λ w → Γ ⊢tm w ∶ B), for the query Γ, B
-- stated in ordinary syntax. `certifiedQ` is the same for a query given
-- as its own table (too large to compare as a tree): the conclusion is
-- about the unfolding of the query table, queryCtxOf / queryTyOf, and
-- `queryMatches-sound` relates that unfolding to ordinary syntax when
-- the query is small.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Dag.Table
open import CaTTExp.Dag.Trie
open import CaTTExp.Dag.Lemmas

module CaTTExp.Dag.Sound where

AllL : (Nat → Set) → List Nat → Set
AllL P []       = ⊤
AllL P (a ∷ as) = P a × AllL P as

module Generic
  (K : Nat)
  (R : Nat → Maybe Item)
  (J : Nat → Nat → Maybe RTy)
  (F : Nat → Maybe (List Nat))
  where

  open import CaTTExp.Dag.Check K R J F
  open import CaTTExp.Dag.Unfold R

  ----------------------------------------------------------------------
  -- Decoding the small boolean checks

  eqM-sound : ∀ m k → T (eqM m k) → m ≡ just k
  eqM-sound (just a) k p = cong just (==ℕ-sound a k p)

  eqRM-sound : ∀ m B → T (eqRM m B) → m ≡ just B
  eqRM-sound (just A) B p = cong just (==R-sound A B p)

  eqL-sound : ∀ xs ys → T (eqL xs ys) → xs ≡ ys
  eqL-sound []       []       _ = refl
  eqL-sound (x ∷ xs) (y ∷ ys) p =
    cong₂ _∷_ (==ℕ-sound x y (∧-fst p)) (eqL-sound xs ys (∧-snd {x ==ℕ y} p))

  isHead-sound : ∀ m → T (isHead m) → Σ Nat λ c → Σ RTy λ A → m ≡ just (H c A)
  isHead-sound (just (H c A)) _ = c , A , refl

  isE-sound : ∀ m → T (isE m) → m ≡ just E
  isE-sound (just E) _ = refl

  isV-sound : ∀ i m → T (isV i m) → m ≡ just (V i)
  isV-sound i (just (V j)) p rewrite ==ℕ-sound i j p = refl

  varsOK-sound : ∀ k → T (varsOK k) → ∀ i → T (i <ℕ k) → R i ≡ just (V i)
  varsOK-sound (suc k) p i q with <-suc-cases i k q
  ... | inl r    = varsOK-sound k (∧-snd {isV k (R k)} p) i r
  ... | inr refl = isV-sound i (R i) (∧-fst p)

  ----------------------------------------------------------------------
  -- Merging free-variable sets

  elem-merge : ∀ x xs ys → elem x (merge xs ys) ≡ (elem x xs ∨ elem x ys)
  elem-merge x []       ys       = refl
  elem-merge x (a ∷ xs) []       = sym (∨-false (elem x (a ∷ xs)))
    where
    ∨-false : ∀ b → (b ∨ false) ≡ b
    ∨-false true  = refl
    ∨-false false = refl
  elem-merge x (a ∷ xs) (b ∷ ys) =
    step (a <ℕ b) (b <ℕ a) refl refl
      (elem-merge x xs (b ∷ ys)) (elem-merge x (a ∷ xs) ys) (elem-merge x xs ys)
    where
    step : ∀ p q → (a <ℕ b) ≡ p → (b <ℕ a) ≡ q →
           elem x (merge xs (b ∷ ys)) ≡ (elem x xs ∨ elem x (b ∷ ys)) →
           elem x (merge (a ∷ xs) ys) ≡ (elem x (a ∷ xs) ∨ elem x ys) →
           elem x (merge xs ys) ≡ (elem x xs ∨ elem x ys) →
           elem x (merge (a ∷ xs) (b ∷ ys)) ≡ (elem x (a ∷ xs) ∨ elem x (b ∷ ys))
    step true q ab ba i1 i2 i3 rewrite ab | i1 =
      ∨-assoc (x ==ℕ a) (elem x xs) (elem x (b ∷ ys))
    step false true ab ba i1 i2 i3 rewrite ab | ba | i2 =
      ∨-swap (x ==ℕ b) (elem x (a ∷ xs)) (elem x ys)
    step false false ab ba i1 i2 i3 rewrite ab | ba | i3 | <-tri a b ab ba with x ==ℕ b
    ... | true  = refl
    ... | false = refl

  ----------------------------------------------------------------------
  -- Hypotheses: every local check passes.

  -- The claims of one context, checked against themselves.
  GoodBlock : Nat → (Nat → Maybe RTy) → Set
  GoodBlock c Jc = ∀ n A → Jc n ≡ just A → T (judgOK c Jc n A)

  module Hyp
    (hV : T (varsOK K))
    (hR : ∀ k it → R k ≡ just it → T (itemOK k it))
    (hJ : ∀ c n A → J c n ≡ just A →
          Σ (Nat → Maybe RTy) λ Jc → GoodBlock c Jc × (Jc n ≡ just A))
    (hF : ∀ n xs → F n ≡ just xs → T (fOK n xs))
    where

    dec : Decreasing
    dec k it e = ∧-fst (hR k it e)

    open Irr dec

    isVar : ∀ i → T (i <ℕ K) → R i ≡ just (V i)
    isVar = varsOK-sound K hV

    -- Every coh item has a head.
    headOf : ∀ {n h as} → R n ≡ just (C h as) → Σ Nat λ c → Σ RTy λ A → R h ≡ just (H c A)
    headOf {n} {h} {as} e = isHead-sound (R h) (∧-snd {decItem n (C h as)} (hR n (C h as) e))

    ⟦⟧-C′ : ∀ {n h as} → R n ≡ just (C h as) →
            Σ Nat λ c → Σ RTy λ A → (R h ≡ just (H c A)) × (⟦ n ⟧ ≡ coh ⟦ c ⟧c ⟦ A ⟧ty ⟦ as ⟧s)
    ⟦⟧-C′ e with headOf e
    ... | c , A , eh = c , A , eh , ⟦⟧-C e eh

    --------------------------------------------------------------------
    -- Instantiation

    module InstS (σ : Trie Nat) (b : Nat) (Σs : Sub)
                 (Hσ : All (λ i a → T (i <ℕ b) → lookupₛ Σs i ≡ ⟦ a ⟧) σ) where
      open Inst σ b

      MemoInv : Trie Nat → Set
      MemoInv M = All (λ s m → ⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧) M

      instV-sound : ∀ i m M {M'} → instV i m M ≡ just M' → (M ≡ M') × (lookupₛ Σs i ≡ ⟦ m ⟧)
      instV-sound i m M e with if-just ((i <ℕ b) ∧ eqM (lookupT i σ) m) e
      ... | p , eq =
        eq , lookup-All Hσ (eqM-sound (lookupT i σ) m (∧-snd {i <ℕ b} p)) (∧-fst p)

      instVar : ∀ s m M {M'} → R s ≡ just (V s) → MemoInv M → instV s m M ≡ just M' →
                MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
      instVar s m M es inv e with instV-sound s m M e
      ... | refl , q rewrite ⟦⟧-V es = inv , q

      mutual
        inst-sound : ∀ f s m M {M'} → MemoInv M → inst f s m M ≡ just M' →
                     MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
        inst-sound zero    s m M inv ()
        inst-sound (suc f) s m M inv e = instK f s m M (s <ℕ K) refl inv e

        instK : ∀ f s m M (k : Bool) → (s <ℕ K) ≡ k → ∀ {M'} → MemoInv M →
                (if k then instV s m M else instHit f s m M (lookupT s M)) ≡ just M' →
                MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
        instK f s m M true  ek inv e = instVar s m M (isVar s (true-T ek)) inv e
        instK f s m M false ek inv e = instHit-sound f s m M (lookupT s M) refl inv e

        instHit-sound : ∀ f s m M (h : Maybe Nat) → lookupT s M ≡ h → ∀ {M'} → MemoInv M →
                        instHit f s m M h ≡ just M' → MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
        instHit-sound f s m M (just m') eh inv e with if-just (m' ==ℕ m) e
        ... | p , refl rewrite ==ℕ-sound m' m p = inv , lookup-All inv eh
        instHit-sound f s m M nothing eh inv e = instI-sound f s m M (R s) (R m) refl refl inv e

        instI-sound : ∀ f s m M (x y : Maybe Item) → R s ≡ x → R m ≡ y → ∀ {M'} → MemoInv M →
                      instI f s m M x y ≡ just M' → MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
        instI-sound f s m M (just (V i)) y es em inv e with instV-sound i m M e
        ... | refl , q rewrite ⟦⟧-V es = inv , q
        instI-sound f s m M (just (C h as)) (just (C h' as')) es em inv e
          with if-just ((h ==ℕ h') ∧ isHead (R h)) {x = instC s m (instL f as as' M)} {y = _}
                 (lemma-if e)
          where
          lemma-if : ∀ {b X Y} → (if b then X else nothing) ≡ just Y →
                     (if b then just X else nothing) ≡ just X
          lemma-if {true}  _ = refl
          lemma-if {false} ()
        ... | p , _ = instC-sound f s m M h as h' as' es em (==ℕ-sound h h' (∧-fst p))
                        (instL f as as' M) refl inv (unif e)
          where
          unif : ∀ {b X Y} → (if b then X else nothing) ≡ just Y → X ≡ just Y
          unif {true} q = q
          unif {false} ()
        instI-sound f s m M nothing _ es em inv ()
        instI-sound f s m M (just E) _ es em inv ()
        instI-sound f s m M (just (S _ _)) _ es em inv ()
        instI-sound f s m M (just (H _ _)) _ es em inv ()
        instI-sound f s m M (just (C _ _)) nothing es em inv ()
        instI-sound f s m M (just (C _ _)) (just (V _)) es em inv ()
        instI-sound f s m M (just (C _ _)) (just E) es em inv ()
        instI-sound f s m M (just (C _ _)) (just (S _ _)) es em inv ()
        instI-sound f s m M (just (C _ _)) (just (H _ _)) es em inv ()

        instC-sound : ∀ f s m M h as h' as' → R s ≡ just (C h as) → R m ≡ just (C h' as') →
                      h ≡ h' → (r : Maybe (Trie Nat)) → instL f as as' M ≡ r → ∀ {M'} →
                      MemoInv M → instC s m r ≡ just M' → MemoInv M' × (⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧)
        instC-sound f s m M h as .h as' es em refl (just M₁) er inv refl
          with instL-sound f as as' M inv er | ⟦⟧-C′ es
        ... | inv₁ , eqσ | c , A , eh , es′ =
          insert-All inv₁ eq , eq
          where
          eq : ⟦ s ⟧ [ Σs ]tm ≡ ⟦ m ⟧
          eq = trans (cong (_[ Σs ]tm) es′)
                 (trans (cong (coh ⟦ c ⟧c ⟦ A ⟧ty) eqσ) (sym (⟦⟧-C em eh)))
        instC-sound f s m M h as .h as' es em refl nothing er inv ()

        instL-sound : ∀ f as as' M {M'} → MemoInv M → instL f as as' M ≡ just M' →
                      MemoInv M' × (⟦ as ⟧s ∘ Σs ≡ ⟦ as' ⟧s)
        instL-sound f []       []         M inv refl = inv , refl
        instL-sound f (a ∷ as) (a' ∷ as') M inv e = instL₂-sound f a a' as as' M (inst f a a' M) refl inv e
        instL-sound f []       (_ ∷ _)    M inv ()
        instL-sound f (_ ∷ _)  []         M inv ()

        instL₂-sound : ∀ f a a' as as' M (r : Maybe (Trie Nat)) → inst f a a' M ≡ r → ∀ {M'} →
                       MemoInv M → instL₂ f as as' r ≡ just M' →
                       MemoInv M' × (⟦ a ∷ as ⟧s ∘ Σs ≡ ⟦ a' ∷ as' ⟧s)
        instL₂-sound f a a' as as' M (just M₁) er inv e with inst-sound f a a' M inv er
        ... | inv₁ , eqa with instL-sound f as as' M₁ inv₁ e
        ...   | inv₂ , eqs = inv₂ , cong₂ _,ₛ_ eqs eqa
        instL₂-sound f a a' as as' M nothing er inv ()

      instR-sound : ∀ B A M {M'} → MemoInv M → instR B A M ≡ just M' →
                    MemoInv M' × (⟦ B ⟧ty [ Σs ]ty ≡ ⟦ A ⟧ty)
      instR-sound ⋆ᵣ ⋆ᵣ M inv refl = inv , refl
      instR-sound (arrᵣ B s t) (arrᵣ A s' t') M inv e =
        instR₂-sound (instR B A M) refl e
        where
        instR₃-sound : ∀ {M₁} (r : Maybe (Trie Nat)) → MemoInv M₁ → ⟦ B ⟧ty [ Σs ]ty ≡ ⟦ A ⟧ty →
                       inst (suc s) s s' M₁ ≡ r → ∀ {M'} → instR₃ t t' r ≡ just M' →
                       MemoInv M' × (⟦ arrᵣ B s t ⟧ty [ Σs ]ty ≡ ⟦ arrᵣ A s' t' ⟧ty)
        instR₃-sound (just M₂) inv₁ eB er e3 with inst-sound (suc s) s s' _ inv₁ er
        ... | inv₂ , eqs with inst-sound (suc t) t t' M₂ inv₂ e3
        ...   | inv₃ , eqt = inv₃ , cong₃ arr eB eqs eqt
          where
          cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
                  a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
          cong₃ f refl refl refl = refl
        instR₃-sound nothing inv₁ eB er ()

        instR₂-sound : (r : Maybe (Trie Nat)) → instR B A M ≡ r → ∀ {M'} →
                       instR₂ s t s' t' r ≡ just M' →
                       MemoInv M' × (⟦ arrᵣ B s t ⟧ty [ Σs ]ty ≡ ⟦ arrᵣ A s' t' ⟧ty)
        instR₂-sound (just M₁) er e2 with instR-sound B A M inv er
        ... | inv₁ , eB = instR₃-sound (inst (suc s) s s' M₁) inv₁ eB refl e2
        instR₂-sound nothing er ()
      instR-sound ⋆ᵣ (arrᵣ _ _ _) M inv ()
      instR-sound (arrᵣ _ _ _) ⋆ᵣ M inv ()

      instOK-sound : ∀ B A → T (instOK σ b B A) → ⟦ B ⟧ty [ Σs ]ty ≡ ⟦ A ⟧ty
      instOK-sound B A p with is-just-sound (instR B A tleaf) p
      ... | M' , e = snd (instR-sound B A tleaf tt e)

    --------------------------------------------------------------------
    -- The argument trie

    SigFull : List Nat → Trie Nat → Set
    SigFull as σ = All (λ i a → T (i <ℕ lenₛ ⟦ as ⟧s) × (lookupₛ ⟦ as ⟧s i ≡ ⟦ a ⟧)) σ

    SigInv : List Nat → Trie Nat → Set
    SigInv as σ = All (λ i a → T (i <ℕ lenₛ ⟦ as ⟧s) → lookupₛ ⟦ as ⟧s i ≡ ⟦ a ⟧) σ

    -- Looking below the last entry ignores it.
    lookupₛ-snoc : ∀ σ t i → T (i <ℕ lenₛ σ) → lookupₛ (σ ,ₛ t) i ≡ lookupₛ σ i
    lookupₛ-snoc σ t i p rewrite ==ℕ-false i (lenₛ σ) p = refl

    sigT-ok : ∀ as → (fst (sigT as) ≡ lenₛ ⟦ as ⟧s) × SigFull as (snd (sigT as))
    sigT-ok []       = refl , tt
    sigT-ok (a ∷ as) = step (sigT as) (sigT-ok as)
      where
      step : (p : Σ Nat (λ _ → Trie Nat)) → (fst p ≡ lenₛ ⟦ as ⟧s) × SigFull as (snd p) →
             (fst (sigT₂ a p) ≡ lenₛ ⟦ a ∷ as ⟧s) × SigFull (a ∷ as) (snd (sigT₂ a p))
      step (L , σ) (refl , full) =
        refl ,
        insert-All
          (All-map (λ i x q → <-suc i (lenₛ ⟦ as ⟧s) (fst q) ,
                              trans (lookupₛ-snoc ⟦ as ⟧s ⟦ a ⟧ i (fst q)) (snd q)) σ full)
          (<-suc-self (lenₛ ⟦ as ⟧s) , lookupₛ-new)
        where
        lookupₛ-new : lookupₛ (⟦ as ⟧s ,ₛ ⟦ a ⟧) (lenₛ ⟦ as ⟧s) ≡ ⟦ a ⟧
        lookupₛ-new rewrite ==ℕ-true (lenₛ ⟦ as ⟧s) = refl

    full→inv : ∀ as σ → SigFull as σ → SigInv as σ
    full→inv as σ = All-map (λ i x q _ → snd q) σ

    inv-drop : ∀ a as σ → SigInv (a ∷ as) σ → SigInv as σ
    inv-drop a as σ =
      All-map (λ i x q p → trans (sym (lookupₛ-snoc ⟦ as ⟧s ⟦ a ⟧ i p))
                                 (q (<-suc i (lenₛ ⟦ as ⟧s) p))) σ

    inv→Hσ : ∀ as σ L → L ≡ lenₛ ⟦ as ⟧s → SigInv as σ →
             All (λ i a → T (i <ℕ L) → lookupₛ ⟦ as ⟧s i ≡ ⟦ a ⟧) σ
    inv→Hσ as σ L refl inv = inv

    --------------------------------------------------------------------
    -- Contexts

    ctxLen-sound : ∀ f c L → ctxLen f c ≡ just L → len ⟦ c ⟧c ≡ L
    ctxLen-sound (suc f) c L e = go (R c) refl e
      where
      go : (x : Maybe Item) → R c ≡ x → ctxLenI f x ≡ just L → len ⟦ c ⟧c ≡ L
      go (just E) ex refl rewrite ⟦⟧c-E ex = refl
      go (just (S c' A)) ex e' = go₂ (ctxLen f c') refl e'
        where
        go₂ : (y : Maybe Nat) → ctxLen f c' ≡ y → ctxLenS y ≡ just L → len ⟦ c ⟧c ≡ L
        go₂ (just L') ey refl rewrite ⟦⟧c-S ex = cong suc (ctxLen-sound f c' L' ey)
        go₂ nothing ey ()
      go nothing ex ()
      go (just (V _)) ex ()
      go (just (C _ _)) ex ()
      go (just (H _ _)) ex ()

    lookupCtx-sound : ∀ L c i B → len ⟦ c ⟧c ≡ L → lookupCtx L c i ≡ just B →
                      lookup ⟦ c ⟧c i ≡ just ⟦ B ⟧ty
    lookupCtx-sound (suc L) c i B el e = go (R c) refl e
      where
      go : (x : Maybe Item) → R c ≡ x → lookupCtxI L i x ≡ just B → lookup ⟦ c ⟧c i ≡ just ⟦ B ⟧ty
      go (just (S c' B')) ex e' =
        subst (λ Γ → lookup Γ i ≡ just ⟦ B ⟧ty) (sym (⟦⟧c-S ex)) (go₂ (i ==ℕ L) refl e')
        where
        el' : len ⟦ c' ⟧c ≡ L
        el' = suc-inj (trans (cong len (sym (⟦⟧c-S ex))) el)
        go₂ : (q : Bool) → (i ==ℕ L) ≡ q → (if q then just B' else lookupCtx L c' i) ≡ just B →
              (if i ==ℕ len ⟦ c' ⟧c then just ⟦ B' ⟧ty else lookup ⟦ c' ⟧c i) ≡ just ⟦ B ⟧ty
        go₂ true  eq refl rewrite el' | eq = refl
        go₂ false eq e2 rewrite el' | eq = lookupCtx-sound L c' i B el' e2
      go nothing ex ()
      go (just (V _)) ex ()
      go (just (C _ _)) ex ()
      go (just E) ex ()
      go (just (H _ _)) ex ()

    --------------------------------------------------------------------
    -- Free variables

    FSem : Nat → Set
    FSem n = ∀ xs → F n ≡ just xs → ∀ x → elem x xs ≡ elem x (fvTm ⟦ n ⟧)

    mergeF-sound : ∀ as ys → AllL FSem as → mergeF as ≡ just ys →
                   ∀ x → elem x ys ≡ elem x (fvSub ⟦ as ⟧s)
    mergeF-sound []       ys _ refl x = refl
    mergeF-sound (a ∷ as) ys (fa , fas) e x = go (F a) (mergeF as) refl refl e
      where
      go : (p q : Maybe (List Nat)) → F a ≡ p → mergeF as ≡ q → mergeF₂ p q ≡ just ys →
           elem x ys ≡ elem x (fvSub ⟦ a ∷ as ⟧s)
      go (just xa) (just ys') ep eq refl =
        trans (elem-merge x ys' xa)
          (trans (cong₂ _∨_ (mergeF-sound as ys' fas eq x) (fa xa ep x))
                 (sym (elem-++ x (fvSub ⟦ as ⟧s) (fvTm ⟦ a ⟧))))
      go nothing _ ep eq ()
      go (just _) nothing ep eq ()

    belowAll : ∀ {P : Nat → Set} f as → (∀ a → T (a <ℕ f) → P a) → T (belowL f as) → AllL P as
    belowAll f []       h _ = tt
    belowAll f (a ∷ as) h p = h a (∧-fst p) , belowAll f as h (∧-snd {a <ℕ f} p)

    F-step : ∀ n → (∀ a → T (a <ℕ n) → FSem a) → FSem n
    F-step n ih xs e x = go (R n) refl (hF n xs e)
      where
      go : (it : Maybe Item) → R n ≡ it → T (fOKI xs it) → elem x xs ≡ elem x (fvTm ⟦ n ⟧)
      go (just (V i)) ei p rewrite eqL-sound xs (i ∷ []) p | ⟦⟧-V ei = refl
      go (just (C h as)) ei p with ⟦⟧-C′ ei
      ... | c , A , eh , en rewrite en = go₂ (mergeF as) refl (∧-snd {isHead (R h)} p)
        where
        go₂ : (m : Maybe (List Nat)) → mergeF as ≡ m → T (fOKM xs m) →
              elem x xs ≡ elem x (fvSub ⟦ as ⟧s)
        go₂ (just ys) em q rewrite eqL-sound xs ys q =
          mergeF-sound as ys
            (belowAll n as ih (∧-snd {h <ℕ n} (dec n (C h as) ei))) em x
      go nothing ei ()
      go (just E) ei ()
      go (just (S _ _)) ei ()
      go (just (H _ _)) ei ()

    F-all : ∀ f n → T (n <ℕ f) → FSem n
    F-all (suc f) n p = F-step n (λ a q → F-all f a (<-pred a n f q p))

    F-sound : ∀ n → FSem n
    F-sound n = F-all (suc n) n (<-suc-self n)

    fvR-sound : ∀ A a → fvR A ≡ just a → ∀ x → elem x a ≡ elem x (fvTy ⟦ A ⟧ty)
    fvR-sound ⋆ᵣ .[] refl x = refl
    fvR-sound (arrᵣ A s t) a e x = go (fvR A) (F s) (F t) refl refl refl e
      where
      go : (p q r : Maybe (List Nat)) → fvR A ≡ p → F s ≡ q → F t ≡ r → fvR₂ p q r ≡ just a →
           elem x a ≡ elem x (fvTy ⟦ arrᵣ A s t ⟧ty)
      go (just xa) (just xs) (just xt) ep eq er refl =
        trans (elem-merge x xa (merge xs xt))
          (trans (cong₂ _∨_ (fvR-sound A xa ep x)
                   (trans (elem-merge x xs xt)
                     (trans (cong₂ _∨_ (F-sound s xs eq x) (F-sound t xt er x))
                            (sym (elem-++ x (fvTm ⟦ s ⟧) (fvTm ⟦ t ⟧))))))
                 (sym (elem-++ x (fvTy ⟦ A ⟧ty) (fvTm ⟦ s ⟧ ++ fvTm ⟦ t ⟧))))
      go nothing _ _ ep eq er ()
      go (just _) nothing _ ep eq er ()
      go (just _) (just _) nothing ep eq er ()

    side-sound : ∀ Δ A s t → T (sideD Δ A s t) → T (cattSide Δ ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧)
    side-sound Δ A s t p = go (fvR A) (F s) (F t) refl refl refl p
      where
      go : (p q r : Maybe (List Nat)) → fvR A ≡ p → F s ≡ q → F t ≡ r → T (sideD₂ Δ p q r) →
           T (cattSide Δ ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧)
      go (just a) (just xs) (just xt) ea es et h = subst T eq h
        where
        mem : ∀ u xu → F u ≡ just xu → ∀ x → elem x (merge xu a) ≡ elem x (fvTmTy ⟦ u ⟧ ⟦ A ⟧ty)
        mem u xu eu x =
          trans (elem-merge x xu a)
            (trans (cong₂ _∨_ (F-sound u xu eu x) (fvR-sound A a ea x))
                   (sym (elem-++ x (fvTm ⟦ u ⟧) (fvTy ⟦ A ⟧ty))))
        eq : sideF Δ (merge xs a) (merge xt a) ≡ cattSide Δ ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧
        eq = cong₂ _∨_
               (cong₂ _∧_ (≈?-cong (merge xs a) (fvTmTy ⟦ s ⟧ ⟦ A ⟧ty) (varsCtx Δ) (mem s xs es))
                          (≈?-cong (merge xt a) (fvTmTy ⟦ t ⟧ ⟦ A ⟧ty) (varsCtx Δ) (mem t xt et)))
               (cong₂ _∧_ (≈?-cong (merge xs a) (fvTmTy ⟦ s ⟧ ⟦ A ⟧ty) (∂⁻ Δ) (mem s xs es))
                          (≈?-cong (merge xt a) (fvTmTy ⟦ t ⟧ ⟦ A ⟧ty) (∂⁺ Δ) (mem t xt et)))
      go nothing _ _ ea es et ()
      go (just _) nothing _ ea es et ()
      go (just _) (just _) nothing ea es et ()

    --------------------------------------------------------------------
    -- The main induction, on ids

    -- What a claim of a context block says.
    SemJ : Nat → Set
    SemJ n = ∀ c (Jc : Nat → Maybe RTy) A → GoodBlock c Jc → Jc n ≡ just A →
             ⟦ c ⟧c ⊢ctx → ⟦ c ⟧c ⊢tm ⟦ n ⟧ ∶ ⟦ A ⟧ty

    SemC : Nat → Set
    SemC c = T (isCtx (R c)) → ⟦ c ⟧c ⊢ctx

    HeadGood : Nat → RTy → Set
    HeadGood c ⋆ᵣ           = ⊥
    HeadGood c (arrᵣ A s t) =
      (⟦ c ⟧c ⊢ps) × (⟦ c ⟧c ⊢ctx) × (⟦ c ⟧c ⊢ty arr ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧) ×
      T (cattSide ⟦ c ⟧c ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧)

    SemH : Nat → Set
    SemH h = ∀ c A → R h ≡ just (H c A) → HeadGood c A

    Sem : Nat → Set
    Sem k = SemJ k × (SemC k × SemH k)

    Below : Nat → Set
    Below f = ∀ k → T (k <ℕ f) → Sem k

    -- A claim of the global table J, through its block.
    semJ-global : ∀ f → Below f → ∀ c s A → T (s <ℕ f) → J c s ≡ just A →
                  ⟦ c ⟧c ⊢ctx → ⟦ c ⟧c ⊢tm ⟦ s ⟧ ∶ ⟦ A ⟧ty
    semJ-global f ih c s A sf e w with hJ c s A e
    ... | Jc , good , e' = fst (ih s sf) c Jc A good e' w

    tyOK-sound : ∀ f → Below f → ∀ c A → T (belowR f A) → ⟦ c ⟧c ⊢ctx → T (tyOK c A) →
                 ⟦ c ⟧c ⊢ty ⟦ A ⟧ty
    tyOK-sound f ih c ⋆ᵣ _ w _ = ⋆-wf w
    tyOK-sound f ih c (arrᵣ A s t) b w p =
      let q  = ∧-snd {tyOK c A} p
          bq = ∧-snd {belowR f A} b
      in arr-wf
           (semJ-global f ih c s A (∧-fst bq) (eqRM-sound (J c s) A (∧-fst q)) w)
           (semJ-global f ih c t A (∧-snd {s <ℕ f} bq)
              (eqRM-sound (J c t) A (∧-snd {eqRM (J c s) A} q)) w)

    args-sound : ∀ f → Below f → ∀ c Jc → GoodBlock c Jc → ⟦ c ⟧c ⊢ctx →
                 ∀ σ ch as L → T (belowL f as) → L ≡ lenₛ ⟦ as ⟧s → SigInv as σ →
                 T (argsOK Jc σ ch as L) → ⟦ c ⟧c ⊢sub ⟦ as ⟧s ∶ ⟦ ch ⟧c
    args-sound f ih c Jc good w σ ch [] zero _ _ _ p =
      subst (λ Δ → ⟦ c ⟧c ⊢sub ⟨⟩ ∶ Δ) (sym (⟦⟧c-E (isE-sound (R ch) p))) (⟨⟩-wf w)
    args-sound f ih c Jc good w σ ch (a ∷ as) (suc L) b el inv p =
      go (R ch) (Jc a) refl refl p
      where
      go : (x : Maybe Item) (y : Maybe RTy) → R ch ≡ x → Jc a ≡ y →
           T (argOK Jc σ as L x y) → ⟦ c ⟧c ⊢sub ⟦ a ∷ as ⟧s ∶ ⟦ ch ⟧c
      go (just (S ch' B)) (just Ta) ex ey q =
        subst (λ Δ → ⟦ c ⟧c ⊢sub ⟦ a ∷ as ⟧s ∶ Δ) (sym (⟦⟧c-S ex))
          (,-wf rest (subst (⟦ c ⟧c ⊢tm ⟦ a ⟧ ∶_) (sym eqB) da))
        where
        el' : L ≡ lenₛ ⟦ as ⟧s
        el' = suc-inj el
        inv' : SigInv as σ
        inv' = inv-drop a as σ inv
        eqB : ⟦ B ⟧ty [ ⟦ as ⟧s ]ty ≡ ⟦ Ta ⟧ty
        eqB = InstS.instOK-sound σ L ⟦ as ⟧s (inv→Hσ as σ L el' inv') B Ta (∧-fst q)
        da : ⟦ c ⟧c ⊢tm ⟦ a ⟧ ∶ ⟦ Ta ⟧ty
        da = fst (ih a (∧-fst b)) c Jc Ta good ey w
        rest : ⟦ c ⟧c ⊢sub ⟦ as ⟧s ∶ ⟦ ch' ⟧c
        rest = args-sound f ih c Jc good w σ ch' as L (∧-snd {a <ℕ f} b) el' inv'
                 (∧-snd {instOK σ L B Ta} q)
      go nothing y ex ey ()
      go (just (V _)) y ex ey ()
      go (just (C _ _)) y ex ey ()
      go (just E) y ex ey ()
      go (just (H _ _)) y ex ey ()
      go (just (S _ _)) nothing ex ey ()
    args-sound f ih c Jc good w σ ch [] (suc L) _ _ _ ()
    args-sound f ih c Jc good w σ ch (a ∷ as) zero _ _ _ ()

    -- The coh case of a claim.
    semC-coh : ∀ f → Below f → ∀ c Jc A n h as → GoodBlock c Jc → ⟦ c ⟧c ⊢ctx →
               R n ≡ just (C h as) → T (n <ℕ suc f) →
               T (judgC Jc A as (R h)) → ⟦ c ⟧c ⊢tm ⟦ n ⟧ ∶ ⟦ A ⟧ty
    semC-coh f ih c Jc A n h as good w en nf p with ⟦⟧-C′ en
    ... | ch , B , eh , eqn = subst (λ x → ⟦ c ⟧c ⊢tm x ∶ ⟦ A ⟧ty) (sym eqn) (go B hg (sigT as) (sigT-ok as) p′)
      where
      dn : T (decItem n (C h as))
      dn = dec n (C h as) en
      hf : T (h <ℕ f)
      hf = <-pred h n f (∧-fst dn) nf
      hg : HeadGood ch B
      hg = snd (snd (ih h hf)) ch B eh
      p′ : T (judgC₂ Jc A as ch B (sigT as))
      p′ = subst (λ x → T (judgC Jc A as x)) eh p
      go : ∀ B′ → HeadGood ch B′ → (q : Σ Nat (λ _ → Trie Nat)) →
           (fst q ≡ lenₛ ⟦ as ⟧s) × SigFull as (snd q) → T (judgC₂ Jc A as ch B′ q) →
           ⟦ c ⟧c ⊢tm coh ⟦ ch ⟧c ⟦ B′ ⟧ty ⟦ as ⟧s ∶ ⟦ A ⟧ty
      go (arrᵣ B′ s t) (psΔ , wΔ , tyΔ , side) (L , σ) (eL , full) r =
        subst (⟦ c ⟧c ⊢tm _ ∶_) eqA (coh-wf psΔ wΔ tyΔ side sub)
        where
        inv : SigInv as σ
        inv = full→inv as σ full
        sub : ⟦ c ⟧c ⊢sub ⟦ as ⟧s ∶ ⟦ ch ⟧c
        sub = args-sound f ih c Jc good w σ ch as L
                (belowL-mono n f as nf (∧-snd {h <ℕ n} dn)) eL inv (∧-fst r)
        eqA : ⟦ arrᵣ B′ s t ⟧ty [ ⟦ as ⟧s ]ty ≡ ⟦ A ⟧ty
        eqA = InstS.instOK-sound σ L ⟦ as ⟧s (inv→Hσ as σ L eL inv) (arrᵣ B′ s t) A
                (∧-snd {argsOK Jc σ ch as L} r)

    semJ-step : ∀ f → Below f → SemJ f
    semJ-step f ih c Jc A good e w = go (R f) refl (good f A e)
      where
      go : (it : Maybe Item) → R f ≡ it → T (judgI c Jc A it) → ⟦ c ⟧c ⊢tm ⟦ f ⟧ ∶ ⟦ A ⟧ty
      go (just (V i)) ei p = go₂ (ctxLen (suc c) c) refl p
        where
        go₂ : (m : Maybe Nat) → ctxLen (suc c) c ≡ m → T (judgV c A i m) →
              ⟦ c ⟧c ⊢tm ⟦ f ⟧ ∶ ⟦ A ⟧ty
        go₂ (just L) eL q rewrite ⟦⟧-V ei =
          var-wf w (lookupCtx-sound L c i A (ctxLen-sound (suc c) c L eL)
                     (eqRM-sound (lookupCtx L c i) A q))
      go (just (C h as)) ei p = semC-coh f ih c Jc A f h as good w ei (<-suc-self f) p
      go nothing ei ()
      go (just E) ei ()
      go (just (S _ _)) ei ()
      go (just (H _ _)) ei ()

    semC-step : ∀ f → Below f → SemC f
    semC-step f ih p = go (R f) refl p
      where
      go : (it : Maybe Item) → R f ≡ it → T (isCtx it) → ⟦ f ⟧c ⊢ctx
      go (just E) ei _ = subst _⊢ctx (sym (⟦⟧c-E ei)) ε-wf
      go (just (S c' B)) ei _ =
        subst _⊢ctx (sym (⟦⟧c-S ei)) (▸-wf wc' tB)
        where
        ok : T (itemOK f (S c' B))
        ok = hR f (S c' B) ei
        d : T (decItem f (S c' B))
        d = ∧-fst ok
        q : T (isCtx (R c') ∧ tyOK c' B)
        q = ∧-snd {decItem f (S c' B)} ok
        wc' : ⟦ c' ⟧c ⊢ctx
        wc' = fst (snd (ih c' (∧-fst d))) (∧-fst q)
        tB : ⟦ c' ⟧c ⊢ty ⟦ B ⟧ty
        tB = tyOK-sound f ih c' B (∧-snd {c' <ℕ f} d) wc' (∧-snd {isCtx (R c')} q)
      go nothing ei ()
      go (just (V _)) ei ()
      go (just (C _ _)) ei ()
      go (just (H _ _)) ei ()

    semH-step : ∀ f → Below f → SemH f
    semH-step f ih c ⋆ᵣ e = ∧-snd {decItem f (H c ⋆ᵣ)} (hR f (H c ⋆ᵣ) e)
    semH-step f ih c (arrᵣ A s t) e =
      psΔ , wc , tyA , side-sound ⟦ c ⟧c A s t (∧-snd {is-just (checkPs ⟦ c ⟧c)} hd)
      where
      ok : T (itemOK f (H c (arrᵣ A s t)))
      ok = hR f (H c (arrᵣ A s t)) e
      d : T (decItem f (H c (arrᵣ A s t)))
      d = ∧-fst ok
      q : T (headOK c (arrᵣ A s t))
      q = ∧-snd {decItem f (H c (arrᵣ A s t))} ok
      q₂ : T (tyOK c (arrᵣ A s t) ∧ headΔ A s t ⟦ c ⟧c)
      q₂ = ∧-snd {isCtx (R c)} q
      hd : T (headΔ A s t ⟦ c ⟧c)
      hd = ∧-snd {tyOK c (arrᵣ A s t)} q₂
      wc : ⟦ c ⟧c ⊢ctx
      wc = fst (snd (ih c (∧-fst d))) (∧-fst q)
      psΔ : ⟦ c ⟧c ⊢ps
      psΔ = fst (is-just-sound (checkPs ⟦ c ⟧c) (∧-fst hd))
      tyA : ⟦ c ⟧c ⊢ty arr ⟦ A ⟧ty ⟦ s ⟧ ⟦ t ⟧
      tyA = tyOK-sound f ih c (arrᵣ A s t) (∧-snd {c <ℕ f} d) wc (∧-fst q₂)

    below-suc : ∀ f → Below f → Below (suc f)
    below-suc f ih k p with <-suc-cases k f p
    ... | inl q    = ih k q
    ... | inr refl = semJ-step f ih , (semC-step f ih , semH-step f ih)

    below : ∀ f → Below f
    below zero    k ()
    below (suc f) = below-suc f (below f)

    sem : ∀ k → Sem k
    sem k = below (suc k) k (<-suc-self k)

    -- The root claim.
    root-sound : ∀ g n A → T (isCtx (R g)) → J g n ≡ just A →
                 (⟦ g ⟧c ⊢ctx) × (⟦ g ⟧c ⊢tm ⟦ n ⟧ ∶ ⟦ A ⟧ty)
    root-sound g n A cg e with hJ g n A e
    ... | Jc , good , e' = wg , fst (sem n) g Jc A good e' wg
      where
      wg : ⟦ g ⟧c ⊢ctx
      wg = fst (snd (sem g)) cg

------------------------------------------------------------------------
-- The string certificates of CaTTExp.Dag.Run

open import CaTTExp.Dag.Run
open import CaTTExp.Dag.NatMap
open import Agda.Builtin.String using (String)

-- Reading an entry of a bucket map that allN accepted: a found entry
-- passes the check p (absent entries are accepted by every check used).
module _ {X : Set} (dec : Nat → Maybe X) (p : Nat → Maybe X → Bool)
         (p0 : ∀ k → T (p k (dec 0))) where
  found-ok : ∀ t → T (allN (λ k v → p k (dec v)) t) →
             ∀ k {x} → dec (lookupN k t) ≡ just x → T (p k (just x))
  found-ok t ok k e = subst (λ m → T (p k m)) e (lookupN-ok (λ k v → p k (dec v)) p0 t ok k)

module Concrete (K : Nat) (Rt : NatMap) (Jt : Trie NatMap) (Ft : NatMap) where
  open Generic K (Rof K Rt Jt Ft) (Jof K Rt Jt Ft) (Fof K Rt Jt Ft)
  open import CaTTExp.Dag.Check K (Rof K Rt Jt Ft) (Jof K Rt Jt Ft) (Fof K Rt Jt Ft)
  open import CaTTExp.Dag.Unfold (Rof K Rt Jt Ft)

  module _ (ok : T (tablesOK K Rt Jt Ft)) where
    private
      okV : T (varsOK K)
      okV = ∧-fst ok
      ok₁ : T (itemsOK K Rt Jt Ft ∧ (claimsOK K Rt Jt Ft ∧ fvOK K Rt Jt Ft))
      ok₁ = ∧-snd {varsOK K} ok
      okR : T (itemsOK K Rt Jt Ft)
      okR = ∧-fst ok₁
      okJF : T (claimsOK K Rt Jt Ft ∧ fvOK K Rt Jt Ft)
      okJF = ∧-snd {itemsOK K Rt Jt Ft} ok₁

      hR : ∀ k it → Rof K Rt Jt Ft k ≡ just it → T (itemOK k it)
      hR k it e = found-ok itemOf (okI K Rt Jt Ft) (λ _ → tt) Rt okR k e

      hF : ∀ n xs → Fof K Rt Jt Ft n ≡ just xs → T (fOK n xs)
      hF n xs e = found-ok fvOf (okF K Rt Jt Ft) (λ _ → tt) Ft
                    (∧-snd {claimsOK K Rt Jt Ft} okJF) n e

      hJ : ∀ c n A → Jof K Rt Jt Ft c n ≡ just A →
           Σ (Nat → Maybe RTy) λ Jc → GoodBlock c Jc × (Jc n ≡ just A)
      hJ c n A e = go (lookupT c Jt) refl e
        where
        go : (m : Maybe NatMap) → lookupT c Jt ≡ m → lookJ₂ n m ≡ just A →
             Σ (Nat → Maybe RTy) λ Jc → GoodBlock c Jc × (Jc n ≡ just A)
        go (just t) et en = blockOf t , good , en
          where
          blk : T (allN (λ n′ v → okJ K Rt Jt Ft c (blockOf t) n′ (claimOf v)) t)
          blk = lookup-All {k = c} {t = Jt} (allT-All _ Jt (∧-fst okJF)) et
          good : GoodBlock c (blockOf t)
          good n′ A′ e′ = found-ok claimOf (okJ K Rt Jt Ft c (blockOf t)) (λ _ → tt) t blk n′ e′

    open Hyp okV hR hJ hF public

  certOK-sound : ∀ g n A Γ B → T (certOK K Rt Jt Ft g n A Γ B) → Σ Tm (λ w → Γ ⊢tm w ∶ B)
  certOK-sound g n A Γ B p =
    ⟦ n ⟧ , subst₂ (λ Δ X → Δ ⊢tm ⟦ n ⟧ ∶ X) eqΓ eqB (snd (root-sound tabs g n A cg ej))
    where
    r : T (rootOK K Rt Jt Ft g n A Γ B)
    r = ∧-fst p
    tabs : T (tablesOK K Rt Jt Ft)
    tabs = ∧-snd {rootOK K Rt Jt Ft g n A Γ B} p
    cg : T (isCtx (Rof K Rt Jt Ft g))
    cg = ∧-fst r
    r₁ = ∧-snd {isCtx (Rof K Rt Jt Ft g)} r
    ej : Jof K Rt Jt Ft g n ≡ just A
    ej = eqRM-sound (Jof K Rt Jt Ft g n) A (∧-fst r₁)
    r₂ = ∧-snd {eqRM (Jof K Rt Jt Ft g n) A} r₁
    eqΓ : ⟦ g ⟧c ≡ Γ
    eqΓ = ==Ctx-sound ⟦ g ⟧c Γ (∧-fst r₂)
    eqB : ⟦ A ⟧ty ≡ B
    eqB = ==Ty-sound ⟦ A ⟧ty B (∧-snd {⟦ g ⟧c ==Ctx Γ} r₂)
    subst₂ : ∀ {X Y : Set} (P : X → Y → Set) {x x' y y'} → x ≡ x' → y ≡ y' → P x y → P x' y'
    subst₂ P refl refl q = q

-- The end-to-end statement used by generated modules: a certificate the
-- checker accepts yields a derivation of the query Γ ⊢ w ∶ B, for the
-- query given in ordinary syntax.
certified : ∀ K (is cs fs : List String) g n (A : List Nat) Γ B →
            runCert K is cs fs g n A Γ B ≡ true → Σ Tm (λ w → Γ ⊢tm w ∶ B)
certified K is cs fs g n A Γ B ok =
  Concrete.certOK-sound K (natmap (nums is)) (claims (nums cs)) (natmap (nums fs))
    g n (fst (rty A)) Γ B (true-T ok)

------------------------------------------------------------------------
-- Queries given as their own table (CaTTExp.Dag.QEq)

module ConcreteQ (K : Nat) (Rt : NatMap) (Jt : Trie NatMap) (Ft : NatMap) (Qt : NatMap) where
  open Concrete K Rt Jt Ft
  open import CaTTExp.Dag.Check K (Rof K Rt Jt Ft) (Jof K Rt Jt Ft) (Fof K Rt Jt Ft)
  open import CaTTExp.Dag.QEq (Qof K Rt Jt Ft Qt) (Rof K Rt Jt Ft)
  import CaTTExp.Dag.Unfold (Qof K Rt Jt Ft Qt) as UQ′
  import CaTTExp.Dag.Unfold (Rof K Rt Jt Ft) as UR′

  certQOK-sound : ∀ g n A qg qA → T (certQOK K Rt Jt Ft Qt g n A qg qA) →
                  Σ Tm (λ w → UQ′.⟦ qg ⟧c ⊢tm w ∶ UQ′.⟦ qA ⟧ty)
  certQOK-sound g n A qg qA p =
    UR′.⟦ n ⟧ ,
    subst₂ (λ Δ X → Δ ⊢tm UR′.⟦ n ⟧ ∶ X) (sym (fst eqs)) (sym (snd eqs))
      (snd (root-sound tabs g n A cg ej))
    where
    r : T (rootQOK K Rt Jt Ft Qt g n A qg qA)
    r = ∧-fst p
    tabs : T (tablesOK K Rt Jt Ft)
    tabs = ∧-snd {rootQOK K Rt Jt Ft Qt g n A qg qA} p
    cg : T (isCtx (Rof K Rt Jt Ft g))
    cg = ∧-fst r
    r₁ = ∧-snd {isCtx (Rof K Rt Jt Ft g)} r
    ej : Jof K Rt Jt Ft g n ≡ just A
    ej = Generic.eqRM-sound K (Rof K Rt Jt Ft) (Jof K Rt Jt Ft) (Fof K Rt Jt Ft)
           (Jof K Rt Jt Ft g n) A (∧-fst r₁)
    r₂ = ∧-snd {eqRM (Jof K Rt Jt Ft g n) A} r₁
    qd : T (qdecOK K Rt Jt Ft Qt)
    qd = ∧-fst r₂
    decQ : UQ.Decreasing
    decQ k it e = found-ok itemOf (okD K Rt Jt Ft Qt) (λ _ → tt) Qt qd k e
    eqs = Sound.qeqOK-sound decQ (dec tabs) (qfuel K Rt Jt Ft Qt) qg g qA A (∧-snd {qdecOK K Rt Jt Ft Qt} r₂)
    subst₂ : ∀ {X Y : Set} (P : X → Y → Set) {x x' y y'} → x ≡ x' → y ≡ y' → P x y → P x' y'
    subst₂ P refl refl q = q

  ctxQOK-sound : ∀ g qg → T (ctxQOK K Rt Jt Ft Qt g qg) → UQ′.⟦ qg ⟧c ⊢ctx
  ctxQOK-sound g qg p =
    subst _⊢ctx (sym (Sound.qeqCOK-sound decQ (dec tabs) (qfuel K Rt Jt Ft Qt) qg g (∧-snd {qdecOK K Rt Jt Ft Qt} r₂)))
      (fst (snd (sem tabs g)) cg)
    where
    r : T (isCtx (Rof K Rt Jt Ft g) ∧ (qdecOK K Rt Jt Ft Qt ∧ qeqCOK (qfuel K Rt Jt Ft Qt) qg g))
    r = ∧-fst p
    tabs : T (tablesOK K Rt Jt Ft)
    tabs = ∧-snd {isCtx (Rof K Rt Jt Ft g) ∧ (qdecOK K Rt Jt Ft Qt ∧ qeqCOK (qfuel K Rt Jt Ft Qt) qg g)} p
    cg : T (isCtx (Rof K Rt Jt Ft g))
    cg = ∧-fst r
    r₂ = ∧-snd {isCtx (Rof K Rt Jt Ft g)} r
    decQ : UQ.Decreasing
    decQ k it e = found-ok itemOf (okD K Rt Jt Ft Qt) (λ _ → tt) Qt (∧-fst r₂) k e

-- The end-to-end statement for a query given as a table: a certificate
-- the checker accepts yields a derivation of the query, i.e. of the
-- unfolding of the query table.
certifiedQ : ∀ K (is cs fs qs : List String) g n (A : List Nat) qg (qA : List Nat) →
             runCertQ K is cs fs qs g n A qg qA ≡ true →
             Σ Tm (λ w → queryCtxOf qs qg ⊢tm w ∶ queryTyOf qs qA)
certifiedQ K is cs fs qs g n A qg qA ok =
  ConcreteQ.certQOK-sound K (natmap (nums is)) (claims (nums cs)) (natmap (nums fs)) (natmap (nums qs))
    g n (fst (rty A)) qg (fst (rty qA)) (true-T ok)

queryMatches-sound : ∀ qs qg qA Γ B → queryMatches qs qg qA Γ B ≡ true →
                     (queryCtxOf qs qg ≡ Γ) × (queryTyOf qs qA ≡ B)
queryMatches-sound qs qg qA Γ B ok =
  ==Ctx-sound _ Γ (∧-fst p) , ==Ty-sound _ B (∧-snd {ctxIn (natmap (nums qs)) qg ==Ctx Γ} p)
  where
  p = true-T ok

-- A context given as a table (queryCtxOf) is well formed, when the
-- checker accepts a certificate for it.
certifiedCtxQ : ∀ K (is cs fs qs : List String) g qg →
                runCtxQ K is cs fs qs g qg ≡ true → queryCtxOf qs qg ⊢ctx
certifiedCtxQ K is cs fs qs g qg ok =
  ConcreteQ.ctxQOK-sound K (natmap (nums is)) (claims (nums cs)) (natmap (nums fs)) (natmap (nums qs))
    g qg (true-T ok)
