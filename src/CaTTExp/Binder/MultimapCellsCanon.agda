------------------------------------------------------------------------
-- The canonical head of a term is canonical (ledger S26j, step 2b):
-- in a well-formed context, if b infers and the atoms around it are
-- below k, then canon k Φ b is a fixed point of canon.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsCanon where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Gray.Biclosed.ListLemmas using (length-map)
open import CaTTExp.Binder.Multimap using (MMI; mmi; mctx; mterm; _==MM_)
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen
  using (T-if; F-if; dec; inl; inr; strengthen; lookup-idx; filter-elem; upTo-elem; closeFrom-mono; nthY-just; lookup-map)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; Deps↓; lookup-some)
open import CaTTExp.Binder.MultimapCellsRen
open import CaTTExp.Binder.MultimapCellsComp

------------------------------------------------------------------------
-- Small facts.

idx-map-suc : ∀ i xs → idx (suc i) (map suc xs) ≡ idx i xs
idx-map-suc i []       = refl
idx-map-suc i (x ∷ xs) with i ==ℕ x
... | true  = refl
... | false = cong suc (idx-map-suc i xs)

idx-upTo : ∀ a i → T (i <ℕ a) → idx i (upTo a) ≡ i
idx-upTo (suc a) zero    _ rewrite upTo-cons a = refl
idx-upTo (suc a) (suc i) l rewrite upTo-cons a = cong suc (trans (idx-map-suc i (upTo a)) (idx-upTo a i l))

length-upTo : ∀ a → length (upTo a) ≡ a
length-upTo zero    = refl
length-upTo (suc a) rewrite upTo-cons a = cong suc (trans (length-map suc (upTo a)) (length-upTo a))

nthY-suc : ∀ A Γ i → nthY (A ∷ Γ) (suc i) ≡ nthY Γ i
nthY-suc A Γ i with lookup Γ i
... | just _  = refl
... | nothing = refl

map-nthY-upTo : ∀ Γ → map (nthY Γ) (upTo (length Γ)) ≡ Γ
map-nthY-upTo []      = refl
map-nthY-upTo (A ∷ Γ) rewrite upTo-cons (length Γ) =
  cong (A ∷_) (trans (map-map′ (nthY (A ∷ Γ)) suc (upTo (length Γ)))
               (trans (map-ext (λ i → nthY-suc A Γ i) (upTo (length Γ))) (map-nthY-upTo Γ)))
  where
  map-map′ : ∀ {B : Set} (f : Nat → B) (g : Nat → Nat) xs → map f (map g xs) ≡ map (λ i → f (g i)) xs
  map-map′ f g []       = refl
  map-map′ f g (x ∷ xs) = cong (f (g x) ∷_) (map-map′ f g xs)
  map-ext : ∀ {B : Set} {f g : Nat → B} → (∀ i → f i ≡ g i) → ∀ xs → map f xs ≡ map g xs
  map-ext h []       = refl
  map-ext h (x ∷ xs) = cong₂ _∷_ (h x) (map-ext h xs)

filter-all : ∀ (P : Nat → Bool) xs → (∀ i → In xs i → T (P i)) → filter P xs ≡ xs
filter-all P []       h = refl
filter-all P (x ∷ xs) h rewrite T-if (P x) {x = x ∷ filter P xs} {y = filter P xs} (h x (∨-l (x ==ℕ x) _ (==ℕ-refl x))) =
  cong (x ∷_) (filter-all P xs (λ i p → h i (∨-r (i ==ℕ x) _ p)))

map-idx-self : ∀ xs → NoDup xs → map (λ i → idx i xs) xs ≡ upTo (length xs)
map-idx-self xs nd =
  trans (cong (map (λ i → idx i xs)) (sym (filter-all (λ _ → true) xs (λ _ _ → tt))))
    (trans (idx-filter (λ _ → true) xs nd) (filter-all (λ _ → true) (upTo (length xs)) (λ _ _ → tt)))

mapᵍ-cong : ∀ {B : Set} (f g : Nat → B) xs → (∀ i → In xs i → f i ≡ g i) → map f xs ≡ map g xs
mapᵍ-cong f g []       h = refl
mapᵍ-cong f g (x ∷ xs) h =
  cong₂ _∷_ (h x (∨-l (x ==ℕ x) _ (==ℕ-refl x))) (mapᵍ-cong f g xs (λ i p → h i (∨-r (i ==ℕ x) _ p)))

mapᵍ-map : ∀ {B C : Set} (f : B → C) (g : Nat → B) xs → map f (map g xs) ≡ map (λ i → f (g i)) xs
mapᵍ-map f g []       = refl
mapᵍ-map f g (x ∷ xs) = cong (f (g x) ∷_) (mapᵍ-map f g xs)

mapG-map : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
mapG-map f g []       = refl
mapG-map f g (x ∷ xs) = cong (f (g x) ∷_) (mapG-map f g xs)

==MM-refl : ∀ h → T (h ==MM h)
==MM-refl (mmi k Φ t) = ∧-in (==ℕ-refl k) (∧-in (eqCtx-refl Φ) (eqTm-refl t))
  where
  ∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in {true} _ q = q

mapᵗ-cong : ∀ (f g : CTy → CTy) xs → (∀ A → f A ≡ g A) → map f xs ≡ map g xs
mapᵗ-cong f g []       h = refl
mapᵗ-cong f g (x ∷ xs) h = cong₂ _∷_ (h x) (mapᵗ-cong f g xs h)

atY-concatAt : ∀ (f : Nat → CTy) xs x → In xs x → atY (f x) ⊆ concatAt (map f xs)
atY-concatAt f (y ∷ xs) x p i q with dec (x ==ℕ y)
... | inl e rewrite ==ℕ-sound x y e = elem-++l i (atY (f y)) (concatAt (map f xs)) q
... | inr e = elem-++r i (atY (f y)) (concatAt (map f xs)) (atY-concatAt f xs x (or-r (x ==ℕ y) _ e p) i q)
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

-- The shape of a canonical head, as a function of its atoms and entries.
headOf : Nat → Ctx → Tm → List Nat → List Nat → MMI
headOf K Ψ s as′ vs′ = mmi (length as′) (map (sY (renOf as′ vs′)) (map (nthY Ψ) vs′)) (sT (renOf as′ vs′) s)

cidx-canon : ∀ K Ψ s → cidx (canon K Ψ s) ≡ headOf K Ψ s (supAtoms K Ψ s) (supVars Ψ s)
cidx-canon K Ψ s = refl

module Idem (k : Nat) (Φ : Ctx) (w : T (wfCtx Φ)) (b : Tm) {B : CTy} (eB : infer Φ b ≡ just B)
            (ab : ∀ i → In (supAtomsOf Φ b) i → T (i <ℕ k)) where

  dd : Deps↓ Φ
  dd j e = wf-deps Φ j w e

  asb : List Nat
  asb = supAtoms k Φ b

  open SupportRen Φ dd (varsT b) asb public

  bvs : varsT b ⊆ vs
  bvs i p = vs-in i (closeFrom-mono Φ n (varsT b) i p) (infer-scope Φ b eB i p)

  open ForTerm b bvs public

  ra : Nat → Nat
  ra i = idx i asb

  S : List Nat
  S = supAtomsOf Φ b

  asb-inc : Inc asb
  asb-inc = inc-filter _ (upTo k) (inc-upTo k)

  asb-nd : NoDup asb
  asb-nd = inc-nodup asb asb-inc

  S-in : ∀ i → In S i → In asb i
  S-in i p = filter-elem (λ i → elem i S) (upTo k) i p (upTo-elem k i (ab i p))

  G1 : supVars Φ′ b′ ≡ upTo m
  G1 = trans supVars-ren (map-idx-self vs vs-nd)

  nthY-Φ′ : ∀ j → In vs j → nthY Φ′ (rr j) ≡ sY ρ (nthY Φ j)
  nthY-Φ′ j p =
    let (A , eA) = lookup-some Φ j (vs-lt j p) in
    trans (nthY-just Φ′ (rr j) (lookup-Φ′-r j eA p)) (cong (sY ρ) (sym (nthY-just Φ j eA)))

  infer-b′ : infer Φ′ b′ ≡ just (sY ρ B)
  infer-b′ = strengthen k Φ b B eB

  types′ : map (nthY Φ′) (supVars Φ′ b′) ≡ map (sY ρ) (map (nthY Φ) vs)
  types′ = trans (cong (map (nthY Φ′)) supVars-ren)
             (trans (mapᵍ-map (nthY Φ′) rr vs)
               (trans (mapᵍ-cong _ _ vs nthY-Φ′) (sym (mapᵍ-map (sY ρ) (nthY Φ) vs))))

  open AtRen asb vs using (atT-ren; atY-ren; concatAt-ren)

  G2a : supAtomsOf Φ′ b′ ≡ map ra S
  G2a =
    trans (cong₂ (λ X Y → concatAt X ++ atT b′ ++ atYM Y) types′ infer-b′)
      (trans (cong₂ _++_ (concatAt-ren (map (nthY Φ) vs)) (cong₂ _++_ (atT-ren b) (atY-ren B)))
        (trans (cong (map ra (concatAt (map (nthY Φ) vs)) ++_) (sym (map-++ ra (atT b) (atY B))))
          (trans (sym (map-++ ra (concatAt (map (nthY Φ) vs)) (atT b ++ atY B)))
                 (cong (λ Y → map ra (concatAt (map (nthY Φ) vs) ++ atT b ++ Y)) (sym (cong atYM eB))))))

  G2 : supAtoms (length asb) Φ′ b′ ≡ upTo (length asb)
  G2 = trans (cong (λ X → filter (λ i → elem i X) (upTo (length asb))) G2a)
         (filter-all _ (upTo (length asb)) (λ p up →
           let l = upTo-In-inv (length asb) p up
               x = nth asb p
               xin = nth-In asb p l
               (xS , _) = filter-In-inv (λ i → elem i S) (upTo k) x xin
           in subst (λ z → In (map ra S) z) (idx-nth asb asb-nd p l) (In-map ra S x xS)))

  ρ″ : Sub
  ρ″ = renOf (upTo (length asb)) (upTo m)

  fixA : ∀ xs → xs ⊆ asb → FixA ρ″ (map ra xs)
  fixA xs h a p =
    let (x , xin , e) = In-map-inv ra xs a p
        l = subst (λ z → T (z <ℕ length asb)) (sym e) (idx-lt asb x (h x xin))
    in cong obj (idx-upTo (length asb) a l)

  fixV : ∀ xs → xs ⊆ vs → FixV ρ″ (map rr xs)
  fixV xs h i p =
    let (x , xin , e) = In-map-inv rr xs i p
        l = subst (λ z → T (z <ℕ m)) (sym e) (idx-lt vs x (h x xin))
    in trans (T-if (elem i (upTo m)) (upTo-elem m i l)) (cong var (idx-upTo m i l))

  fix-b′ : sT ρ″ b′ ≡ b′
  fix-b′ = fixT ρ″ b′
    (subst (FixA ρ″) (sym (atT-ren b))
      (fixA (atT b) (λ i p → S-in i (elem-++r i (concatAt (map (nthY Φ) vs)) (atT b ++ atYM (infer Φ b))
                                      (elem-++l i (atT b) (atYM (infer Φ b)) p)))))
    (subst (FixV ρ″) (sym vars-b′) (fixV (varsT b) bvs))

  fix-entry : ∀ j → In vs j → sY ρ″ (sY ρ (nthY Φ j)) ≡ sY ρ (nthY Φ j)
  fix-entry j p =
    let (A , eA) = lookup-some Φ j (vs-lt j p)
        A≡ = nthY-just Φ j eA
    in fixY ρ″ (sY ρ (nthY Φ j))
         (subst (FixA ρ″) (sym (atY-ren (nthY Φ j)))
           (fixA (atY (nthY Φ j)) (λ i q → S-in i (elem-++l i (concatAt (map (nthY Φ) vs)) _
                                                   (atY-concatAt (nthY Φ) vs j p i q)))))
         (subst (FixV ρ″) (sym (varsY-ren asb vs (nthY Φ j) (subst (λ B → varsY B ⊆ vs) (sym A≡) (vs-closed j eA p))))
           (fixV (varsY (nthY Φ j)) (subst (λ B → varsY B ⊆ vs) (sym A≡) (vs-closed j eA p))))

  fix-Φ′ : map (sY ρ″) Φ′ ≡ Φ′
  fix-Φ′ =
    trans (mapG-map (sY ρ″) (sY ρ) (map (nthY Φ) vs))
      (trans (mapG-map (λ A → sY ρ″ (sY ρ A)) (nthY Φ) vs)
        (trans (mapᵍ-cong _ _ vs fix-entry)
          (sym (mapG-map (sY ρ) (nthY Φ) vs))))

  -- The canonical head of b is canonical.
  canon-idem : cidx (canon (length asb) Φ′ b′) ≡ mmi (length asb) Φ′ b′
  canon-idem =
    trans (cong₂ (headOf (length asb) Φ′ b′) G2 G1)
      (cong₃′ mmi (length-upTo (length asb))
        (trans (cong (map (sY ρ″)) (trans (cong (λ z → map (nthY Φ′) (upTo z)) (sym len-Φ′)) (map-nthY-upTo Φ′))) fix-Φ′)
        fix-b′)

  isCanon-sub : T (isCanon (cidx (canon k Φ b)))
  isCanon-sub = subst (λ h → T (h ==MM mmi (length asb) Φ′ b′)) (sym canon-idem)
                  (==MM-refl (mmi (length asb) Φ′ b′))
