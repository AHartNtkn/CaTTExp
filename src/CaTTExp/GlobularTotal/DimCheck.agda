------------------------------------------------------------------------
-- F2c, for the coh case of (1′): a pasting context of dimension ≥ 1
-- has different source and target.
--
--   bd-distinct : dimCtx (ctxOf τ) ≡ suc k → bd false k (idTree τ) ≡ bd true k (idTree τ) → ⊥
--
-- A variable of top dimension k+1 is a label of idTree τ, so some node
-- of depth k has a child (mem-kid); at that node bd false keeps the
-- first object and bd true the last, and the objects of a node
-- strictly increase (Uniq.objs-inc), so the two differ (kid-bd-ne).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.DimCheck where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; bdL; idTree; module Lists)
open Lists using (lastN)
open import CaTTExp.GlobularTotal.Uniq
  using (mem; memCs; memL; AllN; Cell; Ex; ExCs; dimOf; Inc; Above; objs-inc)
open import CaTTExp.GlobularTotal.PsOrd using (ps-ord)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  <-irr : ∀ a → T (a <ℕ a) → ⊥
  <-irr zero    ()
  <-irr (suc a) p = <-irr a p

  ∷-injₕ : ∀ {x y : Nat} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-injₕ refl = refl

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ' : ∀ {x y : LT} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-injₕ' refl = refl

  ∷-injₜ' : ∀ {x y : LT} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-injₜ' refl = refl

  suc≢ : ∀ e k → e ≡ e + suc k → ⊥
  suc≢ zero    k ()
  suc≢ (suc e) k p = suc≢ e k (cong pred p)
    where
    pred : Nat → Nat
    pred zero    = zero
    pred (suc n) = n

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  above-last : ∀ o o' os → Above o (o' ∷ os) → T (o <ℕ lastN (o' ∷ os))
  above-last o o' []        (p , _) = p
  above-last o o' (o'' ∷ os) (_ , ab) = above-last o o'' os ab

-- a has a node of depth k with at least one branch.
mutual
  HasKid : Nat → LT → Set
  HasKid zero    (lt os [])      = ⊥
  HasKid zero    (lt os (_ ∷ _)) = ⊤
  HasKid (suc k) (lt os cs)      = AnyKid k cs

  AnyKid : Nat → List LT → Set
  AnyKid k []       = ⊥
  AnyKid k (c ∷ cs) = HasKid k c ⊎ AnyKid k cs

module _ (Θ : Ctx) (ord : ∀ y B a b → lookup Θ y ≡ just (arr B (var a) (var b)) → T (a <ℕ b)) where

  private
    allN-mem : ∀ {P : Nat → Set} y xs → AllN P xs → memL y xs ≡ true → P y
    allN-mem y []       _        ()
    allN-mem y (x ∷ xs) (p , pp) e with y ==ℕ x in eq
    ... | true  = subst _ (sym (==ℕ-sound y x (≡-T eq))) p
    ... | false = allN-mem y xs pp e

    cell-dim : ∀ e par o → Cell Θ e par o → dimOf Θ o ≡ e
    cell-dim e nothing        o (_ , d) = d
    cell-dim e (just (p , q)) o (_ , d) = d

  mutual
    kid-bd-ne : ∀ k e par a → Ex Θ e par a → HasKid k a → bd false k a ≡ bd true k a → ⊥
    kid-bd-ne zero e par (lt [] (c ∷ cs)) (_ , ()) h q
    kid-bd-ne zero e par (lt (o ∷ []) (c ∷ cs)) (_ , ()) h q
    kid-bd-ne zero e par (lt (o ∷ o' ∷ os) (c ∷ cs)) (_ , x) h q
      with objs-inc Θ ord e (o ∷ o' ∷ os) (c ∷ cs) x
    ... | ab , _ rewrite ∷-injₕ (lt-injₒ q) = <-irr (lastN (o' ∷ os)) (above-last (lastN (o' ∷ os)) o' os ab)
    kid-bd-ne (suc k) e par (lt os cs) (_ , x) h q =
      kids-ne k e os cs x h (lt-injₛ q)

    kids-ne : ∀ k e os cs → ExCs Θ e os cs → AnyKid k cs → bdL false k cs ≡ bdL true k cs → ⊥
    kids-ne k e []            cs       () h q
    kids-ne k e (o ∷ [])      []       _ () q
    kids-ne k e (o ∷ [])      (c ∷ cs) () h q
    kids-ne k e (o ∷ o' ∷ os) []       () h q
    kids-ne k e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inl hc) q =
      kid-bd-ne k (suc e) _ c xc hc (∷-injₕ' q)
    kids-ne k e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inr hs) q =
      kids-ne k e (o' ∷ os) cs xs hs (∷-injₜ' q)

  -- A label of dimension e + k + 1 in a diagram at depth e sits below
  -- a node of depth k with a branch.
  mutual
    mem-kid : ∀ e par a y k → Ex Θ e par a → mem y a ≡ true → dimOf Θ y ≡ e + suc k → HasKid k a
    mem-kid e par (lt os cs) y k (oks , x) m d with ∨-split (memL y os) (memCs y cs) m
    ... | inl mo = ⊥-elim (suc≢ e k (trans (sym (cell-dim e par y (allN-mem y os oks mo))) d))
    ... | inr mc = memCs-kid e os cs y k x mc d

    memCs-kid : ∀ e os cs y k → ExCs Θ e os cs → memCs y cs ≡ true → dimOf Θ y ≡ e + suc k →
                HasKid k (lt os cs)
    memCs-kid e os [] y k x () d
    memCs-kid e os (c ∷ cs) y zero x m d = tt
    memCs-kid e os (c ∷ cs) y (suc k) x m d = kids e os c cs y k x m d
      where
      kids : ∀ e os c cs y k → ExCs Θ e os (c ∷ cs) → memCs y (c ∷ cs) ≡ true →
             dimOf Θ y ≡ e + suc (suc k) → AnyKid k (c ∷ cs)
      kids e []            c cs y k () m d
      kids e (o ∷ [])      c cs y k () m d
      kids e (o ∷ o' ∷ os) c cs y k (xc , xs) m d with ∨-split (mem y c) (memCs y cs) m
      ... | inl mc = inl (mem-kid (suc e) _ c y k xc mc (trans d (+-suc e (suc k))))
      kids e (o ∷ o' ∷ os) c [] y k (xc , xs) m d | inr ()
      kids e (o ∷ o' ∷ os) c (c' ∷ cs) y k (xc , xs) m d | inr ms =
        inr (kids e (o' ∷ os) c' cs y k xs ms d)

------------------------------------------------------------------------
-- A context of dimension k+1 has a variable of dimension k+1.

private
  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = <-suc (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

  lookup-top : ∀ Γ C → lookup (Γ ▸ C) (len Γ) ≡ just C
  lookup-top Γ C rewrite T-≡ (==ℕ-refl (len Γ)) = refl

  lookup-weak : ∀ Γ C y A → lookup Γ y ≡ just A → lookup (Γ ▸ C) y ≡ just A
  lookup-weak Γ C y A e rewrite <-ne y (len Γ) (lookup-lt Γ y A e) = e

  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

  max-l : ∀ a b → T (b <ℕ suc a) → max a b ≡ a
  max-l zero    zero    p = refl
  max-l zero    (suc b) ()
  max-l (suc a) zero    p = refl
  max-l (suc a) (suc b) p = cong suc (max-l a b p)

  max-r : ∀ a b → (b <ℕ suc a) ≡ false → max a b ≡ b
  max-r zero    zero    ()
  max-r zero    (suc b) p = refl
  max-r (suc a) zero    ()
  max-r (suc a) (suc b) p = cong suc (max-r a b p)

  top-var : ∀ Γ A → Σ Nat λ z → Σ Ty λ B → (lookup (Γ ▸ A) z ≡ just B) × (dim B ≡ dimCtx (Γ ▸ A))
  top-var Γ A with dimCtx Γ <ℕ suc (dim A) in le
  ... | true  = len Γ , A , lookup-top Γ A , sym (max-l (dim A) (dimCtx Γ) (≡-T le))
  top-var ε A | false = ⊥-elim (lem (dim A) le)
    where
    lem : ∀ n → (0 <ℕ suc n) ≡ false → ⊥
    lem n ()
  top-var (Γ ▸ C) A | false with top-var Γ C
  ... | z , B , ez , dz =
    z , B , lookup-weak (Γ ▸ C) A z B ez , trans dz (sym (max-r (dim A) (dimCtx (Γ ▸ C)) le))

------------------------------------------------------------------------
-- The theorem.

bd-distinct : ∀ τ k → dimCtx (ctxOf τ) ≡ suc k → bd false k (idTree τ) ≡ bd true k (idTree τ) → ⊥
bd-distinct τ k d q with top-var′ (ctxOf τ) d
  where
  top-var′ : ∀ Γ → dimCtx Γ ≡ suc k → Σ Nat λ z → Σ Ty λ B → (lookup Γ z ≡ just B) × (dim B ≡ suc k)
  top-var′ ε ()
  top-var′ (Γ ▸ A) d with top-var Γ A
  ... | z , B , ez , dz = z , B , ez , trans dz d
... | z , B , ez , dz =
  kid-bd-ne Θ ord k 0 nothing (idTree τ) (lab-ex τ)
    (mem-kid Θ ord 0 nothing (idTree τ) z k (lab-ex τ)
       (trans (lab-all τ z) (T-≡ (lookup-lt Θ z B ez)))
       (trans (dimOf-just Θ z B ez) dz))
    q
  where
  Θ = ctxOf τ
  ord = ps-ord (snd (psOf τ))
