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

------------------------------------------------------------------------
-- Dimension facts for the coh case of (1′).

open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; wf-bd)
open import CaTTExp.GlobularFiller using (merge)
open Lists using (headN)

private
  0+ : ∀ e → e ≡ e + 0
  0+ zero    = refl
  0+ (suc e) = cong suc (0+ e)

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  ==-refl : ∀ a → (a ==ℕ a) ≡ true
  ==-refl a = T-≡ (==ℕ-refl a)

-- With no node of depth j having a branch, a tree is its own j-boundary.
mutual
  nokid-thin : ∀ j a → WF a → (HasKid j a → ⊥) → ∀ β → bd β j a ≡ a
  nokid-thin zero    (lt os (c ∷ cs))  w nk β = ⊥-elim (nk tt)
  nokid-thin zero    (lt [] [])        (() , _) nk β
  nokid-thin zero    (lt (o ∷ []) [])  w nk false = refl
  nokid-thin zero    (lt (o ∷ []) [])  w nk true  = refl
  nokid-thin zero    (lt (o ∷ o' ∷ os) []) (() , _) nk β
  nokid-thin (suc j) (lt os cs)        (_ , ws) nk β = bd-suc β
    where
    bd-suc : ∀ β → bd β (suc j) (lt os cs) ≡ lt os cs
    bd-suc false = cong (lt os) (nokids-thin j cs ws nk false)
    bd-suc true  = cong (lt os) (nokids-thin j cs ws nk true)

  nokids-thin : ∀ j cs → WFs cs → (AnyKid j cs → ⊥) → ∀ β → bdL β j cs ≡ cs
  nokids-thin j []       _        nk β = refl
  nokids-thin j (c ∷ cs) (w , ws) nk β =
    cong₂ _∷_ (nokid-thin j c w (λ h → nk (inl h)) β) (nokids-thin j cs ws (λ h → nk (inr h)) β)

-- A k-boundary has no branches at depth ≥ k.
mutual
  bd-nokid : ∀ β k i a → HasKid (k + i) (bd β k a) → ⊥
  bd-nokid false zero zero    (lt os cs) ()
  bd-nokid true  zero zero    (lt os cs) ()
  bd-nokid false zero (suc i) (lt os cs) ()
  bd-nokid true  zero (suc i) (lt os cs) ()
  bd-nokid false (suc k) i (lt os cs) h = bdL-nokid false k i cs h
  bd-nokid true  (suc k) i (lt os cs) h = bdL-nokid true  k i cs h

  bdL-nokid : ∀ β k i cs → AnyKid (k + i) (bdL β k cs) → ⊥
  bdL-nokid β k i []       ()
  bdL-nokid β k i (c ∷ cs) (inl h) = bd-nokid β k i c h
  bdL-nokid β k i (c ∷ cs) (inr h) = bdL-nokid β k i cs h

-- Boundaries above k of a k-boundary change nothing.
bd-idem : ∀ β β' k i a → WF a → bd β (k + i) (bd β' k a) ≡ bd β' k a
bd-idem β β' k i a w = nokid-thin (k + i) (bd β' k a) (wf-bd β' k a w) (bd-nokid β' k i a) β

-- Every type in a context has dimension at most that of the context.
private
  ≤-maxl : ∀ a b → T (a <ℕ suc (max a b))
  ≤-maxl zero    b       = tt
  ≤-maxl (suc a) zero    = <-suc a
  ≤-maxl (suc a) (suc b) = ≤-maxl a b

  ≤-maxr : ∀ a b → T (b <ℕ suc (max a b))
  ≤-maxr zero    b       = <-suc b
  ≤-maxr (suc a) zero    = tt
  ≤-maxr (suc a) (suc b) = ≤-maxr a b

  ≤-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
  ≤-trans zero    b       c       p q = tt
  ≤-trans (suc a) zero    c       () q
  ≤-trans (suc a) (suc b) zero    p ()
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

var-dim-le : ∀ Γ y A → lookup Γ y ≡ just A → T (dim A <ℕ suc (dimCtx Γ))
var-dim-le ε       y A ()
var-dim-le (Γ ▸ C) y A e with y ==ℕ len Γ
... | true rewrite just-inj (sym e) = ≤-maxl (dim C) (dimCtx Γ)
... | false = ≤-trans (dim A) (dimCtx Γ) (max (dim C) (dimCtx Γ))
                (var-dim-le Γ y A e) (≤-maxr (dim C) (dimCtx Γ))

module _ (Θ : Ctx) where

  private
    allN-mem : ∀ {P : Nat → Set} y xs → AllN P xs → memL y xs ≡ true → P y
    allN-mem y []       _        ()
    allN-mem y (x ∷ xs) (p , pp) e with y ==ℕ x in eq
    ... | true  = subst _ (sym (==ℕ-sound y x (≡-T eq))) p
    ... | false = allN-mem y xs pp e

    cell-dim : ∀ e par o → Cell Θ e par o → dimOf Θ o ≡ e
    cell-dim e nothing        o (_ , d) = d
    cell-dim e (just (p , q)) o (_ , d) = d

    cell-lookup : ∀ e par o → Cell Θ e par o → Σ Ty λ A → lookup Θ o ≡ just A
    cell-lookup e nothing        o (c , _) = c
    cell-lookup e (just (p , q)) o ((B , eB) , _) = arr B (var p) (var q) , eB

  -- Diagrams are well formed.
  mutual
    ex-wf : ∀ e par a → Ex Θ e par a → WF a
    ex-wf e par (lt os cs) (_ , x) = exCs-wf e os cs x

    exCs-wf : ∀ e os cs → ExCs Θ e os cs → WF (lt os cs)
    exCs-wf e []            cs       ()
    exCs-wf e (o ∷ [])      []       _ = refl , tt
    exCs-wf e (o ∷ [])      (c ∷ cs) ()
    exCs-wf e (o ∷ o' ∷ os) []       ()
    exCs-wf e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) with exCs-wf e (o' ∷ os) cs xs
    ... | l , ws = cong suc l , (ex-wf (suc e) _ c xc , ws)

  -- Labels of a diagram are variables.
  mutual
    mem-cell : ∀ e par a y → Ex Θ e par a → mem y a ≡ true → Σ Ty λ A → lookup Θ y ≡ just A
    mem-cell e par (lt os cs) y (oks , x) m with ∨-split (memL y os) (memCs y cs) m
    ... | inl mo = cell-lookup e par y (allN-mem y os oks mo)
    ... | inr mc = memCs-cell e os cs y x mc

    memCs-cell : ∀ e os cs y → ExCs Θ e os cs → memCs y cs ≡ true → Σ Ty λ A → lookup Θ y ≡ just A
    memCs-cell e os            []       y x ()
    memCs-cell e []            (c ∷ cs) y () m
    memCs-cell e (o ∷ [])      (c ∷ cs) y () m
    memCs-cell e (o ∷ o' ∷ os) (c ∷ cs) y (xc , xs) m with ∨-split (mem y c) (memCs y cs) m
    ... | inl mc = mem-cell (suc e) _ c y xc mc
    ... | inr ms = memCs-cell e (o' ∷ os) cs y xs ms

  -- A branch at depth k carries a label of dimension e + k + 1.
  mutual
    kid-deep : ∀ k e par a → Ex Θ e par a → HasKid k a →
               Σ Nat λ y → (mem y a ≡ true) × (dimOf Θ y ≡ e + suc k)
    kid-deep k e par (lt os cs) (_ , x) h = kids-deep k e os cs x h

    kids-deep : ∀ k e os cs → ExCs Θ e os cs → HasKid k (lt os cs) →
                Σ Nat λ y → (mem y (lt os cs) ≡ true) × (dimOf Θ y ≡ e + suc k)
    kids-deep k e []            cs       () h
    kids-deep k e (o ∷ [])      []       _ h with k
    ... | zero  = ⊥-elim h
    ... | suc _ = ⊥-elim h
    kids-deep k e (o ∷ [])      (c ∷ cs) () h
    kids-deep k e (o ∷ o' ∷ os) []       () h
    kids-deep zero e (o ∷ o' ∷ os) (lt [] cs' ∷ cs) ((_ , ()) , xs) h
    kids-deep zero e (o ∷ o' ∷ os) (lt (h' ∷ hs) cs' ∷ cs) (((ch , _) , _) , xs) h =
      h' ,
      ∨-inr (memL h' (o ∷ o' ∷ os)) _ (∨-inl (mem h' (lt (h' ∷ hs) cs')) _
        (∨-inl (memL h' (h' ∷ hs)) _ (∨-inl (h' ==ℕ h') _ (==-refl h')))) ,
      trans (cell-dim (suc e) (just (o , o')) h' ch) (sym (trans (+-suc e 0) (cong suc (sym (0+ e)))))
    kids-deep (suc k) e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inl hc) with kid-deep k (suc e) _ c xc hc
    ... | y , m , d =
      y , ∨-inr (memL y (o ∷ o' ∷ os)) _ (∨-inl (mem y c) _ m) ,
      trans d (sym (+-suc e (suc k)))
    kids-deep (suc k) e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inr hs)
      with kids-deep (suc k) e (o' ∷ os) cs xs hs
    ... | y , m , d = y , move y o o' os c cs m , d
      where
      move : ∀ y o o' os c cs → mem y (lt (o' ∷ os) cs) ≡ true → mem y (lt (o ∷ o' ∷ os) (c ∷ cs)) ≡ true
      move y o o' os c cs m with ∨-split (memL y (o' ∷ os)) (memCs y cs) m
      ... | inl mo = ∨-inl (memL y (o ∷ o' ∷ os)) _ (∨-inr (y ==ℕ o) _ mo)
      ... | inr mc = ∨-inr (memL y (o ∷ o' ∷ os)) _ (∨-inr (mem y c) _ mc)

  -- A branch at depth k leaves a label of dimension e + k in the source.
  mutual
    kid-src : ∀ k e par a → Ex Θ e par a → HasKid k a →
              Σ Nat λ y → (mem y (bd false k a) ≡ true) × (dimOf Θ y ≡ e + k)
    kid-src zero e par (lt [] (c ∷ cs)) (_ , ()) h
    kid-src zero e par (lt (o ∷ os) (c ∷ cs)) ((co , _) , _) h =
      o , ∨-inl ((o ==ℕ o) ∨ false) false (∨-inl (o ==ℕ o) false (==-refl o)) ,
      trans (cell-dim e par o co) (0+ e)
    kid-src (suc k) e par (lt os cs) (_ , x) h with kids-src k e os cs x h
    ... | y , m , d = y , ∨-inr (memL y os) _ m , d

    kids-src : ∀ k e os cs → ExCs Θ e os cs → AnyKid k cs →
               Σ Nat λ y → (memCs y (bdL false k cs) ≡ true) × (dimOf Θ y ≡ e + suc k)
    kids-src k e []            cs       () h
    kids-src k e (o ∷ [])      []       _ ()
    kids-src k e (o ∷ [])      (c ∷ cs) () h
    kids-src k e (o ∷ o' ∷ os) []       () h
    kids-src k e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inl hc) with kid-src k (suc e) _ c xc hc
    ... | y , m , d = y , ∨-inl (mem y (bd false k c)) _ m , trans d (sym (+-suc e k))
    kids-src k e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) (inr hs) with kids-src k e (o' ∷ os) cs xs hs
    ... | y , m , d = y , ∨-inr (mem y (bd false k c)) _ m , d

-- The tree of a pasting context has the dimension of the context.
private
  no-big : ∀ d i n → n ≡ suc (d + i) → T (n <ℕ suc d) → ⊥
  no-big zero    i .(suc (zero + i)) refl ()
  no-big (suc d) i .(suc (suc d + i)) refl p = no-big d i _ refl p

tree-dim : ∀ τ β i → bd β (dimCtx (ctxOf τ) + i) (idTree τ) ≡ idTree τ
tree-dim τ β i =
  nokid-thin (dimCtx Θ + i) (idTree τ) (ex-wf Θ 0 nothing (idTree τ) (lab-ex τ)) nk β
  where
  Θ = ctxOf τ
  nk : HasKid (dimCtx Θ + i) (idTree τ) → ⊥
  nk h with kid-deep Θ (dimCtx Θ + i) 0 nothing (idTree τ) (lab-ex τ) h
  ... | y , m , d with mem-cell Θ 0 nothing (idTree τ) y (lab-ex τ) m
  ...   | A , eA =
    no-big (dimCtx Θ) i (dim A) (trans (sym (dimOf-just Θ y A eA)) d) (var-dim-le Θ y A eA)

-- A context of dimension k+1: a label of dimension k+1, and a branch at depth k.
top-label : ∀ τ k → dimCtx (ctxOf τ) ≡ suc k →
            Σ Nat λ z → (mem z (idTree τ) ≡ true) × (dimOf (ctxOf τ) z ≡ suc k)
top-label τ k d with top-var′ (ctxOf τ) d
  where
  top-var′ : ∀ Γ → dimCtx Γ ≡ suc k → Σ Nat λ z → Σ Ty λ B → (lookup Γ z ≡ just B) × (dim B ≡ suc k)
  top-var′ ε ()
  top-var′ (Γ ▸ A) d with top-var Γ A
  ... | z , B , ez , dz = z , B , ez , trans dz d
... | z , B , ez , dz =
  z , trans (lab-all τ z) (T-≡ (lookup-lt (ctxOf τ) z B ez)) , trans (dimOf-just (ctxOf τ) z B ez) dz

kid-top : ∀ τ k → dimCtx (ctxOf τ) ≡ suc k → HasKid k (idTree τ)
kid-top τ k d with top-label τ k d
... | z , m , dz = mem-kid (ctxOf τ) (ps-ord (snd (psOf τ))) 0 nothing (idTree τ) z k (lab-ex τ) m dz
