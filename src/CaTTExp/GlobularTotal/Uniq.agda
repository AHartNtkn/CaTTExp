------------------------------------------------------------------------
-- F2c, toward (1c): in a pasting context, a diagram is determined by
-- its set of labels (Uniq).
--
-- A diagram of Θ at depth e (`Ex`) is a labelled tree whose objects at
-- depth e are e-dimensional variables of Θ, and whose branch between
-- consecutive objects o, o′ is a diagram at depth e+1 of cells from o
-- to o′. The only property of Θ used is that sources come before
-- targets (`Ord`), a module parameter here; that every pasting context
-- has it is a separate lemma (to do).
--
--   uniq : Ex e par a → Ex e par b → (∀ y → mem y a ≡ mem y b) → a ≡ b
--
-- Proof: the objects of a node are its labels of dimension e, in
-- increasing order, so they are determined by the label set; a label of
-- a branch lies in the branch whose source object is its iterated
-- source at dimension e, so the label set of each branch is determined
-- too.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Uniq where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt)

------------------------------------------------------------------------
-- Arithmetic and booleans.

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  <-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  <-trans zero    (suc b) (suc c) p q = tt
  <-trans (suc a) (suc b) (suc c) p q = <-trans a b c p q
  <-trans a zero c () q
  <-trans zero (suc b) zero p ()
  <-trans (suc a) (suc b) zero p ()

  <-irrefl : ∀ a → T (a <ℕ a) → ⊥
  <-irrefl zero    ()
  <-irrefl (suc a) p = <-irrefl a p

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-≢ : ∀ a b → T (a <ℕ b) → (b ==ℕ a) ≡ false
  <-≢ zero    zero    ()
  <-≢ zero    (suc b) p = refl
  <-≢ (suc a) zero    ()
  <-≢ (suc a) (suc b) p = <-≢ a b p

  ==-sound : ∀ a b → (a ==ℕ b) ≡ true → a ≡ b
  ==-sound a b e = ==ℕ-sound a b (≡-T e)

  ==-refl : ∀ a → (a ==ℕ a) ≡ true
  ==-refl a = T-≡ (==ℕ-refl a)

  suc∸ : ∀ e → suc e ∸ e ≡ 1
  suc∸ zero    = refl
  suc∸ (suc e) = suc∸ e

  ∸-suc : ∀ d e → T (e <ℕ d) → d ∸ e ≡ suc (d ∸ suc e)
  ∸-suc (suc d) zero    p = refl
  ∸-suc (suc d) (suc e) p = ∸-suc d e p
  ∸-suc zero    e       ()

------------------------------------------------------------------------
-- Labels.

memL : Nat → List Nat → Bool
memL y []       = false
memL y (x ∷ xs) = (y ==ℕ x) ∨ memL y xs

mutual
  mem : Nat → LT → Bool
  mem y (lt os cs) = memL y os ∨ memCs y cs

  memCs : Nat → List LT → Bool
  memCs y []       = false
  memCs y (c ∷ cs) = mem y c ∨ memCs y cs

AllN : (Nat → Set) → List Nat → Set
AllN P []       = ⊤
AllN P (x ∷ xs) = P x × AllN P xs

private
  allN-mem : ∀ {P : Nat → Set} y xs → AllN P xs → memL y xs ≡ true → P y
  allN-mem y []       _        ()
  allN-mem y (x ∷ xs) (p , pp) e with y ==ℕ x in eq
  ... | true  = subst _ (sym (==-sound y x eq)) p
  ... | false = allN-mem y xs pp e

------------------------------------------------------------------------
-- Strictly increasing lists are determined by their members.

Above : Nat → List Nat → Set
Above x = AllN (λ z → T (x <ℕ z))

Inc : List Nat → Set
Inc []       = ⊤
Inc (x ∷ xs) = Above x xs × Inc xs

private
  above-not′ : ∀ x xs → Above x xs → memL x xs ≡ false
  above-not′ x []       _        = refl
  above-not′ x (z ∷ zs) (p , pp) with x ==ℕ z in eq
  ... | true  = ⊥-elim (<-irrefl x (subst (λ w → T (x <ℕ w)) (sym (==-sound x z eq)) p))
  ... | false = above-not′ x zs pp

  memL-head : ∀ y x xs → (y ==ℕ x) ≡ false → memL y (x ∷ xs) ≡ memL y xs
  memL-head y x xs e rewrite e = refl

inc-eq : ∀ xs ys → Inc xs → Inc ys → (∀ y → memL y xs ≡ memL y ys) → xs ≡ ys
inc-eq []       []       _ _ h = refl
inc-eq []       (y ∷ ys) _ _ h with h y
... | e rewrite ==-refl y = ⊥-elim (f e)
  where f : false ≡ true → ⊥
        f ()
inc-eq (x ∷ xs) []       _ _ h with h x
... | e rewrite ==-refl x = ⊥-elim (f e)
  where f : true ≡ false → ⊥
        f ()
inc-eq (x ∷ xs) (y ∷ ys) (ax , ix) (ay , iy) h with x ==ℕ y in exy
... | true with ==-sound x y exy
...   | refl = cong (x ∷_) (inc-eq xs ys ix iy tails)
  where
  tails : ∀ z → memL z xs ≡ memL z ys
  tails z with z ==ℕ x in ezx
  ... | true with ==-sound z x ezx
  ...   | refl = trans (above-not′ z xs ax) (sym (above-not′ z ys ay))
  tails z | false = trans (sym (memL-head z x xs ezx)) (trans (h z) (memL-head z x ys ezx))
inc-eq (x ∷ xs) (y ∷ ys) (ax , ix) (ay , iy) h | false =
  ⊥-elim (<-irrefl x (<-trans x y x x<y y<x))
  where
  x∈ys : memL x ys ≡ true
  x∈ys = trans (sym (memL-head x y ys exy)) (trans (sym (h x)) (cong (_∨ memL x xs) (==-refl x)))

  y≢x : (y ==ℕ x) ≡ false
  y≢x with y ==ℕ x in eyx
  ... | true  = ⊥-elim (bad (trans (sym exy) (subst (λ w → (x ==ℕ w) ≡ true) (sym (==-sound y x eyx)) (==-refl x))))
    where bad : false ≡ true → ⊥
          bad ()
  ... | false = refl

  y∈xs : memL y xs ≡ true
  y∈xs = trans (sym (memL-head y x xs y≢x)) (trans (h y) (cong (_∨ memL y ys) (==-refl y)))

  x<y : T (x <ℕ y)
  x<y = allN-mem y xs ax y∈xs

  y<x : T (y <ℕ x)
  y<x = allN-mem x ys ay x∈ys

------------------------------------------------------------------------
-- Diagrams of a context Θ whose sources come before their targets.

module _ (Θ : Ctx) where

  dimOf : Nat → Nat
  dimOf y with lookup Θ y
  ... | just A  = dim A
  ... | nothing = 0

  src : Nat → Nat
  src y with lookup Θ y
  ... | just (arr _ (var a) _) = a
  ... | _                      = 0

  iter : Nat → (Nat → Nat) → Nat → Nat
  iter zero    f y = y
  iter (suc n) f y = f (iter n f y)

  -- The iterated source of y in dimension e.
  srcAt : Nat → Nat → Nat
  srcAt e y = iter (dimOf y ∸ e) src y

  Cell : Nat → Maybe (Nat × Nat) → Nat → Set
  Cell e nothing         o = (Σ Ty λ A → lookup Θ o ≡ just A) × (dimOf o ≡ e)
  Cell e (just (p , q))  o = (Σ Ty λ B → lookup Θ o ≡ just (arr B (var p) (var q))) × (dimOf o ≡ e)

  mutual
    Ex : Nat → Maybe (Nat × Nat) → LT → Set
    Ex e par (lt os cs) = AllN (Cell e par) os × ExCs e os cs

    ExCs : Nat → List Nat → List LT → Set
    ExCs e (o ∷ [])      []       = ⊤
    ExCs e (o ∷ o' ∷ os) (c ∷ cs) = Ex (suc e) (just (o , o')) c × ExCs e (o' ∷ os) cs
    ExCs e _             _        = ⊥

  module _ (Ord : ∀ y B a b → lookup Θ y ≡ just (arr B (var a) (var b)) → T (a <ℕ b)) where

    private
      cell-dim : ∀ e par o → Cell e par o → dimOf o ≡ e
      cell-dim e nothing        o (_ , d) = d
      cell-dim e (just (p , q)) o (_ , d) = d

      cell-src : ∀ e p q o → Cell e (just (p , q)) o → src o ≡ p
      cell-src e p q o ((B , eo) , _) with lookup Θ o
      cell-src e p q o ((B , refl) , _) | .(just (arr B (var p) (var q))) = refl

      cell-ord : ∀ e p q o → Cell e (just (p , q)) o → T (p <ℕ q)
      cell-ord e p q o ((B , eo) , _) = Ord o B p q eo

      objs-dim : ∀ e par os → AllN (Cell e par) os → ∀ y → memL y os ≡ true → dimOf y ≡ e
      objs-dim e par os cs y m = cell-dim e par y (allN-mem y os cs m)

    -- Labels below depth e have dimension above e.
    mutual
      ex-dim : ∀ e par a y → Ex e par a → mem y a ≡ true → T (e <ℕ suc (dimOf y))
      ex-dim e par (lt os cs) y (ok , x) m with ∨-split (memL y os) (memCs y cs) m
      ... | inl mo rewrite objs-dim e par os ok y mo = <-suc e
      ... | inr mc = <-weak e (dimOf y) (cs-dim e os cs y x mc)

      cs-dim : ∀ e os cs y → ExCs e os cs → memCs y cs ≡ true → T (e <ℕ dimOf y)
      cs-dim e []            cs       y () m
      cs-dim e (o ∷ [])      []       y x ()
      cs-dim e (o ∷ [])      (c ∷ cs) y () m
      cs-dim e (o ∷ o' ∷ os) []       y () m
      cs-dim e (o ∷ o' ∷ os) (c ∷ cs) y (xc , xs) m with ∨-split (mem y c) (memCs y cs) m
      ... | inl mc = ex-dim (suc e) _ c y xc mc
      ... | inr ms = cs-dim e (o' ∷ os) cs y xs ms

    -- The labels of a branch from o lie over o.
    private
      srcAt-step : ∀ e y → T (e <ℕ dimOf y) → srcAt e y ≡ src (srcAt (suc e) y)
      srcAt-step e y p rewrite ∸-suc (dimOf y) e p = refl

    mutual
      br-src : ∀ e o o' c y → Ex (suc e) (just (o , o')) c → mem y c ≡ true → srcAt e y ≡ o
      br-src e o o' (lt os cs) y (ok , x) m with ∨-split (memL y os) (memCs y cs) m
      ... | inl mo =
        let cy = allN-mem y os ok mo in
        trans (cong (λ n → iter n src y) (trans (cong (_∸ e) (cell-dim (suc e) (just (o , o')) y cy)) (suc∸ e)))
              (cell-src (suc e) o o' y cy)
      ... | inr mc = brs-src e o o' os cs y ok x mc

      brs-src : ∀ e o o' os cs y → AllN (Cell (suc e) (just (o , o'))) os → ExCs (suc e) os cs →
                memCs y cs ≡ true → srcAt e y ≡ o
      brs-src e o o' []            cs       y ok () m
      brs-src e o o' (p ∷ [])      []       y ok x ()
      brs-src e o o' (p ∷ [])      (c ∷ cs) y ok () m
      brs-src e o o' (p ∷ q ∷ os)  []       y ok () m
      brs-src e o o' (p ∷ q ∷ os)  (c ∷ cs) y (cp , ok) (xc , xs) m
        with ∨-split (mem y c) (memCs y cs) m
      ... | inl mc =
        trans (srcAt-step e y (<-trans e (suc e) (dimOf y) (<-suc e) (ex-dim′ mc)))
              (trans (cong src (br-src (suc e) p q c y xc mc)) (cell-src (suc e) o o' p cp))
        where
        ex-dim′ : mem y c ≡ true → T (suc e <ℕ dimOf y)
        ex-dim′ mc = cs-dim (suc e) (p ∷ q ∷ os) (c ∷ cs) y (xc , xs) (cong (_∨ memCs y cs) mc)
      ... | inr ms = brs-src e o o' (q ∷ os) cs y ok xs ms

    -- Branches further along lie over later objects.
    private
      branch-ord : ∀ e o o' c → Ex (suc e) (just (o , o')) c → T (o <ℕ o')
      branch-ord e o o' (lt []       cs) (_ , x) = ⊥-elim (no-obj cs x)
        where
        no-obj : ∀ cs → ExCs (suc e) [] cs → ⊥
        no-obj []      ()
        no-obj (_ ∷ _) ()
      branch-ord e o o' (lt (h ∷ hs) cs) ((ch , _) , _) = cell-ord (suc e) o o' h ch

      later : ∀ e o o' os cs y → T (o <ℕ o') → ExCs e (o' ∷ os) cs → memCs y cs ≡ true →
              T (o <ℕ srcAt e y)
      later e o o' []            []       y p x ()
      later e o o' []            (c ∷ cs) y p () m
      later e o o' (o'' ∷ os)    []       y p () m
      later e o o' (o'' ∷ os)    (c ∷ cs) y p (xc , xs) m with ∨-split (mem y c) (memCs y cs) m
      ... | inl mc rewrite br-src e o' o'' c y xc mc = p
      ... | inr ms = later e o o'' os cs y (<-trans o o' o'' p (first-ord xc)) xs ms
        where
        first-ord : Ex (suc e) (just (o' , o'')) c → T (o' <ℕ o'')
        first-ord x = branch-ord e o' o'' c x

    -- The objects of a node increase.
    private
      above-trans : ∀ o o' xs → T (o <ℕ o') → Above o' xs → Above o xs
      above-trans o o' []       p _        = tt
      above-trans o o' (z ∷ zs) p (q , qs) = <-trans o o' z p q , above-trans o o' zs p qs

      chain-inc : ∀ e os cs → ExCs e os cs → Inc os
      chain-inc e []            cs       ()
      chain-inc e (o ∷ [])      []       x = tt , tt
      chain-inc e (o ∷ [])      (c ∷ cs) ()
      chain-inc e (o ∷ o' ∷ os) []       ()
      chain-inc e (o ∷ o' ∷ os) (c ∷ cs) (xc , xs) with chain-inc e (o' ∷ os) cs xs
      ... | ab , inc = (p , above-trans o o' os p ab) , (ab , inc)
        where p = branch-ord e o o' c xc

    ----------------------------------------------------------------------
    -- Uniqueness.

    private
      ∨-true : ∀ a → (a ∨ true) ≡ true
      ∨-true true  = refl
      ∨-true false = refl

      objs-char : ∀ e par os cs y → AllN (Cell e par) os → ExCs e os cs →
                  memL y os ≡ (mem y (lt os cs) ∧ (dimOf y ==ℕ e))
      objs-char e par os cs y ok x with memL y os in em
      ... | true rewrite objs-dim e par os ok y em = sym (==-refl e)
      ... | false with memCs y cs in ec
      ...   | false = refl
      ...   | true rewrite <-≢ e (dimOf y) (cs-dim e os cs y x ec) = refl

      cs-char : ∀ e par os cs y → AllN (Cell e par) os → ExCs e os cs →
                memCs y cs ≡ (mem y (lt os cs) ∧ not (dimOf y ==ℕ e))
      cs-char e par os cs y ok x with memCs y cs in ec
      ... | true rewrite ∨-true (memL y os) | <-≢ e (dimOf y) (cs-dim e os cs y x ec) = refl
      ... | false with memL y os in em
      ...   | false = refl
      ...   | true rewrite objs-dim e par os ok y em | ==-refl e = refl

      head-char : ∀ e o o' os c cs y → ExCs e (o ∷ o' ∷ os) (c ∷ cs) →
                  mem y c ≡ (memCs y (c ∷ cs) ∧ (srcAt e y ==ℕ o))
      head-char e o o' os c cs y (xc , xs) with mem y c in em
      ... | true rewrite br-src e o o' c y xc em = sym (==-refl o)
      ... | false with memCs y cs in es
      ...   | false = refl
      ...   | true rewrite <-≢ o (srcAt e y) (later e o o' os cs y (branch-ord e o o' c xc) xs es) = refl

      tail-char : ∀ e o o' os c cs y → ExCs e (o ∷ o' ∷ os) (c ∷ cs) →
                  memCs y cs ≡ (memCs y (c ∷ cs) ∧ not (srcAt e y ==ℕ o))
      tail-char e o o' os c cs y (xc , xs) with memCs y cs in es
      ... | true rewrite ∨-true (mem y c)
                       | <-≢ o (srcAt e y) (later e o o' os cs y (branch-ord e o o' c xc) xs es) = refl
      ... | false with mem y c in em
      ...   | false = refl
      ...   | true rewrite br-src e o o' c y xc em | ==-refl o = refl

    mutual
      uniq : ∀ e par a b → Ex e par a → Ex e par b → (∀ y → mem y a ≡ mem y b) → a ≡ b
      uniq e par (lt osa csa) (lt osb csb) (oka , xa) (okb , xb) h
        with inc-eq osa osb (chain-inc e osa csa xa) (chain-inc e osb csb xb)
               (λ y → trans (objs-char e par osa csa y oka xa)
                       (trans (cong (_∧ (dimOf y ==ℕ e)) (h y))
                              (sym (objs-char e par osb csb y okb xb))))
      ... | refl = cong (lt osa) (uniqCs e osa csa csb xa xb λ y →
                     trans (cs-char e par osa csa y oka xa)
                       (trans (cong (_∧ not (dimOf y ==ℕ e)) (h y))
                              (sym (cs-char e par osa csb y okb xb))))

      uniqCs : ∀ e os cs ds → ExCs e os cs → ExCs e os ds →
               (∀ y → memCs y cs ≡ memCs y ds) → cs ≡ ds
      uniqCs e []            cs       ds       () xd h
      uniqCs e (o ∷ [])      []       []       xc xd h = refl
      uniqCs e (o ∷ [])      []       (d ∷ ds) xc () h
      uniqCs e (o ∷ [])      (c ∷ cs) ds       () xd h
      uniqCs e (o ∷ o' ∷ os) []       ds       () xd h
      uniqCs e (o ∷ o' ∷ os) (c ∷ cs) []       xc () h
      uniqCs e (o ∷ o' ∷ os) (c ∷ cs) (d ∷ ds) xc xd h =
        cong₂ _∷_
          (uniq (suc e) (just (o , o')) c d (fst xc) (fst xd) λ y →
            trans (head-char e o o' os c cs y xc)
              (trans (cong (_∧ (srcAt e y ==ℕ o)) (h y)) (sym (head-char e o o' os d ds y xd))))
          (uniqCs e (o' ∷ os) cs ds (snd xc) (snd xd) λ y →
            trans (tail-char e o o' os c cs y xc)
              (trans (cong (_∧ not (srcAt e y ==ℕ o)) (h y)) (sym (tail-char e o o' os d ds y xd))))

------------------------------------------------------------------------
-- Example: x →f y →g z. The context has Ord, and its labelled tree is a
-- diagram, so the hypotheses of uniq are inhabited.

private
  Δ : Ctx
  Δ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)

  ordΔ : ∀ y B a b → lookup Δ y ≡ just (arr B (var a) (var b)) → T (a <ℕ b)
  ordΔ 2 ⋆ 0 1 refl = tt
  ordΔ 4 ⋆ 1 3 refl = tt
  ordΔ 0 B a b ()
  ordΔ 1 B a b ()
  ordΔ 3 B a b ()
  ordΔ (suc (suc (suc (suc (suc y))))) B a b ()

  gfTree : LT
  gfTree = lt (0 ∷ 1 ∷ 3 ∷ []) (lt (2 ∷ []) [] ∷ lt (4 ∷ []) [] ∷ [])

  exΔ : Ex Δ 0 nothing gfTree
  exΔ = (((⋆ , refl) , refl) , ((⋆ , refl) , refl) , ((⋆ , refl) , refl) , tt)
      , (((((⋆ , refl) , refl) , tt) , tt)
      , ((((⋆ , refl) , refl) , tt) , tt) , tt)
