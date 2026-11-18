------------------------------------------------------------------------
-- Standardisation of expressions (ledger A5, step L4; Steiner
-- Prop. 4.2, outside response §3.1).
--
-- Every composition-only expression e is rewritten into `std e`,
-- either a single generator or an r-composite f₁ #ᵣ ⋯ #ᵣ fₘ (m ≥ 2)
-- in which every fᵢ has exactly one generator of degree > r and, over
-- all factors, at most one generator has degree > r+1 (`WF`). The
-- rewrite only uses the ω-category axioms and the boundary words of
-- `BdElim`, so it preserves values in every strict ω-category where
-- the words are correct (`Sem.std-sem`).
------------------------------------------------------------------------
module CaTTExp.Strict.Std where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Expr
open import CaTTExp.Strict.BdElim
open import CaTTExp.Strict.StdSem

------------------------------------------------------------------------
-- Arithmetic.

private
  ≤-+ : ∀ {a a′ b b′} → a ≤ a′ → b ≤ b′ → a + b ≤ a′ + b′
  ≤-+ {a′ = a′} z≤n q = go a′ q
    where
    go : ∀ c {b b′} → b ≤ b′ → b ≤ c + b′
    go zero    q = q
    go (suc c) q = ≤-suc (go c q)
  ≤-+ (s≤s p) q = s≤s (≤-+ p q)

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  ≤0 : ∀ {a} → a ≤ 0 → a ≡ 0
  ≤0 z≤n = refl

  -- 2 ≤ a + b from 1 ≤ a and 1 ≤ b.
  two : ∀ {a b} → 1 ≤ a → 1 ≤ b → 2 ≤ a + b
  two {suc a} {suc b} _ _ = s≤s (subst (1 ≤_) (sym (+suc a b)) (s≤s z≤n))
    where
    +suc : ∀ a b → a + suc b ≡ suc (a + b)
    +suc zero    b = refl
    +suc (suc a) b = cong suc (+suc a b)

_⊔ℕ_ : Nat → Nat → Nat
zero  ⊔ℕ n     = n
suc m ⊔ℕ zero  = suc m
suc m ⊔ℕ suc n = suc (m ⊔ℕ n)

⊔-l : ∀ m n → m ≤ m ⊔ℕ n
⊔-l zero    n       = z≤n
⊔-l (suc m) zero    = ≤-refl _
⊔-l (suc m) (suc n) = s≤s (⊔-l m n)

⊔-r : ∀ m n → n ≤ m ⊔ℕ n
⊔-r zero    n       = ≤-refl n
⊔-r (suc m) zero    = z≤n
⊔-r (suc m) (suc n) = s≤s (⊔-r m n)

data Cls (n : Nat) : Set where
  c0 : n ≡ 0 → Cls n
  c1 : n ≡ 1 → Cls n
  c2 : 2 ≤ n → Cls n

cls : ∀ n → Cls n
cls zero          = c0 refl
cls (suc zero)    = c1 refl
cls (suc (suc n)) = c2 (s≤s (s≤s z≤n))

module Std {G : Set} (deg : G → Nat) (W : Sd → G → Expr G) where
  open Syn deg W

  ----------------------------------------------------------------------
  -- Counting generators of degree > s.

  hiG : ∀ {s d} → Tri s d → Nat
  hiG (tri< _) = 1
  hiG (tri≡ _) = 0
  hiG (tri> _) = 0

  hi : Nat → Expr G → Nat
  hi s (gen g)     = hiG (tri s (deg g))
  hi s (cmp k a b) = hi s a + hi s b
  hi s _           = 0

  hiG≤1 : ∀ {s d} (t : Tri s d) → hiG t ≤ 1
  hiG≤1 (tri< _) = s≤s z≤n
  hiG≤1 (tri≡ _) = z≤n
  hiG≤1 (tri> _) = z≤n

  hiG-mono : ∀ {s s′ d} → s ≤ s′ → (t : Tri s d) (t′ : Tri s′ d) → hiG t′ ≤ hiG t
  hiG-mono l (tri< _) t′        = hiG≤1 t′
  hiG-mono l (tri≡ refl) (tri< p) = ⊥-elim (≤-<-⊥ l p)
  hiG-mono l (tri≡ _) (tri≡ _)  = z≤n
  hiG-mono l (tri≡ _) (tri> _)  = z≤n
  hiG-mono l (tri> p) (tri< q)  = ⊥-elim (≤-<-⊥ (≤-trans l (<→≤ q)) p)
  hiG-mono l (tri> _) (tri≡ _)  = z≤n
  hiG-mono l (tri> _) (tri> _)  = z≤n

  hi-mono : ∀ {s s′} → s ≤ s′ → ∀ e → hi s′ e ≤ hi s e
  hi-mono l (gen g)      = hiG-mono l (tri _ (deg g)) (tri _ (deg g))
  hi-mono l (cmp k a b)  = ≤-+ (hi-mono l a) (hi-mono l b)
  hi-mono l (bsrc _ _)   = z≤n
  hi-mono l (btgt _ _)   = z≤n

  -- hi s e = 0 exactly when every generator has degree ≤ s.
  DegLe→hi : ∀ {s e} → DegLe s e → hi s e ≡ 0
  DegLe→hi {s} (dl-gen {g} l) with tri s (deg g)
  ... | tri< p = ⊥-elim (≤-<-⊥ l p)
  ... | tri≡ _ = refl
  ... | tri> _ = refl
  DegLe→hi (dl-cmp a b) = cong₂ _+_ (DegLe→hi a) (DegLe→hi b)

  hi→DegLe : ∀ {s e} → CO e → hi s e ≡ 0 → DegLe s e
  hi→DegLe {s} (co-gen g) h with tri s (deg g)
  hi→DegLe {s} (co-gen g) () | tri< p
  ... | tri≡ p = dl-gen (subst (_≤ s) p (≤-refl s))
  ... | tri> p = dl-gen (<→≤ p)
  hi→DegLe {s} (co-cmp k {a} {b} ca cb) h = dl-cmp (hi→DegLe ca (l h)) (hi→DegLe cb (r h))
    where
    l : ∀ {x y} → x + y ≡ 0 → x ≡ 0
    l {zero} _ = refl
    r : ∀ {x y} → x + y ≡ 0 → y ≡ 0
    r {zero} p = p

  -- A degree bound.
  mx : Expr G → Nat
  mx (gen g)     = deg g
  mx (cmp k a b) = mx a ⊔ℕ mx b
  mx _           = 0

  DegLe-mx : ∀ {e} → CO e → DegLe (mx e) e
  DegLe-mx (co-gen g) = dl-gen (≤-refl _)
  DegLe-mx (co-cmp k {a} {b} ca cb) =
    dl-cmp (DegLe-mono (⊔-l (mx a) (mx b)) (DegLe-mx ca)) (DegLe-mono (⊔-r (mx a) (mx b)) (DegLe-mx cb))

  ----------------------------------------------------------------------
  -- Lists of factors.

  sumHi : Nat → List (Expr G) → Nat
  sumHi s []       = 0
  sumHi s (f ∷ fs) = hi s f + sumHi s fs

  len : List (Expr G) → Nat
  len []       = 0
  len (_ ∷ fs) = suc (len fs)

  data AllF (r : Nat) : List (Expr G) → Set where
    []ᶠ  : AllF r []
    _∷ᶠ_ : ∀ {f fs} → CO f × (hi r f ≡ 1) → AllF r fs → AllF r (f ∷ fs)

  hi-cmpR : ∀ s r f fs → hi s (cmpR r f fs) ≡ sumHi s (f ∷ fs)
  hi-cmpR s r f []       = sym (+0 (hi s f))
  hi-cmpR s r f (g ∷ gs) = cong (hi s f +_) (hi-cmpR s r g gs)

  co-cmpR : ∀ r f fs → AllF r (f ∷ fs) → CO (cmpR r f fs)
  co-cmpR r f []       ((c , _) ∷ᶠ _) = c
  co-cmpR r f (g ∷ gs) ((c , _) ∷ᶠ a) = co-cmp r c (co-cmpR r g gs a)

  sum-one : ∀ r fs → AllF r fs → sumHi r fs ≡ len fs
  sum-one r []       []ᶠ             = refl
  sum-one r (f ∷ fs) ((_ , h) ∷ᶠ a) = cong₂ _+_ h (sum-one r fs a)

  _++ᶠ_ : ∀ {r fs gs} → AllF r fs → AllF r gs → AllF r (fs ++ gs)
  []ᶠ      ++ᶠ b = b
  (x ∷ᶠ a) ++ᶠ b = x ∷ᶠ (a ++ᶠ b)

  sum-++ : ∀ s fs gs → sumHi s (fs ++ gs) ≡ sumHi s fs + sumHi s gs
  sum-++ s []       gs = refl
  sum-++ s (f ∷ fs) gs = trans (cong (hi s f +_) (sum-++ s fs gs)) (sym (+-assoc′ (hi s f) (sumHi s fs) (sumHi s gs)))
    where
    +-assoc′ : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-assoc′ zero    b c = refl
    +-assoc′ (suc a) b c = cong suc (+-assoc′ a b c)

  len-++ : ∀ fs gs → len (fs ++ gs) ≡ len fs + len gs
  len-++ []       gs = refl
  len-++ (f ∷ fs) gs = cong suc (len-++ fs gs)

  ----------------------------------------------------------------------
  -- Results.

  data R : Set where
    one  : G → R
    many : Nat → Expr G → List (Expr G) → R

  toE : R → Expr G
  toE (one g)       = gen g
  toE (many r f fs) = cmpR r f fs

  WF : R → Set
  WF (one g)       = ⊤
  WF (many r f fs) = AllF r (f ∷ fs) × (1 ≤ len fs) × (sumHi (suc r) (f ∷ fs) ≤ 1)

  co-toE : ∀ R → WF R → CO (toE R)
  co-toE (one g)       _           = co-gen g
  co-toE (many r f fs) (a , _ , _) = co-cmpR r f fs a

  -- The cut of a well-formed result is determined by its counts.
  cut-unique : ∀ e {r r′} → 2 ≤ hi r e → hi (suc r) e ≤ 1 → 2 ≤ hi r′ e → hi (suc r′) e ≤ 1 → r ≡ r′
  cut-unique e {r} {r′} a b a′ b′ with tri r r′
  ... | tri< l = ⊥-elim (≤-<-⊥ (≤-trans a′ (≤-trans (hi-mono l e) b)) (s≤s (s≤s z≤n)))
  ... | tri≡ q = q
  ... | tri> l = ⊥-elim (≤-<-⊥ (≤-trans a (≤-trans (hi-mono l e) b′)) (s≤s (s≤s z≤n)))

  many-counts : ∀ r f fs → WF (many r f fs) → (2 ≤ hi r (cmpR r f fs)) × (hi (suc r) (cmpR r f fs) ≤ 1)
  many-counts r f fs (a , l , t) =
    subst (2 ≤_) (sym (trans (hi-cmpR r r f fs) (sum-one r (f ∷ fs) a))) (s≤s l) ,
    subst (_≤ 1) (sym (hi-cmpR (suc r) r f fs)) t

  ----------------------------------------------------------------------
  -- The cut of a composite: the largest r with at least two generators
  -- of degree > r.

  mutual
    findCut : Expr G → Nat → Nat
    findCut E zero    = 0
    findCut E (suc s) = fc E s (cls (hi s E))

    fc : (E : Expr G) (s : Nat) → Cls (hi s E) → Nat
    fc E s (c2 _) = s
    fc E s (c0 _) = findCut E s
    fc E s (c1 _) = findCut E s

  findCut-ok : ∀ E s k → hi s E ≤ 1 → 2 ≤ hi k E →
               let r = findCut E s in (2 ≤ hi r E) × (hi (suc r) E ≤ 1) × (k ≤ r)
  findCut-ok E zero k h a = ⊥-elim (≤-<-⊥ (≤-trans a (≤-trans (hi-mono z≤n E) h)) (s≤s (s≤s z≤n)))
  findCut-ok E (suc s) k h a with cls (hi s E)
  ... | c2 b = b , h , k≤s
    where
    k≤s : k ≤ s
    k≤s with tri k s
    ... | tri< l = <→≤ l
    ... | tri≡ refl = ≤-refl k
    ... | tri> l = ⊥-elim (≤-<-⊥ (≤-trans a (≤-trans (hi-mono l E) h)) (s≤s (s≤s z≤n)))
  ... | c0 b = findCut-ok E s k (subst (_≤ 1) (sym b) z≤n) a
  ... | c1 b = findCut-ok E s k (subst (_≤ 1) (sym b) (≤-refl 1)) a

  ----------------------------------------------------------------------
  -- Groups: the factors a child contributes at cut r.

  grp′ : (r : Nat) (R : R) → Cls (hi r (toE R)) → List (Expr G)
  grp′ r R              (c0 _) = []
  grp′ r R              (c1 _) = toE R ∷ []
  grp′ r (one g)        (c2 _) = gen g ∷ []
  grp′ r (many r′ f fs) (c2 _) = f ∷ fs

  grp : Nat → R → List (Expr G)
  grp r R = grp′ r R (cls (hi r (toE R)))

  ----------------------------------------------------------------------
  -- Standardisation.

  module _ (k r : Nat) (A B : Expr G) where
    D⁻ D⁺ : Expr G
    D⁻ = bd σ⁻ (mx B) r B
    D⁺ = bd σ⁺ (mx A) r A

    lst : List (Expr G) → List (Expr G) → Tri k r → List (Expr G)
    lst Ga Gb (tri≡ _) = Ga ++ Gb
    lst Ga Gb (tri< _) = mapE (λ y → cmp k y D⁻) Ga ++ mapE (λ z → cmp k D⁺ z) Gb
    lst Ga Gb (tri> _) = []

  mk : Nat → List (Expr G) → R → R
  mk r []       R = R
  mk r (f ∷ fs) _ = many r f fs

  cutOf : Nat → R → R → Nat
  cutOf k Ra Rb = findCut (cmp k (toE Ra) (toE Rb)) (mx (cmp k (toE Ra) (toE Rb)))

  cc : Nat → R → R → R
  cc k Ra Rb = mk r (lst k r (toE Ra) (toE Rb) (grp r Ra) (grp r Rb) (tri k r)) Ra
    where r = cutOf k Ra Rb

  cb : (k : Nat) (Ra Rb : R) → Cls (hi k (toE Rb)) → R
  cb k Ra Rb (c0 _) = Ra
  cb k Ra Rb (c1 _) = cc k Ra Rb
  cb k Ra Rb (c2 _) = cc k Ra Rb

  ca : (k : Nat) (Ra Rb : R) → Cls (hi k (toE Ra)) → R
  ca k Ra Rb (c0 _) = Rb
  ca k Ra Rb (c1 _) = cb k Ra Rb (cls (hi k (toE Rb)))
  ca k Ra Rb (c2 _) = cb k Ra Rb (cls (hi k (toE Rb)))

  combine : Nat → R → R → R
  combine k Ra Rb = ca k Ra Rb (cls (hi k (toE Ra)))

  std : Expr G → R
  std (gen g)     = one g
  std (cmp k a b) = combine k (std a) (std b)
  std (bsrc n e)  = std e
  std (btgt n e)  = std e

  ----------------------------------------------------------------------
  -- Well-formedness.

  private
    ≤-+l : ∀ a b → a ≤ a + b
    ≤-+l zero    b = z≤n
    ≤-+l (suc a) b = s≤s (≤-+l a b)

    ≤-+r : ∀ a b → b ≤ a + b
    ≤-+r zero    b = ≤-refl b
    ≤-+r (suc a) b = ≤-suc (≤-+r a b)

    ≤1→0 : ∀ {a} → a ≤ 0 → a ≡ 0
    ≤1→0 z≤n = refl

  -- The facts about a group needed by the parent.
  record GrpOK (r : Nat) (E : Expr G) (Gs : List (Expr G)) : Set where
    field
      g-all : AllF r Gs
      g-len : len Gs ≡ hi r E
      g-top : sumHi (suc r) Gs ≡ hi (suc r) E

  grp-ok : ∀ r R → WF R → hi (suc r) (toE R) ≤ 1 → GrpOK r (toE R) (grp r R)
  grp-ok r R w t = go R w t (cls (hi r (toE R)))
    where
    go : ∀ R → WF R → hi (suc r) (toE R) ≤ 1 → (c : Cls (hi r (toE R))) → GrpOK r (toE R) (grp′ r R c)
    go R w t (c0 h) = record
      { g-all = []ᶠ ; g-len = sym h
      ; g-top = sym (≤1→0 (subst (hi (suc r) (toE R) ≤_) h (hi-mono (≤-suc (≤-refl r)) (toE R)))) }
    go R w t (c1 h) = record
      { g-all = (co-toE R w , h) ∷ᶠ []ᶠ ; g-len = sym h ; g-top = +0 _ }
    go (one g) w t (c2 h) = ⊥-elim (≤-<-⊥ (hiG≤1 (tri r (deg g))) h)
    go (many r′ f fs) w t (c2 h) = same (cut-unique (cmpR r′ f fs) (fst mc) (snd mc) h t)
      where
      mc = many-counts r′ f fs w
      same : r′ ≡ r → GrpOK r (cmpR r′ f fs) (f ∷ fs)
      same refl = record
        { g-all = fst w
        ; g-len = sym (trans (hi-cmpR r r f fs) (sum-one r (f ∷ fs) (fst w)))
        ; g-top = sym (hi-cmpR (suc r) r f fs) }

  private
    map-r-all : ∀ k r D Gs → CO D → hi r D ≡ 0 → AllF r Gs → AllF r (mapE (λ y → cmp k y D) Gs)
    map-r-all k r D []       c h []ᶠ              = []ᶠ
    map-r-all k r D (f ∷ fs) c h ((cf , hf) ∷ᶠ a) =
      (co-cmp k cf c , trans (cong₂ _+_ hf h) refl) ∷ᶠ map-r-all k r D fs c h a

    map-l-all : ∀ k r D Gs → CO D → hi r D ≡ 0 → AllF r Gs → AllF r (mapE (λ z → cmp k D z) Gs)
    map-l-all k r D []       c h []ᶠ              = []ᶠ
    map-l-all k r D (f ∷ fs) c h ((cf , hf) ∷ᶠ a) =
      (co-cmp k c cf , cong₂ _+_ h hf) ∷ᶠ map-l-all k r D fs c h a

    map-r-len : ∀ k D Gs → len (mapE (λ y → cmp k y D) Gs) ≡ len Gs
    map-r-len k D []       = refl
    map-r-len k D (f ∷ fs) = cong suc (map-r-len k D fs)

    map-l-len : ∀ k D Gs → len (mapE (λ z → cmp k D z) Gs) ≡ len Gs
    map-l-len k D []       = refl
    map-l-len k D (f ∷ fs) = cong suc (map-l-len k D fs)

    map-r-sum : ∀ k s D Gs → hi s D ≡ 0 → sumHi s (mapE (λ y → cmp k y D) Gs) ≡ sumHi s Gs
    map-r-sum k s D []       h = refl
    map-r-sum k s D (f ∷ fs) h = cong₂ _+_ (trans (cong (hi s f +_) h) (+0 (hi s f))) (map-r-sum k s D fs h)

    map-l-sum : ∀ k s D Gs → hi s D ≡ 0 → sumHi s (mapE (λ z → cmp k D z) Gs) ≡ sumHi s Gs
    map-l-sum k s D []       h = refl
    map-l-sum k s D (f ∷ fs) h = cong₂ _+_ (cong (_+ hi s f) h) (map-l-sum k s D fs h)

  mk-wf : ∀ r L R → AllF r L → 2 ≤ len L → sumHi (suc r) L ≤ 1 → WF (mk r L R)
  mk-wf r (f ∷ g ∷ gs) R a (s≤s (s≤s _)) t = a , s≤s z≤n , t

  module WFProof (W-co : ∀ s g → CO (W s g)) (W-deg : ∀ s g → DegLe (deg g ∸ 1) (W s g)) where
    open Props W-co W-deg

    -- Facts about the cut of a composite whose children both reach above k.
    record CutOK (k : Nat) (A B : Expr G) (r : Nat) : Set where
      field
        c-two : 2 ≤ hi r (cmp k A B)
        c-top : hi (suc r) (cmp k A B) ≤ 1
        c-ge  : k ≤ r

    cut-ok : ∀ k A B → CO A → CO B → 1 ≤ hi k A → 1 ≤ hi k B →
             CutOK k A B (findCut (cmp k A B) (mx (cmp k A B)))
    cut-ok k A B cA cB hA hB =
      let E  = cmp k A B
          h0 = subst (_≤ 1) (sym (DegLe→hi (DegLe-mx (co-cmp k cA cB)))) z≤n
          (a , b , c) = findCut-ok E (mx E) k h0 (two hA hB)
      in record { c-two = a ; c-top = b ; c-ge = c }

    lst-wf : ∀ k r A B Ra Rb → toE Ra ≡ A → toE Rb ≡ B → CO A → CO B → CutOK k A B r →
             GrpOK r A (grp r Ra) → GrpOK r B (grp r Rb) → (t : Tri k r) →
             AllF r (lst k r A B (grp r Ra) (grp r Rb) t) ×
             (2 ≤ len (lst k r A B (grp r Ra) (grp r Rb) t)) ×
             (sumHi (suc r) (lst k r A B (grp r Ra) (grp r Rb) t) ≤ 1)
    lst-wf k r A B Ra Rb _ _ cA cB co gA gB (tri≡ refl) =
      (GrpOK.g-all gA ++ᶠ GrpOK.g-all gB) ,
      subst (2 ≤_) (sym (trans (len-++ Ga Gb) (cong₂ _+_ (GrpOK.g-len gA) (GrpOK.g-len gB)))) (CutOK.c-two co) ,
      subst (_≤ 1) (sym (trans (sum-++ (suc r) Ga Gb) (cong₂ _+_ (GrpOK.g-top gA) (GrpOK.g-top gB)))) (CutOK.c-top co)
      where
      Ga = grp r Ra
      Gb = grp r Rb
    lst-wf k r A B Ra Rb _ _ cA cB co gA gB (tri< l) =
      (map-r-all k r Dm Ga cDm (DegLe→hi dDm) (GrpOK.g-all gA) ++ᶠ
       map-l-all k r Dp Gb cDp (DegLe→hi dDp) (GrpOK.g-all gB)) ,
      subst (2 ≤_) (sym (trans (len-++ (mapE (λ y → cmp k y Dm) Ga) (mapE (λ z → cmp k Dp z) Gb))
                        (cong₂ _+_ (trans (map-r-len k Dm Ga) (GrpOK.g-len gA))
                                   (trans (map-l-len k Dp Gb) (GrpOK.g-len gB)))))
            (CutOK.c-two co) ,
      subst (_≤ 1) (sym (trans (sum-++ (suc r) (mapE (λ y → cmp k y Dm) Ga) (mapE (λ z → cmp k Dp z) Gb))
                        (cong₂ _+_ (trans (map-r-sum k (suc r) Dm Ga (DegLe→hi (DegLe-mono (≤-suc (≤-refl r)) dDm)))
                                          (GrpOK.g-top gA))
                                   (trans (map-l-sum k (suc r) Dp Gb (DegLe→hi (DegLe-mono (≤-suc (≤-refl r)) dDp)))
                                          (GrpOK.g-top gB)))))
            (CutOK.c-top co)
      where
      Ga = grp r Ra
      Gb = grp r Rb
      Dm = D⁻ k r A B
      Dp = D⁺ k r A B
      cDm = bd-co σ⁻ (mx B) r B cB
      cDp = bd-co σ⁺ (mx A) r A cA
      dDm = bd-deg σ⁻ (mx B) r B (DegLe-mx cB)
      dDp = bd-deg σ⁺ (mx A) r A (DegLe-mx cA)
    lst-wf k r A B Ra Rb _ _ cA cB co gA gB (tri> l) = ⊥-elim (≤-<-⊥ (CutOK.c-ge co) l)

    cc-wf : ∀ k Ra Rb → WF Ra → WF Rb → 1 ≤ hi k (toE Ra) → 1 ≤ hi k (toE Rb) → WF (cc k Ra Rb)
    cc-wf k Ra Rb wa wb hA hB =
      let (a , b , c) = lst-wf k r A B Ra Rb refl refl cA cB co gA gB (tri k r)
      in mk-wf r _ Ra a b c
      where
      A = toE Ra
      B = toE Rb
      cA = co-toE Ra wa
      cB = co-toE Rb wb
      r = cutOf k Ra Rb
      co = cut-ok k A B cA cB hA hB
      gA = grp-ok r Ra wa (≤-trans (≤-+l (hi (suc r) A) (hi (suc r) B)) (CutOK.c-top co))
      gB = grp-ok r Rb wb (≤-trans (≤-+r (hi (suc r) A) (hi (suc r) B)) (CutOK.c-top co))

    private
      pos1 : ∀ {n} → n ≡ 1 → 1 ≤ n
      pos1 refl = s≤s z≤n
      pos2 : ∀ {n} → 2 ≤ n → 1 ≤ n
      pos2 (s≤s _) = s≤s z≤n

    comb-wf : ∀ k Ra Rb → WF Ra → WF Rb → WF (combine k Ra Rb)
    comb-wf k Ra Rb wa wb with cls (hi k (toE Ra))
    ... | c0 _  = wb
    ... | c1 ha = cbw (pos1 (ha))
      where
      cbw : 1 ≤ hi k (toE Ra) → WF (cb k Ra Rb (cls (hi k (toE Rb))))
      cbw hA with cls (hi k (toE Rb))
      ... | c0 _  = wa
      ... | c1 hb = cc-wf k Ra Rb wa wb hA (pos1 (hb))
      ... | c2 hb = cc-wf k Ra Rb wa wb hA (pos2 (hb))
    ... | c2 ha = cbw (pos2 (ha))
      where
      cbw : 1 ≤ hi k (toE Ra) → WF (cb k Ra Rb (cls (hi k (toE Rb))))
      cbw hA with cls (hi k (toE Rb))
      ... | c0 _  = wa
      ... | c1 hb = cc-wf k Ra Rb wa wb hA (pos1 (hb))
      ... | c2 hb = cc-wf k Ra Rb wa wb hA (pos2 (hb))

    std-wf : ∀ e → CO e → WF (std e)
    std-wf (gen g)     _              = tt
    std-wf (cmp k a b) (co-cmp _ x y) = comb-wf k (std a) (std b) (std-wf a x) (std-wf b y)

  ----------------------------------------------------------------------
  -- Generators of degree ≤ r give r-dimensional values.

  module DimProof (𝒞 : ωCat) (ι : G → ωCat.C 𝒞) (dimι : ∀ g → ωCat.src 𝒞 (deg g) (ι g) ≡ ι g) where
    open ωCat 𝒞
    open Eval 𝒞 ι
    open StdSem 𝒞 ι

    dimLe : ∀ {r e y} → DegLe r e → Ev e y → Dim r y
    dimLe {r} (dl-gen {g} l) (ev-gen .g) =
      trans (cong (src r) (sym (dimι g))) (trans (src-src-≥ (ι g) l) (dimι g))
    dimLe {r} (dl-cmp {k} da db) (ev-cmp .k {x = x} {y = y} u v p) with tri k r
    ... | tri< l = trans (src-comp-> x y p l q) (comp-cong k q p (dimLe da u) (dimLe db v))
      where
      q : tgt k (src r x) ≡ src k (src r y)
      q = trans (tgt-src-< x l) (trans p (sym (src-src-< y l)))
    ... | tri≡ refl = trans (src-comp k x y p) (trans (dimLe da u) (sym (absorb-r (dimLe db v) p)))
    ... | tri> l = trans (src-comp-< x y p l) (trans (dimLe da u) (sym (absorb-r dyk p)))
      where
      dyk : Dim k y
      dyk = trans (cong (src k) (sym (dimLe db v))) (trans (src-src-≥ y (<→≤ l)) (dimLe db v))


  ----------------------------------------------------------------------
  -- Soundness in a strict ω-category.

  module SemProof (𝒞 : ωCat) (ι : G → ωCat.C 𝒞)
                  (W-co : ∀ s g → CO (W s g)) (W-deg : ∀ s g → DegLe (deg g ∸ 1) (W s g))
                  (dimι : ∀ g → ωCat.src 𝒞 (deg g) (ι g) ≡ ι g)
                  (W-ev : ∀ s g → 1 ≤ deg g → Eval.Ev 𝒞 ι (W s g) (Sem.bdC 𝒞 ι s (deg g ∸ 1) (ι g))) where
    open ωCat 𝒞
    open Eval 𝒞 ι
    open StdSem 𝒞 ι
    open Sem 𝒞 ι using (bdC) renaming (sound to sound₀)

    sound : ∀ s f n e {x} → DegLe f e → Ev e x → Ev (bd s f n e) (bdC s n x)
    sound = sound₀ W-deg dimι W-ev
    open WFProof W-co W-deg
    open DimProof 𝒞 ι dimι

    private
      Ev-sub : ∀ {e x y} → x ≡ y → Ev e x → Ev e y
      Ev-sub refl v = v

    -- What a group gives: its r-composite has the child's value.
    GS : Nat → List (Expr G) → C → Set
    GS r []       y = ⊤
    GS r (f ∷ fs) y = Ev (cmpR r f fs) y

    grp-sem : ∀ r R {y} → WF R → hi (suc r) (toE R) ≤ 1 → Ev (toE R) y → GS r (grp r R) y
    grp-sem r R w t v = go R w t v (cls (hi r (toE R)))
      where
      go : ∀ R {y} → WF R → hi (suc r) (toE R) ≤ 1 → Ev (toE R) y → (c : Cls (hi r (toE R))) → GS r (grp′ r R c) y
      go R w t v (c0 _) = tt
      go R w t v (c1 _) = v
      go (one g) w t v (c2 h) = ⊥-elim (≤-<-⊥ (hiG≤1 (tri r (deg g))) h)
      go (many r′ f fs) w t v (c2 h) = same (cut-unique (cmpR r′ f fs) (fst mc) (snd mc) h t) v
        where
        mc = many-counts r′ f fs w
        same : ∀ {y} → r′ ≡ r → Ev (cmpR r′ f fs) y → Ev (cmpR r f fs) y
        same refl v = v

    private
      ++-[] : ∀ (xs : List (Expr G)) → xs ++ [] ≡ xs
      ++-[] []       = refl
      ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

    -- What the result of a cut gives.
    MS : Nat → List (Expr G) → C → Set
    MS r []       v = ⊥
    MS r (f ∷ fs) v = Ev (cmpR r f fs) v

    lst-sem : ∀ k r A B {y z} (p : tgt k y ≡ src k z) → CO A → CO B → Ev A y → Ev B z →
              ∀ Ga Gb → GS r Ga y → GS r Gb z → len Ga ≡ hi r A → len Gb ≡ hi r B →
              2 ≤ len Ga + len Gb → 1 ≤ hi k A → 1 ≤ hi k B → k ≤ r → (t : Tri k r) →
              MS r (lst k r A B Ga Gb t) (comp k y z p)
    lst-sem k r A B p cA cB vA vB []       Gb sa sb la lb two hA hB kr (tri≡ refl) =
      ⊥-elim (≤-<-⊥ (subst (1 ≤_) (sym la) hA) (s≤s z≤n))
    lst-sem k r A B p cA cB vA vB (g ∷ gs) []       sa sb la lb two hA hB kr (tri≡ refl) =
      ⊥-elim (≤-<-⊥ (subst (1 ≤_) (sym lb) hB) (s≤s z≤n))
    lst-sem k r A B p cA cB vA vB (g ∷ gs) (h ∷ hs) sa sb la lb two hA hB kr (tri≡ refl) =
      cat r g gs h hs sa sb p
    lst-sem k r A B p cA cB vA vB Ga Gb sa sb la lb two hA hB kr (tri> l) = ⊥-elim (≤-<-⊥ kr l)
    lst-sem k r A B p cA cB vA vB [] [] sa sb la lb () hA hB kr (tri< l)
    lst-sem k r A B {y} {z} p cA cB vA vB [] (h ∷ hs) sa sb la lb two hA hB kr (tri< l) =
      Ev-sub (comp-cong k p′ p (Dim-tgt dy) refl)
        (dist-l l h hs (D⁺ k r A B) sb vDp (src-tgt-≥ y (≤-refl r)) p′)
      where
      dy : Dim r y
      dy = dimLe (hi→DegLe cA (sym la)) vA
      vDp = sound σ⁺ (mx A) r A (DegLe-mx cA) vA
      p′ : tgt k (tgt r y) ≡ src k z
      p′ = trans (tgt-tgt-< y l) p
    lst-sem k r A B {y} {z} p cA cB vA vB (g ∷ gs) [] sa sb la lb two hA hB kr (tri< l) =
      subst (λ L → MS r L (comp k y z p)) (sym (++-[] (mapE (λ y → cmp k y (D⁻ k r A B)) (g ∷ gs))))
        (Ev-sub (comp-cong k p′ p refl dz)
          (dist-r l g gs (D⁻ k r A B) sa vDm (src-src-≥ z (≤-refl r)) p′))
      where
      dz : Dim r z
      dz = dimLe (hi→DegLe cB (sym lb)) vB
      vDm = sound σ⁻ (mx B) r B (DegLe-mx cB) vB
      p′ : tgt k y ≡ src k (src r z)
      p′ = trans p (sym (src-src-< z l))
    lst-sem k r A B {y} {z} p cA cB vA vB (g ∷ gs) (h ∷ hs) sa sb la lb two hA hB kr (tri< l) =
      let (p₁ , p₂ , q , eq) = split l y z p
      in Ev-sub (sym eq)
           (cat r (cmp k g Dm) (mapE (λ y → cmp k y Dm) gs) (cmp k Dp h) (mapE (λ z → cmp k Dp z) hs)
                (dist-r l g gs Dm sa vDm (src-src-≥ z (≤-refl r)) p₁)
                (dist-l l h hs Dp sb vDp (src-tgt-≥ y (≤-refl r)) p₂) q)
      where
      Dm = D⁻ k r A B
      Dp = D⁺ k r A B
      vDm = sound σ⁻ (mx B) r B (DegLe-mx cB) vB
      vDp = sound σ⁺ (mx A) r A (DegLe-mx cA) vA

    mk-ev : ∀ r L R {v} → MS r L v → Ev (toE (mk r L R)) v
    mk-ev r (f ∷ fs) R m = m

    cc-sem : ∀ k Ra Rb → WF Ra → WF Rb → 1 ≤ hi k (toE Ra) → 1 ≤ hi k (toE Rb) →
             ∀ {y z} → Ev (toE Ra) y → Ev (toE Rb) z → (p : tgt k y ≡ src k z) →
             Ev (toE (cc k Ra Rb)) (comp k y z p)
    cc-sem k Ra Rb wa wb hA hB vA vB p =
      mk-ev r L Ra (lst-sem k r A B p cA cB vA vB Ga Gb
                      (grp-sem r Ra wa tA vA) (grp-sem r Rb wb tB vB)
                      (GrpOK.g-len gA) (GrpOK.g-len gB) two′ hA hB (CutOK.c-ge co) (tri k r))
      where
      A = toE Ra
      B = toE Rb
      cA = co-toE Ra wa
      cB = co-toE Rb wb
      r = cutOf k Ra Rb
      Ga = grp r Ra
      Gb = grp r Rb
      L = lst k r A B Ga Gb (tri k r)
      co = cut-ok k A B cA cB hA hB
      tA = ≤-trans (≤-+l (hi (suc r) A) (hi (suc r) B)) (CutOK.c-top co)
      tB = ≤-trans (≤-+r (hi (suc r) A) (hi (suc r) B)) (CutOK.c-top co)
      gA = grp-ok r Ra wa tA
      gB = grp-ok r Rb wb tB
      two′ : 2 ≤ len Ga + len Gb
      two′ = subst (2 ≤_) (sym (cong₂ _+_ (GrpOK.g-len gA) (GrpOK.g-len gB))) (CutOK.c-two co)

    private
      pos1 : ∀ {n} → n ≡ 1 → 1 ≤ n
      pos1 refl = s≤s z≤n
      pos2 : ∀ {n} → 2 ≤ n → 1 ≤ n
      pos2 (s≤s _) = s≤s z≤n

    comb-sem : ∀ k Ra Rb → WF Ra → WF Rb → ∀ {y z} → Ev (toE Ra) y → Ev (toE Rb) z →
               (p : tgt k y ≡ src k z) → Ev (toE (combine k Ra Rb)) (comp k y z p)
    comb-sem k Ra Rb wa wb {y} {z} vA vB p with cls (hi k (toE Ra))
    ... | c0 ha = Ev-sub (sym (absorb-l (dimLe (hi→DegLe (co-toE Ra wa) ha) vA) p)) vB
    ... | c1 ha = cbs (pos1 ha)
      where
      cbs : 1 ≤ hi k (toE Ra) → Ev (toE (cb k Ra Rb (cls (hi k (toE Rb))))) (comp k y z p)
      cbs hA with cls (hi k (toE Rb))
      ... | c0 hb = Ev-sub (sym (absorb-r (dimLe (hi→DegLe (co-toE Rb wb) hb) vB) p)) vA
      ... | c1 hb = cc-sem k Ra Rb wa wb hA (pos1 hb) vA vB p
      ... | c2 hb = cc-sem k Ra Rb wa wb hA (pos2 hb) vA vB p
    ... | c2 ha = cbs (pos2 ha)
      where
      cbs : 1 ≤ hi k (toE Ra) → Ev (toE (cb k Ra Rb (cls (hi k (toE Rb))))) (comp k y z p)
      cbs hA with cls (hi k (toE Rb))
      ... | c0 hb = Ev-sub (sym (absorb-r (dimLe (hi→DegLe (co-toE Rb wb) hb) vB) p)) vA
      ... | c1 hb = cc-sem k Ra Rb wa wb hA (pos1 hb) vA vB p
      ... | c2 hb = cc-sem k Ra Rb wa wb hA (pos2 hb) vA vB p

    -- Standardisation preserves values.
    std-sem : ∀ e {x} → CO e → Ev e x → Ev (toE (std e)) x
    std-sem (gen g)     _              v                = v
    std-sem (cmp k a b) (co-cmp _ x y) (ev-cmp .k u v p) =
      comb-sem k (std a) (std b) (std-wf a x) (std-wf b y) (std-sem a x u) (std-sem b y v) p
