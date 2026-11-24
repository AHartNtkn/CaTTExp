------------------------------------------------------------------------
-- Soundness of the kernel's evaluator on composites (ledger S27 (h′)).
--
-- CaTTExp.Cones types an expression symbolically (`tyF`) and evaluates
-- it to CaTT syntax (`evF`, `evTyF`, `cellF`), all by fuel. This module
-- proves, for the fragment built from variables and binary composites
-- (`v`, `bn`) over any expression context K, that
--
--   * the symbolic type of a composite is the boundary typing of
--     CaTTExp.Lim.ConeCells (`bcell`): `TY`;
--   * evaluation computes the composite's cell: `CELL`, and the
--     evaluated type of an entry of K is its intended type: `evTy-ok`;
--   * the kernel's fuel (`fuelOf`, which grows with the dimensions and
--     weights of K) is enough: `fuel-ok`.
--
-- The intended meaning of the variables is given as a map `semV` to
-- cells. The hypotheses are that each entry of K represents the type of
-- its variable's cell (`Rep`, below) and that K is scoped (each entry
-- mentions only earlier variables); then every composite that is
-- composable (`Good`: each k-composite meets along a common k-cell)
-- evaluates to the typed composite of the cells.
------------------------------------------------------------------------
module CaTTExp.Lim.ConesEval where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
  using (Cell; dimC; srcC; tgtC; binC; Ex; ExTy; ExCtx; v; bn; ob; hom;
         dimE; srcE; tgtE; baseE; tyF; evF; evTyF; cellF; tyE; nth; length;
         wtE; wtTy; weightsGo; weights; maxL; map; fuel; fuelOf; evTy; evCtx; evCtxGo)
open import CaTTExp.Lim.ConeCells
  using (pred; dim-src; dim-tgt; src-type; tgt-type; src-tgt-type; loC; hiC;
         btyR; bcellR; bcell; lo-max; hi-max; bc-dim; lo-above; hi-above;
         bc-src-c; bc-tgt-c; bc-src-nc; bc-tgt-nc; srcN; tgtN)

------------------------------------------------------------------------
-- Arithmetic: a ≤ b as a test.

Le : Nat → Nat → Set
Le a b = T (a <ℕ suc b)

lt0 : ∀ {A : Set} a → T (a <ℕ 0) → A
lt0 _ ()

le0 : ∀ a → Le 0 a
le0 _ = tt

le-refl : ∀ a → Le a a
le-refl zero    = tt
le-refl (suc a) = le-refl a

le-trans : ∀ a b c → Le a b → Le b c → Le a c
le-trans zero    b       c       _ _ = tt
le-trans (suc a) zero    c       p _ = lt0 a p
le-trans (suc a) (suc b) zero    _ q = lt0 b q
le-trans (suc a) (suc b) (suc c) p q = le-trans a b c p q

le-suc : ∀ a → Le a (suc a)
le-suc zero    = tt
le-suc (suc a) = le-suc a

le-step : ∀ a b → Le a b → Le a (suc b)
le-step a b p = le-trans a b (suc b) p (le-suc b)

-- Strict < as ≤ of the successor.
lt-le : ∀ a b → T (a <ℕ b) → Le (suc a) b
lt-le zero    (suc b) _ = tt
lt-le (suc a) (suc b) p = lt-le a b p
lt-le a       zero    p = lt0 a p

le-lt : ∀ a b → Le (suc a) b → T (a <ℕ b)
le-lt zero    (suc b) _ = tt
le-lt (suc a) (suc b) p = le-lt a b p
le-lt zero    zero    ()
le-lt (suc a) zero    p = lt0 a p

le-max-l : ∀ a b → Le a (max a b)
le-max-l zero    b       = tt
le-max-l (suc a) zero    = le-refl a
le-max-l (suc a) (suc b) = le-max-l a b

le-max-r : ∀ a b → Le b (max a b)
le-max-r zero    b       = le-refl b
le-max-r (suc a) zero    = tt
le-max-r (suc a) (suc b) = le-max-r a b

max-lub : ∀ a b c → Le a c → Le b c → Le (max a b) c
max-lub zero    b       c       _ q = q
max-lub (suc a) zero    c       p _ = p
max-lub (suc a) (suc b) zero    p _ = lt0 a p
max-lub (suc a) (suc b) (suc c) p q = max-lub a b c p q

max-mono : ∀ a b a′ b′ → Le a a′ → Le b b′ → Le (max a b) (max a′ b′)
max-mono a b a′ b′ p q =
  max-lub a b (max a′ b′) (le-trans a a′ _ p (le-max-l a′ b′)) (le-trans b b′ _ q (le-max-r a′ b′))

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

le-+ : ∀ a b c d → Le a b → Le c d → Le (a + c) (b + d)
le-+ zero    zero    c d _ q = q
le-+ zero    (suc b) c d _ q = le-step c (b + d) (le-+ zero b c d tt q)
le-+ (suc a) zero    c d p _ = lt0 a p
le-+ (suc a) (suc b) c d p q = le-+ a b c d p q

le-+l : ∀ n a → Le a (n + a)
le-+l zero    a = le-refl a
le-+l (suc n) a = le-step a (n + a) (le-+l n a)

le-eq : ∀ {a b c} → Le a b → b ≡ c → Le a c
le-eq p refl = p

eq-le : ∀ {a b c} → a ≡ b → Le b c → Le a c
eq-le refl p = p

-- k < d ≤ suc k forces d = suc k.
squeeze : ∀ k d → T (k <ℕ d) → Le d (suc k) → d ≡ suc k
squeeze zero    (suc zero)    _ _ = refl
squeeze zero    (suc (suc d)) _ q = lt0 d q
squeeze (suc k) (suc d)       p q = cong suc (squeeze k d p q)
squeeze k       zero          p _ = lt0 k p

suc-pred : ∀ a → T (0 <ℕ a) → suc (pred a) ≡ a
suc-pred (suc a) _ = refl

-- suc k ∸ k = 1, and r′ ∸ k is positive when k < r′.
sk∸k : ∀ k → suc k ∸ k ≡ 1
sk∸k zero    = refl
sk∸k (suc k) = sk∸k k

∸-pos : ∀ k r′ → T (k <ℕ r′) → Σ Nat (λ m → (r′ ∸ k ≡ suc m) × (suc r′ ∸ k ≡ suc (suc m)))
∸-pos zero    (suc r′) _ = r′ , refl , refl
∸-pos (suc k) (suc r′) p = ∸-pos k r′ p
∸-pos k       zero     p = lt0 k p

-- The fuel bound for evaluation.
B : Nat → Nat → Nat
B d ω = suc (d + (ω + ω))

B-mono : ∀ d d′ ω ω′ → Le d d′ → Le ω ω′ → Le (B d ω) (B d′ ω′)
B-mono d d′ ω ω′ p q = le-+ d d′ (ω + ω) (ω′ + ω′) p (le-+ ω ω′ ω ω′ q q)

B-suc : ∀ d ω → B d (suc ω) ≡ suc (suc (B d ω))
B-suc d ω = cong suc (trans (+-suc d (ω + suc ω))
                     (cong suc (trans (cong (d +_) (+-suc ω ω)) (+-suc d (ω + ω)))))

------------------------------------------------------------------------
-- Cells: boundaries of boundaries.

-- In dimension ≥ 2 the (m+1)-fold source of the target is that of the
-- source, and dually (globularity).
glob-src : ∀ m c → T (1 <ℕ dimC c) → srcN (suc m) (tgtC c) ≡ srcN (suc m) (srcC c)
glob-src m (x , arr (arr B a b) s t) _ = refl
glob-src m (x , arr ⋆ s t) ()
glob-src m (x , ⋆) ()

glob-tgt : ∀ m c → T (1 <ℕ dimC c) → tgtN (suc m) (srcC c) ≡ tgtN (suc m) (tgtC c)
glob-tgt m (x , arr (arr B a b) s t) _ = refl
glob-tgt m (x , arr ⋆ s t) ()
glob-tgt m (x , ⋆) ()

-- A positive-dimensional cell's type, from its boundaries.
ty-split : ∀ c → T (0 <ℕ dimC c) → snd c ≡ arr (snd (srcC c)) (fst (srcC c)) (fst (tgtC c))
ty-split (x , arr A s t) _ = refl
ty-split (x , ⋆) ()

lo-yes : ∀ r c → (dimC c <ℕ r) ≡ true → loC r c ≡ c
lo-yes r c e rewrite e = refl

lo-no : ∀ r c → (dimC c <ℕ r) ≡ false → loC r c ≡ srcC c
lo-no r c e rewrite e = refl

hi-yes : ∀ r c → (dimC c <ℕ r) ≡ true → hiC r c ≡ c
hi-yes r c e rewrite e = refl

hi-no : ∀ r c → (dimC c <ℕ r) ≡ false → hiC r c ≡ tgtC c
hi-no r c e rewrite e = refl

-- k-composability: the k-target of a is the k-source of b.
Comp : Nat → Cell → Cell → Set
Comp k a b = tgtN (dimC a ∸ k) a ≡ srcN (dimC b ∸ k) b

private
  dim-src′ : ∀ c r′ → dimC c ≡ suc r′ → dimC (srcC c) ≡ r′
  dim-src′ c r′ e = trans (dim-src c) (cong pred e)

  dim-tgt′ : ∀ c r′ → dimC c ≡ suc r′ → dimC (tgtC c) ≡ r′
  dim-tgt′ c r′ e = trans (dim-tgt c) (cong pred e)

  one< : ∀ k r′ → T (k <ℕ r′) → T (1 <ℕ suc r′)
  one< k (suc r′) _ = tt
  one< k zero     p = lt0 k p

-- Replacing a top-dimensional right factor by its source or target.
comp-r : ∀ k a b r′ → dimC b ≡ suc r′ → T (k <ℕ r′) → Comp k a b →
         Comp k a (srcC b) × Comp k a (tgtC b)
comp-r k a b r′ eb kr cp with ∸-pos k r′ kr
... | m , e1 , e2 =
  trans base (trans (cong (λ n → srcN n (srcC b)) (sym e1))
                    (cong (λ d → srcN (d ∸ k) (srcC b)) (sym (dim-src′ b r′ eb)))) ,
  trans base (trans (sym (glob-src m b (subst (λ d → T (1 <ℕ d)) (sym eb) (one< k r′ kr))))
             (trans (cong (λ n → srcN n (tgtC b)) (sym e1))
                    (cong (λ d → srcN (d ∸ k) (tgtC b)) (sym (dim-tgt′ b r′ eb)))))
  where
  base : tgtN (dimC a ∸ k) a ≡ srcN (suc m) (srcC b)
  base = trans cp (trans (cong (λ d → srcN (d ∸ k) b) eb) (cong (λ n → srcN n b) e2))

-- Replacing a top-dimensional left factor by its source or target.
comp-l : ∀ k a b r′ → dimC a ≡ suc r′ → T (k <ℕ r′) → Comp k a b →
         Comp k (srcC a) b × Comp k (tgtC a) b
comp-l k a b r′ ea kr cp with ∸-pos k r′ kr
... | m , e1 , e2 =
  trans (cong (λ d → tgtN (d ∸ k) (srcC a)) (dim-src′ a r′ ea))
    (trans (cong (λ n → tgtN n (srcC a)) e1)
      (trans (glob-tgt m a (subst (λ d → T (1 <ℕ d)) (sym ea) (one< k r′ kr))) base)) ,
  trans (cong (λ d → tgtN (d ∸ k) (tgtC a)) (dim-tgt′ a r′ ea))
    (trans (cong (λ n → tgtN n (tgtC a)) e1) base)
  where
  base : tgtN (suc m) (tgtC a) ≡ srcN (dimC b ∸ k) b
  base = trans (cong (λ n → tgtN n a) (sym e2)) (trans (cong (λ d → tgtN (d ∸ k) a) (sym ea)) cp)

subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
subst₂ P refl refl p = p

private
  lt-irr : ∀ m → (m <ℕ m) ≡ false
  lt-irr zero    = refl
  lt-irr (suc m) = lt-irr m

  -- d ≤ n and not d < n give d = n.
  nlt-eq : ∀ d n → (d <ℕ n) ≡ false → Le d n → d ≡ n
  nlt-eq zero    zero    _ _ = refl
  nlt-eq zero    (suc n) () _
  nlt-eq (suc d) zero    _ p = lt0 d p
  nlt-eq (suc d) (suc n) e p = cong suc (nlt-eq d n e p)

  max-lt : ∀ a b n → T (a <ℕ n) → T (b <ℕ n) → T (max a b <ℕ n)
  max-lt zero    b       n       p q = q
  max-lt (suc a) zero    n       p q = p
  max-lt (suc a) (suc b) zero    p q = lt0 (suc a) p
  max-lt (suc a) (suc b) (suc n) p q = max-lt a b n p q

  max-both : ∀ a b n → T (a <ℕ n) → T (b <ℕ n) → max a b ≡ n → ⊥
  max-both a b n p q e = subst T (lt-irr n) (subst (λ m → T (m <ℕ n)) e (max-lt a b n p q))

  lt-pos′ : ∀ k a → T (k <ℕ a) → T (0 <ℕ a)
  lt-pos′ k (suc a) _ = tt
  lt-pos′ k zero    p = lt0 k p

-- Both factors at the top lose a dimension, and stay composable.
comp-lohi : ∀ k r′ a b → max (dimC a) (dimC b) ≡ suc r′ → T (k <ℕ r′) → Comp k a b →
  Comp k (loC (suc r′) a) (loC (suc r′) b) × Comp k (hiC (suc r′) a) (hiC (suc r′) b)
comp-lohi k r′ a b e kr cp with dimC a <ℕ suc r′ in ea | dimC b <ℕ suc r′ in eb
... | true  | true  = ⊥-elim (max-both (dimC a) (dimC b) (suc r′) (subst T (sym ea) tt) (subst T (sym eb) tt) e)
... | true  | false =
  (fst cr) ,
  (snd cr)
  where
  db = nlt-eq (dimC b) (suc r′) eb (le-eq {dimC b} (le-max-r (dimC a) (dimC b)) e)
  cr = comp-r k a b r′ db kr cp
... | false | true  =
  (fst cl) ,
  (snd cl)
  where
  da = nlt-eq (dimC a) (suc r′) ea (le-eq {dimC a} (le-max-l (dimC a) (dimC b)) e)
  cl = comp-l k a b r′ da kr cp
... | false | false =
  (fst (comp-r k (srcC a) b r′ db kr (fst cl))) ,
  (snd (comp-r k (tgtC a) b r′ db kr (snd cl)))
  where
  da = nlt-eq (dimC a) (suc r′) ea (le-eq {dimC a} (le-max-l (dimC a) (dimC b)) e)
  db = nlt-eq (dimC b) (suc r′) eb (le-eq {dimC b} (le-max-r (dimC a) (dimC b)) e)
  cl = comp-l k a b r′ da kr cp

-- Two cells agree at level r′ when their boundaries, and their lower
-- and upper parts at r′, agree. Then composites agree in type.
EqAt : Nat → Cell → Cell → Set
EqAt r′ x y = (srcC x ≡ srcC y × tgtC x ≡ tgtC y) × (loC r′ x ≡ loC r′ y × hiC r′ x ≡ hiC r′ y)

eqAt-refl : ∀ r′ x → EqAt r′ x x
eqAt-refl r′ x = (refl , refl) , (refl , refl)

private
  bty6 : Nat → Nat → Cell → Cell → Cell → Cell → Cell → Cell → Ty
  bty6 r″ k sa tb la lb ha hb =
    if r″ ==ℕ k then arr (snd sa) (fst sa) (fst tb)
    else arr (btyR r″ k la lb) (fst (binC k la lb)) (fst (binC k ha hb))

  cong6 : ∀ {A : Set} (f : Cell → Cell → Cell → Cell → Cell → Cell → A) {a a′ b b′ c c′ d d′ e e′ g g′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e′ → g ≡ g′ → f a b c d e g ≡ f a′ b′ c′ d′ e′ g′
  cong6 f refl refl refl refl refl refl = refl

btyR-eq : ∀ r″ k a b a′ b′ → EqAt (suc r″) a a′ → EqAt (suc r″) b b′ →
          btyR (suc r″) k a b ≡ btyR (suc r″) k a′ b′
btyR-eq r″ k a b a′ b′ ((s1 , _) , (l1 , h1)) ((_ , t2) , (l2 , h2)) =
  cong6 (bty6 r″ k) s1 t2 l1 l2 h1 h2

-- The upper and lower parts of a cell at level suc r′ agree at r′.
eqAt-hl : ∀ r′ c → T (0 <ℕ r′) → Le (dimC c) (suc r′) → EqAt r′ (hiC (suc r′) c) (loC (suc r′) c)
eqAt-hl r′ c p le with dimC c <ℕ suc r′ in e
... | true  = eqAt-refl r′ c
... | false = eq
  where
  tyE′ : snd (tgtC c) ≡ snd (srcC c)
  tyE′ = sym (src-tgt-type c)
  dt : dimC (tgtC c) ≡ r′
  dt = trans (dim-tgt c) (cong pred (nlt-eq (dimC c) (suc r′) e le))
  pos : T (0 <ℕ dimC (tgtC c))
  pos = subst (λ d → T (0 <ℕ d)) (sym dt) p
  ds : dimC (srcC c) ≡ r′
  ds = trans (cong dim (sym tyE′)) dt
  ss = src-type {tgtC c} {srcC c} tyE′ pos
  tt′ = tgt-type {tgtC c} {srcC c} tyE′ pos
  eq : EqAt r′ (tgtC c) (srcC c)
  eq = (ss , tt′) ,
       (trans (lo-no r′ (tgtC c) (trans (cong (_<ℕ r′) dt) (lt-irr r′)))
              (trans ss (sym (lo-no r′ (srcC c) (trans (cong (_<ℕ r′) ds) (lt-irr r′))))) ,
        trans (hi-no r′ (tgtC c) (trans (cong (_<ℕ r′) dt) (lt-irr r′)))
              (trans tt′ (sym (hi-no r′ (srcC c) (trans (cong (_<ℕ r′) ds) (lt-irr r′))))))

-- The source and target of a composite in dimension ≥ k+2 are parallel.
par-hl : ∀ k r′ u w → max (dimC u) (dimC w) ≡ suc r′ → T (k <ℕ r′) →
  snd (bcell k (hiC (suc r′) u) (hiC (suc r′) w)) ≡ snd (bcell k (loC (suc r′) u) (loC (suc r′) w))
par-hl k r′ u w e kr =
  trans (cong (λ n → btyR n k hu hw) hm)
        (trans (mid r′ kr refl) (sym (cong (λ n → btyR n k lu lw) lm)))
  where
  hu = hiC (suc r′) u
  hw = hiC (suc r′) w
  lu = loC (suc r′) u
  lw = loC (suc r′) w
  hm : max (dimC hu) (dimC hw) ≡ r′
  hm = subst (λ M → max (dimC (hiC M u)) (dimC (hiC M w)) ≡ pred M) e (hi-max u w)
  lm : max (dimC lu) (dimC lw) ≡ r′
  lm = subst (λ M → max (dimC (loC M u)) (dimC (loC M w)) ≡ pred M) e (lo-max u w)
  mid : ∀ n → T (k <ℕ n) → n ≡ r′ → btyR n k hu hw ≡ btyR n k lu lw
  mid zero     p _    = lt0 k p
  mid (suc r″) p refl =
    btyR-eq r″ k hu hw lu lw
      (eqAt-hl (suc r″) u tt (le-eq {dimC u} (le-max-l (dimC u) (dimC w)) e))
      (eqAt-hl (suc r″) w tt (le-eq {dimC w} (le-max-r (dimC u) (dimC w)) e))

------------------------------------------------------------------------
-- Evaluation over an expression context K whose variable i denotes the
-- cell semV i.

module Eval (K : ExCtx) (semV : Nat → Cell) where

  -- Variable weights, as the kernel computes them.
  W : Nat → Nat
  W i = nth 0 (weights K) i

  wt : Ex → Nat
  wt = wtE W

  -- The intended cell of a v/bn expression.
  sem : Ex → Cell
  sem (v i)      = semV i
  sem (bn k u w) = bcell k (sem u) (sem w)
  sem _          = var 0 , ⋆

  -- Composable composites.
  data Good : Ex → Set where
    gv : ∀ i → Good (v i)
    gb : ∀ {k u w} → Good u → Good w → T (k <ℕ dimC (sem u)) → T (k <ℕ dimC (sem w)) →
         Comp k (sem u) (sem w) → Good (bn k u w)

  -- X represents the type of the cell c.
  Rep : ExTy → Cell → Set
  Rep ob          c = snd c ≡ ⋆
  Rep (hom X s t) c =
    (Good s × Good t) × (sem s ≡ srcC c × sem t ≡ tgtC c) × T (0 <ℕ dimC c) × Rep X (srcC c)

  -- … with every expression in X of weight ≤ ω.
  TyRep : Nat → ExTy → Cell → Set
  TyRep ω ob          c = snd c ≡ ⋆
  TyRep ω (hom X s t) c =
    (Good s × Good t) × (Le (wt s) ω × Le (wt t) ω) × (sem s ≡ srcC c × sem t ≡ tgtC c) ×
    T (0 <ℕ dimC c) × TyRep ω X (srcC c)

  rep-ty : ∀ ω X c → Le (wtTy W X) ω → Rep X c → TyRep ω X c
  rep-ty ω ob          c _ ρ = ρ
  rep-ty ω (hom X s t) c q (g , e , p , ρ) =
    g , (le-trans (wt s) M ω (le-trans (wt s) st M (le-max-l (wt s) (wt t)) (le-max-r (wtTy W X) st)) q ,
         le-trans (wt t) M ω (le-trans (wt t) st M (le-max-r (wt s) (wt t)) (le-max-r (wtTy W X) st)) q) ,
    e , p , rep-ty ω X (srcC c) (le-trans (wtTy W X) M ω (le-max-l (wtTy W X) st) q) ρ
    where
    st = max (wt s) (wt t)
    M  = max (wtTy W X) st

  TyRep-mono : ∀ ω ω′ X c → Le ω ω′ → TyRep ω X c → TyRep ω′ X c
  TyRep-mono ω ω′ ob          c _ ρ = ρ
  TyRep-mono ω ω′ (hom X s t) c q (g , (ws , wt′) , e , p , ρ) =
    g , (le-trans (wt s) ω ω′ ws q , le-trans (wt t) ω ω′ wt′ q) , e , p , TyRep-mono ω ω′ X (srcC c) q ρ

  TyRep-dim : ∀ ω X c → TyRep ω X c → dimE X ≡ dimC c
  TyRep-dim ω ob          c ρ = cong dim (sym ρ)
  TyRep-dim ω (hom X s t) c (_ , _ , _ , p , ρ) =
    trans (cong suc (trans (TyRep-dim ω X (srcC c) ρ) (dim-src c))) (suc-pred (dimC c) p)

  -- The kernel's lower and upper parts of a factor (CaTTExp.Cones.tyF).
  loE hiE : Nat → ExTy → Ex → Ex
  loE r C e = if dimE C <ℕ r then e else srcE C
  hiE r C e = if dimE C <ℕ r then e else tgtE C

  lo-sem : ∀ r A e → Good e → TyRep (wt e) A (sem e) → T (0 <ℕ dimC (sem e)) →
           Good (loE r A e) × (sem (loE r A e) ≡ loC r (sem e)) × Le (wt (loE r A e)) (wt e)
  lo-sem r ob e g ρ p = ⊥-elim (subst (λ d → T (0 <ℕ d)) (sym (TyRep-dim (wt e) ob (sem e) ρ)) p)
  lo-sem r (hom A′ s t) e g ρ@((gs , _) , (ws , _) , (es , _) , _) p
    with suc (dimE A′) <ℕ r in eq
  ... | true  = g , sym (lo-yes r (sem e) (trans (cong (_<ℕ r) (sym (TyRep-dim (wt e) (hom A′ s t) (sem e) ρ))) eq)) ,
                le-refl (wt e)
  ... | false = gs , trans es (sym (lo-no r (sem e) (trans (cong (_<ℕ r) (sym (TyRep-dim (wt e) (hom A′ s t) (sem e) ρ))) eq))) ,
                ws

  hi-sem : ∀ r A e → Good e → TyRep (wt e) A (sem e) → T (0 <ℕ dimC (sem e)) →
           Good (hiE r A e) × (sem (hiE r A e) ≡ hiC r (sem e)) × Le (wt (hiE r A e)) (wt e)
  hi-sem r ob e g ρ p = ⊥-elim (subst (λ d → T (0 <ℕ d)) (sym (TyRep-dim (wt e) ob (sem e) ρ)) p)
  hi-sem r (hom A′ s t) e g ρ@((_ , gt) , (_ , wt′) , (_ , et) , _) p
    with suc (dimE A′) <ℕ r in eq
  ... | true  = g , sym (hi-yes r (sem e) (trans (cong (_<ℕ r) (sym (TyRep-dim (wt e) (hom A′ s t) (sem e) ρ))) eq)) ,
                le-refl (wt e)
  ... | false = gt , trans et (sym (hi-no r (sem e) (trans (cong (_<ℕ r) (sym (TyRep-dim (wt e) (hom A′ s t) (sem e) ρ))) eq))) ,
                wt′

  -- The kernel's type of a composite, split on whether it collapses.
  tyNC : Nat → Nat → ExTy → ExTy → Nat → Ex → Ex → ExTy
  tyNC f r A B k u w =
    hom (tyF f K (bn k (loE r A u) (loE r B w))) (bn k (loE r A u) (loE r B w)) (bn k (hiE r A u) (hiE r B w))

  tyBnB : Bool → Nat → ExTy → ExTy → Nat → Ex → Ex → ExTy
  tyBnB true  f A B k u w = hom (baseE A) (srcE A) (tgtE B)
  tyBnB false f A B k u w = tyNC f (max (dimE A) (dimE B)) A B k u w

  private
    if-bn : ∀ b f A B k u w →
      (if b then hom (baseE A) (srcE A) (tgtE B) else tyNC f (max (dimE A) (dimE B)) A B k u w)
      ≡ tyBnB b f A B k u w
    if-bn true  f A B k u w = refl
    if-bn false f A B k u w = refl

  tyF-bn : ∀ f k u w → tyF (suc f) K (bn k u w)
    ≡ tyBnB (max (dimE (tyF f K u)) (dimE (tyF f K w)) ==ℕ suc k) f (tyF f K u) (tyF f K w) k u w
  tyF-bn f k u w = if-bn (max (dimE (tyF f K u)) (dimE (tyF f K w)) ==ℕ suc k) f (tyF f K u) (tyF f K w) k u w

  private
    ==-true : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
    ==-true m n e = ==ℕ-sound m n (subst T (sym e) tt)

    -- A composite that does not collapse has dimension suc r′ with k < r′.
    nc-dim : ∀ k M → T (k <ℕ M) → (M ==ℕ suc k) ≡ false → Σ Nat (λ r′ → (M ≡ suc r′) × T (k <ℕ r′))
    nc-dim zero    (suc zero)     _ ()
    nc-dim zero    (suc (suc r)) _ _ = suc r , refl , tt
    nc-dim (suc k) (suc M)       p e with nc-dim k M p e
    ... | r′ , refl , q = suc r′ , refl , q
    nc-dim k       zero          p _ = lt0 k p

    ne-k : ∀ k r′ → T (k <ℕ r′) → (r′ ==ℕ k) ≡ false
    ne-k zero    (suc r′) _ = refl
    ne-k (suc k) (suc r′) p = ne-k k r′ p
    ne-k k       zero     p = lt0 k p

  -- Collapsing composites: u ∗_k w : ∂⁻u → ∂⁺w.
  TY-c : ∀ k u w A′ sa ta B′ sb tb →
    TyRep (wt u) (hom A′ sa ta) (sem u) → TyRep (wt w) (hom B′ sb tb) (sem w) →
    T (k <ℕ dimC (sem u)) → T (k <ℕ dimC (sem w)) → Comp k (sem u) (sem w) →
    max (dimC (sem u)) (dimC (sem w)) ≡ suc k →
    TyRep (wt (bn k u w)) (hom A′ sa tb) (sem (bn k u w))
  TY-c k u w A′ sa ta B′ sb tb ((gsa , _) , (wsa , _) , (esa , _) , _ , ρA′) ((_ , gtb) , (_ , wtb) , (_ , etb) , _ , _)
       pu pw cp M =
    (gsa , gtb) ,
    (le-step (wt sa) ω (le-trans (wt sa) (wt u) ω wsa (le-max-l (wt u) (wt w))) ,
     le-step (wt tb) ω (le-trans (wt tb) (wt w) ω wtb (le-max-r (wt u) (wt w)))) ,
    (trans esa (sym (bc-src-c k su sw M)) ,
     trans etb (trans (cong (fst (tgtC sw) ,_) tyeq) (sym (bc-tgt-c k su sw M)))) ,
    subst (λ d → T (0 <ℕ d)) (sym (trans (bc-dim k su sw pu pw) M)) tt ,
    subst (TyRep (suc ω) A′) (sym (bc-src-c k su sw M))
          (TyRep-mono (wt u) (suc ω) A′ (srcC su) (le-step (wt u) ω (le-max-l (wt u) (wt w))) ρA′)
    where
    su = sem u
    sw = sem w
    ω = max (wt u) (wt w)
    du : dimC su ≡ suc k
    du = squeeze k (dimC su) pu (le-eq {dimC su} (le-max-l (dimC su) (dimC sw)) M)
    dw : dimC sw ≡ suc k
    dw = squeeze k (dimC sw) pw (le-eq {dimC sw} (le-max-r (dimC su) (dimC sw)) M)
    c1 : tgtC su ≡ srcC sw
    c1 = trans (sym (trans (cong (λ d → tgtN (d ∸ k) su) du) (cong (λ n → tgtN n su) (sk∸k k))))
               (trans cp (trans (cong (λ d → srcN (d ∸ k) sw) dw) (cong (λ n → srcN n sw) (sk∸k k))))
    tyeq : snd (tgtC sw) ≡ snd (srcC su)
    tyeq = trans (sym (src-tgt-type sw)) (trans (cong snd (sym c1)) (sym (src-tgt-type su)))

  -- Composites that do not collapse: their boundaries are composites
  -- of the lower and upper parts.
  TY-nc : ∀ f r′ k u w A B → Good u → Good w →
    TyRep (wt u) A (sem u) → TyRep (wt w) B (sem w) →
    T (k <ℕ dimC (sem u)) → T (k <ℕ dimC (sem w)) → Comp k (sem u) (sem w) →
    max (dimC (sem u)) (dimC (sem w)) ≡ suc r′ → T (k <ℕ r′) →
    (∀ e → Good e → Le (suc (dimC (sem e) + wt e)) f → TyRep (wt e) (tyF f K e) (sem e)) →
    Le (dimC (sem (bn k u w)) + wt (bn k u w)) f →
    TyRep (wt (bn k u w)) (tyNC f (suc r′) A B k u w) (sem (bn k u w))
  TY-nc f r′ k u w A B gu gw ρA ρB pu pw cp M kr ih q =
    (gs′ , gt′) , (ws′ , wt″) , (es′ , et′) , pos , ρ′
    where
    su = sem u
    sw = sem w
    ω = max (wt u) (wt w)
    r = suc r′
    lu = loE r A u
    lw = loE r B w
    hu = hiE r A u
    hw = hiE r B w
    Lu = lo-sem r A u gu ρA (lt-pos′ k (dimC su) pu)
    Lw = lo-sem r B w gw ρB (lt-pos′ k (dimC sw) pw)
    Hu = hi-sem r A u gu ρA (lt-pos′ k (dimC su) pu)
    Hw = hi-sem r B w gw ρB (lt-pos′ k (dimC sw) pw)
    elu = fst (snd Lu)
    elw = fst (snd Lw)
    ehu = fst (snd Hu)
    ehw = fst (snd Hw)
    ek = ne-k k r′ kr
    s′ = bn k lu lw
    t′ = bn k hu hw
    dB : dimC (bcell k su sw) ≡ r
    dB = trans (bc-dim k su sw pu pw) M
    es′ : sem s′ ≡ srcC (bcell k su sw)
    es′ = trans (cong₂ (bcell k) elu elw) (sym (bc-src-nc r′ k su sw M ek))
    et′ : sem t′ ≡ tgtC (bcell k su sw)
    et′ = trans (cong₂ (bcell k) ehu ehw)
            (trans (cong (fst (bcell k (hiC r su) (hiC r sw)) ,_) (par-hl k r′ su sw M kr))
                   (sym (bc-tgt-nc r′ k su sw M ek)))
    gs′ : Good s′
    gs′ = gb (fst Lu) (fst Lw)
             (subst (λ c → T (k <ℕ dimC c)) (sym elu) (lo-above k r′ su pu kr))
             (subst (λ c → T (k <ℕ dimC c)) (sym elw) (lo-above k r′ sw pw kr))
             (subst₂ (Comp k) (sym elu) (sym elw) (fst (comp-lohi k r′ su sw M kr cp)))
    gt′ : Good t′
    gt′ = gb (fst Hu) (fst Hw)
             (subst (λ c → T (k <ℕ dimC c)) (sym ehu) (hi-above k r′ su pu kr))
             (subst (λ c → T (k <ℕ dimC c)) (sym ehw) (hi-above k r′ sw pw kr))
             (subst₂ (Comp k) (sym ehu) (sym ehw) (snd (comp-lohi k r′ su sw M kr cp)))
    ws′ : Le (wt s′) (suc ω)
    ws′ = max-mono (wt lu) (wt lw) (wt u) (wt w) (snd (snd Lu)) (snd (snd Lw))
    wt″ : Le (wt t′) (suc ω)
    wt″ = max-mono (wt hu) (wt hw) (wt u) (wt w) (snd (snd Hu)) (snd (snd Hw))
    pos : T (0 <ℕ dimC (bcell k su sw))
    pos = subst (λ d → T (0 <ℕ d)) (sym dB) tt
    ds′ : dimC (sem s′) ≡ r′
    ds′ = trans (cong dimC es′) (trans (dim-src (bcell k su sw)) (cong pred dB))
    q′ : Le (suc (r′ + suc ω)) f
    q′ = eq-le {suc r′ + suc ω} {dimC (bcell k su sw) + suc ω} {f} (cong (_+ suc ω) (sym dB)) q
    fs : Le (suc (dimC (sem s′) + wt s′)) f
    fs = eq-le {suc (dimC (sem s′) + wt s′)} {suc (r′ + wt s′)} {f} (cong (λ d → suc (d + wt s′)) ds′)
           (le-trans (suc (r′ + wt s′)) (suc (r′ + suc ω)) f (le-+ r′ r′ (wt s′) (suc ω) (le-refl r′) ws′) q′)
    ρ′ : TyRep (suc ω) (tyF f K s′) (srcC (bcell k su sw))
    ρ′ = subst (TyRep (suc ω) (tyF f K s′)) es′
               (TyRep-mono (wt s′) (suc ω) (tyF f K s′) (sem s′) ws′ (ih s′ gs′ fs))

  le-pred : ∀ n → Le (pred n) n
  le-pred zero    = tt
  le-pred (suc n) = le-suc n

  private

    le-pred′ : ∀ a n → Le (suc a) n → Le a (pred n)
    le-pred′ a (suc n) p = p
    le-pred′ a zero    p = lt0 a p

    lt-max : ∀ k a b → T (k <ℕ a) → T (k <ℕ max a b)
    lt-max k a b p = le-lt k (max a b) (le-trans (suc k) a (max a b) (lt-le k a p) (le-max-l a b))

  -- The symbolic type of a composable composite represents its type.
  module Typing (okv : ∀ i → TyRep (pred (W i)) (nth ob K i) (semV i)) where

    private
      TYb : ∀ f k u w → Good u → Good w → T (k <ℕ dimC (sem u)) → T (k <ℕ dimC (sem w)) →
        Comp k (sem u) (sem w) →
        (∀ e → Good e → Le (suc (dimC (sem e) + wt e)) f → TyRep (wt e) (tyF f K e) (sem e)) →
        ∀ A B → TyRep (wt u) A (sem u) → TyRep (wt w) B (sem w) →
        ∀ b → (max (dimE A) (dimE B) ==ℕ suc k) ≡ b →
        Le (dimC (sem (bn k u w)) + wt (bn k u w)) f →
        TyRep (wt (bn k u w)) (tyBnB b f A B k u w) (sem (bn k u w))
      TYb f k u w gu gw pu pw cp ih ob B ρA ρB b eb q =
        lt0 k (subst (λ d → T (k <ℕ d)) (sym (TyRep-dim (wt u) ob (sem u) ρA)) pu)
      TYb f k u w gu gw pu pw cp ih (hom A′ sa ta) ob ρA ρB b eb q =
        lt0 k (subst (λ d → T (k <ℕ d)) (sym (TyRep-dim (wt w) ob (sem w) ρB)) pw)
      TYb f k u w gu gw pu pw cp ih (hom A′ sa ta) (hom B′ sb tb) ρA ρB true eb q =
        TY-c k u w A′ sa ta B′ sb tb ρA ρB pu pw cp
          (trans (sym (cong₂ max (TyRep-dim (wt u) (hom A′ sa ta) (sem u) ρA)
                                 (TyRep-dim (wt w) (hom B′ sb tb) (sem w) ρB)))
                 (==-true _ _ eb))
      TYb f k u w gu gw pu pw cp ih A B ρA ρB false eb q
        with nc-dim k (max (dimC (sem u)) (dimC (sem w))) (lt-max k (dimC (sem u)) (dimC (sem w)) pu)
               (trans (cong (_==ℕ suc k) (sym MA)) eb)
        where
        MA : max (dimE A) (dimE B) ≡ max (dimC (sem u)) (dimC (sem w))
        MA = cong₂ max (TyRep-dim (wt u) A (sem u) ρA) (TyRep-dim (wt w) B (sem w) ρB)
      ... | r′ , M , kr =
        subst (λ r → TyRep (wt (bn k u w)) (tyNC f r A B k u w) (sem (bn k u w)))
              (sym (trans (cong₂ max (TyRep-dim (wt u) A (sem u) ρA) (TyRep-dim (wt w) B (sem w) ρB)) M))
              (TY-nc f r′ k u w A B gu gw ρA ρB pu pw cp M kr ih q)

    TY : ∀ f e → Good e → Le (suc (dimC (sem e) + wt e)) f → TyRep (wt e) (tyF f K e) (sem e)
    TY zero    e          g q = lt0 (dimC (sem e) + wt e) q
    TY (suc f) (v i)      (gv .i) q =
      TyRep-mono (pred (W i)) (W i) (nth ob K i) (semV i) (le-pred (W i)) (okv i)
    TY (suc f) (bn k u w) (gb gu gw pu pw cp) q =
      subst (λ X → TyRep (wt (bn k u w)) X (sem (bn k u w))) (sym (tyF-bn f k u w))
        (TYb f k u w gu gw pu pw cp (TY f) (tyF f K u) (tyF f K w) (TY f u gu qu) (TY f w gw qw)
             _ refl q)
      where
      su = sem u
      sw = sem w
      Mx = max (dimC su) (dimC sw)
      ω = max (wt u) (wt w)
      q₀ : Le (suc (Mx + ω)) f
      q₀ = eq-le {suc (Mx + ω)} {dimC (bcell k su sw) + suc ω} {f} (trans (sym (+-suc Mx ω)) (cong (_+ suc ω) (sym (bc-dim k su sw pu pw)))) q
      qu : Le (suc (dimC su + wt u)) f
      qu = le-trans (suc (dimC su + wt u)) (suc (Mx + ω)) f
             (le-+ (dimC su) Mx (wt u) ω (le-max-l (dimC su) (dimC sw)) (le-max-l (wt u) (wt w))) q₀
      qw : Le (suc (dimC sw + wt w)) f
      qw = le-trans (suc (dimC sw + wt w)) (suc (Mx + ω)) f
             (le-+ (dimC sw) Mx (wt w) ω (le-max-r (dimC su) (dimC sw)) (le-max-r (wt u) (wt w))) q₀

    -- Evaluation, with every expression of dimension ≤ Dm and weight
    -- ≤ Ωm, and enough fuel for typing.
    module Sound (okf : ∀ i → fst (semV i) ≡ var i) (Dm Ωm : Nat)
                 (fuelOK : Le (suc (Dm + Ωm)) (fuelOf K)) where

      tyE-ok : ∀ e → Good e → Le (dimC (sem e)) Dm → Le (wt e) Ωm → TyRep (wt e) (tyE K e) (sem e)
      tyE-ok e g qd qw =
        TY (fuelOf K) e g (le-trans (suc (dimC (sem e) + wt e)) (suc (Dm + Ωm)) (fuelOf K)
                                    (le-+ (dimC (sem e)) Dm (wt e) Ωm qd qw) fuelOK)

      mutual
        EV : ∀ f e → Good e → Le (dimC (sem e)) Dm → Le (wt e) Ωm → Le (B (dimC (sem e)) (wt e)) f →
             evF f K e ≡ fst (sem e)
        EV zero    e g qd qw qf = lt0 (dimC (sem e) + (wt e + wt e)) qf
        EV (suc f) _ (gv i) qd qw qf = sym (okf i)
        EV (suc zero) _ (gb {k} {u} {w} gu gw pu pw cp) qd qw qf =
          lt0 (B (dimC (sem (bn k u w))) (max (wt u) (wt w)))
              (eq-le {suc (suc (B (dimC (sem (bn k u w))) (max (wt u) (wt w))))}
                     {B (dimC (sem (bn k u w))) (suc (max (wt u) (wt w)))} {suc zero}
                     (sym (B-suc (dimC (sem (bn k u w))) (max (wt u) (wt w)))) qf)
        EV (suc (suc f)) _ (gb {k} {u} {w} gu gw pu pw cp) qd qw qf =
          cong₂ (λ a b → fst (binC k a b))
            (CELL f u gu (le-trans (dimC su) d Dm (dm′ {dimC su} (le-max-l (dimC su) (dimC sw))) qd)
                         (le-trans (wt u) ω Ωm (le-max-l (wt u) (wt w)) qω)
                         (le-trans (B (dimC su) (wt u)) (B d ω) f
                                   (B-mono (dimC su) d (wt u) ω (dm′ {dimC su} (le-max-l (dimC su) (dimC sw))) (le-max-l (wt u) (wt w))) qf′))
            (CELL f w gw (le-trans (dimC sw) d Dm (dm′ {dimC sw} (le-max-r (dimC su) (dimC sw))) qd)
                         (le-trans (wt w) ω Ωm (le-max-r (wt u) (wt w)) qω)
                         (le-trans (B (dimC sw) (wt w)) (B d ω) f
                                   (B-mono (dimC sw) d (wt w) ω (dm′ {dimC sw} (le-max-r (dimC su) (dimC sw))) (le-max-r (wt u) (wt w))) qf′))
          where
          su = sem u
          sw = sem w
          d = dimC (sem (bn k u w))
          Mx = max (dimC su) (dimC sw)
          ω = max (wt u) (wt w)
          dm : Mx ≡ d
          dm = sym (bc-dim k su sw pu pw)
          dm′ : ∀ {a} → Le a Mx → Le a d
          dm′ {a} p = le-eq {a} p dm
          qω : Le ω Ωm
          qω = le-trans ω (suc ω) Ωm (le-suc ω) qw
          qf′ : Le (B d ω) f
          qf′ = eq-le {suc (suc (B d ω))} {B d (suc ω)} {suc (suc f)} (sym (B-suc d ω)) qf

        CELL : ∀ f e → Good e → Le (dimC (sem e)) Dm → Le (wt e) Ωm → Le (B (dimC (sem e)) (wt e)) f →
               cellF (suc f) K e ≡ sem e
        CELL f e g qd qw qf =
          cong₂ _,_ (EV f e g qd qw qf) (TYEV f (tyE K e) (sem e) (wt e) (tyE-ok e g qd qw) qd qw qf)

        TYEV : ∀ f X c ω → TyRep ω X c → Le (dimC c) Dm → Le ω Ωm → Le (B (dimC c) ω) f →
               evTyF f K X ≡ snd c
        TYEV zero    X           c ω ρ qd qw qf = lt0 (dimC c + (ω + ω)) qf
        TYEV (suc f) ob          c ω ρ qd qw qf = sym ρ
        TYEV (suc f) (hom X s t) c ω ((gs , gt) , (ws , wt′) , (es , et) , p , ρ) qd qw qf =
          trans (cong₂ (λ A ab → arr A (fst ab) (snd ab))
                       (TYEV f X (srcC c) ω ρ qd′ qw qfX)
                       (cong₂ _,_ (trans (EV f s gs (ds qd′) (le-trans (wt s) ω Ωm ws qw) (bs ws)) (cong fst es))
                                  (trans (EV f t gt (dt qd′) (le-trans (wt t) ω Ωm wt′ qw) (bt wt′)) (cong fst et))))
                (sym (ty-split c p))
          where
          dc = dimC c
          dsc : dimC (srcC c) ≡ pred dc
          dsc = dim-src c
          qd′ : Le (dimC (srcC c)) Dm
          qd′ = le-trans (dimC (srcC c)) dc Dm (eq-le {dimC (srcC c)} {pred dc} {dc} dsc (le-pred dc)) qd
          qfX : Le (B (dimC (srcC c)) ω) f
          qfX = eq-le {B (dimC (srcC c)) ω} {B (pred dc) ω} {f} (cong (λ n → B n ω) dsc)
                      (eq-le {suc (B (pred dc) ω)} {B dc ω} {suc f} (cong (λ n → B n ω) (suc-pred dc p)) qf)
          ds : Le (dimC (srcC c)) Dm → Le (dimC (sem s)) Dm
          ds q = eq-le {dimC (sem s)} {dimC (srcC c)} {Dm} (cong dimC es) q
          dt : Le (dimC (srcC c)) Dm → Le (dimC (sem t)) Dm
          dt q = eq-le {dimC (sem t)} {dimC (srcC c)} {Dm}
                       (trans (cong dimC et) (trans (dim-tgt c) (sym dsc))) q
          bs : Le (wt s) ω → Le (B (dimC (sem s)) (wt s)) f
          bs q = le-trans (B (dimC (sem s)) (wt s)) (B (dimC (srcC c)) ω) f
                   (B-mono (dimC (sem s)) (dimC (srcC c)) (wt s) ω
                           (eq-le {dimC (sem s)} {dimC (srcC c)} {dimC (srcC c)} (cong dimC es) (le-refl (dimC (srcC c)))) q) qfX
          bt : Le (wt t) ω → Le (B (dimC (sem t)) (wt t)) f
          bt q = le-trans (B (dimC (sem t)) (wt t)) (B (dimC (srcC c)) ω) f
                   (B-mono (dimC (sem t)) (dimC (srcC c)) (wt t) ω
                           (eq-le {dimC (sem t)} {dimC (srcC c)} {dimC (srcC c)}
                                  (trans (cong dimC et) (trans (dim-tgt c) (sym dsc))) (le-refl (dimC (srcC c)))) q) qfX

------------------------------------------------------------------------
-- Lists.

module _ where
  length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  nth-app-l : ∀ {A : Set} (d : A) xs ys i → T (i <ℕ length xs) → nth d (xs ++ ys) i ≡ nth d xs i
  nth-app-l d (x ∷ xs) ys zero    _ = refl
  nth-app-l d (x ∷ xs) ys (suc i) p = nth-app-l d xs ys i p
  nth-app-l d []       ys i       p = lt0 i p

  nth-last : ∀ {A : Set} (d : A) xs (x : A) → nth d (xs ++ (x ∷ [])) (length xs) ≡ x
  nth-last d []       x = refl
  nth-last d (y ∷ xs) x = nth-last d xs x

  nth-out : ∀ {A : Set} (d : A) xs i → (i <ℕ length xs) ≡ false → nth d xs i ≡ d
  nth-out d []       i       _ = refl
  nth-out d (x ∷ xs) zero    ()
  nth-out d (x ∷ xs) (suc i) e = nth-out d xs i e

  lt-len-snoc : ∀ {A : Set} (xs : List A) (x : A) i → T (i <ℕ length xs) → T (i <ℕ length (xs ++ (x ∷ [])))
  lt-len-snoc (y ∷ xs) x zero    _ = tt
  lt-len-snoc (y ∷ xs) x (suc i) p = lt-len-snoc xs x i p
  lt-len-snoc []       x i       p = lt0 i p

  len-snoc-lt : ∀ {A : Set} (xs : List A) (x : A) → T (length xs <ℕ length (xs ++ (x ∷ [])))
  len-snoc-lt []       x = tt
  len-snoc-lt (y ∷ xs) x = len-snoc-lt xs x

  nth-map-dim : ∀ (K : ExCtx) i → nth 0 (map dimE K) i ≡ dimE (nth ob K i)
  nth-map-dim []       i       = refl
  nth-map-dim (A ∷ K) zero    = refl
  nth-map-dim (A ∷ K) (suc i) = nth-map-dim K i

le-maxL : ∀ xs i → Le (nth 0 xs i) (maxL xs)
le-maxL []       i       = tt
le-maxL (x ∷ xs) zero    = le-max-l x (maxL xs)
le-maxL (x ∷ xs) (suc i) = le-trans (nth 0 xs i) (maxL xs) _ (le-maxL xs i) (le-max-r x (maxL xs))

------------------------------------------------------------------------
-- Scoping and weights.

data ScE (n : Nat) : Ex → Set where
  sv : ∀ {j} → T (j <ℕ n) → ScE n (v j)
  sb : ∀ {k u w} → ScE n u → ScE n w → ScE n (bn k u w)

ScTy : Nat → ExTy → Set
ScTy n ob          = ⊤
ScTy n (hom X s t) = ScTy n X × ScE n s × ScE n t

wt-ext : ∀ n (W W′ : Nat → Nat) → (∀ j → T (j <ℕ n) → W j ≡ W′ j) → ∀ {e} → ScE n e → wtE W e ≡ wtE W′ e
wt-ext n W W′ h (sv {j} p)   = h j p
wt-ext n W W′ h (sb su sw)   = cong suc (cong₂ max (wt-ext n W W′ h su) (wt-ext n W W′ h sw))

wtTy-ext : ∀ n (W W′ : Nat → Nat) → (∀ j → T (j <ℕ n) → W j ≡ W′ j) → ∀ X → ScTy n X → wtTy W X ≡ wtTy W′ X
wtTy-ext n W W′ h ob          _              = refl
wtTy-ext n W W′ h (hom X s t) (sX , ss , st) =
  cong₂ max (wtTy-ext n W W′ h X sX) (cong₂ max (wt-ext n W W′ h ss) (wt-ext n W W′ h st))

private
  wG-prefix : ∀ acc As j → T (j <ℕ length acc) → nth 0 (weightsGo acc As) j ≡ nth 0 acc j
  wG-prefix acc []       j p = refl
  wG-prefix acc (A ∷ As) j p =
    trans (wG-prefix (acc ++ (a ∷ [])) As j (lt-len-snoc acc a j p)) (nth-app-l 0 acc (a ∷ []) j p)
    where a = suc (wtTy (λ i → nth 0 acc i) A)

  wG-new : ∀ acc As i → T (i <ℕ length As) → ScTy (length acc + i) (nth ob As i) →
           nth 0 (weightsGo acc As) (length acc + i)
           ≡ suc (wtTy (λ j → nth 0 (weightsGo acc As) j) (nth ob As i))
  wG-new acc (A ∷ As) zero p sc =
    trans (cong (nth 0 (weightsGo acc′ As)) (+-zero (length acc)))
      (trans (wG-prefix acc′ As (length acc) (len-snoc-lt acc a))
        (trans (nth-last 0 acc a)
               (cong suc (wtTy-ext (length acc) (λ j → nth 0 acc j) (λ j → nth 0 (weightsGo acc′ As) j)
                  (λ j q → sym (trans (wG-prefix acc′ As j (lt-len-snoc acc a j q)) (nth-app-l 0 acc (a ∷ []) j q)))
                  A (subst (λ n → ScTy n A) (+-zero (length acc)) sc)))))
    where
    a = suc (wtTy (λ i → nth 0 acc i) A)
    acc′ = acc ++ (a ∷ [])
  wG-new acc (A ∷ As) (suc i) p sc =
    trans (cong (nth 0 (weightsGo acc′ As)) (sym e))
          (wG-new acc′ As i p (subst (λ n → ScTy n (nth ob As i)) (sym e) sc))
    where
    a = suc (wtTy (λ i → nth 0 acc i) A)
    acc′ = acc ++ (a ∷ [])
    e : length acc′ + i ≡ length acc + suc i
    e = trans (cong (_+ i) (length-++ acc (a ∷ []))) (trans (cong (_+ i) (plus1 (length acc))) (sym (+-suc (length acc) i)))
      where
      plus1 : ∀ n → n + 1 ≡ suc n
      plus1 zero    = refl
      plus1 (suc n) = cong suc (plus1 n)
  wG-new acc [] i p sc = lt0 i p

-- In a scoped context, a variable weighs one more than its type.
weight-var : ∀ K i → T (i <ℕ length K) → ScTy i (nth ob K i) →
             nth 0 (weights K) i ≡ suc (wtTy (λ j → nth 0 (weights K) j) (nth ob K i))
weight-var K i p sc = wG-new [] K i p sc

------------------------------------------------------------------------
-- The evaluated context: under the hypotheses below, the kernel
-- evaluates the i-th entry of K to the type of semV i.

module Main (K : ExCtx) (semV : Nat → Cell) where
  open Eval K semV public

  -- The context of the intended types, from level j on.
  semGo : Nat → Nat → Ctx → Ctx
  semGo j zero    acc = acc
  semGo j (suc n) acc = semGo (suc j) n (acc ▸ snd (semV j))

  module Hyp (rep : ∀ i → T (i <ℕ length K) → Rep (nth ob K i) (semV i))
             (repOut : ∀ i → (i <ℕ length K) ≡ false → snd (semV i) ≡ ⋆)
             (okf : ∀ i → fst (semV i) ≡ var i)
             (sc : ∀ i → T (i <ℕ length K) → ScTy i (nth ob K i)) where

    D Ω : Nat
    D = maxL (map dimE K)
    Ω = maxL (weights K)

    okv : ∀ i → TyRep (pred (W i)) (nth ob K i) (semV i)
    okv i with i <ℕ length K in e
    ... | true  = rep-ty (pred (W i)) (nth ob K i) (semV i)
                    (subst (λ n → Le (wtTy W (nth ob K i)) (pred n)) (sym (weight-var K i p (sc i p)))
                           (le-refl (wtTy W (nth ob K i))))
                    (rep i p)
      where p = subst T (sym e) tt
    ... | false = subst (λ X → TyRep (pred (W i)) X (semV i)) (sym (nth-out ob K i e)) (repOut i e)

    fuelB : Le (B D Ω) (fuelOf K)
    fuelB = le-+l fuel (B D Ω)

    fuelOK : Le (suc (D + Ω)) (fuelOf K)
    fuelOK = le-trans (suc (D + Ω)) (B D Ω) (fuelOf K)
                      (le-+ D D Ω (Ω + Ω) (le-refl D) (le-+l Ω Ω)) fuelB

    open Typing okv public
    open Sound okf D Ω fuelOK public

    evTy-ok : ∀ i → evTy K (nth ob K i) ≡ snd (semV i)
    evTy-ok i = TYEV (fuelOf K) (nth ob K i) (semV i) (pred (W i)) (okv i) qd qw
                     (le-trans (B (dimC (semV i)) (pred (W i))) (B D Ω) (fuelOf K)
                               (B-mono (dimC (semV i)) D (pred (W i)) Ω qd qw) fuelB)
      where
      qd : Le (dimC (semV i)) D
      qd = eq-le {dimC (semV i)} {nth 0 (map dimE K) i} {D}
                 (trans (sym (TyRep-dim (pred (W i)) (nth ob K i) (semV i) (okv i))) (sym (nth-map-dim K i)))
                 (le-maxL (map dimE K) i)
      qw : Le (pred (W i)) Ω
      qw = le-trans (pred (W i)) (W i) Ω (le-pred (W i)) (le-maxL (weights K) i)

    evGo : ∀ As j acc → (∀ m → T (m <ℕ length As) → nth ob As m ≡ nth ob K (j + m)) →
           evCtxGo K As acc ≡ semGo j (length As) acc
    evGo []       j acc h = refl
    evGo (A ∷ As) j acc h =
      trans (cong (λ X → evCtxGo K As (acc ▸ X))
                  (trans (cong (evTy K) (trans (h 0 tt) (cong (nth ob K) (+-zero j)))) (evTy-ok j)))
            (evGo As (suc j) (acc ▸ snd (semV j))
                  (λ m q → trans (h (suc m) q) (cong (nth ob K) (+-suc j m))))

    -- The kernel's evaluation of K is the context of intended types.
    evCtx-ok : evCtx K ≡ semGo 0 (length K) ε
    evCtx-ok = evGo K 0 ε (λ m _ → refl)
