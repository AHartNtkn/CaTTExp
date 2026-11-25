------------------------------------------------------------------------
-- The forced-lift rule for the interpretation of a coherence head in
-- V + S (spec/02-lax-core.md §2.2–2.3; ledger S11;
-- notes/designated-lift.md).
--
-- Over a free-object layer (CaTTExp.Uniform.Rule.Layer), a witness of
-- SC(x, z) is a path of letters x → z with full support.  A cell one
-- dimension up is the value ⟦p⟧ of such a path (`Cells`), with
-- decidable equality.  The old spec fixed, per head, a *designated*
-- lift: the first shortest witness in an enumeration order.  When two
-- witnesses have different values this choice is not determined by the
-- free object.
--
-- The repaired rule accepts a head iff its lift is **forced**: some
-- simple witness (no vertex visited twice) exists, and every simple
-- witness has the same value.  That value is the interpretation.
--
-- Proved here, for every layer:
--   forced-unique     the interpretation of a forced head is unique;
--   forced-sc         a forced head satisfies SC (the old rule), so the
--                     repaired rule accepts no more heads than the old;
--   simple-loop,      the only simple path x → x is ε, so a coherence-
--   coh-forced        case head (equal images, full support) is always
--                     forced, at the identity, whatever loops x carries;
--   shortest-simple,  under the hypothesis CutFull (removing a cycle
--   designated-agrees from a witness leaves a witness: in V + S every
--                     cycle projects to an identity of the loop-free
--                     𝔉(Γ), so it adds no support), every shortest
--                     witness is simple; hence on a forced head every
--                     designated choice of the old rule, whatever the
--                     enumeration order, has the forced value;
--   DecideForced.forced?    over a finite closed universe of cells, whether
--                     a head is forced, and its value, is decidable.
--
-- Examples (bottom of the file):
--   Strip       two parallel simple witnesses u, v with different
--               values (setting ∅, the strip C_{2,1} of spec §2.3 (b);
--               the separation itself is r5 (K44)/(K51), not
--               re-proved here): SC holds, the shortest witness is u,
--               and the head is not forced; checked by `forced?`.
--   StripInner  the same graph with the values identified (setting
--               {inner law}): the head is forced.
--   Loop        a vertex w with a loop H whose powers are pairwise
--               distinct (the loop H of (K34)/(K45) against 1_w,
--               ledger E13): every Hⁿ is a witness of w → w, and the
--               head is forced at the identity.
--   LetterHeads option (E) of design-decisions §5.8: forced heads plus
--               native one-letter heads (Native is an abstract parameter).
--   Bridge      the raising bridge B on ΣD⁴ ∨ ΣD⁴: not forced, shortest,
--               accepted by (E) (values: count of B, toy supports).
--   StripE      the strip head is rejected by (E) (no native letters).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite
  using (_∈L_; here; there; NoDup; []; _∷_; lengthL; _≤_; z≤n; s≤s; pigeon)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Rule

module CaTTExp.Uniform.ForcedLift where

------------------------------------------------------------------------
-- Small facts about ≤.

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

<-irrefl : ∀ {m n} → suc m ≤ n → n ≤ m → ⊥
<-irrefl (s≤s p) (s≤s q) = <-irrefl p q

------------------------------------------------------------------------
-- Values of paths.

record Cells (L : Layer) : Set₁ where
  open Layer L
  field
    Up   : Cell → Cell → Set
    ⟦_⟧  : ∀ {x z} → Path L x z → Up x z
    _≟U_ : ∀ {x z} (a b : Up x z) → Dec (a ≡ b)

module Forced (L : Layer) (C : Cells L) where
  open Layer L
  open Cells C

  infixr 5 _++P_
  _++P_ : ∀ {x y z} → Path L x y → Path L y z → Path L x z
  ε            ++P r = r
  (ℓ ◅[ m ] q) ++P r = ℓ ◅[ m ] (q ++P r)

  -- Every vertex a path visits, source and target included.
  vertsP : ∀ {x z} → Path L x z → List Cell
  vertsP {x} ε            = x ∷ []
  vertsP {x} (ℓ ◅[ m ] p) = x ∷ vertsP p

  Simple : ∀ {x z} → Path L x z → Set
  Simple p = NoDup (vertsP p)

  Full : ∀ {x z} → Path L x z → Set
  Full p = T (full (suppP L p))

  -- The repaired rule: the head x → z is accepted, with value c, iff c
  -- is the value of a simple witness and of every simple witness.
  record Forced (x z : Cell) (c : Up x z) : Set where
    field
      path   : Path L x z
      fullW  : Full path
      simple : Simple path
      named  : ⟦ path ⟧ ≡ c
      unique : ∀ (p : Path L x z) → Full p → Simple p → ⟦ p ⟧ ≡ c
  open Forced public

  forced-unique : ∀ {x z c c′} → Forced x z c → Forced x z c′ → c ≡ c′
  forced-unique F F′ = trans (sym (named F)) (unique F′ (path F) (fullW F) (simple F))

  forced-sc : ∀ {x z c} → Forced x z c → SC L x z
  forced-sc F = path F , fullW F

  ----------------------------------------------------------------------
  -- Membership in the vertex list.

  mem? : (y : Cell) (ys : List Cell) → Dec (y ∈L ys)
  mem? y [] = no λ ()
  mem? y (w ∷ ws) with y ≟ w
  ... | yes refl = yes here
  ... | no ne with mem? y ws
  ...   | yes m = yes (there m)
  ...   | no ¬m = no λ { here → ne refl ; (there m) → ¬m m }

  nodup? : (ys : List Cell) → Dec (NoDup ys)
  nodup? [] = yes []
  nodup? (y ∷ ys) with mem? y ys | nodup? ys
  ... | yes m | _      = no λ { (n ∷ _) → n m }
  ... | no ¬m | yes nd = yes (¬m ∷ nd)
  ... | no ¬m | no ¬nd = no λ { (_ ∷ nd) → ¬nd nd }

  end∈ : ∀ {x z} (p : Path L x z) → z ∈L vertsP p
  end∈ ε            = here
  end∈ (ℓ ◅[ m ] p) = there (end∈ p)

  ----------------------------------------------------------------------
  -- The coherence case: the only simple path x → x is ε.

  simple-loop : ∀ {x} (p : Path L x x) → Simple p → p ≡ ε
  simple-loop ε            _        = refl
  simple-loop (ℓ ◅[ m ] p) (n ∷ _) = ⊥-elim (n (end∈ p))

  coh-forced : ∀ {x} → T (full (supp x)) → Forced x x ⟦ ε ⟧
  coh-forced {x} f = record
    { path = ε ; fullW = f ; simple = (λ ()) ∷ [] ; named = refl
    ; unique = λ p _ s → cong ⟦_⟧ (simple-loop p s) }

  ----------------------------------------------------------------------
  -- A path that is not simple contains a nonempty cycle.

  split : ∀ {x y z} (p : Path L x z) → y ∈L vertsP p →
          Σ (Path L x y) λ q → Σ (Path L y z) λ r → p ≡ q ++P r
  split ε            here      = ε , ε , refl
  split ε            (there ())
  split (ℓ ◅[ m ] p) here      = ε , (ℓ ◅[ m ] p) , refl
  split (ℓ ◅[ m ] p) (there k) with split p k
  ... | q , r , e = (ℓ ◅[ m ] q) , r , cong (ℓ ◅[ m ]_) e

  record Cycle {x z} (p : Path L x z) : Set where
    field
      {mid} : Cell
      pre   : Path L x mid
      cyc   : Path L mid mid
      post  : Path L mid z
      eq    : p ≡ pre ++P (cyc ++P post)
      pos   : 1 ≤ lenP L cyc

  cycle : ∀ {x z} (p : Path L x z) → ¬ Simple p → Cycle p
  cycle ε ns = ⊥-elim (ns ((λ ()) ∷ []))
  cycle {x} (ℓ ◅[ m ] p) ns with mem? x (vertsP p)
  ... | yes k with split p k
  ...   | q , r , e = record
          { pre = ε ; cyc = ℓ ◅[ m ] q ; post = r
          ; eq = cong (ℓ ◅[ m ]_) e ; pos = s≤s z≤n }
  cycle {x} (ℓ ◅[ m ] p) ns | no ¬k with cycle p (λ s → ns (¬k ∷ s))
  ... | c = record
          { pre = ℓ ◅[ m ] Cycle.pre c ; cyc = Cycle.cyc c ; post = Cycle.post c
          ; eq = cong (ℓ ◅[ m ]_) (Cycle.eq c) ; pos = Cycle.pos c }

  -- Cutting the cycle makes the path strictly shorter.
  private
    len-tail : ∀ {y w z} (c : Path L y w) (r : Path L w z) → lenP L r ≤ lenP L (c ++P r)
    len-tail ε            r = ≤-refl
    len-tail (ℓ ◅[ m ] c) r = ≤-step (len-tail c r)

    len-cut : ∀ {x y z} (q : Path L x y) (c : Path L y y) (r : Path L y z) →
              1 ≤ lenP L c → suc (lenP L (q ++P r)) ≤ lenP L (q ++P (c ++P r))
    len-cut ε            (ℓ ◅[ m ] c) r _   = s≤s (len-tail c r)
    len-cut (ℓ ◅[ m ] q) c            r pos = s≤s (len-cut q c r pos)

  ----------------------------------------------------------------------
  -- Shortest witnesses are simple, given that cutting a cycle out of a
  -- witness leaves a witness.

  CutFull : Set
  CutFull = ∀ {x y z} (q : Path L x y) (c : Path L y y) (r : Path L y z) →
            Full (q ++P (c ++P r)) → Full (q ++P r)

  Shortest : ∀ {x z} → Path L x z → Set
  Shortest {x} {z} p = ∀ (q : Path L x z) → Full q → lenP L p ≤ lenP L q

  shortest-simple : CutFull → ∀ {x z} (p : Path L x z) → Full p → Shortest p → Simple p
  shortest-simple cf p f sh with nodup? (vertsP p)
  ... | yes s = s
  ... | no ns with cycle p ns
  ...   | c = ⊥-elim (<-irrefl lt (sh _ f′))
    where
      open Cycle c
      f′ : Full (pre ++P post)
      f′ = cf pre cyc post (subst Full eq f)
      lt : suc (lenP L (pre ++P post)) ≤ lenP L p
      lt = subst (λ p′ → suc (lenP L (pre ++P post)) ≤ lenP L p′) (sym eq)
                 (len-cut pre cyc post pos)

  -- On a forced head, every designated choice of the old rule (a
  -- shortest witness, in whatever enumeration order) has the forced
  -- value.
  designated-agrees : CutFull → ∀ {x z c} → Forced x z c →
                      ∀ (p : Path L x z) → Full p → Shortest p → ⟦ p ⟧ ≡ c
  designated-agrees cf F p f sh = unique F p f (shortest-simple cf p f sh)

  -- Every witness can be shortened to a simple witness (loop removal),
  -- so a head satisfies SC iff it has a simple witness.
  simple-witness : CutFull → ∀ {x z} (p : Path L x z) → Full p →
                   Σ (Path L x z) λ q → Full q × Simple q
  simple-witness cf p f = go (lenP L p) p ≤-refl f
    where
      go : ∀ n {x z} (p : Path L x z) → lenP L p ≤ n → Full p →
           Σ (Path L x z) λ q → Full q × Simple q
      go n p le f with nodup? (vertsP p)
      ... | yes s = p , f , s
      go zero    p le f | no ns with cycle p ns
      ... | c with ≤-trans (subst (λ p′ → suc (lenP L (Cycle.pre c ++P Cycle.post c)) ≤ lenP L p′)
                                  (sym (Cycle.eq c))
                                  (len-cut (Cycle.pre c) (Cycle.cyc c) (Cycle.post c) (Cycle.pos c)))
                           le
      ...   | ()
      go (suc n) p le f | no ns with cycle p ns
      ... | c = go n (Cycle.pre c ++P Cycle.post c) le′
                 (cf (Cycle.pre c) (Cycle.cyc c) (Cycle.post c) (subst Full (Cycle.eq c) f))
        where
          le′ : lenP L (Cycle.pre c ++P Cycle.post c) ≤ n
          le′ with ≤-trans (subst (λ p′ → suc (lenP L (Cycle.pre c ++P Cycle.post c)) ≤ lenP L p′)
                                  (sym (Cycle.eq c))
                                  (len-cut (Cycle.pre c) (Cycle.cyc c) (Cycle.post c) (Cycle.pos c)))
                           le
          ... | s≤s q = q

  ----------------------------------------------------------------------
  -- Deciding whether a head is forced, over a finite closed universe.

  module DecideForced (UC : List Cell)
                (closedC : ∀ {y ℓ} → y ∈L UC → ℓ ∈L out y → tgt ℓ ∈L UC)
                where

    verts-in : ∀ {x z} → x ∈L UC → (p : Path L x z) → ∀ {w} → w ∈L vertsP p → w ∈L UC
    verts-in xU ε            here       = xU
    verts-in xU ε            (there ())
    verts-in xU (ℓ ◅[ m ] p) here       = xU
    verts-in xU (ℓ ◅[ m ] p) (there k) = verts-in (closedC xU m) p k

    len-verts : ∀ {x z} (p : Path L x z) → lengthL (vertsP p) ≡ suc (lenP L p)
    len-verts ε            = refl
    len-verts (ℓ ◅[ m ] p) = cong suc (len-verts p)

    pred≤ : ∀ {a n} → suc a ≤ n → a ≤ n
    pred≤ (s≤s p) = ≤-step p

    simple-short : ∀ {x z} → x ∈L UC → (p : Path L x z) → Simple p → lenP L p ≤ lengthL UC
    simple-short xU p s =
      pred≤ (subst (_≤ lengthL UC) (len-verts p) (pigeon s (verts-in xU p)))

    -- Candidates: simple witnesses ending at z, among all paths of
    -- length at most |UC| out of x.
    pick : ∀ {x} z → List (Σ Cell (Path L x)) → List (Path L x z)
    pick z [] = []
    pick z ((z′ , p) ∷ ps) with z′ ≟ z
    ... | no _ = pick z ps
    ... | yes refl with T? (full (suppP L p)) | nodup? (vertsP p)
    ...   | yes _ | yes _ = p ∷ pick z ps
    ...   | _     | _     = pick z ps

    pick-ok : ∀ {x} z (ps : List (Σ Cell (Path L x))) {p} → p ∈L pick z ps → Full p × Simple p
    pick-ok z [] ()
    pick-ok z ((z′ , p) ∷ ps) m with z′ ≟ z
    ... | no _ = pick-ok z ps m
    ... | yes refl with T? (full (suppP L p)) | nodup? (vertsP p)
    ...   | yes f | yes s with m
    ...     | here     = f , s
    ...     | there m′ = pick-ok z ps m′
    pick-ok z ((z′ , p) ∷ ps) m | yes refl | yes _ | no _ = pick-ok z ps m
    pick-ok z ((z′ , p) ∷ ps) m | yes refl | no _  | _    = pick-ok z ps m

    pick-has : ∀ {x} z (ps : List (Σ Cell (Path L x))) (p : Path L x z) →
               (z , p) ∈L ps → Full p → Simple p → p ∈L pick z ps
    pick-has z ((z′ , q) ∷ ps) p here f s with z′ ≟ z
    ... | no ne = ⊥-elim (ne refl)
    ... | yes refl with T? (full (suppP L q)) | nodup? (vertsP q)
    ...   | yes _ | yes _ = here
    ...   | no ¬f | _     = ⊥-elim (¬f f)
    ...   | yes _ | no ¬s = ⊥-elim (¬s s)
    pick-has z ((z′ , q) ∷ ps) p (there k) f s with z′ ≟ z
    ... | no _ = pick-has z ps p k f s
    ... | yes refl with T? (full (suppP L q)) | nodup? (vertsP q)
    ...   | yes _ | yes _ = there (pick-has z ps p k f s)
    ...   | no _  | _     = pick-has z ps p k f s
    ...   | yes _ | no _  = pick-has z ps p k f s

    cands : ∀ {x} z → List (Path L x z)
    cands {x} z = pick z (paths L (lengthL UC) x)

    cands-has : ∀ {x z} → x ∈L UC → (p : Path L x z) → Full p → Simple p → p ∈L cands z
    cands-has {x} {z} xU p f s =
      pick-has z (paths L (lengthL UC) x) p (paths-complete L (lengthL UC) p (simple-short xU p s)) f s

    private
      allEq? : ∀ {x z} (c : Up x z) (ps : List (Path L x z)) →
               Dec (∀ {p} → p ∈L ps → ⟦ p ⟧ ≡ c)
      allEq? c [] = yes λ ()
      allEq? c (p ∷ ps) with ⟦ p ⟧ ≟U c | allEq? c ps
      ... | no ne  | _      = no λ h → ne (h here)
      ... | yes e  | no ¬h  = no λ h → ¬h (λ m → h (there m))
      ... | yes e  | yes h  = yes λ { here → e ; (there m) → h m }

    -- Whether the head x → z is forced, and if so its value.
    forced? : ∀ {x} → x ∈L UC → ∀ z → Dec (Σ (Up x z) (Forced x z))
    forced? {x} xU z with cands {x} z | (λ {p} → pick-ok z (paths L (lengthL UC) x) {p})
                        | cands-has {x} {z} xU
    ... | [] | _ | has = no λ { (c , F) → absurd (has (path F) (fullW F) (simple F)) }
      where absurd : ∀ {A : Set} {p : Path L x z} → p ∈L [] → A
            absurd ()
    ... | p₀ ∷ ps | ok | has with allEq? ⟦ p₀ ⟧ ps
    ...   | yes h = yes (⟦ p₀ ⟧ , record
              { path = p₀ ; fullW = fst (ok here) ; simple = snd (ok here) ; named = refl
              ; unique = λ p f s → all-eq (has p f s) })
      where all-eq : ∀ {p} → p ∈L p₀ ∷ ps → ⟦ p ⟧ ≡ ⟦ p₀ ⟧
            all-eq here      = refl
            all-eq (there m) = h m
    ...   | no ¬h = no λ { (c , F) → ¬h λ {p} m →
              let okp = ok (there m) in
              trans (unique F p (fst okp) (snd okp))
                    (sym (unique F p₀ (fst (ok here)) (snd (ok here)))) }

------------------------------------------------------------------------
-- Example 1: the strip in setting ∅.  Two routes s → t: the direct
-- crossing u, and a then b (the paste of the two elementary crossings).

module Strip where
  data V : Set where s m t : V
  data Lt : Set where u a b : Lt

  _≟V_ : (x y : V) → Dec (x ≡ y)
  s ≟V s = yes refl
  m ≟V m = yes refl
  t ≟V t = yes refl
  s ≟V m = no λ ()
  s ≟V t = no λ ()
  m ≟V s = no λ ()
  m ≟V t = no λ ()
  t ≟V s = no λ ()
  t ≟V m = no λ ()

  out : V → List Lt
  out s = u ∷ a ∷ []
  out m = b ∷ []
  out t = []

  tgt : Lt → V
  tgt u = t
  tgt a = m
  tgt b = t

  L : Layer
  L = record { Cell = V ; _≟_ = _≟V_ ; Letter = Lt ; out = out ; tgt = tgt
             ; Supp = ⊤ ; supp = λ _ → tt ; suppL = λ _ → tt ; _∪_ = λ _ _ → tt
             ; full = λ _ → true }

  -- Setting ∅: the value of a path is its word of letters (no equation
  -- identifies the two routes).
  word : ∀ {x z} → Path L x z → List Lt
  word ε            = []
  word (ℓ ◅[ _ ] p) = ℓ ∷ word p

  _≟Lt_ : (x y : Lt) → Dec (x ≡ y)
  u ≟Lt u = yes refl
  a ≟Lt a = yes refl
  b ≟Lt b = yes refl
  u ≟Lt a = no λ ()
  u ≟Lt b = no λ ()
  a ≟Lt u = no λ ()
  a ≟Lt b = no λ ()
  b ≟Lt u = no λ ()
  b ≟Lt a = no λ ()

  _≟W_ : (x y : List Lt) → Dec (x ≡ y)
  [] ≟W [] = yes refl
  [] ≟W (_ ∷ _) = no λ ()
  (_ ∷ _) ≟W [] = no λ ()
  (x ∷ xs) ≟W (y ∷ ys) with x ≟Lt y | xs ≟W ys
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }

  C : Cells L
  C = record { Up = λ _ _ → List Lt ; ⟦_⟧ = word ; _≟U_ = _≟W_ }

  open Forced L C

  pu : Path L s t
  pu = u ◅[ here ] ε

  pv : Path L s t
  pv = a ◅[ there here ] (b ◅[ here ] ε)

  pu-simple : Simple pu
  pu-simple = (λ { (there ()) }) ∷ ((λ ()) ∷ [])

  pv-simple : Simple pv
  pv-simple = (λ { (there (there ())) }) ∷ ((λ { (there ()) }) ∷ ((λ ()) ∷ []))

  -- The two routes are both witnesses, and differ.
  routes-differ : ¬ (word pu ≡ word pv)
  routes-differ ()

  -- The old rule accepts the head and its designated lift is u.
  sc-holds : SC L s t
  sc-holds = pu , tt

  pu-shortest : Shortest pu
  pu-shortest (ℓ ◅[ k ] q) _ = s≤s z≤n

  -- The repaired rule rejects it: no value is forced.
  strip-not-forced : ∀ c → ¬ Forced s t c
  strip-not-forced c F =
    routes-differ (trans (unique F pu tt pu-simple) (sym (unique F pv tt pv-simple)))

  -- The decision procedure computes this.
  UC : List V
  UC = s ∷ m ∷ t ∷ []

  closedC : ∀ {y ℓ} → y ∈L UC → ℓ ∈L out y → tgt ℓ ∈L UC
  closedC {ℓ = u} _ _ = there (there here)
  closedC {ℓ = a} _ _ = there here
  closedC {ℓ = b} _ _ = there (there here)

  open DecideForced UC closedC

  computed : isYes (forced? here t) ≡ false
  computed = refl

------------------------------------------------------------------------
-- Example 2: the same strip with the inner law switched on: the two
-- routes have the same value, and the head is forced.

module StripInner where
  open Strip using (V; s; t; L; Lt; UC; closedC)

  C : Cells L
  C = record { Up = λ _ _ → ⊤ ; ⟦_⟧ = λ _ → tt ; _≟U_ = λ { tt tt → yes refl } }

  open Forced L C
  open DecideForced UC closedC

  computed : isYes (forced? here t) ≡ true
  computed = refl

------------------------------------------------------------------------
-- Example 3: a loop H at w with pairwise distinct powers (the value of
-- a path is its length).  Every power is a witness of w → w; the head
-- is forced at the identity.

module Loop where
  data W : Set where w : W
  data Hl : Set where H : Hl

  L : Layer
  L = record { Cell = W ; _≟_ = λ { w w → yes refl } ; Letter = Hl
             ; out = λ _ → H ∷ [] ; tgt = λ _ → w
             ; Supp = ⊤ ; supp = λ _ → tt ; suppL = λ _ → tt ; _∪_ = λ _ _ → tt
             ; full = λ _ → true }

  _≟N_ : (m n : Nat) → Dec (m ≡ n)
  zero  ≟N zero  = yes refl
  zero  ≟N suc n = no λ ()
  suc m ≟N zero  = no λ ()
  suc m ≟N suc n with m ≟N n
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }

  C : Cells L
  C = record { Up = λ _ _ → Nat ; ⟦_⟧ = lenP L ; _≟U_ = _≟N_ }

  open Forced L C

  Hpow : Nat → Path L w w
  Hpow zero    = ε
  Hpow (suc n) = H ◅[ here ] Hpow n

  powers-distinct : ∀ m n → lenP L (Hpow m) ≡ lenP L (Hpow n) → m ≡ n
  powers-distinct zero    zero    _ = refl
  powers-distinct zero    (suc n) ()
  powers-distinct (suc m) zero    ()
  powers-distinct (suc m) (suc n) e = cong suc (powers-distinct m n (suc-inj e))
    where suc-inj : ∀ {i j} → suc i ≡ suc j → i ≡ j
          suc-inj refl = refl

  every-power-witnesses : ∀ n → SC L w w
  every-power-witnesses n = Hpow n , tt

  identity-forced : Forced w w 0
  identity-forced = coh-forced tt

------------------------------------------------------------------------
-- Option (E) of notes/design-decisions.md §5.8: forced heads, plus
-- native letter heads.  `Native` marks the letters that are generic
-- letters of V on their own arity (generator operands, no whiskers).
-- A letter head is a one-letter witness by a native letter between
-- distinct endpoints, such that every native one-letter witness has the
-- same value.  (E) accepts a head iff it is forced or a letter head.
--
-- Proved: E-unique (the value is unique, also when both kinds apply),
-- D⊆E, E-sc (E accepts no head the old rule rejects), and E-shortest
-- (a letter head's one-letter path is a shortest witness; so on a single
-- head (E) agrees with (B1) wherever (B1)'s pick is unique).

module LetterHeads (L : Layer) (C : Cells L) (Native : Layer.Letter L → Set) where
  open Layer L
  open Cells C
  open Forced L C

  one : ∀ {x z} (ℓ : Letter) → ℓ ∈L out x → tgt ℓ ≡ z → Path L x z
  one ℓ m refl = ℓ ◅[ m ] ε

  record LetterHead (x z : Cell) (c : Up x z) : Set where
    field
      letter : Letter
      mem    : letter ∈L out x
      hits   : tgt letter ≡ z
      native : Native letter
      apart  : ¬ (x ≡ z)
      fullL  : Full (one letter mem hits)
      namedL : ⟦ one letter mem hits ⟧ ≡ c
      only   : ∀ ℓ (m : ℓ ∈L out x) (e : tgt ℓ ≡ z) → Native ℓ →
               Full (one ℓ m e) → ⟦ one ℓ m e ⟧ ≡ c
  open LetterHead public

  AcceptE : (x z : Cell) → Up x z → Set
  AcceptE x z c = Forced x z c ⊎ LetterHead x z c

  D⊆E : ∀ {x z c} → Forced x z c → AcceptE x z c
  D⊆E = inj₁

  one-simple : ∀ {x z} (ℓ : Letter) (m : ℓ ∈L out x) (e : tgt ℓ ≡ z) → ¬ (x ≡ z) →
               Simple (one ℓ m e)
  one-simple ℓ m refl ne = (λ { here → ne refl ; (there ()) }) ∷ ((λ ()) ∷ [])

  E-unique : ∀ {x z c c′} → AcceptE x z c → AcceptE x z c′ → c ≡ c′
  E-unique (inj₁ F) (inj₁ F′) = forced-unique F F′
  E-unique (inj₁ F) (inj₂ H)  =
    trans (sym (unique F _ (fullL H) (one-simple (letter H) (mem H) (hits H) (apart H))))
          (namedL H)
  E-unique (inj₂ H) (inj₁ F)  =
    trans (sym (namedL H))
          (unique F _ (fullL H) (one-simple (letter H) (mem H) (hits H) (apart H)))
  E-unique (inj₂ H) (inj₂ H′) =
    trans (sym (namedL H)) (only H′ (letter H) (mem H) (hits H) (native H) (fullL H))

  E-sc : ∀ {x z c} → AcceptE x z c → SC L x z
  E-sc (inj₁ F) = forced-sc F
  E-sc (inj₂ H) = one (letter H) (mem H) (hits H) , fullL H

  private
    len-one : ∀ {x z} (ℓ : Letter) (m : ℓ ∈L out x) (e : tgt ℓ ≡ z) → lenP L (one ℓ m e) ≡ 1
    len-one ℓ m refl = refl

  E-shortest : ∀ {x z c} (H : LetterHead x z c) → Shortest (one (letter H) (mem H) (hits H))
  E-shortest H q _ = subst (_≤ lenP L q) (sym (len-one (letter H) (mem H) (hits H))) (pos q)
    where
      pos : ∀ (q : Path L _ _) → 1 ≤ lenP L q
      pos ε            = ⊥-elim (apart H refl)
      pos (ℓ ◅[ k ] p) = s≤s z≤n

------------------------------------------------------------------------
-- Example 4: the raising bridge B = b₄¹ on ΣD⁴ ∨ ΣD⁴
-- (conjectures/answered/forced-lift-generation-2026-11-25.md, verified).
-- Vertices: s = D⁰⁰Y_v⁰X_v¹, m = D⁰⁰X_v⁰Y_v¹, t = X_u⁰D¹⁰Y_v¹.  Letters:
-- the bridge B : s → t (path (1)), the exchange ex : s → m and the
-- smaller bridge whiskered by Y_v¹, bY : m → t (path (2)).  The value of
-- a path is its number of B occurrences, which is well defined in V by
-- rigid factorization (r10 Response 2, cited, not re-proved; here it is
-- the definition of the toy's values).  Supports are trivial.  Only B is
-- native: ex and bY are whiskered instances.

module Bridge where
  open Strip using (V; s; m; t; _≟V_)

  data Lb : Set where Bl ex bY : Lb

  out : V → List Lb
  out s = Bl ∷ ex ∷ []
  out m = bY ∷ []
  out t = []

  tgt : Lb → V
  tgt Bl = t
  tgt ex = m
  tgt bY = t

  L : Layer
  L = record { Cell = V ; _≟_ = _≟V_ ; Letter = Lb ; out = out ; tgt = tgt
             ; Supp = ⊤ ; supp = λ _ → tt ; suppL = λ _ → tt ; _∪_ = λ _ _ → tt
             ; full = λ _ → true }

  isB : Lb → Nat
  isB Bl = 1
  isB ex = 0
  isB bY = 0

  count : ∀ {x z} → Path L x z → Nat
  count ε            = 0
  count (ℓ ◅[ _ ] p) = isB ℓ + count p

  C : Cells L
  C = record { Up = λ _ _ → Nat ; ⟦_⟧ = count ; _≟U_ = Loop._≟N_ }

  data Native : Lb → Set where
    bridge : Native Bl

  open Forced L C
  open LetterHeads L C Native

  p1 : Path L s t
  p1 = Bl ◅[ here ] ε

  p2 : Path L s t
  p2 = ex ◅[ there here ] (bY ◅[ here ] ε)

  p1-simple : Simple p1
  p1-simple = (λ { (there ()) }) ∷ ((λ ()) ∷ [])

  p2-simple : Simple p2
  p2-simple = (λ { (there (there ())) }) ∷ ((λ { (there ()) }) ∷ ((λ ()) ∷ []))

  counts-differ : ¬ (count p1 ≡ count p2)
  counts-differ ()

  -- (D) rejects the bridge's head.
  bridge-not-forced : ∀ c → ¬ Forced s t c
  bridge-not-forced c F =
    counts-differ (trans (unique F p1 tt p1-simple) (sym (unique F p2 tt p2-simple)))

  -- The old rule's designated lift is B (one letter against two).
  p1-shortest : Shortest p1
  p1-shortest (ℓ ◅[ k ] q) _ = s≤s z≤n

  -- (E) accepts it as a letter head, with value B (count 1).
  bridge-letter-head : AcceptE s t 1
  bridge-letter-head = inj₂ record
    { letter = Bl ; mem = here ; hits = refl ; native = bridge
    ; apart = λ () ; fullL = tt ; namedL = refl
    ; only = λ { Bl here refl bridge _ → refl ; Bl (there (there ())) _ _ _ } }

  UC : List V
  UC = s ∷ m ∷ t ∷ []

  closedC : ∀ {y ℓ} → y ∈L UC → ℓ ∈L out y → tgt ℓ ∈L UC
  closedC {ℓ = Bl} _ _ = there (there here)
  closedC {ℓ = ex} _ _ = there here
  closedC {ℓ = bY} _ _ = there (there here)

  open DecideForced UC closedC

  computed : isYes (forced? here t) ≡ false
  computed = refl

-- The strip under (E): u has a composite operand, so it is not native,
-- and (E), like (D), rejects the strip head.
module StripE where
  open Strip using (V; s; t; L; Lt; C; pu; pv; pu-simple; pv-simple; routes-differ)
  open Forced L C

  data NoNative : Lt → Set where

  open LetterHeads L C NoNative

  strip-rejected : ∀ c → ¬ AcceptE s t c
  strip-rejected c (inj₁ F) =
    routes-differ (trans (unique F pu tt pu-simple) (sym (unique F pv tt pv-simple)))
  strip-rejected c (inj₂ H) with native H
  ... | ()
