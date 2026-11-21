------------------------------------------------------------------------
-- Degree-five letters on suspended grids: the grid as a Layer
-- (ledger S3b; spec/02-lax-core.md §2.3 example (b)).
--
-- CaTTExp.Uniform.Grid gives the 4-cells of F_{V+S} on the suspended
-- m × n grid Σ(Σ[m] ∨ Σ[n]) in every setting S: classes of raw paths
-- of block crossings under the enabled split laws. This module adds the
-- letters one dimension up, so that the 4-cells form a `Layer` and the
-- side condition SC between 4-cells (a 5-cell of full support) is
-- decided, not only equality.
--
-- The degree-five alphabet. On these diagrams the only proper 5-letter
-- is the positional square I₂(A, B) of two positive 4-cells on
-- consecutive 3-intervals (4-cells composable along global cut 2). Its
-- faces are (u₀ B)(A v₁) ⇛ (A v₀)(u₁ B): the later interval's cell
-- first, then the earlier one, to the earlier first. Source:
-- r10 (lax-interchange-every-dimension-r10) Response 1, "Decorations
-- by cuts" (line ~490): a positive 4-cell uses both short spans, so no
-- cut-1 variation or join has an active partner; outer (cut-0)
-- operations need a second outer span, which a suspension lacks; the
-- diagram has no 5-globe; cut-3 squares need 5-cell inputs. r9
-- Response 2 ("5- and 6-cells") gives the same list on Σ[2] ∨ Σ[n],
-- and r10 Response 3 says the switch equations add no letter above
-- degree four, only identifications inside lower labels. This is the
-- paper argument; deriving the alphabet from raw T₁₂ syntax is S3a/S3c.
--
-- Model. A raw letter swaps two adjacent edges e′ ; e of a raw path
-- into e ; e′, where e's window lies wholly left of e′'s (`Sq`). Since
-- 4-cells are classes, a letter out of a 4-cell x applies to any raw
-- representative of x, and lands in the class of the result. A square
-- with composite operands A, B has the same endpoints as the paste of
-- the atomic squares that move A's edges one by one before B's, so for
-- existence of 5-cells (all that SC reads) atomic squares suffice.
-- This is argued, not checked here.
--
-- Supports (ledger S1, S3d as settled by the S1 review): SC reads the
-- support of the Gray image π(c). π kills every interchanger along a
-- k-cell with k ≥ 1, so every 4-cell and 5-letter here maps to an
-- identity on the composite of all the a- and b-cells, whose support in
-- 𝔉(Γ) = ν(λ(Σ[m] ∨ Σ[n])) suspended is every generator. So every
-- support in this layer is full: Supp is Bool and every support is
-- `true`. On these diagrams SC between 4-cells is exactly 5-reachability.
--
-- Proved here, for every m, n and every setting:
--   squares, squares-sound, squares-complete   the raw letters;
--   _⇛_, reach5?    5-reachability of 4-cells (closure of equality and
--                   squares), decided by breadth-first search on the
--                   finite universe of raw paths of one charge;
--   layer           the Layer of 4-cells in normal form;
--   path→⇛, ⇛→path  paths of letters in `layer` are exactly
--                   5-reachability;
--   sc?             SC on this layer is decidable, by RuleFin.DecideFin
--                   (no length bound; loops occur, GridFiveExamples).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; _≤_; z≤n; s≤s; lengthL)
open import CaTTExp.Join.SwitchLaws using (Switches)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Arith
open import CaTTExp.Uniform.Grid
open import CaTTExp.Uniform.Rule
import CaTTExp.Uniform.FiniteGraph as FG
import CaTTExp.Uniform.RuleFin as RF

module CaTTExp.Uniform.GridFive where

------------------------------------------------------------------------
-- Raw letters: the positional square on two edges with disjoint
-- windows.

-- The end (exclusive) of an edge's window.
wend : Edge → Nat
wend ⟨ i , p , q ⟩ = i + suc p + suc q

-- e lies wholly left of e′.
leftOf : Edge → Edge → Bool
leftOf e e′ = wend e <ℕ suc (Edge.pos e′)

-- Sq p q: q is p with e′ ; e replaced by e ; e′, e left of e′
-- (right cell first ⇛ left cell first).
data Sq : RawPath → RawPath → Set where
  sq : ∀ pre e e′ post → T (leftOf e e′) → Sq (pre ++ e′ ∷ e ∷ post) (pre ++ e ∷ e′ ∷ post)

private
  one? : ∀ {A : Set} → Bool → A → List A
  one? true  x = x ∷ []
  one? false x = []

  one?-has : ∀ {A : Set} b (x : A) → T b → x ∈L one? b x
  one?-has true x _ = here

  one?-elim : ∀ {A : Set} b (x : A) {y} → y ∈L one? b x → T b × (y ≡ x)
  one?-elim true x here = tt , refl

  sqAt : List Edge × Edge × Edge × List Edge → List RawPath
  sqAt (pre , e′ , e , post) = one? (leftOf e e′) (pre ++ e ∷ e′ ∷ post)

squares : RawPath → List RawPath
squares p = concatK (mapK sqAt (decomps2 p))

squares-complete : ∀ {p q} → Sq p q → q ∈L squares p
squares-complete (sq pre e e′ post t) =
  ∈-concat⁺ _ (one?-has (leftOf e e′) _ t) (∈-map⁺ sqAt (decomps2-has pre e′ e post))

squares-sound : ∀ p {q} → q ∈L squares p → Sq p q
squares-sound p mq with ∈-concat⁻ (mapK sqAt (decomps2 p)) mq
... | qs , mq′ , mqs with ∈-map⁻ sqAt (decomps2 p) mqs
...   | (pre , e′ , e , post) , md , refl with one?-elim (leftOf e e′) _ mq′
...     | t , refl rewrite decomps2-sound p md = sq pre e e′ post t

-- Squares permute edges, so they keep the charge.
sq-charge : ∀ {p q} → Sq p q → charge q ≡ charge p
sq-charge (sq pre e e′ post _) =
  trans (charge-++ pre (e ∷ e′ ∷ post))
    (trans (cong (charge pre +_) (swap2 (chg e) (chg e′) (charge post)))
           (sym (charge-++ pre (e′ ∷ e ∷ post))))
  where
  swap2 : ∀ a b c → a + (b + c) ≡ b + (a + c)
  swap2 a b c = trans (sym (+-assoc a b c))
                  (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

------------------------------------------------------------------------
-- The layer on one grid, in one setting.

module Five (m n : Nat) (sw : Switches) where
  open OnGrid m n
  module S = Setting sw

  ----------------------------------------------------------------------
  -- 5-reachability of 4-cells: generated by equality in the setting and
  -- typed squares.

  infix 3 _⇛_
  data _⇛_ : RawPath → RawPath → Set where
    ⇛-≈     : ∀ {p q} → sw ⊢ p ≈ q → p ⇛ q
    ⇛-sq    : ∀ {p q} → Valid p → Valid q → Sq p q → p ⇛ q
    ⇛-trans : ∀ {p q r} → p ⇛ q → q ⇛ r → p ⇛ r

  -- The step function: switch neighbours and typed squares.
  sqs : RawPath → List RawPath
  sqs p with valid? p
  ... | yes _ = filter validB (squares p)
  ... | no _  = []

  sqs-sound : ∀ p {q} → q ∈L sqs p → Valid p × Valid q × Sq p q
  sqs-sound p {q} mq with valid? p
  ... | yes vp with ∈-filter⁻ validB (squares p) mq
  ...   | m′ , t = vp , isYes-sound (valid? q) t , squares-sound p m′

  sqs-complete : ∀ {p q} → Valid p → Valid q → Sq p q → q ∈L sqs p
  sqs-complete {p} {q} vp vq s with valid? p
  ... | yes _ = ∈-filter⁺ validB (squares p) (squares-complete s) (isYes-complete (valid? q) vq)
  ... | no ¬v = ⊥-elim (¬v vp)

  next5 : RawPath → List RawPath
  next5 p = nb sw p ++ sqs p

  open FG _≟P_ next5 using (Star; ε; _◅_; _◅◅_; reachSet; reachSet-sound; mem?)
  module Sat5 = FG.Saturate _≟P_ next5

  star→⇛ : ∀ {p q} → Star p q → p ⇛ q
  star→⇛ ε = ⇛-≈ ≈-refl
  star→⇛ {p} (m′ ◅ s) with ∈-++⁻ (nb sw p) m′
  ... | inj₁ mn = ⇛-trans (⇛-≈ (S.star→≈ (mn S.◅ S.ε))) (star→⇛ s)
  ... | inj₂ ms with sqs-sound p ms
  ...   | vp , vq , st = ⇛-trans (⇛-sq vp vq st) (star→⇛ s)

  starNb→star : ∀ {p q} → S.Star p q → Star p q
  starNb→star S.ε = ε
  starNb→star {p} (mn S.◅ s) = ∈-++ˡ (sqs p) mn ◅ starNb→star s

  ⇛→star : ∀ {p q} → p ⇛ q → Star p q
  ⇛→star (⇛-≈ e)          = starNb→star (S.≈→star e)
  ⇛→star {p} (⇛-sq vp vq s) = ∈-++ʳ (nb sw p) (sqs-complete vp vq s) ◅ ε
  ⇛→star (⇛-trans a b)    = ⇛→star a ◅◅ ⇛→star b

  -- The universe of a class: valid raw paths of its charge.
  U5-closed : ∀ {p q r} → q ∈L U p → r ∈L next5 q → r ∈L U p
  U5-closed {p} {q} {r} mq mr with ∈-++⁻ (nb sw q) mr
  ... | inj₁ mn = S.U-closed {p} {q} {r} mq mn
  ... | inj₂ ms with sqs-sound q ms | ∈-filter⁻ (λ q → isYes (charge q ≟N charge p)) (allPaths (charge p) start end) mq
  ...   | _ , vr , st | _ , t =
    ∈-filter⁺ (λ q → isYes (charge q ≟N charge p)) _
      (allPaths-has (charge p) start end r vr (subst (lengthL r ≤_) cr (length≤charge r)))
      (isYes-complete (charge r ≟N charge p) cr)
    where
    cr : charge r ≡ charge p
    cr = trans (sq-charge st) (isYes-sound (charge q ≟N charge p) t)

  reach5 : RawPath → RawPath → Bool
  reach5 p q = isYes (mem? q (reachSet (lengthL (U p)) p))

  reach5-sound : ∀ p q → T (reach5 p q) → p ⇛ q
  reach5-sound p q t = star→⇛ (reachSet-sound (lengthL (U p)) p (isYes-sound (mem? q _) t))

  reach5-complete : ∀ {p q} → Valid p → p ⇛ q → T (reach5 p q)
  reach5-complete {p} {q} vp r =
    isYes-complete (mem? q _)
      (Sat5.reachSet-complete (U p) (λ {x} {y} → U5-closed {p} {x} {y}) (U-has vp) (⇛→star r))

  reach5? : ∀ {p} → Valid p → ∀ q → Dec (p ⇛ q)
  reach5? {p} vp q with T? (reach5 p q)
  ... | yes t = yes (reach5-sound p q t)
  ... | no ¬t = no λ r → ¬t (reach5-complete vp r)

  ----------------------------------------------------------------------
  -- Cells: valid raw paths in normal form.

  isNF : RawPath → Bool
  isNF p = validB p ∧ isYes (nf sw p ≟P p)

  Cell : Set
  Cell = Σ RawPath λ p → T (isNF p)

  private
    T-irr : ∀ {b} (s t : T b) → s ≡ t
    T-irr {true} tt tt = refl

  cell-≡ : ∀ {c d : Cell} → fst c ≡ fst d → c ≡ d
  cell-≡ {p , s} {.p , t} refl = cong (p ,_) (T-irr s t)

  _≟C_ : (c d : Cell) → Dec (c ≡ d)
  c ≟C d with fst c ≟P fst d
  ... | yes e = yes (cell-≡ e)
  ... | no ne = no λ e → ne (cong fst e)

  private
    ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
    ∧-intro {true} _ t = t

  nf-valid : ∀ {p} → Valid p → Valid (nf sw p)
  nf-valid {p} vp = snd (≈-valid (nf-≈ sw p)) vp

  nf-idem : ∀ {p} → Valid p → nf sw (nf sw p) ≡ nf sw p
  nf-idem {p} vp = nf-cong sw (nf-valid vp) (nf-≈ sw p)

  cellOf : (p : RawPath) → Valid p → Cell
  cellOf p vp = nf sw p , ∧-intro (isYes-complete (valid? (nf sw p)) (nf-valid vp))
                                  (isYes-complete (nf sw (nf sw p) ≟P nf sw p) (nf-idem vp))

  cell-valid : (c : Cell) → Valid (fst c)
  cell-valid (p , t) = isYes-sound (valid? p) (∧-fst {validB p} t)

  cell-nf : (c : Cell) → nf sw (fst c) ≡ fst c
  cell-nf (p , t) = isYes-sound (nf sw p ≟P p) (∧-snd {validB p} t)

  cellOf-self : (c : Cell) → cellOf (fst c) (cell-valid c) ≡ c
  cellOf-self c = cell-≡ (cell-nf c)

  mkCell : RawPath → List Cell
  mkCell q with valid? q
  ... | yes vq = cellOf q vq ∷ []
  ... | no _   = []

  mkCell-has : ∀ {q} (vq : Valid q) → cellOf q vq ∈L mkCell q
  mkCell-has {q} vq with valid? q
  ... | yes vq′ = subst (_∈L (cellOf q vq′ ∷ [])) (cell-≡ refl) here
  ... | no ¬v   = ⊥-elim (¬v vq)

  mkCell-elim : ∀ q {c} → c ∈L mkCell q → Σ (Valid q) λ vq → c ≡ cellOf q vq
  mkCell-elim q m with valid? q
  mkCell-elim q here | yes vq = vq , refl

  ----------------------------------------------------------------------
  -- The letters out of a 4-cell: every square on every representative
  -- of its class, landing in the class of the result. A letter is
  -- recorded by its target cell.

  members : RawPath → List RawPath
  members p = filter (S.conn p) (U p)

  out : Cell → List Cell
  out c = concatK (mapK (λ r → concatK (mapK mkCell (squares r))) (members (fst c)))

  private
    -- Inversion of membership in `out`, one layer at a time (helper
    -- functions rather than `with`, to keep the goals small).
    out-inv : ∀ (rs : List RawPath) {d} →
              d ∈L concatK (mapK (λ r → concatK (mapK mkCell (squares r))) rs) →
              Σ RawPath λ r → Σ RawPath λ q → (r ∈L rs) × (q ∈L squares r) × (d ∈L mkCell q)
    out-inv rs md = go (∈-concat⁻ (mapK (λ r → concatK (mapK mkCell (squares r))) rs) md)
      where
      go₂ : ∀ {d} r → Σ (List Cell) (λ cs → (d ∈L cs) × (cs ∈L mapK mkCell (squares r))) →
            Σ RawPath λ q → (q ∈L squares r) × (d ∈L mkCell q)
      go₂ r (cs , mc , mcs) = go₃ (∈-map⁻ mkCell (squares r) mcs) mc
        where
        go₃ : ∀ {d} → Σ RawPath (λ q → (q ∈L squares r) × (mkCell q ≡ cs)) → d ∈L cs →
              Σ RawPath λ q → (q ∈L squares r) × (d ∈L mkCell q)
        go₃ (q , mq , refl) mc = q , mq , mc
      go : ∀ {d} → Σ (List Cell) (λ ds → (d ∈L ds) × (ds ∈L mapK (λ r → concatK (mapK mkCell (squares r))) rs)) →
           Σ RawPath λ r → Σ RawPath λ q → (r ∈L rs) × (q ∈L squares r) × (d ∈L mkCell q)
      go (ds , md′ , mds) = go₁ (∈-map⁻ (λ r → concatK (mapK mkCell (squares r))) rs mds) md′
        where
        go₁ : ∀ {d} → Σ RawPath (λ r → (r ∈L rs) × (concatK (mapK mkCell (squares r)) ≡ ds)) → d ∈L ds →
              Σ RawPath λ r → Σ RawPath λ q → (r ∈L rs) × (q ∈L squares r) × (d ∈L mkCell q)
        go₁ (r , mr , refl) md′ with go₂ r (∈-concat⁻ (mapK mkCell (squares r)) md′)
        ... | q , mq , mc = r , q , mr , mq , mc

    out-sound′ : ∀ c {d} r q → r ∈L members (fst c) → q ∈L squares r → d ∈L mkCell q → fst c ⇛ fst d
    out-sound′ c {d} r q mr mq mc = fin (mkCell-elim q mc) (snd (∈-filter⁻ (S.conn (fst c)) (U (fst c)) mr))
      where
      fin : (Σ (Valid q) λ vq → d ≡ cellOf q vq) → T (S.conn (fst c) r) → fst c ⇛ fst d
      fin (vq , refl) t =
        ⇛-trans (⇛-≈ (S.conn-sound (fst c) r t))
          (⇛-trans (⇛-sq (fst (≈-valid (S.conn-sound (fst c) r t)) (cell-valid c)) vq (squares-sound r mq))
                   (⇛-≈ (≈-sym (nf-≈ sw q))))

  out-sound : ∀ c {d} → d ∈L out c → fst c ⇛ fst d
  out-sound c md with out-inv (members (fst c)) md
  ... | r , q , mr , mq , mc = out-sound′ c r q mr mq mc

  out-complete : ∀ {p q} (vp : Valid p) (vq : Valid q) → Sq p q →
                 cellOf q vq ∈L out (cellOf p vp)
  out-complete {p} {q} vp vq s =
    ∈-concat⁺ _ (∈-concat⁺ _ (mkCell-has vq) (∈-map⁺ mkCell (squares-complete s)))
      (∈-map⁺ (λ r → concatK (mapK mkCell (squares r))) mp)
    where
    vn : Valid (nf sw p)
    vn = nf-valid vp
    mp : p ∈L members (nf sw p)
    mp = ∈-filter⁺ (S.conn (nf sw p)) (U (nf sw p))
           (subst (λ c → p ∈L Uc c) (≈-charge (≈-sym (nf-≈ sw p))) (U-has vp))
           (S.conn-complete vn (nf-≈ sw p))

  ----------------------------------------------------------------------
  -- The layer.

  layer : Layer
  layer = record
    { Cell   = Cell
    ; _≟_    = _≟C_
    ; Letter = Cell
    ; out    = out
    ; tgt    = λ c → c
    ; Supp   = Bool
    ; supp   = λ _ → true
    ; suppL  = λ _ → true
    ; _∪_    = _∧_
    ; full   = λ b → b
    }

  -- Paths of letters are exactly 5-reachability.
  path→⇛ : ∀ {c d} → Path layer c d → fst c ⇛ fst d
  path→⇛ ε            = ⇛-≈ ≈-refl
  path→⇛ {c} (ℓ ◅[ m′ ] p) = ⇛-trans (out-sound c m′) (path→⇛ p)

  _++P_ : ∀ {c d e} → Path layer c d → Path layer d e → Path layer c e
  ε             ++P q = q
  (ℓ ◅[ m′ ] p) ++P q = ℓ ◅[ m′ ] (p ++P q)

  ⇛-valid : ∀ {p q} → p ⇛ q → Valid p → Valid q
  ⇛-valid (⇛-≈ e)       v = fst (≈-valid e) v
  ⇛-valid (⇛-sq _ vq _) _ = vq
  ⇛-valid (⇛-trans a b) v = ⇛-valid b (⇛-valid a v)

  ⇛→path : ∀ {p q} (vp : Valid p) (vq : Valid q) → p ⇛ q → Path layer (cellOf p vp) (cellOf q vq)
  ⇛→path {p} vp vq (⇛-≈ e) = subst (λ d → Path layer (cellOf p vp) d) (cell-≡ (nf-cong sw vp e)) ε
  ⇛→path vp vq (⇛-sq _ _ s) = cellOf _ vq ◅[ out-complete vp vq s ] ε
  ⇛→path vp vq (⇛-trans a b) = ⇛→path vp (⇛-valid a vp) a ++P ⇛→path (⇛-valid a vp) vq b

  -- On this layer SC is 5-reachability.
  sc→⇛ : ∀ {c d} → SC layer c d → fst c ⇛ fst d
  sc→⇛ (p , _) = path→⇛ p

  ⇛→sc : ∀ {c d} → fst c ⇛ fst d → SC layer c d
  ⇛→sc {c} {d} r =
    subst₂ (λ x y → Path layer x y) (cellOf-self c) (cellOf-self d)
      (⇛→path (cell-valid c) (cell-valid d) r) , full-all (subst₂ (λ x y → Path layer x y) (cellOf-self c) (cellOf-self d) (⇛→path (cell-valid c) (cell-valid d) r))
    where
    subst₂ : ∀ {A : Set} (P : A → A → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
    subst₂ P refl refl p = p
    full-all : ∀ {x y} (p : Path layer x y) → T (suppP layer p)
    full-all ε            = tt
    full-all (ℓ ◅[ _ ] p) = full-all p

  ----------------------------------------------------------------------
  -- SC is decidable on this layer, with no length bound.

  private
    ∧-assoc : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
    ∧-assoc true  b c = refl
    ∧-assoc false b c = refl

    _≟Bool_ : (a b : Bool) → Dec (a ≡ b)
    true  ≟Bool true  = yes refl
    false ≟Bool false = yes refl
    true  ≟Bool false = no λ ()
    false ≟Bool true  = no λ ()

  -- All cells of one charge.
  UC : Nat → List Cell
  UC k = concatK (mapK mkCell (Uc k))

  UC-has : ∀ {q} (vq : Valid q) → cellOf q vq ∈L UC (charge q)
  UC-has {q} vq = ∈-concat⁺ _ (mkCell-has vq) (∈-map⁺ mkCell (U-has vq))

  UC-charge : ∀ k {c} → c ∈L UC k → charge (fst c) ≡ k
  UC-charge k {c} mc with ∈-concat⁻ (mapK mkCell (Uc k)) mc
  ... | cs , mc′ , mcs with ∈-map⁻ mkCell (Uc k) mcs
  ...   | q , mq , refl with mkCell-elim q mc′
  ...     | vq , refl =
    trans (≈-charge (nf-≈ sw q))
      (isYes-sound (charge q ≟N k) (snd (∈-filter⁻ (λ q → isYes (charge q ≟N k)) (allPaths k start end) mq)))

  ⇛-charge : ∀ {p q} → p ⇛ q → charge q ≡ charge p
  ⇛-charge (⇛-≈ e)       = sym (≈-charge e)
  ⇛-charge (⇛-sq _ _ s)  = sq-charge s
  ⇛-charge (⇛-trans a b) = trans (⇛-charge b) (⇛-charge a)

  closedC : ∀ k {y d} → y ∈L UC k → d ∈L out y → d ∈L UC k
  closedC k {y} {d} my md =
    subst (_∈L UC k) (cellOf-self d)
      (subst (λ j → cellOf (fst d) (cell-valid d) ∈L UC j)
             (trans (⇛-charge (out-sound y md)) (UC-charge k my))
             (UC-has (cell-valid d)))

  closedS : ∀ {y a d} → a ∈L (true ∷ []) → d ∈L out y → (a ∧ (true ∧ true)) ∈L (true ∷ [])
  closedS here _ = here

  sc? : ∀ c d → Dec (SC layer c d)
  sc? c d =
    RF.DecideFin.sc? layer ∧-assoc _≟Bool_ (UC (charge (fst c))) (true ∷ [])
      (closedC (charge (fst c))) (λ {y} {a} {ℓ} _ ma md → closedS {y} {a} {ℓ} ma md)
      (subst (_∈L UC (charge (fst c))) (cellOf-self c) (UC-has (cell-valid c))) here d
