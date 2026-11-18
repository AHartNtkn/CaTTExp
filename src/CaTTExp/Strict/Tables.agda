------------------------------------------------------------------------
-- Tables form a strict ω-category (ledger A5, step N0).
--
-- Fix a commutative monoid M and a length L. A table is a vector
-- x = ((x₀⁻, x₀⁺), …, (x_{L−1}⁻, x_{L−1}⁺)) of pairs of elements of M.
-- Following Steiner (Omega-categories and chain complexes, 2004, §2),
--
--   sₙ x = (x₀, …, x_{n−1}, (xₙ⁻, xₙ⁻), 0, 0, …)
--   tₙ x = (x₀, …, x_{n−1}, (xₙ⁺, xₙ⁺), 0, 0, …)
--   x #ₙ y = (x₀, …, x_{n−1}, (xₙ⁻, yₙ⁺), x_{n+1} + y_{n+1}, …)
--
-- (the last is x + y − tₙ x, without subtraction). Every table, not
-- only a cell of ν(K), satisfies the axioms of a strict ω-category
-- (`tables`): the axioms are identities of commutative monoids, entry
-- by entry. ν(K) is the sub-ω-category of cells (CaTTExp.Strict.Nu).
------------------------------------------------------------------------
module CaTTExp.Strict.Tables where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega

record CMon : Set₁ where
  field
    M     : Set
    ε     : M
    _⊕_   : M → M → M
    ⊕-id  : ∀ a → ε ⊕ a ≡ a
    ⊕-comm  : ∀ a b → a ⊕ b ≡ b ⊕ a
    ⊕-assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module _ (𝕄 : CMon) where
  open CMon 𝕄

  P : Set
  P = M × M

  zP : P
  zP = ε , ε

  _+P_ : P → P → P
  (a , b) +P (c , d) = (a ⊕ c) , (b ⊕ d)

  Tab : Nat → Set
  Tab L = Vec P L

  zeros : ∀ {L} → Tab L
  zeros {zero}  = []
  zeros {suc L} = zP ∷ zeros

  add : ∀ {L} → Tab L → Tab L → Tab L
  add []      []       = []
  add (e ∷ r) (e′ ∷ r′) = (e +P e′) ∷ add r r′

  srcT tgtT : ∀ {L} → Nat → Tab L → Tab L
  srcT n       []            = []
  srcT zero    ((a , b) ∷ r) = (a , a) ∷ zeros
  srcT (suc n) (e ∷ r)       = e ∷ srcT n r
  tgtT n       []            = []
  tgtT zero    ((a , b) ∷ r) = (b , b) ∷ zeros
  tgtT (suc n) (e ∷ r)       = e ∷ tgtT n r

  compT : ∀ {L} → Nat → Tab L → Tab L → Tab L
  compT n       []            []              = []
  compT zero    ((a , b) ∷ r) ((c , d) ∷ r′) = (a , d) ∷ add r r′
  compT (suc n) (e ∷ r)       (e′ ∷ r′)      = e ∷ compT n r r′

  ----------------------------------------------------------------------
  -- Monoid lemmas on tables.

  private
    swap-mid : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
    swap-mid a b c d =
      trans (⊕-assoc a b (c ⊕ d))
        (trans (cong (a ⊕_) (trans (sym (⊕-assoc b c d)) (trans (cong (_⊕ d) (⊕-comm b c)) (⊕-assoc c b d))))
               (sym (⊕-assoc a c (b ⊕ d))))

  ⊕-idr : ∀ a → a ⊕ ε ≡ a
  ⊕-idr a = trans (⊕-comm a ε) (⊕-id a)

  add-zl : ∀ {L} (r : Tab L) → add zeros r ≡ r
  add-zl []            = refl
  add-zl ((a , b) ∷ r) = cong₂ _∷_ (cong₂ _,_ (⊕-id a) (⊕-id b)) (add-zl r)

  add-zr : ∀ {L} (r : Tab L) → add r zeros ≡ r
  add-zr []            = refl
  add-zr ((a , b) ∷ r) = cong₂ _∷_ (cong₂ _,_ (⊕-idr a) (⊕-idr b)) (add-zr r)

  add-assoc : ∀ {L} (r s u : Tab L) → add (add r s) u ≡ add r (add s u)
  add-assoc []            []            []            = refl
  add-assoc ((a , b) ∷ r) ((c , d) ∷ s) ((e , f) ∷ u) =
    cong₂ _∷_ (cong₂ _,_ (⊕-assoc a c e) (⊕-assoc b d f)) (add-assoc r s u)

  add-swap : ∀ {L} (r s u v : Tab L) → add (add r s) (add u v) ≡ add (add r u) (add s v)
  add-swap []            []            []            []            = refl
  add-swap ((a , b) ∷ r) ((c , d) ∷ s) ((e , f) ∷ u) ((g , h) ∷ v) =
    cong₂ _∷_ (cong₂ _,_ (swap-mid a c e g) (swap-mid b d f h)) (add-swap r s u v)

  zeros-add : ∀ {L} → add {L} zeros zeros ≡ zeros
  zeros-add = add-zl zeros

  srcT-zeros : ∀ {L} n → srcT {L} n zeros ≡ zeros
  srcT-zeros {zero}  n       = refl
  srcT-zeros {suc L} zero    = refl
  srcT-zeros {suc L} (suc n) = cong (zP ∷_) (srcT-zeros n)

  tgtT-zeros : ∀ {L} n → tgtT {L} n zeros ≡ zeros
  tgtT-zeros {zero}  n       = refl
  tgtT-zeros {suc L} zero    = refl
  tgtT-zeros {suc L} (suc n) = cong (zP ∷_) (tgtT-zeros n)

  -- composites and sums commute
  add-comp : ∀ {L} n (a b c d : Tab L) → add (compT n a b) (compT n c d) ≡ compT n (add a c) (add b d)
  add-comp n       []            []            []            []            = refl
  add-comp zero    ((a , b) ∷ r) ((c , d) ∷ s) ((e , f) ∷ u) ((g , h) ∷ v) =
    cong ((a ⊕ e , d ⊕ h) ∷_) (add-swap r s u v)
  add-comp (suc n) (x ∷ r) (y ∷ s) (z ∷ u) (w ∷ v) = cong ((x +P z) ∷_) (add-comp n r s u v)

  add-src : ∀ {L} n (a b : Tab L) → add (srcT n a) (srcT n b) ≡ srcT n (add a b)
  add-src n       []            []            = refl
  add-src zero    ((a , b) ∷ r) ((c , d) ∷ s) = cong ((a ⊕ c , a ⊕ c) ∷_) zeros-add
  add-src (suc n) (x ∷ r) (y ∷ s) = cong ((x +P y) ∷_) (add-src n r s)

  add-tgt : ∀ {L} n (a b : Tab L) → add (tgtT n a) (tgtT n b) ≡ tgtT n (add a b)
  add-tgt n       []            []            = refl
  add-tgt zero    ((a , b) ∷ r) ((c , d) ∷ s) = cong ((b ⊕ d , b ⊕ d) ∷_) zeros-add
  add-tgt (suc n) (x ∷ r) (y ∷ s) = cong ((x +P y) ∷_) (add-tgt n r s)

  ----------------------------------------------------------------------
  -- The axioms.


  ss-< : ∀ {L m n} (x : Tab L) → m < n → srcT m (srcT n x) ≡ srcT m x
  ss-< {m = zero} {n = suc n} []            _       = refl
  ss-< {m = zero} {n = suc n} ((a , b) ∷ r) _       = refl
  ss-< {m = suc m} {n = suc n} []            _       = refl
  ss-< {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (ss-< r l)

  st-< : ∀ {L m n} (x : Tab L) → m < n → srcT m (tgtT n x) ≡ srcT m x
  st-< {m = zero} {n = suc n} []            _       = refl
  st-< {m = zero} {n = suc n} ((a , b) ∷ r) _       = refl
  st-< {m = suc m} {n = suc n} []            _       = refl
  st-< {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (st-< r l)

  ts-< : ∀ {L m n} (x : Tab L) → m < n → tgtT m (srcT n x) ≡ tgtT m x
  ts-< {m = zero} {n = suc n} []            _       = refl
  ts-< {m = zero} {n = suc n} ((a , b) ∷ r) _       = refl
  ts-< {m = suc m} {n = suc n} []            _       = refl
  ts-< {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (ts-< r l)

  tt-< : ∀ {L m n} (x : Tab L) → m < n → tgtT m (tgtT n x) ≡ tgtT m x
  tt-< {m = zero} {n = suc n} []            _       = refl
  tt-< {m = zero} {n = suc n} ((a , b) ∷ r) _       = refl
  tt-< {m = suc m} {n = suc n} []            _       = refl
  tt-< {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (tt-< r l)

  ss-≥ : ∀ {L m n} (x : Tab L) → n ≤ m → srcT m (srcT n x) ≡ srcT n x
  ss-≥ {m = m} {n = n}     []            _       = refl
  ss-≥ {m = zero} {n = zero}  ((a , b) ∷ r) _       = refl
  ss-≥ {m = suc m} {n = zero}  ((a , b) ∷ r) _       = cong ((a , a) ∷_) (srcT-zeros m)
  ss-≥ {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (ss-≥ r l)

  ts-≥ : ∀ {L m n} (x : Tab L) → n ≤ m → tgtT m (srcT n x) ≡ srcT n x
  ts-≥ {m = m} {n = n}     []            _       = refl
  ts-≥ {m = zero} {n = zero}  ((a , b) ∷ r) _       = refl
  ts-≥ {m = suc m} {n = zero}  ((a , b) ∷ r) _       = cong ((a , a) ∷_) (tgtT-zeros m)
  ts-≥ {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (ts-≥ r l)

  st-≥ : ∀ {L m n} (x : Tab L) → n ≤ m → srcT m (tgtT n x) ≡ tgtT n x
  st-≥ {m = m} {n = n}     []            _       = refl
  st-≥ {m = zero} {n = zero}  ((a , b) ∷ r) _       = refl
  st-≥ {m = suc m} {n = zero}  ((a , b) ∷ r) _       = cong ((b , b) ∷_) (srcT-zeros m)
  st-≥ {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (st-≥ r l)

  tt-≥ : ∀ {L m n} (x : Tab L) → n ≤ m → tgtT m (tgtT n x) ≡ tgtT n x
  tt-≥ {m = m} {n = n}     []            _       = refl
  tt-≥ {m = zero} {n = zero}  ((a , b) ∷ r) _       = refl
  tt-≥ {m = suc m} {n = zero}  ((a , b) ∷ r) _       = cong ((b , b) ∷_) (tgtT-zeros m)
  tt-≥ {m = suc m} {n = suc n} (e ∷ r)       (s≤s l) = cong (e ∷_) (tt-≥ r l)

  s-comp : ∀ {L} n (x y : Tab L) → srcT n (compT n x y) ≡ srcT n x
  s-comp n       []            []            = refl
  s-comp zero    ((a , b) ∷ r) ((c , d) ∷ s) = refl
  s-comp (suc n) (e ∷ r)       (e′ ∷ s)      = cong (e ∷_) (s-comp n r s)

  -- Composability, entry by entry.
  hd≡ : ∀ {L} {e e′ : P} {r r′ : Tab L} → e ∷ r ≡ e′ ∷ r′ → e ≡ e′
  hd≡ refl = refl

  tl≡ : ∀ {L} {e e′ : P} {r r′ : Tab L} → e ∷ r ≡ e′ ∷ r′ → r ≡ r′
  tl≡ refl = refl

  fst≡ : ∀ {a b c d : M} → (a , b) ≡ (c , d) → a ≡ c
  fst≡ refl = refl

  t-comp : ∀ {L} n (x y : Tab L) → tgtT n x ≡ srcT n y → tgtT n (compT n x y) ≡ tgtT n y
  t-comp n       []            []            p = refl
  t-comp zero    ((a , b) ∷ r) ((c , d) ∷ s) p = refl
  t-comp (suc n) (e ∷ r)       (e′ ∷ s)      p = cong₂ _∷_ (hd≡ p) (t-comp n r s (tl≡ p))

  s-comp-< : ∀ {L m n} (x y : Tab L) → m < n → srcT m (compT n x y) ≡ srcT m x
  s-comp-< {m = zero}  {suc n} []            []            _ = refl
  s-comp-< {m = zero}  {suc n} ((a , b) ∷ r) (e′ ∷ s)      _ = refl
  s-comp-< {m = suc m} {suc n} []            []            _ = refl
  s-comp-< {m = suc m} {suc n} (e ∷ r)       (e′ ∷ s)      (s≤s l) = cong (e ∷_) (s-comp-< r s l)

  t-comp-< : ∀ {L m n} (x y : Tab L) → tgtT n x ≡ srcT n y → m < n → tgtT m (compT n x y) ≡ tgtT m y
  t-comp-< {m = zero}  {suc n} []            []            p _ = refl
  t-comp-< {m = zero}  {suc n} ((a , b) ∷ r) ((c , d) ∷ s) p _ =
    cong (λ z → (z , z) ∷ zeros) (cong snd (hd≡ p))
  t-comp-< {m = suc m} {suc n} []            []            p _ = refl
  t-comp-< {m = suc m} {suc n} (e ∷ r)       (e′ ∷ s)      p (s≤s l) =
    cong₂ _∷_ (hd≡ p) (t-comp-< r s (tl≡ p) l)

  s-comp-> : ∀ {L m n} (x y : Tab L) → n < m → srcT m (compT n x y) ≡ compT n (srcT m x) (srcT m y)
  s-comp-> {m = suc m} {zero}  []            []            _ = refl
  s-comp-> {m = suc m} {zero}  ((a , b) ∷ r) ((c , d) ∷ s) _ = cong ((a , d) ∷_) (sym (add-src m r s))
  s-comp-> {m = suc m} {suc n} []            []            _ = refl
  s-comp-> {m = suc m} {suc n} (e ∷ r)       (e′ ∷ s)      (s≤s l) = cong (e ∷_) (s-comp-> r s l)

  t-comp-> : ∀ {L m n} (x y : Tab L) → n < m → tgtT m (compT n x y) ≡ compT n (tgtT m x) (tgtT m y)
  t-comp-> {m = suc m} {zero}  []            []            _ = refl
  t-comp-> {m = suc m} {zero}  ((a , b) ∷ r) ((c , d) ∷ s) _ = cong ((a , d) ∷_) (sym (add-tgt m r s))
  t-comp-> {m = suc m} {suc n} []            []            _ = refl
  t-comp-> {m = suc m} {suc n} (e ∷ r)       (e′ ∷ s)      (s≤s l) = cong (e ∷_) (t-comp-> r s l)

  u-l : ∀ {L} n (x : Tab L) → compT n (srcT n x) x ≡ x
  u-l n       []            = refl
  u-l zero    ((a , b) ∷ r) = cong ((a , b) ∷_) (add-zl r)
  u-l (suc n) (e ∷ r)       = cong (e ∷_) (u-l n r)

  u-r : ∀ {L} n (x : Tab L) → compT n x (tgtT n x) ≡ x
  u-r n       []            = refl
  u-r zero    ((a , b) ∷ r) = cong ((a , b) ∷_) (add-zr r)
  u-r (suc n) (e ∷ r)       = cong (e ∷_) (u-r n r)

  c-assoc : ∀ {L} n (x y z : Tab L) → compT n (compT n x y) z ≡ compT n x (compT n y z)
  c-assoc n       []            []            []            = refl
  c-assoc zero    ((a , b) ∷ r) ((c , d) ∷ s) ((e , f) ∷ u) = cong ((a , f) ∷_) (add-assoc r s u)
  c-assoc (suc n) (x ∷ r)       (y ∷ s)       (z ∷ u)       = cong (x ∷_) (c-assoc n r s u)

  c-ich : ∀ {L m n} (x y z w : Tab L) → m < n →
          compT m (compT n x y) (compT n z w) ≡ compT n (compT m x z) (compT m y w)
  c-ich {m = zero}  {suc n} []            []            []            []            _ = refl
  c-ich {m = zero}  {suc n} ((a , b) ∷ r) (y ∷ s)       ((c , d) ∷ u) (w ∷ v)       _ =
    cong ((a , d) ∷_) (add-comp n r s u v)
  c-ich {m = suc m} {suc n} []            []            []            []            _ = refl
  c-ich {m = suc m} {suc n} (x ∷ r)       (y ∷ s)       (z ∷ u)       (w ∷ v)       (s≤s l) =
    cong (x ∷_) (c-ich r s u v l)

  -- All tables of length L.
  tables : Nat → ωCat
  tables L = record
    { C = Tab L ; src = srcT ; tgt = tgtT ; comp = λ n x y _ → compT n x y
    ; src-src-< = ss-< ; src-tgt-< = st-< ; tgt-src-< = ts-< ; tgt-tgt-< = tt-<
    ; src-src-≥ = ss-≥ ; tgt-src-≥ = ts-≥ ; src-tgt-≥ = st-≥ ; tgt-tgt-≥ = tt-≥
    ; src-comp = λ n x y _ → s-comp n x y
    ; tgt-comp = λ n x y p → t-comp n x y p
    ; src-comp-< = λ x y _ l → s-comp-< x y l
    ; tgt-comp-< = λ x y p l → t-comp-< x y p l
    ; src-comp-> = λ x y _ l _ → s-comp-> x y l
    ; tgt-comp-> = λ x y _ l _ → t-comp-> x y l
    ; unit-l = λ n x _ → u-l n x
    ; unit-r = λ n x _ → u-r n x
    ; assoc = λ n x y z _ _ _ _ → c-assoc n x y z
    ; interchange = λ x y z w l _ _ _ _ _ _ → c-ich x y z w l
    }
