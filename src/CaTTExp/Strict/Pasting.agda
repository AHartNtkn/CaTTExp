------------------------------------------------------------------------
-- The table of each hom of a pasting context is a cell.
--
-- For a pasting context Γ and objects o, o', the hom table
--     Tb Γ (o , o') b i = { v | v a cell of the hom o → o' of hom
--                               dimension i, not the target (b = −)
--                               resp. source (b = +) of any cell }
-- is the composite ⟨Θ⟩ of the hom's pasting diagram Θ. We prove, by
-- induction on the pasting derivation, the two cell conditions that
-- need the pasting structure, augmentation and the chain equation
-- (`hom-cores`), and that its entries are basis elements of the hom
-- o → o' (`Tb-basis`). The dimension bound and the full TabCell are in
-- CaTTExp.Strict.Bridge (`hom-cell`). Each pse step adds y : A and
-- f : x → y at the cursor x; the table changes only in the hom of x:
-- x leaves the + side of its dimension, y enters it, and f enters
-- both sides one dimension up.
------------------------------------------------------------------------
module CaTTExp.Strict.Pasting where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Tensor
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- Ranges of levels and filters over them.

rng : Nat → List Nat
rng zero    = []
rng (suc n) = rng n ++ (n ∷ [])

sing : Nat → Tuple
sing v = v ∷ []

filter-++ : ∀ (p : Nat → Bool) xs ys → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
filter-++ p []       ys = refl
filter-++ p (x ∷ xs) ys with p x
... | true  = cong (x ∷_) (filter-++ p xs ys)
... | false = filter-++ p xs ys

map-++ : ∀ {A B : Set} (g : A → B) xs ys → map g (xs ++ ys) ≡ map g xs ++ map g ys
map-++ g []       ys = refl
map-++ g (x ∷ xs) ys = cong (g x ∷_) (map-++ g xs ys)

any-++ : ∀ (p : Nat → Bool) xs ys → any p (xs ++ ys) ≡ any p xs ∨ any p ys
any-++ p []       ys = refl
any-++ p (x ∷ xs) ys rewrite any-++ p xs ys = ∨-assoc (p x) (any p xs) (any p ys)
  where
  ∨-assoc : ∀ a b c → a ∨ (b ∨ c) ≡ (a ∨ b) ∨ c
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

filter-rng-ext : ∀ n (p q : Nat → Bool) → (∀ v → T (v <ℕ n) → p v ≡ q v) → filter p (rng n) ≡ filter q (rng n)
filter-rng-ext zero    p q h = refl
filter-rng-ext (suc n) p q h
  rewrite filter-++ p (rng n) (n ∷ []) | filter-++ q (rng n) (n ∷ [])
        | filter-rng-ext n p q (λ v lt → h v (<-suc v n lt)) | h n (n<suc n) = refl

any-rng-ext : ∀ n (p q : Nat → Bool) → (∀ v → T (v <ℕ n) → p v ≡ q v) → any p (rng n) ≡ any q (rng n)
any-rng-ext zero    p q h = refl
any-rng-ext (suc n) p q h
  rewrite any-++ p (rng n) (n ∷ []) | any-++ q (rng n) (n ∷ [])
        | any-rng-ext n p q (λ v lt → h v (<-suc v n lt)) | h n (n<suc n) = refl

any-rng-false : ∀ n (p : Nat → Bool) → (∀ v → T (v <ℕ n) → p v ≡ false) → any p (rng n) ≡ false
any-rng-false n p h = trans (any-rng-ext n p (λ _ → false) h) (lem n)
  where
  lem : ∀ n → any (λ _ → false) (rng n) ≡ false
  lem zero    = refl
  lem (suc n) = trans (any-++ (λ _ → false) (rng n) (n ∷ [])) (cong (_∨ false) (lem n))

≡-sym-false : ∀ x n → (x ==ℕ n) ≡ false → (n ==ℕ x) ≡ false
≡-sym-false zero    zero    ()
≡-sym-false zero    (suc n) e = refl
≡-sym-false (suc x) zero    e = refl
≡-sym-false (suc x) (suc n) e = ≡-sym-false x n e
lt-pred : ∀ x n → T (x <ℕ suc n) → (x ==ℕ n) ≡ false → T (x <ℕ n)
lt-pred zero    zero    _ ()
lt-pred zero    (suc n) _ _ = tt
lt-pred (suc x) (suc n) p e = lt-pred x n p e

-- Dropping one element x from a filtered range.
filter-drop : ∀ n (p q : Nat → Bool) x → T (x <ℕ n) → p x ≡ true → q x ≡ false →
              (∀ v → T (v <ℕ n) → (v ==ℕ x) ≡ false → p v ≡ q v) →
              map sing (filter p (rng n)) ≈ map sing (filter q (rng n)) ++ (sing x ∷ [])
filter-drop (suc n) p q x lt px qx h with x ==ℕ n in ex
... | true rewrite ==→≡ x n ex
             | filter-++ p (rng n) (n ∷ []) | filter-++ q (rng n) (n ∷ []) | px | qx
             | filter-rng-ext n p q (λ v lt' → h v (<-suc v n lt') (<→≢ v n lt')) =
  ≡→≈ (trans (map-++ sing (filter q (rng n)) (n ∷ []))
             (cong (_++ (sing n ∷ [])) (sym (trans (cong (map sing) (++-[]L (filter q (rng n)))) refl))))
... | false rewrite filter-++ p (rng n) (n ∷ []) | filter-++ q (rng n) (n ∷ [])
                  | h n (n<suc n) (≡-sym-false x n ex) =
  begin
    map sing (filter p (rng n) ++ filter q (n ∷ []))
  ≈⟨ ≡→≈ (map-++ sing (filter p (rng n)) _) ⟩
    map sing (filter p (rng n)) ++ map sing (filter q (n ∷ []))
  ≈⟨ ++-cong (filter-drop n p q x (lt-pred x n lt ex) px qx (λ v lt' → h v (<-suc v n lt')))
             (≈-refl {map sing (filter q (n ∷ []))}) ⟩
    (map sing (filter q (rng n)) ++ (sing x ∷ [])) ++ map sing (filter q (n ∷ []))
  ≈⟨ ++-assoc (map sing (filter q (rng n))) _ _ ⟩
    map sing (filter q (rng n)) ++ ((sing x ∷ []) ++ map sing (filter q (n ∷ [])))
  ≈⟨ ++-cong (≈-refl {map sing (filter q (rng n))}) (++-comm (sing x ∷ []) (map sing (filter q (n ∷ [])))) ⟩
    map sing (filter q (rng n)) ++ (map sing (filter q (n ∷ [])) ++ (sing x ∷ []))
  ≈⟨ ≈-sym (++-assoc (map sing (filter q (rng n))) _ _) ⟩
    (map sing (filter q (rng n)) ++ map sing (filter q (n ∷ []))) ++ (sing x ∷ [])
  ≈⟨ ≡→≈ (cong (_++ (sing x ∷ [])) (sym (map-++ sing (filter q (rng n)) _))) ⟩
    map sing (filter q (rng n) ++ filter q (n ∷ [])) ++ (sing x ∷ [])
  ∎

------------------------------------------------------------------------
-- Hom tables.

hitM : Bool → Nat → Maybe (Nat × Nat) → Bool
hitM b v nothing        = false
hitM b v (just (s , t)) = (if b then s else t) ==ℕ v

-- w has v as its source (b = true) or target (b = false).
hitB : Ctx → Bool → Nat → Nat → Bool
hitB Γ b v w = hitM b v (facesTy (lookup Γ w))

homM : Nat × Nat → Maybe (Nat × Nat) → Bool
homM p nothing         = false
homM p (just (s , t))  = (s ==ℕ fst p) ∧ (t ==ℕ snd p)

-- v is a cell of hom dimension i of the hom p.
memHom : Ctx → Nat × Nat → Nat → Nat → Bool
memHom Γ p i v = homM p (endsL (lookup Γ v)) ∧ (hdimV Γ v ==ℕ i)

sel : Ctx → Nat × Nat → Bool → Nat → Nat → Bool
sel Γ p b i v = memHom Γ p i v ∧ not (any (hitB Γ b v) (rng (len Γ)))

Tb : Ctx → Nat × Nat → Tab
Tb Γ p b i = map sing (filter (sel Γ p b i) (rng (len Γ)))

-- The two cell conditions that need the pasting structure.
Core : Ctx → Nat × Nat → Tab → Set
Core Γ p X = (∀ b → Σ Tuple λ w → X b 0 ≈ w ∷ []) × (∀ b k → δ Γ (X b (suc k)) ~ β X k)

------------------------------------------------------------------------
-- Basis elements.

private
  T-∧ : ∀ {a b} → T (a ∧ b) → T a × T b
  T-∧ {true} {b} p = tt , p

  homM-sound : ∀ p m → T (homM p m) → m ≡ just p
  homM-sound (o , o') (just (s , t)) h =
    let (h1 , h2) = T-∧ {s ==ℕ o} h in
    cong₂ (λ a c → just (a , c)) (==ℕ-sound s o h1) (==ℕ-sound t o' h2)

  All-map-sing : ∀ {P : Tuple → Set} (q : Nat → Bool) xs → (∀ v → T (q v) → P (sing v)) →
                 All P (map sing (filter q xs))
  All-map-sing q []       f = tt
  All-map-sing q (x ∷ xs) f with q x in e
  ... | true  = f x (subst T (sym e) tt) , All-map-sing q xs f
  ... | false = All-map-sing q xs f

memHom-basis : ∀ Γ o o' i v → T (memHom Γ (o , o') i v) → Basis Γ o o' i (sing v)
memHom-basis Γ o o' i v m =
  let (h1 , h2) = T-∧ {homM (o , o') (endsL (lookup Γ v))} m in
  (o' , homM-sound (o , o') _ h1 , refl) , trans (+-zero (hdimV Γ v)) (==ℕ-sound _ i h2)

Tb-basis : ∀ Γ o o' b i → All (Basis Γ o o' i) (Tb Γ (o , o') b i)
Tb-basis Γ o o' b i =
  All-map-sing (sel Γ (o , o') b i) (rng (len Γ))
    (λ v s → memHom-basis Γ o o' i v (fst (T-∧ {memHom Γ (o , o') i v} s)))

------------------------------------------------------------------------
-- Context extension.

lookup-old : ∀ Γ C v → T (v <ℕ len Γ) → lookup (Γ ▸ C) v ≡ lookup Γ v
lookup-old Γ C v lt rewrite <→≢ v (len Γ) lt = refl


private
  lt-of-ends : ∀ Γ v {e} → endsL (lookup Γ v) ≡ just e → T (v <ℕ len Γ)
  lt-of-ends Γ v eq with lookup Γ v in lv
  ... | just B = lookup-lt Γ v lv

  ∂T-ext : ∀ Γ C b {x y} w → WFT Γ x y w → ∂T (Γ ▸ C) b w ≡ ∂T Γ b w
  ∂T-ext Γ C b []      _               = refl
  ∂T-ext Γ C b (v ∷ w) (z , ev , wft)
    rewrite lookup-old Γ C v (lt-of-ends Γ v ev) =
    cong (here b (facesTy (lookup Γ v)) w ++_)
         (cong (consB v) (∂T-ext Γ C (flipN (hdimV Γ v) b) w wft))

δ-ext : ∀ Γ C {o o' k} Z → All (Basis Γ o o' k) Z → δ (Γ ▸ C) Z ~ δ Γ Z
δ-ext Γ C Z a =
  ≈d (cm-ext (∂T (Γ ▸ C) true) (∂T Γ true) Z a (λ w bw → ≡→≈ (∂T-ext Γ C true w (fst bw))))
     (cm-ext (∂T (Γ ▸ C) false) (∂T Γ false) Z a (λ w bw → ≡→≈ (∂T-ext Γ C false w (fst bw))))

Core-ext : ∀ Γ C o o' X → (∀ b k → All (Basis Γ o o' k) (X b k)) → Core Γ (o , o') X → Core (Γ ▸ C) (o , o') X
Core-ext Γ C o o' X bas (ag , ch) =
  ag , λ b k → ~-trans {δ (Γ ▸ C) (X b (suc k))} (δ-ext Γ C (X b (suc k)) (bas b (suc k))) (ch b k)

Core-≈ : ∀ Γ p X X' → (∀ b k → X b k ≈ X' b k) → Core Γ p X → Core Γ p X'
Core-≈ Γ p X X' e (ag , ch) =
  (λ b → fst (ag b) , ≈-trans (≈-sym (e b 0)) (snd (ag b))) ,
  (λ b k → ~-trans {δ Γ (X' b (suc k))} {δ Γ (X b (suc k))}
             (≈d (cm-cong _ _ _ (≈-sym (e b (suc k)))) (cm-cong _ _ _ (≈-sym (e b (suc k)))))
             (~-trans {δ Γ (X b (suc k))} (ch b k) (≈d (e true k) (e false k))))

------------------------------------------------------------------------
-- The change of one hom table at a pse step, abstractly.
--
-- X is the old table, X' the new one; x is the cursor, y its new
-- parallel copy and f : x → y. Away from (+, d) the new table adds f in
-- dimension d+1; at (+, d) it trades x for y.

private
  ==-sym : ∀ m n → (m ==ℕ n) ≡ (n ==ℕ m)
  ==-sym zero    zero    = refl
  ==-sym zero    (suc n) = refl
  ==-sym (suc m) zero    = refl
  ==-sym (suc m) (suc n) = ==-sym m n

  ==-suc-self : ∀ d → (d ==ℕ suc d) ≡ false
  ==-suc-self zero    = refl
  ==-suc-self (suc d) = ==-suc-self d

  -- (P + E, N + E) ~ (P, N)
  addBoth : ∀ P N E → (P ++ E , N ++ E) ~ (P , N)
  addBoth P N E = mk~ (≈-trans (++-assoc P E N) (++-cong (≈-refl {P}) (++-comm E N)))

  +≡0ˡ : ∀ m n → m + n ≡ 0 → m ≡ 0
  +≡0ˡ zero    n e = refl
  +≡0ˡ (suc m) n ()

  count-1 : ∀ a x → count a (x ∷ []) ≡ (if eqT a x then 1 else 0)
  count-1 a x with eqT a x
  ... | true  = refl
  ... | false = refl

  single-split : ∀ R x w → R ++ (x ∷ []) ≈ w ∷ [] → R ≈ []
  single-split R x w p = mk≈ lem
    where
    eq : ∀ a → count a R + (if eqT a x then 1 else 0) ≡ (if eqT a w then 1 else 0)
    eq a = trans (sym (trans (count-++ a R (x ∷ [])) (cong (count a R +_) (count-1 a x))))
                 (trans (at p a) (count-1 a w))
    lem : ∀ a → count a R ≡ 0
    lem a with eqT a w in eaw | eqT a x in eax | eq a
    ... | false | _     | e = +≡0ˡ (count a R) _ e
    ... | true  | true  | e = +-cancelʳ 1 (count a R) 0 e
    ... | true  | false | e = ⊥-elim (bad (eqT x w) refl)
      where
      aw : a ≡ w
      aw = eqT-sound a w (subst T (sym eaw) tt)
      bad : ∀ c → eqT x w ≡ c → ⊥
      bad true  exw =
        let xw = eqT-sound x w (subst T (sym exw) tt) in
        absurd (trans (sym (eqT-refl a)) (trans (cong (eqT a) (trans aw (sym xw))) eax))
        where
        absurd : true ≡ false → ⊥
        absurd ()
      bad false exw with eq x
      ... | e' rewrite eqT-refl x | exw = n+1≢0 (count x R) e'
        where
        n+1≢0 : ∀ n → n + 1 ≡ 0 → ⊥
        n+1≢0 zero    ()
        n+1≢0 (suc n) ()

  suc-==-self : ∀ d → (suc d ==ℕ d) ≡ false
  suc-==-self zero    = refl
  suc-==-self (suc d) = suc-==-self d

δ-++ : ∀ Γ A B → δ Γ (A ++ B) ~ δ Γ A ⊕ δ Γ B
δ-++ Γ A B = ≈d (≡→≈ (cm-++ (∂T Γ true) A B)) (≡→≈ (cm-++ (∂T Γ false) A B))

δ-cong : ∀ Γ {A B} → A ≈ B → δ Γ A ~ δ Γ B
δ-cong Γ {A} {B} p = ≈d (cm-cong (∂T Γ true) A B p) (cm-cong (∂T Γ false) A B p)

module Step (Γ : Ctx) (p : Nat × Nat) (X X' : Tab) (d x y f : Nat) (R : Bag) where

  Ef : Nat → Bag
  Ef i = if i ==ℕ suc d then sing f ∷ [] else []

  core-step :
    Core Γ p X →
    (∀ b i → (b ∧ (i ==ℕ d)) ≡ false → X' b i ≈ X b i ++ Ef i) →
    X true d ≈ R ++ (sing x ∷ []) → X' true d ≈ R ++ (sing y ∷ []) →
    δ Γ (sing x ∷ []) ~ δ Γ (sing y ∷ []) →
    δ Γ (sing f ∷ []) ~ ((sing y ∷ []) , (sing x ∷ [])) →
    Core Γ p X'
  core-step (ag , ch) S1 S2a S2b Sx Sf = ag' , ch'
    where
    off : ∀ b i → (b ∧ (i ==ℕ d)) ≡ false → (i ==ℕ suc d) ≡ false → X' b i ≈ X b i
    off b i e e' = ≈-trans (S1 b i e) (subst (λ c → X b i ++ (if c then sing f ∷ [] else []) ≈ X b i) (sym e')
                                              (≡→≈ (++-[]L (X b i))))

    ag' : ∀ b → Σ Tuple λ w → X' b 0 ≈ w ∷ []
    ag' false = fst (ag false) , ≈-trans (off false 0 refl refl) (snd (ag false))
    ag' true = agT d refl
      where
      agT : ∀ e → d ≡ e → Σ Tuple λ w → X' true 0 ≈ w ∷ []
      agT (suc e) ed =
        fst (ag true) , ≈-trans (off true 0 (cong (λ c → 0 ==ℕ c) ed) refl) (snd (ag true))
      agT zero ed =
        let (w , q) = ag true in
        y ∷ [] ,
        ≈-trans (subst (λ e → X' true e ≈ R ++ (sing y ∷ [])) ed S2b)
                (++-cong (single-split R (sing x) w (≈-trans (≈-sym (subst (λ e → X true e ≈ R ++ (sing x ∷ [])) ed S2a)) q))
                         (≈-refl {sing y ∷ []}))

    βoff : ∀ k → (k ==ℕ d) ≡ false → β X' k ~ β X k
    βoff k e =
      ~-trans {β X' k} {(X true k ++ Ef k) , (X false k ++ Ef k)}
        (≈d (S1 true k e) (S1 false k refl)) (addBoth (X true k) (X false k) (Ef k))

    ch' : ∀ b k → δ Γ (X' b (suc k)) ~ β X' k
    ch' b k with k ==ℕ d in e1
    ... | true rewrite ==→≡ k d e1 =
      ~-trans {δ Γ (X' b (suc d))} {δ Γ (X b (suc d) ++ (sing f ∷ []))}
        (δ-cong Γ (subst (λ c → X' b (suc d) ≈ X b (suc d) ++ (if c then sing f ∷ [] else []))
                         (==-true d) (S1 b (suc d) (∧-false b (suc-==-self d)))))
     (~-trans {δ Γ (X b (suc d) ++ (sing f ∷ []))} {δ Γ (X b (suc d)) ⊕ δ Γ (sing f ∷ [])}
        (δ-++ Γ (X b (suc d)) (sing f ∷ []))
     (~-trans {δ Γ (X b (suc d)) ⊕ δ Γ (sing f ∷ [])} {β X d ⊕ ((sing y ∷ []) , (sing x ∷ []))}
        (⊕-cong {δ Γ (X b (suc d))} (ch b d) Sf)
     (~-trans {β X d ⊕ ((sing y ∷ []) , (sing x ∷ []))}
              {((R ++ (sing x ∷ [])) ++ (sing y ∷ [])) , (X false d ++ (sing x ∷ []))}
        (≈d (++-cong S2a (≈-refl {sing y ∷ []})) (≈-refl {X false d ++ (sing x ∷ [])}))
     (~-trans {((R ++ (sing x ∷ [])) ++ (sing y ∷ [])) , (X false d ++ (sing x ∷ []))}
              {(R ++ (sing y ∷ [])) , X false d}
        (mk~ (perm R (X false d) (sing x ∷ []) (sing y ∷ [])))
        (~-sym {β X' d} (≈d S2b (off false d refl (==-suc-self d))))))))
      where
      ∧-false : ∀ b {c} → c ≡ false → (b ∧ c) ≡ false
      ∧-false true  e = e
      ∧-false false e = refl
      -- ((R + x) + y) + N ≈ (R + y) + (N + x)
      perm : ∀ R N X Y → ((R ++ X) ++ Y) ++ N ≈ (R ++ Y) ++ (N ++ X)
      perm R N X Y =
        begin
          ((R ++ X) ++ Y) ++ N
        ≈⟨ ++-cong (swap R X Y) (≈-refl {N}) ⟩
          ((R ++ Y) ++ X) ++ N
        ≈⟨ ++-assoc (R ++ Y) X N ⟩
          (R ++ Y) ++ (X ++ N)
        ≈⟨ ++-cong (≈-refl {R ++ Y}) (++-comm X N) ⟩
          (R ++ Y) ++ (N ++ X)
        ∎
        where
        swap : ∀ A B C → (A ++ B) ++ C ≈ (A ++ C) ++ B
        swap A B C = ≈-trans (++-assoc A B C) (≈-trans (++-cong (≈-refl {A}) (++-comm B C)) (≈-sym (++-assoc A C B)))
    ... | false with suc k ==ℕ d in e2
    ...   | true =
      ~-trans {δ Γ (X' b (suc k))} {δ Γ (X b (suc k))} (topδ b) (~-trans {δ Γ (X b (suc k))} (ch b k) (~-sym {β X' k} (βoff k e1)))
      where
      kd : suc k ≡ d
      kd = ==→≡ (suc k) d e2
      topδ : ∀ b → δ Γ (X' b (suc k)) ~ δ Γ (X b (suc k))
      topδ false = δ-cong Γ (off false (suc k) refl e1)
      topδ true  =
        ~-trans {δ Γ (X' true (suc k))} {δ Γ (R ++ (sing y ∷ []))}
          (δ-cong Γ (subst (λ e → X' true e ≈ R ++ (sing y ∷ [])) (sym kd) S2b))
       (~-trans {δ Γ (R ++ (sing y ∷ []))} {δ Γ R ⊕ δ Γ (sing y ∷ [])} (δ-++ Γ R (sing y ∷ []))
       (~-trans {δ Γ R ⊕ δ Γ (sing y ∷ [])} {δ Γ R ⊕ δ Γ (sing x ∷ [])}
          (⊕-cong {δ Γ R} (~-refl (δ Γ R)) (~-sym {δ Γ (sing x ∷ [])} Sx))
       (~-trans {δ Γ R ⊕ δ Γ (sing x ∷ [])} {δ Γ (R ++ (sing x ∷ []))}
          (~-sym {δ Γ (R ++ (sing x ∷ []))} (δ-++ Γ R (sing x ∷ [])))
          (δ-cong Γ (≈-sym (subst (λ e → X true e ≈ R ++ (sing x ∷ [])) (sym kd) S2a))))))
    ...   | false =
      ~-trans {δ Γ (X' b (suc k))} {δ Γ (X b (suc k))}
        (δ-cong Γ (off b (suc k) (∧-false' b e2) e1))
        (~-trans {δ Γ (X b (suc k))} (ch b k) (~-sym {β X' k} (βoff k e1)))
      where
      ∧-false' : ∀ b {c} → c ≡ false → (b ∧ c) ≡ false
      ∧-false' true  e = e
      ∧-false' false e = refl

------------------------------------------------------------------------
-- Facts about pasting contexts.

faces-lt : ∀ Γ → PsInv Γ → ∀ w {s t} → facesTy (lookup Γ w) ≡ just (s , t) → T (s <ℕ len Γ) × T (t <ℕ len Γ)
faces-lt Γ inv w e with lookup Γ w in lw
faces-lt Γ inv w () | nothing
faces-lt Γ inv w () | just ⋆
faces-lt Γ inv w () | just (arr ⋆ _ _)
faces-lt Γ inv w e  | just (arr (arr B a b) u v) with inv w _ lw
faces-lt Γ inv w refl | just (arr (arr B a b) _ _) | (i , j , refl , refl , li , lj) =
  lookup-lt Γ i li , lookup-lt Γ j lj

ends-lt : ∀ Γ → PsInv Γ → ∀ w {o o'} → endsL (lookup Γ w) ≡ just (o , o') → T (o <ℕ len Γ) × T (o' <ℕ len Γ)
ends-lt Γ inv w e with lookup Γ w in lw
ends-lt Γ inv w () | nothing
ends-lt Γ inv w e  | just C = go C w lw e
  where
  go : ∀ C w → lookup Γ w ≡ just C → ∀ {o o'} → endsV C ≡ just (o , o') → T (o <ℕ len Γ) × T (o' <ℕ len Γ)
  go ⋆ w lw ()
  go (arr ⋆ u v) w lw e with inv w _ lw
  go (arr ⋆ _ _) w lw refl | (i , j , refl , refl , li , lj) = lookup-lt Γ i li , lookup-lt Γ j lj
  go (arr (arr B a b) u v) w lw e =
    let (i , j , qs , qt , li , lj) = inv w _ lw in go (arr B a b) i li e

lt-ge-neq : ∀ s v n → T (s <ℕ n) → (v <ℕ n) ≡ false → (s ==ℕ v) ≡ false
lt-ge-neq zero    zero    (suc n) _ ()
lt-ge-neq zero    (suc v) (suc n) _ _ = refl
lt-ge-neq (suc s) zero    (suc n) _ _ = refl
lt-ge-neq (suc s) (suc v) (suc n) p q = lt-ge-neq s v n p q

-- A level beyond the context is nobody's face.
hit-big : ∀ Γ → PsInv Γ → ∀ b v w → (v <ℕ len Γ) ≡ false → hitB Γ b v w ≡ false
hit-big Γ inv b v w nv with facesTy (lookup Γ w) in ef
... | nothing      = refl
... | just (s , t) with faces-lt Γ inv w ef
...   | (ls , lt) with b
...     | true  = lt-ge-neq s v (len Γ) ls nv
...     | false = lt-ge-neq t v (len Γ) lt nv

len-not-lt : ∀ n → (n <ℕ n) ≡ false
len-not-lt zero    = refl
len-not-lt (suc n) = len-not-lt n

suc-not-lt : ∀ n → (suc n <ℕ n) ≡ false
suc-not-lt zero    = refl
suc-not-lt (suc n) = suc-not-lt n

any-rng-true : ∀ n (p : Nat → Bool) x → T (x <ℕ n) → p x ≡ true → any p (rng n) ≡ true
any-rng-true (suc n) p x lt px with x ==ℕ n in e
... | true rewrite ==→≡ x n e | any-++ p (rng n) (n ∷ []) | px = ∨-true (any p (rng n))
  where
  ∨-true : ∀ a → (a ∨ true ∨ false) ≡ true
  ∨-true true  = refl
  ∨-true false = refl
... | false rewrite any-++ p (rng n) (n ∷ []) | any-rng-true n p x (lt-pred x n lt e) px = refl

∨-true' : ∀ a → (a ∨ true ∨ false) ≡ true
∨-true' true  = refl
∨-true' false = refl

∨-false : ∀ a → (a ∨ false) ≡ a
∨-false true  = refl
∨-false false = refl

-- v is not the source of any cell.
NotSrc : Ctx → Nat → Set
NotSrc Γ v = ∀ w → T (w <ℕ len Γ) → hitB Γ true v w ≡ false

module Pse (Γ : Ctx) (x : Nat) (A : Ty) (inv : PsInv Γ) (lx : lookup Γ x ≡ just A) where

  y f : Nat
  y = len Γ
  f = suc (len Γ)

  F : Ty
  F = arr A (var x) (var y)

  Γ₁ Γ' : Ctx
  Γ₁ = Γ ▸ A
  Γ' = Γ₁ ▸ F

  x<len : T (x <ℕ len Γ)
  x<len = lookup-lt Γ x lx

  lk-old : ∀ v → T (v <ℕ len Γ) → lookup Γ' v ≡ lookup Γ v
  lk-old v lt = trans (lookup-old Γ₁ F v (<-suc v (len Γ) lt)) (lookup-old Γ A v lt)

  lk-y : lookup Γ' y ≡ just A
  lk-y = trans (lookup-old Γ₁ F y (n<suc y)) (lookup-new Γ A)

  lk-f : lookup Γ' f ≡ just F
  lk-f = lookup-new Γ₁ F

  y-big : (y <ℕ len Γ) ≡ false
  y-big = len-not-lt (len Γ)

  f-big : (f <ℕ len Γ) ≡ false
  f-big = suc-not-lt (len Γ)

  hy hf : Bool → Nat → Bool
  hy b v = hitM b v (facesTy (just A))
  hf b v = hitM b v (facesTy (just F))

  anyOld : Bool → Nat → Bool
  anyOld b v = any (hitB Γ b v) (rng (len Γ))

  any' : ∀ b v → any (hitB Γ' b v) (rng (len Γ')) ≡ (anyOld b v ∨ (hy b v ∨ false)) ∨ (hf b v ∨ false)
  any' b v
    rewrite any-++ (hitB Γ' b v) (rng (len Γ) ++ (y ∷ [])) (f ∷ [])
          | any-++ (hitB Γ' b v) (rng (len Γ)) (y ∷ [])
          | any-rng-ext (len Γ) (hitB Γ' b v) (hitB Γ b v) (λ w lt → cong (λ m → hitM b v (facesTy m)) (lk-old w lt))
          | lk-y | lk-f = refl

  memHom-old : ∀ p i v → T (v <ℕ len Γ) → memHom Γ' p i v ≡ memHom Γ p i v
  memHom-old p i v lt rewrite lk-old v lt = refl

  memHom-y : ∀ p i → memHom Γ' p i y ≡ homM p (endsL (just A)) ∧ (hdimTy (just A) ==ℕ i)
  memHom-y p i rewrite lk-y = refl

  memHom-f : ∀ p i → memHom Γ' p i f ≡ homM p (endsL (just F)) ∧ (hdimTy (just F) ==ℕ i)
  memHom-f p i rewrite lk-f = refl

  sel-old : ∀ p b i v → T (v <ℕ len Γ) →
            sel Γ' p b i v ≡ memHom Γ p i v ∧ not ((anyOld b v ∨ (hy b v ∨ false)) ∨ (hf b v ∨ false))
  sel-old p b i v lt rewrite memHom-old p i v lt | any' b v = refl

  -- New levels are nobody's face in Γ.
  anyOld-y : ∀ b → anyOld b y ≡ false
  anyOld-y b = any-rng-false (len Γ) _ (λ w _ → hit-big Γ inv b y w y-big)

  anyOld-f : ∀ b → anyOld b f ≡ false
  anyOld-f b = any-rng-false (len Γ) _ (λ w _ → hit-big Γ inv b f w f-big)

  hy-y : ∀ b → hy b y ≡ false
  hy-y b = trans (cong (λ m → hitM b y (facesTy m)) (sym lx)) (hit-big Γ inv b y x y-big)

  hy-f : ∀ b → hy b f ≡ false
  hy-f b = trans (cong (λ m → hitM b f (facesTy m)) (sym lx)) (hit-big Γ inv b f x f-big)

  Tb-split : ∀ p b i → Tb Γ' p b i ≈
             map sing (filter (sel Γ' p b i) (rng (len Γ))) ++
             (map sing (filter (sel Γ' p b i) (y ∷ [])) ++ map sing (filter (sel Γ' p b i) (f ∷ [])))
  Tb-split p b i =
    ≈-trans (≡→≈ (trans (cong (map sing) (trans (filter-++ (sel Γ' p b i) (rng (len Γ) ++ (y ∷ [])) (f ∷ []))
                                              (cong (_++ filter (sel Γ' p b i) (f ∷ [])) (filter-++ (sel Γ' p b i) (rng (len Γ)) (y ∷ [])))))
                         (trans (map-++ sing (filter (sel Γ' p b i) (rng (len Γ)) ++ filter (sel Γ' p b i) (y ∷ [])) _)
                                (cong (_++ map sing (filter (sel Γ' p b i) (f ∷ []))) (map-++ sing (filter (sel Γ' p b i) (rng (len Γ))) _)))))
            (++-assoc (map sing (filter (sel Γ' p b i) (rng (len Γ)))) _ _)

  Core-lift : ∀ o o' → Core Γ (o , o') (Tb Γ (o , o')) → Core Γ' (o , o') (Tb Γ (o , o'))
  Core-lift o o' c =
    Core-ext Γ₁ F o o' (Tb Γ (o , o'))
      (λ b k → All-map (Tb Γ (o , o') b k) (λ w bw → basis-ext bw) (Tb-basis Γ o o' b k))
      (Core-ext Γ A o o' (Tb Γ (o , o')) (Tb-basis Γ o o') c)
    where
    basis-ext : ∀ {k w} → Basis Γ o o' k w → Basis Γ₁ o o' k w
    basis-ext {k} {w} (wft , dg) = wft-ext w o wft , trans (deg-ext w wft) dg
      where
      lt-of-ends' : ∀ v {e} → endsL (lookup Γ v) ≡ just e → T (v <ℕ len Γ)
      lt-of-ends' v ev with lookup Γ v in lv
      ... | just _ = lookup-lt Γ v lv
      wft-ext : ∀ w z → WFT Γ z o' w → WFT Γ₁ z o' w
      wft-ext []      z e = e
      wft-ext (v ∷ w) z (z' , ev , r) =
        z' , trans (cong endsL (lookup-old Γ A v (lt-of-ends' v ev))) ev , wft-ext w z' r
      deg-ext : ∀ w {z} → WFT Γ z o' w → deg Γ₁ w ≡ deg Γ w
      deg-ext []      _              = refl
      deg-ext (v ∷ w) (z' , ev , r) =
        cong₂ _+_ (cong hdimTy (lookup-old Γ A v (lt-of-ends' v ev))) (deg-ext w r)

∧-true : ∀ a → (a ∧ true) ≡ a
∧-true true  = refl
∧-true false = refl

∧-false : ∀ a → (a ∧ false) ≡ false
∧-false true  = refl
∧-false false = refl

filter-none : ∀ n (p : Nat → Bool) → (∀ v → T (v <ℕ n) → p v ≡ false) → filter p (rng n) ≡ []
filter-none n p h = trans (filter-rng-ext n p (λ _ → false) h) (lem n)
  where
  lem : ∀ n → filter (λ _ → false) (rng n) ≡ []
  lem zero    = refl
  lem (suc n) = trans (filter-++ (λ _ → false) (rng n) (n ∷ [])) (trans (cong (_++ []) (lem n)) refl)

-- pse at an object: a new object y and a new hom x → y holding f.
module PseStar (Γ : Ctx) (x : Nat) (inv : PsInv Γ) (lx : lookup Γ x ≡ just ⋆) where
  open Pse Γ x ⋆ inv lx public

  sel-same : ∀ p b i v → T (v <ℕ len Γ) → sel Γ' p b i v ≡ sel Γ p b i v
  sel-same p b i v lt rewrite sel-old p b i v lt | ∨-false (anyOld b v) | ∨-false (anyOld b v) = refl

  part-y : ∀ p b i → filter (sel Γ' p b i) (y ∷ []) ≡ []
  part-y p b i rewrite memHom-y p i = refl

  sel-f : ∀ p b i → sel Γ' p b i f ≡ homM p (just (x , y)) ∧ (0 ==ℕ i)
  sel-f p b i rewrite memHom-f p i | any' b f | anyOld-f b = ∧-true _

  Tb-old : ∀ o o' → T (o' <ℕ len Γ) → ∀ b i → Tb Γ' (o , o') b i ≈ Tb Γ (o , o') b i
  Tb-old o o' lt b i =
    ≈-trans (Tb-split (o , o') b i)
   (≡→≈ (trans (cong₂ (λ P Q → map sing P ++ (map sing Q ++ map sing (filter (sel Γ' (o , o') b i) (f ∷ []))))
                       (filter-rng-ext (len Γ) _ _ (sel-same (o , o') b i)) (part-y (o , o') b i))
         (trans (cong (λ c → map sing (filter (sel Γ (o , o') b i) (rng (len Γ))) ++ map sing (if c then f ∷ [] else []))
                      (trans (sel-f (o , o') b i) (cong (λ c → ((x ==ℕ o) ∧ c) ∧ (0 ==ℕ i)) (y≠o'))))
                (trans (cong (λ c → map sing (filter (sel Γ (o , o') b i) (rng (len Γ))) ++ map sing (if c then f ∷ [] else []))
                             (∧-false' (x ==ℕ o) (0 ==ℕ i)))
                       (++-[]L _)))))
    where
    y≠o' : (y ==ℕ o') ≡ false
    y≠o' = trans (==-sym y o') (lt-ge-neq o' y (len Γ) lt y-big)
    ∧-false' : ∀ a c → ((a ∧ false) ∧ c) ≡ false
    ∧-false' true  c = refl
    ∧-false' false c = refl

  U : Tab
  U b zero    = sing f ∷ []
  U b (suc i) = []

  Tb-new : ∀ b i → Tb Γ' (x , y) b i ≈ U b i
  Tb-new b i =
    ≈-trans (Tb-split (x , y) b i)
   (≡→≈ (trans (cong₂ (λ P Q → map sing P ++ (map sing Q ++ map sing (filter (sel Γ' (x , y) b i) (f ∷ []))))
                       (trans (filter-rng-ext (len Γ) _ _ (sel-same (x , y) b i))
                              (filter-none (len Γ) _ (λ v lt → old-not v lt)))
                       (part-y (x , y) b i))
         (cong (λ c → map sing (if c then f ∷ [] else []))
               (trans (sel-f (x , y) b i) (trans (cong (λ c → (c ∧ (y ==ℕ y)) ∧ (0 ==ℕ i)) (==-true x))
                                                 (cong (λ c → (true ∧ c) ∧ (0 ==ℕ i)) (==-true y)))))) ∘≈ fin i)
    where
    _∘≈_ : ∀ {A B C : Bag} → A ≈ B → B ≈ C → A ≈ C
    _∘≈_ = ≈-trans
    fin : ∀ i → map sing (if (0 ==ℕ i) then f ∷ [] else []) ≈ U b i
    fin zero    = ≈-refl
    fin (suc i) = ≈-refl
    old-not : ∀ v → T (v <ℕ len Γ) → sel Γ (x , y) b i v ≡ false
    old-not v lt with endsL (lookup Γ v) in ev
    ... | nothing      = refl
    ... | just (s , t) rewrite lt-ge-neq t y (len Γ) (snd (ends-lt Γ inv v ev)) y-big
                             | ∧-false (s ==ℕ x) = refl

  U-core : Core Γ' (x , y) U
  U-core = (λ b → sing f , ≈-refl) , ch
    where
    ch : ∀ b k → δ Γ' (U b (suc k)) ~ β U k
    ch b zero    = mk~ ≈-refl
    ch b (suc k) = mk~ ≈-refl

  core-new : Core Γ' (x , y) (Tb Γ' (x , y))
  core-new = Core-≈ Γ' (x , y) U (Tb Γ' (x , y)) (λ b i → ≈-sym (Tb-new b i)) U-core

  core-old : ∀ o o' → T (o' <ℕ len Γ) → Core Γ (o , o') (Tb Γ (o , o')) → Core Γ' (o , o') (Tb Γ' (o , o'))
  core-old o o' lt c =
    Core-≈ Γ' (o , o') (Tb Γ (o , o')) (Tb Γ' (o , o')) (λ b i → ≈-sym (Tb-old o o' lt b i)) (Core-lift o o' c)

-- pse at a cell x of a hom: y ∥ x and f : x → y join x's hom.
module PseArr (Γ : Ctx) (x : Nat) (B : Ty) (a c : Nat) (inv : PsInv Γ)
              (lx : lookup Γ x ≡ just (arr B (var a) (var c))) (nsx : NotSrc Γ x) where
  open Pse Γ x (arr B (var a) (var c)) inv lx public

  d : Nat
  d = dim B

  hA : Nat × Nat → Bool
  hA p = homM p (endsV (arr B (var a) (var c)))

  absorb : ∀ b v → (anyOld b v ∨ (hy b v ∨ false)) ≡ anyOld b v
  absorb b v with hitB Γ b v x in eh
  ... | true rewrite any-rng-true (len Γ) (hitB Γ b v) x x<len eh = refl
  ... | false rewrite trans (cong (λ m → hitM b v (facesTy m)) (sym lx)) eh = ∨-false (anyOld b v)

  sel-old' : ∀ p b i v → T (v <ℕ len Γ) →
             sel Γ' p b i v ≡ memHom Γ p i v ∧ not (anyOld b v ∨ (((if b then x else y) ==ℕ v) ∨ false))
  sel-old' p b i v lt rewrite sel-old p b i v lt | absorb b v = refl

  memHom-x : ∀ p i → memHom Γ p i x ≡ hA p ∧ (d ==ℕ i)
  memHom-x p i rewrite lx = refl

  v≠y : ∀ v → T (v <ℕ len Γ) → (y ==ℕ v) ≡ false
  v≠y v lt = trans (==-sym y v) (lt-ge-neq v y (len Γ) lt y-big)

  -- Old levels keep their status, except x on the + side.
  sel-keep : ∀ p b i v → T (v <ℕ len Γ) → ((b ∧ (x ==ℕ v)) ≡ false) → sel Γ' p b i v ≡ sel Γ p b i v
  sel-keep p false i v lt _ rewrite sel-old' p false i v lt | v≠y v lt | ∨-false (anyOld false v) = refl
  sel-keep p true  i v lt e rewrite sel-old' p true i v lt | e | ∨-false (anyOld true v) = refl

  sel-x : ∀ p i → sel Γ' p true i x ≡ false
  sel-x p i rewrite sel-old' p true i x x<len | ==-true x | ∨-true' (anyOld true x) = ∧-false (memHom Γ p i x)

  sel-x-old : ∀ p i → sel Γ p true i x ≡ hA p ∧ (d ==ℕ i)
  sel-x-old p i rewrite memHom-x p i | any-rng-false (len Γ) (hitB Γ true x) nsx = ∧-true _

  sel-y : ∀ p b i → sel Γ' p b i y ≡ (hA p ∧ (d ==ℕ i)) ∧ b
  sel-y p b i rewrite memHom-y p i | any' b y | anyOld-y b | hy-y b with b
  ... | true  rewrite lt-ge-neq x y (len Γ) x<len y-big = refl
  ... | false rewrite ==-true y = refl

  sel-f : ∀ p b i → sel Γ' p b i f ≡ hA p ∧ (suc d ==ℕ i)
  sel-f p b i rewrite memHom-f p i | any' b f | anyOld-f b | hy-f b with b
  ... | true  rewrite lt-ge-neq x f (len Γ) x<len f-big = ∧-true _
  ... | false rewrite ==-suc-self (len Γ) = ∧-true _

  part : ∀ (q : Nat → Bool) v → q v ≡ false → filter q (v ∷ []) ≡ []
  part q v e rewrite e = refl

  -- Homs other than x's are unchanged.
  Tb-other : ∀ p → hA p ≡ false → ∀ b i → Tb Γ' p b i ≈ Tb Γ p b i
  Tb-other p ha b i =
    ≈-trans (Tb-split p b i)
   (≡→≈ (trans (cong₂ (λ P Q → map sing P ++ (map sing Q ++ map sing (filter (sel Γ' p b i) (f ∷ []))))
                       (filter-rng-ext (len Γ) _ _ keep)
                       (part (sel Γ' p b i) y (trans (sel-y p b i) (cong (λ h → (h ∧ (d ==ℕ i)) ∧ b) ha))))
         (trans (cong (λ Q → map sing (filter (sel Γ p b i) (rng (len Γ))) ++ map sing Q)
                      (part (sel Γ' p b i) f (trans (sel-f p b i) (cong (λ h → h ∧ (suc d ==ℕ i)) ha))))
                (++-[]L _))))
    where
    keep : ∀ v → T (v <ℕ len Γ) → sel Γ' p b i v ≡ sel Γ p b i v
    keep v lt = keep' b v lt
      where
      keep' : ∀ b v → T (v <ℕ len Γ) → sel Γ' p b i v ≡ sel Γ p b i v
      keep' false v lt = sel-keep p false i v lt refl
      keep' true  v lt with x ==ℕ v in e
      ... | false = sel-keep p true i v lt e
      ... | true rewrite sym (==ℕ-sound x v (subst T (sym e) tt)) | sel-x p i
                       | trans (sel-x-old p i) (cong (λ h → h ∧ (d ==ℕ i)) ha) = refl

  filter-1 : ∀ (q : Nat → Bool) v → filter q (v ∷ []) ≡ (if q v then v ∷ [] else [])
  filter-1 q v with q v
  ... | true  = refl
  ... | false = refl

  -- x's hom: the step of `Step`.
  core-x : ∀ o o' → hA (o , o') ≡ true → Core Γ (o , o') (Tb Γ (o , o')) → Core Γ' (o , o') (Tb Γ' (o , o'))
  core-x o o' ha c = core-step (Core-lift o o' c) S1 S2a S2b Sx Sf
    where
    p = (o , o')
    R : Bag
    R = map sing (filter (sel Γ' p true d) (rng (len Γ)))
    open Step Γ' p (Tb Γ p) (Tb Γ' p) d x y f R

    keep : ∀ b i → (b ∧ (i ==ℕ d)) ≡ false → ∀ v → T (v <ℕ len Γ) → sel Γ' p b i v ≡ sel Γ p b i v
    keep false i e v lt = sel-keep p false i v lt refl
    keep true  i e v lt with x ==ℕ v in ex
    ... | false = sel-keep p true i v lt ex
    ... | true rewrite sym (==ℕ-sound x v (subst T (sym ex) tt)) | sel-x p i | sel-x-old p i | ha
                     | ==-sym d i | e = refl

    S1 : ∀ b i → (b ∧ (i ==ℕ d)) ≡ false → Tb Γ' p b i ≈ Tb Γ p b i ++ Ef i
    S1 b i e =
      ≈-trans (Tb-split p b i)
     (≡→≈ (trans (cong₂ (λ P Q → map sing P ++ (map sing Q ++ map sing (filter (sel Γ' p b i) (f ∷ []))))
                         (filter-rng-ext (len Γ) _ _ (keep b i e)) (trans (filter-1 (sel Γ' p b i) y) (cong (λ c → if c then y ∷ [] else []) (yoff b e))))
           (cong (λ Q → map sing (filter (sel Γ p b i) (rng (len Γ))) ++ Q)
                 (trans (cong (map sing) (filter-1 (sel Γ' p b i) f))
                        (cong (λ c → map sing (if c then f ∷ [] else []))
                              (trans (sel-f p b i) (trans (cong (_∧ (suc d ==ℕ i)) ha) (==-sym (suc d) i))))))))
      ∙≈ fixEf i
      where
      _∙≈_ : ∀ {P Q W : Bag} → P ≈ Q → Q ≈ W → P ≈ W
      _∙≈_ = ≈-trans
      yoff : ∀ b → (b ∧ (i ==ℕ d)) ≡ false → sel Γ' p b i y ≡ false
      yoff false _ rewrite sel-y p false i = ∧-false _
      yoff true  e rewrite sel-y p true i | ha | ==-sym d i | e = refl
      fixEf : ∀ i → map sing (filter (sel Γ p b i) (rng (len Γ))) ++ map sing (if i ==ℕ suc d then f ∷ [] else []) ≈ Tb Γ p b i ++ Ef i
      fixEf i with i ==ℕ suc d
      ... | true  = ≈-refl
      ... | false = ≈-refl

    S2a : Tb Γ p true d ≈ R ++ (sing x ∷ [])
    S2a = filter-drop (len Γ) (sel Γ p true d) (sel Γ' p true d) x x<len
            (trans (sel-x-old p d) (trans (cong (_∧ (d ==ℕ d)) ha) (==-true d)))
            (sel-x p d)
            (λ v lt ne → sym (sel-keep p true d v lt (trans (==-sym x v) ne)))

    S2b : Tb Γ' p true d ≈ R ++ (sing y ∷ [])
    S2b =
      ≈-trans (Tb-split p true d)
     (≡→≈ (cong (R ++_)
       (trans (cong₂ (λ P Q → map sing P ++ map sing Q) (filter-1 (sel Γ' p true d) y) (filter-1 (sel Γ' p true d) f))
              (cong₂ (λ c c' → map sing (if c then y ∷ [] else []) ++ map sing (if c' then f ∷ [] else []))
                     (trans (sel-y p true d) (trans (cong (λ h → (h ∧ (d ==ℕ d)) ∧ true) ha) (cong (λ c → c ∧ true) (==-true d))))
                     (trans (sel-f p true d) (trans (cong (_∧ (suc d ==ℕ d)) ha) (suc-==-self d)))))))

    ∂x≡∂y : ∀ b → ∂T Γ' b (x ∷ []) ≡ ∂T Γ' b (y ∷ [])
    ∂x≡∂y b = cong (λ m → here b (facesTy m) [] ++ []) (trans (lk-old x x<len) (trans lx (sym lk-y)))

    Sx : δ Γ' (sing x ∷ []) ~ δ Γ' (sing y ∷ [])
    Sx = ≈d (≡→≈ (cong (_++ []) (∂x≡∂y true))) (≡→≈ (cong (_++ []) (∂x≡∂y false)))

    ∂f : ∀ b → ∂T Γ' b (f ∷ []) ≡ (((if b then y else x) ∷ []) ∷ [])
    ∂f b rewrite lk-f = refl

    Sf : δ Γ' (sing f ∷ []) ~ ((sing y ∷ []) , (sing x ∷ []))
    Sf = ≈d (≡→≈ (cong (_++ []) (∂f true))) (≡→≈ (cong (_++ []) (∂f false)))

  core-step' : ∀ o o' → Core Γ (o , o') (Tb Γ (o , o')) → Core Γ' (o , o') (Tb Γ' (o , o'))
  core-step' o o' c with hA (o , o') in ha
  ... | true  = core-x o o' ha c
  ... | false = Core-≈ Γ' (o , o') (Tb Γ (o , o')) (Tb Γ' (o , o'))
                  (λ b i → ≈-sym (Tb-other (o , o') ha b i)) (Core-lift o o' c)

------------------------------------------------------------------------
-- Objects and their consecutive pairs.

isStarM : Maybe Ty → Bool
isStarM (just ⋆) = true
isStarM _        = false

objL : Ctx → List Nat
objL Γ = filter (λ v → isStarM (lookup Γ v)) (rng (len Γ))

pairs : List Nat → List (Nat × Nat)
pairs []           = []
pairs (o ∷ [])     = []
pairs (o ∷ o' ∷ os) = (o , o') ∷ pairs (o' ∷ os)

data AllL {A : Set} (P : A → Set) : List A → Set where
  []ᴬ  : AllL P []
  _∷ᴬ_ : ∀ {x xs} → P x → AllL P xs → AllL P (x ∷ xs)

data _∈_ {A : Set} (a : A) : List A → Set where
  hd∈  : ∀ {xs} → a ∈ (a ∷ xs)
  tl∈ : ∀ {x xs} → a ∈ xs → a ∈ (x ∷ xs)

AllL-++ : ∀ {A : Set} {P : A → Set} xs ys → AllL P xs → AllL P ys → AllL P (xs ++ ys)
AllL-++ []       ys []ᴬ       q = q
AllL-++ (x ∷ xs) ys (p ∷ᴬ rs) q = p ∷ᴬ AllL-++ xs ys rs q

AllL-map : ∀ {A : Set} {P Q : A → Set} xs → (∀ x → P x → Q x) → AllL P xs → AllL Q xs
AllL-map []       f []ᴬ       = []ᴬ
AllL-map (x ∷ xs) f (p ∷ᴬ rs) = f x p ∷ᴬ AllL-map xs f rs

∈-++ˡ : ∀ {A : Set} {a : A} xs ys → a ∈ xs → a ∈ (xs ++ ys)
∈-++ˡ (x ∷ xs) ys hd∈      = hd∈
∈-++ˡ (x ∷ xs) ys (tl∈ m) = tl∈ (∈-++ˡ xs ys m)

∈-++ʳ : ∀ {A : Set} {a : A} xs ys → a ∈ ys → a ∈ (xs ++ ys)
∈-++ʳ []       ys m = m
∈-++ʳ (x ∷ xs) ys m = tl∈ (∈-++ʳ xs ys m)

lastO' : List Nat → Nat
lastO' = lastL

pairs-snoc : ∀ o os y → pairs ((o ∷ os) ++ (y ∷ [])) ≡ pairs (o ∷ os) ++ ((lastL (o ∷ os) , y) ∷ [])
pairs-snoc o []        y = refl
pairs-snoc o (o' ∷ os) y = cong ((o , o') ∷_) (pairs-snoc o' os y)

lastL-snoc : ∀ os y → lastL (os ++ (y ∷ [])) ≡ y
lastL-snoc []            y = refl
lastL-snoc (o ∷ [])      y = refl
lastL-snoc (o ∷ o' ∷ os) y = lastL-snoc (o' ∷ os) y

rng-lt : ∀ n → AllL (λ v → T (v <ℕ n)) (rng n)
rng-lt zero    = []ᴬ
rng-lt (suc n) = AllL-++ (rng n) (n ∷ []) (AllL-map (rng n) (λ v lt → <-suc v n lt) (rng-lt n)) (n<suc n ∷ᴬ []ᴬ)

filter-AllL : ∀ {P : Nat → Set} (q : Nat → Bool) xs → AllL P xs → AllL P (filter q xs)
filter-AllL q []       []ᴬ       = []ᴬ
filter-AllL q (x ∷ xs) (p ∷ᴬ rs) with q x
... | true  = p ∷ᴬ filter-AllL q xs rs
... | false = filter-AllL q xs rs

pairs-AllL : ∀ {P : Nat → Set} os → AllL P os → AllL (λ e → P (snd e)) (pairs os)
pairs-AllL []            _                    = []ᴬ
pairs-AllL (o ∷ [])      _                    = []ᴬ
pairs-AllL (o ∷ o' ∷ os) (p ∷ᴬ (p' ∷ᴬ rs)) = p' ∷ᴬ pairs-AllL (o' ∷ os) (p' ∷ᴬ rs)

objL-lt : ∀ Γ → AllL (λ e → T (snd e <ℕ len Γ)) (pairs (objL Γ))
objL-lt Γ = pairs-AllL (objL Γ) (filter-AllL _ (rng (len Γ)) (rng-lt (len Γ)))

AllL-zip : ∀ {A : Set} {P Q R : A → Set} xs → AllL P xs → AllL Q xs → (∀ x → P x → Q x → R x) → AllL R xs
AllL-zip []       []ᴬ       []ᴬ       f = []ᴬ
AllL-zip (x ∷ xs) (p ∷ᴬ rs) (q ∷ᴬ qs) f = f x p q ∷ᴬ AllL-zip xs rs qs f

∈-pairs-snoc : ∀ {e} o os y → e ∈ pairs (o ∷ os) → e ∈ pairs ((o ∷ os) ++ (y ∷ []))
∈-pairs-snoc o os y m rewrite pairs-snoc o os y = ∈-++ˡ (pairs (o ∷ os)) _ m

-- The object a pasting cursor ends at.
objEndArr : Ty → Maybe Nat
objEndArr (arr ⋆ s (var b))          = just b
objEndArr (arr (arr B s' t') s t)    = objEndArr (arr B s' t')
objEndArr _                          = nothing

objEnd : Nat → Ty → Maybe Nat
objEnd x ⋆           = just x
objEnd x (arr A s t) = objEndArr (arr A s t)

TgtChain : Ctx → Ty → Set
TgtChain Γ ⋆                 = ⊤
TgtChain Γ (arr B s (var c)) = NotSrc Γ c × (lookup Γ c ≡ just B) × TgtChain Γ B
TgtChain Γ (arr B s _)       = ⊥

NonEmpty : List Nat → Set
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = ⊤

record Inv (Γ : Ctx) (x : Nat) (A : Ty) : Set where
  field
    cores  : AllL (λ p → Core Γ p (Tb Γ p)) (pairs (objL Γ))
    nsx    : NotSrc Γ x
    tch    : TgtChain Γ A
    lastOK : objEnd x A ≡ just (lastL (objL Γ))
    ne     : NonEmpty (objL Γ)
    homsOK : ∀ v {e} → endsL (lookup Γ v) ≡ just e → e ∈ pairs (objL Γ)

private
  cases3 : ∀ (P : Nat → Set) n w → T (w <ℕ suc (suc n)) →
           (∀ w → T (w <ℕ n) → P w) → P n → P (suc n) → P w
  cases3 P n w lt old pn psn with w ==ℕ suc n in e1
  ... | true rewrite ==→≡ w (suc n) e1 = psn
  ... | false with w ==ℕ n in e2
  ...   | true rewrite ==→≡ w n e2 = pn
  ...   | false = old w (lt-pred w n (lt-pred w (suc n) lt e1) e2)

  ⊥-true : true ≡ false → ⊥
  ⊥-true ()

module PseCommon (Γ : Ctx) (x : Nat) (A : Ty) (inv : PsInv Γ) (lx : lookup Γ x ≡ just A) where
  open Pse Γ x A inv lx

  notsrc-new : ∀ v → (∀ w → T (w <ℕ len Γ) → hitB Γ true v w ≡ false) →
               hitM true v (facesTy (just A)) ≡ false → hitM true v (facesTy (just F)) ≡ false → NotSrc Γ' v
  notsrc-new v old hy0 hf0 w lt =
    cases3 (λ w → hitB Γ' true v w ≡ false) (len Γ) w lt
      (λ w lt' → trans (cong (λ m → hitM true v (facesTy m)) (lk-old w lt')) (old w lt'))
      (trans (cong (λ m → hitM true v (facesTy m)) lk-y) hy0)
      (trans (cong (λ m → hitM true v (facesTy m)) lk-f) hf0)

  objL' : objL Γ' ≡ objL Γ ++ (if isStarM (just A) then y ∷ [] else [])
  objL' =
    trans (filter-++ q (rng (len Γ) ++ (y ∷ [])) (f ∷ []))
   (trans (cong₂ _++_ (filter-++ q (rng (len Γ)) (y ∷ [])) (cong (λ m → if isStarM m then f ∷ [] else []) lk-f))
   (trans (++-[]L _)
          (cong₂ _++_ (filter-rng-ext (len Γ) q _ (λ v lt → cong isStarM (lk-old v lt)))
                      (cong (λ m → if isStarM m then y ∷ [] else []) lk-y))))
    where
    q : Nat → Bool
    q v = isStarM (lookup Γ' v)

  homs-new : ∀ v {e} → endsL (lookup Γ' v) ≡ just e →
             (∀ v {e} → endsL (lookup Γ v) ≡ just e → e ∈ pairs (objL Γ')) →
             (∀ {e} → endsL (just A) ≡ just e → e ∈ pairs (objL Γ')) →
             (∀ {e} → endsL (just F) ≡ just e → e ∈ pairs (objL Γ')) →
             e ∈ pairs (objL Γ')
  homs-new v {e} ev old hyA hfF with lookup Γ' v in lv
  ... | just C =
    cases3 (λ v → lookup Γ' v ≡ just C → e ∈ pairs (objL Γ')) (len Γ) v (lookup-lt Γ' v lv)
      (λ w lt' lw → old w (trans (cong endsL (trans (sym (lk-old w lt')) lw)) ev))
      (λ lw → hyA (trans (cong endsL (trans (sym lk-y) lw)) ev))
      (λ lw → hfF (trans (cong endsL (trans (sym lk-f) lw)) ev))
      lv

module InvStar (Γ : Ctx) (x : Nat) (inv : PsInv Γ) (lx : lookup Γ x ≡ just ⋆) (I : Inv Γ x ⋆) where
  open PseStar Γ x inv lx
  open PseCommon Γ x ⋆ inv lx
  open Inv I

  os = objL Γ

  objL'' : objL Γ' ≡ os ++ (y ∷ [])
  objL'' = objL'

  x-last : x ≡ lastL os
  x-last = just-inj lastOK

  inv' : Inv Γ' f F
  inv' = record
    { cores  = subst (λ l → AllL (λ p → Core Γ' p (Tb Γ' p)) (pairs l)) (sym objL'') cores'
    ; nsx    = notsrc-new f (λ w lt → hit-big Γ inv true f w f-big) refl refl
    ; tch    = notsrc-new y (λ w lt → hit-big Γ inv true y w y-big) refl refl , lk-y , tt
    ; lastOK = cong just (sym (trans (cong lastL objL'') (lastL-snoc os y)))
    ; ne     = subst NonEmpty (sym objL'') (ne-snoc os)
    ; homsOK = λ v ev → homs-new v ev
                 (λ w ew → subst (λ l → _ ∈ pairs l) (sym objL'') (old∈ w ew))
                 (λ ())
                 (λ { refl → subst (λ l → (x , y) ∈ pairs l) (sym objL'') new∈ })
    }
    where
    ne-snoc : ∀ l → NonEmpty (l ++ (y ∷ []))
    ne-snoc []      = tt
    ne-snoc (_ ∷ _) = tt
    snocP : ∀ l → NonEmpty l → pairs (l ++ (y ∷ [])) ≡ pairs l ++ ((lastL l , y) ∷ [])
    snocP (o ∷ l) _ = pairs-snoc o l y
    cores' : AllL (λ p → Core Γ' p (Tb Γ' p)) (pairs (os ++ (y ∷ [])))
    cores' = subst (AllL (λ p → Core Γ' p (Tb Γ' p))) (sym (snocP os ne))
               (AllL-++ (pairs os) _
                  (AllL-zip (pairs os) cores (objL-lt Γ) (λ { (o , o') c lt → core-old o o' lt c }))
                  (subst (λ z → Core Γ' (z , y) (Tb Γ' (z , y))) x-last core-new ∷ᴬ []ᴬ))
    old∈ : ∀ w {e} → endsL (lookup Γ w) ≡ just e → e ∈ pairs (os ++ (y ∷ []))
    old∈ w ew = subst (λ l → _ ∈ l) (sym (snocP os ne)) (∈-++ˡ (pairs os) _ (homsOK w ew))
    new∈ : (x , y) ∈ pairs (os ++ (y ∷ []))
    new∈ = subst (λ l → (x , y) ∈ l) (sym (snocP os ne))
             (∈-++ʳ (pairs os) _ (subst (λ z → (x , y) ∈ ((z , y) ∷ [])) x-last hd∈))

module InvArr (Γ : Ctx) (x : Nat) (B : Ty) (a c : Nat) (inv : PsInv Γ)
              (lx : lookup Γ x ≡ just (arr B (var a) (var c))) (I : Inv Γ x (arr B (var a) (var c))) where
  open Inv I
  open PseArr Γ x B a c inv lx nsx
  open PseCommon Γ x (arr B (var a) (var c)) inv lx

  objL-same : objL Γ' ≡ objL Γ
  objL-same = trans objL' (++-[]L (objL Γ))

  m+suc≢m : ∀ m n → m + suc n ≡ m → ⊥
  m+suc≢m zero    n ()
  m+suc≢m (suc m) n e = m+suc≢m m n (suc-inj e)
    where
    suc-inj : ∀ {p q} → suc p ≡ suc q → p ≡ q
    suc-inj refl = refl

  A = arr B (var a) (var c)

  -- A cell of a lower dimension than x is not x.
  not-x : ∀ c' C n → dim C + suc n ≡ dim A → lookup Γ c' ≡ just C → (x ==ℕ c') ≡ false
  not-x c' C n e lc with x ==ℕ c' in ex
  ... | false = refl
  ... | true rewrite sym (==ℕ-sound x c' (subst T (sym ex) tt)) =
    ⊥-elim (m+suc≢m (dim A) n (subst (λ D → dim D + suc n ≡ dim A) (just-inj (trans (sym lc) lx)) e))

  tchExt : ∀ A' n → dim A' + n ≡ dim A → TgtChain Γ A' → TgtChain Γ' A'
  tchExt ⋆ n e _ = tt
  tchExt (arr B' s' (var c')) n e (nsc , lc' , rest) =
    notsrc-new c' (λ w lt → nsc w lt)
      (trans (cong (λ m → hitM true c' (facesTy m)) (sym lx)) (nsc x x<len))
      (not-x c' B' n (trans (+-suc (dim B') n) e) lc') ,
    trans (lk-old c' (lookup-lt Γ c' lc')) lc' ,
    tchExt B' (suc n) (trans (+-suc (dim B') n) e) rest
  tchExt (arr B' s' (coh _ _ _)) n e ()
  tchExt (arr B' s' (cst _)) n e ()

  inv' : Inv Γ' f F
  inv' = record
    { cores  = subst (λ l → AllL (λ p → Core Γ' p (Tb Γ' p)) (pairs l)) (sym objL-same)
                 (AllL-map (pairs (objL Γ)) (λ { (o , o') cr → core-step' o o' cr }) cores)
    ; nsx    = notsrc-new f (λ w lt → hit-big Γ inv true f w f-big) (hy-f true) (lt-ge-neq x f (len Γ) x<len f-big)
    ; tch    = notsrc-new y (λ w lt → hit-big Γ inv true y w y-big) (hy-y true) (lt-ge-neq x y (len Γ) x<len y-big) ,
               lk-y , tchExt A 0 (+-zero (dim A)) tch
    ; lastOK = trans lastOK (cong (λ l → just (lastL l)) (sym objL-same))
    ; ne     = subst NonEmpty (sym objL-same) ne
    ; homsOK = λ v ev → homs-new v ev
                 (λ w ew → subst (λ l → _ ∈ pairs l) (sym objL-same) (homsOK w ew))
                 (λ ey → subst (λ l → _ ∈ pairs l) (sym objL-same) (homsOK x (trans (cong endsL lx) ey)))
                 (λ ef → subst (λ l → _ ∈ pairs l) (sym objL-same) (homsOK x (trans (cong endsL lx) ef)))
    }

------------------------------------------------------------------------
-- The induction.

inv-ps : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Inv Γ x A
inv-ps pss = record
  { cores = []ᴬ ; nsx = ns ; tch = tt ; lastOK = refl ; ne = tt ; homsOK = hm }
  where
  ns : NotSrc (ε ▸ ⋆) 0
  ns zero    _  = refl
  ns (suc w) ()
  hm : ∀ v {e} → endsL (lookup (ε ▸ ⋆) v) ≡ just e → e ∈ pairs (objL (ε ▸ ⋆))
  hm zero    ()
  hm (suc v) ()
inv-ps (psd {Γ} {f} {A} {x} {y} d) = record
  { cores = cores ; nsx = fst tch ; tch = snd (snd tch) ; lastOK = trans (end A) lastOK ; ne = ne ; homsOK = homsOK }
  where
  open Inv (inv-ps d)
  end : ∀ A → objEnd y A ≡ objEnd f (arr A (var x) (var y))
  end ⋆           = refl
  end (arr _ _ _) = refl
inv-ps (pse {Γ} {x} {⋆} d) = InvStar.inv' Γ x (fst (ps-inv d)) (snd (ps-inv d)) (inv-ps d)
inv-ps (pse {Γ} {x} {arr B s t} d) with fst (ps-inv d) x _ (snd (ps-inv d))
... | (a , c , refl , refl , _ , _) = InvArr.inv' Γ x B a c (fst (ps-inv d)) (snd (ps-inv d)) (inv-ps d)

-- Every hom of a pasting context has a cell as its table (Core part).
hom-cores : ∀ {Γ} → Γ ⊢ps → AllL (λ p → Core Γ p (Tb Γ p)) (pairs (objL Γ))
hom-cores (ps d) = Inv.cores (inv-ps d)

-- Every hom cell lies between consecutive objects.
hom-ends : ∀ {Γ} → Γ ⊢ps → ∀ v {e} → endsL (lookup Γ v) ≡ just e → e ∈ pairs (objL Γ)
hom-ends (ps d) = Inv.homsOK (inv-ps d)
