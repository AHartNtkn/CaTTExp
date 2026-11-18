------------------------------------------------------------------------
-- The table of each hom of a pasting context is a cell.
--
-- For a pasting context Γ and objects o, o', the hom table
--     Tb Γ (o , o') b i = { v | v a cell of the hom o → o' of hom
--                               dimension i, not the target (b = −)
--                               resp. source (b = +) of any cell }
-- is the composite ⟨Θ⟩ of the hom's pasting diagram Θ. We prove, by
-- induction on the pasting derivation, that it is a cell of ν(K(Γ))
-- between o and o' (`hom-cells`). Each pse step adds y : A and
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
