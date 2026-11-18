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
