------------------------------------------------------------------------
-- The labels of the tree of a pasting context and of its boundaries
-- (ledger item A3a, general case).
--
-- Reading the labels of a tree in the order x₀, x₁, labels of T₁, x₂,
-- … (`flat`), the pair y : A, f : x → y appends y and f. So the labels
-- of the truncations of tr Γ follow exactly the recursions that define
-- ∂⁻ᵢ and ∂⁺ᵢ in CaTTExp.Syntax:
--
--     flat (bdm i (tr Γ)) ≡ srcVars i Γ,   flat (bdp i (tr Γ)) ≡ tgtVars i Γ,
--
-- and flat (tr Γ) lists the variables 0, …, len Γ − 1. Also proved:
-- tr Γ has height at most dim Γ, and it is well typed (CaTTExp.Strict.
-- FreeTV).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega using (ωCat; _≤_; _<_; z≤n; s≤s; ≤-refl; ≤-suc; ≤-trans)

module CaTTExp.Strict.TrFlat (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree 𝕊
open import CaTTExp.Strict.LabelSets
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd; ps-facts; ord; dang; lookup-top; lookup-wk; lookup-<; ==→≡)
open import CaTTExp.Strict.GenericEnv 𝕊 using (𝒯)
open import CaTTExp.Strict.FreeTV 𝕊 using (TV; TVB; lastv-ty; tvB-++)
open import CaTTExp.Strict.TreeCat Nat using (bdmB-++; bdpB-++; lastv-bdmB; lastv-bdpB)

private
  lastv-++1 : ∀ {A : Set} (s : A) br T y → lastv s (br ++B cons T y nil) ≡ y
  lastv-++1 s nil          T y = refl
  lastv-++1 s (cons U z r) T y = lastv-++1 z r T y

  lastv-insLast : ∀ {A : Set} n (y f s : A) br → lastv s (insLast n y f br) ≡ lastv s br
  lastv-insLast n y f s nil                       = refl
  lastv-insLast n y f s (cons T z nil)            = refl
  lastv-insLast n y f s (cons T z (cons T′ z′ r)) = lastv-insLast n y f z (cons T′ z′ r)

  bdm-leaf : ∀ i (f : Nat) → bdm i (node f nil) ≡ node f nil
  bdm-leaf zero    f = refl
  bdm-leaf (suc i) f = refl

  bdp-leaf : ∀ i (f : Nat) → bdp i (node f nil) ≡ node f nil
  bdp-leaf zero    f = refl
  bdp-leaf (suc i) f = refl

------------------------------------------------------------------------
-- Truncating after inserting.

mutual
  bdm-ins-hi : ∀ i n (y f : Nat) (T : LT Nat) → i ≤ n → bdm i (insert n y f T) ≡ bdm i T
  bdm-ins-hi zero    zero    y f (node s br) _       = refl
  bdm-ins-hi zero    (suc n) y f (node s br) _       = refl
  bdm-ins-hi (suc i) (suc n) y f (node s br) (s≤s l) = cong (node s) (bdmB-ins-hi i n y f br l)

  bdmB-ins-hi : ∀ i n (y f : Nat) (br : Br Nat) → i ≤ n → bdmB i (insLast n y f br) ≡ bdmB i br
  bdmB-ins-hi i n y f nil                       l = refl
  bdmB-ins-hi i n y f (cons T z nil)            l = cong (λ U → cons U z nil) (bdm-ins-hi i n y f T l)
  bdmB-ins-hi i n y f (cons T z (cons T′ z′ r)) l = cong (cons (bdm i T) z) (bdmB-ins-hi i n y f (cons T′ z′ r) l)

mutual
  bdm-ins-lo : ∀ i n (y f : Nat) (T : LT Nat) → n < i → bdm i (insert n y f T) ≡ insert n y f (bdm i T)
  bdm-ins-lo (suc i) zero    y f (node s br) _ =
    cong (node s) (trans (bdmB-++ i br (cons (node f nil) y nil))
                         (cong (λ U → bdmB i br ++B cons U y nil) (bdm-leaf i f)))
  bdm-ins-lo (suc i) (suc n) y f (node s br) (s≤s l) = cong (node s) (bdmB-ins-lo i n y f br l)

  bdmB-ins-lo : ∀ i n (y f : Nat) (br : Br Nat) → n < i → bdmB i (insLast n y f br) ≡ insLast n y f (bdmB i br)
  bdmB-ins-lo i n y f nil                       l = refl
  bdmB-ins-lo i n y f (cons T z nil)            l = cong (λ U → cons U z nil) (bdm-ins-lo i n y f T l)
  bdmB-ins-lo i n y f (cons T z (cons T′ z′ r)) l = cong (cons (bdm i T) z) (bdmB-ins-lo i n y f (cons T′ z′ r) l)

mutual
  bdp-ins-hi : ∀ i n (y f : Nat) (T : LT Nat) → i < n → bdp i (insert n y f T) ≡ bdp i T
  bdp-ins-hi zero    (suc n) y f (node s br) _       = cong (λ z → node z nil) (lastv-insLast n y f s br)
  bdp-ins-hi (suc i) (suc n) y f (node s br) (s≤s l) = cong (node s) (bdpB-ins-hi i n y f br l)

  bdpB-ins-hi : ∀ i n (y f : Nat) (br : Br Nat) → i < n → bdpB i (insLast n y f br) ≡ bdpB i br
  bdpB-ins-hi i n y f nil                       l = refl
  bdpB-ins-hi i n y f (cons T z nil)            l = cong (λ U → cons U z nil) (bdp-ins-hi i n y f T l)
  bdpB-ins-hi i n y f (cons T z (cons T′ z′ r)) l = cong (cons (bdp i T) z) (bdpB-ins-hi i n y f (cons T′ z′ r) l)

mutual
  bdp-ins-lo : ∀ i n (y f : Nat) (T : LT Nat) → n < i → bdp i (insert n y f T) ≡ insert n y f (bdp i T)
  bdp-ins-lo (suc i) zero    y f (node s br) _ =
    cong (node s) (trans (bdpB-++ i br (cons (node f nil) y nil))
                         (cong (λ U → bdpB i br ++B cons U y nil) (bdp-leaf i f)))
  bdp-ins-lo (suc i) (suc n) y f (node s br) (s≤s l) = cong (node s) (bdpB-ins-lo i n y f br l)

  bdpB-ins-lo : ∀ i n (y f : Nat) (br : Br Nat) → n < i → bdpB i (insLast n y f br) ≡ insLast n y f (bdpB i br)
  bdpB-ins-lo i n y f nil                       l = refl
  bdpB-ins-lo i n y f (cons T z nil)            l = cong (λ U → cons U z nil) (bdp-ins-lo i n y f T l)
  bdpB-ins-lo i n y f (cons T z (cons T′ z′ r)) l = cong (cons (bdp i T) z) (bdpB-ins-lo i n y f (cons T′ z′ r) l)

mutual
  rm-bdm : ∀ n i T (x : Nat) → n < i → RM n T x → RM n (bdm i T) x
  rm-bdm zero    (suc i) (node s br) x _       p = trans (lastv-bdmB i s br) p
  rm-bdm (suc n) (suc i) (node s br) x (s≤s l) p = rmB-bdm n i br x l p

  rmB-bdm : ∀ n i br (x : Nat) → n < i → RMB n br x → RMB n (bdmB i br) x
  rmB-bdm n i nil                       x l ()
  rmB-bdm n i (cons T z nil)            x l p = rm-bdm n i T x l p
  rmB-bdm n i (cons T z (cons T′ z′ r)) x l p = rmB-bdm n i (cons T′ z′ r) x l p

mutual
  rm-bdp : ∀ n i T (x : Nat) → n < i → RM n T x → RM n (bdp i T) x
  rm-bdp zero    (suc i) (node s br) x _       p = trans (lastv-bdpB i s br) p
  rm-bdp (suc n) (suc i) (node s br) x (s≤s l) p = rmB-bdp n i br x l p

  rmB-bdp : ∀ n i br (x : Nat) → n < i → RMB n br x → RMB n (bdpB i br) x
  rmB-bdp n i nil                       x l ()
  rmB-bdp n i (cons T z nil)            x l p = rm-bdp n i T x l p
  rmB-bdp n i (cons T z (cons T′ z′ r)) x l p = rmB-bdp n i (cons T′ z′ r) x l p

------------------------------------------------------------------------
-- Labels after inserting.

private
  NE : List Nat → Set
  NE []      = ⊥
  NE (_ ∷ _) = ⊤

  ne-flat : ∀ X → NE (flat X)
  ne-flat (node a r) = tt

  ne-++ : ∀ xs ys → NE ys → NE (xs ++ ys)
  ne-++ []       ys p = p
  ne-++ (x ∷ xs) ys p = tt

  ne-++l : ∀ xs ys → NE xs → NE (xs ++ ys)
  ne-++l (x ∷ xs) ys _ = tt

  dropLast-∷ : ∀ z M → NE M → dropLastᴸ (z ∷ M) ≡ z ∷ dropLastᴸ M
  dropLast-∷ z (m ∷ ms) _ = refl

  dropLast-++ : ∀ xs ys → NE ys → dropLastᴸ (xs ++ ys) ≡ xs ++ dropLastᴸ ys
  dropLast-++ []       ys p = refl
  dropLast-++ (x ∷ xs) ys p = trans (dropLast-∷ x (xs ++ ys) (ne-++ xs ys p)) (cong (x ∷_) (dropLast-++ xs ys p))

  snoc2 : ∀ L (y f : Nat) → snoc (snoc L y) f ≡ L ++ (y ∷ f ∷ [])
  snoc2 L y f = ++-assoc L (y ∷ []) (f ∷ [])

mutual
  flat-ins : ∀ n (y f : Nat) T x → RM n T x → flat (insert n y f T) ≡ flat T ++ (y ∷ f ∷ [])
  flat-ins zero    y f (node s br) x p = cong (s ∷_) (flatB-++ br (cons (node f nil) y nil))
    where
    flatB-++ : ∀ (r₁ r₂ : Br Nat) → flatB (r₁ ++B r₂) ≡ flatB r₁ ++ flatB r₂
    flatB-++ nil          r₂ = refl
    flatB-++ (cons T y r) r₂ = cong (y ∷_) (trans (cong (flat T ++_) (flatB-++ r r₂)) (sym (++-assoc (flat T) (flatB r) (flatB r₂))))
  flat-ins (suc n) y f (node s br) x p = cong (s ∷_) (flatB-ins n y f br x p)

  flatB-ins : ∀ n (y f : Nat) br x → RMB n br x → flatB (insLast n y f br) ≡ flatB br ++ (y ∷ f ∷ [])
  flatB-ins n y f nil                       x ()
  flatB-ins n y f (cons T z nil)            x p =
    cong (z ∷_) (trans (++-[] (flat (insert n y f T)))
                  (trans (flat-ins n y f T x p) (cong (_++ (y ∷ f ∷ [])) (sym (++-[] (flat T))))))
  flatB-ins n y f (cons T z (cons T′ z′ r)) x p =
    cong (z ∷_) (trans (cong (flat T ++_) (flatB-ins n y f (cons T′ z′ r) x p))
                       (sym (++-assoc (flat T) (flatB (cons T′ z′ r)) (y ∷ f ∷ []))))

mutual
  flat-bdp-ins : ∀ i (y f : Nat) T x → RM i T x → flat (bdp i (insert i y f T)) ≡ snoc (dropLastᴸ (flat (bdp i T))) y
  flat-bdp-ins zero    y f (node s br) x p = cong (_∷ []) (lastv-++1 s br (node f nil) y)
  flat-bdp-ins (suc i) y f (node s br) x p =
    trans (cong (s ∷_) (flatB-bdp-ins i y f br x p))
          (cong (_++ (y ∷ [])) (sym (dropLast-∷ s (flatB (bdpB i br)) (ne-bdpB i br x p))))
    where
    ne-bdpB : ∀ i br x → RMB i br x → NE (flatB (bdpB i br))
    ne-bdpB i nil          x ()
    ne-bdpB i (cons T z r) x _ = tt

  flatB-bdp-ins : ∀ i (y f : Nat) br x → RMB i br x →
                  flatB (bdpB i (insLast i y f br)) ≡ snoc (dropLastᴸ (flatB (bdpB i br))) y
  flatB-bdp-ins i y f nil                       x ()
  flatB-bdp-ins i y f (cons T z nil)            x p =
    trans (cong (z ∷_) (trans (++-[] _)
      (trans (flat-bdp-ins i y f T x p)
        (cong (λ L → snoc (dropLastᴸ L) y) (sym (++-[] (flat (bdp i T))))))))
      (cong (_++ (y ∷ [])) (sym (dropLast-∷ z (flat (bdp i T) ++ []) (ne-++l (flat (bdp i T)) [] (ne-flat (bdp i T))))))
  flatB-bdp-ins i y f (cons T z (cons T′ z′ r)) x p =
    trans (cong (z ∷_) (trans (cong (flat (bdp i T) ++_) (flatB-bdp-ins i y f (cons T′ z′ r) x p))
      (trans (sym (++-assoc (flat (bdp i T)) (dropLastᴸ (flatB (bdpB i (cons T′ z′ r)))) (y ∷ [])))
        (cong (_++ (y ∷ [])) (sym (dropLast-++ (flat (bdp i T)) (flatB (bdpB i (cons T′ z′ r))) tt))))))
      (cong (_++ (y ∷ [])) (sym (dropLast-∷ z (flat (bdp i T) ++ flatB (bdpB i (cons T′ z′ r)))
                                    (ne-++l (flat (bdp i T)) _ (ne-flat (bdp i T))))))

------------------------------------------------------------------------
-- The boundaries of the tree of a pasting context.

private
  <ℕs-true : ∀ i a → (i <ℕ suc a) ≡ true → i ≤ a
  <ℕs-true zero    a       _ = z≤n
  <ℕs-true (suc i) (suc a) p = s≤s (<ℕs-true i a p)

  <ℕs-false : ∀ i a → (i <ℕ suc a) ≡ false → a < i
  <ℕs-false zero    a       ()
  <ℕs-false (suc i) zero    _ = s≤s z≤n
  <ℕs-false (suc i) (suc a) p = s≤s (<ℕs-false i a p)

  <ℕ-true : ∀ i a → (i <ℕ a) ≡ true → i < a
  <ℕ-true zero    (suc a) _ = s≤s z≤n
  <ℕ-true (suc i) (suc a) p = s≤s (<ℕ-true i a p)

  <ℕ-false : ∀ i a → (i <ℕ a) ≡ false → (a ==ℕ i) ≡ false → a < i
  <ℕ-false zero    zero    _ ()
  <ℕ-false (suc i) zero    _ _ = s≤s z≤n
  <ℕ-false (suc i) (suc a) p q = s≤s (<ℕ-false i a p q)
  <ℕ-false zero    (suc a) () _

  bdm-pt : ∀ i → bdm i (node 0 nil) ≡ node 0 nil
  bdm-pt zero    = refl
  bdm-pt (suc i) = refl

  bdp-pt : ∀ i → bdp i (node 0 nil) ≡ node 0 nil
  bdp-pt zero    = refl
  bdp-pt (suc i) = refl

  rm-d : ∀ {Γ x A} → Γ ⊢ps x ∶ A → RM (dim A) (tr Γ) x
  rm-d {Γ} {x} {A} d = rmt-top (tr Γ) x A (tr-rm d)

flat-src : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ i → flat (bdm i (tr Γ)) ≡ srcVars i Γ
flat-src pss i = cong flat (bdm-pt i)
flat-src (pse {Γ} {x} {A} d) i with i <ℕ suc (dim A) in e
... | true  = trans (cong flat (bdm-ins-hi i (dim A) (len Γ) (suc (len Γ)) (tr Γ) (<ℕs-true i (dim A) e))) (flat-src d i)
... | false =
  let l = <ℕs-false i (dim A) e in
  trans (cong flat (bdm-ins-lo i (dim A) (len Γ) (suc (len Γ)) (tr Γ) l))
    (trans (flat-ins (dim A) (len Γ) (suc (len Γ)) (bdm i (tr Γ)) x (rm-bdm (dim A) i (tr Γ) x l (rm-d d)))
      (trans (cong (_++ (len Γ ∷ suc (len Γ) ∷ [])) (flat-src d i)) (sym (snoc2 (srcVars i Γ) (len Γ) (suc (len Γ))))))
flat-src (psd d) i = flat-src d i

flat-tgt : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ i → flat (bdp i (tr Γ)) ≡ tgtVars i Γ
flat-tgt pss i = cong flat (bdp-pt i)
flat-tgt (pse {Γ} {x} {A} d) i with i <ℕ dim A in e
... | true = trans (cong flat (bdp-ins-hi i (dim A) (len Γ) (suc (len Γ)) (tr Γ) (<ℕ-true i (dim A) e))) (flat-tgt d i)
... | false with dim A ==ℕ i in e′
...   | true rewrite ==→≡ (dim A) i e′ =
  trans (flat-bdp-ins i (len Γ) (suc (len Γ)) (tr Γ) x (subst (λ k → RM k (tr Γ) x) (==→≡ (dim A) i e′) (rm-d d)))
        (cong (λ L → snoc (dropLastᴸ L) (len Γ)) (flat-tgt d i))
...   | false =
  let l = <ℕ-false i (dim A) e e′ in
  trans (cong flat (bdp-ins-lo i (dim A) (len Γ) (suc (len Γ)) (tr Γ) l))
    (trans (flat-ins (dim A) (len Γ) (suc (len Γ)) (bdp i (tr Γ)) x (rm-bdp (dim A) i (tr Γ) x l (rm-d d)))
      (trans (cong (_++ (len Γ ∷ suc (len Γ) ∷ [])) (flat-tgt d i)) (sym (snoc2 (tgtVars i Γ) (len Γ) (suc (len Γ))))))
flat-tgt (psd d) i = flat-tgt d i

------------------------------------------------------------------------
-- All the variables.

upTo : Nat → List Nat
upTo zero    = []
upTo (suc n) = snoc (upTo n) n

flat-tr : ∀ {Γ x A} → Γ ⊢ps x ∶ A → flat (tr Γ) ≡ upTo (len Γ)
flat-tr pss = refl
flat-tr (pse {Γ} {x} {A} d) =
  trans (flat-ins (dim A) (len Γ) (suc (len Γ)) (tr Γ) x (rm-d d))
    (trans (cong (_++ (len Γ ∷ suc (len Γ) ∷ [])) (flat-tr d)) (sym (snoc2 (upTo (len Γ)) (len Γ) (suc (len Γ)))))
flat-tr (psd d) = flat-tr d

upTo≈ : ∀ n → upTo n ≈ downFrom n
upTo≈ zero    = ≈-refl
upTo≈ (suc n) =
  let (f , g) = upTo≈ n in
  ⊆-++ (tl⊆ n f) (sing⊆ (∈-hd n (downFrom n))) ,
  ⊆-∷ (∈-++ʳ n (upTo n) (n ∷ []) (∈-hd n [])) (inl⊆ (n ∷ []) g)

------------------------------------------------------------------------
-- Height.

private
  max-l : ∀ a b → a ≤ max a b
  max-l zero    b       = z≤n
  max-l (suc a) zero    = ≤-refl (suc a)
  max-l (suc a) (suc b) = s≤s (max-l a b)

  max-r : ∀ a b → b ≤ max a b
  max-r zero    b       = ≤-refl b
  max-r (suc a) zero    = z≤n
  max-r (suc a) (suc b) = s≤s (max-r a b)

height : ∀ {Γ x A} → Γ ⊢ps x ∶ A → bdm (dimCtx Γ) (tr Γ) ≡ tr Γ
height pss = refl
height (pse {Γ} {x} {A} d) =
  trans (bdm-ins-lo m (dim A) (len Γ) (suc (len Γ)) (tr Γ) (≤-trans (≤-refl (suc (dim A))) (max-l (suc (dim A)) (max (dim A) (dimCtx Γ)))))
        (cong (insert (dim A) (len Γ) (suc (len Γ)))
          (trans (cong (bdm m) (sym (height d)))
            (trans (ωCat.src-src-≥ 𝒯 (tr Γ) (≤-trans (max-r (dim A) (dimCtx Γ)) (max-r (suc (dim A)) (max (dim A) (dimCtx Γ)))))
                   (height d))))
  where
  m = dimCtx (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
height (psd d) = height d

------------------------------------------------------------------------
-- The tree of a pasting context is well typed.

private
  tv-mono : ∀ {Γ Γ′} (o : ArrOrd Γ) (o′ : ArrOrd Γ′) → (∀ v P → lookup Γ v ≡ just P → lookup Γ′ v ≡ just P) →
            ∀ P X → TV Γ o P X → TV Γ′ o′ P X
  tv-mono {Γ} {Γ′} o o′ h = go
    where
    mutual
      go : ∀ P X → TV Γ o P X → TV Γ′ o′ P X
      go P (node x r) (lx , tb) = h x P lx , goB P x r tb

      goB : ∀ P x r → TVB Γ o P x r → TVB Γ′ o′ P x r
      goB P x nil          _               = tt
      goB P x (cons T y r) (tT , ly , tr′) = go _ T tT , h y P ly , goB P y r tr′

  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

module _ (Γ : Ctx) (o : ArrOrd Γ) {A : Ty} {x y f : Nat}
         (lx : lookup Γ x ≡ just A) (ly : lookup Γ y ≡ just A) (lf : lookup Γ f ≡ just (arr A (var x) (var y))) where
  mutual
    tv-ins : ∀ n P T → TV Γ o P T → RM n T x → TV Γ o P (insert n y f T)
    tv-ins zero    P (node s br) (ls , tb) rm with just-inj (trans (sym (subst (λ z → lookup Γ z ≡ just P) rm (lastv-ty Γ o P s br ls tb))) lx)
    ... | refl = ls , tvB-++ Γ o P s br (cons (node f nil) y nil) tb
                        (subst (λ z → TVB Γ o P z (cons (node f nil) y nil)) (sym rm) ((lf , tt) , ly , tt))
    tv-ins (suc n) P (node s br) (ls , tb) rm = ls , tvB-ins n P s br tb rm

    tvB-ins : ∀ n P s br → TVB Γ o P s br → RMB n br x → TVB Γ o P s (insLast n y f br)
    tvB-ins n P s nil                       _                ()
    tvB-ins n P s (cons T z nil)            (tT , lz , _)    rm = tv-ins n _ T tT rm , lz , tt
    tvB-ins n P s (cons T z (cons T′ z′ r)) (tT , lz , tr′) rm = tT , lz , tvB-ins n P z (cons T′ z′ r) tr′ rm

tv-tr : ∀ {Γ x A} (d : Γ ⊢ps x ∶ A) → TV Γ (ord (ps-facts d)) ⋆ (tr Γ)
tv-tr pss = refl , tt
tv-tr {Γ ▸ A ▸ B} (pse {Γ} {x} {A} d) =
  tv-ins (Γ ▸ A ▸ B) o′ (wk x A (dang (ps-facts d))) (lookup-wk (Γ ▸ A) B (len Γ) (n<s (len Γ)) |> λ e → trans e (lookup-top Γ A))
    (lookup-top (Γ ▸ A) B) (dim A) ⋆ (tr Γ)
    (tv-mono (ord (ps-facts d)) o′ wk ⋆ (tr Γ) (tv-tr d)) (rm-d d)
  where
  o′ = ord (ps-facts (pse d))
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  a |> h = h a
  n<s : ∀ n → T (n <ℕ suc n)
  n<s zero    = tt
  n<s (suc n) = n<s n
  <s : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <s zero    (suc n) _ = tt
  <s (suc i) (suc n) q = <s i n q
  wk : ∀ v P → lookup Γ v ≡ just P → lookup (Γ ▸ A ▸ B) v ≡ just P
  wk v P p = trans (lookup-wk (Γ ▸ A) B v (<s v (len Γ) (lookup-< Γ v p))) (trans (lookup-wk Γ A v (lookup-< Γ v p)) p)
tv-tr (psd d) = tv-tr d
