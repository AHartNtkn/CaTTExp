------------------------------------------------------------------------
-- ∂∂ = 0 for the bag boundary of a context whose types are variable
-- towers (every pasting context):
--
--   ∂⁺∂⁺w + ∂⁻∂⁻w = ∂⁺∂⁻w + ∂⁻∂⁺w      (as bags, `dd`).
--
-- By induction on the tuple w = v ∷ w'. With F = the faces (s, t) of v,
-- the terms of ∂^b∂^c(v ∷ w') are
--   * ∂^b of the face x_c of v in front of w', which is the faces of
--     x_c (the same for s and t, as both have v's lower type) and
--     x_c ∷ ∂^{f'b} w';
--   * v's face x_b in front of ∂^{fc} w', with f = f' ∘ not;
--   * v in front of ∂^{fb}∂^{fc} w', handled by induction.
------------------------------------------------------------------------
module CaTTExp.Strict.DD where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.L
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- The boundary of a bag of tuples with a common head.

cm-consB : ∀ v g Y → cm (λ y → consB v (g y)) Y ≡ consB v (cm g Y)
cm-consB v g Y = sym (cm-fuse (λ u → (v ∷ u) ∷ []) g Y)

∂B-consB : ∀ Γ b v Y →
           ∂B Γ b (consB v Y) ≈
           cm (here b (facesTy (lookup Γ v))) Y ++ consB v (∂B Γ (flipN (hdimV Γ v) b) Y)
∂B-consB Γ b v Y =
  ≈-trans (≡→≈ (cm-fuse (∂T Γ b) (λ y → (v ∷ y) ∷ []) Y))
 (≈-trans (cm-ext' _ _ Y (λ y → ≡→≈ (++-[]L (∂T Γ b (v ∷ y)))))
 (≈-trans (cm-sum (here b (facesTy (lookup Γ v))) (λ y → consB v (∂T Γ (flipN (hdimV Γ v) b) y)) Y)
          (≡→≈ (cong (cm (here b (facesTy (lookup Γ v))) Y ++_) (cm-consB v (∂T Γ (flipN (hdimV Γ v) b)) Y)))))

------------------------------------------------------------------------
-- Statement.

X : Ctx → Bool → Bool → Tuple → Bag
X Γ b c w = ∂B Γ b (∂T Γ c w)

DD : Ctx → Tuple → Set
DD Γ w = X Γ true true w ++ X Γ false false w ≈ X Γ true false w ++ X Γ false true w

-- Either sign first.
DD-gen : ∀ Γ w σ → DD Γ w → X Γ σ σ w ++ X Γ (not σ) (not σ) w ≈ X Γ σ (not σ) w ++ X Γ (not σ) σ w
DD-gen Γ w true  p = p
DD-gen Γ w false p =
  ≈-trans (++-comm (X Γ false false w) (X Γ true true w)) (≈-trans p (++-comm (X Γ true false w) (X Γ false true w)))

------------------------------------------------------------------------
-- Arithmetic.

private
  sw : ∀ a b c → a + (b + c) ≡ b + (a + c)
  sw a b c = trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

-- The two sides, term by term.
private
  r3 : ∀ h a b d → h + (a + (b + d)) ≡ (h + (a + b)) + d
  r3 h a b d = trans (cong (h +_) (sym (+-assoc a b d))) (sym (+-assoc h (a + b) d))

  nf : ∀ h a b d h' a' b' d' →
       (h + (a + (b + d))) + (h' + (a' + (b' + d'))) ≡ ((h + h') + ((a + b) + (a' + b'))) + (d + d')
  nf h a b d h' a' b' d' =
    trans (cong₂ _+_ (r3 h a b d) (r3 h' a' b' d'))
   (trans (+-interchange (h + (a + b)) d (h' + (a' + b')) d')
          (cong (_+ (d + d')) (+-interchange h (a + b) h' (a' + b'))))

  arith : ∀ hT hF t1 t2 s1 s2 dTT dFF dTF dFT → dTT + dFF ≡ dTF + dFT →
          (hT + (t1 + (t2 + dTT))) + (hF + (s1 + (s2 + dFF))) ≡
          (hT + (s2 + (t1 + dTF))) + (hF + (t2 + (s1 + dFT)))
  arith hT hF t1 t2 s1 s2 dTT dFF dTF dFT de =
    trans (nf hT t1 t2 dTT hF s1 s2 dFF)
   (trans (cong₂ (λ x y → ((hT + hF) + x) + y) shuffle de)
          (sym (nf hT s2 t1 dTF hF t2 s1 dFT)))
    where
    shuffle : (t1 + t2) + (s1 + s2) ≡ (s2 + t1) + (t2 + s1)
    shuffle = trans (+-interchange t1 t2 s1 s2) (sym B)
      where
      B : (s2 + t1) + (t2 + s1) ≡ (t1 + s1) + (t2 + s2)
      B = trans (+-interchange s2 t1 t2 s1)
         (trans (+-comm (s2 + t2) (t1 + s1)) (cong ((t1 + s1) +_) (+-comm s2 t2)))

------------------------------------------------------------------------
-- The proof.

module _ (Γ : Ctx) where

  private
    fv : Nat → Bool → Bool
    fv v = flipN (hdimV Γ v)

    cnt-cons : ∀ v Y Z a → count a (consB v Y ++ consB v Z) ≡ count a (consB v (Y ++ Z))
    cnt-cons v Y Z a = sym (cong (count a) (cm-++ (λ u → (v ∷ u) ∷ []) Y Z))

  -- The terms of ∂^b∂^c(v ∷ w).
  expand : ∀ v w b c a →
           count a (X Γ b c (v ∷ w)) ≡
           count a (cm (∂T Γ b) (here c (facesTy (lookup Γ v)) w)) +
           (count a (cm (here b (facesTy (lookup Γ v))) (∂T Γ (fv v c) w)) +
            count a (consB v (X Γ (fv v b) (fv v c) w)))
  expand v w b c a =
    trans (cong (count a) (cm-++ (∂T Γ b) (here c (facesTy (lookup Γ v)) w) (consB v (∂T Γ (fv v c) w))))
   (trans (count-++ a (cm (∂T Γ b) (here c (facesTy (lookup Γ v)) w)) (∂B Γ b (consB v (∂T Γ (fv v c) w))))
          (cong (count a (cm (∂T Γ b) (here c (facesTy (lookup Γ v)) w)) +_)
                (trans (at (∂B-consB Γ b v (∂T Γ (fv v c) w)) a)
                       (count-++ a (cm (here b (facesTy (lookup Γ v))) (∂T Γ (fv v c) w))
                                   (consB v (X Γ (fv v b) (fv v c) w))))))

  -- The terms in front of v.
  dterm : ∀ v w → DD Γ w → ∀ a →
          count a (consB v (X Γ (fv v true) (fv v true) w)) + count a (consB v (X Γ (fv v false) (fv v false) w)) ≡
          count a (consB v (X Γ (fv v true) (fv v false) w)) + count a (consB v (X Γ (fv v false) (fv v true) w))
  dterm v w p a =
    trans (sym (count-++ a (consB v (X Γ σ σ w)) (consB v (X Γ σ' σ' w))))
   (trans (cnt-cons v (X Γ σ σ w) (X Γ σ' σ' w) a)
   (trans (at (cm-cong (λ u → (v ∷ u) ∷ []) _ _ q) a)
   (trans (sym (cnt-cons v (X Γ σ σ' w) (X Γ σ' σ w) a))
          (count-++ a (consB v (X Γ σ σ' w)) (consB v (X Γ σ' σ w))))))
    where
    σ  = fv v true
    σ' = fv v false
    e : σ' ≡ not σ
    e = flipN-not (hdimV Γ v) true
    q : X Γ σ σ w ++ X Γ σ' σ' w ≈ X Γ σ σ' w ++ X Γ σ' σ w
    q = subst (λ z → X Γ σ σ w ++ X Γ z z w ≈ X Γ σ z w ++ X Γ z σ w) (sym e) (DD-gen Γ w σ p)

  private
    data FC (v : Nat) : Set where
      noF  : facesTy (lookup Γ v) ≡ nothing → FC v
      yesF : ∀ s t → facesTy (lookup Γ v) ≡ just (s , t) → lookup Γ s ≡ lookup Γ t →
             hdimV Γ v ≡ suc (hdimV Γ s) → FC v

    fcase : PsInv Γ → ∀ v → FC v
    fcase inv v = go (lookup Γ v) refl
      where
      go : ∀ m → lookup Γ v ≡ m → FC v
      go nothing                   e = noF (cong facesTy e)
      go (just ⋆)                  e = noF (cong facesTy e)
      go (just (arr ⋆ _ _))        e = noF (cong facesTy e)
      go (just (arr (arr B a b) s t)) e with inv v _ e
      ... | (i , j , refl , refl , li , lj) =
        yesF i j (cong facesTy e) (trans li (sym lj))
             (trans (cong hdimTy e) (cong (λ m → suc (hdimTy m)) (sym li)))

  dd : PsInv Γ → ∀ w → DD Γ w
  dd inv []      = ≈-refl
  dd inv (v ∷ w) with fcase inv v
  ... | noF eF = mk≈ λ a →
    trans (count-++ a (X Γ true true (v ∷ w)) (X Γ false false (v ∷ w)))
   (trans (cong₂ _+_ (nz a true true) (nz a false false))
   (trans (dterm v w (dd inv w) a)
          (sym (trans (count-++ a (X Γ true false (v ∷ w)) (X Γ false true (v ∷ w)))
                      (cong₂ _+_ (nz a true false) (nz a false true))))))
    where
    nz : ∀ a b c → count a (X Γ b c (v ∷ w)) ≡ count a (consB v (X Γ (fv v b) (fv v c) w))
    nz a b c =
      trans (expand v w b c a)
            (cong₂ (λ m n → m + (n + count a (consB v (X Γ (fv v b) (fv v c) w))))
                   (cong (λ m → count a (cm (∂T Γ b) (here c m w))) eF)
                   (trans (cong (λ m → count a (cm (here b m) (∂T Γ (fv v c) w))) eF)
                          (cong (count a) (cm-nil (∂T Γ (fv v c) w)))))
  ... | yesF s t eF eL eh = mk≈ λ a →
    trans (count-++ a (X Γ true true (v ∷ w)) (X Γ false false (v ∷ w)))
   (trans (cong₂ _+_ (hj a true true) (hj a false false))
   (trans (arith (count a (here true G w)) (count a (here false G w))
                 (count a (consB t (Y true))) (count a (consB t (Y false)))
                 (count a (consB s (Y false))) (count a (consB s (Y true)))
                 (count a (consB v (X Γ (fv v true) (fv v true) w))) (count a (consB v (X Γ (fv v false) (fv v false) w)))
                 (count a (consB v (X Γ (fv v true) (fv v false) w))) (count a (consB v (X Γ (fv v false) (fv v true) w)))
                 (dterm v w (dd inv w) a))
          (sym (trans (count-++ a (X Γ true false (v ∷ w)) (X Γ false true (v ∷ w)))
                      (cong₂ _+_ (hj a true false) (hj a false true))))))
    where
    G = facesTy (lookup Γ s)
    f' = flipN (hdimV Γ s)
    Y : Bool → Bag
    Y b = ∂T Γ (f' b) w
    x : Bool → Nat
    x c = if c then t else s
    xF : ∀ c → facesTy (lookup Γ (x c)) ≡ G
    xF true  = cong facesTy (sym eL)
    xF false = refl
    xH : ∀ c → hdimV Γ (x c) ≡ hdimV Γ s
    xH true  = cong hdimTy (sym eL)
    xH false = refl
    fl : ∀ c → fv v c ≡ f' (not c)
    fl c = trans (cong (λ n → flipN n c) eh) (sym (flipN-not (hdimV Γ s) c))
    hj : ∀ a b c → count a (X Γ b c (v ∷ w)) ≡
         count a (here b G w) + (count a (consB (x c) (Y b)) + (count a (consB (x b) (Y (not c))) +
                                  count a (consB v (X Γ (fv v b) (fv v c) w))))
    hj a b c =
      trans (expand v w b c a)
     (trans (cong₂ (λ m n → m + (n + count a (consB v (X Γ (fv v b) (fv v c) w)))) first second)
            (+-assoc (count a (here b G w)) (count a (consB (x c) (Y b))) _))
      where
      first : count a (cm (∂T Γ b) (here c (facesTy (lookup Γ v)) w)) ≡
              count a (here b G w) + count a (consB (x c) (Y b))
      first =
        trans (cong (λ m → count a (cm (∂T Γ b) (here c m w))) eF)
       (trans (cong (count a) (++-[]L (∂T Γ b (x c ∷ w))))
       (trans (cong₂ (λ m n → count a (here b m w ++ consB (x c) (∂T Γ (flipN n b) w))) (xF c) (xH c))
              (count-++ a (here b G w) (consB (x c) (Y b)))))
      second : count a (cm (here b (facesTy (lookup Γ v))) (∂T Γ (fv v c) w)) ≡ count a (consB (x b) (Y (not c)))
      second =
        trans (cong (λ m → count a (cm (here b m) (∂T Γ (fv v c) w))) eF)
              (cong (λ z → count a (consB (x b) (∂T Γ z w))) (fl c))

  -- For bags.
  ddB : PsInv Γ → ∀ Z →
        ∂B Γ true (∂B Γ true Z) ++ ∂B Γ false (∂B Γ false Z) ≈ ∂B Γ true (∂B Γ false Z) ++ ∂B Γ false (∂B Γ true Z)
  ddB inv []      = ≈-refl
  ddB inv (z ∷ Z) = mk≈ λ a →
    trans (count-++ a (B true true) (B false false))
   (trans (cong₂ _+_ (e true true a) (e false false a))
   (trans (four (count a (X Γ true true z)) (count a (C true true)) (count a (X Γ false false z)) (count a (C false false))
                (count a (X Γ true false z)) (count a (C true false)) (count a (X Γ false true z)) (count a (C false true))
                (trans (sym (count-++ a (X Γ true true z) (X Γ false false z)))
                       (trans (at (dd inv z) a) (count-++ a (X Γ true false z) (X Γ false true z))))
                (trans (sym (count-++ a (C true true) (C false false)))
                       (trans (at (ddB inv Z) a) (count-++ a (C true false) (C false true)))))
          (sym (trans (count-++ a (B true false) (B false true)) (cong₂ _+_ (e true false a) (e false true a))))))
    where
    B : Bool → Bool → Bag
    B b c = ∂B Γ b (∂B Γ c (z ∷ Z))
    C : Bool → Bool → Bag
    C b c = ∂B Γ b (∂B Γ c Z)
    e : ∀ b c a → count a (B b c) ≡ count a (X Γ b c z) + count a (C b c)
    e b c a = trans (cong (count a) (cm-++ (∂T Γ b) (∂T Γ c z) (∂B Γ c Z))) (count-++ a (X Γ b c z) (C b c))
    four : ∀ p q r s p' q' r' s' → p + r ≡ p' + r' → q + s ≡ q' + s' → (p + q) + (r + s) ≡ (p' + q') + (r' + s')
    four p q r s p' q' r' s' e1 e2 =
      trans (+-interchange p q r s) (trans (cong₂ _+_ e1 e2) (sym (+-interchange p' q' r' s')))
