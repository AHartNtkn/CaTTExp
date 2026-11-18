------------------------------------------------------------------------
-- The Steiner complex K(Γ) of a context, on bags.
--
-- For a pasting context Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ (CaTTExp.Gray.Support),
-- K(Γ)(aᵢ, aⱼ) = λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ has as basis the tuples (vᵢ₊₁ … vⱼ)
-- with vₖ a cell of the hom Θₖ. Here everything is read off the types
-- of Γ, so the definitions make sense for any context:
--
--  * the hom-dimension of a variable v : B is dim B − 1;
--  * the degree of a tuple is the sum of the hom-dimensions;
--  * WFT Γ x y w: w is a composable chain of hom cells from the object
--    x to the object y (the empty tuple is the unit of the hom x → x);
--  * the boundary of a tuple follows the Leibniz rule
--        ∂(v ⊗ w) = ∂v ⊗ w + (−1)^{|v|} v ⊗ ∂w,     ∂v = t − s,
--    split into its positive part (∂T Γ true) and negative part
--    (∂T Γ false), which are bags (no cancellation occurs inside the
--    boundary of one basis element).
------------------------------------------------------------------------
module CaTTExp.Strict.Complex where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Gray.Pure using (Ty; ⋆; arr; Tm; var; coh; Ctx; lookup; dim)

------------------------------------------------------------------------
-- Degrees and signs.

hdimTy : Maybe Ty → Nat
hdimTy nothing  = 0
hdimTy (just B) = dim B ∸ 1

hdimV : Ctx → Nat → Nat
hdimV Γ v = hdimTy (lookup Γ v)

deg : Ctx → Tuple → Nat
deg Γ []      = 0
deg Γ (v ∷ w) = hdimV Γ v + deg Γ w

-- (−1)^n acting on a sign (true is +).
flipN : Nat → Bool → Bool
flipN zero    b = b
flipN (suc n) b = not (flipN n b)

flipN-+ : ∀ m n b → flipN (m + n) b ≡ flipN n (flipN m b)
flipN-+ zero    n b = refl
flipN-+ (suc m) n b = trans (cong not (flipN-+ m n b)) (sym (flipN-not n (flipN m b)))
  where
  flipN-not : ∀ n b → flipN n (not b) ≡ not (flipN n b)
  flipN-not zero    b = refl
  flipN-not (suc n) b = cong not (flipN-not n b)

flipN-not : ∀ n b → flipN n (not b) ≡ not (flipN n b)
flipN-not zero    b = refl
flipN-not (suc n) b = cong not (flipN-not n b)

-- The sign after passing a whole tuple.
flipT : Ctx → Tuple → Bool → Bool
flipT Γ []      b = b
flipT Γ (v ∷ w) b = flipT Γ w (flipN (hdimV Γ v) b)

flipT-deg : ∀ Γ w b → flipT Γ w b ≡ flipN (deg Γ w) b
flipT-deg Γ []      b = refl
flipT-deg Γ (v ∷ w) b =
  trans (flipT-deg Γ w (flipN (hdimV Γ v) b)) (sym (flipN-+ (hdimV Γ v) (deg Γ w) b))

deg-++ : ∀ Γ x y → deg Γ (x ++ y) ≡ deg Γ x + deg Γ y
deg-++ Γ []      y = refl
deg-++ Γ (v ∷ x) y = trans (cong (hdimV Γ v +_) (deg-++ Γ x y)) (sym (+-assoc (hdimV Γ v) (deg Γ x) (deg Γ y)))

------------------------------------------------------------------------
-- Endpoints and composable tuples.

endsV : Ty → Maybe (Nat × Nat)
endsV ⋆                       = nothing
endsV (arr ⋆ (var a) (var b)) = just (a , b)
endsV (arr ⋆ _ _)             = nothing
endsV (arr (arr B s t) _ _)   = endsV (arr B s t)

endsL : Maybe Ty → Maybe (Nat × Nat)
endsL nothing  = nothing
endsL (just B) = endsV B

WFT : Ctx → Nat → Nat → Tuple → Set
WFT Γ x y []      = x ≡ y
WFT Γ x y (v ∷ w) = Σ Nat λ z → (endsL (lookup Γ v) ≡ just (x , z)) × WFT Γ z y w

WFT-++ : ∀ Γ x z y a b → WFT Γ x z a → WFT Γ z y b → WFT Γ x y (a ++ b)
WFT-++ Γ x z y []      b refl q = q
WFT-++ Γ x z y (v ∷ a) b (z' , e , p) q = z' , e , WFT-++ Γ z' z y a b p q

-- Basis elements of K(Γ)(x, y) of degree k.
Basis : Ctx → Nat → Nat → Nat → Tuple → Set
Basis Γ x y k w = WFT Γ x y w × (deg Γ w ≡ k)

Basis-++ : ∀ Γ x z y k l a b → Basis Γ x z k a → Basis Γ z y l b → Basis Γ x y (k + l) (a ++ b)
Basis-++ Γ x z y k l a b (p , dp) (q , dq) =
  WFT-++ Γ x z y a b p q , trans (deg-++ Γ a b) (cong₂ _+_ dp dq)

------------------------------------------------------------------------
-- Boundaries.

facesTy : Maybe Ty → Maybe (Nat × Nat)
facesTy (just (arr (arr _ _ _) (var s) (var t))) = just (s , t)
facesTy _                                        = nothing

here : Bool → Maybe (Nat × Nat) → Tuple → Bag
here b nothing        w = []
here b (just (s , t)) w = ((if b then t else s) ∷ w) ∷ []

consB : Nat → Bag → Bag
consB v = cm (λ u → (v ∷ u) ∷ [])

∂T : Ctx → Bool → Tuple → Bag
∂T Γ b []      = []
∂T Γ b (v ∷ w) = here b (facesTy (lookup Γ v)) w ++ consB v (∂T Γ (flipN (hdimV Γ v) b) w)

∂B : Ctx → Bool → Bag → Bag
∂B Γ b = cm (∂T Γ b)

-- right and left multiplication of a bag by a tuple
_·r_ : Bag → Tuple → Bag
X ·r y = cm (λ c → (c ++ y) ∷ []) X

_l·_ : Tuple → Bag → Bag
x l· Y = cm (λ d → (x ++ d) ∷ []) Y

------------------------------------------------------------------------
-- The Leibniz rule.

private
  here-·r : ∀ b F x y → here b F x ·r y ≡ here b F (x ++ y)
  here-·r b nothing        x y = refl
  here-·r b (just (s , t)) x y = refl

  consB-·r : ∀ v Z y → consB v Z ·r y ≡ consB v (Z ·r y)
  consB-·r v []      y = refl
  consB-·r v (z ∷ Z) y = cong (((v ∷ z) ++ y) ∷_) (consB-·r v Z y)

  consB-l· : ∀ v x W → consB v (x l· W) ≡ (v ∷ x) l· W
  consB-l· v x []      = refl
  consB-l· v x (w ∷ W) = cong ((v ∷ (x ++ w)) ∷_) (consB-l· v x W)

  consB-cong : ∀ v {X Y} → X ≈ Y → consB v X ≈ consB v Y
  consB-cong v {X} {Y} p = cm-cong _ X Y p

  consB-++ : ∀ v X Y → consB v (X ++ Y) ≡ consB v X ++ consB v Y
  consB-++ v X Y = cm-++ _ X Y

leibniz : ∀ Γ b x y →
          ∂T Γ b (x ++ y) ≈ (∂T Γ b x ·r y) ++ (x l· ∂T Γ (flipT Γ x b) y)
leibniz Γ b []      y = ≡→≈ (sym (cm-single (∂T Γ b y)))
leibniz Γ b (v ∷ x) y =
  begin
    H (x ++ y) ++ consB v (∂T Γ b' (x ++ y))
  ≈⟨ ++-cong (≈-refl {H (x ++ y)}) (consB-cong v (leibniz Γ b' x y)) ⟩
    H (x ++ y) ++ consB v ((∂T Γ b' x ·r y) ++ (x l· ∂T Γ b'' y))
  ≈⟨ ≡→≈ (cong (H (x ++ y) ++_) (consB-++ v (∂T Γ b' x ·r y) (x l· ∂T Γ b'' y))) ⟩
    H (x ++ y) ++ (consB v (∂T Γ b' x ·r y) ++ consB v (x l· ∂T Γ b'' y))
  ≈⟨ ≈-sym (++-assoc (H (x ++ y)) _ _) ⟩
    (H (x ++ y) ++ consB v (∂T Γ b' x ·r y)) ++ consB v (x l· ∂T Γ b'' y)
  ≈⟨ ≡→≈ (cong₂ _++_
        (cong₂ _++_ (sym (here-·r b F x y)) (sym (consB-·r v (∂T Γ b' x) y)))
        (consB-l· v x (∂T Γ b'' y))) ⟩
    ((here b F x ·r y) ++ (consB v (∂T Γ b' x) ·r y)) ++ ((v ∷ x) l· ∂T Γ b'' y)
  ≈⟨ ≡→≈ (cong (_++ ((v ∷ x) l· ∂T Γ b'' y))
        (sym (cm-++ (λ c → (c ++ y) ∷ []) (here b F x) (consB v (∂T Γ b' x))))) ⟩
    (∂T Γ b (v ∷ x) ·r y) ++ ((v ∷ x) l· ∂T Γ (flipT Γ (v ∷ x) b) y)
  ∎
  where
  F  = facesTy (lookup Γ v)
  H  = here b F
  b' = flipN (hdimV Γ v) b
  b'' = flipT Γ x b'

-- Tuples of one degree all flip a sign the same way.
Deg : Ctx → Nat → Tuple → Set
Deg Γ p c = deg Γ c ≡ p

∂B-prod : ∀ Γ p b C D → All (Deg Γ p) C →
          ∂B Γ b (prod C D) ≈ prod (∂B Γ b C) D ++ prod C (∂B Γ (flipN p b) D)
∂B-prod Γ p b C D hom =
  begin
    cm (∂T Γ b) (cm (λ c → c l· D) C)
  ≈⟨ ≡→≈ (cm-fuse (∂T Γ b) (λ c → c l· D) C) ⟩
    cm (λ c → cm (∂T Γ b) (c l· D)) C
  ≈⟨ cm-ext' _ _ C (λ c → ≡→≈ (cm-fuse (∂T Γ b) (λ d → (c ++ d) ∷ []) D)) ⟩
    cm (λ c → cm (λ d → ∂T Γ b (c ++ d) ++ []) D) C
  ≈⟨ cm-ext _ _ C hom (λ c dc → cm-ext' _ _ D (λ d →
       ≈-trans (≡→≈ (++-[]L (∂T Γ b (c ++ d))))
      (≈-trans (leibniz Γ b c d)
               (≡→≈ (cong (λ s → (∂T Γ b c ·r d) ++ (c l· ∂T Γ s d))
                          (trans (flipT-deg Γ c b) (cong (λ n → flipN n b) dc))))))) ⟩
    cm (λ c → cm (λ d → (∂T Γ b c ·r d) ++ (c l· ∂T Γ b' d)) D) C
  ≈⟨ cm-ext' _ _ C (λ c → cm-sum _ _ D) ⟩
    cm (λ c → cm (λ d → ∂T Γ b c ·r d) D ++ cm (λ d → c l· ∂T Γ b' d) D) C
  ≈⟨ cm-sum _ _ C ⟩
    cm (λ c → cm (λ d → ∂T Γ b c ·r d) D) C ++ cm (λ c → cm (λ d → c l· ∂T Γ b' d) D) C
  ≈⟨ ++-cong part1 part2 ⟩
    prod (∂B Γ b C) D ++ prod C (∂B Γ b' D)
  ∎
  where
  b' = flipN p b
  part1 : cm (λ c → cm (λ d → ∂T Γ b c ·r d) D) C ≈ prod (∂B Γ b C) D
  part1 =
    begin
      cm (λ c → cm (λ d → cm (λ e → (e ++ d) ∷ []) (∂T Γ b c)) D) C
    ≈⟨ cm-ext' _ _ C (λ c → cm-swap (λ e d → (e ++ d) ∷ []) (∂T Γ b c) D) ⟩
      cm (λ c → prod (∂T Γ b c) D) C
    ≈⟨ ≡→≈ (sym (prod-cmˡ (∂T Γ b) C D)) ⟩
      prod (∂B Γ b C) D
    ∎
  part2 : cm (λ c → cm (λ d → c l· ∂T Γ b' d) D) C ≈ prod C (∂B Γ b' D)
  part2 = cm-ext' _ _ C (λ c → ≡→≈ (sym (cm-fuse (λ e → (c ++ e) ∷ []) (∂T Γ b') D)))
