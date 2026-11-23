------------------------------------------------------------------------
-- The tensor of codes and of maps (S3 of the 𝔖̂ instance,
-- notes/gray-model-formal-plan.md).
--
-- The tensor of codes is K ++ L. A basis element of K ++ L is a pair
-- (u, v) (`join`, `split`). Its degree is deg u + deg v, and its
-- boundary follows the Leibniz rule
--   ∂^α (u ⊗ v) = ∂^α u ⊗ v + u ⊗ ∂^{flip (deg u) α} v      (`bd-join`).
-- For maps f : K → K′ and g : L → L′, f ⊗ g : K ++ L → K′ ++ L′ has
-- matrix (f ⊗ g)(u ⊗ v, u′ ⊗ v′) = f(u, u′) · g(v, v′). It is again a
-- map; the sign in the Leibniz rule is respected because f preserves
-- degrees. ⊗ is functorial.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Tensor (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (even; flip; Code; AC)
open import CaTTExp.Gray.Biclosed.Steiner.Maps nmFB public

------------------------------------------------------------------------
-- Signs.

not-not : ∀ b → not (not b) ≡ b
not-not true  = refl
not-not false = refl

even-suc : ∀ n → even (suc n) ≡ not (even n)
even-suc zero          = refl
even-suc (suc zero)    = refl
even-suc (suc (suc n)) = even-suc n

flip-not : ∀ n β → flip n (not β) ≡ not (flip n β)
flip-not n β with even n
... | true  = refl
... | false = refl

flip-suc : ∀ n β → flip (suc n) β ≡ not (flip n β)
flip-suc n β rewrite even-suc n with even n
... | true  = refl
... | false = sym (not-not β)

flip-add : ∀ m n β → flip (m + n) β ≡ flip n (flip m β)
flip-add zero    n β = refl
flip-add (suc m) n β =
  trans (flip-suc (m + n) β) (trans (cong not (flip-add m n β))
        (trans (sym (flip-not n (flip m β))) (cong (flip n) (sym (flip-suc m β)))))

------------------------------------------------------------------------
-- Basis elements of K ++ L.

join : ∀ K L → El K → El L → El (K ++ L)
join []      L tt      v = v
join (a ∷ K) L (i , u) v = i , join K L u v

split : ∀ K L → El (K ++ L) → El K × El L
split []      L x       = tt , x
split (a ∷ K) L (i , x) = (i , fst (split K L x)) , snd (split K L x)

split-join : ∀ K L u v → split K L (join K L u v) ≡ (u , v)
split-join []      L tt      v = refl
split-join (a ∷ K) L (i , u) v rewrite split-join K L u v = refl

join-split : ∀ K L x → join K L (fst (split K L x)) (snd (split K L x)) ≡ x
join-split []      L x       = refl
join-split (a ∷ K) L (i , x) = cong (i ,_) (join-split K L x)

-- Statements about all basis elements of K ++ L, from joins.
by-join : ∀ K L {P : El (K ++ L) → Set} → (∀ u v → P (join K L u v)) → ∀ x → P x
by-join K L {P} h x = subst P (join-split K L x) (h (fst (split K L x)) (snd (split K L x)))

Σ-join : ∀ K L (f : El (K ++ L) → Nat) →
         Σl (els′ (K ++ L)) f ≡ Σl (els′ K) (λ u → Σl (els′ L) (λ v → f (join K L u v)))
Σ-join []      L f = sym (+-zero _)
Σ-join (a ∷ K) L f =
  trans (Σ-pairs (els (enumA a)) (els′ (K ++ L)) f)
  (trans (Σ-cong (els (enumA a)) (λ i → Σ-join K L (λ x → f (i , x))))
         (sym (Σ-pairs (els (enumA a)) (els′ K) (λ p → Σl (els′ L) (λ v → f (join (a ∷ K) L p v))))))

deg-join : ∀ K L u v → deg (K ++ L) (join K L u v) ≡ deg K u + deg L v
deg-join []      L tt      v = refl
deg-join (a ∷ K) L (i , u) v = trans (cong (degA a i +_) (deg-join K L u v)) (sym (+-assoc (degA a i) (deg K u) (deg L v)))

δ-join : ∀ K L u v u′ v′ → δE (K ++ L) (join K L u v) (join K L u′ v′) ≡ δE K u u′ * δE L v v′
δ-join []      L tt      v tt       v′ = sym (+-zero _)
δ-join (a ∷ K) L (i , u) v (i′ , u′) v′ =
  trans (δ× (enumA a) (enumEl (K ++ L)) i (join K L u v) i′ (join K L u′ v′))
  (trans (cong (δ (enumA a) i i′ *_) (δ-join K L u v u′ v′))
  (trans (sym (*-assoc (δ (enumA a) i i′) (δE K u u′) (δE L v v′)))
         (cong (_* δE L v v′) (sym (δ× (enumA a) (enumEl K) i u i′ u′)))))

bd-join : ∀ K L α u v u′ v′ →
          bd (K ++ L) α (join K L u v) (join K L u′ v′)
          ≡ bd K α u u′ * δE L v v′ + δE K u u′ * bd L (flip (deg K u) α) v v′
bd-join []      L α tt      v tt       v′ = sym (+-zero _)
bd-join (a ∷ K) L α (i , u) v (i′ , u′) v′ =
  let A = bdA a α i i′ ; Δ = δ (enumA a) i i′ ; γ = flip (degA a i) α
      dK = δE K u u′ ; dL = δE L v v′ ; bK = bd K γ u u′
      bL = bd L (flip (deg K u) γ) v v′
  in trans (cong₂ _+_ (cong (A *_) (δ-join K L u v u′ v′)) (cong (Δ *_) (bd-join K L γ u v u′ v′)))
     (trans (cong (A * (dK * dL) +_) (distribˡ Δ (bK * dL) (dK * bL)))
     (trans (sym (+-assoc (A * (dK * dL)) (Δ * (bK * dL)) (Δ * (dK * bL))))
     (cong₂ _+_
        (trans (cong₂ _+_ (sym (*-assoc A dK dL)) (sym (*-assoc Δ bK dL)))
               (sym (distribʳ (A * dK) (Δ * bK) dL)))
        (trans (sym (*-assoc Δ dK bL))
        (trans (cong ((Δ * dK) *_) (cong (λ β → bd L β v v′) (sym (flip-add (degA a i) (deg K u) α))))
               (cong (_* bd L (flip (degA a i + deg K u) α) v v′) (sym (δ× (enumA a) (enumEl K) i u i′ u′))))))))

------------------------------------------------------------------------
-- The tensor of maps.

module _ {K K′ L L′ : Code} (f : Map K K′) (g : Map L L′) where
  private
    F = mat f
    G = mat g

  tmat : Mat (K ++ L) (K′ ++ L′)
  tmat x y = F (fst (split K L x)) (fst (split K′ L′ y)) * G (snd (split K L x)) (snd (split K′ L′ y))

  tmat-join : ∀ u v u′ v′ → tmat (join K L u v) (join K′ L′ u′ v′) ≡ F u u′ * G v v′
  tmat-join u v u′ v′ rewrite split-join K L u v | split-join K′ L′ u′ v′ = refl

  private
    *-zeroˡ : ∀ {a} b → a ≡ 0 → a * b ≡ 0
    *-zeroˡ b refl = refl

    *-zeroʳ : ∀ a {b} → b ≡ 0 → a * b ≡ 0
    *-zeroʳ a refl = *-zero a

    -- a sum of products over K′ ++ L′ splits
    Σ-prod : ∀ (p : El K′ → Nat) (q : El L′ → Nat) →
             Σl (els′ (K′ ++ L′)) (λ y → p (fst (split K′ L′ y)) * q (snd (split K′ L′ y)))
             ≡ Σl (els′ K′) p * Σl (els′ L′) q
    Σ-prod p q =
      trans (Σ-join K′ L′ _)
      (trans (Σ-cong (els′ K′) (λ u′ → Σ-cong (els′ L′) (λ v′ → cong (λ s → p (fst s) * q (snd s)) (split-join K′ L′ u′ v′))))
      (trans (Σ-cong (els′ K′) (λ u′ → sym (Σ-*ˡ (els′ L′) (p u′) q)))
             (sym (Σ-*ʳ (els′ K′) (Σl (els′ L′) q) p))))

    sum0 : ∀ m n → m + n ≡ 0 → (m ≡ 0) × (n ≡ 0)
    sum0 zero n e = refl , e
    sum0 (suc m) n ()

  tdeg : ∀ x y → tmat x y ≡ 0 ⊎ deg (K′ ++ L′) y ≡ deg (K ++ L) x
  tdeg = by-join K L λ u v → by-join K′ L′ λ u′ v′ → go u v u′ v′
    where
      go : ∀ u v u′ v′ → tmat (join K L u v) (join K′ L′ u′ v′) ≡ 0
                         ⊎ deg (K′ ++ L′) (join K′ L′ u′ v′) ≡ deg (K ++ L) (join K L u v)
      go u v u′ v′ with mdeg f u u′ | mdeg g v v′
      ... | inj₁ z  | _      = inj₁ (trans (tmat-join u v u′ v′) (*-zeroˡ _ z))
      ... | inj₂ _  | inj₁ z = inj₁ (trans (tmat-join u v u′ v′) (*-zeroʳ (F u u′) z))
      ... | inj₂ d₁ | inj₂ d₂ = inj₂ (trans (deg-join K′ L′ u′ v′) (trans (cong₂ _+_ d₁ d₂) (sym (deg-join K L u v))))

  taug : ∀ x → deg (K ++ L) x ≡ 0 → Σl (els′ (K′ ++ L′)) (tmat x) ≡ 1
  taug = by-join K L λ u v d →
    let ds = sum0 (deg K u) (deg L v) (trans (sym (deg-join K L u v)) d) in
    trans (Σ-cong (els′ (K′ ++ L′)) (λ y → cong (λ s → F (fst s) (fst (split K′ L′ y)) * G (snd s) (snd (split K′ L′ y)))
                                                 (split-join K L u v)))
    (trans (Σ-prod (F u) (G v)) (cong₂ _*_ (maug f u (fst ds)) (maug g v (snd ds))))

  ----------------------------------------------------------------------
  -- Multiplying by a boundary on either side.

  private
    -- (f ⊗ g) · ∂^β, on joins
    T∂ : ∀ β u v u″ v″ →
         (tmat · ∂ (K′ ++ L′) β) (join K L u v) (join K′ L′ u″ v″)
         ≡ (F · ∂ K′ β) u u″ * G v v″ + F u u″ * (G · ∂ L′ (flip (deg K′ u″) β)) v v″
    T∂ β u v u″ v″ =
      trans (Σ-join K′ L′ _)
      (trans (Σ-cong (els′ K′) (λ u′ → Σ-cong (els′ L′) (λ v′ →
                trans (cong₂ _*_ (tmat-join u v u′ v′) (bd-join K′ L′ β u′ v′ u″ v″))
                      (distribˡ (F u u′ * G v v′) _ _))))
      (trans (Σ-cong (els′ K′) (λ u′ → Σ-+ (els′ L′) _ _))
      (trans (Σ-+ (els′ K′) _ _)
      (cong₂ _+_
        (trans (Σ-cong (els′ K′) (λ u′ →
                  trans (Σ-cong (els′ L′) (λ v′ → r1 (F u u′) (G v v′) (bd K′ β u′ u″) (δE L′ v′ v″)))
                        (sym (Σ-*ˡ (els′ L′) (F u u′ * bd K′ β u′ u″) (λ v′ → G v v′ * δE L′ v′ v″)))))
        (trans (sym (Σ-*ʳ (els′ K′) (Σl (els′ L′) (λ v′ → G v v′ * δE L′ v′ v″)) (λ u′ → F u u′ * bd K′ β u′ u″)))
               (cong ((F · ∂ K′ β) u u″ *_) (Σ-δʳ (enumEl L′) v″ (G v)))))
        (trans (Σ-cong (els′ K′) (λ u′ →
                  trans (Σ-cong (els′ L′) (λ v′ → r2 (F u u′) (G v v′) (δE K′ u′ u″) (bd L′ (flip (deg K′ u′) β) v′ v″)))
                        (sym (Σ-*ˡ (els′ L′) (F u u′ * δE K′ u′ u″) (λ v′ → G v v′ * bd L′ (flip (deg K′ u′) β) v′ v″)))))
        (trans (Σ-cong (els′ K′) (λ u′ → *-assoc (F u u′) (δE K′ u′ u″) _))
        (trans (Σ-cong (els′ K′) (λ u′ → cong (F u u′ *_) (*-comm (δE K′ u′ u″) _)))
        (trans (Σ-cong (els′ K′) (λ u′ → sym (*-assoc (F u u′) _ (δE K′ u′ u″))))
               (Σ-δʳ (enumEl K′) u″ (λ u′ → F u u′ * (G · ∂ L′ (flip (deg K′ u′) β)) v v″))))))))))
      where
        r1 : ∀ a b c d → a * b * (c * d) ≡ a * c * (b * d)
        r1 a b c d = trans (*-assoc a b (c * d)) (trans (cong (a *_) (trans (sym (*-assoc b c d))
                     (trans (cong (_* d) (*-comm b c)) (*-assoc c b d)))) (sym (*-assoc a c (b * d))))
        r2 : ∀ a b c d → a * b * (c * d) ≡ a * c * (b * d)
        r2 = r1

    -- ∂^β · (f ⊗ g), on joins
    ∂T : ∀ β u v u″ v″ →
         (∂ (K ++ L) β · tmat) (join K L u v) (join K′ L′ u″ v″)
         ≡ (∂ K β · F) u u″ * G v v″ + F u u″ * (∂ L (flip (deg K u) β) · G) v v″
    ∂T β u v u″ v″ =
      trans (Σ-join K L _)
      (trans (Σ-cong (els′ K) (λ u′ → Σ-cong (els′ L) (λ v′ →
                trans (cong₂ _*_ (bd-join K L β u v u′ v′) (tmat-join u′ v′ u″ v″))
                      (distribʳ (bd K β u u′ * δE L v v′) (δE K u u′ * bd L (flip (deg K u) β) v v′) (F u′ u″ * G v′ v″)))))
      (trans (Σ-cong (els′ K) (λ u′ → Σ-+ (els′ L) _ _))
      (trans (Σ-+ (els′ K) _ _)
      (cong₂ _+_
        (trans (Σ-cong (els′ K) (λ u′ →
                  trans (Σ-cong (els′ L) (λ v′ → r1 (bd K β u u′) (δE L v v′) (F u′ u″) (G v′ v″)))
                        (sym (Σ-*ˡ (els′ L) (bd K β u u′ * F u′ u″) (λ v′ → δE L v v′ * G v′ v″)))))
        (trans (sym (Σ-*ʳ (els′ K) (Σl (els′ L) (λ v′ → δE L v v′ * G v′ v″)) (λ u′ → bd K β u u′ * F u′ u″)))
               (cong ((∂ K β · F) u u″ *_) (Σ-δ (enumEl L) v (λ v′ → G v′ v″)))))
        (trans (Σ-cong (els′ K) (λ u′ →
                  trans (Σ-cong (els′ L) (λ v′ → r1 (δE K u u′) (bd L (flip (deg K u) β) v v′) (F u′ u″) (G v′ v″)))
                        (sym (Σ-*ˡ (els′ L) (δE K u u′ * F u′ u″) (λ v′ → bd L (flip (deg K u) β) v v′ * G v′ v″)))))
        (trans (sym (Σ-*ʳ (els′ K) ((∂ L (flip (deg K u) β) · G) v v″) (λ u′ → δE K u u′ * F u′ u″)))
               (cong (_* (∂ L (flip (deg K u) β) · G) v v″) (Σ-δ (enumEl K) u (λ u′ → F u′ u″)))))))))
      where
        r1 : ∀ a b c d → a * b * (c * d) ≡ a * c * (b * d)
        r1 a b c d = trans (*-assoc a b (c * d)) (trans (cong (a *_) (trans (sym (*-assoc b c d))
                     (trans (cong (_* d) (*-comm b c)) (*-assoc c b d)))) (sym (*-assoc a c (b * d))))

    -- g's chain condition at either parity
    gch : ∀ γ v v″ → (G · ∂ L′ γ) v v″ + (∂ L (not γ) · G) v v″ ≡ (G · ∂ L′ (not γ)) v v″ + (∂ L γ · G) v v″
    gch true  v v″ = mchain g v v″
    gch false v v″ = sym (mchain g v v″)

    flipF : ∀ n → flip n false ≡ not (flip n true)
    flipF n = flip-not n true

  tchain : ((tmat · ∂ (K′ ++ L′) true) ⊕ (∂ (K ++ L) false · tmat))
           ≐ ((tmat · ∂ (K′ ++ L′) false) ⊕ (∂ (K ++ L) true · tmat))
  tchain = by-join K L λ u v → by-join K′ L′ λ u″ v″ → go u v u″ v″
    where
      go : ∀ u v u″ v″ → ((tmat · ∂ (K′ ++ L′) true) ⊕ (∂ (K ++ L) false · tmat)) (join K L u v) (join K′ L′ u″ v″)
                        ≡ ((tmat · ∂ (K′ ++ L′) false) ⊕ (∂ (K ++ L) true · tmat)) (join K L u v) (join K′ L′ u″ v″)
      go u v u″ v″ with mdeg f u u″
      ... | inj₁ z =
        let A = (F · ∂ K′ true) u u″ ; B = (∂ K false · F) u u″
            A′ = (F · ∂ K′ false) u u″ ; B′ = (∂ K true · F) u u″ ; Gv = G v v″ in
        trans (cong₂ _+_ (trans (T∂ true u v u″ v″) (cong (A * Gv +_) (*-zeroˡ _ z)))
                         (trans (∂T false u v u″ v″) (cong (B * Gv +_) (*-zeroˡ _ z))))
        (trans (cong₂ _+_ (+-zero (A * Gv)) (+-zero (B * Gv)))
        (trans (sym (distribʳ A B Gv))
        (trans (cong (_* Gv) (mchain f u u″))
        (trans (distribʳ A′ B′ Gv)
        (sym (trans (cong₂ _+_ (trans (T∂ false u v u″ v″) (cong (A′ * Gv +_) (*-zeroˡ _ z)))
                               (trans (∂T true u v u″ v″) (cong (B′ * Gv +_) (*-zeroˡ _ z))))
                    (cong₂ _+_ (+-zero (A′ * Gv)) (+-zero (B′ * Gv)))))))))
      ... | inj₂ d =
        let A = (F · ∂ K′ true) u u″ ; B = (∂ K false · F) u u″
            A′ = (F · ∂ K′ false) u u″ ; B′ = (∂ K true · F) u u″ ; Gv = G v v″ ; Fu = F u u″
            γ = flip (deg K u) true
            P = (G · ∂ L′ γ) v v″ ; Q = (∂ L (not γ) · G) v v″
            P′ = (G · ∂ L′ (not γ)) v v″ ; Q′ = (∂ L γ · G) v v″
            -- rewrite the signs through deg K′ u″ = deg K u and flip n false = not γ
            s1 : (G · ∂ L′ (flip (deg K′ u″) true)) v v″ ≡ P
            s1 = cong (λ n → (G · ∂ L′ (flip n true)) v v″) d
            s2 : (∂ L (flip (deg K u) false) · G) v v″ ≡ Q
            s2 = cong (λ β → (∂ L β · G) v v″) (flipF (deg K u))
            s3 : (G · ∂ L′ (flip (deg K′ u″) false)) v v″ ≡ P′
            s3 = trans (cong (λ n → (G · ∂ L′ (flip n false)) v v″) d) (cong (λ β → (G · ∂ L′ β) v v″) (flipF (deg K u)))
        in
        trans (cong₂ _+_ (trans (T∂ true u v u″ v″) (cong (λ x → A * Gv + Fu * x) s1))
                         (trans (∂T false u v u″ v″) (cong (λ x → B * Gv + Fu * x) s2)))
        (trans (+-inter (A * Gv) (Fu * P) (B * Gv) (Fu * Q))
        (trans (cong₂ _+_ (trans (sym (distribʳ A B Gv)) (trans (cong (_* Gv) (mchain f u u″)) (distribʳ A′ B′ Gv)))
                          (trans (sym (distribˡ Fu P Q)) (trans (cong (Fu *_) (gch γ v v″)) (distribˡ Fu P′ Q′))))
        (trans (+-inter (A′ * Gv) (B′ * Gv) (Fu * P′) (Fu * Q′))
        (sym (cong₂ _+_ (trans (T∂ false u v u″ v″) (cong (λ x → A′ * Gv + Fu * x) s3))
                        (∂T true u v u″ v″))))))

  _⊗M_ : Map (K ++ L) (K′ ++ L′)
  _⊗M_ = record { mat = tmat ; mdeg = tdeg ; maug = taug ; mchain = tchain }

infixr 7 _⊗ₘ_
_⊗ₘ_ : ∀ {K K′ L L′} → Map K K′ → Map L L′ → Map (K ++ L) (K′ ++ L′)
f ⊗ₘ g = f ⊗M g

------------------------------------------------------------------------
-- Functoriality.

⊗ₘ-cong : ∀ {K K′ L L′} {f f′ : Map K K′} {g g′ : Map L L′} → f ≈M f′ → g ≈M g′ → (f ⊗ₘ g) ≈M (f′ ⊗ₘ g′)
⊗ₘ-cong {K} {K′} {L} {L′} ef eg = ≈m (λ x y → cong₂ _*_ (≈mat ef _ _) (≈mat eg _ _))

⊗ₘ-id : ∀ K L → (idMap K ⊗ₘ idMap L) ≈M idMap (K ++ L)
⊗ₘ-id K L = ≈m (by-join K L λ u v → by-join K L λ u′ v′ →
  trans (tmat-join (idMap K) (idMap L) u v u′ v′) (sym (δ-join K L u v u′ v′)))

⊗ₘ-∘ : ∀ {K K′ K″ L L′ L″} (f′ : Map K′ K″) (f : Map K K′) (g′ : Map L′ L″) (g : Map L L′) →
       ((f′ ∘M f) ⊗ₘ (g′ ∘M g)) ≈M ((f′ ⊗ₘ g′) ∘M (f ⊗ₘ g))
⊗ₘ-∘ {K} {K′} {K″} {L} {L′} {L″} f′ f g′ g = ≈m (by-join K L λ u v → by-join K″ L″ λ u″ v″ →
  trans (tmat-join (f′ ∘M f) (g′ ∘M g) u v u″ v″)
  (sym (trans (Σ-join K′ L′ _)
       (trans (Σ-cong (els′ K′) (λ u′ → Σ-cong (els′ L′) (λ v′ →
                 trans (cong₂ _*_ (tmat-join f g u v u′ v′) (tmat-join f′ g′ u′ v′ u″ v″))
                       (r1 (mat f u u′) (mat g v v′) (mat f′ u′ u″) (mat g′ v′ v″)))))
       (trans (Σ-cong (els′ K′) (λ u′ → sym (Σ-*ˡ (els′ L′) (mat f u u′ * mat f′ u′ u″) _)))
              (sym (Σ-*ʳ (els′ K′) _ _)))))))
  where
    r1 : ∀ a b c d → a * b * (c * d) ≡ a * c * (b * d)
    r1 a b c d = trans (*-assoc a b (c * d)) (trans (cong (a *_) (trans (sym (*-assoc b c d))
                 (trans (cong (_* d) (*-comm b c)) (*-assoc c b d)))) (sym (*-assoc a c (b * d))))
