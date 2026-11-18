------------------------------------------------------------------------
-- ν on morphisms (ledger A5, N3, collapse step [Q]).
--
-- A morphism of augmented directed complexes f : K → K′ (CaTTExp.
-- Strict.Nu.ADC) is an additive map of the chain monoids commuting with
-- ∂ = ∂⁺ − ∂⁻ (in the form f(∂⁺a) + ∂⁻(fa) = f(∂⁻a) + ∂⁺(fa), so that
-- f need not respect ∂⁺ and ∂⁻ separately: the collapse of a cylinder
-- does not) and every projection πⱼ, and preserving the augmentation.
-- Applying f to every entry of a table sends cells of ν(K) to cells of
-- ν(K′) and commutes with sources, targets and composites, so it is a
-- strict functor ν(f) : ν(K) → ν(K′) (Steiner 2004, Thm 2.11: ν is a
-- functor). Nothing is postulated.
------------------------------------------------------------------------
module CaTTExp.Strict.NuMap where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.Expr using (Functor)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms using (at; unit)
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Cylinder using (sel; selV; lin-sel; augm-0)
open import CaTTExp.Strict.Generation using (≤-dec)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Nat using (_*_)

private
  infix  1 begin_
  infixr 2 _≡⟨_⟩_
  infix  3 _∎
  begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin p = p
  _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q
  _∎ : ∀ {A : Set} (x : A) → x ≡ x
  x ∎ = refl

record Hom (K K′ : ADC) : Set where
  private
    module K  = ADC K
    module K′ = ADC K′
  field
    f    : K.M → K′.M
    f-ε  : f K.ε ≡ K′.ε
    f-⊕  : ∀ a b → f (a K.⊕ b) ≡ f a K′.⊕ f b
    f-∂  : ∀ a → f (K.∂⁺ a) K′.⊕ K′.∂⁻ (f a) ≡ f (K.∂⁻ a) K′.⊕ K′.∂⁺ (f a)
    f-π  : ∀ j a → f (K.π j a) ≡ K′.π j (f a)
    f-aug : ∀ a → K′.aug (f a) ≡ K.aug a

module _ {K K′ : ADC} (φ : Hom K K′) (L : Nat) where
  private
    module K  = ADC K
    module K′ = ADC K′
    𝕄  = K.𝕄
    𝕄′ = K′.𝕄
  open Hom φ

  fP : P 𝕄 → P 𝕄′
  fP (a , b) = f a , f b

  mapT : ∀ {m} → Tab 𝕄 m → Tab 𝕄′ m
  mapT []      = []
  mapT (e ∷ r) = fP e ∷ mapT r

  mapT-zeros : ∀ {m} → mapT (zeros 𝕄 {m}) ≡ zeros 𝕄′
  mapT-zeros {zero}  = refl
  mapT-zeros {suc m} = cong₂ _∷_ (cong₂ _,_ f-ε f-ε) mapT-zeros

  mapT-add : ∀ {m} (r r′ : Tab 𝕄 m) → mapT (add 𝕄 r r′) ≡ add 𝕄′ (mapT r) (mapT r′)
  mapT-add []            []              = refl
  mapT-add ((a , b) ∷ r) ((c , d) ∷ r′) = cong₂ _∷_ (cong₂ _,_ (f-⊕ a c) (f-⊕ b d)) (mapT-add r r′)

  mapT-src : ∀ {m} n (x : Tab 𝕄 m) → mapT (srcT 𝕄 n x) ≡ srcT 𝕄′ n (mapT x)
  mapT-src n       []            = refl
  mapT-src zero    ((a , b) ∷ r) = cong ((f a , f a) ∷_) mapT-zeros
  mapT-src (suc n) (e ∷ r)       = cong (fP e ∷_) (mapT-src n r)

  mapT-tgt : ∀ {m} n (x : Tab 𝕄 m) → mapT (tgtT 𝕄 n x) ≡ tgtT 𝕄′ n (mapT x)
  mapT-tgt n       []            = refl
  mapT-tgt zero    ((a , b) ∷ r) = cong ((f b , f b) ∷_) mapT-zeros
  mapT-tgt (suc n) (e ∷ r)       = cong (fP e ∷_) (mapT-tgt n r)

  mapT-comp : ∀ {m} n (x y : Tab 𝕄 m) → mapT (compT 𝕄 n x y) ≡ compT 𝕄′ n (mapT x) (mapT y)
  mapT-comp n       []            []             = refl
  mapT-comp zero    ((a , b) ∷ r) ((c , d) ∷ r′) = cong ((f a , f d) ∷_) (mapT-add r r′)
  mapT-comp (suc n) (e ∷ r)       (e′ ∷ r′)      = cong (fP e ∷_) (mapT-comp n r r′)

  ----------------------------------------------------------------------
  -- Cells go to cells.

  private
    InD : ∀ j u → InDeg K L j u → InDeg K′ L j (f u)
    InD j u p = trans (sym (f-π j u)) (cong f p)

    BdF : ∀ a b u → Bd K L (a , b) u → Bd K′ L (f a , f b) (f u)
    -- (∂⁺fu + fa) + f∂⁻u = ∂⁻fu + f∂⁺u + fa = ∂⁻fu + f(∂⁺u + a)
    --   = ∂⁻fu + f(∂⁻u + b) = (∂⁻fu + fb) + f∂⁻u, then cancel.
    BdF a b u p = K′.cancel _ _ (f (K.∂⁻ u)) (begin
      (K′.∂⁺ (f u) ⊕′ f a) ⊕′ f (K.∂⁻ u)   ≡⟨ sh (K′.∂⁺ (f u)) (f a) (f (K.∂⁻ u)) ⟩
      (f (K.∂⁻ u) ⊕′ K′.∂⁺ (f u)) ⊕′ f a   ≡⟨ cong (_⊕′ f a) (sym (f-∂ u)) ⟩
      (f (K.∂⁺ u) ⊕′ K′.∂⁻ (f u)) ⊕′ f a   ≡⟨ sh2 (f (K.∂⁺ u)) (K′.∂⁻ (f u)) (f a) ⟩
      K′.∂⁻ (f u) ⊕′ (f (K.∂⁺ u) ⊕′ f a)   ≡⟨ cong (K′.∂⁻ (f u) ⊕′_) (sym (f-⊕ _ a)) ⟩
      K′.∂⁻ (f u) ⊕′ f (K.∂⁺ u K.⊕ a)      ≡⟨ cong (λ q → K′.∂⁻ (f u) ⊕′ f q) p ⟩
      K′.∂⁻ (f u) ⊕′ f (K.∂⁻ u K.⊕ b)      ≡⟨ cong (K′.∂⁻ (f u) ⊕′_) (f-⊕ _ b) ⟩
      K′.∂⁻ (f u) ⊕′ (f (K.∂⁻ u) ⊕′ f b)   ≡⟨ sh3 (K′.∂⁻ (f u)) (f (K.∂⁻ u)) (f b) ⟩
      (K′.∂⁻ (f u) ⊕′ f b) ⊕′ f (K.∂⁻ u)   ∎)
      where
      _⊕′_ = K′._⊕_
      -- (x + y) + z ≡ (z + x) + y
      sh : ∀ x y z → (x ⊕′ y) ⊕′ z ≡ (z ⊕′ x) ⊕′ y
      sh x y z = trans (K′.⊕-comm (x ⊕′ y) z) (sym (K′.⊕-assoc z x y))
      -- (x + y) + z ≡ y + (x + z)
      sh2 : ∀ x y z → (x ⊕′ y) ⊕′ z ≡ y ⊕′ (x ⊕′ z)
      sh2 x y z = trans (cong (_⊕′ z) (K′.⊕-comm x y)) (K′.⊕-assoc y x z)
      -- x + (y + z) ≡ (x + z) + y
      sh3 : ∀ x y z → x ⊕′ (y ⊕′ z) ≡ (x ⊕′ z) ⊕′ y
      sh3 x y z = trans (cong (x ⊕′_) (K′.⊕-comm y z)) (sym (K′.⊕-assoc x z y))

    CndF : ∀ {m} j p (r : Tab 𝕄 m) → Cnd K L j p r → Cnd K′ L j (fP p) (mapT r)
    CndF j p []            c = tt
    CndF j (a , b) ((u , v) ∷ r) ((du , dv , bu , bv) , c) =
      (InD j u du , InD j v dv , BdF a b u bu , BdF a b v bv) , CndF (suc j) (u , v) r c

    LastF : ∀ {m} (x : Tab 𝕄 (suc m)) → Last K L x → Last K′ L (mapT x)
    LastF ((u , v) ∷ [])  l = cong f l
    LastF (e ∷ (e′ ∷ r)) l = LastF (e′ ∷ r) l

  cellF : ∀ x → IsCell K L x → IsCell K′ L (mapT x)
  cellF ((u , v) ∷ r) ((du , dv , au , av) , c , l) =
    (InD 0 u du , InD 0 v dv , trans (f-aug u) au , trans (f-aug v) av) ,
    CndF 1 (u , v) r c , LastF ((u , v) ∷ r) l

  νf : Cell K L → Cell K′ L
  νf (x , c) = mapT x , cellF x c

  functor : Functor (nu K L) (nu K′ L)
  functor = record
    { F      = νf
    ; F-src  = λ n x → ≡-cell K′ L (mapT-src n (fst x))
    ; F-tgt  = λ n x → ≡-cell K′ L (mapT-tgt n (fst x))
    ; F-comp = λ n x y p q → ≡-cell K′ L (mapT-comp n (fst x) (fst y))
    }

------------------------------------------------------------------------
-- Morphisms of complexes with finite bases, from checks on the basis.
--
-- Q gives the image of each basis element of B. The checks: Q is a
-- chain map on each basis element (in the ∂⁺/∂⁻ form above), Qᵢ has
-- the degree of bᵢ, and ε(Qᵢ) is 1 for degree-0 elements and 0 else.

module LinHom {N N′ : Nat} (B : Basis N) (B′ : Basis N′) (Q : Vec (Chn N′) N) where
  private
    module B  = Basis B
    module B′ = Basis B′

  qf : Chn N → Chn N′
  qf c = lin c Q

  Qi : Nat → Chn N′
  Qi i = at 0c Q i

  ChainQ DegQ AugQ : Set
  ChainQ = ∀ i → i < N → qf (at 0c B.bplus i) +c lin (Qi i) B′.bminus ≡ qf (at 0c B.bminus i) +c lin (Qi i) B′.bplus
  DegQ   = ∀ i → i < N → prj (at 0 B.gdeg i) B′.gdeg (Qi i) ≡ Qi i
  AugQ   = ∀ i → i < N → augm B′.gdeg (Qi i) ≡ (if at 0 B.gdeg i ==ℕ 0 then 1 else 0)

  private
    at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
    at-out d []       i       _       = refl
    at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

    -- Pointwise agreement below N suffices for lin c vs with c : Chn N.
    lin-pt : ∀ {M} (c : Chn N) (vs ws : Vec (Chn M) N) → (∀ i → i < N → at 0c vs i ≡ at 0c ws i) →
             lin c vs ≡ lin c ws
    lin-pt c vs ws h = lin-supp-cong c vs ws col
      where
      col : ∀ i → (at 0 c i ≡ 0) ⊎ (at 0c vs i ≡ at 0c ws i)
      col i with ≤-dec N i
      ... | inj₁ Ni = inj₂ (trans (at-out 0c vs i Ni) (sym (at-out 0c ws i Ni)))
      ... | inj₂ iN = inj₂ (h i iN)

    if-same : ∀ {A : Set} b {x : A} → (if b then x else x) ≡ x
    if-same true  = refl
    if-same false = refl

    prj-sel : ∀ {m} j (gs u : Vec Nat m) → prj j gs u ≡ sel (λ g → g ==ℕ j) gs u
    prj-sel j []       []      = refl
    prj-sel j (g ∷ gs) (a ∷ u) = cong (_ ∷_) (prj-sel j gs u)

    -- πⱼ πₕ v is πₕ v if h = j and 0 otherwise.
    prj-prj-eq : ∀ {m} j (gs v : Vec Nat m) → prj j gs (prj j gs v) ≡ prj j gs v
    prj-prj-eq j []       []      = refl
    prj-prj-eq j (g ∷ gs) (a ∷ v) with g ==ℕ j
    ... | true  = cong (a ∷_) (prj-prj-eq j gs v)
    ... | false = cong (0 ∷_) (prj-prj-eq j gs v)

    prj-prj-ne : ∀ {m} h j (gs v : Vec Nat m) → (h ==ℕ j) ≡ false → prj j gs (prj h gs v) ≡ 0c
    prj-prj-ne h j []       []      ne = refl
    prj-prj-ne h j (g ∷ gs) (a ∷ v) ne with g ==ℕ h in eh | g ==ℕ j in ej
    ... | true  | true  = ⊥-elim (ne-false (trans (sym (==ℕ-sound g h (subst T (sym eh) tt))) (==ℕ-sound g j (subst T (sym ej) tt))))
      where
      ne-false : h ≡ j → ⊥
      ne-false refl = subst T ne (==ℕ-refl h)
    ... | true  | false = cong (0 ∷_) (prj-prj-ne h j gs v ne)
    ... | false | true  = cong (0 ∷_) (prj-prj-ne h j gs v ne)
    ... | false | false = cong (0 ∷_) (prj-prj-ne h j gs v ne)

    ⊙-* : ∀ {m} (gs : Vec Nat m) k v → augm gs (k ⊙ v) ≡ k * augm gs v
    ⊙-* gs zero    v = augm-0 gs
    ⊙-* gs (suc k) v = trans (augm-+′ gs v (k ⊙ v)) (cong (augm gs v +_) (⊙-* gs k v))

    *1 : ∀ k → k * 1 ≡ k
    *1 zero    = refl
    *1 (suc k) = cong suc (*1 k)

    *0 : ∀ k → k * 0 ≡ 0
    *0 zero    = refl
    *0 (suc k) = *0 k

    augm-lin : ∀ {m} (gs : Vec Nat m) (c : Vec Nat m) (vs : Vec (Chn N′) m) →
               (∀ i → i < m → augm B′.gdeg (at 0c vs i) ≡ (if at 0 gs i ==ℕ 0 then 1 else 0)) →
               augm B′.gdeg (lin c vs) ≡ augm gs c
    augm-lin []       []      []       h = augm-0 B′.gdeg
    augm-lin (g ∷ gs) (k ∷ c) (v ∷ vs) h =
      trans (augm-+′ B′.gdeg (k ⊙ v) (lin c vs))
        (cong₂ _+_ (trans (⊙-* B′.gdeg k v) (hd (h 0 (s≤s z≤n))))
                   (augm-lin gs c vs (λ i p → h (suc i) (s≤s p))))
      where
      hd : augm B′.gdeg v ≡ (if g ==ℕ 0 then 1 else 0) → k * augm B′.gdeg v ≡ (if g ==ℕ 0 then k else 0)
      hd e with g ==ℕ 0
      ... | true  = trans (cong (k *_) e) (*1 k)
      ... | false = trans (cong (k *_) e) (*0 k)

  module _ (ch : ChainQ) (dq : DegQ) (aq : AugQ) where
    hom : Hom (adc B) (adc B′)
    hom = record
      { f     = qf
      ; f-ε   = lin-0 Q
      ; f-⊕   = λ a b → lin-+ a b Q
      ; f-∂   = fd
      ; f-π   = fπ
      ; f-aug = λ a → augm-lin B.gdeg a Q aq
      }
      where
      fd : ∀ a → qf (lin a B.bplus) +c lin (qf a) B′.bminus ≡ qf (lin a B.bminus) +c lin (qf a) B′.bplus
      fd a =
        trans (cong₂ _+c_ (lin-lin a B.bplus Q) (lin-lin a Q B′.bminus))
        (trans (lin-zip a _ _)
        (trans (lin-pt a _ _ pt)
        (trans (sym (lin-zip a _ _))
               (sym (cong₂ _+c_ (lin-lin a B.bminus Q) (lin-lin a Q B′.bplus))))))
        where
        pt : ∀ i → i < N →
             at 0c (zipV _+c_ (mapV qf B.bplus) (mapV (λ v → lin v B′.bminus) Q)) i ≡
             at 0c (zipV _+c_ (mapV qf B.bminus) (mapV (λ v → lin v B′.bplus) Q)) i
        pt i iN =
          trans (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV qf B.bplus) (mapV (λ v → lin v B′.bminus) Q) i)
          (trans (cong₂ _+c_ (at-map qf 0c 0c (lin-0 Q) B.bplus i) (at-map (λ v → lin v B′.bminus) 0c 0c (lin-0 B′.bminus) Q i))
          (trans (ch i iN)
          (sym (trans (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV qf B.bminus) (mapV (λ v → lin v B′.bplus) Q) i)
                      (cong₂ _+c_ (at-map qf 0c 0c (lin-0 Q) B.bminus i) (at-map (λ v → lin v B′.bplus) 0c 0c (lin-0 B′.bplus) Q i))))))

      fπ : ∀ j a → qf (prj j B.gdeg a) ≡ prj j B′.gdeg (qf a)
      fπ j a =
        trans (cong qf (prj-sel j B.gdeg a))
        (trans (sym (lin-sel (λ g → g ==ℕ j) B.gdeg a Q))
        (trans (lin-pt a _ _ pt)
               (sym (prj-lin j B′.gdeg a Q))))
        where
        pt : ∀ i → i < N → at 0c (selV (λ g → g ==ℕ j) B.gdeg Q) i ≡ at 0c (mapV (prj j B′.gdeg) Q) i
        pt i iN =
          trans (at-zip (λ g v → if g ==ℕ j then v else 0c) 0 0c 0c (if-same (0 ==ℕ j)) B.gdeg Q i)
            (trans (go (at 0 B.gdeg i) refl)
                   (sym (at-map (prj j B′.gdeg) 0c 0c (prj-0 j B′.gdeg) Q i)))
          where
          go : ∀ g → at 0 B.gdeg i ≡ g → (if g ==ℕ j then Qi i else 0c) ≡ prj j B′.gdeg (Qi i)
          go g e with g ==ℕ j in gj
          ... | true  rewrite ==ℕ-sound g j (subst T (sym gj) tt) =
                trans (sym (dq i iN)) (trans (cong (λ h → prj h B′.gdeg (Qi i)) e)
                  (sym (trans (cong (prj j B′.gdeg) (trans (sym (dq i iN)) (cong (λ h → prj h B′.gdeg (Qi i)) e)))
                              (prj-prj-eq j B′.gdeg (Qi i)))))
          ... | false = sym (trans (cong (prj j B′.gdeg) (trans (sym (dq i iN)) (cong (λ h → prj h B′.gdeg (Qi i)) e)))
                                   (prj-prj-ne g j B′.gdeg (Qi i) gj))

    -- ν(Q) : ν(B) → ν(B′).
    νQ : ∀ L → Functor (ν B L) (ν B′ L)
    νQ L = functor hom L

------------------------------------------------------------------------
-- Example: the degeneracy D² → D¹ (x, f, α, g, y ↦ x, f, 0, f, y). It
-- is a chain map but does not respect ∂⁺ and ∂⁻ separately (∂⁺α = g ↦
-- f while α ↦ 0), so ν of it sends the atom ⟨α⟩ to the identity on ⟨f⟩.

private
  degen : Vec (Chn 3) 5
  degen = unit 0 ∷ unit 1 ∷ 0c ∷ unit 1 ∷ unit 2 ∷ []

  module DG = LinHom BD² BD¹ degen

  dg-ch : DG.ChainQ
  dg-ch zero                                  _ = refl
  dg-ch (suc zero)                            _ = refl
  dg-ch (suc (suc zero))                      _ = refl
  dg-ch (suc (suc (suc zero)))                _ = refl
  dg-ch (suc (suc (suc (suc zero))))          _ = refl
  dg-ch (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

  dg-deg : DG.DegQ
  dg-deg zero                                  _ = refl
  dg-deg (suc zero)                            _ = refl
  dg-deg (suc (suc zero))                      _ = refl
  dg-deg (suc (suc (suc zero)))                _ = refl
  dg-deg (suc (suc (suc (suc zero))))          _ = refl
  dg-deg (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

  dg-aug : DG.AugQ
  dg-aug zero                                  _ = refl
  dg-aug (suc zero)                            _ = refl
  dg-aug (suc (suc zero))                      _ = refl
  dg-aug (suc (suc (suc zero)))                _ = refl
  dg-aug (suc (suc (suc (suc zero))))          _ = refl
  dg-aug (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

  νdegen : Functor (ν BD² 2) (ν BD¹ 2)
  νdegen = DG.νQ dg-ch dg-deg dg-aug 2

  -- The atom ⟨α⟩ : ⟨f⟩ ⇒ ⟨g⟩ of ν(λD²) …
  atom-α : ωCat.C (ν BD² 2)
  atom-α = ((unit 0 , unit 4) ∷ (unit 1 , unit 3) ∷ (unit 2 , unit 2) ∷ []) ,
           ((refl , refl , refl , refl) , ((refl , refl , refl , refl) , (refl , refl , refl , refl) , tt) , refl)

  -- … goes to the identity 2-cell on ⟨f⟩: the table (x, y), (f, f), (0, 0).
  _ : fst (Functor.F νdegen atom-α) ≡ ((unit 0 , unit 2) ∷ (unit 1 , unit 1) ∷ (0c , 0c) ∷ [])
  _ = refl
