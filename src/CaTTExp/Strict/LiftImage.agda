------------------------------------------------------------------------
-- Images of the closed support under a map of complexes.
--
-- Let X be a cell of ν(K(Δ))(x, y), Δ a pasting context, and F a map
-- of complexes K(Δ) → K(Γ) (given on basis elements, non-negative, a
-- chain map in the bag form of Strict.Cell.Transport). Let Cl be a
-- set of tuples of K(Γ) that contains every row of F(X) and is closed
-- under positive faces. Then for every b in the closed support D X of
-- X (in Δ),
--
--   image : every tuple of F b is in Cl.
--
-- So F does not lose the closed support: ↓F(b) ⊆ ↓F(X) for b ∈ ↓X,
-- although F b may be empty while b's faces are not (identity-like
-- images), so this does not follow from b ∈ ↓X entrywise.
--
-- Proof: lift b to the top row of a cell obtained from X by cuts
-- (Strict.Recon.lift), keeping track of the images. For a cut
-- w = u + ∂(c<a) (Strict.Cut.cut-eq), applying F and the chain-map
-- equation gives F w + ∂⁻F(c<a) = F u + ∂⁺F(c<a) as bags, so every tuple
-- of F w is in F u or a positive face of a tuple of F c.
------------------------------------------------------------------------
module CaTTExp.Strict.LiftImage where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Cut
open import CaTTExp.Strict.Rad using (∈L-count; pos-≤; cm-ge; cm-mem; setTop-top)
open import CaTTExp.Strict.Recon using (step-face; SubT; self; inS; inU; Sub-cell; flat-sub; topdeg; ∈L-++l)
open import CaTTExp.Strict.TopCell using (Pos; _⊎_; inj₁; inj₂)
open import CaTTExp.Strict.CohCase using (count-∈L; All-∈L; ∈L-++r)
open import CaTTExp.Strict.Order using (OInv; oinv-⊢ps)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; _≤_; z≤n; s≤s; ≤-trans; n≤m+n)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; filter⇒)
open import CaTTExp.Gray.DownAgree ∅ renaming (module Faces to DF)

------------------------------------------------------------------------
-- Membership in bags.

in-cm : ∀ g X {b z} → b ∈L X → z ∈L g b → z ∈L cm g X
in-cm g X {b} {z} mb mz = count-∈L z (cm g X) (pos-≤ (∈L-count b X mb) (cm-ge g X b z (∈L-count z (g b) mz)))

cm-out : ∀ g X {z} → z ∈L cm g X → Σ Tuple λ b → (b ∈L X) × (z ∈L g b)
cm-out g X {z} m with cm-mem g X z (∈L-count z (cm g X) m)
... | b , mb , p = b , mb , count-∈L z (g b) p

private
  pos+ : ∀ a b → Pos (a + b) → Pos a ⊎ Pos b
  pos+ (suc a) b _ = inj₁ tt
  pos+ zero    b p = inj₂ p

  -- A + B = C + D and P + B = N + D with C = P = 0 force A = 0.
  arith : ∀ A B C D P N → A + B ≡ C + D → P + B ≡ N + D → Pos A → Pos C ⊎ Pos P
  arith A B (suc C) D P N _ _ _ = inj₁ tt
  arith A B zero D (suc P) N _ _ _ = inj₂ tt
  arith (suc A) B zero D zero N e₁ e₂ _ = ⊥-elim (no A N D (trans (cong (suc A +_) (sym e₂)) e₁))
    where
    no : ∀ A N D → suc A + (N + D) ≡ D → ⊥
    no A N D e = z (+-cancelʳ D (suc A + N) 0 (trans (+-assoc (suc A) N D) e))
      where
      z : suc A + N ≡ 0 → ⊥
      z ()

  top-map : ∀ f X → top (mapTw f X) ≡ f (top X)
  top-map f (base _)     = refl
  top-map f (step _ _ _) = refl

  top-in-flat : ∀ X {t} → t ∈L top X → t ∈L flat X
  top-in-flat (base _)     m = m
  top-in-flat (step S U c) m = ∈L-++r (flat S) (∈L-++r (flat U) m)

------------------------------------------------------------------------
-- The lemma.

module _ {Δ Γ : Ctx} (P : Δ ⊢ps) {x y : Nat}
  (F : Tuple → Bag)
  (f-chain : ∀ k b c → All (Basis Δ x y k) c →
             cm (∂T Γ b) (cm F c) ++ cm F (cm (∂T Δ (not b)) c) ≈ cm (∂T Γ (not b)) (cm F c) ++ cm F (cm (∂T Δ b) c))
  (Cl : Tuple → Set)
  (Cl-face : ∀ {z z'} → Cl z → z' ∈L ∂T Γ true z → Cl z')
  where

  private
    I   = oinv-⊢ps P
    inv = psInv P
    module Fc = DF (cells Δ)
    Cell = IsCellL Δ x y
    topBas = Cells.IsCell-top (∂T Δ) (Basis Δ x y)

  f : Bag → Bag
  f = cm F

  Good : Tower → Set
  Good Z = ∀ {z} → z ∈L flat (mapTw f Z) → Cl z

  -- Every tuple of F(cut) is in F u or a positive face of a tuple of F c.
  cut-image : ∀ q a u v c → All (Basis Δ x y (suc q)) c → ∂B Δ true c ++ u ≈ ∂B Δ false c ++ v →
              ∀ {z} → z ∈L f (cut I a u v c) →
              (z ∈L f u) ⊎ (Σ Tuple λ t → (t ∈L f c) × (z ∈L ∂T Γ true t))
  cut-image q a u v c ac ch {z} m with arith (k (f w)) (k (f N)) (k (f u)) (k (f Pp)) (k (∂B Γ true (f Lo))) (k (∂B Γ false (f Lo))) e₁ e₂ (∈L-count z (f w) m)
    where
    w  = cut I a u v c
    Lo = below I a c
    N  = ∂B Δ false Lo
    Pp = ∂B Δ true Lo
    k : Bag → Nat
    k = count z
    fE : f w ++ f N ≈ f u ++ f Pp
    fE = ≈-trans (≡→≈ (sym (cm-++ F w N))) (≈-trans (cm-cong F _ _ (cut-eq I a u v c ch)) (≡→≈ (cm-++ F u Pp)))
    fC : ∂B Γ true (f Lo) ++ f N ≈ ∂B Γ false (f Lo) ++ f Pp
    fC = f-chain (suc q) true Lo (All-filter _ c ac)
    e₁ : k (f w) + k (f N) ≡ k (f u) + k (f Pp)
    e₁ = trans (sym (count-++ z (f w) (f N))) (trans (at fE z) (count-++ z (f u) (f Pp)))
    e₂ : k (∂B Γ true (f Lo)) + k (f N) ≡ k (∂B Γ false (f Lo)) + k (f Pp)
    e₂ = trans (sym (count-++ z (∂B Γ true (f Lo)) (f N))) (trans (at fC z) (count-++ z (∂B Γ false (f Lo)) (f Pp)))
  ... | inj₁ p = inj₁ (count-∈L z (f u) p)
  ... | inj₂ p with cm-out (∂T Γ true) (f (below I a c)) (count-∈L z _ p)
  ...   | t , mt , mz with cm-out F (below I a c) mt
  ...     | b , mb , mtb = inj₂ (t , in-cm F c (fst (filter⇒ _ c mb)) mtb , mz)

  good-setTop : ∀ S U c w → Good (step S U c) → (∀ {z} → z ∈L f w → Cl z) → Good (setTop S w)
  good-setTop (base s) U c w g h m = h m
  good-setTop (step S₁ S₂ u) U c w g h {z} m with ∈L-++ (flat (mapTw f S₁)) m
  ... | inj₁ a = g (∈L-++l (flat (mapTw f (step S₁ S₂ u))) _ (∈L-++l (flat (mapTw f S₁)) _ a))
  ... | inj₂ b with ∈L-++ (flat (mapTw f S₂)) b
  ...   | inj₁ a = g (∈L-++l (flat (mapTw f (step S₁ S₂ u))) _ (∈L-++r (flat (mapTw f S₁)) (∈L-++l (flat (mapTw f S₂)) _ a)))
  ...   | inj₂ d = h d

  lift-step : ∀ {m Z t t'} → Cell m Z → Good Z → t ∈L top Z → Fc.Step t t' →
              Σ Nat λ m' → Σ Tower λ Z' → Cell m' Z' × Good Z' × (t' ∈L top Z')
  lift-step {zero} {base c} {t} cZ g mt sp with step-face inv sp
  ... | σ , mσ = ⊥-elim (none (subst (λ B → _ ∈L B) (∂-deg0 t (topdeg P 0 (base c) cZ mt) σ) mσ))
    where
    none : ∀ {z} → z ∈L [] → ⊥
    none ()
  lift-step {suc q} {step S U c} {t} {t'} (cS , cU , par , ch , ac) g mt sp with step-face inv sp
  ... | σ , mσ =
    q , setTop S w , cut-cell I inv q t' S (top U) c cS (topBas q U cU) ac ch ,
    good-setTop S U c w g gw ,
    subst (t' ∈L_) (sym (setTop-top S w)) (count-∈L t' w (subst Pos (sym (cut-at I t' (top S) (top U) c)) (pos σ mσ)))
    where
    w = cut I t' (top S) (top U) c
    ge : ∀ σ → t' ∈L ∂T Δ σ t → Pos (count t' (∂B Δ σ c))
    ge σ m = pos-≤ (∈L-count t c mt) (cm-ge (∂T Δ σ) c t t' (∈L-count t' _ m))
    pos : ∀ σ → t' ∈L ∂T Δ σ t → Pos (count t' (top S) + count t' (∂B Δ true c))
    pos true  m = pos-≤ (ge true m) (n≤m+n (count t' (top S)) _)
    pos false m =
      subst Pos (trans (+-comm (count t' (top U)) _)
                (trans (sym (count-++ t' (∂B Δ false c) (top U)))
                (trans (sym (at ch t'))
                (trans (count-++ t' (∂B Δ true c) (top S)) (+-comm _ (count t' (top S)))))))
        (pos-≤ (ge false m) (n≤m+n (count t' (top U)) _))
    inS' : ∀ {z} → z ∈L f (top S) → z ∈L flat (mapTw f (step S U c))
    inS' m = ∈L-++l (flat (mapTw f S)) _ (top-in-flat (mapTw f S) (subst (λ B → _ ∈L B) (sym (top-map f S)) m))
    inC : ∀ {z} → z ∈L f c → z ∈L flat (mapTw f (step S U c))
    inC m = ∈L-++r (flat (mapTw f S)) (∈L-++r (flat (mapTw f U)) m)
    gw : ∀ {z} → z ∈L f w → Cl z
    gw m with cut-image q t' (top S) (top U) c ac ch m
    ... | inj₁ a = g (inS' a)
    ... | inj₂ (t₀ , mt₀ , mz) = Cl-face (g (inC mt₀)) mz

  lift* : ∀ {m Z t j b} → Cell m Z → Good Z → t ∈L top Z → Fc.Reach j t b →
          Σ Nat λ m' → Σ Tower λ Z' → Cell m' Z' × Good Z' × (b ∈L top Z')
  lift* cZ g mt Fc.done = _ , _ , cZ , g , mt
  lift* cZ g mt (Fc.step s r) with lift-step cZ g mt s
  ... | m' , Z' , cZ' , g' , mt' = lift* cZ' g' mt' r

  private
    flat-map-mono : ∀ {n X m Z z} → SubT n X m Z → z ∈L flat (mapTw f Z) → z ∈L flat (mapTw f X)
    flat-map-mono self m = m
    flat-map-mono {X = step S U c} (inS p) m = ∈L-++l (flat (mapTw f S)) _ (flat-map-mono p m)
    flat-map-mono {X = step S U c} (inU p) m = ∈L-++r (flat (mapTw f S)) (∈L-++l (flat (mapTw f U)) _ (flat-map-mono p m))

  -- The images of the closed support of X lie in Cl.
  -- (The face path need not be bounded, unlike in D.)
  image : ∀ {n X b} → Cell n X → Good X → (Σ Tuple λ t → t ∈L flat X × Σ Nat λ j → Fc.Reach j t b) →
          ∀ {z} → z ∈L F b → Cl z
  image {n} {X} {b} cX g (t , mt , j , r) {z} mz with flat-sub P n X cX mt
  ... | m , V , sub , mv with lift* (Sub-cell P cX sub) (λ {z′} m′ → g (flat-map-mono sub m′)) mv r
  ...   | m' , Z' , cZ' , g' , mb =
    g' (top-in-flat (mapTw f Z') (subst (λ B → z ∈L B) (sym (top-map f Z')) (in-cm F (top Z') mb mz)))
